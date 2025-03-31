// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DPU datapath
// Owner: Stefan Mach <stefan.mach@axelera.ai>
// TODO(@stefan.mach): Actually gate half of datapath and flops for PW32 instructions!

module dpu_dp
  import dpu_pkg::*;
  import dpu_csr_reg_pkg::*;
(
  input wire clk_i,
  input wire rst_ni,

  // DPcmd stream
  input  dpu_instr_t instruction_data_i,
  input  logic       instruction_last_i,
  input  logic       instruction_valid_i,
  output logic       instruction_ready_o,

  // DP done
  output logic dp_done_o,

  // IAU AXI stream
  input  logic [PW_IAU_W-1:0] iau_axis_data_i,
  input  logic                iau_axis_last_i,
  input  logic                iau_axis_valid_i,
  output logic                iau_axis_ready_o,

  // IFD1 AXI stream
  input  logic [PW_IO_W-1:0] ifd1_axis_data_i,
  input  logic               ifd1_axis_last_i,
  input  logic               ifd1_axis_valid_i,
  output logic               ifd1_axis_ready_o,

  // ODR AXI stream
  output logic [PW_IO_W-1:0] odr_axis_data_o,
  output logic               odr_axis_last_o,
  output logic               odr_axis_valid_o,
  input  logic               odr_axis_ready_i,

  // CSR configuration
  input dpu_csr_reg_pkg::dpu_csr_reg2hw_dp_ctrl_reg_t dp_ctrl_i,

  // Status observation
  output dpu_csr_reg_pkg::dpu_csr_hw2reg_dp_status_reg_t dp_status_o,

  // Error and IRQ signals
  output dpu_csr_dp_irq_status_reg_t error_irqs_o,

  //Memory SRAM sideband signals
  input  axe_tcl_sram_pkg::impl_inp_t sram_impl_b_i,
  output axe_tcl_sram_pkg::impl_oup_t sram_impl_b_o,
  input  axe_tcl_sram_pkg::impl_inp_t sram_impl_c_i,
  output axe_tcl_sram_pkg::impl_oup_t sram_impl_c_o
);

  // Naming convention for uArch stage signals:
  //   Stage aa     |     Stage bb
  //              +---+
  //    aa_<*> ==>|   |==> aa_bb_<*>
  //    aa_vld -->|   |--> aa_bb_vld
  // aa_bb_rdy <--|   |<-- bb_rdy
  //              +-^-+
  //                |
  // - Signals `aa_bb_*` are driven by the pipe between stages
  // - Signals `aa_*` are driven by stage aa
  // - Signals `bb_*` are driven by stage bb

  // =======================
  // Instruction Fetch (IF)
  // =======================

  // Handshakes to Instruction Decode
  // =================================
  dpu_instr_t if_instr;
  logic       if_last;
  logic if_vld, if_id_rdy, if_id_handshake;
  // Functionality happens in `dpcmd_gen`, just forward into pipe
  assign if_instr = instruction_data_i;
  assign if_last = instruction_last_i;
  assign if_vld = instruction_valid_i;
  assign instruction_ready_o = if_id_rdy;
  assign if_id_handshake = if_vld & if_id_rdy;

  // ==============================================
  // PIPE: Instruction Fetch -> Instruction Decode
  // ==============================================
  dpu_instr_t if_id_instr;
  logic       if_id_last;
  logic if_id_vld, id_rdy;
  // Pipeline register & handshakes
  assign if_id_rdy = id_rdy | ~if_id_vld;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)        if_id_vld <= 1'b0;
    else if (if_id_rdy) if_id_vld <= if_vld;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      if_id_instr <= '0;
      if_id_last  <= '0;
    end else begin
      if (if_id_handshake) begin
        if_id_instr <= if_instr;
        if_id_last  <= if_last;
      end
    end
  end

  // ========================
  // Instruction Decode (ID)
  // ========================
  // Operating prinicple: The instruction coming from the Instruction Fetch (IF) stage is only
  // consumed (i.e. acknowledged using `id_rdy`) once it has been fully decoded and committed to the
  // Issue (ISS) stage. In particular, this means:
  // - Instructions that are stalled when fetching operands (input stream stall, data dependency)
  //   are only acknowledged once the stalling condition is resolved.
  // - Instructions that consume multiple beats from an input stream (FP stream formats,
  //   RFS-operations) are only acknowledged once the last beat has been consumed.

  // Handshakes to Issue
  // ====================
  operation_e id_operation;
  logic id_masked_op, id_bcast_src1, id_bcast_src2;
  mask_bcast_info_t id_mask_bcast_info;
  src_loc_e id_src_loc[3];
  dst_loc_t id_dst_loc;
  logic id_vld, id_iss_rdy, id_iss_handshake;
  assign id_iss_handshake = id_vld & id_iss_rdy;


  // Decode Instruction
  // ===================
  // - 1. Select operation
  // - 2. Select how operands are interpreted & reorder and/or replace operands if necesary
  // - 3. Interpret actual operands and request data form providers
  // - 4. Raise errors on illegal operand combinations

  // Internal decoding helpers
  dpu_instr_t id_instr;  // instruction after step 2, which could have been modified
  logic rfs_instr, rfs_last;
  logic id_instr_neg;  // NEG is unary but has a native src2 when expanded - masking helper

  // Operand types found in instruction - these determine how the operand fields are interpreted
  typedef enum logic [2:0] {
    SRC_NONE,
    SRC_REGULAR,  // streams, a storage, b storage
    SRC_S_RFS,    // RFS: streams only, this is the main stream operand that RFS applies to
    SRC_CL,
    SRC_CH,
    SRC_D,
    SRC_CONST
  } src_type_e;
  typedef enum logic [2:0] {
    DST_NONE,
    DST_REGULAR,     // streams, a storage, b storage
    DST_S_RFS,       // RFS: streams only + demote TLAST outputs unless source is TLAST
    DST_S_RFS_SRC1,  // RFS: dst is src1 or out-stream w/ demoted TLAST unless src is TLAST
    DST_S_RFS_SRC2,  // RFS: dst is src2 or out-stream w/ demoted TLAST unless src is TLAST
    DST_CL,
    DST_CH,
    DST_D
  } dst_type_e;
  src_type_e id_src_type[3];
  dst_type_e id_dst_type;
  // Vector mode (pw64/pw32) of involved operands. Each operand is annotated with its respective
  // "operand vector mode" which is operation-specific (but usually just follows the `vm` flag from
  // the command). The "global vector mode" from the command defines the I/O packing vector mode.
  // TODO(@stefan.mach): rethink the spec and whether it needs to be like this
  vector_mode_e id_src_vm[3];
  vector_mode_e id_dst_vm;

  // Masking & broadcasting information is stored in src2 for instructions that need it
  assign id_mask_bcast_info = if_id_instr.src2;

  // Some errors, put here for now
  logic id_err_illegal_opcode, id_err_illegal_func;

  // 1. & 2.: Select ops and reorder/replace operands
  // TODO(@stefan.mach): this is fully expanded and has redunant typing, think about reducing this
  always_comb begin : id_decode_instr
    // Default assignments
    id_instr              = if_id_instr;
    id_operation          = MV;
    id_instr_neg          = 1'b0;
    id_masked_op          = 1'b0;
    id_bcast_src1         = 1'b0;
    id_bcast_src2         = 1'b0;
    id_src_type           = '{default: SRC_NONE};
    id_dst_type           = DST_NONE;
    id_src_vm             = '{default: if_id_instr.vm};
    id_dst_vm             = if_id_instr.vm;
    id_err_illegal_opcode = 1'b0;
    id_err_illegal_func   = 1'b0;
    // Select operation & operand handling - decode by opcode first
    unique case (if_id_instr.opcode)
      // Unary operations
      OPC_UNARY: begin
        // By default, assume regular unary input and output location
        id_masked_op   = 1'b1;  // Unary ops are masked
        id_src_type[0] = SRC_REGULAR;
        id_src_type[2] = SRC_CONST;  //  mask_value is passed as src2,
        id_instr.src2  = CONST_ZERO;  //  set 0.0 by default
        id_dst_type    = DST_REGULAR;
        // Unary operations are encoded in the func field
        unique case (if_id_instr.src1)
          // No operands in nop, revert to a MV without operands
          FUNC_NOP: begin
            id_operation   = MV;
            id_masked_op   = 1'b0;
            id_src_type[0] = SRC_NONE;
            id_src_type[2] = SRC_NONE;
            id_dst_type    = DST_NONE;  // not having a dst signifies nop
          end
          // Move to low c storage
          FUNC_MVCL, FUNC_MVCL64: begin
            id_operation = MV;
            id_dst_type  = DST_CL;
            id_src_vm[0] = if_id_instr.src1 == FUNC_MVCL64 ? VM_PW64 : if_id_instr.vm;
            id_src_vm[2] = if_id_instr.src1 == FUNC_MVCL64 ? VM_PW64 : if_id_instr.vm;
            id_dst_vm    = if_id_instr.src1 == FUNC_MVCL64 ? VM_PW64 : if_id_instr.vm;
          end
          // Move to high c storage
          FUNC_MVCH, FUNC_MVCH64: begin
            id_operation = MV;
            id_dst_type  = DST_CH;
            id_src_vm[0] = if_id_instr.src1 == FUNC_MVCH64 ? VM_PW64 : if_id_instr.vm;
            id_src_vm[2] = if_id_instr.src1 == FUNC_MVCH64 ? VM_PW64 : if_id_instr.vm;
            id_dst_vm    = if_id_instr.src1 == FUNC_MVCH64 ? VM_PW64 : if_id_instr.vm;
          end
          // Move from low c storage
          FUNC_CLMV: begin
            id_operation   = MV;
            id_src_type[0] = SRC_CL;
          end
          // Move from high c storage
          FUNC_CHMV: begin
            id_operation   = MV;
            id_src_type[0] = SRC_CH;
          end
          // Move from low c to low c storage
          FUNC_CLMVCL: begin
            id_operation = MV;
            id_src_type[0] = SRC_CL;
            id_dst_type    = DST_CL;
          end
          // Move from low c to high c storage
          FUNC_CLMVCH: begin
            id_operation   = MV;
            id_src_type[0] = SRC_CL;
            id_dst_type    = DST_CH;
          end
          // Move from high c to low c storage
          FUNC_CHMVCL: begin
            id_operation   = MV;
            id_src_type[0] = SRC_CH;
            id_dst_type    = DST_CL;
          end
          // Move from high c to high c storage
          FUNC_CHMVCH: begin
            id_operation   = MV;
            id_src_type[0] = SRC_CH;
            id_dst_type    = DST_CH;
          end
          FUNC_MV64: begin
            id_operation = MV;
            id_src_vm[0] = VM_PW64;
            id_src_vm[2] = VM_PW64;
            id_dst_vm    = VM_PW64;
          end
          FUNC_MVLUT64: begin
            id_operation = MV;
            id_src_vm[0] = VM_PW64;
            id_src_vm[2] = VM_PW64;
            id_dst_vm    = VM_PW64;
            id_dst_type  = DST_D;
          end
          // NEG has a multiplicand of -1.0 on src1 and an addend of -0.0 on src2
          FUNC_NEG: begin
            id_operation   = MADD;
            id_instr_neg   = 1'b1;
            id_src_type[1] = SRC_CONST;
            id_instr.src1  = CONST_NEGONE;
            id_src_type[2] = SRC_CONST;
            id_instr.src2  = CONST_NEGZERO;
          end
          // Special functions are individual functions, regular ops
          FUNC_RECIP: begin
            id_operation  = RECIP;
            id_instr.src2 = CONST_INF;  // mask_value in src2
          end
          FUNC_RSQRT: begin
            id_operation  = RSQRT;
            id_instr.src2 = CONST_INF;  // mask_value in src2
          end
          FUNC_SQRT: id_operation = SQRT;
          FUNC_SIN:  id_operation = SIN;
          FUNC_COS: begin
            id_operation  = COS;
            id_instr.src2 = CONST_ONE;  // mask_value in src2
          end
          FUNC_LOG2: begin
            id_operation  = LOG2;
            id_instr.src2 = CONST_ONE;  // mask_value in src2
          end
          FUNC_EXP2: begin
            id_operation  = EXP2;
            id_instr.src2 = CONST_NEGINF;  // mask_value in src2
          end
          FUNC_MAXR: begin
            id_operation  = MAXR;
            id_instr.src2 = CONST_NEGINF;  // mask_value in src2
          end
          FUNC_MINR: begin
            id_operation  = MINR;
            id_instr.src2 = CONST_INF;  // mask_value in src2
          end
          FUNC_SUMR: id_operation = SUMR;
          // Flag illegal values in the FUNC field
          default:   id_err_illegal_func = 1'b1;
        endcase
      end
      // Masked move
      OPC_MV: begin
        id_operation   = MV;
        id_masked_op   = 1'b1; // Masked moves are masked
        // As regular unary moves, but with mask_value_sel in src1
        id_src_type[0] = SRC_REGULAR;
        id_src_type[2] = SRC_CONST; // mask_value in src2
        id_instr.src2  = if_id_instr.src1; // Move mask_value_sel from src1 to src2
        id_dst_type    = DST_REGULAR;
      end
      // LUTs
      OPC_LUT: begin
        id_operation   = LUT;
        // Regular main input and output location
        id_src_type[0] = SRC_REGULAR;
        // LUT operations are encoded in the func field
        unique case (if_id_instr.src2)
          // LUT from regular storage
          FUNC_LUT: id_src_type[1] = SRC_REGULAR;
          // LUT from dedicated storage
          FUNC_DLUT: id_src_type[1] = SRC_D;
          // LUT from low c storage
          FUNC_CLLUT: id_src_type[1] = SRC_CL;
          // LUT from high c storage
          FUNC_CHLUT: id_src_type[1] = SRC_CH;
          // Flag illegal values in the FUNC field
          default: id_err_illegal_func = 1'b1;
        endcase
        id_src_vm[1] = VM_PW64;  // Always pw64
        id_dst_type  = DST_REGULAR;
        // Check for illegal func field
      end
      // Repeat-for-stream
      OPC_RFS: begin
        // By default, only streams are allowed as main input and output
        id_src_type[0] = SRC_S_RFS;
        id_dst_type    = DST_S_RFS;
        // RFS operations are encoded in the func field
        unique case (if_id_instr.src2)
          // NEG has a multiplicand of -1.0 on src1 and an addend of 0.0 on src2
          FUNC_NEG: begin
            id_operation   = MADD;
            id_instr_neg   = 1'b1;  // not needed but for consistency
            id_src_type[1] = SRC_CONST;
            id_instr.src1  = CONST_NEGONE;
            id_src_type[2] = SRC_CONST;
            id_instr.src2  = CONST_NEGZERO;
          end
          // Unary funcs
          FUNC_RECIP: id_operation = RECIP;
          FUNC_RSQRT: id_operation = RSQRT;
          FUNC_SQRT:  id_operation = SQRT;
          FUNC_SIN:   id_operation = SIN;
          FUNC_COS:   id_operation = COS;
          FUNC_LOG2:  id_operation = LOG2;
          FUNC_EXP2:  id_operation = EXP2;
          FUNC_MAXR:  id_operation = MAXR;
          FUNC_MINR:  id_operation = MINR;
          FUNC_SUMR:  id_operation = SUMR;
          // LUT from regular storage
          FUNC_LUT: begin
            id_operation   = LUT;
            id_src_type[1] = SRC_REGULAR;
            id_src_vm[1]   = VM_PW64;  // Always pw64
          end
          FUNC_DLUT: begin
            id_operation   = LUT;
            id_src_type[1] = SRC_D;
            id_src_vm[1]   = VM_PW64; // Always pw64
          end
          // LUT from low c storage
          FUNC_CLLUT: begin
            id_operation   = LUT;
            id_src_type[1] = SRC_CL;
            id_src_vm[1]   = VM_PW64;  // Always pw64
          end
          // LUT from high c storage
          FUNC_CHLUT: begin
            id_operation   = LUT;
            id_src_type[1] = SRC_CH;
            id_src_vm[1]   = VM_PW64;  // Always pw64
          end
          // Unary move
          FUNC_MV: id_operation = MV;
          // MUL has src1, requires addend of -0.0 on src2, rfs can use src1 as dst
          FUNC_MUL: begin
            id_operation   = MADD;
            id_src_type[1] = SRC_REGULAR;
            id_src_type[2] = SRC_CONST;
            id_instr.src2  = CONST_NEGZERO;
            id_dst_type    = DST_S_RFS_SRC1;
          end
          // ADD has src1, src0 as src2 and multiplicand of 1.0 on src0, rfs can use src1 as dst
          FUNC_ADD: begin
            id_operation   = MADD;
            id_src_type[0] = SRC_CONST;
            id_instr.src0  = CONST_ONE;
            id_src_type[1] = SRC_REGULAR;
            id_src_type[2] = SRC_S_RFS;
            id_instr.src2  = if_id_instr.src0; // Move src0 to src2
            id_dst_type    = DST_S_RFS_SRC1;
          end
          // SUB has src1, src0 as src2 and multiplicand of -1.0 on src0
          FUNC_SUB: begin
            id_operation   = MADD;
            id_src_type[0] = SRC_CONST;
            id_instr.src0  = CONST_NEGONE;
            id_src_type[1] = SRC_REGULAR;
            id_src_type[2] = SRC_S_RFS;
            id_instr.src2  = if_id_instr.src0;  // Move src0 to src2
          end
          // MAX, MIN have src1, rfs can use src1 as dst
          FUNC_MAX: begin
            id_operation   = MAX;
            id_src_type[1] = SRC_REGULAR;
            id_dst_type    = DST_S_RFS_SRC1;
          end
          FUNC_MIN: begin
            id_operation   = MIN;
            id_src_type[1] = SRC_REGULAR;
            id_dst_type    = DST_S_RFS_SRC1;
          end
          // PRELU has src1, requires an addend of -0.0 on src2
          FUNC_PRELU: begin
            id_operation   = MADD;
            id_src_type[1] = SRC_REGULAR;
            id_src_type[2] = SRC_CONST;
            id_instr.src2  = CONST_NEGZERO;
          end
          // CMADD has src1 = src2
          FUNC_CMADD: begin
            id_operation   = MADD;
            id_src_type[1] = SRC_CL;
            id_src_type[2] = SRC_CH;
            id_instr.src2  = if_id_instr.src1;  // Copy src1 to src2 for addressing ch
          end
          // Other func values are illegal
          default: id_err_illegal_func = 1'b1;
        endcase
      end
      // MUL requires addend of -0.0 on src2
      OPC_MUL: begin
        id_operation   = MADD;
        id_bcast_src1  = 1'b1;  // Broadcast binary op
        id_src_type[0] = SRC_REGULAR;
        id_src_type[1] = SRC_REGULAR;
        id_src_type[2] = SRC_CONST;
        id_instr.src2  = CONST_NEGZERO;
        id_dst_type    = DST_REGULAR;
      end
      // ADD has src0 as src2 and multiplicand of 1.0 on src0
      OPC_ADD: begin
        id_operation   = MADD;
        id_bcast_src1  = 1'b1;  // Broadcast binary op
        id_src_type[0] = SRC_CONST;
        id_instr.src0  = CONST_ONE;
        id_src_type[1] = SRC_REGULAR;
        id_src_type[2] = SRC_REGULAR;
        id_instr.src2  = if_id_instr.src0;  // Move src0 to src2
        id_dst_type    = DST_REGULAR;
      end
      // SUB has src0 as src2 and multiplicand of -1.0 on src0
      OPC_SUB: begin
        id_operation   = MADD;
        id_bcast_src1  = 1'b1;  // Broadcast binary op
        id_src_type[0] = SRC_CONST;
        id_instr.src0  = CONST_NEGONE;
        id_src_type[1] = SRC_REGULAR;
        id_src_type[2] = SRC_REGULAR;
        id_instr.src2  = if_id_instr.src0;  // Move src0 to src2
        id_dst_type    = DST_REGULAR;
      end
      // MAX, MIN are regular binary ops
      OPC_MAX: begin
        id_operation   = MAX;
        id_bcast_src1  = 1'b1;  // Broadcast binary op
        id_src_type[0] = SRC_REGULAR;
        id_src_type[1] = SRC_REGULAR;
        id_dst_type    = DST_REGULAR;
      end
      // MAX, MIN are regular binary ops
      OPC_MIN: begin
        id_operation   = MIN;
        id_bcast_src1  = 1'b1;  // Broadcast binary op
        id_src_type[0] = SRC_REGULAR;
        id_src_type[1] = SRC_REGULAR;
        id_dst_type    = DST_REGULAR;
      end
      // PRELU requires an addend of -0.0 on src2
      OPC_PRELU: begin
        id_operation   = PRELU;
        id_bcast_src1  = 1'b1;  // Broadcast binary op
        id_src_type[0] = SRC_REGULAR;
        id_src_type[1] = SRC_REGULAR;
        id_src_type[2] = SRC_CONST;
        id_instr.src2  = CONST_NEGZERO;
        id_dst_type    = DST_REGULAR;
      end
      // CMADD has src1 = src2
      OPC_CMADD: begin
        id_operation   = MADD;
        id_bcast_src1  = 1'b1;  // Broadcast ternary op
        id_bcast_src2  = 1'b1;  // Broadcast ternary op
        id_src_type[0] = SRC_REGULAR;
        id_src_type[1] = SRC_CL;
        id_src_type[2] = SRC_CH;
        id_instr.src2  = if_id_instr.src1;  // Copy src1 to src2 for addressing ch
        id_dst_type    = DST_REGULAR;
      end
      // MADD is ternary
      OPC_MADD: begin
        id_operation   = MADD;
        id_src_type[0] = SRC_REGULAR;
        id_src_type[1] = SRC_REGULAR;
        id_src_type[2] = SRC_REGULAR;
        id_dst_type    = DST_REGULAR;
      end
      // RFS-MADD needs a stream source and can have dst=src2
      OPC_MADD_RFS: begin
        id_operation   = MADD;
        id_src_type[0] = SRC_S_RFS;
        id_src_type[1] = SRC_REGULAR;
        id_src_type[2] = SRC_REGULAR;
        id_dst_type    = DST_S_RFS_SRC2;
      end
      default: begin
        id_err_illegal_opcode = 1'b1;
      end
    endcase
    // Mask size is held in src2 of the original instruction.
    if (id_masked_op) begin
      // Check mask size and adapt instruction if possible
      if (id_mask_bcast_info.mask_size == 0) begin
        // Don't enable masking if the mask size is zero. Don't request the const in that case.
        id_masked_op   = 1'b0; // ASO-MULTI_ASSIGN : This is an overwrite of an edge case. Never touched again in process.
        // NEG actually needs the const
        id_src_type[2] = id_instr_neg ? SRC_CONST : SRC_NONE; // ASO-MULTI_ASSIGN : End of process edge case value override.
      end else if (signed'(id_mask_bcast_info.mask_size) == -signed'(PW_LEN)) begin
        // Don't request the source operand if the entire source will be masked
        // TODO(@stefan.mach): Generalize behavior to pw32
        id_src_type[0] = SRC_NONE; // ASO-MULTI_ASSIGN : End of process edge case value override.
      end
    end
    // Broadcast decision and index is held in src2 of the original instruction.
    if (id_bcast_src1 | id_bcast_src2) begin
      // Only enable broadcasting if it's actually enabled in the broadcast info
      id_bcast_src1 &= id_mask_bcast_info.bcast_info.bcast_enable; // ASO-MULTI_ASSIGN : Additionaly the value is masked after it was set via case statement.
      id_bcast_src2 &= id_mask_bcast_info.bcast_info.bcast_enable; // ASO-MULTI_ASSIGN : Additionaly the value is masked after it was set via case statement.
    end
  end

  // Handshakes to operand sources
  // IAU Stream
  stream_fmt_e id_i0_fmt;
  logic id_i0_fmt_vld, id_i0_fmt_rdy, id_i0_last, id_i0_handshake, id_i0_peek;
  vector_mode_e id_i0_op_vm, id_i0_strm_vm;
  logic id_i0_strm_error, id_i0_strm_stl;
  assign id_i0_handshake = id_i0_fmt_vld & id_i0_fmt_rdy;
  // IFD1 Stream
  stream_fmt_e id_i1_fmt;
  logic id_i1_fmt_vld, id_i1_fmt_rdy, id_i1_last, id_i1_handshake, id_i1_peek;
  vector_mode_e id_i1_op_vm, id_i1_strm_vm;
  logic id_i1_strm_error, id_i1_strm_stl;
  assign id_i1_handshake = id_i1_fmt_vld & id_i1_fmt_rdy;
  // A Storage
  a_addr_t [2:0] id_a_addr;
  logic id_a_addr_vld, id_a_addr_rdy, id_a_handshake;
  assign id_a_handshake = id_a_addr_vld & id_a_addr_rdy;
  // B Storage
  b_addr_t id_b_addr;
  logic id_b_addr_vld, id_b_addr_rdy, id_b_handshake;
  assign id_b_handshake = id_b_addr_vld & id_b_addr_rdy;
  // C Storage - two independent halves sharing address
  c_addr_t id_c_addr;
  logic [1:0] id_c_addr_vld, id_c_addr_rdy, id_c_handshake;
  assign id_c_handshake = id_c_addr_vld & id_c_addr_rdy;
  // D Storage
  d_addr_t id_d_addr;
  logic id_d_addr_vld, id_d_addr_rdy, id_d_handshake;
  assign id_d_handshake = id_d_addr_vld & id_d_addr_rdy;
  // Const Provider - three ports, bound to sources
  const_sel_e [2:0] id_const_sel;
  logic [2:0] id_const_sel_vld, id_const_sel_rdy, id_const_handshake;
  assign id_const_handshake = id_const_sel_vld & id_const_sel_rdy;

  // Sources in use - track 3 source operands separately to do error checking
  logic [2:0]
      id_i0_used,
      id_i1_used,
      id_a_used,
      id_b_used,
      id_cl_used,
      id_ch_used,
      id_d_used,
      id_const_used;
  // Stream that is used as main source for RFS operations
  logic id_rfs_src;
  // Last operation of the instruction stream
  logic id_last_op;
  // Errors
  logic id_err_illegal_loc;
  logic id_err_illegal_addr, id_err_addr_collision, id_err_addr_vm_collision;
  logic id_err_illegal_strm_fmt, id_err_strm_fmt_collision, id_err_strm_vm_collision;

  // Source operands as array to write decode as a loop
  operand_t id_instr_src[3];
  assign id_instr_src = '{id_instr.src0, id_instr.src1, id_instr.src2};
  // Source comparators for source checking
  // NOTE: this is handled in a nested foreach triangle further below
  // logic id_src0_eq_src1, id_src0_eq_src2, id_src1_eq_src2;
  // assign id_src0_eq_src1 = id_instr_src[0] == id_instr_src[1];
  // assign id_src0_eq_src2 = id_instr_src[0] == id_instr_src[2];
  // assign id_src1_eq_src2 = id_instr_src[1] == id_instr_src[2];

  // 3. & 4. Interpret the operands and request them from the providers - operating on id_instr!
  always_comb begin : decode_operands
    // Default assignments
    id_i0_used                = 3'h0;
    id_i1_used                = 3'h0;
    id_a_used                 = 3'h0;
    id_b_used                 = 3'h0;
    id_cl_used                = 3'h0;
    id_ch_used                = 3'h0;
    id_d_used                 = 3'h0;
    id_const_used             = 3'h0;
    id_i0_fmt                 = FMT_INT;
    id_i0_op_vm               = id_instr.vm;
    id_i0_strm_vm             = id_instr.vm;
    id_i0_peek                = 1'b0;
    id_i1_fmt                 = FMT_INT;
    id_i1_op_vm               = id_instr.vm;
    id_i1_strm_vm             = id_instr.vm;
    id_i1_peek                = 1'b0;
    id_a_addr                 = '0;
    id_b_addr                 = '0;
    id_c_addr                 = '0;
    id_d_addr                 = '0;
    id_const_sel              = '{default: CONST_ZERO};
    id_rfs_src                = 1'b0;
    id_src_loc                = '{default: SRC_LOC_NONE};
    id_dst_loc                = '{vm: id_dst_vm, last_op: id_last_op, loc: DST_LOC_NONE, addr: '0};
    id_err_illegal_loc        = 1'b0;
    id_err_illegal_addr       = 1'b0;
    id_err_addr_collision     = 1'b0;
    id_err_addr_vm_collision  = 1'b0;
    id_err_illegal_strm_fmt   = 1'b0;
    id_err_strm_fmt_collision = 1'b0;
    id_err_strm_vm_collision  = 1'b0;  // multiple VMs in one stream operand
    // Interpret the possibly recoded id_instr - all src operands
    foreach (id_src_type[i]) begin
      unique case (id_src_type[i])
        // Handle streams, a, or b storage
        SRC_REGULAR, SRC_S_RFS: begin
          // Decode operands with wildcard matches
          unique case (id_instr_src[i]) inside
            // Stream 0
            S0_PREFIX: begin
              if (id_src_type[i] == SRC_S_RFS) id_rfs_src = 1'b0;
              if (stream_fmt_e'(id_instr_src[i]) inside {
                  FMT_INT, FMT_F16, FMT_F32,
                  FMT_BYP, FMT_INTW, FMT_F24}) begin
                id_i0_used[i] = 1'b1;
                id_i0_fmt     = stream_fmt_e'(id_instr_src[i]);
                // Change VM-dependent formats (INT -> INTW in PW32 mode)
                // NOTE: the spec says to split them in the pre-decode but it's too painful -> respec
                if (id_i0_fmt == FMT_INT && id_instr.vm) id_i0_fmt = FMT_INTW;
                id_i0_op_vm = id_src_vm[i];
                // TODO(@stefan.mach): I really don't like that split of stream vm + data vm... if
                // this happened in the stream unit itself, we wouldn't have to pull that state
                // through the whole dpu for the output stream for example. but currently it's
                // contradictingly handled: some formats imply a vector mode (INTW->pw32) while some
                // formats are implied by the vector mode (INT+pw32 -> INTW, BYP)... so still a mess
                if (id_i0_fmt == FMT_INTW) id_i0_strm_vm = VM_PW32;  // i16/48 only in PW32 layout
                id_i0_peek    = id_instr_src[i].as_str.peek;
                id_src_loc[i] = SRC_LOC_S0;
              end else begin
                id_err_illegal_strm_fmt = 1'b1;
              end
            end
            // Stream 1
            S1_PREFIX: begin
              if (id_src_type[i] == SRC_S_RFS) id_rfs_src = 1'b1;
              if (stream_fmt_e'(id_instr_src[i]) inside {
                  FMT_INT, FMT_F16, FMT_F32,
                  FMT_BYP, FMT_INTW, FMT_F24}) begin
                id_i1_used[i] = 1'b1;
                id_i1_fmt     = stream_fmt_e'(id_instr_src[i]);
                // Change VM-dependent formats (INT -> INTW in PW32 mode)
                if (id_i1_fmt == FMT_INT && id_instr.vm) id_i1_fmt = FMT_INTW;
                id_i1_op_vm = id_src_vm[i];
                if (id_i1_fmt == FMT_INTW) id_i1_strm_vm = VM_PW32;  // i16/48 only in PW32 layout
                id_i1_peek    = id_instr_src[i].as_str.peek;
                id_src_loc[i] = SRC_LOC_S1;
              end else begin
                id_err_illegal_strm_fmt = 1'b1;
              end
            end
            // A storage has 3 read ports
            A_PREFIX: begin
              if (id_src_type[i] == SRC_S_RFS) begin
                id_err_illegal_loc = 1'b1;
              end else if ((id_instr_src[i] ^ A_MASK) < A_DEPTH) begin
                id_a_used[i]  = 1'b1;
                id_a_addr[i]  = a_addr_t'(id_instr_src[i]);
                id_src_loc[i] = SRC_LOC_A;
              end else begin
                id_err_illegal_addr = 1'b1;
              end
            end
            // B storage has a single read port
            BC_PREFIX: begin
              if (id_src_type[i] == SRC_S_RFS) begin
                id_err_illegal_loc = 1'b1;
              end else if ((id_instr_src[i] ^ BC_MASK) < B_DEPTH) begin
                id_b_used[i]  = 1'b1;
                id_b_addr     = b_addr_t'(id_instr_src[i]);
                id_src_loc[i] = SRC_LOC_B;
              end else begin
                id_err_illegal_addr = 1'b1;
              end
            end
            default: begin
              id_err_illegal_loc = 1'b1;
            end
          endcase
        end
        // C storage has two independent sources
        SRC_CL, SRC_CH: begin
          if (id_instr_src[i] inside {BC_PREFIX}) begin
            if ((id_instr_src[i] ^ BC_MASK) < C_DEPTH) begin
              // Only one `c` address currently used as src in instructions
              id_c_addr     = c_addr_t'(id_instr_src[i]);
              id_cl_used[i] = id_src_type[i] == SRC_CL;
              id_ch_used[i] = id_src_type[i] == SRC_CH;
              id_src_loc[i] = id_src_type[i] == SRC_CL ? SRC_LOC_CL : SRC_LOC_CH;
            end else begin
              id_err_illegal_addr = 1'b1;
            end
          end else begin
            id_err_illegal_loc = 1'b1;
          end
        end
        // D storage has a single read port
        SRC_D: begin
          if (id_instr_src[i] inside {D_PREFIX}) begin
            if ((id_instr_src[i] ^ D_MASK) < D_DEPTH) begin
              id_d_addr    = d_addr_t'(id_instr_src[i]);
              id_d_used[i] = 1'b1;
            end else begin
              id_err_illegal_addr = 1'b1;
            end
          end else begin
            id_err_illegal_loc = 1'b1;
          end
        end
        SRC_CONST: begin
          if (id_instr_src[i] inside {
              CONST_ZERO, CONST_ONE, CONST_NEGZERO, CONST_NEGONE,
              CONST_INF, CONST_NEGINF, CONST_PI, CONST_2PI
            }) begin
            id_const_used[i] = 1'b1;
            id_const_sel[i] = const_sel_e'(id_instr_src[i]);
            id_src_loc[i] = SRC_LOC_CONST;
          end else begin
            id_err_illegal_loc = 1'b1;
          end
        end
        // Keep defaults when operand not used
        default: ;
      endcase
    end
    // Interpret the possibly recoded id_instr - dst
    // TODO(@stefan.mach): stream ops with reserved "peek" bit set are not detected illegal
    unique case (id_dst_type)
      DST_REGULAR, DST_S_RFS, DST_S_RFS_SRC1, DST_S_RFS_SRC2: begin
        // Decode operands with wildcard matches
        unique case (id_instr.dst) inside
          // Stream 0
          S0_PREFIX: begin
            if (stream_fmt_e'(id_instr.dst) inside {
                FMT_INT, FMT_F16, FMT_F32,
                FMT_BYP, FMT_INTW, FMT_F24
              }) begin
              id_dst_loc.loc  = DST_LOC_S0;
              id_dst_loc.addr = stream_fmt_e'(id_instr.dst);
              // Change VM-dependent formats (INT -> INTW in PW32 mode)
              if (stream_fmt_e'(id_instr.dst) == FMT_INT && id_instr.vm) id_dst_loc.addr = FMT_INTW;
            end else begin
              id_err_illegal_strm_fmt = 1'b1;
            end
          end
          // Stream 1
          S1_PREFIX: begin
            if (stream_fmt_e'(id_instr.dst) inside {
                FMT_INT, FMT_F16, FMT_F32,
                FMT_BYP, FMT_INTW, FMT_F24
              }) begin
              // Demote RFS ops targeting the output stream unless the last stream data is read
              if (!rfs_last & id_dst_type inside {DST_S_RFS, DST_S_RFS_SRC1, DST_S_RFS_SRC2}) begin
                id_dst_loc.loc  = DST_LOC_S0;
                id_dst_loc.addr = stream_fmt_e'(id_instr.dst);
              end else begin
                id_dst_loc.loc  = DST_LOC_S1;
                id_dst_loc.addr = stream_fmt_e'(id_instr.dst);
              end
              // Change VM-dependent formats (INT -> INTW in PW32 mode)
              if (stream_fmt_e'(id_instr.dst) == FMT_INT && id_instr.vm) id_dst_loc.addr = FMT_INTW;
            end else begin
              id_err_illegal_strm_fmt = 1'b1;
            end
          end
          // A storage
          A_PREFIX: begin
            if (id_dst_type == DST_S_RFS) begin
              id_err_illegal_loc = 1'b1;
            end else if ((id_instr.dst ^ A_MASK) < A_DEPTH) begin
              id_dst_loc.loc  = DST_LOC_A;
              id_dst_loc.addr = a_addr_t'(id_instr.dst);
              // Special operand constraints
              if (id_dst_type == DST_S_RFS_SRC1) begin
                id_err_illegal_addr = id_instr_src[1] != id_instr.dst;
              end else if (id_dst_type == DST_S_RFS_SRC2) begin
                id_err_illegal_addr = id_instr_src[2] != id_instr.dst;
              end
            end else begin
              id_err_illegal_addr = 1'b1;
            end
          end
          // B storage
          BC_PREFIX: begin
            if (id_dst_type == DST_S_RFS) begin
              id_err_illegal_loc = 1'b1;
            end else if ((id_instr.dst ^ BC_MASK) < B_DEPTH) begin
              id_dst_loc.loc  = DST_LOC_B;
              id_dst_loc.addr = b_addr_t'(id_instr.dst);
              // Special operand constraints
              if (id_dst_type == DST_S_RFS_SRC1) begin
                id_err_illegal_addr = id_instr_src[1] != id_instr.dst;
              end else if (id_dst_type == DST_S_RFS_SRC2) begin
                id_err_illegal_addr = id_instr_src[2] != id_instr.dst;
              end
            end else begin
              id_err_illegal_addr = 1'b1;
            end
          end
          default: begin
            id_err_illegal_loc = 1'b1;
          end
        endcase
      end
      DST_CL, DST_CH: begin
        if (id_instr.dst inside {BC_PREFIX}) begin
          if ((id_instr.dst ^ BC_MASK) < C_DEPTH) begin
            id_dst_loc.loc  = id_dst_type == DST_CL ? DST_LOC_CL : DST_LOC_CH;
            id_dst_loc.addr = c_addr_t'(id_instr.dst);
          end else begin
            id_err_illegal_addr = 1'b1;
          end
        end else begin
          id_err_illegal_loc = 1'b1;
        end
      end
      DST_D: begin
        if (id_instr.dst inside {D_PREFIX}) begin
          if ((id_instr.dst ^ D_MASK) < D_DEPTH) begin
            id_dst_loc.loc  = DST_LOC_D;
            id_dst_loc.addr = d_addr_t'(id_instr.dst);
          end else begin
            id_err_illegal_addr = 1'b1;
          end
        end else begin
          id_err_illegal_loc = 1'b1;
        end
      end
      // DST_NONE is considered without destination -> no-op
      default: ;
    endcase

    // Now that all operands are decoded, catch the errors concerning illegal combinations:
    // - Multiple operands on the same stream with different formats
    // - Multiple operands on the same stream with different operand vector mode (pw32/64)
    // id_err_strm_fmt_collision |= id_i0_used[0] && id_i0_used[1] && !id_src0_eq_src1;
    // id_err_strm_fmt_collision |= id_i0_used[0] && id_i0_used[2] && !id_src0_eq_src2;
    // id_err_strm_fmt_collision |= id_i0_used[1] && id_i0_used[2] && !id_src1_eq_src2;
    // id_err_strm_fmt_collision |= id_i1_used[0] && id_i1_used[1] && !id_src0_eq_src1;
    // id_err_strm_fmt_collision |= id_i1_used[0] && id_i1_used[2] && !id_src0_eq_src2;
    // id_err_strm_fmt_collision |= id_i1_used[1] && id_i1_used[2] && !id_src1_eq_src2;
    // TODO(@stefan.mach): peek+pop in the same instruction is currently an error!
    // TODO(@stefan.mach): implement error checks for peek followed by change of format!
    foreach (id_i0_used[i]) begin
      foreach (id_i0_used[j]) begin
        if (j > i && (id_i0_used[i] && id_i0_used[j] || id_i1_used[i] && id_i1_used[j])) begin
          id_err_strm_fmt_collision |= id_instr_src[i] != id_instr_src[j];
          id_err_strm_vm_collision |= id_src_vm[i] != id_src_vm[j];
        end
      end
    end
    // - Multiple b operands with different addresses
    // - Multiple b operands with different operand vector mode (pw32/64)
    // NOTE: Add c storage checks in case instructions with multiple `c` src fields are added
    // id_err_addr_collision |= id_b_used[0] && id_b_used[1] && !id_src0_eq_src1;
    // id_err_addr_collision |= id_b_used[0] && id_b_used[2] && !id_src0_eq_src2;
    // id_err_addr_collision |= id_b_used[1] && id_b_used[2] && !id_src1_eq_src2;
    foreach (id_b_used[i]) begin
      foreach (id_b_used[j]) begin
        if (j > i && (id_b_used[i] && id_b_used[j])) begin
          id_err_addr_collision |= (id_instr_src[i] != id_instr_src[j]) || (id_src_vm[i] != id_src_vm[j]);
          id_err_addr_vm_collision |= id_src_vm[i] != id_src_vm[j];
        end
      end
    end
  end

  // Instruction control
  logic id_illegal_instr, id_instr_valid, cfg_drop_illegal;
  logic id_stall_waw;

  // The instruction is illegal if any decoding error occured
  assign id_illegal_instr = id_err_illegal_opcode | id_err_illegal_func | id_err_illegal_loc |
                            id_err_illegal_addr | id_err_addr_collision | id_err_addr_vm_collision |
                            id_err_illegal_strm_fmt | id_err_strm_fmt_collision |
                            id_err_strm_vm_collision;

  // Detect instructions with special control flow
  assign rfs_instr = id_instr.opcode == OPC_RFS;
  assign cfg_drop_illegal = dp_ctrl_i.drop_illegal_instr.q;

  // Instruction will go to dispatch if it's present.
  // Illegal instructions are executed as well unless configured to be dropped.
  // TODO(@stefan.mach): ensure dropping has no side-effects!
  assign id_instr_valid = if_id_vld & ~(cfg_drop_illegal & id_illegal_instr);

  // Operation dispatch
  // ===================
  // The dispatch logic will request all operands necessary for the operation and stall if they are
  // not provided. The stall will continue until all operands are successfully requested. Once all
  // operands have been requested, dispatch to the issue stage is enabled which can also stall.

  // FSM state of the dispatcher
  typedef enum logic {
    DISP_DECODE,
    DISP_STALL
  } id_disp_state_e;
  id_disp_state_e id_disp_state;
  // Dispatch of current operation sources completed
  logic id_sources_dispatched;

  // Track which operands have already been successfully requested.
  logic i0_disp_q, i0_disp_d;
  logic i1_disp_q, i1_disp_d;
  logic i0_last_q, i0_last_d;
  logic i1_last_q, i1_last_d;
  logic a_disp_q, a_disp_d;
  logic b_disp_q, b_disp_d;
  logic [1:0] c_disp_q, c_disp_d;  // two independent requests
  logic d_disp_q, d_disp_d;
  logic [2:0] const_disp_q, const_disp_d;  // three read ports
  // Track handshakes using sticky flops
  assign i0_disp_d    = id_i0_handshake | i0_disp_q;
  assign i1_disp_d    = id_i1_handshake | i1_disp_q;
  assign i0_last_d    = (id_i0_handshake & id_i0_last) | i0_last_q;
  assign i1_last_d    = (id_i1_handshake & id_i1_last) | i1_last_q;
  assign a_disp_d     = id_a_handshake | a_disp_q;
  assign b_disp_d     = id_b_handshake | b_disp_q;
  assign c_disp_d     = id_c_handshake | c_disp_q;
  assign d_disp_d     = id_d_handshake | d_disp_q;
  assign const_disp_d = id_const_handshake | const_disp_q;
  // Flops will track handshakes while a valid instruction is waiting. They will be cleared every
  // time an instruction is dispatched to the ISS stage to start from a clean slate.
`ifndef NO_SYNOPSYS_FF
  /* synopsys sync_set_reset "id_iss_handshake" */
`endif
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      i0_disp_q    <= 1'b0;
      i1_disp_q    <= 1'b0;
      i0_last_q    <= 1'b0;
      i1_last_q    <= 1'b0;
      a_disp_q     <= 1'b0;
      b_disp_q     <= 1'b0;
      c_disp_q     <= 2'h0;
      d_disp_q     <= 1'b0;
      const_disp_q <= 3'h0;
    end else begin
      if (id_iss_handshake) begin
        i0_disp_q    <= 1'b0;
        i1_disp_q    <= 1'b0;
        i0_last_q    <= 1'b0;
        i1_last_q    <= 1'b0;
        a_disp_q     <= 1'b0;
        b_disp_q     <= 1'b0;
        c_disp_q     <= 2'h0;
        d_disp_q     <= 1'b0;
        const_disp_q <= 3'h0;
      end else if (id_instr_valid) begin
        i0_disp_q    <= i0_disp_d;
        i1_disp_q    <= i1_disp_d;
        i0_last_q    <= i0_last_d;
        i1_last_q    <= i1_last_d;
        a_disp_q     <= a_disp_d;
        b_disp_q     <= b_disp_d;
        c_disp_q     <= c_disp_d;
        d_disp_q     <= d_disp_d;
        const_disp_q <= const_disp_d;
      end
    end
  end

  // Request source operands that are used, already dispatched requests are silenced
  assign id_i0_fmt_vld    = id_instr_valid & |id_i0_used & ~i0_disp_q;
  assign id_i1_fmt_vld    = id_instr_valid & |id_i1_used & ~i1_disp_q;
  assign id_a_addr_vld    = id_instr_valid & |id_a_used & ~a_disp_q;
  assign id_b_addr_vld    = id_instr_valid & |id_b_used & ~b_disp_q;
  assign id_c_addr_vld[0] = id_instr_valid & |id_cl_used & ~c_disp_q[0];
  assign id_c_addr_vld[1] = id_instr_valid & |id_ch_used & ~c_disp_q[1];
  assign id_d_addr_vld    = id_instr_valid & |id_d_used & ~d_disp_q;
  assign id_const_sel_vld = {3{id_instr_valid}} & id_const_used & ~const_disp_q;
  // The instruction is dispatched to the source providers once all necessary handshakes are seen
  assign id_sources_dispatched = id_instr_valid
      & (id_i0_handshake      | i0_disp_q    | ~(|id_i0_used))
      & (id_i1_handshake      | i1_disp_q    | ~(|id_i1_used))
      & (id_a_handshake       | a_disp_q     | ~(|id_a_used))
      & (id_b_handshake       | b_disp_q     | ~(|id_b_used))
      & (id_c_handshake[0]    | c_disp_q[0]  | ~(|id_cl_used))
      & (id_c_handshake[1]    | c_disp_q[1]  | ~(|id_ch_used))
      & (id_d_handshake       | d_disp_q     | ~(|id_d_used))
      & (&(id_const_handshake | const_disp_q | ~id_const_used));

  // The FSM isn't really needed but maybe nice just for checking the waves...
  assign id_disp_state = (id_sources_dispatched | ~id_instr_valid) ? DISP_DECODE : DISP_STALL;

  // The operation is dispatched to the ISS stage once all the srources have been dispatched and no
  // WAW hazard is possible
  assign id_vld = id_sources_dispatched & ~id_stall_waw;

  // TODO(@stefan.mach): rethink rfs control
  // The last rfs operation is being dispatched
  assign rfs_last = rfs_instr & (id_rfs_src ? (id_i1_last | i1_last_q) : (id_i0_last | i0_last_q));

  // The last operation is being dispatched
  assign id_last_op = id_instr_valid & if_id_last & (~rfs_instr | rfs_last);

  // Signal ready from downstream - either on completed instruction or if dropping an illegal one
  assign id_rdy = id_iss_handshake & (~rfs_instr | rfs_last) | (cfg_drop_illegal & id_illegal_instr);

  // ==================================
  // PIPE: Instruction Decode -> Issue
  // ==================================
  operation_e id_iss_operation;
  logic id_iss_masked_op, id_iss_bcast_src1, id_iss_bcast_src2;
  mask_bcast_info_t id_iss_mask_bcast_info;
  src_loc_e id_iss_src_loc[3];
  dst_loc_t id_iss_dst_loc;
  logic id_iss_vld, iss_rdy;
  // Pipeline register & handshakes
  assign id_iss_rdy = iss_rdy | ~id_iss_vld;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)         id_iss_vld <= 1'b0;
    else if (id_iss_rdy) id_iss_vld <= id_vld;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      id_iss_operation       <= MV;
      id_iss_masked_op       <= '0;
      id_iss_bcast_src1      <= '0;
      id_iss_bcast_src2      <= '0;
      id_iss_mask_bcast_info <= '0;
      id_iss_src_loc         <= '{default: SRC_LOC_NONE};
      id_iss_dst_loc         <= '0;
    end else begin
      if (id_iss_handshake) begin
        id_iss_operation  <= id_operation;
        id_iss_masked_op  <= id_masked_op;
        id_iss_bcast_src1 <= id_bcast_src1;
        id_iss_bcast_src2 <= id_bcast_src2;
        if (id_masked_op | id_bcast_src1 | id_bcast_src2) begin
          id_iss_mask_bcast_info <= id_mask_bcast_info;
        end
        id_iss_src_loc <= id_src_loc;
        id_iss_dst_loc <= id_dst_loc;
      end
    end
  end

  // ============
  // Issue (ISS)
  // ============
  // This stage takes the source operands as indicated by `src_loc` and applies them to the source
  // registers (src0-2) for the execution stage according to the operation found in `operation`.

  // Handshakes to operand sources
  // ==============================
  // IAU stream
  pw_dpu_fp_t iss_i0_data;
  logic iss_i0_vld, iss_i0_rdy;

  // IFD1 stream
  pw_dpu_fp_t iss_i1_data;
  logic iss_i1_vld, iss_i1_rdy;

  // A storage
  pw_dpu_fp_t [2:0] iss_a_data;
  logic iss_a_vld, iss_a_rdy;

  // B storage
  pw_dpu_fp_t iss_b_data;
  logic iss_b_vld, iss_b_rdy;

  // C storage - two independent halves
  pw_dpu_fp_t [1:0] iss_c_data;
  logic [1:0] iss_c_vld, iss_c_rdy;

  // D storage
  pw_dpu_fp_t iss_d_data;
  logic iss_d_vld, iss_d_rdy;

  // Constants - three read ports
  pw_dpu_fp_t [2:0] iss_const_data;
  logic [2:0] iss_const_vld, iss_const_rdy;

  // Stalling Mechanisms
  // ====================
  // Issue stalled due to ordering of in-flight oputput stream ops
  logic iss_stall_ostr_order;

  // Handshakes to Execution
  // ========================
  operation_e iss_operation;
  pw_dpu_fp_t iss_src[3];
  dst_loc_t iss_dst_loc;
  logic iss_vld, iss_exe_rdy, iss_exe_handshake;
  assign iss_exe_handshake = iss_vld & iss_exe_rdy;
  // Operation & dst are fed through
  assign iss_operation = id_iss_operation;
  assign iss_dst_loc = id_iss_dst_loc;

  // Forwarding to Write Back
  // =========================
  pw_dpu_fp_t iss_fwd_res;
  dst_loc_t   iss_fwd_dst_loc;
  logic iss_wb_vld, iss_wb_rdy, iss_wb_handshake;
  assign iss_wb_handshake = iss_wb_vld & iss_wb_rdy;

  // Srouce Opreand Mapping
  // =======================
  logic iss_i0_used, iss_i1_used, iss_a_used, iss_b_used, iss_cl_used, iss_ch_used, iss_d_used;
  logic [2:0] iss_const_used;  // 3 read ports
  pw_dpu_fp_t iss_src_raw[3];

  // Select the sources
  always_comb begin : iss_source_muxes
    // Default assignments
    iss_src_raw    = '{default: '0};
    iss_i0_used    = 1'b0;
    iss_i1_used    = 1'b0;
    iss_a_used     = 1'b0;
    iss_b_used     = 1'b0;
    iss_cl_used    = 1'b0;
    iss_ch_used    = 1'b0;
    iss_d_used     = 1'b0;
    iss_const_used = 3'h0;
    // Treat all sources the same
    foreach (id_iss_src_loc[i]) begin
      unique case (id_iss_src_loc[i])
        SRC_LOC_S0: begin
          iss_src_raw[i] = iss_i0_data;
          iss_i0_used = 1'b1;
        end
        SRC_LOC_S1: begin
          iss_src_raw[i] = iss_i1_data;
          iss_i1_used = 1'b1;
        end
        SRC_LOC_A: begin
          iss_src_raw[i] = iss_a_data[i];  // 3 read ports
          iss_a_used = 1'b1;
        end
        SRC_LOC_B: begin
          iss_src_raw[i] = iss_b_data;
          iss_b_used = 1'b1;
        end
        SRC_LOC_CL: begin
          iss_src_raw[i] = iss_c_data[0];
          iss_cl_used = 1'b1;
        end
        SRC_LOC_CH: begin
          iss_src_raw[i] = iss_c_data[1];
          iss_ch_used = 1'b1;
        end
        SRC_LOC_D: begin
          iss_src_raw[i] = iss_d_data;
          iss_d_used = 1'b1;
        end
        SRC_LOC_CONST: begin
          iss_src_raw[i] = iss_const_data[i];  // 3 read ports
          iss_const_used[i] = 1'b1;
        end
        // SRC_LOC_NONE does nothing - nop
        default: ;
      endcase
    end
  end

  // ISS Data Modifications
  // =======================
  // Extract masking helpers
  operand_t iss_mask_size;
  assign    iss_mask_size = id_iss_mask_bcast_info.mask_size;

  // SRC0:
  //  - Masking of src0 (europa#185)
  pw_dpu_fp_t iss_src0_mod;
  always_comb begin : iss_src_0_masking
    // By default, feed through sources
    iss_src0_mod = iss_src_raw[0];
    // Masking affects src0 if enabled by using src2 as masked values
    if (id_iss_masked_op) begin
      // NOTE: Compute the mask once and mux accordingly if the synth tool doesn't play nice
      foreach (iss_src0_mod[i]) begin
        if (i < signed'(iss_mask_size) || i >= signed'(iss_mask_size) + signed'(PW_LEN)) begin
          iss_src0_mod[i] = iss_src_raw[2][i];  // raw src2 as mask to avoid long bcast->mask chain
        end
      end
    end
    iss_src[0] = iss_src0_mod;
  end

  // SRC1:
  //  - No Modification
  always_comb begin : iss_src_1_no_mod
    iss_src[1] = iss_src_raw[1];
  end

  // SRC2:
  // - No Modification
  always_comb begin : iss_src_2_no_mod
    iss_src[2] = iss_src_raw[2];
  end

  // Issue Operations
  // =================
  // Fowrarding path is activated for move operations - their result is src0, known in ISS
  logic iss_fwd_to_wb;
  assign iss_fwd_to_wb = iss_operation == MV;
  // Forwarding path signals are silenced if unused, as there is no flop to stop the switching
  assign iss_fwd_res = iss_fwd_to_wb ? iss_src[0] : '0;
  assign iss_fwd_dst_loc = iss_fwd_to_wb ? iss_dst_loc : '0;

  // The issue side is valid if all the required operands are valid
  logic iss_all_ops_valid;
  assign iss_all_ops_valid = id_iss_vld
      & (iss_i0_vld      | ~iss_i0_used)
      & (iss_i1_vld      | ~iss_i1_used)
      & (iss_a_vld       | ~iss_a_used)
      & (iss_b_vld       | ~iss_b_used)
      & (iss_c_vld[0]    | ~iss_cl_used)
      & (iss_c_vld[1]    | ~iss_ch_used)
      & (iss_d_vld       | ~iss_d_used)
      & (&(iss_const_vld | ~iss_const_used));

  // Path towards EXE is valid if oprands are valid, we're not stalled, and we're not forwarding
  assign iss_vld = iss_all_ops_valid & ~iss_stall_ostr_order & ~iss_fwd_to_wb;
  // Forwarding path is valid if oprands are valid, we're not stalled, and we're forwarding
  // TODO(@stefan.mach): check whether all stall conditions apply to both paths!
  assign iss_wb_vld = iss_all_ops_valid & ~iss_stall_ostr_order & iss_fwd_to_wb;

  // Signal ready from either downstream path
  assign iss_rdy = iss_exe_handshake | iss_wb_handshake;
  // Consume sources upon issue
  assign iss_i0_rdy    = iss_rdy & iss_i0_used;
  assign iss_i1_rdy    = iss_rdy & iss_i1_used;
  assign iss_a_rdy     = iss_rdy & iss_a_used;
  assign iss_b_rdy     = iss_rdy & iss_b_used;
  assign iss_c_rdy[0]  = iss_rdy & iss_cl_used;
  assign iss_c_rdy[1]  = iss_rdy & iss_ch_used;
  assign iss_d_rdy     = iss_rdy & iss_d_used;
  assign iss_const_rdy = {3{iss_rdy}} & iss_const_used;


  // =========================
  // PIPE: Issue -> Execution
  // =========================
  // Extract broadcast helpers
  logic [5:0] iss_bcast_index;
  always_comb iss_bcast_index = id_iss_mask_bcast_info.bcast_info.bcast_index;

  operation_e iss_exe_operation;
  pw_dpu_fp_t iss_exe_src[3];

  dpu_fp_t    iss_exe_bcast_src1;
  dpu_fp_t    iss_exe_bcast_src2;
  logic       iss_exe_use_bcast_src1;
  logic       iss_exe_use_bcast_src2;

  dst_loc_t iss_exe_dst_loc;
  logic iss_exe_vld, exe_rdy;
  // Pipeline register & handshakes
  assign iss_exe_rdy = exe_rdy | ~iss_exe_vld;

  always_ff @(posedge clk_i or negedge rst_ni) begin : iss_exe_pipe_vld
    if (!rst_ni)          iss_exe_vld <= 1'b0;
    else if (iss_exe_rdy) iss_exe_vld <= iss_vld;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : iss_exe_pipe_data
    if (!rst_ni) begin
      iss_exe_operation      <= MV;
      iss_exe_dst_loc        <= dst_loc_t'(0);
      iss_exe_src            <= '{default: '0};
      iss_exe_bcast_src1     <= dpu_fp_t'(0);
      iss_exe_bcast_src2     <= dpu_fp_t'(0);
      iss_exe_use_bcast_src1 <= 1'b0;
      iss_exe_use_bcast_src2 <= 1'b0;
    end else begin
      if (iss_exe_handshake) begin
        iss_exe_operation <= iss_operation;
        iss_exe_dst_loc   <= iss_dst_loc;
        // Operands are gated if unused to save switching power
        if ( id_iss_src_loc[0] != SRC_LOC_NONE)                          iss_exe_src[0] <= iss_src[0];
        if ((id_iss_src_loc[1] != SRC_LOC_NONE) && (!id_iss_bcast_src1)) iss_exe_src[1] <= iss_src[1];
        if ((id_iss_src_loc[2] != SRC_LOC_NONE) && (!id_iss_bcast_src2)) iss_exe_src[2] <= iss_src[2];

        // Broadcast handling
        if (id_iss_bcast_src1) iss_exe_bcast_src1 <= iss_src[1][iss_bcast_index];
        if (id_iss_bcast_src2) iss_exe_bcast_src2 <= iss_src[2][iss_bcast_index];
        iss_exe_use_bcast_src1 <= id_iss_bcast_src1;
        iss_exe_use_bcast_src2 <= id_iss_bcast_src2;
      end
    end
  end

  ///////////////////////////////
  // Broadcasting (europa#185) //
  ///////////////////////////////
  pw_dpu_fp_t exe_src[3];

  always_comb exe_src[0] = iss_exe_src[0];

  always_comb begin : exe_src_1_bcast
    for (int pword_index = 0; pword_index < PW_LEN; pword_index++) begin
      exe_src[1][pword_index] = iss_exe_use_bcast_src1 ? iss_exe_bcast_src1 : iss_exe_src[1][pword_index];
    end
  end

  always_comb begin : exe_src_2_bcast
    for (int pword_index = 0; pword_index < PW_LEN; pword_index++) begin
      exe_src[2][pword_index] = iss_exe_use_bcast_src2 ? iss_exe_bcast_src2 : iss_exe_src[2][pword_index];
    end
  end

  // ================
  // Execution (EXE)
  // ================
  // This stage feeds the source data into the datapath blocks according according to the operation
  // found in `operation`.

  // Handshakes at execution blocks
  // ===============================
  // Pack MADD inputs for arbitration
  typedef struct packed {
    dst_loc_t   dst;
    pw_dpu_fp_t src2;
    pw_dpu_fp_t src1;
    pw_dpu_fp_t src0;
  } madd_input_t;
  // Pack outputs for arbitration
  typedef struct packed {
    dst_loc_t   dst;
    pw_dpu_fp_t res;
  } result_t;

  // MADD arbiter second input (for MULADD flavors)
  pw_dpu_fp_t madd_arb_in_src0, madd_arb_in_src1, madd_arb_in_src2;
  dst_loc_t madd_arb_in_dst;
  madd_input_t madd_arb_in;
  logic madd_arb_in_vld, madd_arb_in_rdy;

  // LUT Block
  pw_dpu_fp_t lut_in_in, lut_in_bso;
  dst_loc_t lut_in_dst;
  logic lut_in_vld, lut_in_rdy;
  pw_dpu_fp_t lut_out_src0, lut_out_scl, lut_out_off;
  dst_loc_t lut_out_dst;
  madd_input_t lut_out;
  logic lut_out_vld, lut_out_rdy, lut_busy;

  // MADD Block
  pw_dpu_fp_t madd_in_src0, madd_in_src1, madd_in_src2;
  dst_loc_t madd_in_dst;
  logic madd_in_vld, madd_in_rdy;
  pw_dpu_fp_t madd_out;
  dst_loc_t madd_out_dst;
  result_t madd_res;
  logic madd_out_vld, madd_out_rdy, madd_busy;

  // MAX/MIN Block
  pw_dpu_fp_t max_in_src0, max_in_src1;
  dst_loc_t max_in_dst;
  logic max_in_sel;
  logic max_in_vld, max_in_rdy;
  pw_dpu_fp_t max_out;
  dst_loc_t max_out_dst;
  result_t max_res;
  logic max_out_vld, max_out_rdy, max_busy;

  // MAXR/MINR
  pw_dpu_fp_t maxr_in_src0;
  dst_loc_t maxr_in_dst;
  logic maxr_in_sel;
  logic maxr_in_vld, maxr_in_rdy;
  pw_dpu_fp_t maxr_out;
  dst_loc_t maxr_out_dst;
  result_t maxr_res;
  logic maxr_out_vld, maxr_out_rdy, maxr_busy;

  // SUMR
  pw_dpu_fp_t sumr_in_src0;
  dst_loc_t   sumr_in_dst;
  logic sumr_in_vld, sumr_in_rdy;
  pw_dpu_fp_t sumr_out;
  dst_loc_t sumr_out_dst;
  result_t sumr_res;
  logic sumr_out_vld, sumr_out_rdy, sumr_busy;

  // TODO(tiago,silver): confirm wiring
  pw_dpu_fp_t sfu_in_src0;
  dst_loc_t   sfu_in_dst;
  sfu_func_e  sfu_in_func;
  logic sfu_in_vld, sfu_in_rdy;
  pw_dpu_fp_t sfu_out;
  dst_loc_t sfu_out_dst;
  result_t sfu_res;
  logic sfu_out_vld, sfu_out_rdy, sfu_busy;

  // Handshakes to Write Back
  // =========================
  pw_dpu_fp_t exe_res;
  dst_loc_t   exe_dst_loc;
  logic exe_vld, exe_wb_rdy, exe_wb_handshake;
  assign exe_wb_handshake = exe_vld & exe_wb_rdy;

  // Execution Selection
  // ====================
  // Select the appropriate execution unit
  // NOTE: This would logically be "issue" but some masking here is probably better than pipelined
  // regs for each of these...
  // Furthermore we silence (i.e. tie low) the input data of unselected execution paths to reduce
  // switching power in the general case. Note that adverse patterns can still lead to excessive
  // toggles.
  always_comb begin : exe_sel
    // Default assignments
    madd_arb_in_src0 = '0;
    madd_arb_in_src1 = '0;
    madd_arb_in_src2 = '0;
    madd_arb_in_dst  = '0;
    madd_arb_in_vld  = 1'b0;
    lut_in_in        = '0;
    lut_in_bso       = '0;
    lut_in_dst       = '0;
    lut_in_vld       = 1'b0;
    max_in_src0      = '0;
    max_in_src1      = '0;
    max_in_sel       = 1'b0;
    max_in_dst       = '0;
    max_in_vld       = 1'b0;
    sumr_in_src0     = '0;
    sumr_in_dst      = '0;
    sumr_in_vld      = 1'b0;
    maxr_in_src0     = '0;
    maxr_in_sel      = 1'b0;
    maxr_in_dst      = '0;
    maxr_in_vld      = 1'b0;
    sfu_in_src0      = '0;
    sfu_in_dst       = '0;
    sfu_in_func      = SFU_FUNC_RECIP;
    sfu_in_vld       = 1'b0;
    // Default ready behavior
    exe_rdy          = 1'b1;
    // Handle all ops
    unique case (iss_exe_operation)
      // MADD flavors and PRELU go directly to madd arbiter
      MADD, PRELU: begin
        madd_arb_in_src0 = exe_src[0];
        // PReLU checks the sign bit of src0 to decide whether to use src1 or muxing a 1.0
        foreach (madd_arb_in_src0[i]) begin
          madd_arb_in_src1[i] = (iss_exe_operation == PRELU && !exe_src[0][i].sign) ? DPU_FP_ONE : exe_src[1][i];
        end
        madd_arb_in_src2 = exe_src[2];
        madd_arb_in_dst  = iss_exe_dst_loc;
        madd_arb_in_vld  = iss_exe_vld;
        exe_rdy          = madd_arb_in_rdy;
      end
      LUT: begin
        lut_in_in  = exe_src[0];
        lut_in_bso = exe_src[1];
        lut_in_dst = iss_exe_dst_loc;
        lut_in_vld = iss_exe_vld;
        exe_rdy    = lut_in_rdy;
      end
      MAX, MIN: begin
        max_in_src0 = exe_src[0];
        max_in_src1 = exe_src[1];
        max_in_sel  = iss_exe_operation == MIN;
        max_in_dst  = iss_exe_dst_loc;
        max_in_vld  = iss_exe_vld;
        exe_rdy     = max_in_rdy;
      end
      MAXR, MINR: begin
        maxr_in_src0 = exe_src[0];
        maxr_in_sel  = iss_exe_operation == MINR;
        maxr_in_dst  = iss_exe_dst_loc;
        maxr_in_vld  = iss_exe_vld;
        exe_rdy      = maxr_in_rdy;
      end
      SUMR: begin
        sumr_in_src0 = exe_src[0];
        sumr_in_dst  = iss_exe_dst_loc;
        sumr_in_vld  = iss_exe_vld;
        exe_rdy      = sumr_in_rdy;
      end
      RECIP, RSQRT, SQRT, SIN, COS, LOG2, EXP2: begin
        if (USE_SFU) begin
          sfu_in_src0 = exe_src[0];
          sfu_in_dst  = iss_exe_dst_loc;
          unique case (iss_exe_operation)
            RECIP:   sfu_in_func = SFU_FUNC_RECIP;
            RSQRT:   sfu_in_func = SFU_FUNC_SQRT;
            SQRT:    sfu_in_func = SFU_FUNC_INVSQRT;
            SIN:     sfu_in_func = SFU_FUNC_SIN;
            COS:     sfu_in_func = SFU_FUNC_COS;
            LOG2:    sfu_in_func = SFU_FUNC_LOG2;
            EXP2:    sfu_in_func = SFU_FUNC_EXP2;
            default: ;
          endcase
          sfu_in_vld = iss_exe_vld;
          exe_rdy    = sfu_in_rdy;
        end else begin
          // If SFU not used, replace SFU op by NOP
          sfu_in_src0 = '0;
          sfu_in_dst  = '0;
          sfu_in_func = SFU_FUNC_RECIP;
          sfu_in_vld  = 1'b0;
          exe_rdy     = 1'b1;
        end
      end
      // Ready by default, MV would just get swallowed here
      default: ;
    endcase
  end

  // LUT Block
  // ==========
  dpu_dp_lut i_dpu_dp_lut (
    .clk_i,
    .rst_ni,
    .in_i     (lut_in_in),
    .bso_i    (lut_in_bso),
    .dst_loc_i(lut_in_dst),
    .valid_i  (lut_in_vld),
    .ready_o  (lut_in_rdy),
    .in_o     (lut_out_src0),
    .scale_o  (lut_out_scl),
    .offset_o (lut_out_off),
    .dst_loc_o(lut_out_dst),
    .valid_o  (lut_out_vld),
    .ready_i  (lut_out_rdy),
    .busy_o   (lut_busy)
  );
  assign lut_out = {lut_out_dst, lut_out_off, lut_out_scl, lut_out_src0};

  // MADD Input arbitration
  // ======================
  // Direct input from ISS/EXE pipe for MADD flavors
  assign madd_arb_in = {madd_arb_in_dst, madd_arb_in_src2, madd_arb_in_src1, madd_arb_in_src0};

  // TODO(@stefan.mach): static prio arb
  cc_stream_round_robin_arbiter #(
    .data_t (madd_input_t),
    .N_INP  (2),
    .ARBITER("rr")
  ) u_arb_madd (
    .i_clk      (clk_i),
    .i_rst_n    (rst_ni),
    .inp_data_i ({madd_arb_in, lut_out}),
    .inp_valid_i({madd_arb_in_vld, lut_out_vld}),
    .inp_ready_o({madd_arb_in_rdy, lut_out_rdy}),
    .oup_data_o ({madd_in_dst, madd_in_src2, madd_in_src1, madd_in_src0}),
    .oup_valid_o(madd_in_vld),
    .oup_ready_i(madd_in_rdy)
  );

  // MADD Block
  // ===========
  dpu_dp_madd i_dpu_dp_madd (
    .clk_i,
    .rst_ni,
    .x_i        (madd_in_src0),
    .y_i        (madd_in_src1),
    .z_i        (madd_in_src2),
    .dst_loc_i  (madd_in_dst),
    .valid_i    (madd_in_vld),
    .ready_o    (madd_in_rdy),
    .out_o      (madd_out),
    .dst_loc_o  (madd_out_dst),
    .valid_o    (madd_out_vld),
    .ready_i    (madd_out_rdy),
    .busy_o     (madd_busy),
    .overflow_o (error_irqs_o.err_madd_op_of),
    .underflow_o(error_irqs_o.err_madd_op_uf),
    .inexact_o  (error_irqs_o.err_madd_op_nx),
    .invalid_o  (error_irqs_o.err_madd_op_nv)
  );
  assign madd_res = {madd_out_dst, madd_out};

  // MAX/MIN Block
  // ==============
  // Combinatorial comparators
  dpu_dp_fp_maxmin i_fp_maxmin[PW_LEN-1:0] (
    .in1_i(max_in_src0),
    .in2_i(max_in_src1),
    .sel_i(max_in_sel),
    .out_o(max_out)
  );
  assign max_out_dst = max_in_dst;
  assign max_out_vld = max_in_vld;
  assign max_in_rdy  = max_out_rdy;
  assign max_res     = {max_out_dst, max_out};
  assign max_busy    = max_in_vld | max_out_vld;

  // MAXR/MINR Block
  // ================
  dpu_dp_maxminred i_dpu_dp_maxminred (
    .clk_i,
    .rst_ni,
    .x_i      (maxr_in_src0),
    .maxmin_i (maxr_in_sel),
    .dst_loc_i(maxr_in_dst),
    .valid_i  (maxr_in_vld),
    .ready_o  (maxr_in_rdy),
    .out_o    (maxr_out),
    .dst_loc_o(maxr_out_dst),
    .valid_o  (maxr_out_vld),
    .ready_i  (maxr_out_rdy),
    .busy_o   (maxr_busy)
  );
  assign maxr_res = {maxr_out_dst, maxr_out};

  // SUMR Block
  // ===========
  dpu_dp_sumred i_dpu_dp_sumred (
    .clk_i,
    .rst_ni,
    .x_i       (sumr_in_src0),
    .dst_loc_i (sumr_in_dst),
    .valid_i   (sumr_in_vld),
    .ready_o   (sumr_in_rdy),
    .out_o     (sumr_out),
    .dst_loc_o (sumr_out_dst),
    .valid_o   (sumr_out_vld),
    .ready_i   (sumr_out_rdy),
    .busy_o    (sumr_busy),
    .overflow_o(error_irqs_o.err_sumr_op_of),
    .inexact_o (error_irqs_o.err_sumr_op_nx),
    .invalid_o (error_irqs_o.err_sumr_op_nv)
  );
  assign sumr_res = {sumr_out_dst, sumr_out};

  // SFU Block
  // Special Function Unit
  // ================
  // TODO(tiago,silver): connect interrupts, confirm param and connectivity
  if (USE_SFU) begin : gen_sfu
    dpu_dp_sfu #(
      .FUNC_SEL(7'h7F),  // all functions
      .NUM_REGS(2)       // two pipe regs
    ) u_dpu_dp_sfu (
      .i_clk      (clk_i),
      .i_rst_n    (rst_ni),
      .i_in       (sfu_in_src0),
      .i_sfu_func (sfu_in_func),
      .i_dst_loc  (sfu_in_dst),
      .i_valid    (sfu_in_vld),
      .o_ready    (sfu_in_rdy),
      .o_out      (sfu_out),
      .o_dst_loc  (sfu_out_dst),
      .o_valid    (sfu_out_vld),
      .i_ready    (sfu_out_rdy),
      .o_busy     (sfu_busy),
      .o_overflow (error_irqs_o.err_sfu_op_of),
      .o_underflow(error_irqs_o.err_sfu_op_uf),
      .o_inexact  (error_irqs_o.err_sfu_op_nx),
      .o_invalid  (error_irqs_o.err_sfu_op_nv),
      .o_div_zero (error_irqs_o.err_sfu_op_zr)
    );
    assign sfu_res = {sfu_out_dst, sfu_out};
  end else begin : gen_no_sfu
    assign sfu_in_rdy = '1;
    assign sfu_out = '0;
    assign sfu_out_dst = '0;
    assign sfu_out_vld = '0;
    assign sfu_busy = '0;
  end

  // Output Arbitration
  // ===================
  // TODO(@stefan.mach): static prio arb
  cc_stream_round_robin_arbiter #(
    .data_t (result_t),
    .N_INP  (5),
    .ARBITER("rr")
  ) u_arb_res (
    .i_clk      (clk_i),
    .i_rst_n    (rst_ni),
    .inp_data_i ({sfu_res, sumr_res, maxr_res, max_res, madd_res}),
    .inp_valid_i({sfu_out_vld, sumr_out_vld, maxr_out_vld, max_out_vld, madd_out_vld}),
    .inp_ready_o({sfu_out_rdy, sumr_out_rdy, maxr_out_rdy, max_out_rdy, madd_out_rdy}),
    .oup_data_o ({exe_dst_loc, exe_res}),
    .oup_valid_o(exe_vld),
    .oup_ready_i(exe_wb_rdy)
  );


  // ==============================
  // PIPE: Execution -> Write Back
  // ==============================
  pw_dpu_fp_t exe_wb_res;
  dst_loc_t   exe_wb_dst_loc;
  logic exe_wb_vld, wb_exe_rdy;
  // Pipeline register & handshakes
  assign exe_wb_rdy = wb_exe_rdy | ~exe_wb_vld;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)         exe_wb_vld <= 1'b0;
    else if (exe_wb_rdy) exe_wb_vld <= exe_vld;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      exe_wb_res     <= '0;
      exe_wb_dst_loc <= '0;
    end else begin
      if (exe_wb_handshake) begin
        exe_wb_res     <= exe_res;
        exe_wb_dst_loc <= exe_dst_loc;
      end
    end
  end


  // ================
  // Write Back (WB)
  // ================
  // This stage writes the destination as indicated by `dst_loc`.

  // Handshakes to destinations
  // ===========================
  // ODR Stream, with FIFO
  stream_fmt_e wb_o_fmt, wb_o_fmt_q;
  vector_mode_e wb_o_vm, wb_o_vm_q;
  pw_dpu_fp_t wb_o_wdata, wb_o_wdata_q;
  logic wb_o_vld, wb_o_rdy, wb_o_last, wb_o_handshake;
  logic wb_o_vld_q, wb_o_rdy_q, wb_o_last_q, wb_o_handshake_q;
  logic wb_o_last_op_q;
  assign wb_o_handshake   = wb_o_vld & wb_o_rdy;
  assign wb_o_handshake_q = wb_o_vld_q & wb_o_rdy_q;
  // A Storage
  a_addr_t wb_a_addr;
  pw_dpu_fp_t wb_a_wdata;
  logic wb_a_vld, wb_a_rdy, wb_a_handshake;
  assign wb_a_handshake = wb_a_vld & wb_a_rdy;
  // B Storage
  b_addr_t wb_b_addr;
  pw_dpu_fp_t wb_b_wdata;
  logic wb_b_vld, wb_b_rdy, wb_b_handshake;
  assign wb_b_handshake = wb_b_vld & wb_b_rdy;
  // C Storage
  c_addr_t wb_c_addr;
  pw_dpu_fp_t wb_c_wdata;
  logic wb_c_pair_idx;
  logic wb_c_vld, wb_c_rdy, wb_c_handshake;
  assign wb_c_handshake = wb_c_vld & wb_c_rdy;
  // D Storage
  d_addr_t wb_d_addr;
  pw_dpu_fp_t wb_d_wdata;
  logic wb_d_vld, wb_d_rdy, wb_d_handshake;
  assign wb_d_handshake = wb_d_vld & wb_d_rdy;

  // ISS-WB Arbitration
  // ===================
  result_t exe_wb_result, iss_wb_result;
  pw_dpu_fp_t wb_res;
  dst_loc_t   wb_dst_loc;
  logic wb_arb_vld, wb_arb_rdy;

  // Use a priority arbiter
  assign exe_wb_result = '{dst: exe_wb_dst_loc, res: exe_wb_res};
  assign iss_wb_result = '{dst: iss_fwd_dst_loc, res: iss_fwd_res};
  // TODO(@stefan.mach): this is an RR arb, we should use static prio arb w/ prio on FWD
  cc_stream_round_robin_arbiter #(
    .data_t (result_t),
    .N_INP  (2),
    .ARBITER("rr")
  ) i_iss_wb_arb (
    .i_clk      (clk_i),
    .i_rst_n    (rst_ni),
    .inp_data_i ({exe_wb_result, iss_wb_result}),
    .inp_valid_i({exe_wb_vld, iss_wb_vld}),
    .inp_ready_o({wb_exe_rdy, iss_wb_rdy}),
    .oup_data_o ({wb_dst_loc, wb_res}),
    .oup_valid_o(wb_arb_vld),
    .oup_ready_i(wb_arb_rdy)
  );

  // Destination Decode and Writeback Control
  // =========================================
  logic wb_vld, wb_rdy, wb_handshake;
  logic wb_last_op;
  logic wb_stall_done;  // Writeback stalled due to preceding dp_done not being issued yet
  // WB can be stalled by DP done signaling, only read the arbiter when handshake occurs
  assign wb_vld       = wb_arb_vld & ~wb_stall_done;
  assign wb_handshake = wb_vld & wb_rdy;
  assign wb_arb_rdy   = wb_handshake;
  assign wb_last_op   = wb_dst_loc.last_op;

  // WB state: stall and ok, only used for debug
  typedef enum logic {
    WB_OK,
    WB_STALL
  } wb_state_t;
  wb_state_t wb_state;

  // Destination decode and write with unselected destination muting
  always_comb begin : wb_decode_dest
    // Default assignments
    wb_o_fmt      = FMT_INT;
    wb_o_vm       = wb_dst_loc.vm;
    wb_o_wdata    = '0;
    wb_o_vld      = 1'b0;
    wb_o_last     = 1'b0;
    wb_a_addr     = '0;
    wb_a_wdata    = '0;
    wb_a_vld      = 1'b0;
    wb_b_addr     = '0;
    wb_b_wdata    = '0;
    wb_b_vld      = 1'b0;
    wb_c_addr     = '0;
    wb_c_wdata    = '0;
    wb_c_pair_idx = 1'b0;
    wb_c_vld      = 1'b0;
    wb_d_addr     = '0;
    wb_d_wdata    = '0;
    wb_d_vld      = 1'b0;
    // Default ready behavior!!
    wb_rdy        = 1'b1;
    wb_state      = WB_OK;
    // Select destination from dst field
    unique case (wb_dst_loc.loc)
      // Output stream
      DST_LOC_S0, DST_LOC_S1: begin
        wb_o_fmt   = stream_fmt_e'(wb_dst_loc.addr);
        wb_o_vm    = wb_dst_loc.vm;
        wb_o_wdata = wb_res;
        wb_o_vld   = wb_vld;
        wb_o_last  = wb_dst_loc.loc == DST_LOC_S1;
        // Stalled write
        if (wb_vld & !wb_o_handshake) begin
          wb_rdy   = 1'b0;
          wb_state = WB_STALL;
        end
      end
      DST_LOC_A: begin
        wb_a_addr  = a_addr_t'(wb_dst_loc.addr);
        wb_a_wdata = wb_res;
        wb_a_vld   = wb_vld;
        // Stalled write
        if (wb_vld & !wb_a_handshake) begin
          wb_rdy   = 1'b0;
          wb_state = WB_STALL;
        end
      end
      DST_LOC_B: begin
        wb_b_addr  = b_addr_t'(wb_dst_loc.addr);
        wb_b_wdata = wb_res;
        wb_b_vld   = wb_vld;
        // Stalled write
        if (wb_vld & !wb_b_handshake) begin
          wb_rdy   = 1'b0;
          wb_state = WB_STALL;
        end
      end
      // C storage: explicit pair selection
      DST_LOC_CL, DST_LOC_CH: begin
        wb_c_addr     = c_addr_t'(wb_dst_loc.addr);
        wb_c_pair_idx = wb_dst_loc.loc == DST_LOC_CH;
        wb_c_wdata    = wb_res;
        wb_c_vld      = wb_vld;
        // Stalled write
        if (wb_vld & !wb_c_handshake) begin
          wb_rdy   = 1'b0;
          wb_state = WB_STALL;
        end
      end
      // D storage
      DST_LOC_D: begin
        wb_d_addr  = d_addr_t'(wb_dst_loc.addr);
        wb_d_wdata = wb_res;
        wb_d_vld   = wb_vld;
        // Stalled write
        if (wb_vld & !wb_d_handshake) begin
          wb_rdy   = 1'b0;
          wb_state = WB_STALL;
        end
      end
      // DST_LOC_NONE is a nop and gets swallowed
      default: ;
    endcase
  end


  // ====================
  // Dependency Tracking
  // ====================
  // 1-bit scoreboard per tracked storage location
  logic [A_DEPTH-1:0] a_dirty_q, a_dirty_d;
  logic [B_DEPTH-1:0] b_dirty_q, b_dirty_d;
  logic [C_DEPTH-1:0][1:0] c_dirty_q, c_dirty_d;
  logic [D_DEPTH-1:0] d_dirty_q, d_dirty_d;
  // Dependency tracking process: issued operations claim destination, writes free it
  always_comb begin : scoreboard
    // Default assignments
    a_dirty_d = a_dirty_q;
    b_dirty_d = b_dirty_q;
    c_dirty_d = c_dirty_q;
    d_dirty_d = d_dirty_q;
    // Wait for valid write-back to occur and clear flags, c storage is paired
    if (wb_a_handshake) a_dirty_d[wb_a_addr] = 1'b0;
    if (wb_b_handshake) b_dirty_d[wb_b_addr] = 1'b0;
    if (wb_c_handshake) c_dirty_d[wb_c_addr][wb_c_pair_idx] = 1'b0;
    if (wb_d_handshake) d_dirty_d[wb_d_addr] = 1'b0;
    // Mark destinations of issued instructions dirty
    if (id_iss_handshake) begin
      unique case (id_dst_loc.loc)
        DST_LOC_A:  a_dirty_d[a_addr_t'(id_dst_loc.addr)]    = 1'b1;
        DST_LOC_B:  b_dirty_d[b_addr_t'(id_dst_loc.addr)]    = 1'b1;
        DST_LOC_CL: c_dirty_d[c_addr_t'(id_dst_loc.addr)][0] = 1'b1; // ASO-MULTI_ASSIGN : Set has higher priority than clear (override).
        DST_LOC_CH: c_dirty_d[c_addr_t'(id_dst_loc.addr)][1] = 1'b1; // ASO-MULTI_ASSIGN : Set has higher priority than clear (override).
        DST_LOC_D:  d_dirty_d[d_addr_t'(id_dst_loc.addr)]    = 1'b1;
        default: ;
      endcase
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      a_dirty_q <= '0;
      b_dirty_q <= '0;
      c_dirty_q <= '0;
      d_dirty_q <= '0;
    end else begin
      if (wb_a_handshake || id_iss_handshake) a_dirty_q <= a_dirty_d;
      if (wb_b_handshake || id_iss_handshake) b_dirty_q <= b_dirty_d;
      if (wb_c_handshake || id_iss_handshake) c_dirty_q <= c_dirty_d;
      if (wb_d_handshake || id_iss_handshake) d_dirty_q <= d_dirty_d;
    end
  end

  // Prevent WAW hazards from happening by stalling the dispatch of operations targeting the same
  // destination address as an in-flight operation. This is only for correctness sake and shouldn't
  // happen in reasonable programs, hence it is not performance optimzed.
  // Output stream doesn't stall as WAW ordering is handled separately for performance reasons.
  always_comb begin : waw_stall
    // Don't stall by default
    id_stall_waw = 1'b0;
    // Stall while destination of decoded operation is marked dirty
    unique case (id_dst_loc.loc)
      DST_LOC_A: id_stall_waw = a_dirty_q[a_addr_t'(id_dst_loc.addr)];
      DST_LOC_B: id_stall_waw = b_dirty_q[b_addr_t'(id_dst_loc.addr)];
      DST_LOC_CL: id_stall_waw = c_dirty_q[c_addr_t'(id_dst_loc.addr)][0];
      DST_LOC_CH: id_stall_waw = c_dirty_q[c_addr_t'(id_dst_loc.addr)][1];
      DST_LOC_D: id_stall_waw = d_dirty_q[d_addr_t'(id_dst_loc.addr)];
      default: ;
    endcase
  end


  // ==================================
  // Output Stream Operations Tracking
  // ==================================
  // TODO(@stefan.mach): this counter has no protection and could overlfow!!
  // TODO(@stefan.mach): Broken due to move bypass! iss_exe_handshake -> iss_rdy, two paths!
  // Track currently executed operations that target the output stream
  logic [INFLT_OPS_CTR_W-1:0] num_inflt_ol_ops_q, num_inflt_ol_ops_d;
  // Signal version of the tracking conditions for better debug
  logic iss_dst_ol_issued, exe_dst_ol_retired, enable_inflt_ctr;
  assign iss_dst_ol_issued  = iss_exe_handshake && iss_dst_loc.loc inside {DST_LOC_S0, DST_LOC_S1};
  assign exe_dst_ol_retired = exe_wb_handshake && exe_dst_loc.loc inside {DST_LOC_S0, DST_LOC_S1};
  // Counter to track in-flight ops
  always_comb begin : inflt_outstream_ops
    // Default assingments
    num_inflt_ol_ops_d = num_inflt_ol_ops_q;
    // The counter is incremented for every issued operation and decremented for every retired
    // operation which targets the output stream
    if (iss_dst_ol_issued && !exe_dst_ol_retired) begin
      num_inflt_ol_ops_d = num_inflt_ol_ops_q + 1;
    end else if (exe_dst_ol_retired && !iss_dst_ol_issued) begin
      num_inflt_ol_ops_d = num_inflt_ol_ops_q - 1;
    end
  end
  // The counter register is updated only when needed
  assign enable_inflt_ctr = iss_dst_ol_issued ^ exe_dst_ol_retired;  // or in the proc above?

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)               num_inflt_ol_ops_q <= '0;
    else if (enable_inflt_ctr) num_inflt_ol_ops_q <= num_inflt_ol_ops_d;
  end

  // ==================================
  // Output Stream Operations Ordering
  // ==================================
  // For outstream ordering, store previously issued outstream operation
  operation_e iss_prev_ostr_operation_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni)                iss_prev_ostr_operation_q <= operation_e'(0);
    else if (iss_dst_ol_issued) iss_prev_ostr_operation_q <= iss_operation;
  end

  // Detect if the current operation in ISS has a different execution path from the previous one.
  // NOTE: This would happen in ISS anyways but we moved this logic to EXE to reduce the pipe...
  // TODO(@stefan.mach): check that this still works and/or improve (adapt to changes in arbitation + MV bypass)
  logic iss_diff_ol_dst;
  always_comb begin : iss_diff_ostr_dst
    unique case (iss_operation)
      MV: begin
        iss_diff_ol_dst = ~(iss_prev_ostr_operation_q inside {MV});
      end
      MADD, PRELU: begin
        iss_diff_ol_dst = ~(iss_prev_ostr_operation_q inside {MADD, PRELU});
      end
      LUT: begin
        iss_diff_ol_dst = ~(iss_prev_ostr_operation_q inside {LUT});
      end
      MAX, MIN: begin
        iss_diff_ol_dst = ~(iss_prev_ostr_operation_q inside {MAX, MIN});
      end
      MAXR, MINR: begin
        iss_diff_ol_dst = ~(iss_prev_ostr_operation_q inside {MAXR, MINR});
      end
      SUMR: begin
        iss_diff_ol_dst = ~(iss_prev_ostr_operation_q inside {SUMR});
      end
      RECIP, RSQRT, SQRT, SIN, COS, LOG2, EXP2: begin
        iss_diff_ol_dst = USE_SFU &
            ~(iss_prev_ostr_operation_q inside {RECIP, RSQRT, SQRT, SIN, COS, LOG2, EXP2});
      end
      default: begin
        iss_diff_ol_dst = 1'b0;
      end
    endcase
  end

  // Stall the issue if another execution path will be selected and there are still in-flight
  // opeartions targeting the output stream
  // TODO(@stefan.mach): With static prio arbitration, we could always schedule the longer paths
  always_comb begin : ostr_ordering
    // Default assignment
    iss_stall_ostr_order = 1'b0;
    // Check for ostr ops to-be-issued
    if (id_iss_vld && iss_dst_loc.loc inside {DST_LOC_S0, DST_LOC_S1}) begin
      // Stall for ops that use a different execution path form the presently in-flight ones, as
      // long as they're in-flight. We must construct the decision from the PS of the counter to
      // avoid a combinatorial loop!
      if (iss_diff_ol_dst) begin
        iss_stall_ostr_order = num_inflt_ol_ops_q != 0;
        // WARNING: the following probably causes a comb loop due to exe_ol_retired impacting
        // ISS-WB forwarding arbitrartion decisions!
        // TODO(@stefan.mach): Rework this stall mechanism to be robust and cover the FWD path!
        // unique case (num_inflt_ol_ops_q)
        //   // No in-flight output stream ops -> no stall
        //   0: iss_stall_ostr_order = 1'b0;
        //   // If one instruction is in flight, we stall as long as it's not being retired
        //   1: iss_stall_ostr_order = ~exe_dst_ol_retired;
        //   // Other counter values -> STALL
        //   default: iss_stall_ostr_order = 1'b1;
        // endcase
      end
    end
  end


  // ==================
  // DP Done Signaling
  // ==================
  // The `dp_done_o` signal has to be raised for one clock cycle:
  // - After the last instruction of a command (with `instruction_last_i` set) has been consumed
  //   from the instruction stream
  // - Not before the last output beat of the program is available at the ouput stream
  //
  // When the last instruction of the command reaches write-back, we kick off the DP done signaling
  // process that:
  // 1. Waits for the instruction to retire, either to storage or the output stream
  // 2. Stalls the last instruction of subsequent commands from writing back (for dp_done ordering)
  // 3. Toggles the `dp_done_o` signal

  // Detect last operation being successfully sent to output stream - after FIFO!
  logic wb_last_ostr_op_retired;
  assign wb_last_ostr_op_retired = wb_o_handshake_q && wb_o_last_op_q;

  // The DP Done FSM state
  typedef enum logic {
    DONE_IDLE,
    DONE_WAIT_OSTR
  } done_state_e;
  done_state_e done_state_q, done_state_d;

  // Done FSM
  always_comb begin : done_fsm
    // Default assignments
    wb_stall_done = 1'b0;
    dp_done_o     = 1'b0;
    done_state_d  = done_state_q;
    // FSM
    unique case (done_state_q)
      // Regular operation
      DONE_IDLE: begin
        // Wait for last operation to retire
        if (wb_handshake && wb_last_op) begin
          if (wb_o_vld && !wb_last_ostr_op_retired) begin  // NOTE: can retire here with FallThrough
            // Go to the stalling state if it is an outstanding output-stream operation
            done_state_d = DONE_WAIT_OSTR;
          end else begin
            // Otherwise we can just raise the done signal and stay in this state
            dp_done_o = 1'b1;
          end
        end
        // Otherwise remain in this state
      end
      // Waiting for the last in-flight output stream operation to be written out
      DONE_WAIT_OSTR: begin
        // Stall the WB stage if it's trying to issue another last operation
        wb_stall_done = wb_arb_vld & wb_last_op;
        // If the last operation retires to the output stream, we're done!
        if (wb_last_ostr_op_retired) begin
          // Signal that we're done and go back to accepting new last ops
          dp_done_o    = 1'b1;
          done_state_d = DONE_IDLE;
        end
        // Otherwise remain in this state
      end
      // Illegal states drop into IDLE
      default: begin
        done_state_d = DONE_IDLE;
      end
    endcase
  end

  // The state registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) done_state_q <= DONE_IDLE;
    else         done_state_q <= done_state_d;
  end


  // ==================
  // Storage Locations
  // ==================
  // Input Stream 0 instance
  dpu_dp_in_stream #(
    .WordWidth   (IAU_W),
    .WideIntWidth(PW32_IAU_INT_WIDTH)
  ) i_instream_0 (
    .clk_i,
    .rst_ni,
    .in_data_i       (iau_axis_data_i),
    .in_last_i       (iau_axis_last_i),
    .in_vld_i        (iau_axis_valid_i),
    .in_rdy_o        (iau_axis_ready_o),
    .fmt_i           (id_i0_fmt),
    .stream_vm_i     (id_i0_strm_vm),
    .operand_vm_i    (id_i0_op_vm),
    .peek_i          (id_i0_peek),
    .fmt_vld_i       (id_i0_fmt_vld),
    .fmt_rdy_o       (id_i0_fmt_rdy),
    .last_o          (id_i0_last),
    .illegal_vm_fmt_o(),                        // TODO(@stefan.mach): handle error
    .stream_error_o  (id_i0_strm_error),
    .stream_stalled_o(id_i0_strm_stl),
    .out_data_o      (iss_i0_data),
    .out_vld_o       (iss_i0_vld),
    .out_rdy_i       (iss_i0_rdy),
    .cfg_int_signed_i(dp_ctrl_i.i0_int_sgn.q),
    .overflow_o      (error_irqs_o.err_i0_of),
    .underflow_o     (error_irqs_o.err_i0_uf),
    .inexact_o       (error_irqs_o.err_i0_nx)
  );
  // Handshake detection for IRQs
  logic iau_axis_handshake;
  assign iau_axis_handshake = iau_axis_valid_i & iau_axis_ready_o;

  // Input Stream 1 instance
  dpu_dp_in_stream #(
    .WordWidth(IO_W),
    .WideIntWidth(PW32_IFD1_INT_WIDTH)
  ) i_instream_1 (
    .clk_i,
    .rst_ni,
    .in_data_i       (ifd1_axis_data_i),
    .in_last_i       (ifd1_axis_last_i),
    .in_vld_i        (ifd1_axis_valid_i),
    .in_rdy_o        (ifd1_axis_ready_o),
    .fmt_i           (id_i1_fmt),
    .stream_vm_i     (id_i1_strm_vm),
    .operand_vm_i    (id_i1_op_vm),
    .peek_i          (id_i1_peek),
    .fmt_vld_i       (id_i1_fmt_vld),
    .fmt_rdy_o       (id_i1_fmt_rdy),
    .last_o          (id_i1_last),
    .illegal_vm_fmt_o(),                        // TODO(@stefan.mach): handle error
    .stream_error_o  (id_i1_strm_error),
    .stream_stalled_o(id_i1_strm_stl),
    .out_data_o      (iss_i1_data),
    .out_vld_o       (iss_i1_vld),
    .out_rdy_i       (iss_i1_rdy),
    .cfg_int_signed_i(dp_ctrl_i.i1_int_sgn.q),
    .overflow_o      (error_irqs_o.err_i1_of),
    .underflow_o     (error_irqs_o.err_i1_uf),
    .inexact_o       (error_irqs_o.err_i1_nx)
  );
  // Handshake detection for IRQs
  logic ifd1_axis_handshake;
  assign ifd1_axis_handshake = ifd1_axis_valid_i & ifd1_axis_ready_o;

  // A Storage instance
  dpu_dp_aregs i_dpu_aregs (
    .clk_i,
    .rst_ni,
    .raddr_i     (id_a_addr),
    .raddr_req_i (id_a_used),
    .raddr_vld_i (id_a_addr_vld),
    .raddr_rdy_o (id_a_addr_rdy),
    .rdata_o     (iss_a_data),
    .rdata_vld_o (iss_a_vld),
    .rdata_rdy_i (iss_a_rdy),
    .addr_dirty_i(a_dirty_q),
    .waddr_i     (wb_a_addr),
    .wdata_i     (wb_a_wdata),
    .waddr_vld_i (wb_a_vld),
    .waddr_rdy_o (wb_a_rdy)
  );

  // B Storage instance
  dpu_dp_bstore i_dpu_bstore (
    .clk_i,
    .rst_ni,
    .raddr_i     (id_b_addr),
    .raddr_vld_i (id_b_addr_vld),
    .raddr_rdy_o (id_b_addr_rdy),
    .rdata_o     (iss_b_data),
    .rdata_vld_o (iss_b_vld),
    .rdata_rdy_i (iss_b_rdy),
    .addr_dirty_i(b_dirty_q),
    .waddr_i     (wb_b_addr),
    .wdata_i     (wb_b_wdata),
    .waddr_vld_i (wb_b_vld),
    .waddr_rdy_o (wb_b_rdy),
    .sram_impl_i (sram_impl_b_i),
    .sram_impl_o (sram_impl_b_o)
  );

  // C Storage instance
  dpu_dp_cstore i_dpu_cstore (
    .clk_i,
    .rst_ni,
    .raddr_i     ({id_c_addr, id_c_addr}),  // we only ever read the same addr
    .raddr_vld_i (id_c_addr_vld),
    .raddr_rdy_o (id_c_addr_rdy),
    .rdata_o     (iss_c_data),
    .rdata_vld_o (iss_c_vld),
    .rdata_rdy_i (iss_c_rdy),
    .addr_dirty_i(c_dirty_q),
    .waddr_i     (wb_c_addr),
    .waddr_idx_i (wb_c_pair_idx),
    .wdata_i     (wb_c_wdata),
    .waddr_vld_i (wb_c_vld),
    .waddr_rdy_o (wb_c_rdy),
    .sram_impl_i (sram_impl_c_i),
    .sram_impl_o (sram_impl_c_o)
  );

  // D Storage instance
  dpu_dp_dregs i_dpu_dregs (
    .clk_i,
    .rst_ni,
    .raddr_i     (id_d_addr),
    .raddr_vld_i (id_d_addr_vld),
    .raddr_rdy_o (id_d_addr_rdy),
    .rdata_o     (iss_d_data),
    .rdata_vld_o (iss_d_vld),
    .rdata_rdy_i (iss_d_rdy),
    .addr_dirty_i(d_dirty_q),
    .waddr_i     (wb_d_addr),
    .wdata_i     (wb_d_wdata),
    .waddr_vld_i (wb_d_vld),
    .waddr_rdy_o (wb_d_rdy)
  );

  // Constant provider is just a pipe and a MUX
  dpu_dp_const i_dpu_const (
    .i_clk           (clk_i),
    .i_rst_n         (rst_ni),
    .i_const_sel     (id_const_sel),
    .i_const_sel_vld (id_const_sel_vld),
    .o_const_sel_rdy (id_const_sel_rdy),
    .o_const_data    (iss_const_data),
    .o_const_data_vld(iss_const_vld),
    .i_const_data_rdy(iss_const_rdy)
  );

  // Output-Stream Writeback Buffer (europa#1128)
  typedef struct packed {
    logic         last_op;
    logic         ostr_last;
    stream_fmt_e  ostr_fmt;
    vector_mode_e ostr_vm;
    pw_dpu_fp_t   ostr_wdata;
  } ostr_req_t;

  // Fix for https://git.axelera.ai/prod/europa/-/issues/2270
  ostr_req_t ostr_fifo_inp;
  always_comb
    ostr_fifo_inp = ostr_req_t'{
        last_op:    wb_last_op,
        ostr_last:  wb_o_last,
        ostr_vm:    wb_o_vm,
        ostr_fmt:   wb_o_fmt,
        ostr_wdata: wb_o_wdata
    };

  ostr_req_t ostr_fifo_oup;
  always_comb wb_o_last_op_q = ostr_fifo_oup.last_op;
  always_comb wb_o_last_q    = ostr_fifo_oup.ostr_last;
  always_comb wb_o_fmt_q     = ostr_fifo_oup.ostr_fmt;
  always_comb wb_o_vm_q      = ostr_fifo_oup.ostr_vm;
  always_comb wb_o_wdata_q   = ostr_fifo_oup.ostr_wdata;

  cc_stream_fifo #(
    .Depth(OSTR_FIFO_DEPTH),
    .data_t(ostr_req_t),
    .FallThrough(1'b0)  // TODO(@stefan.mach): Investigate latency improvement by setting 1
  ) i_ostr_fifo (
    .i_clk  (clk_i),
    .i_rst_n(rst_ni),
    .i_flush(1'b0),
    .i_data (ostr_fifo_inp),
    .i_valid(wb_o_vld),
    .o_ready(wb_o_rdy),
    .o_data (ostr_fifo_oup),
    .o_valid(wb_o_vld_q),
    .i_ready(wb_o_rdy_q),
    // TODO(@stefan.mach): busy flags etc.
    .o_usage(),               // ASO-UNUSED_OUTPUT : No propagation of fifo flag
    .o_full (),               // ASO-UNUSED_OUTPUT : No propagation of fifo flag
    .o_empty()                // ASO-UNUSED_OUTPUT : No propagation of fifo flag
  );

  // Output Stream instance
  dpu_dp_out_stream i_outstream (
    .clk_i,
    .rst_ni,
    .in_data_i       (wb_o_wdata_q),
    .out_data_o      (odr_axis_data_o),
    .out_lst_o       (odr_axis_last_o),
    .out_vld_o       (odr_axis_valid_o),
    .out_rdy_i       (odr_axis_ready_i),
    .fmt_i           (wb_o_fmt_q),
    .operand_vm_i    (wb_o_vm_q),
    .fmt_vld_i       (wb_o_vld_q),
    .fmt_last_i      (wb_o_last_q),
    .fmt_rdy_o       (wb_o_rdy_q),
    .cfg_int_signed_i(dp_ctrl_i.out_int_sgn.q),
    .overflow_o      (error_irqs_o.err_o_of),
    .underflow_o     (error_irqs_o.err_o_uf),
    .inexact_o       (error_irqs_o.err_o_nx)
  );
  // Handshake detection for IRQs
  logic odr_axis_handshake;
  assign odr_axis_handshake = odr_axis_valid_o & odr_axis_ready_i;


  // ===========================
  // Error detection and status
  // ===========================
  // Valid program check on streams according to triton#88
  logic in_stream_0_active, act_in_stream_0_q, clr_act_in_stream_0, set_act_in_stream_0;
  logic in_stream_1_active, act_in_stream_1_q, clr_act_in_stream_1, set_act_in_stream_1;
  logic out_stream_active,  act_out_stream_q,  clr_act_out_stream,  set_act_out_stream;
  // Stream activity will be cleared upon completing a transaction with `tlast`
  assign clr_act_in_stream_0 = iau_axis_handshake  & iau_axis_last_i;
  assign clr_act_in_stream_1 = ifd1_axis_handshake & ifd1_axis_last_i;
  assign clr_act_out_stream  = odr_axis_handshake  & odr_axis_last_o;

  // Stream activity will be set upon completing a transaction with no active
  assign set_act_in_stream_0 = iau_axis_handshake  & (~act_in_stream_0_q);
  assign set_act_in_stream_1 = ifd1_axis_handshake & (~act_in_stream_1_q);
  assign set_act_out_stream  = odr_axis_handshake  & (~act_out_stream_q);

  // Any transfer on the streams sets the active flag which can only be cleared with `tlast`
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      act_in_stream_0_q <= 1'b0;
    end else begin
      if (clr_act_in_stream_0)      act_in_stream_0_q <= 1'b0;
      else if (set_act_in_stream_0) act_in_stream_0_q <= 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      act_in_stream_1_q <= 1'b0;
    end else begin
      if (clr_act_in_stream_1)      act_in_stream_1_q <= 1'b0;
      else if (set_act_in_stream_1) act_in_stream_1_q <= 1'b1;
    end
  end

  always_ff @(posedge (clk_i) or negedge (rst_ni)) begin
    if (!rst_ni) begin
      act_out_stream_q <= 1'b0;
    end else begin
      if (clr_act_out_stream)      act_out_stream_q <= 1'b0;
      else if (set_act_out_stream) act_out_stream_q <= 1'b1;
    end
  end
  // The stream is considered active as long as its flag is set and it's not being cleared on the
  // current clock edge
  assign in_stream_0_active = act_in_stream_0_q & ~clr_act_in_stream_0;
  assign in_stream_1_active = act_in_stream_1_q & ~clr_act_in_stream_1;
  assign out_stream_active  = act_out_stream_q  & ~clr_act_out_stream;

  // Invalid program on input stream: Stream active when last operation is dispatched
  assign error_irqs_o.err_act_stream_in0 = id_last_op & id_vld & in_stream_0_active;
  assign error_irqs_o.err_act_stream_in1 = id_last_op & id_vld & in_stream_1_active;
  // Invalid program on output stream: Stream active when last operation committed (`dp_done_o`)
  assign error_irqs_o.err_act_stream_out = dp_done_o & out_stream_active;

  // Stream termination errors: `tlast` inside a multi-beat read
  assign error_irqs_o.err_i0_termination = id_i0_strm_error;
  assign error_irqs_o.err_i1_termination = id_i1_strm_error;

  // Illegal instruction was decoded
  assign error_irqs_o.err_id_illegal_instr = if_id_vld & id_illegal_instr;

  // Status observation
  assign dp_status_o = '{
          in0_vld: '{d: iau_axis_valid_i},
          in0_rdy: '{d: iau_axis_ready_o},
          in0_lst: '{d: iau_axis_last_i},
          in0_stl: '{d: id_i0_strm_stl},
          in1_vld: '{d: ifd1_axis_valid_i},
          in1_rdy: '{d: ifd1_axis_ready_o},
          in1_lst: '{d: ifd1_axis_last_i},
          in1_stl: '{d: id_i1_strm_stl},
          out_vld: '{d: odr_axis_valid_o},
          out_rdy: '{d: odr_axis_ready_i},
          out_lst: '{d: odr_axis_last_o},
          out_stl: '{d: odr_axis_valid_o & ~odr_axis_ready_i},
          dpcmd0_vld: '{d: if_vld},
          dpcmd0_rdy: '{d: if_id_rdy},
          dpcmd0_lst: '{d: if_last},
          dpcmd0_stl: '{d: if_id_rdy & ~if_vld},
          id_current_op: '{d: id_operation},
          id_disp_i_stalled: '{
              d: id_i0_fmt_vld & ~id_i0_fmt_rdy | id_i1_fmt_vld & ~id_i1_fmt_rdy
          },
          id_disp_a_stalled: '{d: id_a_addr_vld & ~id_a_addr_rdy},
          id_disp_b_stalled: '{d: id_b_addr_vld & ~id_b_addr_rdy},
          id_disp_c_stalled: '{d: |(id_c_addr_vld & ~id_c_addr_rdy)},
          id_waw_stalled: '{d: id_stall_waw},
          id_iss_stalled: '{d: id_vld & ~id_iss_rdy},
          iss_i0_stalled: '{d: id_iss_vld & iss_i0_used & ~iss_i0_vld},
          iss_i1_stalled: '{d: id_iss_vld & iss_i1_used & ~iss_i1_vld},
          iss_a_stalled: '{d: id_iss_vld & iss_a_used & ~iss_a_vld},
          iss_b_stalled: '{d: id_iss_vld & iss_b_used & ~iss_b_vld},
          iss_c_stalled: '{d: id_iss_vld & |({iss_ch_used, iss_cl_used} & ~iss_c_vld)},
          iss_order_stalled: '{d: iss_stall_ostr_order},
          iss_done_stalled: '{d: wb_stall_done},  // TODO(@stefan.mach): fix status
          iss_exe_stalled: '{d: iss_vld & ~iss_exe_rdy},
          exe_lut_in_flt: '{d: lut_busy},
          exe_madd_in_flt: '{d: madd_busy},
          exe_max_in_flt: '{d: max_busy},
          exe_maxr_in_flt: '{d: maxr_busy},
          exe_sumr_in_flt: '{d: sumr_busy},
          exe_mv_in_flt: '{d: 1'b0},  // TODO(@stefan.mach): bypass status
          exe_num_in_flt_ostr_ops: '{d: num_inflt_ol_ops_q},
          exe_wb_stalled: '{d: exe_vld & ~exe_wb_rdy},
          wb_o_write: '{d: wb_o_vld},
          wb_a_write: '{d: wb_a_vld},
          wb_b_write: '{d: wb_b_vld},
          wb_c_write: '{d: wb_c_vld}
      };

  //--------------------------------------------------
  // Assertions
  //--------------------------------------------------
  // synopsys translate_off
`ifdef ASSERTIONS_ON
  `include "prim_assert.sv"
  // Active streams at end of computation
  `ASSERT_NEVER(no_act_in_stream_0_at_end, error_irqs_o.err_act_stream_in0, clk_i, !rst_ni)
  `ASSERT_NEVER(no_act_in_stream_1_at_end, error_irqs_o.err_act_stream_in1, clk_i, !rst_ni)
  `ASSERT_NEVER(no_act_out_stream_at_end, error_irqs_o.err_act_stream_out, clk_i, !rst_ni)
  // ISS: Illegal source locations for operands
  // TODO(@stefan.mach): create new assertions that match the changed scheme
  // WB must be writing the output stream if the `dp_done` FSM is stalling for it
  // `ASSERT_IF(done_stall_without_wb_valid_o, wb_o_vld, done_state_q == DONE_WAIT_OSTR, clk_i,
  //            !rst_ni) // NOTE: does not hold anymore, there is a FIFO now
`endif  // ASSERTIONS_ON
  // synopsys translate_on

endmodule
