// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Datapath of IAU for a single Pixel Word
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IAU_PIXEL_DP_SV
`define IAU_PIXEL_DP_SV

module iau_pixel_dp
  import iau_pkg::*;
#(
  parameter int unsigned InWordDw = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE,
  parameter int unsigned OutWordDw = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE,
  parameter int unsigned PWordSize = aic_common_pkg::AIC_PWORD_SIZE,
  parameter int unsigned DW = OutWordDw
) (
  input  wire             i_clk,
  input  wire             i_rst_n,

  // Static signals, to avoid the need for a generate loop and keep the hierarchy intact...
  input  logic            i_pixel_is_msb, // will be used to determine what to do in int16 support mode

  // Global signals
  input  logic            csr_signed_operation_i,
  input  logic            csr_saturated_add_i,
  input  opcode_e         instr_opcode,
  input  logic            vector_mode,
  input  logic      [1:0] instr_src_stream,
  input  logic [1:0][2:0] instr_src_acc_reg,
  input  logic            instr_dst_used,
  input  logic            instr_dst_stream,
  input  logic      [2:0] instr_dst_acc_reg,
  input  logic            exe_instr,
  // Datapath
  input  logic [InWordDw-1:0] i_pixel_data,
  output logic [      DW-1:0] o_pixel_data,
  // alu control:
  input  iau_alu_ctrl_t   i_i16_ctrl, // alu control between lsb and msb element
  output iau_alu_ctrl_t   o_i16_ctrl  // alu control between lsb and msb element
);

  // Sign Extension
  localparam int unsigned ExtendLen = DW - InWordDw;
  localparam int unsigned MsbElDW = IAU_DPU_I16_DW - InWordDw;
  localparam int unsigned MsbExtendLen = DW - MsbElDW;

  // control
  logic        is_i16_lsb, is_i16_msb;

  // Input stream
  logic                 extension_bit;
  logic        [DW-1:0] in_stream_data;
  // Select operands
  logic        [DW-1:0] op_a;
  logic        [DW-1:0] op_b;
  logic signed [  DW:0] op_sgn_ext_a;
  logic signed [  DW:0] op_sgn_ext_b;
  // Accumulation registers
  logic [8-1:0][DW-1:0] acc_reg_d, acc_reg_q;
  // Arithmetic operations
  logic        [DW-1:0] alu_unsigned_sum;
  logic        [DW-1:0] alu_sum;
  logic        [DW-1:0] alu_max;
  logic        [DW-1:0] alu_min;
  logic        [DW-1:0] alu_result;
  // Output buffer
  logic        [DW-1:0] out_buf_data_d, out_buf_data_q;

  /////////////
  // Control:
  always_comb is_i16_lsb = (vector_mode && !i_pixel_is_msb);
  always_comb is_i16_msb = (vector_mode &&  i_pixel_is_msb);

  /////////////
  // Sign extension
  assign extension_bit  = csr_signed_operation_i ? (is_i16_msb ? i_pixel_data[MsbElDW-1] : i_pixel_data[InWordDw-1]) : 1'b0;
  assign in_stream_data = is_i16_msb ? {{MsbExtendLen{extension_bit}}, i_pixel_data[MsbElDW-1:0]} : {{ExtendLen{extension_bit}}, i_pixel_data};

  /////////////
  // Select operands
  assign op_a = instr_src_stream[0] ? in_stream_data : acc_reg_q[instr_src_acc_reg[0]];
  assign op_b = instr_src_stream[1] ? in_stream_data : acc_reg_q[instr_src_acc_reg[1]];

  /////////////
  // Per-source subpath
  logic [7:0] acc_reg_en;
  for(genvar pos = 0; pos < 8; pos++) begin : g_per_src_per_pixel_dp
    always_comb acc_reg_en[pos] = (exe_instr && instr_dst_used && !instr_dst_stream && pos == instr_dst_acc_reg) ? 1'b1 : 1'b0;

    always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_acc_regs
      if(!i_rst_n) begin
        acc_reg_q[pos] <= '0;
      end else begin
        if (acc_reg_en[pos])
          acc_reg_q[pos] <= alu_result;
      end
    end : seq_acc_regs
  end : g_per_src_per_pixel_dp

  // Signed aliases of operands
  always_comb begin
    op_sgn_ext_a = signed'({csr_signed_operation_i & op_a[DW-1], op_a});
    op_sgn_ext_b = signed'({csr_signed_operation_i & op_b[DW-1], op_b});

    // if i16 support, replace bit at MsbElDw:
    if(is_i16_msb) begin
      op_sgn_ext_a[MsbElDW] = csr_signed_operation_i & op_a[MsbElDW-1];
      op_sgn_ext_b[MsbElDW] = csr_signed_operation_i & op_b[MsbElDW-1];
    end
  end
  /////////////
  // Arithmetic operations

  // Add operation
  logic alu_sub;
  logic [DW:0] op_mask; // mask for int16 support, to mask out the upper part in case of lsb element
  logic [DW:0] op_alu_a;
  logic [DW:0] op_alu_b;
  logic op_alu_cin;
  logic op_alu_cout;
  logic alu_sat_pos;
  logic alu_sat_neg;
  logic alu_cout;

  always_comb alu_sub = instr_opcode[IAU_OP_SUB_IDX];
  // subtract in case of compare or subtract A-B => A + (~B) + 1
  // this is done to ease combining elements together via carry
    // for int16 support only the lower InWordDw needs to be taken for the lsb element
  always_comb op_mask = is_i16_lsb ? {(DW-InWordDw+1)'(0), {(InWordDw){1'b1}}} :
                        is_i16_msb ? {(DW-MsbElDW)'(0), {(MsbElDW+1){1'b1}}} :
                        {(DW+1){1'b1}};
  always_comb op_alu_a = op_mask & op_sgn_ext_a;
  always_comb op_alu_b = op_mask & (alu_sub ? ~op_sgn_ext_b : op_sgn_ext_b);
  always_comb op_alu_cin = is_i16_msb ? i_i16_ctrl.lsb_carry : alu_sub;

  always_comb {op_alu_cout, alu_unsigned_sum} = op_alu_a + op_alu_b + op_alu_cin;
  always_comb alu_cout = is_i16_msb ? alu_unsigned_sum[MsbElDW] : op_alu_cout;
  always_comb o_i16_ctrl.lsb_carry = alu_unsigned_sum[InWordDw];

  logic op_a_sign, op_b_sign, sum_sign;

  always_comb op_a_sign = is_i16_msb ? op_a[MsbElDW-1] : op_a[DW-1];
  always_comb op_b_sign = is_i16_msb ? op_b[MsbElDW-1] : op_b[DW-1];
  always_comb sum_sign  = is_i16_msb ? alu_unsigned_sum[MsbElDW-1] : alu_unsigned_sum[DW-1];

  always_comb begin
    alu_sat_pos = 1'b0;
    alu_sat_neg = 1'b0;

    // Saturate the adder depending on configuration
    if (csr_saturated_add_i == 1'b1) begin
      if (csr_signed_operation_i == 1'b1) begin
        // Saturate signed overflow of two positive operands to max value
        if (~op_a_sign & ~op_b_sign == 1'b1) begin
          if (sum_sign == 1'b1) begin
            alu_sat_pos = 1'b1;
          end
        end
        // Saturate signed underflow of two negative operands to min value
        if (op_a_sign & op_b_sign == 1'b1) begin
          if (sum_sign == 1'b0) begin
            alu_sat_neg = 1'b1;
          end
        end
      end else begin
        // Saturate unsigned overflow to max value
        if (alu_cout) begin
          alu_sat_pos = 1'b1;
        end
      end
    end
  end

  always_comb o_i16_ctrl.msb_carry = alu_unsigned_sum[IAU_DPU_I16_DW-InWordDw];
  always_comb o_i16_ctrl.sat_pos = alu_sat_pos;
  always_comb o_i16_ctrl.sat_neg = alu_sat_neg;

  // saturation:
  always_comb begin
    alu_sum = alu_unsigned_sum;

    // Saturate the adder depending on what is required
    // this is different for the msb element in i16 support
    if (is_i16_msb) begin
      if (alu_sat_pos && csr_signed_operation_i) begin
        alu_sum[MsbElDW-1]   = 1'b0;
        alu_sum[MsbElDW-2:0] = '1;
      end else if (alu_sat_pos) begin
        alu_sum = '1;
      end else if (alu_sat_neg) begin
        alu_sum[MsbElDW-1]   = 1'b1;
        alu_sum[MsbElDW-2:0] = '0;
      end
    end else begin
      if ((is_i16_lsb ? i_i16_ctrl.sat_pos : alu_sat_pos) && csr_signed_operation_i) begin
          alu_sum[DW-1]   = 1'b0;
          alu_sum[DW-2:0] = '1;
      end else if ((is_i16_lsb ? i_i16_ctrl.sat_pos : alu_sat_pos)) begin
          alu_sum = '1;
      end else if ((is_i16_lsb ? i_i16_ctrl.sat_neg : alu_sat_neg)) begin
          alu_sum[DW-1]   = 1'b1;
          alu_sum[DW-2:0] = '0;
      end
    end
  end

  // Min/Max operation
  assign alu_max = (is_i16_lsb ? i_i16_ctrl.msb_carry : alu_cout) ? op_b : op_a;
  assign alu_min = (is_i16_lsb ? i_i16_ctrl.msb_carry : alu_cout) ? op_a : op_b;

  // Select result
  always_comb begin
    unique case (instr_opcode)
      OP_NOP:  alu_result = op_a;
      OP_MV:   alu_result = op_a;
      OP_MAX:  alu_result = alu_max;
      OP_MIN:  alu_result = alu_min;
      OP_ADD:  alu_result = alu_sum;
      OP_SUB:  alu_result = alu_sum;
      default: alu_result = op_a;
    endcase
  end

  assign out_buf_data_d = (exe_instr && instr_dst_used && instr_dst_stream) ?
                          alu_result : out_buf_data_q;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n) begin
      out_buf_data_q <= '0;
    end else begin
      if (exe_instr && instr_dst_used && instr_dst_stream)
        out_buf_data_q <= out_buf_data_d;
    end
  end

  assign o_pixel_data = out_buf_data_q;

endmodule

`endif  // IAU_PIXEL_DP_SV
