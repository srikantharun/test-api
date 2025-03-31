// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: dpu package
// Defines parameters and ctrl structs
// Owner: Stefan Mach <stefan.mach@axelera.ai>

package dpu_pkg;

  //-------------------------------------------------
  // Helper Functions
  //-------------------------------------------------
  function automatic int max(int a, int b);
    return (a > b) ? a : b;
  endfunction

  //-------------------------------------------------
  // Parameter definition
  //-------------------------------------------------
  // General parameters
  parameter logic [7:0] DPU_HW_REVISION = 8'b00000010;

  // Observation parameters
  parameter int unsigned OBS_W = aic_common_pkg::AIC_DEV_OBS_DW;

  // Block identification parameters
  parameter int unsigned CID_W = aic_common_pkg::AIC_CID_SUB_W;
  parameter int unsigned BLOCK_ID_W = aic_common_pkg::AIC_BLOCK_ID_WIDTH;

  // Data width parameters
  parameter int unsigned PW_LEN = aic_common_pkg::AIC_PWORD_SIZE;
  parameter int unsigned IO_W = 8;  // IFD/ODR word width
  parameter int unsigned PW_IO_W = aic_common_pkg::AIC_PWORD_WIDTH;
  parameter int unsigned IAU_W = 32;  // IAU word width
  parameter int unsigned PW_IAU_W = aic_common_pkg::AIC_PWORD_I32_WIDTH;

  // Token parameters
  parameter int unsigned NR_TOK_PROD = token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD;
  parameter int unsigned NR_TOK_CONS = token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS;

  // List of AXI slaves in DPU
  parameter int unsigned NR_AXI_SLV = 3;
  parameter int unsigned AXI_S_IDX_CSR = 0;
  parameter int unsigned AXI_S_IDX_CMD_BLOCK = 1;
  parameter int unsigned AXI_S_IDX_DPCMD_GEN = 2;

  // Split the local address space evenly among AXI slaves
  // (address space is in bytes -> 'h4000 = 2048 64-bit rows)
  parameter int unsigned AXI_S_ADDR_CSR = 'h0000;
  parameter int unsigned AXI_S_ADDR_CMD_BLOCK = 'h1000;
  parameter int unsigned AXI_S_ADDR_DPCMD_GEN = 'h8000;
  parameter int unsigned AXI_S_ADDR_CAP_CSR = 'h1000;
  parameter int unsigned AXI_S_ADDR_CAP_CMD_BLOCK = 'h1000;
  parameter int unsigned AXI_S_ADDR_CAP_DPCMD_GEN = 'h8000;

  // Indicates the relevant bits in local address space
  parameter int unsigned AXI_S_ADDR_CAP = 'h10000;

  // CMD block parameters
  parameter int unsigned CMDB_MAX_OUTST_CMDS = aic_common_pkg::AIC_GEN_CMDB_MAX_OUTST_CMDS;
  parameter int unsigned CMDB_FIFO_DEPTH = aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH;

  //-------------------------------------------------
  // DPU DPcmd generation
  //-------------------------------------------------
  // Internal program memory parameters
  parameter bit USE_IMEM_MACRO = 1'b1;
  parameter int unsigned PRG_MEM_DEPTH = 1024;
  parameter int unsigned PRG_MEM_ADDR_W = $clog2(PRG_MEM_DEPTH);
  parameter int unsigned PRG_MEM_WIDTH = 32;

  //-------------------------------------------------
  // Macro daisy chaining
  //-------------------------------------------------
  parameter int unsigned DPU_NUM_MACROS = USE_IMEM_MACRO + 2;
  typedef enum logic [1:0] {
    DPU_MACRO_INSTR   = 'd0,
    DPU_MACRO_B_STORE = 'd1,
    DPU_MACRO_C_STORE = 'd2
  } dpu_macro_e;
  parameter int unsigned DPU_MACRO_DAISY_DEFAULT[DPU_NUM_MACROS] = '{
      0: DPU_MACRO_INSTR,
      1: DPU_MACRO_B_STORE,
      2: DPU_MACRO_C_STORE
  };
  typedef enum logic [1:0] {
    DPU_IDX_CSR  = 0,
    DPU_IDX_CMDB = 1,
    DPU_IDX_IMEM = 2
  } dpu_idx_e;

  // AXI address cap for program memory (64-bit rows) in bytes
  // (PRG_MEM_DEPTH * 8 bytes)
  // should be <= addr cap of dpcmd gen
  parameter longint AXI_S_ADDR_CAP_PRG_MEM = PRG_MEM_DEPTH * 8;

  // DPU DP cmd_gen interrupt parameters
  typedef struct packed {
    logic err_illegal_format;
    logic err_empty_program;
    logic err_init_segfault;
    logic err_loop_segfault;
  } dpu_csr_cmdgen_irq_status_reg_t;

  // ========================
  // DPU Operations Encoding
  // ========================
  // Common Encodings
  // =================
  // Opcode Field
  typedef enum logic [3:0] {
    OPC_UNARY    = 4'h0,
    OPC_MV       = 4'h1,
    OPC_LUT      = 4'h2,
    OPC_RFS      = 4'h3,
    OPC_MUL      = 4'h4,
    OPC_ADD      = 4'h5,
    OPC_SUB      = 4'h6,
    OPC_MAX      = 4'h7,
    OPC_MIN      = 4'h8,
    OPC_PRELU    = 4'h9,
    OPC_CMADD    = 4'hA,
    OPC_MADD     = 4'hB,
    OPC_MADD_RFS = 4'hC,
    OPC_PSEUDO   = 4'hF
  } opcode_e;

  // Function Field
  typedef enum logic [6:0] {
    FUNC_NOP     = 7'h00,
    FUNC_MVCL    = 7'h01,
    FUNC_MVCH    = 7'h02,
    FUNC_CLMV    = 7'h03,
    FUNC_CHMV    = 7'h04,
    FUNC_CLMVCL  = 7'h05,
    FUNC_CLMVCH  = 7'h06,
    FUNC_CHMVCL  = 7'h07,
    FUNC_CHMVCH  = 7'h08,
    FUNC_MV64    = 7'h09,
    FUNC_MVCL64  = 7'h0A,
    FUNC_MVCH64  = 7'h0B,
    FUNC_MVLUT64 = 7'h0C,
    FUNC_NEG     = 7'h0D,
    FUNC_RECIP   = 7'h0E,
    FUNC_RSQRT   = 7'h0F,
    FUNC_SQRT    = 7'h10,
    FUNC_SIN     = 7'h11,
    FUNC_COS     = 7'h12,
    FUNC_LOG2    = 7'h13,
    FUNC_EXP2    = 7'h14,
    FUNC_MAXR    = 7'h15,
    FUNC_MINR    = 7'h16,
    FUNC_SUMR    = 7'h17,
    FUNC_LUT     = 7'h18,
    FUNC_DLUT    = 7'h19,
    FUNC_CLLUT   = 7'h1A,
    FUNC_CHLUT   = 7'h1B,
    FUNC_MV      = 7'h1C,
    FUNC_MUL     = 7'h1D,
    FUNC_ADD     = 7'h1E,
    FUNC_SUB     = 7'h1F,
    FUNC_MAX     = 7'h20,
    FUNC_MIN     = 7'h21,
    FUNC_PRELU   = 7'h22,
    FUNC_CMADD   = 7'h23
  } func_e;

  // Constant Selection
  typedef enum logic [6:0] {
    CONST_ZERO    = 7'h0,
    CONST_ONE     = 7'h1,
    CONST_NEGZERO = 7'h2,
    CONST_NEGONE  = 7'h3,
    CONST_INF     = 7'h4,
    CONST_NEGINF  = 7'h5,
    CONST_PI      = 7'h6,
    CONST_2PI     = 7'h7
  } const_sel_e;

  // Psuedo-Function Field
  typedef enum logic [6:0] {PSEUDO_MVC = 7'h00} pseudo_func_e;

  // Operand location prefixes
  parameter logic [6:0] S0_PREFIX = 7'b000????;
  parameter logic [6:0] S1_PREFIX = 7'b001????;
  parameter logic [6:0] A_PREFIX  = 7'b01?????;
  parameter logic [6:0] BC_PREFIX = 7'b1??????;
  parameter logic [6:0] D_PREFIX  = 7'b000????; // TODO: is this right? spec just says addr between 0 and depth-1
  // Mask versions with don't cares flushed to 0, synth tool can't handle casting it to `bit`
  parameter logic [6:0] S0_MASK = 7'b0000000;
  parameter logic [6:0] S1_MASK = 7'b0010000;
  parameter logic [6:0] A_MASK  = 7'b0100000;
  parameter logic [6:0] BC_MASK = 7'b1000000;
  parameter logic [6:0] D_MASK  = 7'b0000000;

  // Stream format encoding
  typedef enum logic [2:0] {
    FMT_INT  = 3'h0,  // default integer format: vm-dependent in DPC, 1-element int format in instr.
    FMT_F16  = 3'h1,
    FMT_F32  = 3'h2,
    FMT_BYP  = 3'h3,
    FMT_INTW = 3'h4,  // wide integer format: 2-element int format always (i48/i16)
    FMT_F24  = 3'h5
  } stream_fmt_e;
  typedef struct packed {
    logic [2:0]  stream_sel;  // TODO(@stefan.mach): make an enum out of this and get rid of PREFIX
    logic        peek;
    stream_fmt_e fmt;
  } stream_operand_t;
  // TODO(@stefan.mach): switch all decoding to a union of different operand types to not use the
  // prefixes & masks anymore?
  // Operand encoding - DPU operands are 7 bit wide
  typedef union packed {
    logic [6:0]      raw;     // not needed
    stream_operand_t as_str;
  } operand_t;

  // Offset/Broadcast
  typedef enum logic [1:0] {
    MAIN    = 2'b00,
    NESTED0 = 2'b01,
    NESTED1 = 2'b10
  } dpc_offset_bcast_loop_sel_e;
  typedef struct packed {
    dpc_offset_bcast_loop_sel_e loop_sel;
    logic                       bcast_enable;    // TODO(@stefan.mach): 2-bit enum for off/ena/bcena
    logic                       enable_feature;
  } dpc_offset_bcast_info_t;
  typedef struct packed {
    logic [5:0] bcast_index;
    logic       bcast_enable;
  } instr_bcast_info_t;

  // DPU DP Command Encoding
  // ========================
  typedef struct packed {
    operand_t src2;
    operand_t src1;
    operand_t src0;
    operand_t dst;
    opcode_e  opcode;
  } dpu_dp_cmd_t;
  // NOTE: no error checking of illegal ops in shim!

  // DPU Instruction Encoding
  // =========================
  typedef enum logic {
    VM_PW64 = 1'b0,
    VM_PW32 = 1'b1
  } vector_mode_e;

  typedef struct packed {
    vector_mode_e vm;
    operand_t     src2;
    operand_t     src1;
    operand_t     src0;
    operand_t     dst;
    opcode_e      opcode;
  } dpu_instr_t;

  // Canonical bypass instruction
  parameter dpu_dp_cmd_t CANONICAL_BYPASS_DPC = '{
      opcode: OPC_RFS,
      dst: S1_MASK | FMT_BYP,  // l0-bp
      src0: S0_MASK | FMT_BYP,  // io-bp
      src1: '0,
      src2: FUNC_MV
  };  // mv l0-bp, i0-bp, rfs=1


  // =======================
  // DPU Datapath Internals
  // =======================

  // Internal Word Widths
  // =====================
  // All rounded up!
  parameter int unsigned HW_LEN = (PW_LEN + 1) / 2;  // Half-Word (pword32), for VM and conversions
  parameter int unsigned TW_LEN = (PW_LEN + 2) / 3;  // Third-Word (pword22), for conversions
  parameter int unsigned QW_LEN = (PW_LEN + 3) / 4;  // Quarter-Word (pword16), for conversions

  // DPU Internal Storage
  // =====================
  // Internal storage depth
  parameter int unsigned A_DEPTH = 8;
  parameter int unsigned B_DEPTH = 64;
  parameter int unsigned C_DEPTH = 64;
  parameter int unsigned D_DEPTH = 2;
  // Addresses
  parameter int unsigned S_ADDR_W = 3;
  parameter int unsigned A_ADDR_W = $clog2(A_DEPTH);
  parameter int unsigned B_ADDR_W = $clog2(B_DEPTH);
  parameter int unsigned C_ADDR_W = $clog2(C_DEPTH);
  parameter int unsigned D_ADDR_W = $clog2(D_DEPTH);
  typedef logic [S_ADDR_W-1:0] s_addr_t;
  typedef logic [A_ADDR_W-1:0] a_addr_t;
  typedef logic [B_ADDR_W-1:0] b_addr_t;
  typedef logic [C_ADDR_W-1:0] c_addr_t;
  typedef logic [D_ADDR_W-1:0] d_addr_t;

  parameter int unsigned MAX_ADDR_W = max(max(A_ADDR_W, B_ADDR_W), C_ADDR_W);

  // Internal Encodings
  // ===================
  // DPU-internal operations post-decode - MADD derivatives collapsed
  typedef enum logic [3:0] {
    MV,
    MADD,
    PRELU,
    LUT,
    MAX,
    MIN,
    MAXR,
    MINR,
    SUMR,
    RECIP,
    RSQRT,
    SQRT,
    SIN,
    COS,
    LOG2,
    EXP2
  } operation_e;

  // Architectrual location select
  typedef enum logic [3:0] {
    SRC_LOC_NONE,
    SRC_LOC_S0,
    SRC_LOC_S1,
    SRC_LOC_A,
    SRC_LOC_B,
    SRC_LOC_CL,
    SRC_LOC_CH,
    SRC_LOC_D,
    SRC_LOC_CONST
  } src_loc_e;
  typedef enum logic [2:0] {
    DST_LOC_NONE,  // nop
    DST_LOC_S0,
    DST_LOC_S1,
    DST_LOC_A,
    DST_LOC_B,
    DST_LOC_CL,
    DST_LOC_CH,
    DST_LOC_D
  } dst_loc_e;
  // Architectural locations in the DPU (for destinations)
  typedef struct packed {
    vector_mode_e          vm;    // Vector mode of operand (pword32/64)
    logic                  last_op;  // signal dp_done upon completion
    dst_loc_e              loc;
    logic [MAX_ADDR_W-1:0] addr;
  } dst_loc_t;

  // Broadcasting or Masking information from ID to ISS
  typedef union packed {
    operand_t          mask_size;
    instr_bcast_info_t bcast_info;
  } mask_bcast_info_t;

  // Floating-Point Definitions
  // ===========================
  parameter int unsigned DPU_FPT_EXPW = 7;  // Number of bits of exponent
  parameter int unsigned DPU_FPT_SIGW = 10;  // Number of bits of mantisa
  parameter int unsigned DPU_FPT_BIAS = 2 ** (DPU_FPT_EXPW - 1) - 1;  // symmetric bias

  // DPU-Internal FP type (FP18, but generic here)
  typedef struct packed {
    logic sign;
    logic [DPU_FPT_EXPW-1:0] exp;
    logic [DPU_FPT_SIGW-1:0] mant;
  } dpu_fp_t;
  // DPU-Facing PWORDs
  typedef dpu_fp_t [PW_LEN-1:0] pw_dpu_fp_t;
  typedef dpu_fp_t [HW_LEN-1:0] hw_dpu_fp_t;
  typedef dpu_fp_t [TW_LEN-1:0] tw_dpu_fp_t;
  typedef dpu_fp_t [QW_LEN-1:0] qw_dpu_fp_t;

  // FP18 Constants
  // Helper: get mantissa of PI
  function automatic logic [DPU_FPT_SIGW-1:0] get_pi_mant();
    // 64 bits of mantissa of the binary FP representation of PI (truncated)
    parameter logic [63:0] PI_SIG_64 = 64'h921FB54442D18469;
    // Cut out the required number of bits and RNE
    automatic logic [DPU_FPT_SIGW-1:0] res = PI_SIG_64 >> (64 - DPU_FPT_SIGW);
    automatic logic [1:0] rs = {PI_SIG_64[63-DPU_FPT_SIGW], |PI_SIG_64[63-DPU_FPT_SIGW-1:0]};
    automatic logic rnd;
    unique case (rs)
      2'b10:   rnd = PI_SIG_64[64-DPU_FPT_SIGW];
      2'b11:   rnd = 1'b1;
      default: rnd = 1'b0;
    endcase
    return res + rnd;
  endfunction
  // 18'h00000: 0.0 = +1 * 2^-126 * 0.0
  parameter dpu_fp_t DPU_FP_ZERO = '{sign: 0, exp: 0, mant: 0};
  // 18'h20000: -0.0 = -1 * 2^-126 * 0.0
  parameter dpu_fp_t DPU_FP_NEGZERO = '{sign: 1, exp: 0, mant: 0};
  // 18'h0fc00: 1.0 = +1 * 2^0 * 1.0
  parameter dpu_fp_t DPU_FP_ONE = '{sign: 0, exp: 0 + DPU_FPT_BIAS, mant: 0};
  // 18'h2fc00: -1.0 = -1 * 2^0 * 1.0
  parameter dpu_fp_t DPU_FP_NEGONE = '{sign: 1, exp: 0 + DPU_FPT_BIAS, mant: 0};
  // 18'h1fc00: inf := +1 * 2^127 * 1.0
  parameter dpu_fp_t DPU_FP_INF = '{sign: 0, exp: 2 ** DPU_FPT_EXPW - 1, mant: 0};
  // 18'h3fc00: -inf := -1 * 2^127 * 1.0
  parameter dpu_fp_t DPU_FP_NEGINF = '{sign: 1, exp: 2 ** DPU_FPT_EXPW - 1, mant: 0};
  // 18'h10248: 3.140625 = +1 * 2^1 * 1.5703125
  parameter dpu_fp_t DPU_FP_PI = '{sign: 0, exp: 1 + DPU_FPT_BIAS, mant: get_pi_mant()};
  // 18'h10648: 6.28125 = +1 * 2^2 * 1.5703125
  parameter dpu_fp_t DPU_FP_2PI = '{sign: 0, exp: 2 + DPU_FPT_BIAS, mant: get_pi_mant()};

  parameter pw_dpu_fp_t PW_DPU_FP_ZERO = {PW_LEN{DPU_FP_ZERO}};
  parameter pw_dpu_fp_t PW_DPU_FP_NEGZERO = {PW_LEN{DPU_FP_NEGZERO}};
  parameter pw_dpu_fp_t PW_DPU_FP_ONE = {PW_LEN{DPU_FP_ONE}};
  parameter pw_dpu_fp_t PW_DPU_FP_NEGONE = {PW_LEN{DPU_FP_NEGONE}};
  parameter pw_dpu_fp_t PW_DPU_FP_INF = {PW_LEN{DPU_FP_INF}};
  parameter pw_dpu_fp_t PW_DPU_FP_NEGINF = {PW_LEN{DPU_FP_NEGINF}};
  parameter pw_dpu_fp_t PW_DPU_FP_PI = {PW_LEN{DPU_FP_PI}};
  parameter pw_dpu_fp_t PW_DPU_FP_2PI = {PW_LEN{DPU_FP_2PI}};

  // FP32 type
  typedef struct packed {
    logic sign;
    logic [7:0] exp;
    logic [22:0] mant;
  } fp32_t;
  // Stream-Facing PWORD (beat)
  typedef fp32_t [(PW_IO_W+31)/32-1:0] beat_fp32_t;  // 16 elements

  // FP24 type
  typedef struct packed {
    logic sign;
    logic [7:0] exp;
    logic [14:0] mant;
  } fp24_t;
  // Stream-Facing PWORD (beat) - rounded up, at least one beat uses all elements
  typedef fp24_t [(PW_IO_W+23)/24-1:0] beat_fp24_t;  // 22 elements

  // FP16 type
  typedef struct packed {
    logic sign;
    logic [4:0] exp;
    logic [9:0] mant;
  } fp16_t;
  // Stream-Facing PWORD (beat)
  typedef fp16_t [(PW_IO_W+15)/16-1:0] beat_fp16_t;  // 32 elements

  // Stream Representation Vector Modes
  // ===================================
  // TODO(@stefan.mach): these should probably be in an aic_common_pkg somewhere
  parameter int unsigned PW64_IAU_INT_WIDTH = aic_common_pkg::AIC_PWORD64_IAU_DPU_INT_WIDTH;
  parameter int unsigned PW32_IAU_INT_WIDTH = aic_common_pkg::AIC_PWORD32_IAU_DPU_INT_WIDTH;
  parameter int unsigned PW64_IFD1_INT_WIDTH = aic_common_pkg::AIC_PWORD64_INT_WIDTH;
  parameter int unsigned PW32_IFD1_INT_WIDTH = aic_common_pkg::AIC_PWORD32_INT_WIDTH;


  //-------------------------------------------------
  // DP Config
  //-------------------------------------------------
  parameter int unsigned NR_LUT_BINS = 16;

  typedef struct packed {
    dpu_fp_t version;
    dpu_fp_t [8:0] reserved;
    dpu_fp_t hi_off;
    dpu_fp_t hi_bnd;
    dpu_fp_t lo_off;
    dpu_fp_t lo_bnd;
    dpu_fp_t off_16;
    dpu_fp_t scl_16;
  } new_lut_t;

  parameter int unsigned OSTR_FIFO_DEPTH = 4;

  // Output stream ordering is controlled using a counter
  // TODO(@stefan.mach): ensure this is enough + that the ctr is safe!
  parameter int unsigned INFLT_OPS_CTR_W = 3;

  // DP interrupt parameters
  typedef struct packed {
    logic err_act_stream_in0;
    logic err_act_stream_in1;
    logic err_act_stream_out;
    logic err_i0_termination;
    logic err_i1_termination;
    logic err_id_illegal_instr;
    logic err_i0_of;
    logic err_i0_uf;
    logic err_i0_nx;
    logic err_i1_of;
    logic err_i1_uf;
    logic err_i1_nx;
    logic err_madd_op_of;
    logic err_madd_op_uf;
    logic err_madd_op_nx;
    logic err_madd_op_nv;
    logic err_sumr_op_of;
    logic err_sumr_op_nx;
    logic err_sumr_op_nv;
    logic err_sfu_op_of;
    logic err_sfu_op_uf;
    logic err_sfu_op_nx;
    logic err_sfu_op_nv;
    logic err_sfu_op_zr;
    logic err_o_of;
    logic err_o_uf;
    logic err_o_nx;
  } dpu_csr_dp_irq_status_reg_t;

  // DW fp parameters
  parameter int unsigned DW_IEEE_COMPL = 0;
  parameter logic [2:0] DW_RND_RNE = 3'b000;

  // DW Status Flags
  typedef struct packed {
    logic comp_specific;
    logic huge_int;
    logic inexact;
    logic huge;
    logic tiny;
    logic invalid;
    logic infinity;
    logic zero;
  } dw_status_t;

  //-------------------------------------------------
  // SFU
  //-------------------------------------------------
  parameter bit USE_SFU = 1'b1;

  typedef enum logic [15:0] {
    SFU_FUNC_RECIP   = 16'h1,
    SFU_FUNC_SQRT    = 16'h2,
    SFU_FUNC_INVSQRT = 16'h4,
    SFU_FUNC_SIN     = 16'h8,
    SFU_FUNC_COS     = 16'h10,
    SFU_FUNC_LOG2    = 16'h20,
    SFU_FUNC_EXP2    = 16'h40
  } sfu_func_e;

  typedef logic [6:0] sfu_func_sel_t;

endpackage
