// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: mvm package
// Defines parameters and ctrl structs
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_PKG_SV
`define MVM_PKG_SV

// verilog_lint: waive-start line-length
package mvm_pkg;
  import imc_bank_pkg::*;
  import aic_common_pkg::*;
  // =======================================
  // Parameter definition
  // =======================================

  // General parameters
  parameter int unsigned DATA_W = AIC_PWORD_WIDTH / AIC_PWORD_SIZE;
  parameter int unsigned PW_LEN = AIC_PWORD_SIZE;
  parameter int unsigned LIB_CELL_USE = 2;
  parameter int unsigned MAX_INPUT_DATA_W = 16; // Maximum supported input precision

  // HW Revision
  parameter int unsigned MVM_HW_REVISION = 8'b0000_0010;

  // MVM DP related parameters
  parameter int unsigned MVM_NB_IMC_BANKS = 16;
  parameter int unsigned MVM_IMC_BANK_PW = $clog2(MVM_NB_IMC_BANKS);
  parameter int unsigned MVM_OUT_DATA_W = 26;
  parameter int unsigned MVM_ACC_DATA_W = 34;
  parameter int unsigned MVM_TOUT = IMC_NB_COLS_PER_BANK * MVM_NB_IMC_BANKS;
  parameter int unsigned MVM_INP_GATING_GRAN = IMC_BLOCK_GATING_GRANULARITY;

  parameter int unsigned MVM_NR_INPUT_PW = IMC_NB_ROWS / PW_LEN;
  parameter int unsigned MVM_NR_OUTPUT_PW = MVM_TOUT / PW_LEN;
  parameter int unsigned MVM_INP_GATING_DW = IMC_NB_ROWS / IMC_BLOCK_GATING_GRANULARITY;
  parameter int unsigned MVM_OUP_GATING_DW = MVM_NB_IMC_BANKS;

  // IMC Bank group
  parameter int unsigned MVM_IMC_COLS_GROUP = IMC_NB_COLS_PER_BANK/2;
  parameter int unsigned MVM_IMC_COLS_GROUP_OUT_WD = 19;
  parameter int unsigned MVM_IMC_OUT_DATA_W = 19;

  // Util limiting parameters
  parameter int unsigned MVM_UTIL_WIDTH = 10;  // width used internally in the mvm
  parameter int unsigned MVM_UTIL_INTERFACE_WIDTH = 8;  // width exposed to outside the mvm
  parameter int unsigned MVM_UTIL_EXP_AVG_DENOMINATOR = 256;
  parameter int unsigned MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH = $clog2(MVM_UTIL_EXP_AVG_DENOMINATOR);

  // =======================================
  // MVM AXI params
  // =======================================
  parameter int unsigned MVM_AXI_ADDR_CAP = 'h1000_0000;  // Range of ai_core
  parameter int unsigned MVM_EXE_AXI_BASE = 'h10090000 % MVM_AXI_ADDR_CAP; //aipu_addr_map_pkg::AIC_0_M_MVMEXE_ST_ADDR % MVM_AXI_ADDR_CAP;
  parameter int unsigned MVM_PRG_AXI_BASE = 'h100a0000 % MVM_AXI_ADDR_CAP; // aipu_addr_map_pkg::AIC_0_M_MVMPRG_ST_ADDR % MVM_AXI_ADDR_CAP;
  parameter int unsigned MVM_AXI_NR_SLVS = 5;

  // =======================================
  // MVM EXE QCMD params
  // =======================================
  parameter int unsigned MVM_EXE_QCMD_MEM_DEPTH = 256;

  //parameter MVM_EXE_QCMD_STRB_FIELD_LSB = 0;
  //parameter MVM_EXE_QCMD_WS_FIELD_LSB = MVM_EXE_QCMD_STRB_FIELD_LSB + MVM_TOUT;
  parameter int unsigned MVM_EXE_QCMD_WS_FIELD_LSB = 0;
  parameter int unsigned MVM_EXE_QCMD_WS_FIELD_DW = $clog2(IMC_NB_WEIGHT_SETS);
  parameter int unsigned MVM_EXE_QCMD_INPOFF_FIELD_LSB = MVM_EXE_QCMD_WS_FIELD_LSB + MVM_EXE_QCMD_WS_FIELD_DW;
  parameter int unsigned MVM_EXE_QCMD_INPOFF_FIELD_DW = $clog2(MVM_NR_INPUT_PW);
  parameter int unsigned MVM_EXE_QCMD_OUPOFF_FIELD_LSB = MVM_EXE_QCMD_INPOFF_FIELD_LSB + MVM_EXE_QCMD_INPOFF_FIELD_DW;
  parameter int unsigned MVM_EXE_QCMD_OUPOFF_FIELD_DW = $clog2(MVM_NR_OUTPUT_PW);
  parameter int unsigned MVM_EXE_QCMD_INPSIZE_FIELD_LSB = MVM_EXE_QCMD_OUPOFF_FIELD_LSB + MVM_EXE_QCMD_OUPOFF_FIELD_DW;
  parameter int unsigned MVM_EXE_QCMD_INPSIZE_FIELD_DW = $clog2(MVM_NR_INPUT_PW);
  parameter int unsigned MVM_EXE_QCMD_OUPSIZE_FIELD_LSB = MVM_EXE_QCMD_INPSIZE_FIELD_LSB + MVM_EXE_QCMD_INPSIZE_FIELD_DW;
  parameter int unsigned MVM_EXE_QCMD_OUPSIZE_FIELD_DW = $clog2(MVM_NR_OUTPUT_PW);
  parameter int unsigned MVM_EXE_QCMD_ALIGN = 16;
  parameter int unsigned MVM_EXE_QCMD_UNUSED = MVM_EXE_QCMD_ALIGN - (MVM_EXE_QCMD_OUPSIZE_FIELD_LSB + MVM_EXE_QCMD_OUPSIZE_FIELD_DW);
  parameter int unsigned MVM_EXE_QCMD_DW = MVM_EXE_QCMD_OUPSIZE_FIELD_LSB + MVM_EXE_QCMD_OUPSIZE_FIELD_DW + MVM_EXE_QCMD_UNUSED;

  // AXI SLV params
  parameter int unsigned MVM_EXE_QCMD_AXI_SLV = 2;
  parameter int MVM_EXE_QCMD_AXI_ST = 'h8000 + MVM_EXE_AXI_BASE;
  parameter int unsigned MVM_EXE_QCMD_AXI_CAP = 'h8000;

  // =======================================
  // MVM EXE CMDB parameters
  // =======================================
  // FIFO depth
  parameter int unsigned MVM_EXE_CMDB_FIFO_DEPTH = AIC_GEN_CMDB_CMD_FIFO_DEPTH;
  // Outstanding commands
  parameter int unsigned MVM_EXE_CMDB_MAX_OUTST_CMDS = AIC_GEN_CMDB_MAX_OUTST_CMDS;
  // AXI params
  parameter int unsigned MVM_EXE_CMDB_AXI_SLV = 1;
  parameter int unsigned MVM_EXE_CMDB_AXI_CAP = 'h1000;
  parameter int MVM_EXE_CMDB_AXI_ST = 'h1000 + MVM_EXE_AXI_BASE;
  //// OPCODE params
  //parameter int unsigned MVM_EXE_CMDB_CMP_OPC = 0;
  //parameter int unsigned MVM_EXE_CMDB_BYP_OPC = 1;
  parameter int unsigned MVM_EXE_CMDB_OPC_DW = 1;
  //// CMD Block cmd width
  //parameter int unsigned MVM_EXE_CMDB_OPC_FIELD_LSB = 0;
  //parameter int unsigned MVM_EXE_CMDB_OPC_FIELD_DW = 8;  //opcode/icode are always 1 byte
//
  //parameter int unsigned MVM_EXE_CMDB_START_A_FIELD_LSB = 0;
  parameter int unsigned MVM_EXE_CMDB_START_A_FIELD_DW = 8;
  //parameter int unsigned MVM_EXE_CMDB_START_B_FIELD_LSB = 8; //MVM_EXE_CMDB_START_A_FIELD_LSB + MVM_EXE_CMDB_START_A_FIELD_DW
  parameter int unsigned MVM_EXE_CMDB_START_B_FIELD_DW = 8;
  //parameter int unsigned MVM_EXE_CMDB_LEN_FIELD_LSB = 16; //MVM_EXE_CMDB_START_B_FIELD_LSB + MVM_EXE_CMDB_START_B_FIELD_DW
  parameter int unsigned MVM_EXE_CMDB_LEN_FIELD_DW = 16;
  //parameter int unsigned MVM_EXE_CMDB_ITER_FIELD_LSB = 32; //MVM_EXE_CMDB_LEN_FIELD_LSB + MVM_EXE_CMDB_LEN_FIELD_DW + 8
  parameter int unsigned MVM_EXE_CMDB_ITER_FIELD_DW = 24;
  //parameter int unsigned MVM_EXE_CMDB_DP_CTRL_FIELD_LSB = 56; //MVM_EXE_CMDB_DP_CTRL_FIELD_LSB + MVM_EXE_CMDB_DP_CTRL_FIELD_DW
  parameter int unsigned MVM_EXE_CMDB_DP_CTRL_FIELD_DW = 8;
  //parameter int unsigned MVM_EXE_CMDB_CMD_DW = $bits(mvm_exe_cmd_t);//MVM_EXE_CMDB_DP_CTRL_FIELD_LSB + MVM_EXE_CMDB_DP_CTRL_FIELD_DW;
//
  parameter int unsigned MVM_EXE_CMDB_START_FIELD_DW = MVM_EXE_CMDB_START_A_FIELD_DW + MVM_EXE_CMDB_START_B_FIELD_DW;

  // =======================================
  // MVM PRG CMD unpack parameters
  // =======================================
  typedef enum logic [2:0] {
    UuT     = 3'd0,
    TUu     = 3'd1,
    UTu     = 3'd2,
    rsvd[5] = 3'd3
  } prog_mode_e;

  typedef struct packed {
    logic [3:0] rsvd;
    logic       broadcast;
    prog_mode_e prog_mode;
  } prg_t;

  typedef struct packed {
    logic [1:0][7:0] rsvd;
    logic      [7:0] wb_t_pw;
    logic      [7:0] wb_u_pw;
    logic      [7:0] a_t_pw;
    logic      [7:0] a_u_pw;
    logic      [7:0] a_s;
    prg_t            prog;
  } mvm_prg_cmd_t;

  typedef struct packed {
    logic [$clog2(MVM_NR_INPUT_PW)-1:0] block_index;
    logic [$clog2(PW_LEN)-1:0] block_row;
  } row_counter_t;
  typedef logic [$clog2(MVM_NR_OUTPUT_PW)-1:0] col_counter_t;
  typedef struct packed {
    row_counter_t row;
    col_counter_t col;
  } prog_counter_t;
  typedef union packed {
    logic [$clog2(IMC_NB_ROWS)-1:0] bit_array;
  } check_row_counter_t;
  // =======================================
  // MVM EXE CMD unpack parameters
  // =======================================

  typedef enum logic {
    simple = 1'b0,
    advanced = 1'b1
  } mvm_dibw_mode_e;

  typedef enum logic [1:0] {
    w_int8 = 2'd0,
    w_int16 = 2'd1,
    w_rsvd[2] = 2'd2
  } mvm_weight_precision_e;

  typedef enum logic {
    inp_int8 = 1'b0,
    inp_int16 = 1'b1
  } mvm_input_precision_e;

  typedef struct packed {
    logic            [2:0] rsvd;
    mvm_weight_precision_e weight_precision;
    mvm_input_precision_e  input_precision;
    mvm_dibw_mode_e        double_bw_mode;
    logic                  double_bw_en;
  } exe_cmd_dp_ctrl_field_t;

  parameter int unsigned MVM_EXE_CMD_NR_FORMATS = 2;
  parameter int unsigned MVM_EXE_CMD_FORMAT_DW = cc_math_pkg::index_width(MVM_EXE_CMD_NR_FORMATS);
  typedef struct packed {
    exe_cmd_dp_ctrl_field_t dp_ctrl;
    logic            [23:0] iter;
    logic            [15:0] len;
    logic            [15:0] start;
  } mvm_exe_cmd_cmp_t;

  typedef enum logic [7:0] {
    MVM_EXE_CMDB_CMP_OPC = 8'd0,
    MVM_EXE_CMDB_BYP_OPC = 8'd1
  } mvm_exe_cmd_opt_t;

  typedef struct packed {
    logic  [6:0][7:0] rsrv;
    mvm_exe_cmd_opt_t opc;
  } mvm_exe_cmd_byp_t;

  typedef union packed {
    mvm_exe_cmd_cmp_t cmp;
    mvm_exe_cmd_byp_t byp;
  } mvm_exe_cmd_t;

  parameter int unsigned MVM_EXE_CMDB_CMD_DW = $bits(mvm_exe_cmd_t);

  typedef enum logic [MVM_EXE_CMD_FORMAT_DW-1:0] {
    MVM_EXE_CMDB_CMP_FMT = (MVM_EXE_CMD_FORMAT_DW)'('d0),
    MVM_EXE_CMDB_BYP_FMT = (MVM_EXE_CMD_FORMAT_DW)'('d1)
  } mvm_exe_cmd_formats_t;

  parameter int MVM_EXE_CMD_FORMAT_NR_BYTES[MVM_EXE_CMD_NR_FORMATS] = {8, 0};

  parameter mvm_exe_cmd_cmp_t MVM_EXE_CMD_CMP_DEF_VALS = mvm_exe_cmd_cmp_t'{
    dp_ctrl: exe_cmd_dp_ctrl_field_t'{
      rsvd            : '0,
      weight_precision: w_int8,
      input_precision : inp_int8,
      double_bw_mode  : simple,
      double_bw_en    : '0
    },
    iter   : '0,
    len    : '0,
    start  : '0
  };
  parameter mvm_exe_cmd_byp_t MVM_EXE_CMD_BYP_DEF_VALS = mvm_exe_cmd_byp_t'{
    rsrv: '0,
    opc : MVM_EXE_CMDB_CMP_OPC
  };

  ////////////////////////////////
  /// Unions used to check the size of the registers and fields
  typedef union packed {
    logic             [7:0] bit_array;
    exe_cmd_dp_ctrl_field_t exe_cmd_dp_ctrl_field;
    prg_t                   prg_field;
  } mvm_single_byte_fields_checker_t;
  typedef union packed {
    logic      [63:0] bit_array;
    mvm_exe_cmd_cmp_t cmp;
    mvm_exe_cmd_byp_t byp;
    mvm_prg_cmd_t     prg;
  } mvm_8_byte_reg_checker_t;

  // =======================================
  // MVM EXE CSR parameters
  // =======================================
  parameter int unsigned MVM_EXE_CSR_AXI_SLV = 0;
  parameter int MVM_EXE_CSR_AXI_ST = 'h0000 + MVM_EXE_AXI_BASE;
  parameter int unsigned MVM_EXE_CSR_AXI_CAP = 'h1000;

  // =======================================
  // MVM PRG CSR parameters
  // =======================================
  parameter int unsigned MVM_PRG_CSR_AXI_SLV = 3;
  parameter int MVM_PRG_CSR_AXI_ST = 'h0000 + MVM_PRG_AXI_BASE;
  parameter int unsigned MVM_PRG_CSR_AXI_CAP = 'h1000;

  // =======================================
  // MVM PRG CMDB parameters
  // =======================================
  // FIFO depth
  parameter int unsigned MVM_PRG_CMDB_FIFO_DEPTH = AIC_GEN_CMDB_CMD_FIFO_DEPTH;
  // Outstanding commands
  parameter int unsigned MVM_PRG_CMDB_MAX_OUTST_CMDS = AIC_GEN_CMDB_MAX_OUTST_CMDS;
  // AXI params
  parameter int unsigned MVM_PRG_CMDB_AXI_SLV = 4;
  parameter int unsigned MVM_PRG_CMDB_AXI_CAP = 'h1000;
  parameter int MVM_PRG_CMDB_AXI_ST = 'h1000 + MVM_PRG_AXI_BASE;
  // OPCODE params
  parameter int unsigned MVM_PRG_CMDB_WR_WB_OPC = 0;  // For now only one opcode: write_weight_block
  parameter int unsigned MVM_PRG_CMDB_OPC_DW = 1;

  parameter int unsigned MVM_PRG_CMDB_OPC_FIELD_LSB = 0;
  parameter int unsigned MVM_PRG_CMDB_OPC_FIELD_DW = 8;  //opcode/icode are always 1 byte
  parameter int unsigned MVM_PRG_CMDB_WS_FIELD_LSB = 8; // MVM_PRG_CMDB_OPC_FIELD_LSB + MVM_PRG_CMDB_OPC_FIELD_DW
  parameter int unsigned MVM_PRG_CMDB_WS_FIELD_DW = 8;
  parameter int unsigned MVM_PRG_CMDB_INPOFF_FIELD_LSB = 16; // MVM_PRG_CMDB_WS_FIELD_LSB + MVM_PRG_CMDB_WS_FIELD_DW
  parameter int unsigned MVM_PRG_CMDB_INPOFF_FIELD_DW = 8;
  parameter int unsigned MVM_PRG_CMDB_OUPOFF_FIELD_LSB = 24; // MVM_PRG_CMDB_INPOFF_FIELD_LSB + MVM_PRG_CMDB_INPOFF_FIELD_DW
  parameter int unsigned MVM_PRG_CMDB_OUPOFF_FIELD_DW = 8;
  parameter int unsigned MVM_PRG_CMDB_INPSIZE_FIELD_LSB = 32; // MVM_PRG_CMDB_OUPOFF_FIELD_LSB + MVM_PRG_CMDB_OUPOFF_FIELD_DW
  parameter int unsigned MVM_PRG_CMDB_INPSIZE_FIELD_DW = 8;
  parameter int unsigned MVM_PRG_CMDB_OUPSIZE_FIELD_LSB = 40; // MVM_PRG_CMDB_INPSIZE_FIELD_LSB + MVM_PRG_CMDB_INPSIZE_FIELD_DW
  parameter int unsigned MVM_PRG_CMDB_OUPSIZE_FIELD_DW = 8;
  parameter int unsigned MVM_PRG_CMDB_UNUSED_DW = 64 - (MVM_PRG_CMDB_OUPSIZE_FIELD_LSB + MVM_PRG_CMDB_OUPSIZE_FIELD_DW); //=16
  // CMD Block cmd width
  parameter int unsigned MVM_PRG_CMDB_CMD_DW = MVM_PRG_CMDB_OUPSIZE_FIELD_LSB + MVM_PRG_CMDB_OUPSIZE_FIELD_DW + MVM_PRG_CMDB_UNUSED_DW; //=64

  // =======================================
  // MVM DFT modes for IMC banks
  // =======================================
  parameter int unsigned MVM_IMC_TM_CSR_DW = 3;
  parameter bit [MVM_IMC_TM_CSR_DW-1:0] MVM_IMC_TM_OFF = 0;
  parameter bit [MVM_IMC_TM_CSR_DW-1:0] MVM_IMC_TM0 = 1;
  parameter bit [MVM_IMC_TM_CSR_DW-1:0] MVM_IMC_TM1 = 2;
  parameter bit [MVM_IMC_TM_CSR_DW-1:0] MVM_IMC_TM2 = 3;
  parameter bit [MVM_IMC_TM_CSR_DW-1:0] MVM_IMC_TM3 = 4;

  // =======================================
  // Output DP
  // =======================================
  // Pipeline output local mux 0, 2, 5, 7
  parameter bit [MVM_NB_IMC_BANKS/2-1:0] LOCAL_MUX_PIPELINE_EN = '{
    7: 1'b1,
    6: 1'b0,
    5: 1'b1,
    4: 1'b0,
    3: 1'b0,
    2: 1'b1,
    1: 1'b0,
    0: 1'b1
  };
  // Pipeline input_1 of global mux 2 and 3
  parameter bit [MVM_NB_IMC_BANKS/2-3:0] GLOBAL_MUX_PIPELINE_EN = '{
    5: 1'b0,
    4: 1'b0,
    3: 1'b1,
    2: 1'b1,
    1: 1'b0,
    0: 1'b0
  };

  // =======================================
  // MVM EXE QCMD struct
  // =======================================
  typedef struct packed {
    logic [$clog2(MVM_NR_OUTPUT_PW)-1:0] oup_size;  // corresponds to wb_t_pw_s in IntraCoreDataFlow
    logic [$clog2(MVM_NR_INPUT_PW)-1:0] inp_size;  // corresponds to wb_u_pw in IntraCoreDataFlow
    logic [$clog2(MVM_NR_OUTPUT_PW)-1:0] oup_offset;  // corresponds to a_t_pw in IntraCoreDataFlow
    logic [$clog2(MVM_NR_INPUT_PW)-1:0] inp_offset;  // corresponds to a_u_pw in IntraCoreDataFlow
    logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] ws;  // corresponds to a_s in IntraCoreDataFlow
  } mvm_exe_qcmd_t;
  //parameter int unsigned MVM_EXE_QCMD_DW = $bits(mvm_exe_qcmd);

  typedef logic [MVM_NB_IMC_BANKS-1:0][IMC_NB_ROWS/IMC_BLOCK_GATING_GRANULARITY-1:0] block_enable_t;
  typedef logic [MVM_NB_IMC_BANKS-1:0] block_valid_t;

  typedef struct packed {
    logic [IMC_NB_ROWS-1:0] serial_input;
    logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] weight_set;
    block_enable_t block_enable;
    block_valid_t block_valid;
    logic [$clog2(MAX_INPUT_DATA_W)-1:0] acc_shift_pos;
    logic [MVM_NB_IMC_BANKS-1:0] acc_output_enable;
    logic acc_clear;
    logic acc_signed_weights;
    logic acc_signed_inputs;
    logic acc_weight_precision;
    logic acc_input_precision;
    logic tlast;
    logic bist_mode;
  } imc_compute_struct_t;

  typedef struct packed {
    logic [PW_LEN-1:0] [DATA_W-1:0] w_weight_pw; // Write vector of 64 weights, [63:32] for PW 1, [31:0] for PW 0
    logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] w_set;  // Weight set select for all banks
    logic [MVM_NB_IMC_BANKS-1:0] w_wen;  // Write enable for each bank (n-hot)
    logic [$clog2(IMC_NB_ROWS)-1:0] w_row;  // Row select address
    logic bist_mode;
  } imc_weight_struct_t;

  // =======================================
  // MVM DP CMD structs
  // =======================================
  // par2bser ctrl signals
  typedef struct packed {
    logic [MVM_INP_GATING_DW-1:0] inp_gating;
    logic [MVM_OUP_GATING_DW-1:0] oup_gating;
    logic inp_buf_we;
    logic tlast_predict;
    logic [$clog2(MVM_NR_INPUT_PW)-1 : 0] inp_buf_wr_addr;
    logic par2bser_we;
  } par2bser_dp_cmd_t;
  // imc compute ctrl signals
  typedef struct packed {
    logic imc_compute_gate_clock;
    logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] imc_compute_weight_set;
  } imc_compute_dp_cmd_t;
  // ser acc ctrl signals
  typedef struct packed {
    logic [$clog2(MAX_INPUT_DATA_W)-1:0] acc_shift_pos;
    logic [MVM_NB_IMC_BANKS-1:0] acc_output_enable;
    logic [MVM_INP_GATING_DW-1:0] inp_gating;
    logic [MVM_OUP_GATING_DW-1:0] oup_gating;
    logic acc_clear;
    logic acc_weight_precision;
    logic acc_input_precision;
  } acc_dp_cmd_t;
  // strb values and addr
  // typedef struct packed {
  //   logic [PW_LEN-1 : 0] strb_values;
  //   logic [$clog2(MVM_NR_OUTPUT_PW)-1:0] strb_addr;
  // } strb_dp_cmd;
  // output buffer ctrl signals
  typedef struct packed {
    logic tlast;
  } out_dp_cmd_t;
  typedef struct packed {
    out_dp_cmd_t out_dp_cmd_sig;
    exe_cmd_dp_ctrl_field_t dp_ctrl;
  } par2bser_sideband_t;
  typedef struct packed {
    logic last;
    logic interleave_required;
  } compute_out_ctrl_t;
  // weight programming ctrl signals
  typedef struct packed {
    logic [MVM_NB_IMC_BANKS-1:0]           imc_prg_we;
    logic [$clog2(IMC_NB_ROWS)-1:0]        imc_prg_row;
    logic [$clog2(IMC_NB_WEIGHT_SETS)-1:0] imc_prg_weight_set;
  } mvm_prg_dp_cmd_t;
  parameter int unsigned MVM_PRG_DP_CMD_DW = $bits(mvm_prg_dp_cmd_t);
  // signals required after imc op
  typedef struct packed {
    acc_dp_cmd_t acc_dp_cmd_sig;
    //strb_dp_cmd strb_dp_cmd_sig;
    out_dp_cmd_t  out_dp_cmd_sig;
  } acc_out_dp_cmd_t;
  // full mvm exe dp_cmd signal bundle
  typedef struct packed {
    exe_cmd_dp_ctrl_field_t dp_ctrl;
    par2bser_dp_cmd_t par2bser_dp_cmd_sig;
    imc_compute_dp_cmd_t  imc_cmd_sig;
    out_dp_cmd_t  out_dp_cmd_sig;
    //strb_dp_cmd strb_dp_cmd_sig;
    logic bypass_enable;
  } mvm_exe_dp_cmd_t;
  parameter int unsigned MVM_EXE_DP_CMD_DW = $bits(mvm_exe_dp_cmd_t);
  // signals required after par2bser
  typedef struct packed {
    imc_compute_dp_cmd_t  imc_cmd_sig;
    //strb_dp_cmd strb_dp_cmd_sig;
    out_dp_cmd_t  out_dp_cmd_sig;
    acc_dp_cmd_t acc_dp_cmd_sig;
    logic        dibw_en;
    logic        adv_mode_en;
  } imc_acc_dp_cmd_t;
  // signals that have to flow through par2bser internal fifo
  // typedef struct packed {
  //   //imc_compute_dp_cmd_t  imc_cmd_sig;
  //   //strb_dp_cmd strb_dp_cmd_sig;
  //   out_dp_cmd_t  out_dp_cmd_sig;
  // } par2bser_fifo_dp_cmd;
endpackage
// verilog_lint: waive-stop line-length
`endif  // MVM_PKG_SV
