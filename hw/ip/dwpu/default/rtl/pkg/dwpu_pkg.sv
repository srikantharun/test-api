// (C) Copyright 2022 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner:       Stefan Mach <stefan.mach@axelera.ai>
//              Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
// Description: Package containinng parameters and structs for DWPU

/// The DWPU package (`dwpu_pkg`) contains the general unit parameters as well as the definitions for the different commands for the data path.
///
package dwpu_pkg;

  ////////////
  // Config //
  ////////////
  typedef struct packed {
    logic signed_img;
    logic signed_wgt;
  } config_t;

  parameter bit [7:0] HARDWARE_REVISION = 8'h10;

  ///////////////
  // Data path //
  ///////////////
  // AI Core General
  parameter int unsigned NUM_CHANNELS = aic_common_pkg::AIC_PWORD_SIZE;
  parameter int unsigned IN_PIXEL_WIDTH = 8;
  parameter int unsigned IN_PWORD_WIDTH = NUM_CHANNELS * IN_PIXEL_WIDTH;
  parameter int unsigned OUT_PIXEL_WIDTH = 26;
  parameter int unsigned OUT_PWORD_WIDTH = NUM_CHANNELS * OUT_PIXEL_WIDTH;

  // Input FIFO depth (0 to disable)
  parameter int unsigned INPUT_FIFO_DEPTH = 0;

  // Pixel data
  typedef logic [IN_PIXEL_WIDTH-1:0] input_t;
  typedef logic [OUT_PIXEL_WIDTH-1:0] output_t;

  // Weight buffer
  parameter int unsigned NUM_WB_REGS = 64;

  // Scratchpad - 'sp0' is always at 0, 'sp1' is always the current data input
  parameter int unsigned NUM_SP_REGS = 128;

  // Compute Tree
  parameter int unsigned NUM_PIPELINE_STAGES = 2;
  parameter int unsigned NUM_OPERANDS = 9;
  parameter int unsigned I_SEL_WIDTH = $clog2(NUM_SP_REGS);
  parameter int unsigned W_SEL_WIDTH = $clog2(NUM_WB_REGS);

  ////////////////
  // DP command //
  ////////////////

  parameter int unsigned OP_BITS = 2;
  typedef enum logic [OP_BITS-1:0] {
    SOP = 2'h0,
    SUM = 2'h1,
    MAX = 2'h2,
    MIN = 2'h3
  } opcode_e;

  typedef struct packed {
    logic [1:0] rsvd;       // 2 bit
    logic       last_push;
    logic       shift_wb;
    logic       shift_sp;
    logic       op_exe;
    opcode_e    opcode;
  } op_desc_t;

  parameter op_desc_t DEFAULT_OP_DESC = op_desc_t'{
      rsvd:      2'h0,
      last_push: 1'h0,
      shift_wb:  1'h0,
      shift_sp:  1'h0,
      op_exe:    1'h0,
      opcode:    SOP,
      default:   '0
  };

  typedef logic [I_SEL_WIDTH-1:0] i_sel_t;
  typedef logic [W_SEL_WIDTH-1:0] w_sel_t;

  typedef struct packed {
    // WORD 1
    logic                      rsvd_i_sel;  // 1 bit
    i_sel_t [NUM_OPERANDS-1:0] i_sel;
    // WORD 0
    logic [1:0]                rsvd_w_sel;  // 2 bit
    w_sel_t [NUM_OPERANDS-1:0] w_sel;
    op_desc_t                  op_desc;
  } dwpu_dp_command_t;

  parameter dwpu_dp_command_t DEFAULT_DWPU_INSTR = dwpu_dp_command_t'{
      rsvd_i_sel: 1'h0,
      i_sel:      {NUM_OPERANDS*I_SEL_WIDTH{1'b0}},
      rsvd_w_sel: 2'h0,
      w_sel:      {NUM_OPERANDS*W_SEL_WIDTH{1'b0}},
      op_desc:    DEFAULT_OP_DESC,
      default:    '0
  };

  // The command for the datapath has additional information
  typedef struct packed {
    // Select bypass mode
    logic                    bypass;
    // Instruction
    dwpu_dp_command_t        command;
  } dp_instruction_t;

  parameter int unsigned DP_INSTRUCTION_WIDTH = $bits(dp_instruction_t);


  ///////////////////
  // AXI Endpoints //
  ///////////////////
  // We have CSRs, the CMD block and command memory
  parameter int unsigned NUM_AXI_ENDPOINTS = 3;

  typedef enum logic [1:0] {
    CSR   = 0,
    CMDB  = 1,
    IMEM  = 2
  } axi_slave_idx_e;
endpackage
