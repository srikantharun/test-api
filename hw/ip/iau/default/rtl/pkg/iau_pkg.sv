// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Package with parameters and structs for the IAU
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef IAU_PKG_SV
`define IAU_PKG_SV

package iau_pkg;
  // =======================================
  // IAU general parameters
  // =======================================
  parameter logic [7:0] IAU_HW_REVISION = 8'b0000_0010;

  // =======================================
  // IAU DPcmd generation
  // =======================================
  // Internal program memory parameters
  parameter int unsigned IAU_PRG_MEM_DEPTH = 256;
  parameter int unsigned IAU_PRG_MAX_ITER_BITS = 32;
  parameter int unsigned IAU_PRG_MEM_AW = $clog2(IAU_PRG_MEM_DEPTH);

  // AXI address cap for program memory (64-bit rows)
  // (IAU_PRG_MEM_DEPTH * 8 bytes)
  // Note: DPCMD GEN ADDRESS RANGE DOES NOT MATCH THIS
  parameter int unsigned IAU_AXI_ADDR_CAP_PRG_MEM = 'h800;

  // DPcmd opcode enumeration
  typedef enum logic [2:0] {
    OP_NOP = 3'b000,
    OP_MV  = 3'b001,
    OP_MAX = 3'b010,
    OP_MIN = 3'b011,
    OP_ADD = 3'b100,
    OP_SUB = 3'b110
  } opcode_e;
  parameter int unsigned IAU_OP_SUB_IDX = 1; // sets which bit in the opcode determins the required subtraction. This to reduce the decoding logic.

  // =======================================
  // IAU DPcmd struct
  // =======================================
  typedef struct packed {
    logic lsb_carry; // carry from lsb to msb element
    logic msb_carry; // carry out from msb used for min / max in lsb element
    logic sat_pos;   // positive saturation
    logic sat_neg;   // negative saturation
  } iau_alu_ctrl_t;

  parameter int unsigned IAU_MVM_I16_DW = aic_common_pkg::AIC_PWORD32_MVM_IAU_INT_WIDTH;
  parameter int unsigned IAU_DPU_I16_DW = aic_common_pkg::AIC_PWORD32_IAU_DPU_INT_WIDTH;

  // =======================================
  // IAU DPcmd struct
  // =======================================
  typedef struct packed {
    logic [3:0] src1;
    logic [3:0] src0;
    logic [3:0] dst;
    logic       rfs;
    opcode_e    opcode;
  } iau_dp_cmd_t;
  parameter int unsigned IAU_DP_CMD_DW = $bits(iau_dp_cmd_t);
  parameter int unsigned IAU_DP_CMD_ALIGN = 16;

  // Canonical bypass instruction
  parameter iau_dp_cmd_t CANONICAL_BYPASS_INSTR = '{
      src1  : 4'b0000,
      src0  : 4'b1010,
      dst   : 4'b1000,
      rfs   : 1'b1,
      opcode: OP_MV
  };

  // =======================================
  // IAU CMD block
  // =======================================
  // CMD operation code
  typedef enum logic {
    CMD_OP_EXE = 1'b0,
    CMD_OP_BYP = 1'b1
  } cmd_opcode_e;

  // CMD parameters for datapath program loop
  parameter int unsigned IAU_CMD_START_DW = $clog2(IAU_PRG_MEM_DEPTH);
  parameter int unsigned IAU_CMD_ITER_DW = IAU_PRG_MAX_ITER_BITS;
  parameter int unsigned IAU_CMD_LEN_DW = $clog2(IAU_PRG_MEM_DEPTH);
  parameter int unsigned IAU_CMD_RSVD_DW = 64 - (IAU_CMD_START_DW + IAU_CMD_ITER_DW + IAU_CMD_LEN_DW);

  // =======================================
  // IAU CMD struct
  // =======================================
  parameter int unsigned CMD_NR_FORMATS = 2;
  parameter int CMD_FORMAT_NR_BYTES[CMD_NR_FORMATS] = {int'(8), int'(0)};

  typedef enum logic {
    CMD_FORMAT_EXE = 1'b0,
    CMD_FORMAT_BYP = 1'b1
  } cmd_format_e;
  parameter int unsigned IAU_CMD_FORMAT_DW = $bits(cmd_format_e);

  typedef struct packed {
    logic [IAU_CMD_ITER_DW-1:0]  loop_iter;
    logic [IAU_CMD_RSVD_DW-1:0]  reserved;
    logic [IAU_CMD_LEN_DW-1:0]   loop_len;
    logic [IAU_CMD_START_DW-1:0] loop_start;
  } iau_cmd_t;
  parameter int unsigned IAU_CMD_DW = $bits(iau_cmd_t);

  // =======================================
  // IAU SW DPcmd Bypass
  // =======================================
  // SW DPcmd bypass contains two fields: standard DPcmd and last bit
  parameter int unsigned IAU_SW_DPCMD_NR_FIELDS = 2;
  parameter int unsigned IAU_SW_DPCMD_INSTR_DW = IAU_DP_CMD_DW;
  parameter int unsigned IAU_SW_DPCMD_LAST_DW = 1;

  // Byte align fields of SW DPcmd bypass
  parameter int unsigned IAU_SW_DPCMD_INSTR_LSB_IDX = 0;
  parameter int unsigned IAU_SW_DPCMD_LAST_LSB_IDX = ((IAU_DP_CMD_DW + 7) / 8) * 8;

  // =======================================
  // IAU SW DPcmd Bypass struct
  // =======================================
  typedef struct packed {
    logic [IAU_SW_DPCMD_LAST_DW-1:0]  last;
    logic [IAU_SW_DPCMD_INSTR_DW-1:0] dpcmd;
  } iau_sw_dp_cmd_t;
  parameter int unsigned IAU_SW_DPCMD_DW = $bits(iau_sw_dp_cmd_t);

  // =======================================
  // IAU AXI regions
  // =======================================

  // Indicates the relevant bits in local address space
  parameter int unsigned IAU_AXI_ADDR_CAP = 'h10000;

  // List of AXI subordinates in IAU
  parameter int unsigned IAU_AXI_S_COUNT = 3;
  parameter int unsigned IAU_AXI_S_IDX_CSR = 0;
  parameter int unsigned IAU_AXI_S_IDX_CMD_BLOCK = 1;
  parameter int unsigned IAU_AXI_S_IDX_DPCMD_GEN = 2;
  parameter int unsigned IAU_AXI_S_COUNT_WD = cc_math_pkg::index_width(IAU_AXI_S_COUNT);

  typedef enum logic [IAU_AXI_S_COUNT_WD-1:0] {
    IAU_IDX_CSR   = IAU_AXI_S_COUNT_WD'(IAU_AXI_S_IDX_CSR),
    IAU_IDX_CMDB  = IAU_AXI_S_COUNT_WD'(IAU_AXI_S_IDX_CMD_BLOCK),
    IAU_IDX_DPCMD = IAU_AXI_S_COUNT_WD'(IAU_AXI_S_IDX_DPCMD_GEN)
  } iau_idx_e;

  // Split the local address space evenly among AXI subordinates
  // (address space is in bytes -> 'h4000 = 4096 64-bit rows)
  parameter int unsigned IAU_AXI_ST_ADDR_CSR = 'h0000;
  parameter int unsigned IAU_AXI_ST_ADDR_CMD_BLOCK = 'h1000;
  parameter int unsigned IAU_AXI_ST_ADDR_DPCMD_GEN = 'h8000;
  parameter int unsigned IAU_AXI_ADDR_CAP_CSR = 'h1000;
  parameter int unsigned IAU_AXI_ADDR_CAP_CMD_BLOCK = 'h1000;
  parameter int unsigned IAU_AXI_ADDR_CAP_DPCMD_GEN = 'h8000;

endpackage

`endif  // IAU_PKG_SV
