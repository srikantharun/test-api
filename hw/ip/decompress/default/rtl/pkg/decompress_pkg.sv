// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Decompression package
// Owner: Spyridoula Koumousi <koumousi.spyridoula@axelera.ai>

`ifndef DECOMPRESS_PACKAGE_SV
`define DECOMPRESS_PACKAGE_SV

package decompress_pkg;

  // =====================================================
  // Parameter definitions
  // =====================================================
  parameter int unsigned DECOMP_PWORD_SIZE = unsigned'(aic_common_pkg::AIC_PWORD_SIZE); // elements per PWORD (64)
  parameter int DECOMP_PWORD_WIDTH = aic_common_pkg::AIC_PWORD_WIDTH;

  parameter int DECOMP_DW = DECOMP_PWORD_WIDTH;
  parameter int DECOMP_MASK_BIT_WIDTH = DECOMP_PWORD_SIZE;

  parameter int DECOMP_CMD_DEPTH = 4;  // Number of instructions that can be pipelined
  parameter int DECOMP_STREAM_FIFO_DEPTH = 2;  // Number of spill pipeline registers
  parameter int unsigned DECOMP_NUM_BUF = 5;  // Number of compressed data buffers
  parameter int unsigned DECOMP_BYTE_CNT_WRAP = DECOMP_NUM_BUF * DECOMP_PWORD_SIZE;//Wrap around at byte 320
  parameter int DECOMP_NUM_SLICES = 16;  // Number of mask computation chunks
  parameter int DECOMP_SLICE_DECOMP_DW = DECOMP_DW / DECOMP_NUM_SLICES;  // Slice data-width
  parameter int DECOMP_SLICE_MW = DECOMP_MASK_BIT_WIDTH / DECOMP_NUM_SLICES;  // Slice mask-width


  // =====================================================
  // Type definitions
  // =====================================================
  typedef enum logic [3:0] {
    ST_IDLE       = 4'b0000,
    ST_HEADER     = 4'b0001,
    ST_SCHEME     = 4'b0010,
    ST_FVC_INIT   = 4'b0011,
    ST_FVC_DECOMP = 4'b0100,
    ST_FVC_DRAIN  = 4'b0101,
    ST_ZRLE       = 4'b0110,
    ST_NO_COMP    = 4'b0111,
    ST_BYPASS     = 4'b1000,
    ST_INT4       = 4'b1001
  } state_t;

  typedef enum logic [1:0] {
    NO_COMP = 2'b00,
    FVC     = 2'b01,
    ZRLE    = 2'b10,
    INT4    = 2'b11
  } scheme_t;

  typedef struct packed {
    logic          valid;
    logic          ready;
    logic [DECOMP_DW-1:0] data;
    logic          last;
  } axis_t;

  typedef struct packed {
    logic                      valid;
    logic                      ready;
    logic [DECOMP_DW-1:0]             data;
    logic [DECOMP_MASK_BIT_WIDTH-1:0] mask;
    logic                      last;
  } comp_axis_t;

  // =====================================================
  // Functions
  // =====================================================

  function automatic logic [2:0] mask_bitcount(logic [3:0] mask);
    logic [2:0] ret_mask_bitcount = '0;

    foreach (mask[idx]) begin
      ret_mask_bitcount += mask[idx];
    end
    return ret_mask_bitcount;

  endfunction

endpackage
`endif  //DECOMPRESS_PACKAGE_SV
