// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IFD ODR Address Generator Package
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

package dmc_addr_gen_agent_pkg;

  import uvm_pkg::*;
  import aic_common_pkg::*;
  `include "uvm_macros.svh"

  typedef enum { CMDFORMAT_DEF_BASED, CMDFORMAT_LINEAR, CMDFORMAT_3DIM_FALLBACK, CMDFORMAT_OFFSET_BASED, CMDFORMAT_4DIM_FALLBACK } addr_gen_cmdformat_t;
  typedef enum bit[1:0] {NO_COMP, FVC, ZRLE, INT4} compression_scheme_t;
  typedef enum bit[1:0] { INVALID_STREAM_HEADER, INVALID_COMP_SIZE, INVALID_UNCOMP_SIZE } compression_error_t;
  typedef bit[63:0] addr_gen_data_width_t;
  typedef bit[63:0] cfg_data_t;
  typedef bit[31:0] mem_baseaddr_t;
  typedef bit[aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] axis_data_t;

  // Removed dependency on RTL code by simply following specification
  typedef struct packed {
    // word 9
    bit       decomp_en;       // decomp_en is the last bit - 640
    bit[ 7:0] dummy_byte_w9_2; // dummy byte in w9
    bit[ 7:0] outer_stride_d;  // parameter AG_OUTER_STR_D_LSB = 624;
    bit[15:0] outer_length_d;  // parameter AG_OUTER_LEN_D_LSB = 608;
    bit[ 7:0] dummy_byte_w9;   // dummy byte in w9
    bit[ 7:0] inner_stride_d;  // parameter AG_INNER_STR_D_LSB = 592;
    bit[15:0] inner_length_d;  // parameter AG_INNER_LEN_D_LSB = 576;
    // word 8
    bit[31:0] mem_stride_d;    // parameter AG_MEM_STRIDE_D_LSB = 544;
    bit[15:0] dim_width_d;     // parameter AG_DIM_W_D_LSB = 528;
    bit[15:0] dim_offset_d;    // parameter AG_DIM_OFF_D_LSB = 512;
    //word 7
    bit[ 7:0] outer_stride_c;  // parameter AG_OUTER_STR_C_LSB = 504;
    bit[ 7:0] inner_stride_c;  // parameter AG_INNER_STR_C_LSB = 496;
    bit[ 7:0] outer_stride_b;  // parameter AG_OUTER_STR_B_LSB = 488;
    bit[ 7:0] inner_stride_b;  // parameter AG_INNER_STR_B_LSB = 480;
    bit[15:0] outer_length_b;  // parameter AG_OUTER_LEN_B_LSB = 464;
    bit[15:0] inner_length_b;  // parameter AG_INNER_LEN_B_LSB = 448;
    //word 6
    bit[15:0] outer_length_c;  // parameter AG_OUTER_LEN_C_LSB = 432;
    bit[ 7:0] outer_stride_a;  // parameter AG_OUTER_STR_A_LSB = 424;
    bit[ 7:0] inner_stride_a;  // parameter AG_INNER_STR_A_LSB = 416;
    bit[15:0] outer_length_a;  // parameter AG_OUTER_LEN_A_LSB = 400;
    bit[15:0] inner_length_a;  // parameter AG_INNER_LEN_A_LSB = 384;
    //word 5
    bit[31:0] mem_stride_c;    // parameter AG_MEM_STRIDE_C_LSB = 352;
    bit[15:0] dim_width_c;     // parameter AG_DIM_W_C_LSB = 336;
    bit[15:0] dim_offset_c;    // parameter AG_DIM_OFF_C_LSB = 320;
    //word 4
    bit[31:0] mem_stride_b;    // parameter AG_MEM_STRIDE_B_LSB = 288;
    bit[15:0] dim_width_b;     // parameter AG_DIM_W_B_LSB = 272;
    bit[15:0] dim_offset_b;    // parameter AG_DIM_OFF_B_LSB = 256;
    //word 3
    bit[31:0] mem_stride_a;    // parameter AG_MEM_STRIDE_A_LSB = 224;
    bit[15:0] dim_width_a;     // parameter AG_DIM_W_A_LSB = 208;
    bit[15:0] dim_offset_a;    // parameter AG_DIM_OFF_A_LSB = 192;
    //word 2
    bit[31:0] mem_bsize;        // parameter AG_MEM_BSIZE_LSB = 160:191;
    bit[ 7:0] mask_end;       // parameter AG_MSK_END_LSB = 152:159;
    bit[ 7:0] mask_start;     // parameter AG_MSK_START_LSB = 144:151;
    bit[15:0] inner_length_c;  // parameter AG_INNER_LEN_C_LSB = 128:143;
    //word 1
    bit       format;        // parameter AG_PAD_MODE_EDGE_LSB = 127;  // settings bit 4
    bit       pad_mode;        // parameter AG_PAD_MODE_EDGE_LSB = 126;  // settings bit 4
    bit[ 1:0] vtrsp_mode;      // parameter AG_VTRSP_EN_LSB = 124:125;  // settings bit 2
    bit[ 1:0] vect_dim;        // parameter AG_VECT_DIM_LSB = 122:123;  // settings bit 1:0
    bit[ 1:0] num_dim;        // settings bit 120:121
    bit[23:0] ring_buff_size; // parameter AG_RING_BUFFER_SIZE_LSB = 96;
    bit[31:0] mem_offset;     // parameter AG_MEM_OFFSET_LSB = 64:95;
    //word 0
    bit[15:0] intra_pad_val;  // parameter AG_PAD_VAL_LSB = 48:63;
    bit[15:0] pad_val;        // parameter AG_PAD_VAL_LSB = 32:47;
    mem_baseaddr_t mem_baseaddr;   // parameter AG_MEM_BASE_LSB = 0:31;
  } addr_gen_cmd_t;

  typedef struct packed {
    bit [31:0] dpc_addr;
    bit [63:0] dpc_msk;
    bit dpc_format;
    bit dpc_config; // called that way, but for now it's just vector_mode
    bit dpc_pad;
    bit dpc_last;
    bit [15:0] dpc_pad_val;
    bit [15:0] dpc_intra_pad_val;
    bit err_addr_out_of_range;
  } dpc_cmd_t;

  typedef struct packed {
    bit [495:0] unused_bytes;
    bit [15:0] stream_length;
  } decomp_stream_header_t;

  typedef struct packed {
    bit [447:0] unused_bytes;   
    bit [15:0] compressed_stream_length;
    bit [15:0] uncompressed_stream_length;
    bit [5:0]  unused_bits;
    compression_scheme_t compression_scheme;
  } decomp_substream_header_t;

  parameter int unsigned PWORD_ALIGN_SIZE = 64;
  parameter int unsigned CMDB_FIFO_DEPTH  = 16;
  parameter int unsigned MIN_FVC_UNCOMPRESSED_NUM  = 12;
  parameter int unsigned MIN_FVC_COMPRESSED_NUM  = 6;
  parameter int unsigned MAX_STREAM_LENGTH  = 4096;

  `include "dmc_addr_gen_cfg.svh"
  `include "dmc_addr_gen_seq_item.svh"
  `include "ifdw_decompression_seq_item.svh"
  `include "dmc_addr_gen_monitor.svh"
  `include "dmc_addr_gen_driver.svh"
  `include "dmc_addr_gen_sequencer.svh"
  `include "dmc_addr_gen_agent.svh"
endpackage
