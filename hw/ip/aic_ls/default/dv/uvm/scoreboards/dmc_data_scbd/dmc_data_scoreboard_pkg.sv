// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IFD ODR Data Scoreboard Package
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

package dmc_data_scoreboard_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_ls_csr_ral_pkg::*;
  import l1_pkg::*;
  import aic_common_pkg::*;
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import dmc_addr_gen_agent_pkg::*;
  import dmc_addr_gen_ref_model_pkg::*;

  parameter int unsigned  DATA_SB_AI_CORE_BASE_ADDR  = 'h1000_0000;
  parameter int unsigned  DATA_SB_AI_CORE_CID        = 1;
  parameter int unsigned  DATA_SB_L1_START_OFFSET    = 'h0800_0000;
  parameter int unsigned  DATA_SB_L1_END_OFFSET      = 'h083F_FFFF;
  parameter int unsigned  DATA_SB_L1_RAM_DW          = 256; // 4096 array size x 256 bits of data = 128Kbytes
  parameter int unsigned  DATA_SB_L1_RAM_ARRAY_SIZE  = 4096; // 4096 array size x 256 bits of data = 128Kbytes
  parameter string DATA_SB_TOP_L1_MEM_ROOT_PATH   = "hdl_top.dut.u_ai_core.u_aic_ls_p.u_aic_ls.u_l1.u_l1_mem";
  parameter string DATA_SB_L1_MEM_ROOT_PATH   = "hdl_top.dut.u_aic_ls.u_l1.u_l1_mem";


  // Data for SRAM implementation
  parameter int unsigned DATA_SB_L1_SRAM_MUX = 4;
  parameter int unsigned DATA_SB_L1_SRAM_REDUNDANCY_BITS = 4;
  parameter int unsigned DATA_SB_L1_SRAM_WORD_SIZE = 128;
  parameter int unsigned DATA_SB_L1_SRAM_FULL_SIZE = (DATA_SB_L1_SRAM_WORD_SIZE*DATA_SB_L1_SRAM_MUX)+(DATA_SB_L1_SRAM_REDUNDANCY_BITS*2);
  parameter int unsigned DATA_SB_L1_BANK_PARTITION_DEP = DATA_SB_L1_RAM_ARRAY_SIZE/DATA_SB_L1_SRAM_MUX;
  parameter int unsigned DATA_SB_L1_DATA_W         = 512;


  typedef enum { WRITE_INTRA_PAD, NORMAL_DATA, DROP_DATA, CASTED_DATA } odr_write_t;
  typedef struct {
    bit[35:0] addr;
    odr_write_t write_type;
    bit skip;
  } data_sb_mem_t;

  typedef bit[AIC_HT_AXI_ADDR_WIDTH-1:0]   data_sb_axis_addr_t;
  typedef bit[AIC_DMC_PWORD_SIZE/2-1:0]   data_sb_axis_half_addr_t;
  typedef bit[AIC_HT_AXI_DATA_WIDTH-1:0]   data_sb_axis_data_t;
  typedef bit[DATA_SB_L1_SRAM_FULL_SIZE-1:0]   phys_data_sb_axis_data_t;
  typedef bit[AIC_HT_AXI_DATA_WIDTH/2-1:0]   data_sb_axis_half_data_t;
  typedef bit[AIC_HT_AXI_DATA_WIDTH/4-1:0] data_sb_axis_quarter_data_t; // memory blocks are divided into blocks of 128 bits of data

  // types required for ifdw transpose
  typedef data_sb_axis_data_t sb_axis_data_q_t[$];

  `include "dmc_data_scoreboard.svh"
endpackage
