// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AIC_DMC Package
// Owner: Rafael Frangulyan Polyak <rafael.frangulian@axelera.ai>

package aic_ls_agent_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import aic_common_pkg::*;
  import dmc_pkg::*;
  
  //Defines///////////////////////////
  localparam CID_WIDTH         = aic_common_pkg::AIC_CID_WIDTH;
  localparam VA_BASE_LSB       = aic_common_pkg::AIC_VA_BASE_LSB;
  localparam OBS_DW            = aic_common_pkg::AIC_DMC_OBS_DW;
  localparam HP_AXI_ADDR_WIDTH = aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH;
  localparam IRQ_W             = dmc_pkg::DMC_IRQ_W;

  //all the devices' address space in LS
  typedef enum {
    MIFD0      = 'h0_0000,
    MIFD1      = 'h1_0000,
    MIFD2      = 'h2_0000,
    MIFDW      = 'h3_0000,
    MODR       = 'h4_0000,
    DIFD0      = 'h5_0000,
    DIFD1      = 'h6_0000,
    DODR       = 'h7_0000,
    TOKEN_MGR  = 'h8_0000
  } aic_ls_device_t;

  typedef enum {
    MVM_IFD0  = 0,
    MVM_IFD1  = 1,
    MVM_IFD2  = 2,
    MVM_IFDW  = 3,
    DWPU_IFD0 = 4,
    DWPU_IFD1 = 5,
    MVM_ODR   = 6,
    DWPU_ODR  = 7,
    TKN_MGR   = 8
  } aic_ls_device_index_t;

  typedef struct packed {
    bit[ 6:0] reserved_b; // reserved bits
    bit       vector_mode; // affects int8/int16 formatting
    bit[ 7:0] cmd_format;
    bit[15:0] token_consumer;
    bit[15:0] token_producer;
    bit[ 7:0] reserved_a; // reserved bits
    bit[ 7:0] triggers;  // doesn't affect inner works
  } command_header_t;

  parameter int unsigned AIC_LS_ENV_DMC_NUM_DEVICE        = 8;
  parameter int unsigned AIC_LS_ENV_IFD_NUM_DEVICE        = 6;
  parameter int unsigned AIC_LS_ENV_ODR_NUM_DEVICE        = 2;
  parameter int unsigned AIC_LS_ENV_NUM_DEVICE            = AIC_LS_ENV_DMC_NUM_DEVICE;
  parameter int unsigned AIC_LS_ENV_AXI_CFG_ADDR_W        = 36;
  parameter int unsigned AIC_LS_ENV_AXI_CFG_DATA_W        = 64;
  parameter int unsigned AIC_LS_ENV_AXI_HP_ADDR_W         = 36;
  parameter int unsigned AIC_LS_ENV_AXI_HP_DATA_W         = 512;
  parameter int unsigned AIC_LS_ENV_AXI_STREAM_DATA_W     = 512;
  parameter int unsigned AIC_LS_ENV_CMDBLK_CSR_OFFSET     = 'h200_0000;
  parameter int unsigned AIC_LS_ENV_CMDBLK_FIFO_OFFSET    = 'h280_0000;
  parameter int unsigned AIC_LS_ENV_DESCMEM_OFFSET        = 'h300_0000;
  parameter int unsigned AIC_LS_ENV_DEVICE_OFFSET         = 'h1_0000;
  parameter int unsigned AIC_LS_ENV_L1_ADDR_START         = 'h00_0000;
  parameter int unsigned AIC_LS_ENV_L1_ADDR_END           = 'h3F_FFFF;
  parameter int unsigned AIC_LS_ENV_L1_MEM_OFFSET        = 'h800_0000;
  parameter int unsigned AIC_LS_ENV_L1_NUM_BANKS          = 16;
  parameter int unsigned AIC_LS_ENV_L1_NUM_SUB_BANKS      = 4;
  parameter int unsigned AIC_LS_ENV_L1_BANK_DEPTH         = 4096;
  parameter int unsigned AIC_LS_ENV_DMC_DM_DEPTH          = 128; // data/instruction memory depth
  parameter int unsigned AIC_LS_ENV_DMC_CSR_DEPTH         = 'h50; // last CSR address
  parameter int unsigned AIC_LS_ENV_L1_MEM_SIZE           = 'h40_0000; // 4MB
  parameter int unsigned AIC_LS_ENV_L1_BANK_SIZE          = AIC_LS_ENV_L1_MEM_SIZE/AIC_LS_ENV_L1_NUM_BANKS; // 4MB / 16 banks
  parameter int unsigned AIC_LS_ENV_CID_ADDR_OFFSET       = 'h1000_0000;
  parameter string AIC_LS_DMC_DEVICE_NAME[AIC_LS_ENV_NUM_DEVICE] = {"m_ifd0", "m_ifd1", "m_ifd2", "m_ifdw", "d_ifd0", "d_ifd1", "m_odr", "d_odr"};
  parameter string AIC_LS_DMC_DEVICE_NAME_DUT[AIC_LS_ENV_NUM_DEVICE] = {"m_ifd0", "m_ifd1", "m_ifd2", "m_ifdw", "d_ifd0", "d_ifd1", "m_odr", "d_odr"};  // they are identical reight now
  parameter aic_ls_device_t AIC_LS_DMC_IFD_DEVICE[AIC_LS_ENV_IFD_NUM_DEVICE] = { MIFD0, MIFD1, MIFD2, MIFDW, DIFD0, DIFD1};
  parameter aic_ls_device_t AIC_LS_DMC_ODR_DEVICE[AIC_LS_ENV_ODR_NUM_DEVICE] = { MODR, DODR};
  parameter int unsigned AIC_LS_ENV_L2_NUM_BANKS       = 4;
  parameter int unsigned AIC_LS_ENV_L2_START_ADDRESSES[AIC_LS_ENV_L2_NUM_BANKS] = { 'h0800_0000, 'h0880_0000, 'h0900_0000, 'h0980_0000};
  parameter int unsigned AIC_LS_ENV_L2_START_ADDRESS = 'h0800_0000;
  parameter int unsigned AIC_LS_ENV_L2_END_ADDRESS   = 'h09FF_FFFF;
  parameter int unsigned AIC_LS_ENV_L2_MEM_BANK_SIZE_MB = 8;
  parameter int unsigned AIC_LS_ENV_L2_MEM_SIZE_BYTES = 32 * 1024 * 1024; // 32 MB
  parameter string AIC_LS_ENV_L1_MEM_ROOT_PATH = "hdl_top.dut.u_aic_ls.u_l1.u_l1_mem";
  parameter int AIC_LS_ENV_AXI2MMIO_NUM_DEVICE = 2;
  parameter string AIC_LS_DMC_AXI2MMIO_DEVICE_NAME[AIC_LS_ENV_AXI2MMIO_NUM_DEVICE] = {"axi_wr", "axi_rd"};
  parameter int unsigned DEF_MEM_WRITE_LEN = 8; 
  parameter int unsigned DMC_CMD_0_WRITE_LEN = 4;  //def_based
  parameter int unsigned DMC_CMD_1_WRITE_LEN = 2;  //linear
  parameter int unsigned DMC_CMD_2_WRITE_LEN = 9;  //3d fallback
  parameter int unsigned DMC_CMD_3_WRITE_LEN = 5;  //offset def based
  parameter int unsigned DMC_CMD_4_WRITE_LEN = 11; //4d fallback
  parameter int unsigned AIC_LS_ENV_RINGBUFF_SIZE_GRANULARITY = 4096; // based on python model
  parameter int unsigned AIC_LS_ENV_RINGBUFF_MAX_SIZE = 'h40_0000; // based on python model

  // Data relevant to token connections
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_LENGTH                = 16; // 16 total bits
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_DMC_NUM               = AIC_LS_ENV_DMC_NUM_DEVICE - 1; // all the devices, minus current one
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_LEADING_CONN_NUM      = 1; // sw
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_TRAILING_CONN_NUM     = 2; // hp_dma_0, hp_dma_1
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_OTHER_CONN_NUM        = AIC_LS_ENV_TOKEN_VECTOR_LEADING_CONN_NUM + AIC_LS_ENV_TOKEN_VECTOR_TRAILING_CONN_NUM; // sw, acd, hp_dma_0, hp_dma_1
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_TOTAL_CONN_NUM        = AIC_LS_ENV_TOKEN_VECTOR_DMC_NUM + AIC_LS_ENV_TOKEN_VECTOR_OTHER_CONN_NUM; // 7+4=11
  parameter int unsigned AIC_LS_ENV_TOKEN_VECTOR_RESERVED_BITS         = AIC_LS_ENV_TOKEN_VECTOR_LENGTH - AIC_LS_ENV_TOKEN_VECTOR_TOTAL_CONN_NUM; // 16-11=5
  parameter string AIC_LS_ENV_TOKEN_VECTOR_CONNECTIONS[AIC_LS_ENV_TOKEN_VECTOR_TOTAL_CONN_NUM+1] = {"sw", "m_ifd0", "m_ifd1", "m_ifd2", "m_ifdw", "m_odr", "d_ifd0", "d_ifd1", "d_odr", "hp_dma_0", "hp_dma_1"};
  parameter string AIC_LS_ENV_TOKEN_VECTOR_DMC_CONNECTIONS[AIC_LS_ENV_DMC_NUM_DEVICE] = {"m_ifd0", "m_ifd1", "m_ifd2", "m_ifdw", "m_odr", "d_ifd0", "d_ifd1", "d_odr"};
  parameter string AIC_LS_ENV_TOKEN_VECTOR_OTHER_CONNECTIONS[AIC_LS_ENV_TOKEN_VECTOR_OTHER_CONN_NUM] = {"sw", "hp_dma_0", "hp_dma_1"};

  // Data relevant to RVV connections
  parameter int unsigned AIC_LS_ENV_RVV_CONNECTIONS = 8;
  parameter int unsigned AIC_LS_ENV_RVV_DATA_WIDTH = 128;
  parameter int unsigned AIC_LS_ENV_RVV_ADDR_WIDTH = 22;
  parameter int unsigned AIC_LS_ENV_RVV_WBE_WIDTH = (AIC_LS_ENV_RVV_DATA_WIDTH + 7) / 8;

  //For ai_core_top
  parameter string AI_CORE_TOP_ENV_L1_MEM_ROOT_PATH = "hdl_top.dut.u_ai_core_p.u_ai_core.u_aic_ls.u_l1.u_l1_mem";
  parameter int unsigned AI_CORE0_TOP_ENV_CMDBLK_FIFO_OFFSET = 'h1280_0000;

  // Data for SRAM implementation
  parameter int unsigned AIC_LS_ENV_L1_SRAM_MUX = 4;
  parameter int unsigned AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS = 4;
  parameter int unsigned AIC_LS_ENV_L1_SRAM_WORD_SIZE = 128;
  parameter int unsigned AIC_LS_ENV_L1_SRAM_FULL_SIZE = (AIC_LS_ENV_L1_SRAM_WORD_SIZE*AIC_LS_ENV_L1_SRAM_MUX)+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2);
  parameter int unsigned AIC_LS_ENV_L1_BANK_PARTITION_DEP = AIC_LS_ENV_L1_BANK_DEPTH/AIC_LS_ENV_L1_SRAM_MUX;

  
  `include "aic_ls_agent_cfg.svh"
  `include "aic_ls_seq_item.svh"
  `include "aic_ls_monitor.svh"
  `include "aic_ls_agent.svh"
endpackage
