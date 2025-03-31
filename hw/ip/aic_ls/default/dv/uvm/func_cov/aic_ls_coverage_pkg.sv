// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Function Coverage package
//
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>
// -------------------------------------------------

package aic_ls_coverage_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  `include "svt_axi_common_defines.svi"
`endif
  import v_utils_pkg::*;
  import aic_ls_agent_pkg::*;
  import token_agent_uvm_pkg::*;
  import dmc_addr_gen_agent_pkg::*;
  import mmio_agent_pkg::*;
  import mmio_pkg::*;

  typedef struct packed {
    bit[7:0]  reserved;
    bit[7:0]  cmd_format;
    bit[15:0] token_consumer;
    bit[15:0] token_producer;
    bit[15:0] id;
  } cmd_header_t;

  parameter int unsigned AIC_DMC_COV_CMDB_FIFO_DEPTH                                    = 16;
  parameter int unsigned AIC_DMC_COV_MMIO_ADDR_WIDTH                                    = AIC_LS_ENV_RVV_ADDR_WIDTH; // CORE Start address
  parameter int unsigned AIC_DMC_COV_L1_ADDR_START                                      = AIC_LS_ENV_L1_ADDR_START;
  parameter int unsigned AIC_DMC_COV_L1_ADDR_END                                        = AIC_LS_ENV_L1_ADDR_END;
  parameter int unsigned AIC_DMC_COV_L1_NUM_BANKS                                       = AIC_LS_ENV_L1_NUM_BANKS;
  parameter int unsigned AIC_DMC_COV_L1_NUM_SUB_BANKS                                   = AIC_LS_ENV_L1_NUM_SUB_BANKS;
  parameter int unsigned AIC_DMC_COV_DMC_NUM_DEVICE                                     = AIC_LS_ENV_DMC_NUM_DEVICE;
  parameter int unsigned AIC_DMC_COV_RVV_NUM_PORTS                                      = AIC_LS_ENV_RVV_CONNECTIONS;
  parameter int unsigned AIC_DMC_COV_IFD_NUM_DEVICE                                     = AIC_LS_ENV_IFD_NUM_DEVICE;
  parameter int unsigned AIC_DMC_COV_ODR_NUM_DEVICE                                     = AIC_LS_ENV_ODR_NUM_DEVICE;
  parameter int unsigned AIC_DMC_COV_AXI2MMIO_NUM_DEVICE                                = AIC_LS_ENV_AXI2MMIO_NUM_DEVICE;
  parameter int unsigned AIC_DMC_COV_AXI_NUM_DEVICE                                     = AIC_DMC_COV_DMC_NUM_DEVICE+AIC_DMC_COV_AXI2MMIO_NUM_DEVICE;
  parameter int unsigned AIC_DMC_COV_TOTAL_NUM_DEVICE                                   = AIC_DMC_COV_AXI_NUM_DEVICE+AIC_DMC_COV_RVV_NUM_PORTS;
  parameter string AIC_DMC_COV_DEVICE_NAME[AIC_DMC_COV_DMC_NUM_DEVICE]                  = AIC_LS_DMC_DEVICE_NAME;
  parameter string AIC_DMC_COV_AXI2MMIO_DEVICE_NAME[AIC_DMC_COV_AXI2MMIO_NUM_DEVICE]    = AIC_LS_DMC_AXI2MMIO_DEVICE_NAME;
  parameter int unsigned AIC_DMC_COV_RINGBUFF_SIZE_GRANULARITY                          = AIC_LS_ENV_RINGBUFF_SIZE_GRANULARITY; // based on python model
  
  `include "aic_ls_dmc_ag_coverage.svh"
  `include "aic_ls_dmc_dpc_coverage.svh"
  `include "aic_ls_l1_mmio_coverage.svh"
  `include "aic_ls_reg_coverage.svh"
  `include "aic_ls_compression_scheme_coverage.svh"
  `include "aic_ls_coverage.svh"

endpackage : aic_ls_coverage_pkg
