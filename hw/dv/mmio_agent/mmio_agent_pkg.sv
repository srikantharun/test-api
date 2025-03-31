// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Package File for MMIO Agent
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef MMIO_AGENT_PKG_SV
`define MMIO_AGENT_PKG_SV


package mmio_agent_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  typedef enum { MMIO_TXN, MMIO_REQ, MMIO_RSP, MMIO_RESERVED } mmio_txn_t;
  parameter int unsigned MMIO_INTERNAL_ADDRESS_START   = 'h0800_0000;
  parameter int unsigned MMIO_INTERNAL_ADDRESS_END     = 'h083F_FFFF;
  parameter int unsigned MMIO_INTERNAL_CHIP_OFFSET     = 'h1000_0000;

  // Data for SRAM implementation
  parameter int unsigned AIC_LS_ENV_L1_SRAM_MUX = 4;
  parameter int unsigned AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS = 4;
  parameter int unsigned AIC_LS_ENV_L1_SRAM_WORD_SIZE = 128;
  parameter int unsigned AIC_LS_ENV_L1_BANK_DEPTH = 4096;
  parameter int unsigned AIC_LS_ENV_L1_SRAM_FULL_SIZE = (AIC_LS_ENV_L1_SRAM_WORD_SIZE*AIC_LS_ENV_L1_SRAM_MUX)+(AIC_LS_ENV_L1_SRAM_REDUNDANCY_BITS*2);
  parameter int unsigned AIC_LS_ENV_L1_BANK_PARTITION_DEP = AIC_LS_ENV_L1_BANK_DEPTH/AIC_LS_ENV_L1_SRAM_MUX;
  parameter int unsigned AIC_LS_ENV_L1_BANK_DATA_WIDTH = AIC_LS_ENV_L1_SRAM_WORD_SIZE*AIC_LS_ENV_L1_SRAM_MUX;

  typedef bit[AIC_LS_ENV_L1_BANK_DATA_WIDTH-1:0] l1_data_t;
  typedef bit[AIC_LS_ENV_L1_BANK_DATA_WIDTH/2-1:0] l1_half_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_WORD_SIZE-1:0] l1_quarter_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_FULL_SIZE-1:0] l1_phys_data_t;
  typedef bit[AIC_LS_ENV_L1_SRAM_WORD_SIZE-1:0] l1_phys_word_t;

  //include necessary files for mmio package
  //Driver is not implememted yet as it has no use case for first usage in verif_tb/ai_core_ls
  `include "mmio_config.sv"
  `include "mmio_item.sv"
  `include "mmio_monitor.sv"
  `include "mmio_scoreboard.sv"
  `include "mmio_agent.sv"

endpackage : mmio_agent_pkg

`endif // MMIO_AGENT_PKG_SV

