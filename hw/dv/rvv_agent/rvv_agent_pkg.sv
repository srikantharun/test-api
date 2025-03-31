// (C) Copyright Axelera AI 202
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Package File for RVV Agent
// Owner: Rafael Frangulyan Polyak <rafael.frangulian@axelera.ai>

`ifndef RVV_AGENT_PKG_SV
`define RVV_AGENT_PKG_SV


package rvv_agent_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import mmio_agent_pkg::*;
  import l1_pkg::*;
  import aic_common_pkg::*;
  import aic_ls_pkg::*;

  typedef enum { RVV_TXN, RVV_REQ, RVV_RSP, RVV_RESERVED } rvv_txn_t;
  parameter int unsigned RVV_INTERNAL_ADDRESS_START   = 'h0800_0000;
  parameter int unsigned RVV_INTERNAL_ADDRESS_END     = 'h083F_FFFF;
  parameter int unsigned RVV_INTERNAL_CHIP_OFFSET     = 'h1000_0000;

  //include necessary files for rvv package
  `include "rvv_config.svh"
  `include "rvv_seq_item.svh"
  `include "rvv_sequencer.svh"
  `include "rvv_sequence.svh"
  `include "rvv_driver.svh"
  `include "rvv_monitor.svh"
  `include "rvv_agent.svh"

endpackage : rvv_agent_pkg

`endif // RVV_AGENT_PKG_SV

