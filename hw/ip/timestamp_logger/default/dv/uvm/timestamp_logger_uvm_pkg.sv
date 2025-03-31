// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

package timestamp_logger_uvm_pkg;

  import tb_axi_pkg::*;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import axe_uvm_resource_allocator_pkg::*;
  import axe_uvm_scoreboard_pkg::*;
  import axe_uvm_numeric_pkg::*;

  // Configuration
  `include "timestamp_logger_env_cfg.svh"

  // Agent
  `include "timestamp_logger_event_item.svh"
  `include "timestamp_logger_cfg_item.svh"

  `include "timestamp_logger_model.svh"

  `include "timestamp_logger_event_drv.svh"
  `include "timestamp_logger_event_sqr.svh"
  `include "timestamp_logger_event_mon.svh"

  `include "timestamp_logger_cfg_drv.svh"
  `include "timestamp_logger_cfg_sqr.svh"

  `include "timestamp_logger_vseq.svh"

  `include "timestamp_logger_agent.svh"

  // Env
  `include "timestamp_logger_env.svh"

  // Tests
  `include "timestamp_logger_test_lib.svh"

endpackage : timestamp_logger_uvm_pkg
