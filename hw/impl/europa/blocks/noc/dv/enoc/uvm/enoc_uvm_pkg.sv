// *************************************************************************** //
// *** (C) Copyright Axelera AI 2024                                       *** //
// *** All Rights Reserved                                                 *** //
// *** Axelera AI Confidential                                             *** //
// *** Owner : srinivas.prakash@axelera.ai                                 *** //
// *************************************************************************** //
// Description : This pkg is the collection of all the svt_vip dependencies    //
//               and uvm components to build ENOC TB                           //
// *************************************************************************** //


`include "enoc_tb_intf.sv"

package enoc_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

  // Misc files
  `include "enoc_tb_macros.svh"
  `include "warning_catcher.sv"

  // Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.sv"
  `include "cust_svt_apb_system_configuration.sv"

  // UVM Components
  `include "axi_virtual_sequencer.sv"
  //`include "enoc_coverage_define.svh"
  //`include "enoc_coverage.sv"
  //`include "enoc_scoreboard.sv"


  // Environment configuration and environment
  `include "enoc_env_cfg.sv"
  `include "enoc_env.sv"

  // Sequences
  `include "axi_slave_mem_response_sequence.sv"

  // User define sequences
  `include "axi_simple_reset_sequence.sv"
  `include "enoc_seq_lib.sv"

  //Functional tests
  `include "enoc_base_test.sv"
  `include "enoc_smoke_test.sv"
  `include "enoc_bw_utilization_test.sv"
  `include "enoc_exclusives_test.sv"
  
endpackage : enoc_uvm_pkg
