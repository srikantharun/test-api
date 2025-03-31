// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : ana.stoisavljevic@axelera.ai  *** //
package pve_fabric_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  // Environment and environment Configurations
  `include "fabric_csl_tb_define.sv"
  `include "pve_fabric_svt_axi_system_configuration.sv"
  `include "pve_fabric_configuration.sv"
  `include "axi_virtual_sequencer.sv"

  // Environment configuration and environment
  `include "fabric_csl_env.sv"

  // Sequences
  // User define sequences/tasks
  `include "common_seq_library.svh"
  `include "axi_simple_reset_sequence.sv"
  `include "axi_slave_mem_response_sequence.sv"

  //Functional tests
  `include "fabric_csl_base_test.sv"
  `include "fabric_csl_smoke_test.sv"
  `include "fabric_csl_atomic_test.sv"
  `include "fabric_csl_connectivity_test.sv"
  `include "fabric_csl_cluster_l1_test.sv"
  `include "fabric_csl_exclusive_axi_test.sv"
  `include "fabric_csl_random_test.sv"
  `include "fabric_csl_outstanding_test.sv"
  `include "fabric_csl_read_interleave_test.sv"
  
endpackage : pve_fabric_uvm_pkg

