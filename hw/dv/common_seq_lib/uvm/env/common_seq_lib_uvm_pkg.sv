// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

package common_seq_lib_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;

  // Environment and environment Configurations
  `include "common_seq_lib_tb_define.sv"
  `include "cust_svt_axi_system_configuration.sv"
  `include "axi_virtual_sequencer.sv"

  // Environment configuration and environment
  `include "common_seq_lib_env.sv"

  // Sequences
  // User define sequences/tasks
  `include "common_seq_library.svh"
  `include "axi_simple_reset_sequence.sv"
  `include "axi_slave_mem_response_sequence.sv"

endpackage : common_seq_lib_uvm_pkg

