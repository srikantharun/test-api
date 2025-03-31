package ai_core_mvm_seq_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif

  import ai_core_mvm_env_pkg::*;
  import ai_core_mvm_common_pkg::*;
  // Sequences
  `include "axi_master_random_discrete_virtual_sequence.sv"
  `include "axi_slave_mem_response_sequence.sv"
  `include "axi_simple_reset_sequence.sv"
  `include "axi_null_virtual_sequence.sv"
  `include "axi_master_directed_sequence.sv"
  `include "axi_master_random_discrete_sequence.sv"
  `include "axi_master_stream_base_sequence.sv"
  `include "axi_master_zero_delay_sequence.sv"
  `include "axi_slave_mem_zero_delay_sequence.sv"
  `include "axi_slave_mem_delay_sequence.sv"
  // User define sequences/tasks
  `include "ai_core_mvm_seq_library.sv"
  `include "ai_core_mvm_ral_bit_bash_seq.sv"

endpackage
