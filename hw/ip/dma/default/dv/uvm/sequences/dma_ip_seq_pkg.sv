package dma_ip_seq_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif

  import dma_ip_env_pkg::*;
  import dma_ip_common_pkg::*;

  // User define sequences/tasks
  `include "dma_ip_seq_library.sv"

  // Sequences
//  `include "axi_simple_reset_sequence.sv"
  `include "axi_master_directed_sequence.sv"
  `include "axi_slave_mem_response_sequence.sv"
//  `include "axi_master_random_discrete_sequence.sv"
//  `include "axi_master_stream_base_sequence.sv"
//  `include "axi_master_zero_delay_sequence.sv"
//  `include "axi_slave_mem_zero_delay_sequence.sv"
//  `include "axi_slave_mem_delay_sequence.sv"

//  `include "ai_core_mvm_ral_bit_bash_seq.sv"

endpackage
