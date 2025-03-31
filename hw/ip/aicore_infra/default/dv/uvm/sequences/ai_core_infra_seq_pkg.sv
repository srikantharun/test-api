package ai_core_infra_seq_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `include "../env/ai_core_infra_tb_define.svh"
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import ai_core_infra_uvm_pkg::*;
  // Sequences

  `include "axi_simple_reset_sequence.svh"
  `include "axi_slave_mem_response_sequence.svh"
  `include "axi_seq_library.svh"

endpackage
