package ai_core_top_seq_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `include "ai_core_top_tb_define.sv"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import svt_apb_uvm_pkg::*;
  `endif

  import ai_core_top_env_pkg::*;
  // Sequences
  `include "ai_core_top_seq_library.sv"
  `include "ai_core_top_axi_null_virtual_sequence.sv"
  `include "ai_core_top_axi_master_directed_sequence.sv"
  `include "ai_core_top_axi_simple_reset_sequence.sv"
  `include "apb_simple_reset_sequence.svh"
  `include "ai_core_top_apb_seq_library.svh"
  `include "ai_core_top_axi_slave_mem_response_sequence.sv"

endpackage
