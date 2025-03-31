package soc_mgmt_seq_pkg;
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  `ifdef APB_VIP
    import svt_apb_uvm_pkg::*;
  `endif

  import soc_mgmt_env_pkg::*;
  import soc_mgmt_common_pkg::*;
  import soc_mgmt_ral_pkg::*;
  // Sequences
  `include "axi_slave_mem_response_sequence.sv"
  `include "axi_simple_reset_sequence.sv"
  `include "axi_null_virtual_sequence.sv"
  // User define sequences/tasks
  `include "soc_mgmt_seq_library.sv"
  `include "apb_seq_lib.sv"

endpackage
