package soc_mgmt_test_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  `ifdef APB_VIP
    import svt_apb_uvm_pkg::*;
  `endif

  import soc_mgmt_common_pkg::*;
  import soc_mgmt_ral_pkg::*;
  import soc_mgmt_seq_pkg::*;
  import soc_mgmt_env_pkg::*;


  `include "cust_svt_axi_master_transaction.sv"

  `include "soc_mgmt_base_test.sv"
  `include "soc_mgmt_memory_map_axi_test.sv"
  `include "soc_mgmt_memory_map_apb_test.sv"
  `include "soc_mgmt_clkgen_test.sv"

endpackage : soc_mgmt_test_pkg
