package soc_mgmt_func_cov_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_axi_uvm_pkg::*;
  `endif
  `ifdef APB_VIP
    import svt_apb_uvm_pkg::*;
  `endif

  import soc_mgmt_common_pkg::*;
  import soc_mgmt_ral_pkg::*;

  `include "soc_mgmt_func_cov.sv"
endpackage : soc_mgmt_func_cov_pkg
