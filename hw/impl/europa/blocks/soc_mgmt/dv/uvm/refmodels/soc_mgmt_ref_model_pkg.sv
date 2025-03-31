package soc_mgmt_ref_model_pkg;

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

  `include "soc_mgmt_ref_model.sv"
endpackage : soc_mgmt_ref_model_pkg
