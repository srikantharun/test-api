package iau_ref_model_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import iau_pkg::*;
  import iau_common_pkg::*;
  import token_agent_uvm_pkg::*;
  import iau_agent_pkg::*;

  `include "iau_ref_model.svh"
endpackage : iau_ref_model_pkg

