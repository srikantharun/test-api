package ai_core_mvm_ref_model_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*;
  import mvm_pkg::*;
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import ai_core_mvm_common_pkg::*;
  import token_agent_uvm_pkg::*;

  `include "ai_core_mvm_ref_model.sv"
endpackage : ai_core_mvm_ref_model_pkg
