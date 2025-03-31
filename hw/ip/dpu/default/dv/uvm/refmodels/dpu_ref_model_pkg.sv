package dpu_ref_model_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import dpu_pkg::*;
  import dpu_common_pkg::*;
  import token_agent_uvm_pkg::*;
  import dpu_agent_pkg::*;
  import dpu_func_cov_pkg::*;
  `include "dpu_ref_model.svh"
endpackage : dpu_ref_model_pkg

