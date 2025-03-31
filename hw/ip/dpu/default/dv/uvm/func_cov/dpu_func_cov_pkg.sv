package dpu_func_cov_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import dpu_pkg::*;
  `ifdef AXI_VIP
    //import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  import dpu_common_pkg::*;
  import token_agent_uvm_pkg::*;

  `include "dpu_func_cov.svh"
endpackage : dpu_func_cov_pkg

