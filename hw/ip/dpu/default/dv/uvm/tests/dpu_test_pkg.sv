package dpu_test_pkg;
  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
    import axi_icdf_pkg::*;
  `endif


  import aic_common_pkg::*;
  import dpu_pkg::*;

  import token_agent_uvm_pkg::*;
  import dpu_common_pkg::*;
  import ai_core_dp_cmd_gen_uvm_pkg::*;
  import dpu_ral_pkg::*;
  import dpu_seq_pkg::*;
  import dpu_env_pkg::*;
  import dpu_env_pkg::cust_svt_axi_system_configuration;
  `include "dpu_base_test.svh"
  
//  `include "dpu_axi_b2b_test.svh"
//  `include "dpu_register_test.svh"
//  `include "dpu_icdf_test.svh"
//  `include "dpu_sanity_test.svh"
//  `include "dpu_direct_test.svh"
//  `include "dpu_random_test.svh"
//  `include "dpu_irq_test.svh"
//  `include "dpu_rfs_test.svh"
  `include "dpu_smoke_test.svh"
endpackage : dpu_test_pkg

