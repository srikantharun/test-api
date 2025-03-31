package ai_core_top_test_pkg;

  //timeunit 1ns;
  //timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `include "ai_core_top_tb_define.sv"

  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif


  import aic_common_pkg::*;
  import ai_core_pkg::*;

  import token_agent_uvm_pkg::*;
  import ai_core_top_ral_pkg::*;
  import ai_core_top_seq_pkg::*;
  import dmc_addr_gen_agent_pkg::*;
  import aic_ls_agent_pkg::*;
  import aic_ls_env_pkg::*;
  import aic_ls_seq_pkg::*;
  import ai_core_top_env_pkg::*;
  import uvm_sw_ipc_pkg::*;


  `include "ai_core_top_cust_svt_axi_master_transaction.sv"

  `include "ai_core_demoter.sv"
  `include "warning_catcher.sv"
   //// AXI Tests
  `include "ai_core_base_test.sv"
  `include "ai_core_dma_base_test.sv"
  `include "ai_core_lp_dma_l2_to_spm_test.sv"
  `include "ai_core_lp_dma_ddr_to_spm_test.sv"
  `include "ai_core_lp_dma_sysspm_to_spm_test.sv"
  `include "ai_core_test_uvm_sw_ipc_sanity.sv"
  //`include "ai_core_top_ral_bit_bash_test.sv"
  `include "ai_core_dwpu_bypass_test.sv"
  `include "ai_core_mvm_bypass_test.sv"
  `include "ai_core_lp2hp_test.sv"
  
endpackage : ai_core_top_test_pkg
