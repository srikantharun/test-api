package ai_core_mvm_env_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import mvm_pkg::*;
  import axi_icdf_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
  import token_agent_uvm_pkg::*;
  import cc_clk_div_agent_uvm_pkg::*;
  import ai_core_mvm_common_pkg::*;
  import ai_core_mvm_ral_pkg::*;
  import ai_core_mvm_ref_model_pkg::*;
  import ai_core_mvm_func_cov_pkg::*;
  import ai_core_mvm_scoreboard_pkg::*;

  // Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.sv"
  `include "cust_svt_axi_system_cc_configuration.sv"
  `include "axi_virtual_sequencer.sv"

  // Environment configuration and environment
  `include "ai_core_mvm_env_cfg.sv"
  `include "ai_core_mvm_env.sv"

endpackage : ai_core_mvm_env_pkg
