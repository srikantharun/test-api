package dpu_env_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import dpu_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import axi_icdf_pkg::*;
`endif
  import ai_core_dp_cmd_gen_uvm_pkg::*;
  import token_agent_uvm_pkg::*;
  import dpu_agent_pkg::*;
  import dpu_common_pkg::*;
  import dpu_ral_pkg::*;
  import dpu_ref_model_pkg::*;
  import dpu_func_cov_pkg::*;
  import dpu_scoreboard_pkg::*;

  // Environment and environment Configurations
  `include "cust_svt_axi_master_transaction.svh"
  `include "cust_svt_axi_system_configuration.svh"
  `include "axi_virtual_sequencer.svh"

  // Environment configuration and environment
  `include "dpu_env_cfg.svh"
  `include "dpu_env.svh"

endpackage : dpu_env_pkg

