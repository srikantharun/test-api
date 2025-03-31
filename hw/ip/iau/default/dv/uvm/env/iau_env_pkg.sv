package iau_env_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import iau_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import axi_icdf_pkg::*;
`endif
  import token_agent_uvm_pkg::*;
  import iau_agent_pkg::*;
  import iau_common_pkg::*;
  import iau_ral_pkg::*;
  import iau_ref_model_pkg::*;
  import iau_func_cov_pkg::*;
  import iau_scoreboard_pkg::*;

  // Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.sv"
  `include "axi_virtual_sequencer.sv"

  // Environment configuration and environment
  `include "iau_env_cfg.sv"
  `include "iau_env.sv"

endpackage : iau_env_pkg

