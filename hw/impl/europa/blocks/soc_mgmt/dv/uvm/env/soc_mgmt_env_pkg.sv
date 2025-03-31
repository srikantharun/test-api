package soc_mgmt_env_pkg;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif
`ifdef APB_VIP
  import svt_apb_uvm_pkg::*;
`endif
  import soc_mgmt_common_pkg::*;
  import soc_mgmt_ral_pkg::*;
  import soc_mgmt_ref_model_pkg::*;
  import soc_mgmt_func_cov_pkg::*;
  import soc_mgmt_scoreboard_pkg::*;

  // Environment and environment Configurations
  `include "cust_svt_axi_system_configuration.sv"
  `include "cust_svt_axi_system_cc_configuration.sv"
  `include "axi_virtual_sequencer.sv"

  `include "apb_shared_cfg.sv"
  `include "apb_virtual_sequencer.sv"
  // Environment configuration and environment
  `include "soc_mgmt_env_cfg.sv"
  `include "soc_mgmt_env.sv"

endpackage : soc_mgmt_env_pkg
