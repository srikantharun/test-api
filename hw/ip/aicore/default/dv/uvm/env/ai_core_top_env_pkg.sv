// Description: ai_core_top uvm env package which includes env, env configurations, sequencers
// Owner: Roswin Benny<roswin.benny@axelera.ai>

`define AXI_VIP
`define APB_VIP
package ai_core_top_env_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"
  `include "ai_core_top_tb_define.sv"
 `ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
 `endif
 `ifdef APB_VIP
  import svt_apb_uvm_pkg::*;
 `endif
  import ai_core_top_ral_pkg::*;
  import aic_ls_env_pkg::*;
  import aic_ls_seq_pkg::*;

`ifdef AXI_VIP
  `include "cust_svt_axi_system_configuration.sv"
  `include "cust_aicore_svt_apb_system_configuration.sv"
  `include "cust_svt_axi_system_cc_configuration.sv"
  `include "ai_core_top_axi_virtual_sequencer.sv"
  `include "apb_virtual_sequencer.svh"
  `include "ai_core_top_env_cfg.sv"
  `include "ai_core_env.sv"

 `endif


endpackage:ai_core_top_env_pkg
