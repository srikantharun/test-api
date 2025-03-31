`define AI_LS_BASE_ADDR  'h0000000 // Ends at 'h008FFFF

// AI CORE LS UVM package
package aic_ls_env_pkg;

  timeunit 1ns;
  timeprecision 1ns;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import axi_icdf_pkg::*;
`endif
  import aic_common_pkg::*, aic_ls_pkg::*;
  import dmc_pkg::*;
  import l1_pkg::*;
  import aic_ls_csr_ral_pkg::*;
  import mmio_agent_pkg::*;
  import rvv_agent_pkg::*;
  import dmc_addr_gen_agent_pkg::*;
  import aic_ls_agent_pkg::*;
  import dmc_addr_gen_ref_model_pkg::*;
  import dmc_addr_gen_scoreboard_pkg::*;
  import dmc_data_scoreboard_pkg::*;
  import token_agent_uvm_pkg::*;
  import token_mgr_mapping_aic_pkg::*;
  import aic_ls_coverage_pkg::*;
  import mmio_pkg::*;

  `ifdef AXI_VIP
    // Environment and environment Configurations
    `include "aic_ls_axi_system_cfg.svh"
    `include "axi_virtual_sequencer.svh"
    `include "aic_ls_axi_slverr_adapter.svh"
  `endif

  // Environment configuration and environment
  `include "aic_ls_env_cfg.svh"
  `include "aic_ls_env.svh"
endpackage : aic_ls_env_pkg
