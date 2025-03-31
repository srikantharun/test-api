/**
 * Abstract:
 * Defines an interface that provides access to a reset signal.  This
 * interface can be used to write sequences to drive the reset logic.
 */

`ifndef GUARD_AI_CORE_TOP_IF_SVI
`define GUARD_AI_CORE_TOP_IF_SVI
interface ai_core_top_if();
  import uvm_pkg::*;
  import svt_uvm_pkg::*;
  `include "uvm_macros.svh"
  import svt_axi_uvm_pkg::*;

  //RAL FILES
  import dv_base_reg_pkg::*;
  import ai_core_cfg_csr_ral_pkg::*;
  import ai_core_top_ral_pkg::*;

  ai_core_top_reg_block regmodel;
  logic preload_aicore_spm;
  logic [7:0] cid;
  logic clk;
  logic ref_clk;
  logic apb_rst;
  logic axi_rst;

  real T = 25 ; // Signal to be forced by test bench, timing of when the force happens is controlled by test bench
  real V = 0.8; // Voltage to be forced by test bench for Voltage evaluation mode
  integer P = 0;
  logic DATA_VALID;

  logic ls;
  logic ds;
  logic sd;
  logic rop;
  logic [2:0]power_mode=0;
  logic resethaltreq_async_i=0;
  logic msip_async_i=0;
  logic mtip_async_i=0;
  logic nmi_async_i=0;
  logic throttle_i=1'b0;
  logic [35:0]reset_vector_i=0;

  //fcov 
  logic irq_thermal_warning_o;
  logic irq_thermal_shutdown_o;
  logic alert_thermal_warning_o;
  logic alert_thermal_shutdown_o;
  logic ai_core_obs;
  logic dwpu_irq;
  logic mvm_irq;
  logic [13:0]infra_lp_dlock_o;
  logic [11:0]infra_hp_dlock_o;
  logic [6:0]l1_lc_fabric_dlock_o;
  logic iau0_irq;
  logic dpu0_irq;
  logic iau1_irq;
  logic dpu1_irq;
  logic [7:0]ls_irq;
  logic hart_unavail_async_o;
  logic hart_unavail_async;

  //for mvm sw test mode
  logic [25:0]mvm_acc_output;
  logic mvm_acc_output_valid;
  logic mvm_acc_output_last;
  logic [2:0]mvm_sw_test_mode;
  logic [511:0]mvm_odr_output;
  logic mvm_odr_tlast ;
  logic mvm_odr_tready;
  logic mvm_odr_tvalid;
  logic disable_rdataX_assertion = 0;
  logic disable_addr_boundary_assertion = 0;
  logic disable_cdc_level_for_ai_core_obs = 0;
  logic disable_for_cmd_overfilling = 0;

  //assertions to check the sideband signals

  //This is to check the hart_unavail_async_o signal. hart should be availble only when the ax25_clk_en is 1 and hart_unavail is 0.
  // https://git.axelera.ai/ai-hw-team/triton/-/issues/2561
     
endinterface

`endif // GUARD_ai_core_top_if_SVI
