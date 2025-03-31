//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : subsystem_signal_intf.sv
// Unit        : subsystem_signal_intf
//------------------------------------------------------------------------------
// Description : This file contains 
//------------------------------------------------------------------------------

interface subsystem_signal_intf();

  logic i_ao_clk;
  logic i_lpddr_clk;
  logic i_ao_rst_n          ;
  logic i_global_rst_n      ;
  logic o_ao_rst_sync_n     ;
  logic o_noc_async_idle_req; // Fence 0 for lpddr_cfg_apb noc interface; Fence 1 for lpddr_axi noc interface
  logic i_noc_async_idle_ack; // Fence 0 for lpddr_cfg_apb noc interface; Fence 1 for lpddr_axi noc interface
  logic i_noc_async_idle_val; // Fence 0 for lpddr_cfg_apb noc interface; Fence 1 for lpddr_axi noc interface
  logic o_noc_clken         ;
  logic o_noc_rst_n         ;
  // Observability signals for lpddr
  logic [15:0] o_lpddr_obs;
  logic  o_ctrl_sbr_done_intr;
  logic  o_ctrl_derate_temp_limit_intr;
  logic  o_ctrl_ecc_ap_err_intr;
  logic  o_ctrl_ecc_corrected_err_intr;
  logic  o_ctrl_ecc_uncorrected_err_intr;
  logic  o_ctrl_rd_linkecc_corr_err_intr;
  logic  o_ctrl_rd_linkecc_uncorr_err_intr;
  // PHY interrupts
  logic  o_phy_pie_prog_err_intr;
  logic  o_phy_ecc_err_intr;
  logic  o_phy_rdfptrchk_err_intr;
  logic  o_phy_pie_parity_err_intr;
  logic  o_phy_acsm_parity_err_intr;
  logic  o_phy_trng_fail_intr;
  logic  o_phy_init_cmplt_intr;
  logic  o_phy_trng_cmplt_intr;
  // Credit Counters signals
  logic [6:0] hpr_credit_cnt;
  logic [6:0] lpr_credit_cnt;
  logic [6:0] wr_credit_cnt;
  logic [6:0] wrecc_credit_cnt;
  //AXI Side-band signals, these can be asserted anytime, and is not associated to any particular command.
  logic awurgent, arurgentb, arurgentr;

	// Performance logging signals 
	logic [2:0] perf_bank;
	logic [1:0] perf_bg;
	logic perf_dfi_rd_data_cycles;
	logic perf_dfi_wr_data_cycles;
	logic perf_hif_hi_pri_rd;
	logic perf_hif_rd;
	logic perf_hif_rd_or_wr;
	logic perf_hif_rmw;
	logic perf_hif_wr;
	logic perf_hpr_req_with_nocredit;
	logic perf_hpr_xact_when_critical;
	logic perf_ie_blk_hazard;
	logic perf_lpr_req_with_nocredit;
	logic perf_lpr_xact_when_critical;
	logic perf_op_is_activate;
	logic perf_op_is_cas;
	logic perf_op_is_cas_wck_sus;
	logic perf_op_is_cas_ws;
	logic perf_op_is_cas_ws_off;
	logic perf_op_is_crit_ref;
	logic perf_op_is_dqsosc_mpc;
	logic perf_op_is_dqsosc_mrr;
	logic perf_op_is_enter_dsm;
	logic [1:0] perf_op_is_enter_powerdown;
	logic [1:0] perf_op_is_enter_selfref;
	logic perf_op_is_load_mode;
	logic perf_op_is_mwr;
	logic perf_op_is_precharge;
	logic perf_op_is_rd;
	logic perf_op_is_rd_activate;
	logic perf_op_is_rd_or_wr;
	logic perf_op_is_refresh;
	logic perf_op_is_rfm;
	logic perf_op_is_spec_ref;
	logic perf_op_is_tcr_mrr;
	logic perf_op_is_wr;
	logic perf_op_is_zqlatch;
	logic perf_op_is_zqstart;
	logic perf_precharge_for_other;
	logic perf_precharge_for_rdwr;
	logic perf_rank;				// FIXME: Kunal change vector width 
	logic perf_raw_hazard;
	logic perf_rdwr_transitions;
	logic [1:0] perf_selfref_mode;
	logic perf_visible_window_limit_reached_rd;
	logic perf_visible_window_limit_reached_wr;
	logic perf_war_hazard;
	logic perf_waw_hazard;
	logic perf_wr_xact_when_critical;
	logic perf_write_combine;
	logic perf_write_combine_noecc;
	logic perf_write_combine_wrecc;

	logic derate_temp_limit_intr;
	logic [1:0] derate_temp_limit_intr_fault;

	// this is used for polling match
        logic [31:0] apb_master_0_prdata;
endinterface
