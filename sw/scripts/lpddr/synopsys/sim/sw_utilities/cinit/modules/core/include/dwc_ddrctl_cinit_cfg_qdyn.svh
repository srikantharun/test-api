// coreBuilder: This is an automated C header file. DO NOT EDIT.

// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


`ifndef __DWC_DDRCTL_CINIT_CFG_QDYN_H__
`define __DWC_DDRCTL_CINIT_CFG_QDYN_H__

/**
 * @brief Structure to hold programming intent for the quasi-dynamic register fields.
 */
typedef struct {
	rand int unsigned dll_off_mode;
	rand int unsigned target_frequency;
	rand int unsigned geardown_mode[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wck_on[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wck_suspend_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ws_off_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derate_mr4_tuf_dis;
	rand int unsigned dis_mrr4_tcr_srx;
	rand int unsigned derate_temp_limit_intr_normal_en;
	rand int unsigned derate_temp_limit_intr_high_en;
	rand int unsigned derate_temp_limit_intr_low_en;
	rand int unsigned derate_low_temp_limit;
	rand int unsigned derate_high_temp_limit;
	rand int unsigned same_bank_refresh;
	rand int unsigned tcr_refab_thr;
	rand int unsigned fgr_mode;
	rand int unsigned ref_3ds_burst_limit_en;
	rand int unsigned ref_3ds_burst_limit_thr;
	rand int unsigned rfm_en;
	rand int unsigned raaimt;
	rand int unsigned raamult;
	rand int unsigned raadec;
	rand int unsigned rfmth_rm_thr;
	rand int unsigned dis_srx_zqcl;
	rand int unsigned dis_srx_zqcl_hwffc;
	rand int unsigned dqsosc_runtime;
	rand int unsigned wck2dqo_runtime;
	rand int unsigned dis_dqsosc_srx;
	rand int unsigned t_oscs;
	rand int unsigned dis_opt_wrecc_collision_flush;
	rand int unsigned pageclose;
	rand int unsigned rdwr_switch_policy_sel;
	rand int unsigned opt_wrcam_fill_level;
	rand int unsigned dis_opt_ntt_by_act;
	rand int unsigned dis_opt_ntt_by_pre;
	rand int unsigned autopre_rmw;
	rand int unsigned lpr_num_entries;
	rand int unsigned w_starve_free_running;
	rand int unsigned dis_prefer_col_by_act;
	rand int unsigned dis_prefer_col_by_pre;
	rand int unsigned opt_act_lat;
	rand int unsigned prefer_read;
	rand int unsigned dis_speculative_act;
	rand int unsigned opt_vprw_sch;
	rand int unsigned delay_switch_write;
	rand int unsigned visible_window_limit_wr;
	rand int unsigned visible_window_limit_rd;
	rand int unsigned page_hit_limit_wr;
	rand int unsigned page_hit_limit_rd;
	rand int unsigned opt_hit_gt_hpr;
	rand int unsigned wrcam_lowthresh;
	rand int unsigned wrcam_highthresh;
	rand int unsigned wr_pghit_num_thresh;
	rand int unsigned rd_pghit_num_thresh;
	rand int unsigned rd_page_exp_cycles;
	rand int unsigned wr_page_exp_cycles;
	rand int unsigned wrecc_cam_lowthresh;
	rand int unsigned wrecc_cam_highthresh;
	rand int unsigned dis_opt_loaded_wrecc_cam_fill_level;
	rand int unsigned dis_opt_valid_wrecc_cam_fill_level;
	rand int unsigned dis_auto_ctrlupd_srx;
	rand int unsigned dis_auto_ctrlupd;
	rand int unsigned dfi_init_complete_en;
	rand int unsigned dfi_reset_n;
	rand int unsigned dfi_init_start;
	rand int unsigned dis_dyn_adr_tri;
	rand int unsigned lp_optimized_write;
	rand int unsigned dfi_frequency;
	rand int unsigned dfi_tctrlupd_min_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tctrlupd_max_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tinit_start_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tinit_complete_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tlp_ctrl_resp_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tlp_data_resp_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tlp_ctrl_wakeup_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tlp_data_wakeup_poison_err_inj[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tctrlupd_min_poison_margin[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tinit_start_poison_margin[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tlp_ctrl_resp_poison_margin[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tlp_data_resp_poison_margin[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ecc_region_map;
	rand int unsigned blk_channel_idle_time_x32;
	rand int unsigned data_poison_en;
	rand int unsigned data_poison_bit;
	rand int unsigned poison_chip_en;
	rand int unsigned ecc_region_parity_lock;
	rand int unsigned ecc_region_waste_lock;
	rand int unsigned active_blk_channel;
	rand int unsigned poison_advecc_kbd;
	rand int unsigned poison_num_dfi_beat;
	rand int unsigned prop_rd_ecc_err;
	rand int unsigned ecc_poison_col;
	rand int unsigned ecc_poison_cid;
	rand int unsigned ecc_poison_rank;
	rand int unsigned ecc_poison_row;
	rand int unsigned ecc_poison_bank;
	rand int unsigned ecc_poison_bg;
	rand int unsigned ecc_syndrome_sel;
	rand int unsigned ecc_err_symbol_sel;
	rand int unsigned ecc_poison_beats_sel;
	rand int unsigned ecc_poison_data_31_0;
	rand int unsigned ecc_poison_data_63_32;
	rand int unsigned ecc_poison_data_71_64;
	rand int unsigned flip_bit_pos0;
	rand int unsigned flip_bit_pos1;
	rand int unsigned oc_parity_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned oc_parity_type[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned par_wdata_slverr_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned par_wdata_axi_check_bypass_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned par_rdata_slverr_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned par_addr_slverr_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned par_poison_en;
	rand int unsigned par_poison_loc_rd_dfi;
	rand int unsigned par_poison_loc_rd_iecc_type;
	rand int unsigned par_poison_loc_rd_port;
	rand int unsigned par_poison_loc_wr_port;
	rand int unsigned par_poison_byte_num;
	rand int unsigned ocsap_par_en;
	rand int unsigned ocsap_poison_en;
	rand int unsigned wdataram_addr_poison_loc;
	rand int unsigned rdataram_addr_poison_loc;
	rand int unsigned wdataram_addr_poison_ctl;
	rand int unsigned rdataram_addr_poison_ctl;
	rand int unsigned rdataram_addr_poison_port;
	rand int unsigned ocecc_en;
	rand int unsigned ocecc_fec_en;
	rand int unsigned ocecc_wdata_slverr_en;
	rand int unsigned ocecc_rdata_slverr_en;
	rand int unsigned ocecc_poison_en;
	rand int unsigned ocecc_poison_egen_mr_rd_0;
	rand int unsigned ocecc_poison_egen_mr_rd_0_byte_num;
	rand int unsigned ocecc_poison_egen_xpi_rd_out;
	rand int unsigned ocecc_poison_port_num;
	rand int unsigned ocecc_poison_egen_mr_rd_1;
	rand int unsigned ocecc_poison_egen_mr_rd_1_byte_num;
	rand int unsigned ocecc_poison_egen_xpi_rd_0;
	rand int unsigned ocecc_poison_ecc_corr_uncorr;
	rand int unsigned ocecc_poison_pgen_rd;
	rand int unsigned ocecc_poison_pgen_mr_wdata;
	rand int unsigned ocecc_poison_pgen_mr_ecc;
	rand int unsigned occap_en;
	rand int unsigned rd_crc_enable;
	rand int unsigned wr_crc_enable;
	rand int unsigned dis_rd_crc_ecc_upr_nibble;
	rand int unsigned capar_err_max_reached_th;
	rand int unsigned wr_crc_err_max_reached_th;
	rand int unsigned rd_crc_err_max_reached_th;
	rand int unsigned rd_link_ecc_err_byte_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_link_ecc_err_rank_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned init_done[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dbg_st_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned bist_st_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr_min_gap[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_min_gap[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank_switch_gap_unit_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mrr_des_timing_unit_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned selfref_wo_ref_pending[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_alert_assertion_mode[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned speculative_ref_pri_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dimm_t_dcaw[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dimm_n_dcac_m1[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dimm_dcaw_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned enable_trfc_dpr[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned base_timer[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raa_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raa_reset[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_alert_thr[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned auto_ecs_refab_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrlupd_retry_thr[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dis_max_rank_rd_opt;
	rand int unsigned dis_max_rank_wr_opt;
	rand int unsigned lpr_num_entries_extend;
	rand int unsigned wrcam_lowthresh_extend;
	rand int unsigned wrcam_highthresh_extend;
	rand int unsigned wr_pghit_num_thresh_extend;
	rand int unsigned rcd_weak_drive;
	rand int unsigned dm_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr_dbi_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_dbi_en[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_data_copy_en;
	rand int unsigned wr_data_copy_en;
	rand int unsigned wr_data_x_en;
	rand int unsigned skip_dram_init[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned read_reorder_bypass_en[`UMCTL2_A_NPORTS];
	rand int unsigned rdwr_ordered_en[`UMCTL2_A_NPORTS];
	rand int unsigned id_mask[`UMCTL2_A_NPORTS][16];
	rand int unsigned id_value[`UMCTL2_A_NPORTS][16];
	rand int unsigned rqos_map_level1[`UMCTL2_A_NPORTS];
	rand int unsigned rqos_map_level2[`UMCTL2_A_NPORTS];
	rand int unsigned rqos_map_region0[`UMCTL2_A_NPORTS];
	rand int unsigned rqos_map_region1[`UMCTL2_A_NPORTS];
	rand int unsigned rqos_map_region2[`UMCTL2_A_NPORTS];
	rand int unsigned rqos_map_timeoutb[`UMCTL2_A_NPORTS];
	rand int unsigned rqos_map_timeoutr[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_level1[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_level2[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_region0[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_region1[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_region2[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_timeout1[`UMCTL2_A_NPORTS];
	rand int unsigned wqos_map_timeout2[`UMCTL2_A_NPORTS];
	rand int unsigned chb_rqos_map_level1[`UMCTL2_A_NPORTS];
	rand int unsigned chb_rqos_map_level2[`UMCTL2_A_NPORTS];
	rand int unsigned chb_rqos_map_region0[`UMCTL2_A_NPORTS];
	rand int unsigned chb_rqos_map_region1[`UMCTL2_A_NPORTS];
	rand int unsigned chb_rqos_map_region2[`UMCTL2_A_NPORTS];
	rand int unsigned vpr_uncrd_timeout[`UMCTL2_A_NPORTS];
	rand int unsigned vpr_crd_timeout[`UMCTL2_A_NPORTS];
	rand int unsigned chb_wqos_map_level1[`UMCTL2_A_NPORTS];
	rand int unsigned chb_wqos_map_level2[`UMCTL2_A_NPORTS];
	rand int unsigned chb_wqos_map_region0[`UMCTL2_A_NPORTS];
	rand int unsigned chb_wqos_map_region1[`UMCTL2_A_NPORTS];
	rand int unsigned chb_wqos_map_region2[`UMCTL2_A_NPORTS];
	rand int unsigned vpw_uncrd_timeout[`UMCTL2_A_NPORTS];
	rand int unsigned vpw_crd_timeout[`UMCTL2_A_NPORTS];
	rand int unsigned t_ras_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ras_max[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_faw[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rcd_write[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned read_latency[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned write_latency[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rcd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cke[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ckesr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cksre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cksrx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ckcsx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_csh[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mrw_l[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xs_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xs_dll_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xs_abort_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xs_fast_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ddr4_wr_preamble[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_gear_hold[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_gear_setup[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cmd_gear[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_sync_gear[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ckmpe[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mpx_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mpx_lh[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned post_mpsm_gap_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mrd_pda[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cmdcke[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr_mpr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ppd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_mw[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned odtloff[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xsr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_osco[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_stab_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned en_hwffc_t_stab[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned en_dfi_lp_t_stab[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_faw_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rp_ca_parity[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_vrcg_disable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_vrcg_enable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mpsmx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_pd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_csl_srexit[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_csh_srexit[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_casrx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cpded[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mpc_hold[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mpc_setup[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mpc_cs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_csl[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_dpr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_dpr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_dlr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned max_wr_sync[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned max_rd_sync[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned bank_org[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rda2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wra2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned lpddr4_diff_bank_rwa2pre[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_r[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_r_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w_s[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mrr2mpc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ecsc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_srx2srx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cpded2srx[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_cssr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ckact[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ckoff[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mrr2rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mrr2wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mrr2mrw[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raaimt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raa_thr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raa_ref_decr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ws_fs2wck_sus[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wcksus[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ws_off2ws_fs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_r_m[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w_m[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_m[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_mw_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rda2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wra2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2pre_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr_s_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_s_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_s_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned max_wr_sync_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned max_rd_sync_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2mr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2mr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_dr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr_dr_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned diff_rank_rd_gap_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned diff_rank_wr_gap_blx2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ras_min_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_faw_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2pre_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rc_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2pre_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rp_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rcd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xs_x32_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_xs_dll_x32_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ppd_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w2_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_faw_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rp_ca_parity_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_dpr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_dpr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_dlr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_r_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_r_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w_s_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_mrr2mpc_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raaimt_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raa_thr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rfm_raa_ref_decr_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_r_m_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ccd_w_m_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_m_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r0r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r1r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r0r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r1r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r0r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r1r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r0r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r1r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r0r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r2r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r0r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r2r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r0r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r2r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r0r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r2r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r0r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r3r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r0r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r3r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r0r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r3r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r0r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r3r0[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r1r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r2r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r1r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r2r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r1r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r2r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r1r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r2r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r1r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r3r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r1r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r3r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r1r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r3r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r1r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r3r1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r2r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2rd_gap_r3r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r2r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2rd_gap_r3r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r2r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rd2wr_gap_r3r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r2r3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr2wr_gap_r3r2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ras_min_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_faw_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rc_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rp_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rcd_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rrd_s_mram[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned emr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned emr3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned emr2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mr5[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mr4[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mr6[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mr22[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tphy_wrlat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tphy_wrdata[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_rddata_en[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_ctrl_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_dram_clk_enable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_dram_clk_disable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_wrdata_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_parin_lat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_cmd_lat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tphy_wrcslat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_tphy_rdcslat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_geardown_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_dis[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_en_fs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_en_wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_en_rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_toggle_post[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_toggle_cs[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_toggle[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_fast_toggle[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_toggle_post_rd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_twck_toggle_post_rd_en[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_2n_mode_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_init_start[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_init_complete[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_win_size_1xtrefi[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ecs_int_x1024[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rfmpb[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_rfmpb_mp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_win_size_1xtrefi_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_ecs_int_x1024_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_1[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_2[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_3[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_4[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_5[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_6[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_7[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned ctrl_word_8[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank1_mr1_rtt_nom[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank1_mr2_rtt_wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank1_mr5_rtt_park[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank1_mr6_vref_value[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank1_mr6_vref_range[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank2_mr1_rtt_nom[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank2_mr2_rtt_wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank2_mr5_rtt_park[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank2_mr6_vref_value[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank2_mr6_vref_range[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank3_mr1_rtt_nom[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank3_mr2_rtt_wr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank3_mr5_rtt_park[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank3_mr6_vref_value[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rank3_mr6_vref_range[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned mr4_read_interval[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derated_t_rrd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derated_t_rp[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derated_t_ras_min[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derated_t_rcd[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derated_t_rc[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned derated_t_rcd_write[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned hw_lp_idle_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned hpr_max_starve[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned hpr_xact_run_length[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned lpr_max_starve[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned lpr_xact_run_length[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned w_max_starve[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned w_xact_run_length[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned frequency_ratio[`UMCTL2_FREQUENCY_NUM];
	rand int unsigned diff_rank_rd_gap[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned diff_rank_wr_gap[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr2rd_dr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd2wr_dr[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned powerdown_to_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned selfref_to_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_odt_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_odt_hold[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr_odt_delay[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr_odt_hold[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_csalt[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned capar_retry_window[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_wr_crc_retry_window[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned dfi_t_phy_rdlat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned extra_rd_retry_window[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned retry_add_rd_lat[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned retry_add_rd_lat_en[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_pgm_x1_x1024[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_pgm_x1_sel[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_pgmpst_x32[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned t_pgm_exit[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wr_link_ecc_enable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rd_link_ecc_enable[`UMCTL2_FREQUENCY_NUM][`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned key_idx[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned key_slot_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned key_invalidate[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned key_sz[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned bypass_sel[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned wrch_go[`DWC_DDRCTL_NUM_CHANNEL];
	rand int unsigned rdch_go[`DWC_DDRCTL_NUM_CHANNEL];
} dwc_ddrctl_cinit_cfg_qdyn_t;
`endif /* __DWC_DDRCTL_CINIT_CFG_QDYN_H__ */

