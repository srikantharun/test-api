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


#ifndef __DWC_DDRCTL_CINIT_CFG_STATIC_H__
#define __DWC_DDRCTL_CINIT_CFG_STATIC_H__

/**
 * @brief Structure to hold programming intent for the static register fields.
 */
typedef struct tag_dwc_ddrctl_cinit_cfg_static {
	uint32_rnd_t ddr4;
	uint32_rnd_t lpddr4;
	uint32_rnd_t ddr5;
	uint32_rnd_t lpddr5;
	uint32_rnd_t bank_config;
	uint32_rnd_t bg_config;
	uint32_rnd_t burst_mode;
	uint32_rnd_t burstchop;
	uint32_rnd_t en_2t_timing_mode;
	uint32_rnd_t lpddr5x;
	uint32_rnd_t data_bus_width;
	uint32_rnd_t burst_rdwr;
	uint32_rnd_t active_logical_ranks;
	uint32_rnd_t active_ranks;
	uint32_rnd_t device_config;
	uint32_rnd_t rank_tmgreg_sel;
	uint32_rnd_t bank_config_2;
	uint32_rnd_t bg_config_2;
	uint32_rnd_t rfc_tmgreg_sel;
	uint32_rnd_t alt_addrmap_en;
	uint32_rnd_t active_logical_ranks_2;
	uint32_rnd_t device_config_2;
	uint32_rnd_t rank_tmgset_sel[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank_dev_cfg_sel[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t lpddr4_refresh_mode;
	uint32_rnd_t dis_trefi_x0125;
	uint32_rnd_t use_slow_rm_in_low_temp;
	uint32_rnd_t active_derate_byte_rank0;
	uint32_rnd_t active_derate_byte_rank1;
	uint32_rnd_t active_derate_byte_rank2;
	uint32_rnd_t active_derate_byte_rank3;
	uint32_rnd_t derate_temp_limit_intr_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t derate_temp_limit_intr_clr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t derate_temp_limit_intr_force[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dbg_mr4_grp_sel[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dbg_mr4_rank_sel[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t hw_lp_exit_idle_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t hw_lp_ctrl[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t hw_lp_accept_wait_window[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t cactive_in_mask[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t bsm_clk_on;
	uint32_rnd_t auto_refab_en;
	uint32_rnd_t per_bank_refresh;
	uint32_rnd_t per_bank_refresh_opt_en;
	uint32_rnd_t fixed_crit_refpb_bank_en;
	uint32_rnd_t rank_dis_refresh;
	uint32_rnd_t rfmsbc;
	uint32_rnd_t dis_mpsmx_zqcl;
	uint32_rnd_t zq_resistor_shared;
	uint32_rnd_t t_trkcalccur;
	uint32_rnd_t prefer_write;
	uint32_rnd_t lpddr4_opt_act_timing;
	uint32_rnd_t lpddr5_opt_act_timing;
	uint32_rnd_t en_count_every_wr;
	uint32_rnd_t dyn_bsm_mode;
	uint32_rnd_t bank_hit_limit;
	uint32_rnd_t dealloc_bsm_thr;
	uint32_rnd_t dealloc_num_bsm_m1;
	uint32_rnd_t rd_act_idle_gap;
	uint32_rnd_t wr_act_idle_gap;
	uint32_rnd_t hwffc_odt_en;
	uint32_rnd_t hwffc_vref_en;
	uint32_rnd_t init_fsp;
	uint32_rnd_t init_vrcg;
	uint32_rnd_t target_vrcg;
	uint32_rnd_t cke_power_down_mode;
	uint32_rnd_t power_saving_ctrl_word;
	uint32_rnd_t ctrl_word_num;
	uint32_rnd_t skip_mrw_odtvref;
	uint32_rnd_t skip_zq_stop_start;
	uint32_rnd_t zq_interval;
	uint32_rnd_t hwffc_mode;
	uint32_rnd_t dq_nibble_map_0_3;
	uint32_rnd_t dq_nibble_map_4_7;
	uint32_rnd_t dq_nibble_map_8_11;
	uint32_rnd_t dq_nibble_map_12_15;
	uint32_rnd_t dq_nibble_map_16_19;
	uint32_rnd_t dq_nibble_map_20_23;
	uint32_rnd_t dq_nibble_map_24_27;
	uint32_rnd_t dq_nibble_map_28_31;
	uint32_rnd_t dq_nibble_map_32_35;
	uint32_rnd_t dq_nibble_map_36_39;
	uint32_rnd_t dq_nibble_map_40_43;
	uint32_rnd_t dq_nibble_map_44_47;
	uint32_rnd_t dq_nibble_map_48_51;
	uint32_rnd_t dq_nibble_map_52_55;
	uint32_rnd_t dq_nibble_map_56_59;
	uint32_rnd_t dq_nibble_map_60_63;
	uint32_rnd_t dq_nibble_map_cb_0_3;
	uint32_rnd_t dq_nibble_map_cb_4_7;
	uint32_rnd_t dq_nibble_map_cb_8_11;
	uint32_rnd_t dq_nibble_map_cb_12_15;
	uint32_rnd_t dis_dq_rank_swap;
	uint32_rnd_t dfi_lp_en_pd;
	uint32_rnd_t dfi_lp_en_sr;
	uint32_rnd_t dfi_lp_en_dsm;
	uint32_rnd_t dfi_lp_en_mpsm;
	uint32_rnd_t dfi_lp_en_data;
	uint32_rnd_t dfi_lp_data_req_en;
	uint32_rnd_t dfi_lp_extra_gap;
	uint32_rnd_t extra_gap_for_dfi_lp_data;
	uint32_rnd_t dfi_phyupd_en;
	uint32_rnd_t ctrlupd_pre_srx;
	uint32_rnd_t dfi_phyupd_type0_wait_idle;
	uint32_rnd_t dfi_phyupd_type1_wait_idle;
	uint32_rnd_t dfi_phyupd_type2_wait_idle;
	uint32_rnd_t dfi_phyupd_type3_wait_idle;
	uint32_rnd_t phy_dbi_mode;
	uint32_rnd_t dfi_data_cs_polarity;
	uint32_rnd_t share_dfi_dram_clk_disable;
	uint32_rnd_t dfi_channel_mode;
	uint32_rnd_t dfi_phymstr_en;
	uint32_rnd_t dfi_phymstr_blk_ref_x32;
	uint32_rnd_t ecc_mode;
	uint32_rnd_t test_mode;
	uint32_rnd_t ecc_type;
	uint32_rnd_t ecc_ap_en;
	uint32_rnd_t ecc_region_remap_en;
	uint32_rnd_t ecc_ap_err_threshold;
	uint32_rnd_t ecc_region_map_other;
	uint32_rnd_t ecc_region_map_granu;
	uint32_rnd_t ecc_ap_mode;
	uint32_rnd_t med_ecc_en;
	uint32_rnd_t blk_channel_active_term;
	uint32_rnd_t bypass_internal_ecc;
	uint32_rnd_t kbd_en;
	uint32_rnd_t eapar_en;
	uint32_rnd_t parity_enable;
	uint32_rnd_t bypass_internal_crc;
	uint32_rnd_t crc_inc_dm;
	uint32_rnd_t caparity_disable_before_sr;
	uint32_rnd_t dfi_alert_async_mode;
	uint32_rnd_t capar_retry_enable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rd_ue_retry_enable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rd_crc_retry_enable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wr_crc_retry_enable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wr_crc_retry_limiter[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rd_crc_retry_limiter[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rd_ue_retry_limiter[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t capar_retry_limiter[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t make_multi_retry_fatl_err[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dis_capar_selfref_retry[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dis_capar_powerdown_retry[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t pre_sb_enable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t pre_ab_enable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t pre_slot_config[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_mrr_des1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_mrr_des2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_mrw_des1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_mrw_des2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_mpc_des1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_mpc_des2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_rfm_des1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ci_rfm_des2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_ba_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_size_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_ba_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_size_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_ba_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_size_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_ba_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_size_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_ba_2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_size_2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_ba_2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_size_2[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_ba_3[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_entry_size_3[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_ba_3[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_exit_size_3[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_entry1_ba_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_entry1_size_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_entry2_ba_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_entry2_size_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_exit1_ba_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_exit1_size_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_exit2_ba_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t selfref_exit2_size_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rfm_raa_use_ecs_refab[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t capar_retry_size[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_idle_ctrl_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t powerdown_idle_ctrl_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_selfref_exit_stagger;
	uint32_rnd_t pde_odt_ctrl[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t pd_mrr_nt_odt_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t cmd_timer_x32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dis_wc;
	uint32_rnd_t dis_rd_bypass;
	uint32_rnd_t dis_act_bypass;
	uint32_rnd_t hw_ref_zq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t sw_done;
	uint32_rnd_t dimm_stagger_cs_en;
	uint32_rnd_t dimm_addr_mirr_en;
	uint32_rnd_t dimm_output_inv_en;
	uint32_rnd_t mrs_a17_en;
	uint32_rnd_t mrs_bg1_en;
	uint32_rnd_t dimm_dis_bg_mirroring;
	uint32_rnd_t lrdimm_bcom_cmd_prot;
	uint32_rnd_t rcd_num;
	uint32_rnd_t dimm_type;
	uint32_rnd_t rcd_a_output_disabled;
	uint32_rnd_t rcd_b_output_disabled;
	uint32_rnd_t dual_channel_en;
	uint32_rnd_t max_rank_rd;
	uint32_rnd_t max_rank_wr;
	uint32_rnd_t max_logical_rank_rd;
	uint32_rnd_t max_logical_rank_wr;
	uint32_rnd_t rank0_wr_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank0_rd_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank1_wr_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank1_rd_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank2_wr_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank2_rd_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank3_wr_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rank3_rd_odt[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t sw_static_unlock;
	uint32_rnd_t pre_cke_x1024[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t post_cke_x1024[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dev_zqinit_x32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t ime_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t addrmap_dch_bit0;
	uint32_rnd_t addrmap_cs_bit0[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cs_bit1[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cs_bit2[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cs_bit3[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cid_b0[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cid_b1[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cid_b2[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_cid_b3[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_bank_b0[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_bank_b1[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_bank_b2[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_bg_b0[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_bg_b1[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_bg_b2[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b7[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b8[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b9[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b10[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b3[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b4[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b5[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_col_b6[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b14[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b15[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b16[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b17[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b10[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b11[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b12[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b13[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b6[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b7[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b8[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b9[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b2[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b3[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b4[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b5[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b0[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t addrmap_row_b1[DDRCTL_NUM_ADDR_MAP];
	uint32_rnd_t nonbinary_device_density;
	uint32_rnd_t bank_hash_en;
	uint32_rnd_t lpddr_mixed_pkg_en;
	uint32_rnd_t lpddr_mixed_pkg_x16_size;
	uint32_rnd_t addrmap_lut_bypass;
	uint32_rnd_t addrmap_use_lut_cs;
	uint32_rnd_t addrmap_lut_rank_type;
	uint32_rnd_t addrmap_lut_bit0;
	uint32_rnd_t addrmap_lut_bit0_valid;
	uint32_rnd_t addrmap_lut_bit1;
	uint32_rnd_t addrmap_lut_bit1_valid;
	uint32_rnd_t addrmap_lut_max_active_hif_addr_offset;
	uint32_rnd_t go2critical_en;
	uint32_rnd_t pagematch_limit;
	uint32_rnd_t dch_density_ratio;
	uint32_rnd_t rd_port_priority[UMCTL2_A_NPORTS];
	uint32_rnd_t rd_port_aging_en[UMCTL2_A_NPORTS];
	uint32_rnd_t rd_port_urgent_en[UMCTL2_A_NPORTS];
	uint32_rnd_t rd_port_pagematch_en[UMCTL2_A_NPORTS];
	uint32_rnd_t rrb_lock_threshold[UMCTL2_A_NPORTS];
	uint32_rnd_t wr_port_priority[UMCTL2_A_NPORTS];
	uint32_rnd_t wr_port_aging_en[UMCTL2_A_NPORTS];
	uint32_rnd_t wr_port_urgent_en[UMCTL2_A_NPORTS];
	uint32_rnd_t wr_port_pagematch_en[UMCTL2_A_NPORTS];
	uint32_rnd_t snf_mode[UMCTL2_A_NPORTS];
	uint32_rnd_t base_addr[4];
	uint32_rnd_t nblocks[4];
	uint32_rnd_t port_data_channel_0;
	uint32_rnd_t port_data_channel_1;
	uint32_rnd_t port_data_channel_2;
	uint32_rnd_t port_data_channel_3;
	uint32_rnd_t port_data_channel_4;
	uint32_rnd_t port_data_channel_5;
	uint32_rnd_t port_data_channel_6;
	uint32_rnd_t port_data_channel_7;
	uint32_rnd_t port_data_channel_8;
	uint32_rnd_t port_data_channel_9;
	uint32_rnd_t port_data_channel_10;
	uint32_rnd_t port_data_channel_11;
	uint32_rnd_t port_data_channel_12;
	uint32_rnd_t port_data_channel_13;
	uint32_rnd_t port_data_channel_14;
	uint32_rnd_t port_data_channel_15;
	uint32_rnd_t cbusy_select[UMCTL2_A_NPORTS];
	uint32_rnd_t dbg_dis_wrptl_rmw_be_eval[UMCTL2_A_NPORTS];
	uint32_rnd_t prc_exp_cnt[UMCTL2_A_NPORTS];
	uint32_rnd_t exp_cnt_div[UMCTL2_A_NPORTS];
	uint32_rnd_t rpq_lpr_min[UMCTL2_A_NPORTS];
	uint32_rnd_t rpq_hpr_min[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_busy_threshold_hpr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_free_threshold_hpr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_middle_threshold_hpr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_busy_threshold_lpr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_free_threshold_lpr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_middle_threshold_lpr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_busy_threshold_wr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_free_threshold_wr[UMCTL2_A_NPORTS];
	uint32_rnd_t cam_middle_threshold_wr[UMCTL2_A_NPORTS];
	uint32_rnd_t tz_sec_inv_en[UMCTL2_A_NPORTS];
	uint32_rnd_t tz_base_addr_low[UMCTL2_A_NPORTS][8];
	uint32_rnd_t tz_base_addr_high[UMCTL2_A_NPORTS][8];
	uint32_rnd_t tz_region_en[UMCTL2_A_NPORTS][8];
	uint32_rnd_t tz_region_size[UMCTL2_A_NPORTS][8];
	uint32_rnd_t tz_subregion_disable[UMCTL2_A_NPORTS][8];
	uint32_rnd_t tz_reg_sp[UMCTL2_A_NPORTS][8];
	uint32_rnd_t dfi_lp_wakeup_pd;
	uint32_rnd_t dfi_lp_wakeup_sr;
	uint32_rnd_t dfi_lp_wakeup_dsm;
	uint32_rnd_t dfi_lp_wakeup_mpsm;
	uint32_rnd_t dfi_lp_wakeup_data;
	uint32_rnd_t dfi_tlp_resp;
	uint32_rnd_t dfi_t_ctrlup_min;
	uint32_rnd_t dfi_t_ctrlup_max;
	uint32_rnd_t dfi_ctrlup_gap;
	uint32_rnd_t dfi_t_ctrlupd_interval_max_x1024[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dfi_t_ctrlupd_interval_min_x1024[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dfi_t_ctrlmsg_resp;
	uint32_rnd_t ctrlupd_after_dqsosc[UMCTL2_FREQUENCY_NUM];
	uint32_rnd_t ppt2_override[UMCTL2_FREQUENCY_NUM];
	uint32_rnd_t dfi_t_ctrlupd_burst_interval_x8[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t refresh_timer_lr_offset_x32[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t refresh_timer_lr_offset_x32_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_long_nop[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_short_nop[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_short_interval_x1024[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_reset_nop[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_stop[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_long_nop_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t t_zq_short_nop_2[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t dvfsq_enable[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t pageclose_timer[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdwr_idle_gap[UMCTL2_FREQUENCY_NUM][DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key_done_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key_miss_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key_collision_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t apb_timing_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key_size_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t reg_parity_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t glbl[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_usage_hit_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_swapped_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region0_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region0_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region0_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region0_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region1_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region1_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region1_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region1_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region2_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region2_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region2_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region2_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region3_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region3_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region3_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region3_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region4_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region4_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region4_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region4_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region5_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region5_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region5_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region5_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region6_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region6_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region6_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region6_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region7_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region7_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region7_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region7_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region8_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region8_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region8_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region8_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region9_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region9_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region9_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region9_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region10_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region10_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region10_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region10_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region11_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region11_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region11_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region11_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region12_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region12_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region12_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region12_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region13_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region13_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region13_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region13_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region14_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region14_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region14_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region14_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region15_addr_low_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region15_addr_low_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region15_addr_high_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t region15_addr_high_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_usage_thr_31_0[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_usage_thr_63_32[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_usage_auto_clear[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_usage_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key0_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key1_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key2_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key3_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key4_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key5_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key6_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key7_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key8_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key9_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key10_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key11_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key12_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key13_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key14_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t key15_rmw_swap_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tkey_eccc_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tkey_eccu_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_ckey_eccc_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_ckey_eccu_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tval_eccc_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tval_eccu_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tkey_eccc_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tkey_eccu_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_ckey_eccc_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_ckey_eccu_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tval_eccc_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tval_eccu_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tkey_eccc_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tkey_eccu_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_ckey_eccc_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_ckey_eccu_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tval_eccc_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_tval_eccu_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tkey_eccc_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tkey_eccu_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_ckey_eccc_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_ckey_eccu_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tval_eccc_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_tval_eccu_err_thr[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_enc_fifo_warn_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_data_fifo_warn_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_dec_fifo_warn_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_data_fifo_warn_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t cfg_lock_override[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t global_key_size[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_ctx_idx_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_reg_par_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_fsm_par_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_key_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_key_idx_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_uxts_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_self_test_fail_act[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_clr_ssp[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_hw_init_go[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_pipe_num[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_chk_disable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_enc_bypass_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_du_start[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_du_end[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_ecb[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_val[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_st_done[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_st_fail[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_fail_cause_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_funct[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t wrch_key_size[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_ctx_idx_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_reg_par_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_fsm_par_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_key_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_key_idx_err_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_uxts_irq_en[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_self_test_fail_act[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_clr_ssp[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_hw_init_go[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_pipe_num[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_chk_disable[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_enc_bypass_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_du_start[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_du_end[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_ecb[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_val[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_st_done[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_st_fail[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_fail_cause_1[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_funct[DWC_DDRCTL_NUM_CHANNEL];
	uint32_rnd_t rdch_key_size[DWC_DDRCTL_NUM_CHANNEL];
} dwc_ddrctl_cinit_cfg_static_t;
#endif /* __DWC_DDRCTL_CINIT_CFG_STATIC_H__ */

