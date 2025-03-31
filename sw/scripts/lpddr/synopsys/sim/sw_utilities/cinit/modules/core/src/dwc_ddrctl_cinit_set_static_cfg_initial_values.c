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

/**
 * @brief Method to set all static, qdyn, or dyn attr to their memoryMap.tcl defined initial value
 */
#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_util.h"
void dwc_ddrctl_cinit_set_static_cfg_initial_values(void)
{
	STATIC.ddr4 = 0x0;
	STATIC.lpddr4 = 0x0;
	STATIC.ddr5 = 0x0;
	STATIC.lpddr5 = 0x0;
	STATIC.bank_config = 0x1;
	STATIC.bg_config = 0x2;
	STATIC.burst_mode = 0x0;
	STATIC.burstchop = 0x0;
	STATIC.en_2t_timing_mode = 0x0;
	STATIC.lpddr5x = 0x0;
	STATIC.data_bus_width = 0x0;
	STATIC.burst_rdwr = 0x4;
	STATIC.active_logical_ranks = 0x0;
	STATIC.active_ranks = (MEMC_NUM_RANKS == 4) ? 0xF : ((MEMC_NUM_RANKS == 2) ? 0x3 : 0x1);
	STATIC.device_config = 0x0;
	STATIC.rank_tmgreg_sel = 0x0;
	STATIC.bank_config_2 = 0x1;
	STATIC.bg_config_2 = 0x2;
	STATIC.rfc_tmgreg_sel = 0x0;
	STATIC.alt_addrmap_en = 0x0;
	STATIC.active_logical_ranks_2 = 0x0;
	STATIC.device_config_2 = 0x0;
	dwc_cinit_memset32(&STATIC.rank_tmgset_sel, 0x0, sizeof(STATIC.rank_tmgset_sel));
	dwc_cinit_memset32(&STATIC.rank_dev_cfg_sel, 0x0, sizeof(STATIC.rank_dev_cfg_sel));
	STATIC.lpddr4_refresh_mode = 0x0;
	STATIC.dis_trefi_x0125 = 0x0;
	STATIC.use_slow_rm_in_low_temp = 0x1;
	STATIC.active_derate_byte_rank0 = 0x0;
	STATIC.active_derate_byte_rank1 = 0x0;
	STATIC.active_derate_byte_rank2 = 0x0;
	STATIC.active_derate_byte_rank3 = 0x0;
	dwc_cinit_memset32(&STATIC.derate_temp_limit_intr_en, 0x1, sizeof(STATIC.derate_temp_limit_intr_en));
	dwc_cinit_memset32(&STATIC.derate_temp_limit_intr_clr, 0x0, sizeof(STATIC.derate_temp_limit_intr_clr));
	dwc_cinit_memset32(&STATIC.derate_temp_limit_intr_force, 0x0, sizeof(STATIC.derate_temp_limit_intr_force));
	dwc_cinit_memset32(&STATIC.dbg_mr4_grp_sel, 0x0, sizeof(STATIC.dbg_mr4_grp_sel));
	dwc_cinit_memset32(&STATIC.dbg_mr4_rank_sel, 0x0, sizeof(STATIC.dbg_mr4_rank_sel));
	dwc_cinit_memset32(&STATIC.hw_lp_exit_idle_en, 0x1, sizeof(STATIC.hw_lp_exit_idle_en));
	dwc_cinit_memset32(&STATIC.hw_lp_ctrl, 0x0, sizeof(STATIC.hw_lp_ctrl));
	dwc_cinit_memset32(&STATIC.hw_lp_accept_wait_window, (DDRCTL_DDR_DUAL_CHANNEL__OR__SINGLE_INST_DUALCH_EN  ==  1) ? ((DDRCTL_DDR_DUAL_CHANNEL_EN  ==  0) ? (DDRCTL_DCH_SYNC_DELAY_PIPES  +  2) : 2) : 2, sizeof(STATIC.hw_lp_accept_wait_window));
	dwc_cinit_memset32(&STATIC.cactive_in_mask, 0x0, sizeof(STATIC.cactive_in_mask));
	STATIC.bsm_clk_on = 0x3f;
	STATIC.auto_refab_en = 0x0;
	STATIC.per_bank_refresh = 0x0;
	STATIC.per_bank_refresh_opt_en = 0x0;
	STATIC.fixed_crit_refpb_bank_en = 0x0;
	STATIC.rank_dis_refresh = 0x0;
	STATIC.rfmsbc = 0x0;
	STATIC.dis_mpsmx_zqcl = 0x0;
	STATIC.zq_resistor_shared = 0x0;
	STATIC.t_trkcalccur = 0x100;
	STATIC.prefer_write = 0x0;
	STATIC.lpddr4_opt_act_timing = 0x0;
	STATIC.lpddr5_opt_act_timing = 0x1;
	STATIC.en_count_every_wr = 0x1;
	STATIC.dyn_bsm_mode = 0x1;
	STATIC.bank_hit_limit = 0x4;
	STATIC.dealloc_bsm_thr = (UMCTL2_NUM_BSM * 15 / 16);
	STATIC.dealloc_num_bsm_m1 = UMCTL2_NUM_BSM >> 4;
	STATIC.rd_act_idle_gap = 0x10;
	STATIC.wr_act_idle_gap = 0x8;
	STATIC.hwffc_odt_en = 0x0;
	STATIC.hwffc_vref_en = 0x0;
	STATIC.init_fsp = 0x1;
	STATIC.init_vrcg = 0x0;
	STATIC.target_vrcg = 0x0;
	STATIC.cke_power_down_mode = 0x0;
	STATIC.power_saving_ctrl_word = 0x0;
	STATIC.ctrl_word_num = 0x0;
	STATIC.skip_mrw_odtvref = 0x0;
	STATIC.skip_zq_stop_start = 0x0;
	STATIC.zq_interval = 0x1;
	STATIC.hwffc_mode = 0x0;
	STATIC.dq_nibble_map_0_3 = 0x0;
	STATIC.dq_nibble_map_4_7 = 0x0;
	STATIC.dq_nibble_map_8_11 = 0x0;
	STATIC.dq_nibble_map_12_15 = 0x0;
	STATIC.dq_nibble_map_16_19 = 0x0;
	STATIC.dq_nibble_map_20_23 = 0x0;
	STATIC.dq_nibble_map_24_27 = 0x0;
	STATIC.dq_nibble_map_28_31 = 0x0;
	STATIC.dq_nibble_map_32_35 = 0x0;
	STATIC.dq_nibble_map_36_39 = 0x0;
	STATIC.dq_nibble_map_40_43 = 0x0;
	STATIC.dq_nibble_map_44_47 = 0x0;
	STATIC.dq_nibble_map_48_51 = 0x0;
	STATIC.dq_nibble_map_52_55 = 0x0;
	STATIC.dq_nibble_map_56_59 = 0x0;
	STATIC.dq_nibble_map_60_63 = 0x0;
	STATIC.dq_nibble_map_cb_0_3 = 0x0;
	STATIC.dq_nibble_map_cb_4_7 = 0x0;
	STATIC.dq_nibble_map_cb_8_11 = 0x0;
	STATIC.dq_nibble_map_cb_12_15 = 0x0;
	STATIC.dis_dq_rank_swap = 0x0;
	STATIC.dfi_lp_en_pd = 0x0;
	STATIC.dfi_lp_en_sr = 0x0;
	STATIC.dfi_lp_en_dsm = 0x0;
	STATIC.dfi_lp_en_mpsm = 0x0;
	STATIC.dfi_lp_en_data = 0x0;
	STATIC.dfi_lp_data_req_en = 0x1;
	STATIC.dfi_lp_extra_gap = 0x0;
	STATIC.extra_gap_for_dfi_lp_data = 0x0;
	STATIC.dfi_phyupd_en = 0x1;
	STATIC.ctrlupd_pre_srx = 0x0;
	STATIC.dfi_phyupd_type0_wait_idle = 0x0;
	STATIC.dfi_phyupd_type1_wait_idle = 0x0;
	STATIC.dfi_phyupd_type2_wait_idle = 0x0;
	STATIC.dfi_phyupd_type3_wait_idle = 0x0;
	STATIC.phy_dbi_mode = 0x0;
	STATIC.dfi_data_cs_polarity = 0x0;
	STATIC.share_dfi_dram_clk_disable = 0x0;
	STATIC.dfi_channel_mode = 0x0;
	STATIC.dfi_phymstr_en = 0x1;
	STATIC.dfi_phymstr_blk_ref_x32 = 0x80;
	STATIC.ecc_mode = 0x0;
	STATIC.test_mode = 0x0;
	STATIC.ecc_type = 0x0;
	STATIC.ecc_ap_en = 0x1;
	STATIC.ecc_region_remap_en = 0x0;
	STATIC.ecc_ap_err_threshold = MEMC_MAX_INLINE_ECC_PER_BURST / 2 - 1;
	STATIC.ecc_region_map_other = 0x0;
	STATIC.ecc_region_map_granu = 0x0;
	STATIC.ecc_ap_mode = 0x0;
	STATIC.med_ecc_en = 0x0;
	STATIC.blk_channel_active_term = 0x1;
	STATIC.bypass_internal_ecc = 0x0;
	STATIC.kbd_en = 0x1;
	STATIC.eapar_en = 0x0;
	STATIC.parity_enable = 0x0;
	STATIC.bypass_internal_crc = 0x0;
	STATIC.crc_inc_dm = 0x0;
	STATIC.caparity_disable_before_sr = 0x1;
	STATIC.dfi_alert_async_mode = 0x0;
	dwc_cinit_memset32(&STATIC.capar_retry_enable, 0x0, sizeof(STATIC.capar_retry_enable));
	dwc_cinit_memset32(&STATIC.rd_ue_retry_enable, 0x0, sizeof(STATIC.rd_ue_retry_enable));
	dwc_cinit_memset32(&STATIC.rd_crc_retry_enable, 0x0, sizeof(STATIC.rd_crc_retry_enable));
	dwc_cinit_memset32(&STATIC.wr_crc_retry_enable, 0x0, sizeof(STATIC.wr_crc_retry_enable));
	dwc_cinit_memset32(&STATIC.wr_crc_retry_limiter, 0x4, sizeof(STATIC.wr_crc_retry_limiter));
	dwc_cinit_memset32(&STATIC.rd_crc_retry_limiter, 0x4, sizeof(STATIC.rd_crc_retry_limiter));
	dwc_cinit_memset32(&STATIC.rd_ue_retry_limiter, 0x4, sizeof(STATIC.rd_ue_retry_limiter));
	dwc_cinit_memset32(&STATIC.capar_retry_limiter, 0x4, sizeof(STATIC.capar_retry_limiter));
	dwc_cinit_memset32(&STATIC.make_multi_retry_fatl_err, 0x0, sizeof(STATIC.make_multi_retry_fatl_err));
	dwc_cinit_memset32(&STATIC.dis_capar_selfref_retry, 0x1, sizeof(STATIC.dis_capar_selfref_retry));
	dwc_cinit_memset32(&STATIC.dis_capar_powerdown_retry, 0x0, sizeof(STATIC.dis_capar_powerdown_retry));
	dwc_cinit_memset32(&STATIC.pre_sb_enable, 0x1, sizeof(STATIC.pre_sb_enable));
	dwc_cinit_memset32(&STATIC.pre_ab_enable, 0x1, sizeof(STATIC.pre_ab_enable));
	dwc_cinit_memset32(&STATIC.pre_slot_config, 0x0, sizeof(STATIC.pre_slot_config));
	dwc_cinit_memset32(&STATIC.ci_mrr_des1, 0x0, sizeof(STATIC.ci_mrr_des1));
	dwc_cinit_memset32(&STATIC.ci_mrr_des2, 0x5, sizeof(STATIC.ci_mrr_des2));
	dwc_cinit_memset32(&STATIC.ci_mrw_des1, 0x0, sizeof(STATIC.ci_mrw_des1));
	dwc_cinit_memset32(&STATIC.ci_mrw_des2, 0x2, sizeof(STATIC.ci_mrw_des2));
	dwc_cinit_memset32(&STATIC.ci_mpc_des1, 0x2, sizeof(STATIC.ci_mpc_des1));
	dwc_cinit_memset32(&STATIC.ci_mpc_des2, 0x2, sizeof(STATIC.ci_mpc_des2));
	dwc_cinit_memset32(&STATIC.ci_rfm_des1, 0x0, sizeof(STATIC.ci_rfm_des1));
	dwc_cinit_memset32(&STATIC.ci_rfm_des2, 0x2, sizeof(STATIC.ci_rfm_des2));
	dwc_cinit_memset32(&STATIC.powerdown_entry_ba_0, 0x0, sizeof(STATIC.powerdown_entry_ba_0));
	dwc_cinit_memset32(&STATIC.powerdown_entry_size_0, 0x5, sizeof(STATIC.powerdown_entry_size_0));
	dwc_cinit_memset32(&STATIC.powerdown_exit_ba_0, 0x8, sizeof(STATIC.powerdown_exit_ba_0));
	dwc_cinit_memset32(&STATIC.powerdown_exit_size_0, 0x7, sizeof(STATIC.powerdown_exit_size_0));
	dwc_cinit_memset32(&STATIC.powerdown_entry_ba_1, 0x10, sizeof(STATIC.powerdown_entry_ba_1));
	dwc_cinit_memset32(&STATIC.powerdown_entry_size_1, 0x5, sizeof(STATIC.powerdown_entry_size_1));
	dwc_cinit_memset32(&STATIC.powerdown_exit_ba_1, 0x18, sizeof(STATIC.powerdown_exit_ba_1));
	dwc_cinit_memset32(&STATIC.powerdown_exit_size_1, 0x7, sizeof(STATIC.powerdown_exit_size_1));
	dwc_cinit_memset32(&STATIC.powerdown_entry_ba_2, 0x20, sizeof(STATIC.powerdown_entry_ba_2));
	dwc_cinit_memset32(&STATIC.powerdown_entry_size_2, 0x5, sizeof(STATIC.powerdown_entry_size_2));
	dwc_cinit_memset32(&STATIC.powerdown_exit_ba_2, 0x28, sizeof(STATIC.powerdown_exit_ba_2));
	dwc_cinit_memset32(&STATIC.powerdown_exit_size_2, 0x7, sizeof(STATIC.powerdown_exit_size_2));
	dwc_cinit_memset32(&STATIC.powerdown_entry_ba_3, 0x30, sizeof(STATIC.powerdown_entry_ba_3));
	dwc_cinit_memset32(&STATIC.powerdown_entry_size_3, 0x5, sizeof(STATIC.powerdown_entry_size_3));
	dwc_cinit_memset32(&STATIC.powerdown_exit_ba_3, 0x38, sizeof(STATIC.powerdown_exit_ba_3));
	dwc_cinit_memset32(&STATIC.powerdown_exit_size_3, 0x7, sizeof(STATIC.powerdown_exit_size_3));
	dwc_cinit_memset32(&STATIC.selfref_entry1_ba_0, 0x40, sizeof(STATIC.selfref_entry1_ba_0));
	dwc_cinit_memset32(&STATIC.selfref_entry1_size_0, 0xb, sizeof(STATIC.selfref_entry1_size_0));
	dwc_cinit_memset32(&STATIC.selfref_entry2_ba_0, 0x4c, sizeof(STATIC.selfref_entry2_ba_0));
	dwc_cinit_memset32(&STATIC.selfref_entry2_size_0, 0x5, sizeof(STATIC.selfref_entry2_size_0));
	dwc_cinit_memset32(&STATIC.selfref_exit1_ba_0, 0x52, sizeof(STATIC.selfref_exit1_ba_0));
	dwc_cinit_memset32(&STATIC.selfref_exit1_size_0, 0x55, sizeof(STATIC.selfref_exit1_size_0));
	dwc_cinit_memset32(&STATIC.selfref_exit2_ba_0, 0xa8, sizeof(STATIC.selfref_exit2_ba_0));
	dwc_cinit_memset32(&STATIC.selfref_exit2_size_0, 0x0, sizeof(STATIC.selfref_exit2_size_0));
	dwc_cinit_memset32(&STATIC.rfm_raa_use_ecs_refab, 0x0, sizeof(STATIC.rfm_raa_use_ecs_refab));
	dwc_cinit_memset32(&STATIC.capar_retry_size, 0x2e, sizeof(STATIC.capar_retry_size));
	dwc_cinit_memset32(&STATIC.powerdown_idle_ctrl_0, 0x0, sizeof(STATIC.powerdown_idle_ctrl_0));
	dwc_cinit_memset32(&STATIC.powerdown_idle_ctrl_1, 0x0, sizeof(STATIC.powerdown_idle_ctrl_1));
	STATIC.t_selfref_exit_stagger = 0x0;
	dwc_cinit_memset32(&STATIC.pde_odt_ctrl, 0x0, sizeof(STATIC.pde_odt_ctrl));
	dwc_cinit_memset32(&STATIC.pd_mrr_nt_odt_en, 0x1, sizeof(STATIC.pd_mrr_nt_odt_en));
	dwc_cinit_memset32(&STATIC.cmd_timer_x32, 0xfff, sizeof(STATIC.cmd_timer_x32));
	STATIC.dis_wc = 0x0;
	STATIC.dis_rd_bypass = 0x0;
	STATIC.dis_act_bypass = 0x0;
	dwc_cinit_memset32(&STATIC.hw_ref_zq_en, 0x0, sizeof(STATIC.hw_ref_zq_en));
	STATIC.sw_done = 0x1;
	STATIC.dimm_stagger_cs_en = 0x0;
	STATIC.dimm_addr_mirr_en = 0x0;
	STATIC.dimm_output_inv_en = 0x0;
	STATIC.mrs_a17_en = 0x0;
	STATIC.mrs_bg1_en = 0x0;
	STATIC.dimm_dis_bg_mirroring = 0x0;
	STATIC.lrdimm_bcom_cmd_prot = 0x0;
	STATIC.rcd_num = 0x0;
	STATIC.dimm_type = 0x0;
	STATIC.rcd_a_output_disabled = 0x0;
	STATIC.rcd_b_output_disabled = 0x0;
	STATIC.dual_channel_en = 0x1;
	STATIC.max_rank_rd = 0xf;
	STATIC.max_rank_wr = 0x0;
	STATIC.max_logical_rank_rd = 0xf;
	STATIC.max_logical_rank_wr = 0x0;
	dwc_cinit_memset32(&STATIC.rank0_wr_odt, 0x1, sizeof(STATIC.rank0_wr_odt));
	dwc_cinit_memset32(&STATIC.rank0_rd_odt, 0x1, sizeof(STATIC.rank0_rd_odt));
	dwc_cinit_memset32(&STATIC.rank1_wr_odt, (MEMC_NUM_RANKS > 1) ? 0x2 : 0x0, sizeof(STATIC.rank1_wr_odt));
	dwc_cinit_memset32(&STATIC.rank1_rd_odt, (MEMC_NUM_RANKS > 1) ? 0x2 : 0x0, sizeof(STATIC.rank1_rd_odt));
	dwc_cinit_memset32(&STATIC.rank2_wr_odt, (MEMC_NUM_RANKS >= 4) ? 0x4 : 0x0, sizeof(STATIC.rank2_wr_odt));
	dwc_cinit_memset32(&STATIC.rank2_rd_odt, (MEMC_NUM_RANKS >= 4) ? 0x4 : 0x0, sizeof(STATIC.rank2_rd_odt));
	dwc_cinit_memset32(&STATIC.rank3_wr_odt, (MEMC_NUM_RANKS >= 4) ? 0x8 : 0x0, sizeof(STATIC.rank3_wr_odt));
	dwc_cinit_memset32(&STATIC.rank3_rd_odt, (MEMC_NUM_RANKS >= 4) ? 0x8 : 0x0, sizeof(STATIC.rank3_rd_odt));
	STATIC.sw_static_unlock = 0x0;
	dwc_cinit_memset32(&STATIC.pre_cke_x1024, 0x4e, sizeof(STATIC.pre_cke_x1024));
	dwc_cinit_memset32(&STATIC.post_cke_x1024, 0x2, sizeof(STATIC.post_cke_x1024));
	dwc_cinit_memset32(&STATIC.dev_zqinit_x32, 0x10, sizeof(STATIC.dev_zqinit_x32));
	dwc_cinit_memset32(&STATIC.ime_en, 0x0, sizeof(STATIC.ime_en));
	STATIC.addrmap_dch_bit0 = 0x0;
	dwc_cinit_memset32(&STATIC.addrmap_cs_bit0, 0x0, sizeof(STATIC.addrmap_cs_bit0));
	dwc_cinit_memset32(&STATIC.addrmap_cs_bit1, 0x0, sizeof(STATIC.addrmap_cs_bit1));
	dwc_cinit_memset32(&STATIC.addrmap_cs_bit2, 0x0, sizeof(STATIC.addrmap_cs_bit2));
	dwc_cinit_memset32(&STATIC.addrmap_cs_bit3, 0x0, sizeof(STATIC.addrmap_cs_bit3));
	dwc_cinit_memset32(&STATIC.addrmap_cid_b0, 0x0, sizeof(STATIC.addrmap_cid_b0));
	dwc_cinit_memset32(&STATIC.addrmap_cid_b1, 0x0, sizeof(STATIC.addrmap_cid_b1));
	dwc_cinit_memset32(&STATIC.addrmap_cid_b2, 0x0, sizeof(STATIC.addrmap_cid_b2));
	dwc_cinit_memset32(&STATIC.addrmap_cid_b3, 0x0, sizeof(STATIC.addrmap_cid_b3));
	dwc_cinit_memset32(&STATIC.addrmap_bank_b0, 0x0, sizeof(STATIC.addrmap_bank_b0));
	dwc_cinit_memset32(&STATIC.addrmap_bank_b1, 0x0, sizeof(STATIC.addrmap_bank_b1));
	dwc_cinit_memset32(&STATIC.addrmap_bank_b2, 0x0, sizeof(STATIC.addrmap_bank_b2));
	dwc_cinit_memset32(&STATIC.addrmap_bg_b0, 0x0, sizeof(STATIC.addrmap_bg_b0));
	dwc_cinit_memset32(&STATIC.addrmap_bg_b1, 0x0, sizeof(STATIC.addrmap_bg_b1));
	dwc_cinit_memset32(&STATIC.addrmap_bg_b2, 0x0, sizeof(STATIC.addrmap_bg_b2));
	dwc_cinit_memset32(&STATIC.addrmap_col_b7, 0x0, sizeof(STATIC.addrmap_col_b7));
	dwc_cinit_memset32(&STATIC.addrmap_col_b8, 0x0, sizeof(STATIC.addrmap_col_b8));
	dwc_cinit_memset32(&STATIC.addrmap_col_b9, 0x0, sizeof(STATIC.addrmap_col_b9));
	dwc_cinit_memset32(&STATIC.addrmap_col_b10, 0x0, sizeof(STATIC.addrmap_col_b10));
	dwc_cinit_memset32(&STATIC.addrmap_col_b3, 0x0, sizeof(STATIC.addrmap_col_b3));
	dwc_cinit_memset32(&STATIC.addrmap_col_b4, 0x0, sizeof(STATIC.addrmap_col_b4));
	dwc_cinit_memset32(&STATIC.addrmap_col_b5, 0x0, sizeof(STATIC.addrmap_col_b5));
	dwc_cinit_memset32(&STATIC.addrmap_col_b6, 0x0, sizeof(STATIC.addrmap_col_b6));
	dwc_cinit_memset32(&STATIC.addrmap_row_b14, 0x0, sizeof(STATIC.addrmap_row_b14));
	dwc_cinit_memset32(&STATIC.addrmap_row_b15, 0x0, sizeof(STATIC.addrmap_row_b15));
	dwc_cinit_memset32(&STATIC.addrmap_row_b16, 0x0, sizeof(STATIC.addrmap_row_b16));
	dwc_cinit_memset32(&STATIC.addrmap_row_b17, 0x0, sizeof(STATIC.addrmap_row_b17));
	dwc_cinit_memset32(&STATIC.addrmap_row_b10, 0x0, sizeof(STATIC.addrmap_row_b10));
	dwc_cinit_memset32(&STATIC.addrmap_row_b11, 0x0, sizeof(STATIC.addrmap_row_b11));
	dwc_cinit_memset32(&STATIC.addrmap_row_b12, 0x0, sizeof(STATIC.addrmap_row_b12));
	dwc_cinit_memset32(&STATIC.addrmap_row_b13, 0x0, sizeof(STATIC.addrmap_row_b13));
	dwc_cinit_memset32(&STATIC.addrmap_row_b6, 0x0, sizeof(STATIC.addrmap_row_b6));
	dwc_cinit_memset32(&STATIC.addrmap_row_b7, 0x0, sizeof(STATIC.addrmap_row_b7));
	dwc_cinit_memset32(&STATIC.addrmap_row_b8, 0x0, sizeof(STATIC.addrmap_row_b8));
	dwc_cinit_memset32(&STATIC.addrmap_row_b9, 0x0, sizeof(STATIC.addrmap_row_b9));
	dwc_cinit_memset32(&STATIC.addrmap_row_b2, 0x0, sizeof(STATIC.addrmap_row_b2));
	dwc_cinit_memset32(&STATIC.addrmap_row_b3, 0x0, sizeof(STATIC.addrmap_row_b3));
	dwc_cinit_memset32(&STATIC.addrmap_row_b4, 0x0, sizeof(STATIC.addrmap_row_b4));
	dwc_cinit_memset32(&STATIC.addrmap_row_b5, 0x0, sizeof(STATIC.addrmap_row_b5));
	dwc_cinit_memset32(&STATIC.addrmap_row_b0, 0x0, sizeof(STATIC.addrmap_row_b0));
	dwc_cinit_memset32(&STATIC.addrmap_row_b1, 0x0, sizeof(STATIC.addrmap_row_b1));
	STATIC.nonbinary_device_density = 0x0;
	STATIC.bank_hash_en = 0x0;
	STATIC.lpddr_mixed_pkg_en = 0x0;
	STATIC.lpddr_mixed_pkg_x16_size = 0x0;
	STATIC.addrmap_lut_bypass = 0x1;
	STATIC.addrmap_use_lut_cs = 0x0;
	STATIC.addrmap_lut_rank_type = 0x0;
	STATIC.addrmap_lut_bit0 = 0x0;
	STATIC.addrmap_lut_bit0_valid = 0x0;
	STATIC.addrmap_lut_bit1 = 0x0;
	STATIC.addrmap_lut_bit1_valid = 0x0;
	STATIC.addrmap_lut_max_active_hif_addr_offset = 0x0;
	STATIC.go2critical_en = 0x0;
	STATIC.pagematch_limit = 0x0;
	STATIC.dch_density_ratio = 0x0;
	dwc_cinit_memset32(&STATIC.rd_port_priority, 0x1f, sizeof(STATIC.rd_port_priority));
	dwc_cinit_memset32(&STATIC.rd_port_aging_en, 0x1, sizeof(STATIC.rd_port_aging_en));
	dwc_cinit_memset32(&STATIC.rd_port_urgent_en, 0x0, sizeof(STATIC.rd_port_urgent_en));
	dwc_cinit_memset32(&STATIC.rd_port_pagematch_en, (MEMC_DDR4_EN == 1) ? 0x0 : 0x1, sizeof(STATIC.rd_port_pagematch_en));
	dwc_cinit_memset32(&STATIC.rrb_lock_threshold, 0x0, sizeof(STATIC.rrb_lock_threshold));
	dwc_cinit_memset32(&STATIC.wr_port_priority, 0x1f, sizeof(STATIC.wr_port_priority));
	dwc_cinit_memset32(&STATIC.wr_port_aging_en, 0x1, sizeof(STATIC.wr_port_aging_en));
	dwc_cinit_memset32(&STATIC.wr_port_urgent_en, 0x0, sizeof(STATIC.wr_port_urgent_en));
	dwc_cinit_memset32(&STATIC.wr_port_pagematch_en, 0x1, sizeof(STATIC.wr_port_pagematch_en));
	dwc_cinit_memset32(&STATIC.snf_mode, 0x1, sizeof(STATIC.snf_mode));
	dwc_cinit_memset32(&STATIC.base_addr, 0x0, sizeof(STATIC.base_addr));
	dwc_cinit_memset32(&STATIC.nblocks, 0x0, sizeof(STATIC.nblocks));
	STATIC.port_data_channel_0 = 0x0;
	STATIC.port_data_channel_1 = 0x0;
	STATIC.port_data_channel_2 = 0x0;
	STATIC.port_data_channel_3 = 0x0;
	STATIC.port_data_channel_4 = 0x0;
	STATIC.port_data_channel_5 = 0x0;
	STATIC.port_data_channel_6 = 0x0;
	STATIC.port_data_channel_7 = 0x0;
	STATIC.port_data_channel_8 = 0x0;
	STATIC.port_data_channel_9 = 0x0;
	STATIC.port_data_channel_10 = 0x0;
	STATIC.port_data_channel_11 = 0x0;
	STATIC.port_data_channel_12 = 0x0;
	STATIC.port_data_channel_13 = 0x0;
	STATIC.port_data_channel_14 = 0x0;
	STATIC.port_data_channel_15 = 0x0;
	dwc_cinit_memset32(&STATIC.cbusy_select, 0x1, sizeof(STATIC.cbusy_select));
	dwc_cinit_memset32(&STATIC.dbg_dis_wrptl_rmw_be_eval, 0x0, sizeof(STATIC.dbg_dis_wrptl_rmw_be_eval));
	dwc_cinit_memset32(&STATIC.prc_exp_cnt, 0x20, sizeof(STATIC.prc_exp_cnt));
	dwc_cinit_memset32(&STATIC.exp_cnt_div, 0x2, sizeof(STATIC.exp_cnt_div));
	dwc_cinit_memset32(&STATIC.rpq_lpr_min, 0x0, sizeof(STATIC.rpq_lpr_min));
	dwc_cinit_memset32(&STATIC.rpq_hpr_min, 0x0, sizeof(STATIC.rpq_hpr_min));
	dwc_cinit_memset32(&STATIC.cam_busy_threshold_hpr, DDRCTL_CHB_CAM_BUSY_THR_HPR, sizeof(STATIC.cam_busy_threshold_hpr));
	dwc_cinit_memset32(&STATIC.cam_free_threshold_hpr, DDRCTL_CHB_CAM_FREE_THR_HPR, sizeof(STATIC.cam_free_threshold_hpr));
	dwc_cinit_memset32(&STATIC.cam_middle_threshold_hpr, DDRCTL_CHB_CAM_MIDDLE_THR_LPR, sizeof(STATIC.cam_middle_threshold_hpr));
	dwc_cinit_memset32(&STATIC.cam_busy_threshold_lpr, DDRCTL_CHB_CAM_BUSY_THR_LPR, sizeof(STATIC.cam_busy_threshold_lpr));
	dwc_cinit_memset32(&STATIC.cam_free_threshold_lpr, DDRCTL_CHB_CAM_FREE_THR_LPR, sizeof(STATIC.cam_free_threshold_lpr));
	dwc_cinit_memset32(&STATIC.cam_middle_threshold_lpr, DDRCTL_CHB_CAM_MIDDLE_THR_LPR, sizeof(STATIC.cam_middle_threshold_lpr));
	dwc_cinit_memset32(&STATIC.cam_busy_threshold_wr, DDRCTL_CHB_CAM_BUSY_THR_WR, sizeof(STATIC.cam_busy_threshold_wr));
	dwc_cinit_memset32(&STATIC.cam_free_threshold_wr, DDRCTL_CHB_CAM_FREE_THR_WR, sizeof(STATIC.cam_free_threshold_wr));
	dwc_cinit_memset32(&STATIC.cam_middle_threshold_wr, DDRCTL_CHB_CAM_MIDDLE_THR_WR, sizeof(STATIC.cam_middle_threshold_wr));
	dwc_cinit_memset32(&STATIC.tz_sec_inv_en, 0x0, sizeof(STATIC.tz_sec_inv_en));
	dwc_cinit_memset32(&STATIC.tz_reg_sp, 0x3, sizeof(STATIC.tz_reg_sp));
	dwc_cinit_memset32(&STATIC.tz_base_addr_low, 0x0, sizeof(STATIC.tz_base_addr_low));
	dwc_cinit_memset32(&STATIC.tz_base_addr_high, 0x0, sizeof(STATIC.tz_base_addr_high));
	dwc_cinit_memset32(&STATIC.tz_region_en, 0x0, sizeof(STATIC.tz_region_en));
	dwc_cinit_memset32(&STATIC.tz_region_size, 0xe, sizeof(STATIC.tz_region_size));
	dwc_cinit_memset32(&STATIC.tz_subregion_disable, 0x0, sizeof(STATIC.tz_subregion_disable));
	STATIC.dfi_lp_wakeup_pd = 0x0;
	STATIC.dfi_lp_wakeup_sr = 0x0;
	STATIC.dfi_lp_wakeup_dsm = 0x0;
	STATIC.dfi_lp_wakeup_mpsm = 0x0;
	STATIC.dfi_lp_wakeup_data = 0x0;
	STATIC.dfi_tlp_resp = 0x7;
	STATIC.dfi_t_ctrlup_min = 0x3;
	STATIC.dfi_t_ctrlup_max = 0x40;
	STATIC.dfi_ctrlup_gap = 0x1c;
	dwc_cinit_memset32(&STATIC.dfi_t_ctrlupd_interval_max_x1024, 0x1, sizeof(STATIC.dfi_t_ctrlupd_interval_max_x1024));
	dwc_cinit_memset32(&STATIC.dfi_t_ctrlupd_interval_min_x1024, 0x1, sizeof(STATIC.dfi_t_ctrlupd_interval_min_x1024));
	STATIC.dfi_t_ctrlmsg_resp = 0x4;
	dwc_cinit_memset32(&STATIC.ctrlupd_after_dqsosc, 0x0, sizeof(STATIC.ctrlupd_after_dqsosc));
	dwc_cinit_memset32(&STATIC.ppt2_override, 0x0, sizeof(STATIC.ppt2_override));
	dwc_cinit_memset32(&STATIC.dfi_t_ctrlupd_burst_interval_x8, 0x1, sizeof(STATIC.dfi_t_ctrlupd_burst_interval_x8));
	dwc_cinit_memset32(&STATIC.refresh_timer_lr_offset_x32, 0x0, sizeof(STATIC.refresh_timer_lr_offset_x32));
	dwc_cinit_memset32(&STATIC.refresh_timer_lr_offset_x32_2, 0x0, sizeof(STATIC.refresh_timer_lr_offset_x32_2));
	dwc_cinit_memset32(&STATIC.t_zq_long_nop, 0x200, sizeof(STATIC.t_zq_long_nop));
	dwc_cinit_memset32(&STATIC.t_zq_short_nop, 0x40, sizeof(STATIC.t_zq_short_nop));
	dwc_cinit_memset32(&STATIC.t_zq_short_interval_x1024, 0x100, sizeof(STATIC.t_zq_short_interval_x1024));
	dwc_cinit_memset32(&STATIC.t_zq_reset_nop, 0x20, sizeof(STATIC.t_zq_reset_nop));
	dwc_cinit_memset32(&STATIC.t_zq_stop, 0x18, sizeof(STATIC.t_zq_stop));
	dwc_cinit_memset32(&STATIC.t_zq_long_nop_2, 0x200, sizeof(STATIC.t_zq_long_nop_2));
	dwc_cinit_memset32(&STATIC.t_zq_short_nop_2, 0x40, sizeof(STATIC.t_zq_short_nop_2));
	dwc_cinit_memset32(&STATIC.dvfsq_enable, 0x0, sizeof(STATIC.dvfsq_enable));
	dwc_cinit_memset32(&STATIC.pageclose_timer, 0x0, sizeof(STATIC.pageclose_timer));
	dwc_cinit_memset32(&STATIC.rdwr_idle_gap, 0x0, sizeof(STATIC.rdwr_idle_gap));
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.key_done_en, 0x0, sizeof(STATIC.key_done_en));
	dwc_cinit_memset32(&STATIC.key_miss_err_en, 0x0, sizeof(STATIC.key_miss_err_en));
	dwc_cinit_memset32(&STATIC.key_collision_err_en, 0x0, sizeof(STATIC.key_collision_err_en));
	dwc_cinit_memset32(&STATIC.apb_timing_err_en, 0x0, sizeof(STATIC.apb_timing_err_en));
	dwc_cinit_memset32(&STATIC.key_size_err_en, 0x0, sizeof(STATIC.key_size_err_en));
	dwc_cinit_memset32(&STATIC.reg_parity_err_en, 0x0, sizeof(STATIC.reg_parity_err_en));
	dwc_cinit_memset32(&STATIC.glbl, 0x0, sizeof(STATIC.glbl)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.key0_usage_hit_en, 0x0, sizeof(STATIC.key0_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key1_usage_hit_en, 0x0, sizeof(STATIC.key1_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key2_usage_hit_en, 0x0, sizeof(STATIC.key2_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key3_usage_hit_en, 0x0, sizeof(STATIC.key3_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key4_usage_hit_en, 0x0, sizeof(STATIC.key4_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key5_usage_hit_en, 0x0, sizeof(STATIC.key5_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key6_usage_hit_en, 0x0, sizeof(STATIC.key6_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key7_usage_hit_en, 0x0, sizeof(STATIC.key7_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key8_usage_hit_en, 0x0, sizeof(STATIC.key8_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key9_usage_hit_en, 0x0, sizeof(STATIC.key9_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key10_usage_hit_en, 0x0, sizeof(STATIC.key10_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key11_usage_hit_en, 0x0, sizeof(STATIC.key11_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key12_usage_hit_en, 0x0, sizeof(STATIC.key12_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key13_usage_hit_en, 0x0, sizeof(STATIC.key13_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key14_usage_hit_en, 0x0, sizeof(STATIC.key14_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key15_usage_hit_en, 0x0, sizeof(STATIC.key15_usage_hit_en));
	dwc_cinit_memset32(&STATIC.key0_swapped_en, 0x0, sizeof(STATIC.key0_swapped_en));
	dwc_cinit_memset32(&STATIC.key1_swapped_en, 0x0, sizeof(STATIC.key1_swapped_en));
	dwc_cinit_memset32(&STATIC.key2_swapped_en, 0x0, sizeof(STATIC.key2_swapped_en));
	dwc_cinit_memset32(&STATIC.key3_swapped_en, 0x0, sizeof(STATIC.key3_swapped_en));
	dwc_cinit_memset32(&STATIC.key4_swapped_en, 0x0, sizeof(STATIC.key4_swapped_en));
	dwc_cinit_memset32(&STATIC.key5_swapped_en, 0x0, sizeof(STATIC.key5_swapped_en));
	dwc_cinit_memset32(&STATIC.key6_swapped_en, 0x0, sizeof(STATIC.key6_swapped_en));
	dwc_cinit_memset32(&STATIC.key7_swapped_en, 0x0, sizeof(STATIC.key7_swapped_en));
	dwc_cinit_memset32(&STATIC.key8_swapped_en, 0x0, sizeof(STATIC.key8_swapped_en));
	dwc_cinit_memset32(&STATIC.key9_swapped_en, 0x0, sizeof(STATIC.key9_swapped_en));
	dwc_cinit_memset32(&STATIC.key10_swapped_en, 0x0, sizeof(STATIC.key10_swapped_en));
	dwc_cinit_memset32(&STATIC.key11_swapped_en, 0x0, sizeof(STATIC.key11_swapped_en));
	dwc_cinit_memset32(&STATIC.key12_swapped_en, 0x0, sizeof(STATIC.key12_swapped_en));
	dwc_cinit_memset32(&STATIC.key13_swapped_en, 0x0, sizeof(STATIC.key13_swapped_en));
	dwc_cinit_memset32(&STATIC.key14_swapped_en, 0x0, sizeof(STATIC.key14_swapped_en));
	dwc_cinit_memset32(&STATIC.key15_swapped_en, 0x0, sizeof(STATIC.key15_swapped_en)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_ADDR_EN 
	dwc_cinit_memset32(&STATIC.region0_addr_low_31_0, 0x0, sizeof(STATIC.region0_addr_low_31_0)); 
#endif //DWC_IME_REGION_ADDR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_ADDR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32 
	dwc_cinit_memset32(&STATIC.region0_addr_low_63_32, 0x0, sizeof(STATIC.region0_addr_low_63_32)); 
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_ADDR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_ADDR_EN 
	dwc_cinit_memset32(&STATIC.region0_addr_high_31_0, 0x0, sizeof(STATIC.region0_addr_high_31_0)); 
#endif //DWC_IME_REGION_ADDR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_ADDR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32 
	dwc_cinit_memset32(&STATIC.region0_addr_high_63_32, 0x0, sizeof(STATIC.region0_addr_high_63_32)); 
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_ADDR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_1 
	dwc_cinit_memset32(&STATIC.region1_addr_low_31_0, 0x0, sizeof(STATIC.region1_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_1
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_1 
	dwc_cinit_memset32(&STATIC.region1_addr_low_63_32, 0x0, sizeof(STATIC.region1_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_1
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_1 
	dwc_cinit_memset32(&STATIC.region1_addr_high_31_0, 0x0, sizeof(STATIC.region1_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_1
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_1 
	dwc_cinit_memset32(&STATIC.region1_addr_high_63_32, 0x0, sizeof(STATIC.region1_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_1
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_2 
	dwc_cinit_memset32(&STATIC.region2_addr_low_31_0, 0x0, sizeof(STATIC.region2_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_2
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_2 
	dwc_cinit_memset32(&STATIC.region2_addr_low_63_32, 0x0, sizeof(STATIC.region2_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_2
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_2 
	dwc_cinit_memset32(&STATIC.region2_addr_high_31_0, 0x0, sizeof(STATIC.region2_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_2
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_2 
	dwc_cinit_memset32(&STATIC.region2_addr_high_63_32, 0x0, sizeof(STATIC.region2_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_2
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_3 
	dwc_cinit_memset32(&STATIC.region3_addr_low_31_0, 0x0, sizeof(STATIC.region3_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_3
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_3 
	dwc_cinit_memset32(&STATIC.region3_addr_low_63_32, 0x0, sizeof(STATIC.region3_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_3
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_3 
	dwc_cinit_memset32(&STATIC.region3_addr_high_31_0, 0x0, sizeof(STATIC.region3_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_3
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_3 
	dwc_cinit_memset32(&STATIC.region3_addr_high_63_32, 0x0, sizeof(STATIC.region3_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_3
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_4 
	dwc_cinit_memset32(&STATIC.region4_addr_low_31_0, 0x0, sizeof(STATIC.region4_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_4
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_4 
	dwc_cinit_memset32(&STATIC.region4_addr_low_63_32, 0x0, sizeof(STATIC.region4_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_4
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_4 
	dwc_cinit_memset32(&STATIC.region4_addr_high_31_0, 0x0, sizeof(STATIC.region4_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_4
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_4 
	dwc_cinit_memset32(&STATIC.region4_addr_high_63_32, 0x0, sizeof(STATIC.region4_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_4
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_5 
	dwc_cinit_memset32(&STATIC.region5_addr_low_31_0, 0x0, sizeof(STATIC.region5_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_5
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_5 
	dwc_cinit_memset32(&STATIC.region5_addr_low_63_32, 0x0, sizeof(STATIC.region5_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_5
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_5 
	dwc_cinit_memset32(&STATIC.region5_addr_high_31_0, 0x0, sizeof(STATIC.region5_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_5
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_5 
	dwc_cinit_memset32(&STATIC.region5_addr_high_63_32, 0x0, sizeof(STATIC.region5_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_5
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_6 
	dwc_cinit_memset32(&STATIC.region6_addr_low_31_0, 0x0, sizeof(STATIC.region6_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_6
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_6 
	dwc_cinit_memset32(&STATIC.region6_addr_low_63_32, 0x0, sizeof(STATIC.region6_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_6
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_6 
	dwc_cinit_memset32(&STATIC.region6_addr_high_31_0, 0x0, sizeof(STATIC.region6_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_6
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_6 
	dwc_cinit_memset32(&STATIC.region6_addr_high_63_32, 0x0, sizeof(STATIC.region6_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_6
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_7 
	dwc_cinit_memset32(&STATIC.region7_addr_low_31_0, 0x0, sizeof(STATIC.region7_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_7
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_7 
	dwc_cinit_memset32(&STATIC.region7_addr_low_63_32, 0x0, sizeof(STATIC.region7_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_7
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_7 
	dwc_cinit_memset32(&STATIC.region7_addr_high_31_0, 0x0, sizeof(STATIC.region7_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_7
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_7 
	dwc_cinit_memset32(&STATIC.region7_addr_high_63_32, 0x0, sizeof(STATIC.region7_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_7
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_8 
	dwc_cinit_memset32(&STATIC.region8_addr_low_31_0, 0x0, sizeof(STATIC.region8_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_8
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_8 
	dwc_cinit_memset32(&STATIC.region8_addr_low_63_32, 0x0, sizeof(STATIC.region8_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_8
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_8 
	dwc_cinit_memset32(&STATIC.region8_addr_high_31_0, 0x0, sizeof(STATIC.region8_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_8
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_8 
	dwc_cinit_memset32(&STATIC.region8_addr_high_63_32, 0x0, sizeof(STATIC.region8_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_8
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_9 
	dwc_cinit_memset32(&STATIC.region9_addr_low_31_0, 0x0, sizeof(STATIC.region9_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_9
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_9 
	dwc_cinit_memset32(&STATIC.region9_addr_low_63_32, 0x0, sizeof(STATIC.region9_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_9
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_9 
	dwc_cinit_memset32(&STATIC.region9_addr_high_31_0, 0x0, sizeof(STATIC.region9_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_9
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_9 
	dwc_cinit_memset32(&STATIC.region9_addr_high_63_32, 0x0, sizeof(STATIC.region9_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_9
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_10 
	dwc_cinit_memset32(&STATIC.region10_addr_low_31_0, 0x0, sizeof(STATIC.region10_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_10
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_10 
	dwc_cinit_memset32(&STATIC.region10_addr_low_63_32, 0x0, sizeof(STATIC.region10_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_10
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_10 
	dwc_cinit_memset32(&STATIC.region10_addr_high_31_0, 0x0, sizeof(STATIC.region10_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_10
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_10 
	dwc_cinit_memset32(&STATIC.region10_addr_high_63_32, 0x0, sizeof(STATIC.region10_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_10
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_11 
	dwc_cinit_memset32(&STATIC.region11_addr_low_31_0, 0x0, sizeof(STATIC.region11_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_11
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_11 
	dwc_cinit_memset32(&STATIC.region11_addr_low_63_32, 0x0, sizeof(STATIC.region11_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_11
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_11 
	dwc_cinit_memset32(&STATIC.region11_addr_high_31_0, 0x0, sizeof(STATIC.region11_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_11
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_11 
	dwc_cinit_memset32(&STATIC.region11_addr_high_63_32, 0x0, sizeof(STATIC.region11_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_11
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_12 
	dwc_cinit_memset32(&STATIC.region12_addr_low_31_0, 0x0, sizeof(STATIC.region12_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_12
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_12 
	dwc_cinit_memset32(&STATIC.region12_addr_low_63_32, 0x0, sizeof(STATIC.region12_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_12
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_12 
	dwc_cinit_memset32(&STATIC.region12_addr_high_31_0, 0x0, sizeof(STATIC.region12_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_12
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_12 
	dwc_cinit_memset32(&STATIC.region12_addr_high_63_32, 0x0, sizeof(STATIC.region12_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_12
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_13 
	dwc_cinit_memset32(&STATIC.region13_addr_low_31_0, 0x0, sizeof(STATIC.region13_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_13
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_13 
	dwc_cinit_memset32(&STATIC.region13_addr_low_63_32, 0x0, sizeof(STATIC.region13_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_13
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_13 
	dwc_cinit_memset32(&STATIC.region13_addr_high_31_0, 0x0, sizeof(STATIC.region13_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_13
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_13 
	dwc_cinit_memset32(&STATIC.region13_addr_high_63_32, 0x0, sizeof(STATIC.region13_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_13
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_14 
	dwc_cinit_memset32(&STATIC.region14_addr_low_31_0, 0x0, sizeof(STATIC.region14_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_14
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_14 
	dwc_cinit_memset32(&STATIC.region14_addr_low_63_32, 0x0, sizeof(STATIC.region14_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_14
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_14 
	dwc_cinit_memset32(&STATIC.region14_addr_high_31_0, 0x0, sizeof(STATIC.region14_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_14
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_14 
	dwc_cinit_memset32(&STATIC.region14_addr_high_63_32, 0x0, sizeof(STATIC.region14_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_14
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_15 
	dwc_cinit_memset32(&STATIC.region15_addr_low_31_0, 0x0, sizeof(STATIC.region15_addr_low_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_15
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_15 
	dwc_cinit_memset32(&STATIC.region15_addr_low_63_32, 0x0, sizeof(STATIC.region15_addr_low_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_15
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_NUM_REGIONS_GT_15 
	dwc_cinit_memset32(&STATIC.region15_addr_high_31_0, 0x0, sizeof(STATIC.region15_addr_high_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_15
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_REGION_MGR_EN
#ifdef DWC_IME_BYTE_ADDR_WIDTH_GT_32
#ifdef DWC_IME_NUM_REGIONS_GT_15 
	dwc_cinit_memset32(&STATIC.region15_addr_high_63_32, 0x0, sizeof(STATIC.region15_addr_high_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_15
#endif //DWC_IME_BYTE_ADDR_WIDTH_GT_32
#endif //DWC_IME_REGION_MGR_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.key0_usage_thr_31_0, 0x0, sizeof(STATIC.key0_usage_thr_31_0)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.key0_usage_thr_63_32, 0x0, sizeof(STATIC.key0_usage_thr_63_32)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_1 
	dwc_cinit_memset32(&STATIC.key1_usage_thr_31_0, 0x0, sizeof(STATIC.key1_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_1
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_1 
	dwc_cinit_memset32(&STATIC.key1_usage_thr_63_32, 0x0, sizeof(STATIC.key1_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_1
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_2 
	dwc_cinit_memset32(&STATIC.key2_usage_thr_31_0, 0x0, sizeof(STATIC.key2_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_2
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_2 
	dwc_cinit_memset32(&STATIC.key2_usage_thr_63_32, 0x0, sizeof(STATIC.key2_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_2
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_3 
	dwc_cinit_memset32(&STATIC.key3_usage_thr_31_0, 0x0, sizeof(STATIC.key3_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_3
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_3 
	dwc_cinit_memset32(&STATIC.key3_usage_thr_63_32, 0x0, sizeof(STATIC.key3_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_3
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_4 
	dwc_cinit_memset32(&STATIC.key4_usage_thr_31_0, 0x0, sizeof(STATIC.key4_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_4
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_4 
	dwc_cinit_memset32(&STATIC.key4_usage_thr_63_32, 0x0, sizeof(STATIC.key4_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_4
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_5 
	dwc_cinit_memset32(&STATIC.key5_usage_thr_31_0, 0x0, sizeof(STATIC.key5_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_5
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_5 
	dwc_cinit_memset32(&STATIC.key5_usage_thr_63_32, 0x0, sizeof(STATIC.key5_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_5
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_6 
	dwc_cinit_memset32(&STATIC.key6_usage_thr_31_0, 0x0, sizeof(STATIC.key6_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_6
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_6 
	dwc_cinit_memset32(&STATIC.key6_usage_thr_63_32, 0x0, sizeof(STATIC.key6_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_6
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_7 
	dwc_cinit_memset32(&STATIC.key7_usage_thr_31_0, 0x0, sizeof(STATIC.key7_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_7
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_7 
	dwc_cinit_memset32(&STATIC.key7_usage_thr_63_32, 0x0, sizeof(STATIC.key7_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_7
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_8 
	dwc_cinit_memset32(&STATIC.key8_usage_thr_31_0, 0x0, sizeof(STATIC.key8_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_8
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_8 
	dwc_cinit_memset32(&STATIC.key8_usage_thr_63_32, 0x0, sizeof(STATIC.key8_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_8
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_9 
	dwc_cinit_memset32(&STATIC.key9_usage_thr_31_0, 0x0, sizeof(STATIC.key9_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_9
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_9 
	dwc_cinit_memset32(&STATIC.key9_usage_thr_63_32, 0x0, sizeof(STATIC.key9_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_9
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_10 
	dwc_cinit_memset32(&STATIC.key10_usage_thr_31_0, 0x0, sizeof(STATIC.key10_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_10
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_10 
	dwc_cinit_memset32(&STATIC.key10_usage_thr_63_32, 0x0, sizeof(STATIC.key10_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_10
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_11 
	dwc_cinit_memset32(&STATIC.key11_usage_thr_31_0, 0x0, sizeof(STATIC.key11_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_11
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_11 
	dwc_cinit_memset32(&STATIC.key11_usage_thr_63_32, 0x0, sizeof(STATIC.key11_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_11
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_12 
	dwc_cinit_memset32(&STATIC.key12_usage_thr_31_0, 0x0, sizeof(STATIC.key12_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_12
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_12 
	dwc_cinit_memset32(&STATIC.key12_usage_thr_63_32, 0x0, sizeof(STATIC.key12_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_12
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_13 
	dwc_cinit_memset32(&STATIC.key13_usage_thr_31_0, 0x0, sizeof(STATIC.key13_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_13
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_13 
	dwc_cinit_memset32(&STATIC.key13_usage_thr_63_32, 0x0, sizeof(STATIC.key13_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_13
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_14 
	dwc_cinit_memset32(&STATIC.key14_usage_thr_31_0, 0x0, sizeof(STATIC.key14_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_14
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_14 
	dwc_cinit_memset32(&STATIC.key14_usage_thr_63_32, 0x0, sizeof(STATIC.key14_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_14
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_15 
	dwc_cinit_memset32(&STATIC.key15_usage_thr_31_0, 0x0, sizeof(STATIC.key15_usage_thr_31_0)); 
#endif //DWC_IME_NUM_REGIONS_GT_15
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_NUM_REGIONS_GT_15 
	dwc_cinit_memset32(&STATIC.key15_usage_thr_63_32, 0x0, sizeof(STATIC.key15_usage_thr_63_32)); 
#endif //DWC_IME_NUM_REGIONS_GT_15
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.key0_usage_auto_clear, 0x0, sizeof(STATIC.key0_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key1_usage_auto_clear, 0x0, sizeof(STATIC.key1_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key2_usage_auto_clear, 0x0, sizeof(STATIC.key2_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key3_usage_auto_clear, 0x0, sizeof(STATIC.key3_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key4_usage_auto_clear, 0x0, sizeof(STATIC.key4_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key5_usage_auto_clear, 0x0, sizeof(STATIC.key5_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key6_usage_auto_clear, 0x0, sizeof(STATIC.key6_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key7_usage_auto_clear, 0x0, sizeof(STATIC.key7_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key8_usage_auto_clear, 0x0, sizeof(STATIC.key8_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key9_usage_auto_clear, 0x0, sizeof(STATIC.key9_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key10_usage_auto_clear, 0x0, sizeof(STATIC.key10_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key11_usage_auto_clear, 0x0, sizeof(STATIC.key11_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key12_usage_auto_clear, 0x0, sizeof(STATIC.key12_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key13_usage_auto_clear, 0x0, sizeof(STATIC.key13_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key14_usage_auto_clear, 0x0, sizeof(STATIC.key14_usage_auto_clear));
	dwc_cinit_memset32(&STATIC.key15_usage_auto_clear, 0x0, sizeof(STATIC.key15_usage_auto_clear)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.key0_usage_en, 0x0, sizeof(STATIC.key0_usage_en));
	dwc_cinit_memset32(&STATIC.key1_usage_en, 0x0, sizeof(STATIC.key1_usage_en));
	dwc_cinit_memset32(&STATIC.key2_usage_en, 0x0, sizeof(STATIC.key2_usage_en));
	dwc_cinit_memset32(&STATIC.key3_usage_en, 0x0, sizeof(STATIC.key3_usage_en));
	dwc_cinit_memset32(&STATIC.key4_usage_en, 0x0, sizeof(STATIC.key4_usage_en));
	dwc_cinit_memset32(&STATIC.key5_usage_en, 0x0, sizeof(STATIC.key5_usage_en));
	dwc_cinit_memset32(&STATIC.key6_usage_en, 0x0, sizeof(STATIC.key6_usage_en));
	dwc_cinit_memset32(&STATIC.key7_usage_en, 0x0, sizeof(STATIC.key7_usage_en));
	dwc_cinit_memset32(&STATIC.key8_usage_en, 0x0, sizeof(STATIC.key8_usage_en));
	dwc_cinit_memset32(&STATIC.key9_usage_en, 0x0, sizeof(STATIC.key9_usage_en));
	dwc_cinit_memset32(&STATIC.key10_usage_en, 0x0, sizeof(STATIC.key10_usage_en));
	dwc_cinit_memset32(&STATIC.key11_usage_en, 0x0, sizeof(STATIC.key11_usage_en));
	dwc_cinit_memset32(&STATIC.key12_usage_en, 0x0, sizeof(STATIC.key12_usage_en));
	dwc_cinit_memset32(&STATIC.key13_usage_en, 0x0, sizeof(STATIC.key13_usage_en));
	dwc_cinit_memset32(&STATIC.key14_usage_en, 0x0, sizeof(STATIC.key14_usage_en));
	dwc_cinit_memset32(&STATIC.key15_usage_en, 0x0, sizeof(STATIC.key15_usage_en)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_RMW_KEY_SWAP_EN 
	dwc_cinit_memset32(&STATIC.key0_rmw_swap_en, 0x0, sizeof(STATIC.key0_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key1_rmw_swap_en, 0x0, sizeof(STATIC.key1_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key2_rmw_swap_en, 0x0, sizeof(STATIC.key2_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key3_rmw_swap_en, 0x0, sizeof(STATIC.key3_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key4_rmw_swap_en, 0x0, sizeof(STATIC.key4_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key5_rmw_swap_en, 0x0, sizeof(STATIC.key5_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key6_rmw_swap_en, 0x0, sizeof(STATIC.key6_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key7_rmw_swap_en, 0x0, sizeof(STATIC.key7_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key8_rmw_swap_en, 0x0, sizeof(STATIC.key8_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key9_rmw_swap_en, 0x0, sizeof(STATIC.key9_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key10_rmw_swap_en, 0x0, sizeof(STATIC.key10_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key11_rmw_swap_en, 0x0, sizeof(STATIC.key11_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key12_rmw_swap_en, 0x0, sizeof(STATIC.key12_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key13_rmw_swap_en, 0x0, sizeof(STATIC.key13_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key14_rmw_swap_en, 0x0, sizeof(STATIC.key14_rmw_swap_en));
	dwc_cinit_memset32(&STATIC.key15_rmw_swap_en, 0x0, sizeof(STATIC.key15_rmw_swap_en)); 
#endif //DWC_IME_RMW_KEY_SWAP_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_SRAM_ECC_EN 
	dwc_cinit_memset32(&STATIC.wrch_tkey_eccc_irq_en, 0x0, sizeof(STATIC.wrch_tkey_eccc_irq_en));
	dwc_cinit_memset32(&STATIC.wrch_tkey_eccu_irq_en, 0x0, sizeof(STATIC.wrch_tkey_eccu_irq_en));
	dwc_cinit_memset32(&STATIC.wrch_ckey_eccc_irq_en, 0x0, sizeof(STATIC.wrch_ckey_eccc_irq_en));
	dwc_cinit_memset32(&STATIC.wrch_ckey_eccu_irq_en, 0x0, sizeof(STATIC.wrch_ckey_eccu_irq_en));
	dwc_cinit_memset32(&STATIC.wrch_tval_eccc_irq_en, 0x0, sizeof(STATIC.wrch_tval_eccc_irq_en));
	dwc_cinit_memset32(&STATIC.wrch_tval_eccu_irq_en, 0x0, sizeof(STATIC.wrch_tval_eccu_irq_en));
	dwc_cinit_memset32(&STATIC.rdch_tkey_eccc_irq_en, 0x0, sizeof(STATIC.rdch_tkey_eccc_irq_en));
	dwc_cinit_memset32(&STATIC.rdch_tkey_eccu_irq_en, 0x0, sizeof(STATIC.rdch_tkey_eccu_irq_en));
	dwc_cinit_memset32(&STATIC.rdch_ckey_eccc_irq_en, 0x0, sizeof(STATIC.rdch_ckey_eccc_irq_en));
	dwc_cinit_memset32(&STATIC.rdch_ckey_eccu_irq_en, 0x0, sizeof(STATIC.rdch_ckey_eccu_irq_en));
	dwc_cinit_memset32(&STATIC.rdch_tval_eccc_irq_en, 0x0, sizeof(STATIC.rdch_tval_eccc_irq_en));
	dwc_cinit_memset32(&STATIC.rdch_tval_eccu_irq_en, 0x0, sizeof(STATIC.rdch_tval_eccu_irq_en)); 
#endif //DWC_IME_SRAM_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TKEY_ECC_EN 
	dwc_cinit_memset32(&STATIC.wrch_tkey_eccc_err_thr, 0x1, sizeof(STATIC.wrch_tkey_eccc_err_thr));
	dwc_cinit_memset32(&STATIC.wrch_tkey_eccu_err_thr, 0x1, sizeof(STATIC.wrch_tkey_eccu_err_thr)); 
#endif //DWC_IME_TKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_CKEY_ECC_EN 
	dwc_cinit_memset32(&STATIC.wrch_ckey_eccc_err_thr, 0x1, sizeof(STATIC.wrch_ckey_eccc_err_thr));
	dwc_cinit_memset32(&STATIC.wrch_ckey_eccu_err_thr, 0x1, sizeof(STATIC.wrch_ckey_eccu_err_thr)); 
#endif //DWC_IME_CKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TVAL_ECC_EN 
	dwc_cinit_memset32(&STATIC.wrch_tval_eccc_err_thr, 0x1, sizeof(STATIC.wrch_tval_eccc_err_thr));
	dwc_cinit_memset32(&STATIC.wrch_tval_eccu_err_thr, 0x1, sizeof(STATIC.wrch_tval_eccu_err_thr)); 
#endif //DWC_IME_TVAL_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TKEY_ECC_EN 
	dwc_cinit_memset32(&STATIC.rdch_tkey_eccc_err_thr, 0x1, sizeof(STATIC.rdch_tkey_eccc_err_thr));
	dwc_cinit_memset32(&STATIC.rdch_tkey_eccu_err_thr, 0x1, sizeof(STATIC.rdch_tkey_eccu_err_thr)); 
#endif //DWC_IME_TKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_CKEY_ECC_EN 
	dwc_cinit_memset32(&STATIC.rdch_ckey_eccc_err_thr, 0x1, sizeof(STATIC.rdch_ckey_eccc_err_thr));
	dwc_cinit_memset32(&STATIC.rdch_ckey_eccu_err_thr, 0x1, sizeof(STATIC.rdch_ckey_eccu_err_thr)); 
#endif //DWC_IME_CKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TVAL_ECC_EN 
	dwc_cinit_memset32(&STATIC.rdch_tval_eccc_err_thr, 0x1, sizeof(STATIC.rdch_tval_eccc_err_thr));
	dwc_cinit_memset32(&STATIC.rdch_tval_eccu_err_thr, 0x1, sizeof(STATIC.rdch_tval_eccu_err_thr)); 
#endif //DWC_IME_TVAL_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.wrch_enc_fifo_warn_en, 0x0, sizeof(STATIC.wrch_enc_fifo_warn_en));
	dwc_cinit_memset32(&STATIC.wrch_data_fifo_warn_en, 0x0, sizeof(STATIC.wrch_data_fifo_warn_en));
	dwc_cinit_memset32(&STATIC.rdch_dec_fifo_warn_en, 0x0, sizeof(STATIC.rdch_dec_fifo_warn_en));
	dwc_cinit_memset32(&STATIC.rdch_data_fifo_warn_en, 0x0, sizeof(STATIC.rdch_data_fifo_warn_en)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.cfg_lock_override, 0x0, sizeof(STATIC.cfg_lock_override)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_LATENCY_OPTION1
#ifdef DWC_IME_AES_KEY256_EN 
	dwc_cinit_memset32(&STATIC.global_key_size, 0x0, sizeof(STATIC.global_key_size)); 
#endif //DWC_IME_AES_KEY256_EN
#endif //DWC_IME_LATENCY_OPTION1
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.wrch_ctx_idx_err_en, 0x0, sizeof(STATIC.wrch_ctx_idx_err_en));
	dwc_cinit_memset32(&STATIC.wrch_reg_par_err_en, 0x0, sizeof(STATIC.wrch_reg_par_err_en));
	dwc_cinit_memset32(&STATIC.wrch_fsm_par_err_en, 0x0, sizeof(STATIC.wrch_fsm_par_err_en));
	dwc_cinit_memset32(&STATIC.wrch_key_err_en, 0x0, sizeof(STATIC.wrch_key_err_en));
	dwc_cinit_memset32(&STATIC.wrch_key_idx_err_en, 0x0, sizeof(STATIC.wrch_key_idx_err_en));
	dwc_cinit_memset32(&STATIC.wrch_uxts_irq_en, 0x0, sizeof(STATIC.wrch_uxts_irq_en)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.wrch_self_test_fail_act, 0x1, sizeof(STATIC.wrch_self_test_fail_act));
	dwc_cinit_memset32(&STATIC.wrch_clr_ssp, 0x0, sizeof(STATIC.wrch_clr_ssp)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_WRCH_UAES_XTS_CFG_HW_INIT_EN 
	dwc_cinit_memset32(&STATIC.wrch_hw_init_go, 0x0, sizeof(STATIC.wrch_hw_init_go)); 
#endif //DWC_IME_WRCH_UAES_XTS_CFG_HW_INIT_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.wrch_pipe_num, 0x0, sizeof(STATIC.wrch_pipe_num));
	dwc_cinit_memset32(&STATIC.wrch_chk_disable, 0x0, sizeof(STATIC.wrch_chk_disable));
	dwc_cinit_memset32(&STATIC.wrch_enc_bypass_1, 0x0, sizeof(STATIC.wrch_enc_bypass_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.wrch_du_start, 0x0, sizeof(STATIC.wrch_du_start));
	dwc_cinit_memset32(&STATIC.wrch_du_end, 0x0, sizeof(STATIC.wrch_du_end));
	dwc_cinit_memset32(&STATIC.wrch_ecb, 0x0, sizeof(STATIC.wrch_ecb)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifdef DWC_IME_WRCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS_EN 
	dwc_cinit_memset32(&STATIC.wrch_val, 0x0, sizeof(STATIC.wrch_val)); 
#endif //DWC_IME_WRCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.wrch_st_done, 0x0, sizeof(STATIC.wrch_st_done));
	dwc_cinit_memset32(&STATIC.wrch_st_fail, 0x0, sizeof(STATIC.wrch_st_fail));
	dwc_cinit_memset32(&STATIC.wrch_fail_cause_1, 0x0, sizeof(STATIC.wrch_fail_cause_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.wrch_funct, 0x0, sizeof(STATIC.wrch_funct));
	dwc_cinit_memset32(&STATIC.wrch_key_size, 0x0, sizeof(STATIC.wrch_key_size)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.rdch_ctx_idx_err_en, 0x0, sizeof(STATIC.rdch_ctx_idx_err_en));
	dwc_cinit_memset32(&STATIC.rdch_reg_par_err_en, 0x0, sizeof(STATIC.rdch_reg_par_err_en));
	dwc_cinit_memset32(&STATIC.rdch_fsm_par_err_en, 0x0, sizeof(STATIC.rdch_fsm_par_err_en));
	dwc_cinit_memset32(&STATIC.rdch_key_err_en, 0x0, sizeof(STATIC.rdch_key_err_en));
	dwc_cinit_memset32(&STATIC.rdch_key_idx_err_en, 0x0, sizeof(STATIC.rdch_key_idx_err_en));
	dwc_cinit_memset32(&STATIC.rdch_uxts_irq_en, 0x0, sizeof(STATIC.rdch_uxts_irq_en)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&STATIC.rdch_self_test_fail_act, 0x1, sizeof(STATIC.rdch_self_test_fail_act));
	dwc_cinit_memset32(&STATIC.rdch_clr_ssp, 0x0, sizeof(STATIC.rdch_clr_ssp)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_RDCH_UAES_XTS_CFG_HW_INIT_EN 
	dwc_cinit_memset32(&STATIC.rdch_hw_init_go, 0x0, sizeof(STATIC.rdch_hw_init_go)); 
#endif //DWC_IME_RDCH_UAES_XTS_CFG_HW_INIT_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.rdch_pipe_num, 0x0, sizeof(STATIC.rdch_pipe_num));
	dwc_cinit_memset32(&STATIC.rdch_chk_disable, 0x0, sizeof(STATIC.rdch_chk_disable));
	dwc_cinit_memset32(&STATIC.rdch_enc_bypass_1, 0x0, sizeof(STATIC.rdch_enc_bypass_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.rdch_du_start, 0x0, sizeof(STATIC.rdch_du_start));
	dwc_cinit_memset32(&STATIC.rdch_du_end, 0x0, sizeof(STATIC.rdch_du_end));
	dwc_cinit_memset32(&STATIC.rdch_ecb, 0x0, sizeof(STATIC.rdch_ecb)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifdef DWC_IME_RDCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS_EN 
	dwc_cinit_memset32(&STATIC.rdch_val, 0x0, sizeof(STATIC.rdch_val)); 
#endif //DWC_IME_RDCH_UAES_XTS_CFG_RANDOM_BLK_SEQ_ACCESS_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.rdch_st_done, 0x0, sizeof(STATIC.rdch_st_done));
	dwc_cinit_memset32(&STATIC.rdch_st_fail, 0x0, sizeof(STATIC.rdch_st_fail));
	dwc_cinit_memset32(&STATIC.rdch_fail_cause_1, 0x0, sizeof(STATIC.rdch_fail_cause_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&STATIC.rdch_funct, 0x0, sizeof(STATIC.rdch_funct));
	dwc_cinit_memset32(&STATIC.rdch_key_size, 0x0, sizeof(STATIC.rdch_key_size)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
}

