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
void dwc_ddrctl_cinit_set_dyn_cfg_initial_values(void)
{
	dwc_cinit_memset32(&DYN.mr_type, 0x0, sizeof(DYN.mr_type));
	dwc_cinit_memset32(&DYN.mpr_en, 0x0, sizeof(DYN.mpr_en));
	dwc_cinit_memset32(&DYN.pda_en, 0x0, sizeof(DYN.pda_en));
	dwc_cinit_memset32(&DYN.sw_init_int, 0x0, sizeof(DYN.sw_init_int));
	dwc_cinit_memset32(&DYN.mr_rank, (MEMC_NUM_RANKS == 4) ? 0xF : ((MEMC_NUM_RANKS == 2) ? 0x3 : 0x1), sizeof(DYN.mr_rank));
	dwc_cinit_memset32(&DYN.mr_addr, 0x0, sizeof(DYN.mr_addr));
	dwc_cinit_memset32(&DYN.mr_cid, 0x0, sizeof(DYN.mr_cid));
	dwc_cinit_memset32(&DYN.mrr_done_clr, 0x0, sizeof(DYN.mrr_done_clr));
	dwc_cinit_memset32(&DYN.dis_mrrw_trfc, 0x0, sizeof(DYN.dis_mrrw_trfc));
	dwc_cinit_memset32(&DYN.ppr_en, 0x0, sizeof(DYN.ppr_en));
	dwc_cinit_memset32(&DYN.ppr_pgmpst_en, 0x0, sizeof(DYN.ppr_pgmpst_en));
	dwc_cinit_memset32(&DYN.pba_mode, 0x0, sizeof(DYN.pba_mode));
	dwc_cinit_memset32(&DYN.mr_wr, 0x0, sizeof(DYN.mr_wr));
	dwc_cinit_memset32(&DYN.mr_data, 0x0, sizeof(DYN.mr_data));
	dwc_cinit_memset32(&DYN.mr_device_sel, 0x0, sizeof(DYN.mr_device_sel));
	DYN.derate_enable = 0x0;
	DYN.derate_mr4_pause_fc = 0x0;
	DYN.dis_trefi_x6x8 = 0x0;
	dwc_cinit_memset32(&DYN.derate_temp_limit_intr_clr_rank0, 0x0, sizeof(DYN.derate_temp_limit_intr_clr_rank0));
	dwc_cinit_memset32(&DYN.derate_temp_limit_intr_clr_rank1, 0x0, sizeof(DYN.derate_temp_limit_intr_clr_rank1));
	dwc_cinit_memset32(&DYN.derate_temp_limit_intr_clr_rank2, 0x0, sizeof(DYN.derate_temp_limit_intr_clr_rank2));
	dwc_cinit_memset32(&DYN.derate_temp_limit_intr_clr_rank3, 0x0, sizeof(DYN.derate_temp_limit_intr_clr_rank3));
	dwc_cinit_memset32(&DYN.selfref_en, 0x0, sizeof(DYN.selfref_en));
	dwc_cinit_memset32(&DYN.powerdown_en, 0x0, sizeof(DYN.powerdown_en));
	dwc_cinit_memset32(&DYN.actv_pd_en, 0x0, sizeof(DYN.actv_pd_en));
	dwc_cinit_memset32(&DYN.en_dfi_dram_clk_disable, 0x0, sizeof(DYN.en_dfi_dram_clk_disable));
	dwc_cinit_memset32(&DYN.mpsm_en, 0x0, sizeof(DYN.mpsm_en));
	dwc_cinit_memset32(&DYN.selfref_sw, 0x0, sizeof(DYN.selfref_sw));
	dwc_cinit_memset32(&DYN.stay_in_selfref, 0x0, sizeof(DYN.stay_in_selfref));
	dwc_cinit_memset32(&DYN.dis_cam_drain_selfref, 0x0, sizeof(DYN.dis_cam_drain_selfref));
	dwc_cinit_memset32(&DYN.lpddr4_sr_allowed, 0x0, sizeof(DYN.lpddr4_sr_allowed));
	dwc_cinit_memset32(&DYN.dsm_en, 0x0, sizeof(DYN.dsm_en));
	dwc_cinit_memset32(&DYN.mpsm_pd_en, 0x0, sizeof(DYN.mpsm_pd_en));
	dwc_cinit_memset32(&DYN.mpsm_deep_pd_en, 0x0, sizeof(DYN.mpsm_deep_pd_en));
	dwc_cinit_memset32(&DYN.hw_lp_en, 0x1, sizeof(DYN.hw_lp_en));
	DYN.refresh_burst = 0x0;
	DYN.refresh_burst_2x = 0x0;
	DYN.mixed_refsb_hi_thr = 0xf;
	DYN.dis_auto_refresh = 0x0;
	DYN.refresh_update_level = 0x0;
	DYN.init_raa_cnt = 0x0;
	DYN.dbg_raa_rank = 0x0;
	DYN.dbg_raa_bg_bank = 0x0;
	DYN.dis_auto_zq = 0x0;
	dwc_cinit_memset32(&DYN.zq_reset, 0x0, sizeof(DYN.zq_reset));
	DYN.max_num_alloc_bsm_clr = 0x0;
	DYN.max_num_unalloc_entries_clr = 0x0;
	DYN.hwffc_en = 0x0;
	dwc_cinit_memset32(&DYN.hwffc_mrwbuf_addr, 0x0, sizeof(DYN.hwffc_mrwbuf_addr));
	dwc_cinit_memset32(&DYN.hwffc_mrwbuf_select, 0x0, sizeof(DYN.hwffc_mrwbuf_select));
	dwc_cinit_memset32(&DYN.hwffc_mrwbuf_rw_type, 0x0, sizeof(DYN.hwffc_mrwbuf_rw_type));
	dwc_cinit_memset32(&DYN.hwffc_mrwbuf_rw_start, 0x0, sizeof(DYN.hwffc_mrwbuf_rw_start));
	dwc_cinit_memset32(&DYN.hwffc_mrwbuf_wdata, 0x0, sizeof(DYN.hwffc_mrwbuf_wdata));
	DYN.dfi_freq_fsp = 0x0;
	dwc_cinit_memset32(&DYN.dfi0_ctrlmsg_data, 0x0, sizeof(DYN.dfi0_ctrlmsg_data));
	dwc_cinit_memset32(&DYN.dfi0_ctrlmsg_cmd, 0x0, sizeof(DYN.dfi0_ctrlmsg_cmd));
	dwc_cinit_memset32(&DYN.dfi0_ctrlmsg_tout_clr, 0x0, sizeof(DYN.dfi0_ctrlmsg_tout_clr));
	dwc_cinit_memset32(&DYN.dfi0_ctrlmsg_req, 0x0, sizeof(DYN.dfi0_ctrlmsg_req));
	dwc_cinit_memset32(&DYN.dfi_sideband_timer_err_intr_en, 0x1, sizeof(DYN.dfi_sideband_timer_err_intr_en));
	dwc_cinit_memset32(&DYN.dfi_sideband_timer_err_intr_clr, 0x0, sizeof(DYN.dfi_sideband_timer_err_intr_clr));
	dwc_cinit_memset32(&DYN.dfi_sideband_timer_err_intr_force, 0x0, sizeof(DYN.dfi_sideband_timer_err_intr_force));
	dwc_cinit_memset32(&DYN.dfi_error_intr_en, 0x1, sizeof(DYN.dfi_error_intr_en));
	dwc_cinit_memset32(&DYN.dfi_error_intr_clr, 0x0, sizeof(DYN.dfi_error_intr_clr));
	dwc_cinit_memset32(&DYN.dfi_error_intr_force, 0x0, sizeof(DYN.dfi_error_intr_force));
	DYN.wr_poison_slverr_en = 0x1;
	DYN.wr_poison_intr_en = 0x1;
	DYN.wr_poison_intr_clr = 0x0;
	DYN.rd_poison_slverr_en = 0x1;
	DYN.rd_poison_intr_en = 0x1;
	DYN.rd_poison_intr_clr = 0x0;
	dwc_cinit_memset32(&DYN.ecc_corrected_err_clr, 0x0, sizeof(DYN.ecc_corrected_err_clr));
	dwc_cinit_memset32(&DYN.ecc_uncorrected_err_clr, 0x0, sizeof(DYN.ecc_uncorrected_err_clr));
	dwc_cinit_memset32(&DYN.ecc_corr_err_cnt_clr, 0x0, sizeof(DYN.ecc_corr_err_cnt_clr));
	dwc_cinit_memset32(&DYN.ecc_uncorr_err_cnt_clr, 0x0, sizeof(DYN.ecc_uncorr_err_cnt_clr));
	dwc_cinit_memset32(&DYN.ecc_ap_err_intr_clr, 0x0, sizeof(DYN.ecc_ap_err_intr_clr));
	dwc_cinit_memset32(&DYN.ecc_corrected_err_intr_en, 0x1, sizeof(DYN.ecc_corrected_err_intr_en));
	dwc_cinit_memset32(&DYN.ecc_uncorrected_err_intr_en, 0x1, sizeof(DYN.ecc_uncorrected_err_intr_en));
	dwc_cinit_memset32(&DYN.ecc_ap_err_intr_en, 0x1, sizeof(DYN.ecc_ap_err_intr_en));
	dwc_cinit_memset32(&DYN.ecc_corrected_err_intr_force, 0x0, sizeof(DYN.ecc_corrected_err_intr_force));
	dwc_cinit_memset32(&DYN.ecc_uncorrected_err_intr_force, 0x0, sizeof(DYN.ecc_uncorrected_err_intr_force));
	dwc_cinit_memset32(&DYN.ecc_ap_err_intr_force, 0x0, sizeof(DYN.ecc_ap_err_intr_force));
	DYN.dis_rmw_ue_propagation = 0x0;
	dwc_cinit_memset32(&DYN.par_wdata_err_intr_en, 0x1, sizeof(DYN.par_wdata_err_intr_en));
	dwc_cinit_memset32(&DYN.par_wdata_err_intr_clr, 0x0, sizeof(DYN.par_wdata_err_intr_clr));
	dwc_cinit_memset32(&DYN.par_wdata_err_intr_force, 0x0, sizeof(DYN.par_wdata_err_intr_force));
	dwc_cinit_memset32(&DYN.par_rdata_err_intr_en, 0x1, sizeof(DYN.par_rdata_err_intr_en));
	dwc_cinit_memset32(&DYN.par_rdata_err_intr_clr, 0x0, sizeof(DYN.par_rdata_err_intr_clr));
	dwc_cinit_memset32(&DYN.par_rdata_err_intr_force, 0x0, sizeof(DYN.par_rdata_err_intr_force));
	dwc_cinit_memset32(&DYN.par_waddr_err_intr_en, 0x1, sizeof(DYN.par_waddr_err_intr_en));
	dwc_cinit_memset32(&DYN.par_waddr_err_intr_clr, 0x0, sizeof(DYN.par_waddr_err_intr_clr));
	dwc_cinit_memset32(&DYN.par_raddr_err_intr_en, 0x1, sizeof(DYN.par_raddr_err_intr_en));
	dwc_cinit_memset32(&DYN.par_raddr_err_intr_clr, 0x0, sizeof(DYN.par_raddr_err_intr_clr));
	dwc_cinit_memset32(&DYN.par_waddr_err_intr_force, 0x0, sizeof(DYN.par_waddr_err_intr_force));
	dwc_cinit_memset32(&DYN.par_raddr_err_intr_force, 0x0, sizeof(DYN.par_raddr_err_intr_force));
	DYN.ocecc_uncorrected_err_intr_en = 0x1;
	DYN.ocecc_uncorrected_err_intr_clr = 0x0;
	DYN.ocecc_uncorrected_err_intr_force = 0x0;
	DYN.ocecc_corrected_err_intr_en = 0x1;
	DYN.ocecc_corrected_err_intr_clr = 0x0;
	DYN.ocecc_corrected_err_intr_force = 0x0;
	DYN.occap_arb_intr_en = 0x1;
	DYN.occap_arb_intr_clr = 0x0;
	DYN.occap_arb_intr_force = 0x0;
	DYN.occap_arb_cmp_poison_seq = 0x0;
	DYN.occap_arb_cmp_poison_parallel = 0x0;
	DYN.occap_arb_cmp_poison_err_inj = 0x0;
	DYN.occap_arb_raq_poison_en = 0x0;
	dwc_cinit_memset32(&DYN.occap_ddrc_data_intr_en, 0x1, sizeof(DYN.occap_ddrc_data_intr_en));
	dwc_cinit_memset32(&DYN.occap_ddrc_data_intr_clr, 0x0, sizeof(DYN.occap_ddrc_data_intr_clr));
	dwc_cinit_memset32(&DYN.occap_ddrc_data_intr_force, 0x0, sizeof(DYN.occap_ddrc_data_intr_force));
	dwc_cinit_memset32(&DYN.occap_ddrc_data_poison_seq, 0x0, sizeof(DYN.occap_ddrc_data_poison_seq));
	dwc_cinit_memset32(&DYN.occap_ddrc_data_poison_parallel, 0x0, sizeof(DYN.occap_ddrc_data_poison_parallel));
	dwc_cinit_memset32(&DYN.occap_ddrc_data_poison_err_inj, 0x0, sizeof(DYN.occap_ddrc_data_poison_err_inj));
	dwc_cinit_memset32(&DYN.occap_ddrc_ctrl_intr_en, 0x1, sizeof(DYN.occap_ddrc_ctrl_intr_en));
	dwc_cinit_memset32(&DYN.occap_ddrc_ctrl_intr_clr, 0x0, sizeof(DYN.occap_ddrc_ctrl_intr_clr));
	dwc_cinit_memset32(&DYN.occap_ddrc_ctrl_intr_force, 0x0, sizeof(DYN.occap_ddrc_ctrl_intr_force));
	dwc_cinit_memset32(&DYN.occap_ddrc_ctrl_poison_seq, 0x0, sizeof(DYN.occap_ddrc_ctrl_poison_seq));
	dwc_cinit_memset32(&DYN.occap_ddrc_ctrl_poison_parallel, 0x0, sizeof(DYN.occap_ddrc_ctrl_poison_parallel));
	dwc_cinit_memset32(&DYN.occap_ddrc_ctrl_poison_err_inj, 0x0, sizeof(DYN.occap_ddrc_ctrl_poison_err_inj));
	dwc_cinit_memset32(&DYN.occap_dfiic_intr_en, 0x1, sizeof(DYN.occap_dfiic_intr_en));
	dwc_cinit_memset32(&DYN.occap_dfiic_intr_clr, 0x0, sizeof(DYN.occap_dfiic_intr_clr));
	dwc_cinit_memset32(&DYN.occap_dfiic_intr_force, 0x0, sizeof(DYN.occap_dfiic_intr_force));
	dwc_cinit_memset32(&DYN.capar_err_intr_en, 0x1, sizeof(DYN.capar_err_intr_en));
	dwc_cinit_memset32(&DYN.capar_err_intr_clr, 0x0, sizeof(DYN.capar_err_intr_clr));
	dwc_cinit_memset32(&DYN.capar_err_intr_force, 0x0, sizeof(DYN.capar_err_intr_force));
	dwc_cinit_memset32(&DYN.capar_err_max_reached_intr_en, 0x1, sizeof(DYN.capar_err_max_reached_intr_en));
	dwc_cinit_memset32(&DYN.capar_err_max_reached_intr_clr, 0x0, sizeof(DYN.capar_err_max_reached_intr_clr));
	dwc_cinit_memset32(&DYN.capar_err_max_reached_intr_force, 0x0, sizeof(DYN.capar_err_max_reached_intr_force));
	dwc_cinit_memset32(&DYN.capar_err_cnt_clr, 0x0, sizeof(DYN.capar_err_cnt_clr));
	dwc_cinit_memset32(&DYN.wr_crc_err_intr_en, 0x1, sizeof(DYN.wr_crc_err_intr_en));
	dwc_cinit_memset32(&DYN.wr_crc_err_intr_clr, 0x0, sizeof(DYN.wr_crc_err_intr_clr));
	dwc_cinit_memset32(&DYN.wr_crc_err_intr_force, 0x0, sizeof(DYN.wr_crc_err_intr_force));
	dwc_cinit_memset32(&DYN.wr_crc_err_max_reached_intr_en, 0x1, sizeof(DYN.wr_crc_err_max_reached_intr_en));
	dwc_cinit_memset32(&DYN.wr_crc_err_max_reached_intr_clr, 0x0, sizeof(DYN.wr_crc_err_max_reached_intr_clr));
	dwc_cinit_memset32(&DYN.wr_crc_err_max_reached_intr_force, 0x0, sizeof(DYN.wr_crc_err_max_reached_intr_force));
	dwc_cinit_memset32(&DYN.wr_crc_err_cnt_clr, 0x0, sizeof(DYN.wr_crc_err_cnt_clr));
	dwc_cinit_memset32(&DYN.rd_crc_err_max_reached_int_en, 0x0, sizeof(DYN.rd_crc_err_max_reached_int_en));
	dwc_cinit_memset32(&DYN.rd_crc_err_max_reached_int_clr, 0x0, sizeof(DYN.rd_crc_err_max_reached_int_clr));
	dwc_cinit_memset32(&DYN.rd_crc_err_cnt_clr, 0x0, sizeof(DYN.rd_crc_err_cnt_clr));
	dwc_cinit_memset32(&DYN.rd_crc_err_max_reached_intr_force, 0x0, sizeof(DYN.rd_crc_err_max_reached_intr_force));
	dwc_cinit_memset32(&DYN.capar_fatl_err_intr_en, 0x1, sizeof(DYN.capar_fatl_err_intr_en));
	dwc_cinit_memset32(&DYN.capar_fatl_err_intr_clr, 0x0, sizeof(DYN.capar_fatl_err_intr_clr));
	dwc_cinit_memset32(&DYN.capar_fatl_err_intr_force, 0x0, sizeof(DYN.capar_fatl_err_intr_force));
	dwc_cinit_memset32(&DYN.capar_poison_inject_en, 0x0, sizeof(DYN.capar_poison_inject_en));
	dwc_cinit_memset32(&DYN.capar_poison_cmdtype, 0x0, sizeof(DYN.capar_poison_cmdtype));
	dwc_cinit_memset32(&DYN.capar_poison_position, 0x0, sizeof(DYN.capar_poison_position));
	dwc_cinit_memset32(&DYN.crc_poison_inject_en, 0x0, sizeof(DYN.crc_poison_inject_en));
	dwc_cinit_memset32(&DYN.crc_poison_type, 0x0, sizeof(DYN.crc_poison_type));
	dwc_cinit_memset32(&DYN.crc_poison_nibble, 0x0, sizeof(DYN.crc_poison_nibble));
	dwc_cinit_memset32(&DYN.crc_poison_times, 0x0, sizeof(DYN.crc_poison_times));
	DYN.reg_par_en = 0x0;
	DYN.reg_par_err_intr_en = 0x1;
	DYN.reg_par_err_intr_clr = 0x0;
	DYN.reg_par_err_intr_force = 0x0;
	DYN.reg_par_poison_en = 0x0;
	dwc_cinit_memset32(&DYN.wr_crc_retry_limit_intr_en, 0x1, sizeof(DYN.wr_crc_retry_limit_intr_en));
	dwc_cinit_memset32(&DYN.wr_crc_retry_limit_intr_clr, 0x0, sizeof(DYN.wr_crc_retry_limit_intr_clr));
	dwc_cinit_memset32(&DYN.wr_crc_retry_limit_intr_force, 0x0, sizeof(DYN.wr_crc_retry_limit_intr_force));
	dwc_cinit_memset32(&DYN.rd_retry_limit_intr_en, 0x1, sizeof(DYN.rd_retry_limit_intr_en));
	dwc_cinit_memset32(&DYN.rd_retry_limit_intr_clr, 0x0, sizeof(DYN.rd_retry_limit_intr_clr));
	dwc_cinit_memset32(&DYN.rd_retry_limit_intr_force, 0x0, sizeof(DYN.rd_retry_limit_intr_force));
	dwc_cinit_memset32(&DYN.capar_retry_limit_intr_en, 0x0, sizeof(DYN.capar_retry_limit_intr_en));
	dwc_cinit_memset32(&DYN.capar_retry_limit_intr_clr, 0x0, sizeof(DYN.capar_retry_limit_intr_clr));
	dwc_cinit_memset32(&DYN.capar_retry_limit_intr_force, 0x0, sizeof(DYN.capar_retry_limit_intr_force));
	dwc_cinit_memset32(&DYN.rd_link_ecc_corr_intr_en, 0x0, sizeof(DYN.rd_link_ecc_corr_intr_en));
	dwc_cinit_memset32(&DYN.rd_link_ecc_corr_intr_clr, 0x0, sizeof(DYN.rd_link_ecc_corr_intr_clr));
	dwc_cinit_memset32(&DYN.rd_link_ecc_corr_cnt_clr, 0x0, sizeof(DYN.rd_link_ecc_corr_cnt_clr));
	dwc_cinit_memset32(&DYN.rd_link_ecc_corr_intr_force, 0x0, sizeof(DYN.rd_link_ecc_corr_intr_force));
	dwc_cinit_memset32(&DYN.rd_link_ecc_uncorr_intr_en, 0x0, sizeof(DYN.rd_link_ecc_uncorr_intr_en));
	dwc_cinit_memset32(&DYN.rd_link_ecc_uncorr_intr_clr, 0x0, sizeof(DYN.rd_link_ecc_uncorr_intr_clr));
	dwc_cinit_memset32(&DYN.rd_link_ecc_uncorr_cnt_clr, 0x0, sizeof(DYN.rd_link_ecc_uncorr_cnt_clr));
	dwc_cinit_memset32(&DYN.rd_link_ecc_uncorr_intr_force, 0x0, sizeof(DYN.rd_link_ecc_uncorr_intr_force));
	dwc_cinit_memset32(&DYN.linkecc_poison_inject_en, 0x0, sizeof(DYN.linkecc_poison_inject_en));
	dwc_cinit_memset32(&DYN.linkecc_poison_type, 0x0, sizeof(DYN.linkecc_poison_type));
	dwc_cinit_memset32(&DYN.linkecc_poison_rw, 0x0, sizeof(DYN.linkecc_poison_rw));
	dwc_cinit_memset32(&DYN.linkecc_poison_dmi_sel, 0x0, sizeof(DYN.linkecc_poison_dmi_sel));
	dwc_cinit_memset32(&DYN.linkecc_poison_byte_sel, 0x0, sizeof(DYN.linkecc_poison_byte_sel));
	dwc_cinit_memset32(&DYN.eapar_err_intr_en, 0x1, sizeof(DYN.eapar_err_intr_en));
	dwc_cinit_memset32(&DYN.eapar_err_intr_clr, 0x0, sizeof(DYN.eapar_err_intr_clr));
	dwc_cinit_memset32(&DYN.eapar_err_intr_force, 0x0, sizeof(DYN.eapar_err_intr_force));
	dwc_cinit_memset32(&DYN.eapar_err_cnt_clr, 0x0, sizeof(DYN.eapar_err_cnt_clr));
	dwc_cinit_memset32(&DYN.dyn_pre_pri_dis, 0x1, sizeof(DYN.dyn_pre_pri_dis));
	dwc_cinit_memset32(&DYN.fixed_pre_pri_sel, 0x1, sizeof(DYN.fixed_pre_pri_sel));
	dwc_cinit_memset32(&DYN.blk_act_en, 0x1, sizeof(DYN.blk_act_en));
	dwc_cinit_memset32(&DYN.act2rda_cnt_mask, 0x1, sizeof(DYN.act2rda_cnt_mask));
	dwc_cinit_memset32(&DYN.dyn_pre_pri_hi_win_size, 0x8, sizeof(DYN.dyn_pre_pri_hi_win_size));
	dwc_cinit_memset32(&DYN.dyn_pre_pri_lo_wait_thr, 0x30, sizeof(DYN.dyn_pre_pri_lo_wait_thr));
	dwc_cinit_memset32(&DYN.lrank_rd2rd_gap, 0x0, sizeof(DYN.lrank_rd2rd_gap));
	dwc_cinit_memset32(&DYN.lrank_wr2wr_gap, 0x0, sizeof(DYN.lrank_wr2wr_gap));
	dwc_cinit_memset32(&DYN.refsb_hi_wait_thr, 0x10, sizeof(DYN.refsb_hi_wait_thr));
	dwc_cinit_memset32(&DYN.t_ppd_cnt_en, 0x0, sizeof(DYN.t_ppd_cnt_en));
	dwc_cinit_memset32(&DYN.base_timer_en, 0x1, sizeof(DYN.base_timer_en));
	dwc_cinit_memset32(&DYN.glb_blk0_en, 0x0, sizeof(DYN.glb_blk0_en));
	dwc_cinit_memset32(&DYN.glb_blk1_en, 0x0, sizeof(DYN.glb_blk1_en));
	dwc_cinit_memset32(&DYN.glb_blk2_en, 0x0, sizeof(DYN.glb_blk2_en));
	dwc_cinit_memset32(&DYN.glb_blk3_en, 0x0, sizeof(DYN.glb_blk3_en));
	dwc_cinit_memset32(&DYN.glb_blk4_en, 0x0, sizeof(DYN.glb_blk4_en));
	dwc_cinit_memset32(&DYN.glb_blk5_en, 0x0, sizeof(DYN.glb_blk5_en));
	dwc_cinit_memset32(&DYN.glb_blk6_en, 0x0, sizeof(DYN.glb_blk6_en));
	dwc_cinit_memset32(&DYN.glb_blk7_en, 0x0, sizeof(DYN.glb_blk7_en));
	dwc_cinit_memset32(&DYN.rank_blk0_en, 0x0, sizeof(DYN.rank_blk0_en));
	dwc_cinit_memset32(&DYN.rank_blk1_en, 0x0, sizeof(DYN.rank_blk1_en));
	dwc_cinit_memset32(&DYN.rank_blk2_en, 0x0, sizeof(DYN.rank_blk2_en));
	dwc_cinit_memset32(&DYN.rank_blk3_en, 0x0, sizeof(DYN.rank_blk3_en));
	dwc_cinit_memset32(&DYN.rank_blk4_en, 0x0, sizeof(DYN.rank_blk4_en));
	dwc_cinit_memset32(&DYN.rank_blk5_en, 0x0, sizeof(DYN.rank_blk5_en));
	dwc_cinit_memset32(&DYN.rank_blk6_en, 0x0, sizeof(DYN.rank_blk6_en));
	dwc_cinit_memset32(&DYN.rank_blk7_en, 0x0, sizeof(DYN.rank_blk7_en));
	dwc_cinit_memset32(&DYN.rank_blk8_en, 0x0, sizeof(DYN.rank_blk8_en));
	dwc_cinit_memset32(&DYN.rank_blk9_en, 0x0, sizeof(DYN.rank_blk9_en));
	dwc_cinit_memset32(&DYN.rank_blk10_en, 0x0, sizeof(DYN.rank_blk10_en));
	dwc_cinit_memset32(&DYN.rank_blk11_en, 0x0, sizeof(DYN.rank_blk11_en));
	dwc_cinit_memset32(&DYN.rank_blk12_en, 0x0, sizeof(DYN.rank_blk12_en));
	dwc_cinit_memset32(&DYN.rank_blk13_en, 0x0, sizeof(DYN.rank_blk13_en));
	dwc_cinit_memset32(&DYN.rank_blk14_en, 0x0, sizeof(DYN.rank_blk14_en));
	dwc_cinit_memset32(&DYN.rank_blk15_en, 0x0, sizeof(DYN.rank_blk15_en));
	dwc_cinit_memset32(&DYN.rank_blk16_en, 0x0, sizeof(DYN.rank_blk16_en));
	dwc_cinit_memset32(&DYN.rank_blk17_en, 0x0, sizeof(DYN.rank_blk17_en));
	dwc_cinit_memset32(&DYN.rank_blk18_en, 0x0, sizeof(DYN.rank_blk18_en));
	dwc_cinit_memset32(&DYN.rank_blk19_en, 0x0, sizeof(DYN.rank_blk19_en));
	dwc_cinit_memset32(&DYN.rank_blk20_en, 0x0, sizeof(DYN.rank_blk20_en));
	dwc_cinit_memset32(&DYN.rank_blk21_en, 0x0, sizeof(DYN.rank_blk21_en));
	dwc_cinit_memset32(&DYN.rank_blk22_en, 0x0, sizeof(DYN.rank_blk22_en));
	dwc_cinit_memset32(&DYN.rank_blk23_en, 0x0, sizeof(DYN.rank_blk23_en));
	dwc_cinit_memset32(&DYN.rank_blk24_en, 0x0, sizeof(DYN.rank_blk24_en));
	dwc_cinit_memset32(&DYN.rank_blk25_en, 0x0, sizeof(DYN.rank_blk25_en));
	dwc_cinit_memset32(&DYN.rank_blk26_en, 0x0, sizeof(DYN.rank_blk26_en));
	dwc_cinit_memset32(&DYN.rank_blk27_en, 0x0, sizeof(DYN.rank_blk27_en));
	dwc_cinit_memset32(&DYN.rank_blk28_en, 0x0, sizeof(DYN.rank_blk28_en));
	dwc_cinit_memset32(&DYN.rank_blk29_en, 0x0, sizeof(DYN.rank_blk29_en));
	dwc_cinit_memset32(&DYN.rank_blk30_en, 0x0, sizeof(DYN.rank_blk30_en));
	dwc_cinit_memset32(&DYN.rank_blk31_en, 0x0, sizeof(DYN.rank_blk31_en));
	dwc_cinit_memset32(&DYN.glb_blk0_trig, 0x0, sizeof(DYN.glb_blk0_trig));
	dwc_cinit_memset32(&DYN.glb_blk1_trig, 0x0, sizeof(DYN.glb_blk1_trig));
	dwc_cinit_memset32(&DYN.glb_blk2_trig, 0x0, sizeof(DYN.glb_blk2_trig));
	dwc_cinit_memset32(&DYN.glb_blk3_trig, 0x0, sizeof(DYN.glb_blk3_trig));
	dwc_cinit_memset32(&DYN.glb_blk4_trig, 0x0, sizeof(DYN.glb_blk4_trig));
	dwc_cinit_memset32(&DYN.glb_blk5_trig, 0x0, sizeof(DYN.glb_blk5_trig));
	dwc_cinit_memset32(&DYN.glb_blk6_trig, 0x0, sizeof(DYN.glb_blk6_trig));
	dwc_cinit_memset32(&DYN.glb_blk7_trig, 0x0, sizeof(DYN.glb_blk7_trig));
	dwc_cinit_memset32(&DYN.rank_blk0_trig, 0x0, sizeof(DYN.rank_blk0_trig));
	dwc_cinit_memset32(&DYN.rank_blk1_trig, 0x0, sizeof(DYN.rank_blk1_trig));
	dwc_cinit_memset32(&DYN.rank_blk2_trig, 0x0, sizeof(DYN.rank_blk2_trig));
	dwc_cinit_memset32(&DYN.rank_blk3_trig, 0x0, sizeof(DYN.rank_blk3_trig));
	dwc_cinit_memset32(&DYN.rank_blk4_trig, 0x0, sizeof(DYN.rank_blk4_trig));
	dwc_cinit_memset32(&DYN.rank_blk5_trig, 0x0, sizeof(DYN.rank_blk5_trig));
	dwc_cinit_memset32(&DYN.rank_blk6_trig, 0x0, sizeof(DYN.rank_blk6_trig));
	dwc_cinit_memset32(&DYN.rank_blk7_trig, 0x0, sizeof(DYN.rank_blk7_trig));
	dwc_cinit_memset32(&DYN.rank_blk8_trig, 0x0, sizeof(DYN.rank_blk8_trig));
	dwc_cinit_memset32(&DYN.rank_blk9_trig, 0x0, sizeof(DYN.rank_blk9_trig));
	dwc_cinit_memset32(&DYN.rank_blk10_trig, 0x0, sizeof(DYN.rank_blk10_trig));
	dwc_cinit_memset32(&DYN.rank_blk11_trig, 0x0, sizeof(DYN.rank_blk11_trig));
	dwc_cinit_memset32(&DYN.rank_blk12_trig, 0x0, sizeof(DYN.rank_blk12_trig));
	dwc_cinit_memset32(&DYN.rank_blk13_trig, 0x0, sizeof(DYN.rank_blk13_trig));
	dwc_cinit_memset32(&DYN.rank_blk14_trig, 0x0, sizeof(DYN.rank_blk14_trig));
	dwc_cinit_memset32(&DYN.rank_blk15_trig, 0x0, sizeof(DYN.rank_blk15_trig));
	dwc_cinit_memset32(&DYN.rank_blk16_trig, 0x0, sizeof(DYN.rank_blk16_trig));
	dwc_cinit_memset32(&DYN.rank_blk17_trig, 0x0, sizeof(DYN.rank_blk17_trig));
	dwc_cinit_memset32(&DYN.rank_blk18_trig, 0x0, sizeof(DYN.rank_blk18_trig));
	dwc_cinit_memset32(&DYN.rank_blk19_trig, 0x0, sizeof(DYN.rank_blk19_trig));
	dwc_cinit_memset32(&DYN.rank_blk20_trig, 0x0, sizeof(DYN.rank_blk20_trig));
	dwc_cinit_memset32(&DYN.rank_blk21_trig, 0x0, sizeof(DYN.rank_blk21_trig));
	dwc_cinit_memset32(&DYN.rank_blk22_trig, 0x0, sizeof(DYN.rank_blk22_trig));
	dwc_cinit_memset32(&DYN.rank_blk23_trig, 0x0, sizeof(DYN.rank_blk23_trig));
	dwc_cinit_memset32(&DYN.rank_blk24_trig, 0x0, sizeof(DYN.rank_blk24_trig));
	dwc_cinit_memset32(&DYN.rank_blk25_trig, 0x0, sizeof(DYN.rank_blk25_trig));
	dwc_cinit_memset32(&DYN.rank_blk26_trig, 0x0, sizeof(DYN.rank_blk26_trig));
	dwc_cinit_memset32(&DYN.rank_blk27_trig, 0x0, sizeof(DYN.rank_blk27_trig));
	dwc_cinit_memset32(&DYN.rank_blk28_trig, 0x0, sizeof(DYN.rank_blk28_trig));
	dwc_cinit_memset32(&DYN.rank_blk29_trig, 0x0, sizeof(DYN.rank_blk29_trig));
	dwc_cinit_memset32(&DYN.rank_blk30_trig, 0x0, sizeof(DYN.rank_blk30_trig));
	dwc_cinit_memset32(&DYN.rank_blk31_trig, 0x0, sizeof(DYN.rank_blk31_trig));
	DYN.dch_sync_mode = 0x0;
	DYN.dch_ch0_mask = 0x0;
	dwc_cinit_memset32(&DYN.bwl_win_len, 0x0, sizeof(DYN.bwl_win_len));
	dwc_cinit_memset32(&DYN.bwl_en_len, 0x0, sizeof(DYN.bwl_en_len));
	dwc_cinit_memset32(&DYN.bwl_ctrl, 0x1, sizeof(DYN.bwl_ctrl));
	dwc_cinit_memset32(&DYN.bwl_en, 0x0, sizeof(DYN.bwl_en));
	dwc_cinit_memset32(&DYN.target_ecs_mrr_device_idx, 0x0, sizeof(DYN.target_ecs_mrr_device_idx));
	dwc_cinit_memset32(&DYN.cmd_type, 0x0, sizeof(DYN.cmd_type));
	dwc_cinit_memset32(&DYN.multi_cyc_cs_en, 0x1, sizeof(DYN.multi_cyc_cs_en));
	dwc_cinit_memset32(&DYN.mrr_grp_sel, 0x0, sizeof(DYN.mrr_grp_sel));
	dwc_cinit_memset32(&DYN.cmd_ctrl, 0x0, sizeof(DYN.cmd_ctrl));
	dwc_cinit_memset32(&DYN.cmd_code, 0x0, sizeof(DYN.cmd_code));
	dwc_cinit_memset32(&DYN.cmd_seq_ongoing, 0x0, sizeof(DYN.cmd_seq_ongoing));
	dwc_cinit_memset32(&DYN.cmd_seq_last, 0x1, sizeof(DYN.cmd_seq_last));
	dwc_cinit_memset32(&DYN.cmd_start, 0x0, sizeof(DYN.cmd_start));
	dwc_cinit_memset32(&DYN.cmd_ext_ctrl, 0x0, sizeof(DYN.cmd_ext_ctrl));
	dwc_cinit_memset32(&DYN.swcmd_err_intr_en, 0x1, sizeof(DYN.swcmd_err_intr_en));
	dwc_cinit_memset32(&DYN.swcmd_err_intr_clr, 0x0, sizeof(DYN.swcmd_err_intr_clr));
	dwc_cinit_memset32(&DYN.swcmd_err_intr_force, 0x0, sizeof(DYN.swcmd_err_intr_force));
	dwc_cinit_memset32(&DYN.ducmd_err_intr_en, 0x1, sizeof(DYN.ducmd_err_intr_en));
	dwc_cinit_memset32(&DYN.ducmd_err_intr_clr, 0x0, sizeof(DYN.ducmd_err_intr_clr));
	dwc_cinit_memset32(&DYN.ducmd_err_intr_force, 0x0, sizeof(DYN.ducmd_err_intr_force));
	dwc_cinit_memset32(&DYN.lccmd_err_intr_en, 0x1, sizeof(DYN.lccmd_err_intr_en));
	dwc_cinit_memset32(&DYN.lccmd_err_intr_clr, 0x0, sizeof(DYN.lccmd_err_intr_clr));
	dwc_cinit_memset32(&DYN.lccmd_err_intr_force, 0x0, sizeof(DYN.lccmd_err_intr_force));
	dwc_cinit_memset32(&DYN.ctrlupd_err_intr_en, 0x1, sizeof(DYN.ctrlupd_err_intr_en));
	dwc_cinit_memset32(&DYN.ctrlupd_err_intr_clr, 0x0, sizeof(DYN.ctrlupd_err_intr_clr));
	dwc_cinit_memset32(&DYN.ctrlupd_err_intr_force, 0x0, sizeof(DYN.ctrlupd_err_intr_force));
	dwc_cinit_memset32(&DYN.rfm_alert_intr_en, 0x1, sizeof(DYN.rfm_alert_intr_en));
	dwc_cinit_memset32(&DYN.rfm_alert_intr_clr, 0x0, sizeof(DYN.rfm_alert_intr_clr));
	dwc_cinit_memset32(&DYN.rfm_alert_intr_force, 0x0, sizeof(DYN.rfm_alert_intr_force));
	dwc_cinit_memset32(&DYN.caparcmd_err_intr_en, 0x1, sizeof(DYN.caparcmd_err_intr_en));
	dwc_cinit_memset32(&DYN.caparcmd_err_intr_clr, 0x0, sizeof(DYN.caparcmd_err_intr_clr));
	dwc_cinit_memset32(&DYN.caparcmd_err_intr_force, 0x0, sizeof(DYN.caparcmd_err_intr_force));
	dwc_cinit_memset32(&DYN.du_cfgbuf_wdata, 0x0, sizeof(DYN.du_cfgbuf_wdata));
	dwc_cinit_memset32(&DYN.du_cfgbuf_addr, 0x0, sizeof(DYN.du_cfgbuf_addr));
	dwc_cinit_memset32(&DYN.du_cfgbuf_select, 0x0, sizeof(DYN.du_cfgbuf_select));
	dwc_cinit_memset32(&DYN.du_cfgbuf_op_mode, 0x0, sizeof(DYN.du_cfgbuf_op_mode));
	dwc_cinit_memset32(&DYN.du_cfgbuf_rw_type, 0x0, sizeof(DYN.du_cfgbuf_rw_type));
	dwc_cinit_memset32(&DYN.du_cfgbuf_rw_start, 0x0, sizeof(DYN.du_cfgbuf_rw_start));
	dwc_cinit_memset32(&DYN.du_cmdbuf_wdata, 0x0, sizeof(DYN.du_cmdbuf_wdata));
	dwc_cinit_memset32(&DYN.du_cmdbuf_addr, 0x0, sizeof(DYN.du_cmdbuf_addr));
	dwc_cinit_memset32(&DYN.du_cmdbuf_select, 0x0, sizeof(DYN.du_cmdbuf_select));
	dwc_cinit_memset32(&DYN.du_cmdbuf_op_mode, 0x0, sizeof(DYN.du_cmdbuf_op_mode));
	dwc_cinit_memset32(&DYN.du_cmdbuf_rw_type, 0x0, sizeof(DYN.du_cmdbuf_rw_type));
	dwc_cinit_memset32(&DYN.du_cmdbuf_rw_start, 0x0, sizeof(DYN.du_cmdbuf_rw_start));
	dwc_cinit_memset32(&DYN.lp_cmdbuf_wdata, 0x0, sizeof(DYN.lp_cmdbuf_wdata));
	dwc_cinit_memset32(&DYN.lp_cmdbuf_addr, 0x0, sizeof(DYN.lp_cmdbuf_addr));
	dwc_cinit_memset32(&DYN.lp_cmdbuf_op_mode, 0x0, sizeof(DYN.lp_cmdbuf_op_mode));
	dwc_cinit_memset32(&DYN.lp_cmdbuf_rw_type, 0x0, sizeof(DYN.lp_cmdbuf_rw_type));
	dwc_cinit_memset32(&DYN.lp_cmdbuf_rw_start, 0x0, sizeof(DYN.lp_cmdbuf_rw_start));
	dwc_cinit_memset32(&DYN.wr_data_cb, 0x0, sizeof(DYN.wr_data_cb));
	dwc_cinit_memset32(&DYN.wr_data_dq_mask, 0x0, sizeof(DYN.wr_data_dq_mask));
	dwc_cinit_memset32(&DYN.wr_data_cb_mask, 0x0, sizeof(DYN.wr_data_cb_mask));
	dwc_cinit_memset32(&DYN.data_ecc_sel, 0x0, sizeof(DYN.data_ecc_sel));
	dwc_cinit_memset32(&DYN.rw_ecc_en, 0x0, sizeof(DYN.rw_ecc_en));
	dwc_cinit_memset32(&DYN.wr_data_sel, 0x0, sizeof(DYN.wr_data_sel));
	dwc_cinit_memset32(&DYN.buf_addr, 0x0, sizeof(DYN.buf_addr));
	dwc_cinit_memset32(&DYN.buf_rw_op_type, 0x0, sizeof(DYN.buf_rw_op_type));
	dwc_cinit_memset32(&DYN.buf_rw_start, 0x0, sizeof(DYN.buf_rw_start));
	dwc_cinit_memset32(&DYN.wr_data_dq0, 0x0, sizeof(DYN.wr_data_dq0));
	dwc_cinit_memset32(&DYN.wr_data_dq1, 0x0, sizeof(DYN.wr_data_dq1));
	dwc_cinit_memset32(&DYN.capar_cmdbuf_wdata, 0x0, sizeof(DYN.capar_cmdbuf_wdata));
	dwc_cinit_memset32(&DYN.capar_cmdbuf_addr, 0x0, sizeof(DYN.capar_cmdbuf_addr));
	dwc_cinit_memset32(&DYN.capar_cmdbuf_op_mode, 0x0, sizeof(DYN.capar_cmdbuf_op_mode));
	dwc_cinit_memset32(&DYN.capar_cmdbuf_rw_type, 0x0, sizeof(DYN.capar_cmdbuf_rw_type));
	dwc_cinit_memset32(&DYN.capar_cmdbuf_rw_start, 0x0, sizeof(DYN.capar_cmdbuf_rw_start));
	dwc_cinit_memset32(&DYN.dis_dq, 0x0, sizeof(DYN.dis_dq));
	dwc_cinit_memset32(&DYN.dis_hif, 0x0, sizeof(DYN.dis_hif));
	dwc_cinit_memset32(&DYN.zq_calib_short, 0x0, sizeof(DYN.zq_calib_short));
	dwc_cinit_memset32(&DYN.ctrlupd, 0x0, sizeof(DYN.ctrlupd));
	dwc_cinit_memset32(&DYN.ctrlupd_burst, 0x0, sizeof(DYN.ctrlupd_burst));
	dwc_cinit_memset32(&DYN.rank0_refresh, 0x0, sizeof(DYN.rank0_refresh));
	dwc_cinit_memset32(&DYN.rank1_refresh, 0x0, sizeof(DYN.rank1_refresh));
	dwc_cinit_memset32(&DYN.rank2_refresh, 0x0, sizeof(DYN.rank2_refresh));
	dwc_cinit_memset32(&DYN.rank3_refresh, 0x0, sizeof(DYN.rank3_refresh));
	dwc_cinit_memset32(&DYN.rank4_refresh, 0x0, sizeof(DYN.rank4_refresh));
	dwc_cinit_memset32(&DYN.rank5_refresh, 0x0, sizeof(DYN.rank5_refresh));
	dwc_cinit_memset32(&DYN.rank6_refresh, 0x0, sizeof(DYN.rank6_refresh));
	dwc_cinit_memset32(&DYN.rank7_refresh, 0x0, sizeof(DYN.rank7_refresh));
	dwc_cinit_memset32(&DYN.rank8_refresh, 0x0, sizeof(DYN.rank8_refresh));
	dwc_cinit_memset32(&DYN.rank9_refresh, 0x0, sizeof(DYN.rank9_refresh));
	dwc_cinit_memset32(&DYN.rank10_refresh, 0x0, sizeof(DYN.rank10_refresh));
	dwc_cinit_memset32(&DYN.rank11_refresh, 0x0, sizeof(DYN.rank11_refresh));
	dwc_cinit_memset32(&DYN.rank12_refresh, 0x0, sizeof(DYN.rank12_refresh));
	dwc_cinit_memset32(&DYN.rank13_refresh, 0x0, sizeof(DYN.rank13_refresh));
	dwc_cinit_memset32(&DYN.rank14_refresh, 0x0, sizeof(DYN.rank14_refresh));
	dwc_cinit_memset32(&DYN.rank15_refresh, 0x0, sizeof(DYN.rank15_refresh));
	dwc_cinit_memset32(&DYN.rank16_refresh, 0x0, sizeof(DYN.rank16_refresh));
	dwc_cinit_memset32(&DYN.rank17_refresh, 0x0, sizeof(DYN.rank17_refresh));
	dwc_cinit_memset32(&DYN.rank18_refresh, 0x0, sizeof(DYN.rank18_refresh));
	dwc_cinit_memset32(&DYN.rank19_refresh, 0x0, sizeof(DYN.rank19_refresh));
	dwc_cinit_memset32(&DYN.rank20_refresh, 0x0, sizeof(DYN.rank20_refresh));
	dwc_cinit_memset32(&DYN.rank21_refresh, 0x0, sizeof(DYN.rank21_refresh));
	dwc_cinit_memset32(&DYN.rank22_refresh, 0x0, sizeof(DYN.rank22_refresh));
	dwc_cinit_memset32(&DYN.rank23_refresh, 0x0, sizeof(DYN.rank23_refresh));
	dwc_cinit_memset32(&DYN.rank24_refresh, 0x0, sizeof(DYN.rank24_refresh));
	dwc_cinit_memset32(&DYN.rank25_refresh, 0x0, sizeof(DYN.rank25_refresh));
	dwc_cinit_memset32(&DYN.rank26_refresh, 0x0, sizeof(DYN.rank26_refresh));
	dwc_cinit_memset32(&DYN.rank27_refresh, 0x0, sizeof(DYN.rank27_refresh));
	dwc_cinit_memset32(&DYN.rank28_refresh, 0x0, sizeof(DYN.rank28_refresh));
	dwc_cinit_memset32(&DYN.rank29_refresh, 0x0, sizeof(DYN.rank29_refresh));
	dwc_cinit_memset32(&DYN.rank30_refresh, 0x0, sizeof(DYN.rank30_refresh));
	dwc_cinit_memset32(&DYN.rank31_refresh, 0x0, sizeof(DYN.rank31_refresh));
	dwc_cinit_memset32(&DYN.rank32_refresh, 0x0, sizeof(DYN.rank32_refresh));
	dwc_cinit_memset32(&DYN.rank33_refresh, 0x0, sizeof(DYN.rank33_refresh));
	dwc_cinit_memset32(&DYN.rank34_refresh, 0x0, sizeof(DYN.rank34_refresh));
	dwc_cinit_memset32(&DYN.rank35_refresh, 0x0, sizeof(DYN.rank35_refresh));
	dwc_cinit_memset32(&DYN.rank36_refresh, 0x0, sizeof(DYN.rank36_refresh));
	dwc_cinit_memset32(&DYN.rank37_refresh, 0x0, sizeof(DYN.rank37_refresh));
	dwc_cinit_memset32(&DYN.rank38_refresh, 0x0, sizeof(DYN.rank38_refresh));
	dwc_cinit_memset32(&DYN.rank39_refresh, 0x0, sizeof(DYN.rank39_refresh));
	dwc_cinit_memset32(&DYN.rank40_refresh, 0x0, sizeof(DYN.rank40_refresh));
	dwc_cinit_memset32(&DYN.rank41_refresh, 0x0, sizeof(DYN.rank41_refresh));
	dwc_cinit_memset32(&DYN.rank42_refresh, 0x0, sizeof(DYN.rank42_refresh));
	dwc_cinit_memset32(&DYN.rank43_refresh, 0x0, sizeof(DYN.rank43_refresh));
	dwc_cinit_memset32(&DYN.rank44_refresh, 0x0, sizeof(DYN.rank44_refresh));
	dwc_cinit_memset32(&DYN.rank45_refresh, 0x0, sizeof(DYN.rank45_refresh));
	dwc_cinit_memset32(&DYN.rank46_refresh, 0x0, sizeof(DYN.rank46_refresh));
	dwc_cinit_memset32(&DYN.rank47_refresh, 0x0, sizeof(DYN.rank47_refresh));
	dwc_cinit_memset32(&DYN.rank48_refresh, 0x0, sizeof(DYN.rank48_refresh));
	dwc_cinit_memset32(&DYN.rank49_refresh, 0x0, sizeof(DYN.rank49_refresh));
	dwc_cinit_memset32(&DYN.rank50_refresh, 0x0, sizeof(DYN.rank50_refresh));
	dwc_cinit_memset32(&DYN.rank51_refresh, 0x0, sizeof(DYN.rank51_refresh));
	dwc_cinit_memset32(&DYN.rank52_refresh, 0x0, sizeof(DYN.rank52_refresh));
	dwc_cinit_memset32(&DYN.rank53_refresh, 0x0, sizeof(DYN.rank53_refresh));
	dwc_cinit_memset32(&DYN.rank54_refresh, 0x0, sizeof(DYN.rank54_refresh));
	dwc_cinit_memset32(&DYN.rank55_refresh, 0x0, sizeof(DYN.rank55_refresh));
	dwc_cinit_memset32(&DYN.rank56_refresh, 0x0, sizeof(DYN.rank56_refresh));
	dwc_cinit_memset32(&DYN.rank57_refresh, 0x0, sizeof(DYN.rank57_refresh));
	dwc_cinit_memset32(&DYN.rank58_refresh, 0x0, sizeof(DYN.rank58_refresh));
	dwc_cinit_memset32(&DYN.rank59_refresh, 0x0, sizeof(DYN.rank59_refresh));
	dwc_cinit_memset32(&DYN.rank60_refresh, 0x0, sizeof(DYN.rank60_refresh));
	dwc_cinit_memset32(&DYN.rank61_refresh, 0x0, sizeof(DYN.rank61_refresh));
	dwc_cinit_memset32(&DYN.rank62_refresh, 0x0, sizeof(DYN.rank62_refresh));
	dwc_cinit_memset32(&DYN.rank63_refresh, 0x0, sizeof(DYN.rank63_refresh));
	DYN.dimm_selfref_clock_stop_mode = 0x0;
	DYN.force_clk_te_en = 0x0;
	DYN.force_clk_arb_en = 0x0;
	dwc_cinit_memset32(&DYN.dbg_bsm_sel_ctrl, 0x0, sizeof(DYN.dbg_bsm_sel_ctrl));
	dwc_cinit_memset32(&DYN.dbg_lrsm_sel_ctrl, 0x0, sizeof(DYN.dbg_lrsm_sel_ctrl));
	dwc_cinit_memset32(&DYN.cmdfifo_rd_addr, 0x1, sizeof(DYN.cmdfifo_rd_addr));
	dwc_cinit_memset32(&DYN.ecc_corr_threshold, 0x0, sizeof(DYN.ecc_corr_threshold));
	dwc_cinit_memset32(&DYN.ecc_corr_err_cnt_clr_rank0, 0x0, sizeof(DYN.ecc_corr_err_cnt_clr_rank0));
	dwc_cinit_memset32(&DYN.ecc_corr_err_cnt_clr_rank1, 0x0, sizeof(DYN.ecc_corr_err_cnt_clr_rank1));
	dwc_cinit_memset32(&DYN.ecc_corr_err_cnt_clr_rank2, 0x0, sizeof(DYN.ecc_corr_err_cnt_clr_rank2));
	dwc_cinit_memset32(&DYN.ecc_corr_err_cnt_clr_rank3, 0x0, sizeof(DYN.ecc_corr_err_cnt_clr_rank3));
	dwc_cinit_memset32(&DYN.ecc_uncorr_err_log_mode, 0x0, sizeof(DYN.ecc_uncorr_err_log_mode));
	dwc_cinit_memset32(&DYN.ecc_corr_err_log_mode, 0x0, sizeof(DYN.ecc_corr_err_log_mode));
	dwc_cinit_memset32(&DYN.ecc_corr_err_per_rank_intr_en, 0x0, sizeof(DYN.ecc_corr_err_per_rank_intr_en));
	DYN.ppt2_burst_num = 0x200;
	DYN.ppt2_ctrlupd_num_dfi0 = 0x8;
	DYN.ppt2_ctrlupd_num_dfi1 = 0x0;
	DYN.ppt2_burst = 0x0;
	DYN.ppt2_wait_ref = 0x1;
	DYN.addrmap_lut_wdata0 = 0x0;
	DYN.addrmap_lut_wdata1 = 0x0;
	DYN.addrmap_lut_addr = 0x0;
	DYN.addrmap_lut_rw_type = 0x0;
	DYN.addrmap_lut_rw_start = 0x0;
	dwc_cinit_memset32(&DYN.port_en, UMCTL2_PORT_EN_RESET_VALUE, sizeof(DYN.port_en));
	DYN.scrub_en = 0x0;
	DYN.scrub_during_lowpower = 0x0;
	DYN.scrub_en_dch1 = 0x0;
	DYN.scrub_burst_length_nm = 0x1;
	DYN.scrub_interval = 0xff;
	DYN.scrub_cmd_type = 0x0;
	DYN.sbr_correction_mode = 0x0;
	DYN.scrub_burst_length_lp = 0x1;
	DYN.scrub_ue = 0x1;
	DYN.scrub_pattern0 = 0x0;
	DYN.scrub_pattern1 = 0x0;
	DYN.sbr_address_start_mask_0 = 0x0;
	DYN.sbr_address_start_mask_1 = 0x0;
	DYN.sbr_address_range_mask_0 = 0x0;
	DYN.sbr_address_range_mask_1 = 0x0;
	DYN.sbr_address_start_mask_dch1_0 = 0x0;
	DYN.sbr_address_start_mask_dch1_1 = 0x0;
	DYN.sbr_address_range_mask_dch1_0 = 0x0;
	DYN.sbr_address_range_mask_dch1_1 = 0x0;
	DYN.perrank_dis_scrub = 0x0;
	DYN.scrub_restore = 0x0;
	DYN.perrank_dis_scrub_dch1 = 0x0;
	DYN.scrub_restore_dch1 = 0x0;
	DYN.scrub_restore_address0 = 0x0;
	DYN.scrub_restore_address1 = 0x0;
	DYN.scrub_restore_address0_dch1 = 0x0;
	DYN.scrub_restore_address1_dch1 = 0x0;
	dwc_cinit_memset32(&DYN.txsactive_en, 0x0, sizeof(DYN.txsactive_en));
	dwc_cinit_memset32(&DYN.dis_prefetch, 0x0, sizeof(DYN.dis_prefetch));
	dwc_cinit_memset32(&DYN.crc_ue_rsp_sel, (DDRCTL_CHB_POIS_EN_VAL == 1) ? 2 : 1, sizeof(DYN.crc_ue_rsp_sel));
	dwc_cinit_memset32(&DYN.dbg_force_pcrd_steal_mode, 0x0, sizeof(DYN.dbg_force_pcrd_steal_mode));
	dwc_cinit_memset32(&DYN.dbg_wdc_en, 0x1, sizeof(DYN.dbg_wdc_en));
	dwc_cinit_memset32(&DYN.tz_int_enable, 0x1, sizeof(DYN.tz_int_enable));
	dwc_cinit_memset32(&DYN.tz_resperr_enable, 0x0, sizeof(DYN.tz_resperr_enable));
	dwc_cinit_memset32(&DYN.tz_int_clear, 0x0, sizeof(DYN.tz_int_clear));
	dwc_cinit_memset32(&DYN.t_pdn, 0x0, sizeof(DYN.t_pdn));
	dwc_cinit_memset32(&DYN.t_xsr_dsm_x1024, 0x0, sizeof(DYN.t_xsr_dsm_x1024));
	dwc_cinit_memset32(&DYN.dfi_t_ctrlupd_interval_type1, 0x12c, sizeof(DYN.dfi_t_ctrlupd_interval_type1));
	dwc_cinit_memset32(&DYN.ppt2_en, 0x0, sizeof(DYN.ppt2_en));
	dwc_cinit_memset32(&DYN.dfi_t_ctrlupd_interval_type1_unit, 0x3, sizeof(DYN.dfi_t_ctrlupd_interval_type1_unit));
	dwc_cinit_memset32(&DYN.t_refi_x1_x32, 0x62, sizeof(DYN.t_refi_x1_x32));
	dwc_cinit_memset32(&DYN.refresh_to_x1_x32, 0x10, sizeof(DYN.refresh_to_x1_x32));
	dwc_cinit_memset32(&DYN.refresh_margin, 0x2, sizeof(DYN.refresh_margin));
	dwc_cinit_memset32(&DYN.refresh_to_x1_sel, 0x0, sizeof(DYN.refresh_to_x1_sel));
	dwc_cinit_memset32(&DYN.t_refi_x1_sel, 0x0, sizeof(DYN.t_refi_x1_sel));
	dwc_cinit_memset32(&DYN.t_rfc_min, 0x8c, sizeof(DYN.t_rfc_min));
	dwc_cinit_memset32(&DYN.t_rfc_min_ab, 0x0, sizeof(DYN.t_rfc_min_ab));
	dwc_cinit_memset32(&DYN.t_rfc_min_dlr, 0x8c, sizeof(DYN.t_rfc_min_dlr));
	dwc_cinit_memset32(&DYN.t_pbr2pbr, 0x8c, sizeof(DYN.t_pbr2pbr));
	dwc_cinit_memset32(&DYN.t_pbr2act, 0x8c, sizeof(DYN.t_pbr2act));
	dwc_cinit_memset32(&DYN.t_rfcsb, 0x0, sizeof(DYN.t_rfcsb));
	dwc_cinit_memset32(&DYN.t_refsbrd, 0x0, sizeof(DYN.t_refsbrd));
	dwc_cinit_memset32(&DYN.refresh_to_ab_x32, 0x10, sizeof(DYN.refresh_to_ab_x32));
	dwc_cinit_memset32(&DYN.refresh_timer0_start_value_x32, 0x0, sizeof(DYN.refresh_timer0_start_value_x32));
	dwc_cinit_memset32(&DYN.refresh_timer1_start_value_x32, 0x0, sizeof(DYN.refresh_timer1_start_value_x32));
	dwc_cinit_memset32(&DYN.refresh_timer2_start_value_x32, 0x0, sizeof(DYN.refresh_timer2_start_value_x32));
	dwc_cinit_memset32(&DYN.refresh_timer3_start_value_x32, 0x0, sizeof(DYN.refresh_timer3_start_value_x32));
	dwc_cinit_memset32(&DYN.t_rfcsb_dlr, 0x0, sizeof(DYN.t_rfcsb_dlr));
	dwc_cinit_memset32(&DYN.t_refsbrd_dlr, 0x0, sizeof(DYN.t_refsbrd_dlr));
	dwc_cinit_memset32(&DYN.t_rfc_min_het, 0x8c, sizeof(DYN.t_rfc_min_het));
	dwc_cinit_memset32(&DYN.refab_hi_sch_gap, 0x0, sizeof(DYN.refab_hi_sch_gap));
	dwc_cinit_memset32(&DYN.refsb_hi_sch_gap, 0x0, sizeof(DYN.refsb_hi_sch_gap));
	dwc_cinit_memset32(&DYN.t_pbr2pbr_mp, 0x8c, sizeof(DYN.t_pbr2pbr_mp));
	dwc_cinit_memset32(&DYN.t_rfc_min_mp, 0x8c, sizeof(DYN.t_rfc_min_mp));
	dwc_cinit_memset32(&DYN.t_rfc_min_ab_mp, 0x0, sizeof(DYN.t_rfc_min_ab_mp));
	dwc_cinit_memset32(&DYN.t_refi_ecs_offset_x1_x32, 0x0, sizeof(DYN.t_refi_ecs_offset_x1_x32));
	dwc_cinit_memset32(&DYN.t_refi_x1_x32_2, 0x62, sizeof(DYN.t_refi_x1_x32_2));
	dwc_cinit_memset32(&DYN.refresh_to_x1_x32_2, 0x10, sizeof(DYN.refresh_to_x1_x32_2));
	dwc_cinit_memset32(&DYN.refresh_margin_2, 0x2, sizeof(DYN.refresh_margin_2));
	dwc_cinit_memset32(&DYN.t_rfc_min_2, 0x8c, sizeof(DYN.t_rfc_min_2));
	dwc_cinit_memset32(&DYN.t_rfc_min_dlr_2, 0x8c, sizeof(DYN.t_rfc_min_dlr_2));
	dwc_cinit_memset32(&DYN.t_rfcsb_2, 0x0, sizeof(DYN.t_rfcsb_2));
	dwc_cinit_memset32(&DYN.t_refsbrd_2, 0x0, sizeof(DYN.t_refsbrd_2));
	dwc_cinit_memset32(&DYN.t_rfcsb_dlr_2, 0x0, sizeof(DYN.t_rfcsb_dlr_2));
	dwc_cinit_memset32(&DYN.t_refsbrd_dlr_2, 0x0, sizeof(DYN.t_refsbrd_dlr_2));
	dwc_cinit_memset32(&DYN.refab_hi_sch_gap_2, 0x0, sizeof(DYN.refab_hi_sch_gap_2));
	dwc_cinit_memset32(&DYN.refsb_hi_sch_gap_2, 0x0, sizeof(DYN.refsb_hi_sch_gap_2));
	dwc_cinit_memset32(&DYN.t_refi_ecs_offset_x1_x32_2, 0x0, sizeof(DYN.t_refi_ecs_offset_x1_x32_2));
	dwc_cinit_memset32(&DYN.dqsosc_enable, 0x0, sizeof(DYN.dqsosc_enable));
	dwc_cinit_memset32(&DYN.dqsosc_interval_unit, 0x0, sizeof(DYN.dqsosc_interval_unit));
	dwc_cinit_memset32(&DYN.dqsosc_interval, 0x7, sizeof(DYN.dqsosc_interval));
	dwc_cinit_memset32(&DYN.t_wr_crc_alert_pw_max, 0x14, sizeof(DYN.t_wr_crc_alert_pw_max));
	dwc_cinit_memset32(&DYN.t_wr_crc_alert_pw_min, 0x6, sizeof(DYN.t_wr_crc_alert_pw_min));
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&DYN.key_done, 0x0, sizeof(DYN.key_done));
	dwc_cinit_memset32(&DYN.key_miss_err, 0x0, sizeof(DYN.key_miss_err));
	dwc_cinit_memset32(&DYN.key_collision_err, 0x0, sizeof(DYN.key_collision_err));
	dwc_cinit_memset32(&DYN.apb_timing_err, 0x0, sizeof(DYN.apb_timing_err));
	dwc_cinit_memset32(&DYN.key_size_err, 0x0, sizeof(DYN.key_size_err));
	dwc_cinit_memset32(&DYN.reg_parity_err, 0x0, sizeof(DYN.reg_parity_err)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&DYN.key0_usage_hit, 0x0, sizeof(DYN.key0_usage_hit));
	dwc_cinit_memset32(&DYN.key1_usage_hit, 0x0, sizeof(DYN.key1_usage_hit));
	dwc_cinit_memset32(&DYN.key2_usage_hit, 0x0, sizeof(DYN.key2_usage_hit));
	dwc_cinit_memset32(&DYN.key3_usage_hit, 0x0, sizeof(DYN.key3_usage_hit));
	dwc_cinit_memset32(&DYN.key4_usage_hit, 0x0, sizeof(DYN.key4_usage_hit));
	dwc_cinit_memset32(&DYN.key5_usage_hit, 0x0, sizeof(DYN.key5_usage_hit));
	dwc_cinit_memset32(&DYN.key6_usage_hit, 0x0, sizeof(DYN.key6_usage_hit));
	dwc_cinit_memset32(&DYN.key7_usage_hit, 0x0, sizeof(DYN.key7_usage_hit));
	dwc_cinit_memset32(&DYN.key8_usage_hit, 0x0, sizeof(DYN.key8_usage_hit));
	dwc_cinit_memset32(&DYN.key9_usage_hit, 0x0, sizeof(DYN.key9_usage_hit));
	dwc_cinit_memset32(&DYN.key10_usage_hit, 0x0, sizeof(DYN.key10_usage_hit));
	dwc_cinit_memset32(&DYN.key11_usage_hit, 0x0, sizeof(DYN.key11_usage_hit));
	dwc_cinit_memset32(&DYN.key12_usage_hit, 0x0, sizeof(DYN.key12_usage_hit));
	dwc_cinit_memset32(&DYN.key13_usage_hit, 0x0, sizeof(DYN.key13_usage_hit));
	dwc_cinit_memset32(&DYN.key14_usage_hit, 0x0, sizeof(DYN.key14_usage_hit));
	dwc_cinit_memset32(&DYN.key15_usage_hit, 0x0, sizeof(DYN.key15_usage_hit));
	dwc_cinit_memset32(&DYN.key0_swapped, 0x0, sizeof(DYN.key0_swapped));
	dwc_cinit_memset32(&DYN.key1_swapped, 0x0, sizeof(DYN.key1_swapped));
	dwc_cinit_memset32(&DYN.key2_swapped, 0x0, sizeof(DYN.key2_swapped));
	dwc_cinit_memset32(&DYN.key3_swapped, 0x0, sizeof(DYN.key3_swapped));
	dwc_cinit_memset32(&DYN.key4_swapped, 0x0, sizeof(DYN.key4_swapped));
	dwc_cinit_memset32(&DYN.key5_swapped, 0x0, sizeof(DYN.key5_swapped));
	dwc_cinit_memset32(&DYN.key6_swapped, 0x0, sizeof(DYN.key6_swapped));
	dwc_cinit_memset32(&DYN.key7_swapped, 0x0, sizeof(DYN.key7_swapped));
	dwc_cinit_memset32(&DYN.key8_swapped, 0x0, sizeof(DYN.key8_swapped));
	dwc_cinit_memset32(&DYN.key9_swapped, 0x0, sizeof(DYN.key9_swapped));
	dwc_cinit_memset32(&DYN.key10_swapped, 0x0, sizeof(DYN.key10_swapped));
	dwc_cinit_memset32(&DYN.key11_swapped, 0x0, sizeof(DYN.key11_swapped));
	dwc_cinit_memset32(&DYN.key12_swapped, 0x0, sizeof(DYN.key12_swapped));
	dwc_cinit_memset32(&DYN.key13_swapped, 0x0, sizeof(DYN.key13_swapped));
	dwc_cinit_memset32(&DYN.key14_swapped, 0x0, sizeof(DYN.key14_swapped));
	dwc_cinit_memset32(&DYN.key15_swapped, 0x0, sizeof(DYN.key15_swapped)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_KEY_SWAP_EN 
	dwc_cinit_memset32(&DYN.key0_swap_force, 0x0, sizeof(DYN.key0_swap_force));
	dwc_cinit_memset32(&DYN.key1_swap_force, 0x0, sizeof(DYN.key1_swap_force));
	dwc_cinit_memset32(&DYN.key2_swap_force, 0x0, sizeof(DYN.key2_swap_force));
	dwc_cinit_memset32(&DYN.key3_swap_force, 0x0, sizeof(DYN.key3_swap_force));
	dwc_cinit_memset32(&DYN.key4_swap_force, 0x0, sizeof(DYN.key4_swap_force));
	dwc_cinit_memset32(&DYN.key5_swap_force, 0x0, sizeof(DYN.key5_swap_force));
	dwc_cinit_memset32(&DYN.key6_swap_force, 0x0, sizeof(DYN.key6_swap_force));
	dwc_cinit_memset32(&DYN.key7_swap_force, 0x0, sizeof(DYN.key7_swap_force));
	dwc_cinit_memset32(&DYN.key8_swap_force, 0x0, sizeof(DYN.key8_swap_force));
	dwc_cinit_memset32(&DYN.key9_swap_force, 0x0, sizeof(DYN.key9_swap_force));
	dwc_cinit_memset32(&DYN.key10_swap_force, 0x0, sizeof(DYN.key10_swap_force));
	dwc_cinit_memset32(&DYN.key11_swap_force, 0x0, sizeof(DYN.key11_swap_force));
	dwc_cinit_memset32(&DYN.key12_swap_force, 0x0, sizeof(DYN.key12_swap_force));
	dwc_cinit_memset32(&DYN.key13_swap_force, 0x0, sizeof(DYN.key13_swap_force));
	dwc_cinit_memset32(&DYN.key14_swap_force, 0x0, sizeof(DYN.key14_swap_force));
	dwc_cinit_memset32(&DYN.key15_swap_force, 0x0, sizeof(DYN.key15_swap_force)); 
#endif //DWC_IME_KEY_SWAP_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_SRAM_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tkey_poison_en, 0x0, sizeof(DYN.wrch_tkey_poison_en));
	dwc_cinit_memset32(&DYN.wrch_ckey_poison_en, 0x0, sizeof(DYN.wrch_ckey_poison_en));
	dwc_cinit_memset32(&DYN.wrch_tval_poison_en, 0x0, sizeof(DYN.wrch_tval_poison_en));
	dwc_cinit_memset32(&DYN.rdch_tkey_poison_en, 0x0, sizeof(DYN.rdch_tkey_poison_en));
	dwc_cinit_memset32(&DYN.rdch_ckey_poison_en, 0x0, sizeof(DYN.rdch_ckey_poison_en));
	dwc_cinit_memset32(&DYN.rdch_tval_poison_en, 0x0, sizeof(DYN.rdch_tval_poison_en));
	dwc_cinit_memset32(&DYN.wrch_tkey_poison_bit, 0x0, sizeof(DYN.wrch_tkey_poison_bit));
	dwc_cinit_memset32(&DYN.wrch_ckey_poison_bit, 0x0, sizeof(DYN.wrch_ckey_poison_bit));
	dwc_cinit_memset32(&DYN.wrch_tval_poison_bit, 0x0, sizeof(DYN.wrch_tval_poison_bit));
	dwc_cinit_memset32(&DYN.rdch_tkey_poison_bit, 0x0, sizeof(DYN.rdch_tkey_poison_bit));
	dwc_cinit_memset32(&DYN.rdch_ckey_poison_bit, 0x0, sizeof(DYN.rdch_ckey_poison_bit));
	dwc_cinit_memset32(&DYN.rdch_tval_poison_bit, 0x0, sizeof(DYN.rdch_tval_poison_bit)); 
#endif //DWC_IME_SRAM_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tkey_flip_bit_pos0, 0x0, sizeof(DYN.wrch_tkey_flip_bit_pos0));
	dwc_cinit_memset32(&DYN.wrch_tkey_flip_bit_pos1, (DWC_IME_WRCH_UAES_XTS_TKEY_ECC_POISON_POS_WIDTH_INFO > 0 ? 1 : 0), sizeof(DYN.wrch_tkey_flip_bit_pos1)); 
#endif //DWC_IME_TKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_CKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_ckey_flip_bit_pos0, 0x0, sizeof(DYN.wrch_ckey_flip_bit_pos0));
	dwc_cinit_memset32(&DYN.wrch_ckey_flip_bit_pos1, (DWC_IME_WRCH_UAES_XTS_CKEY_ECC_POISON_POS_WIDTH_INFO > 0 ? 1 : 0), sizeof(DYN.wrch_ckey_flip_bit_pos1)); 
#endif //DWC_IME_CKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TVAL_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tval_flip_bit_pos0, 0x0, sizeof(DYN.wrch_tval_flip_bit_pos0));
	dwc_cinit_memset32(&DYN.wrch_tval_flip_bit_pos1, 0x1, sizeof(DYN.wrch_tval_flip_bit_pos1)); 
#endif //DWC_IME_TVAL_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.rdch_tkey_flip_bit_pos0, 0x0, sizeof(DYN.rdch_tkey_flip_bit_pos0));
	dwc_cinit_memset32(&DYN.rdch_tkey_flip_bit_pos1, (DWC_IME_RDCH_UAES_XTS_TKEY_ECC_POISON_POS_WIDTH_INFO > 0 ? 1 : 0), sizeof(DYN.rdch_tkey_flip_bit_pos1)); 
#endif //DWC_IME_TKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_CKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.rdch_ckey_flip_bit_pos0, 0x0, sizeof(DYN.rdch_ckey_flip_bit_pos0));
	dwc_cinit_memset32(&DYN.rdch_ckey_flip_bit_pos1, (DWC_IME_RDCH_UAES_XTS_CKEY_ECC_POISON_POS_WIDTH_INFO > 0 ? 1 : 0), sizeof(DYN.rdch_ckey_flip_bit_pos1)); 
#endif //DWC_IME_CKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TVAL_ECC_EN 
	dwc_cinit_memset32(&DYN.rdch_tval_flip_bit_pos0, 0x0, sizeof(DYN.rdch_tval_flip_bit_pos0));
	dwc_cinit_memset32(&DYN.rdch_tval_flip_bit_pos1, 0x1, sizeof(DYN.rdch_tval_flip_bit_pos1)); 
#endif //DWC_IME_TVAL_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tkey_poison_addr, 0x0, sizeof(DYN.wrch_tkey_poison_addr)); 
#endif //DWC_IME_TKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_CKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_ckey_poison_addr, 0x0, sizeof(DYN.wrch_ckey_poison_addr)); 
#endif //DWC_IME_CKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TVAL_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tval_poison_addr, 0x0, sizeof(DYN.wrch_tval_poison_addr)); 
#endif //DWC_IME_TVAL_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.rdch_tkey_poison_addr, 0x0, sizeof(DYN.rdch_tkey_poison_addr)); 
#endif //DWC_IME_TKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_CKEY_ECC_EN 
	dwc_cinit_memset32(&DYN.rdch_ckey_poison_addr, 0x0, sizeof(DYN.rdch_ckey_poison_addr)); 
#endif //DWC_IME_CKEY_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_TVAL_ECC_EN 
	dwc_cinit_memset32(&DYN.rdch_tval_poison_addr, 0x0, sizeof(DYN.rdch_tval_poison_addr)); 
#endif //DWC_IME_TVAL_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_SRAM_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tkey_eccc_irq_stat, 0x0, sizeof(DYN.wrch_tkey_eccc_irq_stat));
	dwc_cinit_memset32(&DYN.wrch_tkey_eccu_irq_stat, 0x0, sizeof(DYN.wrch_tkey_eccu_irq_stat));
	dwc_cinit_memset32(&DYN.wrch_ckey_eccc_irq_stat, 0x0, sizeof(DYN.wrch_ckey_eccc_irq_stat));
	dwc_cinit_memset32(&DYN.wrch_ckey_eccu_irq_stat, 0x0, sizeof(DYN.wrch_ckey_eccu_irq_stat));
	dwc_cinit_memset32(&DYN.wrch_tval_eccc_irq_stat, 0x0, sizeof(DYN.wrch_tval_eccc_irq_stat));
	dwc_cinit_memset32(&DYN.wrch_tval_eccu_irq_stat, 0x0, sizeof(DYN.wrch_tval_eccu_irq_stat));
	dwc_cinit_memset32(&DYN.rdch_tkey_eccc_irq_stat, 0x0, sizeof(DYN.rdch_tkey_eccc_irq_stat));
	dwc_cinit_memset32(&DYN.rdch_tkey_eccu_irq_stat, 0x0, sizeof(DYN.rdch_tkey_eccu_irq_stat));
	dwc_cinit_memset32(&DYN.rdch_ckey_eccc_irq_stat, 0x0, sizeof(DYN.rdch_ckey_eccc_irq_stat));
	dwc_cinit_memset32(&DYN.rdch_ckey_eccu_irq_stat, 0x0, sizeof(DYN.rdch_ckey_eccu_irq_stat));
	dwc_cinit_memset32(&DYN.rdch_tval_eccc_irq_stat, 0x0, sizeof(DYN.rdch_tval_eccc_irq_stat));
	dwc_cinit_memset32(&DYN.rdch_tval_eccu_irq_stat, 0x0, sizeof(DYN.rdch_tval_eccu_irq_stat)); 
#endif //DWC_IME_SRAM_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_SRAM_ECC_EN 
	dwc_cinit_memset32(&DYN.wrch_tkey_eccc_clr, 0x0, sizeof(DYN.wrch_tkey_eccc_clr));
	dwc_cinit_memset32(&DYN.wrch_tkey_eccu_clr, 0x0, sizeof(DYN.wrch_tkey_eccu_clr));
	dwc_cinit_memset32(&DYN.wrch_ckey_eccc_clr, 0x0, sizeof(DYN.wrch_ckey_eccc_clr));
	dwc_cinit_memset32(&DYN.wrch_ckey_eccu_clr, 0x0, sizeof(DYN.wrch_ckey_eccu_clr));
	dwc_cinit_memset32(&DYN.wrch_tval_eccc_clr, 0x0, sizeof(DYN.wrch_tval_eccc_clr));
	dwc_cinit_memset32(&DYN.wrch_tval_eccu_clr, 0x0, sizeof(DYN.wrch_tval_eccu_clr));
	dwc_cinit_memset32(&DYN.rdch_tkey_eccc_clr, 0x0, sizeof(DYN.rdch_tkey_eccc_clr));
	dwc_cinit_memset32(&DYN.rdch_tkey_eccu_clr, 0x0, sizeof(DYN.rdch_tkey_eccu_clr));
	dwc_cinit_memset32(&DYN.rdch_ckey_eccc_clr, 0x0, sizeof(DYN.rdch_ckey_eccc_clr));
	dwc_cinit_memset32(&DYN.rdch_ckey_eccu_clr, 0x0, sizeof(DYN.rdch_ckey_eccu_clr));
	dwc_cinit_memset32(&DYN.rdch_tval_eccc_clr, 0x0, sizeof(DYN.rdch_tval_eccc_clr));
	dwc_cinit_memset32(&DYN.rdch_tval_eccu_clr, 0x0, sizeof(DYN.rdch_tval_eccu_clr)); 
#endif //DWC_IME_SRAM_ECC_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&DYN.wrch_enc_fifo_warn_stat, 0x0, sizeof(DYN.wrch_enc_fifo_warn_stat));
	dwc_cinit_memset32(&DYN.wrch_data_fifo_warn_stat, 0x0, sizeof(DYN.wrch_data_fifo_warn_stat));
	dwc_cinit_memset32(&DYN.rdch_dec_fifo_warn_stat, 0x0, sizeof(DYN.rdch_dec_fifo_warn_stat));
	dwc_cinit_memset32(&DYN.rdch_data_fifo_warn_stat, 0x0, sizeof(DYN.rdch_data_fifo_warn_stat)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&DYN.wrch_ctx_idx_err, 0x0, sizeof(DYN.wrch_ctx_idx_err));
	dwc_cinit_memset32(&DYN.wrch_reg_par_err, 0x0, sizeof(DYN.wrch_reg_par_err));
	dwc_cinit_memset32(&DYN.wrch_fsm_par_err, 0x0, sizeof(DYN.wrch_fsm_par_err));
	dwc_cinit_memset32(&DYN.wrch_key_err, 0x0, sizeof(DYN.wrch_key_err));
	dwc_cinit_memset32(&DYN.wrch_key_idx_err, 0x0, sizeof(DYN.wrch_key_idx_err)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_pt, 0x0, sizeof(DYN.wrch_pt)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_pt_1, 0x0, sizeof(DYN.wrch_pt_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_pt_2, 0x0, sizeof(DYN.wrch_pt_2)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_pt_3, 0x0, sizeof(DYN.wrch_pt_3)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_ct, 0x0, sizeof(DYN.wrch_ct)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_ct_1, 0x0, sizeof(DYN.wrch_ct_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_ct_2, 0x0, sizeof(DYN.wrch_ct_2)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_ct_3, 0x0, sizeof(DYN.wrch_ct_3)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.wrch_dseq, 0x0, sizeof(DYN.wrch_dseq)); 
#endif //DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.wrch_dseq_1, 0x0, sizeof(DYN.wrch_dseq_1)); 
#endif //DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.wrch_dseq_2, 0x0, sizeof(DYN.wrch_dseq_2)); 
#endif //DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.wrch_dseq_3, 0x0, sizeof(DYN.wrch_dseq_3)); 
#endif //DWC_IME_WRCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_byp_err_inj, 0x0, sizeof(DYN.wrch_byp_err_inj));
	dwc_cinit_memset32(&DYN.wrch_ecb_err_inj, 0x0, sizeof(DYN.wrch_ecb_err_inj));
	dwc_cinit_memset32(&DYN.wrch_xts_err_inj, 0x0, sizeof(DYN.wrch_xts_err_inj));
	dwc_cinit_memset32(&DYN.wrch_cts_err_inj, 0x0, sizeof(DYN.wrch_cts_err_inj)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.wrch_bist_go, 0x0, sizeof(DYN.wrch_bist_go)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE 
	dwc_cinit_memset32(&DYN.rdch_ctx_idx_err, 0x0, sizeof(DYN.rdch_ctx_idx_err));
	dwc_cinit_memset32(&DYN.rdch_reg_par_err, 0x0, sizeof(DYN.rdch_reg_par_err));
	dwc_cinit_memset32(&DYN.rdch_fsm_par_err, 0x0, sizeof(DYN.rdch_fsm_par_err));
	dwc_cinit_memset32(&DYN.rdch_key_err, 0x0, sizeof(DYN.rdch_key_err));
	dwc_cinit_memset32(&DYN.rdch_key_idx_err, 0x0, sizeof(DYN.rdch_key_idx_err)); 
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_pt, 0x0, sizeof(DYN.rdch_pt)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_pt_1, 0x0, sizeof(DYN.rdch_pt_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_pt_2, 0x0, sizeof(DYN.rdch_pt_2)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_pt_3, 0x0, sizeof(DYN.rdch_pt_3)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_ct, 0x0, sizeof(DYN.rdch_ct)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_ct_1, 0x0, sizeof(DYN.rdch_ct_1)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_ct_2, 0x0, sizeof(DYN.rdch_ct_2)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_ct_3, 0x0, sizeof(DYN.rdch_ct_3)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.rdch_dseq, 0x0, sizeof(DYN.rdch_dseq)); 
#endif //DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.rdch_dseq_1, 0x0, sizeof(DYN.rdch_dseq_1)); 
#endif //DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.rdch_dseq_2, 0x0, sizeof(DYN.rdch_dseq_2)); 
#endif //DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN
#ifndef DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN 
	dwc_cinit_memset32(&DYN.rdch_dseq_3, 0x0, sizeof(DYN.rdch_dseq_3)); 
#endif //DWC_IME_RDCH_UAES_XTS_CFG_ECB_EN
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_byp_err_inj, 0x0, sizeof(DYN.rdch_byp_err_inj));
	dwc_cinit_memset32(&DYN.rdch_ecb_err_inj, 0x0, sizeof(DYN.rdch_ecb_err_inj));
	dwc_cinit_memset32(&DYN.rdch_xts_err_inj, 0x0, sizeof(DYN.rdch_xts_err_inj));
	dwc_cinit_memset32(&DYN.rdch_cts_err_inj, 0x0, sizeof(DYN.rdch_cts_err_inj)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
#ifdef DDRCTL_SECURE
#ifdef DWC_IME_FIPS_TEST_MODE_EN 
	dwc_cinit_memset32(&DYN.rdch_bist_go, 0x0, sizeof(DYN.rdch_bist_go)); 
#endif //DWC_IME_FIPS_TEST_MODE_EN
#endif //DDRCTL_SECURE
}

