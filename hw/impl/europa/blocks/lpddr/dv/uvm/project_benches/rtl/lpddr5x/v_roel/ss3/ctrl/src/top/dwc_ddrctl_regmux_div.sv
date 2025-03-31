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
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

// Revision $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_regmux_div.sv#16 $
// Description:
//                  Register muxplexer and division block
//                  This block chooses the register field based on the target frequency and divides registers by the DDRC/DFI frequency ratio
`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"


module dwc_ddrctl_regmux_div
import DWC_ddrctl_reg_pkg::*;
 (

   input logic        core_ddrc_core_clk                // ddrc core clock
  ,input logic        core_ddrc_rstn                    // ddrc reset, low active

  /////////////////////
  // Control signals //
  /////////////////////

  ,input logic   [TARGET_FREQUENCY_WIDTH-1:0]   reg_ddrc_target_frequency

  ,input logic           hwffc_target_freq_en
  ,input logic   [TARGET_FREQUENCY_WIDTH-1:0]   hwffc_target_freq
  ,input logic   [TARGET_FREQUENCY_WIDTH-1:0]   hwffc_target_freq_init
  ,input logic                                                  reg_ddrc_lpddr5



  //////////////////////
  // Normal registers //
  //////////////////////

  ,input logic [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0] reg_ddrc_blk_channel_idle_time_x32


  /////////////////////
  // Freq0 registers //
  /////////////////////

  ,input logic [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq0

  ,input logic [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0
  ,input logic [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0
  ,input logic [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]  reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0
  ,input logic                                              reg_ddrc_ppt2_en_freq0
  ,input logic                                              reg_ddrc_ppt2_override_freq0
  ,input logic                                              reg_ddrc_ctrlupd_after_dqsosc_freq0

  ,input logic           reg_ddrc_frequency_ratio_freq0

  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq0
  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq0

  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_freq0
  ,input logic  [DERATED_T_RAS_MIN_WIDTH-1:0]  reg_ddrc_derated_t_ras_min_freq0
  ,input logic  [DERATED_T_RP_WIDTH-1:0]       reg_ddrc_derated_t_rp_freq0
  ,input logic  [DERATED_T_RRD_WIDTH-1:0]      reg_ddrc_derated_t_rrd_freq0
  ,input logic  [DERATED_T_RC_WIDTH-1:0]       reg_ddrc_derated_t_rc_freq0
  ,input logic   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq0
  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_write_freq0
  ,input logic   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq0
  ,input logic   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq0
  ,input logic   [REFRESH_MARGIN_WIDTH-1:0]   reg_ddrc_refresh_margin_freq0
  ,input logic   [REFRESH_TO_X1_X32_WIDTH-1:0]   reg_ddrc_refresh_to_x1_x32_freq0
  ,input logic   [REFRESH_TO_AB_X32_WIDTH-1:0]   reg_ddrc_refresh_to_ab_x32_freq0
  ,input logic           reg_ddrc_refresh_to_x1_sel_freq0
  ,input logic           reg_ddrc_t_refi_x1_sel_freq0
  ,input logic   [T_REFI_X1_X32_WIDTH-1:0]  reg_ddrc_t_refi_x1_x32_freq0
  ,input logic   [T_RFC_MIN_WIDTH-1:0]   reg_ddrc_t_rfc_min_freq0
  ,input logic   [T_RFC_MIN_AB_WIDTH-1:0] reg_ddrc_t_rfc_min_ab_freq0
  ,input logic   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq0
  ,input logic   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq0

  ,input logic [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq0

  ,input logic  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq0
  ,input logic                             reg_ddrc_t_pgm_x1_sel_freq0
  ,input logic  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq0
  ,input logic  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq0

  ,input logic   [15:0]  reg_ddrc_mr_freq0
  ,input logic   [15:0]  reg_ddrc_emr_freq0
  ,input logic   [15:0]  reg_ddrc_emr2_freq0
  ,input logic   [15:0]  reg_ddrc_emr3_freq0
  ,input logic   [15:0]  reg_ddrc_mr4_freq0
  ,input logic   [15:0]  reg_ddrc_mr5_freq0
  ,input logic   [15:0]  reg_ddrc_mr6_freq0
  ,input logic   [15:0]  reg_ddrc_mr22_freq0
  ,input logic   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq0
  ,input logic   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq0
  ,input logic   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq0
  ,input logic   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq0
  ,input logic   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0
  ,input logic   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq0
  ,input logic   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq0
  ,input logic   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq0
  ,input logic   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq0
  ,input logic   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq0
  ,input logic   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq0
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq0
  ,input logic   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq0
  ,input logic   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq0
  ,input logic   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq0
  ,input logic   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq0
  ,input logic   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq0
  ,input logic   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq0
  ,input logic   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq0
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq0
  ,input logic   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq0
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq0
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq0
  ,input logic   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq0
  ,input logic   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq0
  ,input logic   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq0
  ,input logic   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq0
  ,input logic   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq0
  ,input logic   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq0
  ,input logic   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq0
  ,input logic   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq0
  ,input logic   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq0
  ,input logic   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq0
  ,input logic   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq0
  ,input logic   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq0
  ,input logic   [T_PDN_WIDTH-1:0]   reg_ddrc_t_pdn_freq0
  ,input logic   [T_XSR_DSM_X1024_WIDTH-1:0]   reg_ddrc_t_xsr_dsm_x1024_freq0
  ,input logic   [T_CSH_WIDTH-1:0]   reg_ddrc_t_csh_freq0
  ,input logic   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq0
  ,input logic   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq0
  ,input logic   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq0
  ,input logic   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq0
  ,input logic   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq0
  ,input logic                                 reg_ddrc_dqsosc_enable_freq0
  ,input logic                                 reg_ddrc_dqsosc_interval_unit_freq0
  ,input logic   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq0
  ,input logic   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq0
  ,input logic   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq0
  ,input logic   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq0
  ,input logic                           reg_ddrc_dvfsq_enable_freq0
  ,input logic   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq0
  ,input logic   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq0
  ,input logic [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq0
  ,input logic [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq0
  ,input   [BANK_ORG_WIDTH-1:0]         reg_ddrc_bank_org_freq0
  ,input   [RD2WR_WIDTH-1:0]            reg_ddrc_rd2wr_s_freq0
  ,input   [MRR2RD_WIDTH-1:0]           reg_ddrc_mrr2rd_freq0
  ,input   [MRR2WR_WIDTH-1:0]           reg_ddrc_mrr2wr_freq0
  ,input   [MRR2MRW_WIDTH-1:0]          reg_ddrc_mrr2mrw_freq0
  ,input   [WS_OFF2WS_FS_WIDTH-1:0]     reg_ddrc_ws_off2ws_fs_freq0
  ,input   [T_WCKSUS_WIDTH-1:0]         reg_ddrc_t_wcksus_freq0
  ,input   [WS_FS2WCK_SUS_WIDTH-1:0]    reg_ddrc_ws_fs2wck_sus_freq0
  ,input   [MAX_RD_SYNC_WIDTH-1:0]      reg_ddrc_max_rd_sync_freq0
  ,input   [MAX_WR_SYNC_WIDTH-1:0]      reg_ddrc_max_wr_sync_freq0
  ,input   [DFI_TWCK_DELAY_WIDTH-1:0]   reg_ddrc_dfi_twck_delay_freq0
  ,input   [DFI_TWCK_EN_RD_WIDTH-1:0]       reg_ddrc_dfi_twck_en_rd_freq0
  ,input   [DFI_TWCK_EN_WR_WIDTH-1:0]       reg_ddrc_dfi_twck_en_wr_freq0
  ,input   [DFI_TWCK_EN_FS_WIDTH-1:0]       reg_ddrc_dfi_twck_en_fs_freq0
  ,input   [DFI_TWCK_DIS_WIDTH-1:0]         reg_ddrc_dfi_twck_dis_freq0
  ,input   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] reg_ddrc_dfi_twck_fast_toggle_freq0
  ,input   [DFI_TWCK_TOGGLE_WIDTH-1:0]      reg_ddrc_dfi_twck_toggle_freq0
  ,input   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   reg_ddrc_dfi_twck_toggle_cs_freq0
  ,input   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_freq0
  ,input                                    reg_ddrc_dfi_twck_toggle_post_rd_en_freq0
  ,input   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq0

  ,input logic   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq0
  ,input logic   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq0
  ,input logic   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq0
  ,input logic   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq0
  ,input logic   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq0
  ,input logic   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq0
  ,input logic   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq0
  ,input logic   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq0
  ,input logic   [DFI_TPHY_WRCSLAT_WIDTH-1:0]     reg_ddrc_dfi_tphy_wrcslat_freq0


  ,input logic [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq0
  ,input logic [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq0
  ,input logic [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq0
  ,input logic [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq0
  ,input logic [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq0
  ,input logic [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq0

  ,input logic [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq0
  ,input logic [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq0


  ,input logic                              reg_ddrc_rd_link_ecc_enable_freq0
  ,input logic                              reg_ddrc_wr_link_ecc_enable_freq0


  /////////////////////
  // Freq1 registers //
  /////////////////////

  ,input logic [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq1

  ,input logic [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1
  ,input logic [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1
  ,input logic [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]  reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1
  ,input logic                                              reg_ddrc_ppt2_en_freq1
  ,input logic                                              reg_ddrc_ppt2_override_freq1
  ,input logic                                              reg_ddrc_ctrlupd_after_dqsosc_freq1

  ,input logic           reg_ddrc_frequency_ratio_freq1

  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq1
  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq1

  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_freq1
  ,input logic  [DERATED_T_RAS_MIN_WIDTH-1:0]  reg_ddrc_derated_t_ras_min_freq1
  ,input logic  [DERATED_T_RP_WIDTH-1:0]       reg_ddrc_derated_t_rp_freq1
  ,input logic  [DERATED_T_RRD_WIDTH-1:0]      reg_ddrc_derated_t_rrd_freq1
  ,input logic  [DERATED_T_RC_WIDTH-1:0]       reg_ddrc_derated_t_rc_freq1
  ,input logic   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq1
  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_write_freq1
  ,input logic   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq1
  ,input logic   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq1
  ,input logic   [REFRESH_MARGIN_WIDTH-1:0]   reg_ddrc_refresh_margin_freq1
  ,input logic   [REFRESH_TO_X1_X32_WIDTH-1:0]   reg_ddrc_refresh_to_x1_x32_freq1
  ,input logic   [REFRESH_TO_AB_X32_WIDTH-1:0]   reg_ddrc_refresh_to_ab_x32_freq1
  ,input logic           reg_ddrc_refresh_to_x1_sel_freq1
  ,input logic           reg_ddrc_t_refi_x1_sel_freq1
  ,input logic   [T_REFI_X1_X32_WIDTH-1:0]  reg_ddrc_t_refi_x1_x32_freq1
  ,input logic   [T_RFC_MIN_WIDTH-1:0]   reg_ddrc_t_rfc_min_freq1
  ,input logic   [T_RFC_MIN_AB_WIDTH-1:0] reg_ddrc_t_rfc_min_ab_freq1
  ,input logic   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq1
  ,input logic   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq1

  ,input logic [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq1

  ,input logic  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq1
  ,input logic                             reg_ddrc_t_pgm_x1_sel_freq1
  ,input logic  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq1
  ,input logic  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq1

  ,input logic   [15:0]  reg_ddrc_mr_freq1
  ,input logic   [15:0]  reg_ddrc_emr_freq1
  ,input logic   [15:0]  reg_ddrc_emr2_freq1
  ,input logic   [15:0]  reg_ddrc_emr3_freq1
  ,input logic   [15:0]  reg_ddrc_mr4_freq1
  ,input logic   [15:0]  reg_ddrc_mr5_freq1
  ,input logic   [15:0]  reg_ddrc_mr6_freq1
  ,input logic   [15:0]  reg_ddrc_mr22_freq1
  ,input logic   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq1
  ,input logic   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq1
  ,input logic   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq1
  ,input logic   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq1
  ,input logic   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1
  ,input logic   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq1
  ,input logic   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq1
  ,input logic   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq1
  ,input logic   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq1
  ,input logic   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq1
  ,input logic   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq1
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq1
  ,input logic   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq1
  ,input logic   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq1
  ,input logic   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq1
  ,input logic   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq1
  ,input logic   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq1
  ,input logic   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq1
  ,input logic   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq1
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq1
  ,input logic   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq1
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq1
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq1
  ,input logic   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq1
  ,input logic   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq1
  ,input logic   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq1
  ,input logic   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq1
  ,input logic   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq1
  ,input logic   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq1
  ,input logic   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq1
  ,input logic   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq1
  ,input logic   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq1
  ,input logic   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq1
  ,input logic   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq1
  ,input logic   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq1
  ,input logic   [T_PDN_WIDTH-1:0]   reg_ddrc_t_pdn_freq1
  ,input logic   [T_XSR_DSM_X1024_WIDTH-1:0]   reg_ddrc_t_xsr_dsm_x1024_freq1
  ,input logic   [T_CSH_WIDTH-1:0]   reg_ddrc_t_csh_freq1
  ,input logic   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq1
  ,input logic   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq1
  ,input logic   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq1
  ,input logic   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq1
  ,input logic   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq1
  ,input logic                                 reg_ddrc_dqsosc_enable_freq1
  ,input logic                                 reg_ddrc_dqsosc_interval_unit_freq1
  ,input logic   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq1
  ,input logic   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq1
  ,input logic   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq1
  ,input logic   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq1
  ,input logic                           reg_ddrc_dvfsq_enable_freq1
  ,input logic   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq1
  ,input logic   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq1
  ,input logic [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq1
  ,input logic [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq1
  ,input   [BANK_ORG_WIDTH-1:0]         reg_ddrc_bank_org_freq1
  ,input   [RD2WR_WIDTH-1:0]            reg_ddrc_rd2wr_s_freq1
  ,input   [MRR2RD_WIDTH-1:0]           reg_ddrc_mrr2rd_freq1
  ,input   [MRR2WR_WIDTH-1:0]           reg_ddrc_mrr2wr_freq1
  ,input   [MRR2MRW_WIDTH-1:0]          reg_ddrc_mrr2mrw_freq1
  ,input   [WS_OFF2WS_FS_WIDTH-1:0]     reg_ddrc_ws_off2ws_fs_freq1
  ,input   [T_WCKSUS_WIDTH-1:0]         reg_ddrc_t_wcksus_freq1
  ,input   [WS_FS2WCK_SUS_WIDTH-1:0]    reg_ddrc_ws_fs2wck_sus_freq1
  ,input   [MAX_RD_SYNC_WIDTH-1:0]      reg_ddrc_max_rd_sync_freq1
  ,input   [MAX_WR_SYNC_WIDTH-1:0]      reg_ddrc_max_wr_sync_freq1
  ,input   [DFI_TWCK_DELAY_WIDTH-1:0]   reg_ddrc_dfi_twck_delay_freq1
  ,input   [DFI_TWCK_EN_RD_WIDTH-1:0]       reg_ddrc_dfi_twck_en_rd_freq1
  ,input   [DFI_TWCK_EN_WR_WIDTH-1:0]       reg_ddrc_dfi_twck_en_wr_freq1
  ,input   [DFI_TWCK_EN_FS_WIDTH-1:0]       reg_ddrc_dfi_twck_en_fs_freq1
  ,input   [DFI_TWCK_DIS_WIDTH-1:0]         reg_ddrc_dfi_twck_dis_freq1
  ,input   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] reg_ddrc_dfi_twck_fast_toggle_freq1
  ,input   [DFI_TWCK_TOGGLE_WIDTH-1:0]      reg_ddrc_dfi_twck_toggle_freq1
  ,input   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   reg_ddrc_dfi_twck_toggle_cs_freq1
  ,input   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_freq1
  ,input                                    reg_ddrc_dfi_twck_toggle_post_rd_en_freq1
  ,input   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq1

  ,input logic   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq1
  ,input logic   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq1
  ,input logic   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq1
  ,input logic   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq1
  ,input logic   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq1
  ,input logic   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq1
  ,input logic   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq1
  ,input logic   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq1
  ,input logic   [DFI_TPHY_WRCSLAT_WIDTH-1:0]     reg_ddrc_dfi_tphy_wrcslat_freq1


  ,input logic [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq1
  ,input logic [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq1
  ,input logic [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq1
  ,input logic [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq1
  ,input logic [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq1
  ,input logic [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq1

  ,input logic [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq1
  ,input logic [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq1


  ,input logic                              reg_ddrc_rd_link_ecc_enable_freq1
  ,input logic                              reg_ddrc_wr_link_ecc_enable_freq1


  /////////////////////
  // Freq2 registers //
  /////////////////////

  ,input logic [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq2

  ,input logic [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2
  ,input logic [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2
  ,input logic [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]  reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2
  ,input logic                                              reg_ddrc_ppt2_en_freq2
  ,input logic                                              reg_ddrc_ppt2_override_freq2
  ,input logic                                              reg_ddrc_ctrlupd_after_dqsosc_freq2

  ,input logic           reg_ddrc_frequency_ratio_freq2

  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq2
  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq2

  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_freq2
  ,input logic  [DERATED_T_RAS_MIN_WIDTH-1:0]  reg_ddrc_derated_t_ras_min_freq2
  ,input logic  [DERATED_T_RP_WIDTH-1:0]       reg_ddrc_derated_t_rp_freq2
  ,input logic  [DERATED_T_RRD_WIDTH-1:0]      reg_ddrc_derated_t_rrd_freq2
  ,input logic  [DERATED_T_RC_WIDTH-1:0]       reg_ddrc_derated_t_rc_freq2
  ,input logic   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq2
  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_write_freq2
  ,input logic   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq2
  ,input logic   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq2
  ,input logic   [REFRESH_MARGIN_WIDTH-1:0]   reg_ddrc_refresh_margin_freq2
  ,input logic   [REFRESH_TO_X1_X32_WIDTH-1:0]   reg_ddrc_refresh_to_x1_x32_freq2
  ,input logic   [REFRESH_TO_AB_X32_WIDTH-1:0]   reg_ddrc_refresh_to_ab_x32_freq2
  ,input logic           reg_ddrc_refresh_to_x1_sel_freq2
  ,input logic           reg_ddrc_t_refi_x1_sel_freq2
  ,input logic   [T_REFI_X1_X32_WIDTH-1:0]  reg_ddrc_t_refi_x1_x32_freq2
  ,input logic   [T_RFC_MIN_WIDTH-1:0]   reg_ddrc_t_rfc_min_freq2
  ,input logic   [T_RFC_MIN_AB_WIDTH-1:0] reg_ddrc_t_rfc_min_ab_freq2
  ,input logic   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq2
  ,input logic   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq2

  ,input logic [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq2

  ,input logic  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq2
  ,input logic                             reg_ddrc_t_pgm_x1_sel_freq2
  ,input logic  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq2
  ,input logic  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq2

  ,input logic   [15:0]  reg_ddrc_mr_freq2
  ,input logic   [15:0]  reg_ddrc_emr_freq2
  ,input logic   [15:0]  reg_ddrc_emr2_freq2
  ,input logic   [15:0]  reg_ddrc_emr3_freq2
  ,input logic   [15:0]  reg_ddrc_mr4_freq2
  ,input logic   [15:0]  reg_ddrc_mr5_freq2
  ,input logic   [15:0]  reg_ddrc_mr6_freq2
  ,input logic   [15:0]  reg_ddrc_mr22_freq2
  ,input logic   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq2
  ,input logic   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq2
  ,input logic   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq2
  ,input logic   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq2
  ,input logic   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2
  ,input logic   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq2
  ,input logic   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq2
  ,input logic   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq2
  ,input logic   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq2
  ,input logic   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq2
  ,input logic   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq2
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq2
  ,input logic   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq2
  ,input logic   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq2
  ,input logic   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq2
  ,input logic   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq2
  ,input logic   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq2
  ,input logic   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq2
  ,input logic   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq2
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq2
  ,input logic   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq2
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq2
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq2
  ,input logic   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq2
  ,input logic   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq2
  ,input logic   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq2
  ,input logic   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq2
  ,input logic   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq2
  ,input logic   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq2
  ,input logic   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq2
  ,input logic   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq2
  ,input logic   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq2
  ,input logic   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq2
  ,input logic   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq2
  ,input logic   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq2
  ,input logic   [T_PDN_WIDTH-1:0]   reg_ddrc_t_pdn_freq2
  ,input logic   [T_XSR_DSM_X1024_WIDTH-1:0]   reg_ddrc_t_xsr_dsm_x1024_freq2
  ,input logic   [T_CSH_WIDTH-1:0]   reg_ddrc_t_csh_freq2
  ,input logic   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq2
  ,input logic   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq2
  ,input logic   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq2
  ,input logic   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq2
  ,input logic   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq2
  ,input logic                                 reg_ddrc_dqsosc_enable_freq2
  ,input logic                                 reg_ddrc_dqsosc_interval_unit_freq2
  ,input logic   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq2
  ,input logic   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq2
  ,input logic   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq2
  ,input logic   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq2
  ,input logic                           reg_ddrc_dvfsq_enable_freq2
  ,input logic   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq2
  ,input logic   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq2
  ,input logic [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq2
  ,input logic [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq2
  ,input   [BANK_ORG_WIDTH-1:0]         reg_ddrc_bank_org_freq2
  ,input   [RD2WR_WIDTH-1:0]            reg_ddrc_rd2wr_s_freq2
  ,input   [MRR2RD_WIDTH-1:0]           reg_ddrc_mrr2rd_freq2
  ,input   [MRR2WR_WIDTH-1:0]           reg_ddrc_mrr2wr_freq2
  ,input   [MRR2MRW_WIDTH-1:0]          reg_ddrc_mrr2mrw_freq2
  ,input   [WS_OFF2WS_FS_WIDTH-1:0]     reg_ddrc_ws_off2ws_fs_freq2
  ,input   [T_WCKSUS_WIDTH-1:0]         reg_ddrc_t_wcksus_freq2
  ,input   [WS_FS2WCK_SUS_WIDTH-1:0]    reg_ddrc_ws_fs2wck_sus_freq2
  ,input   [MAX_RD_SYNC_WIDTH-1:0]      reg_ddrc_max_rd_sync_freq2
  ,input   [MAX_WR_SYNC_WIDTH-1:0]      reg_ddrc_max_wr_sync_freq2
  ,input   [DFI_TWCK_DELAY_WIDTH-1:0]   reg_ddrc_dfi_twck_delay_freq2
  ,input   [DFI_TWCK_EN_RD_WIDTH-1:0]       reg_ddrc_dfi_twck_en_rd_freq2
  ,input   [DFI_TWCK_EN_WR_WIDTH-1:0]       reg_ddrc_dfi_twck_en_wr_freq2
  ,input   [DFI_TWCK_EN_FS_WIDTH-1:0]       reg_ddrc_dfi_twck_en_fs_freq2
  ,input   [DFI_TWCK_DIS_WIDTH-1:0]         reg_ddrc_dfi_twck_dis_freq2
  ,input   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] reg_ddrc_dfi_twck_fast_toggle_freq2
  ,input   [DFI_TWCK_TOGGLE_WIDTH-1:0]      reg_ddrc_dfi_twck_toggle_freq2
  ,input   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   reg_ddrc_dfi_twck_toggle_cs_freq2
  ,input   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_freq2
  ,input                                    reg_ddrc_dfi_twck_toggle_post_rd_en_freq2
  ,input   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq2

  ,input logic   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq2
  ,input logic   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq2
  ,input logic   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq2
  ,input logic   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq2
  ,input logic   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq2
  ,input logic   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq2
  ,input logic   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq2
  ,input logic   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq2
  ,input logic   [DFI_TPHY_WRCSLAT_WIDTH-1:0]     reg_ddrc_dfi_tphy_wrcslat_freq2


  ,input logic [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq2
  ,input logic [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq2
  ,input logic [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq2
  ,input logic [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq2
  ,input logic [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq2
  ,input logic [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq2

  ,input logic [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq2
  ,input logic [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq2


  ,input logic                              reg_ddrc_rd_link_ecc_enable_freq2
  ,input logic                              reg_ddrc_wr_link_ecc_enable_freq2


  /////////////////////
  // Freq3 registers //
  /////////////////////

  ,input logic [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq3

  ,input logic [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3
  ,input logic [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3
  ,input logic [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]  reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3
  ,input logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3
  ,input logic                                              reg_ddrc_ppt2_en_freq3
  ,input logic                                              reg_ddrc_ppt2_override_freq3
  ,input logic                                              reg_ddrc_ctrlupd_after_dqsosc_freq3

  ,input logic           reg_ddrc_frequency_ratio_freq3

  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq3
  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq3

  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_freq3
  ,input logic  [DERATED_T_RAS_MIN_WIDTH-1:0]  reg_ddrc_derated_t_ras_min_freq3
  ,input logic  [DERATED_T_RP_WIDTH-1:0]       reg_ddrc_derated_t_rp_freq3
  ,input logic  [DERATED_T_RRD_WIDTH-1:0]      reg_ddrc_derated_t_rrd_freq3
  ,input logic  [DERATED_T_RC_WIDTH-1:0]       reg_ddrc_derated_t_rc_freq3
  ,input logic   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq3
  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_write_freq3
  ,input logic   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq3
  ,input logic   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq3
  ,input logic   [REFRESH_MARGIN_WIDTH-1:0]   reg_ddrc_refresh_margin_freq3
  ,input logic   [REFRESH_TO_X1_X32_WIDTH-1:0]   reg_ddrc_refresh_to_x1_x32_freq3
  ,input logic   [REFRESH_TO_AB_X32_WIDTH-1:0]   reg_ddrc_refresh_to_ab_x32_freq3
  ,input logic           reg_ddrc_refresh_to_x1_sel_freq3
  ,input logic           reg_ddrc_t_refi_x1_sel_freq3
  ,input logic   [T_REFI_X1_X32_WIDTH-1:0]  reg_ddrc_t_refi_x1_x32_freq3
  ,input logic   [T_RFC_MIN_WIDTH-1:0]   reg_ddrc_t_rfc_min_freq3
  ,input logic   [T_RFC_MIN_AB_WIDTH-1:0] reg_ddrc_t_rfc_min_ab_freq3
  ,input logic   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq3
  ,input logic   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq3

  ,input logic [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq3

  ,input logic  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq3
  ,input logic                             reg_ddrc_t_pgm_x1_sel_freq3
  ,input logic  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq3
  ,input logic  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq3

  ,input logic   [15:0]  reg_ddrc_mr_freq3
  ,input logic   [15:0]  reg_ddrc_emr_freq3
  ,input logic   [15:0]  reg_ddrc_emr2_freq3
  ,input logic   [15:0]  reg_ddrc_emr3_freq3
  ,input logic   [15:0]  reg_ddrc_mr4_freq3
  ,input logic   [15:0]  reg_ddrc_mr5_freq3
  ,input logic   [15:0]  reg_ddrc_mr6_freq3
  ,input logic   [15:0]  reg_ddrc_mr22_freq3
  ,input logic   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq3
  ,input logic   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq3
  ,input logic   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq3
  ,input logic   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq3
  ,input logic   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3
  ,input logic   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq3
  ,input logic   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq3
  ,input logic   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq3
  ,input logic   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq3
  ,input logic   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq3
  ,input logic   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq3
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq3
  ,input logic   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq3
  ,input logic   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq3
  ,input logic   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq3
  ,input logic   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq3
  ,input logic   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq3
  ,input logic   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq3
  ,input logic   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq3
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq3
  ,input logic   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq3
  ,input logic   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq3
  ,input logic   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq3
  ,input logic   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq3
  ,input logic   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq3
  ,input logic   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq3
  ,input logic   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq3
  ,input logic   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq3
  ,input logic   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq3
  ,input logic   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq3
  ,input logic   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq3
  ,input logic   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq3
  ,input logic   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq3
  ,input logic   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq3
  ,input logic   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq3
  ,input logic   [T_PDN_WIDTH-1:0]   reg_ddrc_t_pdn_freq3
  ,input logic   [T_XSR_DSM_X1024_WIDTH-1:0]   reg_ddrc_t_xsr_dsm_x1024_freq3
  ,input logic   [T_CSH_WIDTH-1:0]   reg_ddrc_t_csh_freq3
  ,input logic   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq3
  ,input logic   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq3
  ,input logic   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq3
  ,input logic   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq3
  ,input logic   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq3
  ,input logic                                 reg_ddrc_dqsosc_enable_freq3
  ,input logic                                 reg_ddrc_dqsosc_interval_unit_freq3
  ,input logic   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq3
  ,input logic   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq3
  ,input logic   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq3
  ,input logic   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq3
  ,input logic                           reg_ddrc_dvfsq_enable_freq3
  ,input logic   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq3
  ,input logic   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq3
  ,input logic [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq3
  ,input logic [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq3
  ,input   [BANK_ORG_WIDTH-1:0]         reg_ddrc_bank_org_freq3
  ,input   [RD2WR_WIDTH-1:0]            reg_ddrc_rd2wr_s_freq3
  ,input   [MRR2RD_WIDTH-1:0]           reg_ddrc_mrr2rd_freq3
  ,input   [MRR2WR_WIDTH-1:0]           reg_ddrc_mrr2wr_freq3
  ,input   [MRR2MRW_WIDTH-1:0]          reg_ddrc_mrr2mrw_freq3
  ,input   [WS_OFF2WS_FS_WIDTH-1:0]     reg_ddrc_ws_off2ws_fs_freq3
  ,input   [T_WCKSUS_WIDTH-1:0]         reg_ddrc_t_wcksus_freq3
  ,input   [WS_FS2WCK_SUS_WIDTH-1:0]    reg_ddrc_ws_fs2wck_sus_freq3
  ,input   [MAX_RD_SYNC_WIDTH-1:0]      reg_ddrc_max_rd_sync_freq3
  ,input   [MAX_WR_SYNC_WIDTH-1:0]      reg_ddrc_max_wr_sync_freq3
  ,input   [DFI_TWCK_DELAY_WIDTH-1:0]   reg_ddrc_dfi_twck_delay_freq3
  ,input   [DFI_TWCK_EN_RD_WIDTH-1:0]       reg_ddrc_dfi_twck_en_rd_freq3
  ,input   [DFI_TWCK_EN_WR_WIDTH-1:0]       reg_ddrc_dfi_twck_en_wr_freq3
  ,input   [DFI_TWCK_EN_FS_WIDTH-1:0]       reg_ddrc_dfi_twck_en_fs_freq3
  ,input   [DFI_TWCK_DIS_WIDTH-1:0]         reg_ddrc_dfi_twck_dis_freq3
  ,input   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] reg_ddrc_dfi_twck_fast_toggle_freq3
  ,input   [DFI_TWCK_TOGGLE_WIDTH-1:0]      reg_ddrc_dfi_twck_toggle_freq3
  ,input   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   reg_ddrc_dfi_twck_toggle_cs_freq3
  ,input   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_freq3
  ,input                                    reg_ddrc_dfi_twck_toggle_post_rd_en_freq3
  ,input   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq3

  ,input logic   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq3
  ,input logic   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq3
  ,input logic   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq3
  ,input logic   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq3
  ,input logic   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq3
  ,input logic   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq3
  ,input logic   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq3
  ,input logic   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq3
  ,input logic   [DFI_TPHY_WRCSLAT_WIDTH-1:0]     reg_ddrc_dfi_tphy_wrcslat_freq3


  ,input logic [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq3
  ,input logic [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq3
  ,input logic [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq3
  ,input logic [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq3
  ,input logic [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq3
  ,input logic [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq3

  ,input logic [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq3
  ,input logic [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq3


  ,input logic                              reg_ddrc_rd_link_ecc_enable_freq3
  ,input logic                              reg_ddrc_wr_link_ecc_enable_freq3














  ,output logic [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024
  ,output logic [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024
  ,output logic [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]  regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8
  ,output logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     regmux_ddrc_dfi_t_ctrlupd_interval_type1
  ,output logic [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit
  ,output logic                                              regmux_ddrc_ppt2_en
  ,output logic                                              regmux_ddrc_ppt2_override
  ,output logic                                              regmux_ddrc_ctrlupd_after_dqsosc

  ,output logic           regmux_ddrc_frequency_ratio
  ,output logic           regmux_ddrc_frequency_ratio_next

  ,output logic   [TARGET_FREQUENCY_WIDTH-1:0]   regmux_ddrc_hwffc_target_frequency
  ,output logic   [TARGET_FREQUENCY_WIDTH-1:0]   regmux_ddrc_target_frequency

  //ccx_tgl : ; regmux_ddrc_t_zq_long_nop_div[13] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic  [T_ZQ_LONG_NOP_WIDTH-1:0]  regmux_ddrc_t_zq_long_nop_div
  //ccx_tgl : ; regmux_ddrc_t_zq_short_nop_div[9] ;  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic  [T_ZQ_SHORT_NOP_WIDTH-1:0] regmux_ddrc_t_zq_short_nop_div
  //ccx_tgl : ; regmux_ddrc_t_zq_reset_nop_div[9] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_ZQ_RESET_NOP_WIDTH-1:0] regmux_ddrc_t_zq_reset_nop_div
  //ccx_tgl : ; regmux_ddrc_t_zq_short_interval_x1024[19] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] regmux_ddrc_t_zq_short_interval_x1024

   // PWRTMG
  ,output logic [POWERDOWN_TO_X32_WIDTH-1:0] regmux_ddrc_powerdown_to_x32
  ,output logic [SELFREF_TO_X32_WIDTH-1:0] regmux_ddrc_selfref_to_x32

   ,output logic [HW_LP_IDLE_X32_WIDTH-1:0] regmux_ddrc_hw_lp_idle_x32

   ,output logic [MR4_READ_INTERVAL_WIDTH-1:0] regmux_ddrc_mr4_read_interval_div

  ,output logic [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0] reg_ddrc_blk_channel_idle_time_x32_div

  ,output logic  [T_PGM_X1_X1024_WIDTH-1:0]               regmux_ddrc_t_pgm_x1_x1024_div 
  ,output logic                                           regmux_ddrc_t_pgm_x1_sel_div
  ,output logic  [T_PGMPST_X32_WIDTH-1:0]                 regmux_ddrc_t_pgmpst_x32_div
  ,output logic  [T_PGM_EXIT_WIDTH-1:0]                   regmux_ddrc_t_pgm_exit_div


  ,output logic [REFRESH_TO_X1_X32_WIDTH-1:0] regmux_ddrc_refresh_to_x1_x32_div  
  ,output logic [REFRESH_TO_AB_X32_WIDTH-1:0] regmux_ddrc_refresh_to_ab_x32_div
  //ccx_tgl : ; regmux_ddrc_t_rfc_min_div[11:9]; ; The register bit are wider than maximum value to be based on JEDEC spec to be redundancy. 
  ,output logic [T_RFC_MIN_WIDTH-1:0]         regmux_ddrc_t_rfc_min_div
  //ccx_tgl : ; regmux_ddrc_t_rfc_min_ab_div[11:9]; ; The register bit are wider than maximum value to be based on JEDEC spec to be redundancy. 
  ,output logic [T_RFC_MIN_AB_WIDTH-1:0]      regmux_ddrc_t_rfc_min_ab_div
  ,output logic regmux_ddrc_refresh_to_x1_sel
  ,output logic regmux_ddrc_t_refi_x1_sel
  //ccx_tgl : ; regmux_ddrc_t_refi_x1_x32_div[11:9]; ; The register bit are wider than maximum value to be based on JEDEC spec to be redundancy. 
  //ccx_tgl : ; regmux_ddrc_t_refi_x1_x32_div[13]; ; Max value is 13'h1044 in LPDDR. so bit 13 cannot be toggled. P80001562-341729
  ,output logic [T_REFI_X1_X32_WIDTH-1:0]  regmux_ddrc_t_refi_x1_x32_div

  ,output logic  [REFRESH_MARGIN_WIDTH-1:0]  regmux_ddrc_refresh_margin_div


//ccx_tgl : ; regmux_ddrc_t_rfmpb_div[11]; ; This register value is devided by frequency ratio. Thus this MSB can't be toggled. Can be ignored.
  ,output logic [T_RFMPB_WIDTH-1:0] regmux_ddrc_t_rfmpb_div

  //ccx_tgl : ; regmux_ddrc_t_pbr2pbr_div[7]; ; The register bit are wider than maximum value to be based on JEDEC spec to be redundancy. 
  ,output logic [T_PBR2PBR_WIDTH-1:0]       regmux_ddrc_t_pbr2pbr_div
  ,output logic [T_PBR2ACT_WIDTH-1:0]       regmux_ddrc_t_pbr2act
   //ccx_tgl : ; regmux_ddrc_derated_t_rcd_div[7];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic  [DERATED_T_RCD_WIDTH-1:0]      regmux_ddrc_derated_t_rcd_div
   //ccx_tgl : ; regmux_ddrc_derated_t_ras_min_div[7];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic  [DERATED_T_RAS_MIN_WIDTH-1:0]  regmux_ddrc_derated_t_ras_min_div
   //ccx_tgl : ; regmux_ddrc_derated_t_rp_div[6];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic  [DERATED_T_RP_WIDTH-1:0]       regmux_ddrc_derated_t_rp_div
   //ccx_tgl : ; regmux_ddrc_derated_t_rrd_div[5];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic  [DERATED_T_RRD_WIDTH-1:0]      regmux_ddrc_derated_t_rrd_div
   //ccx_tgl : ; regmux_ddrc_derated_t_rc_div[7];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic  [DERATED_T_RC_WIDTH-1:0]       regmux_ddrc_derated_t_rc_div

   //ccx_tgl : ; regmux_ddrc_derated_t_rcd_write_div[7];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic  [DERATED_T_RCD_WIDTH-1:0]      regmux_ddrc_derated_t_rcd_write_div

   //ccx_tgl : ; regmux_ddrc_diff_rank_rd_gap_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic  [DIFF_RANK_RD_GAP_WIDTH-1:0]   regmux_ddrc_diff_rank_rd_gap_div
   //ccx_tgl : ; regmux_ddrc_diff_rank_wr_gap_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic  [DIFF_RANK_WR_GAP_WIDTH-1:0]   regmux_ddrc_diff_rank_wr_gap_div
   //ccx_tgl : ; regmux_ddrc_rd2wr_dr_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic  [RD2WR_DR_WIDTH-1:0]   regmux_ddrc_rd2wr_dr_div
   //ccx_tgl : ; regmux_ddrc_wr2rd_dr_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic  [WR2RD_DR_WIDTH-1:0]   regmux_ddrc_wr2rd_dr_div

   //ccx_tgl : ; regmux_ddrc_refresh_timer0_start_value_x32_div; ; This register toggles only in performance test. So it can be excluded in ARB configuration.
  ,output logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] regmux_ddrc_refresh_timer0_start_value_x32_div
   //ccx_tgl : ; regmux_ddrc_refresh_timer1_start_value_x32_div; ; This register toggles only in performance test. So it can be excluded in ARB configuration.
  ,output logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] regmux_ddrc_refresh_timer1_start_value_x32_div

   //ccx_tgl : ; regmux_ddrc_t_ras_min_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
  ,output logic [T_RAS_MIN_WIDTH-1:0] regmux_ddrc_t_ras_min_div
   //ccx_tgl : ; regmux_ddrc_t_ras_max_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
  ,output logic [T_RAS_MAX_WIDTH-1:0] regmux_ddrc_t_ras_max_div
   //ccx_tgl : ; regmux_ddrc_t_faw_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
  ,output logic [T_FAW_WIDTH-1:0] regmux_ddrc_t_faw_div
  ,output logic [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] regmux_ddrc_lpddr4_diff_bank_rwa2pre_div
   //ccx_tgl : ; regmux_ddrc_wr2pre_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
  ,output logic [WR2PRE_WIDTH-1:0] regmux_ddrc_wr2pre_div
   //ccx_tgl : ; regmux_ddrc_wra2pre_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
  ,output logic [WRA2PRE_WIDTH-1:0] regmux_ddrc_wra2pre_div

   //ccx_tgl : ; regmux_ddrc_t_rc_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic [T_RC_WIDTH-1:0] regmux_ddrc_t_rc_div
   //ccx_tgl : ; regmux_ddrc_rd2pre_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [RD2PRE_WIDTH-1:0] regmux_ddrc_rd2pre_div
   //ccx_tgl : ; regmux_ddrc_rda2pre_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [RDA2PRE_WIDTH-1:0] regmux_ddrc_rda2pre_div
   //ccx_tgl : ; regmux_ddrc_t_xp_div[5]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_XP_WIDTH-1:0] regmux_ddrc_t_xp_div
   //ccx_tgl : ; regmux_ddrc_t_rcd_write_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_RCD_WIDTH-1:0] regmux_ddrc_t_rcd_write_div

   //ccx_tgl : ; regmux_ddrc_wr2rd_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
   ,output logic [WR2RD_WIDTH-1:0] regmux_ddrc_wr2rd_div
   //ccx_tgl : ; regmux_ddrc_rd2wr_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [RD2WR_WIDTH-1:0] regmux_ddrc_rd2wr_div
   //ccx_tgl : ; regmux_ddrc_read_latency_div[6]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [READ_LATENCY_WIDTH-1:0] regmux_ddrc_read_latency_div
   //ccx_tgl : ; regmux_ddrc_write_latency_div[6]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [WRITE_LATENCY_WIDTH-1:0] regmux_ddrc_write_latency_div

  //ccx_tgl : ; regmux_ddrc_rd2mr_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [RD2MR_WIDTH-1:0] regmux_ddrc_rd2mr_div
   //ccx_tgl : ; regmux_ddrc_t_mr_div[6] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used. 
  ,output logic [T_MR_WIDTH-1:0]  regmux_ddrc_t_mr_div
  //ccx_tgl : ; regmux_ddrc_wr2mr_div[7] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [RD2MR_WIDTH-1:0] regmux_ddrc_wr2mr_div

   //ccx_tgl : ; regmux_ddrc_t_rp_div[6]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic [T_RP_WIDTH-1:0] regmux_ddrc_t_rp_div
   //ccx_tgl : ; regmux_ddrc_t_rrd_div[5]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_RRD_WIDTH-1:0] regmux_ddrc_t_rrd_div
   //ccx_tgl : ; regmux_ddrc_t_ccd_div[5]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_CCD_WIDTH-1:0] regmux_ddrc_t_ccd_div
   //ccx_tgl : ; regmux_ddrc_t_rcd_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_RCD_WIDTH-1:0] regmux_ddrc_t_rcd_div

   //ccx_tgl : ; regmux_ddrc_t_cke_div[5]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic [T_CKE_WIDTH-1:0] regmux_ddrc_t_cke_div
  //ccx_tgl : ; regmux_ddrc_t_ckesr_div[6];  ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_CKESR_WIDTH-1:0] regmux_ddrc_t_ckesr_div
  //ccx_tgl : ; regmux_ddrc_t_cksre_div[6:4];  ; This item can be ignored. For LPDDR5, Max is t_xp(tCSLCK) = Max(5ns, 3nCK) = 5ns / 1.25ns = 4(DRAM clock cycle). For LPDDR4, Max is t_xp(tCKELCK) = Max(5ns, 5nCK) = 5ns / 0.468ns = 10(DRAM clock cycle).
  ,output logic [T_CKSRE_WIDTH-1:0] regmux_ddrc_t_cksre_div
  //ccx_tgl : ; regmux_ddrc_t_cksrx_div[5];  ; ccx_tgl : ; par_waddr_err_pulse[0]; ; This item wasn't covered due to VCS tool issue(P80001562-191189).This has been covered on VCS:2021-09-SP2. So we can exclude this item as long as we are using VCS:S-2021.09.
  ,output logic [T_CKSRX_WIDTH-1:0] regmux_ddrc_t_cksrx_div

    //ccx_tgl : ; regmux_ddrc_t_ckcsx_div[5];  ; This item can be ignored. For LPDDR5, Max is tpdxcsodton/tCK+2=20ns/1.25ns+2=18(DRAM clock cycle). if odtd_cs is 0 ,Max is t_xp=Max(7ns,3nCK)=7ns/1.25ns=6(DRAM clock cycle) if odtd_cs is 1. For LPDDR4, Max is t_xp=Max(7.5ns,3nCK)=7.5ns/0.468ns=16(DRAM clock cycle). 
   ,output logic [T_CKCSX_WIDTH-1:0] regmux_ddrc_t_ckcsx_div

   //ccx_tgl : ; regmux_ddrc_wr2rd_s_div[7]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [WR2RD_S_WIDTH-1:0] regmux_ddrc_wr2rd_s_div
   //ccx_tgl : ; regmux_ddrc_t_rrd_s_div[5]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_RRD_S_WIDTH-1:0] regmux_ddrc_t_rrd_s_div
  //ccx_tgl : ; regmux_ddrc_t_ccd_s_div[4]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_CCD_S_WIDTH-1:0] regmux_ddrc_t_ccd_s_div

  //ccx_tgl : ; regmux_ddrc_t_cmdcke_div[3]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_CMDCKE_WIDTH-1:0] regmux_ddrc_t_cmdcke_div
  ,output logic [T_PDN_WIDTH-1:0]    regmux_ddrc_t_pdn
  ,output logic [T_XSR_DSM_X1024_WIDTH-1:0]   regmux_ddrc_t_xsr_dsm_x1024
  ,output logic [T_CSH_WIDTH-1:0]   regmux_ddrc_t_csh

  //ccx_tgl : ; regmux_ddrc_t_ccd_mw_div[6]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [T_CCD_MW_WIDTH-1:0] regmux_ddrc_t_ccd_mw_div
  //ccx_tgl : ; regmux_ddrc_odtloff_div[6]; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
  ,output logic [ODTLOFF_WIDTH-1:0] regmux_ddrc_odtloff_div
   //ccx_tgl : ; regmux_ddrc_t_ppd_div[3] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic [T_PPD_WIDTH-1:0] regmux_ddrc_t_ppd_div

   //ccx_tgl : ; regmux_ddrc_t_xsr_div[11] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic [T_XSR_WIDTH-1:0] regmux_ddrc_t_xsr_div
   //ccx_tgl : ; regmux_ddrc_t_osco_div[8] ; ; This item can be ignored. The register stores a config register value but devided by 2 or 4. Since the register width is the same to the original one, MSB is not used.
   ,output logic [T_OSCO_WIDTH-1:0] regmux_ddrc_t_osco_div
  ,output logic                               regmux_ddrc_dqsosc_enable
  ,output logic                               regmux_ddrc_dqsosc_interval_unit
  ,output logic [DQSOSC_INTERVAL_WIDTH-1:0] regmux_ddrc_dqsosc_interval

   ,output logic [T_VRCG_DISABLE_WIDTH-1:0] regmux_ddrc_t_vrcg_disable_div
  ,output logic [T_VRCG_ENABLE_WIDTH-1:0] regmux_ddrc_t_vrcg_enable_div
  ,output logic  [T_ZQ_STOP_WIDTH-1:0]   regmux_ddrc_t_zq_stop
  ,output logic                          regmux_ddrc_dvfsq_enable
  ,output logic                          regmux_ddrc_dvfsq_enable_next


// INIT3
  ,output logic  [15:0]  regmux_ddrc_mr
  ,output logic  [15:0]  regmux_ddrc_emr
// INIT4
  ,output logic  [15:0]  regmux_ddrc_emr2
  ,output logic  [15:0]  regmux_ddrc_emr3
// INIT6
  ,output logic  [15:0]  regmux_ddrc_mr4
  ,output logic  [15:0]  regmux_ddrc_mr5
// INIT7
  ,output logic  [15:0]  regmux_ddrc_mr6
  ,output logic  [15:0]  regmux_ddrc_mr22

  ,output   [BANK_ORG_WIDTH-1:0]         regmux_ddrc_bank_org
  ,output   [MAX_RD_SYNC_WIDTH-1:0]      regmux_ddrc_rd2wr_s
  ,output   [MRR2RD_WIDTH-1:0]           regmux_ddrc_mrr2rd
  ,output   [MRR2WR_WIDTH-1:0]           regmux_ddrc_mrr2wr
  ,output   [MRR2MRW_WIDTH-1:0]          regmux_ddrc_mrr2mrw
  ,output   [WS_OFF2WS_FS_WIDTH-1:0]     regmux_ddrc_ws_off2ws_fs
  ,output   [T_WCKSUS_WIDTH-1:0]         regmux_ddrc_t_wcksus
  ,output   [WS_FS2WCK_SUS_WIDTH-1:0]    regmux_ddrc_ws_fs2wck_sus
  ,output   [MAX_RD_SYNC_WIDTH-1:0]      regmux_ddrc_max_rd_sync
  ,output   [MAX_WR_SYNC_WIDTH-1:0]      regmux_ddrc_max_wr_sync
  ,output   [DFI_TWCK_DELAY_WIDTH-1:0]   regmux_ddrc_dfi_twck_delay
  ,output   [DFI_TWCK_EN_RD_WIDTH-1:0]       regmux_ddrc_dfi_twck_en_rd
  ,output   [DFI_TWCK_EN_WR_WIDTH-1:0]       regmux_ddrc_dfi_twck_en_wr
  ,output   [DFI_TWCK_EN_FS_WIDTH-1:0]       regmux_ddrc_dfi_twck_en_fs
  ,output   [DFI_TWCK_DIS_WIDTH-1:0]         regmux_ddrc_dfi_twck_dis
  ,output   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] regmux_ddrc_dfi_twck_fast_toggle
  ,output   [DFI_TWCK_TOGGLE_WIDTH-1:0]      regmux_ddrc_dfi_twck_toggle
  ,output   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   regmux_ddrc_dfi_twck_toggle_cs
  ,output   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] regmux_ddrc_dfi_twck_toggle_post
  ,output                                    regmux_ddrc_dfi_twck_toggle_post_rd_en
  ,output   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] regmux_ddrc_dfi_twck_toggle_post_rd

  ,output logic  [6:0]   regmux_ddrc_dfi_t_rddata_en
  ,output logic  [5:0]   regmux_ddrc_dfi_tphy_wrdata
  ,output logic  [DFI_TPHY_WRLAT_WIDTH-1:0]  regmux_ddrc_dfi_tphy_wrlat
  ,output logic  [4:0]   regmux_ddrc_dfi_t_wrdata_delay
  ,output logic  [DFI_T_CTRL_DELAY_WIDTH-1:0]   regmux_ddrc_dfi_t_ctrl_delay
  ,output logic  [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  regmux_ddrc_dfi_t_dram_clk_disable
  ,output logic  [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]   regmux_ddrc_dfi_t_dram_clk_enable

  ,output logic  [6:0]   regmux_ddrc_dfi_tphy_rdcslat
  ,output logic  [DFI_TPHY_WRCSLAT_WIDTH-1:0]     regmux_ddrc_dfi_tphy_wrcslat




  ,output logic [HPR_MAX_STARVE_WIDTH-1:0] regmux_ddrc_hpr_max_starve
  ,output logic [HPR_XACT_RUN_LENGTH_WIDTH-1:0] regmux_ddrc_hpr_xact_run_length
  ,output logic [LPR_MAX_STARVE_WIDTH-1:0] regmux_ddrc_lpr_max_starve
  ,output logic [LPR_XACT_RUN_LENGTH_WIDTH-1:0] regmux_ddrc_lpr_xact_run_length
  ,output logic [W_MAX_STARVE_WIDTH-1:0] regmux_ddrc_w_max_starve
  ,output logic [W_XACT_RUN_LENGTH_WIDTH-1:0] regmux_ddrc_w_xact_run_length

  ,output logic [PAGECLOSE_TIMER_WIDTH-1:0] regmux_ddrc_pageclose_timer
  ,output logic [RDWR_IDLE_GAP_WIDTH-1:0] regmux_ddrc_rdwr_idle_gap



  ,output logic          regmux_ddrc_rd_link_ecc_enable
  ,output logic          regmux_ddrc_wr_link_ecc_enable


);

wire [T_REFI_X1_X32_WIDTH-1 : 0] regmux_ddrc_t_refi_x1_x32_div_comb;
wire [REFRESH_TO_X1_X32_WIDTH-1 : 0] regmux_ddrc_refresh_to_x1_x32_div_comb;
wire [REFRESH_TO_AB_X32_WIDTH-1 : 0] regmux_ddrc_refresh_to_ab_x32_div_comb;
wire regmux_ddrc_refresh_to_x1_sel_comb;
wire regmux_ddrc_t_refi_x1_sel_comb;
wire [REFRESH_MARGIN_WIDTH-1 : 0] regmux_ddrc_refresh_margin_div_comb;
wire [T_RFC_MIN_WIDTH-1 : 0] regmux_ddrc_t_rfc_min_div_comb;
wire [T_RFC_MIN_AB_WIDTH-1 : 0] regmux_ddrc_t_rfc_min_ab_div_comb;
wire [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1 : 0] regmux_ddrc_refresh_timer0_start_value_x32_div_comb;
wire [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1 : 0] regmux_ddrc_refresh_timer1_start_value_x32_div_comb;
wire [T_RFMPB_WIDTH-1 : 0] regmux_ddrc_t_rfmpb_div_comb;

wire [T_PBR2PBR_WIDTH-1 : 0] regmux_ddrc_t_pbr2pbr_div_comb;

// DERATEVAL0
wire [DERATED_T_RCD_WIDTH-1:0]      regmux_ddrc_derated_t_rcd;
wire [DERATED_T_RAS_MIN_WIDTH-1:0]  regmux_ddrc_derated_t_ras_min;
wire [DERATED_T_RP_WIDTH-1:0]       regmux_ddrc_derated_t_rp;
wire [DERATED_T_RRD_WIDTH-1:0]      regmux_ddrc_derated_t_rrd;
// DERATEVAL1
wire [DERATED_T_RC_WIDTH-1:0]       regmux_ddrc_derated_t_rc;
// DERATEINT
wire  [MR4_READ_INTERVAL_WIDTH-1:0]  regmux_ddrc_mr4_read_interval;
// PWRTMG

// DERATEVAL1
wire [DERATED_T_RCD_WIDTH-1:0]      regmux_ddrc_derated_t_rcd_write;

// RFSHCTL0
wire  [REFRESH_MARGIN_WIDTH-1:0]   regmux_ddrc_refresh_margin;
wire  [REFRESH_TO_X1_X32_WIDTH-1:0]   regmux_ddrc_refresh_to_x1_x32;
wire  [REFRESH_TO_AB_X32_WIDTH-1:0]   regmux_ddrc_refresh_to_ab_x32;
// RFSHTMG
wire  [T_REFI_X1_X32_WIDTH-1:0]  regmux_ddrc_t_refi_x1_x32;
wire  [T_RFC_MIN_WIDTH-1:0]   regmux_ddrc_t_rfc_min;
wire  [T_RFC_MIN_AB_WIDTH-1:0]   regmux_ddrc_t_rfc_min_ab;

wire  [T_PBR2PBR_WIDTH-1:0]   regmux_ddrc_t_pbr2pbr;
wire [T_RFMPB_WIDTH-1 : 0] regmux_ddrc_t_rfmpb;

  wire  [T_PGM_X1_X1024_WIDTH-1:0]          regmux_ddrc_t_pgm_x1_x1024;
  wire                                      regmux_ddrc_t_pgm_x1_sel;
  wire  [T_PGMPST_X32_WIDTH-1:0]            regmux_ddrc_t_pgmpst_x32;
  wire  [T_PGM_EXIT_WIDTH-1:0]              regmux_ddrc_t_pgm_exit;


wire  [DIFF_RANK_RD_GAP_WIDTH-1:0]   regmux_ddrc_diff_rank_rd_gap;
wire  [DIFF_RANK_WR_GAP_WIDTH-1:0]   regmux_ddrc_diff_rank_wr_gap;
wire  [RD2WR_DR_WIDTH-1:0]   regmux_ddrc_rd2wr_dr;
wire  [WR2RD_DR_WIDTH-1:0]   regmux_ddrc_wr2rd_dr;

wire [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] regmux_ddrc_refresh_timer0_start_value_x32;
wire [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] regmux_ddrc_refresh_timer1_start_value_x32;

// ECSSET1TMG0, ECSSET1TMG1, ECSSET1TMG2
wire [T_ECS_INT_X1024_WIDTH-1:0]                regmux_ddrc_t_ecs_int_x1024;
wire [T_REFI_ECS_OFFSET_X1_X32_WIDTH-1:0]       regmux_ddrc_t_refi_ecs_offset_x1_x32;


// DRAMSET1TMG0
wire  [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] regmux_ddrc_lpddr4_diff_bank_rwa2pre;
wire  [WR2PRE_WIDTH-1:0]   regmux_ddrc_wr2pre;
wire  [WRA2PRE_WIDTH-1:0]   regmux_ddrc_wra2pre;
wire  [T_FAW_WIDTH-1:0]   regmux_ddrc_t_faw;
wire  [T_RAS_MAX_WIDTH-1:0]   regmux_ddrc_t_ras_max;
wire  [T_RAS_MIN_WIDTH-1:0]   regmux_ddrc_t_ras_min;
// DRAMSET1TMG1
wire  [T_RCD_WIDTH-1:0]   regmux_ddrc_t_rcd_write;
wire  [T_XP_WIDTH-1:0]   regmux_ddrc_t_xp;
wire  [RD2PRE_WIDTH-1:0]   regmux_ddrc_rd2pre;
wire  [RDA2PRE_WIDTH-1:0]   regmux_ddrc_rda2pre;
wire  [T_RC_WIDTH-1:0]   regmux_ddrc_t_rc;
// DRAMTMG2
wire  [WRITE_LATENCY_WIDTH-1:0]   regmux_ddrc_write_latency;
wire  [READ_LATENCY_WIDTH-1:0]   regmux_ddrc_read_latency;
wire  [RD2WR_WIDTH-1:0]   regmux_ddrc_rd2wr;
wire  [WR2RD_WIDTH-1:0]   regmux_ddrc_wr2rd;
// DRAMTMG3
wire  [RD2MR_WIDTH-1:0]   regmux_ddrc_wr2mr;
wire  [T_MR_WIDTH-1:0]    regmux_ddrc_t_mr;
wire  [RD2MR_WIDTH-1:0]   regmux_ddrc_rd2mr;
// DRAMTMG4
wire  [T_RCD_WIDTH-1:0]   regmux_ddrc_t_rcd;
wire  [T_CCD_WIDTH-1:0]   regmux_ddrc_t_ccd;
wire  [T_RRD_WIDTH-1:0]   regmux_ddrc_t_rrd;
wire  [T_RP_WIDTH-1:0]   regmux_ddrc_t_rp;
// DRAMTMG5
wire  [T_CKSRX_WIDTH-1:0]   regmux_ddrc_t_cksrx;
wire  [T_CKSRE_WIDTH-1:0]   regmux_ddrc_t_cksre;
wire  [T_CKESR_WIDTH-1:0]   regmux_ddrc_t_ckesr;
wire  [T_CKE_WIDTH-1:0]   regmux_ddrc_t_cke;
// DRAMTMG6
wire  [T_CKCSX_WIDTH-1:0]   regmux_ddrc_t_ckcsx;
// DRAMTMG8
wire  [T_CCD_S_WIDTH-1:0]   regmux_ddrc_t_ccd_s;
wire  [T_RRD_S_WIDTH-1:0]   regmux_ddrc_t_rrd_s;
wire  [WR2RD_S_WIDTH-1:0]   regmux_ddrc_wr2rd_s;
wire  [T_CMDCKE_WIDTH-1:0]   regmux_ddrc_t_cmdcke;
// DRAMTMG13
wire  [ODTLOFF_WIDTH-1:0]   regmux_ddrc_odtloff;
wire  [T_CCD_MW_WIDTH-1:0]   regmux_ddrc_t_ccd_mw;
wire  [T_PPD_WIDTH-1:0]   regmux_ddrc_t_ppd;
// DRAMTMG14
wire  [T_XSR_WIDTH-1:0]  regmux_ddrc_t_xsr;
wire  [T_OSCO_WIDTH-1:0] regmux_ddrc_t_osco;
// DRAMTMG17
wire  [T_VRCG_ENABLE_WIDTH-1:0]   regmux_ddrc_t_vrcg_enable;
wire  [T_VRCG_DISABLE_WIDTH-1:0]   regmux_ddrc_t_vrcg_disable;
wire  [T_ZQ_LONG_NOP_WIDTH-1:0]  regmux_ddrc_t_zq_long_nop;
wire  [T_ZQ_SHORT_NOP_WIDTH-1:0]   regmux_ddrc_t_zq_short_nop;
wire  [T_ZQ_RESET_NOP_WIDTH-1:0] regmux_ddrc_t_zq_reset_nop;

   dwc_ddrctl_reg_mux
   

  U_reg_mux (

          /////////////////////
          // Control signals //
          /////////////////////

            .reg_regmux_target_frequency                (reg_ddrc_target_frequency),
            .regmux_ddrc_target_frequency               (regmux_ddrc_target_frequency),
            .hwffc_target_freq_en                       (hwffc_target_freq_en),
            .hwffc_target_freq                          (hwffc_target_freq),
            .hwffc_target_freq_init                     (hwffc_target_freq_init),
            .regmux_ddrc_hwffc_target_frequency              (regmux_ddrc_hwffc_target_frequency),

          /////////////////////
          // Freq0 registers //
          /////////////////////

            .reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0),
            .reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0),
            .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0  (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0     (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0(reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0),
            .reg_ddrc_ppt2_en_freq0                          (reg_ddrc_ppt2_en_freq0),
            .reg_ddrc_ppt2_override_freq0                    (reg_ddrc_ppt2_override_freq0),
            .reg_ddrc_ctrlupd_after_dqsosc_freq0             (reg_ddrc_ctrlupd_after_dqsosc_freq0),

            .reg_ddrc_frequency_ratio_freq0             (reg_ddrc_frequency_ratio_freq0),

            .reg_ddrc_refresh_timer0_start_value_x32_freq0 (reg_ddrc_refresh_timer0_start_value_x32_freq0),
            .reg_ddrc_refresh_timer1_start_value_x32_freq0 (reg_ddrc_refresh_timer1_start_value_x32_freq0),

            .reg_ddrc_derated_t_rcd_freq0               (reg_ddrc_derated_t_rcd_freq0),
            .reg_ddrc_derated_t_ras_min_freq0           (reg_ddrc_derated_t_ras_min_freq0),
            .reg_ddrc_derated_t_rp_freq0                (reg_ddrc_derated_t_rp_freq0),
            .reg_ddrc_derated_t_rrd_freq0               (reg_ddrc_derated_t_rrd_freq0),
            .reg_ddrc_derated_t_rc_freq0                (reg_ddrc_derated_t_rc_freq0),
            .reg_ddrc_mr4_read_interval_freq0           (reg_ddrc_mr4_read_interval_freq0),

            .reg_ddrc_derated_t_rcd_write_freq0         (reg_ddrc_derated_t_rcd_write_freq0),

            .reg_ddrc_powerdown_to_x32_freq0            (reg_ddrc_powerdown_to_x32_freq0),
            .reg_ddrc_selfref_to_x32_freq0              (reg_ddrc_selfref_to_x32_freq0),

            .reg_ddrc_hw_lp_idle_x32_freq0              (reg_ddrc_hw_lp_idle_x32_freq0),
            .reg_ddrc_refresh_margin_freq0              (reg_ddrc_refresh_margin_freq0),
            .reg_ddrc_refresh_to_x1_x32_freq0           (reg_ddrc_refresh_to_x1_x32_freq0),
            .reg_ddrc_refresh_to_ab_x32_freq0           (reg_ddrc_refresh_to_ab_x32_freq0),
            .reg_ddrc_refresh_to_x1_sel_freq0           (reg_ddrc_refresh_to_x1_sel_freq0),
            .reg_ddrc_t_refi_x1_sel_freq0               (reg_ddrc_t_refi_x1_sel_freq0),
            .reg_ddrc_t_refi_x32_freq0                  (reg_ddrc_t_refi_x1_x32_freq0),
            .reg_ddrc_t_rfc_min_freq0                   (reg_ddrc_t_rfc_min_freq0),
            .reg_ddrc_t_rfc_min_ab_freq0                (reg_ddrc_t_rfc_min_ab_freq0),
            .reg_ddrc_t_pbr2pbr_freq0                   (reg_ddrc_t_pbr2pbr_freq0),
            .reg_ddrc_t_pbr2act_freq0                   (reg_ddrc_t_pbr2act_freq0),
            .reg_ddrc_t_rfmpb_freq0                     (reg_ddrc_t_rfmpb_freq0),
            .reg_ddrc_t_pgm_x1_x1024_freq0              (reg_ddrc_t_pgm_x1_x1024_freq0),
            .reg_ddrc_t_pgm_x1_sel_freq0                (reg_ddrc_t_pgm_x1_sel_freq0),
            .reg_ddrc_t_pgmpst_x32_freq0                (reg_ddrc_t_pgmpst_x32_freq0),
            .reg_ddrc_t_pgm_exit_freq0                  (reg_ddrc_t_pgm_exit_freq0),

            .reg_ddrc_mr_freq0                          (reg_ddrc_mr_freq0),
            .reg_ddrc_emr_freq0                         (reg_ddrc_emr_freq0),
            .reg_ddrc_emr2_freq0                        (reg_ddrc_emr2_freq0),
            .reg_ddrc_emr3_freq0                        (reg_ddrc_emr3_freq0),
            .reg_ddrc_mr4_freq0                         (reg_ddrc_mr4_freq0),
            .reg_ddrc_mr5_freq0                         (reg_ddrc_mr5_freq0),
            .reg_ddrc_mr6_freq0                         (reg_ddrc_mr6_freq0),
            .reg_ddrc_mr22_freq0                        (reg_ddrc_mr22_freq0),
            .reg_ddrc_diff_rank_rd_gap_freq0            (reg_ddrc_diff_rank_rd_gap_freq0),
            .reg_ddrc_diff_rank_wr_gap_freq0            (reg_ddrc_diff_rank_wr_gap_freq0),
            .reg_ddrc_rd2wr_dr_freq0                    (reg_ddrc_rd2wr_dr_freq0),
            .reg_ddrc_wr2rd_dr_freq0                    (reg_ddrc_wr2rd_dr_freq0),
            .reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0    (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0),
            .reg_ddrc_wr2pre_freq0                      (reg_ddrc_wr2pre_freq0),
            .reg_ddrc_wra2pre_freq0                     (reg_ddrc_wra2pre_freq0),
            .reg_ddrc_t_faw_freq0                       (reg_ddrc_t_faw_freq0),
            .reg_ddrc_t_ras_max_freq0                   (reg_ddrc_t_ras_max_freq0),
            .reg_ddrc_t_ras_min_freq0                   (reg_ddrc_t_ras_min_freq0),
            .reg_ddrc_t_rcd_write_freq0                 (reg_ddrc_t_rcd_write_freq0),
            .reg_ddrc_t_xp_freq0                        (reg_ddrc_t_xp_freq0),
            .reg_ddrc_rd2pre_freq0                      (reg_ddrc_rd2pre_freq0),
            .reg_ddrc_rda2pre_freq0                     (reg_ddrc_rda2pre_freq0),
            .reg_ddrc_t_rc_freq0                        (reg_ddrc_t_rc_freq0),
            .reg_ddrc_write_latency_freq0               (reg_ddrc_write_latency_freq0),
            .reg_ddrc_read_latency_freq0                (reg_ddrc_read_latency_freq0),
            .reg_ddrc_rd2wr_freq0                       (reg_ddrc_rd2wr_freq0),
            .reg_ddrc_wr2rd_freq0                       (reg_ddrc_wr2rd_freq0),
            .reg_ddrc_wr2mr_freq0                       (reg_ddrc_wr2mr_freq0),
            .reg_ddrc_t_mr_freq0                        (reg_ddrc_t_mr_freq0),
            .reg_ddrc_rd2mr_freq0                       (reg_ddrc_rd2mr_freq0),
            .reg_ddrc_t_rcd_freq0                       (reg_ddrc_t_rcd_freq0),
            .reg_ddrc_t_ccd_freq0                       (reg_ddrc_t_ccd_freq0),
            .reg_ddrc_t_rrd_freq0                       (reg_ddrc_t_rrd_freq0),
            .reg_ddrc_t_rp_freq0                        (reg_ddrc_t_rp_freq0),
            .reg_ddrc_t_cksrx_freq0                     (reg_ddrc_t_cksrx_freq0),
            .reg_ddrc_t_cksre_freq0                     (reg_ddrc_t_cksre_freq0),
            .reg_ddrc_t_ckesr_freq0                     (reg_ddrc_t_ckesr_freq0),
            .reg_ddrc_t_cke_freq0                       (reg_ddrc_t_cke_freq0),
            .reg_ddrc_t_ckcsx_freq0                     (reg_ddrc_t_ckcsx_freq0),
            .reg_ddrc_t_ccd_s_freq0                     (reg_ddrc_t_ccd_s_freq0),
            .reg_ddrc_t_rrd_s_freq0                     (reg_ddrc_t_rrd_s_freq0),
            .reg_ddrc_wr2rd_s_freq0                     (reg_ddrc_wr2rd_s_freq0),
            .reg_ddrc_t_cmdcke_freq0                    (reg_ddrc_t_cmdcke_freq0),
            .reg_ddrc_t_pdn_freq0                       (reg_ddrc_t_pdn_freq0),
            .reg_ddrc_t_xsr_dsm_x1024_freq0             (reg_ddrc_t_xsr_dsm_x1024_freq0),
            .reg_ddrc_t_csh_freq0                       (reg_ddrc_t_csh_freq0),
            .reg_ddrc_odtloff_freq0                     (reg_ddrc_odtloff_freq0),
            .reg_ddrc_t_ccd_mw_freq0                    (reg_ddrc_t_ccd_mw_freq0),
            .reg_ddrc_t_ppd_freq0                       (reg_ddrc_t_ppd_freq0),
            .reg_ddrc_t_xsr_freq0                       (reg_ddrc_t_xsr_freq0),
            .reg_ddrc_t_osco_freq0                      (reg_ddrc_t_osco_freq0),
            .reg_ddrc_dqsosc_enable_freq0               (reg_ddrc_dqsosc_enable_freq0),
            .reg_ddrc_dqsosc_interval_unit_freq0        (reg_ddrc_dqsosc_interval_unit_freq0),
            .reg_ddrc_dqsosc_interval_freq0             (reg_ddrc_dqsosc_interval_freq0),
            .reg_ddrc_t_vrcg_enable_freq0               (reg_ddrc_t_vrcg_enable_freq0),
            .reg_ddrc_t_vrcg_disable_freq0              (reg_ddrc_t_vrcg_disable_freq0),
            .reg_ddrc_t_zq_stop_freq0                   (reg_ddrc_t_zq_stop_freq0),
            .reg_ddrc_dvfsq_enable_freq0                (reg_ddrc_dvfsq_enable_freq0),
            .reg_ddrc_t_zq_long_nop_freq0               (reg_ddrc_t_zq_long_nop_freq0),
            .reg_ddrc_t_zq_short_nop_freq0              (reg_ddrc_t_zq_short_nop_freq0),

            .reg_ddrc_t_zq_reset_nop_freq0              (reg_ddrc_t_zq_reset_nop_freq0),
            .reg_ddrc_t_zq_short_interval_x1024_freq0   (reg_ddrc_t_zq_short_interval_x1024_freq0),
            .reg_ddrc_bank_org_freq0                    (reg_ddrc_bank_org_freq0),
            .reg_ddrc_rd2wr_s_freq0                     (reg_ddrc_rd2wr_s_freq0),
            .reg_ddrc_mrr2rd_freq0                      (reg_ddrc_mrr2rd_freq0),
            .reg_ddrc_mrr2wr_freq0                      (reg_ddrc_mrr2wr_freq0),
            .reg_ddrc_mrr2mrw_freq0                     (reg_ddrc_mrr2mrw_freq0),
            .reg_ddrc_ws_off2ws_fs_freq0                (reg_ddrc_ws_off2ws_fs_freq0),
            .reg_ddrc_t_wcksus_freq0                    (reg_ddrc_t_wcksus_freq0),
            .reg_ddrc_ws_fs2wck_sus_freq0               (reg_ddrc_ws_fs2wck_sus_freq0),
            .reg_ddrc_max_rd_sync_freq0                 (reg_ddrc_max_rd_sync_freq0),
            .reg_ddrc_max_wr_sync_freq0                 (reg_ddrc_max_wr_sync_freq0),
            .reg_ddrc_dfi_twck_delay_freq0              (reg_ddrc_dfi_twck_delay_freq0),
            .reg_ddrc_dfi_twck_en_rd_freq0              (reg_ddrc_dfi_twck_en_rd_freq0),
            .reg_ddrc_dfi_twck_en_wr_freq0              (reg_ddrc_dfi_twck_en_wr_freq0),
            .reg_ddrc_dfi_twck_en_fs_freq0              (reg_ddrc_dfi_twck_en_fs_freq0),
            .reg_ddrc_dfi_twck_dis_freq0                (reg_ddrc_dfi_twck_dis_freq0),
            .reg_ddrc_dfi_twck_fast_toggle_freq0        (reg_ddrc_dfi_twck_fast_toggle_freq0),
            .reg_ddrc_dfi_twck_toggle_freq0             (reg_ddrc_dfi_twck_toggle_freq0),
            .reg_ddrc_dfi_twck_toggle_cs_freq0          (reg_ddrc_dfi_twck_toggle_cs_freq0),
            .reg_ddrc_dfi_twck_toggle_post_freq0        (reg_ddrc_dfi_twck_toggle_post_freq0),
            .reg_ddrc_dfi_twck_toggle_post_rd_en_freq0  (reg_ddrc_dfi_twck_toggle_post_rd_en_freq0),
            .reg_ddrc_dfi_twck_toggle_post_rd_freq0     (reg_ddrc_dfi_twck_toggle_post_rd_freq0),
            .reg_ddrc_dfi_t_ctrl_delay_freq0            (reg_ddrc_dfi_t_ctrl_delay_freq0),
            .reg_ddrc_dfi_t_rddata_en_freq0             (reg_ddrc_dfi_t_rddata_en_freq0),
            .reg_ddrc_dfi_tphy_wrdata_freq0             (reg_ddrc_dfi_tphy_wrdata_freq0),
            .reg_ddrc_dfi_tphy_wrlat_freq0              (reg_ddrc_dfi_tphy_wrlat_freq0),
            .reg_ddrc_dfi_t_wrdata_delay_freq0          (reg_ddrc_dfi_t_wrdata_delay_freq0),
            .reg_ddrc_dfi_t_dram_clk_disable_freq0      (reg_ddrc_dfi_t_dram_clk_disable_freq0),
            .reg_ddrc_dfi_t_dram_clk_enable_freq0       (reg_ddrc_dfi_t_dram_clk_enable_freq0),
            .reg_ddrc_dfi_tphy_rdcslat_freq0            (reg_ddrc_dfi_tphy_rdcslat_freq0),
            .reg_ddrc_dfi_tphy_wrcslat_freq0            (reg_ddrc_dfi_tphy_wrcslat_freq0),

            .reg_ddrc_hpr_max_starve_freq0              (reg_ddrc_hpr_max_starve_freq0),
            .reg_ddrc_hpr_xact_run_length_freq0         (reg_ddrc_hpr_xact_run_length_freq0),
            .reg_ddrc_lpr_max_starve_freq0              (reg_ddrc_lpr_max_starve_freq0),
            .reg_ddrc_lpr_xact_run_length_freq0         (reg_ddrc_lpr_xact_run_length_freq0),
            .reg_ddrc_w_max_starve_freq0                (reg_ddrc_w_max_starve_freq0),
            .reg_ddrc_w_xact_run_length_freq0           (reg_ddrc_w_xact_run_length_freq0),



            .reg_ddrc_rdwr_idle_gap_freq0               (reg_ddrc_rdwr_idle_gap_freq0),
            .reg_ddrc_pageclose_timer_freq0             (reg_ddrc_pageclose_timer_freq0),


            .reg_ddrc_rd_link_ecc_enable_freq0 (reg_ddrc_rd_link_ecc_enable_freq0),
            .reg_ddrc_wr_link_ecc_enable_freq0 (reg_ddrc_wr_link_ecc_enable_freq0),

          /////////////////////
          // Freq1 registers //
          /////////////////////

            .reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1),
            .reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1),
            .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1  (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1     (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1(reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1),
            .reg_ddrc_ppt2_en_freq1                          (reg_ddrc_ppt2_en_freq1),
            .reg_ddrc_ppt2_override_freq1                    (reg_ddrc_ppt2_override_freq1),
            .reg_ddrc_ctrlupd_after_dqsosc_freq1             (reg_ddrc_ctrlupd_after_dqsosc_freq1),

            .reg_ddrc_frequency_ratio_freq1             (reg_ddrc_frequency_ratio_freq1),

            .reg_ddrc_refresh_timer0_start_value_x32_freq1 (reg_ddrc_refresh_timer0_start_value_x32_freq1),
            .reg_ddrc_refresh_timer1_start_value_x32_freq1 (reg_ddrc_refresh_timer1_start_value_x32_freq1),

            .reg_ddrc_derated_t_rcd_freq1               (reg_ddrc_derated_t_rcd_freq1),
            .reg_ddrc_derated_t_ras_min_freq1           (reg_ddrc_derated_t_ras_min_freq1),
            .reg_ddrc_derated_t_rp_freq1                (reg_ddrc_derated_t_rp_freq1),
            .reg_ddrc_derated_t_rrd_freq1               (reg_ddrc_derated_t_rrd_freq1),
            .reg_ddrc_derated_t_rc_freq1                (reg_ddrc_derated_t_rc_freq1),
            .reg_ddrc_mr4_read_interval_freq1           (reg_ddrc_mr4_read_interval_freq1),

            .reg_ddrc_derated_t_rcd_write_freq1         (reg_ddrc_derated_t_rcd_write_freq1),

            .reg_ddrc_powerdown_to_x32_freq1            (reg_ddrc_powerdown_to_x32_freq1),
            .reg_ddrc_selfref_to_x32_freq1              (reg_ddrc_selfref_to_x32_freq1),

            .reg_ddrc_hw_lp_idle_x32_freq1              (reg_ddrc_hw_lp_idle_x32_freq1),
            .reg_ddrc_refresh_margin_freq1              (reg_ddrc_refresh_margin_freq1),
            .reg_ddrc_refresh_to_x1_x32_freq1           (reg_ddrc_refresh_to_x1_x32_freq1),
            .reg_ddrc_refresh_to_ab_x32_freq1           (reg_ddrc_refresh_to_ab_x32_freq1),
            .reg_ddrc_refresh_to_x1_sel_freq1           (reg_ddrc_refresh_to_x1_sel_freq1),
            .reg_ddrc_t_refi_x1_sel_freq1               (reg_ddrc_t_refi_x1_sel_freq1),
            .reg_ddrc_t_refi_x32_freq1                  (reg_ddrc_t_refi_x1_x32_freq1),
            .reg_ddrc_t_rfc_min_freq1                   (reg_ddrc_t_rfc_min_freq1),
            .reg_ddrc_t_rfc_min_ab_freq1                (reg_ddrc_t_rfc_min_ab_freq1),
            .reg_ddrc_t_pbr2pbr_freq1                   (reg_ddrc_t_pbr2pbr_freq1),
            .reg_ddrc_t_pbr2act_freq1                   (reg_ddrc_t_pbr2act_freq1),
            .reg_ddrc_t_rfmpb_freq1                     (reg_ddrc_t_rfmpb_freq1),
            .reg_ddrc_t_pgm_x1_x1024_freq1              (reg_ddrc_t_pgm_x1_x1024_freq1),
            .reg_ddrc_t_pgm_x1_sel_freq1                (reg_ddrc_t_pgm_x1_sel_freq1),
            .reg_ddrc_t_pgmpst_x32_freq1                (reg_ddrc_t_pgmpst_x32_freq1),
            .reg_ddrc_t_pgm_exit_freq1                  (reg_ddrc_t_pgm_exit_freq1),

            .reg_ddrc_mr_freq1                          (reg_ddrc_mr_freq1),
            .reg_ddrc_emr_freq1                         (reg_ddrc_emr_freq1),
            .reg_ddrc_emr2_freq1                        (reg_ddrc_emr2_freq1),
            .reg_ddrc_emr3_freq1                        (reg_ddrc_emr3_freq1),
            .reg_ddrc_mr4_freq1                         (reg_ddrc_mr4_freq1),
            .reg_ddrc_mr5_freq1                         (reg_ddrc_mr5_freq1),
            .reg_ddrc_mr6_freq1                         (reg_ddrc_mr6_freq1),
            .reg_ddrc_mr22_freq1                        (reg_ddrc_mr22_freq1),
            .reg_ddrc_diff_rank_rd_gap_freq1            (reg_ddrc_diff_rank_rd_gap_freq1),
            .reg_ddrc_diff_rank_wr_gap_freq1            (reg_ddrc_diff_rank_wr_gap_freq1),
            .reg_ddrc_rd2wr_dr_freq1                    (reg_ddrc_rd2wr_dr_freq1),
            .reg_ddrc_wr2rd_dr_freq1                    (reg_ddrc_wr2rd_dr_freq1),
            .reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1    (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1),
            .reg_ddrc_wr2pre_freq1                      (reg_ddrc_wr2pre_freq1),
            .reg_ddrc_wra2pre_freq1                     (reg_ddrc_wra2pre_freq1),
            .reg_ddrc_t_faw_freq1                       (reg_ddrc_t_faw_freq1),
            .reg_ddrc_t_ras_max_freq1                   (reg_ddrc_t_ras_max_freq1),
            .reg_ddrc_t_ras_min_freq1                   (reg_ddrc_t_ras_min_freq1),
            .reg_ddrc_t_rcd_write_freq1                 (reg_ddrc_t_rcd_write_freq1),
            .reg_ddrc_t_xp_freq1                        (reg_ddrc_t_xp_freq1),
            .reg_ddrc_rd2pre_freq1                      (reg_ddrc_rd2pre_freq1),
            .reg_ddrc_rda2pre_freq1                     (reg_ddrc_rda2pre_freq1),
            .reg_ddrc_t_rc_freq1                        (reg_ddrc_t_rc_freq1),
            .reg_ddrc_write_latency_freq1               (reg_ddrc_write_latency_freq1),
            .reg_ddrc_read_latency_freq1                (reg_ddrc_read_latency_freq1),
            .reg_ddrc_rd2wr_freq1                       (reg_ddrc_rd2wr_freq1),
            .reg_ddrc_wr2rd_freq1                       (reg_ddrc_wr2rd_freq1),
            .reg_ddrc_wr2mr_freq1                       (reg_ddrc_wr2mr_freq1),
            .reg_ddrc_t_mr_freq1                        (reg_ddrc_t_mr_freq1),
            .reg_ddrc_rd2mr_freq1                       (reg_ddrc_rd2mr_freq1),
            .reg_ddrc_t_rcd_freq1                       (reg_ddrc_t_rcd_freq1),
            .reg_ddrc_t_ccd_freq1                       (reg_ddrc_t_ccd_freq1),
            .reg_ddrc_t_rrd_freq1                       (reg_ddrc_t_rrd_freq1),
            .reg_ddrc_t_rp_freq1                        (reg_ddrc_t_rp_freq1),
            .reg_ddrc_t_cksrx_freq1                     (reg_ddrc_t_cksrx_freq1),
            .reg_ddrc_t_cksre_freq1                     (reg_ddrc_t_cksre_freq1),
            .reg_ddrc_t_ckesr_freq1                     (reg_ddrc_t_ckesr_freq1),
            .reg_ddrc_t_cke_freq1                       (reg_ddrc_t_cke_freq1),
            .reg_ddrc_t_ckcsx_freq1                     (reg_ddrc_t_ckcsx_freq1),
            .reg_ddrc_t_ccd_s_freq1                     (reg_ddrc_t_ccd_s_freq1),
            .reg_ddrc_t_rrd_s_freq1                     (reg_ddrc_t_rrd_s_freq1),
            .reg_ddrc_wr2rd_s_freq1                     (reg_ddrc_wr2rd_s_freq1),
            .reg_ddrc_t_cmdcke_freq1                    (reg_ddrc_t_cmdcke_freq1),
            .reg_ddrc_t_pdn_freq1                       (reg_ddrc_t_pdn_freq1),
            .reg_ddrc_t_xsr_dsm_x1024_freq1             (reg_ddrc_t_xsr_dsm_x1024_freq1),
            .reg_ddrc_t_csh_freq1                       (reg_ddrc_t_csh_freq1),
            .reg_ddrc_odtloff_freq1                     (reg_ddrc_odtloff_freq1),
            .reg_ddrc_t_ccd_mw_freq1                    (reg_ddrc_t_ccd_mw_freq1),
            .reg_ddrc_t_ppd_freq1                       (reg_ddrc_t_ppd_freq1),
            .reg_ddrc_t_xsr_freq1                       (reg_ddrc_t_xsr_freq1),
            .reg_ddrc_t_osco_freq1                      (reg_ddrc_t_osco_freq1),
            .reg_ddrc_dqsosc_enable_freq1               (reg_ddrc_dqsosc_enable_freq1),
            .reg_ddrc_dqsosc_interval_unit_freq1        (reg_ddrc_dqsosc_interval_unit_freq1),
            .reg_ddrc_dqsosc_interval_freq1             (reg_ddrc_dqsosc_interval_freq1),
            .reg_ddrc_t_vrcg_enable_freq1               (reg_ddrc_t_vrcg_enable_freq1),
            .reg_ddrc_t_vrcg_disable_freq1              (reg_ddrc_t_vrcg_disable_freq1),
            .reg_ddrc_t_zq_stop_freq1                   (reg_ddrc_t_zq_stop_freq1),
            .reg_ddrc_dvfsq_enable_freq1                (reg_ddrc_dvfsq_enable_freq1),
            .reg_ddrc_t_zq_long_nop_freq1               (reg_ddrc_t_zq_long_nop_freq1),
            .reg_ddrc_t_zq_short_nop_freq1              (reg_ddrc_t_zq_short_nop_freq1),

            .reg_ddrc_t_zq_reset_nop_freq1              (reg_ddrc_t_zq_reset_nop_freq1),
            .reg_ddrc_t_zq_short_interval_x1024_freq1   (reg_ddrc_t_zq_short_interval_x1024_freq1),
            .reg_ddrc_bank_org_freq1                    (reg_ddrc_bank_org_freq1),
            .reg_ddrc_rd2wr_s_freq1                     (reg_ddrc_rd2wr_s_freq1),
            .reg_ddrc_mrr2rd_freq1                      (reg_ddrc_mrr2rd_freq1),
            .reg_ddrc_mrr2wr_freq1                      (reg_ddrc_mrr2wr_freq1),
            .reg_ddrc_mrr2mrw_freq1                     (reg_ddrc_mrr2mrw_freq1),
            .reg_ddrc_ws_off2ws_fs_freq1                (reg_ddrc_ws_off2ws_fs_freq1),
            .reg_ddrc_t_wcksus_freq1                    (reg_ddrc_t_wcksus_freq1),
            .reg_ddrc_ws_fs2wck_sus_freq1               (reg_ddrc_ws_fs2wck_sus_freq1),
            .reg_ddrc_max_rd_sync_freq1                 (reg_ddrc_max_rd_sync_freq1),
            .reg_ddrc_max_wr_sync_freq1                 (reg_ddrc_max_wr_sync_freq1),
            .reg_ddrc_dfi_twck_delay_freq1              (reg_ddrc_dfi_twck_delay_freq1),
            .reg_ddrc_dfi_twck_en_rd_freq1              (reg_ddrc_dfi_twck_en_rd_freq1),
            .reg_ddrc_dfi_twck_en_wr_freq1              (reg_ddrc_dfi_twck_en_wr_freq1),
            .reg_ddrc_dfi_twck_en_fs_freq1              (reg_ddrc_dfi_twck_en_fs_freq1),
            .reg_ddrc_dfi_twck_dis_freq1                (reg_ddrc_dfi_twck_dis_freq1),
            .reg_ddrc_dfi_twck_fast_toggle_freq1        (reg_ddrc_dfi_twck_fast_toggle_freq1),
            .reg_ddrc_dfi_twck_toggle_freq1             (reg_ddrc_dfi_twck_toggle_freq1),
            .reg_ddrc_dfi_twck_toggle_cs_freq1          (reg_ddrc_dfi_twck_toggle_cs_freq1),
            .reg_ddrc_dfi_twck_toggle_post_freq1        (reg_ddrc_dfi_twck_toggle_post_freq1),
            .reg_ddrc_dfi_twck_toggle_post_rd_en_freq1  (reg_ddrc_dfi_twck_toggle_post_rd_en_freq1),
            .reg_ddrc_dfi_twck_toggle_post_rd_freq1     (reg_ddrc_dfi_twck_toggle_post_rd_freq1),
            .reg_ddrc_dfi_t_ctrl_delay_freq1            (reg_ddrc_dfi_t_ctrl_delay_freq1),
            .reg_ddrc_dfi_t_rddata_en_freq1             (reg_ddrc_dfi_t_rddata_en_freq1),
            .reg_ddrc_dfi_tphy_wrdata_freq1             (reg_ddrc_dfi_tphy_wrdata_freq1),
            .reg_ddrc_dfi_tphy_wrlat_freq1              (reg_ddrc_dfi_tphy_wrlat_freq1),
            .reg_ddrc_dfi_t_wrdata_delay_freq1          (reg_ddrc_dfi_t_wrdata_delay_freq1),
            .reg_ddrc_dfi_t_dram_clk_disable_freq1      (reg_ddrc_dfi_t_dram_clk_disable_freq1),
            .reg_ddrc_dfi_t_dram_clk_enable_freq1       (reg_ddrc_dfi_t_dram_clk_enable_freq1),
            .reg_ddrc_dfi_tphy_rdcslat_freq1            (reg_ddrc_dfi_tphy_rdcslat_freq1),
            .reg_ddrc_dfi_tphy_wrcslat_freq1            (reg_ddrc_dfi_tphy_wrcslat_freq1),

            .reg_ddrc_hpr_max_starve_freq1              (reg_ddrc_hpr_max_starve_freq1),
            .reg_ddrc_hpr_xact_run_length_freq1         (reg_ddrc_hpr_xact_run_length_freq1),
            .reg_ddrc_lpr_max_starve_freq1              (reg_ddrc_lpr_max_starve_freq1),
            .reg_ddrc_lpr_xact_run_length_freq1         (reg_ddrc_lpr_xact_run_length_freq1),
            .reg_ddrc_w_max_starve_freq1                (reg_ddrc_w_max_starve_freq1),
            .reg_ddrc_w_xact_run_length_freq1           (reg_ddrc_w_xact_run_length_freq1),



            .reg_ddrc_rdwr_idle_gap_freq1               (reg_ddrc_rdwr_idle_gap_freq1),
            .reg_ddrc_pageclose_timer_freq1             (reg_ddrc_pageclose_timer_freq1),


            .reg_ddrc_rd_link_ecc_enable_freq1 (reg_ddrc_rd_link_ecc_enable_freq1),
            .reg_ddrc_wr_link_ecc_enable_freq1 (reg_ddrc_wr_link_ecc_enable_freq1),

          /////////////////////
          // Freq2 registers //
          /////////////////////

            .reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2),
            .reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2),
            .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2  (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2     (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2(reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2),
            .reg_ddrc_ppt2_en_freq2                          (reg_ddrc_ppt2_en_freq2),
            .reg_ddrc_ppt2_override_freq2                    (reg_ddrc_ppt2_override_freq2),
            .reg_ddrc_ctrlupd_after_dqsosc_freq2             (reg_ddrc_ctrlupd_after_dqsosc_freq2),

            .reg_ddrc_frequency_ratio_freq2             (reg_ddrc_frequency_ratio_freq2),

            .reg_ddrc_refresh_timer0_start_value_x32_freq2 (reg_ddrc_refresh_timer0_start_value_x32_freq2),
            .reg_ddrc_refresh_timer1_start_value_x32_freq2 (reg_ddrc_refresh_timer1_start_value_x32_freq2),

            .reg_ddrc_derated_t_rcd_freq2               (reg_ddrc_derated_t_rcd_freq2),
            .reg_ddrc_derated_t_ras_min_freq2           (reg_ddrc_derated_t_ras_min_freq2),
            .reg_ddrc_derated_t_rp_freq2                (reg_ddrc_derated_t_rp_freq2),
            .reg_ddrc_derated_t_rrd_freq2               (reg_ddrc_derated_t_rrd_freq2),
            .reg_ddrc_derated_t_rc_freq2                (reg_ddrc_derated_t_rc_freq2),
            .reg_ddrc_mr4_read_interval_freq2           (reg_ddrc_mr4_read_interval_freq2),

            .reg_ddrc_derated_t_rcd_write_freq2         (reg_ddrc_derated_t_rcd_write_freq2),

            .reg_ddrc_powerdown_to_x32_freq2            (reg_ddrc_powerdown_to_x32_freq2),
            .reg_ddrc_selfref_to_x32_freq2              (reg_ddrc_selfref_to_x32_freq2),

            .reg_ddrc_hw_lp_idle_x32_freq2              (reg_ddrc_hw_lp_idle_x32_freq2),
            .reg_ddrc_refresh_margin_freq2              (reg_ddrc_refresh_margin_freq2),
            .reg_ddrc_refresh_to_x1_x32_freq2           (reg_ddrc_refresh_to_x1_x32_freq2),
            .reg_ddrc_refresh_to_ab_x32_freq2           (reg_ddrc_refresh_to_ab_x32_freq2),
            .reg_ddrc_refresh_to_x1_sel_freq2           (reg_ddrc_refresh_to_x1_sel_freq2),
            .reg_ddrc_t_refi_x1_sel_freq2               (reg_ddrc_t_refi_x1_sel_freq2),
            .reg_ddrc_t_refi_x32_freq2                  (reg_ddrc_t_refi_x1_x32_freq2),
            .reg_ddrc_t_rfc_min_freq2                   (reg_ddrc_t_rfc_min_freq2),
            .reg_ddrc_t_rfc_min_ab_freq2                (reg_ddrc_t_rfc_min_ab_freq2),
            .reg_ddrc_t_pbr2pbr_freq2                   (reg_ddrc_t_pbr2pbr_freq2),
            .reg_ddrc_t_pbr2act_freq2                   (reg_ddrc_t_pbr2act_freq2),
            .reg_ddrc_t_rfmpb_freq2                     (reg_ddrc_t_rfmpb_freq2),
            .reg_ddrc_t_pgm_x1_x1024_freq2              (reg_ddrc_t_pgm_x1_x1024_freq2),
            .reg_ddrc_t_pgm_x1_sel_freq2                (reg_ddrc_t_pgm_x1_sel_freq2),
            .reg_ddrc_t_pgmpst_x32_freq2                (reg_ddrc_t_pgmpst_x32_freq2),
            .reg_ddrc_t_pgm_exit_freq2                  (reg_ddrc_t_pgm_exit_freq2),

            .reg_ddrc_mr_freq2                          (reg_ddrc_mr_freq2),
            .reg_ddrc_emr_freq2                         (reg_ddrc_emr_freq2),
            .reg_ddrc_emr2_freq2                        (reg_ddrc_emr2_freq2),
            .reg_ddrc_emr3_freq2                        (reg_ddrc_emr3_freq2),
            .reg_ddrc_mr4_freq2                         (reg_ddrc_mr4_freq2),
            .reg_ddrc_mr5_freq2                         (reg_ddrc_mr5_freq2),
            .reg_ddrc_mr6_freq2                         (reg_ddrc_mr6_freq2),
            .reg_ddrc_mr22_freq2                        (reg_ddrc_mr22_freq2),
            .reg_ddrc_diff_rank_rd_gap_freq2            (reg_ddrc_diff_rank_rd_gap_freq2),
            .reg_ddrc_diff_rank_wr_gap_freq2            (reg_ddrc_diff_rank_wr_gap_freq2),
            .reg_ddrc_rd2wr_dr_freq2                    (reg_ddrc_rd2wr_dr_freq2),
            .reg_ddrc_wr2rd_dr_freq2                    (reg_ddrc_wr2rd_dr_freq2),
            .reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2    (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2),
            .reg_ddrc_wr2pre_freq2                      (reg_ddrc_wr2pre_freq2),
            .reg_ddrc_wra2pre_freq2                     (reg_ddrc_wra2pre_freq2),
            .reg_ddrc_t_faw_freq2                       (reg_ddrc_t_faw_freq2),
            .reg_ddrc_t_ras_max_freq2                   (reg_ddrc_t_ras_max_freq2),
            .reg_ddrc_t_ras_min_freq2                   (reg_ddrc_t_ras_min_freq2),
            .reg_ddrc_t_rcd_write_freq2                 (reg_ddrc_t_rcd_write_freq2),
            .reg_ddrc_t_xp_freq2                        (reg_ddrc_t_xp_freq2),
            .reg_ddrc_rd2pre_freq2                      (reg_ddrc_rd2pre_freq2),
            .reg_ddrc_rda2pre_freq2                     (reg_ddrc_rda2pre_freq2),
            .reg_ddrc_t_rc_freq2                        (reg_ddrc_t_rc_freq2),
            .reg_ddrc_write_latency_freq2               (reg_ddrc_write_latency_freq2),
            .reg_ddrc_read_latency_freq2                (reg_ddrc_read_latency_freq2),
            .reg_ddrc_rd2wr_freq2                       (reg_ddrc_rd2wr_freq2),
            .reg_ddrc_wr2rd_freq2                       (reg_ddrc_wr2rd_freq2),
            .reg_ddrc_wr2mr_freq2                       (reg_ddrc_wr2mr_freq2),
            .reg_ddrc_t_mr_freq2                        (reg_ddrc_t_mr_freq2),
            .reg_ddrc_rd2mr_freq2                       (reg_ddrc_rd2mr_freq2),
            .reg_ddrc_t_rcd_freq2                       (reg_ddrc_t_rcd_freq2),
            .reg_ddrc_t_ccd_freq2                       (reg_ddrc_t_ccd_freq2),
            .reg_ddrc_t_rrd_freq2                       (reg_ddrc_t_rrd_freq2),
            .reg_ddrc_t_rp_freq2                        (reg_ddrc_t_rp_freq2),
            .reg_ddrc_t_cksrx_freq2                     (reg_ddrc_t_cksrx_freq2),
            .reg_ddrc_t_cksre_freq2                     (reg_ddrc_t_cksre_freq2),
            .reg_ddrc_t_ckesr_freq2                     (reg_ddrc_t_ckesr_freq2),
            .reg_ddrc_t_cke_freq2                       (reg_ddrc_t_cke_freq2),
            .reg_ddrc_t_ckcsx_freq2                     (reg_ddrc_t_ckcsx_freq2),
            .reg_ddrc_t_ccd_s_freq2                     (reg_ddrc_t_ccd_s_freq2),
            .reg_ddrc_t_rrd_s_freq2                     (reg_ddrc_t_rrd_s_freq2),
            .reg_ddrc_wr2rd_s_freq2                     (reg_ddrc_wr2rd_s_freq2),
            .reg_ddrc_t_cmdcke_freq2                    (reg_ddrc_t_cmdcke_freq2),
            .reg_ddrc_t_pdn_freq2                       (reg_ddrc_t_pdn_freq2),
            .reg_ddrc_t_xsr_dsm_x1024_freq2             (reg_ddrc_t_xsr_dsm_x1024_freq2),
            .reg_ddrc_t_csh_freq2                       (reg_ddrc_t_csh_freq2),
            .reg_ddrc_odtloff_freq2                     (reg_ddrc_odtloff_freq2),
            .reg_ddrc_t_ccd_mw_freq2                    (reg_ddrc_t_ccd_mw_freq2),
            .reg_ddrc_t_ppd_freq2                       (reg_ddrc_t_ppd_freq2),
            .reg_ddrc_t_xsr_freq2                       (reg_ddrc_t_xsr_freq2),
            .reg_ddrc_t_osco_freq2                      (reg_ddrc_t_osco_freq2),
            .reg_ddrc_dqsosc_enable_freq2               (reg_ddrc_dqsosc_enable_freq2),
            .reg_ddrc_dqsosc_interval_unit_freq2        (reg_ddrc_dqsosc_interval_unit_freq2),
            .reg_ddrc_dqsosc_interval_freq2             (reg_ddrc_dqsosc_interval_freq2),
            .reg_ddrc_t_vrcg_enable_freq2               (reg_ddrc_t_vrcg_enable_freq2),
            .reg_ddrc_t_vrcg_disable_freq2              (reg_ddrc_t_vrcg_disable_freq2),
            .reg_ddrc_t_zq_stop_freq2                   (reg_ddrc_t_zq_stop_freq2),
            .reg_ddrc_dvfsq_enable_freq2                (reg_ddrc_dvfsq_enable_freq2),
            .reg_ddrc_t_zq_long_nop_freq2               (reg_ddrc_t_zq_long_nop_freq2),
            .reg_ddrc_t_zq_short_nop_freq2              (reg_ddrc_t_zq_short_nop_freq2),

            .reg_ddrc_t_zq_reset_nop_freq2              (reg_ddrc_t_zq_reset_nop_freq2),
            .reg_ddrc_t_zq_short_interval_x1024_freq2   (reg_ddrc_t_zq_short_interval_x1024_freq2),
            .reg_ddrc_bank_org_freq2                    (reg_ddrc_bank_org_freq2),
            .reg_ddrc_rd2wr_s_freq2                     (reg_ddrc_rd2wr_s_freq2),
            .reg_ddrc_mrr2rd_freq2                      (reg_ddrc_mrr2rd_freq2),
            .reg_ddrc_mrr2wr_freq2                      (reg_ddrc_mrr2wr_freq2),
            .reg_ddrc_mrr2mrw_freq2                     (reg_ddrc_mrr2mrw_freq2),
            .reg_ddrc_ws_off2ws_fs_freq2                (reg_ddrc_ws_off2ws_fs_freq2),
            .reg_ddrc_t_wcksus_freq2                    (reg_ddrc_t_wcksus_freq2),
            .reg_ddrc_ws_fs2wck_sus_freq2               (reg_ddrc_ws_fs2wck_sus_freq2),
            .reg_ddrc_max_rd_sync_freq2                 (reg_ddrc_max_rd_sync_freq2),
            .reg_ddrc_max_wr_sync_freq2                 (reg_ddrc_max_wr_sync_freq2),
            .reg_ddrc_dfi_twck_delay_freq2              (reg_ddrc_dfi_twck_delay_freq2),
            .reg_ddrc_dfi_twck_en_rd_freq2              (reg_ddrc_dfi_twck_en_rd_freq2),
            .reg_ddrc_dfi_twck_en_wr_freq2              (reg_ddrc_dfi_twck_en_wr_freq2),
            .reg_ddrc_dfi_twck_en_fs_freq2              (reg_ddrc_dfi_twck_en_fs_freq2),
            .reg_ddrc_dfi_twck_dis_freq2                (reg_ddrc_dfi_twck_dis_freq2),
            .reg_ddrc_dfi_twck_fast_toggle_freq2        (reg_ddrc_dfi_twck_fast_toggle_freq2),
            .reg_ddrc_dfi_twck_toggle_freq2             (reg_ddrc_dfi_twck_toggle_freq2),
            .reg_ddrc_dfi_twck_toggle_cs_freq2          (reg_ddrc_dfi_twck_toggle_cs_freq2),
            .reg_ddrc_dfi_twck_toggle_post_freq2        (reg_ddrc_dfi_twck_toggle_post_freq2),
            .reg_ddrc_dfi_twck_toggle_post_rd_en_freq2  (reg_ddrc_dfi_twck_toggle_post_rd_en_freq2),
            .reg_ddrc_dfi_twck_toggle_post_rd_freq2     (reg_ddrc_dfi_twck_toggle_post_rd_freq2),
            .reg_ddrc_dfi_t_ctrl_delay_freq2            (reg_ddrc_dfi_t_ctrl_delay_freq2),
            .reg_ddrc_dfi_t_rddata_en_freq2             (reg_ddrc_dfi_t_rddata_en_freq2),
            .reg_ddrc_dfi_tphy_wrdata_freq2             (reg_ddrc_dfi_tphy_wrdata_freq2),
            .reg_ddrc_dfi_tphy_wrlat_freq2              (reg_ddrc_dfi_tphy_wrlat_freq2),
            .reg_ddrc_dfi_t_wrdata_delay_freq2          (reg_ddrc_dfi_t_wrdata_delay_freq2),
            .reg_ddrc_dfi_t_dram_clk_disable_freq2      (reg_ddrc_dfi_t_dram_clk_disable_freq2),
            .reg_ddrc_dfi_t_dram_clk_enable_freq2       (reg_ddrc_dfi_t_dram_clk_enable_freq2),
            .reg_ddrc_dfi_tphy_rdcslat_freq2            (reg_ddrc_dfi_tphy_rdcslat_freq2),
            .reg_ddrc_dfi_tphy_wrcslat_freq2            (reg_ddrc_dfi_tphy_wrcslat_freq2),

            .reg_ddrc_hpr_max_starve_freq2              (reg_ddrc_hpr_max_starve_freq2),
            .reg_ddrc_hpr_xact_run_length_freq2         (reg_ddrc_hpr_xact_run_length_freq2),
            .reg_ddrc_lpr_max_starve_freq2              (reg_ddrc_lpr_max_starve_freq2),
            .reg_ddrc_lpr_xact_run_length_freq2         (reg_ddrc_lpr_xact_run_length_freq2),
            .reg_ddrc_w_max_starve_freq2                (reg_ddrc_w_max_starve_freq2),
            .reg_ddrc_w_xact_run_length_freq2           (reg_ddrc_w_xact_run_length_freq2),



            .reg_ddrc_rdwr_idle_gap_freq2               (reg_ddrc_rdwr_idle_gap_freq2),
            .reg_ddrc_pageclose_timer_freq2             (reg_ddrc_pageclose_timer_freq2),


            .reg_ddrc_rd_link_ecc_enable_freq2 (reg_ddrc_rd_link_ecc_enable_freq2),
            .reg_ddrc_wr_link_ecc_enable_freq2 (reg_ddrc_wr_link_ecc_enable_freq2),

          /////////////////////
          // Freq3 registers //
          /////////////////////

            .reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3),
            .reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3),
            .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3  (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3     (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3),
            .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3(reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3),
            .reg_ddrc_ppt2_en_freq3                          (reg_ddrc_ppt2_en_freq3),
            .reg_ddrc_ppt2_override_freq3                    (reg_ddrc_ppt2_override_freq3),
            .reg_ddrc_ctrlupd_after_dqsosc_freq3             (reg_ddrc_ctrlupd_after_dqsosc_freq3),

            .reg_ddrc_frequency_ratio_freq3             (reg_ddrc_frequency_ratio_freq3),

            .reg_ddrc_refresh_timer0_start_value_x32_freq3 (reg_ddrc_refresh_timer0_start_value_x32_freq3),
            .reg_ddrc_refresh_timer1_start_value_x32_freq3 (reg_ddrc_refresh_timer1_start_value_x32_freq3),

            .reg_ddrc_derated_t_rcd_freq3               (reg_ddrc_derated_t_rcd_freq3),
            .reg_ddrc_derated_t_ras_min_freq3           (reg_ddrc_derated_t_ras_min_freq3),
            .reg_ddrc_derated_t_rp_freq3                (reg_ddrc_derated_t_rp_freq3),
            .reg_ddrc_derated_t_rrd_freq3               (reg_ddrc_derated_t_rrd_freq3),
            .reg_ddrc_derated_t_rc_freq3                (reg_ddrc_derated_t_rc_freq3),
            .reg_ddrc_mr4_read_interval_freq3           (reg_ddrc_mr4_read_interval_freq3),

            .reg_ddrc_derated_t_rcd_write_freq3         (reg_ddrc_derated_t_rcd_write_freq3),

            .reg_ddrc_powerdown_to_x32_freq3            (reg_ddrc_powerdown_to_x32_freq3),
            .reg_ddrc_selfref_to_x32_freq3              (reg_ddrc_selfref_to_x32_freq3),

            .reg_ddrc_hw_lp_idle_x32_freq3              (reg_ddrc_hw_lp_idle_x32_freq3),
            .reg_ddrc_refresh_margin_freq3              (reg_ddrc_refresh_margin_freq3),
            .reg_ddrc_refresh_to_x1_x32_freq3           (reg_ddrc_refresh_to_x1_x32_freq3),
            .reg_ddrc_refresh_to_ab_x32_freq3           (reg_ddrc_refresh_to_ab_x32_freq3),
            .reg_ddrc_refresh_to_x1_sel_freq3           (reg_ddrc_refresh_to_x1_sel_freq3),
            .reg_ddrc_t_refi_x1_sel_freq3               (reg_ddrc_t_refi_x1_sel_freq3),
            .reg_ddrc_t_refi_x32_freq3                  (reg_ddrc_t_refi_x1_x32_freq3),
            .reg_ddrc_t_rfc_min_freq3                   (reg_ddrc_t_rfc_min_freq3),
            .reg_ddrc_t_rfc_min_ab_freq3                (reg_ddrc_t_rfc_min_ab_freq3),
            .reg_ddrc_t_pbr2pbr_freq3                   (reg_ddrc_t_pbr2pbr_freq3),
            .reg_ddrc_t_pbr2act_freq3                   (reg_ddrc_t_pbr2act_freq3),
            .reg_ddrc_t_rfmpb_freq3                     (reg_ddrc_t_rfmpb_freq3),
            .reg_ddrc_t_pgm_x1_x1024_freq3              (reg_ddrc_t_pgm_x1_x1024_freq3),
            .reg_ddrc_t_pgm_x1_sel_freq3                (reg_ddrc_t_pgm_x1_sel_freq3),
            .reg_ddrc_t_pgmpst_x32_freq3                (reg_ddrc_t_pgmpst_x32_freq3),
            .reg_ddrc_t_pgm_exit_freq3                  (reg_ddrc_t_pgm_exit_freq3),

            .reg_ddrc_mr_freq3                          (reg_ddrc_mr_freq3),
            .reg_ddrc_emr_freq3                         (reg_ddrc_emr_freq3),
            .reg_ddrc_emr2_freq3                        (reg_ddrc_emr2_freq3),
            .reg_ddrc_emr3_freq3                        (reg_ddrc_emr3_freq3),
            .reg_ddrc_mr4_freq3                         (reg_ddrc_mr4_freq3),
            .reg_ddrc_mr5_freq3                         (reg_ddrc_mr5_freq3),
            .reg_ddrc_mr6_freq3                         (reg_ddrc_mr6_freq3),
            .reg_ddrc_mr22_freq3                        (reg_ddrc_mr22_freq3),
            .reg_ddrc_diff_rank_rd_gap_freq3            (reg_ddrc_diff_rank_rd_gap_freq3),
            .reg_ddrc_diff_rank_wr_gap_freq3            (reg_ddrc_diff_rank_wr_gap_freq3),
            .reg_ddrc_rd2wr_dr_freq3                    (reg_ddrc_rd2wr_dr_freq3),
            .reg_ddrc_wr2rd_dr_freq3                    (reg_ddrc_wr2rd_dr_freq3),
            .reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3    (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3),
            .reg_ddrc_wr2pre_freq3                      (reg_ddrc_wr2pre_freq3),
            .reg_ddrc_wra2pre_freq3                     (reg_ddrc_wra2pre_freq3),
            .reg_ddrc_t_faw_freq3                       (reg_ddrc_t_faw_freq3),
            .reg_ddrc_t_ras_max_freq3                   (reg_ddrc_t_ras_max_freq3),
            .reg_ddrc_t_ras_min_freq3                   (reg_ddrc_t_ras_min_freq3),
            .reg_ddrc_t_rcd_write_freq3                 (reg_ddrc_t_rcd_write_freq3),
            .reg_ddrc_t_xp_freq3                        (reg_ddrc_t_xp_freq3),
            .reg_ddrc_rd2pre_freq3                      (reg_ddrc_rd2pre_freq3),
            .reg_ddrc_rda2pre_freq3                     (reg_ddrc_rda2pre_freq3),
            .reg_ddrc_t_rc_freq3                        (reg_ddrc_t_rc_freq3),
            .reg_ddrc_write_latency_freq3               (reg_ddrc_write_latency_freq3),
            .reg_ddrc_read_latency_freq3                (reg_ddrc_read_latency_freq3),
            .reg_ddrc_rd2wr_freq3                       (reg_ddrc_rd2wr_freq3),
            .reg_ddrc_wr2rd_freq3                       (reg_ddrc_wr2rd_freq3),
            .reg_ddrc_wr2mr_freq3                       (reg_ddrc_wr2mr_freq3),
            .reg_ddrc_t_mr_freq3                        (reg_ddrc_t_mr_freq3),
            .reg_ddrc_rd2mr_freq3                       (reg_ddrc_rd2mr_freq3),
            .reg_ddrc_t_rcd_freq3                       (reg_ddrc_t_rcd_freq3),
            .reg_ddrc_t_ccd_freq3                       (reg_ddrc_t_ccd_freq3),
            .reg_ddrc_t_rrd_freq3                       (reg_ddrc_t_rrd_freq3),
            .reg_ddrc_t_rp_freq3                        (reg_ddrc_t_rp_freq3),
            .reg_ddrc_t_cksrx_freq3                     (reg_ddrc_t_cksrx_freq3),
            .reg_ddrc_t_cksre_freq3                     (reg_ddrc_t_cksre_freq3),
            .reg_ddrc_t_ckesr_freq3                     (reg_ddrc_t_ckesr_freq3),
            .reg_ddrc_t_cke_freq3                       (reg_ddrc_t_cke_freq3),
            .reg_ddrc_t_ckcsx_freq3                     (reg_ddrc_t_ckcsx_freq3),
            .reg_ddrc_t_ccd_s_freq3                     (reg_ddrc_t_ccd_s_freq3),
            .reg_ddrc_t_rrd_s_freq3                     (reg_ddrc_t_rrd_s_freq3),
            .reg_ddrc_wr2rd_s_freq3                     (reg_ddrc_wr2rd_s_freq3),
            .reg_ddrc_t_cmdcke_freq3                    (reg_ddrc_t_cmdcke_freq3),
            .reg_ddrc_t_pdn_freq3                       (reg_ddrc_t_pdn_freq3),
            .reg_ddrc_t_xsr_dsm_x1024_freq3             (reg_ddrc_t_xsr_dsm_x1024_freq3),
            .reg_ddrc_t_csh_freq3                       (reg_ddrc_t_csh_freq3),
            .reg_ddrc_odtloff_freq3                     (reg_ddrc_odtloff_freq3),
            .reg_ddrc_t_ccd_mw_freq3                    (reg_ddrc_t_ccd_mw_freq3),
            .reg_ddrc_t_ppd_freq3                       (reg_ddrc_t_ppd_freq3),
            .reg_ddrc_t_xsr_freq3                       (reg_ddrc_t_xsr_freq3),
            .reg_ddrc_t_osco_freq3                      (reg_ddrc_t_osco_freq3),
            .reg_ddrc_dqsosc_enable_freq3               (reg_ddrc_dqsosc_enable_freq3),
            .reg_ddrc_dqsosc_interval_unit_freq3        (reg_ddrc_dqsosc_interval_unit_freq3),
            .reg_ddrc_dqsosc_interval_freq3             (reg_ddrc_dqsosc_interval_freq3),
            .reg_ddrc_t_vrcg_enable_freq3               (reg_ddrc_t_vrcg_enable_freq3),
            .reg_ddrc_t_vrcg_disable_freq3              (reg_ddrc_t_vrcg_disable_freq3),
            .reg_ddrc_t_zq_stop_freq3                   (reg_ddrc_t_zq_stop_freq3),
            .reg_ddrc_dvfsq_enable_freq3                (reg_ddrc_dvfsq_enable_freq3),
            .reg_ddrc_t_zq_long_nop_freq3               (reg_ddrc_t_zq_long_nop_freq3),
            .reg_ddrc_t_zq_short_nop_freq3              (reg_ddrc_t_zq_short_nop_freq3),

            .reg_ddrc_t_zq_reset_nop_freq3              (reg_ddrc_t_zq_reset_nop_freq3),
            .reg_ddrc_t_zq_short_interval_x1024_freq3   (reg_ddrc_t_zq_short_interval_x1024_freq3),
            .reg_ddrc_bank_org_freq3                    (reg_ddrc_bank_org_freq3),
            .reg_ddrc_rd2wr_s_freq3                     (reg_ddrc_rd2wr_s_freq3),
            .reg_ddrc_mrr2rd_freq3                      (reg_ddrc_mrr2rd_freq3),
            .reg_ddrc_mrr2wr_freq3                      (reg_ddrc_mrr2wr_freq3),
            .reg_ddrc_mrr2mrw_freq3                     (reg_ddrc_mrr2mrw_freq3),
            .reg_ddrc_ws_off2ws_fs_freq3                (reg_ddrc_ws_off2ws_fs_freq3),
            .reg_ddrc_t_wcksus_freq3                    (reg_ddrc_t_wcksus_freq3),
            .reg_ddrc_ws_fs2wck_sus_freq3               (reg_ddrc_ws_fs2wck_sus_freq3),
            .reg_ddrc_max_rd_sync_freq3                 (reg_ddrc_max_rd_sync_freq3),
            .reg_ddrc_max_wr_sync_freq3                 (reg_ddrc_max_wr_sync_freq3),
            .reg_ddrc_dfi_twck_delay_freq3              (reg_ddrc_dfi_twck_delay_freq3),
            .reg_ddrc_dfi_twck_en_rd_freq3              (reg_ddrc_dfi_twck_en_rd_freq3),
            .reg_ddrc_dfi_twck_en_wr_freq3              (reg_ddrc_dfi_twck_en_wr_freq3),
            .reg_ddrc_dfi_twck_en_fs_freq3              (reg_ddrc_dfi_twck_en_fs_freq3),
            .reg_ddrc_dfi_twck_dis_freq3                (reg_ddrc_dfi_twck_dis_freq3),
            .reg_ddrc_dfi_twck_fast_toggle_freq3        (reg_ddrc_dfi_twck_fast_toggle_freq3),
            .reg_ddrc_dfi_twck_toggle_freq3             (reg_ddrc_dfi_twck_toggle_freq3),
            .reg_ddrc_dfi_twck_toggle_cs_freq3          (reg_ddrc_dfi_twck_toggle_cs_freq3),
            .reg_ddrc_dfi_twck_toggle_post_freq3        (reg_ddrc_dfi_twck_toggle_post_freq3),
            .reg_ddrc_dfi_twck_toggle_post_rd_en_freq3  (reg_ddrc_dfi_twck_toggle_post_rd_en_freq3),
            .reg_ddrc_dfi_twck_toggle_post_rd_freq3     (reg_ddrc_dfi_twck_toggle_post_rd_freq3),
            .reg_ddrc_dfi_t_ctrl_delay_freq3            (reg_ddrc_dfi_t_ctrl_delay_freq3),
            .reg_ddrc_dfi_t_rddata_en_freq3             (reg_ddrc_dfi_t_rddata_en_freq3),
            .reg_ddrc_dfi_tphy_wrdata_freq3             (reg_ddrc_dfi_tphy_wrdata_freq3),
            .reg_ddrc_dfi_tphy_wrlat_freq3              (reg_ddrc_dfi_tphy_wrlat_freq3),
            .reg_ddrc_dfi_t_wrdata_delay_freq3          (reg_ddrc_dfi_t_wrdata_delay_freq3),
            .reg_ddrc_dfi_t_dram_clk_disable_freq3      (reg_ddrc_dfi_t_dram_clk_disable_freq3),
            .reg_ddrc_dfi_t_dram_clk_enable_freq3       (reg_ddrc_dfi_t_dram_clk_enable_freq3),
            .reg_ddrc_dfi_tphy_rdcslat_freq3            (reg_ddrc_dfi_tphy_rdcslat_freq3),
            .reg_ddrc_dfi_tphy_wrcslat_freq3            (reg_ddrc_dfi_tphy_wrcslat_freq3),

            .reg_ddrc_hpr_max_starve_freq3              (reg_ddrc_hpr_max_starve_freq3),
            .reg_ddrc_hpr_xact_run_length_freq3         (reg_ddrc_hpr_xact_run_length_freq3),
            .reg_ddrc_lpr_max_starve_freq3              (reg_ddrc_lpr_max_starve_freq3),
            .reg_ddrc_lpr_xact_run_length_freq3         (reg_ddrc_lpr_xact_run_length_freq3),
            .reg_ddrc_w_max_starve_freq3                (reg_ddrc_w_max_starve_freq3),
            .reg_ddrc_w_xact_run_length_freq3           (reg_ddrc_w_xact_run_length_freq3),



            .reg_ddrc_rdwr_idle_gap_freq3               (reg_ddrc_rdwr_idle_gap_freq3),
            .reg_ddrc_pageclose_timer_freq3             (reg_ddrc_pageclose_timer_freq3),


            .reg_ddrc_rd_link_ecc_enable_freq3 (reg_ddrc_rd_link_ecc_enable_freq3),
            .reg_ddrc_wr_link_ecc_enable_freq3 (reg_ddrc_wr_link_ecc_enable_freq3),


          /////////////
          // Outputs //
          /////////////

            .regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024 (regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024),
            .regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024 (regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024),
            .regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8  (regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8),
            .regmux_ddrc_dfi_t_ctrlupd_interval_type1     (regmux_ddrc_dfi_t_ctrlupd_interval_type1),
            .regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit(regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit),
            .regmux_ddrc_ppt2_en                          (regmux_ddrc_ppt2_en),
            .regmux_ddrc_ppt2_override                    (regmux_ddrc_ppt2_override),
            .regmux_ddrc_ctrlupd_after_dqsosc             (regmux_ddrc_ctrlupd_after_dqsosc),

            .regmux_ddrc_frequency_ratio                   (regmux_ddrc_frequency_ratio),
            .regmux_ddrc_frequency_ratio_next              (regmux_ddrc_frequency_ratio_next),


            .regmux_ddrc_refresh_timer0_start_value_x32 (regmux_ddrc_refresh_timer0_start_value_x32),
            .regmux_ddrc_refresh_timer1_start_value_x32 (regmux_ddrc_refresh_timer1_start_value_x32),

            .regmux_ddrc_derated_t_rcd               (regmux_ddrc_derated_t_rcd),
            .regmux_ddrc_derated_t_ras_min           (regmux_ddrc_derated_t_ras_min),
            .regmux_ddrc_derated_t_rp                (regmux_ddrc_derated_t_rp),
            .regmux_ddrc_derated_t_rrd               (regmux_ddrc_derated_t_rrd),
            .regmux_ddrc_derated_t_rc                (regmux_ddrc_derated_t_rc),
            .regmux_ddrc_mr4_read_interval           (regmux_ddrc_mr4_read_interval),
            .regmux_ddrc_derated_t_rcd_write         (regmux_ddrc_derated_t_rcd_write),
            .regmux_ddrc_powerdown_to_x32            (regmux_ddrc_powerdown_to_x32),
            .regmux_ddrc_selfref_to_x32              (regmux_ddrc_selfref_to_x32),

            .regmux_ddrc_hw_lp_idle_x32              (regmux_ddrc_hw_lp_idle_x32),
            .regmux_ddrc_refresh_margin              (regmux_ddrc_refresh_margin),
            .regmux_ddrc_refresh_to_x1_x32           (regmux_ddrc_refresh_to_x1_x32),
            .regmux_ddrc_refresh_to_ab_x32           (regmux_ddrc_refresh_to_ab_x32),
            .regmux_ddrc_refresh_to_x1_sel           (regmux_ddrc_refresh_to_x1_sel_comb),
            .regmux_ddrc_t_refi_x1_sel               (regmux_ddrc_t_refi_x1_sel_comb),
            .regmux_ddrc_t_refi_x32                  (regmux_ddrc_t_refi_x1_x32),
            .regmux_ddrc_t_rfc_min                   (regmux_ddrc_t_rfc_min),
            .regmux_ddrc_t_rfc_min_ab                   (regmux_ddrc_t_rfc_min_ab),
            .regmux_ddrc_t_pbr2pbr                      (regmux_ddrc_t_pbr2pbr),
            .regmux_ddrc_t_pbr2act                      (regmux_ddrc_t_pbr2act),
            .regmux_ddrc_t_rfmpb                      (regmux_ddrc_t_rfmpb),
            .regmux_ddrc_t_pgm_x1_x1024                    (regmux_ddrc_t_pgm_x1_x1024),
            .regmux_ddrc_t_pgm_x1_sel                      (regmux_ddrc_t_pgm_x1_sel),
            .regmux_ddrc_t_pgmpst_x32                      (regmux_ddrc_t_pgmpst_x32),
            .regmux_ddrc_t_pgm_exit                        (regmux_ddrc_t_pgm_exit),
            .regmux_ddrc_mr                             (regmux_ddrc_mr),
            .regmux_ddrc_emr                            (regmux_ddrc_emr),
            .regmux_ddrc_emr2                           (regmux_ddrc_emr2),
            .regmux_ddrc_emr3                           (regmux_ddrc_emr3),
            .regmux_ddrc_mr4                            (regmux_ddrc_mr4),
            .regmux_ddrc_mr5                            (regmux_ddrc_mr5),
            .regmux_ddrc_mr6                            (regmux_ddrc_mr6),
            .regmux_ddrc_mr22                           (regmux_ddrc_mr22),
            .regmux_ddrc_diff_rank_rd_gap               (regmux_ddrc_diff_rank_rd_gap),
            .regmux_ddrc_diff_rank_wr_gap               (regmux_ddrc_diff_rank_wr_gap),
            .regmux_ddrc_rd2wr_dr                       (regmux_ddrc_rd2wr_dr),
            .regmux_ddrc_wr2rd_dr                       (regmux_ddrc_wr2rd_dr),
            .regmux_ddrc_lpddr4_diff_bank_rwa2pre       (regmux_ddrc_lpddr4_diff_bank_rwa2pre),
            .regmux_ddrc_wr2pre                         (regmux_ddrc_wr2pre),
            .regmux_ddrc_wra2pre                        (regmux_ddrc_wra2pre),
            .regmux_ddrc_t_faw                          (regmux_ddrc_t_faw),
            .regmux_ddrc_t_ras_max                      (regmux_ddrc_t_ras_max),
            .regmux_ddrc_t_ras_min                      (regmux_ddrc_t_ras_min),
            .regmux_ddrc_t_rcd_write                    (regmux_ddrc_t_rcd_write),
            .regmux_ddrc_t_xp                           (regmux_ddrc_t_xp),
            .regmux_ddrc_rd2pre                         (regmux_ddrc_rd2pre),
            .regmux_ddrc_rda2pre                        (regmux_ddrc_rda2pre),
            .regmux_ddrc_t_rc                           (regmux_ddrc_t_rc),
            .regmux_ddrc_write_latency                  (regmux_ddrc_write_latency),
            .regmux_ddrc_read_latency                   (regmux_ddrc_read_latency),
            .regmux_ddrc_rd2wr                          (regmux_ddrc_rd2wr),
            .regmux_ddrc_wr2rd                          (regmux_ddrc_wr2rd),
            .regmux_ddrc_wr2mr                          (regmux_ddrc_wr2mr),
            .regmux_ddrc_t_mr                           (regmux_ddrc_t_mr),
            .regmux_ddrc_rd2mr                          (regmux_ddrc_rd2mr),
            .regmux_ddrc_t_rcd                          (regmux_ddrc_t_rcd),
            .regmux_ddrc_t_ccd                          (regmux_ddrc_t_ccd),
            .regmux_ddrc_t_rrd                          (regmux_ddrc_t_rrd),
            .regmux_ddrc_t_rp                           (regmux_ddrc_t_rp),
            .regmux_ddrc_t_cksrx                        (regmux_ddrc_t_cksrx),
            .regmux_ddrc_t_cksre                        (regmux_ddrc_t_cksre),
            .regmux_ddrc_t_ckesr                        (regmux_ddrc_t_ckesr),
            .regmux_ddrc_t_cke                          (regmux_ddrc_t_cke),
            .regmux_ddrc_t_ckcsx                        (regmux_ddrc_t_ckcsx),
            .regmux_ddrc_t_ccd_s                        (regmux_ddrc_t_ccd_s),
            .regmux_ddrc_t_rrd_s                        (regmux_ddrc_t_rrd_s),
            .regmux_ddrc_wr2rd_s                        (regmux_ddrc_wr2rd_s),
            .regmux_ddrc_t_cmdcke                       (regmux_ddrc_t_cmdcke),
            .regmux_ddrc_t_pdn                          (regmux_ddrc_t_pdn),
            .regmux_ddrc_t_xsr_dsm_x1024                (regmux_ddrc_t_xsr_dsm_x1024),
            .regmux_ddrc_t_csh                          (regmux_ddrc_t_csh),
            .regmux_ddrc_odtloff                        (regmux_ddrc_odtloff),
            .regmux_ddrc_t_ccd_mw                       (regmux_ddrc_t_ccd_mw),
            .regmux_ddrc_t_ppd                          (regmux_ddrc_t_ppd),
            .regmux_ddrc_t_xsr                          (regmux_ddrc_t_xsr),
            .regmux_ddrc_t_osco                         (regmux_ddrc_t_osco),
            .regmux_ddrc_dqsosc_enable                  (regmux_ddrc_dqsosc_enable),
            .regmux_ddrc_dqsosc_interval_unit           (regmux_ddrc_dqsosc_interval_unit),
            .regmux_ddrc_dqsosc_interval                (regmux_ddrc_dqsosc_interval),
            .regmux_ddrc_t_vrcg_enable                  (regmux_ddrc_t_vrcg_enable),
            .regmux_ddrc_t_vrcg_disable                 (regmux_ddrc_t_vrcg_disable),
            .regmux_ddrc_t_zq_stop                      (regmux_ddrc_t_zq_stop),
            .regmux_ddrc_dvfsq_enable                   (regmux_ddrc_dvfsq_enable),
            .regmux_ddrc_dvfsq_enable_next              (regmux_ddrc_dvfsq_enable_next),
            .regmux_ddrc_t_zq_long_nop                  (regmux_ddrc_t_zq_long_nop),
            .regmux_ddrc_t_zq_short_nop                 (regmux_ddrc_t_zq_short_nop),

            .regmux_ddrc_t_zq_reset_nop                 (regmux_ddrc_t_zq_reset_nop),
            .regmux_ddrc_t_zq_short_interval_x1024      (regmux_ddrc_t_zq_short_interval_x1024),
            .regmux_ddrc_bank_org                       (regmux_ddrc_bank_org),
            .regmux_ddrc_rd2wr_s                        (regmux_ddrc_rd2wr_s),
            .regmux_ddrc_mrr2rd                         (regmux_ddrc_mrr2rd),
            .regmux_ddrc_mrr2wr                         (regmux_ddrc_mrr2wr),
            .regmux_ddrc_mrr2mrw                        (regmux_ddrc_mrr2mrw),
            .regmux_ddrc_ws_off2ws_fs                   (regmux_ddrc_ws_off2ws_fs),
            .regmux_ddrc_t_wcksus                       (regmux_ddrc_t_wcksus),
            .regmux_ddrc_ws_fs2wck_sus                  (regmux_ddrc_ws_fs2wck_sus),
            .regmux_ddrc_max_rd_sync                    (regmux_ddrc_max_rd_sync),
            .regmux_ddrc_max_wr_sync                    (regmux_ddrc_max_wr_sync),
            .regmux_ddrc_dfi_twck_delay                 (regmux_ddrc_dfi_twck_delay),
            .regmux_ddrc_dfi_twck_en_rd                 (regmux_ddrc_dfi_twck_en_rd),
            .regmux_ddrc_dfi_twck_en_wr                 (regmux_ddrc_dfi_twck_en_wr),
            .regmux_ddrc_dfi_twck_en_fs                 (regmux_ddrc_dfi_twck_en_fs),
            .regmux_ddrc_dfi_twck_dis                   (regmux_ddrc_dfi_twck_dis),
            .regmux_ddrc_dfi_twck_fast_toggle           (regmux_ddrc_dfi_twck_fast_toggle),
            .regmux_ddrc_dfi_twck_toggle                (regmux_ddrc_dfi_twck_toggle),
            .regmux_ddrc_dfi_twck_toggle_cs             (regmux_ddrc_dfi_twck_toggle_cs),
            .regmux_ddrc_dfi_twck_toggle_post           (regmux_ddrc_dfi_twck_toggle_post),
            .regmux_ddrc_dfi_twck_toggle_post_rd_en     (regmux_ddrc_dfi_twck_toggle_post_rd_en),
            .regmux_ddrc_dfi_twck_toggle_post_rd        (regmux_ddrc_dfi_twck_toggle_post_rd),
            .regmux_ddrc_dfi_t_ctrl_delay               (regmux_ddrc_dfi_t_ctrl_delay),
            .regmux_ddrc_dfi_t_rddata_en                (regmux_ddrc_dfi_t_rddata_en),
            .regmux_ddrc_dfi_tphy_wrdata                (regmux_ddrc_dfi_tphy_wrdata),
            .regmux_ddrc_dfi_tphy_wrlat                 (regmux_ddrc_dfi_tphy_wrlat),
            .regmux_ddrc_dfi_t_wrdata_delay             (regmux_ddrc_dfi_t_wrdata_delay),
            .regmux_ddrc_dfi_t_dram_clk_disable         (regmux_ddrc_dfi_t_dram_clk_disable),
            .regmux_ddrc_dfi_t_dram_clk_enable          (regmux_ddrc_dfi_t_dram_clk_enable),
            .regmux_ddrc_dfi_tphy_rdcslat               (regmux_ddrc_dfi_tphy_rdcslat),
            .regmux_ddrc_dfi_tphy_wrcslat               (regmux_ddrc_dfi_tphy_wrcslat),



            .regmux_ddrc_hpr_max_starve (regmux_ddrc_hpr_max_starve),
            .regmux_ddrc_hpr_xact_run_length (regmux_ddrc_hpr_xact_run_length),
            .regmux_ddrc_lpr_max_starve (regmux_ddrc_lpr_max_starve),
            .regmux_ddrc_lpr_xact_run_length (regmux_ddrc_lpr_xact_run_length),
            .regmux_ddrc_w_max_starve (regmux_ddrc_w_max_starve),
            .regmux_ddrc_w_xact_run_length (regmux_ddrc_w_xact_run_length),

            .regmux_ddrc_rdwr_idle_gap               (regmux_ddrc_rdwr_idle_gap),
            .regmux_ddrc_pageclose_timer             (regmux_ddrc_pageclose_timer)


            ,.regmux_ddrc_rd_link_ecc_enable (regmux_ddrc_rd_link_ecc_enable)
            ,.regmux_ddrc_wr_link_ecc_enable (regmux_ddrc_wr_link_ecc_enable)

            );




// --------------------
// Assigning the new LPDDR5X registers directly without taking them through the dwc_ddrctl_reg_div
// module. The reason is that in LPDDR5 mode, DRAM timing parameters are specified in DRAM clock
// cycles and in both 1:1:2 and 1:1:4 modes, DRAM clock and DDRC/DFI clock frequencies are same,
// and hence there is no need to divide the values
// --------------------
assign regmux_ddrc_derated_t_rcd_write_div = regmux_ddrc_derated_t_rcd_write;

assign regmux_ddrc_t_rcd_write_div         = regmux_ddrc_t_rcd_write;

// -------------------------

   dwc_ddrctl_reg_div
   
    U_reg_div (

             .reg_ddrc_t_zq_long_nop_in                (regmux_ddrc_t_zq_long_nop)
            ,.reg_ddrc_t_zq_long_nop_out               (regmux_ddrc_t_zq_long_nop_div)

            ,.reg_ddrc_t_zq_short_nop_in               (regmux_ddrc_t_zq_short_nop)
            ,.reg_ddrc_t_zq_short_nop_out              (regmux_ddrc_t_zq_short_nop_div)

            ,.reg_ddrc_t_pgm_x1_x1024_in                  (regmux_ddrc_t_pgm_x1_x1024)
            ,.reg_ddrc_t_pgm_x1_x1024_out                 (regmux_ddrc_t_pgm_x1_x1024_div)
            ,.reg_ddrc_t_pgm_x1_sel_in                    (regmux_ddrc_t_pgm_x1_sel)
            ,.reg_ddrc_t_pgm_x1_sel_out                   (regmux_ddrc_t_pgm_x1_sel_div)
            ,.reg_ddrc_t_pgmpst_x32_in                    (regmux_ddrc_t_pgmpst_x32)
            ,.reg_ddrc_t_pgmpst_x32_out                   (regmux_ddrc_t_pgmpst_x32_div)
            ,.reg_ddrc_t_pgm_exit_in                      (regmux_ddrc_t_pgm_exit)
            ,.reg_ddrc_t_pgm_exit_out                     (regmux_ddrc_t_pgm_exit_div)



            ,.reg_ddrc_t_zq_reset_nop_in               (regmux_ddrc_t_zq_reset_nop)
            ,.reg_ddrc_t_zq_reset_nop_out              (regmux_ddrc_t_zq_reset_nop_div)


            ,.reg_ddrc_mr4_read_interval_in             (regmux_ddrc_mr4_read_interval)
            ,.reg_ddrc_mr4_read_interval_out            (regmux_ddrc_mr4_read_interval_div)

            ,.reg_ddrc_blk_channel_idle_time_x32_in            (reg_ddrc_blk_channel_idle_time_x32)
            ,.reg_ddrc_blk_channel_idle_time_x32_out            (reg_ddrc_blk_channel_idle_time_x32_div)


           ,.reg_ddrc_refresh_to_x1_x32_in              (regmux_ddrc_refresh_to_x1_x32)
           ,.reg_ddrc_refresh_to_x1_x32_out             (regmux_ddrc_refresh_to_x1_x32_div_comb)
           ,.reg_ddrc_refresh_to_ab_x32_in              (regmux_ddrc_refresh_to_ab_x32)
           ,.reg_ddrc_refresh_to_ab_x32_out             (regmux_ddrc_refresh_to_ab_x32_div_comb)
           ,.reg_ddrc_t_rfc_min_in                      (regmux_ddrc_t_rfc_min)
           ,.reg_ddrc_t_rfc_min_out                     (regmux_ddrc_t_rfc_min_div_comb)
           ,.reg_ddrc_t_rfc_min_ab_in                   (regmux_ddrc_t_rfc_min_ab)
           ,.reg_ddrc_t_rfc_min_ab_out                  (regmux_ddrc_t_rfc_min_ab_div_comb)
           ,.reg_ddrc_t_refi_x1_x32_in                  (regmux_ddrc_t_refi_x1_x32)
           ,.reg_ddrc_t_refi_x1_x32_out                 (regmux_ddrc_t_refi_x1_x32_div_comb)
           ,.reg_ddrc_refresh_margin_in                 (regmux_ddrc_refresh_margin)
           ,.reg_ddrc_refresh_margin_out                (regmux_ddrc_refresh_margin_div_comb)

           ,.reg_ddrc_refresh_timer0_start_value_x32_in (regmux_ddrc_refresh_timer0_start_value_x32)
           ,.reg_ddrc_refresh_timer0_start_value_x32_out(regmux_ddrc_refresh_timer0_start_value_x32_div_comb)
           ,.reg_ddrc_refresh_timer1_start_value_x32_in (regmux_ddrc_refresh_timer1_start_value_x32)
           ,.reg_ddrc_refresh_timer1_start_value_x32_out(regmux_ddrc_refresh_timer1_start_value_x32_div_comb)
           ,.reg_ddrc_derated_t_rcd_in                  (regmux_ddrc_derated_t_rcd)
           ,.reg_ddrc_derated_t_rcd_out                 (regmux_ddrc_derated_t_rcd_div)
           ,.reg_ddrc_derated_t_ras_min_in              (regmux_ddrc_derated_t_ras_min)
           ,.reg_ddrc_derated_t_ras_min_out             (regmux_ddrc_derated_t_ras_min_div)
           ,.reg_ddrc_derated_t_rp_in                   (regmux_ddrc_derated_t_rp)
           ,.reg_ddrc_derated_t_rp_out                  (regmux_ddrc_derated_t_rp_div)
           ,.reg_ddrc_derated_t_rrd_in                  (regmux_ddrc_derated_t_rrd)
           ,.reg_ddrc_derated_t_rrd_out                 (regmux_ddrc_derated_t_rrd_div)
           ,.reg_ddrc_derated_t_rc_in                   (regmux_ddrc_derated_t_rc)
           ,.reg_ddrc_derated_t_rc_out                  (regmux_ddrc_derated_t_rc_div)

           ,.reg_ddrc_t_pbr2pbr_in                      (regmux_ddrc_t_pbr2pbr)
           ,.reg_ddrc_t_pbr2pbr_out                     (regmux_ddrc_t_pbr2pbr_div_comb)

           ,.reg_ddrc_t_rfmpb_in                        (regmux_ddrc_t_rfmpb)
           ,.reg_ddrc_t_rfmpb_out                       (regmux_ddrc_t_rfmpb_div_comb)

           ,.reg_ddrc_diff_rank_rd_gap_in                (regmux_ddrc_diff_rank_rd_gap)
           ,.reg_ddrc_diff_rank_rd_gap_out               (regmux_ddrc_diff_rank_rd_gap_div)
           ,.reg_ddrc_diff_rank_wr_gap_in                (regmux_ddrc_diff_rank_wr_gap)
           ,.reg_ddrc_diff_rank_wr_gap_out               (regmux_ddrc_diff_rank_wr_gap_div)
           ,.reg_ddrc_rd2wr_dr_in                        (regmux_ddrc_rd2wr_dr)
           ,.reg_ddrc_rd2wr_dr_out                       (regmux_ddrc_rd2wr_dr_div)
           ,.reg_ddrc_wr2rd_dr_in                        (regmux_ddrc_wr2rd_dr)
           ,.reg_ddrc_wr2rd_dr_out                       (regmux_ddrc_wr2rd_dr_div)

           ,.reg_ddrc_t_ras_min_in               (regmux_ddrc_t_ras_min)
           ,.reg_ddrc_t_ras_min_out               (regmux_ddrc_t_ras_min_div)
           ,.reg_ddrc_t_ras_max_in               (regmux_ddrc_t_ras_max)
           ,.reg_ddrc_t_ras_max_out               (regmux_ddrc_t_ras_max_div)
           ,.reg_ddrc_t_faw_in               (regmux_ddrc_t_faw)
           ,.reg_ddrc_t_faw_out               (regmux_ddrc_t_faw_div)
           ,.reg_ddrc_wr2pre_in               (regmux_ddrc_wr2pre)
           ,.reg_ddrc_wr2pre_out               (regmux_ddrc_wr2pre_div)
           ,.reg_ddrc_lpddr4_diff_bank_rwa2pre_in  (regmux_ddrc_lpddr4_diff_bank_rwa2pre)
           ,.reg_ddrc_lpddr4_diff_bank_rwa2pre_out (regmux_ddrc_lpddr4_diff_bank_rwa2pre_div)
           ,.reg_ddrc_wra2pre_in               (regmux_ddrc_wra2pre)
           ,.reg_ddrc_wra2pre_out               (regmux_ddrc_wra2pre_div)

           ,.reg_ddrc_t_rc_in               (regmux_ddrc_t_rc)
           ,.reg_ddrc_t_rc_out               (regmux_ddrc_t_rc_div)
           ,.reg_ddrc_rd2pre_in               (regmux_ddrc_rd2pre)
           ,.reg_ddrc_rd2pre_out               (regmux_ddrc_rd2pre_div)
           ,.reg_ddrc_rda2pre_in               (regmux_ddrc_rda2pre)
           ,.reg_ddrc_rda2pre_out               (regmux_ddrc_rda2pre_div)
           ,.reg_ddrc_t_xp_in               (regmux_ddrc_t_xp)
           ,.reg_ddrc_t_xp_out               (regmux_ddrc_t_xp_div)

           ,.reg_ddrc_wr2rd_in               (regmux_ddrc_wr2rd)
           ,.reg_ddrc_wr2rd_out               (regmux_ddrc_wr2rd_div)
           ,.reg_ddrc_rd2wr_in               (regmux_ddrc_rd2wr)
           ,.reg_ddrc_rd2wr_out               (regmux_ddrc_rd2wr_div)
           ,.reg_ddrc_read_latency_in               (regmux_ddrc_read_latency)
           ,.reg_ddrc_read_latency_out               (regmux_ddrc_read_latency_div)
           ,.reg_ddrc_write_latency_in               (regmux_ddrc_write_latency)
           ,.reg_ddrc_write_latency_out               (regmux_ddrc_write_latency_div)

           ,.reg_ddrc_rd2mr_in               (regmux_ddrc_rd2mr)
           ,.reg_ddrc_rd2mr_out               (regmux_ddrc_rd2mr_div)
           ,.reg_ddrc_t_mr_in                (regmux_ddrc_t_mr)
           ,.reg_ddrc_t_mr_out                (regmux_ddrc_t_mr_div)
           ,.reg_ddrc_wr2mr_in               (regmux_ddrc_wr2mr)
           ,.reg_ddrc_wr2mr_out               (regmux_ddrc_wr2mr_div)

           ,.reg_ddrc_t_rp_in               (regmux_ddrc_t_rp)
           ,.reg_ddrc_t_rp_out               (regmux_ddrc_t_rp_div)
           ,.reg_ddrc_t_rrd_in               (regmux_ddrc_t_rrd)
           ,.reg_ddrc_t_rrd_out               (regmux_ddrc_t_rrd_div)
           ,.reg_ddrc_t_ccd_in               (regmux_ddrc_t_ccd)
           ,.reg_ddrc_t_ccd_out               (regmux_ddrc_t_ccd_div)
           ,.reg_ddrc_t_rcd_in               (regmux_ddrc_t_rcd)
           ,.reg_ddrc_t_rcd_out               (regmux_ddrc_t_rcd_div)

           ,.reg_ddrc_t_cke_in               (regmux_ddrc_t_cke)
           ,.reg_ddrc_t_cke_out               (regmux_ddrc_t_cke_div)
           ,.reg_ddrc_t_ckesr_in               (regmux_ddrc_t_ckesr)
           ,.reg_ddrc_t_ckesr_out               (regmux_ddrc_t_ckesr_div)
           ,.reg_ddrc_t_cksre_in               (regmux_ddrc_t_cksre)
           ,.reg_ddrc_t_cksre_out               (regmux_ddrc_t_cksre_div)
           ,.reg_ddrc_t_cksrx_in               (regmux_ddrc_t_cksrx)
           ,.reg_ddrc_t_cksrx_out               (regmux_ddrc_t_cksrx_div)

           ,.reg_ddrc_t_ckcsx_in               (regmux_ddrc_t_ckcsx)
           ,.reg_ddrc_t_ckcsx_out               (regmux_ddrc_t_ckcsx_div)


           ,.reg_ddrc_wr2rd_s_in               (regmux_ddrc_wr2rd_s)
           ,.reg_ddrc_wr2rd_s_out               (regmux_ddrc_wr2rd_s_div)
           ,.reg_ddrc_t_rrd_s_in               (regmux_ddrc_t_rrd_s)
           ,.reg_ddrc_t_rrd_s_out               (regmux_ddrc_t_rrd_s_div)
           ,.reg_ddrc_t_ccd_s_in               (regmux_ddrc_t_ccd_s)
           ,.reg_ddrc_t_ccd_s_out               (regmux_ddrc_t_ccd_s_div)

           ,.reg_ddrc_t_cmdcke_in               (regmux_ddrc_t_cmdcke)
           ,.reg_ddrc_t_cmdcke_out               (regmux_ddrc_t_cmdcke_div)

           ,.reg_ddrc_t_ccd_mw_in               (regmux_ddrc_t_ccd_mw)
           ,.reg_ddrc_t_ccd_mw_out               (regmux_ddrc_t_ccd_mw_div)
           ,.reg_ddrc_odtloff_in               (regmux_ddrc_odtloff)
           ,.reg_ddrc_odtloff_out               (regmux_ddrc_odtloff_div)
           ,.reg_ddrc_t_ppd_in               (regmux_ddrc_t_ppd)
           ,.reg_ddrc_t_ppd_out               (regmux_ddrc_t_ppd_div)

           ,.reg_ddrc_t_xsr_in               (regmux_ddrc_t_xsr)
           ,.reg_ddrc_t_xsr_out               (regmux_ddrc_t_xsr_div)
           ,.reg_ddrc_t_osco_in              (regmux_ddrc_t_osco)
           ,.reg_ddrc_t_osco_out             (regmux_ddrc_t_osco_div)

           ,.reg_ddrc_t_vrcg_disable_in               (regmux_ddrc_t_vrcg_disable)
           ,.reg_ddrc_t_vrcg_disable_out               (regmux_ddrc_t_vrcg_disable_div)
           ,.reg_ddrc_t_vrcg_enable_in               (regmux_ddrc_t_vrcg_enable)
           ,.reg_ddrc_t_vrcg_enable_out               (regmux_ddrc_t_vrcg_enable_div)


           ,.reg_ddrc_lpddr5 (reg_ddrc_lpddr5)


           ,.reg_ddrc_frequency_ratio (regmux_ddrc_frequency_ratio)

   );


   dwc_ddrctl_reg_ff
   
   U_reg_ff (

     .core_ddrc_core_clk                     (core_ddrc_core_clk)
    ,.core_ddrc_rstn                         (core_ddrc_rstn)

    ,.regmux_ddrc_t_refi_x1_x32_div_comb (regmux_ddrc_t_refi_x1_x32_div_comb)
    ,.regmux_ddrc_refresh_to_x1_x32_div_comb (regmux_ddrc_refresh_to_x1_x32_div_comb)
    ,.regmux_ddrc_refresh_to_ab_x32_div_comb (regmux_ddrc_refresh_to_ab_x32_div_comb)
    ,.regmux_ddrc_refresh_to_x1_sel_comb (regmux_ddrc_refresh_to_x1_sel_comb)
    ,.regmux_ddrc_t_refi_x1_sel_comb (regmux_ddrc_t_refi_x1_sel_comb)
    ,.regmux_ddrc_refresh_margin_div_comb (regmux_ddrc_refresh_margin_div_comb)
    ,.regmux_ddrc_t_rfc_min_div_comb (regmux_ddrc_t_rfc_min_div_comb)
    ,.regmux_ddrc_t_rfc_min_ab_div_comb (regmux_ddrc_t_rfc_min_ab_div_comb)
    ,.regmux_ddrc_refresh_timer0_start_value_x32_div_comb (regmux_ddrc_refresh_timer0_start_value_x32_div_comb)
    ,.regmux_ddrc_refresh_timer1_start_value_x32_div_comb (regmux_ddrc_refresh_timer1_start_value_x32_div_comb)
    ,.regmux_ddrc_t_rfmpb_div_comb (regmux_ddrc_t_rfmpb_div_comb)
    ,.regmux_ddrc_t_pbr2pbr_div_comb (regmux_ddrc_t_pbr2pbr_div_comb)

    ,.regmux_ddrc_t_refi_x1_x32_div_r (regmux_ddrc_t_refi_x1_x32_div)
    ,.regmux_ddrc_refresh_to_x1_x32_div_r (regmux_ddrc_refresh_to_x1_x32_div)
    ,.regmux_ddrc_refresh_to_ab_x32_div_r (regmux_ddrc_refresh_to_ab_x32_div)
    ,.regmux_ddrc_refresh_to_x1_sel_r (regmux_ddrc_refresh_to_x1_sel)
    ,.regmux_ddrc_t_refi_x1_sel_r (regmux_ddrc_t_refi_x1_sel)
    ,.regmux_ddrc_refresh_margin_div_r (regmux_ddrc_refresh_margin_div)
    ,.regmux_ddrc_t_rfc_min_div_r (regmux_ddrc_t_rfc_min_div)
    ,.regmux_ddrc_t_rfc_min_ab_div_r (regmux_ddrc_t_rfc_min_ab_div)
    ,.regmux_ddrc_refresh_timer0_start_value_x32_div_r (regmux_ddrc_refresh_timer0_start_value_x32_div)
    ,.regmux_ddrc_refresh_timer1_start_value_x32_div_r (regmux_ddrc_refresh_timer1_start_value_x32_div)
    ,.regmux_ddrc_t_rfmpb_div_r (regmux_ddrc_t_rfmpb_div)
    ,.regmux_ddrc_t_pbr2pbr_div_r (regmux_ddrc_t_pbr2pbr_div)
  );

endmodule : dwc_ddrctl_regmux_div
