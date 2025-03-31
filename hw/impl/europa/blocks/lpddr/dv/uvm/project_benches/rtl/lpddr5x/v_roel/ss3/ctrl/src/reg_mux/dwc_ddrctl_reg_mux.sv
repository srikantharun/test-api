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

// Revision $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/reg_mux/dwc_ddrctl_reg_mux.sv#10 $
// Description:
//                  Register muxplexer
//                  This block chooses the register field based on the target frequency

`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"

module dwc_ddrctl_reg_mux
import DWC_ddrctl_reg_pkg::*;
#(

) (
  /////////////////////
  // Control signals //
  /////////////////////

       input   [TARGET_FREQUENCY_WIDTH - 1:0]   reg_regmux_target_frequency
      ,output  [TARGET_FREQUENCY_WIDTH - 1:0]   regmux_ddrc_target_frequency

      ,input           hwffc_target_freq_en
      ,input   [TARGET_FREQUENCY_WIDTH - 1:0]   hwffc_target_freq
      ,input   [TARGET_FREQUENCY_WIDTH - 1:0]   hwffc_target_freq_init
      ,output  [TARGET_FREQUENCY_WIDTH - 1:0]   regmux_ddrc_hwffc_target_frequency

  /////////////////////
  // Freq0 registers //
  /////////////////////

     ,input [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0
     ,input [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0
     ,input [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0
     ,input                                              reg_ddrc_ppt2_en_freq0
     ,input                                              reg_ddrc_ppt2_override_freq0
     ,input                                              reg_ddrc_ctrlupd_after_dqsosc_freq0

     ,input [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq0

      ,input           reg_ddrc_frequency_ratio_freq0

      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq0
      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq0

      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_write_freq0
      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_freq0
      ,input  [DERATED_T_RAS_MIN_WIDTH-1:0] reg_ddrc_derated_t_ras_min_freq0
      ,input  [DERATED_T_RP_WIDTH-1:0]      reg_ddrc_derated_t_rp_freq0
      ,input  [DERATED_T_RRD_WIDTH-1:0]     reg_ddrc_derated_t_rrd_freq0
      ,input  [DERATED_T_RC_WIDTH-1:0]      reg_ddrc_derated_t_rc_freq0
      ,input   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq0
      ,input   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq0
      ,input   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq0
      ,input   [REFRESH_MARGIN_WIDTH-1:0]       reg_ddrc_refresh_margin_freq0
      ,input   [REFRESH_TO_X1_X32_WIDTH-1:0]    reg_ddrc_refresh_to_x1_x32_freq0
      ,input   [REFRESH_TO_AB_X32_WIDTH-1:0]    reg_ddrc_refresh_to_ab_x32_freq0
      ,input                                    reg_ddrc_refresh_to_x1_sel_freq0
      ,input                                    reg_ddrc_t_refi_x1_sel_freq0
      ,input   [T_REFI_X1_X32_WIDTH-1:0]        reg_ddrc_t_refi_x32_freq0
      ,input   [T_RFC_MIN_WIDTH-1:0]            reg_ddrc_t_rfc_min_freq0
      ,input   [T_RFC_MIN_AB_WIDTH-1:0]         reg_ddrc_t_rfc_min_ab_freq0
      ,input   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq0
      ,input   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq0
      ,input  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq0
      ,input                             reg_ddrc_t_pgm_x1_sel_freq0
      ,input  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq0
      ,input  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq0

      ,input   [15:0]  reg_ddrc_mr_freq0
      ,input   [15:0]  reg_ddrc_emr_freq0
      ,input   [15:0]  reg_ddrc_emr2_freq0
      ,input   [15:0]  reg_ddrc_emr3_freq0
      ,input   [15:0]  reg_ddrc_mr4_freq0
      ,input   [15:0]  reg_ddrc_mr5_freq0
      ,input   [15:0]  reg_ddrc_mr6_freq0
      ,input   [15:0]  reg_ddrc_mr22_freq0
      ,input   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq0
      ,input   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq0
      ,input   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq0
      ,input   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq0
      ,input   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0
      ,input   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq0
      ,input   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq0
      ,input   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq0
      ,input   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq0
      ,input   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq0
      ,input   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq0
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq0
      ,input   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq0
      ,input   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq0
      ,input   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq0
      ,input   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq0
      ,input   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq0
      ,input   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq0
      ,input   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq0
      ,input   [WR2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq0
      ,input   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq0
      ,input   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq0
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq0
      ,input   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq0
      ,input   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq0
      ,input   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq0
      ,input   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq0
      ,input   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq0
      ,input   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq0
      ,input   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq0
      ,input   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq0
      ,input   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq0
      ,input   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq0
      ,input   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq0
      ,input   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq0
      ,input   [T_PDN_WIDTH-1:0]      reg_ddrc_t_pdn_freq0
      ,input   [T_XSR_DSM_X1024_WIDTH-1:0]  reg_ddrc_t_xsr_dsm_x1024_freq0
      ,input   [T_CSH_WIDTH-1:0]      reg_ddrc_t_csh_freq0
      ,input   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq0
      ,input   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq0
      ,input   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq0
      ,input   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq0
      ,input   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq0
      ,input                                 reg_ddrc_dqsosc_enable_freq0
      ,input                                 reg_ddrc_dqsosc_interval_unit_freq0
      ,input   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq0
      ,input   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq0
      ,input   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq0
      ,input   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq0
      ,input                           reg_ddrc_dvfsq_enable_freq0
      ,input   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq0
      ,input   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq0
      ,input   [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq0
      ,input   [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq0
      ,input   [BANK_ORG_WIDTH-1:0]             reg_ddrc_bank_org_freq0
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_rd2wr_s_freq0
      ,input   [MRR2RD_WIDTH-1:0]               reg_ddrc_mrr2rd_freq0
      ,input   [MRR2WR_WIDTH-1:0]               reg_ddrc_mrr2wr_freq0
      ,input   [MRR2MRW_WIDTH-1:0]              reg_ddrc_mrr2mrw_freq0
      ,input   [WS_OFF2WS_FS_WIDTH-1:0]         reg_ddrc_ws_off2ws_fs_freq0
      ,input   [T_WCKSUS_WIDTH-1:0]             reg_ddrc_t_wcksus_freq0
      ,input   [WS_FS2WCK_SUS_WIDTH-1:0]        reg_ddrc_ws_fs2wck_sus_freq0
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_max_rd_sync_freq0
      ,input   [MAX_WR_SYNC_WIDTH-1:0]          reg_ddrc_max_wr_sync_freq0
      ,input   [DFI_TWCK_DELAY_WIDTH-1:0]       reg_ddrc_dfi_twck_delay_freq0
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

      ,input   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq0
      ,input   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq0
      ,input   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq0
      ,input   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq0
      ,input   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq0
      ,input   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq0
      ,input   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq0
      ,input   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq0
      ,input   [DFI_TPHY_WRCSLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrcslat_freq0

      ,input [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq0
      ,input [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq0
      ,input [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq0
      ,input [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq0
      ,input [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq0
      ,input [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq0

      ,input  [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq0
      ,input  [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq0



      ,input [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq0


      ,input    reg_ddrc_rd_link_ecc_enable_freq0
      ,input    reg_ddrc_wr_link_ecc_enable_freq0


  /////////////////////
  // Freq1 registers //
  /////////////////////

     ,input [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1
     ,input [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1
     ,input [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1
     ,input                                              reg_ddrc_ppt2_en_freq1
     ,input                                              reg_ddrc_ppt2_override_freq1
     ,input                                              reg_ddrc_ctrlupd_after_dqsosc_freq1

     ,input [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq1

      ,input           reg_ddrc_frequency_ratio_freq1

      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq1
      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq1

      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_write_freq1
      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_freq1
      ,input  [DERATED_T_RAS_MIN_WIDTH-1:0] reg_ddrc_derated_t_ras_min_freq1
      ,input  [DERATED_T_RP_WIDTH-1:0]      reg_ddrc_derated_t_rp_freq1
      ,input  [DERATED_T_RRD_WIDTH-1:0]     reg_ddrc_derated_t_rrd_freq1
      ,input  [DERATED_T_RC_WIDTH-1:0]      reg_ddrc_derated_t_rc_freq1
      ,input   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq1
      ,input   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq1
      ,input   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq1
      ,input   [REFRESH_MARGIN_WIDTH-1:0]       reg_ddrc_refresh_margin_freq1
      ,input   [REFRESH_TO_X1_X32_WIDTH-1:0]    reg_ddrc_refresh_to_x1_x32_freq1
      ,input   [REFRESH_TO_AB_X32_WIDTH-1:0]    reg_ddrc_refresh_to_ab_x32_freq1
      ,input                                    reg_ddrc_refresh_to_x1_sel_freq1
      ,input                                    reg_ddrc_t_refi_x1_sel_freq1
      ,input   [T_REFI_X1_X32_WIDTH-1:0]        reg_ddrc_t_refi_x32_freq1
      ,input   [T_RFC_MIN_WIDTH-1:0]            reg_ddrc_t_rfc_min_freq1
      ,input   [T_RFC_MIN_AB_WIDTH-1:0]         reg_ddrc_t_rfc_min_ab_freq1
      ,input   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq1
      ,input   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq1
      ,input  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq1
      ,input                             reg_ddrc_t_pgm_x1_sel_freq1
      ,input  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq1
      ,input  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq1

      ,input   [15:0]  reg_ddrc_mr_freq1
      ,input   [15:0]  reg_ddrc_emr_freq1
      ,input   [15:0]  reg_ddrc_emr2_freq1
      ,input   [15:0]  reg_ddrc_emr3_freq1
      ,input   [15:0]  reg_ddrc_mr4_freq1
      ,input   [15:0]  reg_ddrc_mr5_freq1
      ,input   [15:0]  reg_ddrc_mr6_freq1
      ,input   [15:0]  reg_ddrc_mr22_freq1
      ,input   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq1
      ,input   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq1
      ,input   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq1
      ,input   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq1
      ,input   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1
      ,input   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq1
      ,input   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq1
      ,input   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq1
      ,input   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq1
      ,input   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq1
      ,input   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq1
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq1
      ,input   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq1
      ,input   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq1
      ,input   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq1
      ,input   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq1
      ,input   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq1
      ,input   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq1
      ,input   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq1
      ,input   [WR2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq1
      ,input   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq1
      ,input   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq1
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq1
      ,input   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq1
      ,input   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq1
      ,input   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq1
      ,input   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq1
      ,input   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq1
      ,input   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq1
      ,input   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq1
      ,input   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq1
      ,input   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq1
      ,input   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq1
      ,input   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq1
      ,input   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq1
      ,input   [T_PDN_WIDTH-1:0]      reg_ddrc_t_pdn_freq1
      ,input   [T_XSR_DSM_X1024_WIDTH-1:0]  reg_ddrc_t_xsr_dsm_x1024_freq1
      ,input   [T_CSH_WIDTH-1:0]      reg_ddrc_t_csh_freq1
      ,input   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq1
      ,input   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq1
      ,input   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq1
      ,input   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq1
      ,input   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq1
      ,input                                 reg_ddrc_dqsosc_enable_freq1
      ,input                                 reg_ddrc_dqsosc_interval_unit_freq1
      ,input   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq1
      ,input   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq1
      ,input   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq1
      ,input   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq1
      ,input                           reg_ddrc_dvfsq_enable_freq1
      ,input   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq1
      ,input   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq1
      ,input   [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq1
      ,input   [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq1
      ,input   [BANK_ORG_WIDTH-1:0]             reg_ddrc_bank_org_freq1
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_rd2wr_s_freq1
      ,input   [MRR2RD_WIDTH-1:0]               reg_ddrc_mrr2rd_freq1
      ,input   [MRR2WR_WIDTH-1:0]               reg_ddrc_mrr2wr_freq1
      ,input   [MRR2MRW_WIDTH-1:0]              reg_ddrc_mrr2mrw_freq1
      ,input   [WS_OFF2WS_FS_WIDTH-1:0]         reg_ddrc_ws_off2ws_fs_freq1
      ,input   [T_WCKSUS_WIDTH-1:0]             reg_ddrc_t_wcksus_freq1
      ,input   [WS_FS2WCK_SUS_WIDTH-1:0]        reg_ddrc_ws_fs2wck_sus_freq1
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_max_rd_sync_freq1
      ,input   [MAX_WR_SYNC_WIDTH-1:0]          reg_ddrc_max_wr_sync_freq1
      ,input   [DFI_TWCK_DELAY_WIDTH-1:0]       reg_ddrc_dfi_twck_delay_freq1
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

      ,input   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq1
      ,input   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq1
      ,input   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq1
      ,input   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq1
      ,input   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq1
      ,input   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq1
      ,input   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq1
      ,input   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq1
      ,input   [DFI_TPHY_WRCSLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrcslat_freq1

      ,input [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq1
      ,input [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq1
      ,input [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq1
      ,input [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq1
      ,input [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq1
      ,input [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq1

      ,input  [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq1
      ,input  [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq1



      ,input [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq1


      ,input    reg_ddrc_rd_link_ecc_enable_freq1
      ,input    reg_ddrc_wr_link_ecc_enable_freq1


  /////////////////////
  // Freq2 registers //
  /////////////////////

     ,input [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2
     ,input [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2
     ,input [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2
     ,input                                              reg_ddrc_ppt2_en_freq2
     ,input                                              reg_ddrc_ppt2_override_freq2
     ,input                                              reg_ddrc_ctrlupd_after_dqsosc_freq2

     ,input [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq2

      ,input           reg_ddrc_frequency_ratio_freq2

      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq2
      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq2

      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_write_freq2
      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_freq2
      ,input  [DERATED_T_RAS_MIN_WIDTH-1:0] reg_ddrc_derated_t_ras_min_freq2
      ,input  [DERATED_T_RP_WIDTH-1:0]      reg_ddrc_derated_t_rp_freq2
      ,input  [DERATED_T_RRD_WIDTH-1:0]     reg_ddrc_derated_t_rrd_freq2
      ,input  [DERATED_T_RC_WIDTH-1:0]      reg_ddrc_derated_t_rc_freq2
      ,input   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq2
      ,input   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq2
      ,input   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq2
      ,input   [REFRESH_MARGIN_WIDTH-1:0]       reg_ddrc_refresh_margin_freq2
      ,input   [REFRESH_TO_X1_X32_WIDTH-1:0]    reg_ddrc_refresh_to_x1_x32_freq2
      ,input   [REFRESH_TO_AB_X32_WIDTH-1:0]    reg_ddrc_refresh_to_ab_x32_freq2
      ,input                                    reg_ddrc_refresh_to_x1_sel_freq2
      ,input                                    reg_ddrc_t_refi_x1_sel_freq2
      ,input   [T_REFI_X1_X32_WIDTH-1:0]        reg_ddrc_t_refi_x32_freq2
      ,input   [T_RFC_MIN_WIDTH-1:0]            reg_ddrc_t_rfc_min_freq2
      ,input   [T_RFC_MIN_AB_WIDTH-1:0]         reg_ddrc_t_rfc_min_ab_freq2
      ,input   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq2
      ,input   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq2
      ,input  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq2
      ,input                             reg_ddrc_t_pgm_x1_sel_freq2
      ,input  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq2
      ,input  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq2

      ,input   [15:0]  reg_ddrc_mr_freq2
      ,input   [15:0]  reg_ddrc_emr_freq2
      ,input   [15:0]  reg_ddrc_emr2_freq2
      ,input   [15:0]  reg_ddrc_emr3_freq2
      ,input   [15:0]  reg_ddrc_mr4_freq2
      ,input   [15:0]  reg_ddrc_mr5_freq2
      ,input   [15:0]  reg_ddrc_mr6_freq2
      ,input   [15:0]  reg_ddrc_mr22_freq2
      ,input   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq2
      ,input   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq2
      ,input   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq2
      ,input   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq2
      ,input   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2
      ,input   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq2
      ,input   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq2
      ,input   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq2
      ,input   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq2
      ,input   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq2
      ,input   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq2
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq2
      ,input   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq2
      ,input   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq2
      ,input   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq2
      ,input   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq2
      ,input   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq2
      ,input   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq2
      ,input   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq2
      ,input   [WR2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq2
      ,input   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq2
      ,input   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq2
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq2
      ,input   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq2
      ,input   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq2
      ,input   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq2
      ,input   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq2
      ,input   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq2
      ,input   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq2
      ,input   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq2
      ,input   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq2
      ,input   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq2
      ,input   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq2
      ,input   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq2
      ,input   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq2
      ,input   [T_PDN_WIDTH-1:0]      reg_ddrc_t_pdn_freq2
      ,input   [T_XSR_DSM_X1024_WIDTH-1:0]  reg_ddrc_t_xsr_dsm_x1024_freq2
      ,input   [T_CSH_WIDTH-1:0]      reg_ddrc_t_csh_freq2
      ,input   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq2
      ,input   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq2
      ,input   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq2
      ,input   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq2
      ,input   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq2
      ,input                                 reg_ddrc_dqsosc_enable_freq2
      ,input                                 reg_ddrc_dqsosc_interval_unit_freq2
      ,input   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq2
      ,input   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq2
      ,input   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq2
      ,input   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq2
      ,input                           reg_ddrc_dvfsq_enable_freq2
      ,input   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq2
      ,input   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq2
      ,input   [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq2
      ,input   [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq2
      ,input   [BANK_ORG_WIDTH-1:0]             reg_ddrc_bank_org_freq2
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_rd2wr_s_freq2
      ,input   [MRR2RD_WIDTH-1:0]               reg_ddrc_mrr2rd_freq2
      ,input   [MRR2WR_WIDTH-1:0]               reg_ddrc_mrr2wr_freq2
      ,input   [MRR2MRW_WIDTH-1:0]              reg_ddrc_mrr2mrw_freq2
      ,input   [WS_OFF2WS_FS_WIDTH-1:0]         reg_ddrc_ws_off2ws_fs_freq2
      ,input   [T_WCKSUS_WIDTH-1:0]             reg_ddrc_t_wcksus_freq2
      ,input   [WS_FS2WCK_SUS_WIDTH-1:0]        reg_ddrc_ws_fs2wck_sus_freq2
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_max_rd_sync_freq2
      ,input   [MAX_WR_SYNC_WIDTH-1:0]          reg_ddrc_max_wr_sync_freq2
      ,input   [DFI_TWCK_DELAY_WIDTH-1:0]       reg_ddrc_dfi_twck_delay_freq2
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

      ,input   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq2
      ,input   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq2
      ,input   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq2
      ,input   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq2
      ,input   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq2
      ,input   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq2
      ,input   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq2
      ,input   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq2
      ,input   [DFI_TPHY_WRCSLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrcslat_freq2

      ,input [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq2
      ,input [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq2
      ,input [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq2
      ,input [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq2
      ,input [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq2
      ,input [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq2

      ,input  [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq2
      ,input  [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq2



      ,input [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq2


      ,input    reg_ddrc_rd_link_ecc_enable_freq2
      ,input    reg_ddrc_wr_link_ecc_enable_freq2


  /////////////////////
  // Freq3 registers //
  /////////////////////

     ,input [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3
     ,input [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3
     ,input [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3
     ,input [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3
     ,input                                              reg_ddrc_ppt2_en_freq3
     ,input                                              reg_ddrc_ppt2_override_freq3
     ,input                                              reg_ddrc_ctrlupd_after_dqsosc_freq3

     ,input [HW_LP_IDLE_X32_WIDTH-1:0] reg_ddrc_hw_lp_idle_x32_freq3

      ,input           reg_ddrc_frequency_ratio_freq3

      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_freq3
      ,input [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_freq3

      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_write_freq3
      ,input  [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_freq3
      ,input  [DERATED_T_RAS_MIN_WIDTH-1:0] reg_ddrc_derated_t_ras_min_freq3
      ,input  [DERATED_T_RP_WIDTH-1:0]      reg_ddrc_derated_t_rp_freq3
      ,input  [DERATED_T_RRD_WIDTH-1:0]     reg_ddrc_derated_t_rrd_freq3
      ,input  [DERATED_T_RC_WIDTH-1:0]      reg_ddrc_derated_t_rc_freq3
      ,input   [MR4_READ_INTERVAL_WIDTH-1:0]  reg_ddrc_mr4_read_interval_freq3
      ,input   [POWERDOWN_TO_X32_WIDTH-1:0]   reg_ddrc_powerdown_to_x32_freq3
      ,input   [SELFREF_TO_X32_WIDTH-1:0]   reg_ddrc_selfref_to_x32_freq3
      ,input   [REFRESH_MARGIN_WIDTH-1:0]       reg_ddrc_refresh_margin_freq3
      ,input   [REFRESH_TO_X1_X32_WIDTH-1:0]    reg_ddrc_refresh_to_x1_x32_freq3
      ,input   [REFRESH_TO_AB_X32_WIDTH-1:0]    reg_ddrc_refresh_to_ab_x32_freq3
      ,input                                    reg_ddrc_refresh_to_x1_sel_freq3
      ,input                                    reg_ddrc_t_refi_x1_sel_freq3
      ,input   [T_REFI_X1_X32_WIDTH-1:0]        reg_ddrc_t_refi_x32_freq3
      ,input   [T_RFC_MIN_WIDTH-1:0]            reg_ddrc_t_rfc_min_freq3
      ,input   [T_RFC_MIN_AB_WIDTH-1:0]         reg_ddrc_t_rfc_min_ab_freq3
      ,input   [T_PBR2PBR_WIDTH-1:0]   reg_ddrc_t_pbr2pbr_freq3
      ,input   [T_PBR2ACT_WIDTH-1:0]   reg_ddrc_t_pbr2act_freq3
      ,input  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_freq3
      ,input                             reg_ddrc_t_pgm_x1_sel_freq3
      ,input  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_freq3
      ,input  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_freq3

      ,input   [15:0]  reg_ddrc_mr_freq3
      ,input   [15:0]  reg_ddrc_emr_freq3
      ,input   [15:0]  reg_ddrc_emr2_freq3
      ,input   [15:0]  reg_ddrc_emr3_freq3
      ,input   [15:0]  reg_ddrc_mr4_freq3
      ,input   [15:0]  reg_ddrc_mr5_freq3
      ,input   [15:0]  reg_ddrc_mr6_freq3
      ,input   [15:0]  reg_ddrc_mr22_freq3
      ,input   [DIFF_RANK_RD_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_rd_gap_freq3
      ,input   [DIFF_RANK_WR_GAP_WIDTH-1:0]   reg_ddrc_diff_rank_wr_gap_freq3
      ,input   [RD2WR_DR_WIDTH-1:0]   reg_ddrc_rd2wr_dr_freq3
      ,input   [WR2RD_DR_WIDTH-1:0]   reg_ddrc_wr2rd_dr_freq3
      ,input   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3
      ,input   [WR2PRE_WIDTH-1:0]   reg_ddrc_wr2pre_freq3
      ,input   [WRA2PRE_WIDTH-1:0]   reg_ddrc_wra2pre_freq3
      ,input   [T_FAW_WIDTH-1:0]   reg_ddrc_t_faw_freq3
      ,input   [T_RAS_MAX_WIDTH-1:0]   reg_ddrc_t_ras_max_freq3
      ,input   [T_RAS_MIN_WIDTH-1:0]   reg_ddrc_t_ras_min_freq3
      ,input   [T_XP_WIDTH-1:0]   reg_ddrc_t_xp_freq3
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_write_freq3
      ,input   [RD2PRE_WIDTH-1:0]   reg_ddrc_rd2pre_freq3
      ,input   [RDA2PRE_WIDTH-1:0]   reg_ddrc_rda2pre_freq3
      ,input   [T_RC_WIDTH-1:0]   reg_ddrc_t_rc_freq3
      ,input   [WRITE_LATENCY_WIDTH-1:0]   reg_ddrc_write_latency_freq3
      ,input   [READ_LATENCY_WIDTH-1:0]   reg_ddrc_read_latency_freq3
      ,input   [RD2WR_WIDTH-1:0]   reg_ddrc_rd2wr_freq3
      ,input   [WR2RD_WIDTH-1:0]   reg_ddrc_wr2rd_freq3
      ,input   [WR2MR_WIDTH-1:0]   reg_ddrc_wr2mr_freq3
      ,input   [T_MR_WIDTH-1:0]    reg_ddrc_t_mr_freq3
      ,input   [RD2MR_WIDTH-1:0]   reg_ddrc_rd2mr_freq3
      ,input   [T_RCD_WIDTH-1:0]   reg_ddrc_t_rcd_freq3
      ,input   [T_CCD_WIDTH-1:0]   reg_ddrc_t_ccd_freq3
      ,input   [T_RRD_WIDTH-1:0]   reg_ddrc_t_rrd_freq3
      ,input   [T_RP_WIDTH-1:0]   reg_ddrc_t_rp_freq3
      ,input   [T_CKSRX_WIDTH-1:0]   reg_ddrc_t_cksrx_freq3
      ,input   [T_CKSRE_WIDTH-1:0]   reg_ddrc_t_cksre_freq3
      ,input   [T_CKESR_WIDTH-1:0]   reg_ddrc_t_ckesr_freq3
      ,input   [T_CKE_WIDTH-1:0]   reg_ddrc_t_cke_freq3
      ,input   [T_CKCSX_WIDTH-1:0]   reg_ddrc_t_ckcsx_freq3
      ,input   [T_CCD_S_WIDTH-1:0]   reg_ddrc_t_ccd_s_freq3
      ,input   [T_RRD_S_WIDTH-1:0]   reg_ddrc_t_rrd_s_freq3
      ,input   [WR2RD_S_WIDTH-1:0]   reg_ddrc_wr2rd_s_freq3
      ,input   [T_CMDCKE_WIDTH-1:0]   reg_ddrc_t_cmdcke_freq3
      ,input   [T_PDN_WIDTH-1:0]      reg_ddrc_t_pdn_freq3
      ,input   [T_XSR_DSM_X1024_WIDTH-1:0]  reg_ddrc_t_xsr_dsm_x1024_freq3
      ,input   [T_CSH_WIDTH-1:0]      reg_ddrc_t_csh_freq3
      ,input   [ODTLOFF_WIDTH-1:0]   reg_ddrc_odtloff_freq3
      ,input   [T_CCD_MW_WIDTH-1:0]   reg_ddrc_t_ccd_mw_freq3
      ,input   [T_PPD_WIDTH-1:0]   reg_ddrc_t_ppd_freq3
      ,input   [T_XSR_WIDTH-1:0]  reg_ddrc_t_xsr_freq3
      ,input   [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_freq3
      ,input                                 reg_ddrc_dqsosc_enable_freq3
      ,input                                 reg_ddrc_dqsosc_interval_unit_freq3
      ,input   [DQSOSC_INTERVAL_WIDTH-1:0] reg_ddrc_dqsosc_interval_freq3
      ,input   [T_VRCG_ENABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_enable_freq3
      ,input   [T_VRCG_DISABLE_WIDTH-1:0]   reg_ddrc_t_vrcg_disable_freq3
      ,input   [T_ZQ_STOP_WIDTH-1:0]   reg_ddrc_t_zq_stop_freq3
      ,input                           reg_ddrc_dvfsq_enable_freq3
      ,input   [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_freq3
      ,input   [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_freq3
      ,input   [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_freq3
      ,input   [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] reg_ddrc_t_zq_short_interval_x1024_freq3
      ,input   [BANK_ORG_WIDTH-1:0]             reg_ddrc_bank_org_freq3
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_rd2wr_s_freq3
      ,input   [MRR2RD_WIDTH-1:0]               reg_ddrc_mrr2rd_freq3
      ,input   [MRR2WR_WIDTH-1:0]               reg_ddrc_mrr2wr_freq3
      ,input   [MRR2MRW_WIDTH-1:0]              reg_ddrc_mrr2mrw_freq3
      ,input   [WS_OFF2WS_FS_WIDTH-1:0]         reg_ddrc_ws_off2ws_fs_freq3
      ,input   [T_WCKSUS_WIDTH-1:0]             reg_ddrc_t_wcksus_freq3
      ,input   [WS_FS2WCK_SUS_WIDTH-1:0]        reg_ddrc_ws_fs2wck_sus_freq3
      ,input   [MAX_RD_SYNC_WIDTH-1:0]          reg_ddrc_max_rd_sync_freq3
      ,input   [MAX_WR_SYNC_WIDTH-1:0]          reg_ddrc_max_wr_sync_freq3
      ,input   [DFI_TWCK_DELAY_WIDTH-1:0]       reg_ddrc_dfi_twck_delay_freq3
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

      ,input   [DFI_T_CTRL_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_ctrl_delay_freq3
      ,input   [DFI_T_RDDATA_EN_WIDTH-1:0]   reg_ddrc_dfi_t_rddata_en_freq3
      ,input   [DFI_TPHY_WRDATA_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrdata_freq3
      ,input   [DFI_TPHY_WRLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrlat_freq3
      ,input   [DFI_T_WRDATA_DELAY_WIDTH-1:0]   reg_ddrc_dfi_t_wrdata_delay_freq3
      ,input   [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable_freq3
      ,input   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable_freq3
      ,input   [6:0]   reg_ddrc_dfi_tphy_rdcslat_freq3
      ,input   [DFI_TPHY_WRCSLAT_WIDTH-1:0]   reg_ddrc_dfi_tphy_wrcslat_freq3

      ,input [HPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_hpr_max_starve_freq3
      ,input [HPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_hpr_xact_run_length_freq3
      ,input [LPR_MAX_STARVE_WIDTH-1:0] reg_ddrc_lpr_max_starve_freq3
      ,input [LPR_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_lpr_xact_run_length_freq3
      ,input [W_MAX_STARVE_WIDTH-1:0] reg_ddrc_w_max_starve_freq3
      ,input [W_XACT_RUN_LENGTH_WIDTH-1:0] reg_ddrc_w_xact_run_length_freq3

      ,input  [PAGECLOSE_TIMER_WIDTH-1:0] reg_ddrc_pageclose_timer_freq3
      ,input  [RDWR_IDLE_GAP_WIDTH-1:0] reg_ddrc_rdwr_idle_gap_freq3



      ,input [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_freq3


      ,input    reg_ddrc_rd_link_ecc_enable_freq3
      ,input    reg_ddrc_wr_link_ecc_enable_freq3














  /////////////
  // Outputs //
  /////////////

      ,output [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0] regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024
      ,output [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0] regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024
      ,output [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]  regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8
      ,output [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]      regmux_ddrc_dfi_t_ctrlupd_interval_type1
      ,output [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0] regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit
      ,output                                               regmux_ddrc_ppt2_en
      ,output                                               regmux_ddrc_ppt2_override
      ,output                                               regmux_ddrc_ctrlupd_after_dqsosc

      ,output logic [HW_LP_IDLE_X32_WIDTH-1:0] regmux_ddrc_hw_lp_idle_x32

      ,output           regmux_ddrc_frequency_ratio
      ,output           regmux_ddrc_frequency_ratio_next


      ,output  [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] regmux_ddrc_refresh_timer0_start_value_x32
      ,output  [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] regmux_ddrc_refresh_timer1_start_value_x32

// DERATEVAL0
      ,output  [DERATED_T_RCD_WIDTH-1:0]     regmux_ddrc_derated_t_rcd
      ,output  [DERATED_T_RAS_MIN_WIDTH-1:0] regmux_ddrc_derated_t_ras_min
      ,output  [DERATED_T_RP_WIDTH-1:0]      regmux_ddrc_derated_t_rp
      ,output  [DERATED_T_RRD_WIDTH-1:0]     regmux_ddrc_derated_t_rrd
// DERATEVAL1
      ,output  [DERATED_T_RC_WIDTH-1:0]      regmux_ddrc_derated_t_rc
      ,output  [DERATED_T_RCD_WIDTH-1:0]     regmux_ddrc_derated_t_rcd_write
// DERATEINT
      ,output  [MR4_READ_INTERVAL_WIDTH-1:0]  regmux_ddrc_mr4_read_interval
// PWRTMG
      ,output  [POWERDOWN_TO_X32_WIDTH-1:0]   regmux_ddrc_powerdown_to_x32
      ,output  [SELFREF_TO_X32_WIDTH-1:0]   regmux_ddrc_selfref_to_x32
// HWFFCEX
// RFSHCTL0
      ,output  [REFRESH_MARGIN_WIDTH-1:0]   regmux_ddrc_refresh_margin
      ,output  [REFRESH_TO_X1_X32_WIDTH-1:0]   regmux_ddrc_refresh_to_x1_x32
      ,output  [REFRESH_TO_AB_X32_WIDTH-1:0]   regmux_ddrc_refresh_to_ab_x32
// RFSHTMG
      ,output          regmux_ddrc_t_refi_x1_sel
      ,output          regmux_ddrc_refresh_to_x1_sel
      ,output  [T_REFI_X1_X32_WIDTH-1:0]  regmux_ddrc_t_refi_x32
      ,output  [T_RFC_MIN_WIDTH-1:0]   regmux_ddrc_t_rfc_min
      ,output  [T_RFC_MIN_AB_WIDTH-1:0] regmux_ddrc_t_rfc_min_ab
      ,output  [T_PBR2PBR_WIDTH-1:0]   regmux_ddrc_t_pbr2pbr
      ,output  [T_PBR2ACT_WIDTH-1:0]   regmux_ddrc_t_pbr2act
      ,output  [T_PGM_X1_X1024_WIDTH-1:0]          regmux_ddrc_t_pgm_x1_x1024
      ,output                                      regmux_ddrc_t_pgm_x1_sel
      ,output  [T_PGMPST_X32_WIDTH-1:0]            regmux_ddrc_t_pgmpst_x32
      ,output  [T_PGM_EXIT_WIDTH-1:0]              regmux_ddrc_t_pgm_exit
// INIT3
      ,output  [15:0]  regmux_ddrc_mr
      ,output  [15:0]  regmux_ddrc_emr
// INIT4
      ,output  [15:0]  regmux_ddrc_emr2
      ,output  [15:0]  regmux_ddrc_emr3
// INIT6
      ,output  [15:0]  regmux_ddrc_mr4
      ,output  [15:0]  regmux_ddrc_mr5
// INIT7
      ,output  [15:0]  regmux_ddrc_mr6
      ,output  [15:0]  regmux_ddrc_mr22
// RANKCTL
      ,output  [DIFF_RANK_RD_GAP_WIDTH-1:0]   regmux_ddrc_diff_rank_rd_gap
      ,output  [DIFF_RANK_WR_GAP_WIDTH-1:0]   regmux_ddrc_diff_rank_wr_gap
      ,output  [RD2WR_DR_WIDTH-1:0]   regmux_ddrc_rd2wr_dr
      ,output  [WR2RD_DR_WIDTH-1:0]   regmux_ddrc_wr2rd_dr
      ,output  [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] regmux_ddrc_lpddr4_diff_bank_rwa2pre
      ,output  [WR2PRE_WIDTH-1:0]   regmux_ddrc_wr2pre
      ,output  [WRA2PRE_WIDTH-1:0]   regmux_ddrc_wra2pre
      ,output  [T_FAW_WIDTH-1:0]   regmux_ddrc_t_faw
      ,output  [T_RAS_MAX_WIDTH-1:0]   regmux_ddrc_t_ras_max
      ,output  [T_RAS_MIN_WIDTH-1:0]   regmux_ddrc_t_ras_min
// DRAMSET1TMG1
      ,output  [T_RCD_WIDTH-1:0]   regmux_ddrc_t_rcd_write
      ,output  [T_XP_WIDTH-1:0]   regmux_ddrc_t_xp
      ,output  [RD2PRE_WIDTH-1:0]   regmux_ddrc_rd2pre
      ,output  [RDA2PRE_WIDTH-1:0]   regmux_ddrc_rda2pre
      ,output  [T_RC_WIDTH-1:0]   regmux_ddrc_t_rc
// DRAMSET1TMG2
      ,output  [WRITE_LATENCY_WIDTH-1:0]   regmux_ddrc_write_latency
      ,output  [READ_LATENCY_WIDTH-1:0]   regmux_ddrc_read_latency
      ,output  [RD2WR_WIDTH-1:0]   regmux_ddrc_rd2wr
      ,output  [WR2RD_WIDTH-1:0]   regmux_ddrc_wr2rd
// DRAMSET1TMG3
      ,output  [WR2MR_WIDTH-1:0]   regmux_ddrc_wr2mr
      ,output  [T_MR_WIDTH-1:0]    regmux_ddrc_t_mr
      ,output  [RD2MR_WIDTH-1:0]   regmux_ddrc_rd2mr
// DRAMSET1TMG4
      ,output  [T_RCD_WIDTH-1:0]   regmux_ddrc_t_rcd
      ,output  [T_CCD_WIDTH-1:0]   regmux_ddrc_t_ccd
      ,output  [T_RRD_WIDTH-1:0]   regmux_ddrc_t_rrd
      ,output  [T_RP_WIDTH-1:0]   regmux_ddrc_t_rp
// DRAMTMG5
      ,output  [T_CKSRX_WIDTH-1:0]   regmux_ddrc_t_cksrx
      ,output  [T_CKSRE_WIDTH-1:0]   regmux_ddrc_t_cksre
      ,output  [T_CKESR_WIDTH-1:0]   regmux_ddrc_t_ckesr
      ,output  [T_CKE_WIDTH-1:0]   regmux_ddrc_t_cke
// DRAMTMG6
      ,output  [T_CKCSX_WIDTH-1:0]   regmux_ddrc_t_ckcsx
// DRAMTMG8
      ,output  [T_CCD_S_WIDTH-1:0]   regmux_ddrc_t_ccd_s
      ,output  [T_RRD_S_WIDTH-1:0]   regmux_ddrc_t_rrd_s
      ,output  [WR2RD_S_WIDTH-1:0]   regmux_ddrc_wr2rd_s
      ,output  [T_CMDCKE_WIDTH-1:0]   regmux_ddrc_t_cmdcke
      ,output  [T_PDN_WIDTH-1:0]      regmux_ddrc_t_pdn
      ,output  [T_XSR_DSM_X1024_WIDTH-1:0]  regmux_ddrc_t_xsr_dsm_x1024
      ,output  [T_CSH_WIDTH-1:0]      regmux_ddrc_t_csh
// DRAMTMG13
      ,output  [ODTLOFF_WIDTH-1:0]   regmux_ddrc_odtloff
      ,output  [T_CCD_MW_WIDTH-1:0]   regmux_ddrc_t_ccd_mw
      ,output  [T_PPD_WIDTH-1:0]   regmux_ddrc_t_ppd
// DRAMTMG14
      ,output  [T_XSR_WIDTH-1:0]  regmux_ddrc_t_xsr
      ,output  [T_OSCO_WIDTH-1:0] regmux_ddrc_t_osco
      ,output                                regmux_ddrc_dqsosc_enable
      ,output                                regmux_ddrc_dqsosc_interval_unit
      ,output  [DQSOSC_INTERVAL_WIDTH-1:0] regmux_ddrc_dqsosc_interval
// DRAMTMG17
      ,output  [T_VRCG_ENABLE_WIDTH-1:0]   regmux_ddrc_t_vrcg_enable
      ,output  [T_VRCG_DISABLE_WIDTH-1:0]   regmux_ddrc_t_vrcg_disable
// ZQSET1TMG2
      ,output  [T_ZQ_STOP_WIDTH-1:0]   regmux_ddrc_t_zq_stop
      ,output                          regmux_ddrc_dvfsq_enable
      ,output                          regmux_ddrc_dvfsq_enable_next
// ZQCTL0
      ,output  [T_ZQ_LONG_NOP_WIDTH-1:0]  regmux_ddrc_t_zq_long_nop
      ,output  [T_ZQ_SHORT_NOP_WIDTH-1:0]   regmux_ddrc_t_zq_short_nop
      ,output   [T_ZQ_RESET_NOP_WIDTH-1:0] regmux_ddrc_t_zq_reset_nop
      ,output   [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] regmux_ddrc_t_zq_short_interval_x1024
      ,output   [BANK_ORG_WIDTH-1:0]             regmux_ddrc_bank_org
      ,output   [MAX_RD_SYNC_WIDTH-1:0]          regmux_ddrc_rd2wr_s
      ,output   [MRR2RD_WIDTH-1:0]               regmux_ddrc_mrr2rd
      ,output   [MRR2WR_WIDTH-1:0]               regmux_ddrc_mrr2wr
      ,output   [MRR2MRW_WIDTH-1:0]              regmux_ddrc_mrr2mrw
      ,output   [WS_OFF2WS_FS_WIDTH-1:0]         regmux_ddrc_ws_off2ws_fs
      ,output   [T_WCKSUS_WIDTH-1:0]             regmux_ddrc_t_wcksus
      ,output   [WS_FS2WCK_SUS_WIDTH-1:0]        regmux_ddrc_ws_fs2wck_sus
      ,output   [MAX_RD_SYNC_WIDTH-1:0]          regmux_ddrc_max_rd_sync
      ,output   [MAX_WR_SYNC_WIDTH-1:0]          regmux_ddrc_max_wr_sync
      ,output   [DFI_TWCK_DELAY_WIDTH-1:0]       regmux_ddrc_dfi_twck_delay
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

// DFITMG0
      ,output  [4:0]   regmux_ddrc_dfi_t_ctrl_delay
      ,output  [6:0]   regmux_ddrc_dfi_t_rddata_en
      ,output  [5:0]   regmux_ddrc_dfi_tphy_wrdata
      ,output  [DFI_TPHY_WRLAT_WIDTH-1:0]   regmux_ddrc_dfi_tphy_wrlat
// DFITMG1
      ,output  [4:0]   regmux_ddrc_dfi_t_wrdata_delay
      ,output  [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  regmux_ddrc_dfi_t_dram_clk_disable
      ,output  [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  regmux_ddrc_dfi_t_dram_clk_enable
// DFITMG2
      ,output  [6:0]   regmux_ddrc_dfi_tphy_rdcslat
      ,output  [DFI_TPHY_WRCSLAT_WIDTH-1:0]   regmux_ddrc_dfi_tphy_wrcslat



      ,output [T_RFMPB_WIDTH-1:0] regmux_ddrc_t_rfmpb

      ,output  [HPR_MAX_STARVE_WIDTH-1:0] regmux_ddrc_hpr_max_starve
      ,output  [HPR_XACT_RUN_LENGTH_WIDTH-1:0] regmux_ddrc_hpr_xact_run_length
      ,output  [LPR_MAX_STARVE_WIDTH-1:0] regmux_ddrc_lpr_max_starve
      ,output  [LPR_XACT_RUN_LENGTH_WIDTH-1:0] regmux_ddrc_lpr_xact_run_length
      ,output  [W_MAX_STARVE_WIDTH-1:0] regmux_ddrc_w_max_starve
      ,output  [W_XACT_RUN_LENGTH_WIDTH-1:0] regmux_ddrc_w_xact_run_length

      ,output  [PAGECLOSE_TIMER_WIDTH-1:0] regmux_ddrc_pageclose_timer
      ,output  [RDWR_IDLE_GAP_WIDTH-1:0] regmux_ddrc_rdwr_idle_gap


      ,output   regmux_ddrc_rd_link_ecc_enable
      ,output   regmux_ddrc_wr_link_ecc_enable
    );

localparam  FREQ_NUM = `UMCTL2_FREQUENCY_NUM;

  ///////////
  // Wires //
  ///////////

// For frequency selection
wire    [TARGET_FREQUENCY_WIDTH - 1:0]   i_target_frequency;
wire    [TARGET_FREQUENCY_WIDTH - 1:0]   regmux_ddrc_target_frequency_init;

wire  [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]        i_regmux_ddrc_dfi_t_ctrlupd_interval_type1[0:FREQ_NUM-1];
wire  [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]   i_regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit[0:FREQ_NUM-1];
wire                                                  i_regmux_ddrc_ppt2_en[0:FREQ_NUM-1];
wire                                                  i_regmux_ddrc_ppt2_override[0:FREQ_NUM-1];
wire                                                  i_regmux_ddrc_ctrlupd_after_dqsosc[0:FREQ_NUM-1];

wire   [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0]  i_regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024[0:FREQ_NUM-1];
wire   [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0]  i_regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024[0:FREQ_NUM-1];
wire   [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]   i_regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8[0:FREQ_NUM-1];
wire   [HW_LP_IDLE_X32_WIDTH-1:0] i_regmux_ddrc_hw_lp_idle_x32[0:FREQ_NUM-1];

wire            i_regmux_ddrc_frequency_ratio[0:FREQ_NUM-1];

wire [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] i_regmux_ddrc_refresh_timer0_start_value_x32[0:FREQ_NUM-1];
wire [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] i_regmux_ddrc_refresh_timer1_start_value_x32[0:FREQ_NUM-1];

// DERATEVAL0
wire  [DERATED_T_RCD_WIDTH-1:0]     i_regmux_ddrc_derated_t_rcd [0:FREQ_NUM-1];
wire  [DERATED_T_RAS_MIN_WIDTH-1:0] i_regmux_ddrc_derated_t_ras_min [0:FREQ_NUM-1];
wire  [DERATED_T_RP_WIDTH-1:0]      i_regmux_ddrc_derated_t_rp [0:FREQ_NUM-1];
wire  [DERATED_T_RRD_WIDTH-1:0]     i_regmux_ddrc_derated_t_rrd [0:FREQ_NUM-1];
// DERATEVAL1
wire  [DERATED_T_RC_WIDTH-1:0]      i_regmux_ddrc_derated_t_rc [0:FREQ_NUM-1];
wire  [DERATED_T_RCD_WIDTH-1:0]     i_regmux_ddrc_derated_t_rcd_write [0:FREQ_NUM-1];
// DERATEINT
wire    [MR4_READ_INTERVAL_WIDTH-1:0]  i_regmux_ddrc_mr4_read_interval [0:FREQ_NUM-1];
// PWRTMG
wire    [POWERDOWN_TO_X32_WIDTH-1:0]   i_regmux_ddrc_powerdown_to_x32[0:FREQ_NUM-1];
wire    [SELFREF_TO_X32_WIDTH-1:0]   i_regmux_ddrc_selfref_to_x32[0:FREQ_NUM-1];
// HWFFCEX
// RFSHCTL0
wire    [REFRESH_MARGIN_WIDTH-1:0]        i_regmux_ddrc_refresh_margin [0:FREQ_NUM-1];
wire    [REFRESH_TO_X1_X32_WIDTH-1:0]     i_regmux_ddrc_refresh_to_x1_x32 [0:FREQ_NUM-1];
wire    [REFRESH_TO_AB_X32_WIDTH-1:0]     i_regmux_ddrc_refresh_to_ab_x32 [0:FREQ_NUM-1];
// RFSHTMG
wire                                      i_regmux_ddrc_t_refi_x1_sel [0:FREQ_NUM-1];
wire                                      i_regmux_ddrc_refresh_to_x1_sel [0:FREQ_NUM-1];
wire    [T_REFI_X1_X32_WIDTH-1:0]         i_regmux_ddrc_t_refi_x32 [0:FREQ_NUM-1];
wire    [T_RFC_MIN_WIDTH-1:0]             i_regmux_ddrc_t_rfc_min [0:FREQ_NUM-1];
wire    [T_RFC_MIN_AB_WIDTH-1:0]          i_regmux_ddrc_t_rfc_min_ab [0:FREQ_NUM-1];
wire    [T_PBR2PBR_WIDTH-1:0]             i_regmux_ddrc_t_pbr2pbr [0:FREQ_NUM-1];
wire    [T_PBR2ACT_WIDTH-1:0]             i_regmux_ddrc_t_pbr2act [0:FREQ_NUM-1];
wire    [T_PGM_X1_X1024_WIDTH-1:0]          i_regmux_ddrc_t_pgm_x1_x1024 [0:FREQ_NUM-1];
wire                                        i_regmux_ddrc_t_pgm_x1_sel [0:FREQ_NUM-1];
wire    [T_PGMPST_X32_WIDTH-1:0]            i_regmux_ddrc_t_pgmpst_x32 [0:FREQ_NUM-1];
wire    [T_PGM_EXIT_WIDTH-1:0]              i_regmux_ddrc_t_pgm_exit [0:FREQ_NUM-1];
// INIT3
wire    [15:0]  i_regmux_ddrc_mr [0:FREQ_NUM-1];
wire    [15:0]  i_regmux_ddrc_emr [0:FREQ_NUM-1];
// INIT4
wire    [15:0]  i_regmux_ddrc_emr2 [0:FREQ_NUM-1];
wire    [15:0]  i_regmux_ddrc_emr3 [0:FREQ_NUM-1];
// INIT6
wire    [15:0]  i_regmux_ddrc_mr4 [0:FREQ_NUM-1];
wire    [15:0]  i_regmux_ddrc_mr5 [0:FREQ_NUM-1];
// INIT7
wire    [15:0]  i_regmux_ddrc_mr6 [0:FREQ_NUM-1];
wire    [15:0]  i_regmux_ddrc_mr22 [0:FREQ_NUM-1];
// RANKCTL
wire    [DIFF_RANK_RD_GAP_WIDTH-1:0]   i_regmux_ddrc_diff_rank_rd_gap [0:FREQ_NUM-1];
wire    [DIFF_RANK_WR_GAP_WIDTH-1:0]   i_regmux_ddrc_diff_rank_wr_gap [0:FREQ_NUM-1];
wire    [RD2WR_DR_WIDTH-1:0]   i_regmux_ddrc_rd2wr_dr [0:FREQ_NUM-1];
wire    [WR2RD_DR_WIDTH-1:0]   i_regmux_ddrc_wr2rd_dr [0:FREQ_NUM-1];
wire    [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] i_regmux_ddrc_lpddr4_diff_bank_rwa2pre [0:FREQ_NUM-1];
wire    [WR2PRE_WIDTH-1:0]   i_regmux_ddrc_wr2pre [0:FREQ_NUM-1];
wire    [WRA2PRE_WIDTH-1:0]   i_regmux_ddrc_wra2pre [0:FREQ_NUM-1];
wire    [T_FAW_WIDTH-1:0]   i_regmux_ddrc_t_faw [0:FREQ_NUM-1];
wire    [T_RAS_MAX_WIDTH-1:0]   i_regmux_ddrc_t_ras_max [0:FREQ_NUM-1];
wire    [T_RAS_MIN_WIDTH-1:0]   i_regmux_ddrc_t_ras_min [0:FREQ_NUM-1];
// DRAMSET1TMG1
wire    [T_RCD_WIDTH-1:0]   i_regmux_ddrc_t_rcd_write [0:FREQ_NUM-1];
wire    [T_XP_WIDTH-1:0]   i_regmux_ddrc_t_xp [0:FREQ_NUM-1];
wire    [RD2PRE_WIDTH-1:0]   i_regmux_ddrc_rd2pre [0:FREQ_NUM-1];
wire    [RDA2PRE_WIDTH-1:0]   i_regmux_ddrc_rda2pre [0:FREQ_NUM-1];
wire    [T_RC_WIDTH-1:0]   i_regmux_ddrc_t_rc [0:FREQ_NUM-1];
// DRAMSET1TMG2
wire    [WRITE_LATENCY_WIDTH-1:0]   i_regmux_ddrc_write_latency [0:FREQ_NUM-1];
wire    [READ_LATENCY_WIDTH-1:0]   i_regmux_ddrc_read_latency [0:FREQ_NUM-1];
wire    [RD2WR_WIDTH-1:0]   i_regmux_ddrc_rd2wr [0:FREQ_NUM-1];
wire    [WR2RD_WIDTH-1:0]   i_regmux_ddrc_wr2rd [0:FREQ_NUM-1];
// DRAMSET1TMG3
wire    [WR2MR_WIDTH-1:0]   i_regmux_ddrc_wr2mr [0:FREQ_NUM-1];
wire    [T_MR_WIDTH-1:0]    i_regmux_ddrc_t_mr [0:FREQ_NUM-1];
wire    [RD2MR_WIDTH-1:0]   i_regmux_ddrc_rd2mr [0:FREQ_NUM-1];
// DRAMSET1TMG4
wire    [T_RCD_WIDTH-1:0]   i_regmux_ddrc_t_rcd [0:FREQ_NUM-1];
wire    [T_CCD_WIDTH-1:0]   i_regmux_ddrc_t_ccd [0:FREQ_NUM-1];
wire    [T_RRD_WIDTH-1:0]   i_regmux_ddrc_t_rrd [0:FREQ_NUM-1];
wire    [T_RP_WIDTH-1:0]   i_regmux_ddrc_t_rp [0:FREQ_NUM-1];
// DRAMTMG5
wire    [T_CKSRX_WIDTH-1:0]   i_regmux_ddrc_t_cksrx [0:FREQ_NUM-1];
wire    [T_CKSRE_WIDTH-1:0]   i_regmux_ddrc_t_cksre [0:FREQ_NUM-1];
wire    [T_CKESR_WIDTH-1:0]   i_regmux_ddrc_t_ckesr [0:FREQ_NUM-1];
wire    [T_CKE_WIDTH-1:0]   i_regmux_ddrc_t_cke [0:FREQ_NUM-1];
// DRAMTMG6
wire    [T_CKCSX_WIDTH-1:0]   i_regmux_ddrc_t_ckcsx [0:FREQ_NUM-1];
// DRAMTMG8
wire    [T_CCD_S_WIDTH-1:0]   i_regmux_ddrc_t_ccd_s [0:FREQ_NUM-1];
wire    [T_RRD_S_WIDTH-1:0]   i_regmux_ddrc_t_rrd_s [0:FREQ_NUM-1];
wire    [WR2RD_S_WIDTH-1:0]   i_regmux_ddrc_wr2rd_s [0:FREQ_NUM-1];
wire    [T_CMDCKE_WIDTH-1:0]   i_regmux_ddrc_t_cmdcke [0:FREQ_NUM-1];
wire    [T_PDN_WIDTH-1:0]      i_regmux_ddrc_t_pdn [0:FREQ_NUM-1];
wire    [T_XSR_DSM_X1024_WIDTH-1:0]  i_regmux_ddrc_t_xsr_dsm_x1024 [0:FREQ_NUM-1];
wire    [T_CSH_WIDTH-1:0]      i_regmux_ddrc_t_csh [0:FREQ_NUM-1];
// DRAMTMG13
wire    [ODTLOFF_WIDTH-1:0]   i_regmux_ddrc_odtloff [0:FREQ_NUM-1];
wire    [T_CCD_MW_WIDTH-1:0]   i_regmux_ddrc_t_ccd_mw [0:FREQ_NUM-1];
wire    [T_PPD_WIDTH-1:0]   i_regmux_ddrc_t_ppd [0:FREQ_NUM-1];
// DRAMTMG14
wire    [T_XSR_WIDTH-1:0]  i_regmux_ddrc_t_xsr [0:FREQ_NUM-1];
wire    [T_OSCO_WIDTH-1:0]  i_regmux_ddrc_t_osco [0:FREQ_NUM-1];
wire                                   i_regmux_ddrc_dqsosc_enable [0:FREQ_NUM-1];
wire                                   i_regmux_ddrc_dqsosc_interval_unit [0:FREQ_NUM-1];
wire    [DQSOSC_INTERVAL_WIDTH-1:0]  i_regmux_ddrc_dqsosc_interval [0:FREQ_NUM-1];
// DRAMTMG17
wire    [T_VRCG_ENABLE_WIDTH-1:0]   i_regmux_ddrc_t_vrcg_enable [0:FREQ_NUM-1];
wire    [T_VRCG_DISABLE_WIDTH-1:0]   i_regmux_ddrc_t_vrcg_disable [0:FREQ_NUM-1];
// ZQSET1TMG2
wire    [T_ZQ_STOP_WIDTH-1:0]   i_regmux_ddrc_t_zq_stop [0:FREQ_NUM-1];
wire                            i_regmux_ddrc_dvfsq_enable [0:FREQ_NUM-1];
// ZQCTL0
wire    [T_ZQ_LONG_NOP_WIDTH-1:0]  i_regmux_ddrc_t_zq_long_nop [0:FREQ_NUM-1];
wire    [T_ZQ_SHORT_NOP_WIDTH-1:0]   i_regmux_ddrc_t_zq_short_nop [0:FREQ_NUM-1];
wire    [T_ZQ_RESET_NOP_WIDTH-1:0] i_regmux_ddrc_t_zq_reset_nop[0:FREQ_NUM-1];
wire    [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0] i_regmux_ddrc_t_zq_short_interval_x1024[0:FREQ_NUM-1];
wire   [BANK_ORG_WIDTH-1:0]             i_regmux_ddrc_bank_org[0:FREQ_NUM-1];
wire   [MAX_RD_SYNC_WIDTH-1:0]          i_regmux_ddrc_rd2wr_s[0:FREQ_NUM-1];
wire   [MRR2RD_WIDTH-1:0]               i_regmux_ddrc_mrr2rd[0:FREQ_NUM-1];
wire   [MRR2WR_WIDTH-1:0]               i_regmux_ddrc_mrr2wr[0:FREQ_NUM-1];
wire   [MRR2MRW_WIDTH-1:0]              i_regmux_ddrc_mrr2mrw[0:FREQ_NUM-1];
wire   [WS_OFF2WS_FS_WIDTH-1:0]         i_regmux_ddrc_ws_off2ws_fs[0:FREQ_NUM-1];
wire   [T_WCKSUS_WIDTH-1:0]             i_regmux_ddrc_t_wcksus[0:FREQ_NUM-1];
wire   [WS_FS2WCK_SUS_WIDTH-1:0]        i_regmux_ddrc_ws_fs2wck_sus[0:FREQ_NUM-1];
wire   [MAX_RD_SYNC_WIDTH-1:0]          i_regmux_ddrc_max_rd_sync[0:FREQ_NUM-1];
wire   [MAX_WR_SYNC_WIDTH-1:0]          i_regmux_ddrc_max_wr_sync[0:FREQ_NUM-1];
wire   [DFI_TWCK_DELAY_WIDTH-1:0]       i_regmux_ddrc_dfi_twck_delay[0:FREQ_NUM-1];
wire   [DFI_TWCK_EN_RD_WIDTH-1:0]       i_regmux_ddrc_dfi_twck_en_rd[0:FREQ_NUM-1];
wire   [DFI_TWCK_EN_WR_WIDTH-1:0]       i_regmux_ddrc_dfi_twck_en_wr[0:FREQ_NUM-1];
wire   [DFI_TWCK_EN_FS_WIDTH-1:0]       i_regmux_ddrc_dfi_twck_en_fs[0:FREQ_NUM-1];
wire   [DFI_TWCK_DIS_WIDTH-1:0]         i_regmux_ddrc_dfi_twck_dis[0:FREQ_NUM-1];
wire   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] i_regmux_ddrc_dfi_twck_fast_toggle[0:FREQ_NUM-1];
wire   [DFI_TWCK_TOGGLE_WIDTH-1:0]      i_regmux_ddrc_dfi_twck_toggle[0:FREQ_NUM-1];
wire   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   i_regmux_ddrc_dfi_twck_toggle_cs[0:FREQ_NUM-1];
wire   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] i_regmux_ddrc_dfi_twck_toggle_post[0:FREQ_NUM-1];
wire                                    i_regmux_ddrc_dfi_twck_toggle_post_rd_en[0:FREQ_NUM-1];
wire   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] i_regmux_ddrc_dfi_twck_toggle_post_rd[0:FREQ_NUM-1];
// DFITMG0
wire    [4:0]   i_regmux_ddrc_dfi_t_ctrl_delay [0:FREQ_NUM-1];
wire    [6:0]   i_regmux_ddrc_dfi_t_rddata_en [0:FREQ_NUM-1];
wire    [5:0]   i_regmux_ddrc_dfi_tphy_wrdata [0:FREQ_NUM-1];
wire    [DFI_TPHY_WRLAT_WIDTH-1:0]   i_regmux_ddrc_dfi_tphy_wrlat [0:FREQ_NUM-1];
// DFITMG1
wire    [4:0]   i_regmux_ddrc_dfi_t_wrdata_delay [0:FREQ_NUM-1];
wire    [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  i_regmux_ddrc_dfi_t_dram_clk_disable [0:FREQ_NUM-1];
wire    [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  i_regmux_ddrc_dfi_t_dram_clk_enable [0:FREQ_NUM-1];
// DFITMG2
wire    [6:0]   i_regmux_ddrc_dfi_tphy_rdcslat [0:FREQ_NUM-1];
wire    [DFI_TPHY_WRCSLAT_WIDTH-1:0]   i_regmux_ddrc_dfi_tphy_wrcslat [0:FREQ_NUM-1];






wire  [T_RFMPB_WIDTH-1:0] i_regmux_ddrc_t_rfmpb [0:FREQ_NUM-1];

wire  [HPR_MAX_STARVE_WIDTH-1:0] i_regmux_ddrc_hpr_max_starve [0:FREQ_NUM-1];
wire  [HPR_XACT_RUN_LENGTH_WIDTH-1:0] i_regmux_ddrc_hpr_xact_run_length [0:FREQ_NUM-1];
wire  [LPR_MAX_STARVE_WIDTH-1:0] i_regmux_ddrc_lpr_max_starve [0:FREQ_NUM-1];
wire  [LPR_XACT_RUN_LENGTH_WIDTH-1:0] i_regmux_ddrc_lpr_xact_run_length [0:FREQ_NUM-1];
wire  [W_MAX_STARVE_WIDTH-1:0] i_regmux_ddrc_w_max_starve [0:FREQ_NUM-1];
wire  [W_XACT_RUN_LENGTH_WIDTH-1:0] i_regmux_ddrc_w_xact_run_length [0:FREQ_NUM-1];

wire  [PAGECLOSE_TIMER_WIDTH-1:0] i_regmux_ddrc_pageclose_timer [0:FREQ_NUM-1];
wire  [RDWR_IDLE_GAP_WIDTH-1:0] i_regmux_ddrc_rdwr_idle_gap [0:FREQ_NUM-1];


wire  i_regmux_ddrc_rd_link_ecc_enable [0:FREQ_NUM-1];
wire  i_regmux_ddrc_wr_link_ecc_enable [0:FREQ_NUM-1];

  /////////////
  // REG_MUX //
  /////////////

assign i_target_frequency   = reg_regmux_target_frequency;

assign regmux_ddrc_hwffc_target_frequency        = i_target_frequency;
assign regmux_ddrc_target_frequency         = hwffc_target_freq_en ? hwffc_target_freq      : i_target_frequency;
assign regmux_ddrc_target_frequency_init    = hwffc_target_freq_en ? hwffc_target_freq_init : i_target_frequency;


  /////////////////////
  // Freq0 registers //
  /////////////////////

assign i_regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024[0]     = reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024[0]     = reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0;
assign i_regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8[0]      = reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1[0]         = reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit[0]    = reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0;
assign i_regmux_ddrc_ppt2_en[0]                              = reg_ddrc_ppt2_en_freq0;
assign i_regmux_ddrc_ppt2_override[0]                        = reg_ddrc_ppt2_override_freq0;
assign i_regmux_ddrc_ctrlupd_after_dqsosc[0]                 = reg_ddrc_ctrlupd_after_dqsosc_freq0;

assign i_regmux_ddrc_hw_lp_idle_x32[0]   = reg_ddrc_hw_lp_idle_x32_freq0;

assign i_regmux_ddrc_frequency_ratio[0]       = reg_ddrc_frequency_ratio_freq0;

assign i_regmux_ddrc_refresh_timer0_start_value_x32[0]    = reg_ddrc_refresh_timer0_start_value_x32_freq0;
assign i_regmux_ddrc_refresh_timer1_start_value_x32[0]    = reg_ddrc_refresh_timer1_start_value_x32_freq0;

assign i_regmux_ddrc_derated_t_rcd[0]              = reg_ddrc_derated_t_rcd_freq0;
assign i_regmux_ddrc_derated_t_ras_min[0]          = reg_ddrc_derated_t_ras_min_freq0;
assign i_regmux_ddrc_derated_t_rp[0]               = reg_ddrc_derated_t_rp_freq0;
assign i_regmux_ddrc_derated_t_rrd[0]              = reg_ddrc_derated_t_rrd_freq0;
assign i_regmux_ddrc_derated_t_rc[0]               = reg_ddrc_derated_t_rc_freq0;
assign i_regmux_ddrc_derated_t_rcd_write[0]        = reg_ddrc_derated_t_rcd_write_freq0;
assign i_regmux_ddrc_mr4_read_interval[0]          = reg_ddrc_mr4_read_interval_freq0;
assign i_regmux_ddrc_powerdown_to_x32[0]           = reg_ddrc_powerdown_to_x32_freq0;
assign i_regmux_ddrc_selfref_to_x32[0]             = reg_ddrc_selfref_to_x32_freq0;


assign i_regmux_ddrc_refresh_margin[0]             = reg_ddrc_refresh_margin_freq0;
assign i_regmux_ddrc_refresh_to_x1_x32[0]          = reg_ddrc_refresh_to_x1_x32_freq0;
assign i_regmux_ddrc_refresh_to_ab_x32[0]          = reg_ddrc_refresh_to_ab_x32_freq0;
assign i_regmux_ddrc_t_refi_x1_sel[0]              = reg_ddrc_t_refi_x1_sel_freq0;
assign i_regmux_ddrc_refresh_to_x1_sel[0]          = reg_ddrc_refresh_to_x1_sel_freq0;
assign i_regmux_ddrc_t_refi_x32[0]                 = reg_ddrc_t_refi_x32_freq0;
assign i_regmux_ddrc_t_rfc_min[0]                  = reg_ddrc_t_rfc_min_freq0;
assign i_regmux_ddrc_t_rfc_min_ab[0]               = reg_ddrc_t_rfc_min_ab_freq0;
assign i_regmux_ddrc_t_pbr2pbr[0]                  = reg_ddrc_t_pbr2pbr_freq0;
assign i_regmux_ddrc_t_pbr2act[0]                  = reg_ddrc_t_pbr2act_freq0;
assign i_regmux_ddrc_t_pgm_x1_x1024 [0]            = reg_ddrc_t_pgm_x1_x1024_freq0;
assign i_regmux_ddrc_t_pgm_x1_sel [0]              = reg_ddrc_t_pgm_x1_sel_freq0;
assign i_regmux_ddrc_t_pgmpst_x32 [0]              = reg_ddrc_t_pgmpst_x32_freq0;
assign i_regmux_ddrc_t_pgm_exit [0]                = reg_ddrc_t_pgm_exit_freq0;
assign i_regmux_ddrc_mr[0]                         = reg_ddrc_mr_freq0;
assign i_regmux_ddrc_emr[0]                        = reg_ddrc_emr_freq0;
assign i_regmux_ddrc_emr2[0]                       = reg_ddrc_emr2_freq0;
assign i_regmux_ddrc_emr3[0]                       = reg_ddrc_emr3_freq0;
assign i_regmux_ddrc_mr4[0]                        = reg_ddrc_mr4_freq0;
assign i_regmux_ddrc_mr5[0]                        = reg_ddrc_mr5_freq0;
assign i_regmux_ddrc_mr6[0]                        = reg_ddrc_mr6_freq0;
assign i_regmux_ddrc_mr22[0]                       = reg_ddrc_mr22_freq0;
assign i_regmux_ddrc_diff_rank_rd_gap[0]           = reg_ddrc_diff_rank_rd_gap_freq0;
assign i_regmux_ddrc_diff_rank_wr_gap[0]           = reg_ddrc_diff_rank_wr_gap_freq0;
assign i_regmux_ddrc_rd2wr_dr[0]                   = reg_ddrc_rd2wr_dr_freq0;
assign i_regmux_ddrc_wr2rd_dr[0]                   = reg_ddrc_wr2rd_dr_freq0;
assign i_regmux_ddrc_lpddr4_diff_bank_rwa2pre[0]   = reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0;
assign i_regmux_ddrc_wr2pre[0]                     = reg_ddrc_wr2pre_freq0;
assign i_regmux_ddrc_wra2pre[0]                    = reg_ddrc_wra2pre_freq0;
assign i_regmux_ddrc_t_faw[0]                      = reg_ddrc_t_faw_freq0;
assign i_regmux_ddrc_t_ras_max[0]                  = reg_ddrc_t_ras_max_freq0;
assign i_regmux_ddrc_t_ras_min[0]                  = reg_ddrc_t_ras_min_freq0;
assign i_regmux_ddrc_t_rcd_write[0]                = reg_ddrc_t_rcd_write_freq0;
assign i_regmux_ddrc_t_xp[0]                       = reg_ddrc_t_xp_freq0;
assign i_regmux_ddrc_rd2pre[0]                     = reg_ddrc_rd2pre_freq0;
assign i_regmux_ddrc_rda2pre[0]                    = reg_ddrc_rda2pre_freq0;
assign i_regmux_ddrc_t_rc[0]                       = reg_ddrc_t_rc_freq0;
assign i_regmux_ddrc_write_latency[0]              = reg_ddrc_write_latency_freq0;
assign i_regmux_ddrc_read_latency[0]               = reg_ddrc_read_latency_freq0;
assign i_regmux_ddrc_rd2wr[0]                      = reg_ddrc_rd2wr_freq0;
assign i_regmux_ddrc_wr2rd[0]                      = reg_ddrc_wr2rd_freq0;
assign i_regmux_ddrc_wr2mr[0]                      = reg_ddrc_wr2mr_freq0;
assign i_regmux_ddrc_t_mr[0]                       = reg_ddrc_t_mr_freq0;
assign i_regmux_ddrc_rd2mr[0]                      = reg_ddrc_rd2mr_freq0;
assign i_regmux_ddrc_t_rcd[0]                      = reg_ddrc_t_rcd_freq0;
assign i_regmux_ddrc_t_ccd[0]                      = reg_ddrc_t_ccd_freq0;
assign i_regmux_ddrc_t_rrd[0]                      = reg_ddrc_t_rrd_freq0;
assign i_regmux_ddrc_t_rp[0]                       = reg_ddrc_t_rp_freq0;
assign i_regmux_ddrc_t_cksrx[0]                    = reg_ddrc_t_cksrx_freq0;
assign i_regmux_ddrc_t_cksre[0]                    = reg_ddrc_t_cksre_freq0;
assign i_regmux_ddrc_t_ckesr[0]                    = reg_ddrc_t_ckesr_freq0;
assign i_regmux_ddrc_t_cke[0]                      = reg_ddrc_t_cke_freq0;
assign i_regmux_ddrc_t_ckcsx[0]                    = reg_ddrc_t_ckcsx_freq0;
assign i_regmux_ddrc_t_ccd_s[0]                    = reg_ddrc_t_ccd_s_freq0;
assign i_regmux_ddrc_t_rrd_s[0]                    = reg_ddrc_t_rrd_s_freq0;
assign i_regmux_ddrc_wr2rd_s[0]                    = reg_ddrc_wr2rd_s_freq0;
assign i_regmux_ddrc_t_cmdcke[0]                   = reg_ddrc_t_cmdcke_freq0;
assign i_regmux_ddrc_t_pdn[0]                      = reg_ddrc_t_pdn_freq0;
assign i_regmux_ddrc_t_xsr_dsm_x1024[0]            = reg_ddrc_t_xsr_dsm_x1024_freq0;
assign i_regmux_ddrc_t_csh[0]                      = reg_ddrc_t_csh_freq0;
assign i_regmux_ddrc_odtloff[0]                    = reg_ddrc_odtloff_freq0;
assign i_regmux_ddrc_t_ccd_mw[0]                   = reg_ddrc_t_ccd_mw_freq0;
assign i_regmux_ddrc_t_ppd[0]                      = reg_ddrc_t_ppd_freq0;
assign i_regmux_ddrc_t_xsr[0]                      = reg_ddrc_t_xsr_freq0;
assign i_regmux_ddrc_t_osco[0]                     = reg_ddrc_t_osco_freq0;
assign i_regmux_ddrc_dqsosc_enable[0]              = reg_ddrc_dqsosc_enable_freq0;
assign i_regmux_ddrc_dqsosc_interval_unit[0]       = reg_ddrc_dqsosc_interval_unit_freq0;
assign i_regmux_ddrc_dqsosc_interval[0]            = reg_ddrc_dqsosc_interval_freq0;
assign i_regmux_ddrc_t_vrcg_enable[0]              = reg_ddrc_t_vrcg_enable_freq0;
assign i_regmux_ddrc_t_vrcg_disable[0]             = reg_ddrc_t_vrcg_disable_freq0;
assign i_regmux_ddrc_t_zq_stop[0]                  = reg_ddrc_t_zq_stop_freq0;
assign i_regmux_ddrc_dvfsq_enable[0]               = reg_ddrc_dvfsq_enable_freq0;
assign i_regmux_ddrc_t_zq_long_nop[0]              = reg_ddrc_t_zq_long_nop_freq0;
assign i_regmux_ddrc_t_zq_short_nop[0]             = reg_ddrc_t_zq_short_nop_freq0;
assign i_regmux_ddrc_t_zq_reset_nop[0]             = reg_ddrc_t_zq_reset_nop_freq0;
assign i_regmux_ddrc_t_zq_short_interval_x1024[0]  = reg_ddrc_t_zq_short_interval_x1024_freq0;
assign i_regmux_ddrc_bank_org[0]                   = reg_ddrc_bank_org_freq0;
assign i_regmux_ddrc_rd2wr_s[0]                    = reg_ddrc_rd2wr_s_freq0;
assign i_regmux_ddrc_mrr2rd[0]                     = reg_ddrc_mrr2rd_freq0;
assign i_regmux_ddrc_mrr2wr[0]                     = reg_ddrc_mrr2wr_freq0;
assign i_regmux_ddrc_mrr2mrw[0]                    = reg_ddrc_mrr2mrw_freq0;
assign i_regmux_ddrc_ws_off2ws_fs[0]               = reg_ddrc_ws_off2ws_fs_freq0;
assign i_regmux_ddrc_t_wcksus[0]                   = reg_ddrc_t_wcksus_freq0;
assign i_regmux_ddrc_ws_fs2wck_sus[0]              = reg_ddrc_ws_fs2wck_sus_freq0;
assign i_regmux_ddrc_max_rd_sync[0]                = reg_ddrc_max_rd_sync_freq0;
assign i_regmux_ddrc_max_wr_sync[0]                = reg_ddrc_max_wr_sync_freq0;
assign i_regmux_ddrc_dfi_twck_delay[0]             = reg_ddrc_dfi_twck_delay_freq0;
assign i_regmux_ddrc_dfi_twck_en_rd[0]             = reg_ddrc_dfi_twck_en_rd_freq0;
assign i_regmux_ddrc_dfi_twck_en_wr[0]             = reg_ddrc_dfi_twck_en_wr_freq0;
assign i_regmux_ddrc_dfi_twck_en_fs[0]             = reg_ddrc_dfi_twck_en_fs_freq0;
assign i_regmux_ddrc_dfi_twck_dis[0]               = reg_ddrc_dfi_twck_dis_freq0;
assign i_regmux_ddrc_dfi_twck_fast_toggle[0]       = reg_ddrc_dfi_twck_fast_toggle_freq0;
assign i_regmux_ddrc_dfi_twck_toggle[0]            = reg_ddrc_dfi_twck_toggle_freq0;
assign i_regmux_ddrc_dfi_twck_toggle_cs[0]         = reg_ddrc_dfi_twck_toggle_cs_freq0;
assign i_regmux_ddrc_dfi_twck_toggle_post[0]       = reg_ddrc_dfi_twck_toggle_post_freq0;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd_en[0] = reg_ddrc_dfi_twck_toggle_post_rd_en_freq0;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd[0]    = reg_ddrc_dfi_twck_toggle_post_rd_freq0;
assign i_regmux_ddrc_dfi_t_ctrl_delay[0]           = reg_ddrc_dfi_t_ctrl_delay_freq0;
assign i_regmux_ddrc_dfi_t_rddata_en[0]            = reg_ddrc_dfi_t_rddata_en_freq0;
assign i_regmux_ddrc_dfi_tphy_wrdata[0]            = reg_ddrc_dfi_tphy_wrdata_freq0;
assign i_regmux_ddrc_dfi_tphy_wrlat[0]             = reg_ddrc_dfi_tphy_wrlat_freq0;
assign i_regmux_ddrc_dfi_t_wrdata_delay[0]         = reg_ddrc_dfi_t_wrdata_delay_freq0;
assign i_regmux_ddrc_dfi_t_dram_clk_disable[0]     = reg_ddrc_dfi_t_dram_clk_disable_freq0;
assign i_regmux_ddrc_dfi_t_dram_clk_enable[0]      = reg_ddrc_dfi_t_dram_clk_enable_freq0;
assign i_regmux_ddrc_dfi_tphy_rdcslat[0]           = reg_ddrc_dfi_tphy_rdcslat_freq0;
assign i_regmux_ddrc_dfi_tphy_wrcslat[0]           = reg_ddrc_dfi_tphy_wrcslat_freq0;



assign i_regmux_ddrc_t_rfmpb[0]     = reg_ddrc_t_rfmpb_freq0;

assign i_regmux_ddrc_hpr_max_starve[0]             = reg_ddrc_hpr_max_starve_freq0;
assign i_regmux_ddrc_hpr_xact_run_length[0]        = reg_ddrc_hpr_xact_run_length_freq0;
assign i_regmux_ddrc_lpr_max_starve[0]             = reg_ddrc_lpr_max_starve_freq0;
assign i_regmux_ddrc_lpr_xact_run_length[0]        = reg_ddrc_lpr_xact_run_length_freq0;
assign i_regmux_ddrc_w_max_starve[0]               = reg_ddrc_w_max_starve_freq0;
assign i_regmux_ddrc_w_xact_run_length[0]          = reg_ddrc_w_xact_run_length_freq0;

assign i_regmux_ddrc_pageclose_timer[0]            = reg_ddrc_pageclose_timer_freq0;
assign i_regmux_ddrc_rdwr_idle_gap[0]              = reg_ddrc_rdwr_idle_gap_freq0;


assign i_regmux_ddrc_rd_link_ecc_enable[0]  = reg_ddrc_rd_link_ecc_enable_freq0;
assign i_regmux_ddrc_wr_link_ecc_enable[0]  = reg_ddrc_wr_link_ecc_enable_freq0;

  /////////////////////
  // Freq1 registers //
  /////////////////////

assign i_regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024[1]     = reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024[1]     = reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1;
assign i_regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8[1]      = reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1[1]         = reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit[1]    = reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1;
assign i_regmux_ddrc_ppt2_en[1]                              = reg_ddrc_ppt2_en_freq1;
assign i_regmux_ddrc_ppt2_override[1]                        = reg_ddrc_ppt2_override_freq1;
assign i_regmux_ddrc_ctrlupd_after_dqsosc[1]                 = reg_ddrc_ctrlupd_after_dqsosc_freq1;

assign i_regmux_ddrc_hw_lp_idle_x32[1]   = reg_ddrc_hw_lp_idle_x32_freq1;

assign i_regmux_ddrc_frequency_ratio[1]       = reg_ddrc_frequency_ratio_freq1;

assign i_regmux_ddrc_refresh_timer0_start_value_x32[1]    = reg_ddrc_refresh_timer0_start_value_x32_freq1;
assign i_regmux_ddrc_refresh_timer1_start_value_x32[1]    = reg_ddrc_refresh_timer1_start_value_x32_freq1;

assign i_regmux_ddrc_derated_t_rcd[1]              = reg_ddrc_derated_t_rcd_freq1;
assign i_regmux_ddrc_derated_t_ras_min[1]          = reg_ddrc_derated_t_ras_min_freq1;
assign i_regmux_ddrc_derated_t_rp[1]               = reg_ddrc_derated_t_rp_freq1;
assign i_regmux_ddrc_derated_t_rrd[1]              = reg_ddrc_derated_t_rrd_freq1;
assign i_regmux_ddrc_derated_t_rc[1]               = reg_ddrc_derated_t_rc_freq1;
assign i_regmux_ddrc_derated_t_rcd_write[1]        = reg_ddrc_derated_t_rcd_write_freq1;
assign i_regmux_ddrc_mr4_read_interval[1]          = reg_ddrc_mr4_read_interval_freq1;
assign i_regmux_ddrc_powerdown_to_x32[1]           = reg_ddrc_powerdown_to_x32_freq1;
assign i_regmux_ddrc_selfref_to_x32[1]             = reg_ddrc_selfref_to_x32_freq1;


assign i_regmux_ddrc_refresh_margin[1]             = reg_ddrc_refresh_margin_freq1;
assign i_regmux_ddrc_refresh_to_x1_x32[1]          = reg_ddrc_refresh_to_x1_x32_freq1;
assign i_regmux_ddrc_refresh_to_ab_x32[1]          = reg_ddrc_refresh_to_ab_x32_freq1;
assign i_regmux_ddrc_t_refi_x1_sel[1]              = reg_ddrc_t_refi_x1_sel_freq1;
assign i_regmux_ddrc_refresh_to_x1_sel[1]          = reg_ddrc_refresh_to_x1_sel_freq1;
assign i_regmux_ddrc_t_refi_x32[1]                 = reg_ddrc_t_refi_x32_freq1;
assign i_regmux_ddrc_t_rfc_min[1]                  = reg_ddrc_t_rfc_min_freq1;
assign i_regmux_ddrc_t_rfc_min_ab[1]               = reg_ddrc_t_rfc_min_ab_freq1;
assign i_regmux_ddrc_t_pbr2pbr[1]                  = reg_ddrc_t_pbr2pbr_freq1;
assign i_regmux_ddrc_t_pbr2act[1]                  = reg_ddrc_t_pbr2act_freq1;
assign i_regmux_ddrc_t_pgm_x1_x1024 [1]            = reg_ddrc_t_pgm_x1_x1024_freq1;
assign i_regmux_ddrc_t_pgm_x1_sel [1]              = reg_ddrc_t_pgm_x1_sel_freq1;
assign i_regmux_ddrc_t_pgmpst_x32 [1]              = reg_ddrc_t_pgmpst_x32_freq1;
assign i_regmux_ddrc_t_pgm_exit [1]                = reg_ddrc_t_pgm_exit_freq1;
assign i_regmux_ddrc_mr[1]                         = reg_ddrc_mr_freq1;
assign i_regmux_ddrc_emr[1]                        = reg_ddrc_emr_freq1;
assign i_regmux_ddrc_emr2[1]                       = reg_ddrc_emr2_freq1;
assign i_regmux_ddrc_emr3[1]                       = reg_ddrc_emr3_freq1;
assign i_regmux_ddrc_mr4[1]                        = reg_ddrc_mr4_freq1;
assign i_regmux_ddrc_mr5[1]                        = reg_ddrc_mr5_freq1;
assign i_regmux_ddrc_mr6[1]                        = reg_ddrc_mr6_freq1;
assign i_regmux_ddrc_mr22[1]                       = reg_ddrc_mr22_freq1;
assign i_regmux_ddrc_diff_rank_rd_gap[1]           = reg_ddrc_diff_rank_rd_gap_freq1;
assign i_regmux_ddrc_diff_rank_wr_gap[1]           = reg_ddrc_diff_rank_wr_gap_freq1;
assign i_regmux_ddrc_rd2wr_dr[1]                   = reg_ddrc_rd2wr_dr_freq1;
assign i_regmux_ddrc_wr2rd_dr[1]                   = reg_ddrc_wr2rd_dr_freq1;
assign i_regmux_ddrc_lpddr4_diff_bank_rwa2pre[1]   = reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1;
assign i_regmux_ddrc_wr2pre[1]                     = reg_ddrc_wr2pre_freq1;
assign i_regmux_ddrc_wra2pre[1]                    = reg_ddrc_wra2pre_freq1;
assign i_regmux_ddrc_t_faw[1]                      = reg_ddrc_t_faw_freq1;
assign i_regmux_ddrc_t_ras_max[1]                  = reg_ddrc_t_ras_max_freq1;
assign i_regmux_ddrc_t_ras_min[1]                  = reg_ddrc_t_ras_min_freq1;
assign i_regmux_ddrc_t_rcd_write[1]                = reg_ddrc_t_rcd_write_freq1;
assign i_regmux_ddrc_t_xp[1]                       = reg_ddrc_t_xp_freq1;
assign i_regmux_ddrc_rd2pre[1]                     = reg_ddrc_rd2pre_freq1;
assign i_regmux_ddrc_rda2pre[1]                    = reg_ddrc_rda2pre_freq1;
assign i_regmux_ddrc_t_rc[1]                       = reg_ddrc_t_rc_freq1;
assign i_regmux_ddrc_write_latency[1]              = reg_ddrc_write_latency_freq1;
assign i_regmux_ddrc_read_latency[1]               = reg_ddrc_read_latency_freq1;
assign i_regmux_ddrc_rd2wr[1]                      = reg_ddrc_rd2wr_freq1;
assign i_regmux_ddrc_wr2rd[1]                      = reg_ddrc_wr2rd_freq1;
assign i_regmux_ddrc_wr2mr[1]                      = reg_ddrc_wr2mr_freq1;
assign i_regmux_ddrc_t_mr[1]                       = reg_ddrc_t_mr_freq1;
assign i_regmux_ddrc_rd2mr[1]                      = reg_ddrc_rd2mr_freq1;
assign i_regmux_ddrc_t_rcd[1]                      = reg_ddrc_t_rcd_freq1;
assign i_regmux_ddrc_t_ccd[1]                      = reg_ddrc_t_ccd_freq1;
assign i_regmux_ddrc_t_rrd[1]                      = reg_ddrc_t_rrd_freq1;
assign i_regmux_ddrc_t_rp[1]                       = reg_ddrc_t_rp_freq1;
assign i_regmux_ddrc_t_cksrx[1]                    = reg_ddrc_t_cksrx_freq1;
assign i_regmux_ddrc_t_cksre[1]                    = reg_ddrc_t_cksre_freq1;
assign i_regmux_ddrc_t_ckesr[1]                    = reg_ddrc_t_ckesr_freq1;
assign i_regmux_ddrc_t_cke[1]                      = reg_ddrc_t_cke_freq1;
assign i_regmux_ddrc_t_ckcsx[1]                    = reg_ddrc_t_ckcsx_freq1;
assign i_regmux_ddrc_t_ccd_s[1]                    = reg_ddrc_t_ccd_s_freq1;
assign i_regmux_ddrc_t_rrd_s[1]                    = reg_ddrc_t_rrd_s_freq1;
assign i_regmux_ddrc_wr2rd_s[1]                    = reg_ddrc_wr2rd_s_freq1;
assign i_regmux_ddrc_t_cmdcke[1]                   = reg_ddrc_t_cmdcke_freq1;
assign i_regmux_ddrc_t_pdn[1]                      = reg_ddrc_t_pdn_freq1;
assign i_regmux_ddrc_t_xsr_dsm_x1024[1]            = reg_ddrc_t_xsr_dsm_x1024_freq1;
assign i_regmux_ddrc_t_csh[1]                      = reg_ddrc_t_csh_freq1;
assign i_regmux_ddrc_odtloff[1]                    = reg_ddrc_odtloff_freq1;
assign i_regmux_ddrc_t_ccd_mw[1]                   = reg_ddrc_t_ccd_mw_freq1;
assign i_regmux_ddrc_t_ppd[1]                      = reg_ddrc_t_ppd_freq1;
assign i_regmux_ddrc_t_xsr[1]                      = reg_ddrc_t_xsr_freq1;
assign i_regmux_ddrc_t_osco[1]                     = reg_ddrc_t_osco_freq1;
assign i_regmux_ddrc_dqsosc_enable[1]              = reg_ddrc_dqsosc_enable_freq1;
assign i_regmux_ddrc_dqsosc_interval_unit[1]       = reg_ddrc_dqsosc_interval_unit_freq1;
assign i_regmux_ddrc_dqsosc_interval[1]            = reg_ddrc_dqsosc_interval_freq1;
assign i_regmux_ddrc_t_vrcg_enable[1]              = reg_ddrc_t_vrcg_enable_freq1;
assign i_regmux_ddrc_t_vrcg_disable[1]             = reg_ddrc_t_vrcg_disable_freq1;
assign i_regmux_ddrc_t_zq_stop[1]                  = reg_ddrc_t_zq_stop_freq1;
assign i_regmux_ddrc_dvfsq_enable[1]               = reg_ddrc_dvfsq_enable_freq1;
assign i_regmux_ddrc_t_zq_long_nop[1]              = reg_ddrc_t_zq_long_nop_freq1;
assign i_regmux_ddrc_t_zq_short_nop[1]             = reg_ddrc_t_zq_short_nop_freq1;
assign i_regmux_ddrc_t_zq_reset_nop[1]             = reg_ddrc_t_zq_reset_nop_freq1;
assign i_regmux_ddrc_t_zq_short_interval_x1024[1]  = reg_ddrc_t_zq_short_interval_x1024_freq1;
assign i_regmux_ddrc_bank_org[1]                   = reg_ddrc_bank_org_freq1;
assign i_regmux_ddrc_rd2wr_s[1]                    = reg_ddrc_rd2wr_s_freq1;
assign i_regmux_ddrc_mrr2rd[1]                     = reg_ddrc_mrr2rd_freq1;
assign i_regmux_ddrc_mrr2wr[1]                     = reg_ddrc_mrr2wr_freq1;
assign i_regmux_ddrc_mrr2mrw[1]                    = reg_ddrc_mrr2mrw_freq1;
assign i_regmux_ddrc_ws_off2ws_fs[1]               = reg_ddrc_ws_off2ws_fs_freq1;
assign i_regmux_ddrc_t_wcksus[1]                   = reg_ddrc_t_wcksus_freq1;
assign i_regmux_ddrc_ws_fs2wck_sus[1]              = reg_ddrc_ws_fs2wck_sus_freq1;
assign i_regmux_ddrc_max_rd_sync[1]                = reg_ddrc_max_rd_sync_freq1;
assign i_regmux_ddrc_max_wr_sync[1]                = reg_ddrc_max_wr_sync_freq1;
assign i_regmux_ddrc_dfi_twck_delay[1]             = reg_ddrc_dfi_twck_delay_freq1;
assign i_regmux_ddrc_dfi_twck_en_rd[1]             = reg_ddrc_dfi_twck_en_rd_freq1;
assign i_regmux_ddrc_dfi_twck_en_wr[1]             = reg_ddrc_dfi_twck_en_wr_freq1;
assign i_regmux_ddrc_dfi_twck_en_fs[1]             = reg_ddrc_dfi_twck_en_fs_freq1;
assign i_regmux_ddrc_dfi_twck_dis[1]               = reg_ddrc_dfi_twck_dis_freq1;
assign i_regmux_ddrc_dfi_twck_fast_toggle[1]       = reg_ddrc_dfi_twck_fast_toggle_freq1;
assign i_regmux_ddrc_dfi_twck_toggle[1]            = reg_ddrc_dfi_twck_toggle_freq1;
assign i_regmux_ddrc_dfi_twck_toggle_cs[1]         = reg_ddrc_dfi_twck_toggle_cs_freq1;
assign i_regmux_ddrc_dfi_twck_toggle_post[1]       = reg_ddrc_dfi_twck_toggle_post_freq1;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd_en[1] = reg_ddrc_dfi_twck_toggle_post_rd_en_freq1;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd[1]    = reg_ddrc_dfi_twck_toggle_post_rd_freq1;
assign i_regmux_ddrc_dfi_t_ctrl_delay[1]           = reg_ddrc_dfi_t_ctrl_delay_freq1;
assign i_regmux_ddrc_dfi_t_rddata_en[1]            = reg_ddrc_dfi_t_rddata_en_freq1;
assign i_regmux_ddrc_dfi_tphy_wrdata[1]            = reg_ddrc_dfi_tphy_wrdata_freq1;
assign i_regmux_ddrc_dfi_tphy_wrlat[1]             = reg_ddrc_dfi_tphy_wrlat_freq1;
assign i_regmux_ddrc_dfi_t_wrdata_delay[1]         = reg_ddrc_dfi_t_wrdata_delay_freq1;
assign i_regmux_ddrc_dfi_t_dram_clk_disable[1]     = reg_ddrc_dfi_t_dram_clk_disable_freq1;
assign i_regmux_ddrc_dfi_t_dram_clk_enable[1]      = reg_ddrc_dfi_t_dram_clk_enable_freq1;
assign i_regmux_ddrc_dfi_tphy_rdcslat[1]           = reg_ddrc_dfi_tphy_rdcslat_freq1;
assign i_regmux_ddrc_dfi_tphy_wrcslat[1]           = reg_ddrc_dfi_tphy_wrcslat_freq1;



assign i_regmux_ddrc_t_rfmpb[1]     = reg_ddrc_t_rfmpb_freq1;

assign i_regmux_ddrc_hpr_max_starve[1]             = reg_ddrc_hpr_max_starve_freq1;
assign i_regmux_ddrc_hpr_xact_run_length[1]        = reg_ddrc_hpr_xact_run_length_freq1;
assign i_regmux_ddrc_lpr_max_starve[1]             = reg_ddrc_lpr_max_starve_freq1;
assign i_regmux_ddrc_lpr_xact_run_length[1]        = reg_ddrc_lpr_xact_run_length_freq1;
assign i_regmux_ddrc_w_max_starve[1]               = reg_ddrc_w_max_starve_freq1;
assign i_regmux_ddrc_w_xact_run_length[1]          = reg_ddrc_w_xact_run_length_freq1;

assign i_regmux_ddrc_pageclose_timer[1]            = reg_ddrc_pageclose_timer_freq1;
assign i_regmux_ddrc_rdwr_idle_gap[1]              = reg_ddrc_rdwr_idle_gap_freq1;


assign i_regmux_ddrc_rd_link_ecc_enable[1]  = reg_ddrc_rd_link_ecc_enable_freq1;
assign i_regmux_ddrc_wr_link_ecc_enable[1]  = reg_ddrc_wr_link_ecc_enable_freq1;

  /////////////////////
  // Freq2 registers //
  /////////////////////

assign i_regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024[2]     = reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024[2]     = reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2;
assign i_regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8[2]      = reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1[2]         = reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit[2]    = reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2;
assign i_regmux_ddrc_ppt2_en[2]                              = reg_ddrc_ppt2_en_freq2;
assign i_regmux_ddrc_ppt2_override[2]                        = reg_ddrc_ppt2_override_freq2;
assign i_regmux_ddrc_ctrlupd_after_dqsosc[2]                 = reg_ddrc_ctrlupd_after_dqsosc_freq2;

assign i_regmux_ddrc_hw_lp_idle_x32[2]   = reg_ddrc_hw_lp_idle_x32_freq2;

assign i_regmux_ddrc_frequency_ratio[2]       = reg_ddrc_frequency_ratio_freq2;

assign i_regmux_ddrc_refresh_timer0_start_value_x32[2]    = reg_ddrc_refresh_timer0_start_value_x32_freq2;
assign i_regmux_ddrc_refresh_timer1_start_value_x32[2]    = reg_ddrc_refresh_timer1_start_value_x32_freq2;

assign i_regmux_ddrc_derated_t_rcd[2]              = reg_ddrc_derated_t_rcd_freq2;
assign i_regmux_ddrc_derated_t_ras_min[2]          = reg_ddrc_derated_t_ras_min_freq2;
assign i_regmux_ddrc_derated_t_rp[2]               = reg_ddrc_derated_t_rp_freq2;
assign i_regmux_ddrc_derated_t_rrd[2]              = reg_ddrc_derated_t_rrd_freq2;
assign i_regmux_ddrc_derated_t_rc[2]               = reg_ddrc_derated_t_rc_freq2;
assign i_regmux_ddrc_derated_t_rcd_write[2]        = reg_ddrc_derated_t_rcd_write_freq2;
assign i_regmux_ddrc_mr4_read_interval[2]          = reg_ddrc_mr4_read_interval_freq2;
assign i_regmux_ddrc_powerdown_to_x32[2]           = reg_ddrc_powerdown_to_x32_freq2;
assign i_regmux_ddrc_selfref_to_x32[2]             = reg_ddrc_selfref_to_x32_freq2;


assign i_regmux_ddrc_refresh_margin[2]             = reg_ddrc_refresh_margin_freq2;
assign i_regmux_ddrc_refresh_to_x1_x32[2]          = reg_ddrc_refresh_to_x1_x32_freq2;
assign i_regmux_ddrc_refresh_to_ab_x32[2]          = reg_ddrc_refresh_to_ab_x32_freq2;
assign i_regmux_ddrc_t_refi_x1_sel[2]              = reg_ddrc_t_refi_x1_sel_freq2;
assign i_regmux_ddrc_refresh_to_x1_sel[2]          = reg_ddrc_refresh_to_x1_sel_freq2;
assign i_regmux_ddrc_t_refi_x32[2]                 = reg_ddrc_t_refi_x32_freq2;
assign i_regmux_ddrc_t_rfc_min[2]                  = reg_ddrc_t_rfc_min_freq2;
assign i_regmux_ddrc_t_rfc_min_ab[2]               = reg_ddrc_t_rfc_min_ab_freq2;
assign i_regmux_ddrc_t_pbr2pbr[2]                  = reg_ddrc_t_pbr2pbr_freq2;
assign i_regmux_ddrc_t_pbr2act[2]                  = reg_ddrc_t_pbr2act_freq2;
assign i_regmux_ddrc_t_pgm_x1_x1024 [2]            = reg_ddrc_t_pgm_x1_x1024_freq2;
assign i_regmux_ddrc_t_pgm_x1_sel [2]              = reg_ddrc_t_pgm_x1_sel_freq2;
assign i_regmux_ddrc_t_pgmpst_x32 [2]              = reg_ddrc_t_pgmpst_x32_freq2;
assign i_regmux_ddrc_t_pgm_exit [2]                = reg_ddrc_t_pgm_exit_freq2;
assign i_regmux_ddrc_mr[2]                         = reg_ddrc_mr_freq2;
assign i_regmux_ddrc_emr[2]                        = reg_ddrc_emr_freq2;
assign i_regmux_ddrc_emr2[2]                       = reg_ddrc_emr2_freq2;
assign i_regmux_ddrc_emr3[2]                       = reg_ddrc_emr3_freq2;
assign i_regmux_ddrc_mr4[2]                        = reg_ddrc_mr4_freq2;
assign i_regmux_ddrc_mr5[2]                        = reg_ddrc_mr5_freq2;
assign i_regmux_ddrc_mr6[2]                        = reg_ddrc_mr6_freq2;
assign i_regmux_ddrc_mr22[2]                       = reg_ddrc_mr22_freq2;
assign i_regmux_ddrc_diff_rank_rd_gap[2]           = reg_ddrc_diff_rank_rd_gap_freq2;
assign i_regmux_ddrc_diff_rank_wr_gap[2]           = reg_ddrc_diff_rank_wr_gap_freq2;
assign i_regmux_ddrc_rd2wr_dr[2]                   = reg_ddrc_rd2wr_dr_freq2;
assign i_regmux_ddrc_wr2rd_dr[2]                   = reg_ddrc_wr2rd_dr_freq2;
assign i_regmux_ddrc_lpddr4_diff_bank_rwa2pre[2]   = reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2;
assign i_regmux_ddrc_wr2pre[2]                     = reg_ddrc_wr2pre_freq2;
assign i_regmux_ddrc_wra2pre[2]                    = reg_ddrc_wra2pre_freq2;
assign i_regmux_ddrc_t_faw[2]                      = reg_ddrc_t_faw_freq2;
assign i_regmux_ddrc_t_ras_max[2]                  = reg_ddrc_t_ras_max_freq2;
assign i_regmux_ddrc_t_ras_min[2]                  = reg_ddrc_t_ras_min_freq2;
assign i_regmux_ddrc_t_rcd_write[2]                = reg_ddrc_t_rcd_write_freq2;
assign i_regmux_ddrc_t_xp[2]                       = reg_ddrc_t_xp_freq2;
assign i_regmux_ddrc_rd2pre[2]                     = reg_ddrc_rd2pre_freq2;
assign i_regmux_ddrc_rda2pre[2]                    = reg_ddrc_rda2pre_freq2;
assign i_regmux_ddrc_t_rc[2]                       = reg_ddrc_t_rc_freq2;
assign i_regmux_ddrc_write_latency[2]              = reg_ddrc_write_latency_freq2;
assign i_regmux_ddrc_read_latency[2]               = reg_ddrc_read_latency_freq2;
assign i_regmux_ddrc_rd2wr[2]                      = reg_ddrc_rd2wr_freq2;
assign i_regmux_ddrc_wr2rd[2]                      = reg_ddrc_wr2rd_freq2;
assign i_regmux_ddrc_wr2mr[2]                      = reg_ddrc_wr2mr_freq2;
assign i_regmux_ddrc_t_mr[2]                       = reg_ddrc_t_mr_freq2;
assign i_regmux_ddrc_rd2mr[2]                      = reg_ddrc_rd2mr_freq2;
assign i_regmux_ddrc_t_rcd[2]                      = reg_ddrc_t_rcd_freq2;
assign i_regmux_ddrc_t_ccd[2]                      = reg_ddrc_t_ccd_freq2;
assign i_regmux_ddrc_t_rrd[2]                      = reg_ddrc_t_rrd_freq2;
assign i_regmux_ddrc_t_rp[2]                       = reg_ddrc_t_rp_freq2;
assign i_regmux_ddrc_t_cksrx[2]                    = reg_ddrc_t_cksrx_freq2;
assign i_regmux_ddrc_t_cksre[2]                    = reg_ddrc_t_cksre_freq2;
assign i_regmux_ddrc_t_ckesr[2]                    = reg_ddrc_t_ckesr_freq2;
assign i_regmux_ddrc_t_cke[2]                      = reg_ddrc_t_cke_freq2;
assign i_regmux_ddrc_t_ckcsx[2]                    = reg_ddrc_t_ckcsx_freq2;
assign i_regmux_ddrc_t_ccd_s[2]                    = reg_ddrc_t_ccd_s_freq2;
assign i_regmux_ddrc_t_rrd_s[2]                    = reg_ddrc_t_rrd_s_freq2;
assign i_regmux_ddrc_wr2rd_s[2]                    = reg_ddrc_wr2rd_s_freq2;
assign i_regmux_ddrc_t_cmdcke[2]                   = reg_ddrc_t_cmdcke_freq2;
assign i_regmux_ddrc_t_pdn[2]                      = reg_ddrc_t_pdn_freq2;
assign i_regmux_ddrc_t_xsr_dsm_x1024[2]            = reg_ddrc_t_xsr_dsm_x1024_freq2;
assign i_regmux_ddrc_t_csh[2]                      = reg_ddrc_t_csh_freq2;
assign i_regmux_ddrc_odtloff[2]                    = reg_ddrc_odtloff_freq2;
assign i_regmux_ddrc_t_ccd_mw[2]                   = reg_ddrc_t_ccd_mw_freq2;
assign i_regmux_ddrc_t_ppd[2]                      = reg_ddrc_t_ppd_freq2;
assign i_regmux_ddrc_t_xsr[2]                      = reg_ddrc_t_xsr_freq2;
assign i_regmux_ddrc_t_osco[2]                     = reg_ddrc_t_osco_freq2;
assign i_regmux_ddrc_dqsosc_enable[2]              = reg_ddrc_dqsosc_enable_freq2;
assign i_regmux_ddrc_dqsosc_interval_unit[2]       = reg_ddrc_dqsosc_interval_unit_freq2;
assign i_regmux_ddrc_dqsosc_interval[2]            = reg_ddrc_dqsosc_interval_freq2;
assign i_regmux_ddrc_t_vrcg_enable[2]              = reg_ddrc_t_vrcg_enable_freq2;
assign i_regmux_ddrc_t_vrcg_disable[2]             = reg_ddrc_t_vrcg_disable_freq2;
assign i_regmux_ddrc_t_zq_stop[2]                  = reg_ddrc_t_zq_stop_freq2;
assign i_regmux_ddrc_dvfsq_enable[2]               = reg_ddrc_dvfsq_enable_freq2;
assign i_regmux_ddrc_t_zq_long_nop[2]              = reg_ddrc_t_zq_long_nop_freq2;
assign i_regmux_ddrc_t_zq_short_nop[2]             = reg_ddrc_t_zq_short_nop_freq2;
assign i_regmux_ddrc_t_zq_reset_nop[2]             = reg_ddrc_t_zq_reset_nop_freq2;
assign i_regmux_ddrc_t_zq_short_interval_x1024[2]  = reg_ddrc_t_zq_short_interval_x1024_freq2;
assign i_regmux_ddrc_bank_org[2]                   = reg_ddrc_bank_org_freq2;
assign i_regmux_ddrc_rd2wr_s[2]                    = reg_ddrc_rd2wr_s_freq2;
assign i_regmux_ddrc_mrr2rd[2]                     = reg_ddrc_mrr2rd_freq2;
assign i_regmux_ddrc_mrr2wr[2]                     = reg_ddrc_mrr2wr_freq2;
assign i_regmux_ddrc_mrr2mrw[2]                    = reg_ddrc_mrr2mrw_freq2;
assign i_regmux_ddrc_ws_off2ws_fs[2]               = reg_ddrc_ws_off2ws_fs_freq2;
assign i_regmux_ddrc_t_wcksus[2]                   = reg_ddrc_t_wcksus_freq2;
assign i_regmux_ddrc_ws_fs2wck_sus[2]              = reg_ddrc_ws_fs2wck_sus_freq2;
assign i_regmux_ddrc_max_rd_sync[2]                = reg_ddrc_max_rd_sync_freq2;
assign i_regmux_ddrc_max_wr_sync[2]                = reg_ddrc_max_wr_sync_freq2;
assign i_regmux_ddrc_dfi_twck_delay[2]             = reg_ddrc_dfi_twck_delay_freq2;
assign i_regmux_ddrc_dfi_twck_en_rd[2]             = reg_ddrc_dfi_twck_en_rd_freq2;
assign i_regmux_ddrc_dfi_twck_en_wr[2]             = reg_ddrc_dfi_twck_en_wr_freq2;
assign i_regmux_ddrc_dfi_twck_en_fs[2]             = reg_ddrc_dfi_twck_en_fs_freq2;
assign i_regmux_ddrc_dfi_twck_dis[2]               = reg_ddrc_dfi_twck_dis_freq2;
assign i_regmux_ddrc_dfi_twck_fast_toggle[2]       = reg_ddrc_dfi_twck_fast_toggle_freq2;
assign i_regmux_ddrc_dfi_twck_toggle[2]            = reg_ddrc_dfi_twck_toggle_freq2;
assign i_regmux_ddrc_dfi_twck_toggle_cs[2]         = reg_ddrc_dfi_twck_toggle_cs_freq2;
assign i_regmux_ddrc_dfi_twck_toggle_post[2]       = reg_ddrc_dfi_twck_toggle_post_freq2;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd_en[2] = reg_ddrc_dfi_twck_toggle_post_rd_en_freq2;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd[2]    = reg_ddrc_dfi_twck_toggle_post_rd_freq2;
assign i_regmux_ddrc_dfi_t_ctrl_delay[2]           = reg_ddrc_dfi_t_ctrl_delay_freq2;
assign i_regmux_ddrc_dfi_t_rddata_en[2]            = reg_ddrc_dfi_t_rddata_en_freq2;
assign i_regmux_ddrc_dfi_tphy_wrdata[2]            = reg_ddrc_dfi_tphy_wrdata_freq2;
assign i_regmux_ddrc_dfi_tphy_wrlat[2]             = reg_ddrc_dfi_tphy_wrlat_freq2;
assign i_regmux_ddrc_dfi_t_wrdata_delay[2]         = reg_ddrc_dfi_t_wrdata_delay_freq2;
assign i_regmux_ddrc_dfi_t_dram_clk_disable[2]     = reg_ddrc_dfi_t_dram_clk_disable_freq2;
assign i_regmux_ddrc_dfi_t_dram_clk_enable[2]      = reg_ddrc_dfi_t_dram_clk_enable_freq2;
assign i_regmux_ddrc_dfi_tphy_rdcslat[2]           = reg_ddrc_dfi_tphy_rdcslat_freq2;
assign i_regmux_ddrc_dfi_tphy_wrcslat[2]           = reg_ddrc_dfi_tphy_wrcslat_freq2;



assign i_regmux_ddrc_t_rfmpb[2]     = reg_ddrc_t_rfmpb_freq2;

assign i_regmux_ddrc_hpr_max_starve[2]             = reg_ddrc_hpr_max_starve_freq2;
assign i_regmux_ddrc_hpr_xact_run_length[2]        = reg_ddrc_hpr_xact_run_length_freq2;
assign i_regmux_ddrc_lpr_max_starve[2]             = reg_ddrc_lpr_max_starve_freq2;
assign i_regmux_ddrc_lpr_xact_run_length[2]        = reg_ddrc_lpr_xact_run_length_freq2;
assign i_regmux_ddrc_w_max_starve[2]               = reg_ddrc_w_max_starve_freq2;
assign i_regmux_ddrc_w_xact_run_length[2]          = reg_ddrc_w_xact_run_length_freq2;

assign i_regmux_ddrc_pageclose_timer[2]            = reg_ddrc_pageclose_timer_freq2;
assign i_regmux_ddrc_rdwr_idle_gap[2]              = reg_ddrc_rdwr_idle_gap_freq2;


assign i_regmux_ddrc_rd_link_ecc_enable[2]  = reg_ddrc_rd_link_ecc_enable_freq2;
assign i_regmux_ddrc_wr_link_ecc_enable[2]  = reg_ddrc_wr_link_ecc_enable_freq2;

  /////////////////////
  // Freq3 registers //
  /////////////////////

assign i_regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024[3]     = reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024[3]     = reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3;
assign i_regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8[3]      = reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1[3]         = reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3;
assign i_regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit[3]    = reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3;
assign i_regmux_ddrc_ppt2_en[3]                              = reg_ddrc_ppt2_en_freq3;
assign i_regmux_ddrc_ppt2_override[3]                        = reg_ddrc_ppt2_override_freq3;
assign i_regmux_ddrc_ctrlupd_after_dqsosc[3]                 = reg_ddrc_ctrlupd_after_dqsosc_freq3;

assign i_regmux_ddrc_hw_lp_idle_x32[3]   = reg_ddrc_hw_lp_idle_x32_freq3;

assign i_regmux_ddrc_frequency_ratio[3]       = reg_ddrc_frequency_ratio_freq3;

assign i_regmux_ddrc_refresh_timer0_start_value_x32[3]    = reg_ddrc_refresh_timer0_start_value_x32_freq3;
assign i_regmux_ddrc_refresh_timer1_start_value_x32[3]    = reg_ddrc_refresh_timer1_start_value_x32_freq3;

assign i_regmux_ddrc_derated_t_rcd[3]              = reg_ddrc_derated_t_rcd_freq3;
assign i_regmux_ddrc_derated_t_ras_min[3]          = reg_ddrc_derated_t_ras_min_freq3;
assign i_regmux_ddrc_derated_t_rp[3]               = reg_ddrc_derated_t_rp_freq3;
assign i_regmux_ddrc_derated_t_rrd[3]              = reg_ddrc_derated_t_rrd_freq3;
assign i_regmux_ddrc_derated_t_rc[3]               = reg_ddrc_derated_t_rc_freq3;
assign i_regmux_ddrc_derated_t_rcd_write[3]        = reg_ddrc_derated_t_rcd_write_freq3;
assign i_regmux_ddrc_mr4_read_interval[3]          = reg_ddrc_mr4_read_interval_freq3;
assign i_regmux_ddrc_powerdown_to_x32[3]           = reg_ddrc_powerdown_to_x32_freq3;
assign i_regmux_ddrc_selfref_to_x32[3]             = reg_ddrc_selfref_to_x32_freq3;


assign i_regmux_ddrc_refresh_margin[3]             = reg_ddrc_refresh_margin_freq3;
assign i_regmux_ddrc_refresh_to_x1_x32[3]          = reg_ddrc_refresh_to_x1_x32_freq3;
assign i_regmux_ddrc_refresh_to_ab_x32[3]          = reg_ddrc_refresh_to_ab_x32_freq3;
assign i_regmux_ddrc_t_refi_x1_sel[3]              = reg_ddrc_t_refi_x1_sel_freq3;
assign i_regmux_ddrc_refresh_to_x1_sel[3]          = reg_ddrc_refresh_to_x1_sel_freq3;
assign i_regmux_ddrc_t_refi_x32[3]                 = reg_ddrc_t_refi_x32_freq3;
assign i_regmux_ddrc_t_rfc_min[3]                  = reg_ddrc_t_rfc_min_freq3;
assign i_regmux_ddrc_t_rfc_min_ab[3]               = reg_ddrc_t_rfc_min_ab_freq3;
assign i_regmux_ddrc_t_pbr2pbr[3]                  = reg_ddrc_t_pbr2pbr_freq3;
assign i_regmux_ddrc_t_pbr2act[3]                  = reg_ddrc_t_pbr2act_freq3;
assign i_regmux_ddrc_t_pgm_x1_x1024 [3]            = reg_ddrc_t_pgm_x1_x1024_freq3;
assign i_regmux_ddrc_t_pgm_x1_sel [3]              = reg_ddrc_t_pgm_x1_sel_freq3;
assign i_regmux_ddrc_t_pgmpst_x32 [3]              = reg_ddrc_t_pgmpst_x32_freq3;
assign i_regmux_ddrc_t_pgm_exit [3]                = reg_ddrc_t_pgm_exit_freq3;
assign i_regmux_ddrc_mr[3]                         = reg_ddrc_mr_freq3;
assign i_regmux_ddrc_emr[3]                        = reg_ddrc_emr_freq3;
assign i_regmux_ddrc_emr2[3]                       = reg_ddrc_emr2_freq3;
assign i_regmux_ddrc_emr3[3]                       = reg_ddrc_emr3_freq3;
assign i_regmux_ddrc_mr4[3]                        = reg_ddrc_mr4_freq3;
assign i_regmux_ddrc_mr5[3]                        = reg_ddrc_mr5_freq3;
assign i_regmux_ddrc_mr6[3]                        = reg_ddrc_mr6_freq3;
assign i_regmux_ddrc_mr22[3]                       = reg_ddrc_mr22_freq3;
assign i_regmux_ddrc_diff_rank_rd_gap[3]           = reg_ddrc_diff_rank_rd_gap_freq3;
assign i_regmux_ddrc_diff_rank_wr_gap[3]           = reg_ddrc_diff_rank_wr_gap_freq3;
assign i_regmux_ddrc_rd2wr_dr[3]                   = reg_ddrc_rd2wr_dr_freq3;
assign i_regmux_ddrc_wr2rd_dr[3]                   = reg_ddrc_wr2rd_dr_freq3;
assign i_regmux_ddrc_lpddr4_diff_bank_rwa2pre[3]   = reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3;
assign i_regmux_ddrc_wr2pre[3]                     = reg_ddrc_wr2pre_freq3;
assign i_regmux_ddrc_wra2pre[3]                    = reg_ddrc_wra2pre_freq3;
assign i_regmux_ddrc_t_faw[3]                      = reg_ddrc_t_faw_freq3;
assign i_regmux_ddrc_t_ras_max[3]                  = reg_ddrc_t_ras_max_freq3;
assign i_regmux_ddrc_t_ras_min[3]                  = reg_ddrc_t_ras_min_freq3;
assign i_regmux_ddrc_t_rcd_write[3]                = reg_ddrc_t_rcd_write_freq3;
assign i_regmux_ddrc_t_xp[3]                       = reg_ddrc_t_xp_freq3;
assign i_regmux_ddrc_rd2pre[3]                     = reg_ddrc_rd2pre_freq3;
assign i_regmux_ddrc_rda2pre[3]                    = reg_ddrc_rda2pre_freq3;
assign i_regmux_ddrc_t_rc[3]                       = reg_ddrc_t_rc_freq3;
assign i_regmux_ddrc_write_latency[3]              = reg_ddrc_write_latency_freq3;
assign i_regmux_ddrc_read_latency[3]               = reg_ddrc_read_latency_freq3;
assign i_regmux_ddrc_rd2wr[3]                      = reg_ddrc_rd2wr_freq3;
assign i_regmux_ddrc_wr2rd[3]                      = reg_ddrc_wr2rd_freq3;
assign i_regmux_ddrc_wr2mr[3]                      = reg_ddrc_wr2mr_freq3;
assign i_regmux_ddrc_t_mr[3]                       = reg_ddrc_t_mr_freq3;
assign i_regmux_ddrc_rd2mr[3]                      = reg_ddrc_rd2mr_freq3;
assign i_regmux_ddrc_t_rcd[3]                      = reg_ddrc_t_rcd_freq3;
assign i_regmux_ddrc_t_ccd[3]                      = reg_ddrc_t_ccd_freq3;
assign i_regmux_ddrc_t_rrd[3]                      = reg_ddrc_t_rrd_freq3;
assign i_regmux_ddrc_t_rp[3]                       = reg_ddrc_t_rp_freq3;
assign i_regmux_ddrc_t_cksrx[3]                    = reg_ddrc_t_cksrx_freq3;
assign i_regmux_ddrc_t_cksre[3]                    = reg_ddrc_t_cksre_freq3;
assign i_regmux_ddrc_t_ckesr[3]                    = reg_ddrc_t_ckesr_freq3;
assign i_regmux_ddrc_t_cke[3]                      = reg_ddrc_t_cke_freq3;
assign i_regmux_ddrc_t_ckcsx[3]                    = reg_ddrc_t_ckcsx_freq3;
assign i_regmux_ddrc_t_ccd_s[3]                    = reg_ddrc_t_ccd_s_freq3;
assign i_regmux_ddrc_t_rrd_s[3]                    = reg_ddrc_t_rrd_s_freq3;
assign i_regmux_ddrc_wr2rd_s[3]                    = reg_ddrc_wr2rd_s_freq3;
assign i_regmux_ddrc_t_cmdcke[3]                   = reg_ddrc_t_cmdcke_freq3;
assign i_regmux_ddrc_t_pdn[3]                      = reg_ddrc_t_pdn_freq3;
assign i_regmux_ddrc_t_xsr_dsm_x1024[3]            = reg_ddrc_t_xsr_dsm_x1024_freq3;
assign i_regmux_ddrc_t_csh[3]                      = reg_ddrc_t_csh_freq3;
assign i_regmux_ddrc_odtloff[3]                    = reg_ddrc_odtloff_freq3;
assign i_regmux_ddrc_t_ccd_mw[3]                   = reg_ddrc_t_ccd_mw_freq3;
assign i_regmux_ddrc_t_ppd[3]                      = reg_ddrc_t_ppd_freq3;
assign i_regmux_ddrc_t_xsr[3]                      = reg_ddrc_t_xsr_freq3;
assign i_regmux_ddrc_t_osco[3]                     = reg_ddrc_t_osco_freq3;
assign i_regmux_ddrc_dqsosc_enable[3]              = reg_ddrc_dqsosc_enable_freq3;
assign i_regmux_ddrc_dqsosc_interval_unit[3]       = reg_ddrc_dqsosc_interval_unit_freq3;
assign i_regmux_ddrc_dqsosc_interval[3]            = reg_ddrc_dqsosc_interval_freq3;
assign i_regmux_ddrc_t_vrcg_enable[3]              = reg_ddrc_t_vrcg_enable_freq3;
assign i_regmux_ddrc_t_vrcg_disable[3]             = reg_ddrc_t_vrcg_disable_freq3;
assign i_regmux_ddrc_t_zq_stop[3]                  = reg_ddrc_t_zq_stop_freq3;
assign i_regmux_ddrc_dvfsq_enable[3]               = reg_ddrc_dvfsq_enable_freq3;
assign i_regmux_ddrc_t_zq_long_nop[3]              = reg_ddrc_t_zq_long_nop_freq3;
assign i_regmux_ddrc_t_zq_short_nop[3]             = reg_ddrc_t_zq_short_nop_freq3;
assign i_regmux_ddrc_t_zq_reset_nop[3]             = reg_ddrc_t_zq_reset_nop_freq3;
assign i_regmux_ddrc_t_zq_short_interval_x1024[3]  = reg_ddrc_t_zq_short_interval_x1024_freq3;
assign i_regmux_ddrc_bank_org[3]                   = reg_ddrc_bank_org_freq3;
assign i_regmux_ddrc_rd2wr_s[3]                    = reg_ddrc_rd2wr_s_freq3;
assign i_regmux_ddrc_mrr2rd[3]                     = reg_ddrc_mrr2rd_freq3;
assign i_regmux_ddrc_mrr2wr[3]                     = reg_ddrc_mrr2wr_freq3;
assign i_regmux_ddrc_mrr2mrw[3]                    = reg_ddrc_mrr2mrw_freq3;
assign i_regmux_ddrc_ws_off2ws_fs[3]               = reg_ddrc_ws_off2ws_fs_freq3;
assign i_regmux_ddrc_t_wcksus[3]                   = reg_ddrc_t_wcksus_freq3;
assign i_regmux_ddrc_ws_fs2wck_sus[3]              = reg_ddrc_ws_fs2wck_sus_freq3;
assign i_regmux_ddrc_max_rd_sync[3]                = reg_ddrc_max_rd_sync_freq3;
assign i_regmux_ddrc_max_wr_sync[3]                = reg_ddrc_max_wr_sync_freq3;
assign i_regmux_ddrc_dfi_twck_delay[3]             = reg_ddrc_dfi_twck_delay_freq3;
assign i_regmux_ddrc_dfi_twck_en_rd[3]             = reg_ddrc_dfi_twck_en_rd_freq3;
assign i_regmux_ddrc_dfi_twck_en_wr[3]             = reg_ddrc_dfi_twck_en_wr_freq3;
assign i_regmux_ddrc_dfi_twck_en_fs[3]             = reg_ddrc_dfi_twck_en_fs_freq3;
assign i_regmux_ddrc_dfi_twck_dis[3]               = reg_ddrc_dfi_twck_dis_freq3;
assign i_regmux_ddrc_dfi_twck_fast_toggle[3]       = reg_ddrc_dfi_twck_fast_toggle_freq3;
assign i_regmux_ddrc_dfi_twck_toggle[3]            = reg_ddrc_dfi_twck_toggle_freq3;
assign i_regmux_ddrc_dfi_twck_toggle_cs[3]         = reg_ddrc_dfi_twck_toggle_cs_freq3;
assign i_regmux_ddrc_dfi_twck_toggle_post[3]       = reg_ddrc_dfi_twck_toggle_post_freq3;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd_en[3] = reg_ddrc_dfi_twck_toggle_post_rd_en_freq3;
assign i_regmux_ddrc_dfi_twck_toggle_post_rd[3]    = reg_ddrc_dfi_twck_toggle_post_rd_freq3;
assign i_regmux_ddrc_dfi_t_ctrl_delay[3]           = reg_ddrc_dfi_t_ctrl_delay_freq3;
assign i_regmux_ddrc_dfi_t_rddata_en[3]            = reg_ddrc_dfi_t_rddata_en_freq3;
assign i_regmux_ddrc_dfi_tphy_wrdata[3]            = reg_ddrc_dfi_tphy_wrdata_freq3;
assign i_regmux_ddrc_dfi_tphy_wrlat[3]             = reg_ddrc_dfi_tphy_wrlat_freq3;
assign i_regmux_ddrc_dfi_t_wrdata_delay[3]         = reg_ddrc_dfi_t_wrdata_delay_freq3;
assign i_regmux_ddrc_dfi_t_dram_clk_disable[3]     = reg_ddrc_dfi_t_dram_clk_disable_freq3;
assign i_regmux_ddrc_dfi_t_dram_clk_enable[3]      = reg_ddrc_dfi_t_dram_clk_enable_freq3;
assign i_regmux_ddrc_dfi_tphy_rdcslat[3]           = reg_ddrc_dfi_tphy_rdcslat_freq3;
assign i_regmux_ddrc_dfi_tphy_wrcslat[3]           = reg_ddrc_dfi_tphy_wrcslat_freq3;



assign i_regmux_ddrc_t_rfmpb[3]     = reg_ddrc_t_rfmpb_freq3;

assign i_regmux_ddrc_hpr_max_starve[3]             = reg_ddrc_hpr_max_starve_freq3;
assign i_regmux_ddrc_hpr_xact_run_length[3]        = reg_ddrc_hpr_xact_run_length_freq3;
assign i_regmux_ddrc_lpr_max_starve[3]             = reg_ddrc_lpr_max_starve_freq3;
assign i_regmux_ddrc_lpr_xact_run_length[3]        = reg_ddrc_lpr_xact_run_length_freq3;
assign i_regmux_ddrc_w_max_starve[3]               = reg_ddrc_w_max_starve_freq3;
assign i_regmux_ddrc_w_xact_run_length[3]          = reg_ddrc_w_xact_run_length_freq3;

assign i_regmux_ddrc_pageclose_timer[3]            = reg_ddrc_pageclose_timer_freq3;
assign i_regmux_ddrc_rdwr_idle_gap[3]              = reg_ddrc_rdwr_idle_gap_freq3;


assign i_regmux_ddrc_rd_link_ecc_enable[3]  = reg_ddrc_rd_link_ecc_enable_freq3;
assign i_regmux_ddrc_wr_link_ecc_enable[3]  = reg_ddrc_wr_link_ecc_enable_freq3;


  /////////////
  // Outputs //
  /////////////

// P80001562-512648
//spyglass disable_block ImproperRangeIndex-ML
//SMD: Index 'regmux_ddrc_target_frequency(_init)' of width '4' can have max value '15' which is greater than the required max value '13' of the signal 'X'[Hierarchy: :DWC_ddrctl:U_regmux_div_ch0@dwc_ddrctl_regmux_div:U_reg_mux@dwc_ddrctl_reg_mux]
//SJ: The range of regmux_ddrc_target_frequency(_init) is 0 to TARGET_FREQUENCY_WIDTH-1. Signals i_regmux_ddrc_* are replicated TARGET_FREQUENCY_WIDTH times. Overflow cannot occur.

assign regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024         = i_regmux_ddrc_dfi_t_ctrlupd_interval_max_x1024[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024         = i_regmux_ddrc_dfi_t_ctrlupd_interval_min_x1024[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8          = i_regmux_ddrc_dfi_t_ctrlupd_burst_interval_x8[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_ctrlupd_interval_type1             = i_regmux_ddrc_dfi_t_ctrlupd_interval_type1[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit        = i_regmux_ddrc_dfi_t_ctrlupd_interval_type1_unit[regmux_ddrc_target_frequency];
assign regmux_ddrc_ppt2_en                                  = i_regmux_ddrc_ppt2_en[regmux_ddrc_target_frequency];
assign regmux_ddrc_ppt2_override                            = i_regmux_ddrc_ppt2_override[regmux_ddrc_target_frequency];
assign regmux_ddrc_ctrlupd_after_dqsosc                     = i_regmux_ddrc_ctrlupd_after_dqsosc[regmux_ddrc_target_frequency];

assign regmux_ddrc_hw_lp_idle_x32   = i_regmux_ddrc_hw_lp_idle_x32[regmux_ddrc_target_frequency];

assign regmux_ddrc_frequency_ratio            = i_regmux_ddrc_frequency_ratio[regmux_ddrc_target_frequency];
assign regmux_ddrc_frequency_ratio_next       = i_regmux_ddrc_frequency_ratio[regmux_ddrc_target_frequency_init];

assign regmux_ddrc_refresh_timer0_start_value_x32    = i_regmux_ddrc_refresh_timer0_start_value_x32[regmux_ddrc_target_frequency];
assign regmux_ddrc_refresh_timer1_start_value_x32    = i_regmux_ddrc_refresh_timer1_start_value_x32[regmux_ddrc_target_frequency];


// DERATEVAL0
assign regmux_ddrc_derated_t_rcd              = i_regmux_ddrc_derated_t_rcd[regmux_ddrc_target_frequency];
assign regmux_ddrc_derated_t_ras_min          = i_regmux_ddrc_derated_t_ras_min[regmux_ddrc_target_frequency];
assign regmux_ddrc_derated_t_rp               = i_regmux_ddrc_derated_t_rp[regmux_ddrc_target_frequency];
assign regmux_ddrc_derated_t_rrd              = i_regmux_ddrc_derated_t_rrd[regmux_ddrc_target_frequency];
// DERATEVAL1
assign regmux_ddrc_derated_t_rc               = i_regmux_ddrc_derated_t_rc[regmux_ddrc_target_frequency];
assign regmux_ddrc_derated_t_rcd_write        = i_regmux_ddrc_derated_t_rcd_write[regmux_ddrc_target_frequency];
// DERATEINT
assign regmux_ddrc_mr4_read_interval          = i_regmux_ddrc_mr4_read_interval[regmux_ddrc_target_frequency];
// PWRTMG
assign regmux_ddrc_powerdown_to_x32           = i_regmux_ddrc_powerdown_to_x32[regmux_ddrc_target_frequency];
assign regmux_ddrc_selfref_to_x32             = i_regmux_ddrc_selfref_to_x32[regmux_ddrc_target_frequency];
// HWFFCEX

// RFSHCTL0
assign regmux_ddrc_refresh_margin             = i_regmux_ddrc_refresh_margin[regmux_ddrc_target_frequency];
assign regmux_ddrc_refresh_to_x1_x32          = i_regmux_ddrc_refresh_to_x1_x32[regmux_ddrc_target_frequency];
assign regmux_ddrc_refresh_to_ab_x32          = i_regmux_ddrc_refresh_to_ab_x32[regmux_ddrc_target_frequency];
// RFSHTMG
assign regmux_ddrc_t_refi_x1_sel              = i_regmux_ddrc_t_refi_x1_sel[regmux_ddrc_target_frequency];
assign regmux_ddrc_refresh_to_x1_sel          = i_regmux_ddrc_refresh_to_x1_sel[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_refi_x32                 = i_regmux_ddrc_t_refi_x32[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_rfc_min                  = i_regmux_ddrc_t_rfc_min[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_rfc_min_ab               = i_regmux_ddrc_t_rfc_min_ab[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pbr2pbr                  = i_regmux_ddrc_t_pbr2pbr[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pbr2act                  = i_regmux_ddrc_t_pbr2act[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pgm_x1_x1024            = i_regmux_ddrc_t_pgm_x1_x1024 [regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pgm_x1_sel              = i_regmux_ddrc_t_pgm_x1_sel [regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pgmpst_x32              = i_regmux_ddrc_t_pgmpst_x32 [regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pgm_exit                = i_regmux_ddrc_t_pgm_exit [regmux_ddrc_target_frequency];
// INIT3
assign regmux_ddrc_mr                         = i_regmux_ddrc_mr[regmux_ddrc_target_frequency_init];
assign regmux_ddrc_emr                        = i_regmux_ddrc_emr[regmux_ddrc_target_frequency_init];
// INIT4
assign regmux_ddrc_emr2                       = i_regmux_ddrc_emr2[regmux_ddrc_target_frequency_init];
assign regmux_ddrc_emr3                       = i_regmux_ddrc_emr3[regmux_ddrc_target_frequency_init];
// INIT6
assign regmux_ddrc_mr4                        = i_regmux_ddrc_mr4[regmux_ddrc_target_frequency_init];
assign regmux_ddrc_mr5                        = i_regmux_ddrc_mr5[regmux_ddrc_target_frequency_init];
// INIT7
assign regmux_ddrc_mr6                        = i_regmux_ddrc_mr6[regmux_ddrc_target_frequency_init];
assign regmux_ddrc_mr22                       = i_regmux_ddrc_mr22[regmux_ddrc_target_frequency_init];
// RANKCTL_FREQ3
assign regmux_ddrc_diff_rank_rd_gap           = i_regmux_ddrc_diff_rank_rd_gap[regmux_ddrc_target_frequency];
assign regmux_ddrc_diff_rank_wr_gap           = i_regmux_ddrc_diff_rank_wr_gap[regmux_ddrc_target_frequency];
assign regmux_ddrc_rd2wr_dr                   = i_regmux_ddrc_rd2wr_dr[regmux_ddrc_target_frequency];
assign regmux_ddrc_wr2rd_dr                   = i_regmux_ddrc_wr2rd_dr[regmux_ddrc_target_frequency];
assign regmux_ddrc_lpddr4_diff_bank_rwa2pre   = i_regmux_ddrc_lpddr4_diff_bank_rwa2pre[regmux_ddrc_target_frequency];
assign regmux_ddrc_wr2pre                     = i_regmux_ddrc_wr2pre[regmux_ddrc_target_frequency];
assign regmux_ddrc_wra2pre                    = i_regmux_ddrc_wra2pre[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_faw                      = i_regmux_ddrc_t_faw[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_ras_max                  = i_regmux_ddrc_t_ras_max[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_ras_min                  = i_regmux_ddrc_t_ras_min[regmux_ddrc_target_frequency];
// DRAMSET1TMG1
assign regmux_ddrc_t_rcd_write                = i_regmux_ddrc_t_rcd_write[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_xp                       = i_regmux_ddrc_t_xp[regmux_ddrc_target_frequency];
assign regmux_ddrc_rd2pre                     = i_regmux_ddrc_rd2pre[regmux_ddrc_target_frequency];
assign regmux_ddrc_rda2pre                    = i_regmux_ddrc_rda2pre[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_rc                       = i_regmux_ddrc_t_rc[regmux_ddrc_target_frequency];
// DRAMSET1TMG2
assign regmux_ddrc_write_latency              = i_regmux_ddrc_write_latency[regmux_ddrc_target_frequency];
assign regmux_ddrc_read_latency               = i_regmux_ddrc_read_latency[regmux_ddrc_target_frequency];
assign regmux_ddrc_rd2wr                      = i_regmux_ddrc_rd2wr[regmux_ddrc_target_frequency];
assign regmux_ddrc_wr2rd                      = i_regmux_ddrc_wr2rd[regmux_ddrc_target_frequency];
// DRAMSET1TMG3
assign regmux_ddrc_wr2mr                      = i_regmux_ddrc_wr2mr[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_mr                       = i_regmux_ddrc_t_mr[regmux_ddrc_target_frequency];
assign regmux_ddrc_rd2mr                      = i_regmux_ddrc_rd2mr[regmux_ddrc_target_frequency];
// DRAMSET1TMG4
assign regmux_ddrc_t_rcd                      = i_regmux_ddrc_t_rcd[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_ccd                      = i_regmux_ddrc_t_ccd[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_rrd                      = i_regmux_ddrc_t_rrd[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_rp                       = i_regmux_ddrc_t_rp[regmux_ddrc_target_frequency];
// DRAMTMG5
assign regmux_ddrc_t_cksrx                    = i_regmux_ddrc_t_cksrx[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_cksre                    = i_regmux_ddrc_t_cksre[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_ckesr                    = i_regmux_ddrc_t_ckesr[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_cke                      = i_regmux_ddrc_t_cke[regmux_ddrc_target_frequency];
// DRAMTMG6
assign regmux_ddrc_t_ckcsx                    = i_regmux_ddrc_t_ckcsx[regmux_ddrc_target_frequency];
// DRAMTMG8
// DRAMTMG9
assign regmux_ddrc_t_ccd_s                    = i_regmux_ddrc_t_ccd_s[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_rrd_s                    = i_regmux_ddrc_t_rrd_s[regmux_ddrc_target_frequency];
assign regmux_ddrc_wr2rd_s                    = i_regmux_ddrc_wr2rd_s[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_cmdcke                   = i_regmux_ddrc_t_cmdcke[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_pdn                      = i_regmux_ddrc_t_pdn[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_xsr_dsm_x1024            = i_regmux_ddrc_t_xsr_dsm_x1024[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_csh                      = i_regmux_ddrc_t_csh[regmux_ddrc_target_frequency];
// DRAMTMG13
assign regmux_ddrc_odtloff                    = i_regmux_ddrc_odtloff[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_ccd_mw                   = i_regmux_ddrc_t_ccd_mw[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_ppd                      = i_regmux_ddrc_t_ppd[regmux_ddrc_target_frequency];
// DRAMTMG14
assign regmux_ddrc_t_xsr                      = i_regmux_ddrc_t_xsr[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_osco                     = i_regmux_ddrc_t_osco[regmux_ddrc_target_frequency];
assign regmux_ddrc_dqsosc_enable              = i_regmux_ddrc_dqsosc_enable[regmux_ddrc_target_frequency];
assign regmux_ddrc_dqsosc_interval_unit       = i_regmux_ddrc_dqsosc_interval_unit[regmux_ddrc_target_frequency];
assign regmux_ddrc_dqsosc_interval            = i_regmux_ddrc_dqsosc_interval[regmux_ddrc_target_frequency];
// DRAMTMG17
assign regmux_ddrc_t_vrcg_enable              = i_regmux_ddrc_t_vrcg_enable[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_vrcg_disable             = i_regmux_ddrc_t_vrcg_disable[regmux_ddrc_target_frequency];
// ZQSET1TMG2
assign regmux_ddrc_t_zq_stop                  = i_regmux_ddrc_t_zq_stop[regmux_ddrc_target_frequency];
assign regmux_ddrc_dvfsq_enable               = i_regmux_ddrc_dvfsq_enable[regmux_ddrc_target_frequency];
assign regmux_ddrc_dvfsq_enable_next          = i_regmux_ddrc_dvfsq_enable[regmux_ddrc_target_frequency_init];
// ZQCTL0
assign regmux_ddrc_t_zq_long_nop              = i_regmux_ddrc_t_zq_long_nop[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_zq_short_nop             = i_regmux_ddrc_t_zq_short_nop[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_zq_reset_nop             = i_regmux_ddrc_t_zq_reset_nop[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_zq_short_interval_x1024  = i_regmux_ddrc_t_zq_short_interval_x1024[regmux_ddrc_target_frequency];
assign regmux_ddrc_bank_org                   = i_regmux_ddrc_bank_org[regmux_ddrc_target_frequency];
assign regmux_ddrc_rd2wr_s                    = i_regmux_ddrc_rd2wr_s[regmux_ddrc_target_frequency];
assign regmux_ddrc_mrr2rd                     = i_regmux_ddrc_mrr2rd[regmux_ddrc_target_frequency];
assign regmux_ddrc_mrr2wr                     = i_regmux_ddrc_mrr2wr[regmux_ddrc_target_frequency];
assign regmux_ddrc_mrr2mrw                    = i_regmux_ddrc_mrr2mrw[regmux_ddrc_target_frequency];
assign regmux_ddrc_ws_off2ws_fs               = i_regmux_ddrc_ws_off2ws_fs[regmux_ddrc_target_frequency];
assign regmux_ddrc_t_wcksus                   = i_regmux_ddrc_t_wcksus[regmux_ddrc_target_frequency];
assign regmux_ddrc_ws_fs2wck_sus              = i_regmux_ddrc_ws_fs2wck_sus[regmux_ddrc_target_frequency];
assign regmux_ddrc_max_rd_sync                = i_regmux_ddrc_max_rd_sync[regmux_ddrc_target_frequency];
assign regmux_ddrc_max_wr_sync                = i_regmux_ddrc_max_wr_sync[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_delay             = i_regmux_ddrc_dfi_twck_delay[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_en_rd             = i_regmux_ddrc_dfi_twck_en_rd[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_en_wr             = i_regmux_ddrc_dfi_twck_en_wr[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_en_fs             = i_regmux_ddrc_dfi_twck_en_fs[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_dis               = i_regmux_ddrc_dfi_twck_dis[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_fast_toggle       = i_regmux_ddrc_dfi_twck_fast_toggle[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_toggle            = i_regmux_ddrc_dfi_twck_toggle[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_toggle_cs         = i_regmux_ddrc_dfi_twck_toggle_cs[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_toggle_post       = i_regmux_ddrc_dfi_twck_toggle_post[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_toggle_post_rd_en = i_regmux_ddrc_dfi_twck_toggle_post_rd_en[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_twck_toggle_post_rd    = i_regmux_ddrc_dfi_twck_toggle_post_rd[regmux_ddrc_target_frequency];
// DFITMG0
assign regmux_ddrc_dfi_t_ctrl_delay           = i_regmux_ddrc_dfi_t_ctrl_delay[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_rddata_en            = i_regmux_ddrc_dfi_t_rddata_en[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_tphy_wrdata            = i_regmux_ddrc_dfi_tphy_wrdata[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_tphy_wrlat             = i_regmux_ddrc_dfi_tphy_wrlat[regmux_ddrc_target_frequency];
// DFITMG1
assign regmux_ddrc_dfi_t_wrdata_delay         = i_regmux_ddrc_dfi_t_wrdata_delay[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_dram_clk_disable     = i_regmux_ddrc_dfi_t_dram_clk_disable[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_t_dram_clk_enable      = i_regmux_ddrc_dfi_t_dram_clk_enable[regmux_ddrc_target_frequency];
// DFITMG2
assign regmux_ddrc_dfi_tphy_rdcslat           = i_regmux_ddrc_dfi_tphy_rdcslat[regmux_ddrc_target_frequency];
assign regmux_ddrc_dfi_tphy_wrcslat           = i_regmux_ddrc_dfi_tphy_wrcslat[regmux_ddrc_target_frequency];




assign regmux_ddrc_t_rfmpb       = i_regmux_ddrc_t_rfmpb[regmux_ddrc_target_frequency];

assign regmux_ddrc_hpr_max_starve             = i_regmux_ddrc_hpr_max_starve[regmux_ddrc_target_frequency];
assign regmux_ddrc_hpr_xact_run_length        = i_regmux_ddrc_hpr_xact_run_length[regmux_ddrc_target_frequency];
assign regmux_ddrc_lpr_max_starve             = i_regmux_ddrc_lpr_max_starve[regmux_ddrc_target_frequency];
assign regmux_ddrc_lpr_xact_run_length        = i_regmux_ddrc_lpr_xact_run_length[regmux_ddrc_target_frequency];
assign regmux_ddrc_w_max_starve               = i_regmux_ddrc_w_max_starve[regmux_ddrc_target_frequency];
assign regmux_ddrc_w_xact_run_length          = i_regmux_ddrc_w_xact_run_length[regmux_ddrc_target_frequency];

assign regmux_ddrc_pageclose_timer            = i_regmux_ddrc_pageclose_timer[regmux_ddrc_target_frequency];
assign regmux_ddrc_rdwr_idle_gap              = i_regmux_ddrc_rdwr_idle_gap[regmux_ddrc_target_frequency];


assign regmux_ddrc_rd_link_ecc_enable         = i_regmux_ddrc_rd_link_ecc_enable[regmux_ddrc_target_frequency];
assign regmux_ddrc_wr_link_ecc_enable         = i_regmux_ddrc_wr_link_ecc_enable[regmux_ddrc_target_frequency];

//spyglass enable_block ImproperRangeIndex-ML

endmodule
