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

// Revision $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/apb/DWC_ddrctl_apb_coreif.sv#19 $
`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"

module DWC_ddrctl_apb_coreif
import DWC_ddrctl_reg_pkg::*;
  #(parameter APB_AW          = 16,
    parameter REG_WIDTH       = 32,
    parameter BCM_F_SYNC_TYPE_C2P = 2,
    parameter BCM_F_SYNC_TYPE_P2C = 2,
    parameter BCM_R_SYNC_TYPE_C2P = 2,
    parameter BCM_R_SYNC_TYPE_P2C = 2,
    parameter REG_OUTPUTS_C2P = 1,
    parameter REG_OUTPUTS_P2C = 1,
    parameter BCM_VERIF_EN    = 1,
   parameter ECC_CORRECTED_BIT_NUM_WIDTH = 1,
   parameter ECC_CORRECTED_ERR_WIDTH     = 1,
   parameter ECC_UNCORRECTED_ERR_WIDTH   = 1,
    parameter RW_REGS         = `UMCTL2_REGS_RW_REGS,
    parameter RWSELWIDTH      = RW_REGS
    ) 
  (
    input                apb_clk
    ,input               apb_rst
    ,input               core_ddrc_core_clk_apbrw
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
    ,input               core_ddrc_core_clk
    ,input               sync_core_ddrc_rstn
    ,input               core_ddrc_rstn
    ,input [RWSELWIDTH-1:0] rwselect
    ,input               write_en
//spyglass enable_block W240
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used under different `ifdefs. Decided to keep the current implementation.
    ,input               aclk_0
    ,input               sync_aresetn_0
//spyglass enable_block W240

    ,input              core_derate_temp_limit_intr
   //------------------------
   // Register REGB_DDRC_CH0.MSTR0
   //------------------------
   ,input  [REG_WIDTH -1:0] r0_mstr0
   ,output reg_ddrc_lpddr4 // @core_ddrc_core_clk
   ,output reg_apb_lpddr4 // @pclk
   ,output reg_arba0_lpddr4 // @aclk_0
   ,output reg_ddrc_lpddr5 // @core_ddrc_core_clk
   ,output reg_apb_lpddr5 // @pclk
   ,output reg_arba0_lpddr5 // @aclk_0
   ,output reg_ddrc_lpddr5x // @core_ddrc_core_clk
   ,output reg_apb_lpddr5x // @pclk
   ,output reg_arba0_lpddr5x // @aclk_0
   ,output [1:0] reg_ddrc_data_bus_width // @core_ddrc_core_clk
   ,output [1:0] reg_apb_data_bus_width // @pclk
   ,output [1:0] reg_arba0_data_bus_width // @aclk_0
   ,output [4:0] reg_ddrc_burst_rdwr // @core_ddrc_core_clk
   ,output [4:0] reg_apb_burst_rdwr // @pclk
   ,output [4:0] reg_arba0_burst_rdwr // @aclk_0
   ,output [((`MEMC_NUM_RANKS==2) ? 2 : 4)-1:0] reg_ddrc_active_ranks // @core_ddrc_core_clk
   ,output [((`MEMC_NUM_RANKS==2) ? 2 : 4)-1:0] reg_apb_active_ranks // @pclk
   ,output [((`MEMC_NUM_RANKS==2) ? 2 : 4)-1:0] reg_arba0_active_ranks // @aclk_0
   //------------------------
   // Register REGB_DDRC_CH0.MSTR2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2_mstr2
   ,output [(`DDRCTL_FREQUENCY_BITS)-1:0] reg_ddrc_target_frequency // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.MSTR4
   //------------------------
   ,input  [REG_WIDTH -1:0] r4_mstr4
   ,output reg_ddrc_wck_on // @core_ddrc_core_clk
   ,output reg_ddrc_wck_suspend_en // @core_ddrc_core_clk
   ,output reg_ddrc_ws_off_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.STAT
   //------------------------
   ,output  [REG_WIDTH -1:0] r5_stat
   ,input [2:0] ddrc_reg_operating_mode // @core_ddrc_core_clk
   ,input [((`DDRCTL_DDR_EN==1) ? (`MEMC_NUM_RANKS*2) : 2)-1:0] ddrc_reg_selfref_type // @core_ddrc_core_clk
   ,input [2:0] ddrc_reg_selfref_state // @core_ddrc_core_clk
   ,input ddrc_reg_selfref_cam_not_empty // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r8_mrctrl0
   ,output reg_ddrc_mr_type // @core_ddrc_core_clk
   ,output reg_ddrc_sw_init_int // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_mr_rank // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_mr_addr // @core_ddrc_core_clk
   ,output reg_ddrc_mrr_done_clr_ack_pclk
   ,output reg_ddrc_mrr_done_clr // @core_ddrc_core_clk
   ,output reg_ddrc_dis_mrrw_trfc // @core_ddrc_core_clk
   ,output reg_ddrc_ppr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ppr_pgmpst_en // @core_ddrc_core_clk
   ,output reg_ddrc_mr_wr_ack_pclk
   ,input ff_regb_ddrc_ch0_mr_wr_saved
   ,output reg_ddrc_mr_wr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r9_mrctrl1
   ,output [(`MEMC_PAGE_BITS)-1:0] reg_ddrc_mr_data // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.MRSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r11_mrstat
   ,output ddrc_reg_mr_wr_busy_int
   ,input ddrc_reg_mr_wr_busy // @core_ddrc_core_clk
   ,input ddrc_reg_mrr_done // @core_ddrc_core_clk
   ,input ddrc_reg_ppr_done // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.MRRDATA0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r12_mrrdata0
   ,input [31:0] ddrc_reg_mrr_data_lwr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.MRRDATA1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r13_mrrdata1
   ,input [31:0] ddrc_reg_mrr_data_upr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r14_deratectl0
   ,output reg_ddrc_derate_enable // @core_ddrc_core_clk
   ,output reg_ddrc_lpddr4_refresh_mode // @core_ddrc_core_clk
   ,output reg_ddrc_derate_mr4_pause_fc // @core_ddrc_core_clk
   ,output reg_ddrc_dis_trefi_x6x8 // @core_ddrc_core_clk
   ,output reg_ddrc_dis_trefi_x0125 // @core_ddrc_core_clk
   ,output reg_ddrc_use_slow_rm_in_low_temp // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r15_deratectl1
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/4)-1:0] reg_ddrc_active_derate_byte_rank0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL2
   //------------------------
   ,input  [REG_WIDTH -1:0] r16_deratectl2
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/4)-1:0] reg_ddrc_active_derate_byte_rank1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL5
   //------------------------
   ,input  [REG_WIDTH-1:0] r19_deratectl5
   ,output reg_ddrc_derate_temp_limit_intr_en // @pclk
   ,output reg_ddrc_derate_temp_limit_intr_clr_ack_pclk
   ,output reg_ddrc_derate_temp_limit_intr_clr // @pclk
   ,output reg_ddrc_derate_temp_limit_intr_force_ack_pclk
   ,output reg_ddrc_derate_temp_limit_intr_force // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL6
   //------------------------
   ,input  [REG_WIDTH -1:0] r20_deratectl6
   ,output reg_ddrc_derate_mr4_tuf_dis // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DERATESTAT0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r22_deratestat0
   ,input ddrc_reg_derate_temp_limit_intr // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r24_deratedbgctl
   ,output [1:0] reg_ddrc_dbg_mr4_rank_sel // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r25_deratedbgstat
   ,input [7:0] ddrc_reg_dbg_mr4_byte0 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte1 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte2 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.PWRCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r26_pwrctl
   ,output [((`DDRCTL_DDR_EN==1) ? `MEMC_NUM_RANKS : 1)-1:0] reg_ddrc_selfref_en // @core_ddrc_core_clk
   ,output [((`DDRCTL_DDR_EN==1) ? `MEMC_NUM_RANKS : 1)-1:0] reg_ddrc_powerdown_en // @core_ddrc_core_clk
   ,output reg_ddrc_en_dfi_dram_clk_disable // @core_ddrc_core_clk
   ,output reg_ddrc_selfref_sw // @core_ddrc_core_clk
   ,output reg_ddrc_stay_in_selfref // @core_ddrc_core_clk
   ,output reg_ddrc_dis_cam_drain_selfref // @core_ddrc_core_clk
   ,output reg_ddrc_lpddr4_sr_allowed // @core_ddrc_core_clk
   ,output reg_ddrc_dsm_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.HWLPCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r27_hwlpctl
   ,output reg_ddrc_hw_lp_en // @core_ddrc_core_clk
   ,output reg_ddrc_hw_lp_exit_idle_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.CLKGATECTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r29_clkgatectl
   ,output [5:0] reg_ddrc_bsm_clk_on // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RFSHMOD0
   //------------------------
   ,input  [REG_WIDTH -1:0] r30_rfshmod0
   ,output [5:0] reg_ddrc_refresh_burst // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_auto_refab_en // @core_ddrc_core_clk
   ,output reg_ddrc_per_bank_refresh // @core_ddrc_core_clk
   ,output reg_ddrc_per_bank_refresh_opt_en // @core_ddrc_core_clk
   ,output reg_ddrc_fixed_crit_refpb_bank_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RFSHCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r32_rfshctl0
   ,output reg_ddrc_dis_auto_refresh // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_update_level // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD0
   //------------------------
   ,input  [REG_WIDTH -1:0] r33_rfmmod0
   ,output reg_ddrc_rfm_en // @core_ddrc_core_clk
   ,output reg_ddrc_rfmsbc // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_raaimt // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_raamult // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_raadec // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_rfmth_rm_thr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD1
   //------------------------
   ,input  [REG_WIDTH -1:0] r34_rfmmod1
   ,output [10:0] reg_ddrc_init_raa_cnt // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RFMCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r35_rfmctl
   ,output [(`MEMC_RANK_BITS)-1:0] reg_ddrc_dbg_raa_rank // @core_ddrc_core_clk
   ,output [((`DDRCTL_LPDDR_RFMSBC_EN==1) ? `MEMC_BG_BANK_BITS : (`MEMC_BG_BANK_BITS-1))-1:0] reg_ddrc_dbg_raa_bg_bank // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RFMSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r36_rfmstat
   ,input [(`MEMC_NUM_RANKS)-1:0] ddrc_reg_rank_raa_cnt_gt0 // @core_ddrc_core_clk
   ,input [10:0] ddrc_reg_dbg_raa_cnt // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r37_zqctl0
   ,output reg_ddrc_zq_resistor_shared // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_zq // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r38_zqctl1
   ,output reg_ddrc_zq_reset_ack_pclk
   ,input ff_regb_ddrc_ch0_zq_reset_saved
   ,output reg_ddrc_zq_reset // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL2
   //------------------------
   ,input  [REG_WIDTH-1:0] r39_zqctl2
   ,output reg_ddrc_dis_srx_zqcl // @core_ddrc_core_clk
   ,output reg_ddrc_dis_srx_zqcl_hwffc // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ZQSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r40_zqstat
   ,output ddrc_reg_zq_reset_busy_int
   ,input ddrc_reg_zq_reset_busy // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCRUNTIME
   //------------------------
   ,input  [REG_WIDTH-1:0] r41_dqsoscruntime
   ,output [7:0] reg_ddrc_dqsosc_runtime // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wck2dqo_runtime // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCSTAT0
   //------------------------
   ,output  [REG_WIDTH -1:0] r42_dqsoscstat0
   ,input [2:0] ddrc_reg_dqsosc_state // @core_ddrc_core_clk
   ,input [(`MEMC_NUM_RANKS)-1:0] ddrc_reg_dqsosc_per_rank_stat // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCCFG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r43_dqsosccfg0
   ,output reg_ddrc_dis_dqsosc_srx // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SCHED0
   //------------------------
   ,input  [REG_WIDTH-1:0] r45_sched0
   ,output reg_ddrc_dis_opt_wrecc_collision_flush // @core_ddrc_core_clk
   ,output reg_ddrc_prefer_write // @core_ddrc_core_clk
   ,output reg_ddrc_pageclose // @core_ddrc_core_clk
   ,output reg_ddrc_opt_wrcam_fill_level // @core_ddrc_core_clk
   ,output reg_ddrc_dis_opt_ntt_by_act // @core_ddrc_core_clk
   ,output reg_ddrc_dis_opt_ntt_by_pre // @core_ddrc_core_clk
   ,output reg_ddrc_autopre_rmw // @core_ddrc_core_clk
   ,output [(`MEMC_RDCMD_ENTRY_BITS)-1:0] reg_ddrc_lpr_num_entries // @core_ddrc_core_clk
   ,output reg_ddrc_lpddr4_opt_act_timing // @core_ddrc_core_clk
   ,output reg_ddrc_lpddr5_opt_act_timing // @core_ddrc_core_clk
   ,output reg_ddrc_w_starve_free_running // @core_ddrc_core_clk
   ,output reg_ddrc_opt_act_lat // @core_ddrc_core_clk
   ,output reg_ddrc_prefer_read // @core_ddrc_core_clk
   ,output reg_ddrc_dis_speculative_act // @core_ddrc_core_clk
   ,output reg_ddrc_opt_vprw_sch // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SCHED1
   //------------------------
   ,input  [REG_WIDTH-1:0] r46_sched1
   ,output [3:0] reg_ddrc_delay_switch_write // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_visible_window_limit_wr // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_visible_window_limit_rd // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_page_hit_limit_wr // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_page_hit_limit_rd // @core_ddrc_core_clk
   ,output reg_ddrc_opt_hit_gt_hpr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SCHED3
   //------------------------
   ,input  [REG_WIDTH-1:0] r48_sched3
   ,output [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wrcam_lowthresh // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wrcam_highthresh // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wr_pghit_num_thresh // @core_ddrc_core_clk
   ,output [(`MEMC_RDCMD_ENTRY_BITS)-1:0] reg_ddrc_rd_pghit_num_thresh // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SCHED4
   //------------------------
   ,input  [REG_WIDTH-1:0] r49_sched4
   ,output [7:0] reg_ddrc_rd_act_idle_gap // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr_act_idle_gap // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd_page_exp_cycles // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr_page_exp_cycles // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SCHED5
   //------------------------
   ,input  [REG_WIDTH-1:0] r50_sched5
   ,output [(`MEMC_WRCMD_ENTRY_BITS-1)-1:0] reg_ddrc_wrecc_cam_lowthresh // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS-1)-1:0] reg_ddrc_wrecc_cam_highthresh // @core_ddrc_core_clk
   ,output reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level // @core_ddrc_core_clk
   ,output reg_ddrc_dis_opt_valid_wrecc_cam_fill_level // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r51_hwffcctl
   ,output [1:0] reg_ddrc_hwffc_en // @core_ddrc_core_clk
   ,output reg_ddrc_init_fsp // @core_ddrc_core_clk
   ,output reg_ddrc_init_vrcg // @core_ddrc_core_clk
   ,output reg_ddrc_target_vrcg // @core_ddrc_core_clk
   ,output reg_ddrc_skip_mrw_odtvref // @core_ddrc_core_clk
   ,output reg_ddrc_skip_zq_stop_start // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_zq_interval // @core_ddrc_core_clk
   ,output reg_ddrc_hwffc_mode // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r52_hwffcstat
   ,input ddrc_reg_hwffc_in_progress // @core_ddrc_core_clk
   ,input ddrc_reg_hwffc_operating_mode // @core_ddrc_core_clk
   ,input [(`DDRCTL_FREQUENCY_BITS)-1:0] ddrc_reg_current_frequency // @core_ddrc_core_clk
   ,input ddrc_reg_current_fsp // @core_ddrc_core_clk
   ,input ddrc_reg_current_vrcg // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DFILPCFG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r62_dfilpcfg0
   ,output reg_ddrc_dfi_lp_en_pd // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_sr // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_dsm // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_data // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_data_req_en // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_extra_gap_for_dfi_lp_data // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DFIUPD0
   //------------------------
   ,input  [REG_WIDTH -1:0] r63_dfiupd0
   ,output reg_ddrc_dfi_phyupd_en // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_pre_srx // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_ctrlupd_srx // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_ctrlupd // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DFIMISC
   //------------------------
   ,input  [REG_WIDTH -1:0] r65_dfimisc
   ,output reg_ddrc_dfi_init_complete_en // @core_ddrc_core_clk
   ,output reg_ddrc_phy_dbi_mode // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_data_cs_polarity // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_reset_n // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_init_start // @core_ddrc_core_clk
   ,output reg_ddrc_lp_optimized_write // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_frequency // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_freq_fsp // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_channel_mode // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DFISTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r66_dfistat
   ,input ddrc_reg_dfi_init_complete // @core_ddrc_core_clk
   ,input ddrc_reg_dfi_lp_ctrl_ack_stat // @core_ddrc_core_clk
   ,input ddrc_reg_dfi_lp_data_ack_stat // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DFIPHYMSTR
   //------------------------
   ,input  [REG_WIDTH -1:0] r67_dfiphymstr
   ,output reg_ddrc_dfi_phymstr_en // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_phymstr_blk_ref_x32 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.POISONCFG
   //------------------------
   ,input  [REG_WIDTH -1:0] r77_poisoncfg
   ,output reg_ddrc_wr_poison_slverr_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_poison_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_poison_intr_clr_ack_pclk
   ,output reg_ddrc_wr_poison_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_poison_slverr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_poison_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_poison_intr_clr_ack_pclk
   ,output reg_ddrc_rd_poison_intr_clr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.POISONSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r78_poisonstat
   ,input ddrc_reg_wr_poison_intr_0 // @core_ddrc_core_clk
   ,input ddrc_reg_rd_poison_intr_0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r79_ecccfg0
   ,output [2:0] reg_ddrc_ecc_mode // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_remap_en // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_ecc_region_map // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_blk_channel_idle_time_x32 // @core_ddrc_core_clk
   ,output [(`MEMC_MAX_INLINE_ECC_PER_BURST_BITS)-1:0] reg_ddrc_ecc_ap_err_threshold // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_map_other // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_ecc_region_map_granu // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r80_ecccfg1
   ,output reg_ddrc_data_poison_en // @core_ddrc_core_clk
   ,output reg_ddrc_data_poison_bit // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_parity_lock // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_waste_lock // @core_ddrc_core_clk
   ,output reg_ddrc_med_ecc_en // @core_ddrc_core_clk
   ,output reg_ddrc_blk_channel_active_term // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_active_blk_channel // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r81_eccstat
   ,input [6:0] ddrc_reg_ecc_corrected_bit_num // @pclk
   ,input [((`MEMC_INLINE_ECC_EN==1 && `MEMC_SIDEBAND_ECC_EN==0) ? 1 : (`MEMC_FREQ_RATIO==4) ? 8 : 4)-1:0] ddrc_reg_ecc_corrected_err // @pclk
   ,input [((`MEMC_INLINE_ECC_EN==1 && `MEMC_SIDEBAND_ECC_EN==0) ? 1 : (`MEMC_FREQ_RATIO==4) ? 8 : 4)-1:0] ddrc_reg_ecc_uncorrected_err // @pclk
   ,input ddrc_reg_sbr_read_ecc_ce // @pclk
   ,input ddrc_reg_sbr_read_ecc_ue // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r82_eccctl
   ,output reg_ddrc_ecc_corrected_err_clr_ack_pclk
   ,output reg_ddrc_ecc_corrected_err_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorrected_err_clr_ack_pclk
   ,output reg_ddrc_ecc_uncorrected_err_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk
   ,output reg_ddrc_ecc_corr_err_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk
   ,output reg_ddrc_ecc_uncorr_err_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_err_intr_clr_ack_pclk
   ,output reg_ddrc_ecc_ap_err_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_corrected_err_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorrected_err_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_err_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_corrected_err_intr_force_ack_pclk
   ,output reg_ddrc_ecc_corrected_err_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk
   ,output reg_ddrc_ecc_uncorrected_err_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_err_intr_force_ack_pclk
   ,output reg_ddrc_ecc_ap_err_intr_force // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCERRCNT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r83_eccerrcnt
   ,input [15:0] ddrc_reg_ecc_corr_err_cnt // @core_ddrc_core_clk
   ,input [15:0] ddrc_reg_ecc_uncorr_err_cnt // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCADDR0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r84_ecccaddr0
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_ecc_corr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_ecc_corr_rank // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCADDR1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r85_ecccaddr1
   ,input [10:0] ddrc_reg_ecc_corr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_ecc_corr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_ecc_corr_bg // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r86_ecccsyn0
   ,input [31:0] ddrc_reg_ecc_corr_syndromes_31_0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r87_ecccsyn1
   ,input [31:0] ddrc_reg_ecc_corr_syndromes_63_32 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN2
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r88_ecccsyn2
   ,input [7:0] ddrc_reg_ecc_corr_syndromes_71_64 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r89_eccbitmask0
   ,input [31:0] ddrc_reg_ecc_corr_bit_mask_31_0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r90_eccbitmask1
   ,input [31:0] ddrc_reg_ecc_corr_bit_mask_63_32 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK2
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r91_eccbitmask2
   ,input [7:0] ddrc_reg_ecc_corr_bit_mask_71_64 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCUADDR0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r92_eccuaddr0
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_ecc_uncorr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_ecc_uncorr_rank // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCUADDR1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r93_eccuaddr1
   ,input [10:0] ddrc_reg_ecc_uncorr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_ecc_uncorr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_ecc_uncorr_bg // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r94_eccusyn0
   ,input [31:0] ddrc_reg_ecc_uncorr_syndromes_31_0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r95_eccusyn1
   ,input [31:0] ddrc_reg_ecc_uncorr_syndromes_63_32 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN2
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r96_eccusyn2
   ,input [7:0] ddrc_reg_ecc_uncorr_syndromes_71_64 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR0
   //------------------------
   ,input  [REG_WIDTH-1:0] r97_eccpoisonaddr0
   ,output [11:0] reg_ddrc_ecc_poison_col // @core_ddrc_core_clk
   ,output [(`MEMC_RANK_BITS)-1:0] reg_ddrc_ecc_poison_rank // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r98_eccpoisonaddr1
   ,output [(`MEMC_PAGE_BITS)-1:0] reg_ddrc_ecc_poison_row // @core_ddrc_core_clk
   ,output [(`MEMC_BANK_BITS)-1:0] reg_ddrc_ecc_poison_bank // @core_ddrc_core_clk
   ,output [(`MEMC_BG_BITS)-1:0] reg_ddrc_ecc_poison_bg // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT0
   //------------------------
   ,input  [REG_WIDTH-1:0] r101_eccpoisonpat0
   ,output [31:0] reg_ddrc_ecc_poison_data_31_0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT2
   //------------------------
   ,input  [REG_WIDTH-1:0] r103_eccpoisonpat2
   ,output [7:0] reg_ddrc_ecc_poison_data_71_64 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ECCAPSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r104_eccapstat
   ,input ddrc_reg_ecc_ap_err // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCTL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r161_lnkeccctl1
   ,output reg_ddrc_rd_link_ecc_corr_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk
   ,output reg_ddrc_rd_link_ecc_corr_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk
   ,output reg_ddrc_rd_link_ecc_corr_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk
   ,output reg_ddrc_rd_link_ecc_corr_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk
   ,output reg_ddrc_rd_link_ecc_uncorr_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_force // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r162_lnkeccpoisonctl0
   ,output reg_ddrc_linkecc_poison_inject_en // @core_ddrc_core_clk
   ,output reg_ddrc_linkecc_poison_type // @core_ddrc_core_clk
   ,output reg_ddrc_linkecc_poison_rw // @core_ddrc_core_clk
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/8)-1:0] reg_ddrc_linkecc_poison_dmi_sel // @core_ddrc_core_clk
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/8)-1:0] reg_ddrc_linkecc_poison_byte_sel // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r163_lnkeccpoisonstat
   ,input ddrc_reg_linkecc_poison_complete // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCINDEX
   //------------------------
   ,input  [REG_WIDTH -1:0] r164_lnkeccindex
   ,output [2:0] reg_ddrc_rd_link_ecc_err_byte_sel // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_rd_link_ecc_err_rank_sel // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCERRCNT0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r165_lnkeccerrcnt0
   ,input [8:0] ddrc_reg_rd_link_ecc_err_syndrome // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_rd_link_ecc_corr_cnt // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_rd_link_ecc_uncorr_cnt // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCERRSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r166_lnkeccerrstat
   ,input [3:0] ddrc_reg_rd_link_ecc_corr_err_int // @pclk
   ,input [3:0] ddrc_reg_rd_link_ecc_uncorr_err_int // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCADDR0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r175_lnkecccaddr0
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_link_ecc_corr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_link_ecc_corr_rank // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCADDR1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r176_lnkecccaddr1
   ,input [10:0] ddrc_reg_link_ecc_corr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_link_ecc_corr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_link_ecc_corr_bg // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCUADDR0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r177_lnkeccuaddr0
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_link_ecc_uncorr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_link_ecc_uncorr_rank // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCUADDR1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r178_lnkeccuaddr1
   ,input [10:0] ddrc_reg_link_ecc_uncorr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_link_ecc_uncorr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_link_ecc_uncorr_bg // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL0
   //------------------------
   ,input  [REG_WIDTH-1:0] r234_opctrl0
   ,output reg_ddrc_dis_wc // @core_ddrc_core_clk
   ,output reg_ddrc_dis_max_rank_rd_opt // @core_ddrc_core_clk
   ,output reg_ddrc_dis_max_rank_wr_opt // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r235_opctrl1
   ,output reg_ddrc_dis_dq // @core_ddrc_core_clk
   ,output reg_ddrc_dis_hif // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCAM
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r236_opctrlcam
   ,input [(`MEMC_RDCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_hpr_q_depth // @core_ddrc_core_clk
   ,input [(`MEMC_RDCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_lpr_q_depth // @core_ddrc_core_clk
   ,input [(`MEMC_WRCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_w_q_depth // @core_ddrc_core_clk
   ,input ddrc_reg_dbg_stall // @core_ddrc_core_clk
   ,input ddrc_reg_dbg_rd_q_empty // @core_ddrc_core_clk
   ,input ddrc_reg_dbg_wr_q_empty // @core_ddrc_core_clk
   ,input ddrc_reg_rd_data_pipeline_empty // @core_ddrc_core_clk
   ,input ddrc_reg_wr_data_pipeline_empty // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCMD
   //------------------------
   ,input  [REG_WIDTH -1:0] r237_opctrlcmd
   ,output reg_ddrc_zq_calib_short_ack_pclk
   ,input ff_regb_ddrc_ch0_zq_calib_short_saved
   ,output reg_ddrc_zq_calib_short // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_ack_pclk
   ,input ff_regb_ddrc_ch0_ctrlupd_saved
   ,output reg_ddrc_ctrlupd // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_burst // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r238_opctrlstat
   ,output ddrc_reg_zq_calib_short_busy_int
   ,input ddrc_reg_zq_calib_short_busy // @core_ddrc_core_clk
   ,output ddrc_reg_ctrlupd_busy_int
   ,input ddrc_reg_ctrlupd_busy // @core_ddrc_core_clk
   ,input ddrc_reg_ctrlupd_burst_busy // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCAM1
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r239_opctrlcam1
   ,input [(`MEMC_WRCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_wrecc_q_depth // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPREFCTRL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r240_oprefctrl0
   ,output reg_ddrc_rank0_refresh_ack_pclk
   ,input ff_regb_ddrc_ch0_rank0_refresh_saved
   ,output reg_ddrc_rank0_refresh // @core_ddrc_core_clk
   ,output reg_ddrc_rank1_refresh_ack_pclk
   ,input ff_regb_ddrc_ch0_rank1_refresh_saved
   ,output reg_ddrc_rank1_refresh // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.OPREFSTAT0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r242_oprefstat0
   ,output ddrc_reg_rank0_refresh_busy_int
   ,input ddrc_reg_rank0_refresh_busy // @core_ddrc_core_clk
   ,output ddrc_reg_rank1_refresh_busy_int
   ,input ddrc_reg_rank1_refresh_busy // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SWCTL
   //------------------------
   ,input  [REG_WIDTH-1:0] r249_swctl
   ,output reg_ddrc_sw_done // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.SWSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r250_swstat
   ,input ddrc_reg_sw_done_ack // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.RANKCTL
   //------------------------
   ,input  [REG_WIDTH-1:0] r253_rankctl
   ,output [3:0] reg_ddrc_max_rank_rd // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_max_rank_wr // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DBICTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r254_dbictl
   ,output reg_ddrc_dm_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_dbi_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_dbi_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.ODTMAP
   //------------------------
   ,input  [REG_WIDTH -1:0] r256_odtmap
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank0_wr_odt // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank0_rd_odt // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank1_wr_odt // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank1_rd_odt // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DATACTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r257_datactl0
   ,output reg_ddrc_rd_data_copy_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_data_copy_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_data_x_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.SWCTLSTATIC
   //------------------------
   ,input  [REG_WIDTH-1:0] r258_swctlstatic
   ,output reg_ddrc_sw_static_unlock // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.CGCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r259_cgctl
   ,output reg_ddrc_force_clk_te_en // @core_ddrc_core_clk
   ,output reg_ddrc_force_clk_arb_en // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.INITTMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r260_inittmg0
   ,output [12:0] reg_ddrc_pre_cke_x1024 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_post_cke_x1024 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_skip_dram_init // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.PPT2CTRL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r285_ppt2ctrl0
   ,output [9:0] reg_ddrc_ppt2_burst_num // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_ppt2_ctrlupd_num_dfi0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_ppt2_ctrlupd_num_dfi1 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_burst_ack_pclk
   ,input ff_regb_ddrc_ch0_ppt2_burst_saved
   ,output reg_ddrc_ppt2_burst // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_wait_ref // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.PPT2STAT0
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r286_ppt2stat0
   ,input [3:0] ddrc_reg_ppt2_state // @core_ddrc_core_clk
   ,output ddrc_reg_ppt2_burst_busy_int
   ,input ddrc_reg_ppt2_burst_busy // @core_ddrc_core_clk
   //------------------------
   // Register REGB_DDRC_CH0.DDRCTL_VER_NUMBER
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r289_ddrctl_ver_number
   ,input [31:0] ddrc_reg_ver_number // @pclk
   //------------------------
   // Register REGB_DDRC_CH0.DDRCTL_VER_TYPE
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r290_ddrctl_ver_type
   ,input [31:0] ddrc_reg_ver_type // @pclk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP1
   //------------------------
   ,input  [REG_WIDTH-1:0] r495_addrmap1_map0
   ,output [5:0] reg_ddrc_addrmap_cs_bit0_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP3
   //------------------------
   ,input  [REG_WIDTH-1:0] r497_addrmap3_map0
   ,output [5:0] reg_ddrc_addrmap_bank_b0_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bank_b1_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bank_b2_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP4
   //------------------------
   ,input  [REG_WIDTH-1:0] r498_addrmap4_map0
   ,output [5:0] reg_ddrc_addrmap_bg_b0_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bg_b1_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP5
   //------------------------
   ,input  [REG_WIDTH-1:0] r499_addrmap5_map0
   ,output [4:0] reg_ddrc_addrmap_col_b7_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b8_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b9_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b10_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP6
   //------------------------
   ,input  [REG_WIDTH-1:0] r500_addrmap6_map0
   ,output [3:0] reg_ddrc_addrmap_col_b3_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b4_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b5_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b6_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP7
   //------------------------
   ,input  [REG_WIDTH-1:0] r501_addrmap7_map0
   ,output [4:0] reg_ddrc_addrmap_row_b14_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b15_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b16_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b17_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP8
   //------------------------
   ,input  [REG_WIDTH-1:0] r502_addrmap8_map0
   ,output [4:0] reg_ddrc_addrmap_row_b10_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b11_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b12_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b13_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP9
   //------------------------
   ,input  [REG_WIDTH-1:0] r503_addrmap9_map0
   ,output [4:0] reg_ddrc_addrmap_row_b6_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b7_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b8_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b9_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP10
   //------------------------
   ,input  [REG_WIDTH-1:0] r504_addrmap10_map0
   ,output [4:0] reg_ddrc_addrmap_row_b2_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b3_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b4_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b5_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP11
   //------------------------
   ,input  [REG_WIDTH-1:0] r505_addrmap11_map0
   ,output [4:0] reg_ddrc_addrmap_row_b0_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b1_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP12
   //------------------------
   ,input  [REG_WIDTH -1:0] r506_addrmap12_map0
   ,output [2:0] reg_ddrc_nonbinary_device_density_map0 // @core_ddrc_core_clk
   ,output reg_ddrc_bank_hash_en_map0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.PCCFG
   //------------------------
   ,input  [REG_WIDTH-1:0] r521_pccfg_port0
   ,output reg_arb_go2critical_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_pagematch_limit_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.PCFGR
   //------------------------
   ,input  [REG_WIDTH-1:0] r522_pcfgr_port0
   ,output [9:0] reg_arb_rd_port_priority_port0 // @core_ddrc_core_clk
   ,output reg_arb_rd_port_aging_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_rd_port_urgent_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_rd_port_pagematch_en_port0 // @core_ddrc_core_clk
   ,output [3:0] reg_arb_rrb_lock_threshold_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.PCFGW
   //------------------------
   ,input  [REG_WIDTH-1:0] r523_pcfgw_port0
   ,output [9:0] reg_arb_wr_port_priority_port0 // @core_ddrc_core_clk
   ,output reg_arb_wr_port_aging_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_wr_port_urgent_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_wr_port_pagematch_en_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.PCTRL
   //------------------------
   ,input  [REG_WIDTH -1:0] r556_pctrl_port0
   ,output reg_arb_port_en_port0 // @core_ddrc_core_clk
   ,output reg_apb_port_en_port0 // @pclk
   ,output reg_arba0_port_en_port0 // @aclk_0
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS0
   //------------------------
   ,input  [REG_WIDTH-1:0] r557_pcfgqos0_port0
   ,output [(`UMCTL2_XPI_RQOS_MLW)-1:0] reg_arba0_rqos_map_level1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_MLW)-1:0] reg_arba0_rqos_map_level2_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region0_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region2_port0 // @aclk_0
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS1
   //------------------------
   ,input  [REG_WIDTH-1:0] r558_pcfgqos1_port0
   ,output [(`UMCTL2_XPI_RQOS_TW)-1:0] reg_arb_rqos_map_timeoutb_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_XPI_RQOS_TW)-1:0] reg_arb_rqos_map_timeoutr_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS0
   //------------------------
   ,input  [REG_WIDTH-1:0] r559_pcfgwqos0_port0
   ,output [(`UMCTL2_XPI_WQOS_MLW)-1:0] reg_arba0_wqos_map_level1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_MLW)-1:0] reg_arba0_wqos_map_level2_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region0_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region2_port0 // @aclk_0
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS1
   //------------------------
   ,input  [REG_WIDTH-1:0] r560_pcfgwqos1_port0
   ,output [(`UMCTL2_XPI_WQOS_TW)-1:0] reg_arb_wqos_map_timeout1_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_XPI_WQOS_TW)-1:0] reg_arb_wqos_map_timeout2_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRCTL
   //------------------------
   ,input  [REG_WIDTH -1:0] r569_sbrctl_port0
   ,output reg_arb_scrub_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_scrub_during_lowpower_port0 // @core_ddrc_core_clk
   ,output [2:0] reg_arb_scrub_burst_length_nm_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_REG_SCRUB_INTERVALW)-1:0] reg_arb_scrub_interval_port0 // @core_ddrc_core_clk
   ,output [1:0] reg_arb_scrub_cmd_type_port0 // @core_ddrc_core_clk
   ,output [2:0] reg_arb_scrub_burst_length_lp_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r570_sbrstat_port0
   ,input arb_reg_scrub_busy_port0 // @core_ddrc_core_clk
   ,input arb_reg_scrub_done_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRWDATA0
   //------------------------
   ,input  [REG_WIDTH -1:0] r571_sbrwdata0_port0
   ,output [31:0] reg_arb_scrub_pattern0_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART0
   //------------------------
   ,input  [REG_WIDTH -1:0] r573_sbrstart0_port0
   ,output [31:0] reg_arb_sbr_address_start_mask_0_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART1
   //------------------------
   ,input  [REG_WIDTH -1:0] r574_sbrstart1_port0
   ,output [(`MEMC_HIF_ADDR_WIDTH_MAX-32)-1:0] reg_arb_sbr_address_start_mask_1_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE0
   //------------------------
   ,input  [REG_WIDTH -1:0] r575_sbrrange0_port0
   ,output [31:0] reg_arb_sbr_address_range_mask_0_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE1
   //------------------------
   ,input  [REG_WIDTH -1:0] r576_sbrrange1_port0
   ,output [(`MEMC_HIF_ADDR_WIDTH_MAX-32)-1:0] reg_arb_sbr_address_range_mask_1_port0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_ARB_PORT0.PSTAT
   //------------------------
   ,output  reg  [REG_WIDTH -1:0] r582_pstat_port0
   ,input arb_reg_rd_port_busy_0_port0 // @aclk_0
   ,input arb_reg_wr_port_busy_0_port0 // @aclk_0
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r1929_dramset1tmg0_freq0
   ,output [7:0] reg_ddrc_t_ras_min_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r1930_dramset1tmg1_freq0
   ,output [7:0] reg_ddrc_t_rc_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r1931_dramset1tmg2_freq0
   ,output [7:0] reg_ddrc_wr2rd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r1932_dramset1tmg3_freq0
   ,output [7:0] reg_ddrc_wr2mr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r1933_dramset1tmg4_freq0
   ,output [6:0] reg_ddrc_t_rp_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG5
   //------------------------
   ,input  [REG_WIDTH -1:0] r1934_dramset1tmg5_freq0
   ,output [5:0] reg_ddrc_t_cke_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r1935_dramset1tmg6_freq0
   ,output [5:0] reg_ddrc_t_ckcsx_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG7
   //------------------------
   ,input  [REG_WIDTH -1:0] r1936_dramset1tmg7_freq0
   ,output [3:0] reg_ddrc_t_csh_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG9
   //------------------------
   ,input  [REG_WIDTH-1:0] r1938_dramset1tmg9_freq0
   ,output [7:0] reg_ddrc_wr2rd_s_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG12
   //------------------------
   ,input  [REG_WIDTH-1:0] r1941_dramset1tmg12_freq0
   ,output [3:0] reg_ddrc_t_cmdcke_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG13
   //------------------------
   ,input  [REG_WIDTH-1:0] r1942_dramset1tmg13_freq0
   ,output [3:0] reg_ddrc_t_ppd_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG14
   //------------------------
   ,input  [REG_WIDTH-1:0] r1943_dramset1tmg14_freq0
   ,output [11:0] reg_ddrc_t_xsr_freq0 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG17
   //------------------------
   ,input  [REG_WIDTH-1:0] r1946_dramset1tmg17_freq0
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG23
   //------------------------
   ,input  [REG_WIDTH -1:0] r1951_dramset1tmg23_freq0
   ,output [11:0] reg_ddrc_t_pdn_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG24
   //------------------------
   ,input  [REG_WIDTH-1:0] r1952_dramset1tmg24_freq0
   ,output [7:0] reg_ddrc_max_wr_sync_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq0 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG25
   //------------------------
   ,input  [REG_WIDTH-1:0] r1953_dramset1tmg25_freq0
   ,output [7:0] reg_ddrc_rda2pre_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq0 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG30
   //------------------------
   ,input  [REG_WIDTH -1:0] r1958_dramset1tmg30_freq0
   ,output [7:0] reg_ddrc_mrr2rd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG32
   //------------------------
   ,input  [REG_WIDTH -1:0] r1960_dramset1tmg32_freq0
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR0
   //------------------------
   ,input  [REG_WIDTH-1:0] r1991_initmr0_freq0
   ,output [15:0] reg_ddrc_emr_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR1
   //------------------------
   ,input  [REG_WIDTH -1:0] r1992_initmr1_freq0
   ,output [15:0] reg_ddrc_emr3_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR2
   //------------------------
   ,input  [REG_WIDTH-1:0] r1993_initmr2_freq0
   ,output [15:0] reg_ddrc_mr5_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR3
   //------------------------
   ,input  [REG_WIDTH-1:0] r1994_initmr3_freq0
   ,output [15:0] reg_ddrc_mr6_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r1995_dfitmg0_freq0
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r1996_dfitmg1_freq0
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r1997_dfitmg2_freq0
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r1999_dfitmg4_freq0
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG5
   //------------------------
   ,input  [REG_WIDTH-1:0] r2000_dfitmg5_freq0
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2001_dfitmg6_freq0
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2003_dfilptmg0_freq0
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_pd_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_sr_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_dsm_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2004_dfilptmg1_freq0
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_data_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_tlp_resp_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2005_dfiupdtmg0_freq0
   ,output [9:0] reg_ddrc_dfi_t_ctrlup_min_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_dfi_t_ctrlup_max_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2006_dfiupdtmg1_freq0
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2008_dfiupdtmg2_freq0
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq0 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2009_dfiupdtmg3_freq0
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2010_rfshset1tmg0_freq0
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2011_rfshset1tmg1_freq0
   ,output [11:0] reg_ddrc_t_rfc_min_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2012_rfshset1tmg2_freq0
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG3
   //------------------------
   ,input  [REG_WIDTH -1:0] r2013_rfshset1tmg3_freq0
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG4
   //------------------------
   ,input  [REG_WIDTH -1:0] r2014_rfshset1tmg4_freq0
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RFMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2024_rfmset1tmg0_freq0
   ,output [11:0] reg_ddrc_t_rfmpb_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2035_zqset1tmg0_freq0
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2036_zqset1tmg1_freq0
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2037_zqset1tmg2_freq0
   ,output [6:0] reg_ddrc_t_zq_stop_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DQSOSCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2046_dqsoscctl0_freq0
   ,output reg_ddrc_dqsosc_enable_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEINT
   //------------------------
   ,input  [REG_WIDTH-1:0] r2047_derateint_freq0
   ,output [31:0] reg_ddrc_mr4_read_interval_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2048_derateval0_freq0
   ,output [5:0] reg_ddrc_derated_t_rrd_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2049_derateval1_freq0
   ,output [7:0] reg_ddrc_derated_t_rc_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.HWLPTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2050_hwlptmg0_freq0
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DVFSCTL0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2051_dvfsctl0_freq0
   ,output reg_ddrc_dvfsq_enable_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.SCHEDTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2052_schedtmg0_freq0
   ,output [7:0] reg_ddrc_pageclose_timer_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.PERFHPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2053_perfhpr1_freq0
   ,output [15:0] reg_ddrc_hpr_max_starve_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.PERFLPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2054_perflpr1_freq0
   ,output [15:0] reg_ddrc_lpr_max_starve_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.PERFWR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2055_perfwr1_freq0
   ,output [15:0] reg_ddrc_w_max_starve_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.TMGCFG
   //------------------------
   ,input  [REG_WIDTH -1:0] r2056_tmgcfg_freq0
   ,output reg_ddrc_frequency_ratio_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2057_ranktmg0_freq0
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2058_ranktmg1_freq0
   ,output [7:0] reg_ddrc_wr2rd_dr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.PWRTMG
   //------------------------
   ,input  [REG_WIDTH-1:0] r2059_pwrtmg_freq0
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2065_ddr4pprtmg0_freq0
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2066_ddr4pprtmg1_freq0
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ0_CH0.LNKECCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2067_lnkeccctl0_freq0
   ,output reg_ddrc_wr_link_ecc_enable_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq0 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2201_dramset1tmg0_freq1
   ,output [7:0] reg_ddrc_t_ras_min_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2202_dramset1tmg1_freq1
   ,output [7:0] reg_ddrc_t_rc_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2203_dramset1tmg2_freq1
   ,output [7:0] reg_ddrc_wr2rd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2204_dramset1tmg3_freq1
   ,output [7:0] reg_ddrc_wr2mr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r2205_dramset1tmg4_freq1
   ,output [6:0] reg_ddrc_t_rp_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG5
   //------------------------
   ,input  [REG_WIDTH -1:0] r2206_dramset1tmg5_freq1
   ,output [5:0] reg_ddrc_t_cke_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2207_dramset1tmg6_freq1
   ,output [5:0] reg_ddrc_t_ckcsx_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG7
   //------------------------
   ,input  [REG_WIDTH -1:0] r2208_dramset1tmg7_freq1
   ,output [3:0] reg_ddrc_t_csh_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG9
   //------------------------
   ,input  [REG_WIDTH-1:0] r2210_dramset1tmg9_freq1
   ,output [7:0] reg_ddrc_wr2rd_s_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG12
   //------------------------
   ,input  [REG_WIDTH-1:0] r2213_dramset1tmg12_freq1
   ,output [3:0] reg_ddrc_t_cmdcke_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG13
   //------------------------
   ,input  [REG_WIDTH-1:0] r2214_dramset1tmg13_freq1
   ,output [3:0] reg_ddrc_t_ppd_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG14
   //------------------------
   ,input  [REG_WIDTH-1:0] r2215_dramset1tmg14_freq1
   ,output [11:0] reg_ddrc_t_xsr_freq1 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG17
   //------------------------
   ,input  [REG_WIDTH-1:0] r2218_dramset1tmg17_freq1
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG23
   //------------------------
   ,input  [REG_WIDTH -1:0] r2223_dramset1tmg23_freq1
   ,output [11:0] reg_ddrc_t_pdn_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG24
   //------------------------
   ,input  [REG_WIDTH-1:0] r2224_dramset1tmg24_freq1
   ,output [7:0] reg_ddrc_max_wr_sync_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq1 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG25
   //------------------------
   ,input  [REG_WIDTH-1:0] r2225_dramset1tmg25_freq1
   ,output [7:0] reg_ddrc_rda2pre_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq1 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG30
   //------------------------
   ,input  [REG_WIDTH -1:0] r2230_dramset1tmg30_freq1
   ,output [7:0] reg_ddrc_mrr2rd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG32
   //------------------------
   ,input  [REG_WIDTH -1:0] r2232_dramset1tmg32_freq1
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2263_initmr0_freq1
   ,output [15:0] reg_ddrc_emr_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2264_initmr1_freq1
   ,output [15:0] reg_ddrc_emr3_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2265_initmr2_freq1
   ,output [15:0] reg_ddrc_mr5_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2266_initmr3_freq1
   ,output [15:0] reg_ddrc_mr6_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2267_dfitmg0_freq1
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2268_dfitmg1_freq1
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2269_dfitmg2_freq1
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r2271_dfitmg4_freq1
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG5
   //------------------------
   ,input  [REG_WIDTH-1:0] r2272_dfitmg5_freq1
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2273_dfitmg6_freq1
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2275_dfiupdtmg1_freq1
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2276_dfiupdtmg2_freq1
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq1 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2277_dfiupdtmg3_freq1
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2278_rfshset1tmg0_freq1
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2279_rfshset1tmg1_freq1
   ,output [11:0] reg_ddrc_t_rfc_min_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2280_rfshset1tmg2_freq1
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG3
   //------------------------
   ,input  [REG_WIDTH -1:0] r2281_rfshset1tmg3_freq1
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG4
   //------------------------
   ,input  [REG_WIDTH -1:0] r2282_rfshset1tmg4_freq1
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RFMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2292_rfmset1tmg0_freq1
   ,output [11:0] reg_ddrc_t_rfmpb_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2303_zqset1tmg0_freq1
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2304_zqset1tmg1_freq1
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2305_zqset1tmg2_freq1
   ,output [6:0] reg_ddrc_t_zq_stop_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DQSOSCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2314_dqsoscctl0_freq1
   ,output reg_ddrc_dqsosc_enable_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEINT
   //------------------------
   ,input  [REG_WIDTH-1:0] r2315_derateint_freq1
   ,output [31:0] reg_ddrc_mr4_read_interval_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2316_derateval0_freq1
   ,output [5:0] reg_ddrc_derated_t_rrd_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2317_derateval1_freq1
   ,output [7:0] reg_ddrc_derated_t_rc_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.HWLPTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2318_hwlptmg0_freq1
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DVFSCTL0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2319_dvfsctl0_freq1
   ,output reg_ddrc_dvfsq_enable_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.SCHEDTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2320_schedtmg0_freq1
   ,output [7:0] reg_ddrc_pageclose_timer_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.PERFHPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2321_perfhpr1_freq1
   ,output [15:0] reg_ddrc_hpr_max_starve_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.PERFLPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2322_perflpr1_freq1
   ,output [15:0] reg_ddrc_lpr_max_starve_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.PERFWR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2323_perfwr1_freq1
   ,output [15:0] reg_ddrc_w_max_starve_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.TMGCFG
   //------------------------
   ,input  [REG_WIDTH -1:0] r2324_tmgcfg_freq1
   ,output reg_ddrc_frequency_ratio_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2325_ranktmg0_freq1
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2326_ranktmg1_freq1
   ,output [7:0] reg_ddrc_wr2rd_dr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.PWRTMG
   //------------------------
   ,input  [REG_WIDTH-1:0] r2327_pwrtmg_freq1
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2333_ddr4pprtmg0_freq1
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2334_ddr4pprtmg1_freq1
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ1_CH0.LNKECCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2335_lnkeccctl0_freq1
   ,output reg_ddrc_wr_link_ecc_enable_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq1 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2469_dramset1tmg0_freq2
   ,output [7:0] reg_ddrc_t_ras_min_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2470_dramset1tmg1_freq2
   ,output [7:0] reg_ddrc_t_rc_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2471_dramset1tmg2_freq2
   ,output [7:0] reg_ddrc_wr2rd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2472_dramset1tmg3_freq2
   ,output [7:0] reg_ddrc_wr2mr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r2473_dramset1tmg4_freq2
   ,output [6:0] reg_ddrc_t_rp_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG5
   //------------------------
   ,input  [REG_WIDTH -1:0] r2474_dramset1tmg5_freq2
   ,output [5:0] reg_ddrc_t_cke_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2475_dramset1tmg6_freq2
   ,output [5:0] reg_ddrc_t_ckcsx_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG7
   //------------------------
   ,input  [REG_WIDTH -1:0] r2476_dramset1tmg7_freq2
   ,output [3:0] reg_ddrc_t_csh_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG9
   //------------------------
   ,input  [REG_WIDTH-1:0] r2478_dramset1tmg9_freq2
   ,output [7:0] reg_ddrc_wr2rd_s_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG12
   //------------------------
   ,input  [REG_WIDTH-1:0] r2481_dramset1tmg12_freq2
   ,output [3:0] reg_ddrc_t_cmdcke_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG13
   //------------------------
   ,input  [REG_WIDTH-1:0] r2482_dramset1tmg13_freq2
   ,output [3:0] reg_ddrc_t_ppd_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG14
   //------------------------
   ,input  [REG_WIDTH-1:0] r2483_dramset1tmg14_freq2
   ,output [11:0] reg_ddrc_t_xsr_freq2 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG17
   //------------------------
   ,input  [REG_WIDTH-1:0] r2486_dramset1tmg17_freq2
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG23
   //------------------------
   ,input  [REG_WIDTH -1:0] r2491_dramset1tmg23_freq2
   ,output [11:0] reg_ddrc_t_pdn_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG24
   //------------------------
   ,input  [REG_WIDTH-1:0] r2492_dramset1tmg24_freq2
   ,output [7:0] reg_ddrc_max_wr_sync_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq2 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG25
   //------------------------
   ,input  [REG_WIDTH-1:0] r2493_dramset1tmg25_freq2
   ,output [7:0] reg_ddrc_rda2pre_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq2 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG30
   //------------------------
   ,input  [REG_WIDTH -1:0] r2498_dramset1tmg30_freq2
   ,output [7:0] reg_ddrc_mrr2rd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG32
   //------------------------
   ,input  [REG_WIDTH -1:0] r2500_dramset1tmg32_freq2
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2531_initmr0_freq2
   ,output [15:0] reg_ddrc_emr_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2532_initmr1_freq2
   ,output [15:0] reg_ddrc_emr3_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2533_initmr2_freq2
   ,output [15:0] reg_ddrc_mr5_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2534_initmr3_freq2
   ,output [15:0] reg_ddrc_mr6_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2535_dfitmg0_freq2
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2536_dfitmg1_freq2
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2537_dfitmg2_freq2
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r2539_dfitmg4_freq2
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG5
   //------------------------
   ,input  [REG_WIDTH-1:0] r2540_dfitmg5_freq2
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2541_dfitmg6_freq2
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2543_dfiupdtmg1_freq2
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2544_dfiupdtmg2_freq2
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq2 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2545_dfiupdtmg3_freq2
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2546_rfshset1tmg0_freq2
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2547_rfshset1tmg1_freq2
   ,output [11:0] reg_ddrc_t_rfc_min_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2548_rfshset1tmg2_freq2
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG3
   //------------------------
   ,input  [REG_WIDTH -1:0] r2549_rfshset1tmg3_freq2
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG4
   //------------------------
   ,input  [REG_WIDTH -1:0] r2550_rfshset1tmg4_freq2
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RFMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2560_rfmset1tmg0_freq2
   ,output [11:0] reg_ddrc_t_rfmpb_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2571_zqset1tmg0_freq2
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2572_zqset1tmg1_freq2
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2573_zqset1tmg2_freq2
   ,output [6:0] reg_ddrc_t_zq_stop_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DQSOSCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2582_dqsoscctl0_freq2
   ,output reg_ddrc_dqsosc_enable_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEINT
   //------------------------
   ,input  [REG_WIDTH-1:0] r2583_derateint_freq2
   ,output [31:0] reg_ddrc_mr4_read_interval_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2584_derateval0_freq2
   ,output [5:0] reg_ddrc_derated_t_rrd_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2585_derateval1_freq2
   ,output [7:0] reg_ddrc_derated_t_rc_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.HWLPTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2586_hwlptmg0_freq2
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DVFSCTL0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2587_dvfsctl0_freq2
   ,output reg_ddrc_dvfsq_enable_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.SCHEDTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2588_schedtmg0_freq2
   ,output [7:0] reg_ddrc_pageclose_timer_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.PERFHPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2589_perfhpr1_freq2
   ,output [15:0] reg_ddrc_hpr_max_starve_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.PERFLPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2590_perflpr1_freq2
   ,output [15:0] reg_ddrc_lpr_max_starve_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.PERFWR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2591_perfwr1_freq2
   ,output [15:0] reg_ddrc_w_max_starve_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.TMGCFG
   //------------------------
   ,input  [REG_WIDTH -1:0] r2592_tmgcfg_freq2
   ,output reg_ddrc_frequency_ratio_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2593_ranktmg0_freq2
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2594_ranktmg1_freq2
   ,output [7:0] reg_ddrc_wr2rd_dr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.PWRTMG
   //------------------------
   ,input  [REG_WIDTH-1:0] r2595_pwrtmg_freq2
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2601_ddr4pprtmg0_freq2
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2602_ddr4pprtmg1_freq2
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ2_CH0.LNKECCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2603_lnkeccctl0_freq2
   ,output reg_ddrc_wr_link_ecc_enable_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq2 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2737_dramset1tmg0_freq3
   ,output [7:0] reg_ddrc_t_ras_min_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2738_dramset1tmg1_freq3
   ,output [7:0] reg_ddrc_t_rc_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2739_dramset1tmg2_freq3
   ,output [7:0] reg_ddrc_wr2rd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2740_dramset1tmg3_freq3
   ,output [7:0] reg_ddrc_wr2mr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r2741_dramset1tmg4_freq3
   ,output [6:0] reg_ddrc_t_rp_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG5
   //------------------------
   ,input  [REG_WIDTH -1:0] r2742_dramset1tmg5_freq3
   ,output [5:0] reg_ddrc_t_cke_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2743_dramset1tmg6_freq3
   ,output [5:0] reg_ddrc_t_ckcsx_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG7
   //------------------------
   ,input  [REG_WIDTH -1:0] r2744_dramset1tmg7_freq3
   ,output [3:0] reg_ddrc_t_csh_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG9
   //------------------------
   ,input  [REG_WIDTH-1:0] r2746_dramset1tmg9_freq3
   ,output [7:0] reg_ddrc_wr2rd_s_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG12
   //------------------------
   ,input  [REG_WIDTH-1:0] r2749_dramset1tmg12_freq3
   ,output [3:0] reg_ddrc_t_cmdcke_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG13
   //------------------------
   ,input  [REG_WIDTH-1:0] r2750_dramset1tmg13_freq3
   ,output [3:0] reg_ddrc_t_ppd_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG14
   //------------------------
   ,input  [REG_WIDTH-1:0] r2751_dramset1tmg14_freq3
   ,output [11:0] reg_ddrc_t_xsr_freq3 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG17
   //------------------------
   ,input  [REG_WIDTH-1:0] r2754_dramset1tmg17_freq3
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG23
   //------------------------
   ,input  [REG_WIDTH -1:0] r2759_dramset1tmg23_freq3
   ,output [11:0] reg_ddrc_t_pdn_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG24
   //------------------------
   ,input  [REG_WIDTH-1:0] r2760_dramset1tmg24_freq3
   ,output [7:0] reg_ddrc_max_wr_sync_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq3 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG25
   //------------------------
   ,input  [REG_WIDTH-1:0] r2761_dramset1tmg25_freq3
   ,output [7:0] reg_ddrc_rda2pre_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq3 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG30
   //------------------------
   ,input  [REG_WIDTH -1:0] r2766_dramset1tmg30_freq3
   ,output [7:0] reg_ddrc_mrr2rd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG32
   //------------------------
   ,input  [REG_WIDTH -1:0] r2768_dramset1tmg32_freq3
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2799_initmr0_freq3
   ,output [15:0] reg_ddrc_emr_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2800_initmr1_freq3
   ,output [15:0] reg_ddrc_emr3_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2801_initmr2_freq3
   ,output [15:0] reg_ddrc_mr5_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2802_initmr3_freq3
   ,output [15:0] reg_ddrc_mr6_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2803_dfitmg0_freq3
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2804_dfitmg1_freq3
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG2
   //------------------------
   ,input  [REG_WIDTH-1:0] r2805_dfitmg2_freq3
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG4
   //------------------------
   ,input  [REG_WIDTH-1:0] r2807_dfitmg4_freq3
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG5
   //------------------------
   ,input  [REG_WIDTH-1:0] r2808_dfitmg5_freq3
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG6
   //------------------------
   ,input  [REG_WIDTH-1:0] r2809_dfitmg6_freq3
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2811_dfiupdtmg1_freq3
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2812_dfiupdtmg2_freq3
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq3 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG3
   //------------------------
   ,input  [REG_WIDTH-1:0] r2813_dfiupdtmg3_freq3
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2814_rfshset1tmg0_freq3
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2815_rfshset1tmg1_freq3
   ,output [11:0] reg_ddrc_t_rfc_min_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2816_rfshset1tmg2_freq3
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG3
   //------------------------
   ,input  [REG_WIDTH -1:0] r2817_rfshset1tmg3_freq3
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG4
   //------------------------
   ,input  [REG_WIDTH -1:0] r2818_rfshset1tmg4_freq3
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RFMSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2828_rfmset1tmg0_freq3
   ,output [11:0] reg_ddrc_t_rfmpb_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2839_zqset1tmg0_freq3
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2840_zqset1tmg1_freq3
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG2
   //------------------------
   ,input  [REG_WIDTH -1:0] r2841_zqset1tmg2_freq3
   ,output [6:0] reg_ddrc_t_zq_stop_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DQSOSCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2850_dqsoscctl0_freq3
   ,output reg_ddrc_dqsosc_enable_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEINT
   //------------------------
   ,input  [REG_WIDTH-1:0] r2851_derateint_freq3
   ,output [31:0] reg_ddrc_mr4_read_interval_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2852_derateval0_freq3
   ,output [5:0] reg_ddrc_derated_t_rrd_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL1
   //------------------------
   ,input  [REG_WIDTH -1:0] r2853_derateval1_freq3
   ,output [7:0] reg_ddrc_derated_t_rc_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.HWLPTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2854_hwlptmg0_freq3
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DVFSCTL0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2855_dvfsctl0_freq3
   ,output reg_ddrc_dvfsq_enable_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.SCHEDTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2856_schedtmg0_freq3
   ,output [7:0] reg_ddrc_pageclose_timer_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.PERFHPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2857_perfhpr1_freq3
   ,output [15:0] reg_ddrc_hpr_max_starve_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.PERFLPR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2858_perflpr1_freq3
   ,output [15:0] reg_ddrc_lpr_max_starve_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.PERFWR1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2859_perfwr1_freq3
   ,output [15:0] reg_ddrc_w_max_starve_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.TMGCFG
   //------------------------
   ,input  [REG_WIDTH -1:0] r2860_tmgcfg_freq3
   ,output reg_ddrc_frequency_ratio_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2861_ranktmg0_freq3
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2862_ranktmg1_freq3
   ,output [7:0] reg_ddrc_wr2rd_dr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.PWRTMG
   //------------------------
   ,input  [REG_WIDTH-1:0] r2863_pwrtmg_freq3
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG0
   //------------------------
   ,input  [REG_WIDTH-1:0] r2869_ddr4pprtmg0_freq3
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG1
   //------------------------
   ,input  [REG_WIDTH-1:0] r2870_ddr4pprtmg1_freq3
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq3 // @core_ddrc_core_clk
   //------------------------
   // Register REGB_FREQ3_CH0.LNKECCCTL0
   //------------------------
   ,input  [REG_WIDTH -1:0] r2871_lnkeccctl0_freq3
   ,output reg_ddrc_wr_link_ecc_enable_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq3 // @core_ddrc_core_clk

    ,output              ecc_corrected_err_intr_en
    ,output              ecc_uncorrected_err_intr_en
    ,output              ecc_ap_err_intr_en
    ,output              pclk_derate_temp_limit_intr
     ,input ddrc_reg_ecc_ap_err_int
     ,output pclk_ddrc_reg_ecc_ap_err
    ,input  [ECC_CORRECTED_ERR_WIDTH-1:0]      ddrc_reg_ecc_corrected_err_int
    ,input  [ECC_UNCORRECTED_ERR_WIDTH-1:0]    ddrc_reg_ecc_uncorrected_err_int
    ,input  [ECC_CORRECTED_BIT_NUM_WIDTH-1:0]  ddrc_reg_ecc_corrected_bit_num_int
    ,output [ECC_CORRECTED_ERR_WIDTH-1:0]      pclk_ddrc_reg_ecc_corrected_err
    ,output [ECC_UNCORRECTED_ERR_WIDTH-1:0]    pclk_ddrc_reg_ecc_uncorrected_err
    ,output [ECC_CORRECTED_BIT_NUM_WIDTH-1:0]  pclk_ddrc_reg_ecc_corrected_bit_num
    ,input  [1:0]                              ddrc_reg_sbr_read_ecc_err_int
    ,output [1:0]                              pclk_ddrc_reg_sbr_read_ecc_err




    ,input  [3:0]  ddrc_reg_rd_linkecc_uncorr_err_intr
    ,input  [3:0]  ddrc_reg_rd_linkecc_corr_err_intr
    ,output [3:0]  pclk_ddrc_reg_rd_linkecc_uncorr_err_int
    ,output [3:0]  pclk_ddrc_reg_rd_linkecc_corr_err_int
    ,output        rd_link_ecc_uncorr_intr_en
    ,output        rd_link_ecc_corr_intr_en


   );
   
   localparam TMR_EN = 0; //`UMCTL2_REGPAR_EN;
   localparam WAIT_ACK_TIMEOUT = 96;
 





   //------------------------
   // Register REGB_DDRC_CH0.MSTR0
   //------------------------
   assign reg_ddrc_lpddr4 = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR4+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR4];
   assign reg_apb_lpddr4 = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR4+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR4];
   assign reg_arba0_lpddr4 = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR4+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR4];
   assign reg_ddrc_lpddr5 = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5];
   assign reg_apb_lpddr5 = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5];
   assign reg_arba0_lpddr5 = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5];
   assign reg_ddrc_lpddr5x = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5X+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5X];
   assign reg_apb_lpddr5x = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5X+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5X];
   assign reg_arba0_lpddr5x = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_LPDDR5X+:`REGB_DDRC_CH0_SIZE_MSTR0_LPDDR5X];
   assign reg_ddrc_data_bus_width[(`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_DATA_BUS_WIDTH+:`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH];
   assign reg_apb_data_bus_width[(`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_DATA_BUS_WIDTH+:`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH];
   assign reg_arba0_data_bus_width[(`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_DATA_BUS_WIDTH+:`REGB_DDRC_CH0_SIZE_MSTR0_DATA_BUS_WIDTH];
   assign reg_ddrc_burst_rdwr[(`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_BURST_RDWR+:`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR];
   assign reg_apb_burst_rdwr[(`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_BURST_RDWR+:`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR];
   assign reg_arba0_burst_rdwr[(`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_BURST_RDWR+:`REGB_DDRC_CH0_SIZE_MSTR0_BURST_RDWR];
   assign reg_ddrc_active_ranks[(`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_ACTIVE_RANKS+:`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS];
   assign reg_apb_active_ranks[(`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_ACTIVE_RANKS+:`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS];
   assign reg_arba0_active_ranks[(`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS) -1:0] = r0_mstr0[`REGB_DDRC_CH0_OFFSET_MSTR0_ACTIVE_RANKS+:`REGB_DDRC_CH0_SIZE_MSTR0_ACTIVE_RANKS];
   //------------------------
   // Register REGB_DDRC_CH0.MSTR2
   //------------------------
   assign reg_ddrc_target_frequency[(`REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY) -1:0] = r2_mstr2[`REGB_DDRC_CH0_OFFSET_MSTR2_TARGET_FREQUENCY+:`REGB_DDRC_CH0_SIZE_MSTR2_TARGET_FREQUENCY];
   //------------------------
   // Register REGB_DDRC_CH0.MSTR4
   //------------------------
   assign reg_ddrc_wck_on = r4_mstr4[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_ON+:`REGB_DDRC_CH0_SIZE_MSTR4_WCK_ON];
   assign reg_ddrc_wck_suspend_en = r4_mstr4[`REGB_DDRC_CH0_OFFSET_MSTR4_WCK_SUSPEND_EN+:`REGB_DDRC_CH0_SIZE_MSTR4_WCK_SUSPEND_EN];
   assign reg_ddrc_ws_off_en = r4_mstr4[`REGB_DDRC_CH0_OFFSET_MSTR4_WS_OFF_EN+:`REGB_DDRC_CH0_SIZE_MSTR4_WS_OFF_EN];
   //------------------------
   // Register REGB_DDRC_CH0.STAT
   //------------------------
   reg  [REG_WIDTH-1:0] r5_stat_cclk;
   always_comb begin : r5_stat_cclk_combo_PROC
      r5_stat_cclk = {REG_WIDTH{1'b0}};
      r5_stat_cclk[`REGB_DDRC_CH0_OFFSET_STAT_OPERATING_MODE+:`REGB_DDRC_CH0_SIZE_STAT_OPERATING_MODE] = ddrc_reg_operating_mode[(`REGB_DDRC_CH0_SIZE_STAT_OPERATING_MODE) -1:0];
      r5_stat_cclk[`REGB_DDRC_CH0_OFFSET_STAT_SELFREF_TYPE+:`REGB_DDRC_CH0_SIZE_STAT_SELFREF_TYPE] = ddrc_reg_selfref_type[(`REGB_DDRC_CH0_SIZE_STAT_SELFREF_TYPE) -1:0];
      r5_stat_cclk[`REGB_DDRC_CH0_OFFSET_STAT_SELFREF_STATE+:`REGB_DDRC_CH0_SIZE_STAT_SELFREF_STATE] = ddrc_reg_selfref_state[(`REGB_DDRC_CH0_SIZE_STAT_SELFREF_STATE) -1:0];
      r5_stat_cclk[`REGB_DDRC_CH0_OFFSET_STAT_SELFREF_CAM_NOT_EMPTY+:`REGB_DDRC_CH0_SIZE_STAT_SELFREF_CAM_NOT_EMPTY] = ddrc_reg_selfref_cam_not_empty;
   end
   assign r5_stat= r5_stat_cclk ;

   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL0
   //------------------------
   assign reg_ddrc_mr_type = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_TYPE+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_TYPE];
   assign reg_ddrc_sw_init_int = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_SW_INIT_INT+:`REGB_DDRC_CH0_SIZE_MRCTRL0_SW_INIT_INT];
   assign reg_ddrc_mr_rank[(`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK) -1:0] = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_RANK+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_RANK];
   assign reg_ddrc_mr_addr[(`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR) -1:0] = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_ADDR+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_ADDR];
   wire reg_ddrc_mrr_done_clr_pclk;
   assign reg_ddrc_mrr_done_clr_pclk = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MRR_DONE_CLR+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MRR_DONE_CLR];
 reg reg_ddrc_mrr_done_clr_pclk_s0;
 reg reg_ddrc_mrr_done_clr_ack;
 // reset reg_ddrc_mrr_done_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_mrr_done_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_mrr_done_clr_pclk_s0 <= 1'b0;
 reg_ddrc_mrr_done_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_mrr_done_clr_pclk_s0 <= reg_ddrc_mrr_done_clr_pclk;
 reg_ddrc_mrr_done_clr_ack <= reg_ddrc_mrr_done_clr;
 end
 end
 assign reg_ddrc_mrr_done_clr = reg_ddrc_mrr_done_clr_pclk & (!reg_ddrc_mrr_done_clr_pclk_s0);
 assign reg_ddrc_mrr_done_clr_ack_pclk = reg_ddrc_mrr_done_clr_ack;
   assign reg_ddrc_dis_mrrw_trfc = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_DIS_MRRW_TRFC+:`REGB_DDRC_CH0_SIZE_MRCTRL0_DIS_MRRW_TRFC];
   assign reg_ddrc_ppr_en = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_EN+:`REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_EN];
   assign reg_ddrc_ppr_pgmpst_en = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_PPR_PGMPST_EN+:`REGB_DDRC_CH0_SIZE_MRCTRL0_PPR_PGMPST_EN];
   wire reg_ddrc_mr_wr_pclk;
   assign reg_ddrc_mr_wr_pclk = r8_mrctrl0[`REGB_DDRC_CH0_OFFSET_MRCTRL0_MR_WR+:`REGB_DDRC_CH0_SIZE_MRCTRL0_MR_WR];
 reg reg_ddrc_mr_wr_pclk_s0;
 reg reg_ddrc_mr_wr_ack;
 // reset reg_ddrc_mr_wr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_mr_wr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_mr_wr_pclk_s0 <= 1'b0;
 reg_ddrc_mr_wr_ack <= 1'b0;
 end else begin
 reg_ddrc_mr_wr_pclk_s0 <= reg_ddrc_mr_wr_pclk;
 reg_ddrc_mr_wr_ack <= reg_ddrc_mr_wr;
 end
 end
 assign reg_ddrc_mr_wr = reg_ddrc_mr_wr_pclk & (!reg_ddrc_mr_wr_pclk_s0);
 assign reg_ddrc_mr_wr_ack_pclk = reg_ddrc_mr_wr_ack;
 assign ddrc_reg_mr_wr_busy_int = ddrc_reg_mr_wr_busy;
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL1
   //------------------------
   assign reg_ddrc_mr_data[(`REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA) -1:0] = r9_mrctrl1[`REGB_DDRC_CH0_OFFSET_MRCTRL1_MR_DATA+:`REGB_DDRC_CH0_SIZE_MRCTRL1_MR_DATA];
   //------------------------
   // Register REGB_DDRC_CH0.MRSTAT
   //------------------------
   always_comb begin : r11_mrstat_combo_PROC
      r11_mrstat = {REG_WIDTH{1'b0}};
      r11_mrstat[`REGB_DDRC_CH0_OFFSET_MRSTAT_MR_WR_BUSY+:`REGB_DDRC_CH0_SIZE_MRSTAT_MR_WR_BUSY] = ddrc_reg_mr_wr_busy | ff_regb_ddrc_ch0_mr_wr_saved;
      r11_mrstat[`REGB_DDRC_CH0_OFFSET_MRSTAT_MRR_DONE+:`REGB_DDRC_CH0_SIZE_MRSTAT_MRR_DONE] = ddrc_reg_mrr_done;
      r11_mrstat[`REGB_DDRC_CH0_OFFSET_MRSTAT_PPR_DONE+:`REGB_DDRC_CH0_SIZE_MRSTAT_PPR_DONE] = ddrc_reg_ppr_done;
   end
   //------------------------
   // Register REGB_DDRC_CH0.MRRDATA0
   //------------------------
   always_comb begin : r12_mrrdata0_combo_PROC
      r12_mrrdata0 = {REG_WIDTH{1'b0}};
      r12_mrrdata0[`REGB_DDRC_CH0_OFFSET_MRRDATA0_MRR_DATA_LWR+:`REGB_DDRC_CH0_SIZE_MRRDATA0_MRR_DATA_LWR] = ddrc_reg_mrr_data_lwr[(`REGB_DDRC_CH0_SIZE_MRRDATA0_MRR_DATA_LWR) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.MRRDATA1
   //------------------------
   always_comb begin : r13_mrrdata1_combo_PROC
      r13_mrrdata1 = {REG_WIDTH{1'b0}};
      r13_mrrdata1[`REGB_DDRC_CH0_OFFSET_MRRDATA1_MRR_DATA_UPR+:`REGB_DDRC_CH0_SIZE_MRRDATA1_MRR_DATA_UPR] = ddrc_reg_mrr_data_upr[(`REGB_DDRC_CH0_SIZE_MRRDATA1_MRR_DATA_UPR) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL0
   //------------------------
   assign reg_ddrc_derate_enable = r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_ENABLE+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_ENABLE];
   assign reg_ddrc_lpddr4_refresh_mode = r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_LPDDR4_REFRESH_MODE+:`REGB_DDRC_CH0_SIZE_DERATECTL0_LPDDR4_REFRESH_MODE];
   assign reg_ddrc_derate_mr4_pause_fc = r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DERATE_MR4_PAUSE_FC+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DERATE_MR4_PAUSE_FC];
   assign reg_ddrc_dis_trefi_x6x8 = r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X6X8+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X6X8];
   assign reg_ddrc_dis_trefi_x0125 = r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_DIS_TREFI_X0125+:`REGB_DDRC_CH0_SIZE_DERATECTL0_DIS_TREFI_X0125];
   assign reg_ddrc_use_slow_rm_in_low_temp = r14_deratectl0[`REGB_DDRC_CH0_OFFSET_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP+:`REGB_DDRC_CH0_SIZE_DERATECTL0_USE_SLOW_RM_IN_LOW_TEMP];
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL1
   //------------------------
   assign reg_ddrc_active_derate_byte_rank0[(`REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0) -1:0] = r15_deratectl1[`REGB_DDRC_CH0_OFFSET_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0+:`REGB_DDRC_CH0_SIZE_DERATECTL1_ACTIVE_DERATE_BYTE_RANK0];
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL2
   //------------------------
   assign reg_ddrc_active_derate_byte_rank1[(`REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1) -1:0] = r16_deratectl2[`REGB_DDRC_CH0_OFFSET_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1+:`REGB_DDRC_CH0_SIZE_DERATECTL2_ACTIVE_DERATE_BYTE_RANK1];
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL5
   //------------------------
   assign reg_ddrc_derate_temp_limit_intr_en = r19_deratectl5[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN+:`REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_EN];
   wire reg_ddrc_derate_temp_limit_intr_clr_pclk;
   assign reg_ddrc_derate_temp_limit_intr_clr_pclk = r19_deratectl5[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR+:`REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_CLR];
 reg reg_ddrc_derate_temp_limit_intr_clr_pclk_s0;
 reg reg_ddrc_derate_temp_limit_intr_clr_ack;
 // reset reg_ddrc_derate_temp_limit_intr_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_derate_temp_limit_intr_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_derate_temp_limit_intr_clr_pclk_s0 <= 1'b0;
 reg_ddrc_derate_temp_limit_intr_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_derate_temp_limit_intr_clr_pclk_s0 <= reg_ddrc_derate_temp_limit_intr_clr_pclk;
 reg_ddrc_derate_temp_limit_intr_clr_ack <= reg_ddrc_derate_temp_limit_intr_clr;
 end
 end
 assign reg_ddrc_derate_temp_limit_intr_clr = reg_ddrc_derate_temp_limit_intr_clr_pclk & (!reg_ddrc_derate_temp_limit_intr_clr_pclk_s0);
 assign reg_ddrc_derate_temp_limit_intr_clr_ack_pclk = reg_ddrc_derate_temp_limit_intr_clr_ack;
   wire reg_ddrc_derate_temp_limit_intr_force_pclk;
   assign reg_ddrc_derate_temp_limit_intr_force_pclk = r19_deratectl5[`REGB_DDRC_CH0_OFFSET_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_DERATECTL5_DERATE_TEMP_LIMIT_INTR_FORCE];
 reg reg_ddrc_derate_temp_limit_intr_force_pclk_s0;
 reg reg_ddrc_derate_temp_limit_intr_force_ack;
 // reset reg_ddrc_derate_temp_limit_intr_force field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_derate_temp_limit_intr_force_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_derate_temp_limit_intr_force_pclk_s0 <= 1'b0;
 reg_ddrc_derate_temp_limit_intr_force_ack <= 1'b0;
 end else begin
 reg_ddrc_derate_temp_limit_intr_force_pclk_s0 <= reg_ddrc_derate_temp_limit_intr_force_pclk;
 reg_ddrc_derate_temp_limit_intr_force_ack <= reg_ddrc_derate_temp_limit_intr_force;
 end
 end
 assign reg_ddrc_derate_temp_limit_intr_force = reg_ddrc_derate_temp_limit_intr_force_pclk & (!reg_ddrc_derate_temp_limit_intr_force_pclk_s0);
 assign reg_ddrc_derate_temp_limit_intr_force_ack_pclk = reg_ddrc_derate_temp_limit_intr_force_ack;
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL6
   //------------------------
   assign reg_ddrc_derate_mr4_tuf_dis = r20_deratectl6[`REGB_DDRC_CH0_OFFSET_DERATECTL6_DERATE_MR4_TUF_DIS+:`REGB_DDRC_CH0_SIZE_DERATECTL6_DERATE_MR4_TUF_DIS];
   //------------------------
   // Register REGB_DDRC_CH0.DERATESTAT0
   //------------------------
   always_comb begin : r22_deratestat0_combo_PROC
      r22_deratestat0 = {REG_WIDTH{1'b0}};
      r22_deratestat0[`REGB_DDRC_CH0_OFFSET_DERATESTAT0_DERATE_TEMP_LIMIT_INTR+:`REGB_DDRC_CH0_SIZE_DERATESTAT0_DERATE_TEMP_LIMIT_INTR] = ddrc_reg_derate_temp_limit_intr;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGCTL
   //------------------------
   assign reg_ddrc_dbg_mr4_rank_sel[(`REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL) -1:0] = r24_deratedbgctl[`REGB_DDRC_CH0_OFFSET_DERATEDBGCTL_DBG_MR4_RANK_SEL+:`REGB_DDRC_CH0_SIZE_DERATEDBGCTL_DBG_MR4_RANK_SEL];
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGSTAT
   //------------------------
   always_comb begin : r25_deratedbgstat_combo_PROC
      r25_deratedbgstat = {REG_WIDTH{1'b0}};
      r25_deratedbgstat[`REGB_DDRC_CH0_OFFSET_DERATEDBGSTAT_DBG_MR4_BYTE0+:`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE0] = ddrc_reg_dbg_mr4_byte0[(`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE0) -1:0];
      r25_deratedbgstat[`REGB_DDRC_CH0_OFFSET_DERATEDBGSTAT_DBG_MR4_BYTE1+:`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE1] = ddrc_reg_dbg_mr4_byte1[(`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE1) -1:0];
      r25_deratedbgstat[`REGB_DDRC_CH0_OFFSET_DERATEDBGSTAT_DBG_MR4_BYTE2+:`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE2] = ddrc_reg_dbg_mr4_byte2[(`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE2) -1:0];
      r25_deratedbgstat[`REGB_DDRC_CH0_OFFSET_DERATEDBGSTAT_DBG_MR4_BYTE3+:`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE3] = ddrc_reg_dbg_mr4_byte3[(`REGB_DDRC_CH0_SIZE_DERATEDBGSTAT_DBG_MR4_BYTE3) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.PWRCTL
   //------------------------
   assign reg_ddrc_selfref_en[(`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN) -1:0] = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_EN+:`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_EN];
   assign reg_ddrc_powerdown_en[(`REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN) -1:0] = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_POWERDOWN_EN+:`REGB_DDRC_CH0_SIZE_PWRCTL_POWERDOWN_EN];
   assign reg_ddrc_en_dfi_dram_clk_disable = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_EN_DFI_DRAM_CLK_DISABLE+:`REGB_DDRC_CH0_SIZE_PWRCTL_EN_DFI_DRAM_CLK_DISABLE];
   assign reg_ddrc_selfref_sw = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_SELFREF_SW+:`REGB_DDRC_CH0_SIZE_PWRCTL_SELFREF_SW];
   assign reg_ddrc_stay_in_selfref = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_STAY_IN_SELFREF+:`REGB_DDRC_CH0_SIZE_PWRCTL_STAY_IN_SELFREF];
   assign reg_ddrc_dis_cam_drain_selfref = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_DIS_CAM_DRAIN_SELFREF+:`REGB_DDRC_CH0_SIZE_PWRCTL_DIS_CAM_DRAIN_SELFREF];
   assign reg_ddrc_lpddr4_sr_allowed = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_LPDDR4_SR_ALLOWED+:`REGB_DDRC_CH0_SIZE_PWRCTL_LPDDR4_SR_ALLOWED];
   assign reg_ddrc_dsm_en = r26_pwrctl[`REGB_DDRC_CH0_OFFSET_PWRCTL_DSM_EN+:`REGB_DDRC_CH0_SIZE_PWRCTL_DSM_EN];
   //------------------------
   // Register REGB_DDRC_CH0.HWLPCTL
   //------------------------
   assign reg_ddrc_hw_lp_en = r27_hwlpctl[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EN+:`REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EN];
   assign reg_ddrc_hw_lp_exit_idle_en = r27_hwlpctl[`REGB_DDRC_CH0_OFFSET_HWLPCTL_HW_LP_EXIT_IDLE_EN+:`REGB_DDRC_CH0_SIZE_HWLPCTL_HW_LP_EXIT_IDLE_EN];
   //------------------------
   // Register REGB_DDRC_CH0.CLKGATECTL
   //------------------------
   assign reg_ddrc_bsm_clk_on[(`REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON) -1:0] = r29_clkgatectl[`REGB_DDRC_CH0_OFFSET_CLKGATECTL_BSM_CLK_ON+:`REGB_DDRC_CH0_SIZE_CLKGATECTL_BSM_CLK_ON];
   //------------------------
   // Register REGB_DDRC_CH0.RFSHMOD0
   //------------------------
   assign reg_ddrc_refresh_burst[(`REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST) -1:0] = r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_REFRESH_BURST+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_REFRESH_BURST];
   assign reg_ddrc_auto_refab_en[(`REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN) -1:0] = r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_AUTO_REFAB_EN+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_AUTO_REFAB_EN];
   assign reg_ddrc_per_bank_refresh = r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH];
   assign reg_ddrc_per_bank_refresh_opt_en = r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_PER_BANK_REFRESH_OPT_EN+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_PER_BANK_REFRESH_OPT_EN];
   assign reg_ddrc_fixed_crit_refpb_bank_en = r30_rfshmod0[`REGB_DDRC_CH0_OFFSET_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN+:`REGB_DDRC_CH0_SIZE_RFSHMOD0_FIXED_CRIT_REFPB_BANK_EN];
   //------------------------
   // Register REGB_DDRC_CH0.RFSHCTL0
   //------------------------
   assign reg_ddrc_dis_auto_refresh = r32_rfshctl0[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_DIS_AUTO_REFRESH+:`REGB_DDRC_CH0_SIZE_RFSHCTL0_DIS_AUTO_REFRESH];
   assign reg_ddrc_refresh_update_level = r32_rfshctl0[`REGB_DDRC_CH0_OFFSET_RFSHCTL0_REFRESH_UPDATE_LEVEL+:`REGB_DDRC_CH0_SIZE_RFSHCTL0_REFRESH_UPDATE_LEVEL];
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD0
   //------------------------
   assign reg_ddrc_rfm_en = r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFM_EN+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RFM_EN];
   assign reg_ddrc_rfmsbc = r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMSBC+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMSBC];
   assign reg_ddrc_raaimt[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT) -1:0] = r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAIMT+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAIMT];
   assign reg_ddrc_raamult[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT) -1:0] = r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAAMULT+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RAAMULT];
   assign reg_ddrc_raadec[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC) -1:0] = r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RAADEC+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RAADEC];
   assign reg_ddrc_rfmth_rm_thr[(`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR) -1:0] = r33_rfmmod0[`REGB_DDRC_CH0_OFFSET_RFMMOD0_RFMTH_RM_THR+:`REGB_DDRC_CH0_SIZE_RFMMOD0_RFMTH_RM_THR];
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD1
   //------------------------
   assign reg_ddrc_init_raa_cnt[(`REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT) -1:0] = r34_rfmmod1[`REGB_DDRC_CH0_OFFSET_RFMMOD1_INIT_RAA_CNT+:`REGB_DDRC_CH0_SIZE_RFMMOD1_INIT_RAA_CNT];
   //------------------------
   // Register REGB_DDRC_CH0.RFMCTL
   //------------------------
   assign reg_ddrc_dbg_raa_rank[(`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK) -1:0] = r35_rfmctl[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_RANK+:`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_RANK];
   assign reg_ddrc_dbg_raa_bg_bank[(`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK) -1:0] = r35_rfmctl[`REGB_DDRC_CH0_OFFSET_RFMCTL_DBG_RAA_BG_BANK+:`REGB_DDRC_CH0_SIZE_RFMCTL_DBG_RAA_BG_BANK];
   //------------------------
   // Register REGB_DDRC_CH0.RFMSTAT
   //------------------------
   always_comb begin : r36_rfmstat_combo_PROC
      r36_rfmstat = {REG_WIDTH{1'b0}};
      r36_rfmstat[`REGB_DDRC_CH0_OFFSET_RFMSTAT_RANK_RAA_CNT_GT0+:`REGB_DDRC_CH0_SIZE_RFMSTAT_RANK_RAA_CNT_GT0] = ddrc_reg_rank_raa_cnt_gt0[(`REGB_DDRC_CH0_SIZE_RFMSTAT_RANK_RAA_CNT_GT0) -1:0];
      r36_rfmstat[`REGB_DDRC_CH0_OFFSET_RFMSTAT_DBG_RAA_CNT+:`REGB_DDRC_CH0_SIZE_RFMSTAT_DBG_RAA_CNT] = ddrc_reg_dbg_raa_cnt[(`REGB_DDRC_CH0_SIZE_RFMSTAT_DBG_RAA_CNT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL0
   //------------------------
   assign reg_ddrc_zq_resistor_shared = r37_zqctl0[`REGB_DDRC_CH0_OFFSET_ZQCTL0_ZQ_RESISTOR_SHARED+:`REGB_DDRC_CH0_SIZE_ZQCTL0_ZQ_RESISTOR_SHARED];
   assign reg_ddrc_dis_auto_zq = r37_zqctl0[`REGB_DDRC_CH0_OFFSET_ZQCTL0_DIS_AUTO_ZQ+:`REGB_DDRC_CH0_SIZE_ZQCTL0_DIS_AUTO_ZQ];
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL1
   //------------------------
   wire reg_ddrc_zq_reset_pclk;
   assign reg_ddrc_zq_reset_pclk = r38_zqctl1[`REGB_DDRC_CH0_OFFSET_ZQCTL1_ZQ_RESET+:`REGB_DDRC_CH0_SIZE_ZQCTL1_ZQ_RESET];
 reg reg_ddrc_zq_reset_pclk_s0;
 reg reg_ddrc_zq_reset_ack;
 // reset reg_ddrc_zq_reset field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_zq_reset_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_zq_reset_pclk_s0 <= 1'b0;
 reg_ddrc_zq_reset_ack <= 1'b0;
 end else begin
 reg_ddrc_zq_reset_pclk_s0 <= reg_ddrc_zq_reset_pclk;
 reg_ddrc_zq_reset_ack <= reg_ddrc_zq_reset;
 end
 end
 assign reg_ddrc_zq_reset = reg_ddrc_zq_reset_pclk & (!reg_ddrc_zq_reset_pclk_s0);
 assign reg_ddrc_zq_reset_ack_pclk = reg_ddrc_zq_reset_ack;
 assign ddrc_reg_zq_reset_busy_int = ddrc_reg_zq_reset_busy;
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL2
   //------------------------
   assign reg_ddrc_dis_srx_zqcl = r39_zqctl2[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL+:`REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL];
   assign reg_ddrc_dis_srx_zqcl_hwffc = r39_zqctl2[`REGB_DDRC_CH0_OFFSET_ZQCTL2_DIS_SRX_ZQCL_HWFFC+:`REGB_DDRC_CH0_SIZE_ZQCTL2_DIS_SRX_ZQCL_HWFFC];
   //------------------------
   // Register REGB_DDRC_CH0.ZQSTAT
   //------------------------
   always_comb begin : r40_zqstat_combo_PROC
      r40_zqstat = {REG_WIDTH{1'b0}};
      r40_zqstat[`REGB_DDRC_CH0_OFFSET_ZQSTAT_ZQ_RESET_BUSY+:`REGB_DDRC_CH0_SIZE_ZQSTAT_ZQ_RESET_BUSY] = ddrc_reg_zq_reset_busy | ff_regb_ddrc_ch0_zq_reset_saved;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCRUNTIME
   //------------------------
   assign reg_ddrc_dqsosc_runtime[(`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME) -1:0] = r41_dqsoscruntime[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_DQSOSC_RUNTIME+:`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_DQSOSC_RUNTIME];
   assign reg_ddrc_wck2dqo_runtime[(`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME) -1:0] = r41_dqsoscruntime[`REGB_DDRC_CH0_OFFSET_DQSOSCRUNTIME_WCK2DQO_RUNTIME+:`REGB_DDRC_CH0_SIZE_DQSOSCRUNTIME_WCK2DQO_RUNTIME];
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCSTAT0
   //------------------------
   reg  [REG_WIDTH-1:0] r42_dqsoscstat0_cclk;
   always_comb begin : r42_dqsoscstat0_cclk_combo_PROC
      r42_dqsoscstat0_cclk = {REG_WIDTH{1'b0}};
      r42_dqsoscstat0_cclk[`REGB_DDRC_CH0_OFFSET_DQSOSCSTAT0_DQSOSC_STATE+:`REGB_DDRC_CH0_SIZE_DQSOSCSTAT0_DQSOSC_STATE] = ddrc_reg_dqsosc_state[(`REGB_DDRC_CH0_SIZE_DQSOSCSTAT0_DQSOSC_STATE) -1:0];
      r42_dqsoscstat0_cclk[`REGB_DDRC_CH0_OFFSET_DQSOSCSTAT0_DQSOSC_PER_RANK_STAT+:`REGB_DDRC_CH0_SIZE_DQSOSCSTAT0_DQSOSC_PER_RANK_STAT] = ddrc_reg_dqsosc_per_rank_stat[(`REGB_DDRC_CH0_SIZE_DQSOSCSTAT0_DQSOSC_PER_RANK_STAT) -1:0];
   end
   assign r42_dqsoscstat0= r42_dqsoscstat0_cclk ;

   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCCFG0
   //------------------------
   assign reg_ddrc_dis_dqsosc_srx = r43_dqsosccfg0[`REGB_DDRC_CH0_OFFSET_DQSOSCCFG0_DIS_DQSOSC_SRX+:`REGB_DDRC_CH0_SIZE_DQSOSCCFG0_DIS_DQSOSC_SRX];
   //------------------------
   // Register REGB_DDRC_CH0.SCHED0
   //------------------------
   assign reg_ddrc_dis_opt_wrecc_collision_flush = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_WRECC_COLLISION_FLUSH];
   assign reg_ddrc_prefer_write = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_WRITE+:`REGB_DDRC_CH0_SIZE_SCHED0_PREFER_WRITE];
   assign reg_ddrc_pageclose = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_PAGECLOSE+:`REGB_DDRC_CH0_SIZE_SCHED0_PAGECLOSE];
   assign reg_ddrc_opt_wrcam_fill_level = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_WRCAM_FILL_LEVEL+:`REGB_DDRC_CH0_SIZE_SCHED0_OPT_WRCAM_FILL_LEVEL];
   assign reg_ddrc_dis_opt_ntt_by_act = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_ACT+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_ACT];
   assign reg_ddrc_dis_opt_ntt_by_pre = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_OPT_NTT_BY_PRE+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_OPT_NTT_BY_PRE];
   assign reg_ddrc_autopre_rmw = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_AUTOPRE_RMW+:`REGB_DDRC_CH0_SIZE_SCHED0_AUTOPRE_RMW];
   assign reg_ddrc_lpr_num_entries[(`REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES) -1:0] = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_LPR_NUM_ENTRIES+:`REGB_DDRC_CH0_SIZE_SCHED0_LPR_NUM_ENTRIES];
   assign reg_ddrc_lpddr4_opt_act_timing = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR4_OPT_ACT_TIMING+:`REGB_DDRC_CH0_SIZE_SCHED0_LPDDR4_OPT_ACT_TIMING];
   assign reg_ddrc_lpddr5_opt_act_timing = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_LPDDR5_OPT_ACT_TIMING+:`REGB_DDRC_CH0_SIZE_SCHED0_LPDDR5_OPT_ACT_TIMING];
   assign reg_ddrc_w_starve_free_running = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_W_STARVE_FREE_RUNNING+:`REGB_DDRC_CH0_SIZE_SCHED0_W_STARVE_FREE_RUNNING];
   assign reg_ddrc_opt_act_lat = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_ACT_LAT+:`REGB_DDRC_CH0_SIZE_SCHED0_OPT_ACT_LAT];
   assign reg_ddrc_prefer_read = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_PREFER_READ+:`REGB_DDRC_CH0_SIZE_SCHED0_PREFER_READ];
   assign reg_ddrc_dis_speculative_act = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_DIS_SPECULATIVE_ACT+:`REGB_DDRC_CH0_SIZE_SCHED0_DIS_SPECULATIVE_ACT];
   assign reg_ddrc_opt_vprw_sch = r45_sched0[`REGB_DDRC_CH0_OFFSET_SCHED0_OPT_VPRW_SCH+:`REGB_DDRC_CH0_SIZE_SCHED0_OPT_VPRW_SCH];
   //------------------------
   // Register REGB_DDRC_CH0.SCHED1
   //------------------------
   assign reg_ddrc_delay_switch_write[(`REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE) -1:0] = r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_DELAY_SWITCH_WRITE+:`REGB_DDRC_CH0_SIZE_SCHED1_DELAY_SWITCH_WRITE];
   assign reg_ddrc_visible_window_limit_wr[(`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR) -1:0] = r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_WR+:`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_WR];
   assign reg_ddrc_visible_window_limit_rd[(`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD) -1:0] = r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_VISIBLE_WINDOW_LIMIT_RD+:`REGB_DDRC_CH0_SIZE_SCHED1_VISIBLE_WINDOW_LIMIT_RD];
   assign reg_ddrc_page_hit_limit_wr[(`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR) -1:0] = r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_WR+:`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_WR];
   assign reg_ddrc_page_hit_limit_rd[(`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD) -1:0] = r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_PAGE_HIT_LIMIT_RD+:`REGB_DDRC_CH0_SIZE_SCHED1_PAGE_HIT_LIMIT_RD];
   assign reg_ddrc_opt_hit_gt_hpr = r46_sched1[`REGB_DDRC_CH0_OFFSET_SCHED1_OPT_HIT_GT_HPR+:`REGB_DDRC_CH0_SIZE_SCHED1_OPT_HIT_GT_HPR];
   //------------------------
   // Register REGB_DDRC_CH0.SCHED3
   //------------------------
   assign reg_ddrc_wrcam_lowthresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH) -1:0] = r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_LOWTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_LOWTHRESH];
   assign reg_ddrc_wrcam_highthresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH) -1:0] = r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_WRCAM_HIGHTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_WRCAM_HIGHTHRESH];
   assign reg_ddrc_wr_pghit_num_thresh[(`REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH) -1:0] = r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_WR_PGHIT_NUM_THRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_WR_PGHIT_NUM_THRESH];
   assign reg_ddrc_rd_pghit_num_thresh[(`REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH) -1:0] = r48_sched3[`REGB_DDRC_CH0_OFFSET_SCHED3_RD_PGHIT_NUM_THRESH+:`REGB_DDRC_CH0_SIZE_SCHED3_RD_PGHIT_NUM_THRESH];
   //------------------------
   // Register REGB_DDRC_CH0.SCHED4
   //------------------------
   assign reg_ddrc_rd_act_idle_gap[(`REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP) -1:0] = r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_ACT_IDLE_GAP+:`REGB_DDRC_CH0_SIZE_SCHED4_RD_ACT_IDLE_GAP];
   assign reg_ddrc_wr_act_idle_gap[(`REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP) -1:0] = r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_ACT_IDLE_GAP+:`REGB_DDRC_CH0_SIZE_SCHED4_WR_ACT_IDLE_GAP];
   assign reg_ddrc_rd_page_exp_cycles[(`REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES) -1:0] = r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_RD_PAGE_EXP_CYCLES+:`REGB_DDRC_CH0_SIZE_SCHED4_RD_PAGE_EXP_CYCLES];
   assign reg_ddrc_wr_page_exp_cycles[(`REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES) -1:0] = r49_sched4[`REGB_DDRC_CH0_OFFSET_SCHED4_WR_PAGE_EXP_CYCLES+:`REGB_DDRC_CH0_SIZE_SCHED4_WR_PAGE_EXP_CYCLES];
   //------------------------
   // Register REGB_DDRC_CH0.SCHED5
   //------------------------
   assign reg_ddrc_wrecc_cam_lowthresh[(`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH) -1:0] = r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_LOWTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_LOWTHRESH];
   assign reg_ddrc_wrecc_cam_highthresh[(`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH) -1:0] = r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_WRECC_CAM_HIGHTHRESH+:`REGB_DDRC_CH0_SIZE_SCHED5_WRECC_CAM_HIGHTHRESH];
   assign reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level = r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL+:`REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_LOADED_WRECC_CAM_FILL_LEVEL];
   assign reg_ddrc_dis_opt_valid_wrecc_cam_fill_level = r50_sched5[`REGB_DDRC_CH0_OFFSET_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL+:`REGB_DDRC_CH0_SIZE_SCHED5_DIS_OPT_VALID_WRECC_CAM_FILL_LEVEL];
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCCTL
   //------------------------
   assign reg_ddrc_hwffc_en[(`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN) -1:0] = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_EN+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_EN];
   assign reg_ddrc_init_fsp = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_FSP+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_FSP];
   assign reg_ddrc_init_vrcg = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_INIT_VRCG+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_INIT_VRCG];
   assign reg_ddrc_target_vrcg = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_TARGET_VRCG+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_TARGET_VRCG];
   assign reg_ddrc_skip_mrw_odtvref = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_MRW_ODTVREF+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_MRW_ODTVREF];
   assign reg_ddrc_skip_zq_stop_start = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_SKIP_ZQ_STOP_START+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_SKIP_ZQ_STOP_START];
   assign reg_ddrc_zq_interval[(`REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL) -1:0] = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_ZQ_INTERVAL+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_ZQ_INTERVAL];
   assign reg_ddrc_hwffc_mode = r51_hwffcctl[`REGB_DDRC_CH0_OFFSET_HWFFCCTL_HWFFC_MODE+:`REGB_DDRC_CH0_SIZE_HWFFCCTL_HWFFC_MODE];
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCSTAT
   //------------------------
   always_comb begin : r52_hwffcstat_combo_PROC
      r52_hwffcstat = {REG_WIDTH{1'b0}};
      r52_hwffcstat[`REGB_DDRC_CH0_OFFSET_HWFFCSTAT_HWFFC_IN_PROGRESS+:`REGB_DDRC_CH0_SIZE_HWFFCSTAT_HWFFC_IN_PROGRESS] = ddrc_reg_hwffc_in_progress;
      r52_hwffcstat[`REGB_DDRC_CH0_OFFSET_HWFFCSTAT_HWFFC_OPERATING_MODE+:`REGB_DDRC_CH0_SIZE_HWFFCSTAT_HWFFC_OPERATING_MODE] = ddrc_reg_hwffc_operating_mode;
      r52_hwffcstat[`REGB_DDRC_CH0_OFFSET_HWFFCSTAT_CURRENT_FREQUENCY+:`REGB_DDRC_CH0_SIZE_HWFFCSTAT_CURRENT_FREQUENCY] = ddrc_reg_current_frequency[(`REGB_DDRC_CH0_SIZE_HWFFCSTAT_CURRENT_FREQUENCY) -1:0];
      r52_hwffcstat[`REGB_DDRC_CH0_OFFSET_HWFFCSTAT_CURRENT_FSP+:`REGB_DDRC_CH0_SIZE_HWFFCSTAT_CURRENT_FSP] = ddrc_reg_current_fsp;
      r52_hwffcstat[`REGB_DDRC_CH0_OFFSET_HWFFCSTAT_CURRENT_VRCG+:`REGB_DDRC_CH0_SIZE_HWFFCSTAT_CURRENT_VRCG] = ddrc_reg_current_vrcg;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DFILPCFG0
   //------------------------
   assign reg_ddrc_dfi_lp_en_pd = r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_PD+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_PD];
   assign reg_ddrc_dfi_lp_en_sr = r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_SR+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_SR];
   assign reg_ddrc_dfi_lp_en_dsm = r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DSM+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DSM];
   assign reg_ddrc_dfi_lp_en_data = r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_EN_DATA+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_EN_DATA];
   assign reg_ddrc_dfi_lp_data_req_en = r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_DFI_LP_DATA_REQ_EN+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_DFI_LP_DATA_REQ_EN];
   assign reg_ddrc_extra_gap_for_dfi_lp_data[(`REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA) -1:0] = r62_dfilpcfg0[`REGB_DDRC_CH0_OFFSET_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA+:`REGB_DDRC_CH0_SIZE_DFILPCFG0_EXTRA_GAP_FOR_DFI_LP_DATA];
   //------------------------
   // Register REGB_DDRC_CH0.DFIUPD0
   //------------------------
   assign reg_ddrc_dfi_phyupd_en = r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DFI_PHYUPD_EN+:`REGB_DDRC_CH0_SIZE_DFIUPD0_DFI_PHYUPD_EN];
   assign reg_ddrc_ctrlupd_pre_srx = r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_CTRLUPD_PRE_SRX+:`REGB_DDRC_CH0_SIZE_DFIUPD0_CTRLUPD_PRE_SRX];
   assign reg_ddrc_dis_auto_ctrlupd_srx = r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD_SRX+:`REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD_SRX];
   assign reg_ddrc_dis_auto_ctrlupd = r63_dfiupd0[`REGB_DDRC_CH0_OFFSET_DFIUPD0_DIS_AUTO_CTRLUPD+:`REGB_DDRC_CH0_SIZE_DFIUPD0_DIS_AUTO_CTRLUPD];
   //------------------------
   // Register REGB_DDRC_CH0.DFIMISC
   //------------------------
   assign reg_ddrc_dfi_init_complete_en = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_COMPLETE_EN+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_COMPLETE_EN];
   assign reg_ddrc_phy_dbi_mode = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_PHY_DBI_MODE+:`REGB_DDRC_CH0_SIZE_DFIMISC_PHY_DBI_MODE];
   assign reg_ddrc_dfi_data_cs_polarity = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_DATA_CS_POLARITY+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_DATA_CS_POLARITY];
   assign reg_ddrc_dfi_reset_n = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_RESET_N+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_RESET_N];
   assign reg_ddrc_dfi_init_start = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_INIT_START+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_INIT_START];
   assign reg_ddrc_lp_optimized_write = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_LP_OPTIMIZED_WRITE+:`REGB_DDRC_CH0_SIZE_DFIMISC_LP_OPTIMIZED_WRITE];
   assign reg_ddrc_dfi_frequency[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY) -1:0] = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQUENCY+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQUENCY];
   assign reg_ddrc_dfi_freq_fsp[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP) -1:0] = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_FREQ_FSP+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_FREQ_FSP];
   assign reg_ddrc_dfi_channel_mode[(`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE) -1:0] = r65_dfimisc[`REGB_DDRC_CH0_OFFSET_DFIMISC_DFI_CHANNEL_MODE+:`REGB_DDRC_CH0_SIZE_DFIMISC_DFI_CHANNEL_MODE];
   //------------------------
   // Register REGB_DDRC_CH0.DFISTAT
   //------------------------
   always_comb begin : r66_dfistat_combo_PROC
      r66_dfistat = {REG_WIDTH{1'b0}};
      r66_dfistat[`REGB_DDRC_CH0_OFFSET_DFISTAT_DFI_INIT_COMPLETE+:`REGB_DDRC_CH0_SIZE_DFISTAT_DFI_INIT_COMPLETE] = ddrc_reg_dfi_init_complete;
      r66_dfistat[`REGB_DDRC_CH0_OFFSET_DFISTAT_DFI_LP_CTRL_ACK_STAT+:`REGB_DDRC_CH0_SIZE_DFISTAT_DFI_LP_CTRL_ACK_STAT] = ddrc_reg_dfi_lp_ctrl_ack_stat;
      r66_dfistat[`REGB_DDRC_CH0_OFFSET_DFISTAT_DFI_LP_DATA_ACK_STAT+:`REGB_DDRC_CH0_SIZE_DFISTAT_DFI_LP_DATA_ACK_STAT] = ddrc_reg_dfi_lp_data_ack_stat;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DFIPHYMSTR
   //------------------------
   assign reg_ddrc_dfi_phymstr_en = r67_dfiphymstr[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_EN+:`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_EN];
   assign reg_ddrc_dfi_phymstr_blk_ref_x32[(`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32) -1:0] = r67_dfiphymstr[`REGB_DDRC_CH0_OFFSET_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32+:`REGB_DDRC_CH0_SIZE_DFIPHYMSTR_DFI_PHYMSTR_BLK_REF_X32];
   //------------------------
   // Register REGB_DDRC_CH0.POISONCFG
   //------------------------
   assign reg_ddrc_wr_poison_slverr_en = r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_SLVERR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_SLVERR_EN];
   assign reg_ddrc_wr_poison_intr_en = r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_EN];
   wire reg_ddrc_wr_poison_intr_clr_pclk;
   assign reg_ddrc_wr_poison_intr_clr_pclk = r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_WR_POISON_INTR_CLR+:`REGB_DDRC_CH0_SIZE_POISONCFG_WR_POISON_INTR_CLR];
 reg reg_ddrc_wr_poison_intr_clr_pclk_s0;
 reg reg_ddrc_wr_poison_intr_clr_ack;
 // reset reg_ddrc_wr_poison_intr_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_wr_poison_intr_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_wr_poison_intr_clr_pclk_s0 <= 1'b0;
 reg_ddrc_wr_poison_intr_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_wr_poison_intr_clr_pclk_s0 <= reg_ddrc_wr_poison_intr_clr_pclk;
 reg_ddrc_wr_poison_intr_clr_ack <= reg_ddrc_wr_poison_intr_clr;
 end
 end
 assign reg_ddrc_wr_poison_intr_clr = reg_ddrc_wr_poison_intr_clr_pclk & (!reg_ddrc_wr_poison_intr_clr_pclk_s0);
 assign reg_ddrc_wr_poison_intr_clr_ack_pclk = reg_ddrc_wr_poison_intr_clr_ack;
   assign reg_ddrc_rd_poison_slverr_en = r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_SLVERR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_SLVERR_EN];
   assign reg_ddrc_rd_poison_intr_en = r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_EN+:`REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_EN];
   wire reg_ddrc_rd_poison_intr_clr_pclk;
   assign reg_ddrc_rd_poison_intr_clr_pclk = r77_poisoncfg[`REGB_DDRC_CH0_OFFSET_POISONCFG_RD_POISON_INTR_CLR+:`REGB_DDRC_CH0_SIZE_POISONCFG_RD_POISON_INTR_CLR];
 reg reg_ddrc_rd_poison_intr_clr_pclk_s0;
 reg reg_ddrc_rd_poison_intr_clr_ack;
 // reset reg_ddrc_rd_poison_intr_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_poison_intr_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_poison_intr_clr_pclk_s0 <= 1'b0;
 reg_ddrc_rd_poison_intr_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_poison_intr_clr_pclk_s0 <= reg_ddrc_rd_poison_intr_clr_pclk;
 reg_ddrc_rd_poison_intr_clr_ack <= reg_ddrc_rd_poison_intr_clr;
 end
 end
 assign reg_ddrc_rd_poison_intr_clr = reg_ddrc_rd_poison_intr_clr_pclk & (!reg_ddrc_rd_poison_intr_clr_pclk_s0);
 assign reg_ddrc_rd_poison_intr_clr_ack_pclk = reg_ddrc_rd_poison_intr_clr_ack;
   //------------------------
   // Register REGB_DDRC_CH0.POISONSTAT
   //------------------------
   always_comb begin : r78_poisonstat_combo_PROC
      r78_poisonstat = {REG_WIDTH{1'b0}};
      r78_poisonstat[`REGB_DDRC_CH0_OFFSET_POISONSTAT_WR_POISON_INTR_0+:`REGB_DDRC_CH0_SIZE_POISONSTAT_WR_POISON_INTR_0] = ddrc_reg_wr_poison_intr_0;
      r78_poisonstat[`REGB_DDRC_CH0_OFFSET_POISONSTAT_RD_POISON_INTR_0+:`REGB_DDRC_CH0_SIZE_POISONSTAT_RD_POISON_INTR_0] = ddrc_reg_rd_poison_intr_0;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG0
   //------------------------
   assign reg_ddrc_ecc_mode[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE) -1:0] = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_MODE+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_MODE];
   assign reg_ddrc_ecc_ap_en = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_EN];
   assign reg_ddrc_ecc_region_remap_en = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_REMAP_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_REMAP_EN];
   assign reg_ddrc_ecc_region_map[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP) -1:0] = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP];
   assign reg_ddrc_blk_channel_idle_time_x32[(`REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32) -1:0] = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32+:`REGB_DDRC_CH0_SIZE_ECCCFG0_BLK_CHANNEL_IDLE_TIME_X32];
   assign reg_ddrc_ecc_ap_err_threshold[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD) -1:0] = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_AP_ERR_THRESHOLD+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_AP_ERR_THRESHOLD];
   assign reg_ddrc_ecc_region_map_other = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_OTHER+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_OTHER];
   assign reg_ddrc_ecc_region_map_granu[(`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU) -1:0] = r79_ecccfg0[`REGB_DDRC_CH0_OFFSET_ECCCFG0_ECC_REGION_MAP_GRANU+:`REGB_DDRC_CH0_SIZE_ECCCFG0_ECC_REGION_MAP_GRANU];
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG1
   //------------------------
   assign reg_ddrc_data_poison_en = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_EN];
   assign reg_ddrc_data_poison_bit = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_DATA_POISON_BIT+:`REGB_DDRC_CH0_SIZE_ECCCFG1_DATA_POISON_BIT];
   assign reg_ddrc_ecc_region_parity_lock = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_PARITY_LOCK+:`REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_PARITY_LOCK];
   assign reg_ddrc_ecc_region_waste_lock = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ECC_REGION_WASTE_LOCK+:`REGB_DDRC_CH0_SIZE_ECCCFG1_ECC_REGION_WASTE_LOCK];
   assign reg_ddrc_med_ecc_en = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_MED_ECC_EN+:`REGB_DDRC_CH0_SIZE_ECCCFG1_MED_ECC_EN];
   assign reg_ddrc_blk_channel_active_term = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM+:`REGB_DDRC_CH0_SIZE_ECCCFG1_BLK_CHANNEL_ACTIVE_TERM];
   assign reg_ddrc_active_blk_channel[(`REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL) -1:0] = r80_ecccfg1[`REGB_DDRC_CH0_OFFSET_ECCCFG1_ACTIVE_BLK_CHANNEL+:`REGB_DDRC_CH0_SIZE_ECCCFG1_ACTIVE_BLK_CHANNEL];
   //------------------------
   // Register REGB_DDRC_CH0.ECCSTAT
   //------------------------
   always_comb begin : r81_eccstat_combo_PROC
      r81_eccstat = {REG_WIDTH{1'b0}};
      r81_eccstat[`REGB_DDRC_CH0_OFFSET_ECCSTAT_ECC_CORRECTED_BIT_NUM+:`REGB_DDRC_CH0_SIZE_ECCSTAT_ECC_CORRECTED_BIT_NUM] = ddrc_reg_ecc_corrected_bit_num[(`REGB_DDRC_CH0_SIZE_ECCSTAT_ECC_CORRECTED_BIT_NUM) -1:0];
      r81_eccstat[`REGB_DDRC_CH0_OFFSET_ECCSTAT_ECC_CORRECTED_ERR+:`REGB_DDRC_CH0_SIZE_ECCSTAT_ECC_CORRECTED_ERR] = ddrc_reg_ecc_corrected_err[(`REGB_DDRC_CH0_SIZE_ECCSTAT_ECC_CORRECTED_ERR) -1:0];
      r81_eccstat[`REGB_DDRC_CH0_OFFSET_ECCSTAT_ECC_UNCORRECTED_ERR+:`REGB_DDRC_CH0_SIZE_ECCSTAT_ECC_UNCORRECTED_ERR] = ddrc_reg_ecc_uncorrected_err[(`REGB_DDRC_CH0_SIZE_ECCSTAT_ECC_UNCORRECTED_ERR) -1:0];
      r81_eccstat[`REGB_DDRC_CH0_OFFSET_ECCSTAT_SBR_READ_ECC_CE+:`REGB_DDRC_CH0_SIZE_ECCSTAT_SBR_READ_ECC_CE] = ddrc_reg_sbr_read_ecc_ce;
      r81_eccstat[`REGB_DDRC_CH0_OFFSET_ECCSTAT_SBR_READ_ECC_UE+:`REGB_DDRC_CH0_SIZE_ECCSTAT_SBR_READ_ECC_UE] = ddrc_reg_sbr_read_ecc_ue;
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCTL
   //------------------------
   wire reg_ddrc_ecc_corrected_err_clr_pclk;
   assign reg_ddrc_ecc_corrected_err_clr_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_CLR];
 reg reg_ddrc_ecc_corrected_err_clr_pclk_s0;
 reg reg_ddrc_ecc_corrected_err_clr_ack;
 // reset reg_ddrc_ecc_corrected_err_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_corrected_err_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_corrected_err_clr_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_corrected_err_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_corrected_err_clr_pclk_s0 <= reg_ddrc_ecc_corrected_err_clr_pclk;
 reg_ddrc_ecc_corrected_err_clr_ack <= reg_ddrc_ecc_corrected_err_clr;
 end
 end
 assign reg_ddrc_ecc_corrected_err_clr = reg_ddrc_ecc_corrected_err_clr_pclk & (!reg_ddrc_ecc_corrected_err_clr_pclk_s0);
 assign reg_ddrc_ecc_corrected_err_clr_ack_pclk = reg_ddrc_ecc_corrected_err_clr_ack;
   wire reg_ddrc_ecc_uncorrected_err_clr_pclk;
   assign reg_ddrc_ecc_uncorrected_err_clr_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_CLR];
 reg reg_ddrc_ecc_uncorrected_err_clr_pclk_s0;
 reg reg_ddrc_ecc_uncorrected_err_clr_ack;
 // reset reg_ddrc_ecc_uncorrected_err_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_uncorrected_err_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_uncorrected_err_clr_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_uncorrected_err_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_uncorrected_err_clr_pclk_s0 <= reg_ddrc_ecc_uncorrected_err_clr_pclk;
 reg_ddrc_ecc_uncorrected_err_clr_ack <= reg_ddrc_ecc_uncorrected_err_clr;
 end
 end
 assign reg_ddrc_ecc_uncorrected_err_clr = reg_ddrc_ecc_uncorrected_err_clr_pclk & (!reg_ddrc_ecc_uncorrected_err_clr_pclk_s0);
 assign reg_ddrc_ecc_uncorrected_err_clr_ack_pclk = reg_ddrc_ecc_uncorrected_err_clr_ack;
   wire reg_ddrc_ecc_corr_err_cnt_clr_pclk;
   assign reg_ddrc_ecc_corr_err_cnt_clr_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORR_ERR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORR_ERR_CNT_CLR];
 reg reg_ddrc_ecc_corr_err_cnt_clr_pclk_s0;
 reg reg_ddrc_ecc_corr_err_cnt_clr_ack;
 // reset reg_ddrc_ecc_corr_err_cnt_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_corr_err_cnt_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_corr_err_cnt_clr_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_corr_err_cnt_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_corr_err_cnt_clr_pclk_s0 <= reg_ddrc_ecc_corr_err_cnt_clr_pclk;
 reg_ddrc_ecc_corr_err_cnt_clr_ack <= reg_ddrc_ecc_corr_err_cnt_clr;
 end
 end
 assign reg_ddrc_ecc_corr_err_cnt_clr = reg_ddrc_ecc_corr_err_cnt_clr_pclk & (!reg_ddrc_ecc_corr_err_cnt_clr_pclk_s0);
 assign reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk = reg_ddrc_ecc_corr_err_cnt_clr_ack;
   wire reg_ddrc_ecc_uncorr_err_cnt_clr_pclk;
   assign reg_ddrc_ecc_uncorr_err_cnt_clr_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORR_ERR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORR_ERR_CNT_CLR];
 reg reg_ddrc_ecc_uncorr_err_cnt_clr_pclk_s0;
 reg reg_ddrc_ecc_uncorr_err_cnt_clr_ack;
 // reset reg_ddrc_ecc_uncorr_err_cnt_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_uncorr_err_cnt_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_uncorr_err_cnt_clr_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_uncorr_err_cnt_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_uncorr_err_cnt_clr_pclk_s0 <= reg_ddrc_ecc_uncorr_err_cnt_clr_pclk;
 reg_ddrc_ecc_uncorr_err_cnt_clr_ack <= reg_ddrc_ecc_uncorr_err_cnt_clr;
 end
 end
 assign reg_ddrc_ecc_uncorr_err_cnt_clr = reg_ddrc_ecc_uncorr_err_cnt_clr_pclk & (!reg_ddrc_ecc_uncorr_err_cnt_clr_pclk_s0);
 assign reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk = reg_ddrc_ecc_uncorr_err_cnt_clr_ack;
   wire reg_ddrc_ecc_ap_err_intr_clr_pclk;
   assign reg_ddrc_ecc_ap_err_intr_clr_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_CLR+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_CLR];
 reg reg_ddrc_ecc_ap_err_intr_clr_pclk_s0;
 reg reg_ddrc_ecc_ap_err_intr_clr_ack;
 // reset reg_ddrc_ecc_ap_err_intr_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_ap_err_intr_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_ap_err_intr_clr_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_ap_err_intr_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_ap_err_intr_clr_pclk_s0 <= reg_ddrc_ecc_ap_err_intr_clr_pclk;
 reg_ddrc_ecc_ap_err_intr_clr_ack <= reg_ddrc_ecc_ap_err_intr_clr;
 end
 end
 assign reg_ddrc_ecc_ap_err_intr_clr = reg_ddrc_ecc_ap_err_intr_clr_pclk & (!reg_ddrc_ecc_ap_err_intr_clr_pclk_s0);
 assign reg_ddrc_ecc_ap_err_intr_clr_ack_pclk = reg_ddrc_ecc_ap_err_intr_clr_ack;
   assign reg_ddrc_ecc_corrected_err_intr_en = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_EN+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_EN];
   assign reg_ddrc_ecc_uncorrected_err_intr_en = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_EN];
   assign reg_ddrc_ecc_ap_err_intr_en = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_EN+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_EN];
   wire reg_ddrc_ecc_corrected_err_intr_force_pclk;
   assign reg_ddrc_ecc_corrected_err_intr_force_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_CORRECTED_ERR_INTR_FORCE];
 reg reg_ddrc_ecc_corrected_err_intr_force_pclk_s0;
 reg reg_ddrc_ecc_corrected_err_intr_force_ack;
 // reset reg_ddrc_ecc_corrected_err_intr_force field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_corrected_err_intr_force_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_corrected_err_intr_force_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_corrected_err_intr_force_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_corrected_err_intr_force_pclk_s0 <= reg_ddrc_ecc_corrected_err_intr_force_pclk;
 reg_ddrc_ecc_corrected_err_intr_force_ack <= reg_ddrc_ecc_corrected_err_intr_force;
 end
 end
 assign reg_ddrc_ecc_corrected_err_intr_force = reg_ddrc_ecc_corrected_err_intr_force_pclk & (!reg_ddrc_ecc_corrected_err_intr_force_pclk_s0);
 assign reg_ddrc_ecc_corrected_err_intr_force_ack_pclk = reg_ddrc_ecc_corrected_err_intr_force_ack;
   wire reg_ddrc_ecc_uncorrected_err_intr_force_pclk;
   assign reg_ddrc_ecc_uncorrected_err_intr_force_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_UNCORRECTED_ERR_INTR_FORCE];
 reg reg_ddrc_ecc_uncorrected_err_intr_force_pclk_s0;
 reg reg_ddrc_ecc_uncorrected_err_intr_force_ack;
 // reset reg_ddrc_ecc_uncorrected_err_intr_force field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_uncorrected_err_intr_force_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_uncorrected_err_intr_force_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_uncorrected_err_intr_force_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_uncorrected_err_intr_force_pclk_s0 <= reg_ddrc_ecc_uncorrected_err_intr_force_pclk;
 reg_ddrc_ecc_uncorrected_err_intr_force_ack <= reg_ddrc_ecc_uncorrected_err_intr_force;
 end
 end
 assign reg_ddrc_ecc_uncorrected_err_intr_force = reg_ddrc_ecc_uncorrected_err_intr_force_pclk & (!reg_ddrc_ecc_uncorrected_err_intr_force_pclk_s0);
 assign reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk = reg_ddrc_ecc_uncorrected_err_intr_force_ack;
   wire reg_ddrc_ecc_ap_err_intr_force_pclk;
   assign reg_ddrc_ecc_ap_err_intr_force_pclk = r82_eccctl[`REGB_DDRC_CH0_OFFSET_ECCCTL_ECC_AP_ERR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_ECCCTL_ECC_AP_ERR_INTR_FORCE];
 reg reg_ddrc_ecc_ap_err_intr_force_pclk_s0;
 reg reg_ddrc_ecc_ap_err_intr_force_ack;
 // reset reg_ddrc_ecc_ap_err_intr_force field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ecc_ap_err_intr_force_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ecc_ap_err_intr_force_pclk_s0 <= 1'b0;
 reg_ddrc_ecc_ap_err_intr_force_ack <= 1'b0;
 end else begin
 reg_ddrc_ecc_ap_err_intr_force_pclk_s0 <= reg_ddrc_ecc_ap_err_intr_force_pclk;
 reg_ddrc_ecc_ap_err_intr_force_ack <= reg_ddrc_ecc_ap_err_intr_force;
 end
 end
 assign reg_ddrc_ecc_ap_err_intr_force = reg_ddrc_ecc_ap_err_intr_force_pclk & (!reg_ddrc_ecc_ap_err_intr_force_pclk_s0);
 assign reg_ddrc_ecc_ap_err_intr_force_ack_pclk = reg_ddrc_ecc_ap_err_intr_force_ack;
   //------------------------
   // Register REGB_DDRC_CH0.ECCERRCNT
   //------------------------
   always_comb begin : r83_eccerrcnt_combo_PROC
      r83_eccerrcnt = {REG_WIDTH{1'b0}};
      r83_eccerrcnt[`REGB_DDRC_CH0_OFFSET_ECCERRCNT_ECC_CORR_ERR_CNT+:`REGB_DDRC_CH0_SIZE_ECCERRCNT_ECC_CORR_ERR_CNT] = ddrc_reg_ecc_corr_err_cnt[(`REGB_DDRC_CH0_SIZE_ECCERRCNT_ECC_CORR_ERR_CNT) -1:0];
      r83_eccerrcnt[`REGB_DDRC_CH0_OFFSET_ECCERRCNT_ECC_UNCORR_ERR_CNT+:`REGB_DDRC_CH0_SIZE_ECCERRCNT_ECC_UNCORR_ERR_CNT] = ddrc_reg_ecc_uncorr_err_cnt[(`REGB_DDRC_CH0_SIZE_ECCERRCNT_ECC_UNCORR_ERR_CNT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCADDR0
   //------------------------
   always_comb begin : r84_ecccaddr0_combo_PROC
      r84_ecccaddr0 = {REG_WIDTH{1'b0}};
      r84_ecccaddr0[`REGB_DDRC_CH0_OFFSET_ECCCADDR0_ECC_CORR_ROW+:`REGB_DDRC_CH0_SIZE_ECCCADDR0_ECC_CORR_ROW] = ddrc_reg_ecc_corr_row[(`REGB_DDRC_CH0_SIZE_ECCCADDR0_ECC_CORR_ROW) -1:0];
      r84_ecccaddr0[`REGB_DDRC_CH0_OFFSET_ECCCADDR0_ECC_CORR_RANK+:`REGB_DDRC_CH0_SIZE_ECCCADDR0_ECC_CORR_RANK] = ddrc_reg_ecc_corr_rank[(`REGB_DDRC_CH0_SIZE_ECCCADDR0_ECC_CORR_RANK) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCADDR1
   //------------------------
   always_comb begin : r85_ecccaddr1_combo_PROC
      r85_ecccaddr1 = {REG_WIDTH{1'b0}};
      r85_ecccaddr1[`REGB_DDRC_CH0_OFFSET_ECCCADDR1_ECC_CORR_COL+:`REGB_DDRC_CH0_SIZE_ECCCADDR1_ECC_CORR_COL] = ddrc_reg_ecc_corr_col[(`REGB_DDRC_CH0_SIZE_ECCCADDR1_ECC_CORR_COL) -1:0];
      r85_ecccaddr1[`REGB_DDRC_CH0_OFFSET_ECCCADDR1_ECC_CORR_BANK+:`REGB_DDRC_CH0_SIZE_ECCCADDR1_ECC_CORR_BANK] = ddrc_reg_ecc_corr_bank[(`REGB_DDRC_CH0_SIZE_ECCCADDR1_ECC_CORR_BANK) -1:0];
      r85_ecccaddr1[`REGB_DDRC_CH0_OFFSET_ECCCADDR1_ECC_CORR_BG+:`REGB_DDRC_CH0_SIZE_ECCCADDR1_ECC_CORR_BG] = ddrc_reg_ecc_corr_bg[(`REGB_DDRC_CH0_SIZE_ECCCADDR1_ECC_CORR_BG) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN0
   //------------------------
   always_comb begin : r86_ecccsyn0_combo_PROC
      r86_ecccsyn0 = {REG_WIDTH{1'b0}};
      r86_ecccsyn0[`REGB_DDRC_CH0_OFFSET_ECCCSYN0_ECC_CORR_SYNDROMES_31_0+:`REGB_DDRC_CH0_SIZE_ECCCSYN0_ECC_CORR_SYNDROMES_31_0] = ddrc_reg_ecc_corr_syndromes_31_0[(`REGB_DDRC_CH0_SIZE_ECCCSYN0_ECC_CORR_SYNDROMES_31_0) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN1
   //------------------------
   always_comb begin : r87_ecccsyn1_combo_PROC
      r87_ecccsyn1 = {REG_WIDTH{1'b0}};
      r87_ecccsyn1[`REGB_DDRC_CH0_OFFSET_ECCCSYN1_ECC_CORR_SYNDROMES_63_32+:`REGB_DDRC_CH0_SIZE_ECCCSYN1_ECC_CORR_SYNDROMES_63_32] = ddrc_reg_ecc_corr_syndromes_63_32[(`REGB_DDRC_CH0_SIZE_ECCCSYN1_ECC_CORR_SYNDROMES_63_32) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN2
   //------------------------
   always_comb begin : r88_ecccsyn2_combo_PROC
      r88_ecccsyn2 = {REG_WIDTH{1'b0}};
      r88_ecccsyn2[`REGB_DDRC_CH0_OFFSET_ECCCSYN2_ECC_CORR_SYNDROMES_71_64+:`REGB_DDRC_CH0_SIZE_ECCCSYN2_ECC_CORR_SYNDROMES_71_64] = ddrc_reg_ecc_corr_syndromes_71_64[(`REGB_DDRC_CH0_SIZE_ECCCSYN2_ECC_CORR_SYNDROMES_71_64) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK0
   //------------------------
   always_comb begin : r89_eccbitmask0_combo_PROC
      r89_eccbitmask0 = {REG_WIDTH{1'b0}};
      r89_eccbitmask0[`REGB_DDRC_CH0_OFFSET_ECCBITMASK0_ECC_CORR_BIT_MASK_31_0+:`REGB_DDRC_CH0_SIZE_ECCBITMASK0_ECC_CORR_BIT_MASK_31_0] = ddrc_reg_ecc_corr_bit_mask_31_0[(`REGB_DDRC_CH0_SIZE_ECCBITMASK0_ECC_CORR_BIT_MASK_31_0) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK1
   //------------------------
   always_comb begin : r90_eccbitmask1_combo_PROC
      r90_eccbitmask1 = {REG_WIDTH{1'b0}};
      r90_eccbitmask1[`REGB_DDRC_CH0_OFFSET_ECCBITMASK1_ECC_CORR_BIT_MASK_63_32+:`REGB_DDRC_CH0_SIZE_ECCBITMASK1_ECC_CORR_BIT_MASK_63_32] = ddrc_reg_ecc_corr_bit_mask_63_32[(`REGB_DDRC_CH0_SIZE_ECCBITMASK1_ECC_CORR_BIT_MASK_63_32) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK2
   //------------------------
   always_comb begin : r91_eccbitmask2_combo_PROC
      r91_eccbitmask2 = {REG_WIDTH{1'b0}};
      r91_eccbitmask2[`REGB_DDRC_CH0_OFFSET_ECCBITMASK2_ECC_CORR_BIT_MASK_71_64+:`REGB_DDRC_CH0_SIZE_ECCBITMASK2_ECC_CORR_BIT_MASK_71_64] = ddrc_reg_ecc_corr_bit_mask_71_64[(`REGB_DDRC_CH0_SIZE_ECCBITMASK2_ECC_CORR_BIT_MASK_71_64) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCUADDR0
   //------------------------
   always_comb begin : r92_eccuaddr0_combo_PROC
      r92_eccuaddr0 = {REG_WIDTH{1'b0}};
      r92_eccuaddr0[`REGB_DDRC_CH0_OFFSET_ECCUADDR0_ECC_UNCORR_ROW+:`REGB_DDRC_CH0_SIZE_ECCUADDR0_ECC_UNCORR_ROW] = ddrc_reg_ecc_uncorr_row[(`REGB_DDRC_CH0_SIZE_ECCUADDR0_ECC_UNCORR_ROW) -1:0];
      r92_eccuaddr0[`REGB_DDRC_CH0_OFFSET_ECCUADDR0_ECC_UNCORR_RANK+:`REGB_DDRC_CH0_SIZE_ECCUADDR0_ECC_UNCORR_RANK] = ddrc_reg_ecc_uncorr_rank[(`REGB_DDRC_CH0_SIZE_ECCUADDR0_ECC_UNCORR_RANK) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCUADDR1
   //------------------------
   always_comb begin : r93_eccuaddr1_combo_PROC
      r93_eccuaddr1 = {REG_WIDTH{1'b0}};
      r93_eccuaddr1[`REGB_DDRC_CH0_OFFSET_ECCUADDR1_ECC_UNCORR_COL+:`REGB_DDRC_CH0_SIZE_ECCUADDR1_ECC_UNCORR_COL] = ddrc_reg_ecc_uncorr_col[(`REGB_DDRC_CH0_SIZE_ECCUADDR1_ECC_UNCORR_COL) -1:0];
      r93_eccuaddr1[`REGB_DDRC_CH0_OFFSET_ECCUADDR1_ECC_UNCORR_BANK+:`REGB_DDRC_CH0_SIZE_ECCUADDR1_ECC_UNCORR_BANK] = ddrc_reg_ecc_uncorr_bank[(`REGB_DDRC_CH0_SIZE_ECCUADDR1_ECC_UNCORR_BANK) -1:0];
      r93_eccuaddr1[`REGB_DDRC_CH0_OFFSET_ECCUADDR1_ECC_UNCORR_BG+:`REGB_DDRC_CH0_SIZE_ECCUADDR1_ECC_UNCORR_BG] = ddrc_reg_ecc_uncorr_bg[(`REGB_DDRC_CH0_SIZE_ECCUADDR1_ECC_UNCORR_BG) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN0
   //------------------------
   always_comb begin : r94_eccusyn0_combo_PROC
      r94_eccusyn0 = {REG_WIDTH{1'b0}};
      r94_eccusyn0[`REGB_DDRC_CH0_OFFSET_ECCUSYN0_ECC_UNCORR_SYNDROMES_31_0+:`REGB_DDRC_CH0_SIZE_ECCUSYN0_ECC_UNCORR_SYNDROMES_31_0] = ddrc_reg_ecc_uncorr_syndromes_31_0[(`REGB_DDRC_CH0_SIZE_ECCUSYN0_ECC_UNCORR_SYNDROMES_31_0) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN1
   //------------------------
   always_comb begin : r95_eccusyn1_combo_PROC
      r95_eccusyn1 = {REG_WIDTH{1'b0}};
      r95_eccusyn1[`REGB_DDRC_CH0_OFFSET_ECCUSYN1_ECC_UNCORR_SYNDROMES_63_32+:`REGB_DDRC_CH0_SIZE_ECCUSYN1_ECC_UNCORR_SYNDROMES_63_32] = ddrc_reg_ecc_uncorr_syndromes_63_32[(`REGB_DDRC_CH0_SIZE_ECCUSYN1_ECC_UNCORR_SYNDROMES_63_32) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN2
   //------------------------
   always_comb begin : r96_eccusyn2_combo_PROC
      r96_eccusyn2 = {REG_WIDTH{1'b0}};
      r96_eccusyn2[`REGB_DDRC_CH0_OFFSET_ECCUSYN2_ECC_UNCORR_SYNDROMES_71_64+:`REGB_DDRC_CH0_SIZE_ECCUSYN2_ECC_UNCORR_SYNDROMES_71_64] = ddrc_reg_ecc_uncorr_syndromes_71_64[(`REGB_DDRC_CH0_SIZE_ECCUSYN2_ECC_UNCORR_SYNDROMES_71_64) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR0
   //------------------------
   assign reg_ddrc_ecc_poison_col[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL) -1:0] = r97_eccpoisonaddr0[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_COL+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_COL];
   assign reg_ddrc_ecc_poison_rank[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK) -1:0] = r97_eccpoisonaddr0[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR0_ECC_POISON_RANK+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR0_ECC_POISON_RANK];
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR1
   //------------------------
   assign reg_ddrc_ecc_poison_row[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW) -1:0] = r98_eccpoisonaddr1[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_ROW+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_ROW];
   assign reg_ddrc_ecc_poison_bank[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK) -1:0] = r98_eccpoisonaddr1[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BANK+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BANK];
   assign reg_ddrc_ecc_poison_bg[(`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG) -1:0] = r98_eccpoisonaddr1[`REGB_DDRC_CH0_OFFSET_ECCPOISONADDR1_ECC_POISON_BG+:`REGB_DDRC_CH0_SIZE_ECCPOISONADDR1_ECC_POISON_BG];
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT0
   //------------------------
   assign reg_ddrc_ecc_poison_data_31_0[(`REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0) -1:0] = r101_eccpoisonpat0[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT0_ECC_POISON_DATA_31_0+:`REGB_DDRC_CH0_SIZE_ECCPOISONPAT0_ECC_POISON_DATA_31_0];
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT2
   //------------------------
   assign reg_ddrc_ecc_poison_data_71_64[(`REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64) -1:0] = r103_eccpoisonpat2[`REGB_DDRC_CH0_OFFSET_ECCPOISONPAT2_ECC_POISON_DATA_71_64+:`REGB_DDRC_CH0_SIZE_ECCPOISONPAT2_ECC_POISON_DATA_71_64];
   //------------------------
   // Register REGB_DDRC_CH0.ECCAPSTAT
   //------------------------
   always_comb begin : r104_eccapstat_combo_PROC
      r104_eccapstat = {REG_WIDTH{1'b0}};
      r104_eccapstat[`REGB_DDRC_CH0_OFFSET_ECCAPSTAT_ECC_AP_ERR+:`REGB_DDRC_CH0_SIZE_ECCAPSTAT_ECC_AP_ERR] = ddrc_reg_ecc_ap_err;
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCTL1
   //------------------------
   assign reg_ddrc_rd_link_ecc_corr_intr_en = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_EN];
   wire reg_ddrc_rd_link_ecc_corr_intr_clr_pclk;
   assign reg_ddrc_rd_link_ecc_corr_intr_clr_pclk = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_CLR];
 reg reg_ddrc_rd_link_ecc_corr_intr_clr_pclk_s0;
 reg reg_ddrc_rd_link_ecc_corr_intr_clr_ack;
 // reset reg_ddrc_rd_link_ecc_corr_intr_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_link_ecc_corr_intr_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_link_ecc_corr_intr_clr_pclk_s0 <= 1'b0;
 reg_ddrc_rd_link_ecc_corr_intr_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_link_ecc_corr_intr_clr_pclk_s0 <= reg_ddrc_rd_link_ecc_corr_intr_clr_pclk;
 reg_ddrc_rd_link_ecc_corr_intr_clr_ack <= reg_ddrc_rd_link_ecc_corr_intr_clr;
 end
 end
 assign reg_ddrc_rd_link_ecc_corr_intr_clr = reg_ddrc_rd_link_ecc_corr_intr_clr_pclk & (!reg_ddrc_rd_link_ecc_corr_intr_clr_pclk_s0);
 assign reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk = reg_ddrc_rd_link_ecc_corr_intr_clr_ack;
   wire reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk;
   assign reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_CNT_CLR];
 reg reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk_s0;
 reg reg_ddrc_rd_link_ecc_corr_cnt_clr_ack;
 // reset reg_ddrc_rd_link_ecc_corr_cnt_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk_s0 <= 1'b0;
 reg_ddrc_rd_link_ecc_corr_cnt_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk_s0 <= reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk;
 reg_ddrc_rd_link_ecc_corr_cnt_clr_ack <= reg_ddrc_rd_link_ecc_corr_cnt_clr;
 end
 end
 assign reg_ddrc_rd_link_ecc_corr_cnt_clr = reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk & (!reg_ddrc_rd_link_ecc_corr_cnt_clr_pclk_s0);
 assign reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk = reg_ddrc_rd_link_ecc_corr_cnt_clr_ack;
   wire reg_ddrc_rd_link_ecc_corr_intr_force_pclk;
   assign reg_ddrc_rd_link_ecc_corr_intr_force_pclk = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_CORR_INTR_FORCE];
 reg reg_ddrc_rd_link_ecc_corr_intr_force_pclk_s0;
 reg reg_ddrc_rd_link_ecc_corr_intr_force_ack;
 // reset reg_ddrc_rd_link_ecc_corr_intr_force field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_link_ecc_corr_intr_force_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_link_ecc_corr_intr_force_pclk_s0 <= 1'b0;
 reg_ddrc_rd_link_ecc_corr_intr_force_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_link_ecc_corr_intr_force_pclk_s0 <= reg_ddrc_rd_link_ecc_corr_intr_force_pclk;
 reg_ddrc_rd_link_ecc_corr_intr_force_ack <= reg_ddrc_rd_link_ecc_corr_intr_force;
 end
 end
 assign reg_ddrc_rd_link_ecc_corr_intr_force = reg_ddrc_rd_link_ecc_corr_intr_force_pclk & (!reg_ddrc_rd_link_ecc_corr_intr_force_pclk_s0);
 assign reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk = reg_ddrc_rd_link_ecc_corr_intr_force_ack;
   assign reg_ddrc_rd_link_ecc_uncorr_intr_en = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_EN];
   wire reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk;
   assign reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_CLR];
 reg reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk_s0;
 reg reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack;
 // reset reg_ddrc_rd_link_ecc_uncorr_intr_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk_s0 <= 1'b0;
 reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk_s0 <= reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk;
 reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack <= reg_ddrc_rd_link_ecc_uncorr_intr_clr;
 end
 end
 assign reg_ddrc_rd_link_ecc_uncorr_intr_clr = reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk & (!reg_ddrc_rd_link_ecc_uncorr_intr_clr_pclk_s0);
 assign reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk = reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack;
   wire reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk;
   assign reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_CNT_CLR];
 reg reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk_s0;
 reg reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack;
 // reset reg_ddrc_rd_link_ecc_uncorr_cnt_clr field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk_s0 <= 1'b0;
 reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk_s0 <= reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk;
 reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack <= reg_ddrc_rd_link_ecc_uncorr_cnt_clr;
 end
 end
 assign reg_ddrc_rd_link_ecc_uncorr_cnt_clr = reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk & (!reg_ddrc_rd_link_ecc_uncorr_cnt_clr_pclk_s0);
 assign reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk = reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack;
   wire reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk;
   assign reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk = r161_lnkeccctl1[`REGB_DDRC_CH0_OFFSET_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE+:`REGB_DDRC_CH0_SIZE_LNKECCCTL1_RD_LINK_ECC_UNCORR_INTR_FORCE];
 reg reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk_s0;
 reg reg_ddrc_rd_link_ecc_uncorr_intr_force_ack;
 // reset reg_ddrc_rd_link_ecc_uncorr_intr_force field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk_s0 <= 1'b0;
 reg_ddrc_rd_link_ecc_uncorr_intr_force_ack <= 1'b0;
 end else begin
 reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk_s0 <= reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk;
 reg_ddrc_rd_link_ecc_uncorr_intr_force_ack <= reg_ddrc_rd_link_ecc_uncorr_intr_force;
 end
 end
 assign reg_ddrc_rd_link_ecc_uncorr_intr_force = reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk & (!reg_ddrc_rd_link_ecc_uncorr_intr_force_pclk_s0);
 assign reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk = reg_ddrc_rd_link_ecc_uncorr_intr_force_ack;
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONCTL0
   //------------------------
   assign reg_ddrc_linkecc_poison_inject_en = r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_INJECT_EN];
   assign reg_ddrc_linkecc_poison_type = r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_TYPE+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_TYPE];
   assign reg_ddrc_linkecc_poison_rw = r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_RW+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_RW];
   assign reg_ddrc_linkecc_poison_dmi_sel[(`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL) -1:0] = r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_DMI_SEL];
   assign reg_ddrc_linkecc_poison_byte_sel[(`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL) -1:0] = r162_lnkeccpoisonctl0[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONCTL0_LINKECC_POISON_BYTE_SEL];
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONSTAT
   //------------------------
   always_comb begin : r163_lnkeccpoisonstat_combo_PROC
      r163_lnkeccpoisonstat = {REG_WIDTH{1'b0}};
      r163_lnkeccpoisonstat[`REGB_DDRC_CH0_OFFSET_LNKECCPOISONSTAT_LINKECC_POISON_COMPLETE+:`REGB_DDRC_CH0_SIZE_LNKECCPOISONSTAT_LINKECC_POISON_COMPLETE] = ddrc_reg_linkecc_poison_complete;
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCINDEX
   //------------------------
   assign reg_ddrc_rd_link_ecc_err_byte_sel[(`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL) -1:0] = r164_lnkeccindex[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_BYTE_SEL];
   assign reg_ddrc_rd_link_ecc_err_rank_sel[(`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL) -1:0] = r164_lnkeccindex[`REGB_DDRC_CH0_OFFSET_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL+:`REGB_DDRC_CH0_SIZE_LNKECCINDEX_RD_LINK_ECC_ERR_RANK_SEL];
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCERRCNT0
   //------------------------
   always_comb begin : r165_lnkeccerrcnt0_combo_PROC
      r165_lnkeccerrcnt0 = {REG_WIDTH{1'b0}};
      r165_lnkeccerrcnt0[`REGB_DDRC_CH0_OFFSET_LNKECCERRCNT0_RD_LINK_ECC_ERR_SYNDROME+:`REGB_DDRC_CH0_SIZE_LNKECCERRCNT0_RD_LINK_ECC_ERR_SYNDROME] = ddrc_reg_rd_link_ecc_err_syndrome[(`REGB_DDRC_CH0_SIZE_LNKECCERRCNT0_RD_LINK_ECC_ERR_SYNDROME) -1:0];
      r165_lnkeccerrcnt0[`REGB_DDRC_CH0_OFFSET_LNKECCERRCNT0_RD_LINK_ECC_CORR_CNT+:`REGB_DDRC_CH0_SIZE_LNKECCERRCNT0_RD_LINK_ECC_CORR_CNT] = ddrc_reg_rd_link_ecc_corr_cnt[(`REGB_DDRC_CH0_SIZE_LNKECCERRCNT0_RD_LINK_ECC_CORR_CNT) -1:0];
      r165_lnkeccerrcnt0[`REGB_DDRC_CH0_OFFSET_LNKECCERRCNT0_RD_LINK_ECC_UNCORR_CNT+:`REGB_DDRC_CH0_SIZE_LNKECCERRCNT0_RD_LINK_ECC_UNCORR_CNT] = ddrc_reg_rd_link_ecc_uncorr_cnt[(`REGB_DDRC_CH0_SIZE_LNKECCERRCNT0_RD_LINK_ECC_UNCORR_CNT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCERRSTAT
   //------------------------
   always_comb begin : r166_lnkeccerrstat_combo_PROC
      r166_lnkeccerrstat = {REG_WIDTH{1'b0}};
      r166_lnkeccerrstat[`REGB_DDRC_CH0_OFFSET_LNKECCERRSTAT_RD_LINK_ECC_CORR_ERR_INT+:`REGB_DDRC_CH0_SIZE_LNKECCERRSTAT_RD_LINK_ECC_CORR_ERR_INT] = ddrc_reg_rd_link_ecc_corr_err_int[(`REGB_DDRC_CH0_SIZE_LNKECCERRSTAT_RD_LINK_ECC_CORR_ERR_INT) -1:0];
      r166_lnkeccerrstat[`REGB_DDRC_CH0_OFFSET_LNKECCERRSTAT_RD_LINK_ECC_UNCORR_ERR_INT+:`REGB_DDRC_CH0_SIZE_LNKECCERRSTAT_RD_LINK_ECC_UNCORR_ERR_INT] = ddrc_reg_rd_link_ecc_uncorr_err_int[(`REGB_DDRC_CH0_SIZE_LNKECCERRSTAT_RD_LINK_ECC_UNCORR_ERR_INT) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCADDR0
   //------------------------
   always_comb begin : r175_lnkecccaddr0_combo_PROC
      r175_lnkecccaddr0 = {REG_WIDTH{1'b0}};
      r175_lnkecccaddr0[`REGB_DDRC_CH0_OFFSET_LNKECCCADDR0_LINK_ECC_CORR_ROW+:`REGB_DDRC_CH0_SIZE_LNKECCCADDR0_LINK_ECC_CORR_ROW] = ddrc_reg_link_ecc_corr_row[(`REGB_DDRC_CH0_SIZE_LNKECCCADDR0_LINK_ECC_CORR_ROW) -1:0];
      r175_lnkecccaddr0[`REGB_DDRC_CH0_OFFSET_LNKECCCADDR0_LINK_ECC_CORR_RANK+:`REGB_DDRC_CH0_SIZE_LNKECCCADDR0_LINK_ECC_CORR_RANK] = ddrc_reg_link_ecc_corr_rank[(`REGB_DDRC_CH0_SIZE_LNKECCCADDR0_LINK_ECC_CORR_RANK) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCADDR1
   //------------------------
   always_comb begin : r176_lnkecccaddr1_combo_PROC
      r176_lnkecccaddr1 = {REG_WIDTH{1'b0}};
      r176_lnkecccaddr1[`REGB_DDRC_CH0_OFFSET_LNKECCCADDR1_LINK_ECC_CORR_COL+:`REGB_DDRC_CH0_SIZE_LNKECCCADDR1_LINK_ECC_CORR_COL] = ddrc_reg_link_ecc_corr_col[(`REGB_DDRC_CH0_SIZE_LNKECCCADDR1_LINK_ECC_CORR_COL) -1:0];
      r176_lnkecccaddr1[`REGB_DDRC_CH0_OFFSET_LNKECCCADDR1_LINK_ECC_CORR_BANK+:`REGB_DDRC_CH0_SIZE_LNKECCCADDR1_LINK_ECC_CORR_BANK] = ddrc_reg_link_ecc_corr_bank[(`REGB_DDRC_CH0_SIZE_LNKECCCADDR1_LINK_ECC_CORR_BANK) -1:0];
      r176_lnkecccaddr1[`REGB_DDRC_CH0_OFFSET_LNKECCCADDR1_LINK_ECC_CORR_BG+:`REGB_DDRC_CH0_SIZE_LNKECCCADDR1_LINK_ECC_CORR_BG] = ddrc_reg_link_ecc_corr_bg[(`REGB_DDRC_CH0_SIZE_LNKECCCADDR1_LINK_ECC_CORR_BG) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCUADDR0
   //------------------------
   always_comb begin : r177_lnkeccuaddr0_combo_PROC
      r177_lnkeccuaddr0 = {REG_WIDTH{1'b0}};
      r177_lnkeccuaddr0[`REGB_DDRC_CH0_OFFSET_LNKECCUADDR0_LINK_ECC_UNCORR_ROW+:`REGB_DDRC_CH0_SIZE_LNKECCUADDR0_LINK_ECC_UNCORR_ROW] = ddrc_reg_link_ecc_uncorr_row[(`REGB_DDRC_CH0_SIZE_LNKECCUADDR0_LINK_ECC_UNCORR_ROW) -1:0];
      r177_lnkeccuaddr0[`REGB_DDRC_CH0_OFFSET_LNKECCUADDR0_LINK_ECC_UNCORR_RANK+:`REGB_DDRC_CH0_SIZE_LNKECCUADDR0_LINK_ECC_UNCORR_RANK] = ddrc_reg_link_ecc_uncorr_rank[(`REGB_DDRC_CH0_SIZE_LNKECCUADDR0_LINK_ECC_UNCORR_RANK) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCUADDR1
   //------------------------
   always_comb begin : r178_lnkeccuaddr1_combo_PROC
      r178_lnkeccuaddr1 = {REG_WIDTH{1'b0}};
      r178_lnkeccuaddr1[`REGB_DDRC_CH0_OFFSET_LNKECCUADDR1_LINK_ECC_UNCORR_COL+:`REGB_DDRC_CH0_SIZE_LNKECCUADDR1_LINK_ECC_UNCORR_COL] = ddrc_reg_link_ecc_uncorr_col[(`REGB_DDRC_CH0_SIZE_LNKECCUADDR1_LINK_ECC_UNCORR_COL) -1:0];
      r178_lnkeccuaddr1[`REGB_DDRC_CH0_OFFSET_LNKECCUADDR1_LINK_ECC_UNCORR_BANK+:`REGB_DDRC_CH0_SIZE_LNKECCUADDR1_LINK_ECC_UNCORR_BANK] = ddrc_reg_link_ecc_uncorr_bank[(`REGB_DDRC_CH0_SIZE_LNKECCUADDR1_LINK_ECC_UNCORR_BANK) -1:0];
      r178_lnkeccuaddr1[`REGB_DDRC_CH0_OFFSET_LNKECCUADDR1_LINK_ECC_UNCORR_BG+:`REGB_DDRC_CH0_SIZE_LNKECCUADDR1_LINK_ECC_UNCORR_BG] = ddrc_reg_link_ecc_uncorr_bg[(`REGB_DDRC_CH0_SIZE_LNKECCUADDR1_LINK_ECC_UNCORR_BG) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL0
   //------------------------
   assign reg_ddrc_dis_wc = r234_opctrl0[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_WC+:`REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_WC];
   assign reg_ddrc_dis_max_rank_rd_opt = r234_opctrl0[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_RD_OPT+:`REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_RD_OPT];
   assign reg_ddrc_dis_max_rank_wr_opt = r234_opctrl0[`REGB_DDRC_CH0_OFFSET_OPCTRL0_DIS_MAX_RANK_WR_OPT+:`REGB_DDRC_CH0_SIZE_OPCTRL0_DIS_MAX_RANK_WR_OPT];
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL1
   //------------------------
   assign reg_ddrc_dis_dq = r235_opctrl1[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_DQ+:`REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_DQ];
   assign reg_ddrc_dis_hif = r235_opctrl1[`REGB_DDRC_CH0_OFFSET_OPCTRL1_DIS_HIF+:`REGB_DDRC_CH0_SIZE_OPCTRL1_DIS_HIF];
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCAM
   //------------------------
   always_comb begin : r236_opctrlcam_combo_PROC
      r236_opctrlcam = {REG_WIDTH{1'b0}};
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_DBG_HPR_Q_DEPTH+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_HPR_Q_DEPTH] = ddrc_reg_dbg_hpr_q_depth[(`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_HPR_Q_DEPTH) -1:0];
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_DBG_LPR_Q_DEPTH+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_LPR_Q_DEPTH] = ddrc_reg_dbg_lpr_q_depth[(`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_LPR_Q_DEPTH) -1:0];
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_DBG_W_Q_DEPTH+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_W_Q_DEPTH] = ddrc_reg_dbg_w_q_depth[(`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_W_Q_DEPTH) -1:0];
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_DBG_STALL+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_STALL] = ddrc_reg_dbg_stall;
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_DBG_RD_Q_EMPTY+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_RD_Q_EMPTY] = ddrc_reg_dbg_rd_q_empty;
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_DBG_WR_Q_EMPTY+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_DBG_WR_Q_EMPTY] = ddrc_reg_dbg_wr_q_empty;
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_RD_DATA_PIPELINE_EMPTY+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_RD_DATA_PIPELINE_EMPTY] = ddrc_reg_rd_data_pipeline_empty;
      r236_opctrlcam[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM_WR_DATA_PIPELINE_EMPTY+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM_WR_DATA_PIPELINE_EMPTY] = ddrc_reg_wr_data_pipeline_empty;
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCMD
   //------------------------
   wire reg_ddrc_zq_calib_short_pclk;
   assign reg_ddrc_zq_calib_short_pclk = r237_opctrlcmd[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_ZQ_CALIB_SHORT+:`REGB_DDRC_CH0_SIZE_OPCTRLCMD_ZQ_CALIB_SHORT];
 reg reg_ddrc_zq_calib_short_pclk_s0;
 reg reg_ddrc_zq_calib_short_ack;
 // reset reg_ddrc_zq_calib_short field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_zq_calib_short_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_zq_calib_short_pclk_s0 <= 1'b0;
 reg_ddrc_zq_calib_short_ack <= 1'b0;
 end else begin
 reg_ddrc_zq_calib_short_pclk_s0 <= reg_ddrc_zq_calib_short_pclk;
 reg_ddrc_zq_calib_short_ack <= reg_ddrc_zq_calib_short;
 end
 end
 assign reg_ddrc_zq_calib_short = reg_ddrc_zq_calib_short_pclk & (!reg_ddrc_zq_calib_short_pclk_s0);
 assign reg_ddrc_zq_calib_short_ack_pclk = reg_ddrc_zq_calib_short_ack;
 assign ddrc_reg_zq_calib_short_busy_int = ddrc_reg_zq_calib_short_busy;
   wire reg_ddrc_ctrlupd_pclk;
   assign reg_ddrc_ctrlupd_pclk = r237_opctrlcmd[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD+:`REGB_DDRC_CH0_SIZE_OPCTRLCMD_CTRLUPD];
 reg reg_ddrc_ctrlupd_pclk_s0;
 reg reg_ddrc_ctrlupd_ack;
 // reset reg_ddrc_ctrlupd field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ctrlupd_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ctrlupd_pclk_s0 <= 1'b0;
 reg_ddrc_ctrlupd_ack <= 1'b0;
 end else begin
 reg_ddrc_ctrlupd_pclk_s0 <= reg_ddrc_ctrlupd_pclk;
 reg_ddrc_ctrlupd_ack <= reg_ddrc_ctrlupd;
 end
 end
 assign reg_ddrc_ctrlupd = reg_ddrc_ctrlupd_pclk & (!reg_ddrc_ctrlupd_pclk_s0);
 assign reg_ddrc_ctrlupd_ack_pclk = reg_ddrc_ctrlupd_ack;
 assign ddrc_reg_ctrlupd_busy_int = ddrc_reg_ctrlupd_busy;
   assign reg_ddrc_ctrlupd_burst = r237_opctrlcmd[`REGB_DDRC_CH0_OFFSET_OPCTRLCMD_CTRLUPD_BURST+:`REGB_DDRC_CH0_SIZE_OPCTRLCMD_CTRLUPD_BURST];
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLSTAT
   //------------------------
   always_comb begin : r238_opctrlstat_combo_PROC
      r238_opctrlstat = {REG_WIDTH{1'b0}};
      r238_opctrlstat[`REGB_DDRC_CH0_OFFSET_OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY+:`REGB_DDRC_CH0_SIZE_OPCTRLSTAT_ZQ_CALIB_SHORT_BUSY] = ddrc_reg_zq_calib_short_busy | ff_regb_ddrc_ch0_zq_calib_short_saved;
      r238_opctrlstat[`REGB_DDRC_CH0_OFFSET_OPCTRLSTAT_CTRLUPD_BUSY+:`REGB_DDRC_CH0_SIZE_OPCTRLSTAT_CTRLUPD_BUSY] = ddrc_reg_ctrlupd_busy | ff_regb_ddrc_ch0_ctrlupd_saved;
      r238_opctrlstat[`REGB_DDRC_CH0_OFFSET_OPCTRLSTAT_CTRLUPD_BURST_BUSY+:`REGB_DDRC_CH0_SIZE_OPCTRLSTAT_CTRLUPD_BURST_BUSY] = ddrc_reg_ctrlupd_burst_busy;
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCAM1
   //------------------------
   always_comb begin : r239_opctrlcam1_combo_PROC
      r239_opctrlcam1 = {REG_WIDTH{1'b0}};
      r239_opctrlcam1[`REGB_DDRC_CH0_OFFSET_OPCTRLCAM1_DBG_WRECC_Q_DEPTH+:`REGB_DDRC_CH0_SIZE_OPCTRLCAM1_DBG_WRECC_Q_DEPTH] = ddrc_reg_dbg_wrecc_q_depth[(`REGB_DDRC_CH0_SIZE_OPCTRLCAM1_DBG_WRECC_Q_DEPTH) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.OPREFCTRL0
   //------------------------
   wire reg_ddrc_rank0_refresh_pclk;
   assign reg_ddrc_rank0_refresh_pclk = r240_oprefctrl0[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK0_REFRESH+:`REGB_DDRC_CH0_SIZE_OPREFCTRL0_RANK0_REFRESH];
 reg reg_ddrc_rank0_refresh_pclk_s0;
 reg reg_ddrc_rank0_refresh_ack;
 // reset reg_ddrc_rank0_refresh field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rank0_refresh_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rank0_refresh_pclk_s0 <= 1'b0;
 reg_ddrc_rank0_refresh_ack <= 1'b0;
 end else begin
 reg_ddrc_rank0_refresh_pclk_s0 <= reg_ddrc_rank0_refresh_pclk;
 reg_ddrc_rank0_refresh_ack <= reg_ddrc_rank0_refresh;
 end
 end
 assign reg_ddrc_rank0_refresh = reg_ddrc_rank0_refresh_pclk & (!reg_ddrc_rank0_refresh_pclk_s0);
 assign reg_ddrc_rank0_refresh_ack_pclk = reg_ddrc_rank0_refresh_ack;
 assign ddrc_reg_rank0_refresh_busy_int = ddrc_reg_rank0_refresh_busy;
   wire reg_ddrc_rank1_refresh_pclk;
   assign reg_ddrc_rank1_refresh_pclk = r240_oprefctrl0[`REGB_DDRC_CH0_OFFSET_OPREFCTRL0_RANK1_REFRESH+:`REGB_DDRC_CH0_SIZE_OPREFCTRL0_RANK1_REFRESH];
 reg reg_ddrc_rank1_refresh_pclk_s0;
 reg reg_ddrc_rank1_refresh_ack;
 // reset reg_ddrc_rank1_refresh field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_rank1_refresh_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_rank1_refresh_pclk_s0 <= 1'b0;
 reg_ddrc_rank1_refresh_ack <= 1'b0;
 end else begin
 reg_ddrc_rank1_refresh_pclk_s0 <= reg_ddrc_rank1_refresh_pclk;
 reg_ddrc_rank1_refresh_ack <= reg_ddrc_rank1_refresh;
 end
 end
 assign reg_ddrc_rank1_refresh = reg_ddrc_rank1_refresh_pclk & (!reg_ddrc_rank1_refresh_pclk_s0);
 assign reg_ddrc_rank1_refresh_ack_pclk = reg_ddrc_rank1_refresh_ack;
 assign ddrc_reg_rank1_refresh_busy_int = ddrc_reg_rank1_refresh_busy;
   //------------------------
   // Register REGB_DDRC_CH0.OPREFSTAT0
   //------------------------
   always_comb begin : r242_oprefstat0_combo_PROC
      r242_oprefstat0 = {REG_WIDTH{1'b0}};
      r242_oprefstat0[`REGB_DDRC_CH0_OFFSET_OPREFSTAT0_RANK0_REFRESH_BUSY+:`REGB_DDRC_CH0_SIZE_OPREFSTAT0_RANK0_REFRESH_BUSY] = ddrc_reg_rank0_refresh_busy | ff_regb_ddrc_ch0_rank0_refresh_saved;
      r242_oprefstat0[`REGB_DDRC_CH0_OFFSET_OPREFSTAT0_RANK1_REFRESH_BUSY+:`REGB_DDRC_CH0_SIZE_OPREFSTAT0_RANK1_REFRESH_BUSY] = ddrc_reg_rank1_refresh_busy | ff_regb_ddrc_ch0_rank1_refresh_saved;
   end
   //------------------------
   // Register REGB_DDRC_CH0.SWCTL
   //------------------------
   assign reg_ddrc_sw_done = r249_swctl[`REGB_DDRC_CH0_OFFSET_SWCTL_SW_DONE+:`REGB_DDRC_CH0_SIZE_SWCTL_SW_DONE];
   //------------------------
   // Register REGB_DDRC_CH0.SWSTAT
   //------------------------
   always_comb begin : r250_swstat_combo_PROC
      r250_swstat = {REG_WIDTH{1'b0}};
      r250_swstat[`REGB_DDRC_CH0_OFFSET_SWSTAT_SW_DONE_ACK+:`REGB_DDRC_CH0_SIZE_SWSTAT_SW_DONE_ACK] = ddrc_reg_sw_done_ack;
   end
   //------------------------
   // Register REGB_DDRC_CH0.RANKCTL
   //------------------------
   assign reg_ddrc_max_rank_rd[(`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD) -1:0] = r253_rankctl[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_RD+:`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_RD];
   assign reg_ddrc_max_rank_wr[(`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR) -1:0] = r253_rankctl[`REGB_DDRC_CH0_OFFSET_RANKCTL_MAX_RANK_WR+:`REGB_DDRC_CH0_SIZE_RANKCTL_MAX_RANK_WR];
   //------------------------
   // Register REGB_DDRC_CH0.DBICTL
   //------------------------
   assign reg_ddrc_dm_en = r254_dbictl[`REGB_DDRC_CH0_OFFSET_DBICTL_DM_EN+:`REGB_DDRC_CH0_SIZE_DBICTL_DM_EN];
   assign reg_ddrc_wr_dbi_en = r254_dbictl[`REGB_DDRC_CH0_OFFSET_DBICTL_WR_DBI_EN+:`REGB_DDRC_CH0_SIZE_DBICTL_WR_DBI_EN];
   assign reg_ddrc_rd_dbi_en = r254_dbictl[`REGB_DDRC_CH0_OFFSET_DBICTL_RD_DBI_EN+:`REGB_DDRC_CH0_SIZE_DBICTL_RD_DBI_EN];
   //------------------------
   // Register REGB_DDRC_CH0.ODTMAP
   //------------------------
   assign reg_ddrc_rank0_wr_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT) -1:0] = r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_WR_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_WR_ODT];
   assign reg_ddrc_rank0_rd_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT) -1:0] = r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK0_RD_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK0_RD_ODT];
   assign reg_ddrc_rank1_wr_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT) -1:0] = r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_WR_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_WR_ODT];
   assign reg_ddrc_rank1_rd_odt[(`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT) -1:0] = r256_odtmap[`REGB_DDRC_CH0_OFFSET_ODTMAP_RANK1_RD_ODT+:`REGB_DDRC_CH0_SIZE_ODTMAP_RANK1_RD_ODT];
   //------------------------
   // Register REGB_DDRC_CH0.DATACTL0
   //------------------------
   assign reg_ddrc_rd_data_copy_en = r257_datactl0[`REGB_DDRC_CH0_OFFSET_DATACTL0_RD_DATA_COPY_EN+:`REGB_DDRC_CH0_SIZE_DATACTL0_RD_DATA_COPY_EN];
   assign reg_ddrc_wr_data_copy_en = r257_datactl0[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_COPY_EN+:`REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_COPY_EN];
   assign reg_ddrc_wr_data_x_en = r257_datactl0[`REGB_DDRC_CH0_OFFSET_DATACTL0_WR_DATA_X_EN+:`REGB_DDRC_CH0_SIZE_DATACTL0_WR_DATA_X_EN];
   //------------------------
   // Register REGB_DDRC_CH0.SWCTLSTATIC
   //------------------------
   assign reg_ddrc_sw_static_unlock = r258_swctlstatic[`REGB_DDRC_CH0_OFFSET_SWCTLSTATIC_SW_STATIC_UNLOCK+:`REGB_DDRC_CH0_SIZE_SWCTLSTATIC_SW_STATIC_UNLOCK];
   //------------------------
   // Register REGB_DDRC_CH0.CGCTL
   //------------------------
   assign reg_ddrc_force_clk_te_en = r259_cgctl[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_TE_EN+:`REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_TE_EN];
   assign reg_ddrc_force_clk_arb_en = r259_cgctl[`REGB_DDRC_CH0_OFFSET_CGCTL_FORCE_CLK_ARB_EN+:`REGB_DDRC_CH0_SIZE_CGCTL_FORCE_CLK_ARB_EN];
   //------------------------
   // Register REGB_DDRC_CH0.INITTMG0
   //------------------------
   assign reg_ddrc_pre_cke_x1024[(`REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024) -1:0] = r260_inittmg0[`REGB_DDRC_CH0_OFFSET_INITTMG0_PRE_CKE_X1024+:`REGB_DDRC_CH0_SIZE_INITTMG0_PRE_CKE_X1024];
   assign reg_ddrc_post_cke_x1024[(`REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024) -1:0] = r260_inittmg0[`REGB_DDRC_CH0_OFFSET_INITTMG0_POST_CKE_X1024+:`REGB_DDRC_CH0_SIZE_INITTMG0_POST_CKE_X1024];
   assign reg_ddrc_skip_dram_init[(`REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT) -1:0] = r260_inittmg0[`REGB_DDRC_CH0_OFFSET_INITTMG0_SKIP_DRAM_INIT+:`REGB_DDRC_CH0_SIZE_INITTMG0_SKIP_DRAM_INIT];
   //------------------------
   // Register REGB_DDRC_CH0.PPT2CTRL0
   //------------------------
   assign reg_ddrc_ppt2_burst_num[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM) -1:0] = r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST_NUM+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST_NUM];
   assign reg_ddrc_ppt2_ctrlupd_num_dfi0[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0) -1:0] = r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI0];
   assign reg_ddrc_ppt2_ctrlupd_num_dfi1[(`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1) -1:0] = r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_CTRLUPD_NUM_DFI1];
   wire reg_ddrc_ppt2_burst_pclk;
   assign reg_ddrc_ppt2_burst_pclk = r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_BURST+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_BURST];
 reg reg_ddrc_ppt2_burst_pclk_s0;
 reg reg_ddrc_ppt2_burst_ack;
 // reset reg_ddrc_ppt2_burst field when the core logic has completed the update
 always @(posedge apb_clk or negedge apb_rst) begin : sample_reg_ddrc_ppt2_burst_ack_PROC
 if (~apb_rst) begin
 reg_ddrc_ppt2_burst_pclk_s0 <= 1'b0;
 reg_ddrc_ppt2_burst_ack <= 1'b0;
 end else begin
 reg_ddrc_ppt2_burst_pclk_s0 <= reg_ddrc_ppt2_burst_pclk;
 reg_ddrc_ppt2_burst_ack <= reg_ddrc_ppt2_burst;
 end
 end
 assign reg_ddrc_ppt2_burst = reg_ddrc_ppt2_burst_pclk & (!reg_ddrc_ppt2_burst_pclk_s0);
 assign reg_ddrc_ppt2_burst_ack_pclk = reg_ddrc_ppt2_burst_ack;
 assign ddrc_reg_ppt2_burst_busy_int = ddrc_reg_ppt2_burst_busy;
   assign reg_ddrc_ppt2_wait_ref = r285_ppt2ctrl0[`REGB_DDRC_CH0_OFFSET_PPT2CTRL0_PPT2_WAIT_REF+:`REGB_DDRC_CH0_SIZE_PPT2CTRL0_PPT2_WAIT_REF];
   //------------------------
   // Register REGB_DDRC_CH0.PPT2STAT0
   //------------------------
   always_comb begin : r286_ppt2stat0_combo_PROC
      r286_ppt2stat0 = {REG_WIDTH{1'b0}};
      r286_ppt2stat0[`REGB_DDRC_CH0_OFFSET_PPT2STAT0_PPT2_STATE+:`REGB_DDRC_CH0_SIZE_PPT2STAT0_PPT2_STATE] = ddrc_reg_ppt2_state[(`REGB_DDRC_CH0_SIZE_PPT2STAT0_PPT2_STATE) -1:0];
      r286_ppt2stat0[`REGB_DDRC_CH0_OFFSET_PPT2STAT0_PPT2_BURST_BUSY+:`REGB_DDRC_CH0_SIZE_PPT2STAT0_PPT2_BURST_BUSY] = ddrc_reg_ppt2_burst_busy | ff_regb_ddrc_ch0_ppt2_burst_saved;
   end
   //------------------------
   // Register REGB_DDRC_CH0.DDRCTL_VER_NUMBER
   //------------------------
   always_comb begin : r289_ddrctl_ver_number_combo_PROC
      r289_ddrctl_ver_number = {REG_WIDTH{1'b0}};
      r289_ddrctl_ver_number[`REGB_DDRC_CH0_OFFSET_DDRCTL_VER_NUMBER_VER_NUMBER+:`REGB_DDRC_CH0_SIZE_DDRCTL_VER_NUMBER_VER_NUMBER] = ddrc_reg_ver_number[(`REGB_DDRC_CH0_SIZE_DDRCTL_VER_NUMBER_VER_NUMBER) -1:0];
   end
   //------------------------
   // Register REGB_DDRC_CH0.DDRCTL_VER_TYPE
   //------------------------
   always_comb begin : r290_ddrctl_ver_type_combo_PROC
      r290_ddrctl_ver_type = {REG_WIDTH{1'b0}};
      r290_ddrctl_ver_type[`REGB_DDRC_CH0_OFFSET_DDRCTL_VER_TYPE_VER_TYPE+:`REGB_DDRC_CH0_SIZE_DDRCTL_VER_TYPE_VER_TYPE] = ddrc_reg_ver_type[(`REGB_DDRC_CH0_SIZE_DDRCTL_VER_TYPE_VER_TYPE) -1:0];
   end
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP1
   //------------------------
   assign reg_ddrc_addrmap_cs_bit0_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0) -1:0] = r495_addrmap1_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP1_ADDRMAP_CS_BIT0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP1_ADDRMAP_CS_BIT0];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP3
   //------------------------
   assign reg_ddrc_addrmap_bank_b0_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0) -1:0] = r497_addrmap3_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B0];
   assign reg_ddrc_addrmap_bank_b1_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1) -1:0] = r497_addrmap3_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B1+:`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B1];
   assign reg_ddrc_addrmap_bank_b2_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2) -1:0] = r497_addrmap3_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP3_ADDRMAP_BANK_B2+:`REGB_ADDR_MAP0_SIZE_ADDRMAP3_ADDRMAP_BANK_B2];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP4
   //------------------------
   assign reg_ddrc_addrmap_bg_b0_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0) -1:0] = r498_addrmap4_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B0];
   assign reg_ddrc_addrmap_bg_b1_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1) -1:0] = r498_addrmap4_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP4_ADDRMAP_BG_B1+:`REGB_ADDR_MAP0_SIZE_ADDRMAP4_ADDRMAP_BG_B1];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP5
   //------------------------
   assign reg_ddrc_addrmap_col_b7_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7) -1:0] = r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B7+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B7];
   assign reg_ddrc_addrmap_col_b8_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8) -1:0] = r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B8+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B8];
   assign reg_ddrc_addrmap_col_b9_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9) -1:0] = r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B9+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B9];
   assign reg_ddrc_addrmap_col_b10_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10) -1:0] = r499_addrmap5_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP5_ADDRMAP_COL_B10+:`REGB_ADDR_MAP0_SIZE_ADDRMAP5_ADDRMAP_COL_B10];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP6
   //------------------------
   assign reg_ddrc_addrmap_col_b3_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3) -1:0] = r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B3+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B3];
   assign reg_ddrc_addrmap_col_b4_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4) -1:0] = r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B4+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B4];
   assign reg_ddrc_addrmap_col_b5_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5) -1:0] = r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B5+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B5];
   assign reg_ddrc_addrmap_col_b6_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6) -1:0] = r500_addrmap6_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP6_ADDRMAP_COL_B6+:`REGB_ADDR_MAP0_SIZE_ADDRMAP6_ADDRMAP_COL_B6];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP7
   //------------------------
   assign reg_ddrc_addrmap_row_b14_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14) -1:0] = r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B14+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B14];
   assign reg_ddrc_addrmap_row_b15_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15) -1:0] = r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B15+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B15];
   assign reg_ddrc_addrmap_row_b16_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16) -1:0] = r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B16+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B16];
   assign reg_ddrc_addrmap_row_b17_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17) -1:0] = r501_addrmap7_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP7_ADDRMAP_ROW_B17+:`REGB_ADDR_MAP0_SIZE_ADDRMAP7_ADDRMAP_ROW_B17];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP8
   //------------------------
   assign reg_ddrc_addrmap_row_b10_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10) -1:0] = r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B10+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B10];
   assign reg_ddrc_addrmap_row_b11_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11) -1:0] = r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B11+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B11];
   assign reg_ddrc_addrmap_row_b12_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12) -1:0] = r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B12+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B12];
   assign reg_ddrc_addrmap_row_b13_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13) -1:0] = r502_addrmap8_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP8_ADDRMAP_ROW_B13+:`REGB_ADDR_MAP0_SIZE_ADDRMAP8_ADDRMAP_ROW_B13];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP9
   //------------------------
   assign reg_ddrc_addrmap_row_b6_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6) -1:0] = r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B6+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B6];
   assign reg_ddrc_addrmap_row_b7_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7) -1:0] = r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B7+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B7];
   assign reg_ddrc_addrmap_row_b8_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8) -1:0] = r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B8+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B8];
   assign reg_ddrc_addrmap_row_b9_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9) -1:0] = r503_addrmap9_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP9_ADDRMAP_ROW_B9+:`REGB_ADDR_MAP0_SIZE_ADDRMAP9_ADDRMAP_ROW_B9];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP10
   //------------------------
   assign reg_ddrc_addrmap_row_b2_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2) -1:0] = r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B2+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B2];
   assign reg_ddrc_addrmap_row_b3_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3) -1:0] = r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B3+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B3];
   assign reg_ddrc_addrmap_row_b4_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4) -1:0] = r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B4+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B4];
   assign reg_ddrc_addrmap_row_b5_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5) -1:0] = r504_addrmap10_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP10_ADDRMAP_ROW_B5+:`REGB_ADDR_MAP0_SIZE_ADDRMAP10_ADDRMAP_ROW_B5];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP11
   //------------------------
   assign reg_ddrc_addrmap_row_b0_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0) -1:0] = r505_addrmap11_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B0+:`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B0];
   assign reg_ddrc_addrmap_row_b1_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1) -1:0] = r505_addrmap11_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP11_ADDRMAP_ROW_B1+:`REGB_ADDR_MAP0_SIZE_ADDRMAP11_ADDRMAP_ROW_B1];
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP12
   //------------------------
   assign reg_ddrc_nonbinary_device_density_map0[(`REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY) -1:0] = r506_addrmap12_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_NONBINARY_DEVICE_DENSITY+:`REGB_ADDR_MAP0_SIZE_ADDRMAP12_NONBINARY_DEVICE_DENSITY];
   assign reg_ddrc_bank_hash_en_map0 = r506_addrmap12_map0[`REGB_ADDR_MAP0_OFFSET_ADDRMAP12_BANK_HASH_EN+:`REGB_ADDR_MAP0_SIZE_ADDRMAP12_BANK_HASH_EN];
   //------------------------
   // Register REGB_ARB_PORT0.PCCFG
   //------------------------
   assign reg_arb_go2critical_en_port0 = r521_pccfg_port0[`REGB_ARB_PORT0_OFFSET_PCCFG_GO2CRITICAL_EN+:`REGB_ARB_PORT0_SIZE_PCCFG_GO2CRITICAL_EN];
   assign reg_arb_pagematch_limit_port0 = r521_pccfg_port0[`REGB_ARB_PORT0_OFFSET_PCCFG_PAGEMATCH_LIMIT+:`REGB_ARB_PORT0_SIZE_PCCFG_PAGEMATCH_LIMIT];
   //------------------------
   // Register REGB_ARB_PORT0.PCFGR
   //------------------------
   assign reg_arb_rd_port_priority_port0[(`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY) -1:0] = r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PRIORITY+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PRIORITY];
   assign reg_arb_rd_port_aging_en_port0 = r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_AGING_EN+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_AGING_EN];
   assign reg_arb_rd_port_urgent_en_port0 = r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_URGENT_EN+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_URGENT_EN];
   assign reg_arb_rd_port_pagematch_en_port0 = r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RD_PORT_PAGEMATCH_EN+:`REGB_ARB_PORT0_SIZE_PCFGR_RD_PORT_PAGEMATCH_EN];
   assign reg_arb_rrb_lock_threshold_port0[(`REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD) -1:0] = r522_pcfgr_port0[`REGB_ARB_PORT0_OFFSET_PCFGR_RRB_LOCK_THRESHOLD+:`REGB_ARB_PORT0_SIZE_PCFGR_RRB_LOCK_THRESHOLD];
   //------------------------
   // Register REGB_ARB_PORT0.PCFGW
   //------------------------
   assign reg_arb_wr_port_priority_port0[(`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY) -1:0] = r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PRIORITY+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PRIORITY];
   assign reg_arb_wr_port_aging_en_port0 = r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_AGING_EN+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_AGING_EN];
   assign reg_arb_wr_port_urgent_en_port0 = r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_URGENT_EN+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_URGENT_EN];
   assign reg_arb_wr_port_pagematch_en_port0 = r523_pcfgw_port0[`REGB_ARB_PORT0_OFFSET_PCFGW_WR_PORT_PAGEMATCH_EN+:`REGB_ARB_PORT0_SIZE_PCFGW_WR_PORT_PAGEMATCH_EN];
   //------------------------
   // Register REGB_ARB_PORT0.PCTRL
   //------------------------
   assign reg_arb_port_en_port0 = r556_pctrl_port0[`REGB_ARB_PORT0_OFFSET_PCTRL_PORT_EN+:`REGB_ARB_PORT0_SIZE_PCTRL_PORT_EN];
   assign reg_apb_port_en_port0 = r556_pctrl_port0[`REGB_ARB_PORT0_OFFSET_PCTRL_PORT_EN+:`REGB_ARB_PORT0_SIZE_PCTRL_PORT_EN];
   assign reg_arba0_port_en_port0 = r556_pctrl_port0[`REGB_ARB_PORT0_OFFSET_PCTRL_PORT_EN+:`REGB_ARB_PORT0_SIZE_PCTRL_PORT_EN];
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS0
   //------------------------
   assign reg_arba0_rqos_map_level1_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1) -1:0] = r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL1+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL1];
   assign reg_arba0_rqos_map_level2_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2) -1:0] = r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_LEVEL2+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_LEVEL2];
   assign reg_arba0_rqos_map_region0_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0) -1:0] = r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION0+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION0];
   assign reg_arba0_rqos_map_region1_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1) -1:0] = r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION1+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION1];
   assign reg_arba0_rqos_map_region2_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2) -1:0] = r557_pcfgqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS0_RQOS_MAP_REGION2+:`REGB_ARB_PORT0_SIZE_PCFGQOS0_RQOS_MAP_REGION2];
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS1
   //------------------------
   assign reg_arb_rqos_map_timeoutb_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB) -1:0] = r558_pcfgqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTB+:`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTB];
   assign reg_arb_rqos_map_timeoutr_port0[(`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR) -1:0] = r558_pcfgqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGQOS1_RQOS_MAP_TIMEOUTR+:`REGB_ARB_PORT0_SIZE_PCFGQOS1_RQOS_MAP_TIMEOUTR];
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS0
   //------------------------
   assign reg_arba0_wqos_map_level1_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1) -1:0] = r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL1+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL1];
   assign reg_arba0_wqos_map_level2_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2) -1:0] = r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_LEVEL2+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_LEVEL2];
   assign reg_arba0_wqos_map_region0_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0) -1:0] = r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION0+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION0];
   assign reg_arba0_wqos_map_region1_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1) -1:0] = r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION1+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION1];
   assign reg_arba0_wqos_map_region2_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2) -1:0] = r559_pcfgwqos0_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS0_WQOS_MAP_REGION2+:`REGB_ARB_PORT0_SIZE_PCFGWQOS0_WQOS_MAP_REGION2];
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS1
   //------------------------
   assign reg_arb_wqos_map_timeout1_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1) -1:0] = r560_pcfgwqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT1+:`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT1];
   assign reg_arb_wqos_map_timeout2_port0[(`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2) -1:0] = r560_pcfgwqos1_port0[`REGB_ARB_PORT0_OFFSET_PCFGWQOS1_WQOS_MAP_TIMEOUT2+:`REGB_ARB_PORT0_SIZE_PCFGWQOS1_WQOS_MAP_TIMEOUT2];
   //------------------------
   // Register REGB_ARB_PORT0.SBRCTL
   //------------------------
   assign reg_arb_scrub_en_port0 = r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_EN+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_EN];
   assign reg_arb_scrub_during_lowpower_port0 = r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_DURING_LOWPOWER+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_DURING_LOWPOWER];
   assign reg_arb_scrub_burst_length_nm_port0[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM) -1:0] = r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_NM+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_NM];
   assign reg_arb_scrub_interval_port0[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL) -1:0] = r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_INTERVAL+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_INTERVAL];
   assign reg_arb_scrub_cmd_type_port0[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE) -1:0] = r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_CMD_TYPE+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_CMD_TYPE];
   assign reg_arb_scrub_burst_length_lp_port0[(`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP) -1:0] = r569_sbrctl_port0[`REGB_ARB_PORT0_OFFSET_SBRCTL_SCRUB_BURST_LENGTH_LP+:`REGB_ARB_PORT0_SIZE_SBRCTL_SCRUB_BURST_LENGTH_LP];
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTAT
   //------------------------
   always_comb begin : r570_sbrstat_port0_combo_PROC
      r570_sbrstat_port0 = {REG_WIDTH{1'b0}};
      r570_sbrstat_port0[`REGB_ARB_PORT0_OFFSET_SBRSTAT_SCRUB_BUSY+:`REGB_ARB_PORT0_SIZE_SBRSTAT_SCRUB_BUSY] = arb_reg_scrub_busy_port0;
      r570_sbrstat_port0[`REGB_ARB_PORT0_OFFSET_SBRSTAT_SCRUB_DONE+:`REGB_ARB_PORT0_SIZE_SBRSTAT_SCRUB_DONE] = arb_reg_scrub_done_port0;
   end
   //------------------------
   // Register REGB_ARB_PORT0.SBRWDATA0
   //------------------------
   assign reg_arb_scrub_pattern0_port0[(`REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0) -1:0] = r571_sbrwdata0_port0[`REGB_ARB_PORT0_OFFSET_SBRWDATA0_SCRUB_PATTERN0+:`REGB_ARB_PORT0_SIZE_SBRWDATA0_SCRUB_PATTERN0];
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART0
   //------------------------
   assign reg_arb_sbr_address_start_mask_0_port0[(`REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0) -1:0] = r573_sbrstart0_port0[`REGB_ARB_PORT0_OFFSET_SBRSTART0_SBR_ADDRESS_START_MASK_0+:`REGB_ARB_PORT0_SIZE_SBRSTART0_SBR_ADDRESS_START_MASK_0];
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART1
   //------------------------
   assign reg_arb_sbr_address_start_mask_1_port0[(`REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1) -1:0] = r574_sbrstart1_port0[`REGB_ARB_PORT0_OFFSET_SBRSTART1_SBR_ADDRESS_START_MASK_1+:`REGB_ARB_PORT0_SIZE_SBRSTART1_SBR_ADDRESS_START_MASK_1];
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE0
   //------------------------
   assign reg_arb_sbr_address_range_mask_0_port0[(`REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0) -1:0] = r575_sbrrange0_port0[`REGB_ARB_PORT0_OFFSET_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0+:`REGB_ARB_PORT0_SIZE_SBRRANGE0_SBR_ADDRESS_RANGE_MASK_0];
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE1
   //------------------------
   assign reg_arb_sbr_address_range_mask_1_port0[(`REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1) -1:0] = r576_sbrrange1_port0[`REGB_ARB_PORT0_OFFSET_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1+:`REGB_ARB_PORT0_SIZE_SBRRANGE1_SBR_ADDRESS_RANGE_MASK_1];
   //------------------------
   // Register REGB_ARB_PORT0.PSTAT
   //------------------------
   always_comb begin : r582_pstat_port0_combo_PROC
      r582_pstat_port0 = {REG_WIDTH{1'b0}};
      r582_pstat_port0[`REGB_ARB_PORT0_OFFSET_PSTAT_RD_PORT_BUSY_0+:`REGB_ARB_PORT0_SIZE_PSTAT_RD_PORT_BUSY_0] = arb_reg_rd_port_busy_0_port0;
      r582_pstat_port0[`REGB_ARB_PORT0_OFFSET_PSTAT_WR_PORT_BUSY_0+:`REGB_ARB_PORT0_SIZE_PSTAT_WR_PORT_BUSY_0] = arb_reg_wr_port_busy_0_port0;
   end
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG0
   //------------------------
   assign reg_ddrc_t_ras_min_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] = r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
   assign reg_ddrc_t_ras_max_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] = r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
   assign reg_ddrc_t_faw_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] = r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_T_FAW];
   assign reg_ddrc_wr2pre_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] = r1929_dramset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG1
   //------------------------
   assign reg_ddrc_t_rc_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] = r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RC];
   assign reg_ddrc_rd2pre_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] = r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
   assign reg_ddrc_t_xp_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] = r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_XP];
   assign reg_ddrc_t_rcd_write_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] = r1930_dramset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG2
   //------------------------
   assign reg_ddrc_wr2rd_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] = r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WR2RD];
   assign reg_ddrc_rd2wr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] = r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_RD2WR];
   assign reg_ddrc_read_latency_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] = r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
   assign reg_ddrc_write_latency_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] = r1931_dramset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG3
   //------------------------
   assign reg_ddrc_wr2mr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] = r1932_dramset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_WR2MR];
   assign reg_ddrc_rd2mr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] = r1932_dramset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_RD2MR];
   assign reg_ddrc_t_mr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] = r1932_dramset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG3_T_MR];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG4
   //------------------------
   assign reg_ddrc_t_rp_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] = r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RP];
   assign reg_ddrc_t_rrd_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] = r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RRD];
   assign reg_ddrc_t_ccd_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] = r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_CCD];
   assign reg_ddrc_t_rcd_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] = r1933_dramset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG4_T_RCD];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG5
   //------------------------
   assign reg_ddrc_t_cke_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] = r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKE];
   assign reg_ddrc_t_ckesr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] = r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
   assign reg_ddrc_t_cksre_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] = r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
   assign reg_ddrc_t_cksrx_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] = r1934_dramset1tmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG6
   //------------------------
   assign reg_ddrc_t_ckcsx_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] = r1935_dramset1tmg6_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG7
   //------------------------
   assign reg_ddrc_t_csh_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] = r1936_dramset1tmg7_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG7_T_CSH];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG9
   //------------------------
   assign reg_ddrc_wr2rd_s_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] = r1938_dramset1tmg9_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
   assign reg_ddrc_t_rrd_s_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] = r1938_dramset1tmg9_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
   assign reg_ddrc_t_ccd_s_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] = r1938_dramset1tmg9_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG12
   //------------------------
   assign reg_ddrc_t_cmdcke_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] = r1941_dramset1tmg12_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG13
   //------------------------
   assign reg_ddrc_t_ppd_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] = r1942_dramset1tmg13_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_PPD];
   assign reg_ddrc_t_ccd_mw_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] = r1942_dramset1tmg13_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
   assign reg_ddrc_odtloff_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] = r1942_dramset1tmg13_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG14
   //------------------------
   assign reg_ddrc_t_xsr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] = r1943_dramset1tmg14_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_XSR];
   assign reg_ddrc_t_osco_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] = r1943_dramset1tmg14_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG17
   //------------------------
   assign reg_ddrc_t_vrcg_disable_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] = r1946_dramset1tmg17_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
   assign reg_ddrc_t_vrcg_enable_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] = r1946_dramset1tmg17_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG23
   //------------------------
   assign reg_ddrc_t_pdn_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] = r1951_dramset1tmg23_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_PDN];
   assign reg_ddrc_t_xsr_dsm_x1024_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] = r1951_dramset1tmg23_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG24
   //------------------------
   assign reg_ddrc_max_wr_sync_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] = r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
   assign reg_ddrc_max_rd_sync_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] = r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
   assign reg_ddrc_rd2wr_s_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] = r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
   assign reg_ddrc_bank_org_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] = r1952_dramset1tmg24_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG25
   //------------------------
   assign reg_ddrc_rda2pre_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] = r1953_dramset1tmg25_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
   assign reg_ddrc_wra2pre_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] = r1953_dramset1tmg25_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
   assign reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] = r1953_dramset1tmg25_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG30
   //------------------------
   assign reg_ddrc_mrr2rd_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] = r1958_dramset1tmg30_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
   assign reg_ddrc_mrr2wr_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] = r1958_dramset1tmg30_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
   assign reg_ddrc_mrr2mrw_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] = r1958_dramset1tmg30_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG32
   //------------------------
   assign reg_ddrc_ws_fs2wck_sus_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] = r1960_dramset1tmg32_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
   assign reg_ddrc_t_wcksus_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] = r1960_dramset1tmg32_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
   assign reg_ddrc_ws_off2ws_fs_freq0[(`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] = r1960_dramset1tmg32_freq0[`REGB_FREQ0_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ0_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR0
   //------------------------
   assign reg_ddrc_emr_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR0_EMR) -1:0] = r1991_initmr0_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ0_CH0_SIZE_INITMR0_EMR];
   assign reg_ddrc_mr_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR0_MR) -1:0] = r1991_initmr0_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ0_CH0_SIZE_INITMR0_MR];
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR1
   //------------------------
   assign reg_ddrc_emr3_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR1_EMR3) -1:0] = r1992_initmr1_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ0_CH0_SIZE_INITMR1_EMR3];
   assign reg_ddrc_emr2_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR1_EMR2) -1:0] = r1992_initmr1_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ0_CH0_SIZE_INITMR1_EMR2];
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR2
   //------------------------
   assign reg_ddrc_mr5_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR2_MR5) -1:0] = r1993_initmr2_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ0_CH0_SIZE_INITMR2_MR5];
   assign reg_ddrc_mr4_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR2_MR4) -1:0] = r1993_initmr2_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ0_CH0_SIZE_INITMR2_MR4];
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR3
   //------------------------
   assign reg_ddrc_mr6_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR3_MR6) -1:0] = r1994_initmr3_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ0_CH0_SIZE_INITMR3_MR6];
   assign reg_ddrc_mr22_freq0[(`REGB_FREQ0_CH0_SIZE_INITMR3_MR22) -1:0] = r1994_initmr3_freq0[`REGB_FREQ0_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ0_CH0_SIZE_INITMR3_MR22];
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG0
   //------------------------
   assign reg_ddrc_dfi_tphy_wrlat_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] = r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
   assign reg_ddrc_dfi_tphy_wrdata_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] = r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
   assign reg_ddrc_dfi_t_rddata_en_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] = r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
   assign reg_ddrc_dfi_t_ctrl_delay_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] = r1995_dfitmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ0_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG1
   //------------------------
   assign reg_ddrc_dfi_t_dram_clk_enable_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] = r1996_dfitmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
   assign reg_ddrc_dfi_t_dram_clk_disable_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] = r1996_dfitmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
   assign reg_ddrc_dfi_t_wrdata_delay_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] = r1996_dfitmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ0_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG2
   //------------------------
   assign reg_ddrc_dfi_tphy_wrcslat_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] = r1997_dfitmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
   assign reg_ddrc_dfi_tphy_rdcslat_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] = r1997_dfitmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
   assign reg_ddrc_dfi_twck_delay_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] = r1997_dfitmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ0_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG4
   //------------------------
   assign reg_ddrc_dfi_twck_dis_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] = r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
   assign reg_ddrc_dfi_twck_en_fs_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] = r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
   assign reg_ddrc_dfi_twck_en_wr_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] = r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
   assign reg_ddrc_dfi_twck_en_rd_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] = r1999_dfitmg4_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ0_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG5
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] = r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
   assign reg_ddrc_dfi_twck_toggle_cs_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] = r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
   assign reg_ddrc_dfi_twck_toggle_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] = r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
   assign reg_ddrc_dfi_twck_fast_toggle_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] = r2000_dfitmg5_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ0_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG6
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_rd_freq0[(`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] = r2001_dfitmg6_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
   assign reg_ddrc_dfi_twck_toggle_post_rd_en_freq0 = r2001_dfitmg6_freq0[`REGB_FREQ0_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ0_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG0
   //------------------------
   assign reg_ddrc_dfi_lp_wakeup_pd_freq0[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD) -1:0] = r2003_dfilptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_PD+:`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_PD];
   assign reg_ddrc_dfi_lp_wakeup_sr_freq0[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR) -1:0] = r2003_dfilptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_SR+:`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_SR];
   assign reg_ddrc_dfi_lp_wakeup_dsm_freq0[(`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM) -1:0] = r2003_dfilptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG0_DFI_LP_WAKEUP_DSM+:`REGB_FREQ0_CH0_SIZE_DFILPTMG0_DFI_LP_WAKEUP_DSM];
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG1
   //------------------------
   assign reg_ddrc_dfi_lp_wakeup_data_freq0[(`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA) -1:0] = r2004_dfilptmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_LP_WAKEUP_DATA+:`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_LP_WAKEUP_DATA];
   assign reg_ddrc_dfi_tlp_resp_freq0[(`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP) -1:0] = r2004_dfilptmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFILPTMG1_DFI_TLP_RESP+:`REGB_FREQ0_CH0_SIZE_DFILPTMG1_DFI_TLP_RESP];
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG0
   //------------------------
   assign reg_ddrc_dfi_t_ctrlup_min_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN) -1:0] = r2005_dfiupdtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MIN+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MIN];
   assign reg_ddrc_dfi_t_ctrlup_max_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX) -1:0] = r2005_dfiupdtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG0_DFI_T_CTRLUP_MAX+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG0_DFI_T_CTRLUP_MAX];
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG1
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] = r2006_dfiupdtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
   assign reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] = r2006_dfiupdtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG2
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] = r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
   assign reg_ddrc_ctrlupd_after_dqsosc_freq0 = r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
   assign reg_ddrc_ppt2_override_freq0 = r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
   assign reg_ddrc_ppt2_en_freq0 = r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] = r2008_dfiupdtmg2_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG3
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0[(`REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] = r2009_dfiupdtmg3_freq0[`REGB_FREQ0_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ0_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG0
   //------------------------
   assign reg_ddrc_t_refi_x1_x32_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] = r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
   assign reg_ddrc_refresh_to_x1_x32_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] = r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
   assign reg_ddrc_refresh_margin_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] = r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
   assign reg_ddrc_refresh_to_x1_sel_freq0 = r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
   assign reg_ddrc_t_refi_x1_sel_freq0 = r2010_rfshset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG1
   //------------------------
   assign reg_ddrc_t_rfc_min_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] = r2011_rfshset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
   assign reg_ddrc_t_rfc_min_ab_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] = r2011_rfshset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG2
   //------------------------
   assign reg_ddrc_t_pbr2pbr_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] = r2012_rfshset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
   assign reg_ddrc_t_pbr2act_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] = r2012_rfshset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG3
   //------------------------
   assign reg_ddrc_refresh_to_ab_x32_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] = r2013_rfshset1tmg3_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG4
   //------------------------
   assign reg_ddrc_refresh_timer0_start_value_x32_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] = r2014_rfshset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
   assign reg_ddrc_refresh_timer1_start_value_x32_freq0[(`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] = r2014_rfshset1tmg4_freq0[`REGB_FREQ0_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ0_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
   //------------------------
   // Register REGB_FREQ0_CH0.RFMSET1TMG0
   //------------------------
   assign reg_ddrc_t_rfmpb_freq0[(`REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] = r2024_rfmset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ0_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG0
   //------------------------
   assign reg_ddrc_t_zq_long_nop_freq0[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] = r2035_zqset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
   assign reg_ddrc_t_zq_short_nop_freq0[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] = r2035_zqset1tmg0_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG1
   //------------------------
   assign reg_ddrc_t_zq_short_interval_x1024_freq0[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] = r2036_zqset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
   assign reg_ddrc_t_zq_reset_nop_freq0[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] = r2036_zqset1tmg1_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG2
   //------------------------
   assign reg_ddrc_t_zq_stop_freq0[(`REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] = r2037_zqset1tmg2_freq0[`REGB_FREQ0_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ0_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
   //------------------------
   // Register REGB_FREQ0_CH0.DQSOSCCTL0
   //------------------------
   assign reg_ddrc_dqsosc_enable_freq0 = r2046_dqsoscctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
   assign reg_ddrc_dqsosc_interval_unit_freq0 = r2046_dqsoscctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
   assign reg_ddrc_dqsosc_interval_freq0[(`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] = r2046_dqsoscctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ0_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEINT
   //------------------------
   assign reg_ddrc_mr4_read_interval_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] = r2047_derateint_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ0_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL0
   //------------------------
   assign reg_ddrc_derated_t_rrd_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] = r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
   assign reg_ddrc_derated_t_rp_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] = r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
   assign reg_ddrc_derated_t_ras_min_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] = r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
   assign reg_ddrc_derated_t_rcd_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] = r2048_derateval0_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ0_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL1
   //------------------------
   assign reg_ddrc_derated_t_rc_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] = r2049_derateval1_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
   assign reg_ddrc_derated_t_rcd_write_freq0[(`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] = r2049_derateval1_freq0[`REGB_FREQ0_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ0_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ0_CH0.HWLPTMG0
   //------------------------
   assign reg_ddrc_hw_lp_idle_x32_freq0[(`REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] = r2050_hwlptmg0_freq0[`REGB_FREQ0_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ0_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
   //------------------------
   // Register REGB_FREQ0_CH0.DVFSCTL0
   //------------------------
   assign reg_ddrc_dvfsq_enable_freq0 = r2051_dvfsctl0_freq0[`REGB_FREQ0_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ0_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
   //------------------------
   // Register REGB_FREQ0_CH0.SCHEDTMG0
   //------------------------
   assign reg_ddrc_pageclose_timer_freq0[(`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] = r2052_schedtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
   assign reg_ddrc_rdwr_idle_gap_freq0[(`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] = r2052_schedtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ0_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
   //------------------------
   // Register REGB_FREQ0_CH0.PERFHPR1
   //------------------------
   assign reg_ddrc_hpr_max_starve_freq0[(`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] = r2053_perfhpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
   assign reg_ddrc_hpr_xact_run_length_freq0[(`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] = r2053_perfhpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ0_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ0_CH0.PERFLPR1
   //------------------------
   assign reg_ddrc_lpr_max_starve_freq0[(`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] = r2054_perflpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
   assign reg_ddrc_lpr_xact_run_length_freq0[(`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] = r2054_perflpr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ0_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ0_CH0.PERFWR1
   //------------------------
   assign reg_ddrc_w_max_starve_freq0[(`REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] = r2055_perfwr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ0_CH0_SIZE_PERFWR1_W_MAX_STARVE];
   assign reg_ddrc_w_xact_run_length_freq0[(`REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] = r2055_perfwr1_freq0[`REGB_FREQ0_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ0_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ0_CH0.TMGCFG
   //------------------------
   assign reg_ddrc_frequency_ratio_freq0 = r2056_tmgcfg_freq0[`REGB_FREQ0_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ0_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG0
   //------------------------
   assign reg_ddrc_diff_rank_rd_gap_freq0[(`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] = r2057_ranktmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
   assign reg_ddrc_diff_rank_wr_gap_freq0[(`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] = r2057_ranktmg0_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG1
   //------------------------
   assign reg_ddrc_wr2rd_dr_freq0[(`REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] = r2058_ranktmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ0_CH0_SIZE_RANKTMG1_WR2RD_DR];
   assign reg_ddrc_rd2wr_dr_freq0[(`REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] = r2058_ranktmg1_freq0[`REGB_FREQ0_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ0_CH0_SIZE_RANKTMG1_RD2WR_DR];
   //------------------------
   // Register REGB_FREQ0_CH0.PWRTMG
   //------------------------
   assign reg_ddrc_powerdown_to_x32_freq0[(`REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] = r2059_pwrtmg_freq0[`REGB_FREQ0_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ0_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
   assign reg_ddrc_selfref_to_x32_freq0[(`REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] = r2059_pwrtmg_freq0[`REGB_FREQ0_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ0_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG0
   //------------------------
   assign reg_ddrc_t_pgm_x1_x1024_freq0[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] = r2065_ddr4pprtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
   assign reg_ddrc_t_pgm_x1_sel_freq0 = r2065_ddr4pprtmg0_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG1
   //------------------------
   assign reg_ddrc_t_pgmpst_x32_freq0[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] = r2066_ddr4pprtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
   assign reg_ddrc_t_pgm_exit_freq0[(`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] = r2066_ddr4pprtmg1_freq0[`REGB_FREQ0_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ0_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
   //------------------------
   // Register REGB_FREQ0_CH0.LNKECCCTL0
   //------------------------
   assign reg_ddrc_wr_link_ecc_enable_freq0 = r2067_lnkeccctl0_freq0[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ0_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
   assign reg_ddrc_rd_link_ecc_enable_freq0 = r2067_lnkeccctl0_freq0[`REGB_FREQ0_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ0_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG0
   //------------------------
   assign reg_ddrc_t_ras_min_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] = r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
   assign reg_ddrc_t_ras_max_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] = r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
   assign reg_ddrc_t_faw_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] = r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_T_FAW];
   assign reg_ddrc_wr2pre_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] = r2201_dramset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG1
   //------------------------
   assign reg_ddrc_t_rc_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] = r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RC];
   assign reg_ddrc_rd2pre_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] = r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
   assign reg_ddrc_t_xp_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] = r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_XP];
   assign reg_ddrc_t_rcd_write_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] = r2202_dramset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG2
   //------------------------
   assign reg_ddrc_wr2rd_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] = r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WR2RD];
   assign reg_ddrc_rd2wr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] = r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_RD2WR];
   assign reg_ddrc_read_latency_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] = r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
   assign reg_ddrc_write_latency_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] = r2203_dramset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG3
   //------------------------
   assign reg_ddrc_wr2mr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] = r2204_dramset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_WR2MR];
   assign reg_ddrc_rd2mr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] = r2204_dramset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_RD2MR];
   assign reg_ddrc_t_mr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] = r2204_dramset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG3_T_MR];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG4
   //------------------------
   assign reg_ddrc_t_rp_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] = r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RP];
   assign reg_ddrc_t_rrd_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] = r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RRD];
   assign reg_ddrc_t_ccd_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] = r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_CCD];
   assign reg_ddrc_t_rcd_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] = r2205_dramset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG4_T_RCD];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG5
   //------------------------
   assign reg_ddrc_t_cke_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] = r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKE];
   assign reg_ddrc_t_ckesr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] = r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
   assign reg_ddrc_t_cksre_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] = r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
   assign reg_ddrc_t_cksrx_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] = r2206_dramset1tmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG6
   //------------------------
   assign reg_ddrc_t_ckcsx_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] = r2207_dramset1tmg6_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG7
   //------------------------
   assign reg_ddrc_t_csh_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] = r2208_dramset1tmg7_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG7_T_CSH];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG9
   //------------------------
   assign reg_ddrc_wr2rd_s_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] = r2210_dramset1tmg9_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
   assign reg_ddrc_t_rrd_s_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] = r2210_dramset1tmg9_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
   assign reg_ddrc_t_ccd_s_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] = r2210_dramset1tmg9_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG12
   //------------------------
   assign reg_ddrc_t_cmdcke_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] = r2213_dramset1tmg12_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG13
   //------------------------
   assign reg_ddrc_t_ppd_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] = r2214_dramset1tmg13_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_PPD];
   assign reg_ddrc_t_ccd_mw_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] = r2214_dramset1tmg13_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
   assign reg_ddrc_odtloff_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] = r2214_dramset1tmg13_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG14
   //------------------------
   assign reg_ddrc_t_xsr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] = r2215_dramset1tmg14_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_XSR];
   assign reg_ddrc_t_osco_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] = r2215_dramset1tmg14_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG17
   //------------------------
   assign reg_ddrc_t_vrcg_disable_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] = r2218_dramset1tmg17_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
   assign reg_ddrc_t_vrcg_enable_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] = r2218_dramset1tmg17_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG23
   //------------------------
   assign reg_ddrc_t_pdn_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] = r2223_dramset1tmg23_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_PDN];
   assign reg_ddrc_t_xsr_dsm_x1024_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] = r2223_dramset1tmg23_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG24
   //------------------------
   assign reg_ddrc_max_wr_sync_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] = r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
   assign reg_ddrc_max_rd_sync_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] = r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
   assign reg_ddrc_rd2wr_s_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] = r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
   assign reg_ddrc_bank_org_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] = r2224_dramset1tmg24_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG25
   //------------------------
   assign reg_ddrc_rda2pre_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] = r2225_dramset1tmg25_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
   assign reg_ddrc_wra2pre_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] = r2225_dramset1tmg25_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
   assign reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] = r2225_dramset1tmg25_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG30
   //------------------------
   assign reg_ddrc_mrr2rd_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] = r2230_dramset1tmg30_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
   assign reg_ddrc_mrr2wr_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] = r2230_dramset1tmg30_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
   assign reg_ddrc_mrr2mrw_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] = r2230_dramset1tmg30_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG32
   //------------------------
   assign reg_ddrc_ws_fs2wck_sus_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] = r2232_dramset1tmg32_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
   assign reg_ddrc_t_wcksus_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] = r2232_dramset1tmg32_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
   assign reg_ddrc_ws_off2ws_fs_freq1[(`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] = r2232_dramset1tmg32_freq1[`REGB_FREQ1_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ1_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR0
   //------------------------
   assign reg_ddrc_emr_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR0_EMR) -1:0] = r2263_initmr0_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ1_CH0_SIZE_INITMR0_EMR];
   assign reg_ddrc_mr_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR0_MR) -1:0] = r2263_initmr0_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ1_CH0_SIZE_INITMR0_MR];
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR1
   //------------------------
   assign reg_ddrc_emr3_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR1_EMR3) -1:0] = r2264_initmr1_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ1_CH0_SIZE_INITMR1_EMR3];
   assign reg_ddrc_emr2_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR1_EMR2) -1:0] = r2264_initmr1_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ1_CH0_SIZE_INITMR1_EMR2];
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR2
   //------------------------
   assign reg_ddrc_mr5_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR2_MR5) -1:0] = r2265_initmr2_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ1_CH0_SIZE_INITMR2_MR5];
   assign reg_ddrc_mr4_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR2_MR4) -1:0] = r2265_initmr2_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ1_CH0_SIZE_INITMR2_MR4];
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR3
   //------------------------
   assign reg_ddrc_mr6_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR3_MR6) -1:0] = r2266_initmr3_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ1_CH0_SIZE_INITMR3_MR6];
   assign reg_ddrc_mr22_freq1[(`REGB_FREQ1_CH0_SIZE_INITMR3_MR22) -1:0] = r2266_initmr3_freq1[`REGB_FREQ1_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ1_CH0_SIZE_INITMR3_MR22];
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG0
   //------------------------
   assign reg_ddrc_dfi_tphy_wrlat_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] = r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
   assign reg_ddrc_dfi_tphy_wrdata_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] = r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
   assign reg_ddrc_dfi_t_rddata_en_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] = r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
   assign reg_ddrc_dfi_t_ctrl_delay_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] = r2267_dfitmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ1_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG1
   //------------------------
   assign reg_ddrc_dfi_t_dram_clk_enable_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] = r2268_dfitmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
   assign reg_ddrc_dfi_t_dram_clk_disable_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] = r2268_dfitmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
   assign reg_ddrc_dfi_t_wrdata_delay_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] = r2268_dfitmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ1_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG2
   //------------------------
   assign reg_ddrc_dfi_tphy_wrcslat_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] = r2269_dfitmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
   assign reg_ddrc_dfi_tphy_rdcslat_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] = r2269_dfitmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
   assign reg_ddrc_dfi_twck_delay_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] = r2269_dfitmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ1_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG4
   //------------------------
   assign reg_ddrc_dfi_twck_dis_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] = r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
   assign reg_ddrc_dfi_twck_en_fs_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] = r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
   assign reg_ddrc_dfi_twck_en_wr_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] = r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
   assign reg_ddrc_dfi_twck_en_rd_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] = r2271_dfitmg4_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ1_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG5
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] = r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
   assign reg_ddrc_dfi_twck_toggle_cs_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] = r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
   assign reg_ddrc_dfi_twck_toggle_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] = r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
   assign reg_ddrc_dfi_twck_fast_toggle_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] = r2272_dfitmg5_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ1_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG6
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_rd_freq1[(`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] = r2273_dfitmg6_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
   assign reg_ddrc_dfi_twck_toggle_post_rd_en_freq1 = r2273_dfitmg6_freq1[`REGB_FREQ1_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ1_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG1
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] = r2275_dfiupdtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
   assign reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] = r2275_dfiupdtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG2
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] = r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
   assign reg_ddrc_ctrlupd_after_dqsosc_freq1 = r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
   assign reg_ddrc_ppt2_override_freq1 = r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
   assign reg_ddrc_ppt2_en_freq1 = r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] = r2276_dfiupdtmg2_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG3
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1[(`REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] = r2277_dfiupdtmg3_freq1[`REGB_FREQ1_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ1_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG0
   //------------------------
   assign reg_ddrc_t_refi_x1_x32_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] = r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
   assign reg_ddrc_refresh_to_x1_x32_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] = r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
   assign reg_ddrc_refresh_margin_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] = r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
   assign reg_ddrc_refresh_to_x1_sel_freq1 = r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
   assign reg_ddrc_t_refi_x1_sel_freq1 = r2278_rfshset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG1
   //------------------------
   assign reg_ddrc_t_rfc_min_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] = r2279_rfshset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
   assign reg_ddrc_t_rfc_min_ab_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] = r2279_rfshset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG2
   //------------------------
   assign reg_ddrc_t_pbr2pbr_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] = r2280_rfshset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
   assign reg_ddrc_t_pbr2act_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] = r2280_rfshset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG3
   //------------------------
   assign reg_ddrc_refresh_to_ab_x32_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] = r2281_rfshset1tmg3_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG4
   //------------------------
   assign reg_ddrc_refresh_timer0_start_value_x32_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] = r2282_rfshset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
   assign reg_ddrc_refresh_timer1_start_value_x32_freq1[(`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] = r2282_rfshset1tmg4_freq1[`REGB_FREQ1_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ1_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
   //------------------------
   // Register REGB_FREQ1_CH0.RFMSET1TMG0
   //------------------------
   assign reg_ddrc_t_rfmpb_freq1[(`REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] = r2292_rfmset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ1_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG0
   //------------------------
   assign reg_ddrc_t_zq_long_nop_freq1[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] = r2303_zqset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
   assign reg_ddrc_t_zq_short_nop_freq1[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] = r2303_zqset1tmg0_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG1
   //------------------------
   assign reg_ddrc_t_zq_short_interval_x1024_freq1[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] = r2304_zqset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
   assign reg_ddrc_t_zq_reset_nop_freq1[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] = r2304_zqset1tmg1_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG2
   //------------------------
   assign reg_ddrc_t_zq_stop_freq1[(`REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] = r2305_zqset1tmg2_freq1[`REGB_FREQ1_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ1_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
   //------------------------
   // Register REGB_FREQ1_CH0.DQSOSCCTL0
   //------------------------
   assign reg_ddrc_dqsosc_enable_freq1 = r2314_dqsoscctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
   assign reg_ddrc_dqsosc_interval_unit_freq1 = r2314_dqsoscctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
   assign reg_ddrc_dqsosc_interval_freq1[(`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] = r2314_dqsoscctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ1_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEINT
   //------------------------
   assign reg_ddrc_mr4_read_interval_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] = r2315_derateint_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ1_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL0
   //------------------------
   assign reg_ddrc_derated_t_rrd_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] = r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
   assign reg_ddrc_derated_t_rp_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] = r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
   assign reg_ddrc_derated_t_ras_min_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] = r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
   assign reg_ddrc_derated_t_rcd_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] = r2316_derateval0_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ1_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL1
   //------------------------
   assign reg_ddrc_derated_t_rc_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] = r2317_derateval1_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
   assign reg_ddrc_derated_t_rcd_write_freq1[(`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] = r2317_derateval1_freq1[`REGB_FREQ1_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ1_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ1_CH0.HWLPTMG0
   //------------------------
   assign reg_ddrc_hw_lp_idle_x32_freq1[(`REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] = r2318_hwlptmg0_freq1[`REGB_FREQ1_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ1_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
   //------------------------
   // Register REGB_FREQ1_CH0.DVFSCTL0
   //------------------------
   assign reg_ddrc_dvfsq_enable_freq1 = r2319_dvfsctl0_freq1[`REGB_FREQ1_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ1_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
   //------------------------
   // Register REGB_FREQ1_CH0.SCHEDTMG0
   //------------------------
   assign reg_ddrc_pageclose_timer_freq1[(`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] = r2320_schedtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
   assign reg_ddrc_rdwr_idle_gap_freq1[(`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] = r2320_schedtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ1_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
   //------------------------
   // Register REGB_FREQ1_CH0.PERFHPR1
   //------------------------
   assign reg_ddrc_hpr_max_starve_freq1[(`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] = r2321_perfhpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
   assign reg_ddrc_hpr_xact_run_length_freq1[(`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] = r2321_perfhpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ1_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ1_CH0.PERFLPR1
   //------------------------
   assign reg_ddrc_lpr_max_starve_freq1[(`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] = r2322_perflpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
   assign reg_ddrc_lpr_xact_run_length_freq1[(`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] = r2322_perflpr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ1_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ1_CH0.PERFWR1
   //------------------------
   assign reg_ddrc_w_max_starve_freq1[(`REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] = r2323_perfwr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ1_CH0_SIZE_PERFWR1_W_MAX_STARVE];
   assign reg_ddrc_w_xact_run_length_freq1[(`REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] = r2323_perfwr1_freq1[`REGB_FREQ1_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ1_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ1_CH0.TMGCFG
   //------------------------
   assign reg_ddrc_frequency_ratio_freq1 = r2324_tmgcfg_freq1[`REGB_FREQ1_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ1_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG0
   //------------------------
   assign reg_ddrc_diff_rank_rd_gap_freq1[(`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] = r2325_ranktmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
   assign reg_ddrc_diff_rank_wr_gap_freq1[(`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] = r2325_ranktmg0_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ1_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG1
   //------------------------
   assign reg_ddrc_wr2rd_dr_freq1[(`REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] = r2326_ranktmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ1_CH0_SIZE_RANKTMG1_WR2RD_DR];
   assign reg_ddrc_rd2wr_dr_freq1[(`REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] = r2326_ranktmg1_freq1[`REGB_FREQ1_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ1_CH0_SIZE_RANKTMG1_RD2WR_DR];
   //------------------------
   // Register REGB_FREQ1_CH0.PWRTMG
   //------------------------
   assign reg_ddrc_powerdown_to_x32_freq1[(`REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] = r2327_pwrtmg_freq1[`REGB_FREQ1_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ1_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
   assign reg_ddrc_selfref_to_x32_freq1[(`REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] = r2327_pwrtmg_freq1[`REGB_FREQ1_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ1_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG0
   //------------------------
   assign reg_ddrc_t_pgm_x1_x1024_freq1[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] = r2333_ddr4pprtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
   assign reg_ddrc_t_pgm_x1_sel_freq1 = r2333_ddr4pprtmg0_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG1
   //------------------------
   assign reg_ddrc_t_pgmpst_x32_freq1[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] = r2334_ddr4pprtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
   assign reg_ddrc_t_pgm_exit_freq1[(`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] = r2334_ddr4pprtmg1_freq1[`REGB_FREQ1_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ1_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
   //------------------------
   // Register REGB_FREQ1_CH0.LNKECCCTL0
   //------------------------
   assign reg_ddrc_wr_link_ecc_enable_freq1 = r2335_lnkeccctl0_freq1[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ1_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
   assign reg_ddrc_rd_link_ecc_enable_freq1 = r2335_lnkeccctl0_freq1[`REGB_FREQ1_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ1_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG0
   //------------------------
   assign reg_ddrc_t_ras_min_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] = r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
   assign reg_ddrc_t_ras_max_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] = r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
   assign reg_ddrc_t_faw_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] = r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_T_FAW];
   assign reg_ddrc_wr2pre_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] = r2469_dramset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG1
   //------------------------
   assign reg_ddrc_t_rc_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] = r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RC];
   assign reg_ddrc_rd2pre_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] = r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
   assign reg_ddrc_t_xp_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] = r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_XP];
   assign reg_ddrc_t_rcd_write_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] = r2470_dramset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG2
   //------------------------
   assign reg_ddrc_wr2rd_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] = r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WR2RD];
   assign reg_ddrc_rd2wr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] = r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_RD2WR];
   assign reg_ddrc_read_latency_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] = r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
   assign reg_ddrc_write_latency_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] = r2471_dramset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG3
   //------------------------
   assign reg_ddrc_wr2mr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] = r2472_dramset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_WR2MR];
   assign reg_ddrc_rd2mr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] = r2472_dramset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_RD2MR];
   assign reg_ddrc_t_mr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] = r2472_dramset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG3_T_MR];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG4
   //------------------------
   assign reg_ddrc_t_rp_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] = r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RP];
   assign reg_ddrc_t_rrd_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] = r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RRD];
   assign reg_ddrc_t_ccd_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] = r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_CCD];
   assign reg_ddrc_t_rcd_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] = r2473_dramset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG4_T_RCD];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG5
   //------------------------
   assign reg_ddrc_t_cke_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] = r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKE];
   assign reg_ddrc_t_ckesr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] = r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
   assign reg_ddrc_t_cksre_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] = r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
   assign reg_ddrc_t_cksrx_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] = r2474_dramset1tmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG6
   //------------------------
   assign reg_ddrc_t_ckcsx_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] = r2475_dramset1tmg6_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG7
   //------------------------
   assign reg_ddrc_t_csh_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] = r2476_dramset1tmg7_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG7_T_CSH];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG9
   //------------------------
   assign reg_ddrc_wr2rd_s_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] = r2478_dramset1tmg9_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
   assign reg_ddrc_t_rrd_s_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] = r2478_dramset1tmg9_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
   assign reg_ddrc_t_ccd_s_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] = r2478_dramset1tmg9_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG12
   //------------------------
   assign reg_ddrc_t_cmdcke_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] = r2481_dramset1tmg12_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG13
   //------------------------
   assign reg_ddrc_t_ppd_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] = r2482_dramset1tmg13_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_PPD];
   assign reg_ddrc_t_ccd_mw_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] = r2482_dramset1tmg13_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
   assign reg_ddrc_odtloff_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] = r2482_dramset1tmg13_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG14
   //------------------------
   assign reg_ddrc_t_xsr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] = r2483_dramset1tmg14_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_XSR];
   assign reg_ddrc_t_osco_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] = r2483_dramset1tmg14_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG17
   //------------------------
   assign reg_ddrc_t_vrcg_disable_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] = r2486_dramset1tmg17_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
   assign reg_ddrc_t_vrcg_enable_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] = r2486_dramset1tmg17_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG23
   //------------------------
   assign reg_ddrc_t_pdn_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] = r2491_dramset1tmg23_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_PDN];
   assign reg_ddrc_t_xsr_dsm_x1024_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] = r2491_dramset1tmg23_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG24
   //------------------------
   assign reg_ddrc_max_wr_sync_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] = r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
   assign reg_ddrc_max_rd_sync_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] = r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
   assign reg_ddrc_rd2wr_s_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] = r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
   assign reg_ddrc_bank_org_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] = r2492_dramset1tmg24_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG25
   //------------------------
   assign reg_ddrc_rda2pre_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] = r2493_dramset1tmg25_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
   assign reg_ddrc_wra2pre_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] = r2493_dramset1tmg25_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
   assign reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] = r2493_dramset1tmg25_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG30
   //------------------------
   assign reg_ddrc_mrr2rd_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] = r2498_dramset1tmg30_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
   assign reg_ddrc_mrr2wr_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] = r2498_dramset1tmg30_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
   assign reg_ddrc_mrr2mrw_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] = r2498_dramset1tmg30_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG32
   //------------------------
   assign reg_ddrc_ws_fs2wck_sus_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] = r2500_dramset1tmg32_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
   assign reg_ddrc_t_wcksus_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] = r2500_dramset1tmg32_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
   assign reg_ddrc_ws_off2ws_fs_freq2[(`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] = r2500_dramset1tmg32_freq2[`REGB_FREQ2_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ2_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR0
   //------------------------
   assign reg_ddrc_emr_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR0_EMR) -1:0] = r2531_initmr0_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ2_CH0_SIZE_INITMR0_EMR];
   assign reg_ddrc_mr_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR0_MR) -1:0] = r2531_initmr0_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ2_CH0_SIZE_INITMR0_MR];
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR1
   //------------------------
   assign reg_ddrc_emr3_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR1_EMR3) -1:0] = r2532_initmr1_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ2_CH0_SIZE_INITMR1_EMR3];
   assign reg_ddrc_emr2_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR1_EMR2) -1:0] = r2532_initmr1_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ2_CH0_SIZE_INITMR1_EMR2];
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR2
   //------------------------
   assign reg_ddrc_mr5_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR2_MR5) -1:0] = r2533_initmr2_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ2_CH0_SIZE_INITMR2_MR5];
   assign reg_ddrc_mr4_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR2_MR4) -1:0] = r2533_initmr2_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ2_CH0_SIZE_INITMR2_MR4];
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR3
   //------------------------
   assign reg_ddrc_mr6_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR3_MR6) -1:0] = r2534_initmr3_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ2_CH0_SIZE_INITMR3_MR6];
   assign reg_ddrc_mr22_freq2[(`REGB_FREQ2_CH0_SIZE_INITMR3_MR22) -1:0] = r2534_initmr3_freq2[`REGB_FREQ2_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ2_CH0_SIZE_INITMR3_MR22];
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG0
   //------------------------
   assign reg_ddrc_dfi_tphy_wrlat_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] = r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
   assign reg_ddrc_dfi_tphy_wrdata_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] = r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
   assign reg_ddrc_dfi_t_rddata_en_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] = r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
   assign reg_ddrc_dfi_t_ctrl_delay_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] = r2535_dfitmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ2_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG1
   //------------------------
   assign reg_ddrc_dfi_t_dram_clk_enable_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] = r2536_dfitmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
   assign reg_ddrc_dfi_t_dram_clk_disable_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] = r2536_dfitmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
   assign reg_ddrc_dfi_t_wrdata_delay_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] = r2536_dfitmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ2_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG2
   //------------------------
   assign reg_ddrc_dfi_tphy_wrcslat_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] = r2537_dfitmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
   assign reg_ddrc_dfi_tphy_rdcslat_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] = r2537_dfitmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
   assign reg_ddrc_dfi_twck_delay_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] = r2537_dfitmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ2_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG4
   //------------------------
   assign reg_ddrc_dfi_twck_dis_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] = r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
   assign reg_ddrc_dfi_twck_en_fs_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] = r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
   assign reg_ddrc_dfi_twck_en_wr_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] = r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
   assign reg_ddrc_dfi_twck_en_rd_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] = r2539_dfitmg4_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ2_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG5
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] = r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
   assign reg_ddrc_dfi_twck_toggle_cs_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] = r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
   assign reg_ddrc_dfi_twck_toggle_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] = r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
   assign reg_ddrc_dfi_twck_fast_toggle_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] = r2540_dfitmg5_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ2_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG6
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_rd_freq2[(`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] = r2541_dfitmg6_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
   assign reg_ddrc_dfi_twck_toggle_post_rd_en_freq2 = r2541_dfitmg6_freq2[`REGB_FREQ2_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ2_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG1
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] = r2543_dfiupdtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
   assign reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] = r2543_dfiupdtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG2
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] = r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
   assign reg_ddrc_ctrlupd_after_dqsosc_freq2 = r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
   assign reg_ddrc_ppt2_override_freq2 = r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
   assign reg_ddrc_ppt2_en_freq2 = r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] = r2544_dfiupdtmg2_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG3
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2[(`REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] = r2545_dfiupdtmg3_freq2[`REGB_FREQ2_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ2_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG0
   //------------------------
   assign reg_ddrc_t_refi_x1_x32_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] = r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
   assign reg_ddrc_refresh_to_x1_x32_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] = r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
   assign reg_ddrc_refresh_margin_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] = r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
   assign reg_ddrc_refresh_to_x1_sel_freq2 = r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
   assign reg_ddrc_t_refi_x1_sel_freq2 = r2546_rfshset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG1
   //------------------------
   assign reg_ddrc_t_rfc_min_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] = r2547_rfshset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
   assign reg_ddrc_t_rfc_min_ab_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] = r2547_rfshset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG2
   //------------------------
   assign reg_ddrc_t_pbr2pbr_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] = r2548_rfshset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
   assign reg_ddrc_t_pbr2act_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] = r2548_rfshset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG3
   //------------------------
   assign reg_ddrc_refresh_to_ab_x32_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] = r2549_rfshset1tmg3_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG4
   //------------------------
   assign reg_ddrc_refresh_timer0_start_value_x32_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] = r2550_rfshset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
   assign reg_ddrc_refresh_timer1_start_value_x32_freq2[(`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] = r2550_rfshset1tmg4_freq2[`REGB_FREQ2_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ2_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
   //------------------------
   // Register REGB_FREQ2_CH0.RFMSET1TMG0
   //------------------------
   assign reg_ddrc_t_rfmpb_freq2[(`REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] = r2560_rfmset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ2_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG0
   //------------------------
   assign reg_ddrc_t_zq_long_nop_freq2[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] = r2571_zqset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
   assign reg_ddrc_t_zq_short_nop_freq2[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] = r2571_zqset1tmg0_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG1
   //------------------------
   assign reg_ddrc_t_zq_short_interval_x1024_freq2[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] = r2572_zqset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
   assign reg_ddrc_t_zq_reset_nop_freq2[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] = r2572_zqset1tmg1_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG2
   //------------------------
   assign reg_ddrc_t_zq_stop_freq2[(`REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] = r2573_zqset1tmg2_freq2[`REGB_FREQ2_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ2_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
   //------------------------
   // Register REGB_FREQ2_CH0.DQSOSCCTL0
   //------------------------
   assign reg_ddrc_dqsosc_enable_freq2 = r2582_dqsoscctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
   assign reg_ddrc_dqsosc_interval_unit_freq2 = r2582_dqsoscctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
   assign reg_ddrc_dqsosc_interval_freq2[(`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] = r2582_dqsoscctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ2_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEINT
   //------------------------
   assign reg_ddrc_mr4_read_interval_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] = r2583_derateint_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ2_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL0
   //------------------------
   assign reg_ddrc_derated_t_rrd_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] = r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
   assign reg_ddrc_derated_t_rp_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] = r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
   assign reg_ddrc_derated_t_ras_min_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] = r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
   assign reg_ddrc_derated_t_rcd_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] = r2584_derateval0_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ2_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL1
   //------------------------
   assign reg_ddrc_derated_t_rc_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] = r2585_derateval1_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
   assign reg_ddrc_derated_t_rcd_write_freq2[(`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] = r2585_derateval1_freq2[`REGB_FREQ2_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ2_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ2_CH0.HWLPTMG0
   //------------------------
   assign reg_ddrc_hw_lp_idle_x32_freq2[(`REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] = r2586_hwlptmg0_freq2[`REGB_FREQ2_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ2_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
   //------------------------
   // Register REGB_FREQ2_CH0.DVFSCTL0
   //------------------------
   assign reg_ddrc_dvfsq_enable_freq2 = r2587_dvfsctl0_freq2[`REGB_FREQ2_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ2_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
   //------------------------
   // Register REGB_FREQ2_CH0.SCHEDTMG0
   //------------------------
   assign reg_ddrc_pageclose_timer_freq2[(`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] = r2588_schedtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
   assign reg_ddrc_rdwr_idle_gap_freq2[(`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] = r2588_schedtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ2_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
   //------------------------
   // Register REGB_FREQ2_CH0.PERFHPR1
   //------------------------
   assign reg_ddrc_hpr_max_starve_freq2[(`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] = r2589_perfhpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
   assign reg_ddrc_hpr_xact_run_length_freq2[(`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] = r2589_perfhpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ2_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ2_CH0.PERFLPR1
   //------------------------
   assign reg_ddrc_lpr_max_starve_freq2[(`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] = r2590_perflpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
   assign reg_ddrc_lpr_xact_run_length_freq2[(`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] = r2590_perflpr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ2_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ2_CH0.PERFWR1
   //------------------------
   assign reg_ddrc_w_max_starve_freq2[(`REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] = r2591_perfwr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ2_CH0_SIZE_PERFWR1_W_MAX_STARVE];
   assign reg_ddrc_w_xact_run_length_freq2[(`REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] = r2591_perfwr1_freq2[`REGB_FREQ2_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ2_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ2_CH0.TMGCFG
   //------------------------
   assign reg_ddrc_frequency_ratio_freq2 = r2592_tmgcfg_freq2[`REGB_FREQ2_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ2_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG0
   //------------------------
   assign reg_ddrc_diff_rank_rd_gap_freq2[(`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] = r2593_ranktmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
   assign reg_ddrc_diff_rank_wr_gap_freq2[(`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] = r2593_ranktmg0_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ2_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG1
   //------------------------
   assign reg_ddrc_wr2rd_dr_freq2[(`REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] = r2594_ranktmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ2_CH0_SIZE_RANKTMG1_WR2RD_DR];
   assign reg_ddrc_rd2wr_dr_freq2[(`REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] = r2594_ranktmg1_freq2[`REGB_FREQ2_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ2_CH0_SIZE_RANKTMG1_RD2WR_DR];
   //------------------------
   // Register REGB_FREQ2_CH0.PWRTMG
   //------------------------
   assign reg_ddrc_powerdown_to_x32_freq2[(`REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] = r2595_pwrtmg_freq2[`REGB_FREQ2_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ2_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
   assign reg_ddrc_selfref_to_x32_freq2[(`REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] = r2595_pwrtmg_freq2[`REGB_FREQ2_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ2_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG0
   //------------------------
   assign reg_ddrc_t_pgm_x1_x1024_freq2[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] = r2601_ddr4pprtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
   assign reg_ddrc_t_pgm_x1_sel_freq2 = r2601_ddr4pprtmg0_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG1
   //------------------------
   assign reg_ddrc_t_pgmpst_x32_freq2[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] = r2602_ddr4pprtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
   assign reg_ddrc_t_pgm_exit_freq2[(`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] = r2602_ddr4pprtmg1_freq2[`REGB_FREQ2_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ2_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
   //------------------------
   // Register REGB_FREQ2_CH0.LNKECCCTL0
   //------------------------
   assign reg_ddrc_wr_link_ecc_enable_freq2 = r2603_lnkeccctl0_freq2[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ2_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
   assign reg_ddrc_rd_link_ecc_enable_freq2 = r2603_lnkeccctl0_freq2[`REGB_FREQ2_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ2_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG0
   //------------------------
   assign reg_ddrc_t_ras_min_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN) -1:0] = r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MIN+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MIN];
   assign reg_ddrc_t_ras_max_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX) -1:0] = r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_RAS_MAX+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_RAS_MAX];
   assign reg_ddrc_t_faw_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW) -1:0] = r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_T_FAW+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_T_FAW];
   assign reg_ddrc_wr2pre_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE) -1:0] = r2737_dramset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG0_WR2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG0_WR2PRE];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG1
   //------------------------
   assign reg_ddrc_t_rc_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC) -1:0] = r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RC+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RC];
   assign reg_ddrc_rd2pre_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE) -1:0] = r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_RD2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_RD2PRE];
   assign reg_ddrc_t_xp_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP) -1:0] = r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_XP+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_XP];
   assign reg_ddrc_t_rcd_write_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE) -1:0] = r2738_dramset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG1_T_RCD_WRITE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG1_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG2
   //------------------------
   assign reg_ddrc_wr2rd_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD) -1:0] = r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WR2RD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WR2RD];
   assign reg_ddrc_rd2wr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR) -1:0] = r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_RD2WR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_RD2WR];
   assign reg_ddrc_read_latency_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY) -1:0] = r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_READ_LATENCY+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_READ_LATENCY];
   assign reg_ddrc_write_latency_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY) -1:0] = r2739_dramset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG2_WRITE_LATENCY+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG2_WRITE_LATENCY];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG3
   //------------------------
   assign reg_ddrc_wr2mr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR) -1:0] = r2740_dramset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_WR2MR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_WR2MR];
   assign reg_ddrc_rd2mr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR) -1:0] = r2740_dramset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_RD2MR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_RD2MR];
   assign reg_ddrc_t_mr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR) -1:0] = r2740_dramset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG3_T_MR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG3_T_MR];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG4
   //------------------------
   assign reg_ddrc_t_rp_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP) -1:0] = r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RP+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RP];
   assign reg_ddrc_t_rrd_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD) -1:0] = r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RRD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RRD];
   assign reg_ddrc_t_ccd_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD) -1:0] = r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_CCD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_CCD];
   assign reg_ddrc_t_rcd_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD) -1:0] = r2741_dramset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG4_T_RCD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG4_T_RCD];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG5
   //------------------------
   assign reg_ddrc_t_cke_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE) -1:0] = r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKE];
   assign reg_ddrc_t_ckesr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR) -1:0] = r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKESR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKESR];
   assign reg_ddrc_t_cksre_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE) -1:0] = r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRE];
   assign reg_ddrc_t_cksrx_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX) -1:0] = r2742_dramset1tmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG5_T_CKSRX+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG5_T_CKSRX];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG6
   //------------------------
   assign reg_ddrc_t_ckcsx_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX) -1:0] = r2743_dramset1tmg6_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG6_T_CKCSX+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG6_T_CKCSX];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG7
   //------------------------
   assign reg_ddrc_t_csh_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH) -1:0] = r2744_dramset1tmg7_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG7_T_CSH+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG7_T_CSH];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG9
   //------------------------
   assign reg_ddrc_wr2rd_s_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S) -1:0] = r2746_dramset1tmg9_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_WR2RD_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_WR2RD_S];
   assign reg_ddrc_t_rrd_s_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S) -1:0] = r2746_dramset1tmg9_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_RRD_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_RRD_S];
   assign reg_ddrc_t_ccd_s_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S) -1:0] = r2746_dramset1tmg9_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG9_T_CCD_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG9_T_CCD_S];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG12
   //------------------------
   assign reg_ddrc_t_cmdcke_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE) -1:0] = r2749_dramset1tmg12_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG12_T_CMDCKE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG12_T_CMDCKE];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG13
   //------------------------
   assign reg_ddrc_t_ppd_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD) -1:0] = r2750_dramset1tmg13_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_PPD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_PPD];
   assign reg_ddrc_t_ccd_mw_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW) -1:0] = r2750_dramset1tmg13_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_T_CCD_MW+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_T_CCD_MW];
   assign reg_ddrc_odtloff_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF) -1:0] = r2750_dramset1tmg13_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG13_ODTLOFF+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG13_ODTLOFF];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG14
   //------------------------
   assign reg_ddrc_t_xsr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR) -1:0] = r2751_dramset1tmg14_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_XSR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_XSR];
   assign reg_ddrc_t_osco_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO) -1:0] = r2751_dramset1tmg14_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG14_T_OSCO+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG14_T_OSCO];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG17
   //------------------------
   assign reg_ddrc_t_vrcg_disable_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE) -1:0] = r2754_dramset1tmg17_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_DISABLE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_DISABLE];
   assign reg_ddrc_t_vrcg_enable_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE) -1:0] = r2754_dramset1tmg17_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG17_T_VRCG_ENABLE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG17_T_VRCG_ENABLE];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG23
   //------------------------
   assign reg_ddrc_t_pdn_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN) -1:0] = r2759_dramset1tmg23_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_PDN+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_PDN];
   assign reg_ddrc_t_xsr_dsm_x1024_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024) -1:0] = r2759_dramset1tmg23_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG23_T_XSR_DSM_X1024+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG23_T_XSR_DSM_X1024];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG24
   //------------------------
   assign reg_ddrc_max_wr_sync_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC) -1:0] = r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_WR_SYNC+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_WR_SYNC];
   assign reg_ddrc_max_rd_sync_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC) -1:0] = r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_MAX_RD_SYNC+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_MAX_RD_SYNC];
   assign reg_ddrc_rd2wr_s_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S) -1:0] = r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_RD2WR_S+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_RD2WR_S];
   assign reg_ddrc_bank_org_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG) -1:0] = r2760_dramset1tmg24_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG24_BANK_ORG+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG24_BANK_ORG];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG25
   //------------------------
   assign reg_ddrc_rda2pre_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE) -1:0] = r2761_dramset1tmg25_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_RDA2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_RDA2PRE];
   assign reg_ddrc_wra2pre_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE) -1:0] = r2761_dramset1tmg25_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_WRA2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_WRA2PRE];
   assign reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE) -1:0] = r2761_dramset1tmg25_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG25_LPDDR4_DIFF_BANK_RWA2PRE];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG30
   //------------------------
   assign reg_ddrc_mrr2rd_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD) -1:0] = r2766_dramset1tmg30_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2RD+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2RD];
   assign reg_ddrc_mrr2wr_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR) -1:0] = r2766_dramset1tmg30_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2WR+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2WR];
   assign reg_ddrc_mrr2mrw_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW) -1:0] = r2766_dramset1tmg30_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG30_MRR2MRW+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG30_MRR2MRW];
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG32
   //------------------------
   assign reg_ddrc_ws_fs2wck_sus_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS) -1:0] = r2768_dramset1tmg32_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_FS2WCK_SUS+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_FS2WCK_SUS];
   assign reg_ddrc_t_wcksus_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS) -1:0] = r2768_dramset1tmg32_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_T_WCKSUS+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_T_WCKSUS];
   assign reg_ddrc_ws_off2ws_fs_freq3[(`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS) -1:0] = r2768_dramset1tmg32_freq3[`REGB_FREQ3_CH0_OFFSET_DRAMSET1TMG32_WS_OFF2WS_FS+:`REGB_FREQ3_CH0_SIZE_DRAMSET1TMG32_WS_OFF2WS_FS];
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR0
   //------------------------
   assign reg_ddrc_emr_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR0_EMR) -1:0] = r2799_initmr0_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR0_EMR+:`REGB_FREQ3_CH0_SIZE_INITMR0_EMR];
   assign reg_ddrc_mr_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR0_MR) -1:0] = r2799_initmr0_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR0_MR+:`REGB_FREQ3_CH0_SIZE_INITMR0_MR];
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR1
   //------------------------
   assign reg_ddrc_emr3_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR1_EMR3) -1:0] = r2800_initmr1_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR3+:`REGB_FREQ3_CH0_SIZE_INITMR1_EMR3];
   assign reg_ddrc_emr2_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR1_EMR2) -1:0] = r2800_initmr1_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR1_EMR2+:`REGB_FREQ3_CH0_SIZE_INITMR1_EMR2];
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR2
   //------------------------
   assign reg_ddrc_mr5_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR2_MR5) -1:0] = r2801_initmr2_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR5+:`REGB_FREQ3_CH0_SIZE_INITMR2_MR5];
   assign reg_ddrc_mr4_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR2_MR4) -1:0] = r2801_initmr2_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR2_MR4+:`REGB_FREQ3_CH0_SIZE_INITMR2_MR4];
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR3
   //------------------------
   assign reg_ddrc_mr6_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR3_MR6) -1:0] = r2802_initmr3_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR6+:`REGB_FREQ3_CH0_SIZE_INITMR3_MR6];
   assign reg_ddrc_mr22_freq3[(`REGB_FREQ3_CH0_SIZE_INITMR3_MR22) -1:0] = r2802_initmr3_freq3[`REGB_FREQ3_CH0_OFFSET_INITMR3_MR22+:`REGB_FREQ3_CH0_SIZE_INITMR3_MR22];
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG0
   //------------------------
   assign reg_ddrc_dfi_tphy_wrlat_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT) -1:0] = r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRLAT+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRLAT];
   assign reg_ddrc_dfi_tphy_wrdata_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA) -1:0] = r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_TPHY_WRDATA+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_TPHY_WRDATA];
   assign reg_ddrc_dfi_t_rddata_en_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN) -1:0] = r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_RDDATA_EN+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_RDDATA_EN];
   assign reg_ddrc_dfi_t_ctrl_delay_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY) -1:0] = r2803_dfitmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG0_DFI_T_CTRL_DELAY+:`REGB_FREQ3_CH0_SIZE_DFITMG0_DFI_T_CTRL_DELAY];
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG1
   //------------------------
   assign reg_ddrc_dfi_t_dram_clk_enable_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE) -1:0] = r2804_dfitmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_ENABLE+:`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_ENABLE];
   assign reg_ddrc_dfi_t_dram_clk_disable_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE) -1:0] = r2804_dfitmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_DRAM_CLK_DISABLE+:`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_DRAM_CLK_DISABLE];
   assign reg_ddrc_dfi_t_wrdata_delay_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY) -1:0] = r2804_dfitmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG1_DFI_T_WRDATA_DELAY+:`REGB_FREQ3_CH0_SIZE_DFITMG1_DFI_T_WRDATA_DELAY];
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG2
   //------------------------
   assign reg_ddrc_dfi_tphy_wrcslat_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT) -1:0] = r2805_dfitmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_WRCSLAT+:`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_WRCSLAT];
   assign reg_ddrc_dfi_tphy_rdcslat_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT) -1:0] = r2805_dfitmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TPHY_RDCSLAT+:`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TPHY_RDCSLAT];
   assign reg_ddrc_dfi_twck_delay_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY) -1:0] = r2805_dfitmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG2_DFI_TWCK_DELAY+:`REGB_FREQ3_CH0_SIZE_DFITMG2_DFI_TWCK_DELAY];
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG4
   //------------------------
   assign reg_ddrc_dfi_twck_dis_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS) -1:0] = r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_DIS+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_DIS];
   assign reg_ddrc_dfi_twck_en_fs_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS) -1:0] = r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_FS+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_FS];
   assign reg_ddrc_dfi_twck_en_wr_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR) -1:0] = r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_WR+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_WR];
   assign reg_ddrc_dfi_twck_en_rd_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD) -1:0] = r2807_dfitmg4_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG4_DFI_TWCK_EN_RD+:`REGB_FREQ3_CH0_SIZE_DFITMG4_DFI_TWCK_EN_RD];
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG5
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST) -1:0] = r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_POST+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_POST];
   assign reg_ddrc_dfi_twck_toggle_cs_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS) -1:0] = r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE_CS+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE_CS];
   assign reg_ddrc_dfi_twck_toggle_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE) -1:0] = r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_TOGGLE+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_TOGGLE];
   assign reg_ddrc_dfi_twck_fast_toggle_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE) -1:0] = r2808_dfitmg5_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG5_DFI_TWCK_FAST_TOGGLE+:`REGB_FREQ3_CH0_SIZE_DFITMG5_DFI_TWCK_FAST_TOGGLE];
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG6
   //------------------------
   assign reg_ddrc_dfi_twck_toggle_post_rd_freq3[(`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD) -1:0] = r2809_dfitmg6_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD+:`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD];
   assign reg_ddrc_dfi_twck_toggle_post_rd_en_freq3 = r2809_dfitmg6_freq3[`REGB_FREQ3_CH0_OFFSET_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN+:`REGB_FREQ3_CH0_SIZE_DFITMG6_DFI_TWCK_TOGGLE_POST_RD_EN];
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG1
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024) -1:0] = r2811_dfiupdtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MAX_X1024];
   assign reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024) -1:0] = r2811_dfiupdtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG1_DFI_T_CTRLUPD_INTERVAL_MIN_X1024];
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG2
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1) -1:0] = r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1];
   assign reg_ddrc_ctrlupd_after_dqsosc_freq3 = r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_CTRLUPD_AFTER_DQSOSC];
   assign reg_ddrc_ppt2_override_freq3 = r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_OVERRIDE+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_OVERRIDE];
   assign reg_ddrc_ppt2_en_freq3 = r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_PPT2_EN+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_PPT2_EN];
   assign reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT) -1:0] = r2812_dfiupdtmg2_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG2_DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT];
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG3
   //------------------------
   assign reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3[(`REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8) -1:0] = r2813_dfiupdtmg3_freq3[`REGB_FREQ3_CH0_OFFSET_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8+:`REGB_FREQ3_CH0_SIZE_DFIUPDTMG3_DFI_T_CTRLUPD_BURST_INTERVAL_X8];
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG0
   //------------------------
   assign reg_ddrc_t_refi_x1_x32_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32) -1:0] = r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_X32];
   assign reg_ddrc_refresh_to_x1_x32_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32) -1:0] = r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_X32];
   assign reg_ddrc_refresh_margin_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN) -1:0] = r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_MARGIN+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_MARGIN];
   assign reg_ddrc_refresh_to_x1_sel_freq3 = r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_REFRESH_TO_X1_SEL+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_REFRESH_TO_X1_SEL];
   assign reg_ddrc_t_refi_x1_sel_freq3 = r2814_rfshset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG0_T_REFI_X1_SEL+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG0_T_REFI_X1_SEL];
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG1
   //------------------------
   assign reg_ddrc_t_rfc_min_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN) -1:0] = r2815_rfshset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN];
   assign reg_ddrc_t_rfc_min_ab_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB) -1:0] = r2815_rfshset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG1_T_RFC_MIN_AB+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG1_T_RFC_MIN_AB];
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG2
   //------------------------
   assign reg_ddrc_t_pbr2pbr_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR) -1:0] = r2816_rfshset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2PBR+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2PBR];
   assign reg_ddrc_t_pbr2act_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT) -1:0] = r2816_rfshset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG2_T_PBR2ACT+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG2_T_PBR2ACT];
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG3
   //------------------------
   assign reg_ddrc_refresh_to_ab_x32_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32) -1:0] = r2817_rfshset1tmg3_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG3_REFRESH_TO_AB_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG3_REFRESH_TO_AB_X32];
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG4
   //------------------------
   assign reg_ddrc_refresh_timer0_start_value_x32_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32) -1:0] = r2818_rfshset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER0_START_VALUE_X32];
   assign reg_ddrc_refresh_timer1_start_value_x32_freq3[(`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32) -1:0] = r2818_rfshset1tmg4_freq3[`REGB_FREQ3_CH0_OFFSET_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32+:`REGB_FREQ3_CH0_SIZE_RFSHSET1TMG4_REFRESH_TIMER1_START_VALUE_X32];
   //------------------------
   // Register REGB_FREQ3_CH0.RFMSET1TMG0
   //------------------------
   assign reg_ddrc_t_rfmpb_freq3[(`REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB) -1:0] = r2828_rfmset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RFMSET1TMG0_T_RFMPB+:`REGB_FREQ3_CH0_SIZE_RFMSET1TMG0_T_RFMPB];
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG0
   //------------------------
   assign reg_ddrc_t_zq_long_nop_freq3[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP) -1:0] = r2839_zqset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_LONG_NOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_LONG_NOP];
   assign reg_ddrc_t_zq_short_nop_freq3[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP) -1:0] = r2839_zqset1tmg0_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG0_T_ZQ_SHORT_NOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG0_T_ZQ_SHORT_NOP];
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG1
   //------------------------
   assign reg_ddrc_t_zq_short_interval_x1024_freq3[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024) -1:0] = r2840_zqset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_SHORT_INTERVAL_X1024];
   assign reg_ddrc_t_zq_reset_nop_freq3[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP) -1:0] = r2840_zqset1tmg1_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG1_T_ZQ_RESET_NOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG1_T_ZQ_RESET_NOP];
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG2
   //------------------------
   assign reg_ddrc_t_zq_stop_freq3[(`REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP) -1:0] = r2841_zqset1tmg2_freq3[`REGB_FREQ3_CH0_OFFSET_ZQSET1TMG2_T_ZQ_STOP+:`REGB_FREQ3_CH0_SIZE_ZQSET1TMG2_T_ZQ_STOP];
   //------------------------
   // Register REGB_FREQ3_CH0.DQSOSCCTL0
   //------------------------
   assign reg_ddrc_dqsosc_enable_freq3 = r2850_dqsoscctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_ENABLE+:`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_ENABLE];
   assign reg_ddrc_dqsosc_interval_unit_freq3 = r2850_dqsoscctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT+:`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL_UNIT];
   assign reg_ddrc_dqsosc_interval_freq3[(`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL) -1:0] = r2850_dqsoscctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DQSOSCCTL0_DQSOSC_INTERVAL+:`REGB_FREQ3_CH0_SIZE_DQSOSCCTL0_DQSOSC_INTERVAL];
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEINT
   //------------------------
   assign reg_ddrc_mr4_read_interval_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL) -1:0] = r2851_derateint_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEINT_MR4_READ_INTERVAL+:`REGB_FREQ3_CH0_SIZE_DERATEINT_MR4_READ_INTERVAL];
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL0
   //------------------------
   assign reg_ddrc_derated_t_rrd_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD) -1:0] = r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RRD+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RRD];
   assign reg_ddrc_derated_t_rp_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP) -1:0] = r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RP+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RP];
   assign reg_ddrc_derated_t_ras_min_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN) -1:0] = r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RAS_MIN+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RAS_MIN];
   assign reg_ddrc_derated_t_rcd_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD) -1:0] = r2852_derateval0_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL0_DERATED_T_RCD+:`REGB_FREQ3_CH0_SIZE_DERATEVAL0_DERATED_T_RCD];
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL1
   //------------------------
   assign reg_ddrc_derated_t_rc_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC) -1:0] = r2853_derateval1_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RC+:`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RC];
   assign reg_ddrc_derated_t_rcd_write_freq3[(`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE) -1:0] = r2853_derateval1_freq3[`REGB_FREQ3_CH0_OFFSET_DERATEVAL1_DERATED_T_RCD_WRITE+:`REGB_FREQ3_CH0_SIZE_DERATEVAL1_DERATED_T_RCD_WRITE];
   //------------------------
   // Register REGB_FREQ3_CH0.HWLPTMG0
   //------------------------
   assign reg_ddrc_hw_lp_idle_x32_freq3[(`REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32) -1:0] = r2854_hwlptmg0_freq3[`REGB_FREQ3_CH0_OFFSET_HWLPTMG0_HW_LP_IDLE_X32+:`REGB_FREQ3_CH0_SIZE_HWLPTMG0_HW_LP_IDLE_X32];
   //------------------------
   // Register REGB_FREQ3_CH0.DVFSCTL0
   //------------------------
   assign reg_ddrc_dvfsq_enable_freq3 = r2855_dvfsctl0_freq3[`REGB_FREQ3_CH0_OFFSET_DVFSCTL0_DVFSQ_ENABLE+:`REGB_FREQ3_CH0_SIZE_DVFSCTL0_DVFSQ_ENABLE];
   //------------------------
   // Register REGB_FREQ3_CH0.SCHEDTMG0
   //------------------------
   assign reg_ddrc_pageclose_timer_freq3[(`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER) -1:0] = r2856_schedtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_PAGECLOSE_TIMER+:`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_PAGECLOSE_TIMER];
   assign reg_ddrc_rdwr_idle_gap_freq3[(`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP) -1:0] = r2856_schedtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_SCHEDTMG0_RDWR_IDLE_GAP+:`REGB_FREQ3_CH0_SIZE_SCHEDTMG0_RDWR_IDLE_GAP];
   //------------------------
   // Register REGB_FREQ3_CH0.PERFHPR1
   //------------------------
   assign reg_ddrc_hpr_max_starve_freq3[(`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE) -1:0] = r2857_perfhpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_MAX_STARVE+:`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_MAX_STARVE];
   assign reg_ddrc_hpr_xact_run_length_freq3[(`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH) -1:0] = r2857_perfhpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFHPR1_HPR_XACT_RUN_LENGTH+:`REGB_FREQ3_CH0_SIZE_PERFHPR1_HPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ3_CH0.PERFLPR1
   //------------------------
   assign reg_ddrc_lpr_max_starve_freq3[(`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE) -1:0] = r2858_perflpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_MAX_STARVE+:`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_MAX_STARVE];
   assign reg_ddrc_lpr_xact_run_length_freq3[(`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH) -1:0] = r2858_perflpr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFLPR1_LPR_XACT_RUN_LENGTH+:`REGB_FREQ3_CH0_SIZE_PERFLPR1_LPR_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ3_CH0.PERFWR1
   //------------------------
   assign reg_ddrc_w_max_starve_freq3[(`REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE) -1:0] = r2859_perfwr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_MAX_STARVE+:`REGB_FREQ3_CH0_SIZE_PERFWR1_W_MAX_STARVE];
   assign reg_ddrc_w_xact_run_length_freq3[(`REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH) -1:0] = r2859_perfwr1_freq3[`REGB_FREQ3_CH0_OFFSET_PERFWR1_W_XACT_RUN_LENGTH+:`REGB_FREQ3_CH0_SIZE_PERFWR1_W_XACT_RUN_LENGTH];
   //------------------------
   // Register REGB_FREQ3_CH0.TMGCFG
   //------------------------
   assign reg_ddrc_frequency_ratio_freq3 = r2860_tmgcfg_freq3[`REGB_FREQ3_CH0_OFFSET_TMGCFG_FREQUENCY_RATIO+:`REGB_FREQ3_CH0_SIZE_TMGCFG_FREQUENCY_RATIO];
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG0
   //------------------------
   assign reg_ddrc_diff_rank_rd_gap_freq3[(`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP) -1:0] = r2861_ranktmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_RD_GAP+:`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP];
   assign reg_ddrc_diff_rank_wr_gap_freq3[(`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP) -1:0] = r2861_ranktmg0_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG0_DIFF_RANK_WR_GAP+:`REGB_FREQ3_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP];
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG1
   //------------------------
   assign reg_ddrc_wr2rd_dr_freq3[(`REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR) -1:0] = r2862_ranktmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_WR2RD_DR+:`REGB_FREQ3_CH0_SIZE_RANKTMG1_WR2RD_DR];
   assign reg_ddrc_rd2wr_dr_freq3[(`REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR) -1:0] = r2862_ranktmg1_freq3[`REGB_FREQ3_CH0_OFFSET_RANKTMG1_RD2WR_DR+:`REGB_FREQ3_CH0_SIZE_RANKTMG1_RD2WR_DR];
   //------------------------
   // Register REGB_FREQ3_CH0.PWRTMG
   //------------------------
   assign reg_ddrc_powerdown_to_x32_freq3[(`REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32) -1:0] = r2863_pwrtmg_freq3[`REGB_FREQ3_CH0_OFFSET_PWRTMG_POWERDOWN_TO_X32+:`REGB_FREQ3_CH0_SIZE_PWRTMG_POWERDOWN_TO_X32];
   assign reg_ddrc_selfref_to_x32_freq3[(`REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32) -1:0] = r2863_pwrtmg_freq3[`REGB_FREQ3_CH0_OFFSET_PWRTMG_SELFREF_TO_X32+:`REGB_FREQ3_CH0_SIZE_PWRTMG_SELFREF_TO_X32];
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG0
   //------------------------
   assign reg_ddrc_t_pgm_x1_x1024_freq3[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024) -1:0] = r2869_ddr4pprtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_X1024+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_X1024];
   assign reg_ddrc_t_pgm_x1_sel_freq3 = r2869_ddr4pprtmg0_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG0_T_PGM_X1_SEL+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG0_T_PGM_X1_SEL];
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG1
   //------------------------
   assign reg_ddrc_t_pgmpst_x32_freq3[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32) -1:0] = r2870_ddr4pprtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGMPST_X32+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGMPST_X32];
   assign reg_ddrc_t_pgm_exit_freq3[(`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT) -1:0] = r2870_ddr4pprtmg1_freq3[`REGB_FREQ3_CH0_OFFSET_DDR4PPRTMG1_T_PGM_EXIT+:`REGB_FREQ3_CH0_SIZE_DDR4PPRTMG1_T_PGM_EXIT];
   //------------------------
   // Register REGB_FREQ3_CH0.LNKECCCTL0
   //------------------------
   assign reg_ddrc_wr_link_ecc_enable_freq3 = r2871_lnkeccctl0_freq3[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_WR_LINK_ECC_ENABLE+:`REGB_FREQ3_CH0_SIZE_LNKECCCTL0_WR_LINK_ECC_ENABLE];
   assign reg_ddrc_rd_link_ecc_enable_freq3 = r2871_lnkeccctl0_freq3[`REGB_FREQ3_CH0_OFFSET_LNKECCCTL0_RD_LINK_ECC_ENABLE+:`REGB_FREQ3_CH0_SIZE_LNKECCCTL0_RD_LINK_ECC_ENABLE];



// ecc interrupt wires
//wire ecc_corrected_err_int;
wire ecc_uncorrected_err_en;
wire ecc_corrected_err_en;

assign ecc_corrected_err_intr_en          =  ecc_corrected_err_en;
assign ecc_uncorrected_err_intr_en        =  ecc_uncorrected_err_en;



wire   rd_link_ecc_uncorr_err_en, rd_link_ecc_corr_err_en;
assign rd_link_ecc_uncorr_intr_en = rd_link_ecc_uncorr_err_en;
assign rd_link_ecc_corr_intr_en   = rd_link_ecc_corr_err_en;



// ecc ap interrupt wires
wire ecc_ap_err_en;

assign ecc_ap_err_intr_en                     = ecc_ap_err_en;


   assign ecc_corrected_err_en      = reg_ddrc_ecc_corrected_err_intr_en;
   assign ecc_uncorrected_err_en    = reg_ddrc_ecc_uncorrected_err_intr_en;
   //assign ecc_corrected_err_int     = |ddrc_reg_ecc_corrected_err;
   //assign ecc_uncorrected_err_int   = |ddrc_reg_ecc_uncorrected_err;
   assign ecc_ap_err_en                      = reg_ddrc_ecc_ap_err_intr_en;
   assign rd_link_ecc_uncorr_err_en  = reg_ddrc_rd_link_ecc_uncorr_intr_en;
   assign rd_link_ecc_corr_err_en    = reg_ddrc_rd_link_ecc_corr_intr_en;




   //-------------------------------------------------
   // Clock domain crossing: DYNAMIC registers
   //-------------------------------------------------   































   wire wait_reg_ddrc_zq_reset_ack = 1'b0;




























































































































































































































































































































































































































































































   wire wait_reg_ddrc_ppt2_burst_ack = 1'b0;























































































































































































































































































































































































































































































































































































































































































































































































































































   assign pclk_derate_temp_limit_intr = core_derate_temp_limit_intr;


   //------------------------------------------------
   // instantiate ecc_poison_reg (indirect write registers)
   //------------------------------------------------


   //-----------------------------------------
   // Register Parity checking of *_busy logic
   //-----------------------------------------


  assign pclk_ddrc_reg_ecc_ap_err = ddrc_reg_ecc_ap_err_int; 



  assign pclk_ddrc_reg_ecc_corrected_err = ddrc_reg_ecc_corrected_err_int;

  assign pclk_ddrc_reg_ecc_uncorrected_err = ddrc_reg_ecc_uncorrected_err_int;

  assign pclk_ddrc_reg_ecc_corrected_bit_num = ddrc_reg_ecc_corrected_bit_num_int;

  assign pclk_ddrc_reg_sbr_read_ecc_err = ddrc_reg_sbr_read_ecc_err_int;





//-----------------------
// Bit synchronizers for the DFI Sideband Watchdog Timer Error interrupt inputs
//-----------------------


//-----------------------
// Bit synchronizers for the DFI Error interface interrupt inputs
//-----------------------


//-------------------------------------------------------------------------------------------

    //-----------------------------------------------------------------------------------------------
    // DCH0 P-SYNC
    //-----------------------------------------------------------------------------------------------
  assign pclk_ddrc_reg_rd_linkecc_uncorr_err_int = ddrc_reg_rd_linkecc_uncorr_err_intr;
  assign pclk_ddrc_reg_rd_linkecc_corr_err_int = ddrc_reg_rd_linkecc_corr_err_intr;

    //-----------------------------------------------------------------------------------------------


endmodule
