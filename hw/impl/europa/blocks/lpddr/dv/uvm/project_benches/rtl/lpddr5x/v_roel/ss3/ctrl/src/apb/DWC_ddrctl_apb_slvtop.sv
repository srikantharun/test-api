//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/apb/DWC_ddrctl_apb_slvtop.sv#31 $
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

`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"


module DWC_ddrctl_apb_slvtop
import DWC_ddrctl_reg_pkg::*;
  #(parameter APB_AW  = `UMCTL2_APB_AW,
    parameter APB_DW  = `UMCTL2_APB_DW,
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
    parameter N_REGS  = `UMCTL2_REGS_N_REGS,
    parameter RW_REGS = `UMCTL2_REGS_RW_REGS
    )
   (
    //---APB MASTER INTERFACE---//
    input               pclk,    
    input               presetn,
    input               pclk_apbrw,    
    input               core_ddrc_core_clk_apbrw,    
    input [APB_AW-1:2]  paddr,
    input [APB_DW-1:0]  pwdata,
    input               pwrite,
    input               psel,
    input               penable,
    output              pready,
    output [APB_DW-1:0] prdata,
    output              pslverr
    //--- uMCTL2 INTERFACE ---//
    ,input              core_ddrc_core_clk
    ,input              sync_core_ddrc_rstn
    ,input              core_ddrc_rstn
    ,input               aclk_0
    ,input               sync_aresetn_0
  `ifndef SYNTHESIS
    ,input               aresetn_0
  `endif //SYNTHESIS
    ,input               static_wr_en_core_ddrc_core_clk
    ,input               quasi_dyn_wr_en_core_ddrc_core_clk
//`ifdef UMCTL2_OCECC_EN_1    
//    ,input               quasi_dyn_wr_en_pclk
//`endif //UMCTL2_OCPAR_OR_OCECC_EN_1
    ,input               static_wr_en_aclk_0
    ,input               quasi_dyn_wr_en_aclk_0

    ,input               core_derate_temp_limit_intr

//ccx_tgl : ; ddrc_reg_dbg_hpr_q_depth[6] ; ; SCHED.lpr_num_entries is defined such that there is always a min of one CAM entry for LPR. So cannot have 64 CAM entries for HPR - can have a max of 63 for HPR only.
//ccx_tgl : ; ddrc_reg_ecc_corr_bit_mask_71_64[7:0] ;  ; Error logging register is not covered since errors on ECC bits (these bit indices) are detected and logged as errors in data bits, due to the nature of the Hamming algorithm. Unreachable.
//ccx_tgl : ; ddrc_reg_ecc_corr_col[10] ;  ; Error logging register that stores column bit 10 value of address where error was detected. There are currently no memory devices that have such high densities, so bit 10 is unreachable
//ccx_tgl : ; ddrc_reg_ecc_corr_err_cnt[15:9] ;  ; Error logging register that stores occurrence count of ECC errors detected. We don't generate that many errors as to toggle the high bits of this counter, but the counter's functionality is covered in lower counts. Very low risk.
//ccx_tgl : ; ddrc_reg_ecc_corr_err_cnt[8] ; 1->0 ; Error logging register that stores occurrence count of ECC errors detected. We don't generate that many errors as to toggle the high bits of this counter, but the counter's functionality is covered in lower counts. Very low risk.
//ccx_tgl : ; ddrc_reg_ecc_corr_row[17] ;  ; This should be covered however stimulus is lacking. Task to cover this item is captured at https://jira.internal.synopsys.com/browse/P80001562-99868
//ccx_tgl : ; ddrc_reg_ecc_uncorr_col[10] ; ; Error logging register that stores column bit 10 value of address where error was detected. There are currently no memory devices that have such high densities, so bit 10 is unreachable.
//ccx_tgl : ; ddrc_reg_ecc_uncorr_err_cnt[15:10] ; ; Error logging register that stores occurrence count of ECC errors detected. We don't generate that many errors as to toggle the high bits of this counter, but the counter's functionality is covered in lower counts. Very low risk.
//ccx_tgl : ; ddrc_reg_ecc_uncorr_row[17] ; ; This should be covered however stimulus is lacking. Task to cover this item is captured at https://jira.internal.synopsys.com/browse/P80001562-99868
//ccx_tgl : ; ddrc_reg_rd_link_ecc_err_syndrome[8] ; ; This is corresponding to S8 of ECC syndrome, which can be toggled from 0 to 1, but not toggled from 1 to 0.
//ccx_tgl : ; ddrc_reg_link_ecc_corr_bank[2] ; ; Link ECC is supported in DRAMs where WCK frequency is greater than 1600Mhz. Only BG mode is used in these devices, so bit 2 is unreachable.
//ccx_tgl : ; ddrc_reg_link_ecc_corr_col[10] ; ; Error logging register that stores column bit 10 value of address where error was detected. There are currently no memory devices that have such high densities, so bit 10 is unreachable
//ccx_tgl : ; ddrc_reg_link_ecc_corr_row[17] ; ; This should be covered however stimulus is lacking. Task to cover this item is captured at https://jira.internal.synopsys.com/browse/P80001562-99868
//ccx_tgl : ; ddrc_reg_link_ecc_uncorr_bank[2] ; ; Link ECC is supported in DRAMs where WCK frequency is greater than 1600Mhz. Only BG mode is used in these devices, so bit 2 is unreachable.
//ccx_tgl : ; ddrc_reg_link_ecc_uncorr_col[10] ; ; Error logging register that stores column bit 10 value of address where error was detected. There are currently no memory devices that have such high densities, so bit 10 is unreachable.
//ccx_tgl : ; ddrc_reg_link_ecc_uncorr_row[17] ; ; This should be covered however stimulus is lacking. Task to cover this item is captured at https://jira.internal.synopsys.com/browse/P80001562-99868
//ccx_tgl : ; reg_ddrc_ppt2_ctrlupd_num_dfi0[5:4] ; 1->0 ; Expected value in this register is 3, 4, 6 or 8. This item can be ignored.
//ccx_tgl : ; reg_ddrc_ppt2_ctrlupd_num_dfi1[5:4] ; 1->0 ; Expected value in this register is 3, 4, 6 or 8. This item can be ignored.
//ccx_tgl : ; reg_ddrc_ppt2_ctrlupd_num_dfi0[5:4] ; 0->1 ; Can be ignored as its score is expected. Uncovered part is ppt2_ctrlupd_num_dfi0/1[5:4]. Since it's only written as 3,4,6 or 8, [5:4] can be left unused.
//ccx_tgl : ; reg_ddrc_ppt2_ctrlupd_num_dfi1[5:4] ; 0->1 ; Can be ignored as its score is expected. Uncovered part is ppt2_ctrlupd_num_dfi0/1[5:4]. Since it's only written as 3,4,6 or 8, [5:4] can be left unused.
//ccx_tgl : ; reg_ddrc_ppt2_burst_num[0] ; ; It can be multiple of 2 ([0] is uncoverable) when dual dfi. PPT2 is currently enabled only in SOCIONEXT config which is dual dfi.
//ccx_tgl : ; reg_ddrc_ppt2_burst_num[7:1] ; 1->0 ; reg_ddrc_ppt2_burst_num[7:1] 1->0 is hardly coverable because it needs multiple burst ppt2 sequence with changing ppt2_burst_num for all of its bits. As the range of [9:8] is enough and left to be checked for coverage verification, ignoring [7:1].
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
   ,output [(`DDRCTL_FREQUENCY_BITS)-1:0] reg_ddrc_target_frequency // @core_ddrc_core_clk
   ,output reg_ddrc_wck_on // @core_ddrc_core_clk
   ,output reg_ddrc_wck_suspend_en // @core_ddrc_core_clk
   ,output reg_ddrc_ws_off_en // @core_ddrc_core_clk
   ,input [2:0] ddrc_reg_operating_mode // @core_ddrc_core_clk
   ,input [((`DDRCTL_DDR_EN==1) ? (`MEMC_NUM_RANKS*2) : 2)-1:0] ddrc_reg_selfref_type // @core_ddrc_core_clk
   ,input [2:0] ddrc_reg_selfref_state // @core_ddrc_core_clk
   ,input ddrc_reg_selfref_cam_not_empty // @core_ddrc_core_clk
   ,output reg_ddrc_mr_type // @core_ddrc_core_clk
   ,output reg_ddrc_sw_init_int // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_mr_rank // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_mr_addr // @core_ddrc_core_clk
   ,output reg_ddrc_mrr_done_clr // @core_ddrc_core_clk
   ,output reg_ddrc_dis_mrrw_trfc // @core_ddrc_core_clk
   ,output reg_ddrc_ppr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ppr_pgmpst_en // @core_ddrc_core_clk
   ,output reg_ddrc_mr_wr // @core_ddrc_core_clk
   ,output [(`MEMC_PAGE_BITS)-1:0] reg_ddrc_mr_data // @core_ddrc_core_clk
   ,input ddrc_reg_mr_wr_busy // @core_ddrc_core_clk
   ,input ddrc_reg_mrr_done // @core_ddrc_core_clk
   ,input ddrc_reg_ppr_done // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_mrr_data_lwr // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_mrr_data_upr // @core_ddrc_core_clk
   ,output reg_ddrc_derate_enable // @core_ddrc_core_clk
   ,output reg_ddrc_lpddr4_refresh_mode // @core_ddrc_core_clk
   ,output reg_ddrc_derate_mr4_pause_fc // @core_ddrc_core_clk
   ,output reg_ddrc_dis_trefi_x6x8 // @core_ddrc_core_clk
   ,output reg_ddrc_dis_trefi_x0125 // @core_ddrc_core_clk
   ,output reg_ddrc_use_slow_rm_in_low_temp // @core_ddrc_core_clk
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/4)-1:0] reg_ddrc_active_derate_byte_rank0 // @core_ddrc_core_clk
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/4)-1:0] reg_ddrc_active_derate_byte_rank1 // @core_ddrc_core_clk
   ,output reg_ddrc_derate_temp_limit_intr_en // @pclk
   ,output reg_ddrc_derate_temp_limit_intr_clr // @pclk
   ,output reg_ddrc_derate_temp_limit_intr_force // @pclk
   ,output reg_ddrc_derate_mr4_tuf_dis // @core_ddrc_core_clk
   ,input ddrc_reg_derate_temp_limit_intr // @pclk
   ,output [1:0] reg_ddrc_dbg_mr4_rank_sel // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte0 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte1 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte2 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_dbg_mr4_byte3 // @core_ddrc_core_clk
   ,output [((`DDRCTL_DDR_EN==1) ? `MEMC_NUM_RANKS : 1)-1:0] reg_ddrc_selfref_en // @core_ddrc_core_clk
   ,output [((`DDRCTL_DDR_EN==1) ? `MEMC_NUM_RANKS : 1)-1:0] reg_ddrc_powerdown_en // @core_ddrc_core_clk
   ,output reg_ddrc_en_dfi_dram_clk_disable // @core_ddrc_core_clk
   ,output reg_ddrc_selfref_sw // @core_ddrc_core_clk
   ,output reg_ddrc_stay_in_selfref // @core_ddrc_core_clk
   ,output reg_ddrc_dis_cam_drain_selfref // @core_ddrc_core_clk
   ,output reg_ddrc_lpddr4_sr_allowed // @core_ddrc_core_clk
   ,output reg_ddrc_dsm_en // @core_ddrc_core_clk
   ,output reg_ddrc_hw_lp_en // @core_ddrc_core_clk
   ,output reg_ddrc_hw_lp_exit_idle_en // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_bsm_clk_on // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_burst // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_auto_refab_en // @core_ddrc_core_clk
   ,output reg_ddrc_per_bank_refresh // @core_ddrc_core_clk
   ,output reg_ddrc_per_bank_refresh_opt_en // @core_ddrc_core_clk
   ,output reg_ddrc_fixed_crit_refpb_bank_en // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_refresh // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_update_level // @core_ddrc_core_clk
   ,output reg_ddrc_rfm_en // @core_ddrc_core_clk
   ,output reg_ddrc_rfmsbc // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_raaimt // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_raamult // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_raadec // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_rfmth_rm_thr // @core_ddrc_core_clk
   ,output [10:0] reg_ddrc_init_raa_cnt // @core_ddrc_core_clk
   ,output [(`MEMC_RANK_BITS)-1:0] reg_ddrc_dbg_raa_rank // @core_ddrc_core_clk
   ,output [((`DDRCTL_LPDDR_RFMSBC_EN==1) ? `MEMC_BG_BANK_BITS : (`MEMC_BG_BANK_BITS-1))-1:0] reg_ddrc_dbg_raa_bg_bank // @core_ddrc_core_clk
   ,input [(`MEMC_NUM_RANKS)-1:0] ddrc_reg_rank_raa_cnt_gt0 // @core_ddrc_core_clk
   ,input [10:0] ddrc_reg_dbg_raa_cnt // @core_ddrc_core_clk
   ,output reg_ddrc_zq_resistor_shared // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_zq // @core_ddrc_core_clk
   ,output reg_ddrc_zq_reset // @core_ddrc_core_clk
   ,output reg_ddrc_dis_srx_zqcl // @core_ddrc_core_clk
   ,output reg_ddrc_dis_srx_zqcl_hwffc // @core_ddrc_core_clk
   ,input ddrc_reg_zq_reset_busy // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dqsosc_runtime // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wck2dqo_runtime // @core_ddrc_core_clk
   ,input [2:0] ddrc_reg_dqsosc_state // @core_ddrc_core_clk
   ,input [(`MEMC_NUM_RANKS)-1:0] ddrc_reg_dqsosc_per_rank_stat // @core_ddrc_core_clk
   ,output reg_ddrc_dis_dqsosc_srx // @core_ddrc_core_clk
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
   ,output [3:0] reg_ddrc_delay_switch_write // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_visible_window_limit_wr // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_visible_window_limit_rd // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_page_hit_limit_wr // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_page_hit_limit_rd // @core_ddrc_core_clk
   ,output reg_ddrc_opt_hit_gt_hpr // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wrcam_lowthresh // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wrcam_highthresh // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wr_pghit_num_thresh // @core_ddrc_core_clk
   ,output [(`MEMC_RDCMD_ENTRY_BITS)-1:0] reg_ddrc_rd_pghit_num_thresh // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd_act_idle_gap // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr_act_idle_gap // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd_page_exp_cycles // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr_page_exp_cycles // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS-1)-1:0] reg_ddrc_wrecc_cam_lowthresh // @core_ddrc_core_clk
   ,output [(`MEMC_WRCMD_ENTRY_BITS-1)-1:0] reg_ddrc_wrecc_cam_highthresh // @core_ddrc_core_clk
   ,output reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level // @core_ddrc_core_clk
   ,output reg_ddrc_dis_opt_valid_wrecc_cam_fill_level // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_hwffc_en // @core_ddrc_core_clk
   ,output reg_ddrc_init_fsp // @core_ddrc_core_clk
   ,output reg_ddrc_init_vrcg // @core_ddrc_core_clk
   ,output reg_ddrc_target_vrcg // @core_ddrc_core_clk
   ,output reg_ddrc_skip_mrw_odtvref // @core_ddrc_core_clk
   ,output reg_ddrc_skip_zq_stop_start // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_zq_interval // @core_ddrc_core_clk
   ,output reg_ddrc_hwffc_mode // @core_ddrc_core_clk
   ,input ddrc_reg_hwffc_in_progress // @core_ddrc_core_clk
   ,input ddrc_reg_hwffc_operating_mode // @core_ddrc_core_clk
   ,input [(`DDRCTL_FREQUENCY_BITS)-1:0] ddrc_reg_current_frequency // @core_ddrc_core_clk
   ,input ddrc_reg_current_fsp // @core_ddrc_core_clk
   ,input ddrc_reg_current_vrcg // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_pd // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_sr // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_dsm // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_en_data // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_lp_data_req_en // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_extra_gap_for_dfi_lp_data // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_phyupd_en // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_pre_srx // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_ctrlupd_srx // @core_ddrc_core_clk
   ,output reg_ddrc_dis_auto_ctrlupd // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_init_complete_en // @core_ddrc_core_clk
   ,output reg_ddrc_phy_dbi_mode // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_data_cs_polarity // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_reset_n // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_init_start // @core_ddrc_core_clk
   ,output reg_ddrc_lp_optimized_write // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_frequency // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_freq_fsp // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_channel_mode // @core_ddrc_core_clk
   ,input ddrc_reg_dfi_init_complete // @core_ddrc_core_clk
   ,input ddrc_reg_dfi_lp_ctrl_ack_stat // @core_ddrc_core_clk
   ,input ddrc_reg_dfi_lp_data_ack_stat // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_phymstr_en // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_phymstr_blk_ref_x32 // @core_ddrc_core_clk
   ,output reg_ddrc_wr_poison_slverr_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_poison_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_poison_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_poison_slverr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_poison_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_poison_intr_clr // @core_ddrc_core_clk
   ,input ddrc_reg_wr_poison_intr_0 // @core_ddrc_core_clk
   ,input ddrc_reg_rd_poison_intr_0 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_ecc_mode // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_remap_en // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_ecc_region_map // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_blk_channel_idle_time_x32 // @core_ddrc_core_clk
   ,output [(`MEMC_MAX_INLINE_ECC_PER_BURST_BITS)-1:0] reg_ddrc_ecc_ap_err_threshold // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_map_other // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_ecc_region_map_granu // @core_ddrc_core_clk
   ,output reg_ddrc_data_poison_en // @core_ddrc_core_clk
   ,output reg_ddrc_data_poison_bit // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_parity_lock // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_region_waste_lock // @core_ddrc_core_clk
   ,output reg_ddrc_med_ecc_en // @core_ddrc_core_clk
   ,output reg_ddrc_blk_channel_active_term // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_active_blk_channel // @core_ddrc_core_clk
   ,input [6:0] ddrc_reg_ecc_corrected_bit_num // @pclk
   ,input [((`MEMC_INLINE_ECC_EN==1 && `MEMC_SIDEBAND_ECC_EN==0) ? 1 : (`MEMC_FREQ_RATIO==4) ? 8 : 4)-1:0] ddrc_reg_ecc_corrected_err // @pclk
   ,input [((`MEMC_INLINE_ECC_EN==1 && `MEMC_SIDEBAND_ECC_EN==0) ? 1 : (`MEMC_FREQ_RATIO==4) ? 8 : 4)-1:0] ddrc_reg_ecc_uncorrected_err // @pclk
   ,input ddrc_reg_sbr_read_ecc_ce // @pclk
   ,input ddrc_reg_sbr_read_ecc_ue // @pclk
   ,output reg_ddrc_ecc_corrected_err_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorrected_err_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_corr_err_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorr_err_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_err_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_corrected_err_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorrected_err_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_err_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_corrected_err_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_uncorrected_err_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_ecc_ap_err_intr_force // @core_ddrc_core_clk
   ,input [15:0] ddrc_reg_ecc_corr_err_cnt // @core_ddrc_core_clk
   ,input [15:0] ddrc_reg_ecc_uncorr_err_cnt // @core_ddrc_core_clk
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_ecc_corr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_ecc_corr_rank // @core_ddrc_core_clk
   ,input [10:0] ddrc_reg_ecc_corr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_ecc_corr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_ecc_corr_bg // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ecc_corr_syndromes_31_0 // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ecc_corr_syndromes_63_32 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_ecc_corr_syndromes_71_64 // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ecc_corr_bit_mask_31_0 // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ecc_corr_bit_mask_63_32 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_ecc_corr_bit_mask_71_64 // @core_ddrc_core_clk
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_ecc_uncorr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_ecc_uncorr_rank // @core_ddrc_core_clk
   ,input [10:0] ddrc_reg_ecc_uncorr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_ecc_uncorr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_ecc_uncorr_bg // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ecc_uncorr_syndromes_31_0 // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ecc_uncorr_syndromes_63_32 // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_ecc_uncorr_syndromes_71_64 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_ecc_poison_col // @core_ddrc_core_clk
   ,output [(`MEMC_RANK_BITS)-1:0] reg_ddrc_ecc_poison_rank // @core_ddrc_core_clk
   ,output [(`MEMC_PAGE_BITS)-1:0] reg_ddrc_ecc_poison_row // @core_ddrc_core_clk
   ,output [(`MEMC_BANK_BITS)-1:0] reg_ddrc_ecc_poison_bank // @core_ddrc_core_clk
   ,output [(`MEMC_BG_BITS)-1:0] reg_ddrc_ecc_poison_bg // @core_ddrc_core_clk
   ,output [31:0] reg_ddrc_ecc_poison_data_31_0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_ecc_poison_data_71_64 // @core_ddrc_core_clk
   ,input ddrc_reg_ecc_ap_err // @pclk
   ,output reg_ddrc_rd_link_ecc_corr_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_corr_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_corr_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_corr_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_cnt_clr // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_uncorr_intr_force // @core_ddrc_core_clk
   ,output reg_ddrc_linkecc_poison_inject_en // @core_ddrc_core_clk
   ,output reg_ddrc_linkecc_poison_type // @core_ddrc_core_clk
   ,output reg_ddrc_linkecc_poison_rw // @core_ddrc_core_clk
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/8)-1:0] reg_ddrc_linkecc_poison_dmi_sel // @core_ddrc_core_clk
   ,output [(`MEMC_DRAM_TOTAL_DATA_WIDTH/8)-1:0] reg_ddrc_linkecc_poison_byte_sel // @core_ddrc_core_clk
   ,input ddrc_reg_linkecc_poison_complete // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_rd_link_ecc_err_byte_sel // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_rd_link_ecc_err_rank_sel // @core_ddrc_core_clk
   ,input [8:0] ddrc_reg_rd_link_ecc_err_syndrome // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_rd_link_ecc_corr_cnt // @core_ddrc_core_clk
   ,input [7:0] ddrc_reg_rd_link_ecc_uncorr_cnt // @core_ddrc_core_clk
   ,input [3:0] ddrc_reg_rd_link_ecc_corr_err_int // @pclk
   ,input [3:0] ddrc_reg_rd_link_ecc_uncorr_err_int // @pclk
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_link_ecc_corr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_link_ecc_corr_rank // @core_ddrc_core_clk
   ,input [10:0] ddrc_reg_link_ecc_corr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_link_ecc_corr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_link_ecc_corr_bg // @core_ddrc_core_clk
   ,input [(`MEMC_PAGE_BITS)-1:0] ddrc_reg_link_ecc_uncorr_row // @core_ddrc_core_clk
   ,input [(`MEMC_RANK_BITS)-1:0] ddrc_reg_link_ecc_uncorr_rank // @core_ddrc_core_clk
   ,input [10:0] ddrc_reg_link_ecc_uncorr_col // @core_ddrc_core_clk
   ,input [(`MEMC_BANK_BITS)-1:0] ddrc_reg_link_ecc_uncorr_bank // @core_ddrc_core_clk
   ,input [(`MEMC_BG_BITS)-1:0] ddrc_reg_link_ecc_uncorr_bg // @core_ddrc_core_clk
   ,output reg_ddrc_dis_wc // @core_ddrc_core_clk
   ,output reg_ddrc_dis_max_rank_rd_opt // @core_ddrc_core_clk
   ,output reg_ddrc_dis_max_rank_wr_opt // @core_ddrc_core_clk
   ,output reg_ddrc_dis_dq // @core_ddrc_core_clk
   ,output reg_ddrc_dis_hif // @core_ddrc_core_clk
   ,input [(`MEMC_RDCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_hpr_q_depth // @core_ddrc_core_clk
   ,input [(`MEMC_RDCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_lpr_q_depth // @core_ddrc_core_clk
   ,input [(`MEMC_WRCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_w_q_depth // @core_ddrc_core_clk
   ,input ddrc_reg_dbg_stall // @core_ddrc_core_clk
   ,input ddrc_reg_dbg_rd_q_empty // @core_ddrc_core_clk
   ,input ddrc_reg_dbg_wr_q_empty // @core_ddrc_core_clk
   ,input ddrc_reg_rd_data_pipeline_empty // @core_ddrc_core_clk
   ,input ddrc_reg_wr_data_pipeline_empty // @core_ddrc_core_clk
   ,output reg_ddrc_zq_calib_short // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_burst // @core_ddrc_core_clk
   ,input ddrc_reg_zq_calib_short_busy // @core_ddrc_core_clk
   ,input ddrc_reg_ctrlupd_busy // @core_ddrc_core_clk
   ,input ddrc_reg_ctrlupd_burst_busy // @core_ddrc_core_clk
   ,input [(`MEMC_WRCMD_ENTRY_BITS+1)-1:0] ddrc_reg_dbg_wrecc_q_depth // @core_ddrc_core_clk
   ,output reg_ddrc_rank0_refresh // @core_ddrc_core_clk
   ,output reg_ddrc_rank1_refresh // @core_ddrc_core_clk
   ,input ddrc_reg_rank0_refresh_busy // @core_ddrc_core_clk
   ,input ddrc_reg_rank1_refresh_busy // @core_ddrc_core_clk
   ,output reg_ddrc_sw_done // @pclk
   ,input ddrc_reg_sw_done_ack // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_max_rank_rd // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_max_rank_wr // @core_ddrc_core_clk
   ,output reg_ddrc_dm_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_dbi_en // @core_ddrc_core_clk
   ,output reg_ddrc_rd_dbi_en // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank0_wr_odt // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank0_rd_odt // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank1_wr_odt // @core_ddrc_core_clk
   ,output [(`MEMC_NUM_RANKS)-1:0] reg_ddrc_rank1_rd_odt // @core_ddrc_core_clk
   ,output reg_ddrc_rd_data_copy_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_data_copy_en // @core_ddrc_core_clk
   ,output reg_ddrc_wr_data_x_en // @core_ddrc_core_clk
   ,output reg_ddrc_sw_static_unlock // @pclk
   ,output reg_ddrc_force_clk_te_en // @core_ddrc_core_clk
   ,output reg_ddrc_force_clk_arb_en // @core_ddrc_core_clk
   ,output [12:0] reg_ddrc_pre_cke_x1024 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_post_cke_x1024 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_skip_dram_init // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_ppt2_burst_num // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_ppt2_ctrlupd_num_dfi0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_ppt2_ctrlupd_num_dfi1 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_burst // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_wait_ref // @core_ddrc_core_clk
   ,input [3:0] ddrc_reg_ppt2_state // @core_ddrc_core_clk
   ,input ddrc_reg_ppt2_burst_busy // @core_ddrc_core_clk
   ,input [31:0] ddrc_reg_ver_number // @pclk
   ,input [31:0] ddrc_reg_ver_type // @pclk
   ,output [5:0] reg_ddrc_addrmap_cs_bit0_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bank_b0_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bank_b1_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bank_b2_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bg_b0_map0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_addrmap_bg_b1_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b7_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b8_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b9_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_col_b10_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b3_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b4_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b5_map0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_addrmap_col_b6_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b14_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b15_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b16_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b17_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b10_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b11_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b12_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b13_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b6_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b7_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b8_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b9_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b2_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b3_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b4_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b5_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b0_map0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_addrmap_row_b1_map0 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_nonbinary_device_density_map0 // @core_ddrc_core_clk
   ,output reg_ddrc_bank_hash_en_map0 // @core_ddrc_core_clk
   ,output reg_arb_go2critical_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_pagematch_limit_port0 // @core_ddrc_core_clk
   ,output [9:0] reg_arb_rd_port_priority_port0 // @core_ddrc_core_clk
   ,output reg_arb_rd_port_aging_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_rd_port_urgent_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_rd_port_pagematch_en_port0 // @core_ddrc_core_clk
   ,output [3:0] reg_arb_rrb_lock_threshold_port0 // @core_ddrc_core_clk
   ,output [9:0] reg_arb_wr_port_priority_port0 // @core_ddrc_core_clk
   ,output reg_arb_wr_port_aging_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_wr_port_urgent_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_wr_port_pagematch_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_port_en_port0 // @core_ddrc_core_clk
   ,output reg_apb_port_en_port0 // @pclk 
   ,output reg_arba0_port_en_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_MLW)-1:0] reg_arba0_rqos_map_level1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_MLW)-1:0] reg_arba0_rqos_map_level2_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region0_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region2_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_RQOS_TW)-1:0] reg_arb_rqos_map_timeoutb_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_XPI_RQOS_TW)-1:0] reg_arb_rqos_map_timeoutr_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_XPI_WQOS_MLW)-1:0] reg_arba0_wqos_map_level1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_MLW)-1:0] reg_arba0_wqos_map_level2_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region0_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region1_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region2_port0 // @aclk_0
   ,output [(`UMCTL2_XPI_WQOS_TW)-1:0] reg_arb_wqos_map_timeout1_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_XPI_WQOS_TW)-1:0] reg_arb_wqos_map_timeout2_port0 // @core_ddrc_core_clk
   ,output reg_arb_scrub_en_port0 // @core_ddrc_core_clk
   ,output reg_arb_scrub_during_lowpower_port0 // @core_ddrc_core_clk
   ,output [2:0] reg_arb_scrub_burst_length_nm_port0 // @core_ddrc_core_clk
   ,output [(`UMCTL2_REG_SCRUB_INTERVALW)-1:0] reg_arb_scrub_interval_port0 // @core_ddrc_core_clk
   ,output [1:0] reg_arb_scrub_cmd_type_port0 // @core_ddrc_core_clk
   ,output [2:0] reg_arb_scrub_burst_length_lp_port0 // @core_ddrc_core_clk
   ,input arb_reg_scrub_busy_port0 // @core_ddrc_core_clk
   ,input arb_reg_scrub_done_port0 // @core_ddrc_core_clk
   ,output [31:0] reg_arb_scrub_pattern0_port0 // @core_ddrc_core_clk
   ,output [31:0] reg_arb_sbr_address_start_mask_0_port0 // @core_ddrc_core_clk
   ,output [(`MEMC_HIF_ADDR_WIDTH_MAX-32)-1:0] reg_arb_sbr_address_start_mask_1_port0 // @core_ddrc_core_clk
   ,output [31:0] reg_arb_sbr_address_range_mask_0_port0 // @core_ddrc_core_clk
   ,output [(`MEMC_HIF_ADDR_WIDTH_MAX-32)-1:0] reg_arb_sbr_address_range_mask_1_port0 // @core_ddrc_core_clk
   ,input arb_reg_rd_port_busy_0_port0 // @aclk_0
   ,input arb_reg_wr_port_busy_0_port0 // @aclk_0
   ,output [7:0] reg_ddrc_t_ras_min_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rc_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2mr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_rp_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cke_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ckcsx_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_csh_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_s_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_cmdcke_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_ppd_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_xsr_freq0 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_pdn_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_wr_sync_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq0 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rda2pre_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq0 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2rd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr3_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr5_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr6_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_pd_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_sr_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_dsm_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_lp_wakeup_data_freq0 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_tlp_resp_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_dfi_t_ctrlup_min_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_dfi_t_ctrlup_max_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq0 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0 // @core_ddrc_core_clk
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq0 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfmpb_freq0 // @core_ddrc_core_clk
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq0 // @core_ddrc_core_clk
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_zq_stop_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_enable_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq0 // @core_ddrc_core_clk
   ,output [31:0] reg_ddrc_mr4_read_interval_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_derated_t_rrd_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rc_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq0 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_dvfsq_enable_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_pageclose_timer_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_hpr_max_starve_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_lpr_max_starve_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_w_max_starve_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_frequency_ratio_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_dr_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq0 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq0 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq0 // @core_ddrc_core_clk
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq0 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq0 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_wr_link_ecc_enable_freq0 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq0 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_min_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rc_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2mr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_rp_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cke_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ckcsx_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_csh_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_s_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_cmdcke_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_ppd_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_xsr_freq1 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_pdn_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_wr_sync_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq1 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rda2pre_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq1 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2rd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr3_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr5_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr6_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq1 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq1 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1 // @core_ddrc_core_clk
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq1 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfmpb_freq1 // @core_ddrc_core_clk
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq1 // @core_ddrc_core_clk
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_zq_stop_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_enable_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq1 // @core_ddrc_core_clk
   ,output [31:0] reg_ddrc_mr4_read_interval_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_derated_t_rrd_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rc_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq1 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_dvfsq_enable_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_pageclose_timer_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_hpr_max_starve_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_lpr_max_starve_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_w_max_starve_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_frequency_ratio_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_dr_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq1 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq1 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq1 // @core_ddrc_core_clk
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq1 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq1 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_wr_link_ecc_enable_freq1 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq1 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_min_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rc_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2mr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_rp_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cke_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ckcsx_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_csh_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_s_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_cmdcke_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_ppd_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_xsr_freq2 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_pdn_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_wr_sync_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq2 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rda2pre_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq2 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2rd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr3_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr5_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr6_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq2 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq2 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2 // @core_ddrc_core_clk
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq2 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfmpb_freq2 // @core_ddrc_core_clk
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq2 // @core_ddrc_core_clk
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_zq_stop_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_enable_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq2 // @core_ddrc_core_clk
   ,output [31:0] reg_ddrc_mr4_read_interval_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_derated_t_rrd_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rc_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq2 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_dvfsq_enable_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_pageclose_timer_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_hpr_max_starve_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_lpr_max_starve_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_w_max_starve_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_frequency_ratio_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_dr_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq2 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq2 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq2 // @core_ddrc_core_clk
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq2 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq2 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_wr_link_ecc_enable_freq2 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq2 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_min_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_ras_max_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_faw_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2pre_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rc_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2pre_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_xp_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_write_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_read_latency_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_write_latency_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2mr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2mr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_mr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_rp_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ccd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_rcd_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cke_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ckesr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_cksre_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_cksrx_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_ckcsx_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_csh_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_s_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_rrd_s_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_t_ccd_s_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_cmdcke_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_ppd_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_ccd_mw_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_odtloff_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_xsr_freq3 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_t_osco_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_disable_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_vrcg_enable_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_pdn_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_xsr_dsm_x1024_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_wr_sync_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_max_rd_sync_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_s_freq3 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_bank_org_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rda2pre_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wra2pre_freq3 // @core_ddrc_core_clk
   ,output [2:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2rd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2wr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_mrr2mrw_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_fs2wck_sus_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_t_wcksus_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_ws_off2ws_fs_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr3_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_emr2_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr5_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr4_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr6_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_mr22_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrlat_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_tphy_wrdata_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_t_rddata_en_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_ctrl_delay_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_enable_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_dram_clk_disable_freq3 // @core_ddrc_core_clk
   ,output [4:0] reg_ddrc_dfi_t_wrdata_delay_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_wrcslat_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_dfi_tphy_rdcslat_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_dfi_twck_delay_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_dis_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_fs_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_wr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_en_rd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_cs_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_fast_toggle_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_twck_toggle_post_rd_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_dfi_twck_toggle_post_rd_en_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_ctrlupd_after_dqsosc_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_override_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_ppt2_en_freq3 // @core_ddrc_core_clk
   ,output [1:0] reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3 // @core_ddrc_core_clk
   ,output [8:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3 // @core_ddrc_core_clk
   ,output [((`DDRCTL_LPDDR_EN==1) ? 14 : 12)-1:0] reg_ddrc_t_refi_x1_x32_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_x1_x32_freq3 // @core_ddrc_core_clk
   ,output [3:0] reg_ddrc_refresh_margin_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_refresh_to_x1_sel_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_t_refi_x1_sel_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfc_min_ab_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2pbr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_t_pbr2act_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_refresh_to_ab_x32_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer0_start_value_x32_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_refresh_timer1_start_value_x32_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_t_rfmpb_freq3 // @core_ddrc_core_clk
   ,output [13:0] reg_ddrc_t_zq_long_nop_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_short_nop_freq3 // @core_ddrc_core_clk
   ,output [19:0] reg_ddrc_t_zq_short_interval_x1024_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_t_zq_reset_nop_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_t_zq_stop_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_enable_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_dqsosc_interval_unit_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_dqsosc_interval_freq3 // @core_ddrc_core_clk
   ,output [31:0] reg_ddrc_mr4_read_interval_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_derated_t_rrd_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_derated_t_rp_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_ras_min_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rc_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_derated_t_rcd_write_freq3 // @core_ddrc_core_clk
   ,output [11:0] reg_ddrc_hw_lp_idle_x32_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_dvfsq_enable_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_pageclose_timer_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_rdwr_idle_gap_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_hpr_max_starve_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_hpr_xact_run_length_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_lpr_max_starve_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_lpr_xact_run_length_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_w_max_starve_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_w_xact_run_length_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_frequency_ratio_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_rd_gap_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_diff_rank_wr_gap_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_wr2rd_dr_freq3 // @core_ddrc_core_clk
   ,output [7:0] reg_ddrc_rd2wr_dr_freq3 // @core_ddrc_core_clk
   ,output [6:0] reg_ddrc_powerdown_to_x32_freq3 // @core_ddrc_core_clk
   ,output [9:0] reg_ddrc_selfref_to_x32_freq3 // @core_ddrc_core_clk
   ,output [21:0] reg_ddrc_t_pgm_x1_x1024_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_t_pgm_x1_sel_freq3 // @core_ddrc_core_clk
   ,output [15:0] reg_ddrc_t_pgmpst_x32_freq3 // @core_ddrc_core_clk
   ,output [5:0] reg_ddrc_t_pgm_exit_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_wr_link_ecc_enable_freq3 // @core_ddrc_core_clk
   ,output reg_ddrc_rd_link_ecc_enable_freq3 // @core_ddrc_core_clk


    ,output              ecc_corrected_err_intr
    ,output              ecc_uncorrected_err_intr
    ,output              ecc_ap_err_intr
    ,output                derate_temp_limit_intr_out
    ,output                derate_temp_limit_intr_ret
    ,output [1:0]          derate_temp_limit_intr_fault
    ,input                 ddrc_reg_ecc_ap_err_int
    ,output [1:0]          ecc_ap_err_intr_fault
    ,output                ddrc_reg_ecc_ap_err_stat
    ,output [1:0]                              ecc_corrected_err_intr_fault
    ,output [1:0]                              ecc_uncorrected_err_intr_fault
    ,input  [ECC_CORRECTED_ERR_WIDTH-1:0]      ddrc_reg_ecc_corrected_err_int
    ,input  [ECC_UNCORRECTED_ERR_WIDTH-1:0]    ddrc_reg_ecc_uncorrected_err_int
    ,output [ECC_CORRECTED_ERR_WIDTH-1:0]      ddrc_reg_ecc_corrected_err_stat
    ,output [ECC_UNCORRECTED_ERR_WIDTH-1:0]    ddrc_reg_ecc_uncorrected_err_stat
    ,input  [ECC_CORRECTED_BIT_NUM_WIDTH-1:0]  ddrc_reg_ecc_corrected_bit_num_int
    ,output [ECC_CORRECTED_BIT_NUM_WIDTH-1:0]  ddrc_reg_ecc_corrected_bit_num_stat
    ,input  [1:0]                              ddrc_reg_sbr_read_ecc_err_int
    ,output [1:0]                              ddrc_reg_sbr_read_ecc_err_stat
    ,input  [3:0]                              ddrc_reg_rd_linkecc_uncorr_err_intr
    ,input  [3:0]                              ddrc_reg_rd_linkecc_corr_err_intr
    ,output [1:0]                              rd_linkecc_uncorr_err_intr_fault
    ,output [1:0]                              rd_linkecc_corr_err_intr_fault
    ,output                                    rd_linkecc_uncorr_err_intr
    ,output                                    rd_linkecc_corr_err_intr
    ,output [3:0]                              ddrc_reg_rd_link_ecc_uncorr_err_stat
    ,output [3:0]                              ddrc_reg_rd_link_ecc_corr_err_stat



    );

   localparam REG_WIDTH = `UMCTL2_REGS_REG_WIDTH;

   localparam N_APBFSMSTAT=
                           5;   

   // No of bits in the one-hot addr
   localparam RWSELWIDTH = RW_REGS;
      
   wire [N_APBFSMSTAT-1:0] apb_slv_cs_unused;
   wire [N_APBFSMSTAT-1:0] apb_slv_ns;
   wire                    write_en_s0;
   wire                    recalc_parity;
   wire [RWSELWIDTH-1:0]   rwselect;
   wire                    write_en_pulse;
   wire                    write_en;
   wire                    store_rqst;
   wire                    set_async_reg;
   wire                    ack_async_reg;
   
  wire pclk_derate_temp_limit_intr;
  reg  r_derate_temp_limit_intr_force;
  always @(posedge pclk or negedge presetn) begin
    if (!presetn) begin
      r_derate_temp_limit_intr_force <= 1'b0;
    end
    else if (reg_ddrc_derate_temp_limit_intr_force | (r_derate_temp_limit_intr_force & ~reg_ddrc_derate_temp_limit_intr_clr)) begin
      r_derate_temp_limit_intr_force <= 1'b1;
    end
    else begin
      r_derate_temp_limit_intr_force <= 1'b0;
    end
  end
    assign derate_temp_limit_intr_ret   = (r_derate_temp_limit_intr_force | pclk_derate_temp_limit_intr); // Passed to DERATESTAT.derate_temp_limit_intr status register through TOP
    //assign derate_temp_limit_intr_out   = (r_derate_temp_limit_intr_force | pclk_derate_temp_limit_intr) & reg_ddrc_derate_temp_limit_intr_en;
    //assign derate_temp_limit_intr_fault = pclk_derate_temp_limit_intr;
    DWC_ddrctl_antivalent_reg
     U_derate_temp_limit_intr_fault (
       .clk                       (pclk)
      ,.rstn                      (presetn)
      ,.fault_intr                (pclk_derate_temp_limit_intr)
      ,.intr                      ((r_derate_temp_limit_intr_force | pclk_derate_temp_limit_intr))
      ,.intr_en                   (reg_ddrc_derate_temp_limit_intr_en)
      ,.antivalent_fault_intr_out (derate_temp_limit_intr_fault)
      ,.intr_out                  (derate_temp_limit_intr_out)
    );    
 



    wire    [ECC_CORRECTED_ERR_WIDTH-1:0]      pclk_ddrc_reg_ecc_corrected_err;
    wire    [ECC_UNCORRECTED_ERR_WIDTH-1:0]    pclk_ddrc_reg_ecc_uncorrected_err;
    wire    [ECC_CORRECTED_BIT_NUM_WIDTH-1:0]  pclk_ddrc_reg_ecc_corrected_bit_num;
    wire                                       ecc_uncorrected_err_intr_en;
    reg                                        pclk_ddrc_reg_ecc_corrected_err_force;
    reg                                        pclk_ddrc_reg_ecc_uncorrected_err_force;
    wire                                       ecc_corrected_err_int; 
    wire                                       ecc_corrected_err_intr_en;
    wire                                       ecc_uncorrected_err_int; 
    wire                                       ecc_corrected_err_fault_int; 
    wire                                       ecc_uncorrected_err_fault_int;    
    assign  ddrc_reg_ecc_corrected_bit_num_stat = pclk_ddrc_reg_ecc_corrected_bit_num;





  wire pclk_ddrc_reg_ecc_ap_err;
  reg  pclk_ddrc_reg_ecc_ap_err_force;
  wire ecc_ap_err_intr_en;




reg           pclk_ddrc_reg_rd_link_ecc_corr_err_force;
wire [3:0]    pclk_ddrc_reg_rd_linkecc_corr_err_int;
//wire [3:0]    ddrc_reg_rd_link_ecc_corr_err_stat;
wire          rd_link_kecc_corr_err_int;
wire          rd_link_kecc_corr_err_int_fault;
wire          rd_link_ecc_corr_intr_en;

reg           pclk_ddrc_reg_rd_link_ecc_uncorr_err_force;
wire [3:0]    pclk_ddrc_reg_rd_linkecc_uncorr_err_int;
//wire [3:0]    ddrc_reg_rd_link_ecc_uncorr_err_stat;
wire          rd_link_kecc_uncorr_err_int;
wire          rd_link_kecc_uncorr_err_int_fault;
wire          rd_link_ecc_uncorr_intr_en;



   wire [REG_WIDTH -1:0] r0_mstr0;
   wire [REG_WIDTH -1:0] r2_mstr2;
   wire [REG_WIDTH -1:0] r4_mstr4;
   wire [REG_WIDTH -1:0] r5_stat;
   wire [REG_WIDTH -1:0] r8_mrctrl0;
   wire reg_ddrc_mrr_done_clr_ack_pclk;
   wire reg_ddrc_mr_wr_ack_pclk;
   wire ff_regb_ddrc_ch0_mr_wr_saved;
   wire [REG_WIDTH -1:0] r9_mrctrl1;
   wire [REG_WIDTH -1:0] r11_mrstat;
   wire ddrc_reg_mr_wr_busy_int;
   wire [REG_WIDTH -1:0] r12_mrrdata0;
   wire [REG_WIDTH -1:0] r13_mrrdata1;
   wire [REG_WIDTH -1:0] r14_deratectl0;
   wire [REG_WIDTH -1:0] r15_deratectl1;
   wire [REG_WIDTH -1:0] r16_deratectl2;
   wire [REG_WIDTH -1:0] r19_deratectl5;
   wire reg_ddrc_derate_temp_limit_intr_clr_ack_pclk;
   wire reg_ddrc_derate_temp_limit_intr_force_ack_pclk;
   wire [REG_WIDTH -1:0] r20_deratectl6;
   wire [REG_WIDTH -1:0] r22_deratestat0;
   wire [REG_WIDTH -1:0] r24_deratedbgctl;
   wire [REG_WIDTH -1:0] r25_deratedbgstat;
   wire [REG_WIDTH -1:0] r26_pwrctl;
   wire [REG_WIDTH -1:0] r27_hwlpctl;
   wire [REG_WIDTH -1:0] r29_clkgatectl;
   wire [REG_WIDTH -1:0] r30_rfshmod0;
   wire [REG_WIDTH -1:0] r32_rfshctl0;
   wire [REG_WIDTH -1:0] r33_rfmmod0;
   wire [REG_WIDTH -1:0] r34_rfmmod1;
   wire [REG_WIDTH -1:0] r35_rfmctl;
   wire [REG_WIDTH -1:0] r36_rfmstat;
   wire [REG_WIDTH -1:0] r37_zqctl0;
   wire [REG_WIDTH -1:0] r38_zqctl1;
   wire reg_ddrc_zq_reset_ack_pclk;
   wire ff_regb_ddrc_ch0_zq_reset_saved;
   wire [REG_WIDTH -1:0] r39_zqctl2;
   wire [REG_WIDTH -1:0] r40_zqstat;
   wire ddrc_reg_zq_reset_busy_int;
   wire [REG_WIDTH -1:0] r41_dqsoscruntime;
   wire [REG_WIDTH -1:0] r42_dqsoscstat0;
   wire [REG_WIDTH -1:0] r43_dqsosccfg0;
   wire [REG_WIDTH -1:0] r45_sched0;
   wire [REG_WIDTH -1:0] r46_sched1;
   wire [REG_WIDTH -1:0] r48_sched3;
   wire [REG_WIDTH -1:0] r49_sched4;
   wire [REG_WIDTH -1:0] r50_sched5;
   wire [REG_WIDTH -1:0] r51_hwffcctl;
   wire [REG_WIDTH -1:0] r52_hwffcstat;
   wire [REG_WIDTH -1:0] r62_dfilpcfg0;
   wire [REG_WIDTH -1:0] r63_dfiupd0;
   wire [REG_WIDTH -1:0] r65_dfimisc;
   wire [REG_WIDTH -1:0] r66_dfistat;
   wire [REG_WIDTH -1:0] r67_dfiphymstr;
   wire [REG_WIDTH -1:0] r77_poisoncfg;
   wire reg_ddrc_wr_poison_intr_clr_ack_pclk;
   wire reg_ddrc_rd_poison_intr_clr_ack_pclk;
   wire [REG_WIDTH -1:0] r78_poisonstat;
   wire [REG_WIDTH -1:0] r79_ecccfg0;
   wire [REG_WIDTH -1:0] r80_ecccfg1;
   wire [REG_WIDTH -1:0] r81_eccstat;
   wire [REG_WIDTH -1:0] r82_eccctl;
   wire reg_ddrc_ecc_corrected_err_clr_ack_pclk;
   wire reg_ddrc_ecc_uncorrected_err_clr_ack_pclk;
   wire reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk;
   wire reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk;
   wire reg_ddrc_ecc_ap_err_intr_clr_ack_pclk;
   wire reg_ddrc_ecc_corrected_err_intr_force_ack_pclk;
   wire reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk;
   wire reg_ddrc_ecc_ap_err_intr_force_ack_pclk;
   wire [REG_WIDTH -1:0] r83_eccerrcnt;
   wire [REG_WIDTH -1:0] r84_ecccaddr0;
   wire [REG_WIDTH -1:0] r85_ecccaddr1;
   wire [REG_WIDTH -1:0] r86_ecccsyn0;
   wire [REG_WIDTH -1:0] r87_ecccsyn1;
   wire [REG_WIDTH -1:0] r88_ecccsyn2;
   wire [REG_WIDTH -1:0] r89_eccbitmask0;
   wire [REG_WIDTH -1:0] r90_eccbitmask1;
   wire [REG_WIDTH -1:0] r91_eccbitmask2;
   wire [REG_WIDTH -1:0] r92_eccuaddr0;
   wire [REG_WIDTH -1:0] r93_eccuaddr1;
   wire [REG_WIDTH -1:0] r94_eccusyn0;
   wire [REG_WIDTH -1:0] r95_eccusyn1;
   wire [REG_WIDTH -1:0] r96_eccusyn2;
   wire [REG_WIDTH -1:0] r97_eccpoisonaddr0;
   wire [REG_WIDTH -1:0] r98_eccpoisonaddr1;
   wire [REG_WIDTH -1:0] r101_eccpoisonpat0;
   wire [REG_WIDTH -1:0] r103_eccpoisonpat2;
   wire [REG_WIDTH -1:0] r104_eccapstat;
   wire [REG_WIDTH -1:0] r161_lnkeccctl1;
   wire reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk;
   wire reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk;
   wire reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk;
   wire reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk;
   wire reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk;
   wire reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk;
   wire [REG_WIDTH -1:0] r162_lnkeccpoisonctl0;
   wire [REG_WIDTH -1:0] r163_lnkeccpoisonstat;
   wire [REG_WIDTH -1:0] r164_lnkeccindex;
   wire [REG_WIDTH -1:0] r165_lnkeccerrcnt0;
   wire [REG_WIDTH -1:0] r166_lnkeccerrstat;
   wire [REG_WIDTH -1:0] r175_lnkecccaddr0;
   wire [REG_WIDTH -1:0] r176_lnkecccaddr1;
   wire [REG_WIDTH -1:0] r177_lnkeccuaddr0;
   wire [REG_WIDTH -1:0] r178_lnkeccuaddr1;
   wire [REG_WIDTH -1:0] r234_opctrl0;
   wire [REG_WIDTH -1:0] r235_opctrl1;
   wire [REG_WIDTH -1:0] r236_opctrlcam;
   wire [REG_WIDTH -1:0] r237_opctrlcmd;
   wire reg_ddrc_zq_calib_short_ack_pclk;
   wire ff_regb_ddrc_ch0_zq_calib_short_saved;
   wire reg_ddrc_ctrlupd_ack_pclk;
   wire ff_regb_ddrc_ch0_ctrlupd_saved;
   wire [REG_WIDTH -1:0] r238_opctrlstat;
   wire ddrc_reg_zq_calib_short_busy_int;
   wire ddrc_reg_ctrlupd_busy_int;
   wire [REG_WIDTH -1:0] r239_opctrlcam1;
   wire [REG_WIDTH -1:0] r240_oprefctrl0;
   wire reg_ddrc_rank0_refresh_ack_pclk;
   wire ff_regb_ddrc_ch0_rank0_refresh_saved;
   wire reg_ddrc_rank1_refresh_ack_pclk;
   wire ff_regb_ddrc_ch0_rank1_refresh_saved;
   wire [REG_WIDTH -1:0] r242_oprefstat0;
   wire ddrc_reg_rank0_refresh_busy_int;
   wire ddrc_reg_rank1_refresh_busy_int;
   wire [REG_WIDTH -1:0] r249_swctl;
   wire [REG_WIDTH -1:0] r250_swstat;
   wire [REG_WIDTH -1:0] r253_rankctl;
   wire [REG_WIDTH -1:0] r254_dbictl;
   wire [REG_WIDTH -1:0] r256_odtmap;
   wire [REG_WIDTH -1:0] r257_datactl0;
   wire [REG_WIDTH -1:0] r258_swctlstatic;
   wire [REG_WIDTH -1:0] r259_cgctl;
   wire [REG_WIDTH -1:0] r260_inittmg0;
   wire [REG_WIDTH -1:0] r285_ppt2ctrl0;
   wire reg_ddrc_ppt2_burst_ack_pclk;
   wire ff_regb_ddrc_ch0_ppt2_burst_saved;
   wire [REG_WIDTH -1:0] r286_ppt2stat0;
   wire ddrc_reg_ppt2_burst_busy_int;
   wire [REG_WIDTH -1:0] r289_ddrctl_ver_number;
   wire [REG_WIDTH -1:0] r290_ddrctl_ver_type;
   wire [REG_WIDTH -1:0] r495_addrmap1_map0;
   wire [REG_WIDTH -1:0] r497_addrmap3_map0;
   wire [REG_WIDTH -1:0] r498_addrmap4_map0;
   wire [REG_WIDTH -1:0] r499_addrmap5_map0;
   wire [REG_WIDTH -1:0] r500_addrmap6_map0;
   wire [REG_WIDTH -1:0] r501_addrmap7_map0;
   wire [REG_WIDTH -1:0] r502_addrmap8_map0;
   wire [REG_WIDTH -1:0] r503_addrmap9_map0;
   wire [REG_WIDTH -1:0] r504_addrmap10_map0;
   wire [REG_WIDTH -1:0] r505_addrmap11_map0;
   wire [REG_WIDTH -1:0] r506_addrmap12_map0;
   wire [REG_WIDTH -1:0] r521_pccfg_port0;
   wire [REG_WIDTH -1:0] r522_pcfgr_port0;
   wire [REG_WIDTH -1:0] r523_pcfgw_port0;
   wire [REG_WIDTH -1:0] r556_pctrl_port0;
   wire [REG_WIDTH -1:0] r557_pcfgqos0_port0;
   wire [REG_WIDTH -1:0] r558_pcfgqos1_port0;
   wire [REG_WIDTH -1:0] r559_pcfgwqos0_port0;
   wire [REG_WIDTH -1:0] r560_pcfgwqos1_port0;
   wire [REG_WIDTH -1:0] r569_sbrctl_port0;
   wire [REG_WIDTH -1:0] r570_sbrstat_port0;
   wire [REG_WIDTH -1:0] r571_sbrwdata0_port0;
   wire [REG_WIDTH -1:0] r573_sbrstart0_port0;
   wire [REG_WIDTH -1:0] r574_sbrstart1_port0;
   wire [REG_WIDTH -1:0] r575_sbrrange0_port0;
   wire [REG_WIDTH -1:0] r576_sbrrange1_port0;
   wire [REG_WIDTH -1:0] r582_pstat_port0;
   wire [REG_WIDTH -1:0] r1929_dramset1tmg0_freq0;
   wire [REG_WIDTH -1:0] r1930_dramset1tmg1_freq0;
   wire [REG_WIDTH -1:0] r1931_dramset1tmg2_freq0;
   wire [REG_WIDTH -1:0] r1932_dramset1tmg3_freq0;
   wire [REG_WIDTH -1:0] r1933_dramset1tmg4_freq0;
   wire [REG_WIDTH -1:0] r1934_dramset1tmg5_freq0;
   wire [REG_WIDTH -1:0] r1935_dramset1tmg6_freq0;
   wire [REG_WIDTH -1:0] r1936_dramset1tmg7_freq0;
   wire [REG_WIDTH -1:0] r1938_dramset1tmg9_freq0;
   wire [REG_WIDTH -1:0] r1941_dramset1tmg12_freq0;
   wire [REG_WIDTH -1:0] r1942_dramset1tmg13_freq0;
   wire [REG_WIDTH -1:0] r1943_dramset1tmg14_freq0;
   wire [REG_WIDTH -1:0] r1946_dramset1tmg17_freq0;
   wire [REG_WIDTH -1:0] r1951_dramset1tmg23_freq0;
   wire [REG_WIDTH -1:0] r1952_dramset1tmg24_freq0;
   wire [REG_WIDTH -1:0] r1953_dramset1tmg25_freq0;
   wire [REG_WIDTH -1:0] r1958_dramset1tmg30_freq0;
   wire [REG_WIDTH -1:0] r1960_dramset1tmg32_freq0;
   wire [REG_WIDTH -1:0] r1991_initmr0_freq0;
   wire [REG_WIDTH -1:0] r1992_initmr1_freq0;
   wire [REG_WIDTH -1:0] r1993_initmr2_freq0;
   wire [REG_WIDTH -1:0] r1994_initmr3_freq0;
   wire [REG_WIDTH -1:0] r1995_dfitmg0_freq0;
   wire [REG_WIDTH -1:0] r1996_dfitmg1_freq0;
   wire [REG_WIDTH -1:0] r1997_dfitmg2_freq0;
   wire [REG_WIDTH -1:0] r1999_dfitmg4_freq0;
   wire [REG_WIDTH -1:0] r2000_dfitmg5_freq0;
   wire [REG_WIDTH -1:0] r2001_dfitmg6_freq0;
   wire [REG_WIDTH -1:0] r2003_dfilptmg0_freq0;
   wire [REG_WIDTH -1:0] r2004_dfilptmg1_freq0;
   wire [REG_WIDTH -1:0] r2005_dfiupdtmg0_freq0;
   wire [REG_WIDTH -1:0] r2006_dfiupdtmg1_freq0;
   wire [REG_WIDTH -1:0] r2008_dfiupdtmg2_freq0;
   wire [REG_WIDTH -1:0] r2009_dfiupdtmg3_freq0;
   wire [REG_WIDTH -1:0] r2010_rfshset1tmg0_freq0;
   wire [REG_WIDTH -1:0] r2011_rfshset1tmg1_freq0;
   wire [REG_WIDTH -1:0] r2012_rfshset1tmg2_freq0;
   wire [REG_WIDTH -1:0] r2013_rfshset1tmg3_freq0;
   wire [REG_WIDTH -1:0] r2014_rfshset1tmg4_freq0;
   wire [REG_WIDTH -1:0] r2024_rfmset1tmg0_freq0;
   wire [REG_WIDTH -1:0] r2035_zqset1tmg0_freq0;
   wire [REG_WIDTH -1:0] r2036_zqset1tmg1_freq0;
   wire [REG_WIDTH -1:0] r2037_zqset1tmg2_freq0;
   wire [REG_WIDTH -1:0] r2046_dqsoscctl0_freq0;
   wire [REG_WIDTH -1:0] r2047_derateint_freq0;
   wire [REG_WIDTH -1:0] r2048_derateval0_freq0;
   wire [REG_WIDTH -1:0] r2049_derateval1_freq0;
   wire [REG_WIDTH -1:0] r2050_hwlptmg0_freq0;
   wire [REG_WIDTH -1:0] r2051_dvfsctl0_freq0;
   wire [REG_WIDTH -1:0] r2052_schedtmg0_freq0;
   wire [REG_WIDTH -1:0] r2053_perfhpr1_freq0;
   wire [REG_WIDTH -1:0] r2054_perflpr1_freq0;
   wire [REG_WIDTH -1:0] r2055_perfwr1_freq0;
   wire [REG_WIDTH -1:0] r2056_tmgcfg_freq0;
   wire [REG_WIDTH -1:0] r2057_ranktmg0_freq0;
   wire [REG_WIDTH -1:0] r2058_ranktmg1_freq0;
   wire [REG_WIDTH -1:0] r2059_pwrtmg_freq0;
   wire [REG_WIDTH -1:0] r2065_ddr4pprtmg0_freq0;
   wire [REG_WIDTH -1:0] r2066_ddr4pprtmg1_freq0;
   wire [REG_WIDTH -1:0] r2067_lnkeccctl0_freq0;
   wire [REG_WIDTH -1:0] r2201_dramset1tmg0_freq1;
   wire [REG_WIDTH -1:0] r2202_dramset1tmg1_freq1;
   wire [REG_WIDTH -1:0] r2203_dramset1tmg2_freq1;
   wire [REG_WIDTH -1:0] r2204_dramset1tmg3_freq1;
   wire [REG_WIDTH -1:0] r2205_dramset1tmg4_freq1;
   wire [REG_WIDTH -1:0] r2206_dramset1tmg5_freq1;
   wire [REG_WIDTH -1:0] r2207_dramset1tmg6_freq1;
   wire [REG_WIDTH -1:0] r2208_dramset1tmg7_freq1;
   wire [REG_WIDTH -1:0] r2210_dramset1tmg9_freq1;
   wire [REG_WIDTH -1:0] r2213_dramset1tmg12_freq1;
   wire [REG_WIDTH -1:0] r2214_dramset1tmg13_freq1;
   wire [REG_WIDTH -1:0] r2215_dramset1tmg14_freq1;
   wire [REG_WIDTH -1:0] r2218_dramset1tmg17_freq1;
   wire [REG_WIDTH -1:0] r2223_dramset1tmg23_freq1;
   wire [REG_WIDTH -1:0] r2224_dramset1tmg24_freq1;
   wire [REG_WIDTH -1:0] r2225_dramset1tmg25_freq1;
   wire [REG_WIDTH -1:0] r2230_dramset1tmg30_freq1;
   wire [REG_WIDTH -1:0] r2232_dramset1tmg32_freq1;
   wire [REG_WIDTH -1:0] r2263_initmr0_freq1;
   wire [REG_WIDTH -1:0] r2264_initmr1_freq1;
   wire [REG_WIDTH -1:0] r2265_initmr2_freq1;
   wire [REG_WIDTH -1:0] r2266_initmr3_freq1;
   wire [REG_WIDTH -1:0] r2267_dfitmg0_freq1;
   wire [REG_WIDTH -1:0] r2268_dfitmg1_freq1;
   wire [REG_WIDTH -1:0] r2269_dfitmg2_freq1;
   wire [REG_WIDTH -1:0] r2271_dfitmg4_freq1;
   wire [REG_WIDTH -1:0] r2272_dfitmg5_freq1;
   wire [REG_WIDTH -1:0] r2273_dfitmg6_freq1;
   wire [REG_WIDTH -1:0] r2275_dfiupdtmg1_freq1;
   wire [REG_WIDTH -1:0] r2276_dfiupdtmg2_freq1;
   wire [REG_WIDTH -1:0] r2277_dfiupdtmg3_freq1;
   wire [REG_WIDTH -1:0] r2278_rfshset1tmg0_freq1;
   wire [REG_WIDTH -1:0] r2279_rfshset1tmg1_freq1;
   wire [REG_WIDTH -1:0] r2280_rfshset1tmg2_freq1;
   wire [REG_WIDTH -1:0] r2281_rfshset1tmg3_freq1;
   wire [REG_WIDTH -1:0] r2282_rfshset1tmg4_freq1;
   wire [REG_WIDTH -1:0] r2292_rfmset1tmg0_freq1;
   wire [REG_WIDTH -1:0] r2303_zqset1tmg0_freq1;
   wire [REG_WIDTH -1:0] r2304_zqset1tmg1_freq1;
   wire [REG_WIDTH -1:0] r2305_zqset1tmg2_freq1;
   wire [REG_WIDTH -1:0] r2314_dqsoscctl0_freq1;
   wire [REG_WIDTH -1:0] r2315_derateint_freq1;
   wire [REG_WIDTH -1:0] r2316_derateval0_freq1;
   wire [REG_WIDTH -1:0] r2317_derateval1_freq1;
   wire [REG_WIDTH -1:0] r2318_hwlptmg0_freq1;
   wire [REG_WIDTH -1:0] r2319_dvfsctl0_freq1;
   wire [REG_WIDTH -1:0] r2320_schedtmg0_freq1;
   wire [REG_WIDTH -1:0] r2321_perfhpr1_freq1;
   wire [REG_WIDTH -1:0] r2322_perflpr1_freq1;
   wire [REG_WIDTH -1:0] r2323_perfwr1_freq1;
   wire [REG_WIDTH -1:0] r2324_tmgcfg_freq1;
   wire [REG_WIDTH -1:0] r2325_ranktmg0_freq1;
   wire [REG_WIDTH -1:0] r2326_ranktmg1_freq1;
   wire [REG_WIDTH -1:0] r2327_pwrtmg_freq1;
   wire [REG_WIDTH -1:0] r2333_ddr4pprtmg0_freq1;
   wire [REG_WIDTH -1:0] r2334_ddr4pprtmg1_freq1;
   wire [REG_WIDTH -1:0] r2335_lnkeccctl0_freq1;
   wire [REG_WIDTH -1:0] r2469_dramset1tmg0_freq2;
   wire [REG_WIDTH -1:0] r2470_dramset1tmg1_freq2;
   wire [REG_WIDTH -1:0] r2471_dramset1tmg2_freq2;
   wire [REG_WIDTH -1:0] r2472_dramset1tmg3_freq2;
   wire [REG_WIDTH -1:0] r2473_dramset1tmg4_freq2;
   wire [REG_WIDTH -1:0] r2474_dramset1tmg5_freq2;
   wire [REG_WIDTH -1:0] r2475_dramset1tmg6_freq2;
   wire [REG_WIDTH -1:0] r2476_dramset1tmg7_freq2;
   wire [REG_WIDTH -1:0] r2478_dramset1tmg9_freq2;
   wire [REG_WIDTH -1:0] r2481_dramset1tmg12_freq2;
   wire [REG_WIDTH -1:0] r2482_dramset1tmg13_freq2;
   wire [REG_WIDTH -1:0] r2483_dramset1tmg14_freq2;
   wire [REG_WIDTH -1:0] r2486_dramset1tmg17_freq2;
   wire [REG_WIDTH -1:0] r2491_dramset1tmg23_freq2;
   wire [REG_WIDTH -1:0] r2492_dramset1tmg24_freq2;
   wire [REG_WIDTH -1:0] r2493_dramset1tmg25_freq2;
   wire [REG_WIDTH -1:0] r2498_dramset1tmg30_freq2;
   wire [REG_WIDTH -1:0] r2500_dramset1tmg32_freq2;
   wire [REG_WIDTH -1:0] r2531_initmr0_freq2;
   wire [REG_WIDTH -1:0] r2532_initmr1_freq2;
   wire [REG_WIDTH -1:0] r2533_initmr2_freq2;
   wire [REG_WIDTH -1:0] r2534_initmr3_freq2;
   wire [REG_WIDTH -1:0] r2535_dfitmg0_freq2;
   wire [REG_WIDTH -1:0] r2536_dfitmg1_freq2;
   wire [REG_WIDTH -1:0] r2537_dfitmg2_freq2;
   wire [REG_WIDTH -1:0] r2539_dfitmg4_freq2;
   wire [REG_WIDTH -1:0] r2540_dfitmg5_freq2;
   wire [REG_WIDTH -1:0] r2541_dfitmg6_freq2;
   wire [REG_WIDTH -1:0] r2543_dfiupdtmg1_freq2;
   wire [REG_WIDTH -1:0] r2544_dfiupdtmg2_freq2;
   wire [REG_WIDTH -1:0] r2545_dfiupdtmg3_freq2;
   wire [REG_WIDTH -1:0] r2546_rfshset1tmg0_freq2;
   wire [REG_WIDTH -1:0] r2547_rfshset1tmg1_freq2;
   wire [REG_WIDTH -1:0] r2548_rfshset1tmg2_freq2;
   wire [REG_WIDTH -1:0] r2549_rfshset1tmg3_freq2;
   wire [REG_WIDTH -1:0] r2550_rfshset1tmg4_freq2;
   wire [REG_WIDTH -1:0] r2560_rfmset1tmg0_freq2;
   wire [REG_WIDTH -1:0] r2571_zqset1tmg0_freq2;
   wire [REG_WIDTH -1:0] r2572_zqset1tmg1_freq2;
   wire [REG_WIDTH -1:0] r2573_zqset1tmg2_freq2;
   wire [REG_WIDTH -1:0] r2582_dqsoscctl0_freq2;
   wire [REG_WIDTH -1:0] r2583_derateint_freq2;
   wire [REG_WIDTH -1:0] r2584_derateval0_freq2;
   wire [REG_WIDTH -1:0] r2585_derateval1_freq2;
   wire [REG_WIDTH -1:0] r2586_hwlptmg0_freq2;
   wire [REG_WIDTH -1:0] r2587_dvfsctl0_freq2;
   wire [REG_WIDTH -1:0] r2588_schedtmg0_freq2;
   wire [REG_WIDTH -1:0] r2589_perfhpr1_freq2;
   wire [REG_WIDTH -1:0] r2590_perflpr1_freq2;
   wire [REG_WIDTH -1:0] r2591_perfwr1_freq2;
   wire [REG_WIDTH -1:0] r2592_tmgcfg_freq2;
   wire [REG_WIDTH -1:0] r2593_ranktmg0_freq2;
   wire [REG_WIDTH -1:0] r2594_ranktmg1_freq2;
   wire [REG_WIDTH -1:0] r2595_pwrtmg_freq2;
   wire [REG_WIDTH -1:0] r2601_ddr4pprtmg0_freq2;
   wire [REG_WIDTH -1:0] r2602_ddr4pprtmg1_freq2;
   wire [REG_WIDTH -1:0] r2603_lnkeccctl0_freq2;
   wire [REG_WIDTH -1:0] r2737_dramset1tmg0_freq3;
   wire [REG_WIDTH -1:0] r2738_dramset1tmg1_freq3;
   wire [REG_WIDTH -1:0] r2739_dramset1tmg2_freq3;
   wire [REG_WIDTH -1:0] r2740_dramset1tmg3_freq3;
   wire [REG_WIDTH -1:0] r2741_dramset1tmg4_freq3;
   wire [REG_WIDTH -1:0] r2742_dramset1tmg5_freq3;
   wire [REG_WIDTH -1:0] r2743_dramset1tmg6_freq3;
   wire [REG_WIDTH -1:0] r2744_dramset1tmg7_freq3;
   wire [REG_WIDTH -1:0] r2746_dramset1tmg9_freq3;
   wire [REG_WIDTH -1:0] r2749_dramset1tmg12_freq3;
   wire [REG_WIDTH -1:0] r2750_dramset1tmg13_freq3;
   wire [REG_WIDTH -1:0] r2751_dramset1tmg14_freq3;
   wire [REG_WIDTH -1:0] r2754_dramset1tmg17_freq3;
   wire [REG_WIDTH -1:0] r2759_dramset1tmg23_freq3;
   wire [REG_WIDTH -1:0] r2760_dramset1tmg24_freq3;
   wire [REG_WIDTH -1:0] r2761_dramset1tmg25_freq3;
   wire [REG_WIDTH -1:0] r2766_dramset1tmg30_freq3;
   wire [REG_WIDTH -1:0] r2768_dramset1tmg32_freq3;
   wire [REG_WIDTH -1:0] r2799_initmr0_freq3;
   wire [REG_WIDTH -1:0] r2800_initmr1_freq3;
   wire [REG_WIDTH -1:0] r2801_initmr2_freq3;
   wire [REG_WIDTH -1:0] r2802_initmr3_freq3;
   wire [REG_WIDTH -1:0] r2803_dfitmg0_freq3;
   wire [REG_WIDTH -1:0] r2804_dfitmg1_freq3;
   wire [REG_WIDTH -1:0] r2805_dfitmg2_freq3;
   wire [REG_WIDTH -1:0] r2807_dfitmg4_freq3;
   wire [REG_WIDTH -1:0] r2808_dfitmg5_freq3;
   wire [REG_WIDTH -1:0] r2809_dfitmg6_freq3;
   wire [REG_WIDTH -1:0] r2811_dfiupdtmg1_freq3;
   wire [REG_WIDTH -1:0] r2812_dfiupdtmg2_freq3;
   wire [REG_WIDTH -1:0] r2813_dfiupdtmg3_freq3;
   wire [REG_WIDTH -1:0] r2814_rfshset1tmg0_freq3;
   wire [REG_WIDTH -1:0] r2815_rfshset1tmg1_freq3;
   wire [REG_WIDTH -1:0] r2816_rfshset1tmg2_freq3;
   wire [REG_WIDTH -1:0] r2817_rfshset1tmg3_freq3;
   wire [REG_WIDTH -1:0] r2818_rfshset1tmg4_freq3;
   wire [REG_WIDTH -1:0] r2828_rfmset1tmg0_freq3;
   wire [REG_WIDTH -1:0] r2839_zqset1tmg0_freq3;
   wire [REG_WIDTH -1:0] r2840_zqset1tmg1_freq3;
   wire [REG_WIDTH -1:0] r2841_zqset1tmg2_freq3;
   wire [REG_WIDTH -1:0] r2850_dqsoscctl0_freq3;
   wire [REG_WIDTH -1:0] r2851_derateint_freq3;
   wire [REG_WIDTH -1:0] r2852_derateval0_freq3;
   wire [REG_WIDTH -1:0] r2853_derateval1_freq3;
   wire [REG_WIDTH -1:0] r2854_hwlptmg0_freq3;
   wire [REG_WIDTH -1:0] r2855_dvfsctl0_freq3;
   wire [REG_WIDTH -1:0] r2856_schedtmg0_freq3;
   wire [REG_WIDTH -1:0] r2857_perfhpr1_freq3;
   wire [REG_WIDTH -1:0] r2858_perflpr1_freq3;
   wire [REG_WIDTH -1:0] r2859_perfwr1_freq3;
   wire [REG_WIDTH -1:0] r2860_tmgcfg_freq3;
   wire [REG_WIDTH -1:0] r2861_ranktmg0_freq3;
   wire [REG_WIDTH -1:0] r2862_ranktmg1_freq3;
   wire [REG_WIDTH -1:0] r2863_pwrtmg_freq3;
   wire [REG_WIDTH -1:0] r2869_ddr4pprtmg0_freq3;
   wire [REG_WIDTH -1:0] r2870_ddr4pprtmg1_freq3;
   wire [REG_WIDTH -1:0] r2871_lnkeccctl0_freq3;

 `ifdef SNPS_ASSERT_ON
 `ifndef SYNTHESIS
    property p_reg_ddrc_mr_wr_postponed_and_ddrc_reg_mr_wr_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_MRSTAT_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_MRSTAT address
           reg_ddrc_mr_wr == 1'b1) // and reg_ddrc_mr_wr is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_mr_wr_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_mr_wr_postponed_and_ddrc_reg_mr_wr_busy : assert property (p_reg_ddrc_mr_wr_postponed_and_ddrc_reg_mr_wr_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_MRSTAT is read while postponed reg_ddrc_mr_wr is executed", $realtime);
 
    property p_reg_ddrc_zq_reset_postponed_and_ddrc_reg_zq_reset_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_ZQSTAT_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_ZQSTAT address
           reg_ddrc_zq_reset == 1'b1) // and reg_ddrc_zq_reset is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_zq_reset_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_zq_reset_postponed_and_ddrc_reg_zq_reset_busy : assert property (p_reg_ddrc_zq_reset_postponed_and_ddrc_reg_zq_reset_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_ZQSTAT is read while postponed reg_ddrc_zq_reset is executed", $realtime);
 
    property p_reg_ddrc_zq_calib_short_postponed_and_ddrc_reg_zq_calib_short_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_OPCTRLSTAT_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_OPCTRLSTAT address
           reg_ddrc_zq_calib_short == 1'b1) // and reg_ddrc_zq_calib_short is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_zq_calib_short_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_zq_calib_short_postponed_and_ddrc_reg_zq_calib_short_busy : assert property (p_reg_ddrc_zq_calib_short_postponed_and_ddrc_reg_zq_calib_short_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_OPCTRLSTAT is read while postponed reg_ddrc_zq_calib_short is executed", $realtime);
 
    property p_reg_ddrc_ctrlupd_postponed_and_ddrc_reg_ctrlupd_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_OPCTRLSTAT_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_OPCTRLSTAT address
           reg_ddrc_ctrlupd == 1'b1) // and reg_ddrc_ctrlupd is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_ctrlupd_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_ctrlupd_postponed_and_ddrc_reg_ctrlupd_busy : assert property (p_reg_ddrc_ctrlupd_postponed_and_ddrc_reg_ctrlupd_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_OPCTRLSTAT is read while postponed reg_ddrc_ctrlupd is executed", $realtime);
 
    property p_reg_ddrc_rank0_refresh_postponed_and_ddrc_reg_rank0_refresh_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_OPREFSTAT0_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_OPREFSTAT0 address
           reg_ddrc_rank0_refresh == 1'b1) // and reg_ddrc_rank0_refresh is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_rank0_refresh_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_rank0_refresh_postponed_and_ddrc_reg_rank0_refresh_busy : assert property (p_reg_ddrc_rank0_refresh_postponed_and_ddrc_reg_rank0_refresh_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_OPREFSTAT0 is read while postponed reg_ddrc_rank0_refresh is executed", $realtime);
 
    property p_reg_ddrc_rank1_refresh_postponed_and_ddrc_reg_rank1_refresh_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_OPREFSTAT0_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_OPREFSTAT0 address
           reg_ddrc_rank1_refresh == 1'b1) // and reg_ddrc_rank1_refresh is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_rank1_refresh_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_rank1_refresh_postponed_and_ddrc_reg_rank1_refresh_busy : assert property (p_reg_ddrc_rank1_refresh_postponed_and_ddrc_reg_rank1_refresh_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_OPREFSTAT0 is read while postponed reg_ddrc_rank1_refresh is executed", $realtime);
 
    property p_reg_ddrc_ppt2_burst_postponed_and_ddrc_reg_ppt2_burst_busy;
       @(posedge pclk) disable iff(!presetn)
          (adrdec.apb_slv_ns == adrdec.ADDRDECODE && // during address phase
           adrdec.reg_addr == adrdec.REGB_DDRC_CH0_PPT2STAT0_ADDR[adrdec.REG_AW-1:0] && // when accessing (reading) at REGB_DDRC_CH0_PPT2STAT0 address
           reg_ddrc_ppt2_burst == 1'b1) // and reg_ddrc_ppt2_burst is set high at the output of APB block
          |-> slvif.ff_regb_ddrc_ch0_ppt2_burst_saved==0; // it should not be the execution of a postponed command.
    endproperty
 
 //   a_reg_ddrc_ppt2_burst_postponed_and_ddrc_reg_ppt2_burst_busy : assert property (p_reg_ddrc_ppt2_burst_postponed_and_ddrc_reg_ppt2_burst_busy) else
 //      $display("-> %0t ERROR: REGB_DDRC_CH0_PPT2STAT0 is read while postponed reg_ddrc_ppt2_burst is executed", $realtime);
 
 `endif // SYNTHESIS
 `endif // SNPS_ASSERT_ON


//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current implementation.
   assign set_async_reg = (1'b0

                           ) & write_en;

   assign ack_async_reg =
                        reg_ddrc_derate_temp_limit_intr_clr_ack_pclk |
                        reg_ddrc_derate_temp_limit_intr_force_ack_pclk |

                           1'b0;
//spyglass enable_block W528

wire              psel_int;
wire              pready_int;
wire              pslverr_int;
wire [APB_DW-1:0] prdata_int;
assign psel_int   = psel;
assign pready     = pready_int;
assign pslverr    = pslverr_int;
assign prdata     = prdata_int;

  wire apb_secure;
    assign apb_secure = 1'b0;

   // ----------------------------------------------------------------------------
   // The block performs the address decoding and data multiplexing for the local
   // interface and the configuration registers. The input address is decoded to
   // give a one-hot address that selects the respective register from the bank
   // ----------------------------------------------------------------------------
   DWC_ddrctl_apb_adrdec
   
     #(.APB_AW       (APB_AW),
       .APB_DW       (APB_DW),
       .REG_WIDTH    (REG_WIDTH),
       .N_REGS       (N_REGS),
       .RW_REGS      (RW_REGS),
       .RWSELWIDTH   (RWSELWIDTH),
       .N_APBFSMSTAT (N_APBFSMSTAT)
       )
   adrdec
     (.presetn           (presetn),
      .pclk              (pclk),
      .paddr             (paddr),
      .pwrite            (pwrite),
      .psel              (psel_int),
      .apb_secure        (apb_secure),
      .apb_slv_ns        (apb_slv_ns),
      //----------------------------  
      .rwselect          (rwselect),
      .prdata            (prdata_int),
      .pslverr           (pslverr_int)

      ,.r0_mstr0 (r0_mstr0)
      ,.r2_mstr2 (r2_mstr2)
      ,.r4_mstr4 (r4_mstr4)
      ,.r5_stat (r5_stat)
      ,.r8_mrctrl0 (r8_mrctrl0)
      ,.r9_mrctrl1 (r9_mrctrl1)
      ,.r11_mrstat (r11_mrstat)
      ,.r12_mrrdata0 (r12_mrrdata0)
      ,.r13_mrrdata1 (r13_mrrdata1)
      ,.r14_deratectl0 (r14_deratectl0)
      ,.r15_deratectl1 (r15_deratectl1)
      ,.r16_deratectl2 (r16_deratectl2)
      ,.r19_deratectl5 (r19_deratectl5)
      ,.r20_deratectl6 (r20_deratectl6)
      ,.r22_deratestat0 (r22_deratestat0)
      ,.r24_deratedbgctl (r24_deratedbgctl)
      ,.r25_deratedbgstat (r25_deratedbgstat)
      ,.r26_pwrctl (r26_pwrctl)
      ,.r27_hwlpctl (r27_hwlpctl)
      ,.r29_clkgatectl (r29_clkgatectl)
      ,.r30_rfshmod0 (r30_rfshmod0)
      ,.r32_rfshctl0 (r32_rfshctl0)
      ,.r33_rfmmod0 (r33_rfmmod0)
      ,.r34_rfmmod1 (r34_rfmmod1)
      ,.r35_rfmctl (r35_rfmctl)
      ,.r36_rfmstat (r36_rfmstat)
      ,.r37_zqctl0 (r37_zqctl0)
      ,.r38_zqctl1 (r38_zqctl1)
      ,.r39_zqctl2 (r39_zqctl2)
      ,.r40_zqstat (r40_zqstat)
      ,.r41_dqsoscruntime (r41_dqsoscruntime)
      ,.r42_dqsoscstat0 (r42_dqsoscstat0)
      ,.r43_dqsosccfg0 (r43_dqsosccfg0)
      ,.r45_sched0 (r45_sched0)
      ,.r46_sched1 (r46_sched1)
      ,.r48_sched3 (r48_sched3)
      ,.r49_sched4 (r49_sched4)
      ,.r50_sched5 (r50_sched5)
      ,.r51_hwffcctl (r51_hwffcctl)
      ,.r52_hwffcstat (r52_hwffcstat)
      ,.r62_dfilpcfg0 (r62_dfilpcfg0)
      ,.r63_dfiupd0 (r63_dfiupd0)
      ,.r65_dfimisc (r65_dfimisc)
      ,.r66_dfistat (r66_dfistat)
      ,.r67_dfiphymstr (r67_dfiphymstr)
      ,.r77_poisoncfg (r77_poisoncfg)
      ,.r78_poisonstat (r78_poisonstat)
      ,.r79_ecccfg0 (r79_ecccfg0)
      ,.r80_ecccfg1 (r80_ecccfg1)
      ,.r81_eccstat (r81_eccstat)
      ,.r82_eccctl (r82_eccctl)
      ,.r83_eccerrcnt (r83_eccerrcnt)
      ,.r84_ecccaddr0 (r84_ecccaddr0)
      ,.r85_ecccaddr1 (r85_ecccaddr1)
      ,.r86_ecccsyn0 (r86_ecccsyn0)
      ,.r87_ecccsyn1 (r87_ecccsyn1)
      ,.r88_ecccsyn2 (r88_ecccsyn2)
      ,.r89_eccbitmask0 (r89_eccbitmask0)
      ,.r90_eccbitmask1 (r90_eccbitmask1)
      ,.r91_eccbitmask2 (r91_eccbitmask2)
      ,.r92_eccuaddr0 (r92_eccuaddr0)
      ,.r93_eccuaddr1 (r93_eccuaddr1)
      ,.r94_eccusyn0 (r94_eccusyn0)
      ,.r95_eccusyn1 (r95_eccusyn1)
      ,.r96_eccusyn2 (r96_eccusyn2)
      ,.r97_eccpoisonaddr0 (r97_eccpoisonaddr0)
      ,.r98_eccpoisonaddr1 (r98_eccpoisonaddr1)
      ,.r101_eccpoisonpat0 (r101_eccpoisonpat0)
      ,.r103_eccpoisonpat2 (r103_eccpoisonpat2)
      ,.r104_eccapstat (r104_eccapstat)
      ,.r161_lnkeccctl1 (r161_lnkeccctl1)
      ,.r162_lnkeccpoisonctl0 (r162_lnkeccpoisonctl0)
      ,.r163_lnkeccpoisonstat (r163_lnkeccpoisonstat)
      ,.r164_lnkeccindex (r164_lnkeccindex)
      ,.r165_lnkeccerrcnt0 (r165_lnkeccerrcnt0)
      ,.r166_lnkeccerrstat (r166_lnkeccerrstat)
      ,.r175_lnkecccaddr0 (r175_lnkecccaddr0)
      ,.r176_lnkecccaddr1 (r176_lnkecccaddr1)
      ,.r177_lnkeccuaddr0 (r177_lnkeccuaddr0)
      ,.r178_lnkeccuaddr1 (r178_lnkeccuaddr1)
      ,.r234_opctrl0 (r234_opctrl0)
      ,.r235_opctrl1 (r235_opctrl1)
      ,.r236_opctrlcam (r236_opctrlcam)
      ,.r237_opctrlcmd (r237_opctrlcmd)
      ,.r238_opctrlstat (r238_opctrlstat)
      ,.r239_opctrlcam1 (r239_opctrlcam1)
      ,.r240_oprefctrl0 (r240_oprefctrl0)
      ,.r242_oprefstat0 (r242_oprefstat0)
      ,.r249_swctl (r249_swctl)
      ,.r250_swstat (r250_swstat)
      ,.r253_rankctl (r253_rankctl)
      ,.r254_dbictl (r254_dbictl)
      ,.r256_odtmap (r256_odtmap)
      ,.r257_datactl0 (r257_datactl0)
      ,.r258_swctlstatic (r258_swctlstatic)
      ,.r259_cgctl (r259_cgctl)
      ,.r260_inittmg0 (r260_inittmg0)
      ,.r285_ppt2ctrl0 (r285_ppt2ctrl0)
      ,.r286_ppt2stat0 (r286_ppt2stat0)
      ,.r289_ddrctl_ver_number (r289_ddrctl_ver_number)
      ,.r290_ddrctl_ver_type (r290_ddrctl_ver_type)
      ,.r495_addrmap1_map0 (r495_addrmap1_map0)
      ,.r497_addrmap3_map0 (r497_addrmap3_map0)
      ,.r498_addrmap4_map0 (r498_addrmap4_map0)
      ,.r499_addrmap5_map0 (r499_addrmap5_map0)
      ,.r500_addrmap6_map0 (r500_addrmap6_map0)
      ,.r501_addrmap7_map0 (r501_addrmap7_map0)
      ,.r502_addrmap8_map0 (r502_addrmap8_map0)
      ,.r503_addrmap9_map0 (r503_addrmap9_map0)
      ,.r504_addrmap10_map0 (r504_addrmap10_map0)
      ,.r505_addrmap11_map0 (r505_addrmap11_map0)
      ,.r506_addrmap12_map0 (r506_addrmap12_map0)
      ,.r521_pccfg_port0 (r521_pccfg_port0)
      ,.r522_pcfgr_port0 (r522_pcfgr_port0)
      ,.r523_pcfgw_port0 (r523_pcfgw_port0)
      ,.r556_pctrl_port0 (r556_pctrl_port0)
      ,.r557_pcfgqos0_port0 (r557_pcfgqos0_port0)
      ,.r558_pcfgqos1_port0 (r558_pcfgqos1_port0)
      ,.r559_pcfgwqos0_port0 (r559_pcfgwqos0_port0)
      ,.r560_pcfgwqos1_port0 (r560_pcfgwqos1_port0)
      ,.r569_sbrctl_port0 (r569_sbrctl_port0)
      ,.r570_sbrstat_port0 (r570_sbrstat_port0)
      ,.r571_sbrwdata0_port0 (r571_sbrwdata0_port0)
      ,.r573_sbrstart0_port0 (r573_sbrstart0_port0)
      ,.r574_sbrstart1_port0 (r574_sbrstart1_port0)
      ,.r575_sbrrange0_port0 (r575_sbrrange0_port0)
      ,.r576_sbrrange1_port0 (r576_sbrrange1_port0)
      ,.r582_pstat_port0 (r582_pstat_port0)
      ,.r1929_dramset1tmg0_freq0 (r1929_dramset1tmg0_freq0)
      ,.r1930_dramset1tmg1_freq0 (r1930_dramset1tmg1_freq0)
      ,.r1931_dramset1tmg2_freq0 (r1931_dramset1tmg2_freq0)
      ,.r1932_dramset1tmg3_freq0 (r1932_dramset1tmg3_freq0)
      ,.r1933_dramset1tmg4_freq0 (r1933_dramset1tmg4_freq0)
      ,.r1934_dramset1tmg5_freq0 (r1934_dramset1tmg5_freq0)
      ,.r1935_dramset1tmg6_freq0 (r1935_dramset1tmg6_freq0)
      ,.r1936_dramset1tmg7_freq0 (r1936_dramset1tmg7_freq0)
      ,.r1938_dramset1tmg9_freq0 (r1938_dramset1tmg9_freq0)
      ,.r1941_dramset1tmg12_freq0 (r1941_dramset1tmg12_freq0)
      ,.r1942_dramset1tmg13_freq0 (r1942_dramset1tmg13_freq0)
      ,.r1943_dramset1tmg14_freq0 (r1943_dramset1tmg14_freq0)
      ,.r1946_dramset1tmg17_freq0 (r1946_dramset1tmg17_freq0)
      ,.r1951_dramset1tmg23_freq0 (r1951_dramset1tmg23_freq0)
      ,.r1952_dramset1tmg24_freq0 (r1952_dramset1tmg24_freq0)
      ,.r1953_dramset1tmg25_freq0 (r1953_dramset1tmg25_freq0)
      ,.r1958_dramset1tmg30_freq0 (r1958_dramset1tmg30_freq0)
      ,.r1960_dramset1tmg32_freq0 (r1960_dramset1tmg32_freq0)
      ,.r1991_initmr0_freq0 (r1991_initmr0_freq0)
      ,.r1992_initmr1_freq0 (r1992_initmr1_freq0)
      ,.r1993_initmr2_freq0 (r1993_initmr2_freq0)
      ,.r1994_initmr3_freq0 (r1994_initmr3_freq0)
      ,.r1995_dfitmg0_freq0 (r1995_dfitmg0_freq0)
      ,.r1996_dfitmg1_freq0 (r1996_dfitmg1_freq0)
      ,.r1997_dfitmg2_freq0 (r1997_dfitmg2_freq0)
      ,.r1999_dfitmg4_freq0 (r1999_dfitmg4_freq0)
      ,.r2000_dfitmg5_freq0 (r2000_dfitmg5_freq0)
      ,.r2001_dfitmg6_freq0 (r2001_dfitmg6_freq0)
      ,.r2003_dfilptmg0_freq0 (r2003_dfilptmg0_freq0)
      ,.r2004_dfilptmg1_freq0 (r2004_dfilptmg1_freq0)
      ,.r2005_dfiupdtmg0_freq0 (r2005_dfiupdtmg0_freq0)
      ,.r2006_dfiupdtmg1_freq0 (r2006_dfiupdtmg1_freq0)
      ,.r2008_dfiupdtmg2_freq0 (r2008_dfiupdtmg2_freq0)
      ,.r2009_dfiupdtmg3_freq0 (r2009_dfiupdtmg3_freq0)
      ,.r2010_rfshset1tmg0_freq0 (r2010_rfshset1tmg0_freq0)
      ,.r2011_rfshset1tmg1_freq0 (r2011_rfshset1tmg1_freq0)
      ,.r2012_rfshset1tmg2_freq0 (r2012_rfshset1tmg2_freq0)
      ,.r2013_rfshset1tmg3_freq0 (r2013_rfshset1tmg3_freq0)
      ,.r2014_rfshset1tmg4_freq0 (r2014_rfshset1tmg4_freq0)
      ,.r2024_rfmset1tmg0_freq0 (r2024_rfmset1tmg0_freq0)
      ,.r2035_zqset1tmg0_freq0 (r2035_zqset1tmg0_freq0)
      ,.r2036_zqset1tmg1_freq0 (r2036_zqset1tmg1_freq0)
      ,.r2037_zqset1tmg2_freq0 (r2037_zqset1tmg2_freq0)
      ,.r2046_dqsoscctl0_freq0 (r2046_dqsoscctl0_freq0)
      ,.r2047_derateint_freq0 (r2047_derateint_freq0)
      ,.r2048_derateval0_freq0 (r2048_derateval0_freq0)
      ,.r2049_derateval1_freq0 (r2049_derateval1_freq0)
      ,.r2050_hwlptmg0_freq0 (r2050_hwlptmg0_freq0)
      ,.r2051_dvfsctl0_freq0 (r2051_dvfsctl0_freq0)
      ,.r2052_schedtmg0_freq0 (r2052_schedtmg0_freq0)
      ,.r2053_perfhpr1_freq0 (r2053_perfhpr1_freq0)
      ,.r2054_perflpr1_freq0 (r2054_perflpr1_freq0)
      ,.r2055_perfwr1_freq0 (r2055_perfwr1_freq0)
      ,.r2056_tmgcfg_freq0 (r2056_tmgcfg_freq0)
      ,.r2057_ranktmg0_freq0 (r2057_ranktmg0_freq0)
      ,.r2058_ranktmg1_freq0 (r2058_ranktmg1_freq0)
      ,.r2059_pwrtmg_freq0 (r2059_pwrtmg_freq0)
      ,.r2065_ddr4pprtmg0_freq0 (r2065_ddr4pprtmg0_freq0)
      ,.r2066_ddr4pprtmg1_freq0 (r2066_ddr4pprtmg1_freq0)
      ,.r2067_lnkeccctl0_freq0 (r2067_lnkeccctl0_freq0)
      ,.r2201_dramset1tmg0_freq1 (r2201_dramset1tmg0_freq1)
      ,.r2202_dramset1tmg1_freq1 (r2202_dramset1tmg1_freq1)
      ,.r2203_dramset1tmg2_freq1 (r2203_dramset1tmg2_freq1)
      ,.r2204_dramset1tmg3_freq1 (r2204_dramset1tmg3_freq1)
      ,.r2205_dramset1tmg4_freq1 (r2205_dramset1tmg4_freq1)
      ,.r2206_dramset1tmg5_freq1 (r2206_dramset1tmg5_freq1)
      ,.r2207_dramset1tmg6_freq1 (r2207_dramset1tmg6_freq1)
      ,.r2208_dramset1tmg7_freq1 (r2208_dramset1tmg7_freq1)
      ,.r2210_dramset1tmg9_freq1 (r2210_dramset1tmg9_freq1)
      ,.r2213_dramset1tmg12_freq1 (r2213_dramset1tmg12_freq1)
      ,.r2214_dramset1tmg13_freq1 (r2214_dramset1tmg13_freq1)
      ,.r2215_dramset1tmg14_freq1 (r2215_dramset1tmg14_freq1)
      ,.r2218_dramset1tmg17_freq1 (r2218_dramset1tmg17_freq1)
      ,.r2223_dramset1tmg23_freq1 (r2223_dramset1tmg23_freq1)
      ,.r2224_dramset1tmg24_freq1 (r2224_dramset1tmg24_freq1)
      ,.r2225_dramset1tmg25_freq1 (r2225_dramset1tmg25_freq1)
      ,.r2230_dramset1tmg30_freq1 (r2230_dramset1tmg30_freq1)
      ,.r2232_dramset1tmg32_freq1 (r2232_dramset1tmg32_freq1)
      ,.r2263_initmr0_freq1 (r2263_initmr0_freq1)
      ,.r2264_initmr1_freq1 (r2264_initmr1_freq1)
      ,.r2265_initmr2_freq1 (r2265_initmr2_freq1)
      ,.r2266_initmr3_freq1 (r2266_initmr3_freq1)
      ,.r2267_dfitmg0_freq1 (r2267_dfitmg0_freq1)
      ,.r2268_dfitmg1_freq1 (r2268_dfitmg1_freq1)
      ,.r2269_dfitmg2_freq1 (r2269_dfitmg2_freq1)
      ,.r2271_dfitmg4_freq1 (r2271_dfitmg4_freq1)
      ,.r2272_dfitmg5_freq1 (r2272_dfitmg5_freq1)
      ,.r2273_dfitmg6_freq1 (r2273_dfitmg6_freq1)
      ,.r2275_dfiupdtmg1_freq1 (r2275_dfiupdtmg1_freq1)
      ,.r2276_dfiupdtmg2_freq1 (r2276_dfiupdtmg2_freq1)
      ,.r2277_dfiupdtmg3_freq1 (r2277_dfiupdtmg3_freq1)
      ,.r2278_rfshset1tmg0_freq1 (r2278_rfshset1tmg0_freq1)
      ,.r2279_rfshset1tmg1_freq1 (r2279_rfshset1tmg1_freq1)
      ,.r2280_rfshset1tmg2_freq1 (r2280_rfshset1tmg2_freq1)
      ,.r2281_rfshset1tmg3_freq1 (r2281_rfshset1tmg3_freq1)
      ,.r2282_rfshset1tmg4_freq1 (r2282_rfshset1tmg4_freq1)
      ,.r2292_rfmset1tmg0_freq1 (r2292_rfmset1tmg0_freq1)
      ,.r2303_zqset1tmg0_freq1 (r2303_zqset1tmg0_freq1)
      ,.r2304_zqset1tmg1_freq1 (r2304_zqset1tmg1_freq1)
      ,.r2305_zqset1tmg2_freq1 (r2305_zqset1tmg2_freq1)
      ,.r2314_dqsoscctl0_freq1 (r2314_dqsoscctl0_freq1)
      ,.r2315_derateint_freq1 (r2315_derateint_freq1)
      ,.r2316_derateval0_freq1 (r2316_derateval0_freq1)
      ,.r2317_derateval1_freq1 (r2317_derateval1_freq1)
      ,.r2318_hwlptmg0_freq1 (r2318_hwlptmg0_freq1)
      ,.r2319_dvfsctl0_freq1 (r2319_dvfsctl0_freq1)
      ,.r2320_schedtmg0_freq1 (r2320_schedtmg0_freq1)
      ,.r2321_perfhpr1_freq1 (r2321_perfhpr1_freq1)
      ,.r2322_perflpr1_freq1 (r2322_perflpr1_freq1)
      ,.r2323_perfwr1_freq1 (r2323_perfwr1_freq1)
      ,.r2324_tmgcfg_freq1 (r2324_tmgcfg_freq1)
      ,.r2325_ranktmg0_freq1 (r2325_ranktmg0_freq1)
      ,.r2326_ranktmg1_freq1 (r2326_ranktmg1_freq1)
      ,.r2327_pwrtmg_freq1 (r2327_pwrtmg_freq1)
      ,.r2333_ddr4pprtmg0_freq1 (r2333_ddr4pprtmg0_freq1)
      ,.r2334_ddr4pprtmg1_freq1 (r2334_ddr4pprtmg1_freq1)
      ,.r2335_lnkeccctl0_freq1 (r2335_lnkeccctl0_freq1)
      ,.r2469_dramset1tmg0_freq2 (r2469_dramset1tmg0_freq2)
      ,.r2470_dramset1tmg1_freq2 (r2470_dramset1tmg1_freq2)
      ,.r2471_dramset1tmg2_freq2 (r2471_dramset1tmg2_freq2)
      ,.r2472_dramset1tmg3_freq2 (r2472_dramset1tmg3_freq2)
      ,.r2473_dramset1tmg4_freq2 (r2473_dramset1tmg4_freq2)
      ,.r2474_dramset1tmg5_freq2 (r2474_dramset1tmg5_freq2)
      ,.r2475_dramset1tmg6_freq2 (r2475_dramset1tmg6_freq2)
      ,.r2476_dramset1tmg7_freq2 (r2476_dramset1tmg7_freq2)
      ,.r2478_dramset1tmg9_freq2 (r2478_dramset1tmg9_freq2)
      ,.r2481_dramset1tmg12_freq2 (r2481_dramset1tmg12_freq2)
      ,.r2482_dramset1tmg13_freq2 (r2482_dramset1tmg13_freq2)
      ,.r2483_dramset1tmg14_freq2 (r2483_dramset1tmg14_freq2)
      ,.r2486_dramset1tmg17_freq2 (r2486_dramset1tmg17_freq2)
      ,.r2491_dramset1tmg23_freq2 (r2491_dramset1tmg23_freq2)
      ,.r2492_dramset1tmg24_freq2 (r2492_dramset1tmg24_freq2)
      ,.r2493_dramset1tmg25_freq2 (r2493_dramset1tmg25_freq2)
      ,.r2498_dramset1tmg30_freq2 (r2498_dramset1tmg30_freq2)
      ,.r2500_dramset1tmg32_freq2 (r2500_dramset1tmg32_freq2)
      ,.r2531_initmr0_freq2 (r2531_initmr0_freq2)
      ,.r2532_initmr1_freq2 (r2532_initmr1_freq2)
      ,.r2533_initmr2_freq2 (r2533_initmr2_freq2)
      ,.r2534_initmr3_freq2 (r2534_initmr3_freq2)
      ,.r2535_dfitmg0_freq2 (r2535_dfitmg0_freq2)
      ,.r2536_dfitmg1_freq2 (r2536_dfitmg1_freq2)
      ,.r2537_dfitmg2_freq2 (r2537_dfitmg2_freq2)
      ,.r2539_dfitmg4_freq2 (r2539_dfitmg4_freq2)
      ,.r2540_dfitmg5_freq2 (r2540_dfitmg5_freq2)
      ,.r2541_dfitmg6_freq2 (r2541_dfitmg6_freq2)
      ,.r2543_dfiupdtmg1_freq2 (r2543_dfiupdtmg1_freq2)
      ,.r2544_dfiupdtmg2_freq2 (r2544_dfiupdtmg2_freq2)
      ,.r2545_dfiupdtmg3_freq2 (r2545_dfiupdtmg3_freq2)
      ,.r2546_rfshset1tmg0_freq2 (r2546_rfshset1tmg0_freq2)
      ,.r2547_rfshset1tmg1_freq2 (r2547_rfshset1tmg1_freq2)
      ,.r2548_rfshset1tmg2_freq2 (r2548_rfshset1tmg2_freq2)
      ,.r2549_rfshset1tmg3_freq2 (r2549_rfshset1tmg3_freq2)
      ,.r2550_rfshset1tmg4_freq2 (r2550_rfshset1tmg4_freq2)
      ,.r2560_rfmset1tmg0_freq2 (r2560_rfmset1tmg0_freq2)
      ,.r2571_zqset1tmg0_freq2 (r2571_zqset1tmg0_freq2)
      ,.r2572_zqset1tmg1_freq2 (r2572_zqset1tmg1_freq2)
      ,.r2573_zqset1tmg2_freq2 (r2573_zqset1tmg2_freq2)
      ,.r2582_dqsoscctl0_freq2 (r2582_dqsoscctl0_freq2)
      ,.r2583_derateint_freq2 (r2583_derateint_freq2)
      ,.r2584_derateval0_freq2 (r2584_derateval0_freq2)
      ,.r2585_derateval1_freq2 (r2585_derateval1_freq2)
      ,.r2586_hwlptmg0_freq2 (r2586_hwlptmg0_freq2)
      ,.r2587_dvfsctl0_freq2 (r2587_dvfsctl0_freq2)
      ,.r2588_schedtmg0_freq2 (r2588_schedtmg0_freq2)
      ,.r2589_perfhpr1_freq2 (r2589_perfhpr1_freq2)
      ,.r2590_perflpr1_freq2 (r2590_perflpr1_freq2)
      ,.r2591_perfwr1_freq2 (r2591_perfwr1_freq2)
      ,.r2592_tmgcfg_freq2 (r2592_tmgcfg_freq2)
      ,.r2593_ranktmg0_freq2 (r2593_ranktmg0_freq2)
      ,.r2594_ranktmg1_freq2 (r2594_ranktmg1_freq2)
      ,.r2595_pwrtmg_freq2 (r2595_pwrtmg_freq2)
      ,.r2601_ddr4pprtmg0_freq2 (r2601_ddr4pprtmg0_freq2)
      ,.r2602_ddr4pprtmg1_freq2 (r2602_ddr4pprtmg1_freq2)
      ,.r2603_lnkeccctl0_freq2 (r2603_lnkeccctl0_freq2)
      ,.r2737_dramset1tmg0_freq3 (r2737_dramset1tmg0_freq3)
      ,.r2738_dramset1tmg1_freq3 (r2738_dramset1tmg1_freq3)
      ,.r2739_dramset1tmg2_freq3 (r2739_dramset1tmg2_freq3)
      ,.r2740_dramset1tmg3_freq3 (r2740_dramset1tmg3_freq3)
      ,.r2741_dramset1tmg4_freq3 (r2741_dramset1tmg4_freq3)
      ,.r2742_dramset1tmg5_freq3 (r2742_dramset1tmg5_freq3)
      ,.r2743_dramset1tmg6_freq3 (r2743_dramset1tmg6_freq3)
      ,.r2744_dramset1tmg7_freq3 (r2744_dramset1tmg7_freq3)
      ,.r2746_dramset1tmg9_freq3 (r2746_dramset1tmg9_freq3)
      ,.r2749_dramset1tmg12_freq3 (r2749_dramset1tmg12_freq3)
      ,.r2750_dramset1tmg13_freq3 (r2750_dramset1tmg13_freq3)
      ,.r2751_dramset1tmg14_freq3 (r2751_dramset1tmg14_freq3)
      ,.r2754_dramset1tmg17_freq3 (r2754_dramset1tmg17_freq3)
      ,.r2759_dramset1tmg23_freq3 (r2759_dramset1tmg23_freq3)
      ,.r2760_dramset1tmg24_freq3 (r2760_dramset1tmg24_freq3)
      ,.r2761_dramset1tmg25_freq3 (r2761_dramset1tmg25_freq3)
      ,.r2766_dramset1tmg30_freq3 (r2766_dramset1tmg30_freq3)
      ,.r2768_dramset1tmg32_freq3 (r2768_dramset1tmg32_freq3)
      ,.r2799_initmr0_freq3 (r2799_initmr0_freq3)
      ,.r2800_initmr1_freq3 (r2800_initmr1_freq3)
      ,.r2801_initmr2_freq3 (r2801_initmr2_freq3)
      ,.r2802_initmr3_freq3 (r2802_initmr3_freq3)
      ,.r2803_dfitmg0_freq3 (r2803_dfitmg0_freq3)
      ,.r2804_dfitmg1_freq3 (r2804_dfitmg1_freq3)
      ,.r2805_dfitmg2_freq3 (r2805_dfitmg2_freq3)
      ,.r2807_dfitmg4_freq3 (r2807_dfitmg4_freq3)
      ,.r2808_dfitmg5_freq3 (r2808_dfitmg5_freq3)
      ,.r2809_dfitmg6_freq3 (r2809_dfitmg6_freq3)
      ,.r2811_dfiupdtmg1_freq3 (r2811_dfiupdtmg1_freq3)
      ,.r2812_dfiupdtmg2_freq3 (r2812_dfiupdtmg2_freq3)
      ,.r2813_dfiupdtmg3_freq3 (r2813_dfiupdtmg3_freq3)
      ,.r2814_rfshset1tmg0_freq3 (r2814_rfshset1tmg0_freq3)
      ,.r2815_rfshset1tmg1_freq3 (r2815_rfshset1tmg1_freq3)
      ,.r2816_rfshset1tmg2_freq3 (r2816_rfshset1tmg2_freq3)
      ,.r2817_rfshset1tmg3_freq3 (r2817_rfshset1tmg3_freq3)
      ,.r2818_rfshset1tmg4_freq3 (r2818_rfshset1tmg4_freq3)
      ,.r2828_rfmset1tmg0_freq3 (r2828_rfmset1tmg0_freq3)
      ,.r2839_zqset1tmg0_freq3 (r2839_zqset1tmg0_freq3)
      ,.r2840_zqset1tmg1_freq3 (r2840_zqset1tmg1_freq3)
      ,.r2841_zqset1tmg2_freq3 (r2841_zqset1tmg2_freq3)
      ,.r2850_dqsoscctl0_freq3 (r2850_dqsoscctl0_freq3)
      ,.r2851_derateint_freq3 (r2851_derateint_freq3)
      ,.r2852_derateval0_freq3 (r2852_derateval0_freq3)
      ,.r2853_derateval1_freq3 (r2853_derateval1_freq3)
      ,.r2854_hwlptmg0_freq3 (r2854_hwlptmg0_freq3)
      ,.r2855_dvfsctl0_freq3 (r2855_dvfsctl0_freq3)
      ,.r2856_schedtmg0_freq3 (r2856_schedtmg0_freq3)
      ,.r2857_perfhpr1_freq3 (r2857_perfhpr1_freq3)
      ,.r2858_perflpr1_freq3 (r2858_perflpr1_freq3)
      ,.r2859_perfwr1_freq3 (r2859_perfwr1_freq3)
      ,.r2860_tmgcfg_freq3 (r2860_tmgcfg_freq3)
      ,.r2861_ranktmg0_freq3 (r2861_ranktmg0_freq3)
      ,.r2862_ranktmg1_freq3 (r2862_ranktmg1_freq3)
      ,.r2863_pwrtmg_freq3 (r2863_pwrtmg_freq3)
      ,.r2869_ddr4pprtmg0_freq3 (r2869_ddr4pprtmg0_freq3)
      ,.r2870_ddr4pprtmg1_freq3 (r2870_ddr4pprtmg1_freq3)
      ,.r2871_lnkeccctl0_freq3 (r2871_lnkeccctl0_freq3)

      );    

   // ----------------------------------------------------------------------------
   // Module apbslvif (APB Slave Interface)
   // This module drives all the outputs for the APB module. It receives the
   // decoded address and depending on the SM state latches the data for a
   // write operation. This module also asserts pslverr in case the timer expires
   // or the address is out of bounds
   // The data is latched on the last clock of address decode (should we do it here
   // or move it to the address decoder-the latter seems to be easier)
   // pready is asserted and the data is put on the bus. This is on the same clk
   // when the SM is in the dataxfer state
   // The slave interfaces with the actual register file and retrieves the read
   // data from the register file (should the reg_file module be instantiated here?)
   // ----------------------------------------------------------------------------
      
   DWC_ddrctl_apb_slvif
   
     #(.APB_AW        (APB_AW),
       .APB_DW        (APB_DW),
       .RW_REGS       (RW_REGS),
       .REG_WIDTH     (REG_WIDTH),
       .RWSELWIDTH    (RWSELWIDTH)
       ) 
   slvif
     (
       .presetn            (presetn)
      ,.pclk               (pclk_apbrw)
      ,.pwdata             (pwdata)
      ,.rwselect           (rwselect)
      ,.write_en           (write_en_pulse)
      ,.store_rqst         (store_rqst)
      // static registers write enable
      ,.static_wr_en_aclk_0             (static_wr_en_aclk_0)
      ,.quasi_dyn_wr_en_aclk_0          (quasi_dyn_wr_en_aclk_0)
      ,.static_wr_en_core_ddrc_core_clk    (static_wr_en_core_ddrc_core_clk)
      ,.quasi_dyn_wr_en_core_ddrc_core_clk (quasi_dyn_wr_en_core_ddrc_core_clk)
//`ifdef UMCTL2_OCECC_EN_1      
//      ,.quasi_dyn_wr_en_pclk               (quasi_dyn_wr_en_pclk)
//`endif // UMCTL2_OCPAR_OR_OCECC_EN_1
      //------------------------------
      ,.r0_mstr0 (r0_mstr0)
      ,.r2_mstr2 (r2_mstr2)
      ,.r4_mstr4 (r4_mstr4)
      ,.r8_mrctrl0 (r8_mrctrl0)
      ,.reg_ddrc_mrr_done_clr_ack_pclk (reg_ddrc_mrr_done_clr_ack_pclk)
      ,.reg_ddrc_mr_wr_ack_pclk (reg_ddrc_mr_wr_ack_pclk)
      ,.ff_regb_ddrc_ch0_mr_wr_saved (ff_regb_ddrc_ch0_mr_wr_saved)
      ,.r9_mrctrl1 (r9_mrctrl1)
      ,.ddrc_reg_mr_wr_busy_int (ddrc_reg_mr_wr_busy_int)
      ,.r14_deratectl0 (r14_deratectl0)
      ,.r15_deratectl1 (r15_deratectl1)
      ,.r16_deratectl2 (r16_deratectl2)
      ,.r19_deratectl5 (r19_deratectl5)
      ,.reg_ddrc_derate_temp_limit_intr_clr_ack_pclk (reg_ddrc_derate_temp_limit_intr_clr_ack_pclk)
      ,.reg_ddrc_derate_temp_limit_intr_force_ack_pclk (reg_ddrc_derate_temp_limit_intr_force_ack_pclk)
      ,.r20_deratectl6 (r20_deratectl6)
      ,.r24_deratedbgctl (r24_deratedbgctl)
      ,.r26_pwrctl (r26_pwrctl)
      ,.r27_hwlpctl (r27_hwlpctl)
      ,.r29_clkgatectl (r29_clkgatectl)
      ,.r30_rfshmod0 (r30_rfshmod0)
      ,.r32_rfshctl0 (r32_rfshctl0)
      ,.r33_rfmmod0 (r33_rfmmod0)
      ,.r34_rfmmod1 (r34_rfmmod1)
      ,.r35_rfmctl (r35_rfmctl)
      ,.r37_zqctl0 (r37_zqctl0)
      ,.r38_zqctl1 (r38_zqctl1)
      ,.reg_ddrc_zq_reset_ack_pclk (reg_ddrc_zq_reset_ack_pclk)
      ,.ff_regb_ddrc_ch0_zq_reset_saved (ff_regb_ddrc_ch0_zq_reset_saved)
      ,.r39_zqctl2 (r39_zqctl2)
      ,.ddrc_reg_zq_reset_busy_int (ddrc_reg_zq_reset_busy_int)
      ,.r41_dqsoscruntime (r41_dqsoscruntime)
      ,.r43_dqsosccfg0 (r43_dqsosccfg0)
      ,.r45_sched0 (r45_sched0)
      ,.r46_sched1 (r46_sched1)
      ,.r48_sched3 (r48_sched3)
      ,.r49_sched4 (r49_sched4)
      ,.r50_sched5 (r50_sched5)
      ,.r51_hwffcctl (r51_hwffcctl)
      ,.r62_dfilpcfg0 (r62_dfilpcfg0)
      ,.r63_dfiupd0 (r63_dfiupd0)
      ,.r65_dfimisc (r65_dfimisc)
      ,.r67_dfiphymstr (r67_dfiphymstr)
      ,.r77_poisoncfg (r77_poisoncfg)
      ,.reg_ddrc_wr_poison_intr_clr_ack_pclk (reg_ddrc_wr_poison_intr_clr_ack_pclk)
      ,.reg_ddrc_rd_poison_intr_clr_ack_pclk (reg_ddrc_rd_poison_intr_clr_ack_pclk)
      ,.r79_ecccfg0 (r79_ecccfg0)
      ,.r80_ecccfg1 (r80_ecccfg1)
      ,.r82_eccctl (r82_eccctl)
      ,.reg_ddrc_ecc_corrected_err_clr_ack_pclk (reg_ddrc_ecc_corrected_err_clr_ack_pclk)
      ,.reg_ddrc_ecc_uncorrected_err_clr_ack_pclk (reg_ddrc_ecc_uncorrected_err_clr_ack_pclk)
      ,.reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk (reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk)
      ,.reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk (reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk)
      ,.reg_ddrc_ecc_ap_err_intr_clr_ack_pclk (reg_ddrc_ecc_ap_err_intr_clr_ack_pclk)
      ,.reg_ddrc_ecc_corrected_err_intr_force_ack_pclk (reg_ddrc_ecc_corrected_err_intr_force_ack_pclk)
      ,.reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk (reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk)
      ,.reg_ddrc_ecc_ap_err_intr_force_ack_pclk (reg_ddrc_ecc_ap_err_intr_force_ack_pclk)
      ,.r97_eccpoisonaddr0 (r97_eccpoisonaddr0)
      ,.r98_eccpoisonaddr1 (r98_eccpoisonaddr1)
      ,.r101_eccpoisonpat0 (r101_eccpoisonpat0)
      ,.r103_eccpoisonpat2 (r103_eccpoisonpat2)
      ,.r161_lnkeccctl1 (r161_lnkeccctl1)
      ,.reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk (reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk (reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk (reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk (reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk (reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk (reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk)
      ,.r162_lnkeccpoisonctl0 (r162_lnkeccpoisonctl0)
      ,.r164_lnkeccindex (r164_lnkeccindex)
      ,.r234_opctrl0 (r234_opctrl0)
      ,.r235_opctrl1 (r235_opctrl1)
      ,.r237_opctrlcmd (r237_opctrlcmd)
      ,.reg_ddrc_zq_calib_short_ack_pclk (reg_ddrc_zq_calib_short_ack_pclk)
      ,.ff_regb_ddrc_ch0_zq_calib_short_saved (ff_regb_ddrc_ch0_zq_calib_short_saved)
      ,.reg_ddrc_ctrlupd_ack_pclk (reg_ddrc_ctrlupd_ack_pclk)
      ,.ff_regb_ddrc_ch0_ctrlupd_saved (ff_regb_ddrc_ch0_ctrlupd_saved)
      ,.ddrc_reg_zq_calib_short_busy_int (ddrc_reg_zq_calib_short_busy_int)
      ,.ddrc_reg_ctrlupd_busy_int (ddrc_reg_ctrlupd_busy_int)
      ,.r240_oprefctrl0 (r240_oprefctrl0)
      ,.reg_ddrc_rank0_refresh_ack_pclk (reg_ddrc_rank0_refresh_ack_pclk)
      ,.ff_regb_ddrc_ch0_rank0_refresh_saved (ff_regb_ddrc_ch0_rank0_refresh_saved)
      ,.reg_ddrc_rank1_refresh_ack_pclk (reg_ddrc_rank1_refresh_ack_pclk)
      ,.ff_regb_ddrc_ch0_rank1_refresh_saved (ff_regb_ddrc_ch0_rank1_refresh_saved)
      ,.ddrc_reg_rank0_refresh_busy_int (ddrc_reg_rank0_refresh_busy_int)
      ,.ddrc_reg_rank1_refresh_busy_int (ddrc_reg_rank1_refresh_busy_int)
      ,.r249_swctl (r249_swctl)
      ,.r253_rankctl (r253_rankctl)
      ,.r254_dbictl (r254_dbictl)
      ,.r256_odtmap (r256_odtmap)
      ,.r257_datactl0 (r257_datactl0)
      ,.r258_swctlstatic (r258_swctlstatic)
      ,.r259_cgctl (r259_cgctl)
      ,.r260_inittmg0 (r260_inittmg0)
      ,.r285_ppt2ctrl0 (r285_ppt2ctrl0)
      ,.reg_ddrc_ppt2_burst_ack_pclk (reg_ddrc_ppt2_burst_ack_pclk)
      ,.ff_regb_ddrc_ch0_ppt2_burst_saved (ff_regb_ddrc_ch0_ppt2_burst_saved)
      ,.ddrc_reg_ppt2_burst_busy_int (ddrc_reg_ppt2_burst_busy_int)
      ,.r495_addrmap1_map0 (r495_addrmap1_map0)
      ,.r497_addrmap3_map0 (r497_addrmap3_map0)
      ,.r498_addrmap4_map0 (r498_addrmap4_map0)
      ,.r499_addrmap5_map0 (r499_addrmap5_map0)
      ,.r500_addrmap6_map0 (r500_addrmap6_map0)
      ,.r501_addrmap7_map0 (r501_addrmap7_map0)
      ,.r502_addrmap8_map0 (r502_addrmap8_map0)
      ,.r503_addrmap9_map0 (r503_addrmap9_map0)
      ,.r504_addrmap10_map0 (r504_addrmap10_map0)
      ,.r505_addrmap11_map0 (r505_addrmap11_map0)
      ,.r506_addrmap12_map0 (r506_addrmap12_map0)
      ,.r521_pccfg_port0 (r521_pccfg_port0)
      ,.r522_pcfgr_port0 (r522_pcfgr_port0)
      ,.r523_pcfgw_port0 (r523_pcfgw_port0)
      ,.r556_pctrl_port0 (r556_pctrl_port0)
      ,.r557_pcfgqos0_port0 (r557_pcfgqos0_port0)
      ,.r558_pcfgqos1_port0 (r558_pcfgqos1_port0)
      ,.r559_pcfgwqos0_port0 (r559_pcfgwqos0_port0)
      ,.r560_pcfgwqos1_port0 (r560_pcfgwqos1_port0)
      ,.r569_sbrctl_port0 (r569_sbrctl_port0)
      ,.r571_sbrwdata0_port0 (r571_sbrwdata0_port0)
      ,.r573_sbrstart0_port0 (r573_sbrstart0_port0)
      ,.r574_sbrstart1_port0 (r574_sbrstart1_port0)
      ,.r575_sbrrange0_port0 (r575_sbrrange0_port0)
      ,.r576_sbrrange1_port0 (r576_sbrrange1_port0)
      ,.r1929_dramset1tmg0_freq0 (r1929_dramset1tmg0_freq0)
      ,.r1930_dramset1tmg1_freq0 (r1930_dramset1tmg1_freq0)
      ,.r1931_dramset1tmg2_freq0 (r1931_dramset1tmg2_freq0)
      ,.r1932_dramset1tmg3_freq0 (r1932_dramset1tmg3_freq0)
      ,.r1933_dramset1tmg4_freq0 (r1933_dramset1tmg4_freq0)
      ,.r1934_dramset1tmg5_freq0 (r1934_dramset1tmg5_freq0)
      ,.r1935_dramset1tmg6_freq0 (r1935_dramset1tmg6_freq0)
      ,.r1936_dramset1tmg7_freq0 (r1936_dramset1tmg7_freq0)
      ,.r1938_dramset1tmg9_freq0 (r1938_dramset1tmg9_freq0)
      ,.r1941_dramset1tmg12_freq0 (r1941_dramset1tmg12_freq0)
      ,.r1942_dramset1tmg13_freq0 (r1942_dramset1tmg13_freq0)
      ,.r1943_dramset1tmg14_freq0 (r1943_dramset1tmg14_freq0)
      ,.r1946_dramset1tmg17_freq0 (r1946_dramset1tmg17_freq0)
      ,.r1951_dramset1tmg23_freq0 (r1951_dramset1tmg23_freq0)
      ,.r1952_dramset1tmg24_freq0 (r1952_dramset1tmg24_freq0)
      ,.r1953_dramset1tmg25_freq0 (r1953_dramset1tmg25_freq0)
      ,.r1958_dramset1tmg30_freq0 (r1958_dramset1tmg30_freq0)
      ,.r1960_dramset1tmg32_freq0 (r1960_dramset1tmg32_freq0)
      ,.r1991_initmr0_freq0 (r1991_initmr0_freq0)
      ,.r1992_initmr1_freq0 (r1992_initmr1_freq0)
      ,.r1993_initmr2_freq0 (r1993_initmr2_freq0)
      ,.r1994_initmr3_freq0 (r1994_initmr3_freq0)
      ,.r1995_dfitmg0_freq0 (r1995_dfitmg0_freq0)
      ,.r1996_dfitmg1_freq0 (r1996_dfitmg1_freq0)
      ,.r1997_dfitmg2_freq0 (r1997_dfitmg2_freq0)
      ,.r1999_dfitmg4_freq0 (r1999_dfitmg4_freq0)
      ,.r2000_dfitmg5_freq0 (r2000_dfitmg5_freq0)
      ,.r2001_dfitmg6_freq0 (r2001_dfitmg6_freq0)
      ,.r2003_dfilptmg0_freq0 (r2003_dfilptmg0_freq0)
      ,.r2004_dfilptmg1_freq0 (r2004_dfilptmg1_freq0)
      ,.r2005_dfiupdtmg0_freq0 (r2005_dfiupdtmg0_freq0)
      ,.r2006_dfiupdtmg1_freq0 (r2006_dfiupdtmg1_freq0)
      ,.r2008_dfiupdtmg2_freq0 (r2008_dfiupdtmg2_freq0)
      ,.r2009_dfiupdtmg3_freq0 (r2009_dfiupdtmg3_freq0)
      ,.r2010_rfshset1tmg0_freq0 (r2010_rfshset1tmg0_freq0)
      ,.r2011_rfshset1tmg1_freq0 (r2011_rfshset1tmg1_freq0)
      ,.r2012_rfshset1tmg2_freq0 (r2012_rfshset1tmg2_freq0)
      ,.r2013_rfshset1tmg3_freq0 (r2013_rfshset1tmg3_freq0)
      ,.r2014_rfshset1tmg4_freq0 (r2014_rfshset1tmg4_freq0)
      ,.r2024_rfmset1tmg0_freq0 (r2024_rfmset1tmg0_freq0)
      ,.r2035_zqset1tmg0_freq0 (r2035_zqset1tmg0_freq0)
      ,.r2036_zqset1tmg1_freq0 (r2036_zqset1tmg1_freq0)
      ,.r2037_zqset1tmg2_freq0 (r2037_zqset1tmg2_freq0)
      ,.r2046_dqsoscctl0_freq0 (r2046_dqsoscctl0_freq0)
      ,.r2047_derateint_freq0 (r2047_derateint_freq0)
      ,.r2048_derateval0_freq0 (r2048_derateval0_freq0)
      ,.r2049_derateval1_freq0 (r2049_derateval1_freq0)
      ,.r2050_hwlptmg0_freq0 (r2050_hwlptmg0_freq0)
      ,.r2051_dvfsctl0_freq0 (r2051_dvfsctl0_freq0)
      ,.r2052_schedtmg0_freq0 (r2052_schedtmg0_freq0)
      ,.r2053_perfhpr1_freq0 (r2053_perfhpr1_freq0)
      ,.r2054_perflpr1_freq0 (r2054_perflpr1_freq0)
      ,.r2055_perfwr1_freq0 (r2055_perfwr1_freq0)
      ,.r2056_tmgcfg_freq0 (r2056_tmgcfg_freq0)
      ,.r2057_ranktmg0_freq0 (r2057_ranktmg0_freq0)
      ,.r2058_ranktmg1_freq0 (r2058_ranktmg1_freq0)
      ,.r2059_pwrtmg_freq0 (r2059_pwrtmg_freq0)
      ,.r2065_ddr4pprtmg0_freq0 (r2065_ddr4pprtmg0_freq0)
      ,.r2066_ddr4pprtmg1_freq0 (r2066_ddr4pprtmg1_freq0)
      ,.r2067_lnkeccctl0_freq0 (r2067_lnkeccctl0_freq0)
      ,.r2201_dramset1tmg0_freq1 (r2201_dramset1tmg0_freq1)
      ,.r2202_dramset1tmg1_freq1 (r2202_dramset1tmg1_freq1)
      ,.r2203_dramset1tmg2_freq1 (r2203_dramset1tmg2_freq1)
      ,.r2204_dramset1tmg3_freq1 (r2204_dramset1tmg3_freq1)
      ,.r2205_dramset1tmg4_freq1 (r2205_dramset1tmg4_freq1)
      ,.r2206_dramset1tmg5_freq1 (r2206_dramset1tmg5_freq1)
      ,.r2207_dramset1tmg6_freq1 (r2207_dramset1tmg6_freq1)
      ,.r2208_dramset1tmg7_freq1 (r2208_dramset1tmg7_freq1)
      ,.r2210_dramset1tmg9_freq1 (r2210_dramset1tmg9_freq1)
      ,.r2213_dramset1tmg12_freq1 (r2213_dramset1tmg12_freq1)
      ,.r2214_dramset1tmg13_freq1 (r2214_dramset1tmg13_freq1)
      ,.r2215_dramset1tmg14_freq1 (r2215_dramset1tmg14_freq1)
      ,.r2218_dramset1tmg17_freq1 (r2218_dramset1tmg17_freq1)
      ,.r2223_dramset1tmg23_freq1 (r2223_dramset1tmg23_freq1)
      ,.r2224_dramset1tmg24_freq1 (r2224_dramset1tmg24_freq1)
      ,.r2225_dramset1tmg25_freq1 (r2225_dramset1tmg25_freq1)
      ,.r2230_dramset1tmg30_freq1 (r2230_dramset1tmg30_freq1)
      ,.r2232_dramset1tmg32_freq1 (r2232_dramset1tmg32_freq1)
      ,.r2263_initmr0_freq1 (r2263_initmr0_freq1)
      ,.r2264_initmr1_freq1 (r2264_initmr1_freq1)
      ,.r2265_initmr2_freq1 (r2265_initmr2_freq1)
      ,.r2266_initmr3_freq1 (r2266_initmr3_freq1)
      ,.r2267_dfitmg0_freq1 (r2267_dfitmg0_freq1)
      ,.r2268_dfitmg1_freq1 (r2268_dfitmg1_freq1)
      ,.r2269_dfitmg2_freq1 (r2269_dfitmg2_freq1)
      ,.r2271_dfitmg4_freq1 (r2271_dfitmg4_freq1)
      ,.r2272_dfitmg5_freq1 (r2272_dfitmg5_freq1)
      ,.r2273_dfitmg6_freq1 (r2273_dfitmg6_freq1)
      ,.r2275_dfiupdtmg1_freq1 (r2275_dfiupdtmg1_freq1)
      ,.r2276_dfiupdtmg2_freq1 (r2276_dfiupdtmg2_freq1)
      ,.r2277_dfiupdtmg3_freq1 (r2277_dfiupdtmg3_freq1)
      ,.r2278_rfshset1tmg0_freq1 (r2278_rfshset1tmg0_freq1)
      ,.r2279_rfshset1tmg1_freq1 (r2279_rfshset1tmg1_freq1)
      ,.r2280_rfshset1tmg2_freq1 (r2280_rfshset1tmg2_freq1)
      ,.r2281_rfshset1tmg3_freq1 (r2281_rfshset1tmg3_freq1)
      ,.r2282_rfshset1tmg4_freq1 (r2282_rfshset1tmg4_freq1)
      ,.r2292_rfmset1tmg0_freq1 (r2292_rfmset1tmg0_freq1)
      ,.r2303_zqset1tmg0_freq1 (r2303_zqset1tmg0_freq1)
      ,.r2304_zqset1tmg1_freq1 (r2304_zqset1tmg1_freq1)
      ,.r2305_zqset1tmg2_freq1 (r2305_zqset1tmg2_freq1)
      ,.r2314_dqsoscctl0_freq1 (r2314_dqsoscctl0_freq1)
      ,.r2315_derateint_freq1 (r2315_derateint_freq1)
      ,.r2316_derateval0_freq1 (r2316_derateval0_freq1)
      ,.r2317_derateval1_freq1 (r2317_derateval1_freq1)
      ,.r2318_hwlptmg0_freq1 (r2318_hwlptmg0_freq1)
      ,.r2319_dvfsctl0_freq1 (r2319_dvfsctl0_freq1)
      ,.r2320_schedtmg0_freq1 (r2320_schedtmg0_freq1)
      ,.r2321_perfhpr1_freq1 (r2321_perfhpr1_freq1)
      ,.r2322_perflpr1_freq1 (r2322_perflpr1_freq1)
      ,.r2323_perfwr1_freq1 (r2323_perfwr1_freq1)
      ,.r2324_tmgcfg_freq1 (r2324_tmgcfg_freq1)
      ,.r2325_ranktmg0_freq1 (r2325_ranktmg0_freq1)
      ,.r2326_ranktmg1_freq1 (r2326_ranktmg1_freq1)
      ,.r2327_pwrtmg_freq1 (r2327_pwrtmg_freq1)
      ,.r2333_ddr4pprtmg0_freq1 (r2333_ddr4pprtmg0_freq1)
      ,.r2334_ddr4pprtmg1_freq1 (r2334_ddr4pprtmg1_freq1)
      ,.r2335_lnkeccctl0_freq1 (r2335_lnkeccctl0_freq1)
      ,.r2469_dramset1tmg0_freq2 (r2469_dramset1tmg0_freq2)
      ,.r2470_dramset1tmg1_freq2 (r2470_dramset1tmg1_freq2)
      ,.r2471_dramset1tmg2_freq2 (r2471_dramset1tmg2_freq2)
      ,.r2472_dramset1tmg3_freq2 (r2472_dramset1tmg3_freq2)
      ,.r2473_dramset1tmg4_freq2 (r2473_dramset1tmg4_freq2)
      ,.r2474_dramset1tmg5_freq2 (r2474_dramset1tmg5_freq2)
      ,.r2475_dramset1tmg6_freq2 (r2475_dramset1tmg6_freq2)
      ,.r2476_dramset1tmg7_freq2 (r2476_dramset1tmg7_freq2)
      ,.r2478_dramset1tmg9_freq2 (r2478_dramset1tmg9_freq2)
      ,.r2481_dramset1tmg12_freq2 (r2481_dramset1tmg12_freq2)
      ,.r2482_dramset1tmg13_freq2 (r2482_dramset1tmg13_freq2)
      ,.r2483_dramset1tmg14_freq2 (r2483_dramset1tmg14_freq2)
      ,.r2486_dramset1tmg17_freq2 (r2486_dramset1tmg17_freq2)
      ,.r2491_dramset1tmg23_freq2 (r2491_dramset1tmg23_freq2)
      ,.r2492_dramset1tmg24_freq2 (r2492_dramset1tmg24_freq2)
      ,.r2493_dramset1tmg25_freq2 (r2493_dramset1tmg25_freq2)
      ,.r2498_dramset1tmg30_freq2 (r2498_dramset1tmg30_freq2)
      ,.r2500_dramset1tmg32_freq2 (r2500_dramset1tmg32_freq2)
      ,.r2531_initmr0_freq2 (r2531_initmr0_freq2)
      ,.r2532_initmr1_freq2 (r2532_initmr1_freq2)
      ,.r2533_initmr2_freq2 (r2533_initmr2_freq2)
      ,.r2534_initmr3_freq2 (r2534_initmr3_freq2)
      ,.r2535_dfitmg0_freq2 (r2535_dfitmg0_freq2)
      ,.r2536_dfitmg1_freq2 (r2536_dfitmg1_freq2)
      ,.r2537_dfitmg2_freq2 (r2537_dfitmg2_freq2)
      ,.r2539_dfitmg4_freq2 (r2539_dfitmg4_freq2)
      ,.r2540_dfitmg5_freq2 (r2540_dfitmg5_freq2)
      ,.r2541_dfitmg6_freq2 (r2541_dfitmg6_freq2)
      ,.r2543_dfiupdtmg1_freq2 (r2543_dfiupdtmg1_freq2)
      ,.r2544_dfiupdtmg2_freq2 (r2544_dfiupdtmg2_freq2)
      ,.r2545_dfiupdtmg3_freq2 (r2545_dfiupdtmg3_freq2)
      ,.r2546_rfshset1tmg0_freq2 (r2546_rfshset1tmg0_freq2)
      ,.r2547_rfshset1tmg1_freq2 (r2547_rfshset1tmg1_freq2)
      ,.r2548_rfshset1tmg2_freq2 (r2548_rfshset1tmg2_freq2)
      ,.r2549_rfshset1tmg3_freq2 (r2549_rfshset1tmg3_freq2)
      ,.r2550_rfshset1tmg4_freq2 (r2550_rfshset1tmg4_freq2)
      ,.r2560_rfmset1tmg0_freq2 (r2560_rfmset1tmg0_freq2)
      ,.r2571_zqset1tmg0_freq2 (r2571_zqset1tmg0_freq2)
      ,.r2572_zqset1tmg1_freq2 (r2572_zqset1tmg1_freq2)
      ,.r2573_zqset1tmg2_freq2 (r2573_zqset1tmg2_freq2)
      ,.r2582_dqsoscctl0_freq2 (r2582_dqsoscctl0_freq2)
      ,.r2583_derateint_freq2 (r2583_derateint_freq2)
      ,.r2584_derateval0_freq2 (r2584_derateval0_freq2)
      ,.r2585_derateval1_freq2 (r2585_derateval1_freq2)
      ,.r2586_hwlptmg0_freq2 (r2586_hwlptmg0_freq2)
      ,.r2587_dvfsctl0_freq2 (r2587_dvfsctl0_freq2)
      ,.r2588_schedtmg0_freq2 (r2588_schedtmg0_freq2)
      ,.r2589_perfhpr1_freq2 (r2589_perfhpr1_freq2)
      ,.r2590_perflpr1_freq2 (r2590_perflpr1_freq2)
      ,.r2591_perfwr1_freq2 (r2591_perfwr1_freq2)
      ,.r2592_tmgcfg_freq2 (r2592_tmgcfg_freq2)
      ,.r2593_ranktmg0_freq2 (r2593_ranktmg0_freq2)
      ,.r2594_ranktmg1_freq2 (r2594_ranktmg1_freq2)
      ,.r2595_pwrtmg_freq2 (r2595_pwrtmg_freq2)
      ,.r2601_ddr4pprtmg0_freq2 (r2601_ddr4pprtmg0_freq2)
      ,.r2602_ddr4pprtmg1_freq2 (r2602_ddr4pprtmg1_freq2)
      ,.r2603_lnkeccctl0_freq2 (r2603_lnkeccctl0_freq2)
      ,.r2737_dramset1tmg0_freq3 (r2737_dramset1tmg0_freq3)
      ,.r2738_dramset1tmg1_freq3 (r2738_dramset1tmg1_freq3)
      ,.r2739_dramset1tmg2_freq3 (r2739_dramset1tmg2_freq3)
      ,.r2740_dramset1tmg3_freq3 (r2740_dramset1tmg3_freq3)
      ,.r2741_dramset1tmg4_freq3 (r2741_dramset1tmg4_freq3)
      ,.r2742_dramset1tmg5_freq3 (r2742_dramset1tmg5_freq3)
      ,.r2743_dramset1tmg6_freq3 (r2743_dramset1tmg6_freq3)
      ,.r2744_dramset1tmg7_freq3 (r2744_dramset1tmg7_freq3)
      ,.r2746_dramset1tmg9_freq3 (r2746_dramset1tmg9_freq3)
      ,.r2749_dramset1tmg12_freq3 (r2749_dramset1tmg12_freq3)
      ,.r2750_dramset1tmg13_freq3 (r2750_dramset1tmg13_freq3)
      ,.r2751_dramset1tmg14_freq3 (r2751_dramset1tmg14_freq3)
      ,.r2754_dramset1tmg17_freq3 (r2754_dramset1tmg17_freq3)
      ,.r2759_dramset1tmg23_freq3 (r2759_dramset1tmg23_freq3)
      ,.r2760_dramset1tmg24_freq3 (r2760_dramset1tmg24_freq3)
      ,.r2761_dramset1tmg25_freq3 (r2761_dramset1tmg25_freq3)
      ,.r2766_dramset1tmg30_freq3 (r2766_dramset1tmg30_freq3)
      ,.r2768_dramset1tmg32_freq3 (r2768_dramset1tmg32_freq3)
      ,.r2799_initmr0_freq3 (r2799_initmr0_freq3)
      ,.r2800_initmr1_freq3 (r2800_initmr1_freq3)
      ,.r2801_initmr2_freq3 (r2801_initmr2_freq3)
      ,.r2802_initmr3_freq3 (r2802_initmr3_freq3)
      ,.r2803_dfitmg0_freq3 (r2803_dfitmg0_freq3)
      ,.r2804_dfitmg1_freq3 (r2804_dfitmg1_freq3)
      ,.r2805_dfitmg2_freq3 (r2805_dfitmg2_freq3)
      ,.r2807_dfitmg4_freq3 (r2807_dfitmg4_freq3)
      ,.r2808_dfitmg5_freq3 (r2808_dfitmg5_freq3)
      ,.r2809_dfitmg6_freq3 (r2809_dfitmg6_freq3)
      ,.r2811_dfiupdtmg1_freq3 (r2811_dfiupdtmg1_freq3)
      ,.r2812_dfiupdtmg2_freq3 (r2812_dfiupdtmg2_freq3)
      ,.r2813_dfiupdtmg3_freq3 (r2813_dfiupdtmg3_freq3)
      ,.r2814_rfshset1tmg0_freq3 (r2814_rfshset1tmg0_freq3)
      ,.r2815_rfshset1tmg1_freq3 (r2815_rfshset1tmg1_freq3)
      ,.r2816_rfshset1tmg2_freq3 (r2816_rfshset1tmg2_freq3)
      ,.r2817_rfshset1tmg3_freq3 (r2817_rfshset1tmg3_freq3)
      ,.r2818_rfshset1tmg4_freq3 (r2818_rfshset1tmg4_freq3)
      ,.r2828_rfmset1tmg0_freq3 (r2828_rfmset1tmg0_freq3)
      ,.r2839_zqset1tmg0_freq3 (r2839_zqset1tmg0_freq3)
      ,.r2840_zqset1tmg1_freq3 (r2840_zqset1tmg1_freq3)
      ,.r2841_zqset1tmg2_freq3 (r2841_zqset1tmg2_freq3)
      ,.r2850_dqsoscctl0_freq3 (r2850_dqsoscctl0_freq3)
      ,.r2851_derateint_freq3 (r2851_derateint_freq3)
      ,.r2852_derateval0_freq3 (r2852_derateval0_freq3)
      ,.r2853_derateval1_freq3 (r2853_derateval1_freq3)
      ,.r2854_hwlptmg0_freq3 (r2854_hwlptmg0_freq3)
      ,.r2855_dvfsctl0_freq3 (r2855_dvfsctl0_freq3)
      ,.r2856_schedtmg0_freq3 (r2856_schedtmg0_freq3)
      ,.r2857_perfhpr1_freq3 (r2857_perfhpr1_freq3)
      ,.r2858_perflpr1_freq3 (r2858_perflpr1_freq3)
      ,.r2859_perfwr1_freq3 (r2859_perfwr1_freq3)
      ,.r2860_tmgcfg_freq3 (r2860_tmgcfg_freq3)
      ,.r2861_ranktmg0_freq3 (r2861_ranktmg0_freq3)
      ,.r2862_ranktmg1_freq3 (r2862_ranktmg1_freq3)
      ,.r2863_pwrtmg_freq3 (r2863_pwrtmg_freq3)
      ,.r2869_ddr4pprtmg0_freq3 (r2869_ddr4pprtmg0_freq3)
      ,.r2870_ddr4pprtmg1_freq3 (r2870_ddr4pprtmg1_freq3)
      ,.r2871_lnkeccctl0_freq3 (r2871_lnkeccctl0_freq3)

      );

   // ----------------------------------------------------------------------------
   // APB Slave State Machine
   // The APB Slave machine has the following states:
   // Idle : This is the default state. During Idle, if psel & penable
   // are asserted, apb_addr is latched.
   //
   // Address Decode: The SM enters Address Decode on psel & penable.
   // The  address is decoded in 4 clock cycles. During the last cycle the data
   // is latched (in case of a write). If there is an error during address
   // decode, pslverr is asserted with pready and the SM moves back to Idle
   //
   // Data Transfer: For a read operation the data is put on the bus and
   // pready is asserted for one clock cycle. In case of an error,
   // pslverr is asserted with pready
   // ----------------------------------------------------------------------------
   DWC_ddrctl_apb_slvfsm
   
     #(.N_APBFSMSTAT(N_APBFSMSTAT))
   slvfsm
     (.pclk           (pclk),
      .presetn        (presetn),
      .psel           (psel_int),
      .penable        (penable),
      .pwrite         (pwrite),
      //------------------------------
      //------------------------------
      .apb_slv_cs     (apb_slv_cs_unused),
      .apb_slv_ns     (apb_slv_ns),
      .pready         (pready_int),
      .write_en       (write_en),
      .write_en_pulse (write_en_pulse),
      .write_en_s0    (write_en_s0),
      .store_rqst     (store_rqst)
      );

   wire reg_ddrc_dis_srx_zqcl_bcm36in;
   wire reg_ddrc_dis_srx_zqcl_hwffc_bcm36in;
   wire [8-1:0] reg_ddrc_dqsosc_runtime_bcm36in;
   wire [8-1:0] reg_ddrc_wck2dqo_runtime_bcm36in;
   wire reg_ddrc_dis_dqsosc_srx_bcm36in;
   wire reg_ddrc_dis_opt_wrecc_collision_flush_bcm36in;
   wire reg_ddrc_prefer_write_bcm36in;
   wire reg_ddrc_pageclose_bcm36in;
   wire reg_ddrc_opt_wrcam_fill_level_bcm36in;
   wire reg_ddrc_dis_opt_ntt_by_act_bcm36in;
   wire reg_ddrc_dis_opt_ntt_by_pre_bcm36in;
   wire reg_ddrc_autopre_rmw_bcm36in;
   wire [(`MEMC_RDCMD_ENTRY_BITS)-1:0] reg_ddrc_lpr_num_entries_bcm36in;
   wire reg_ddrc_lpddr4_opt_act_timing_bcm36in;
   wire reg_ddrc_lpddr5_opt_act_timing_bcm36in;
   wire reg_ddrc_w_starve_free_running_bcm36in;
   wire reg_ddrc_opt_act_lat_bcm36in;
   wire reg_ddrc_prefer_read_bcm36in;
   wire reg_ddrc_dis_speculative_act_bcm36in;
   wire reg_ddrc_opt_vprw_sch_bcm36in;
   wire [4-1:0] reg_ddrc_delay_switch_write_bcm36in;
   wire [3-1:0] reg_ddrc_visible_window_limit_wr_bcm36in;
   wire [3-1:0] reg_ddrc_visible_window_limit_rd_bcm36in;
   wire [3-1:0] reg_ddrc_page_hit_limit_wr_bcm36in;
   wire [3-1:0] reg_ddrc_page_hit_limit_rd_bcm36in;
   wire reg_ddrc_opt_hit_gt_hpr_bcm36in;
   wire [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wrcam_lowthresh_bcm36in;
   wire [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wrcam_highthresh_bcm36in;
   wire [(`MEMC_WRCMD_ENTRY_BITS)-1:0] reg_ddrc_wr_pghit_num_thresh_bcm36in;
   wire [(`MEMC_RDCMD_ENTRY_BITS)-1:0] reg_ddrc_rd_pghit_num_thresh_bcm36in;
   wire [8-1:0] reg_ddrc_rd_act_idle_gap_bcm36in;
   wire [8-1:0] reg_ddrc_wr_act_idle_gap_bcm36in;
   wire [8-1:0] reg_ddrc_rd_page_exp_cycles_bcm36in;
   wire [8-1:0] reg_ddrc_wr_page_exp_cycles_bcm36in;
   wire [(`MEMC_WRCMD_ENTRY_BITS-1)-1:0] reg_ddrc_wrecc_cam_lowthresh_bcm36in;
   wire [(`MEMC_WRCMD_ENTRY_BITS-1)-1:0] reg_ddrc_wrecc_cam_highthresh_bcm36in;
   wire reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level_bcm36in;
   wire reg_ddrc_dis_opt_valid_wrecc_cam_fill_level_bcm36in;
   wire reg_ddrc_data_poison_en_bcm36in;
   wire reg_ddrc_data_poison_bit_bcm36in;
   wire reg_ddrc_ecc_region_parity_lock_bcm36in;
   wire reg_ddrc_ecc_region_waste_lock_bcm36in;
   wire reg_ddrc_med_ecc_en_bcm36in;
   wire reg_ddrc_blk_channel_active_term_bcm36in;
   wire [5-1:0] reg_ddrc_active_blk_channel_bcm36in;
   wire [12-1:0] reg_ddrc_ecc_poison_col_bcm36in;
   wire [(`MEMC_RANK_BITS)-1:0] reg_ddrc_ecc_poison_rank_bcm36in;
   wire [(`MEMC_PAGE_BITS)-1:0] reg_ddrc_ecc_poison_row_bcm36in;
   wire [(`MEMC_BANK_BITS)-1:0] reg_ddrc_ecc_poison_bank_bcm36in;
   wire [(`MEMC_BG_BITS)-1:0] reg_ddrc_ecc_poison_bg_bcm36in;
   wire [32-1:0] reg_ddrc_ecc_poison_data_31_0_bcm36in;
   wire [8-1:0] reg_ddrc_ecc_poison_data_71_64_bcm36in;
   wire reg_ddrc_dis_wc_bcm36in;
   wire reg_ddrc_dis_max_rank_rd_opt_bcm36in;
   wire reg_ddrc_dis_max_rank_wr_opt_bcm36in;
   wire [4-1:0] reg_ddrc_max_rank_rd_bcm36in;
   wire [4-1:0] reg_ddrc_max_rank_wr_bcm36in;
   wire [6-1:0] reg_ddrc_addrmap_cs_bit0_map0_bcm36in;
   wire [6-1:0] reg_ddrc_addrmap_bank_b0_map0_bcm36in;
   wire [6-1:0] reg_ddrc_addrmap_bank_b1_map0_bcm36in;
   wire [6-1:0] reg_ddrc_addrmap_bank_b2_map0_bcm36in;
   wire [6-1:0] reg_ddrc_addrmap_bg_b0_map0_bcm36in;
   wire [6-1:0] reg_ddrc_addrmap_bg_b1_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_col_b7_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_col_b8_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_col_b9_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_col_b10_map0_bcm36in;
   wire [4-1:0] reg_ddrc_addrmap_col_b3_map0_bcm36in;
   wire [4-1:0] reg_ddrc_addrmap_col_b4_map0_bcm36in;
   wire [4-1:0] reg_ddrc_addrmap_col_b5_map0_bcm36in;
   wire [4-1:0] reg_ddrc_addrmap_col_b6_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b14_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b15_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b16_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b17_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b10_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b11_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b12_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b13_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b6_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b7_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b8_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b9_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b2_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b3_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b4_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b5_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b0_map0_bcm36in;
   wire [5-1:0] reg_ddrc_addrmap_row_b1_map0_bcm36in;
   wire reg_arb_go2critical_en_port0_bcm36in;
   wire reg_arb_pagematch_limit_port0_bcm36in;
   wire [10-1:0] reg_arb_rd_port_priority_port0_bcm36in;
   wire reg_arb_rd_port_aging_en_port0_bcm36in;
   wire reg_arb_rd_port_urgent_en_port0_bcm36in;
   wire reg_arb_rd_port_pagematch_en_port0_bcm36in;
   wire [4-1:0] reg_arb_rrb_lock_threshold_port0_bcm36in;
   wire [10-1:0] reg_arb_wr_port_priority_port0_bcm36in;
   wire reg_arb_wr_port_aging_en_port0_bcm36in;
   wire reg_arb_wr_port_urgent_en_port0_bcm36in;
   wire reg_arb_wr_port_pagematch_en_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_MLW)-1:0] reg_arba0_rqos_map_level1_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_MLW)-1:0] reg_arba0_rqos_map_level2_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region0_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region1_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_RW)-1:0] reg_arba0_rqos_map_region2_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_TW)-1:0] reg_arb_rqos_map_timeoutb_port0_bcm36in;
   wire [(`UMCTL2_XPI_RQOS_TW)-1:0] reg_arb_rqos_map_timeoutr_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_MLW)-1:0] reg_arba0_wqos_map_level1_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_MLW)-1:0] reg_arba0_wqos_map_level2_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region0_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region1_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_RW)-1:0] reg_arba0_wqos_map_region2_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_TW)-1:0] reg_arb_wqos_map_timeout1_port0_bcm36in;
   wire [(`UMCTL2_XPI_WQOS_TW)-1:0] reg_arb_wqos_map_timeout2_port0_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_min_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_max_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_t_faw_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_wr2pre_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_t_rc_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_rd2pre_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_t_xp_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_write_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_read_latency_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_write_latency_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_wr2mr_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_rd2mr_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_t_mr_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_t_rp_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_t_ccd_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_t_ckcsx_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_s_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_s_freq0_bcm36in;
   wire [5-1:0] reg_ddrc_t_ccd_s_freq0_bcm36in;
   wire [4-1:0] reg_ddrc_t_cmdcke_freq0_bcm36in;
   wire [4-1:0] reg_ddrc_t_ppd_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_t_ccd_mw_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_odtloff_freq0_bcm36in;
   wire [12-1:0] reg_ddrc_t_xsr_freq0_bcm36in;
   wire [9-1:0] reg_ddrc_t_osco_freq0_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_disable_freq0_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_enable_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_max_wr_sync_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_max_rd_sync_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_s_freq0_bcm36in;
   wire [2-1:0] reg_ddrc_bank_org_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_rda2pre_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_wra2pre_freq0_bcm36in;
   wire [3-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_emr_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_mr_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_mr5_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_mr4_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_mr6_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_mr22_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_wrcslat_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_rdcslat_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_dfi_twck_delay_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_dis_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_fs_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_wr_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_rd_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_cs_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_fast_toggle_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq0_bcm36in;
   wire reg_ddrc_dfi_twck_toggle_post_rd_en_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0_bcm36in;
   wire [9-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0_bcm36in;
   wire [20-1:0] reg_ddrc_t_zq_short_interval_x1024_freq0_bcm36in;
   wire [10-1:0] reg_ddrc_t_zq_reset_nop_freq0_bcm36in;
   wire [32-1:0] reg_ddrc_mr4_read_interval_freq0_bcm36in;
   wire [12-1:0] reg_ddrc_hw_lp_idle_x32_freq0_bcm36in;
   wire reg_ddrc_dvfsq_enable_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_pageclose_timer_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_rdwr_idle_gap_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_hpr_max_starve_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_hpr_xact_run_length_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_lpr_max_starve_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_lpr_xact_run_length_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_w_max_starve_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_w_xact_run_length_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_rd_gap_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_wr_gap_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_dr_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_dr_freq0_bcm36in;
   wire [7-1:0] reg_ddrc_powerdown_to_x32_freq0_bcm36in;
   wire [10-1:0] reg_ddrc_selfref_to_x32_freq0_bcm36in;
   wire [22-1:0] reg_ddrc_t_pgm_x1_x1024_freq0_bcm36in;
   wire reg_ddrc_t_pgm_x1_sel_freq0_bcm36in;
   wire [16-1:0] reg_ddrc_t_pgmpst_x32_freq0_bcm36in;
   wire [6-1:0] reg_ddrc_t_pgm_exit_freq0_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_min_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_max_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_t_faw_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_wr2pre_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_t_rc_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_rd2pre_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_t_xp_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_write_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_read_latency_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_write_latency_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_wr2mr_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_rd2mr_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_t_mr_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_t_rp_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_t_ccd_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_t_ckcsx_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_s_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_s_freq1_bcm36in;
   wire [5-1:0] reg_ddrc_t_ccd_s_freq1_bcm36in;
   wire [4-1:0] reg_ddrc_t_cmdcke_freq1_bcm36in;
   wire [4-1:0] reg_ddrc_t_ppd_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_t_ccd_mw_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_odtloff_freq1_bcm36in;
   wire [12-1:0] reg_ddrc_t_xsr_freq1_bcm36in;
   wire [9-1:0] reg_ddrc_t_osco_freq1_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_disable_freq1_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_enable_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_max_wr_sync_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_max_rd_sync_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_s_freq1_bcm36in;
   wire [2-1:0] reg_ddrc_bank_org_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_rda2pre_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_wra2pre_freq1_bcm36in;
   wire [3-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_emr_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_mr_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_mr5_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_mr4_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_mr6_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_mr22_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_wrcslat_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_rdcslat_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_dfi_twck_delay_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_dis_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_fs_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_wr_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_rd_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_cs_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_fast_toggle_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq1_bcm36in;
   wire reg_ddrc_dfi_twck_toggle_post_rd_en_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1_bcm36in;
   wire [9-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1_bcm36in;
   wire [20-1:0] reg_ddrc_t_zq_short_interval_x1024_freq1_bcm36in;
   wire [10-1:0] reg_ddrc_t_zq_reset_nop_freq1_bcm36in;
   wire [32-1:0] reg_ddrc_mr4_read_interval_freq1_bcm36in;
   wire [12-1:0] reg_ddrc_hw_lp_idle_x32_freq1_bcm36in;
   wire reg_ddrc_dvfsq_enable_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_pageclose_timer_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_rdwr_idle_gap_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_hpr_max_starve_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_hpr_xact_run_length_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_lpr_max_starve_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_lpr_xact_run_length_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_w_max_starve_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_w_xact_run_length_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_rd_gap_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_wr_gap_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_dr_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_dr_freq1_bcm36in;
   wire [7-1:0] reg_ddrc_powerdown_to_x32_freq1_bcm36in;
   wire [10-1:0] reg_ddrc_selfref_to_x32_freq1_bcm36in;
   wire [22-1:0] reg_ddrc_t_pgm_x1_x1024_freq1_bcm36in;
   wire reg_ddrc_t_pgm_x1_sel_freq1_bcm36in;
   wire [16-1:0] reg_ddrc_t_pgmpst_x32_freq1_bcm36in;
   wire [6-1:0] reg_ddrc_t_pgm_exit_freq1_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_min_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_max_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_t_faw_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_wr2pre_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_t_rc_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_rd2pre_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_t_xp_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_write_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_read_latency_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_write_latency_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_wr2mr_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_rd2mr_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_t_mr_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_t_rp_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_t_ccd_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_t_ckcsx_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_s_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_s_freq2_bcm36in;
   wire [5-1:0] reg_ddrc_t_ccd_s_freq2_bcm36in;
   wire [4-1:0] reg_ddrc_t_cmdcke_freq2_bcm36in;
   wire [4-1:0] reg_ddrc_t_ppd_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_t_ccd_mw_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_odtloff_freq2_bcm36in;
   wire [12-1:0] reg_ddrc_t_xsr_freq2_bcm36in;
   wire [9-1:0] reg_ddrc_t_osco_freq2_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_disable_freq2_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_enable_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_max_wr_sync_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_max_rd_sync_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_s_freq2_bcm36in;
   wire [2-1:0] reg_ddrc_bank_org_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_rda2pre_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_wra2pre_freq2_bcm36in;
   wire [3-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_emr_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_mr_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_mr5_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_mr4_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_mr6_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_mr22_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_wrcslat_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_rdcslat_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_dfi_twck_delay_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_dis_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_fs_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_wr_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_rd_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_cs_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_fast_toggle_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq2_bcm36in;
   wire reg_ddrc_dfi_twck_toggle_post_rd_en_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2_bcm36in;
   wire [9-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2_bcm36in;
   wire [20-1:0] reg_ddrc_t_zq_short_interval_x1024_freq2_bcm36in;
   wire [10-1:0] reg_ddrc_t_zq_reset_nop_freq2_bcm36in;
   wire [32-1:0] reg_ddrc_mr4_read_interval_freq2_bcm36in;
   wire [12-1:0] reg_ddrc_hw_lp_idle_x32_freq2_bcm36in;
   wire reg_ddrc_dvfsq_enable_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_pageclose_timer_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_rdwr_idle_gap_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_hpr_max_starve_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_hpr_xact_run_length_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_lpr_max_starve_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_lpr_xact_run_length_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_w_max_starve_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_w_xact_run_length_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_rd_gap_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_wr_gap_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_dr_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_dr_freq2_bcm36in;
   wire [7-1:0] reg_ddrc_powerdown_to_x32_freq2_bcm36in;
   wire [10-1:0] reg_ddrc_selfref_to_x32_freq2_bcm36in;
   wire [22-1:0] reg_ddrc_t_pgm_x1_x1024_freq2_bcm36in;
   wire reg_ddrc_t_pgm_x1_sel_freq2_bcm36in;
   wire [16-1:0] reg_ddrc_t_pgmpst_x32_freq2_bcm36in;
   wire [6-1:0] reg_ddrc_t_pgm_exit_freq2_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_min_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_t_ras_max_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_t_faw_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_wr2pre_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_t_rc_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_rd2pre_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_t_xp_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_write_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_read_latency_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_write_latency_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_wr2mr_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_rd2mr_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_t_mr_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_t_rp_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_t_ccd_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_t_rcd_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_t_ckcsx_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_s_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_t_rrd_s_freq3_bcm36in;
   wire [5-1:0] reg_ddrc_t_ccd_s_freq3_bcm36in;
   wire [4-1:0] reg_ddrc_t_cmdcke_freq3_bcm36in;
   wire [4-1:0] reg_ddrc_t_ppd_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_t_ccd_mw_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_odtloff_freq3_bcm36in;
   wire [12-1:0] reg_ddrc_t_xsr_freq3_bcm36in;
   wire [9-1:0] reg_ddrc_t_osco_freq3_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_disable_freq3_bcm36in;
   wire [10-1:0] reg_ddrc_t_vrcg_enable_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_max_wr_sync_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_max_rd_sync_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_s_freq3_bcm36in;
   wire [2-1:0] reg_ddrc_bank_org_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_rda2pre_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_wra2pre_freq3_bcm36in;
   wire [3-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_emr_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_mr_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_mr5_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_mr4_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_mr6_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_mr22_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_wrcslat_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_dfi_tphy_rdcslat_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_dfi_twck_delay_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_dis_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_fs_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_wr_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_en_rd_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_cs_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_fast_toggle_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_twck_toggle_post_rd_freq3_bcm36in;
   wire reg_ddrc_dfi_twck_toggle_post_rd_en_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3_bcm36in;
   wire [9-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3_bcm36in;
   wire [20-1:0] reg_ddrc_t_zq_short_interval_x1024_freq3_bcm36in;
   wire [10-1:0] reg_ddrc_t_zq_reset_nop_freq3_bcm36in;
   wire [32-1:0] reg_ddrc_mr4_read_interval_freq3_bcm36in;
   wire [12-1:0] reg_ddrc_hw_lp_idle_x32_freq3_bcm36in;
   wire reg_ddrc_dvfsq_enable_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_pageclose_timer_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_rdwr_idle_gap_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_hpr_max_starve_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_hpr_xact_run_length_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_lpr_max_starve_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_lpr_xact_run_length_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_w_max_starve_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_w_xact_run_length_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_rd_gap_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_diff_rank_wr_gap_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_wr2rd_dr_freq3_bcm36in;
   wire [8-1:0] reg_ddrc_rd2wr_dr_freq3_bcm36in;
   wire [7-1:0] reg_ddrc_powerdown_to_x32_freq3_bcm36in;
   wire [10-1:0] reg_ddrc_selfref_to_x32_freq3_bcm36in;
   wire [22-1:0] reg_ddrc_t_pgm_x1_x1024_freq3_bcm36in;
   wire reg_ddrc_t_pgm_x1_sel_freq3_bcm36in;
   wire [16-1:0] reg_ddrc_t_pgmpst_x32_freq3_bcm36in;
   wire [6-1:0] reg_ddrc_t_pgm_exit_freq3_bcm36in;


   // ----------------------------------------------------------------------------
   // output to the core is given from here. Each
   // register value is assigned to the corresponding core signal
   // ----------------------------------------------------------------------------     
   DWC_ddrctl_apb_coreif
   
     #(.APB_AW              (APB_AW),
       .REG_WIDTH           (REG_WIDTH),
       .BCM_F_SYNC_TYPE_C2P (BCM_F_SYNC_TYPE_C2P),
       .BCM_F_SYNC_TYPE_P2C (BCM_F_SYNC_TYPE_P2C),
       .BCM_R_SYNC_TYPE_C2P (BCM_R_SYNC_TYPE_C2P),
       .BCM_R_SYNC_TYPE_P2C (BCM_R_SYNC_TYPE_P2C),
       .REG_OUTPUTS_C2P     (REG_OUTPUTS_C2P),
       .REG_OUTPUTS_P2C     (REG_OUTPUTS_P2C),
       .BCM_VERIF_EN        (BCM_VERIF_EN),
       .RW_REGS             (RW_REGS),
       .RWSELWIDTH          (RWSELWIDTH)
       ,.ECC_CORRECTED_BIT_NUM_WIDTH (ECC_CORRECTED_BIT_NUM_WIDTH)
       ,.ECC_CORRECTED_ERR_WIDTH     (ECC_CORRECTED_ERR_WIDTH)
       ,.ECC_UNCORRECTED_ERR_WIDTH   (ECC_UNCORRECTED_ERR_WIDTH)
       )
     coreif
     (
      .apb_clk            (pclk),
      .apb_rst            (presetn),
      .core_ddrc_core_clk (core_ddrc_core_clk),
      .core_ddrc_core_clk_apbrw (core_ddrc_core_clk_apbrw),
      .sync_core_ddrc_rstn(sync_core_ddrc_rstn),
      .core_ddrc_rstn     (core_ddrc_rstn),
      .rwselect           (rwselect),// should be rwselect s0 but address is latched
      .write_en           (write_en_s0)
      ,.aclk_0             (aclk_0)
      ,.sync_aresetn_0     (sync_aresetn_0)

   //------------------------
   // Register REGB_DDRC_CH0.MSTR0
   //------------------------
      ,.r0_mstr0 (r0_mstr0)
      ,.reg_ddrc_lpddr4 (reg_ddrc_lpddr4)
      ,.reg_apb_lpddr4 (reg_apb_lpddr4)
      ,.reg_arba0_lpddr4 (reg_arba0_lpddr4)
      ,.reg_ddrc_lpddr5 (reg_ddrc_lpddr5)
      ,.reg_apb_lpddr5 (reg_apb_lpddr5)
      ,.reg_arba0_lpddr5 (reg_arba0_lpddr5)
      ,.reg_ddrc_lpddr5x (reg_ddrc_lpddr5x)
      ,.reg_apb_lpddr5x (reg_apb_lpddr5x)
      ,.reg_arba0_lpddr5x (reg_arba0_lpddr5x)
      ,.reg_ddrc_data_bus_width (reg_ddrc_data_bus_width)
      ,.reg_apb_data_bus_width (reg_apb_data_bus_width)
      ,.reg_arba0_data_bus_width (reg_arba0_data_bus_width)
      ,.reg_ddrc_burst_rdwr (reg_ddrc_burst_rdwr)
      ,.reg_apb_burst_rdwr (reg_apb_burst_rdwr)
      ,.reg_arba0_burst_rdwr (reg_arba0_burst_rdwr)
      ,.reg_ddrc_active_ranks (reg_ddrc_active_ranks)
      ,.reg_apb_active_ranks (reg_apb_active_ranks)
      ,.reg_arba0_active_ranks (reg_arba0_active_ranks)
   //------------------------
   // Register REGB_DDRC_CH0.MSTR2
   //------------------------
      ,.r2_mstr2 (r2_mstr2)
      ,.reg_ddrc_target_frequency (reg_ddrc_target_frequency)
   //------------------------
   // Register REGB_DDRC_CH0.MSTR4
   //------------------------
      ,.r4_mstr4 (r4_mstr4)
      ,.reg_ddrc_wck_on (reg_ddrc_wck_on)
      ,.reg_ddrc_wck_suspend_en (reg_ddrc_wck_suspend_en)
      ,.reg_ddrc_ws_off_en (reg_ddrc_ws_off_en)
   //------------------------
   // Register REGB_DDRC_CH0.STAT
   //------------------------
      ,.r5_stat (r5_stat)
      ,.ddrc_reg_operating_mode (ddrc_reg_operating_mode)
      ,.ddrc_reg_selfref_type (ddrc_reg_selfref_type)
      ,.ddrc_reg_selfref_state (ddrc_reg_selfref_state)
      ,.ddrc_reg_selfref_cam_not_empty (ddrc_reg_selfref_cam_not_empty)
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL0
   //------------------------
      ,.r8_mrctrl0 (r8_mrctrl0)
      ,.reg_ddrc_mr_type (reg_ddrc_mr_type)
      ,.reg_ddrc_sw_init_int (reg_ddrc_sw_init_int)
      ,.reg_ddrc_mr_rank (reg_ddrc_mr_rank)
      ,.reg_ddrc_mr_addr (reg_ddrc_mr_addr)
      ,.reg_ddrc_mrr_done_clr_ack_pclk (reg_ddrc_mrr_done_clr_ack_pclk)
      ,.reg_ddrc_mrr_done_clr (reg_ddrc_mrr_done_clr)
      ,.reg_ddrc_dis_mrrw_trfc (reg_ddrc_dis_mrrw_trfc)
      ,.reg_ddrc_ppr_en (reg_ddrc_ppr_en)
      ,.reg_ddrc_ppr_pgmpst_en (reg_ddrc_ppr_pgmpst_en)
      ,.reg_ddrc_mr_wr_ack_pclk (reg_ddrc_mr_wr_ack_pclk)
      ,.ff_regb_ddrc_ch0_mr_wr_saved (ff_regb_ddrc_ch0_mr_wr_saved)
      ,.reg_ddrc_mr_wr (reg_ddrc_mr_wr)
   //------------------------
   // Register REGB_DDRC_CH0.MRCTRL1
   //------------------------
      ,.r9_mrctrl1 (r9_mrctrl1)
      ,.reg_ddrc_mr_data (reg_ddrc_mr_data)
   //------------------------
   // Register REGB_DDRC_CH0.MRSTAT
   //------------------------
      ,.r11_mrstat (r11_mrstat)
      ,.ddrc_reg_mr_wr_busy_int (ddrc_reg_mr_wr_busy_int)
      ,.ddrc_reg_mr_wr_busy (ddrc_reg_mr_wr_busy)
      ,.ddrc_reg_mrr_done (ddrc_reg_mrr_done)
      ,.ddrc_reg_ppr_done (ddrc_reg_ppr_done)
   //------------------------
   // Register REGB_DDRC_CH0.MRRDATA0
   //------------------------
      ,.r12_mrrdata0 (r12_mrrdata0)
      ,.ddrc_reg_mrr_data_lwr (ddrc_reg_mrr_data_lwr)
   //------------------------
   // Register REGB_DDRC_CH0.MRRDATA1
   //------------------------
      ,.r13_mrrdata1 (r13_mrrdata1)
      ,.ddrc_reg_mrr_data_upr (ddrc_reg_mrr_data_upr)
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL0
   //------------------------
      ,.r14_deratectl0 (r14_deratectl0)
      ,.reg_ddrc_derate_enable (reg_ddrc_derate_enable)
      ,.reg_ddrc_lpddr4_refresh_mode (reg_ddrc_lpddr4_refresh_mode)
      ,.reg_ddrc_derate_mr4_pause_fc (reg_ddrc_derate_mr4_pause_fc)
      ,.reg_ddrc_dis_trefi_x6x8 (reg_ddrc_dis_trefi_x6x8)
      ,.reg_ddrc_dis_trefi_x0125 (reg_ddrc_dis_trefi_x0125)
      ,.reg_ddrc_use_slow_rm_in_low_temp (reg_ddrc_use_slow_rm_in_low_temp)
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL1
   //------------------------
      ,.r15_deratectl1 (r15_deratectl1)
      ,.reg_ddrc_active_derate_byte_rank0 (reg_ddrc_active_derate_byte_rank0)
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL2
   //------------------------
      ,.r16_deratectl2 (r16_deratectl2)
      ,.reg_ddrc_active_derate_byte_rank1 (reg_ddrc_active_derate_byte_rank1)
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL5
   //------------------------
      ,.r19_deratectl5 (r19_deratectl5[REG_WIDTH-1:0])
      ,.reg_ddrc_derate_temp_limit_intr_en (reg_ddrc_derate_temp_limit_intr_en)
      ,.reg_ddrc_derate_temp_limit_intr_clr_ack_pclk (reg_ddrc_derate_temp_limit_intr_clr_ack_pclk)
      ,.reg_ddrc_derate_temp_limit_intr_clr (reg_ddrc_derate_temp_limit_intr_clr)
      ,.reg_ddrc_derate_temp_limit_intr_force_ack_pclk (reg_ddrc_derate_temp_limit_intr_force_ack_pclk)
      ,.reg_ddrc_derate_temp_limit_intr_force (reg_ddrc_derate_temp_limit_intr_force)
   //------------------------
   // Register REGB_DDRC_CH0.DERATECTL6
   //------------------------
      ,.r20_deratectl6 (r20_deratectl6)
      ,.reg_ddrc_derate_mr4_tuf_dis (reg_ddrc_derate_mr4_tuf_dis)
   //------------------------
   // Register REGB_DDRC_CH0.DERATESTAT0
   //------------------------
      ,.r22_deratestat0 (r22_deratestat0)
      ,.ddrc_reg_derate_temp_limit_intr (ddrc_reg_derate_temp_limit_intr)
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGCTL
   //------------------------
      ,.r24_deratedbgctl (r24_deratedbgctl)
      ,.reg_ddrc_dbg_mr4_rank_sel (reg_ddrc_dbg_mr4_rank_sel)
   //------------------------
   // Register REGB_DDRC_CH0.DERATEDBGSTAT
   //------------------------
      ,.r25_deratedbgstat (r25_deratedbgstat)
      ,.ddrc_reg_dbg_mr4_byte0 (ddrc_reg_dbg_mr4_byte0)
      ,.ddrc_reg_dbg_mr4_byte1 (ddrc_reg_dbg_mr4_byte1)
      ,.ddrc_reg_dbg_mr4_byte2 (ddrc_reg_dbg_mr4_byte2)
      ,.ddrc_reg_dbg_mr4_byte3 (ddrc_reg_dbg_mr4_byte3)
   //------------------------
   // Register REGB_DDRC_CH0.PWRCTL
   //------------------------
      ,.r26_pwrctl (r26_pwrctl)
      ,.reg_ddrc_selfref_en (reg_ddrc_selfref_en)
      ,.reg_ddrc_powerdown_en (reg_ddrc_powerdown_en)
      ,.reg_ddrc_en_dfi_dram_clk_disable (reg_ddrc_en_dfi_dram_clk_disable)
      ,.reg_ddrc_selfref_sw (reg_ddrc_selfref_sw)
      ,.reg_ddrc_stay_in_selfref (reg_ddrc_stay_in_selfref)
      ,.reg_ddrc_dis_cam_drain_selfref (reg_ddrc_dis_cam_drain_selfref)
      ,.reg_ddrc_lpddr4_sr_allowed (reg_ddrc_lpddr4_sr_allowed)
      ,.reg_ddrc_dsm_en (reg_ddrc_dsm_en)
   //------------------------
   // Register REGB_DDRC_CH0.HWLPCTL
   //------------------------
      ,.r27_hwlpctl (r27_hwlpctl)
      ,.reg_ddrc_hw_lp_en (reg_ddrc_hw_lp_en)
      ,.reg_ddrc_hw_lp_exit_idle_en (reg_ddrc_hw_lp_exit_idle_en)
   //------------------------
   // Register REGB_DDRC_CH0.CLKGATECTL
   //------------------------
      ,.r29_clkgatectl (r29_clkgatectl)
      ,.reg_ddrc_bsm_clk_on (reg_ddrc_bsm_clk_on)
   //------------------------
   // Register REGB_DDRC_CH0.RFSHMOD0
   //------------------------
      ,.r30_rfshmod0 (r30_rfshmod0)
      ,.reg_ddrc_refresh_burst (reg_ddrc_refresh_burst)
      ,.reg_ddrc_auto_refab_en (reg_ddrc_auto_refab_en)
      ,.reg_ddrc_per_bank_refresh (reg_ddrc_per_bank_refresh)
      ,.reg_ddrc_per_bank_refresh_opt_en (reg_ddrc_per_bank_refresh_opt_en)
      ,.reg_ddrc_fixed_crit_refpb_bank_en (reg_ddrc_fixed_crit_refpb_bank_en)
   //------------------------
   // Register REGB_DDRC_CH0.RFSHCTL0
   //------------------------
      ,.r32_rfshctl0 (r32_rfshctl0)
      ,.reg_ddrc_dis_auto_refresh (reg_ddrc_dis_auto_refresh)
      ,.reg_ddrc_refresh_update_level (reg_ddrc_refresh_update_level)
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD0
   //------------------------
      ,.r33_rfmmod0 (r33_rfmmod0)
      ,.reg_ddrc_rfm_en (reg_ddrc_rfm_en)
      ,.reg_ddrc_rfmsbc (reg_ddrc_rfmsbc)
      ,.reg_ddrc_raaimt (reg_ddrc_raaimt)
      ,.reg_ddrc_raamult (reg_ddrc_raamult)
      ,.reg_ddrc_raadec (reg_ddrc_raadec)
      ,.reg_ddrc_rfmth_rm_thr (reg_ddrc_rfmth_rm_thr)
   //------------------------
   // Register REGB_DDRC_CH0.RFMMOD1
   //------------------------
      ,.r34_rfmmod1 (r34_rfmmod1)
      ,.reg_ddrc_init_raa_cnt (reg_ddrc_init_raa_cnt)
   //------------------------
   // Register REGB_DDRC_CH0.RFMCTL
   //------------------------
      ,.r35_rfmctl (r35_rfmctl)
      ,.reg_ddrc_dbg_raa_rank (reg_ddrc_dbg_raa_rank)
      ,.reg_ddrc_dbg_raa_bg_bank (reg_ddrc_dbg_raa_bg_bank)
   //------------------------
   // Register REGB_DDRC_CH0.RFMSTAT
   //------------------------
      ,.r36_rfmstat (r36_rfmstat)
      ,.ddrc_reg_rank_raa_cnt_gt0 (ddrc_reg_rank_raa_cnt_gt0)
      ,.ddrc_reg_dbg_raa_cnt (ddrc_reg_dbg_raa_cnt)
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL0
   //------------------------
      ,.r37_zqctl0 (r37_zqctl0)
      ,.reg_ddrc_zq_resistor_shared (reg_ddrc_zq_resistor_shared)
      ,.reg_ddrc_dis_auto_zq (reg_ddrc_dis_auto_zq)
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL1
   //------------------------
      ,.r38_zqctl1 (r38_zqctl1)
      ,.reg_ddrc_zq_reset_ack_pclk (reg_ddrc_zq_reset_ack_pclk)
      ,.ff_regb_ddrc_ch0_zq_reset_saved (ff_regb_ddrc_ch0_zq_reset_saved)
      ,.reg_ddrc_zq_reset (reg_ddrc_zq_reset)
   //------------------------
   // Register REGB_DDRC_CH0.ZQCTL2
   //------------------------
      ,.r39_zqctl2 (r39_zqctl2[REG_WIDTH-1:0])
      ,.reg_ddrc_dis_srx_zqcl (reg_ddrc_dis_srx_zqcl_bcm36in)
      ,.reg_ddrc_dis_srx_zqcl_hwffc (reg_ddrc_dis_srx_zqcl_hwffc_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.ZQSTAT
   //------------------------
      ,.r40_zqstat (r40_zqstat)
      ,.ddrc_reg_zq_reset_busy_int (ddrc_reg_zq_reset_busy_int)
      ,.ddrc_reg_zq_reset_busy (ddrc_reg_zq_reset_busy)
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCRUNTIME
   //------------------------
      ,.r41_dqsoscruntime (r41_dqsoscruntime[REG_WIDTH-1:0])
      ,.reg_ddrc_dqsosc_runtime (reg_ddrc_dqsosc_runtime_bcm36in)
      ,.reg_ddrc_wck2dqo_runtime (reg_ddrc_wck2dqo_runtime_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCSTAT0
   //------------------------
      ,.r42_dqsoscstat0 (r42_dqsoscstat0)
      ,.ddrc_reg_dqsosc_state (ddrc_reg_dqsosc_state)
      ,.ddrc_reg_dqsosc_per_rank_stat (ddrc_reg_dqsosc_per_rank_stat)
   //------------------------
   // Register REGB_DDRC_CH0.DQSOSCCFG0
   //------------------------
      ,.r43_dqsosccfg0 (r43_dqsosccfg0[REG_WIDTH-1:0])
      ,.reg_ddrc_dis_dqsosc_srx (reg_ddrc_dis_dqsosc_srx_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.SCHED0
   //------------------------
      ,.r45_sched0 (r45_sched0[REG_WIDTH-1:0])
      ,.reg_ddrc_dis_opt_wrecc_collision_flush (reg_ddrc_dis_opt_wrecc_collision_flush_bcm36in)
      ,.reg_ddrc_prefer_write (reg_ddrc_prefer_write_bcm36in)
      ,.reg_ddrc_pageclose (reg_ddrc_pageclose_bcm36in)
      ,.reg_ddrc_opt_wrcam_fill_level (reg_ddrc_opt_wrcam_fill_level_bcm36in)
      ,.reg_ddrc_dis_opt_ntt_by_act (reg_ddrc_dis_opt_ntt_by_act_bcm36in)
      ,.reg_ddrc_dis_opt_ntt_by_pre (reg_ddrc_dis_opt_ntt_by_pre_bcm36in)
      ,.reg_ddrc_autopre_rmw (reg_ddrc_autopre_rmw_bcm36in)
      ,.reg_ddrc_lpr_num_entries (reg_ddrc_lpr_num_entries_bcm36in)
      ,.reg_ddrc_lpddr4_opt_act_timing (reg_ddrc_lpddr4_opt_act_timing_bcm36in)
      ,.reg_ddrc_lpddr5_opt_act_timing (reg_ddrc_lpddr5_opt_act_timing_bcm36in)
      ,.reg_ddrc_w_starve_free_running (reg_ddrc_w_starve_free_running_bcm36in)
      ,.reg_ddrc_opt_act_lat (reg_ddrc_opt_act_lat_bcm36in)
      ,.reg_ddrc_prefer_read (reg_ddrc_prefer_read_bcm36in)
      ,.reg_ddrc_dis_speculative_act (reg_ddrc_dis_speculative_act_bcm36in)
      ,.reg_ddrc_opt_vprw_sch (reg_ddrc_opt_vprw_sch_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.SCHED1
   //------------------------
      ,.r46_sched1 (r46_sched1[REG_WIDTH-1:0])
      ,.reg_ddrc_delay_switch_write (reg_ddrc_delay_switch_write_bcm36in)
      ,.reg_ddrc_visible_window_limit_wr (reg_ddrc_visible_window_limit_wr_bcm36in)
      ,.reg_ddrc_visible_window_limit_rd (reg_ddrc_visible_window_limit_rd_bcm36in)
      ,.reg_ddrc_page_hit_limit_wr (reg_ddrc_page_hit_limit_wr_bcm36in)
      ,.reg_ddrc_page_hit_limit_rd (reg_ddrc_page_hit_limit_rd_bcm36in)
      ,.reg_ddrc_opt_hit_gt_hpr (reg_ddrc_opt_hit_gt_hpr_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.SCHED3
   //------------------------
      ,.r48_sched3 (r48_sched3[REG_WIDTH-1:0])
      ,.reg_ddrc_wrcam_lowthresh (reg_ddrc_wrcam_lowthresh_bcm36in)
      ,.reg_ddrc_wrcam_highthresh (reg_ddrc_wrcam_highthresh_bcm36in)
      ,.reg_ddrc_wr_pghit_num_thresh (reg_ddrc_wr_pghit_num_thresh_bcm36in)
      ,.reg_ddrc_rd_pghit_num_thresh (reg_ddrc_rd_pghit_num_thresh_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.SCHED4
   //------------------------
      ,.r49_sched4 (r49_sched4[REG_WIDTH-1:0])
      ,.reg_ddrc_rd_act_idle_gap (reg_ddrc_rd_act_idle_gap_bcm36in)
      ,.reg_ddrc_wr_act_idle_gap (reg_ddrc_wr_act_idle_gap_bcm36in)
      ,.reg_ddrc_rd_page_exp_cycles (reg_ddrc_rd_page_exp_cycles_bcm36in)
      ,.reg_ddrc_wr_page_exp_cycles (reg_ddrc_wr_page_exp_cycles_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.SCHED5
   //------------------------
      ,.r50_sched5 (r50_sched5[REG_WIDTH-1:0])
      ,.reg_ddrc_wrecc_cam_lowthresh (reg_ddrc_wrecc_cam_lowthresh_bcm36in)
      ,.reg_ddrc_wrecc_cam_highthresh (reg_ddrc_wrecc_cam_highthresh_bcm36in)
      ,.reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level (reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level_bcm36in)
      ,.reg_ddrc_dis_opt_valid_wrecc_cam_fill_level (reg_ddrc_dis_opt_valid_wrecc_cam_fill_level_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCCTL
   //------------------------
      ,.r51_hwffcctl (r51_hwffcctl)
      ,.reg_ddrc_hwffc_en (reg_ddrc_hwffc_en)
      ,.reg_ddrc_init_fsp (reg_ddrc_init_fsp)
      ,.reg_ddrc_init_vrcg (reg_ddrc_init_vrcg)
      ,.reg_ddrc_target_vrcg (reg_ddrc_target_vrcg)
      ,.reg_ddrc_skip_mrw_odtvref (reg_ddrc_skip_mrw_odtvref)
      ,.reg_ddrc_skip_zq_stop_start (reg_ddrc_skip_zq_stop_start)
      ,.reg_ddrc_zq_interval (reg_ddrc_zq_interval)
      ,.reg_ddrc_hwffc_mode (reg_ddrc_hwffc_mode)
   //------------------------
   // Register REGB_DDRC_CH0.HWFFCSTAT
   //------------------------
      ,.r52_hwffcstat (r52_hwffcstat)
      ,.ddrc_reg_hwffc_in_progress (ddrc_reg_hwffc_in_progress)
      ,.ddrc_reg_hwffc_operating_mode (ddrc_reg_hwffc_operating_mode)
      ,.ddrc_reg_current_frequency (ddrc_reg_current_frequency)
      ,.ddrc_reg_current_fsp (ddrc_reg_current_fsp)
      ,.ddrc_reg_current_vrcg (ddrc_reg_current_vrcg)
   //------------------------
   // Register REGB_DDRC_CH0.DFILPCFG0
   //------------------------
      ,.r62_dfilpcfg0 (r62_dfilpcfg0)
      ,.reg_ddrc_dfi_lp_en_pd (reg_ddrc_dfi_lp_en_pd)
      ,.reg_ddrc_dfi_lp_en_sr (reg_ddrc_dfi_lp_en_sr)
      ,.reg_ddrc_dfi_lp_en_dsm (reg_ddrc_dfi_lp_en_dsm)
      ,.reg_ddrc_dfi_lp_en_data (reg_ddrc_dfi_lp_en_data)
      ,.reg_ddrc_dfi_lp_data_req_en (reg_ddrc_dfi_lp_data_req_en)
      ,.reg_ddrc_extra_gap_for_dfi_lp_data (reg_ddrc_extra_gap_for_dfi_lp_data)
   //------------------------
   // Register REGB_DDRC_CH0.DFIUPD0
   //------------------------
      ,.r63_dfiupd0 (r63_dfiupd0)
      ,.reg_ddrc_dfi_phyupd_en (reg_ddrc_dfi_phyupd_en)
      ,.reg_ddrc_ctrlupd_pre_srx (reg_ddrc_ctrlupd_pre_srx)
      ,.reg_ddrc_dis_auto_ctrlupd_srx (reg_ddrc_dis_auto_ctrlupd_srx)
      ,.reg_ddrc_dis_auto_ctrlupd (reg_ddrc_dis_auto_ctrlupd)
   //------------------------
   // Register REGB_DDRC_CH0.DFIMISC
   //------------------------
      ,.r65_dfimisc (r65_dfimisc)
      ,.reg_ddrc_dfi_init_complete_en (reg_ddrc_dfi_init_complete_en)
      ,.reg_ddrc_phy_dbi_mode (reg_ddrc_phy_dbi_mode)
      ,.reg_ddrc_dfi_data_cs_polarity (reg_ddrc_dfi_data_cs_polarity)
      ,.reg_ddrc_dfi_reset_n (reg_ddrc_dfi_reset_n)
      ,.reg_ddrc_dfi_init_start (reg_ddrc_dfi_init_start)
      ,.reg_ddrc_lp_optimized_write (reg_ddrc_lp_optimized_write)
      ,.reg_ddrc_dfi_frequency (reg_ddrc_dfi_frequency)
      ,.reg_ddrc_dfi_freq_fsp (reg_ddrc_dfi_freq_fsp)
      ,.reg_ddrc_dfi_channel_mode (reg_ddrc_dfi_channel_mode)
   //------------------------
   // Register REGB_DDRC_CH0.DFISTAT
   //------------------------
      ,.r66_dfistat (r66_dfistat)
      ,.ddrc_reg_dfi_init_complete (ddrc_reg_dfi_init_complete)
      ,.ddrc_reg_dfi_lp_ctrl_ack_stat (ddrc_reg_dfi_lp_ctrl_ack_stat)
      ,.ddrc_reg_dfi_lp_data_ack_stat (ddrc_reg_dfi_lp_data_ack_stat)
   //------------------------
   // Register REGB_DDRC_CH0.DFIPHYMSTR
   //------------------------
      ,.r67_dfiphymstr (r67_dfiphymstr)
      ,.reg_ddrc_dfi_phymstr_en (reg_ddrc_dfi_phymstr_en)
      ,.reg_ddrc_dfi_phymstr_blk_ref_x32 (reg_ddrc_dfi_phymstr_blk_ref_x32)
   //------------------------
   // Register REGB_DDRC_CH0.POISONCFG
   //------------------------
      ,.r77_poisoncfg (r77_poisoncfg)
      ,.reg_ddrc_wr_poison_slverr_en (reg_ddrc_wr_poison_slverr_en)
      ,.reg_ddrc_wr_poison_intr_en (reg_ddrc_wr_poison_intr_en)
      ,.reg_ddrc_wr_poison_intr_clr_ack_pclk (reg_ddrc_wr_poison_intr_clr_ack_pclk)
      ,.reg_ddrc_wr_poison_intr_clr (reg_ddrc_wr_poison_intr_clr)
      ,.reg_ddrc_rd_poison_slverr_en (reg_ddrc_rd_poison_slverr_en)
      ,.reg_ddrc_rd_poison_intr_en (reg_ddrc_rd_poison_intr_en)
      ,.reg_ddrc_rd_poison_intr_clr_ack_pclk (reg_ddrc_rd_poison_intr_clr_ack_pclk)
      ,.reg_ddrc_rd_poison_intr_clr (reg_ddrc_rd_poison_intr_clr)
   //------------------------
   // Register REGB_DDRC_CH0.POISONSTAT
   //------------------------
      ,.r78_poisonstat (r78_poisonstat)
      ,.ddrc_reg_wr_poison_intr_0 (ddrc_reg_wr_poison_intr_0)
      ,.ddrc_reg_rd_poison_intr_0 (ddrc_reg_rd_poison_intr_0)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG0
   //------------------------
      ,.r79_ecccfg0 (r79_ecccfg0)
      ,.reg_ddrc_ecc_mode (reg_ddrc_ecc_mode)
      ,.reg_ddrc_ecc_ap_en (reg_ddrc_ecc_ap_en)
      ,.reg_ddrc_ecc_region_remap_en (reg_ddrc_ecc_region_remap_en)
      ,.reg_ddrc_ecc_region_map (reg_ddrc_ecc_region_map)
      ,.reg_ddrc_blk_channel_idle_time_x32 (reg_ddrc_blk_channel_idle_time_x32)
      ,.reg_ddrc_ecc_ap_err_threshold (reg_ddrc_ecc_ap_err_threshold)
      ,.reg_ddrc_ecc_region_map_other (reg_ddrc_ecc_region_map_other)
      ,.reg_ddrc_ecc_region_map_granu (reg_ddrc_ecc_region_map_granu)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCFG1
   //------------------------
      ,.r80_ecccfg1 (r80_ecccfg1[REG_WIDTH-1:0])
      ,.reg_ddrc_data_poison_en (reg_ddrc_data_poison_en_bcm36in)
      ,.reg_ddrc_data_poison_bit (reg_ddrc_data_poison_bit_bcm36in)
      ,.reg_ddrc_ecc_region_parity_lock (reg_ddrc_ecc_region_parity_lock_bcm36in)
      ,.reg_ddrc_ecc_region_waste_lock (reg_ddrc_ecc_region_waste_lock_bcm36in)
      ,.reg_ddrc_med_ecc_en (reg_ddrc_med_ecc_en_bcm36in)
      ,.reg_ddrc_blk_channel_active_term (reg_ddrc_blk_channel_active_term_bcm36in)
      ,.reg_ddrc_active_blk_channel (reg_ddrc_active_blk_channel_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.ECCSTAT
   //------------------------
      ,.r81_eccstat (r81_eccstat)
      ,.ddrc_reg_ecc_corrected_bit_num (ddrc_reg_ecc_corrected_bit_num)
      ,.ddrc_reg_ecc_corrected_err (ddrc_reg_ecc_corrected_err)
      ,.ddrc_reg_ecc_uncorrected_err (ddrc_reg_ecc_uncorrected_err)
      ,.ddrc_reg_sbr_read_ecc_ce (ddrc_reg_sbr_read_ecc_ce)
      ,.ddrc_reg_sbr_read_ecc_ue (ddrc_reg_sbr_read_ecc_ue)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCTL
   //------------------------
      ,.r82_eccctl (r82_eccctl)
      ,.reg_ddrc_ecc_corrected_err_clr_ack_pclk (reg_ddrc_ecc_corrected_err_clr_ack_pclk)
      ,.reg_ddrc_ecc_corrected_err_clr (reg_ddrc_ecc_corrected_err_clr)
      ,.reg_ddrc_ecc_uncorrected_err_clr_ack_pclk (reg_ddrc_ecc_uncorrected_err_clr_ack_pclk)
      ,.reg_ddrc_ecc_uncorrected_err_clr (reg_ddrc_ecc_uncorrected_err_clr)
      ,.reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk (reg_ddrc_ecc_corr_err_cnt_clr_ack_pclk)
      ,.reg_ddrc_ecc_corr_err_cnt_clr (reg_ddrc_ecc_corr_err_cnt_clr)
      ,.reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk (reg_ddrc_ecc_uncorr_err_cnt_clr_ack_pclk)
      ,.reg_ddrc_ecc_uncorr_err_cnt_clr (reg_ddrc_ecc_uncorr_err_cnt_clr)
      ,.reg_ddrc_ecc_ap_err_intr_clr_ack_pclk (reg_ddrc_ecc_ap_err_intr_clr_ack_pclk)
      ,.reg_ddrc_ecc_ap_err_intr_clr (reg_ddrc_ecc_ap_err_intr_clr)
      ,.reg_ddrc_ecc_corrected_err_intr_en (reg_ddrc_ecc_corrected_err_intr_en)
      ,.reg_ddrc_ecc_uncorrected_err_intr_en (reg_ddrc_ecc_uncorrected_err_intr_en)
      ,.reg_ddrc_ecc_ap_err_intr_en (reg_ddrc_ecc_ap_err_intr_en)
      ,.reg_ddrc_ecc_corrected_err_intr_force_ack_pclk (reg_ddrc_ecc_corrected_err_intr_force_ack_pclk)
      ,.reg_ddrc_ecc_corrected_err_intr_force (reg_ddrc_ecc_corrected_err_intr_force)
      ,.reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk (reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk)
      ,.reg_ddrc_ecc_uncorrected_err_intr_force (reg_ddrc_ecc_uncorrected_err_intr_force)
      ,.reg_ddrc_ecc_ap_err_intr_force_ack_pclk (reg_ddrc_ecc_ap_err_intr_force_ack_pclk)
      ,.reg_ddrc_ecc_ap_err_intr_force (reg_ddrc_ecc_ap_err_intr_force)
   //------------------------
   // Register REGB_DDRC_CH0.ECCERRCNT
   //------------------------
      ,.r83_eccerrcnt (r83_eccerrcnt)
      ,.ddrc_reg_ecc_corr_err_cnt (ddrc_reg_ecc_corr_err_cnt)
      ,.ddrc_reg_ecc_uncorr_err_cnt (ddrc_reg_ecc_uncorr_err_cnt)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCADDR0
   //------------------------
      ,.r84_ecccaddr0 (r84_ecccaddr0)
      ,.ddrc_reg_ecc_corr_row (ddrc_reg_ecc_corr_row)
      ,.ddrc_reg_ecc_corr_rank (ddrc_reg_ecc_corr_rank)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCADDR1
   //------------------------
      ,.r85_ecccaddr1 (r85_ecccaddr1)
      ,.ddrc_reg_ecc_corr_col (ddrc_reg_ecc_corr_col)
      ,.ddrc_reg_ecc_corr_bank (ddrc_reg_ecc_corr_bank)
      ,.ddrc_reg_ecc_corr_bg (ddrc_reg_ecc_corr_bg)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN0
   //------------------------
      ,.r86_ecccsyn0 (r86_ecccsyn0)
      ,.ddrc_reg_ecc_corr_syndromes_31_0 (ddrc_reg_ecc_corr_syndromes_31_0)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN1
   //------------------------
      ,.r87_ecccsyn1 (r87_ecccsyn1)
      ,.ddrc_reg_ecc_corr_syndromes_63_32 (ddrc_reg_ecc_corr_syndromes_63_32)
   //------------------------
   // Register REGB_DDRC_CH0.ECCCSYN2
   //------------------------
      ,.r88_ecccsyn2 (r88_ecccsyn2)
      ,.ddrc_reg_ecc_corr_syndromes_71_64 (ddrc_reg_ecc_corr_syndromes_71_64)
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK0
   //------------------------
      ,.r89_eccbitmask0 (r89_eccbitmask0)
      ,.ddrc_reg_ecc_corr_bit_mask_31_0 (ddrc_reg_ecc_corr_bit_mask_31_0)
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK1
   //------------------------
      ,.r90_eccbitmask1 (r90_eccbitmask1)
      ,.ddrc_reg_ecc_corr_bit_mask_63_32 (ddrc_reg_ecc_corr_bit_mask_63_32)
   //------------------------
   // Register REGB_DDRC_CH0.ECCBITMASK2
   //------------------------
      ,.r91_eccbitmask2 (r91_eccbitmask2)
      ,.ddrc_reg_ecc_corr_bit_mask_71_64 (ddrc_reg_ecc_corr_bit_mask_71_64)
   //------------------------
   // Register REGB_DDRC_CH0.ECCUADDR0
   //------------------------
      ,.r92_eccuaddr0 (r92_eccuaddr0)
      ,.ddrc_reg_ecc_uncorr_row (ddrc_reg_ecc_uncorr_row)
      ,.ddrc_reg_ecc_uncorr_rank (ddrc_reg_ecc_uncorr_rank)
   //------------------------
   // Register REGB_DDRC_CH0.ECCUADDR1
   //------------------------
      ,.r93_eccuaddr1 (r93_eccuaddr1)
      ,.ddrc_reg_ecc_uncorr_col (ddrc_reg_ecc_uncorr_col)
      ,.ddrc_reg_ecc_uncorr_bank (ddrc_reg_ecc_uncorr_bank)
      ,.ddrc_reg_ecc_uncorr_bg (ddrc_reg_ecc_uncorr_bg)
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN0
   //------------------------
      ,.r94_eccusyn0 (r94_eccusyn0)
      ,.ddrc_reg_ecc_uncorr_syndromes_31_0 (ddrc_reg_ecc_uncorr_syndromes_31_0)
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN1
   //------------------------
      ,.r95_eccusyn1 (r95_eccusyn1)
      ,.ddrc_reg_ecc_uncorr_syndromes_63_32 (ddrc_reg_ecc_uncorr_syndromes_63_32)
   //------------------------
   // Register REGB_DDRC_CH0.ECCUSYN2
   //------------------------
      ,.r96_eccusyn2 (r96_eccusyn2)
      ,.ddrc_reg_ecc_uncorr_syndromes_71_64 (ddrc_reg_ecc_uncorr_syndromes_71_64)
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR0
   //------------------------
      ,.r97_eccpoisonaddr0 (r97_eccpoisonaddr0[REG_WIDTH-1:0])
      ,.reg_ddrc_ecc_poison_col (reg_ddrc_ecc_poison_col_bcm36in)
      ,.reg_ddrc_ecc_poison_rank (reg_ddrc_ecc_poison_rank_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONADDR1
   //------------------------
      ,.r98_eccpoisonaddr1 (r98_eccpoisonaddr1[REG_WIDTH-1:0])
      ,.reg_ddrc_ecc_poison_row (reg_ddrc_ecc_poison_row_bcm36in)
      ,.reg_ddrc_ecc_poison_bank (reg_ddrc_ecc_poison_bank_bcm36in)
      ,.reg_ddrc_ecc_poison_bg (reg_ddrc_ecc_poison_bg_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT0
   //------------------------
      ,.r101_eccpoisonpat0 (r101_eccpoisonpat0[REG_WIDTH-1:0])
      ,.reg_ddrc_ecc_poison_data_31_0 (reg_ddrc_ecc_poison_data_31_0_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.ECCPOISONPAT2
   //------------------------
      ,.r103_eccpoisonpat2 (r103_eccpoisonpat2[REG_WIDTH-1:0])
      ,.reg_ddrc_ecc_poison_data_71_64 (reg_ddrc_ecc_poison_data_71_64_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.ECCAPSTAT
   //------------------------
      ,.r104_eccapstat (r104_eccapstat)
      ,.ddrc_reg_ecc_ap_err (ddrc_reg_ecc_ap_err)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCTL1
   //------------------------
      ,.r161_lnkeccctl1 (r161_lnkeccctl1)
      ,.reg_ddrc_rd_link_ecc_corr_intr_en (reg_ddrc_rd_link_ecc_corr_intr_en)
      ,.reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk (reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_corr_intr_clr (reg_ddrc_rd_link_ecc_corr_intr_clr)
      ,.reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk (reg_ddrc_rd_link_ecc_corr_cnt_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_corr_cnt_clr (reg_ddrc_rd_link_ecc_corr_cnt_clr)
      ,.reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk (reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_corr_intr_force (reg_ddrc_rd_link_ecc_corr_intr_force)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_en (reg_ddrc_rd_link_ecc_uncorr_intr_en)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk (reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_clr (reg_ddrc_rd_link_ecc_uncorr_intr_clr)
      ,.reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk (reg_ddrc_rd_link_ecc_uncorr_cnt_clr_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_uncorr_cnt_clr (reg_ddrc_rd_link_ecc_uncorr_cnt_clr)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk (reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_force (reg_ddrc_rd_link_ecc_uncorr_intr_force)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONCTL0
   //------------------------
      ,.r162_lnkeccpoisonctl0 (r162_lnkeccpoisonctl0)
      ,.reg_ddrc_linkecc_poison_inject_en (reg_ddrc_linkecc_poison_inject_en)
      ,.reg_ddrc_linkecc_poison_type (reg_ddrc_linkecc_poison_type)
      ,.reg_ddrc_linkecc_poison_rw (reg_ddrc_linkecc_poison_rw)
      ,.reg_ddrc_linkecc_poison_dmi_sel (reg_ddrc_linkecc_poison_dmi_sel)
      ,.reg_ddrc_linkecc_poison_byte_sel (reg_ddrc_linkecc_poison_byte_sel)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCPOISONSTAT
   //------------------------
      ,.r163_lnkeccpoisonstat (r163_lnkeccpoisonstat)
      ,.ddrc_reg_linkecc_poison_complete (ddrc_reg_linkecc_poison_complete)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCINDEX
   //------------------------
      ,.r164_lnkeccindex (r164_lnkeccindex)
      ,.reg_ddrc_rd_link_ecc_err_byte_sel (reg_ddrc_rd_link_ecc_err_byte_sel)
      ,.reg_ddrc_rd_link_ecc_err_rank_sel (reg_ddrc_rd_link_ecc_err_rank_sel)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCERRCNT0
   //------------------------
      ,.r165_lnkeccerrcnt0 (r165_lnkeccerrcnt0)
      ,.ddrc_reg_rd_link_ecc_err_syndrome (ddrc_reg_rd_link_ecc_err_syndrome)
      ,.ddrc_reg_rd_link_ecc_corr_cnt (ddrc_reg_rd_link_ecc_corr_cnt)
      ,.ddrc_reg_rd_link_ecc_uncorr_cnt (ddrc_reg_rd_link_ecc_uncorr_cnt)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCERRSTAT
   //------------------------
      ,.r166_lnkeccerrstat (r166_lnkeccerrstat)
      ,.ddrc_reg_rd_link_ecc_corr_err_int (ddrc_reg_rd_link_ecc_corr_err_int)
      ,.ddrc_reg_rd_link_ecc_uncorr_err_int (ddrc_reg_rd_link_ecc_uncorr_err_int)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCADDR0
   //------------------------
      ,.r175_lnkecccaddr0 (r175_lnkecccaddr0)
      ,.ddrc_reg_link_ecc_corr_row (ddrc_reg_link_ecc_corr_row)
      ,.ddrc_reg_link_ecc_corr_rank (ddrc_reg_link_ecc_corr_rank)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCCADDR1
   //------------------------
      ,.r176_lnkecccaddr1 (r176_lnkecccaddr1)
      ,.ddrc_reg_link_ecc_corr_col (ddrc_reg_link_ecc_corr_col)
      ,.ddrc_reg_link_ecc_corr_bank (ddrc_reg_link_ecc_corr_bank)
      ,.ddrc_reg_link_ecc_corr_bg (ddrc_reg_link_ecc_corr_bg)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCUADDR0
   //------------------------
      ,.r177_lnkeccuaddr0 (r177_lnkeccuaddr0)
      ,.ddrc_reg_link_ecc_uncorr_row (ddrc_reg_link_ecc_uncorr_row)
      ,.ddrc_reg_link_ecc_uncorr_rank (ddrc_reg_link_ecc_uncorr_rank)
   //------------------------
   // Register REGB_DDRC_CH0.LNKECCUADDR1
   //------------------------
      ,.r178_lnkeccuaddr1 (r178_lnkeccuaddr1)
      ,.ddrc_reg_link_ecc_uncorr_col (ddrc_reg_link_ecc_uncorr_col)
      ,.ddrc_reg_link_ecc_uncorr_bank (ddrc_reg_link_ecc_uncorr_bank)
      ,.ddrc_reg_link_ecc_uncorr_bg (ddrc_reg_link_ecc_uncorr_bg)
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL0
   //------------------------
      ,.r234_opctrl0 (r234_opctrl0[REG_WIDTH-1:0])
      ,.reg_ddrc_dis_wc (reg_ddrc_dis_wc_bcm36in)
      ,.reg_ddrc_dis_max_rank_rd_opt (reg_ddrc_dis_max_rank_rd_opt_bcm36in)
      ,.reg_ddrc_dis_max_rank_wr_opt (reg_ddrc_dis_max_rank_wr_opt_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRL1
   //------------------------
      ,.r235_opctrl1 (r235_opctrl1)
      ,.reg_ddrc_dis_dq (reg_ddrc_dis_dq)
      ,.reg_ddrc_dis_hif (reg_ddrc_dis_hif)
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCAM
   //------------------------
      ,.r236_opctrlcam (r236_opctrlcam)
      ,.ddrc_reg_dbg_hpr_q_depth (ddrc_reg_dbg_hpr_q_depth)
      ,.ddrc_reg_dbg_lpr_q_depth (ddrc_reg_dbg_lpr_q_depth)
      ,.ddrc_reg_dbg_w_q_depth (ddrc_reg_dbg_w_q_depth)
      ,.ddrc_reg_dbg_stall (ddrc_reg_dbg_stall)
      ,.ddrc_reg_dbg_rd_q_empty (ddrc_reg_dbg_rd_q_empty)
      ,.ddrc_reg_dbg_wr_q_empty (ddrc_reg_dbg_wr_q_empty)
      ,.ddrc_reg_rd_data_pipeline_empty (ddrc_reg_rd_data_pipeline_empty)
      ,.ddrc_reg_wr_data_pipeline_empty (ddrc_reg_wr_data_pipeline_empty)
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCMD
   //------------------------
      ,.r237_opctrlcmd (r237_opctrlcmd)
      ,.reg_ddrc_zq_calib_short_ack_pclk (reg_ddrc_zq_calib_short_ack_pclk)
      ,.ff_regb_ddrc_ch0_zq_calib_short_saved (ff_regb_ddrc_ch0_zq_calib_short_saved)
      ,.reg_ddrc_zq_calib_short (reg_ddrc_zq_calib_short)
      ,.reg_ddrc_ctrlupd_ack_pclk (reg_ddrc_ctrlupd_ack_pclk)
      ,.ff_regb_ddrc_ch0_ctrlupd_saved (ff_regb_ddrc_ch0_ctrlupd_saved)
      ,.reg_ddrc_ctrlupd (reg_ddrc_ctrlupd)
      ,.reg_ddrc_ctrlupd_burst (reg_ddrc_ctrlupd_burst)
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLSTAT
   //------------------------
      ,.r238_opctrlstat (r238_opctrlstat)
      ,.ddrc_reg_zq_calib_short_busy_int (ddrc_reg_zq_calib_short_busy_int)
      ,.ddrc_reg_zq_calib_short_busy (ddrc_reg_zq_calib_short_busy)
      ,.ddrc_reg_ctrlupd_busy_int (ddrc_reg_ctrlupd_busy_int)
      ,.ddrc_reg_ctrlupd_busy (ddrc_reg_ctrlupd_busy)
      ,.ddrc_reg_ctrlupd_burst_busy (ddrc_reg_ctrlupd_burst_busy)
   //------------------------
   // Register REGB_DDRC_CH0.OPCTRLCAM1
   //------------------------
      ,.r239_opctrlcam1 (r239_opctrlcam1)
      ,.ddrc_reg_dbg_wrecc_q_depth (ddrc_reg_dbg_wrecc_q_depth)
   //------------------------
   // Register REGB_DDRC_CH0.OPREFCTRL0
   //------------------------
      ,.r240_oprefctrl0 (r240_oprefctrl0)
      ,.reg_ddrc_rank0_refresh_ack_pclk (reg_ddrc_rank0_refresh_ack_pclk)
      ,.ff_regb_ddrc_ch0_rank0_refresh_saved (ff_regb_ddrc_ch0_rank0_refresh_saved)
      ,.reg_ddrc_rank0_refresh (reg_ddrc_rank0_refresh)
      ,.reg_ddrc_rank1_refresh_ack_pclk (reg_ddrc_rank1_refresh_ack_pclk)
      ,.ff_regb_ddrc_ch0_rank1_refresh_saved (ff_regb_ddrc_ch0_rank1_refresh_saved)
      ,.reg_ddrc_rank1_refresh (reg_ddrc_rank1_refresh)
   //------------------------
   // Register REGB_DDRC_CH0.OPREFSTAT0
   //------------------------
      ,.r242_oprefstat0 (r242_oprefstat0)
      ,.ddrc_reg_rank0_refresh_busy_int (ddrc_reg_rank0_refresh_busy_int)
      ,.ddrc_reg_rank0_refresh_busy (ddrc_reg_rank0_refresh_busy)
      ,.ddrc_reg_rank1_refresh_busy_int (ddrc_reg_rank1_refresh_busy_int)
      ,.ddrc_reg_rank1_refresh_busy (ddrc_reg_rank1_refresh_busy)
   //------------------------
   // Register REGB_DDRC_CH0.SWCTL
   //------------------------
      ,.r249_swctl (r249_swctl[REG_WIDTH-1:0])
      ,.reg_ddrc_sw_done (reg_ddrc_sw_done)
   //------------------------
   // Register REGB_DDRC_CH0.SWSTAT
   //------------------------
      ,.r250_swstat (r250_swstat)
      ,.ddrc_reg_sw_done_ack (ddrc_reg_sw_done_ack)
   //------------------------
   // Register REGB_DDRC_CH0.RANKCTL
   //------------------------
      ,.r253_rankctl (r253_rankctl[REG_WIDTH-1:0])
      ,.reg_ddrc_max_rank_rd (reg_ddrc_max_rank_rd_bcm36in)
      ,.reg_ddrc_max_rank_wr (reg_ddrc_max_rank_wr_bcm36in)
   //------------------------
   // Register REGB_DDRC_CH0.DBICTL
   //------------------------
      ,.r254_dbictl (r254_dbictl)
      ,.reg_ddrc_dm_en (reg_ddrc_dm_en)
      ,.reg_ddrc_wr_dbi_en (reg_ddrc_wr_dbi_en)
      ,.reg_ddrc_rd_dbi_en (reg_ddrc_rd_dbi_en)
   //------------------------
   // Register REGB_DDRC_CH0.ODTMAP
   //------------------------
      ,.r256_odtmap (r256_odtmap)
      ,.reg_ddrc_rank0_wr_odt (reg_ddrc_rank0_wr_odt)
      ,.reg_ddrc_rank0_rd_odt (reg_ddrc_rank0_rd_odt)
      ,.reg_ddrc_rank1_wr_odt (reg_ddrc_rank1_wr_odt)
      ,.reg_ddrc_rank1_rd_odt (reg_ddrc_rank1_rd_odt)
   //------------------------
   // Register REGB_DDRC_CH0.DATACTL0
   //------------------------
      ,.r257_datactl0 (r257_datactl0)
      ,.reg_ddrc_rd_data_copy_en (reg_ddrc_rd_data_copy_en)
      ,.reg_ddrc_wr_data_copy_en (reg_ddrc_wr_data_copy_en)
      ,.reg_ddrc_wr_data_x_en (reg_ddrc_wr_data_x_en)
   //------------------------
   // Register REGB_DDRC_CH0.SWCTLSTATIC
   //------------------------
      ,.r258_swctlstatic (r258_swctlstatic[REG_WIDTH-1:0])
      ,.reg_ddrc_sw_static_unlock (reg_ddrc_sw_static_unlock)
   //------------------------
   // Register REGB_DDRC_CH0.CGCTL
   //------------------------
      ,.r259_cgctl (r259_cgctl)
      ,.reg_ddrc_force_clk_te_en (reg_ddrc_force_clk_te_en)
      ,.reg_ddrc_force_clk_arb_en (reg_ddrc_force_clk_arb_en)
   //------------------------
   // Register REGB_DDRC_CH0.INITTMG0
   //------------------------
      ,.r260_inittmg0 (r260_inittmg0)
      ,.reg_ddrc_pre_cke_x1024 (reg_ddrc_pre_cke_x1024)
      ,.reg_ddrc_post_cke_x1024 (reg_ddrc_post_cke_x1024)
      ,.reg_ddrc_skip_dram_init (reg_ddrc_skip_dram_init)
   //------------------------
   // Register REGB_DDRC_CH0.PPT2CTRL0
   //------------------------
      ,.r285_ppt2ctrl0 (r285_ppt2ctrl0)
      ,.reg_ddrc_ppt2_burst_num (reg_ddrc_ppt2_burst_num)
      ,.reg_ddrc_ppt2_ctrlupd_num_dfi0 (reg_ddrc_ppt2_ctrlupd_num_dfi0)
      ,.reg_ddrc_ppt2_ctrlupd_num_dfi1 (reg_ddrc_ppt2_ctrlupd_num_dfi1)
      ,.reg_ddrc_ppt2_burst_ack_pclk (reg_ddrc_ppt2_burst_ack_pclk)
      ,.ff_regb_ddrc_ch0_ppt2_burst_saved (ff_regb_ddrc_ch0_ppt2_burst_saved)
      ,.reg_ddrc_ppt2_burst (reg_ddrc_ppt2_burst)
      ,.reg_ddrc_ppt2_wait_ref (reg_ddrc_ppt2_wait_ref)
   //------------------------
   // Register REGB_DDRC_CH0.PPT2STAT0
   //------------------------
      ,.r286_ppt2stat0 (r286_ppt2stat0)
      ,.ddrc_reg_ppt2_state (ddrc_reg_ppt2_state)
      ,.ddrc_reg_ppt2_burst_busy_int (ddrc_reg_ppt2_burst_busy_int)
      ,.ddrc_reg_ppt2_burst_busy (ddrc_reg_ppt2_burst_busy)
   //------------------------
   // Register REGB_DDRC_CH0.DDRCTL_VER_NUMBER
   //------------------------
      ,.r289_ddrctl_ver_number (r289_ddrctl_ver_number)
      ,.ddrc_reg_ver_number (ddrc_reg_ver_number)
   //------------------------
   // Register REGB_DDRC_CH0.DDRCTL_VER_TYPE
   //------------------------
      ,.r290_ddrctl_ver_type (r290_ddrctl_ver_type)
      ,.ddrc_reg_ver_type (ddrc_reg_ver_type)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP1
   //------------------------
      ,.r495_addrmap1_map0 (r495_addrmap1_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_cs_bit0_map0 (reg_ddrc_addrmap_cs_bit0_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP3
   //------------------------
      ,.r497_addrmap3_map0 (r497_addrmap3_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_bank_b0_map0 (reg_ddrc_addrmap_bank_b0_map0_bcm36in)
      ,.reg_ddrc_addrmap_bank_b1_map0 (reg_ddrc_addrmap_bank_b1_map0_bcm36in)
      ,.reg_ddrc_addrmap_bank_b2_map0 (reg_ddrc_addrmap_bank_b2_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP4
   //------------------------
      ,.r498_addrmap4_map0 (r498_addrmap4_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_bg_b0_map0 (reg_ddrc_addrmap_bg_b0_map0_bcm36in)
      ,.reg_ddrc_addrmap_bg_b1_map0 (reg_ddrc_addrmap_bg_b1_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP5
   //------------------------
      ,.r499_addrmap5_map0 (r499_addrmap5_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_col_b7_map0 (reg_ddrc_addrmap_col_b7_map0_bcm36in)
      ,.reg_ddrc_addrmap_col_b8_map0 (reg_ddrc_addrmap_col_b8_map0_bcm36in)
      ,.reg_ddrc_addrmap_col_b9_map0 (reg_ddrc_addrmap_col_b9_map0_bcm36in)
      ,.reg_ddrc_addrmap_col_b10_map0 (reg_ddrc_addrmap_col_b10_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP6
   //------------------------
      ,.r500_addrmap6_map0 (r500_addrmap6_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_col_b3_map0 (reg_ddrc_addrmap_col_b3_map0_bcm36in)
      ,.reg_ddrc_addrmap_col_b4_map0 (reg_ddrc_addrmap_col_b4_map0_bcm36in)
      ,.reg_ddrc_addrmap_col_b5_map0 (reg_ddrc_addrmap_col_b5_map0_bcm36in)
      ,.reg_ddrc_addrmap_col_b6_map0 (reg_ddrc_addrmap_col_b6_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP7
   //------------------------
      ,.r501_addrmap7_map0 (r501_addrmap7_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_row_b14_map0 (reg_ddrc_addrmap_row_b14_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b15_map0 (reg_ddrc_addrmap_row_b15_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b16_map0 (reg_ddrc_addrmap_row_b16_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b17_map0 (reg_ddrc_addrmap_row_b17_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP8
   //------------------------
      ,.r502_addrmap8_map0 (r502_addrmap8_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_row_b10_map0 (reg_ddrc_addrmap_row_b10_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b11_map0 (reg_ddrc_addrmap_row_b11_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b12_map0 (reg_ddrc_addrmap_row_b12_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b13_map0 (reg_ddrc_addrmap_row_b13_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP9
   //------------------------
      ,.r503_addrmap9_map0 (r503_addrmap9_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_row_b6_map0 (reg_ddrc_addrmap_row_b6_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b7_map0 (reg_ddrc_addrmap_row_b7_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b8_map0 (reg_ddrc_addrmap_row_b8_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b9_map0 (reg_ddrc_addrmap_row_b9_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP10
   //------------------------
      ,.r504_addrmap10_map0 (r504_addrmap10_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_row_b2_map0 (reg_ddrc_addrmap_row_b2_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b3_map0 (reg_ddrc_addrmap_row_b3_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b4_map0 (reg_ddrc_addrmap_row_b4_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b5_map0 (reg_ddrc_addrmap_row_b5_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP11
   //------------------------
      ,.r505_addrmap11_map0 (r505_addrmap11_map0[REG_WIDTH-1:0])
      ,.reg_ddrc_addrmap_row_b0_map0 (reg_ddrc_addrmap_row_b0_map0_bcm36in)
      ,.reg_ddrc_addrmap_row_b1_map0 (reg_ddrc_addrmap_row_b1_map0_bcm36in)
   //------------------------
   // Register REGB_ADDR_MAP0.ADDRMAP12
   //------------------------
      ,.r506_addrmap12_map0 (r506_addrmap12_map0)
      ,.reg_ddrc_nonbinary_device_density_map0 (reg_ddrc_nonbinary_device_density_map0)
      ,.reg_ddrc_bank_hash_en_map0 (reg_ddrc_bank_hash_en_map0)
   //------------------------
   // Register REGB_ARB_PORT0.PCCFG
   //------------------------
      ,.r521_pccfg_port0 (r521_pccfg_port0[REG_WIDTH-1:0])
      ,.reg_arb_go2critical_en_port0 (reg_arb_go2critical_en_port0_bcm36in)
      ,.reg_arb_pagematch_limit_port0 (reg_arb_pagematch_limit_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.PCFGR
   //------------------------
      ,.r522_pcfgr_port0 (r522_pcfgr_port0[REG_WIDTH-1:0])
      ,.reg_arb_rd_port_priority_port0 (reg_arb_rd_port_priority_port0_bcm36in)
      ,.reg_arb_rd_port_aging_en_port0 (reg_arb_rd_port_aging_en_port0_bcm36in)
      ,.reg_arb_rd_port_urgent_en_port0 (reg_arb_rd_port_urgent_en_port0_bcm36in)
      ,.reg_arb_rd_port_pagematch_en_port0 (reg_arb_rd_port_pagematch_en_port0_bcm36in)
      ,.reg_arb_rrb_lock_threshold_port0 (reg_arb_rrb_lock_threshold_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.PCFGW
   //------------------------
      ,.r523_pcfgw_port0 (r523_pcfgw_port0[REG_WIDTH-1:0])
      ,.reg_arb_wr_port_priority_port0 (reg_arb_wr_port_priority_port0_bcm36in)
      ,.reg_arb_wr_port_aging_en_port0 (reg_arb_wr_port_aging_en_port0_bcm36in)
      ,.reg_arb_wr_port_urgent_en_port0 (reg_arb_wr_port_urgent_en_port0_bcm36in)
      ,.reg_arb_wr_port_pagematch_en_port0 (reg_arb_wr_port_pagematch_en_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.PCTRL
   //------------------------
      ,.r556_pctrl_port0 (r556_pctrl_port0)
      ,.reg_arb_port_en_port0 (reg_arb_port_en_port0)
      ,.reg_apb_port_en_port0 (reg_apb_port_en_port0)
      ,.reg_arba0_port_en_port0 (reg_arba0_port_en_port0)
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS0
   //------------------------
      ,.r557_pcfgqos0_port0 (r557_pcfgqos0_port0[REG_WIDTH-1:0])
      ,.reg_arba0_rqos_map_level1_port0 (reg_arba0_rqos_map_level1_port0_bcm36in)
      ,.reg_arba0_rqos_map_level2_port0 (reg_arba0_rqos_map_level2_port0_bcm36in)
      ,.reg_arba0_rqos_map_region0_port0 (reg_arba0_rqos_map_region0_port0_bcm36in)
      ,.reg_arba0_rqos_map_region1_port0 (reg_arba0_rqos_map_region1_port0_bcm36in)
      ,.reg_arba0_rqos_map_region2_port0 (reg_arba0_rqos_map_region2_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.PCFGQOS1
   //------------------------
      ,.r558_pcfgqos1_port0 (r558_pcfgqos1_port0[REG_WIDTH-1:0])
      ,.reg_arb_rqos_map_timeoutb_port0 (reg_arb_rqos_map_timeoutb_port0_bcm36in)
      ,.reg_arb_rqos_map_timeoutr_port0 (reg_arb_rqos_map_timeoutr_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS0
   //------------------------
      ,.r559_pcfgwqos0_port0 (r559_pcfgwqos0_port0[REG_WIDTH-1:0])
      ,.reg_arba0_wqos_map_level1_port0 (reg_arba0_wqos_map_level1_port0_bcm36in)
      ,.reg_arba0_wqos_map_level2_port0 (reg_arba0_wqos_map_level2_port0_bcm36in)
      ,.reg_arba0_wqos_map_region0_port0 (reg_arba0_wqos_map_region0_port0_bcm36in)
      ,.reg_arba0_wqos_map_region1_port0 (reg_arba0_wqos_map_region1_port0_bcm36in)
      ,.reg_arba0_wqos_map_region2_port0 (reg_arba0_wqos_map_region2_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.PCFGWQOS1
   //------------------------
      ,.r560_pcfgwqos1_port0 (r560_pcfgwqos1_port0[REG_WIDTH-1:0])
      ,.reg_arb_wqos_map_timeout1_port0 (reg_arb_wqos_map_timeout1_port0_bcm36in)
      ,.reg_arb_wqos_map_timeout2_port0 (reg_arb_wqos_map_timeout2_port0_bcm36in)
   //------------------------
   // Register REGB_ARB_PORT0.SBRCTL
   //------------------------
      ,.r569_sbrctl_port0 (r569_sbrctl_port0)
      ,.reg_arb_scrub_en_port0 (reg_arb_scrub_en_port0)
      ,.reg_arb_scrub_during_lowpower_port0 (reg_arb_scrub_during_lowpower_port0)
      ,.reg_arb_scrub_burst_length_nm_port0 (reg_arb_scrub_burst_length_nm_port0)
      ,.reg_arb_scrub_interval_port0 (reg_arb_scrub_interval_port0)
      ,.reg_arb_scrub_cmd_type_port0 (reg_arb_scrub_cmd_type_port0)
      ,.reg_arb_scrub_burst_length_lp_port0 (reg_arb_scrub_burst_length_lp_port0)
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTAT
   //------------------------
      ,.r570_sbrstat_port0 (r570_sbrstat_port0)
      ,.arb_reg_scrub_busy_port0 (arb_reg_scrub_busy_port0)
      ,.arb_reg_scrub_done_port0 (arb_reg_scrub_done_port0)
   //------------------------
   // Register REGB_ARB_PORT0.SBRWDATA0
   //------------------------
      ,.r571_sbrwdata0_port0 (r571_sbrwdata0_port0)
      ,.reg_arb_scrub_pattern0_port0 (reg_arb_scrub_pattern0_port0)
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART0
   //------------------------
      ,.r573_sbrstart0_port0 (r573_sbrstart0_port0)
      ,.reg_arb_sbr_address_start_mask_0_port0 (reg_arb_sbr_address_start_mask_0_port0)
   //------------------------
   // Register REGB_ARB_PORT0.SBRSTART1
   //------------------------
      ,.r574_sbrstart1_port0 (r574_sbrstart1_port0)
      ,.reg_arb_sbr_address_start_mask_1_port0 (reg_arb_sbr_address_start_mask_1_port0)
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE0
   //------------------------
      ,.r575_sbrrange0_port0 (r575_sbrrange0_port0)
      ,.reg_arb_sbr_address_range_mask_0_port0 (reg_arb_sbr_address_range_mask_0_port0)
   //------------------------
   // Register REGB_ARB_PORT0.SBRRANGE1
   //------------------------
      ,.r576_sbrrange1_port0 (r576_sbrrange1_port0)
      ,.reg_arb_sbr_address_range_mask_1_port0 (reg_arb_sbr_address_range_mask_1_port0)
   //------------------------
   // Register REGB_ARB_PORT0.PSTAT
   //------------------------
      ,.r582_pstat_port0 (r582_pstat_port0)
      ,.arb_reg_rd_port_busy_0_port0 (arb_reg_rd_port_busy_0_port0)
      ,.arb_reg_wr_port_busy_0_port0 (arb_reg_wr_port_busy_0_port0)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG0
   //------------------------
      ,.r1929_dramset1tmg0_freq0 (r1929_dramset1tmg0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ras_min_freq0 (reg_ddrc_t_ras_min_freq0_bcm36in)
      ,.reg_ddrc_t_ras_max_freq0 (reg_ddrc_t_ras_max_freq0_bcm36in)
      ,.reg_ddrc_t_faw_freq0 (reg_ddrc_t_faw_freq0_bcm36in)
      ,.reg_ddrc_wr2pre_freq0 (reg_ddrc_wr2pre_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG1
   //------------------------
      ,.r1930_dramset1tmg1_freq0 (r1930_dramset1tmg1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rc_freq0 (reg_ddrc_t_rc_freq0_bcm36in)
      ,.reg_ddrc_rd2pre_freq0 (reg_ddrc_rd2pre_freq0_bcm36in)
      ,.reg_ddrc_t_xp_freq0 (reg_ddrc_t_xp_freq0_bcm36in)
      ,.reg_ddrc_t_rcd_write_freq0 (reg_ddrc_t_rcd_write_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG2
   //------------------------
      ,.r1931_dramset1tmg2_freq0 (r1931_dramset1tmg2_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_freq0 (reg_ddrc_wr2rd_freq0_bcm36in)
      ,.reg_ddrc_rd2wr_freq0 (reg_ddrc_rd2wr_freq0_bcm36in)
      ,.reg_ddrc_read_latency_freq0 (reg_ddrc_read_latency_freq0_bcm36in)
      ,.reg_ddrc_write_latency_freq0 (reg_ddrc_write_latency_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG3
   //------------------------
      ,.r1932_dramset1tmg3_freq0 (r1932_dramset1tmg3_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2mr_freq0 (reg_ddrc_wr2mr_freq0_bcm36in)
      ,.reg_ddrc_rd2mr_freq0 (reg_ddrc_rd2mr_freq0_bcm36in)
      ,.reg_ddrc_t_mr_freq0 (reg_ddrc_t_mr_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG4
   //------------------------
      ,.r1933_dramset1tmg4_freq0 (r1933_dramset1tmg4_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rp_freq0 (reg_ddrc_t_rp_freq0_bcm36in)
      ,.reg_ddrc_t_rrd_freq0 (reg_ddrc_t_rrd_freq0_bcm36in)
      ,.reg_ddrc_t_ccd_freq0 (reg_ddrc_t_ccd_freq0_bcm36in)
      ,.reg_ddrc_t_rcd_freq0 (reg_ddrc_t_rcd_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG5
   //------------------------
      ,.r1934_dramset1tmg5_freq0 (r1934_dramset1tmg5_freq0)
      ,.reg_ddrc_t_cke_freq0 (reg_ddrc_t_cke_freq0)
      ,.reg_ddrc_t_ckesr_freq0 (reg_ddrc_t_ckesr_freq0)
      ,.reg_ddrc_t_cksre_freq0 (reg_ddrc_t_cksre_freq0)
      ,.reg_ddrc_t_cksrx_freq0 (reg_ddrc_t_cksrx_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG6
   //------------------------
      ,.r1935_dramset1tmg6_freq0 (r1935_dramset1tmg6_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ckcsx_freq0 (reg_ddrc_t_ckcsx_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG7
   //------------------------
      ,.r1936_dramset1tmg7_freq0 (r1936_dramset1tmg7_freq0)
      ,.reg_ddrc_t_csh_freq0 (reg_ddrc_t_csh_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG9
   //------------------------
      ,.r1938_dramset1tmg9_freq0 (r1938_dramset1tmg9_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_s_freq0 (reg_ddrc_wr2rd_s_freq0_bcm36in)
      ,.reg_ddrc_t_rrd_s_freq0 (reg_ddrc_t_rrd_s_freq0_bcm36in)
      ,.reg_ddrc_t_ccd_s_freq0 (reg_ddrc_t_ccd_s_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG12
   //------------------------
      ,.r1941_dramset1tmg12_freq0 (r1941_dramset1tmg12_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_cmdcke_freq0 (reg_ddrc_t_cmdcke_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG13
   //------------------------
      ,.r1942_dramset1tmg13_freq0 (r1942_dramset1tmg13_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ppd_freq0 (reg_ddrc_t_ppd_freq0_bcm36in)
      ,.reg_ddrc_t_ccd_mw_freq0 (reg_ddrc_t_ccd_mw_freq0_bcm36in)
      ,.reg_ddrc_odtloff_freq0 (reg_ddrc_odtloff_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG14
   //------------------------
      ,.r1943_dramset1tmg14_freq0 (r1943_dramset1tmg14_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_xsr_freq0 (reg_ddrc_t_xsr_freq0_bcm36in)
      ,.reg_ddrc_t_osco_freq0 (reg_ddrc_t_osco_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG17
   //------------------------
      ,.r1946_dramset1tmg17_freq0 (r1946_dramset1tmg17_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_vrcg_disable_freq0 (reg_ddrc_t_vrcg_disable_freq0_bcm36in)
      ,.reg_ddrc_t_vrcg_enable_freq0 (reg_ddrc_t_vrcg_enable_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG23
   //------------------------
      ,.r1951_dramset1tmg23_freq0 (r1951_dramset1tmg23_freq0)
      ,.reg_ddrc_t_pdn_freq0 (reg_ddrc_t_pdn_freq0)
      ,.reg_ddrc_t_xsr_dsm_x1024_freq0 (reg_ddrc_t_xsr_dsm_x1024_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG24
   //------------------------
      ,.r1952_dramset1tmg24_freq0 (r1952_dramset1tmg24_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_max_wr_sync_freq0 (reg_ddrc_max_wr_sync_freq0_bcm36in)
      ,.reg_ddrc_max_rd_sync_freq0 (reg_ddrc_max_rd_sync_freq0_bcm36in)
      ,.reg_ddrc_rd2wr_s_freq0 (reg_ddrc_rd2wr_s_freq0_bcm36in)
      ,.reg_ddrc_bank_org_freq0 (reg_ddrc_bank_org_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG25
   //------------------------
      ,.r1953_dramset1tmg25_freq0 (r1953_dramset1tmg25_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_rda2pre_freq0 (reg_ddrc_rda2pre_freq0_bcm36in)
      ,.reg_ddrc_wra2pre_freq0 (reg_ddrc_wra2pre_freq0_bcm36in)
      ,.reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0 (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG30
   //------------------------
      ,.r1958_dramset1tmg30_freq0 (r1958_dramset1tmg30_freq0)
      ,.reg_ddrc_mrr2rd_freq0 (reg_ddrc_mrr2rd_freq0)
      ,.reg_ddrc_mrr2wr_freq0 (reg_ddrc_mrr2wr_freq0)
      ,.reg_ddrc_mrr2mrw_freq0 (reg_ddrc_mrr2mrw_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DRAMSET1TMG32
   //------------------------
      ,.r1960_dramset1tmg32_freq0 (r1960_dramset1tmg32_freq0)
      ,.reg_ddrc_ws_fs2wck_sus_freq0 (reg_ddrc_ws_fs2wck_sus_freq0)
      ,.reg_ddrc_t_wcksus_freq0 (reg_ddrc_t_wcksus_freq0)
      ,.reg_ddrc_ws_off2ws_fs_freq0 (reg_ddrc_ws_off2ws_fs_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR0
   //------------------------
      ,.r1991_initmr0_freq0 (r1991_initmr0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_emr_freq0 (reg_ddrc_emr_freq0_bcm36in)
      ,.reg_ddrc_mr_freq0 (reg_ddrc_mr_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR1
   //------------------------
      ,.r1992_initmr1_freq0 (r1992_initmr1_freq0)
      ,.reg_ddrc_emr3_freq0 (reg_ddrc_emr3_freq0)
      ,.reg_ddrc_emr2_freq0 (reg_ddrc_emr2_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR2
   //------------------------
      ,.r1993_initmr2_freq0 (r1993_initmr2_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_mr5_freq0 (reg_ddrc_mr5_freq0_bcm36in)
      ,.reg_ddrc_mr4_freq0 (reg_ddrc_mr4_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.INITMR3
   //------------------------
      ,.r1994_initmr3_freq0 (r1994_initmr3_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_mr6_freq0 (reg_ddrc_mr6_freq0_bcm36in)
      ,.reg_ddrc_mr22_freq0 (reg_ddrc_mr22_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG0
   //------------------------
      ,.r1995_dfitmg0_freq0 (r1995_dfitmg0_freq0)
      ,.reg_ddrc_dfi_tphy_wrlat_freq0 (reg_ddrc_dfi_tphy_wrlat_freq0)
      ,.reg_ddrc_dfi_tphy_wrdata_freq0 (reg_ddrc_dfi_tphy_wrdata_freq0)
      ,.reg_ddrc_dfi_t_rddata_en_freq0 (reg_ddrc_dfi_t_rddata_en_freq0)
      ,.reg_ddrc_dfi_t_ctrl_delay_freq0 (reg_ddrc_dfi_t_ctrl_delay_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG1
   //------------------------
      ,.r1996_dfitmg1_freq0 (r1996_dfitmg1_freq0)
      ,.reg_ddrc_dfi_t_dram_clk_enable_freq0 (reg_ddrc_dfi_t_dram_clk_enable_freq0)
      ,.reg_ddrc_dfi_t_dram_clk_disable_freq0 (reg_ddrc_dfi_t_dram_clk_disable_freq0)
      ,.reg_ddrc_dfi_t_wrdata_delay_freq0 (reg_ddrc_dfi_t_wrdata_delay_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG2
   //------------------------
      ,.r1997_dfitmg2_freq0 (r1997_dfitmg2_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_tphy_wrcslat_freq0 (reg_ddrc_dfi_tphy_wrcslat_freq0_bcm36in)
      ,.reg_ddrc_dfi_tphy_rdcslat_freq0 (reg_ddrc_dfi_tphy_rdcslat_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_delay_freq0 (reg_ddrc_dfi_twck_delay_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG4
   //------------------------
      ,.r1999_dfitmg4_freq0 (r1999_dfitmg4_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_dis_freq0 (reg_ddrc_dfi_twck_dis_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_en_fs_freq0 (reg_ddrc_dfi_twck_en_fs_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_en_wr_freq0 (reg_ddrc_dfi_twck_en_wr_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_en_rd_freq0 (reg_ddrc_dfi_twck_en_rd_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG5
   //------------------------
      ,.r2000_dfitmg5_freq0 (r2000_dfitmg5_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_freq0 (reg_ddrc_dfi_twck_toggle_post_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_cs_freq0 (reg_ddrc_dfi_twck_toggle_cs_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_freq0 (reg_ddrc_dfi_twck_toggle_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_fast_toggle_freq0 (reg_ddrc_dfi_twck_fast_toggle_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DFITMG6
   //------------------------
      ,.r2001_dfitmg6_freq0 (r2001_dfitmg6_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_rd_freq0 (reg_ddrc_dfi_twck_toggle_post_rd_freq0_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_post_rd_en_freq0 (reg_ddrc_dfi_twck_toggle_post_rd_en_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG0
   //------------------------
      ,.r2003_dfilptmg0_freq0 (r2003_dfilptmg0_freq0)
      ,.reg_ddrc_dfi_lp_wakeup_pd_freq0 (reg_ddrc_dfi_lp_wakeup_pd_freq0)
      ,.reg_ddrc_dfi_lp_wakeup_sr_freq0 (reg_ddrc_dfi_lp_wakeup_sr_freq0)
      ,.reg_ddrc_dfi_lp_wakeup_dsm_freq0 (reg_ddrc_dfi_lp_wakeup_dsm_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DFILPTMG1
   //------------------------
      ,.r2004_dfilptmg1_freq0 (r2004_dfilptmg1_freq0)
      ,.reg_ddrc_dfi_lp_wakeup_data_freq0 (reg_ddrc_dfi_lp_wakeup_data_freq0)
      ,.reg_ddrc_dfi_tlp_resp_freq0 (reg_ddrc_dfi_tlp_resp_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG0
   //------------------------
      ,.r2005_dfiupdtmg0_freq0 (r2005_dfiupdtmg0_freq0)
      ,.reg_ddrc_dfi_t_ctrlup_min_freq0 (reg_ddrc_dfi_t_ctrlup_min_freq0)
      ,.reg_ddrc_dfi_t_ctrlup_max_freq0 (reg_ddrc_dfi_t_ctrlup_max_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG1
   //------------------------
      ,.r2006_dfiupdtmg1_freq0 (r2006_dfiupdtmg1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0_bcm36in)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG2
   //------------------------
      ,.r2008_dfiupdtmg2_freq0 (r2008_dfiupdtmg2_freq0)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0 (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq0)
      ,.reg_ddrc_ctrlupd_after_dqsosc_freq0 (reg_ddrc_ctrlupd_after_dqsosc_freq0)
      ,.reg_ddrc_ppt2_override_freq0 (reg_ddrc_ppt2_override_freq0)
      ,.reg_ddrc_ppt2_en_freq0 (reg_ddrc_ppt2_en_freq0)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0 (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DFIUPDTMG3
   //------------------------
      ,.r2009_dfiupdtmg3_freq0 (r2009_dfiupdtmg3_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0 (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG0
   //------------------------
      ,.r2010_rfshset1tmg0_freq0 (r2010_rfshset1tmg0_freq0)
      ,.reg_ddrc_t_refi_x1_x32_freq0 (reg_ddrc_t_refi_x1_x32_freq0)
      ,.reg_ddrc_refresh_to_x1_x32_freq0 (reg_ddrc_refresh_to_x1_x32_freq0)
      ,.reg_ddrc_refresh_margin_freq0 (reg_ddrc_refresh_margin_freq0)
      ,.reg_ddrc_refresh_to_x1_sel_freq0 (reg_ddrc_refresh_to_x1_sel_freq0)
      ,.reg_ddrc_t_refi_x1_sel_freq0 (reg_ddrc_t_refi_x1_sel_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG1
   //------------------------
      ,.r2011_rfshset1tmg1_freq0 (r2011_rfshset1tmg1_freq0)
      ,.reg_ddrc_t_rfc_min_freq0 (reg_ddrc_t_rfc_min_freq0)
      ,.reg_ddrc_t_rfc_min_ab_freq0 (reg_ddrc_t_rfc_min_ab_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG2
   //------------------------
      ,.r2012_rfshset1tmg2_freq0 (r2012_rfshset1tmg2_freq0)
      ,.reg_ddrc_t_pbr2pbr_freq0 (reg_ddrc_t_pbr2pbr_freq0)
      ,.reg_ddrc_t_pbr2act_freq0 (reg_ddrc_t_pbr2act_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG3
   //------------------------
      ,.r2013_rfshset1tmg3_freq0 (r2013_rfshset1tmg3_freq0)
      ,.reg_ddrc_refresh_to_ab_x32_freq0 (reg_ddrc_refresh_to_ab_x32_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.RFSHSET1TMG4
   //------------------------
      ,.r2014_rfshset1tmg4_freq0 (r2014_rfshset1tmg4_freq0)
      ,.reg_ddrc_refresh_timer0_start_value_x32_freq0 (reg_ddrc_refresh_timer0_start_value_x32_freq0)
      ,.reg_ddrc_refresh_timer1_start_value_x32_freq0 (reg_ddrc_refresh_timer1_start_value_x32_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.RFMSET1TMG0
   //------------------------
      ,.r2024_rfmset1tmg0_freq0 (r2024_rfmset1tmg0_freq0)
      ,.reg_ddrc_t_rfmpb_freq0 (reg_ddrc_t_rfmpb_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG0
   //------------------------
      ,.r2035_zqset1tmg0_freq0 (r2035_zqset1tmg0_freq0)
      ,.reg_ddrc_t_zq_long_nop_freq0 (reg_ddrc_t_zq_long_nop_freq0)
      ,.reg_ddrc_t_zq_short_nop_freq0 (reg_ddrc_t_zq_short_nop_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG1
   //------------------------
      ,.r2036_zqset1tmg1_freq0 (r2036_zqset1tmg1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_zq_short_interval_x1024_freq0 (reg_ddrc_t_zq_short_interval_x1024_freq0_bcm36in)
      ,.reg_ddrc_t_zq_reset_nop_freq0 (reg_ddrc_t_zq_reset_nop_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.ZQSET1TMG2
   //------------------------
      ,.r2037_zqset1tmg2_freq0 (r2037_zqset1tmg2_freq0)
      ,.reg_ddrc_t_zq_stop_freq0 (reg_ddrc_t_zq_stop_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DQSOSCCTL0
   //------------------------
      ,.r2046_dqsoscctl0_freq0 (r2046_dqsoscctl0_freq0)
      ,.reg_ddrc_dqsosc_enable_freq0 (reg_ddrc_dqsosc_enable_freq0)
      ,.reg_ddrc_dqsosc_interval_unit_freq0 (reg_ddrc_dqsosc_interval_unit_freq0)
      ,.reg_ddrc_dqsosc_interval_freq0 (reg_ddrc_dqsosc_interval_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEINT
   //------------------------
      ,.r2047_derateint_freq0 (r2047_derateint_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_mr4_read_interval_freq0 (reg_ddrc_mr4_read_interval_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL0
   //------------------------
      ,.r2048_derateval0_freq0 (r2048_derateval0_freq0)
      ,.reg_ddrc_derated_t_rrd_freq0 (reg_ddrc_derated_t_rrd_freq0)
      ,.reg_ddrc_derated_t_rp_freq0 (reg_ddrc_derated_t_rp_freq0)
      ,.reg_ddrc_derated_t_ras_min_freq0 (reg_ddrc_derated_t_ras_min_freq0)
      ,.reg_ddrc_derated_t_rcd_freq0 (reg_ddrc_derated_t_rcd_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.DERATEVAL1
   //------------------------
      ,.r2049_derateval1_freq0 (r2049_derateval1_freq0)
      ,.reg_ddrc_derated_t_rc_freq0 (reg_ddrc_derated_t_rc_freq0)
      ,.reg_ddrc_derated_t_rcd_write_freq0 (reg_ddrc_derated_t_rcd_write_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.HWLPTMG0
   //------------------------
      ,.r2050_hwlptmg0_freq0 (r2050_hwlptmg0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_hw_lp_idle_x32_freq0 (reg_ddrc_hw_lp_idle_x32_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DVFSCTL0
   //------------------------
      ,.r2051_dvfsctl0_freq0 (r2051_dvfsctl0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_dvfsq_enable_freq0 (reg_ddrc_dvfsq_enable_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.SCHEDTMG0
   //------------------------
      ,.r2052_schedtmg0_freq0 (r2052_schedtmg0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_pageclose_timer_freq0 (reg_ddrc_pageclose_timer_freq0_bcm36in)
      ,.reg_ddrc_rdwr_idle_gap_freq0 (reg_ddrc_rdwr_idle_gap_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.PERFHPR1
   //------------------------
      ,.r2053_perfhpr1_freq0 (r2053_perfhpr1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_hpr_max_starve_freq0 (reg_ddrc_hpr_max_starve_freq0_bcm36in)
      ,.reg_ddrc_hpr_xact_run_length_freq0 (reg_ddrc_hpr_xact_run_length_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.PERFLPR1
   //------------------------
      ,.r2054_perflpr1_freq0 (r2054_perflpr1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_lpr_max_starve_freq0 (reg_ddrc_lpr_max_starve_freq0_bcm36in)
      ,.reg_ddrc_lpr_xact_run_length_freq0 (reg_ddrc_lpr_xact_run_length_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.PERFWR1
   //------------------------
      ,.r2055_perfwr1_freq0 (r2055_perfwr1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_w_max_starve_freq0 (reg_ddrc_w_max_starve_freq0_bcm36in)
      ,.reg_ddrc_w_xact_run_length_freq0 (reg_ddrc_w_xact_run_length_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.TMGCFG
   //------------------------
      ,.r2056_tmgcfg_freq0 (r2056_tmgcfg_freq0)
      ,.reg_ddrc_frequency_ratio_freq0 (reg_ddrc_frequency_ratio_freq0)
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG0
   //------------------------
      ,.r2057_ranktmg0_freq0 (r2057_ranktmg0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_diff_rank_rd_gap_freq0 (reg_ddrc_diff_rank_rd_gap_freq0_bcm36in)
      ,.reg_ddrc_diff_rank_wr_gap_freq0 (reg_ddrc_diff_rank_wr_gap_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.RANKTMG1
   //------------------------
      ,.r2058_ranktmg1_freq0 (r2058_ranktmg1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_dr_freq0 (reg_ddrc_wr2rd_dr_freq0_bcm36in)
      ,.reg_ddrc_rd2wr_dr_freq0 (reg_ddrc_rd2wr_dr_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.PWRTMG
   //------------------------
      ,.r2059_pwrtmg_freq0 (r2059_pwrtmg_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_powerdown_to_x32_freq0 (reg_ddrc_powerdown_to_x32_freq0_bcm36in)
      ,.reg_ddrc_selfref_to_x32_freq0 (reg_ddrc_selfref_to_x32_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG0
   //------------------------
      ,.r2065_ddr4pprtmg0_freq0 (r2065_ddr4pprtmg0_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgm_x1_x1024_freq0 (reg_ddrc_t_pgm_x1_x1024_freq0_bcm36in)
      ,.reg_ddrc_t_pgm_x1_sel_freq0 (reg_ddrc_t_pgm_x1_sel_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.DDR4PPRTMG1
   //------------------------
      ,.r2066_ddr4pprtmg1_freq0 (r2066_ddr4pprtmg1_freq0[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgmpst_x32_freq0 (reg_ddrc_t_pgmpst_x32_freq0_bcm36in)
      ,.reg_ddrc_t_pgm_exit_freq0 (reg_ddrc_t_pgm_exit_freq0_bcm36in)
   //------------------------
   // Register REGB_FREQ0_CH0.LNKECCCTL0
   //------------------------
      ,.r2067_lnkeccctl0_freq0 (r2067_lnkeccctl0_freq0)
      ,.reg_ddrc_wr_link_ecc_enable_freq0 (reg_ddrc_wr_link_ecc_enable_freq0)
      ,.reg_ddrc_rd_link_ecc_enable_freq0 (reg_ddrc_rd_link_ecc_enable_freq0)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG0
   //------------------------
      ,.r2201_dramset1tmg0_freq1 (r2201_dramset1tmg0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ras_min_freq1 (reg_ddrc_t_ras_min_freq1_bcm36in)
      ,.reg_ddrc_t_ras_max_freq1 (reg_ddrc_t_ras_max_freq1_bcm36in)
      ,.reg_ddrc_t_faw_freq1 (reg_ddrc_t_faw_freq1_bcm36in)
      ,.reg_ddrc_wr2pre_freq1 (reg_ddrc_wr2pre_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG1
   //------------------------
      ,.r2202_dramset1tmg1_freq1 (r2202_dramset1tmg1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rc_freq1 (reg_ddrc_t_rc_freq1_bcm36in)
      ,.reg_ddrc_rd2pre_freq1 (reg_ddrc_rd2pre_freq1_bcm36in)
      ,.reg_ddrc_t_xp_freq1 (reg_ddrc_t_xp_freq1_bcm36in)
      ,.reg_ddrc_t_rcd_write_freq1 (reg_ddrc_t_rcd_write_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG2
   //------------------------
      ,.r2203_dramset1tmg2_freq1 (r2203_dramset1tmg2_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_freq1 (reg_ddrc_wr2rd_freq1_bcm36in)
      ,.reg_ddrc_rd2wr_freq1 (reg_ddrc_rd2wr_freq1_bcm36in)
      ,.reg_ddrc_read_latency_freq1 (reg_ddrc_read_latency_freq1_bcm36in)
      ,.reg_ddrc_write_latency_freq1 (reg_ddrc_write_latency_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG3
   //------------------------
      ,.r2204_dramset1tmg3_freq1 (r2204_dramset1tmg3_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2mr_freq1 (reg_ddrc_wr2mr_freq1_bcm36in)
      ,.reg_ddrc_rd2mr_freq1 (reg_ddrc_rd2mr_freq1_bcm36in)
      ,.reg_ddrc_t_mr_freq1 (reg_ddrc_t_mr_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG4
   //------------------------
      ,.r2205_dramset1tmg4_freq1 (r2205_dramset1tmg4_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rp_freq1 (reg_ddrc_t_rp_freq1_bcm36in)
      ,.reg_ddrc_t_rrd_freq1 (reg_ddrc_t_rrd_freq1_bcm36in)
      ,.reg_ddrc_t_ccd_freq1 (reg_ddrc_t_ccd_freq1_bcm36in)
      ,.reg_ddrc_t_rcd_freq1 (reg_ddrc_t_rcd_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG5
   //------------------------
      ,.r2206_dramset1tmg5_freq1 (r2206_dramset1tmg5_freq1)
      ,.reg_ddrc_t_cke_freq1 (reg_ddrc_t_cke_freq1)
      ,.reg_ddrc_t_ckesr_freq1 (reg_ddrc_t_ckesr_freq1)
      ,.reg_ddrc_t_cksre_freq1 (reg_ddrc_t_cksre_freq1)
      ,.reg_ddrc_t_cksrx_freq1 (reg_ddrc_t_cksrx_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG6
   //------------------------
      ,.r2207_dramset1tmg6_freq1 (r2207_dramset1tmg6_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ckcsx_freq1 (reg_ddrc_t_ckcsx_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG7
   //------------------------
      ,.r2208_dramset1tmg7_freq1 (r2208_dramset1tmg7_freq1)
      ,.reg_ddrc_t_csh_freq1 (reg_ddrc_t_csh_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG9
   //------------------------
      ,.r2210_dramset1tmg9_freq1 (r2210_dramset1tmg9_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_s_freq1 (reg_ddrc_wr2rd_s_freq1_bcm36in)
      ,.reg_ddrc_t_rrd_s_freq1 (reg_ddrc_t_rrd_s_freq1_bcm36in)
      ,.reg_ddrc_t_ccd_s_freq1 (reg_ddrc_t_ccd_s_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG12
   //------------------------
      ,.r2213_dramset1tmg12_freq1 (r2213_dramset1tmg12_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_cmdcke_freq1 (reg_ddrc_t_cmdcke_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG13
   //------------------------
      ,.r2214_dramset1tmg13_freq1 (r2214_dramset1tmg13_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ppd_freq1 (reg_ddrc_t_ppd_freq1_bcm36in)
      ,.reg_ddrc_t_ccd_mw_freq1 (reg_ddrc_t_ccd_mw_freq1_bcm36in)
      ,.reg_ddrc_odtloff_freq1 (reg_ddrc_odtloff_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG14
   //------------------------
      ,.r2215_dramset1tmg14_freq1 (r2215_dramset1tmg14_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_xsr_freq1 (reg_ddrc_t_xsr_freq1_bcm36in)
      ,.reg_ddrc_t_osco_freq1 (reg_ddrc_t_osco_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG17
   //------------------------
      ,.r2218_dramset1tmg17_freq1 (r2218_dramset1tmg17_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_vrcg_disable_freq1 (reg_ddrc_t_vrcg_disable_freq1_bcm36in)
      ,.reg_ddrc_t_vrcg_enable_freq1 (reg_ddrc_t_vrcg_enable_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG23
   //------------------------
      ,.r2223_dramset1tmg23_freq1 (r2223_dramset1tmg23_freq1)
      ,.reg_ddrc_t_pdn_freq1 (reg_ddrc_t_pdn_freq1)
      ,.reg_ddrc_t_xsr_dsm_x1024_freq1 (reg_ddrc_t_xsr_dsm_x1024_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG24
   //------------------------
      ,.r2224_dramset1tmg24_freq1 (r2224_dramset1tmg24_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_max_wr_sync_freq1 (reg_ddrc_max_wr_sync_freq1_bcm36in)
      ,.reg_ddrc_max_rd_sync_freq1 (reg_ddrc_max_rd_sync_freq1_bcm36in)
      ,.reg_ddrc_rd2wr_s_freq1 (reg_ddrc_rd2wr_s_freq1_bcm36in)
      ,.reg_ddrc_bank_org_freq1 (reg_ddrc_bank_org_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG25
   //------------------------
      ,.r2225_dramset1tmg25_freq1 (r2225_dramset1tmg25_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_rda2pre_freq1 (reg_ddrc_rda2pre_freq1_bcm36in)
      ,.reg_ddrc_wra2pre_freq1 (reg_ddrc_wra2pre_freq1_bcm36in)
      ,.reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1 (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG30
   //------------------------
      ,.r2230_dramset1tmg30_freq1 (r2230_dramset1tmg30_freq1)
      ,.reg_ddrc_mrr2rd_freq1 (reg_ddrc_mrr2rd_freq1)
      ,.reg_ddrc_mrr2wr_freq1 (reg_ddrc_mrr2wr_freq1)
      ,.reg_ddrc_mrr2mrw_freq1 (reg_ddrc_mrr2mrw_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DRAMSET1TMG32
   //------------------------
      ,.r2232_dramset1tmg32_freq1 (r2232_dramset1tmg32_freq1)
      ,.reg_ddrc_ws_fs2wck_sus_freq1 (reg_ddrc_ws_fs2wck_sus_freq1)
      ,.reg_ddrc_t_wcksus_freq1 (reg_ddrc_t_wcksus_freq1)
      ,.reg_ddrc_ws_off2ws_fs_freq1 (reg_ddrc_ws_off2ws_fs_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR0
   //------------------------
      ,.r2263_initmr0_freq1 (r2263_initmr0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_emr_freq1 (reg_ddrc_emr_freq1_bcm36in)
      ,.reg_ddrc_mr_freq1 (reg_ddrc_mr_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR1
   //------------------------
      ,.r2264_initmr1_freq1 (r2264_initmr1_freq1)
      ,.reg_ddrc_emr3_freq1 (reg_ddrc_emr3_freq1)
      ,.reg_ddrc_emr2_freq1 (reg_ddrc_emr2_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR2
   //------------------------
      ,.r2265_initmr2_freq1 (r2265_initmr2_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_mr5_freq1 (reg_ddrc_mr5_freq1_bcm36in)
      ,.reg_ddrc_mr4_freq1 (reg_ddrc_mr4_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.INITMR3
   //------------------------
      ,.r2266_initmr3_freq1 (r2266_initmr3_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_mr6_freq1 (reg_ddrc_mr6_freq1_bcm36in)
      ,.reg_ddrc_mr22_freq1 (reg_ddrc_mr22_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG0
   //------------------------
      ,.r2267_dfitmg0_freq1 (r2267_dfitmg0_freq1)
      ,.reg_ddrc_dfi_tphy_wrlat_freq1 (reg_ddrc_dfi_tphy_wrlat_freq1)
      ,.reg_ddrc_dfi_tphy_wrdata_freq1 (reg_ddrc_dfi_tphy_wrdata_freq1)
      ,.reg_ddrc_dfi_t_rddata_en_freq1 (reg_ddrc_dfi_t_rddata_en_freq1)
      ,.reg_ddrc_dfi_t_ctrl_delay_freq1 (reg_ddrc_dfi_t_ctrl_delay_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG1
   //------------------------
      ,.r2268_dfitmg1_freq1 (r2268_dfitmg1_freq1)
      ,.reg_ddrc_dfi_t_dram_clk_enable_freq1 (reg_ddrc_dfi_t_dram_clk_enable_freq1)
      ,.reg_ddrc_dfi_t_dram_clk_disable_freq1 (reg_ddrc_dfi_t_dram_clk_disable_freq1)
      ,.reg_ddrc_dfi_t_wrdata_delay_freq1 (reg_ddrc_dfi_t_wrdata_delay_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG2
   //------------------------
      ,.r2269_dfitmg2_freq1 (r2269_dfitmg2_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_tphy_wrcslat_freq1 (reg_ddrc_dfi_tphy_wrcslat_freq1_bcm36in)
      ,.reg_ddrc_dfi_tphy_rdcslat_freq1 (reg_ddrc_dfi_tphy_rdcslat_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_delay_freq1 (reg_ddrc_dfi_twck_delay_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG4
   //------------------------
      ,.r2271_dfitmg4_freq1 (r2271_dfitmg4_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_dis_freq1 (reg_ddrc_dfi_twck_dis_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_en_fs_freq1 (reg_ddrc_dfi_twck_en_fs_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_en_wr_freq1 (reg_ddrc_dfi_twck_en_wr_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_en_rd_freq1 (reg_ddrc_dfi_twck_en_rd_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG5
   //------------------------
      ,.r2272_dfitmg5_freq1 (r2272_dfitmg5_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_freq1 (reg_ddrc_dfi_twck_toggle_post_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_cs_freq1 (reg_ddrc_dfi_twck_toggle_cs_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_freq1 (reg_ddrc_dfi_twck_toggle_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_fast_toggle_freq1 (reg_ddrc_dfi_twck_fast_toggle_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DFITMG6
   //------------------------
      ,.r2273_dfitmg6_freq1 (r2273_dfitmg6_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_rd_freq1 (reg_ddrc_dfi_twck_toggle_post_rd_freq1_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_post_rd_en_freq1 (reg_ddrc_dfi_twck_toggle_post_rd_en_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG1
   //------------------------
      ,.r2275_dfiupdtmg1_freq1 (r2275_dfiupdtmg1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1_bcm36in)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG2
   //------------------------
      ,.r2276_dfiupdtmg2_freq1 (r2276_dfiupdtmg2_freq1)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1 (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq1)
      ,.reg_ddrc_ctrlupd_after_dqsosc_freq1 (reg_ddrc_ctrlupd_after_dqsosc_freq1)
      ,.reg_ddrc_ppt2_override_freq1 (reg_ddrc_ppt2_override_freq1)
      ,.reg_ddrc_ppt2_en_freq1 (reg_ddrc_ppt2_en_freq1)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1 (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DFIUPDTMG3
   //------------------------
      ,.r2277_dfiupdtmg3_freq1 (r2277_dfiupdtmg3_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1 (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG0
   //------------------------
      ,.r2278_rfshset1tmg0_freq1 (r2278_rfshset1tmg0_freq1)
      ,.reg_ddrc_t_refi_x1_x32_freq1 (reg_ddrc_t_refi_x1_x32_freq1)
      ,.reg_ddrc_refresh_to_x1_x32_freq1 (reg_ddrc_refresh_to_x1_x32_freq1)
      ,.reg_ddrc_refresh_margin_freq1 (reg_ddrc_refresh_margin_freq1)
      ,.reg_ddrc_refresh_to_x1_sel_freq1 (reg_ddrc_refresh_to_x1_sel_freq1)
      ,.reg_ddrc_t_refi_x1_sel_freq1 (reg_ddrc_t_refi_x1_sel_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG1
   //------------------------
      ,.r2279_rfshset1tmg1_freq1 (r2279_rfshset1tmg1_freq1)
      ,.reg_ddrc_t_rfc_min_freq1 (reg_ddrc_t_rfc_min_freq1)
      ,.reg_ddrc_t_rfc_min_ab_freq1 (reg_ddrc_t_rfc_min_ab_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG2
   //------------------------
      ,.r2280_rfshset1tmg2_freq1 (r2280_rfshset1tmg2_freq1)
      ,.reg_ddrc_t_pbr2pbr_freq1 (reg_ddrc_t_pbr2pbr_freq1)
      ,.reg_ddrc_t_pbr2act_freq1 (reg_ddrc_t_pbr2act_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG3
   //------------------------
      ,.r2281_rfshset1tmg3_freq1 (r2281_rfshset1tmg3_freq1)
      ,.reg_ddrc_refresh_to_ab_x32_freq1 (reg_ddrc_refresh_to_ab_x32_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.RFSHSET1TMG4
   //------------------------
      ,.r2282_rfshset1tmg4_freq1 (r2282_rfshset1tmg4_freq1)
      ,.reg_ddrc_refresh_timer0_start_value_x32_freq1 (reg_ddrc_refresh_timer0_start_value_x32_freq1)
      ,.reg_ddrc_refresh_timer1_start_value_x32_freq1 (reg_ddrc_refresh_timer1_start_value_x32_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.RFMSET1TMG0
   //------------------------
      ,.r2292_rfmset1tmg0_freq1 (r2292_rfmset1tmg0_freq1)
      ,.reg_ddrc_t_rfmpb_freq1 (reg_ddrc_t_rfmpb_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG0
   //------------------------
      ,.r2303_zqset1tmg0_freq1 (r2303_zqset1tmg0_freq1)
      ,.reg_ddrc_t_zq_long_nop_freq1 (reg_ddrc_t_zq_long_nop_freq1)
      ,.reg_ddrc_t_zq_short_nop_freq1 (reg_ddrc_t_zq_short_nop_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG1
   //------------------------
      ,.r2304_zqset1tmg1_freq1 (r2304_zqset1tmg1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_zq_short_interval_x1024_freq1 (reg_ddrc_t_zq_short_interval_x1024_freq1_bcm36in)
      ,.reg_ddrc_t_zq_reset_nop_freq1 (reg_ddrc_t_zq_reset_nop_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.ZQSET1TMG2
   //------------------------
      ,.r2305_zqset1tmg2_freq1 (r2305_zqset1tmg2_freq1)
      ,.reg_ddrc_t_zq_stop_freq1 (reg_ddrc_t_zq_stop_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DQSOSCCTL0
   //------------------------
      ,.r2314_dqsoscctl0_freq1 (r2314_dqsoscctl0_freq1)
      ,.reg_ddrc_dqsosc_enable_freq1 (reg_ddrc_dqsosc_enable_freq1)
      ,.reg_ddrc_dqsosc_interval_unit_freq1 (reg_ddrc_dqsosc_interval_unit_freq1)
      ,.reg_ddrc_dqsosc_interval_freq1 (reg_ddrc_dqsosc_interval_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEINT
   //------------------------
      ,.r2315_derateint_freq1 (r2315_derateint_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_mr4_read_interval_freq1 (reg_ddrc_mr4_read_interval_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL0
   //------------------------
      ,.r2316_derateval0_freq1 (r2316_derateval0_freq1)
      ,.reg_ddrc_derated_t_rrd_freq1 (reg_ddrc_derated_t_rrd_freq1)
      ,.reg_ddrc_derated_t_rp_freq1 (reg_ddrc_derated_t_rp_freq1)
      ,.reg_ddrc_derated_t_ras_min_freq1 (reg_ddrc_derated_t_ras_min_freq1)
      ,.reg_ddrc_derated_t_rcd_freq1 (reg_ddrc_derated_t_rcd_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.DERATEVAL1
   //------------------------
      ,.r2317_derateval1_freq1 (r2317_derateval1_freq1)
      ,.reg_ddrc_derated_t_rc_freq1 (reg_ddrc_derated_t_rc_freq1)
      ,.reg_ddrc_derated_t_rcd_write_freq1 (reg_ddrc_derated_t_rcd_write_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.HWLPTMG0
   //------------------------
      ,.r2318_hwlptmg0_freq1 (r2318_hwlptmg0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_hw_lp_idle_x32_freq1 (reg_ddrc_hw_lp_idle_x32_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DVFSCTL0
   //------------------------
      ,.r2319_dvfsctl0_freq1 (r2319_dvfsctl0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_dvfsq_enable_freq1 (reg_ddrc_dvfsq_enable_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.SCHEDTMG0
   //------------------------
      ,.r2320_schedtmg0_freq1 (r2320_schedtmg0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_pageclose_timer_freq1 (reg_ddrc_pageclose_timer_freq1_bcm36in)
      ,.reg_ddrc_rdwr_idle_gap_freq1 (reg_ddrc_rdwr_idle_gap_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.PERFHPR1
   //------------------------
      ,.r2321_perfhpr1_freq1 (r2321_perfhpr1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_hpr_max_starve_freq1 (reg_ddrc_hpr_max_starve_freq1_bcm36in)
      ,.reg_ddrc_hpr_xact_run_length_freq1 (reg_ddrc_hpr_xact_run_length_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.PERFLPR1
   //------------------------
      ,.r2322_perflpr1_freq1 (r2322_perflpr1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_lpr_max_starve_freq1 (reg_ddrc_lpr_max_starve_freq1_bcm36in)
      ,.reg_ddrc_lpr_xact_run_length_freq1 (reg_ddrc_lpr_xact_run_length_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.PERFWR1
   //------------------------
      ,.r2323_perfwr1_freq1 (r2323_perfwr1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_w_max_starve_freq1 (reg_ddrc_w_max_starve_freq1_bcm36in)
      ,.reg_ddrc_w_xact_run_length_freq1 (reg_ddrc_w_xact_run_length_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.TMGCFG
   //------------------------
      ,.r2324_tmgcfg_freq1 (r2324_tmgcfg_freq1)
      ,.reg_ddrc_frequency_ratio_freq1 (reg_ddrc_frequency_ratio_freq1)
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG0
   //------------------------
      ,.r2325_ranktmg0_freq1 (r2325_ranktmg0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_diff_rank_rd_gap_freq1 (reg_ddrc_diff_rank_rd_gap_freq1_bcm36in)
      ,.reg_ddrc_diff_rank_wr_gap_freq1 (reg_ddrc_diff_rank_wr_gap_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.RANKTMG1
   //------------------------
      ,.r2326_ranktmg1_freq1 (r2326_ranktmg1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_dr_freq1 (reg_ddrc_wr2rd_dr_freq1_bcm36in)
      ,.reg_ddrc_rd2wr_dr_freq1 (reg_ddrc_rd2wr_dr_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.PWRTMG
   //------------------------
      ,.r2327_pwrtmg_freq1 (r2327_pwrtmg_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_powerdown_to_x32_freq1 (reg_ddrc_powerdown_to_x32_freq1_bcm36in)
      ,.reg_ddrc_selfref_to_x32_freq1 (reg_ddrc_selfref_to_x32_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG0
   //------------------------
      ,.r2333_ddr4pprtmg0_freq1 (r2333_ddr4pprtmg0_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgm_x1_x1024_freq1 (reg_ddrc_t_pgm_x1_x1024_freq1_bcm36in)
      ,.reg_ddrc_t_pgm_x1_sel_freq1 (reg_ddrc_t_pgm_x1_sel_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.DDR4PPRTMG1
   //------------------------
      ,.r2334_ddr4pprtmg1_freq1 (r2334_ddr4pprtmg1_freq1[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgmpst_x32_freq1 (reg_ddrc_t_pgmpst_x32_freq1_bcm36in)
      ,.reg_ddrc_t_pgm_exit_freq1 (reg_ddrc_t_pgm_exit_freq1_bcm36in)
   //------------------------
   // Register REGB_FREQ1_CH0.LNKECCCTL0
   //------------------------
      ,.r2335_lnkeccctl0_freq1 (r2335_lnkeccctl0_freq1)
      ,.reg_ddrc_wr_link_ecc_enable_freq1 (reg_ddrc_wr_link_ecc_enable_freq1)
      ,.reg_ddrc_rd_link_ecc_enable_freq1 (reg_ddrc_rd_link_ecc_enable_freq1)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG0
   //------------------------
      ,.r2469_dramset1tmg0_freq2 (r2469_dramset1tmg0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ras_min_freq2 (reg_ddrc_t_ras_min_freq2_bcm36in)
      ,.reg_ddrc_t_ras_max_freq2 (reg_ddrc_t_ras_max_freq2_bcm36in)
      ,.reg_ddrc_t_faw_freq2 (reg_ddrc_t_faw_freq2_bcm36in)
      ,.reg_ddrc_wr2pre_freq2 (reg_ddrc_wr2pre_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG1
   //------------------------
      ,.r2470_dramset1tmg1_freq2 (r2470_dramset1tmg1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rc_freq2 (reg_ddrc_t_rc_freq2_bcm36in)
      ,.reg_ddrc_rd2pre_freq2 (reg_ddrc_rd2pre_freq2_bcm36in)
      ,.reg_ddrc_t_xp_freq2 (reg_ddrc_t_xp_freq2_bcm36in)
      ,.reg_ddrc_t_rcd_write_freq2 (reg_ddrc_t_rcd_write_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG2
   //------------------------
      ,.r2471_dramset1tmg2_freq2 (r2471_dramset1tmg2_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_freq2 (reg_ddrc_wr2rd_freq2_bcm36in)
      ,.reg_ddrc_rd2wr_freq2 (reg_ddrc_rd2wr_freq2_bcm36in)
      ,.reg_ddrc_read_latency_freq2 (reg_ddrc_read_latency_freq2_bcm36in)
      ,.reg_ddrc_write_latency_freq2 (reg_ddrc_write_latency_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG3
   //------------------------
      ,.r2472_dramset1tmg3_freq2 (r2472_dramset1tmg3_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2mr_freq2 (reg_ddrc_wr2mr_freq2_bcm36in)
      ,.reg_ddrc_rd2mr_freq2 (reg_ddrc_rd2mr_freq2_bcm36in)
      ,.reg_ddrc_t_mr_freq2 (reg_ddrc_t_mr_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG4
   //------------------------
      ,.r2473_dramset1tmg4_freq2 (r2473_dramset1tmg4_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rp_freq2 (reg_ddrc_t_rp_freq2_bcm36in)
      ,.reg_ddrc_t_rrd_freq2 (reg_ddrc_t_rrd_freq2_bcm36in)
      ,.reg_ddrc_t_ccd_freq2 (reg_ddrc_t_ccd_freq2_bcm36in)
      ,.reg_ddrc_t_rcd_freq2 (reg_ddrc_t_rcd_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG5
   //------------------------
      ,.r2474_dramset1tmg5_freq2 (r2474_dramset1tmg5_freq2)
      ,.reg_ddrc_t_cke_freq2 (reg_ddrc_t_cke_freq2)
      ,.reg_ddrc_t_ckesr_freq2 (reg_ddrc_t_ckesr_freq2)
      ,.reg_ddrc_t_cksre_freq2 (reg_ddrc_t_cksre_freq2)
      ,.reg_ddrc_t_cksrx_freq2 (reg_ddrc_t_cksrx_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG6
   //------------------------
      ,.r2475_dramset1tmg6_freq2 (r2475_dramset1tmg6_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ckcsx_freq2 (reg_ddrc_t_ckcsx_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG7
   //------------------------
      ,.r2476_dramset1tmg7_freq2 (r2476_dramset1tmg7_freq2)
      ,.reg_ddrc_t_csh_freq2 (reg_ddrc_t_csh_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG9
   //------------------------
      ,.r2478_dramset1tmg9_freq2 (r2478_dramset1tmg9_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_s_freq2 (reg_ddrc_wr2rd_s_freq2_bcm36in)
      ,.reg_ddrc_t_rrd_s_freq2 (reg_ddrc_t_rrd_s_freq2_bcm36in)
      ,.reg_ddrc_t_ccd_s_freq2 (reg_ddrc_t_ccd_s_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG12
   //------------------------
      ,.r2481_dramset1tmg12_freq2 (r2481_dramset1tmg12_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_cmdcke_freq2 (reg_ddrc_t_cmdcke_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG13
   //------------------------
      ,.r2482_dramset1tmg13_freq2 (r2482_dramset1tmg13_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ppd_freq2 (reg_ddrc_t_ppd_freq2_bcm36in)
      ,.reg_ddrc_t_ccd_mw_freq2 (reg_ddrc_t_ccd_mw_freq2_bcm36in)
      ,.reg_ddrc_odtloff_freq2 (reg_ddrc_odtloff_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG14
   //------------------------
      ,.r2483_dramset1tmg14_freq2 (r2483_dramset1tmg14_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_xsr_freq2 (reg_ddrc_t_xsr_freq2_bcm36in)
      ,.reg_ddrc_t_osco_freq2 (reg_ddrc_t_osco_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG17
   //------------------------
      ,.r2486_dramset1tmg17_freq2 (r2486_dramset1tmg17_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_vrcg_disable_freq2 (reg_ddrc_t_vrcg_disable_freq2_bcm36in)
      ,.reg_ddrc_t_vrcg_enable_freq2 (reg_ddrc_t_vrcg_enable_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG23
   //------------------------
      ,.r2491_dramset1tmg23_freq2 (r2491_dramset1tmg23_freq2)
      ,.reg_ddrc_t_pdn_freq2 (reg_ddrc_t_pdn_freq2)
      ,.reg_ddrc_t_xsr_dsm_x1024_freq2 (reg_ddrc_t_xsr_dsm_x1024_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG24
   //------------------------
      ,.r2492_dramset1tmg24_freq2 (r2492_dramset1tmg24_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_max_wr_sync_freq2 (reg_ddrc_max_wr_sync_freq2_bcm36in)
      ,.reg_ddrc_max_rd_sync_freq2 (reg_ddrc_max_rd_sync_freq2_bcm36in)
      ,.reg_ddrc_rd2wr_s_freq2 (reg_ddrc_rd2wr_s_freq2_bcm36in)
      ,.reg_ddrc_bank_org_freq2 (reg_ddrc_bank_org_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG25
   //------------------------
      ,.r2493_dramset1tmg25_freq2 (r2493_dramset1tmg25_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_rda2pre_freq2 (reg_ddrc_rda2pre_freq2_bcm36in)
      ,.reg_ddrc_wra2pre_freq2 (reg_ddrc_wra2pre_freq2_bcm36in)
      ,.reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2 (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG30
   //------------------------
      ,.r2498_dramset1tmg30_freq2 (r2498_dramset1tmg30_freq2)
      ,.reg_ddrc_mrr2rd_freq2 (reg_ddrc_mrr2rd_freq2)
      ,.reg_ddrc_mrr2wr_freq2 (reg_ddrc_mrr2wr_freq2)
      ,.reg_ddrc_mrr2mrw_freq2 (reg_ddrc_mrr2mrw_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DRAMSET1TMG32
   //------------------------
      ,.r2500_dramset1tmg32_freq2 (r2500_dramset1tmg32_freq2)
      ,.reg_ddrc_ws_fs2wck_sus_freq2 (reg_ddrc_ws_fs2wck_sus_freq2)
      ,.reg_ddrc_t_wcksus_freq2 (reg_ddrc_t_wcksus_freq2)
      ,.reg_ddrc_ws_off2ws_fs_freq2 (reg_ddrc_ws_off2ws_fs_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR0
   //------------------------
      ,.r2531_initmr0_freq2 (r2531_initmr0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_emr_freq2 (reg_ddrc_emr_freq2_bcm36in)
      ,.reg_ddrc_mr_freq2 (reg_ddrc_mr_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR1
   //------------------------
      ,.r2532_initmr1_freq2 (r2532_initmr1_freq2)
      ,.reg_ddrc_emr3_freq2 (reg_ddrc_emr3_freq2)
      ,.reg_ddrc_emr2_freq2 (reg_ddrc_emr2_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR2
   //------------------------
      ,.r2533_initmr2_freq2 (r2533_initmr2_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_mr5_freq2 (reg_ddrc_mr5_freq2_bcm36in)
      ,.reg_ddrc_mr4_freq2 (reg_ddrc_mr4_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.INITMR3
   //------------------------
      ,.r2534_initmr3_freq2 (r2534_initmr3_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_mr6_freq2 (reg_ddrc_mr6_freq2_bcm36in)
      ,.reg_ddrc_mr22_freq2 (reg_ddrc_mr22_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG0
   //------------------------
      ,.r2535_dfitmg0_freq2 (r2535_dfitmg0_freq2)
      ,.reg_ddrc_dfi_tphy_wrlat_freq2 (reg_ddrc_dfi_tphy_wrlat_freq2)
      ,.reg_ddrc_dfi_tphy_wrdata_freq2 (reg_ddrc_dfi_tphy_wrdata_freq2)
      ,.reg_ddrc_dfi_t_rddata_en_freq2 (reg_ddrc_dfi_t_rddata_en_freq2)
      ,.reg_ddrc_dfi_t_ctrl_delay_freq2 (reg_ddrc_dfi_t_ctrl_delay_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG1
   //------------------------
      ,.r2536_dfitmg1_freq2 (r2536_dfitmg1_freq2)
      ,.reg_ddrc_dfi_t_dram_clk_enable_freq2 (reg_ddrc_dfi_t_dram_clk_enable_freq2)
      ,.reg_ddrc_dfi_t_dram_clk_disable_freq2 (reg_ddrc_dfi_t_dram_clk_disable_freq2)
      ,.reg_ddrc_dfi_t_wrdata_delay_freq2 (reg_ddrc_dfi_t_wrdata_delay_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG2
   //------------------------
      ,.r2537_dfitmg2_freq2 (r2537_dfitmg2_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_tphy_wrcslat_freq2 (reg_ddrc_dfi_tphy_wrcslat_freq2_bcm36in)
      ,.reg_ddrc_dfi_tphy_rdcslat_freq2 (reg_ddrc_dfi_tphy_rdcslat_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_delay_freq2 (reg_ddrc_dfi_twck_delay_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG4
   //------------------------
      ,.r2539_dfitmg4_freq2 (r2539_dfitmg4_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_dis_freq2 (reg_ddrc_dfi_twck_dis_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_en_fs_freq2 (reg_ddrc_dfi_twck_en_fs_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_en_wr_freq2 (reg_ddrc_dfi_twck_en_wr_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_en_rd_freq2 (reg_ddrc_dfi_twck_en_rd_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG5
   //------------------------
      ,.r2540_dfitmg5_freq2 (r2540_dfitmg5_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_freq2 (reg_ddrc_dfi_twck_toggle_post_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_cs_freq2 (reg_ddrc_dfi_twck_toggle_cs_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_freq2 (reg_ddrc_dfi_twck_toggle_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_fast_toggle_freq2 (reg_ddrc_dfi_twck_fast_toggle_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DFITMG6
   //------------------------
      ,.r2541_dfitmg6_freq2 (r2541_dfitmg6_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_rd_freq2 (reg_ddrc_dfi_twck_toggle_post_rd_freq2_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_post_rd_en_freq2 (reg_ddrc_dfi_twck_toggle_post_rd_en_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG1
   //------------------------
      ,.r2543_dfiupdtmg1_freq2 (r2543_dfiupdtmg1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2_bcm36in)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG2
   //------------------------
      ,.r2544_dfiupdtmg2_freq2 (r2544_dfiupdtmg2_freq2)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2 (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq2)
      ,.reg_ddrc_ctrlupd_after_dqsosc_freq2 (reg_ddrc_ctrlupd_after_dqsosc_freq2)
      ,.reg_ddrc_ppt2_override_freq2 (reg_ddrc_ppt2_override_freq2)
      ,.reg_ddrc_ppt2_en_freq2 (reg_ddrc_ppt2_en_freq2)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2 (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DFIUPDTMG3
   //------------------------
      ,.r2545_dfiupdtmg3_freq2 (r2545_dfiupdtmg3_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2 (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG0
   //------------------------
      ,.r2546_rfshset1tmg0_freq2 (r2546_rfshset1tmg0_freq2)
      ,.reg_ddrc_t_refi_x1_x32_freq2 (reg_ddrc_t_refi_x1_x32_freq2)
      ,.reg_ddrc_refresh_to_x1_x32_freq2 (reg_ddrc_refresh_to_x1_x32_freq2)
      ,.reg_ddrc_refresh_margin_freq2 (reg_ddrc_refresh_margin_freq2)
      ,.reg_ddrc_refresh_to_x1_sel_freq2 (reg_ddrc_refresh_to_x1_sel_freq2)
      ,.reg_ddrc_t_refi_x1_sel_freq2 (reg_ddrc_t_refi_x1_sel_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG1
   //------------------------
      ,.r2547_rfshset1tmg1_freq2 (r2547_rfshset1tmg1_freq2)
      ,.reg_ddrc_t_rfc_min_freq2 (reg_ddrc_t_rfc_min_freq2)
      ,.reg_ddrc_t_rfc_min_ab_freq2 (reg_ddrc_t_rfc_min_ab_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG2
   //------------------------
      ,.r2548_rfshset1tmg2_freq2 (r2548_rfshset1tmg2_freq2)
      ,.reg_ddrc_t_pbr2pbr_freq2 (reg_ddrc_t_pbr2pbr_freq2)
      ,.reg_ddrc_t_pbr2act_freq2 (reg_ddrc_t_pbr2act_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG3
   //------------------------
      ,.r2549_rfshset1tmg3_freq2 (r2549_rfshset1tmg3_freq2)
      ,.reg_ddrc_refresh_to_ab_x32_freq2 (reg_ddrc_refresh_to_ab_x32_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.RFSHSET1TMG4
   //------------------------
      ,.r2550_rfshset1tmg4_freq2 (r2550_rfshset1tmg4_freq2)
      ,.reg_ddrc_refresh_timer0_start_value_x32_freq2 (reg_ddrc_refresh_timer0_start_value_x32_freq2)
      ,.reg_ddrc_refresh_timer1_start_value_x32_freq2 (reg_ddrc_refresh_timer1_start_value_x32_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.RFMSET1TMG0
   //------------------------
      ,.r2560_rfmset1tmg0_freq2 (r2560_rfmset1tmg0_freq2)
      ,.reg_ddrc_t_rfmpb_freq2 (reg_ddrc_t_rfmpb_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG0
   //------------------------
      ,.r2571_zqset1tmg0_freq2 (r2571_zqset1tmg0_freq2)
      ,.reg_ddrc_t_zq_long_nop_freq2 (reg_ddrc_t_zq_long_nop_freq2)
      ,.reg_ddrc_t_zq_short_nop_freq2 (reg_ddrc_t_zq_short_nop_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG1
   //------------------------
      ,.r2572_zqset1tmg1_freq2 (r2572_zqset1tmg1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_zq_short_interval_x1024_freq2 (reg_ddrc_t_zq_short_interval_x1024_freq2_bcm36in)
      ,.reg_ddrc_t_zq_reset_nop_freq2 (reg_ddrc_t_zq_reset_nop_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.ZQSET1TMG2
   //------------------------
      ,.r2573_zqset1tmg2_freq2 (r2573_zqset1tmg2_freq2)
      ,.reg_ddrc_t_zq_stop_freq2 (reg_ddrc_t_zq_stop_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DQSOSCCTL0
   //------------------------
      ,.r2582_dqsoscctl0_freq2 (r2582_dqsoscctl0_freq2)
      ,.reg_ddrc_dqsosc_enable_freq2 (reg_ddrc_dqsosc_enable_freq2)
      ,.reg_ddrc_dqsosc_interval_unit_freq2 (reg_ddrc_dqsosc_interval_unit_freq2)
      ,.reg_ddrc_dqsosc_interval_freq2 (reg_ddrc_dqsosc_interval_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEINT
   //------------------------
      ,.r2583_derateint_freq2 (r2583_derateint_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_mr4_read_interval_freq2 (reg_ddrc_mr4_read_interval_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL0
   //------------------------
      ,.r2584_derateval0_freq2 (r2584_derateval0_freq2)
      ,.reg_ddrc_derated_t_rrd_freq2 (reg_ddrc_derated_t_rrd_freq2)
      ,.reg_ddrc_derated_t_rp_freq2 (reg_ddrc_derated_t_rp_freq2)
      ,.reg_ddrc_derated_t_ras_min_freq2 (reg_ddrc_derated_t_ras_min_freq2)
      ,.reg_ddrc_derated_t_rcd_freq2 (reg_ddrc_derated_t_rcd_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.DERATEVAL1
   //------------------------
      ,.r2585_derateval1_freq2 (r2585_derateval1_freq2)
      ,.reg_ddrc_derated_t_rc_freq2 (reg_ddrc_derated_t_rc_freq2)
      ,.reg_ddrc_derated_t_rcd_write_freq2 (reg_ddrc_derated_t_rcd_write_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.HWLPTMG0
   //------------------------
      ,.r2586_hwlptmg0_freq2 (r2586_hwlptmg0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_hw_lp_idle_x32_freq2 (reg_ddrc_hw_lp_idle_x32_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DVFSCTL0
   //------------------------
      ,.r2587_dvfsctl0_freq2 (r2587_dvfsctl0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_dvfsq_enable_freq2 (reg_ddrc_dvfsq_enable_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.SCHEDTMG0
   //------------------------
      ,.r2588_schedtmg0_freq2 (r2588_schedtmg0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_pageclose_timer_freq2 (reg_ddrc_pageclose_timer_freq2_bcm36in)
      ,.reg_ddrc_rdwr_idle_gap_freq2 (reg_ddrc_rdwr_idle_gap_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.PERFHPR1
   //------------------------
      ,.r2589_perfhpr1_freq2 (r2589_perfhpr1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_hpr_max_starve_freq2 (reg_ddrc_hpr_max_starve_freq2_bcm36in)
      ,.reg_ddrc_hpr_xact_run_length_freq2 (reg_ddrc_hpr_xact_run_length_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.PERFLPR1
   //------------------------
      ,.r2590_perflpr1_freq2 (r2590_perflpr1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_lpr_max_starve_freq2 (reg_ddrc_lpr_max_starve_freq2_bcm36in)
      ,.reg_ddrc_lpr_xact_run_length_freq2 (reg_ddrc_lpr_xact_run_length_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.PERFWR1
   //------------------------
      ,.r2591_perfwr1_freq2 (r2591_perfwr1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_w_max_starve_freq2 (reg_ddrc_w_max_starve_freq2_bcm36in)
      ,.reg_ddrc_w_xact_run_length_freq2 (reg_ddrc_w_xact_run_length_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.TMGCFG
   //------------------------
      ,.r2592_tmgcfg_freq2 (r2592_tmgcfg_freq2)
      ,.reg_ddrc_frequency_ratio_freq2 (reg_ddrc_frequency_ratio_freq2)
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG0
   //------------------------
      ,.r2593_ranktmg0_freq2 (r2593_ranktmg0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_diff_rank_rd_gap_freq2 (reg_ddrc_diff_rank_rd_gap_freq2_bcm36in)
      ,.reg_ddrc_diff_rank_wr_gap_freq2 (reg_ddrc_diff_rank_wr_gap_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.RANKTMG1
   //------------------------
      ,.r2594_ranktmg1_freq2 (r2594_ranktmg1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_dr_freq2 (reg_ddrc_wr2rd_dr_freq2_bcm36in)
      ,.reg_ddrc_rd2wr_dr_freq2 (reg_ddrc_rd2wr_dr_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.PWRTMG
   //------------------------
      ,.r2595_pwrtmg_freq2 (r2595_pwrtmg_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_powerdown_to_x32_freq2 (reg_ddrc_powerdown_to_x32_freq2_bcm36in)
      ,.reg_ddrc_selfref_to_x32_freq2 (reg_ddrc_selfref_to_x32_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG0
   //------------------------
      ,.r2601_ddr4pprtmg0_freq2 (r2601_ddr4pprtmg0_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgm_x1_x1024_freq2 (reg_ddrc_t_pgm_x1_x1024_freq2_bcm36in)
      ,.reg_ddrc_t_pgm_x1_sel_freq2 (reg_ddrc_t_pgm_x1_sel_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.DDR4PPRTMG1
   //------------------------
      ,.r2602_ddr4pprtmg1_freq2 (r2602_ddr4pprtmg1_freq2[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgmpst_x32_freq2 (reg_ddrc_t_pgmpst_x32_freq2_bcm36in)
      ,.reg_ddrc_t_pgm_exit_freq2 (reg_ddrc_t_pgm_exit_freq2_bcm36in)
   //------------------------
   // Register REGB_FREQ2_CH0.LNKECCCTL0
   //------------------------
      ,.r2603_lnkeccctl0_freq2 (r2603_lnkeccctl0_freq2)
      ,.reg_ddrc_wr_link_ecc_enable_freq2 (reg_ddrc_wr_link_ecc_enable_freq2)
      ,.reg_ddrc_rd_link_ecc_enable_freq2 (reg_ddrc_rd_link_ecc_enable_freq2)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG0
   //------------------------
      ,.r2737_dramset1tmg0_freq3 (r2737_dramset1tmg0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ras_min_freq3 (reg_ddrc_t_ras_min_freq3_bcm36in)
      ,.reg_ddrc_t_ras_max_freq3 (reg_ddrc_t_ras_max_freq3_bcm36in)
      ,.reg_ddrc_t_faw_freq3 (reg_ddrc_t_faw_freq3_bcm36in)
      ,.reg_ddrc_wr2pre_freq3 (reg_ddrc_wr2pre_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG1
   //------------------------
      ,.r2738_dramset1tmg1_freq3 (r2738_dramset1tmg1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rc_freq3 (reg_ddrc_t_rc_freq3_bcm36in)
      ,.reg_ddrc_rd2pre_freq3 (reg_ddrc_rd2pre_freq3_bcm36in)
      ,.reg_ddrc_t_xp_freq3 (reg_ddrc_t_xp_freq3_bcm36in)
      ,.reg_ddrc_t_rcd_write_freq3 (reg_ddrc_t_rcd_write_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG2
   //------------------------
      ,.r2739_dramset1tmg2_freq3 (r2739_dramset1tmg2_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_freq3 (reg_ddrc_wr2rd_freq3_bcm36in)
      ,.reg_ddrc_rd2wr_freq3 (reg_ddrc_rd2wr_freq3_bcm36in)
      ,.reg_ddrc_read_latency_freq3 (reg_ddrc_read_latency_freq3_bcm36in)
      ,.reg_ddrc_write_latency_freq3 (reg_ddrc_write_latency_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG3
   //------------------------
      ,.r2740_dramset1tmg3_freq3 (r2740_dramset1tmg3_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2mr_freq3 (reg_ddrc_wr2mr_freq3_bcm36in)
      ,.reg_ddrc_rd2mr_freq3 (reg_ddrc_rd2mr_freq3_bcm36in)
      ,.reg_ddrc_t_mr_freq3 (reg_ddrc_t_mr_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG4
   //------------------------
      ,.r2741_dramset1tmg4_freq3 (r2741_dramset1tmg4_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_rp_freq3 (reg_ddrc_t_rp_freq3_bcm36in)
      ,.reg_ddrc_t_rrd_freq3 (reg_ddrc_t_rrd_freq3_bcm36in)
      ,.reg_ddrc_t_ccd_freq3 (reg_ddrc_t_ccd_freq3_bcm36in)
      ,.reg_ddrc_t_rcd_freq3 (reg_ddrc_t_rcd_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG5
   //------------------------
      ,.r2742_dramset1tmg5_freq3 (r2742_dramset1tmg5_freq3)
      ,.reg_ddrc_t_cke_freq3 (reg_ddrc_t_cke_freq3)
      ,.reg_ddrc_t_ckesr_freq3 (reg_ddrc_t_ckesr_freq3)
      ,.reg_ddrc_t_cksre_freq3 (reg_ddrc_t_cksre_freq3)
      ,.reg_ddrc_t_cksrx_freq3 (reg_ddrc_t_cksrx_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG6
   //------------------------
      ,.r2743_dramset1tmg6_freq3 (r2743_dramset1tmg6_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ckcsx_freq3 (reg_ddrc_t_ckcsx_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG7
   //------------------------
      ,.r2744_dramset1tmg7_freq3 (r2744_dramset1tmg7_freq3)
      ,.reg_ddrc_t_csh_freq3 (reg_ddrc_t_csh_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG9
   //------------------------
      ,.r2746_dramset1tmg9_freq3 (r2746_dramset1tmg9_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_s_freq3 (reg_ddrc_wr2rd_s_freq3_bcm36in)
      ,.reg_ddrc_t_rrd_s_freq3 (reg_ddrc_t_rrd_s_freq3_bcm36in)
      ,.reg_ddrc_t_ccd_s_freq3 (reg_ddrc_t_ccd_s_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG12
   //------------------------
      ,.r2749_dramset1tmg12_freq3 (r2749_dramset1tmg12_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_cmdcke_freq3 (reg_ddrc_t_cmdcke_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG13
   //------------------------
      ,.r2750_dramset1tmg13_freq3 (r2750_dramset1tmg13_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_ppd_freq3 (reg_ddrc_t_ppd_freq3_bcm36in)
      ,.reg_ddrc_t_ccd_mw_freq3 (reg_ddrc_t_ccd_mw_freq3_bcm36in)
      ,.reg_ddrc_odtloff_freq3 (reg_ddrc_odtloff_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG14
   //------------------------
      ,.r2751_dramset1tmg14_freq3 (r2751_dramset1tmg14_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_xsr_freq3 (reg_ddrc_t_xsr_freq3_bcm36in)
      ,.reg_ddrc_t_osco_freq3 (reg_ddrc_t_osco_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG17
   //------------------------
      ,.r2754_dramset1tmg17_freq3 (r2754_dramset1tmg17_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_vrcg_disable_freq3 (reg_ddrc_t_vrcg_disable_freq3_bcm36in)
      ,.reg_ddrc_t_vrcg_enable_freq3 (reg_ddrc_t_vrcg_enable_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG23
   //------------------------
      ,.r2759_dramset1tmg23_freq3 (r2759_dramset1tmg23_freq3)
      ,.reg_ddrc_t_pdn_freq3 (reg_ddrc_t_pdn_freq3)
      ,.reg_ddrc_t_xsr_dsm_x1024_freq3 (reg_ddrc_t_xsr_dsm_x1024_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG24
   //------------------------
      ,.r2760_dramset1tmg24_freq3 (r2760_dramset1tmg24_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_max_wr_sync_freq3 (reg_ddrc_max_wr_sync_freq3_bcm36in)
      ,.reg_ddrc_max_rd_sync_freq3 (reg_ddrc_max_rd_sync_freq3_bcm36in)
      ,.reg_ddrc_rd2wr_s_freq3 (reg_ddrc_rd2wr_s_freq3_bcm36in)
      ,.reg_ddrc_bank_org_freq3 (reg_ddrc_bank_org_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG25
   //------------------------
      ,.r2761_dramset1tmg25_freq3 (r2761_dramset1tmg25_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_rda2pre_freq3 (reg_ddrc_rda2pre_freq3_bcm36in)
      ,.reg_ddrc_wra2pre_freq3 (reg_ddrc_wra2pre_freq3_bcm36in)
      ,.reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3 (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG30
   //------------------------
      ,.r2766_dramset1tmg30_freq3 (r2766_dramset1tmg30_freq3)
      ,.reg_ddrc_mrr2rd_freq3 (reg_ddrc_mrr2rd_freq3)
      ,.reg_ddrc_mrr2wr_freq3 (reg_ddrc_mrr2wr_freq3)
      ,.reg_ddrc_mrr2mrw_freq3 (reg_ddrc_mrr2mrw_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DRAMSET1TMG32
   //------------------------
      ,.r2768_dramset1tmg32_freq3 (r2768_dramset1tmg32_freq3)
      ,.reg_ddrc_ws_fs2wck_sus_freq3 (reg_ddrc_ws_fs2wck_sus_freq3)
      ,.reg_ddrc_t_wcksus_freq3 (reg_ddrc_t_wcksus_freq3)
      ,.reg_ddrc_ws_off2ws_fs_freq3 (reg_ddrc_ws_off2ws_fs_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR0
   //------------------------
      ,.r2799_initmr0_freq3 (r2799_initmr0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_emr_freq3 (reg_ddrc_emr_freq3_bcm36in)
      ,.reg_ddrc_mr_freq3 (reg_ddrc_mr_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR1
   //------------------------
      ,.r2800_initmr1_freq3 (r2800_initmr1_freq3)
      ,.reg_ddrc_emr3_freq3 (reg_ddrc_emr3_freq3)
      ,.reg_ddrc_emr2_freq3 (reg_ddrc_emr2_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR2
   //------------------------
      ,.r2801_initmr2_freq3 (r2801_initmr2_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_mr5_freq3 (reg_ddrc_mr5_freq3_bcm36in)
      ,.reg_ddrc_mr4_freq3 (reg_ddrc_mr4_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.INITMR3
   //------------------------
      ,.r2802_initmr3_freq3 (r2802_initmr3_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_mr6_freq3 (reg_ddrc_mr6_freq3_bcm36in)
      ,.reg_ddrc_mr22_freq3 (reg_ddrc_mr22_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG0
   //------------------------
      ,.r2803_dfitmg0_freq3 (r2803_dfitmg0_freq3)
      ,.reg_ddrc_dfi_tphy_wrlat_freq3 (reg_ddrc_dfi_tphy_wrlat_freq3)
      ,.reg_ddrc_dfi_tphy_wrdata_freq3 (reg_ddrc_dfi_tphy_wrdata_freq3)
      ,.reg_ddrc_dfi_t_rddata_en_freq3 (reg_ddrc_dfi_t_rddata_en_freq3)
      ,.reg_ddrc_dfi_t_ctrl_delay_freq3 (reg_ddrc_dfi_t_ctrl_delay_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG1
   //------------------------
      ,.r2804_dfitmg1_freq3 (r2804_dfitmg1_freq3)
      ,.reg_ddrc_dfi_t_dram_clk_enable_freq3 (reg_ddrc_dfi_t_dram_clk_enable_freq3)
      ,.reg_ddrc_dfi_t_dram_clk_disable_freq3 (reg_ddrc_dfi_t_dram_clk_disable_freq3)
      ,.reg_ddrc_dfi_t_wrdata_delay_freq3 (reg_ddrc_dfi_t_wrdata_delay_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG2
   //------------------------
      ,.r2805_dfitmg2_freq3 (r2805_dfitmg2_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_tphy_wrcslat_freq3 (reg_ddrc_dfi_tphy_wrcslat_freq3_bcm36in)
      ,.reg_ddrc_dfi_tphy_rdcslat_freq3 (reg_ddrc_dfi_tphy_rdcslat_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_delay_freq3 (reg_ddrc_dfi_twck_delay_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG4
   //------------------------
      ,.r2807_dfitmg4_freq3 (r2807_dfitmg4_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_dis_freq3 (reg_ddrc_dfi_twck_dis_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_en_fs_freq3 (reg_ddrc_dfi_twck_en_fs_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_en_wr_freq3 (reg_ddrc_dfi_twck_en_wr_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_en_rd_freq3 (reg_ddrc_dfi_twck_en_rd_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG5
   //------------------------
      ,.r2808_dfitmg5_freq3 (r2808_dfitmg5_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_freq3 (reg_ddrc_dfi_twck_toggle_post_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_cs_freq3 (reg_ddrc_dfi_twck_toggle_cs_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_freq3 (reg_ddrc_dfi_twck_toggle_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_fast_toggle_freq3 (reg_ddrc_dfi_twck_fast_toggle_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DFITMG6
   //------------------------
      ,.r2809_dfitmg6_freq3 (r2809_dfitmg6_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_twck_toggle_post_rd_freq3 (reg_ddrc_dfi_twck_toggle_post_rd_freq3_bcm36in)
      ,.reg_ddrc_dfi_twck_toggle_post_rd_en_freq3 (reg_ddrc_dfi_twck_toggle_post_rd_en_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG1
   //------------------------
      ,.r2811_dfiupdtmg1_freq3 (r2811_dfiupdtmg1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3 (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3_bcm36in)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3 (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG2
   //------------------------
      ,.r2812_dfiupdtmg2_freq3 (r2812_dfiupdtmg2_freq3)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3 (reg_ddrc_dfi_t_ctrlupd_interval_type1_freq3)
      ,.reg_ddrc_ctrlupd_after_dqsosc_freq3 (reg_ddrc_ctrlupd_after_dqsosc_freq3)
      ,.reg_ddrc_ppt2_override_freq3 (reg_ddrc_ppt2_override_freq3)
      ,.reg_ddrc_ppt2_en_freq3 (reg_ddrc_ppt2_en_freq3)
      ,.reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3 (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DFIUPDTMG3
   //------------------------
      ,.r2813_dfiupdtmg3_freq3 (r2813_dfiupdtmg3_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3 (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG0
   //------------------------
      ,.r2814_rfshset1tmg0_freq3 (r2814_rfshset1tmg0_freq3)
      ,.reg_ddrc_t_refi_x1_x32_freq3 (reg_ddrc_t_refi_x1_x32_freq3)
      ,.reg_ddrc_refresh_to_x1_x32_freq3 (reg_ddrc_refresh_to_x1_x32_freq3)
      ,.reg_ddrc_refresh_margin_freq3 (reg_ddrc_refresh_margin_freq3)
      ,.reg_ddrc_refresh_to_x1_sel_freq3 (reg_ddrc_refresh_to_x1_sel_freq3)
      ,.reg_ddrc_t_refi_x1_sel_freq3 (reg_ddrc_t_refi_x1_sel_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG1
   //------------------------
      ,.r2815_rfshset1tmg1_freq3 (r2815_rfshset1tmg1_freq3)
      ,.reg_ddrc_t_rfc_min_freq3 (reg_ddrc_t_rfc_min_freq3)
      ,.reg_ddrc_t_rfc_min_ab_freq3 (reg_ddrc_t_rfc_min_ab_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG2
   //------------------------
      ,.r2816_rfshset1tmg2_freq3 (r2816_rfshset1tmg2_freq3)
      ,.reg_ddrc_t_pbr2pbr_freq3 (reg_ddrc_t_pbr2pbr_freq3)
      ,.reg_ddrc_t_pbr2act_freq3 (reg_ddrc_t_pbr2act_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG3
   //------------------------
      ,.r2817_rfshset1tmg3_freq3 (r2817_rfshset1tmg3_freq3)
      ,.reg_ddrc_refresh_to_ab_x32_freq3 (reg_ddrc_refresh_to_ab_x32_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.RFSHSET1TMG4
   //------------------------
      ,.r2818_rfshset1tmg4_freq3 (r2818_rfshset1tmg4_freq3)
      ,.reg_ddrc_refresh_timer0_start_value_x32_freq3 (reg_ddrc_refresh_timer0_start_value_x32_freq3)
      ,.reg_ddrc_refresh_timer1_start_value_x32_freq3 (reg_ddrc_refresh_timer1_start_value_x32_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.RFMSET1TMG0
   //------------------------
      ,.r2828_rfmset1tmg0_freq3 (r2828_rfmset1tmg0_freq3)
      ,.reg_ddrc_t_rfmpb_freq3 (reg_ddrc_t_rfmpb_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG0
   //------------------------
      ,.r2839_zqset1tmg0_freq3 (r2839_zqset1tmg0_freq3)
      ,.reg_ddrc_t_zq_long_nop_freq3 (reg_ddrc_t_zq_long_nop_freq3)
      ,.reg_ddrc_t_zq_short_nop_freq3 (reg_ddrc_t_zq_short_nop_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG1
   //------------------------
      ,.r2840_zqset1tmg1_freq3 (r2840_zqset1tmg1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_zq_short_interval_x1024_freq3 (reg_ddrc_t_zq_short_interval_x1024_freq3_bcm36in)
      ,.reg_ddrc_t_zq_reset_nop_freq3 (reg_ddrc_t_zq_reset_nop_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.ZQSET1TMG2
   //------------------------
      ,.r2841_zqset1tmg2_freq3 (r2841_zqset1tmg2_freq3)
      ,.reg_ddrc_t_zq_stop_freq3 (reg_ddrc_t_zq_stop_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DQSOSCCTL0
   //------------------------
      ,.r2850_dqsoscctl0_freq3 (r2850_dqsoscctl0_freq3)
      ,.reg_ddrc_dqsosc_enable_freq3 (reg_ddrc_dqsosc_enable_freq3)
      ,.reg_ddrc_dqsosc_interval_unit_freq3 (reg_ddrc_dqsosc_interval_unit_freq3)
      ,.reg_ddrc_dqsosc_interval_freq3 (reg_ddrc_dqsosc_interval_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEINT
   //------------------------
      ,.r2851_derateint_freq3 (r2851_derateint_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_mr4_read_interval_freq3 (reg_ddrc_mr4_read_interval_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL0
   //------------------------
      ,.r2852_derateval0_freq3 (r2852_derateval0_freq3)
      ,.reg_ddrc_derated_t_rrd_freq3 (reg_ddrc_derated_t_rrd_freq3)
      ,.reg_ddrc_derated_t_rp_freq3 (reg_ddrc_derated_t_rp_freq3)
      ,.reg_ddrc_derated_t_ras_min_freq3 (reg_ddrc_derated_t_ras_min_freq3)
      ,.reg_ddrc_derated_t_rcd_freq3 (reg_ddrc_derated_t_rcd_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.DERATEVAL1
   //------------------------
      ,.r2853_derateval1_freq3 (r2853_derateval1_freq3)
      ,.reg_ddrc_derated_t_rc_freq3 (reg_ddrc_derated_t_rc_freq3)
      ,.reg_ddrc_derated_t_rcd_write_freq3 (reg_ddrc_derated_t_rcd_write_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.HWLPTMG0
   //------------------------
      ,.r2854_hwlptmg0_freq3 (r2854_hwlptmg0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_hw_lp_idle_x32_freq3 (reg_ddrc_hw_lp_idle_x32_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DVFSCTL0
   //------------------------
      ,.r2855_dvfsctl0_freq3 (r2855_dvfsctl0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_dvfsq_enable_freq3 (reg_ddrc_dvfsq_enable_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.SCHEDTMG0
   //------------------------
      ,.r2856_schedtmg0_freq3 (r2856_schedtmg0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_pageclose_timer_freq3 (reg_ddrc_pageclose_timer_freq3_bcm36in)
      ,.reg_ddrc_rdwr_idle_gap_freq3 (reg_ddrc_rdwr_idle_gap_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.PERFHPR1
   //------------------------
      ,.r2857_perfhpr1_freq3 (r2857_perfhpr1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_hpr_max_starve_freq3 (reg_ddrc_hpr_max_starve_freq3_bcm36in)
      ,.reg_ddrc_hpr_xact_run_length_freq3 (reg_ddrc_hpr_xact_run_length_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.PERFLPR1
   //------------------------
      ,.r2858_perflpr1_freq3 (r2858_perflpr1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_lpr_max_starve_freq3 (reg_ddrc_lpr_max_starve_freq3_bcm36in)
      ,.reg_ddrc_lpr_xact_run_length_freq3 (reg_ddrc_lpr_xact_run_length_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.PERFWR1
   //------------------------
      ,.r2859_perfwr1_freq3 (r2859_perfwr1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_w_max_starve_freq3 (reg_ddrc_w_max_starve_freq3_bcm36in)
      ,.reg_ddrc_w_xact_run_length_freq3 (reg_ddrc_w_xact_run_length_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.TMGCFG
   //------------------------
      ,.r2860_tmgcfg_freq3 (r2860_tmgcfg_freq3)
      ,.reg_ddrc_frequency_ratio_freq3 (reg_ddrc_frequency_ratio_freq3)
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG0
   //------------------------
      ,.r2861_ranktmg0_freq3 (r2861_ranktmg0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_diff_rank_rd_gap_freq3 (reg_ddrc_diff_rank_rd_gap_freq3_bcm36in)
      ,.reg_ddrc_diff_rank_wr_gap_freq3 (reg_ddrc_diff_rank_wr_gap_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.RANKTMG1
   //------------------------
      ,.r2862_ranktmg1_freq3 (r2862_ranktmg1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_wr2rd_dr_freq3 (reg_ddrc_wr2rd_dr_freq3_bcm36in)
      ,.reg_ddrc_rd2wr_dr_freq3 (reg_ddrc_rd2wr_dr_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.PWRTMG
   //------------------------
      ,.r2863_pwrtmg_freq3 (r2863_pwrtmg_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_powerdown_to_x32_freq3 (reg_ddrc_powerdown_to_x32_freq3_bcm36in)
      ,.reg_ddrc_selfref_to_x32_freq3 (reg_ddrc_selfref_to_x32_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG0
   //------------------------
      ,.r2869_ddr4pprtmg0_freq3 (r2869_ddr4pprtmg0_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgm_x1_x1024_freq3 (reg_ddrc_t_pgm_x1_x1024_freq3_bcm36in)
      ,.reg_ddrc_t_pgm_x1_sel_freq3 (reg_ddrc_t_pgm_x1_sel_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.DDR4PPRTMG1
   //------------------------
      ,.r2870_ddr4pprtmg1_freq3 (r2870_ddr4pprtmg1_freq3[REG_WIDTH-1:0])
      ,.reg_ddrc_t_pgmpst_x32_freq3 (reg_ddrc_t_pgmpst_x32_freq3_bcm36in)
      ,.reg_ddrc_t_pgm_exit_freq3 (reg_ddrc_t_pgm_exit_freq3_bcm36in)
   //------------------------
   // Register REGB_FREQ3_CH0.LNKECCCTL0
   //------------------------
      ,.r2871_lnkeccctl0_freq3 (r2871_lnkeccctl0_freq3)
      ,.reg_ddrc_wr_link_ecc_enable_freq3 (reg_ddrc_wr_link_ecc_enable_freq3)
      ,.reg_ddrc_rd_link_ecc_enable_freq3 (reg_ddrc_rd_link_ecc_enable_freq3)



      ,.ecc_corrected_err_intr_en   (ecc_corrected_err_intr_en)
      ,.ecc_uncorrected_err_intr_en (ecc_uncorrected_err_intr_en)

     ,.ecc_ap_err_intr_en        (ecc_ap_err_intr_en)
      ,.core_derate_temp_limit_intr     (core_derate_temp_limit_intr)
      ,.pclk_derate_temp_limit_intr     (pclk_derate_temp_limit_intr)
     ,.ddrc_reg_ecc_ap_err_int              (ddrc_reg_ecc_ap_err_int)
     ,.pclk_ddrc_reg_ecc_ap_err             (pclk_ddrc_reg_ecc_ap_err)
    ,.ddrc_reg_ecc_corrected_err_int        (ddrc_reg_ecc_corrected_err_int) 
    ,.ddrc_reg_ecc_uncorrected_err_int      (ddrc_reg_ecc_uncorrected_err_int)
    ,.ddrc_reg_ecc_corrected_bit_num_int    (ddrc_reg_ecc_corrected_bit_num_int)
    ,.pclk_ddrc_reg_ecc_corrected_err       (pclk_ddrc_reg_ecc_corrected_err)
    ,.pclk_ddrc_reg_ecc_uncorrected_err     (pclk_ddrc_reg_ecc_uncorrected_err)
    ,.pclk_ddrc_reg_ecc_corrected_bit_num   (pclk_ddrc_reg_ecc_corrected_bit_num)
    ,.ddrc_reg_sbr_read_ecc_err_int         (ddrc_reg_sbr_read_ecc_err_int)
    ,.pclk_ddrc_reg_sbr_read_ecc_err        (ddrc_reg_sbr_read_ecc_err_stat)



    ,.ddrc_reg_rd_linkecc_uncorr_err_intr      (ddrc_reg_rd_linkecc_uncorr_err_intr)
    ,.ddrc_reg_rd_linkecc_corr_err_intr        (ddrc_reg_rd_linkecc_corr_err_intr)
    ,.pclk_ddrc_reg_rd_linkecc_uncorr_err_int  (pclk_ddrc_reg_rd_linkecc_uncorr_err_int)
    ,.pclk_ddrc_reg_rd_linkecc_corr_err_int    (pclk_ddrc_reg_rd_linkecc_corr_err_int)
    ,.rd_link_ecc_uncorr_intr_en               (rd_link_ecc_uncorr_intr_en)
    ,.rd_link_ecc_corr_intr_en                 (rd_link_ecc_corr_intr_en)


);

   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_srx_zqcl (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_srx_zqcl_bcm36in),
       .data_d     (reg_ddrc_dis_srx_zqcl)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_srx_zqcl_hwffc (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_srx_zqcl_hwffc_bcm36in),
       .data_d     (reg_ddrc_dis_srx_zqcl_hwffc)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dqsosc_runtime (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dqsosc_runtime_bcm36in),
       .data_d     (reg_ddrc_dqsosc_runtime)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wck2dqo_runtime (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wck2dqo_runtime_bcm36in),
       .data_d     (reg_ddrc_wck2dqo_runtime)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_dqsosc_srx (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_dqsosc_srx_bcm36in),
       .data_d     (reg_ddrc_dis_dqsosc_srx)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_opt_wrecc_collision_flush (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_opt_wrecc_collision_flush_bcm36in),
       .data_d     (reg_ddrc_dis_opt_wrecc_collision_flush)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_prefer_write (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_prefer_write_bcm36in),
       .data_d     (reg_ddrc_prefer_write)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_pageclose (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_pageclose_bcm36in),
       .data_d     (reg_ddrc_pageclose)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_opt_wrcam_fill_level (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_opt_wrcam_fill_level_bcm36in),
       .data_d     (reg_ddrc_opt_wrcam_fill_level)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_opt_ntt_by_act (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_opt_ntt_by_act_bcm36in),
       .data_d     (reg_ddrc_dis_opt_ntt_by_act)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_opt_ntt_by_pre (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_opt_ntt_by_pre_bcm36in),
       .data_d     (reg_ddrc_dis_opt_ntt_by_pre)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_autopre_rmw (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_autopre_rmw_bcm36in),
       .data_d     (reg_ddrc_autopre_rmw)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_RDCMD_ENTRY_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_num_entries (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_num_entries_bcm36in),
       .data_d     (reg_ddrc_lpr_num_entries)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpddr4_opt_act_timing (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpddr4_opt_act_timing_bcm36in),
       .data_d     (reg_ddrc_lpddr4_opt_act_timing)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpddr5_opt_act_timing (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpddr5_opt_act_timing_bcm36in),
       .data_d     (reg_ddrc_lpddr5_opt_act_timing)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_starve_free_running (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_starve_free_running_bcm36in),
       .data_d     (reg_ddrc_w_starve_free_running)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_opt_act_lat (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_opt_act_lat_bcm36in),
       .data_d     (reg_ddrc_opt_act_lat)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_prefer_read (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_prefer_read_bcm36in),
       .data_d     (reg_ddrc_prefer_read)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_speculative_act (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_speculative_act_bcm36in),
       .data_d     (reg_ddrc_dis_speculative_act)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_opt_vprw_sch (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_opt_vprw_sch_bcm36in),
       .data_d     (reg_ddrc_opt_vprw_sch)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_delay_switch_write (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_delay_switch_write_bcm36in),
       .data_d     (reg_ddrc_delay_switch_write)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_visible_window_limit_wr (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_visible_window_limit_wr_bcm36in),
       .data_d     (reg_ddrc_visible_window_limit_wr)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_visible_window_limit_rd (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_visible_window_limit_rd_bcm36in),
       .data_d     (reg_ddrc_visible_window_limit_rd)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_page_hit_limit_wr (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_page_hit_limit_wr_bcm36in),
       .data_d     (reg_ddrc_page_hit_limit_wr)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_page_hit_limit_rd (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_page_hit_limit_rd_bcm36in),
       .data_d     (reg_ddrc_page_hit_limit_rd)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_opt_hit_gt_hpr (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_opt_hit_gt_hpr_bcm36in),
       .data_d     (reg_ddrc_opt_hit_gt_hpr)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_WRCMD_ENTRY_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wrcam_lowthresh (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wrcam_lowthresh_bcm36in),
       .data_d     (reg_ddrc_wrcam_lowthresh)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_WRCMD_ENTRY_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wrcam_highthresh (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wrcam_highthresh_bcm36in),
       .data_d     (reg_ddrc_wrcam_highthresh)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_WRCMD_ENTRY_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr_pghit_num_thresh (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr_pghit_num_thresh_bcm36in),
       .data_d     (reg_ddrc_wr_pghit_num_thresh)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_RDCMD_ENTRY_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd_pghit_num_thresh (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd_pghit_num_thresh_bcm36in),
       .data_d     (reg_ddrc_rd_pghit_num_thresh)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd_act_idle_gap (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd_act_idle_gap_bcm36in),
       .data_d     (reg_ddrc_rd_act_idle_gap)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr_act_idle_gap (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr_act_idle_gap_bcm36in),
       .data_d     (reg_ddrc_wr_act_idle_gap)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd_page_exp_cycles (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd_page_exp_cycles_bcm36in),
       .data_d     (reg_ddrc_rd_page_exp_cycles)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr_page_exp_cycles (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr_page_exp_cycles_bcm36in),
       .data_d     (reg_ddrc_wr_page_exp_cycles)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_WRCMD_ENTRY_BITS-1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wrecc_cam_lowthresh (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wrecc_cam_lowthresh_bcm36in),
       .data_d     (reg_ddrc_wrecc_cam_lowthresh)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_WRCMD_ENTRY_BITS-1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wrecc_cam_highthresh (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wrecc_cam_highthresh_bcm36in),
       .data_d     (reg_ddrc_wrecc_cam_highthresh)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level_bcm36in),
       .data_d     (reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_opt_valid_wrecc_cam_fill_level (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_opt_valid_wrecc_cam_fill_level_bcm36in),
       .data_d     (reg_ddrc_dis_opt_valid_wrecc_cam_fill_level)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_data_poison_en (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_data_poison_en_bcm36in),
       .data_d     (reg_ddrc_data_poison_en)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_data_poison_bit (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_data_poison_bit_bcm36in),
       .data_d     (reg_ddrc_data_poison_bit)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_region_parity_lock (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_region_parity_lock_bcm36in),
       .data_d     (reg_ddrc_ecc_region_parity_lock)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_region_waste_lock (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_region_waste_lock_bcm36in),
       .data_d     (reg_ddrc_ecc_region_waste_lock)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_med_ecc_en (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_med_ecc_en_bcm36in),
       .data_d     (reg_ddrc_med_ecc_en)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_blk_channel_active_term (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_blk_channel_active_term_bcm36in),
       .data_d     (reg_ddrc_blk_channel_active_term)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_active_blk_channel (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_active_blk_channel_bcm36in),
       .data_d     (reg_ddrc_active_blk_channel)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_col (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_col_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_col)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_RANK_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_rank (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_rank_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_rank)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_PAGE_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_row (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_row_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_row)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_BANK_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_bank (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_bank_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_bank)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`MEMC_BG_BITS),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_bg (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_bg_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_bg)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (32),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_data_31_0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_data_31_0_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_data_31_0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_ecc_poison_data_71_64 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_ecc_poison_data_71_64_bcm36in),
       .data_d     (reg_ddrc_ecc_poison_data_71_64)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_wc (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_wc_bcm36in),
       .data_d     (reg_ddrc_dis_wc)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_max_rank_rd_opt (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_max_rank_rd_opt_bcm36in),
       .data_d     (reg_ddrc_dis_max_rank_rd_opt)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dis_max_rank_wr_opt (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dis_max_rank_wr_opt_bcm36in),
       .data_d     (reg_ddrc_dis_max_rank_wr_opt)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_rank_rd (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_rank_rd_bcm36in),
       .data_d     (reg_ddrc_max_rank_rd)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_rank_wr (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_rank_wr_bcm36in),
       .data_d     (reg_ddrc_max_rank_wr)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_cs_bit0_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_cs_bit0_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_cs_bit0_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_bank_b0_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_bank_b0_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_bank_b0_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_bank_b1_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_bank_b1_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_bank_b1_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_bank_b2_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_bank_b2_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_bank_b2_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_bg_b0_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_bg_b0_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_bg_b0_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_bg_b1_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_bg_b1_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_bg_b1_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b7_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b7_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b7_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b8_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b8_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b8_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b9_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b9_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b9_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b10_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b10_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b10_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b3_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b3_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b3_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b4_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b4_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b4_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b5_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b5_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b5_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_col_b6_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_col_b6_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_col_b6_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b14_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b14_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b14_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b15_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b15_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b15_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b16_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b16_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b16_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b17_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b17_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b17_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b10_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b10_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b10_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b11_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b11_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b11_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b12_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b12_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b12_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b13_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b13_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b13_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b6_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b6_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b6_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b7_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b7_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b7_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b8_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b8_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b8_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b9_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b9_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b9_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b2_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b2_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b2_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b3_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b3_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b3_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b4_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b4_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b4_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b5_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b5_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b5_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b0_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b0_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b0_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_addrmap_row_b1_map0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_addrmap_row_b1_map0_bcm36in),
       .data_d     (reg_ddrc_addrmap_row_b1_map0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_go2critical_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_go2critical_en_port0_bcm36in),
       .data_d     (reg_arb_go2critical_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_pagematch_limit_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_pagematch_limit_port0_bcm36in),
       .data_d     (reg_arb_pagematch_limit_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rd_port_priority_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rd_port_priority_port0_bcm36in),
       .data_d     (reg_arb_rd_port_priority_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rd_port_aging_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rd_port_aging_en_port0_bcm36in),
       .data_d     (reg_arb_rd_port_aging_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rd_port_urgent_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rd_port_urgent_en_port0_bcm36in),
       .data_d     (reg_arb_rd_port_urgent_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rd_port_pagematch_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rd_port_pagematch_en_port0_bcm36in),
       .data_d     (reg_arb_rd_port_pagematch_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rrb_lock_threshold_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rrb_lock_threshold_port0_bcm36in),
       .data_d     (reg_arb_rrb_lock_threshold_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_wr_port_priority_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_wr_port_priority_port0_bcm36in),
       .data_d     (reg_arb_wr_port_priority_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_wr_port_aging_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_wr_port_aging_en_port0_bcm36in),
       .data_d     (reg_arb_wr_port_aging_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_wr_port_urgent_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_wr_port_urgent_en_port0_bcm36in),
       .data_d     (reg_arb_wr_port_urgent_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_wr_port_pagematch_en_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_wr_port_pagematch_en_port0_bcm36in),
       .data_d     (reg_arb_wr_port_pagematch_en_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_MLW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_rqos_map_level1_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_rqos_map_level1_port0_bcm36in),
       .data_d     (reg_arba0_rqos_map_level1_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_MLW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_rqos_map_level2_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_rqos_map_level2_port0_bcm36in),
       .data_d     (reg_arba0_rqos_map_level2_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_RW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_rqos_map_region0_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_rqos_map_region0_port0_bcm36in),
       .data_d     (reg_arba0_rqos_map_region0_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_RW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_rqos_map_region1_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_rqos_map_region1_port0_bcm36in),
       .data_d     (reg_arba0_rqos_map_region1_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_RW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_rqos_map_region2_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_rqos_map_region2_port0_bcm36in),
       .data_d     (reg_arba0_rqos_map_region2_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_TW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rqos_map_timeoutb_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rqos_map_timeoutb_port0_bcm36in),
       .data_d     (reg_arb_rqos_map_timeoutb_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_RQOS_TW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_rqos_map_timeoutr_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_rqos_map_timeoutr_port0_bcm36in),
       .data_d     (reg_arb_rqos_map_timeoutr_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_MLW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_wqos_map_level1_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_wqos_map_level1_port0_bcm36in),
       .data_d     (reg_arba0_wqos_map_level1_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_MLW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_wqos_map_level2_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_wqos_map_level2_port0_bcm36in),
       .data_d     (reg_arba0_wqos_map_level2_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_RW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_wqos_map_region0_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_wqos_map_region0_port0_bcm36in),
       .data_d     (reg_arba0_wqos_map_region0_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_RW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_wqos_map_region1_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_wqos_map_region1_port0_bcm36in),
       .data_d     (reg_arba0_wqos_map_region1_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_RW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arba0_wqos_map_region2_port0 (
   `ifndef SYNTHESIS
       .clk_d      (aclk_0),
       .rst_d_n    (aresetn_0),
   `endif
       .data_s     (reg_arba0_wqos_map_region2_port0_bcm36in),
       .data_d     (reg_arba0_wqos_map_region2_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_TW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_wqos_map_timeout1_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_wqos_map_timeout1_port0_bcm36in),
       .data_d     (reg_arb_wqos_map_timeout1_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (`UMCTL2_XPI_WQOS_TW),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_arb_wqos_map_timeout2_port0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_arb_wqos_map_timeout2_port0_bcm36in),
       .data_d     (reg_arb_wqos_map_timeout2_port0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_min_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_min_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ras_min_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_max_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_max_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ras_max_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_faw_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_faw_freq0_bcm36in),
       .data_d     (reg_ddrc_t_faw_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2pre_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2pre_freq0_bcm36in),
       .data_d     (reg_ddrc_wr2pre_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rc_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rc_freq0_bcm36in),
       .data_d     (reg_ddrc_t_rc_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2pre_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2pre_freq0_bcm36in),
       .data_d     (reg_ddrc_rd2pre_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xp_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xp_freq0_bcm36in),
       .data_d     (reg_ddrc_t_xp_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_write_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_write_freq0_bcm36in),
       .data_d     (reg_ddrc_t_rcd_write_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_freq0_bcm36in),
       .data_d     (reg_ddrc_wr2rd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_freq0_bcm36in),
       .data_d     (reg_ddrc_rd2wr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_read_latency_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_read_latency_freq0_bcm36in),
       .data_d     (reg_ddrc_read_latency_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_write_latency_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_write_latency_freq0_bcm36in),
       .data_d     (reg_ddrc_write_latency_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2mr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2mr_freq0_bcm36in),
       .data_d     (reg_ddrc_wr2mr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2mr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2mr_freq0_bcm36in),
       .data_d     (reg_ddrc_rd2mr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_mr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_mr_freq0_bcm36in),
       .data_d     (reg_ddrc_t_mr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rp_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rp_freq0_bcm36in),
       .data_d     (reg_ddrc_t_rp_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_freq0_bcm36in),
       .data_d     (reg_ddrc_t_rrd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ccd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_freq0_bcm36in),
       .data_d     (reg_ddrc_t_rcd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ckcsx_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ckcsx_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ckcsx_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_s_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_s_freq0_bcm36in),
       .data_d     (reg_ddrc_wr2rd_s_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_s_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_s_freq0_bcm36in),
       .data_d     (reg_ddrc_t_rrd_s_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_s_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_s_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ccd_s_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_cmdcke_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_cmdcke_freq0_bcm36in),
       .data_d     (reg_ddrc_t_cmdcke_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ppd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ppd_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ppd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_mw_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_mw_freq0_bcm36in),
       .data_d     (reg_ddrc_t_ccd_mw_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_odtloff_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_odtloff_freq0_bcm36in),
       .data_d     (reg_ddrc_odtloff_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xsr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xsr_freq0_bcm36in),
       .data_d     (reg_ddrc_t_xsr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_osco_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_osco_freq0_bcm36in),
       .data_d     (reg_ddrc_t_osco_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_disable_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_disable_freq0_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_disable_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_enable_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_enable_freq0_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_enable_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_wr_sync_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_wr_sync_freq0_bcm36in),
       .data_d     (reg_ddrc_max_wr_sync_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_rd_sync_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_rd_sync_freq0_bcm36in),
       .data_d     (reg_ddrc_max_rd_sync_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_s_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_s_freq0_bcm36in),
       .data_d     (reg_ddrc_rd2wr_s_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (2),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_bank_org_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_bank_org_freq0_bcm36in),
       .data_d     (reg_ddrc_bank_org_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rda2pre_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rda2pre_freq0_bcm36in),
       .data_d     (reg_ddrc_rda2pre_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wra2pre_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wra2pre_freq0_bcm36in),
       .data_d     (reg_ddrc_wra2pre_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0_bcm36in),
       .data_d     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_emr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_emr_freq0_bcm36in),
       .data_d     (reg_ddrc_emr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr_freq0_bcm36in),
       .data_d     (reg_ddrc_mr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr5_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr5_freq0_bcm36in),
       .data_d     (reg_ddrc_mr5_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_freq0_bcm36in),
       .data_d     (reg_ddrc_mr4_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr6_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr6_freq0_bcm36in),
       .data_d     (reg_ddrc_mr6_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr22_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr22_freq0_bcm36in),
       .data_d     (reg_ddrc_mr22_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_wrcslat_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_wrcslat_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_wrcslat_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_rdcslat_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_rdcslat_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_rdcslat_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_delay_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_delay_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_delay_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_dis_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_dis_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_dis_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_fs_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_fs_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_fs_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_wr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_wr_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_wr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_rd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_rd_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_rd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_cs_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_cs_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_cs_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_fast_toggle_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_fast_toggle_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_fast_toggle_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_en_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (20),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_short_interval_x1024_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_short_interval_x1024_freq0_bcm36in),
       .data_d     (reg_ddrc_t_zq_short_interval_x1024_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_reset_nop_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_reset_nop_freq0_bcm36in),
       .data_d     (reg_ddrc_t_zq_reset_nop_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (32),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_read_interval_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_read_interval_freq0_bcm36in),
       .data_d     (reg_ddrc_mr4_read_interval_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hw_lp_idle_x32_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hw_lp_idle_x32_freq0_bcm36in),
       .data_d     (reg_ddrc_hw_lp_idle_x32_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dvfsq_enable_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dvfsq_enable_freq0_bcm36in),
       .data_d     (reg_ddrc_dvfsq_enable_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_pageclose_timer_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_pageclose_timer_freq0_bcm36in),
       .data_d     (reg_ddrc_pageclose_timer_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rdwr_idle_gap_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rdwr_idle_gap_freq0_bcm36in),
       .data_d     (reg_ddrc_rdwr_idle_gap_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_max_starve_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_max_starve_freq0_bcm36in),
       .data_d     (reg_ddrc_hpr_max_starve_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_xact_run_length_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_xact_run_length_freq0_bcm36in),
       .data_d     (reg_ddrc_hpr_xact_run_length_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_max_starve_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_max_starve_freq0_bcm36in),
       .data_d     (reg_ddrc_lpr_max_starve_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_xact_run_length_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_xact_run_length_freq0_bcm36in),
       .data_d     (reg_ddrc_lpr_xact_run_length_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_max_starve_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_max_starve_freq0_bcm36in),
       .data_d     (reg_ddrc_w_max_starve_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_xact_run_length_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_xact_run_length_freq0_bcm36in),
       .data_d     (reg_ddrc_w_xact_run_length_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_rd_gap_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_rd_gap_freq0_bcm36in),
       .data_d     (reg_ddrc_diff_rank_rd_gap_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_wr_gap_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_wr_gap_freq0_bcm36in),
       .data_d     (reg_ddrc_diff_rank_wr_gap_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_dr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_dr_freq0_bcm36in),
       .data_d     (reg_ddrc_wr2rd_dr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_dr_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_dr_freq0_bcm36in),
       .data_d     (reg_ddrc_rd2wr_dr_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_powerdown_to_x32_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_powerdown_to_x32_freq0_bcm36in),
       .data_d     (reg_ddrc_powerdown_to_x32_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_selfref_to_x32_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_selfref_to_x32_freq0_bcm36in),
       .data_d     (reg_ddrc_selfref_to_x32_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (22),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_x1024_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_x1024_freq0_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_x1024_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_sel_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_sel_freq0_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_sel_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgmpst_x32_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgmpst_x32_freq0_bcm36in),
       .data_d     (reg_ddrc_t_pgmpst_x32_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_exit_freq0 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_exit_freq0_bcm36in),
       .data_d     (reg_ddrc_t_pgm_exit_freq0)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_min_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_min_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ras_min_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_max_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_max_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ras_max_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_faw_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_faw_freq1_bcm36in),
       .data_d     (reg_ddrc_t_faw_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2pre_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2pre_freq1_bcm36in),
       .data_d     (reg_ddrc_wr2pre_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rc_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rc_freq1_bcm36in),
       .data_d     (reg_ddrc_t_rc_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2pre_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2pre_freq1_bcm36in),
       .data_d     (reg_ddrc_rd2pre_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xp_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xp_freq1_bcm36in),
       .data_d     (reg_ddrc_t_xp_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_write_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_write_freq1_bcm36in),
       .data_d     (reg_ddrc_t_rcd_write_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_freq1_bcm36in),
       .data_d     (reg_ddrc_wr2rd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_freq1_bcm36in),
       .data_d     (reg_ddrc_rd2wr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_read_latency_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_read_latency_freq1_bcm36in),
       .data_d     (reg_ddrc_read_latency_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_write_latency_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_write_latency_freq1_bcm36in),
       .data_d     (reg_ddrc_write_latency_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2mr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2mr_freq1_bcm36in),
       .data_d     (reg_ddrc_wr2mr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2mr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2mr_freq1_bcm36in),
       .data_d     (reg_ddrc_rd2mr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_mr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_mr_freq1_bcm36in),
       .data_d     (reg_ddrc_t_mr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rp_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rp_freq1_bcm36in),
       .data_d     (reg_ddrc_t_rp_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_freq1_bcm36in),
       .data_d     (reg_ddrc_t_rrd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ccd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_freq1_bcm36in),
       .data_d     (reg_ddrc_t_rcd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ckcsx_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ckcsx_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ckcsx_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_s_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_s_freq1_bcm36in),
       .data_d     (reg_ddrc_wr2rd_s_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_s_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_s_freq1_bcm36in),
       .data_d     (reg_ddrc_t_rrd_s_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_s_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_s_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ccd_s_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_cmdcke_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_cmdcke_freq1_bcm36in),
       .data_d     (reg_ddrc_t_cmdcke_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ppd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ppd_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ppd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_mw_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_mw_freq1_bcm36in),
       .data_d     (reg_ddrc_t_ccd_mw_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_odtloff_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_odtloff_freq1_bcm36in),
       .data_d     (reg_ddrc_odtloff_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xsr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xsr_freq1_bcm36in),
       .data_d     (reg_ddrc_t_xsr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_osco_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_osco_freq1_bcm36in),
       .data_d     (reg_ddrc_t_osco_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_disable_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_disable_freq1_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_disable_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_enable_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_enable_freq1_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_enable_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_wr_sync_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_wr_sync_freq1_bcm36in),
       .data_d     (reg_ddrc_max_wr_sync_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_rd_sync_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_rd_sync_freq1_bcm36in),
       .data_d     (reg_ddrc_max_rd_sync_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_s_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_s_freq1_bcm36in),
       .data_d     (reg_ddrc_rd2wr_s_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (2),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_bank_org_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_bank_org_freq1_bcm36in),
       .data_d     (reg_ddrc_bank_org_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rda2pre_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rda2pre_freq1_bcm36in),
       .data_d     (reg_ddrc_rda2pre_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wra2pre_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wra2pre_freq1_bcm36in),
       .data_d     (reg_ddrc_wra2pre_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1_bcm36in),
       .data_d     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_emr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_emr_freq1_bcm36in),
       .data_d     (reg_ddrc_emr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr_freq1_bcm36in),
       .data_d     (reg_ddrc_mr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr5_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr5_freq1_bcm36in),
       .data_d     (reg_ddrc_mr5_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_freq1_bcm36in),
       .data_d     (reg_ddrc_mr4_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr6_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr6_freq1_bcm36in),
       .data_d     (reg_ddrc_mr6_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr22_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr22_freq1_bcm36in),
       .data_d     (reg_ddrc_mr22_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_wrcslat_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_wrcslat_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_wrcslat_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_rdcslat_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_rdcslat_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_rdcslat_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_delay_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_delay_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_delay_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_dis_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_dis_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_dis_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_fs_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_fs_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_fs_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_wr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_wr_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_wr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_rd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_rd_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_rd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_cs_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_cs_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_cs_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_fast_toggle_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_fast_toggle_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_fast_toggle_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_en_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (20),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_short_interval_x1024_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_short_interval_x1024_freq1_bcm36in),
       .data_d     (reg_ddrc_t_zq_short_interval_x1024_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_reset_nop_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_reset_nop_freq1_bcm36in),
       .data_d     (reg_ddrc_t_zq_reset_nop_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (32),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_read_interval_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_read_interval_freq1_bcm36in),
       .data_d     (reg_ddrc_mr4_read_interval_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hw_lp_idle_x32_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hw_lp_idle_x32_freq1_bcm36in),
       .data_d     (reg_ddrc_hw_lp_idle_x32_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dvfsq_enable_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dvfsq_enable_freq1_bcm36in),
       .data_d     (reg_ddrc_dvfsq_enable_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_pageclose_timer_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_pageclose_timer_freq1_bcm36in),
       .data_d     (reg_ddrc_pageclose_timer_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rdwr_idle_gap_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rdwr_idle_gap_freq1_bcm36in),
       .data_d     (reg_ddrc_rdwr_idle_gap_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_max_starve_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_max_starve_freq1_bcm36in),
       .data_d     (reg_ddrc_hpr_max_starve_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_xact_run_length_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_xact_run_length_freq1_bcm36in),
       .data_d     (reg_ddrc_hpr_xact_run_length_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_max_starve_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_max_starve_freq1_bcm36in),
       .data_d     (reg_ddrc_lpr_max_starve_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_xact_run_length_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_xact_run_length_freq1_bcm36in),
       .data_d     (reg_ddrc_lpr_xact_run_length_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_max_starve_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_max_starve_freq1_bcm36in),
       .data_d     (reg_ddrc_w_max_starve_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_xact_run_length_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_xact_run_length_freq1_bcm36in),
       .data_d     (reg_ddrc_w_xact_run_length_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_rd_gap_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_rd_gap_freq1_bcm36in),
       .data_d     (reg_ddrc_diff_rank_rd_gap_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_wr_gap_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_wr_gap_freq1_bcm36in),
       .data_d     (reg_ddrc_diff_rank_wr_gap_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_dr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_dr_freq1_bcm36in),
       .data_d     (reg_ddrc_wr2rd_dr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_dr_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_dr_freq1_bcm36in),
       .data_d     (reg_ddrc_rd2wr_dr_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_powerdown_to_x32_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_powerdown_to_x32_freq1_bcm36in),
       .data_d     (reg_ddrc_powerdown_to_x32_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_selfref_to_x32_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_selfref_to_x32_freq1_bcm36in),
       .data_d     (reg_ddrc_selfref_to_x32_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (22),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_x1024_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_x1024_freq1_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_x1024_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_sel_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_sel_freq1_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_sel_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgmpst_x32_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgmpst_x32_freq1_bcm36in),
       .data_d     (reg_ddrc_t_pgmpst_x32_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_exit_freq1 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_exit_freq1_bcm36in),
       .data_d     (reg_ddrc_t_pgm_exit_freq1)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_min_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_min_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ras_min_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_max_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_max_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ras_max_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_faw_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_faw_freq2_bcm36in),
       .data_d     (reg_ddrc_t_faw_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2pre_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2pre_freq2_bcm36in),
       .data_d     (reg_ddrc_wr2pre_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rc_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rc_freq2_bcm36in),
       .data_d     (reg_ddrc_t_rc_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2pre_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2pre_freq2_bcm36in),
       .data_d     (reg_ddrc_rd2pre_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xp_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xp_freq2_bcm36in),
       .data_d     (reg_ddrc_t_xp_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_write_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_write_freq2_bcm36in),
       .data_d     (reg_ddrc_t_rcd_write_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_freq2_bcm36in),
       .data_d     (reg_ddrc_wr2rd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_freq2_bcm36in),
       .data_d     (reg_ddrc_rd2wr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_read_latency_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_read_latency_freq2_bcm36in),
       .data_d     (reg_ddrc_read_latency_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_write_latency_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_write_latency_freq2_bcm36in),
       .data_d     (reg_ddrc_write_latency_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2mr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2mr_freq2_bcm36in),
       .data_d     (reg_ddrc_wr2mr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2mr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2mr_freq2_bcm36in),
       .data_d     (reg_ddrc_rd2mr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_mr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_mr_freq2_bcm36in),
       .data_d     (reg_ddrc_t_mr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rp_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rp_freq2_bcm36in),
       .data_d     (reg_ddrc_t_rp_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_freq2_bcm36in),
       .data_d     (reg_ddrc_t_rrd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ccd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_freq2_bcm36in),
       .data_d     (reg_ddrc_t_rcd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ckcsx_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ckcsx_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ckcsx_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_s_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_s_freq2_bcm36in),
       .data_d     (reg_ddrc_wr2rd_s_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_s_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_s_freq2_bcm36in),
       .data_d     (reg_ddrc_t_rrd_s_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_s_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_s_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ccd_s_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_cmdcke_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_cmdcke_freq2_bcm36in),
       .data_d     (reg_ddrc_t_cmdcke_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ppd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ppd_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ppd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_mw_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_mw_freq2_bcm36in),
       .data_d     (reg_ddrc_t_ccd_mw_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_odtloff_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_odtloff_freq2_bcm36in),
       .data_d     (reg_ddrc_odtloff_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xsr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xsr_freq2_bcm36in),
       .data_d     (reg_ddrc_t_xsr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_osco_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_osco_freq2_bcm36in),
       .data_d     (reg_ddrc_t_osco_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_disable_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_disable_freq2_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_disable_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_enable_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_enable_freq2_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_enable_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_wr_sync_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_wr_sync_freq2_bcm36in),
       .data_d     (reg_ddrc_max_wr_sync_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_rd_sync_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_rd_sync_freq2_bcm36in),
       .data_d     (reg_ddrc_max_rd_sync_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_s_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_s_freq2_bcm36in),
       .data_d     (reg_ddrc_rd2wr_s_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (2),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_bank_org_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_bank_org_freq2_bcm36in),
       .data_d     (reg_ddrc_bank_org_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rda2pre_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rda2pre_freq2_bcm36in),
       .data_d     (reg_ddrc_rda2pre_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wra2pre_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wra2pre_freq2_bcm36in),
       .data_d     (reg_ddrc_wra2pre_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2_bcm36in),
       .data_d     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_emr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_emr_freq2_bcm36in),
       .data_d     (reg_ddrc_emr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr_freq2_bcm36in),
       .data_d     (reg_ddrc_mr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr5_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr5_freq2_bcm36in),
       .data_d     (reg_ddrc_mr5_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_freq2_bcm36in),
       .data_d     (reg_ddrc_mr4_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr6_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr6_freq2_bcm36in),
       .data_d     (reg_ddrc_mr6_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr22_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr22_freq2_bcm36in),
       .data_d     (reg_ddrc_mr22_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_wrcslat_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_wrcslat_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_wrcslat_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_rdcslat_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_rdcslat_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_rdcslat_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_delay_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_delay_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_delay_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_dis_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_dis_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_dis_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_fs_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_fs_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_fs_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_wr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_wr_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_wr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_rd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_rd_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_rd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_cs_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_cs_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_cs_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_fast_toggle_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_fast_toggle_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_fast_toggle_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_en_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (20),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_short_interval_x1024_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_short_interval_x1024_freq2_bcm36in),
       .data_d     (reg_ddrc_t_zq_short_interval_x1024_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_reset_nop_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_reset_nop_freq2_bcm36in),
       .data_d     (reg_ddrc_t_zq_reset_nop_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (32),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_read_interval_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_read_interval_freq2_bcm36in),
       .data_d     (reg_ddrc_mr4_read_interval_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hw_lp_idle_x32_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hw_lp_idle_x32_freq2_bcm36in),
       .data_d     (reg_ddrc_hw_lp_idle_x32_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dvfsq_enable_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dvfsq_enable_freq2_bcm36in),
       .data_d     (reg_ddrc_dvfsq_enable_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_pageclose_timer_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_pageclose_timer_freq2_bcm36in),
       .data_d     (reg_ddrc_pageclose_timer_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rdwr_idle_gap_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rdwr_idle_gap_freq2_bcm36in),
       .data_d     (reg_ddrc_rdwr_idle_gap_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_max_starve_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_max_starve_freq2_bcm36in),
       .data_d     (reg_ddrc_hpr_max_starve_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_xact_run_length_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_xact_run_length_freq2_bcm36in),
       .data_d     (reg_ddrc_hpr_xact_run_length_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_max_starve_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_max_starve_freq2_bcm36in),
       .data_d     (reg_ddrc_lpr_max_starve_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_xact_run_length_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_xact_run_length_freq2_bcm36in),
       .data_d     (reg_ddrc_lpr_xact_run_length_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_max_starve_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_max_starve_freq2_bcm36in),
       .data_d     (reg_ddrc_w_max_starve_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_xact_run_length_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_xact_run_length_freq2_bcm36in),
       .data_d     (reg_ddrc_w_xact_run_length_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_rd_gap_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_rd_gap_freq2_bcm36in),
       .data_d     (reg_ddrc_diff_rank_rd_gap_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_wr_gap_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_wr_gap_freq2_bcm36in),
       .data_d     (reg_ddrc_diff_rank_wr_gap_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_dr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_dr_freq2_bcm36in),
       .data_d     (reg_ddrc_wr2rd_dr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_dr_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_dr_freq2_bcm36in),
       .data_d     (reg_ddrc_rd2wr_dr_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_powerdown_to_x32_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_powerdown_to_x32_freq2_bcm36in),
       .data_d     (reg_ddrc_powerdown_to_x32_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_selfref_to_x32_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_selfref_to_x32_freq2_bcm36in),
       .data_d     (reg_ddrc_selfref_to_x32_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (22),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_x1024_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_x1024_freq2_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_x1024_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_sel_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_sel_freq2_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_sel_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgmpst_x32_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgmpst_x32_freq2_bcm36in),
       .data_d     (reg_ddrc_t_pgmpst_x32_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_exit_freq2 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_exit_freq2_bcm36in),
       .data_d     (reg_ddrc_t_pgm_exit_freq2)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_min_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_min_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ras_min_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ras_max_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ras_max_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ras_max_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_faw_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_faw_freq3_bcm36in),
       .data_d     (reg_ddrc_t_faw_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2pre_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2pre_freq3_bcm36in),
       .data_d     (reg_ddrc_wr2pre_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rc_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rc_freq3_bcm36in),
       .data_d     (reg_ddrc_t_rc_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2pre_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2pre_freq3_bcm36in),
       .data_d     (reg_ddrc_rd2pre_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xp_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xp_freq3_bcm36in),
       .data_d     (reg_ddrc_t_xp_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_write_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_write_freq3_bcm36in),
       .data_d     (reg_ddrc_t_rcd_write_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_freq3_bcm36in),
       .data_d     (reg_ddrc_wr2rd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_freq3_bcm36in),
       .data_d     (reg_ddrc_rd2wr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_read_latency_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_read_latency_freq3_bcm36in),
       .data_d     (reg_ddrc_read_latency_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_write_latency_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_write_latency_freq3_bcm36in),
       .data_d     (reg_ddrc_write_latency_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2mr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2mr_freq3_bcm36in),
       .data_d     (reg_ddrc_wr2mr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2mr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2mr_freq3_bcm36in),
       .data_d     (reg_ddrc_rd2mr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_mr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_mr_freq3_bcm36in),
       .data_d     (reg_ddrc_t_mr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rp_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rp_freq3_bcm36in),
       .data_d     (reg_ddrc_t_rp_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_freq3_bcm36in),
       .data_d     (reg_ddrc_t_rrd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ccd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rcd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rcd_freq3_bcm36in),
       .data_d     (reg_ddrc_t_rcd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ckcsx_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ckcsx_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ckcsx_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_s_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_s_freq3_bcm36in),
       .data_d     (reg_ddrc_wr2rd_s_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_rrd_s_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_rrd_s_freq3_bcm36in),
       .data_d     (reg_ddrc_t_rrd_s_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (5),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_s_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_s_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ccd_s_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_cmdcke_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_cmdcke_freq3_bcm36in),
       .data_d     (reg_ddrc_t_cmdcke_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (4),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ppd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ppd_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ppd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_ccd_mw_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_ccd_mw_freq3_bcm36in),
       .data_d     (reg_ddrc_t_ccd_mw_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_odtloff_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_odtloff_freq3_bcm36in),
       .data_d     (reg_ddrc_odtloff_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_xsr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_xsr_freq3_bcm36in),
       .data_d     (reg_ddrc_t_xsr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_osco_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_osco_freq3_bcm36in),
       .data_d     (reg_ddrc_t_osco_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_disable_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_disable_freq3_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_disable_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_vrcg_enable_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_vrcg_enable_freq3_bcm36in),
       .data_d     (reg_ddrc_t_vrcg_enable_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_wr_sync_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_wr_sync_freq3_bcm36in),
       .data_d     (reg_ddrc_max_wr_sync_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_max_rd_sync_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_max_rd_sync_freq3_bcm36in),
       .data_d     (reg_ddrc_max_rd_sync_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_s_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_s_freq3_bcm36in),
       .data_d     (reg_ddrc_rd2wr_s_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (2),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_bank_org_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_bank_org_freq3_bcm36in),
       .data_d     (reg_ddrc_bank_org_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rda2pre_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rda2pre_freq3_bcm36in),
       .data_d     (reg_ddrc_rda2pre_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wra2pre_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wra2pre_freq3_bcm36in),
       .data_d     (reg_ddrc_wra2pre_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (3),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3_bcm36in),
       .data_d     (reg_ddrc_lpddr4_diff_bank_rwa2pre_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_emr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_emr_freq3_bcm36in),
       .data_d     (reg_ddrc_emr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr_freq3_bcm36in),
       .data_d     (reg_ddrc_mr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr5_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr5_freq3_bcm36in),
       .data_d     (reg_ddrc_mr5_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_freq3_bcm36in),
       .data_d     (reg_ddrc_mr4_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr6_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr6_freq3_bcm36in),
       .data_d     (reg_ddrc_mr6_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr22_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr22_freq3_bcm36in),
       .data_d     (reg_ddrc_mr22_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_wrcslat_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_wrcslat_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_wrcslat_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_tphy_rdcslat_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_tphy_rdcslat_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_tphy_rdcslat_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_delay_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_delay_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_delay_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_dis_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_dis_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_dis_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_fs_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_fs_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_fs_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_wr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_wr_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_wr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_en_rd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_en_rd_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_en_rd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_cs_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_cs_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_cs_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_fast_toggle_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_fast_toggle_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_fast_toggle_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_twck_toggle_post_rd_en_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_twck_toggle_post_rd_en_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (9),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3_bcm36in),
       .data_d     (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (20),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_short_interval_x1024_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_short_interval_x1024_freq3_bcm36in),
       .data_d     (reg_ddrc_t_zq_short_interval_x1024_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_zq_reset_nop_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_zq_reset_nop_freq3_bcm36in),
       .data_d     (reg_ddrc_t_zq_reset_nop_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (32),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_mr4_read_interval_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_mr4_read_interval_freq3_bcm36in),
       .data_d     (reg_ddrc_mr4_read_interval_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (12),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hw_lp_idle_x32_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hw_lp_idle_x32_freq3_bcm36in),
       .data_d     (reg_ddrc_hw_lp_idle_x32_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_dvfsq_enable_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_dvfsq_enable_freq3_bcm36in),
       .data_d     (reg_ddrc_dvfsq_enable_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_pageclose_timer_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_pageclose_timer_freq3_bcm36in),
       .data_d     (reg_ddrc_pageclose_timer_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rdwr_idle_gap_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rdwr_idle_gap_freq3_bcm36in),
       .data_d     (reg_ddrc_rdwr_idle_gap_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_max_starve_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_max_starve_freq3_bcm36in),
       .data_d     (reg_ddrc_hpr_max_starve_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_hpr_xact_run_length_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_hpr_xact_run_length_freq3_bcm36in),
       .data_d     (reg_ddrc_hpr_xact_run_length_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_max_starve_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_max_starve_freq3_bcm36in),
       .data_d     (reg_ddrc_lpr_max_starve_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_lpr_xact_run_length_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_lpr_xact_run_length_freq3_bcm36in),
       .data_d     (reg_ddrc_lpr_xact_run_length_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_max_starve_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_max_starve_freq3_bcm36in),
       .data_d     (reg_ddrc_w_max_starve_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_w_xact_run_length_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_w_xact_run_length_freq3_bcm36in),
       .data_d     (reg_ddrc_w_xact_run_length_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_rd_gap_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_rd_gap_freq3_bcm36in),
       .data_d     (reg_ddrc_diff_rank_rd_gap_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_diff_rank_wr_gap_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_diff_rank_wr_gap_freq3_bcm36in),
       .data_d     (reg_ddrc_diff_rank_wr_gap_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_wr2rd_dr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_wr2rd_dr_freq3_bcm36in),
       .data_d     (reg_ddrc_wr2rd_dr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (8),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_rd2wr_dr_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_rd2wr_dr_freq3_bcm36in),
       .data_d     (reg_ddrc_rd2wr_dr_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (7),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_powerdown_to_x32_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_powerdown_to_x32_freq3_bcm36in),
       .data_d     (reg_ddrc_powerdown_to_x32_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (10),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_selfref_to_x32_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_selfref_to_x32_freq3_bcm36in),
       .data_d     (reg_ddrc_selfref_to_x32_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (22),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_x1024_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_x1024_freq3_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_x1024_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (1),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_x1_sel_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_x1_sel_freq3_bcm36in),
       .data_d     (reg_ddrc_t_pgm_x1_sel_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (16),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgmpst_x32_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgmpst_x32_freq3_bcm36in),
       .data_d     (reg_ddrc_t_pgmpst_x32_freq3)
       );
   DWC_ddr_umctl2_bcmwrp36_nhs_inject_x
   
     #(.WIDTH      (6),
       .DATA_DELAY (`UMCTL2_BCM36_NHS_DELAY),
       .INJECT_X   (`UMCTL2_BCM36_NHS_INJECT_X))
   U_bcm36_nhs_inject_x_reg_ddrc_t_pgm_exit_freq3 (
   `ifndef SYNTHESIS
       .clk_d      (core_ddrc_core_clk),
       .rst_d_n    (core_ddrc_rstn),
   `endif
       .data_s     (reg_ddrc_t_pgm_exit_freq3_bcm36in),
       .data_d     (reg_ddrc_t_pgm_exit_freq3)
       );











//-------------------------------------------------

  always @(posedge pclk or negedge presetn) begin: ecc_ap_err_force
     if (~presetn) begin
        pclk_ddrc_reg_ecc_ap_err_force <= 1'b0;
     end
     else begin
        if (reg_ddrc_ecc_ap_err_intr_clr_ack_pclk) pclk_ddrc_reg_ecc_ap_err_force <= 1'b0;
        else if (reg_ddrc_ecc_ap_err_intr_force_ack_pclk) pclk_ddrc_reg_ecc_ap_err_force <= 1'b1;
     end
  end

  assign ddrc_reg_ecc_ap_err_stat = pclk_ddrc_reg_ecc_ap_err_force | pclk_ddrc_reg_ecc_ap_err;
  DWC_ddrctl_antivalent_reg
   U_ecc_ap_err_intr_fault (
     .clk                       (pclk)
    ,.rstn                      (presetn)
    ,.fault_intr                (pclk_ddrc_reg_ecc_ap_err)
    ,.intr                      (pclk_ddrc_reg_ecc_ap_err_force | pclk_ddrc_reg_ecc_ap_err)
    ,.intr_en                   (ecc_ap_err_intr_en)
    ,.antivalent_fault_intr_out (ecc_ap_err_intr_fault)
    ,.intr_out                  (ecc_ap_err_intr)
  );


  always @(posedge pclk or negedge presetn) begin: pclk_ddrc_reg_ecc_corrected_err_force_PROC
     if (~presetn) begin
        pclk_ddrc_reg_ecc_corrected_err_force <= 1'b0;
     end
     else begin
        if (reg_ddrc_ecc_corrected_err_clr_ack_pclk) pclk_ddrc_reg_ecc_corrected_err_force <= 1'b0;
        else if (reg_ddrc_ecc_corrected_err_intr_force_ack_pclk) pclk_ddrc_reg_ecc_corrected_err_force <= 1'b1;
     end
  end    
  always @(posedge pclk or negedge presetn) begin: pclk_ddrc_reg_ecc_uncorrected_err_force_PROC
     if (~presetn) begin
        pclk_ddrc_reg_ecc_uncorrected_err_force <= 1'b0;
     end
     else begin
        if (reg_ddrc_ecc_uncorrected_err_clr_ack_pclk) pclk_ddrc_reg_ecc_uncorrected_err_force <= 1'b0;
        else if (reg_ddrc_ecc_uncorrected_err_intr_force_ack_pclk) pclk_ddrc_reg_ecc_uncorrected_err_force <= 1'b1;
     end
  end  
     assign ddrc_reg_ecc_corrected_err_stat      = pclk_ddrc_reg_ecc_corrected_err | {ECC_CORRECTED_ERR_WIDTH{pclk_ddrc_reg_ecc_corrected_err_force}};
     assign ecc_corrected_err_int                = |ddrc_reg_ecc_corrected_err_stat;// & ecc_corrected_err_intr_en;
     assign ecc_corrected_err_fault_int          = |pclk_ddrc_reg_ecc_corrected_err;
   assign ddrc_reg_ecc_uncorrected_err_stat    = pclk_ddrc_reg_ecc_uncorrected_err | {ECC_UNCORRECTED_ERR_WIDTH{pclk_ddrc_reg_ecc_uncorrected_err_force}};
   assign ecc_uncorrected_err_int              = |ddrc_reg_ecc_uncorrected_err_stat;// & ecc_uncorrected_err_intr_en;
   assign ecc_uncorrected_err_fault_int        = |pclk_ddrc_reg_ecc_uncorrected_err;   

 localparam CORR_ERR_INTR_EN_WIDTH  = 
                                    1;

  DWC_ddrctl_antivalent_reg
   #(
     .INTR_EN_WIDTH    (CORR_ERR_INTR_EN_WIDTH)
) U_ecc_corrected_err_intr_fault
(
     .clk                       (pclk)
    ,.rstn                      (presetn)
    ,.fault_intr                (ecc_corrected_err_fault_int)
    ,.intr                      (ecc_corrected_err_int)
    ,.intr_en                   (ecc_corrected_err_intr_en)
    ,.antivalent_fault_intr_out (ecc_corrected_err_intr_fault)
    ,.intr_out                  (ecc_corrected_err_intr)
  );
  DWC_ddrctl_antivalent_reg
   U_ecc_uncorrected_err_intr_fault(
     .clk                       (pclk)
    ,.rstn                      (presetn)
    ,.fault_intr                (ecc_uncorrected_err_fault_int)
    ,.intr                      (ecc_uncorrected_err_int)
    ,.intr_en                   (ecc_uncorrected_err_intr_en)
    ,.antivalent_fault_intr_out (ecc_uncorrected_err_intr_fault)
    ,.intr_out                  (ecc_uncorrected_err_intr)
  );  


  always @(posedge pclk or negedge presetn) begin: pclk_ddrc_reg_rd_link_ecc_corr_err_force_PROC
     if (~presetn) begin
        pclk_ddrc_reg_rd_link_ecc_corr_err_force <= 1'b0;
     end
     else begin
        if (reg_ddrc_rd_link_ecc_corr_intr_clr_ack_pclk) pclk_ddrc_reg_rd_link_ecc_corr_err_force <= 1'b0;
        else if (reg_ddrc_rd_link_ecc_corr_intr_force_ack_pclk) pclk_ddrc_reg_rd_link_ecc_corr_err_force <= 1'b1;
     end
  end

  assign ddrc_reg_rd_link_ecc_corr_err_stat   = pclk_ddrc_reg_rd_linkecc_corr_err_int |
                                                       {2'b00 ,{2{pclk_ddrc_reg_rd_link_ecc_corr_err_force}}};
  assign rd_link_kecc_corr_err_int            = |ddrc_reg_rd_link_ecc_corr_err_stat;
  assign rd_link_kecc_corr_err_int_fault      = |pclk_ddrc_reg_rd_linkecc_corr_err_int;

  DWC_ddrctl_antivalent_reg
   U_rd_link_ecc_corr_err_intr_fault(
     .clk                       (pclk)
    ,.rstn                      (presetn)
    ,.fault_intr                (rd_link_kecc_corr_err_int_fault)
    ,.intr                      (rd_link_kecc_corr_err_int)
    ,.intr_en                   (rd_link_ecc_corr_intr_en)
    ,.antivalent_fault_intr_out (rd_linkecc_corr_err_intr_fault)
    ,.intr_out                  (rd_linkecc_corr_err_intr)
  );


  always @(posedge pclk or negedge presetn) begin: pclk_ddrc_reg_rd_link_ecc_uncorr_err_force_PROC
     if (~presetn) begin
        pclk_ddrc_reg_rd_link_ecc_uncorr_err_force <= 1'b0;
     end
     else begin
        if (reg_ddrc_rd_link_ecc_uncorr_intr_clr_ack_pclk) pclk_ddrc_reg_rd_link_ecc_uncorr_err_force <= 1'b0;
        else if (reg_ddrc_rd_link_ecc_uncorr_intr_force_ack_pclk) pclk_ddrc_reg_rd_link_ecc_uncorr_err_force <= 1'b1;
     end
  end

  assign ddrc_reg_rd_link_ecc_uncorr_err_stat   = pclk_ddrc_reg_rd_linkecc_uncorr_err_int |
                                                       {2'b00 ,{2{pclk_ddrc_reg_rd_link_ecc_uncorr_err_force}}};
  assign rd_link_kecc_uncorr_err_int            = |ddrc_reg_rd_link_ecc_uncorr_err_stat;
  assign rd_link_kecc_uncorr_err_int_fault      = |pclk_ddrc_reg_rd_linkecc_uncorr_err_int;

  DWC_ddrctl_antivalent_reg
   U_rd_link_ecc_uncorr_err_intr_fault(
     .clk                       (pclk)
    ,.rstn                      (presetn)
    ,.fault_intr                (rd_link_kecc_uncorr_err_int_fault)
    ,.intr                      (rd_link_kecc_uncorr_err_int)
    ,.intr_en                   (rd_link_ecc_uncorr_intr_en)
    ,.antivalent_fault_intr_out (rd_linkecc_uncorr_err_intr_fault)
    ,.intr_out                  (rd_linkecc_uncorr_err_intr)
  );

endmodule // DWC_ddrctl_apb_slvtop
