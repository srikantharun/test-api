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

// -------------------------------------------------------------------------
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs.sv#16 $
// -------------------------------------------------------------------------
// Description:
//
// Global Scheduler unit.  This block is responsible for choosing from
// among the available transactions to perform to DRAM, except for
// the bypass path (which this block also has the ability to disable).
// The global scheduler also schedules the init sequence, self-refresh
// entry and exit and powerdown entry and exit.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "ts/DWC_ddrctl_ts_if.svh"
module gs
import DWC_ddrctl_reg_pkg::*;
#(
  //------------------------------- PARAMETERS ----------------------------------
     parameter    CHANNEL_NUM         = 0
    ,parameter    SHARED_AC           = 0
    ,parameter    RANK_BITS           = `MEMC_RANK_BITS
    ,parameter    LRANK_BITS          = `DDRCTL_DDRC_LRANK_BITS
    ,parameter    BANK_BITS           = `MEMC_BANK_BITS
    ,parameter    BG_BITS             = `MEMC_BG_BITS
    ,parameter    BG_BANK_BITS        = `MEMC_BG_BANK_BITS
    ,parameter    BSM_BITS            = `UMCTL2_BSM_BITS
    ,parameter    NUM_TOTAL_BANKS     = `DDRCTL_DDRC_NUM_TOTAL_BANKS
    ,parameter    NUM_TOTAL_BSMS      = `UMCTL2_NUM_BSM
    ,parameter    BCM_VERIF_EN        = 1
    ,parameter    BCM_DDRC_N_SYNC     = 2
    ,parameter    NPORTS              = 1 // no. of ports (for cactive_in_ddrc width) gets overwritten by toplevel
    ,parameter    A_SYNC_TABLE        = 16'hffff
    ,parameter    NUM_LANES           = 4
    ,parameter    MRS_A_BITS          = `MEMC_PAGE_BITS
    ,parameter    MRS_BA_BITS         = `MEMC_BG_BANK_BITS
    ,parameter    RD_CAM_ENTRIES      = 1<<`MEMC_RDCMD_ENTRY_BITS
    ,parameter    WR_CAM_ENTRIES      = 1<<`MEMC_WRCMD_ENTRY_BITS

    ,parameter    FSM_STATE_WIDTH     = 5
    ,parameter    RANKBANK_BITS       = LRANK_BITS + BG_BANK_BITS
    ,parameter    NUM_RANKS           = 1 << RANK_BITS // max # of ranks supported
    ,parameter    NUM_BG_BANKS        = 1 << BG_BANK_BITS
    ,parameter    NUM_BANKS           = 1 << BANK_BITS
    ,parameter    NUM_LRANKS          = `DDRCTL_DDRC_NUM_LRANKS_TOTAL
    ,parameter    NUM_PRANKS          = `DDRCTL_DDRC_NUM_PR_CONSTRAINTS

    ,parameter    BLK_ACT_TRFC_WDT    = (`MEMC_LPDDR4_EN == 1) ? (1 << BANK_BITS) : 1
    ,parameter    BLK_ACT_TRRD_WDT    = 1 << BG_BITS
    ,parameter    BLK_ACT_TRFM_WDT    = NUM_BANKS
    ,parameter    BLK_ACT_RAAC_WDT    = (`DDRCTL_LPDDR_RFMSBC_EN == 1) ? NUM_BG_BANKS : NUM_BG_BANKS/2
    ,parameter    NUM_BG_PER_RANK     = 1 << BG_BITS
    ,parameter    NUM_TOTAL_BGS       = NUM_BG_PER_RANK * NUM_LRANKS
    ,parameter    MAX_CMD_DELAY       = `UMCTL2_MAX_CMD_DELAY
    ,parameter    CMD_DELAY_BITS      = `UMCTL2_CMD_DELAY_BITS
    ,parameter    CMD_LEN_BITS        = 1

    ,parameter    MAX_CMD_NUM         = 2

    ,parameter    SELFREF_SW_WIDTH_INT = SELFREF_SW_WIDTH
    ,parameter    SELFREF_TYPE_WIDTH_INT = SELFREF_TYPE_WIDTH
    ,parameter    SELFREF_EN_WIDTH_INT = SELFREF_EN_WIDTH
    ,parameter    POWERDOWN_EN_WIDTH_INT = POWERDOWN_EN_WIDTH
  )
  (
  //--------------------------- INPUTS AND OUTPUTS -------------------------------
     input                                              co_yy_clk                           // clock
    ,input                                              core_ddrc_rstn                      // asynchronous falling-edge reset
    ,output [NUM_RANKS-1:0]                             bsm_clk_en                          // Clock enable for bsm instances
    ,input  [BSM_CLK_ON_WIDTH-1:0]                      bsm_clk_on                          // bsm_clk always on
    ,input                                              dh_gs_2t_mode                       // 1= 2T mode, 0 = regular mode(
    ,input                                              dh_gs_frequency_ratio               // 1= 1:1 mode, 0 = 1:2 mode

    ,input  [15:0]                                      dh_gs_mr                            // mode register
    ,input  [15:0]                                      dh_gs_emr                           // extended mode register
    ,input  [15:0]                                      dh_gs_emr2                          // extended mode register 2 (ddr2 only)
    ,input  [15:0]                                      dh_gs_emr3                          // extended mode register 3 (ddr2 only)
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used under multiple `ifdefs. Decided to keep current coding style for now.
    ,input  [15:0]                                      dh_gs_mr4                           // mode register
    ,input  [15:0]                                      dh_gs_mr5                           // mode register
    ,input  [15:0]                                      dh_gs_mr6                           // mode register
    ,input  [15:0]                                      dh_gs_mr22                          // mode register
//spyglass enable_block W240

    ,input                                              phy_dfi_ctrlupd_ack1
    ,input                                              phy_dfi_init_complete               // PHY initialization complete.All DFI signals that communicate commands or status
                                                                                            // must be held at their default values until the dfi_init_complete signal asserts
    ,input                                              dh_gs_dfi_init_complete_en
    ,output                                             ddrc_dfi_ctrlupd_req
    ,output [1:0]                                       ddrc_dfi_ctrlupd_type
    ,output [1:0]                                       ddrc_dfi_ctrlupd_target
    ,input  [DFI_T_CTRLUP_MIN_WIDTH-1:0]                dh_gs_dfi_t_ctrlup_min
    ,input  [DFI_T_CTRLUP_MAX_WIDTH-1:0]                dh_gs_dfi_t_ctrlup_max
    ,output [1:0]                                       gs_dh_ctrlupd_state

    ,input  [T_MR_WIDTH-1:0]                            reg_ddrc_t_mr                       // time to wait between MRS/MRW to valid command
    ,input                                              dh_gs_sw_init_int                   // SW intervention in auto SDRAM initialization
    ,input                                              reg_ddrc_dfi_reset_n                // controls dfi_reset_n
    ,output                                             gs_pi_dram_rst_n                    // ddrc to dram active low reset
    ,input  [T_ZQ_LONG_NOP_WIDTH-1:0]                   dh_gs_t_zq_long_nop                 // time to wait in ZQCL during init sequence
    ,input  [T_ZQ_SHORT_NOP_WIDTH-1:0]                  dh_gs_t_zq_short_nop                // time to wait in ZQCS during init sequence
    ,input  [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0]       dh_gs_t_zq_short_interval_x1024     // time interval between auto_zqcs
    ,input                                              dh_gs_zq_calib_short                // zq calib short command
    ,output                                             gs_dh_zq_calib_short_busy           // if 1: Previous zq calib short has not been initiated
    ,input                                              dh_gs_dis_auto_zq
    ,input                                              dh_gs_dis_srx_zqcl                  // when 1, disable zqcl after self-refresh exit
    ,input                                              dh_gs_dis_srx_zqcl_hwffc            // when 1, disable zqcl at hwffc end
    ,input                                              dh_gs_zq_resistor_shared            // when 1: ZQ resistor is shared
    ,input  [READ_LATENCY_WIDTH-1:0]                    dh_gs_read_latency                  // read latency - used to ensure MRR -> PD/SR timing
    ,input  [WRITE_LATENCY_WIDTH-1:0]                   dh_gs_write_latency                 // write latency - used to ensure MRS -> MRS timing in PDA mode
    ,input                                              dh_gs_zq_reset                      // ZQ Reset command
    ,input  [T_ZQ_RESET_NOP_WIDTH-1:0]                  dh_gs_t_zq_reset_nop                // ZQ Reset NOP period
    ,output                                             gs_dh_zq_reset_busy                 // if 1: Previous ZQ Reset is being executed
    ,input  [T_RCD_WIDTH-1:0]                           dh_gs_t_rcd
    ,input                                              dh_gs_lpddr4
    ,input                                              reg_ddrc_lpddr5
    ,input  [BANK_ORG_WIDTH-1:0]                        reg_ddrc_bank_org
    ,input  [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0]        dh_gs_lpddr4_diff_bank_rwa2pre
    ,input                                              dh_gs_stay_in_selfref
    ,input  [T_PPD_WIDTH-1:0]                           dh_gs_t_ppd                         // tPPD: PRE(A)-to-PRE(A) min delay
    ,input  [T_CMDCKE_WIDTH-1:0]                        dh_gs_t_cmdcke
    ,input                                              reg_ddrc_dsm_en
    ,input  [T_PDN_WIDTH-1:0]                           reg_ddrc_t_pdn
    ,input  [T_XSR_DSM_X1024_WIDTH-1:0]                       reg_ddrc_t_xsr_dsm_x1024
    ,input  [T_CSH_WIDTH-1:0]                           reg_ddrc_t_csh
    ,input  [ODTLOFF_WIDTH-1:0]                         dh_gs_odtloff
    ,input  [RD2MR_WIDTH-1:0]                           reg_ddrc_rd2mr
    ,input  [WR2MR_WIDTH-1:0]                           reg_ddrc_wr2mr
    ,input                                              os_te_autopre
    ,input  [WRA2PRE_WIDTH-1:0]                         reg_ddrc_wra2pre
    ,input                                              dh_gs_mr_wr                         // input from core to write mode register
    ,input  [3:0]                                       dh_gs_mr_addr                       // input from core: mode register address
                                                                                            // 0000: MR0, 0001: MR1, 0010: MR2, 0011: MR3, 0100: MR4, 0101: MR5, 0110: MR6
    ,input  [MRS_A_BITS-1:0]                            dh_gs_mr_data                       // mode register data to be written
    ,output                                             gs_dh_mr_wr_busy                    // indicates that mode register write operation is in progress

    ,input                                              dh_gs_mr_type                       // MR Type R/W.
    ,output                                             mrr_op_on                           // is high when MRR operation is being processed
    ,input                                              dh_gs_derate_enable
    ,input  [T_REFI_X1_X32_WIDTH+4:0]                          derate_gs_t_refie
    ,input  [T_REFI_X1_X32_WIDTH+4:0]                          derate_gs_t_refi
    ,input  [5:0]                                       max_postponed_ref_cmd
    ,input  [4:0]                                       max_ref_cmd_within_2trefi
    ,input                                              derate_force_refab
    ,input  [REFRESH_TO_AB_X32_WIDTH-1:0]               reg_ddrc_refresh_to_ab_x32
    ,output                                             ddrc_co_perf_lpr_xact_when_critical // lpr transaction when lpr q is critical
    ,output                                             ddrc_co_perf_hpr_xact_when_critical // hpr transaction when hpr q is critical
    ,output                                             ddrc_co_perf_wr_xact_when_critical  // wr transaction when wr q is critical
    ,output                                             ddrc_co_perf_rdwr_transitions       // pulses everytime there is a rd/wr or wr/rd transition in global_fsm


    ,input  [BURST_RDWR_WIDTH-1:0]                      dh_gs_burst_rdwr                    // 5'b00100=burst of 8 data read/write
                                                                                            // 5'b01000=burst of 16 data read/write
                                                                                            // 5'b10000=burst of 32 data read/write
    ,input  [RD2WR_WIDTH-1:0]                           dh_gs_rd2wr                         // read-to-write latency
    ,input  [WR2RD_WIDTH-1:0]                           dh_gs_wr2rd                         // write-to-read latency
    ,input  [DIFF_RANK_RD_GAP_WIDTH-1:0]                dh_gs_diff_rank_rd_gap              // cycle gap between reads to different ranks
    ,input  [DIFF_RANK_WR_GAP_WIDTH-1:0]                dh_gs_diff_rank_wr_gap              // cycle gap between writes to different ranks
    ,input  [RD2WR_DR_WIDTH-1:0]                        reg_ddrc_rd2wr_dr
    ,input  [WR2RD_DR_WIDTH-1:0]                        reg_ddrc_wr2rd_dr
    ,input  [3:0]                                       dh_gs_max_rank_rd                   // max consecutive reads to a rank before
    ,input  [3:0]                                       dh_gs_max_rank_wr                   // max consecutive writes to a rank before
    ,input  [NUM_RANKS-1:0]                             dh_gs_active_ranks                  // populated DRAM ranks
    ,input                                              dh_gs_dis_max_rank_rd_opt           // Disable max rank read optimization
    ,input                                              dh_gs_dis_max_rank_wr_opt           // Disable max rank write optimization
    ,input  [5:0]                                       dh_gs_refresh_burst                 // 0 = refresh after each nominal refresh period
                                                                                            // 1 = send 2 consecutive refreshes after 2 nominal refresh periods
                                                                                            // ...
                                                                                            // 7 = send 8 consecutive refreshes after 8 nominal refresh periods
    ,input  [T_CKE_WIDTH-1:0]                           dh_gs_t_cke                         // tCKE:    min time between CKE
                                                                                            //      assertion/de-assertion
    ,input  [T_FAW_WIDTH-1:0]                           dh_gs_t_faw                         // sliding window size in which 4 ACTs
                                                                                            //  to a rank are allowed
    ,input  [T_RFC_MIN_WIDTH-1:0]                       dh_gs_t_rfc_min                     // minimum time between refreshes
    ,input  [T_RFC_MIN_AB_WIDTH-1:0]                    dh_gs_t_rfc_min_ab
    ,input  [T_PBR2PBR_WIDTH-1:0]                       dh_gs_t_pbr2pbr                     // minimum time between LPDDR4 per-bank refresh refreshes different bank
    ,input  [T_PBR2ACT_WIDTH-1:0]                       dh_gs_t_pbr2act                     // minimum time between LPDDR5 per-bank refresh act different bank
    ,input                                              dh_gs_rfm_en
    ,input                                              dh_gs_dis_mrrw_trfc                 // disable MRR/MRW operation during tRFC
    ,input                                              dh_gs_rfmsbc
    ,input   [RAAIMT_WIDTH-1:0]                         dh_gs_raaimt
    ,input   [RAAMULT_WIDTH-1:0]                        dh_gs_raamult
    ,input   [RAADEC_WIDTH-1:0]                         dh_gs_raadec
    ,input   [RFMTH_RM_THR_WIDTH-1:0]                   dh_gs_rfmth_rm_thr
    ,input   [INIT_RAA_CNT_WIDTH-1:0]                   dh_gs_init_raa_cnt
    ,input   [T_RFMPB_WIDTH-1:0]                        dh_gs_t_rfmpb
    ,input   [DBG_RAA_RANK_WIDTH-1:0]                   dh_gs_dbg_raa_rank
    ,input   [DBG_RAA_BG_BANK_WIDTH-1:0]                dh_gs_dbg_raa_bg_bank
    ,output  [DBG_RAA_CNT_WIDTH-1:0]                    gs_dh_dbg_raa_cnt
    ,output  [NUM_RANKS-1:0]                            gs_dh_rank_raa_cnt_gt0
    ,input   [4:0]                                      derate_operating_rm
    ,input   [NUM_LRANKS*NUM_BG_BANKS-1:0]              bank_pgmiss_exvpr_valid
    ,input   [NUM_LRANKS*NUM_BG_BANKS-1:0]              bank_pgmiss_exvpw_valid
    ,output  [NUM_LRANKS-1:0]                           gs_bs_rank_rfm_required
    ,output  [NUM_LRANKS*BANK_BITS-1:0]                 gs_bs_rfmpb_bank
    ,output  [NUM_LRANKS-1:0]                           gs_bs_rfmpb_sb0
    ,output  [NUM_LRANKS*BLK_ACT_TRFM_WDT-1:0]          gs_bs_rank_block_act_trfm_bk_nxt
    ,output  [NUM_LRANKS*BLK_ACT_RAAC_WDT-1:0]          gs_bs_rank_block_act_raa_expired
    ,output                                             gs_op_is_rfm
    ,output  [NUM_RANKS-1:0]                            gs_rfm_cs_n
    ,output  [BANK_BITS-1:0]                            gs_pi_rfmpb_bank
    ,output                                             gs_pi_rfmpb_sb0
    ,input                                              dh_gs_t_refi_x1_sel              // specifies whether reg_ddrc_t_refi_x1_x32 reg is x1 or x32
    ,input                                              dh_gs_refresh_to_x1_sel          // specifies whether reg_ddrc_refresh_to_x1_x32 reg is x1 or x32
    ,input  [T_REFI_X1_X32_WIDTH-1:0]                          dh_gs_t_refi_x1_x32              // average periodic refresh interval x1/x32
    ,input  [T_RRD_WIDTH-1:0]                           dh_gs_t_rrd                         // tRRD:    ACT to ACT min (rank)
    ,input  [T_RRD_S_WIDTH-1:0]                         dh_gs_t_rrd_s                       // tRRD_S:  ACT to ACT min to different BG (rank)
    ,input  [REFRESH_TO_X1_X32_WIDTH-1:0]               dh_gs_refresh_to_x1_x32             // idle time before issuing refresh x32
    ,input  [PRE_CKE_X1024_WIDTH-1:0]                   dh_gs_pre_cke_x1024                 // cycles to wait before enabling clock
    ,input  [POST_CKE_X1024_WIDTH-1:0]                  dh_gs_post_cke_x1024                // cycles to wait after enabling clock
    ,input                                              dh_gs_prefer_write                  // flush writes
    ,input  [6:0]                                       dh_gs_rdwr_idle_gap                 // idle time before switching from reads to writes
    ,input  [POWERDOWN_EN_WIDTH_INT-1:0]                    dh_gs_powerdown_en                  // powerdown is enabled
    ,input  [POWERDOWN_TO_X32_WIDTH-1:0]                dh_gs_powerdown_to_x32              // idle timeout period b4 powerdown x32
    ,input  [T_XP_WIDTH-1:0]                            dh_gs_t_xp                          // tXP:     duration of powerdown exit

    ,input [SELFREF_SW_WIDTH_INT-1:0]                       reg_ddrc_selfref_sw
    ,input                                              reg_ddrc_hw_lp_en
    ,input                                              reg_ddrc_hw_lp_exit_idle_en
    ,input  [SELFREF_TO_X32_WIDTH-1:0]                  reg_ddrc_selfref_to_x32
    ,input  [HW_LP_IDLE_X32_WIDTH-1:0]                  reg_ddrc_hw_lp_idle_x32
    ,output [SELFREF_TYPE_WIDTH_INT-1:0]                    ddrc_reg_selfref_type
    ,input                                              ih_busy
    ,input                                              hif_cmd_valid
    ,output                                             gsfsm_sr_co_if_stall
    ,input                                              cactive_in_ddrc_sync_or
    ,input  [NPORTS-1:0]                                cactive_in_ddrc_async
    ,input                                              csysreq_ddrc
    ,input                                              csysmode_ddrc
    ,input  [4:0]                                       csysfrequency_ddrc
    ,input                                              csysdiscamdrain_ddrc
    ,input                                              csysfsp_ddrc
    ,output                                             csysack_ddrc
    ,output                                             cactive_ddrc

    ,input  [SELFREF_EN_WIDTH_INT-1:0]                  dh_gs_selfref_en                    // self refresh is enabled
    ,input  [T_XSR_WIDTH-1:0]                           dh_gs_t_xsr                         // SRX to commands (unit of 1 cycle)
    ,input  [NUM_RANKS-1:0]                             dh_gs_mr_rank                       // Software configurable rank input
    ,input  [REFRESH_MARGIN_WIDTH-1:0]                  dh_gs_refresh_margin                // # cycles (x32) early to start attempting refresh
    ,input  [NUM_RANKS-1:0]                             dh_gs_rank0_wr_odt                  // ODT settings for all ranks when writing to rank 0
    ,input  [NUM_RANKS-1:0]                             dh_gs_rank0_rd_odt                  // ODT settings for all ranks when reading from rank 0
    ,input                                              dh_gs_refresh_update_level          // this signal pulses everytime refresh_update_level register toggles
    ,input                                              derate_refresh_update_level

    ,input  [NUM_LRANKS-1:0]                            dh_gs_rank_refresh                  // cmd issuing refresh to DRAM
    ,output [NUM_LRANKS-1:0]                            gs_dh_rank_refresh_busy             // If 1: Previous dh_gs_rank_refresh has not been stored
    ,input                                              dh_gs_dis_auto_refresh              // 1 - disbale auto-refresh from the controller
    ,input                                              dh_gs_ctrlupd                       // cmd issuing ctrlupd
    ,output                                             gs_dh_ctrlupd_busy                  // If 1: Previous dh_gs_ctrlupd has not been initiated
    ,input                                              reg_ddrc_ctrlupd_burst
    ,output                                             ddrc_reg_ctrlupd_burst_busy
    ,input                                              dh_gs_dis_auto_ctrlupd              // 1- disable ctrlupd issued by the controller
    ,input                                              dh_gs_dis_auto_ctrlupd_srx          // 1- disable ctrlupd issued by the controller at self-refresh exit
    ,input                                              dh_gs_ctrlupd_pre_srx               // ctrlupd behaviour at SRX (sent before or after SRX)

    ,input  [NUM_RANKS-1:0]                             dh_gs_rank1_wr_odt                  // ODT settings for all ranks when writing to rank 1
    ,input  [NUM_RANKS-1:0]                             dh_gs_rank1_rd_odt                  // ODT settings for all ranks when reading from rank 1
    ,input  [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0]  dh_gs_refresh_timer0_start_value_x32 // initial timer value (used to stagger refresh timeouts)
    ,input  [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0]  dh_gs_refresh_timer1_start_value_x32 // initial timer value
    ,input                                              reg_ddrc_prefer_read
    ,input  [7:0]                                       dh_gs_hpr_xact_run_length           // # of cycles the high priority queue is guaranteed to be serviced once queue is critical
    ,input  [15:0]                                      dh_gs_hpr_max_starve                // # of cycles the high priority queue can be starved before going critical
    ,input  [7:0]                                       dh_gs_lpr_xact_run_length           // # of cycles the low priority queue is guaranteed to be serviced once queue is critical
    ,input  [15:0]                                      dh_gs_lpr_max_starve                // # of cycles the low priority queue can be starved before going critical
    ,input  [7:0]                                       dh_gs_w_xact_run_length             // # of transactions to service when the write queue is critical
    ,input  [15:0]                                      dh_gs_w_max_starve                  // # of cycles the low priority queue can be starved before going critical
    ,input  [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0]dh_gs_ctrlupd_min_to_x1024          // min time between DFI controller updates in units of 1024 clock cycles
    ,input  [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0]dh_gs_ctrlupd_max_to_x1024          // max time between DFI controller updates in units of 1024 clock cycles
    ,input  [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8
    ,input  [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1        // max time between controller updates for PPT2.
    ,input  [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit   // t_ctrlupd_interval_type1 unit

    ,input                                              dh_gs_dis_dq                        // disable dequeue of reads and writes (and all bypass paths)

    ,input  [CMD_DELAY_BITS-1:0]                        dfi_cmd_delay
    ,input  [DFI_TWCK_EN_RD_WIDTH-2:0]                  mr_lp_data_rd
    ,input  [DFI_TWCK_EN_WR_WIDTH-2:0]                  mr_lp_data_wr

    ,input                                              pi_gs_rd_vld                        // PI is scheduling a read
    ,input                                              pi_gs_noxact                        // PI is scheduling transaction, so GS may not do so
    ,input                                              pi_gs_ctrlupd_ok

    // command for a single request
    ,input                                              hif_go2critical_lpr                 // go to critical lp read after critical_starve time
    ,input                                              hif_go2critical_hpr                 // go to critical hp read after critical_starve time
    ,input                                              hif_go2critical_wr                  // go to critical read after critical_starve time
    ,input                                              hif_go2critical_l1_wr
    ,input                                              hif_go2critical_l2_wr
    ,input                                              hif_go2critical_l1_lpr
    ,input                                              hif_go2critical_l2_lpr
    ,input                                              hif_go2critical_l1_hpr
    ,input                                              hif_go2critical_l2_hpr
    ,input                                              ih_gs_xact_valid                    // input handler has a valid transaction
    ,input                                              rt_gs_empty                         // read tracking pipeline is empty
    ,input                                              mr_gs_empty                         // write pipeline is empty
    ,input  [1:0]                                       wu_gs_enable_wr                     // data_enable coming from WU module
                                                                                            // if any of these bits are 1, it indicates that a write
                                                                                            // operation is going on. This is used in gs_global_fsm
                                                                                            // in clock_stop logic AND in gs_glue for issuing speculative refresh

    ,input                                              te_gs_any_vpr_timed_out
    ,input                                              ih_gs_any_vpr_timed_out
    ,input                                              te_gs_any_vpw_timed_out
    ,input                                              ih_gs_any_vpw_timed_out
    ,input                                              te_gs_rd_flush                      // flush reads (for write-hits-read)
    ,input                                              te_gs_wr_flush                      // flush writes (for read-hits-write)
    ,input                                              te_gs_any_rd_pending                // 1 or more valid reads pending
    ,input                                              te_gs_any_wr_pending                // 1 or more valid writes pending
    ,input                                              ih_gs_rdhigh_empty                  // no high priority reads pending
    ,input                                              ih_gs_rdlow_empty                   // no low priority reads pending
    ,input                                              os_gs_act_hi_vld                    // high priority activate pending
    ,input  [BSM_BITS-1:0]                              os_gs_act_hi_bsm                    // BSM number of the chosen hi priority activate
    ,input                                              os_gs_rdwr_hi_vld                   // low priority read/write pending
    ,input  [BSM_BITS-1:0]                              os_gs_rdwr_hi_bsm                   // BSM number of the chosen hi priority read/write
    ,input                                              os_gs_act_lo_vld                    // high priority activate pending
    ,input  [BSM_BITS-1:0]                              os_gs_act_lo_bsm                    // BSM number of the chosen lo priority activate
    ,input                                              os_gs_rdwr_lo_vld                   // low priority read/write pending
    ,input  [BSM_BITS-1:0]                              os_gs_rdwr_lo_bsm                   // BSM number of the chosen lo priority read/write
    ,input                                              os_gs_pre_crit_vld                  // critical precharge pending
    ,input  [BSM_BITS-1:0]                              os_gs_pre_crit_bsm                  // BSM number of the chosen critical precharge
    ,input                                              os_gs_pre_req_vld                   // requested precharge pending
    ,input  [BSM_BITS-1:0]                              os_gs_pre_req_bsm                   // BSM number of the chosen requested precharge
    ,input                                              os_gs_act_wr_vld                    // activate for write pending
    ,input  [BSM_BITS-1:0]                              os_gs_act_wr_bsm                    // BSM number of the chosen activate for write
    ,input                                              gs_act_pre_rd_priority              // high priority activate pending
    ,input                                              os_gs_act_wrecc_vld                 // activate for wrecc pending
    ,input  [BSM_BITS-1:0]                              os_gs_act_wrecc_bsm                 // BSM number of the chosen activate for wrecc
    ,input  [NUM_LRANKS-1:0]                            os_gs_rank_closed                   // per-rank indicator: all banks in rank are closed
    ,input  [NUM_RANKS*8-1:0]                           os_gs_bank_closed                   // per-bank indicator
    ,input  [NUM_RANKS*16-1:0]                          os_gs_bg_bank_closed                // BG/banks with pages closed
    ,input  [NUM_LRANKS-1:0]                            te_gs_rank_rd_valid
    ,input  [NUM_LRANKS-1:0]                            te_gs_rank_wr_valid
    ,output [4:0]                                       gs_dh_init_curr_state               // init state for debug
    ,output [4:0]                                       gs_dh_init_next_state               // init state for debug

    ,output                                             gs_dh_selfref_cam_not_empty
    ,input  [NUM_RANKS-1:0]                             os_gs_no_2ck_cmds_after_pre         // blocks 2-cycles commands after PRE or commands w/AP
    ,output [2:0]                                       gs_dh_selfref_state
    ,output [2:0]                                       gs_dh_operating_mode                // 00 = uninitialized
                                                                                            // 01 = normal
                                                                                            // 02 = powerdown
                                                                                            // 03 = self-refresh
    ,output                                             gs_pi_ctrlupd_req                   // DFI controller update - pulsed with refresh signal
    ,output                                             gs_pi_wr_data_pipeline_empty        // indicates no read/write data in flight
    ,output                                             gs_pi_rd_data_pipeline_empty        // indicates no read/write data in flight
    ,output                                             gs_pi_data_pipeline_empty           // indicates no read/write data in flight

    ,output                                             gs_op_is_rd                       // read command issued to DRAM
    ,output                                             gs_op_is_wr                       // read command issued to DRAM
    ,output                                             gs_op_is_act                      // activate command issued to DRAM
    ,output                                             gs_op_is_pre                      // precharge command issued to DRAM
    ,output                                             gs_op_is_ref                      // refresh command issued to DRAM
    ,output                                             gs_op_is_enter_selfref            // send command to enter self refresh
    ,output                                             gs_op_is_exit_selfref             // send command to exit self refresh
    ,output                                             gs_op_is_enter_powerdown          // send command to enter power-down
    ,output                                             gs_op_is_exit_powerdown           // send command to exit power-down
    ,output                                             gs_op_is_load_mode                // load mode register (only driven from init)
    ,output [NUM_RANKS-1:0]                             gs_rdwr_cs_n                      // chip selects for read/write
    ,output [NUM_RANKS-1:0]                             gs_act_cs_n                       // chip selects for act
    ,output [NUM_RANKS-1:0]                             gs_pre_cs_n                       // chip selects for precharge
    ,output [NUM_RANKS-1:0]                             gs_ref_cs_n                       // chip selects for refresh
    ,output [NUM_RANKS-1:0]                             gs_other_cs_n                     // chip selects for other
    ,output [BSM_BITS-1:0]                              gs_rdwr_bsm_num                   // BSM # for read & write commands
    ,output [BSM_BITS-1:0]                              gs_act_bsm_num                    // BSM # for activate
    ,output [BSM_BITS-1:0]                              gs_pre_bsm_num                    // BSM # for precharge

    ,output [RANKBANK_BITS-1:0]                         gs_pre_rankbank_num                 // bank number to precharge the DRAM address for
    ,output [RANKBANK_BITS-1:0]                         gs_rdwr_rankbank_num                // bank number to read/write the DRAM address for
    ,output [RANKBANK_BITS-1:0]                         gs_act_rankbank_num                 // bank number to activate the DRAM address for
    ,output [BANK_BITS-1:0]                             gs_pi_refpb_bank
    ,output                                             gs_cas_ws_req
    ,input                                              pi_rdwr_ok
    ,input                                              pi_col_b3
    ,input                                              pi_lp5_act2_cmd
    ,input                                              pi_lp5_noxact
    ,input                                              pi_lp5_preref_ok
    ,output                                             gs_wr_mode                          // 1=performing writes; 0=performing reads
    ,output                                             gs_te_wr_possible                   // 1=write may be scheduled this cycle
                                                                                            // 0=write may not be scheduled this cycle
    ,output                                             gs_te_pri_level                     // 1=prefer high pri; 0=reverse priority
    ,output [1:0]                                       gs_dh_hpr_q_state                   // state of high priority read queue
    ,output [1:0]                                       gs_dh_lpr_q_state                   // state of low priority read queue
    ,output [1:0]                                       gs_dh_w_q_state                     // state of write queue
    ,output                                             gs_bs_wr_mode_early                 // same as above, 1 clock earlier
    ,output                                             gs_bs_close_pages                   // global FSM requesting all open pages
                                                                                            // to be closed for powerdown or self-refresh
    ,output [NUM_LRANKS-1:0]                            gs_bs_rank_refresh_required         // ranks requiring refresh
    ,output [NUM_LRANKS-1:0]                            gs_bs_rank_refresh_required_early   // ranks requireing refresh early
    ,output [NUM_LRANKS*NUM_BANKS-1:0]                  gs_bs_bank_speculative_ref          // speculative refresh may be issued
    ,output [NUM_LRANKS-1:0]                            gs_rank_block_cas_b3_nxt
    ,output [NUM_LRANKS*BLK_ACT_TRRD_WDT-1:0]           gs_bs_rank_act2_invalid_tmg_nxt
    ,output [NUM_LRANKS-1:0]                            gs_bs_rank_block_act_nxt            // block activate commands from a rank's BSMs
    ,output [NUM_LRANKS*BLK_ACT_TRFC_WDT-1:0]           gs_bs_rank_block_act_trfc_bk_nxt    // block activate commands for tRFC from a rank's BSMs
    ,output [NUM_LRANKS*BLK_ACT_TRRD_WDT-1:0]           gs_bs_rank_block_act_trrd_bg_nxt    // block activate commands for tRRD from a rank's BSMs
    ,output [NUM_LRANKS-1:0]                            gs_bs_rank_block_act_ref_req        // block activate commands from a rank's BSMs
    ,output [NUM_LRANKS-1:0]                            gs_bs_rank_block_rd_nxt             // block read commands from a rank's BSMs
    ,output [NUM_LRANKS-1:0]                            gs_bs_rank_block_wr_nxt             // block write commands from a rank's BSMs
    ,output                                             gs_os_wr_mode_early                 // 1=performing writes; 0=reads
    ,output [NUM_RANKS-1:0]                             gs_bs_zq_calib_short_required       // request to issue zq calib short command - level signal
    ,output [NUM_RANKS-1:0]                             gs_bs_load_mr_norm_required

    ,output                                             gs_pi_init_cke                      // CKE
    ,output                                             gs_pi_init_in_progress

    // address/command will be taken directly from GS
    ,output [MRS_A_BITS-1:0]                            gs_pi_mrs_a                         // value to drive on address bus during mode register set (load mode)
    ,output                                             gs_mpc_zq_start                     // MCP: ZQ Start
    ,output                                             gs_mpc_zq_latch                     // MCP: ZQ Latch
    ,output                                             mr4_req_o
    ,output [`MEMC_FREQ_RATIO * NUM_RANKS-1:0]          gs_pi_odt                           // per-rank ODT controls
    ,output                                             gs_pi_odt_pending                   // waiting for the ODT command to complete

    ,input  [DFI_TPHY_WRLAT_WIDTH-1:0]                  reg_ddrc_dfi_tphy_wrlat
    ,input  [DFI_T_RDDATA_EN_WIDTH-1:0]                 reg_ddrc_dfi_t_rddata_en


    ,input  [DFI_TPHY_WRCSLAT_WIDTH-1:0]                reg_ddrc_dfi_tphy_wrcslat
    ,input  [6:0]                                       reg_ddrc_dfi_tphy_rdcslat
    ,input                                              reg_ddrc_dfi_data_cs_polarity
    ,output [`MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES-1:0]  gs_pi_wrdata_cs_n                   //
    ,output [`MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES-1:0]  gs_pi_rddata_cs_n                   //

    ,output                                             gs_pi_pads_powerdown                // powerdown many pads for DDR powerdown mode
    ,output                                             gs_pi_pads_selfref                  // powerdown more pads for DDR self-refresh mode
    ,output                                             gs_op_is_enter_sr_lpddr             // enter lpddr4 self-refresh mode
    ,output                                             gs_op_is_exit_sr_lpddr              // exit lpddr4 self-refresh mode
    ,output                                             gs_op_is_enter_dsm                  // enter deep sleep mode
    ,output                                             gs_op_is_exit_dsm                   // exit deep sleep mode
    ,output                                             gs_op_is_cas_ws_off
    ,output                                             gs_op_is_cas_wck_sus              // CAS-WCK_SUSPEND command
    ,output                                             gs_wck_stop_ok
    ,input                                              reg_en_dfi_dram_clk_disable
    ,input  [NUM_TOTAL_BSMS-1:0]                        bs_gs_stop_clk_ok                   // stop clk ok from all the BSMs
    ,output                                             gs_pi_stop_clk_ok                   // stop the clock to DRAM during self refresh
    ,output [1:0]                                       gs_pi_stop_clk_type
    ,output                                             dfilp_ctrl_lp
    ,input                                              pi_gs_stop_clk_early
    ,input  [1:0]                                       pi_gs_stop_clk_type
    ,input                                              pi_gs_dfilp_wait
    ,input  [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]           reg_ddrc_dfi_t_dram_clk_enable
    ,input  [T_CKSRE_WIDTH-1:0]                         reg_ddrc_t_cksre
    ,input  [T_CKSRX_WIDTH-1:0]                         reg_ddrc_t_cksrx
    ,input  [T_CKCSX_WIDTH-1:0]                         reg_ddrc_t_ckcsx
    ,input  [T_CKESR_WIDTH-1:0]                         reg_ddrc_t_ckesr

    ,output                                             dfi_lp_ctrl_req
    ,output [DFI_LP_WAKEUP_PD_WIDTH-1:0]                dfi_lp_ctrl_wakeup
    ,input                                              dfi_lp_ctrl_ack
    ,output                                             dfi_lp_data_req
    ,output [DFI_LP_WAKEUP_PD_WIDTH-1:0]                dfi_lp_data_wakeup
    ,input                                              dfi_lp_data_ack
    ,input                                              dfi_reset_n_in
    ,output                                             dfi_reset_n_ref
    ,input                                              init_mr_done_in
    ,output                                             init_mr_done_out
    ,input                                              reg_ddrc_lpddr4_opt_act_timing
    ,input                                              reg_ddrc_lpddr5_opt_act_timing
    ,output                                             lpddr4_blk_act_nxt

    ,input                                              reg_ddrc_dfi_lp_data_req_en
    ,input                                              reg_ddrc_dfi_lp_en_pd
    ,input  [DFI_LP_WAKEUP_PD_WIDTH-1:0]                reg_ddrc_dfi_lp_wakeup_pd
    ,input                                              reg_ddrc_dfi_lp_en_sr
    ,input  [DFI_LP_WAKEUP_SR_WIDTH-1:0]                reg_ddrc_dfi_lp_wakeup_sr
    ,input                                              reg_ddrc_dfi_lp_en_data
    ,input  [DFI_LP_WAKEUP_DATA_WIDTH-1:0]              reg_ddrc_dfi_lp_wakeup_data
    ,input                                              reg_ddrc_dfi_lp_en_dsm
    ,input  [DFI_LP_WAKEUP_DSM_WIDTH-1:0]               reg_ddrc_dfi_lp_wakeup_dsm
    ,input  [DFI_TLP_RESP_WIDTH-1:0]                    reg_ddrc_dfi_tlp_resp
    ,output                                             gs_pi_mrr
    ,output                                             gs_pi_mrr_ext
    ,input                                              dh_gs_mr4_req
    ,input  [NUM_RANKS-1:0]                             dh_gs_mr4_req_rank
    ,output [NUM_LRANKS*BANK_BITS-1:0]                  gs_bs_refpb_bank                    // Bank being targetted per rank for current refpb command

    ,input                                              dh_gs_per_bank_refresh
    ,input                                              dh_gs_per_bank_refresh_opt_en
    ,input                                              dh_gs_fixed_crit_refpb_bank_en
    ,output                                             per_bank_refresh
    ,input                                              phy_dfi_phyupd_req                  // DFI PHY update request
    ,input                                              phy_dfi_phyupd_req_r                // registered DFI PHY update request
    ,output                                             ddrc_dfi_phyupd_ack                 // DFI PHY update acknowledge

    ,input                                              phy_dfi_phymstr_req            // DFI PHY Master request
    ,input [`MEMC_NUM_RANKS-1:0]                        phy_dfi_phymstr_cs_state       // DFI PHY Master CS state
    ,input                                              phy_dfi_phymstr_state_sel      // DFI PHY Master state select
    ,input [1:0]                                        phy_dfi_phymstr_type           // DFI PHY Master time type
    ,output                                             ddrc_dfi_phymstr_ack           // DFI PHY Master acknowledge

    ,input                                              reg_ddrc_dfi_phyupd_en         // Enable for DFI PHY update logic
    ,input                                              reg_ddrc_dfi_phymstr_en        // Enable for DFI PHY Master Interface
    ,input  [7:0]                                       reg_ddrc_dfi_phymstr_blk_ref_x32 // Number of 32 DFI cycles that is delayed to block refresh when there is PHY Master
    ,input                                              reg_ddrc_dis_cam_drain_selfref // Disable CAM draining before entering selfref
    ,input                                              reg_ddrc_lpddr4_sr_allowed     // Allow transition from SR-PD to SR and back to SR-PD when PHY Master request
    ,input   [DFI_T_CTRL_DELAY_WIDTH-1:0]               reg_ddrc_dfi_t_ctrl_delay      // timer value for DFI tctrl_delay
    ,input   [DFI_T_WRDATA_DELAY_WIDTH-1:0]             reg_ddrc_dfi_t_wrdata_delay    // timer value for DFI twrdata_delay

    ,output                                             gs_pi_phyupd_pause_req              // Sent to rest of uMCTL2 to tell system to pause
    ,input                                              pi_gs_phyupd_pause_ok               // resonse from PI to say alright to ack PHY update request

    ,output                                             gs_pi_dfi_lp_changing

    ,input  [1:0]                                       reg_ddrc_skip_dram_init
    ,output                                             gsfsm_dis_dq

    ,output [T_RFC_MIN_WIDTH-1:0]                       gs_bs_t_rfc_min_upd
    ,output [REFRESH_MARGIN_WIDTH-1:0]                  gs_bs_refresh_margin_upd


    ,input  [TARGET_FREQUENCY_WIDTH-1:0]                reg_ddrc_target_frequency
    ,input  [T_VRCG_ENABLE_WIDTH-1:0]                   reg_ddrc_t_vrcg_enable
    ,input  [T_VRCG_DISABLE_WIDTH-1:0]                  reg_ddrc_t_vrcg_disable
    ,input                                              reg_ddrc_target_vrcg
    ,input  [1:0]                                       reg_ddrc_hwffc_en
    ,input                                              reg_ddrc_init_vrcg
    ,input                                              reg_ddrc_skip_mrw_odtvref
    ,input                                              reg_ddrc_dvfsq_enable
    ,input                                              reg_ddrc_dvfsq_enable_next
    ,input                                              reg_ddrc_init_fsp
    ,output                                             ddrc_reg_current_fsp
    ,input  [6:0]                                       reg_ddrc_t_zq_stop
    ,input  [1:0]                                       reg_ddrc_zq_interval
    ,input                                              reg_ddrc_skip_zq_stop_start
    ,output                                             ddrc_reg_hwffc_in_progress
    ,output [TARGET_FREQUENCY_WIDTH-1:0]                                ddrc_reg_current_frequency
    ,output                                             ddrc_reg_current_vrcg
    ,output                                             ddrc_reg_hwffc_operating_mode
    ,output                                             hwffc_dis_zq_derate
    ,output                                             hwffc_hif_wd_stall
    ,output                                             ddrc_xpi_port_disable_req
    ,output                                             ddrc_xpi_clock_required
    ,input [NPORTS-1:0]                                 xpi_ddrc_port_disable_ack
    ,input [NPORTS-2:0]                                 xpi_ddrc_wch_locked

    ,input  [NUM_LRANKS-1:0]                            te_gs_rank_wr_pending // WR command pending in the CAM per rank
    ,input  [NUM_LRANKS-1:0]                            te_gs_rank_rd_pending // RD command pending in the CAM per rank
    ,input  [NUM_TOTAL_BANKS-1:0]                       te_gs_bank_wr_pending // WR command pending in the CAM per rank/bank
    ,input  [NUM_TOTAL_BANKS-1:0]                       te_gs_bank_rd_pending // RD command pending in the CAM per rank/bank
    ,input                                              te_gs_block_wr // Write is not allowed this cycle
    ,output                                             gs_phymstr_sre_req
    ,output                                             gs_bs_sre_stall
    ,output                                             gs_bs_sre_hw_sw
    ,input                                              reg_ddrc_hwffc_mode

    // Frequency selection
    ,output                                             hwffc_target_freq_en
    ,output  [TARGET_FREQUENCY_WIDTH-1:0]                               hwffc_target_freq
    ,output  [TARGET_FREQUENCY_WIDTH-1:0]                               hwffc_target_freq_init
    // DFI frequency change I/F
    ,output                                             hwffc_freq_change
    ,output                                             hwffc_dfi_init_start
    ,output  [4:0]                                      hwffc_dfi_frequency
    ,output                                             hwffc_dfi_freq_fsp
    ,input                                              dfi_init_start
    ,input      [T_CCD_WIDTH-1:0]                       dh_bs_t_ccd
    ,input      [WR2RD_WIDTH-1:0]                       dh_bs_wr2rd
    ,input      [T_CCD_S_WIDTH-1:0]                     dh_bs_t_ccd_s                     // short version for DDR4, the no '_' version is used as Long in DDR4 mode
    ,input      [WR2RD_S_WIDTH-1:0]                     dh_bs_wr2rd_s                     // short version for DDR4, the no '_' version is used as Long in DDR4 mode
    ,input      [RD2WR_WIDTH-1:0]                       reg_ddrc_rd2wr_s                  // short version for DDR4, the no '_' version is used as Long in DDR4 mode
    ,input      [MRR2RD_WIDTH-1:0]                      reg_ddrc_mrr2rd
    ,input      [MRR2WR_WIDTH-1:0]                      reg_ddrc_mrr2wr
    ,input      [MRR2MRW_WIDTH-1:0]                     reg_ddrc_mrr2mrw
    ,output     [NUM_TOTAL_BGS-1:0]                     gs_bs_blk_ccd_timer
    ,output     [NUM_TOTAL_BGS-1:0]                     gs_bs_blk_wr2rd_timer
    ,output     [NUM_TOTAL_BGS-1:0]                     gs_bs_blk_rd2wr_timer

    ,input                                              reg_ddrc_opt_wrcam_fill_level
    ,input [3:0]                                        reg_ddrc_delay_switch_write

    ,input   [NUM_TOTAL_BSMS-1:0]                       te_bs_rd_page_hit               // banks with reads pending to open pages
    ,input   [NUM_TOTAL_BSMS-1:0]                       te_bs_rd_valid                  // banks with reads pending
    ,input   [NUM_TOTAL_BSMS-1:0]                       te_bs_wr_page_hit               // banks with writes pending to open pages
    ,input   [NUM_TOTAL_BSMS-1:0]                       te_bs_wr_valid                  // banks with writes pending
    ,input   [NUM_TOTAL_BSMS-1:0]                       te_ts_vpw_valid                 // banks with writes pending
    ,input   [NUM_TOTAL_BSMS-1:0]                       te_ts_vpr_valid                 // banks with writes pending
    ,input [NUM_TOTAL_BSMS-1:0]                         sel_act_wr
    ,input [NUM_TOTAL_BSMS-1:0]                         bank_wr_activated_early
    ,input [NUM_TOTAL_BSMS-1:0]                         bank_activated_early
    ,input [NUM_TOTAL_BSMS-1:0]                         te_rws_wr_col_bank              // entry of colliding bank (1bit for 1bank)
    ,input [NUM_TOTAL_BSMS-1:0]                         te_rws_rd_col_bank              // entry of colliding bank (1bit for 1bank)
    ,input                                              wr_cam_up_highth
    ,input                                              wr_cam_up_lowth
    ,input                                              wrecc_cam_up_highth             // valid (loaded absolutely)
    ,input                                              wrecc_cam_up_lowth
    ,input                                              wrecc_cam_up_highth_loaded      // loaded (regardless of valid signal)
    ,input                                              wr_cam_up_wrecc_highth
    ,input [NUM_TOTAL_BSMS-1:0]                         te_gs_wrecc_ntt
    ,output                                             gs_te_force_btt
    ,input                                              wr_pghit_up_thresh
    ,input                                              rd_pghit_up_thresh
    ,output                                             delay_switch_write_state
    ,output                                             rd_more_crit
    ,output                                             wr_more_crit
    ,output                                             gs_ts_any_vpr_timed_out
    ,output                                             gs_ts_any_vpw_timed_out
    ,input                                              reg_ddrc_dis_opt_ntt_by_act
    ,input                                                te_rd_bank_pghit_vld_prefer   // Page hit and valid information of oldest entry for read
    ,input                                                te_wr_bank_pghit_vld_prefer   // Page hit and valid information of oldest entry for write
    ,input [RANK_BITS-1:0]                                te_gs_rank_wr_prefer          // rank number of oldest entry in te_wr_cam
    ,input [RANK_BITS-1:0]                                te_gs_rank_rd_prefer          // rank number of oldest entry in te_rd_cam
    ,input                                                reg_ddrc_wck_on
    ,input                                                reg_ddrc_wck_suspend_en
    ,input                                                reg_ddrc_ws_off_en
    ,input [WS_OFF2WS_FS_WIDTH-1:0]                       reg_ddrc_ws_off2ws_fs
    ,input [T_WCKSUS_WIDTH-1:0]                           reg_ddrc_t_wcksus
    ,input [WS_FS2WCK_SUS_WIDTH-1:0]                      reg_ddrc_ws_fs2wck_sus
    ,input [MAX_RD_SYNC_WIDTH-1:0]                        reg_ddrc_max_rd_sync
    ,input [MAX_WR_SYNC_WIDTH-1:0]                        reg_ddrc_max_wr_sync
    ,input [DFI_TWCK_DELAY_WIDTH-1:0]                     reg_ddrc_dfi_twck_delay
    ,input [DFI_TWCK_EN_RD_WIDTH-1:0]                     reg_ddrc_dfi_twck_en_rd
    ,input [DFI_TWCK_EN_WR_WIDTH-1:0]                     reg_ddrc_dfi_twck_en_wr
    ,input [DFI_TWCK_EN_FS_WIDTH-1:0]                     reg_ddrc_dfi_twck_en_fs
    ,input [DFI_TWCK_DIS_WIDTH-1:0]                       reg_ddrc_dfi_twck_dis
    ,input [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0]               reg_ddrc_dfi_twck_fast_toggle
    ,input [DFI_TWCK_TOGGLE_WIDTH-1:0]                    reg_ddrc_dfi_twck_toggle
    ,input [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]                 reg_ddrc_dfi_twck_toggle_cs
    ,input [DFI_TWCK_TOGGLE_POST_WIDTH-1:0]               reg_ddrc_dfi_twck_toggle_post
    ,input                                                reg_ddrc_dfi_twck_toggle_post_rd_en
    ,input [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0]            reg_ddrc_dfi_twck_toggle_post_rd

    ,output [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]              gs_dfi_wck_cs
    ,output [`MEMC_FREQ_RATIO-1:0]                        gs_dfi_wck_en
    ,output [2*`MEMC_FREQ_RATIO-1:0]                      gs_dfi_wck_toggle
    ,input                                                reg_ddrc_dqsosc_enable                 // DQSOSC enable
    ,input  [T_OSCO_WIDTH-1:0]                            reg_ddrc_t_osco                        // t_osco timing
    ,input  [7:0]                                         reg_ddrc_dqsosc_runtime                // Oscillator runtime
    ,input  [7:0]                                         reg_ddrc_wck2dqo_runtime               // Oscillator runtime only for LPDDR5
    ,input  [11:0]                                        reg_ddrc_dqsosc_interval               // DQSOSC inverval
    ,input                                                reg_ddrc_dqsosc_interval_unit          // DQSOSC interval unit
    ,input                                                reg_ddrc_dis_dqsosc_srx
    ,output [2:0]                                         dqsosc_state
    ,output                                               dqsosc_running
    ,output [NUM_RANKS-1:0]                               dqsosc_per_rank_stat
    ,output                                               gs_mpc_dqsosc_start
    ,output [3:0]                                         gs_pi_mrr_snoop_en
    ,output [NUM_RANKS-1:0]                               dqsosc_block_other_cmd
    ,output                                               ddrc_co_perf_op_is_dqsosc_mpc_w
    ,output                                               ddrc_co_perf_op_is_dqsosc_mrr_w
    ,input   [T_PGM_X1_X1024_WIDTH-1:0]                  reg_ddrc_t_pgm_x1_x1024
    ,input                                               reg_ddrc_t_pgm_x1_sel
    ,input   [T_PGMPST_X32_WIDTH-1:0]                    reg_ddrc_t_pgmpst_x32
    ,input   [T_PGM_EXIT_WIDTH-1:0]                      reg_ddrc_t_pgm_exit
    ,input                                               reg_ddrc_ppr_en
    ,output                                              ddrc_reg_ppr_done
    ,input                                               reg_ddrc_ppr_pgmpst_en
    ,input                                               reg_ddrc_ppt2_en
    ,input                                               reg_ddrc_ctrlupd_after_dqsosc
    ,input                                               reg_ddrc_ppt2_wait_ref
    ,input  [PPT2_BURST_NUM_WIDTH-1:0]                   reg_ddrc_ppt2_burst_num
    ,input                                               reg_ddrc_ppt2_burst
    ,output                                              ddrc_reg_ppt2_burst_busy
    ,output [PPT2_STATE_WIDTH-1:0]                       ddrc_reg_ppt2_state
    ,output                                              ppt2_stop_clk_req
    ,input  [PPT2_CTRLUPD_NUM_DFI_WIDTH-1:0]             reg_ddrc_ppt2_ctrlupd_num_dfi1
    ,input  [PPT2_CTRLUPD_NUM_DFI_WIDTH-1:0]             reg_ddrc_ppt2_ctrlupd_num_dfi0
  );

//--------------------------------- WIRES --------------------------------------

wire                          csysreq_ddrc_mux;
wire [FSM_STATE_WIDTH-1:0]    gs_dh_global_fsm_state; // more detailed version of above for debug register readback



wire [NUM_LRANKS-1:0]         gs_bs_refpb_rank_unused;

wire [NUM_LRANKS-1:0]           gs_lpddr54_refpb; // in LPDDR54 connect REFpb bank to next_xact -> sends bank number to PI
                                                 // [NUM_LRANKS-1:NUM_RANKS] are not used in case of NUM_LRANKS>NUM_LRANKS
wire [NUM_LRANKS*8-1:0]         i_os_gs_bank_closed; // padding version of os_gs_bank_closed upper part will not be used as there are no 3DS with LPDDR4.

assign i_os_gs_bank_closed[NUM_RANKS*8-1:0] = os_gs_bank_closed;

generate
   if (NUM_LRANKS>NUM_RANKS) begin: LRANK_GT_RANK
      assign i_os_gs_bank_closed[NUM_LRANKS*8-1:NUM_RANKS*8] = {(NUM_LRANKS-NUM_RANKS)*8{1'b0}};
   end
endgenerate


// All timer start values cat'd together.  (4 values x 8 bits each)
// This has to be done to assign correctly in the generate statement for
// the rank_constraints block
//`ifdef MEMC_NUM_RANKS_1
//wire    [11:0]   dh_gs_refresh_timer_start_values_x32;
//`else // 4 ranks
wire    [REFRESH_TIMER0_START_VALUE_X32_WIDTH*NUM_RANKS-1:0]  dh_gs_refresh_timer_start_values_x32;
wire                        start_zqcs_timer;               // ZQ timer started in init sequence
wire                        ctrlupd_req;
wire                        end_init_ddr;                   // init_ddr fsm done
wire                        normal_operating_mode;          // normal (read/write) operating mode
wire                        init_operating_mode;            // init sequence operating mode
wire                        rdwr_operating_mode_unused;
wire                        sr_mrrw_en;                     // MRR/MRW enable during Self refresh for LPDDR4
wire                        enter_selfref_related_state;    // Enter to SR, SRPD and DSM

wire                        enter_selfref;                  // send command to enter self refresh
wire                        exit_selfref;                   // send command to exit self refresh
wire                        enter_powerdown;                // send command to enter power-down
wire                        exit_powerdown;                 // send command to enter power-down
wire                        exit_selfref_ready;             // controller is ready to exit self refresh
wire                        init_refresh;                   // refresh command during init sequence
wire                        global_block_cke_change;        // no CKE change allowed this cycle
wire                        global_block_rd;                // read blocked globally
wire                        global_block_rd_early;          // read blocked globally - 1 cycle early indication
wire                        global_block_wr_early;          // write blocked globally - 1 cycle early indication
                                                            //  (incomplete, because it does not comprehend
                                                            //   commands issued in the current cycle)

wire                        block_t_xs;                     // block commands during tXS
wire                        block_t_xs_dll;                 // block commands during tXSDLL

wire                        clock_stop_exited;

wire    [NUM_LRANKS-1:0]    refresh_required_early;
wire    [NUM_LRANKS-1:0]    rank_nop_after_refresh;         // block everything after refresh (rank)
wire    [NUM_LRANKS-1:0]    rank_no_refresh_after_refresh;  // delay between 2 refresh commands (Include 16REF/2*tREFI logic)
wire    [NUM_LRANKS-1:0]    rank_no_load_mr_after_refresh;  // no load MR required after a refresh (include DDR4 MPR RD/WR)
wire    [NUM_LRANKS-1:0]    rank_no_rfmpb_for_tpbr2pbr;     // no RFMpb after REFpb/RFMpb to different bank pair for tpbr2pbr
wire    [NUM_LRANKS-1:0]    rank_no_refpb_after_act;        // delay between ACT and REFpb = tRRD
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
wire    [NUM_LRANKS-1:0]    rank_ref_idle_timeout;          // controller has been idle long enough to
`endif // SNPS_ASSERT_ON
`endif // !SYNTHESIS
wire    [NUM_LRANKS-1:0]    rank_refresh_pending;           // ranks requiring refresh, earlier than rank_refresh_required
wire    [NUM_LRANKS-1:0]    rank_refresh_required;          // ranks requiring refresh, per rank
wire    [NUM_LRANKS-1:0]    rank_block_pre;                 // block precharge command per rank
wire                        start_refresh_timer;            // indication to start refresh timers
//wire                        init_dec_refresh_cnt;           // decrement the refresh counter due
//                                                            //  to init sequence refreshes (global)
wire   wr_mode_early;
wire   wr_mode;
wire                        reverse_priority;               // swith high and low priorities
wire    [NUM_LRANKS-1:0]    rank_nop_after_rfm;
wire    [NUM_LRANKS-1:0]    rank_no_load_mr_after_rfm;
wire    [NUM_LRANKS*DBG_RAA_CNT_WIDTH-1:0]  rank_dbg_raa_cnt;

wire                        rdhigh_critical;
wire                        rdlow_critical;
wire                        wr_critical;
wire                        timer_pulse_x32;                // glue logic pulses this once every 32 cycles
wire                        timer_pulse_x1024;              // glue logic pulses this once every 1024 cycles
wire                        timer_pulse_x32_dram;           // glue logic pulses this once every 32 dram cycles
wire                        timer_pulse_x1024_dram;         // glue logic pulses this once every 1024 dram cycles

wire    [7:0]               powerdown_idle_timer;
wire    [7:0]               min_ctrlupd_timer;
wire    [NUM_LRANKS-1:0]    rank_selfref_wait_ref;

wire    [NUM_RANKS-1:0]     rank_nop_after_zqcs;            // NOP after ZQCS
wire    [NUM_RANKS-1:0]     rank_nop_after_zqcs_gfsm;       // NOP after ZQCS gs_global_fsm
wire                        zq_calib_mr_cmd;                // zq calib short command used inside GS
wire                        init_mpc_zq_start;              // MPC: ZQStart
wire                        init_mpc_zq_latch;              // MPC: ZQLatch
wire                        load_mpc_zq_start;              // MPC: ZQStart
wire                        load_mpc_zq_latch;              // MPC: ZQLatch
wire    [NUM_RANKS-1:0]     gs_zq_calib_active_ranks;

// New signals for the mode register write logic addition
wire    [MRS_A_BITS-1:0]    gs_pi_mrs_a_init;
wire    [MRS_BA_BITS-1:0]   gs_pi_mrs_ba_init;
wire                        gs_pi_op_is_load_mode_init;

wire    [MRS_A_BITS-1:0]    gs_pi_mrs_a_norm;
wire    [MRS_BA_BITS-1:0]   gs_pi_mrs_ba_norm;
wire                        gs_pi_op_is_load_mr_norm;

wire                        load_mr_norm;
wire    [NUM_RANKS-1:0]     load_mr_norm_required_to_fsm;
wire    [NUM_RANKS-1:0]     rank_nop_after_load_mr_norm;
wire                        rdwr2mrw_satisfied;
wire                        mrri_satisfied;
wire    [NUM_LRANKS-1:0]    block_mrr2mrw;
wire                        gs_op_is_rd_hi;
wire                        gs_op_is_rd_lo;
wire                        gsnx_op_is_ref;
wire    [NUM_RANKS-1:0]     gsnx_ref_cs_n;
wire    [NUM_RANKS-1:0]     gsnx_other_cs_n;

wire                        gs_hw_mr_norm_busy;
wire                        gsfsm_sr_entry_req;
wire                        zqcl_due_to_sr_exit;

wire                        zqcl_mask_cmds_zq_resistor_shared;

wire                        zqcl_due_to_sr_exit_ext;

wire                        zqcl_due_to_sr_exit_ext_add_x;
wire                        zqcl_due_to_sr_exit_ext_add_y;
wire                        zqcl_due_to_sr_exit_ext_block_new_zq;

wire                        zq_reset_req_on;

wire                        load_mrw_reset_norm;
wire                        zq_lat;
wire                        block_zqlat;
wire                        gs_sw_init_int_possible;

// DFI LP I/F

// from gs_global_fsm
wire                        gfsm_dfilp_trig_pde;
wire                        gfsm_dfilp_trig_pdx;
wire                        gfsm_dfilp_trig_sre;
wire                        gfsm_dfilp_trig_srx;
wire                        gfsm_dfilp_trig_dsme;
wire                        gfsm_dfilp_trig_dsmx;

wire                        dfilp_pde_done;
wire                        dfilp_pde_aborted;
wire                        dfilp_pdx_aborted;
wire                        dfilp_pdx_done;
wire                        dfilp_sre_done;
wire                        dfilp_sre_aborted;
wire                        dfilp_srx_done;
wire                        dfilp_ctrlupd_ok;
wire                        dfilp_phyupd_pause_ok;
wire                        dfilp_dsme_done;
wire                        dfilp_dsme_aborted;
wire                        dfilp_dsmx_done;
wire                        dfilp_active;
wire  [DFI_T_WRDATA_DELAY_WIDTH-1:0]   gs_dfi_t_wrdata_delay_cnt;  // counter value for DFI twrdata_delay

wire                        gsfsm_sr_exit_req;

wire [NUM_RANKS-1:0]        init_cs_n;        // chip select during init sequence
//---------------------------
// Signals associated HWFFC (from/to gs_global_fsm)
//---------------------------
wire                        hwffc_in_progress;
wire                        hwffc_no_other_load_mr;
wire [3:0]                  hwffc_mr_update_start;
wire                        hwffc_mr_update_done;
wire                        hwffc_st_mr_vrcg;
wire                        hwffc_bgzq_stopped;
wire [3:0]                  hwffc_zq_restart;
wire                        hwffc_vrcg;
wire                        hwffc_operating_mode;
wire                        hwffc_mask_dfireq;
wire                        hwffc_refresh_update_pulse;
wire                        i_reg_ddrc_dfi_lp_en_sr;
wire                        dfi_init_complete_init;
wire                        dfi_init_complete_hwffc;

wire                        normal_ppt2_prepare;
wire                        gsfsm_asr_to_sre_asr;
wire                        ppt2_asr_to_sre_asr;    // ASR w/ PD -> SR w/o PD transition is due to PPT2 request
wire                        gs_ppt2_stop_clk_ok_norm;


// Status output
assign ddrc_reg_hwffc_in_progress       = hwffc_in_progress;
assign ddrc_reg_current_frequency       = hwffc_target_freq;    // duplicated
assign ddrc_reg_current_fsp             = hwffc_dfi_freq_fsp;
assign ddrc_reg_current_vrcg            = hwffc_vrcg;
assign ddrc_reg_hwffc_operating_mode    = hwffc_operating_mode;
// Internal
assign i_reg_ddrc_dfi_lp_en_sr          = reg_ddrc_dfi_lp_en_sr & ~hwffc_operating_mode
                                                                                                         ;
assign dfi_init_complete_init           = phy_dfi_init_complete | hwffc_freq_change;
assign dfi_init_complete_hwffc          = phy_dfi_init_complete | !hwffc_freq_change;

//---------------------------
// Signals associated with refresh_update_level pulse generation
//---------------------------
wire                        dh_gs_refresh_update_pulse;
wire                        derate_refresh_update_pulse;

// Updated refresh registers

wire     [T_RFC_MIN_WIDTH-1:0]              t_rfc_min_upd;
wire     [T_PBR2PBR_WIDTH-1:0] t_pbr2pbr_upd;
wire     [T_PBR2ACT_WIDTH-1:0] t_pbr2act_upd;
wire     [REFRESH_MARGIN_WIDTH-1:0]              refresh_margin_upd;
wire     [REFRESH_TO_X1_X32_WIDTH-1:0]              refresh_to_x1_x32_upd;
wire     [5:0]              refresh_burst_upd;

assign gs_bs_t_rfc_min_upd      = t_rfc_min_upd;
assign gs_bs_refresh_margin_upd = refresh_margin_upd;

wire    [T_REFI_X1_X32_WIDTH+4:0]              t_refi;

//--------------------



wire  [NUM_LRANKS-1:0]     rank_block_mrr;


// dual channel signal adjust
wire        dh_gs_2t_mode_2gs;
wire        dh_gs_geardown_mode_2gs;
wire [1:0]  gs_mr_pda_data_sel_2gs;

//spyglass disable_block W528
//SMD: A signal or variable is set but never read - dh_gs_geardown_mode_2gs
//SJ: Used under `ifdef branch but assigned in generate statement
generate
   if (SHARED_AC==1 && CHANNEL_NUM==0) begin: DUAL_ch

      assign dh_gs_2t_mode_2gs         =
                                          1'b0; //don't plus ODT delay in 2T mode if this is DDRC_dch0 on Shared AC mode

      assign dh_gs_geardown_mode_2gs   = 1'b0;
      assign gs_mr_pda_data_sel_2gs    = 2'b00;

   end
   else begin: SINGLE_ch

      assign dh_gs_2t_mode_2gs         = dh_gs_2t_mode;
         assign dh_gs_geardown_mode_2gs   = 1'b0;
         assign gs_mr_pda_data_sel_2gs    = 2'b00;


   end
endgenerate
//spyglass enable_block W528


wire    [NUM_LRANKS-1:0]                gs_ts_lrank_enable_bits;
wire    [NUM_LRANKS-1:0]                rank_speculative_ref;
wire    [NUM_LRANKS*NUM_BANKS-1:0]      bank_speculative_ref;
wire    [NUM_LRANKS-1:0]                wck_sync_st;
wire    [NUM_LRANKS-1:0]                cas_ws_off_req;
wire    [NUM_LRANKS-1:0]                wck_actv_st;
wire    [NUM_LRANKS-1:0]                wck_sus_en;
wire    [NUM_LRANKS-1:0]                blk_mrr_after_cas;
wire    [NUM_LRANKS-1:0]                blk_pd_after_cas;
wire                                    blk_pd_after_wra;
wire    [NUM_RANKS-1:0]                 physical_rank_refresh_required;
wire    [NUM_RANKS-1:0]                 physical_rank_speculative_ref;
wire    [NUM_RANKS-1:0]                 physical_rank_no_refresh_after_refresh;
wire    [NUM_RANKS-1:0]                 physical_rank_no_load_mr_after_refresh;
wire    [NUM_RANKS-1:0]                 physical_rank_block_mrr;
wire    [NUM_RANKS-1:0]                 physical_rank_nop_after_refresh;
wire    [NUM_RANKS-1:0]                 physical_rank_os_gs_rank_closed;
wire    [NUM_RANKS-1:0]                 logical_rank_os_gs_rank_closed_for_ref;
wire te_gs_rd_vld_ref_rdwr_switch;
wire te_gs_wr_vld_ref_rdwr_switch;
wire [NUM_LRANKS-1:0] t_rfc_min_timer_bitor;

// PHY Master Interface related signals
wire gs_dram_st_sr;
wire gs_phymstr_clr_lp_req;
wire gs_phymstr_mask_dfilp;
wire phymstr_active;

wire st_lp_e_ack_check;
wire no_sr_mrrw_due_to_phymstr;

`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
wire    [8:0]       block_rd_timer [NUM_LRANKS-1:0];
wire    [8:0]       block_wr_timer [NUM_LRANKS-1:0];
wire    [NUM_LRANKS-1:0]                load_diff_rank_dly_for_max_rank_rd_non3ds;
wire    [NUM_LRANKS-1:0]                load_diff_rank_dly_for_max_rank_wr_non3ds;
`endif // SNPS_ASSERT_ON
`endif // ~SYNTHESIS

wire                        dqsosc_pd_forbidden;
wire                        dqsosc_loadmr_upd_req_p;
wire                        loadmr_dqsosc_upd_done_p;
wire                        dqsosc_required;
wire                        powerdown_operating_mode;
wire [NUM_RANKS-1:0]        dqsosc_loadmr_rank;
wire                        dqsosc_stopped;
wire [MRS_A_BITS-1:0]       dqsosc_loadmr_a;
wire                        dqsosc_loadmr_mpc;
wire                        dqsosc_loadmr_mrr;
wire [3:0]                  dqsosc_loadmr_snoop_en;


wire                        mr_gs_empty_w;

wire [BURST_RDWR_WIDTH-1:0]       dh_gs_burst_rdwr_int;
assign  dh_gs_burst_rdwr_int = (dh_gs_frequency_ratio) ? dh_gs_burst_rdwr >> 2 : dh_gs_burst_rdwr >> 1;


//--------------------------- BLOCK INSTANTIATIONS -----------------------------

localparam REF_RDWR_SWITCH_EN = `UMCTL2_REF_RDWR_SWITCH_EN;

generate
if (REF_RDWR_SWITCH_EN == 1) begin : rdwr_switch_gen
  gs_ref_rdwr_switch
   #(
    .RD_CAM_ENTRIES                     (RD_CAM_ENTRIES),
    .WR_CAM_ENTRIES                     (WR_CAM_ENTRIES),
    .LRANK_BITS                         (LRANK_BITS),
    .NUM_LRANKS                         (1 << LRANK_BITS) // max # of ranks supported
  )  gs_ref_rdwr_switch (
        //Inputs
        .co_yy_clk                          (co_yy_clk),
        .core_ddrc_rstn                     (core_ddrc_rstn),
        .te_gs_rank_wr_pending              (te_gs_rank_wr_pending),
        .te_gs_rank_rd_pending              (te_gs_rank_rd_pending),
        .te_gs_any_wr_pending               (te_gs_any_wr_pending),
        .te_gs_any_rd_pending               (te_gs_any_rd_pending),
        .t_rfc_min_timer_bitor              (t_rfc_min_timer_bitor),
        .dh_gs_per_bank_refresh             (per_bank_refresh),
        //Outputs
        .te_gs_rd_vld_ref_rdwr_switch       (te_gs_rd_vld_ref_rdwr_switch),
        .te_gs_wr_vld_ref_rdwr_switch       (te_gs_wr_vld_ref_rdwr_switch)
  );
end else begin: n_rdwr_switch_gen
  assign te_gs_rd_vld_ref_rdwr_switch = te_gs_any_rd_pending;
  assign te_gs_wr_vld_ref_rdwr_switch = te_gs_any_wr_pending;
end
endgenerate

wire refab_forced;
wire [T_REFI_X1_X32_WIDTH+4:0] derated_t_refi;
wire [T_REFI_X1_X32_WIDTH+4:0] derated_t_refie;

gs_glue

  gs_glue (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .gs_op_is_wr                        (gs_op_is_wr),
    .global_block_wr_early              (global_block_wr_early),
    .wr_mode_early                      (wr_mode_early),
    .gsnx_op_is_ref                     (gsnx_op_is_ref),
    .init_refresh                       (init_refresh),
    .gs_op_is_ref                       (gs_op_is_ref),
    .init_cs_n                          (init_cs_n),
    .gsnx_ref_cs_n                      (gsnx_ref_cs_n),
    .gsnx_other_cs_n                    (gsnx_other_cs_n),
    .gs_other_cs_n                      (gs_other_cs_n),
    .gs_ref_cs_n                        (gs_ref_cs_n),

// refresh update level related signals
    .dh_gs_refresh_update_level         (dh_gs_refresh_update_level),
    .dh_gs_refresh_update_pulse         (dh_gs_refresh_update_pulse),
    .derate_refresh_update_level        (derate_refresh_update_level),
    .derate_refresh_update_pulse        (derate_refresh_update_pulse),

    .dh_gs_refresh_margin               (dh_gs_refresh_margin),
    .dh_gs_t_rfc_min                    (dh_gs_t_rfc_min),
    .dh_gs_t_rfc_min_ab                 (dh_gs_t_rfc_min_ab),
    .dh_gs_t_pbr2pbr                    (dh_gs_t_pbr2pbr),
    .dh_gs_t_pbr2act                    (dh_gs_t_pbr2act),
    .dh_gs_refresh_to_x1_x32            (dh_gs_refresh_to_x1_x32),
    .dh_gs_refresh_burst                (dh_gs_refresh_burst),
    .dh_gs_t_refi_x1_sel                (dh_gs_t_refi_x1_sel),
    .dh_gs_t_refi_x1_x32                (dh_gs_t_refi_x1_x32),
    .dh_gs_per_bank_refresh             (dh_gs_per_bank_refresh),
    .dh_gs_per_bank_refresh_opt_en      (dh_gs_per_bank_refresh_opt_en),
    .t_refi                             (t_refi),
    .derate_gs_t_refi                   (derate_gs_t_refi),
    .derate_gs_t_refie                  (derate_gs_t_refie),
    .derated_t_refi                     (derated_t_refi),
    .derated_t_refie                    (derated_t_refie),
    .derate_force_refab                 (derate_force_refab),
    .refab_forced                       (refab_forced),
    .reg_ddrc_refresh_to_ab_x32         (reg_ddrc_refresh_to_ab_x32),
    .per_bank_refresh                   (per_bank_refresh),
    .t_rfc_min_upd                      (t_rfc_min_upd),
    .t_pbr2pbr_upd                      (t_pbr2pbr_upd),
    .t_pbr2act_upd                      (t_pbr2act_upd),
    .refresh_margin_upd                 (refresh_margin_upd),
    .refresh_to_x1_x32_upd              (refresh_to_x1_x32_upd),
    .refresh_burst_upd                  (refresh_burst_upd),
//---- end refresh update level related signals

    .dh_gs_sw_init_int                  (dh_gs_sw_init_int),
    .gs_pi_mrs_a_init                   (gs_pi_mrs_a_init),
    .gs_pi_mrs_a_norm                   (gs_pi_mrs_a_norm),
    .gs_pi_mrs_a                        (gs_pi_mrs_a),
    .gs_pi_op_is_load_mode_init         (gs_pi_op_is_load_mode_init),
    .gs_pi_op_is_load_mr_norm           (gs_pi_op_is_load_mr_norm),
    .gs_op_is_load_mode                 (gs_op_is_load_mode),
    .init_mpc_zq_start                  (init_mpc_zq_start),
    .init_mpc_zq_latch                  (init_mpc_zq_latch),
    .load_mpc_zq_start                  (load_mpc_zq_start),
    .load_mpc_zq_latch                  (load_mpc_zq_latch),
    .gs_mpc_zq_start                    (gs_mpc_zq_start),
    .gs_mpc_zq_latch                    (gs_mpc_zq_latch),
    .init_operating_mode                (init_operating_mode),
    .timer_pulse_x32                    (timer_pulse_x32),
    .timer_pulse_x1024                  (timer_pulse_x1024),
    .timer_pulse_x32_dram               (timer_pulse_x32_dram),
    .timer_pulse_x1024_dram             (timer_pulse_x1024_dram),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .reg_ddrc_frequency_ratio           (dh_gs_frequency_ratio),
    .hwffc_refresh_update_pulse         (hwffc_refresh_update_pulse),
    .gs_te_wr_possible                  (gs_te_wr_possible)
);

gs_phyupd
 #(
     .RANK_BITS                          (RANK_BITS)
    ,.CMD_DELAY_BITS                     (CMD_DELAY_BITS)
    ) gs_phyupd (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .phy_dfi_phyupd_req                 (phy_dfi_phyupd_req_r),
    .ddrc_dfi_phyupd_ack                (ddrc_dfi_phyupd_ack),
    .ddrc_dfi_ctrlupd_req               (ddrc_dfi_ctrlupd_req),
    .reg_ddrc_dfi_phyupd_en             (reg_ddrc_dfi_phyupd_en),
    .reg_ddrc_dfi_t_ctrl_delay          (reg_ddrc_dfi_t_ctrl_delay),
    .gs_dfi_t_wrdata_delay_cnt          (gs_dfi_t_wrdata_delay_cnt),
    .dfi_cmd_delay                      (dfi_cmd_delay),
    .gs_wck_stop_ok                     (gs_wck_stop_ok),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    .dfilp_phyupd_pause_ok              (dfilp_phyupd_pause_ok),
    .pi_gs_phyupd_pause_ok              (pi_gs_phyupd_pause_ok)
);

gs_dfilp
 #(
      .CMD_DELAY_BITS                   (CMD_DELAY_BITS)

  )
  gs_dfilp (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dfi_lp_ctrl_req                    (dfi_lp_ctrl_req),
    .dfi_lp_ctrl_wakeup                 (dfi_lp_ctrl_wakeup),
    .dfi_lp_ctrl_ack                    (dfi_lp_ctrl_ack),
    .dfi_lp_data_req                    (dfi_lp_data_req),
    .dfi_lp_data_wakeup                 (dfi_lp_data_wakeup),
    .dfi_lp_data_ack                    (dfi_lp_data_ack),
    .reg_ddrc_dfi_lp_data_req_en        (reg_ddrc_dfi_lp_data_req_en),
    .reg_ddrc_dfi_lp_en_pd              (reg_ddrc_dfi_lp_en_pd),
    .reg_ddrc_dfi_lp_wakeup_pd          (reg_ddrc_dfi_lp_wakeup_pd),
    .reg_ddrc_dfi_lp_en_sr              (i_reg_ddrc_dfi_lp_en_sr),
    .reg_ddrc_dfi_lp_wakeup_sr          (reg_ddrc_dfi_lp_wakeup_sr),
    .reg_ddrc_dfi_lp_en_data            (reg_ddrc_dfi_lp_en_data),
    .reg_ddrc_dfi_lp_wakeup_data        (reg_ddrc_dfi_lp_wakeup_data),
    .reg_ddrc_dfi_lp_en_dsm             (reg_ddrc_dfi_lp_en_dsm),
    .reg_ddrc_dfi_lp_wakeup_dsm         (reg_ddrc_dfi_lp_wakeup_dsm),
    .gfsm_dfilp_trig_pde                (gfsm_dfilp_trig_pde),
    .gfsm_dfilp_trig_pdx                (gfsm_dfilp_trig_pdx),
    .gfsm_dfilp_trig_sre                (gfsm_dfilp_trig_sre),
    .gfsm_dfilp_trig_srx                (gfsm_dfilp_trig_srx),
    .gfsm_dfilp_trig_dsme               (gfsm_dfilp_trig_dsme),
    .gfsm_dfilp_trig_dsmx               (gfsm_dfilp_trig_dsmx),
    .gs_wck_stop_ok                     (gs_wck_stop_ok),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),
    .ctrlupd_req                        (ctrlupd_req),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    .phy_dfi_init_complete              (phy_dfi_init_complete),
    .gs_pi_op_is_load_mr_norm           (gs_pi_op_is_load_mr_norm),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .reg_ddrc_dfi_t_wrdata_delay        (reg_ddrc_dfi_t_wrdata_delay),
    .gs_pi_wr_data_pipeline_empty       (gs_pi_wr_data_pipeline_empty),
    .gs_pi_rd_data_pipeline_empty       (gs_pi_rd_data_pipeline_empty),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .gs_dfi_wck_en                      (gs_dfi_wck_en),
    .hwffc_operating_mode               (hwffc_operating_mode),
    .dfi_cmd_delay                      (dfi_cmd_delay),
    .mr_lp_data_rd                      (mr_lp_data_rd),
    .mr_lp_data_wr                      (mr_lp_data_wr),
    .dfilp_pde_done                     (dfilp_pde_done),
    .dfilp_pde_aborted                  (dfilp_pde_aborted),
    .dfilp_pdx_aborted                  (dfilp_pdx_aborted),
    .dfilp_pdx_done                     (dfilp_pdx_done),
    .dfilp_sre_done                     (dfilp_sre_done),
    .dfilp_sre_aborted                  (dfilp_sre_aborted),
    .dfilp_srx_done                     (dfilp_srx_done),
    .dfilp_ctrlupd_ok                   (dfilp_ctrlupd_ok),
    .dfilp_phyupd_pause_ok              (dfilp_phyupd_pause_ok),
    .dfilp_dsme_done                    (dfilp_dsme_done),
    .dfilp_dsme_aborted                 (dfilp_dsme_aborted),
    .dfilp_dsmx_done                    (dfilp_dsmx_done),
    .dfilp_active                       (dfilp_active),
    .reg_ddrc_dfi_tlp_resp              (reg_ddrc_dfi_tlp_resp),
    .reg_ddrc_dfi_t_ctrl_delay          (reg_ddrc_dfi_t_ctrl_delay),
    .gs_dfi_t_wrdata_delay_cnt          (gs_dfi_t_wrdata_delay_cnt),
    .reg_ddrc_dfi_t_dram_clk_enable     (reg_ddrc_dfi_t_dram_clk_enable),
    .reg_ddrc_t_cksre                   (reg_ddrc_t_cksre),
    .reg_ddrc_t_cksrx                   (reg_ddrc_t_cksrx),
    .reg_ddrc_t_ckcsx                   (reg_ddrc_t_ckcsx),
    .reg_en_dfi_dram_clk_disable        (reg_en_dfi_dram_clk_disable),
    .stop_clk_type                      (gs_pi_stop_clk_type),
    .pi_gs_dfilp_wait                   (pi_gs_dfilp_wait),
    .gs_pi_odt_pending                  (gs_pi_odt_pending),
    .gs_phymstr_clr_lp_req              (gs_phymstr_clr_lp_req),
    .gs_phymstr_mask_dfilp              (gs_phymstr_mask_dfilp),
    .st_lp_e_ack_check                  (st_lp_e_ack_check),
    .dfilp_ctrl_lp                      (dfilp_ctrl_lp)
);

gs_ctrlupd
 #(
    .MAX_CMD_DELAY                      (MAX_CMD_DELAY)
   ,.CMD_DELAY_BITS                     (CMD_DELAY_BITS)
  )
  gs_ctrlupd (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_gs_ctrlupd_min_to_x1024         (dh_gs_ctrlupd_min_to_x1024),
    .dh_gs_ctrlupd_max_to_x1024         (dh_gs_ctrlupd_max_to_x1024),
    .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8 (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8),
    .reg_ddrc_dfi_t_ctrlupd_interval_type1       (reg_ddrc_dfi_t_ctrlupd_interval_type1),
    .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit  (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit),
    .dh_gs_ctrlupd                      (dh_gs_ctrlupd),
    .gs_dh_ctrlupd_busy                 (gs_dh_ctrlupd_busy),
    .reg_ddrc_ctrlupd_burst             (reg_ddrc_ctrlupd_burst),
    .ddrc_reg_ctrlupd_burst_busy        (ddrc_reg_ctrlupd_burst_busy),
    .dh_gs_dis_auto_ctrlupd             (dh_gs_dis_auto_ctrlupd),
    .dh_gs_dis_auto_ctrlupd_srx         (dh_gs_dis_auto_ctrlupd_srx),
    .dh_gs_ctrlupd_pre_srx              (dh_gs_ctrlupd_pre_srx),
    .end_init_ddr                       (end_init_ddr),
    .exit_selfref                       (exit_selfref),
    .exit_selfref_ready                 (exit_selfref_ready),
    .phy_dfi_ctrlupd_ack1               (phy_dfi_ctrlupd_ack1),
    .ddrc_dfi_ctrlupd_req               (ddrc_dfi_ctrlupd_req),
    .ddrc_dfi_ctrlupd_type              (ddrc_dfi_ctrlupd_type),
    .ddrc_dfi_ctrlupd_target            (ddrc_dfi_ctrlupd_target),
    .dh_gs_dfi_t_ctrlup_min             (dh_gs_dfi_t_ctrlup_min),
    .dh_gs_dfi_t_ctrlup_max             (dh_gs_dfi_t_ctrlup_max),
    .reg_ddrc_dfi_t_ctrl_delay          (reg_ddrc_dfi_t_ctrl_delay),
    .reg_ddrc_dfi_t_wrdata_delay        (reg_ddrc_dfi_t_wrdata_delay),
    .gs_dfi_t_wrdata_delay_cnt          (gs_dfi_t_wrdata_delay_cnt),
    .gs_dh_ctrlupd_state                (gs_dh_ctrlupd_state),
    .hwffc_mask_dfireq                  (hwffc_mask_dfireq),
    .reg_ddrc_hwffc_mode                (reg_ddrc_hwffc_mode),
    .timer_pulse_x32                    (timer_pulse_x32),
    .timer_pulse_x1024                  (timer_pulse_x1024),
    .gs_op_is_ref                       (gs_op_is_ref),
    .pi_gs_rd_vld                       (pi_gs_rd_vld),
    .rt_gs_empty                        (rt_gs_empty),
    .mr_gs_empty                        (mr_gs_empty_w),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in ts_assertions module
    .min_ctrlupd_timer                  (min_ctrlupd_timer),
//spyglass enable_block W528
    .dfilp_ctrlupd_ok                   (dfilp_ctrlupd_ok),
    .gs_wck_stop_ok                     (gs_wck_stop_ok),
    .normal_ppt2_prepare                (normal_ppt2_prepare),            // Exit automatic lowpower state.
    .gsfsm_asr_to_sre_asr               (gsfsm_asr_to_sre_asr),
    .ppt2_asr_to_sre_asr                (ppt2_asr_to_sre_asr),
    .reg_ddrc_ppt2_en                   (reg_ddrc_ppt2_en),
    .reg_ddrc_ctrlupd_after_dqsosc      (reg_ddrc_ctrlupd_after_dqsosc),
    .reg_ddrc_ppt2_wait_ref             (reg_ddrc_ppt2_wait_ref),
    .gs_ppt2_stop_clk_ok_norm           (gs_ppt2_stop_clk_ok_norm),
    .reg_ddrc_ppt2_burst_num            (reg_ddrc_ppt2_burst_num),
    .reg_ddrc_ppt2_burst                (reg_ddrc_ppt2_burst),
    .ddrc_reg_ppt2_burst_busy           (ddrc_reg_ppt2_burst_busy),
    .ddrc_reg_ppt2_state                (ddrc_reg_ppt2_state),
    .ppt2_stop_clk_req                  (ppt2_stop_clk_req),
    .reg_ddrc_ppt2_ctrlupd_num_dfi1     (reg_ddrc_ppt2_ctrlupd_num_dfi1),
    .reg_ddrc_ppt2_ctrlupd_num_dfi0     (reg_ddrc_ppt2_ctrlupd_num_dfi0),
    .normal_operating_mode              (normal_operating_mode),
    .dqsosc_running                     (dqsosc_running),

    .dfi_cmd_delay                      (dfi_cmd_delay),
    .ctrlupd_req                        (ctrlupd_req),
    .gs_pi_ctrlupd_req                  (gs_pi_ctrlupd_req),
    .gs_pi_wr_data_pipeline_empty       (gs_pi_wr_data_pipeline_empty),
    .gs_pi_rd_data_pipeline_empty       (gs_pi_rd_data_pipeline_empty),
    .gs_pi_data_pipeline_empty          (gs_pi_data_pipeline_empty),
    .pi_gs_ctrlupd_ok                   (pi_gs_ctrlupd_ok),
    .ddrc_dfi_phyupd_ack                (ddrc_dfi_phyupd_ack),
    .ddrc_dfi_phymstr_ack               (ddrc_dfi_phymstr_ack)
);

gs_global_constraints
 #(
  )
  gs_global_constraints (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_bs_t_ccd                        (dh_bs_t_ccd),
    .dh_bs_t_ccd_s                      (dh_bs_t_ccd_s),
    .dh_gs_rd2wr                        (dh_gs_rd2wr),
    .dh_gs_wr2rd                        (dh_gs_wr2rd),
    .dh_gs_t_cke                        (dh_gs_t_cke),
    .reg_ddrc_t_ckesr                   (reg_ddrc_t_ckesr),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),
    .gs_op_is_load_mode                 (gs_op_is_load_mode),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .enter_powerdown                    (enter_powerdown),
    .enter_selfref                      (enter_selfref),
    .reg_ddrc_lpddr4_opt_act_timing     (reg_ddrc_lpddr4_opt_act_timing),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .lpddr4_blk_act_nxt                 (lpddr4_blk_act_nxt),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .reg_ddrc_bank_org                  (reg_ddrc_bank_org),
    .reg_ddrc_rd2wr_s                   (reg_ddrc_rd2wr_s),
    .os_te_autopre                      (os_te_autopre),
    .reg_ddrc_wra2pre                   (reg_ddrc_wra2pre),
    .dh_gs_t_cmdcke                     (dh_gs_t_cmdcke),
    .blk_pd_after_wra                   (blk_pd_after_wra),
    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio),
    .exit_powerdown                     (exit_powerdown),
    .exit_selfref                       (exit_selfref),
    .global_block_rd                    (global_block_rd),
    .dh_gs_t_xp                         (dh_gs_t_xp),
    .dh_gs_t_rcd                        (dh_gs_t_rcd),
    .reg_ddrc_t_csh                     (reg_ddrc_t_csh),
    .reg_ddrc_rd2mr                     (reg_ddrc_rd2mr),
    .reg_ddrc_wr2mr                     (reg_ddrc_wr2mr),
    .mrri_satisfied                     (mrri_satisfied),
    .rdwr2mrw_satisfied                 (rdwr2mrw_satisfied),
    .global_block_rd_early              (global_block_rd_early),
    .global_block_wr_early              (global_block_wr_early),
    .global_block_cke_change            (global_block_cke_change)
);

gs_next_xact

  gs_next_xact (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_gs_2t_mode                      (dh_gs_2t_mode),
    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio),
    .dh_gs_sw_init_int                  (dh_gs_sw_init_int),
    .gs_sw_init_int_possible            (gs_sw_init_int_possible),
    .hwffc_no_other_load_mr             (hwffc_no_other_load_mr),
    .ih_gs_xact_valid                   (ih_gs_xact_valid),
    .pi_gs_noxact                       (pi_gs_noxact),
    .gs_hw_mr_norm_busy                 (gs_hw_mr_norm_busy),
    .pi_gs_stop_clk_early               (pi_gs_stop_clk_early),
    .pi_gs_stop_clk_type                (pi_gs_stop_clk_type),
    .clock_stop_exited                  (clock_stop_exited),
    .reg_ddrc_dfi_t_ctrl_delay          (reg_ddrc_dfi_t_ctrl_delay),
    .reg_ddrc_dfi_t_dram_clk_enable     (reg_ddrc_dfi_t_dram_clk_enable),
    .reg_ddrc_t_cksrx                   (reg_ddrc_t_cksrx),
    .reg_ddrc_t_ckcsx                   (reg_ddrc_t_ckcsx),
    .os_gs_act_lo_vld                   (os_gs_act_lo_vld),
    .os_gs_act_lo_bsm                   (os_gs_act_lo_bsm),
    .os_gs_act_hi_vld                   (os_gs_act_hi_vld),
    .os_gs_act_hi_bsm                   (os_gs_act_hi_bsm),
    .os_gs_rdwr_hi_vld                  (os_gs_rdwr_hi_vld),
    .os_gs_rdwr_hi_bsm                  (os_gs_rdwr_hi_bsm),
    .reverse_priority                   (reverse_priority),
    .os_gs_rdwr_lo_vld                  (os_gs_rdwr_lo_vld),
    .os_gs_rdwr_lo_bsm                  (os_gs_rdwr_lo_bsm),
    .os_gs_pre_crit_vld                 (os_gs_pre_crit_vld),
    .os_gs_pre_crit_bsm                 (os_gs_pre_crit_bsm),
    .os_gs_pre_req_vld                  (os_gs_pre_req_vld),
    .os_gs_pre_req_bsm                  (os_gs_pre_req_bsm),
    .os_gs_act_wr_vld                   (os_gs_act_wr_vld),
    .os_gs_act_wr_bsm                   (os_gs_act_wr_bsm),
    .os_gs_act_wrecc_vld                (os_gs_act_wrecc_vld),
    .os_gs_act_wrecc_bsm                (os_gs_act_wrecc_bsm),
    .gs_act_pre_rd_priority             (gs_act_pre_rd_priority),
    .os_gs_rank_closed                  (physical_rank_os_gs_rank_closed),
    .os_gs_rank_closed_for_ref          (logical_rank_os_gs_rank_closed_for_ref),
    .os_gs_bank_closed                  (os_gs_bank_closed),
    .dh_gs_rfmsbc                       (dh_gs_rfmsbc),
    .os_gs_bg_bank_closed               (os_gs_bg_bank_closed),
    .enter_selfref                      (gs_op_is_enter_selfref),
    .wr_mode                            (wr_mode),
    .normal_operating_mode              (normal_operating_mode),
    .init_operating_mode                (init_operating_mode),
    .os_gs_no_2ck_cmds_after_pre        (os_gs_no_2ck_cmds_after_pre),
    .sr_mrrw_en                         (sr_mrrw_en),
    .block_zqlat                        (block_zqlat),
    .rank_block_pre                     (rank_block_pre),
    .rank_refresh_required              (physical_rank_refresh_required),
    .rank_speculative_ref               (physical_rank_speculative_ref),
    .rank_nop_after_refresh             (physical_rank_nop_after_refresh),
    .rank_no_refresh_after_refresh      (physical_rank_no_refresh_after_refresh),
    .rank_no_load_mr_after_refresh      (physical_rank_no_load_mr_after_refresh),
    .rank_no_rfmpb_for_tpbr2pbr         (rank_no_rfmpb_for_tpbr2pbr),
    .rank_no_refpb_after_act            (rank_no_refpb_after_act),
    .rank_rfm_required                  (gs_bs_rank_rfm_required),
    .gs_op_is_rfm                       (gs_op_is_rfm),
    .gs_rfm_cs_n                        (gs_rfm_cs_n),
    .gs_bs_rfmpb_bank                   (gs_bs_rfmpb_bank),
    .gs_pi_rfmpb_bank                   (gs_pi_rfmpb_bank),
    .gs_bs_rfmpb_sb0                    (gs_bs_rfmpb_sb0),
    .gs_pi_rfmpb_sb0                    (gs_pi_rfmpb_sb0),
    .rank_nop_after_rfm                 (rank_nop_after_rfm),
    .rank_no_load_mr_after_rfm          (rank_no_load_mr_after_rfm),
    .global_block_rd                    (global_block_rd),
    .load_mr_norm_required              (gs_bs_load_mr_norm_required),
    .load_mr_norm                       (load_mr_norm),
    .rank_nop_after_load_mr_norm        (rank_nop_after_load_mr_norm),
    .gs_pi_op_is_load_mr_norm           (gs_pi_op_is_load_mr_norm),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .rank_block_mrr                     (physical_rank_block_mrr),
    .rank_nop_after_zqcs                (rank_nop_after_zqcs),
    .zqcl_due_to_sr_exit_ext            (zqcl_due_to_sr_exit_ext),
    .dh_gs_rank0_wr_odt                 (dh_gs_rank0_wr_odt),
    .dh_gs_rank1_wr_odt                 (dh_gs_rank1_wr_odt),
    .block_t_xs                         (block_t_xs),
    .block_t_xs_dll                     (block_t_xs_dll),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_rd_hi                     (gs_op_is_rd_hi),
    .gs_op_is_rd_lo                     (gs_op_is_rd_lo),
    .gs_op_is_wr                        (gs_op_is_wr),
    .gs_op_is_act                       (gs_op_is_act),
    .gs_op_is_pre                       (gs_op_is_pre),
    .gsnx_op_is_ref                     (gsnx_op_is_ref),
    .gs_op_is_cas_ws_off                (gs_op_is_cas_ws_off),
    .gs_op_is_cas_wck_sus               (gs_op_is_cas_wck_sus),
    .gs_rdwr_cs_n                       (gs_rdwr_cs_n),
    .gs_act_cs_n                        (gs_act_cs_n),
    .gs_pre_cs_n                        (gs_pre_cs_n),
    .gsnx_ref_cs_n                      (gsnx_ref_cs_n),
    .gsnx_other_cs_n                    (gsnx_other_cs_n),
    .gs_pre_bsm_num                     (gs_pre_bsm_num),
    .gs_rdwr_bsm_num                    (gs_rdwr_bsm_num),
    .gs_act_bsm_num                     (gs_act_bsm_num),
    .gs_pre_rankbank_num                (gs_pre_rankbank_num),
    .gs_rdwr_rankbank_num               (gs_rdwr_rankbank_num),
    .gs_act_rankbank_num                (gs_act_rankbank_num)
    ,.gs_refpb_bank                      (gs_bs_refpb_bank) // Use only bits for existing physical rank(s)
    ,.gs_lpddr54_refpb                   (gs_lpddr54_refpb)
    ,.gs_pi_refpb_bank                   (gs_pi_refpb_bank)
    ,.gs_cas_ws_req                      (gs_cas_ws_req)
    ,.wck_sync_st                        (wck_sync_st)
    ,.cas_ws_off_req                     (cas_ws_off_req)
    ,.gs_op_is_enter_powerdown           (gs_op_is_enter_powerdown)
    ,.gs_op_is_enter_selfref             (gs_op_is_enter_selfref)
    ,.gs_op_is_enter_dsm                 (gs_op_is_enter_dsm)
    ,.reg_ddrc_wck_on                    (reg_ddrc_wck_on)
    ,.reg_ddrc_wck_suspend_en            (reg_ddrc_wck_suspend_en)
    ,.reg_ddrc_ws_off_en                 (reg_ddrc_ws_off_en)
    ,.wck_actv_st                        (wck_actv_st)
    ,.wck_sus_en                         (wck_sus_en)
    ,.blk_mrr_after_cas                  (blk_mrr_after_cas)
    ,.pi_rdwr_ok                         (pi_rdwr_ok)
    ,.pi_lp5_noxact                      (pi_lp5_noxact)
    ,.pi_lp5_preref_ok                   (pi_lp5_preref_ok)
    ,.pi_col_b3                          (pi_col_b3)
    ,.dh_gs_per_bank_refresh             (per_bank_refresh)
    ,.refab_forced                       (refab_forced)
    ,.rdwr2mrw_satisfied                 (rdwr2mrw_satisfied)
    ,.mrri_satisfied                     (mrri_satisfied)
    ,.block_mrr2mrw                      (block_mrr2mrw)
    ,.init_refresh                       (init_refresh)
    ,.dh_gs_lpddr4                       (dh_gs_lpddr4)
    ,.reg_ddrc_lpddr5                    (reg_ddrc_lpddr5)
    ,.dh_gs_active_ranks                 (dh_gs_active_ranks)
    ,.no_sr_mrrw_due_to_phymstr          (no_sr_mrrw_due_to_phymstr)
    ,.reg_ddrc_dis_opt_ntt_by_act        (reg_ddrc_dis_opt_ntt_by_act)
    ,.sel_act_wr                        (sel_act_wr)
    ,.te_gs_block_wr                    (te_gs_block_wr)
`ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
    ,.dh_gs_refresh_to_x1_x32            (refresh_to_x1_x32_upd)
    ,.rank_ref_idle_timeout              (rank_ref_idle_timeout[NUM_RANKS-1:0])
    ,.lrank_speculative_ref              (rank_speculative_ref)
    ,.bank_speculative_ref               (bank_speculative_ref)
    ,.os_gs_lrank_closed                 (os_gs_rank_closed)
    `endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
);


gs_odt

      #(.NUM_LANES(NUM_LANES))
     gs_odt (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),

    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio),

    .dh_gs_rank0_wr_odt                 (dh_gs_rank0_wr_odt),
    .dh_gs_rank0_rd_odt                 (dh_gs_rank0_rd_odt),
    .dh_gs_rank1_wr_odt                 (dh_gs_rank1_wr_odt),
    .dh_gs_rank1_rd_odt                 (dh_gs_rank1_rd_odt),
    .gs_rdwr_cs_n                       (gs_rdwr_cs_n),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_op_is_load_mode                 (gs_op_is_load_mode),
    .dh_gs_mr_rank                      (dh_gs_mr_rank),
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .dh_gs_mr4_req_rank                 (dh_gs_mr4_req_rank),
    .dh_gs_2t_mode                      (dh_gs_2t_mode_2gs),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .dqsosc_loadmr_rank                (dqsosc_loadmr_rank),
    .dqsosc_loadmr_mrr                 (dqsosc_loadmr_mrr),
    .gs_pi_odt                          (gs_pi_odt),
    .gs_pi_odt_pending                  (gs_pi_odt_pending)
   ,.reg_ddrc_dfi_tphy_wrcslat          (reg_ddrc_dfi_tphy_wrcslat)
   ,.reg_ddrc_dfi_tphy_rdcslat          (reg_ddrc_dfi_tphy_rdcslat)
   ,.reg_ddrc_dfi_data_cs_polarity      (reg_ddrc_dfi_data_cs_polarity)
   ,.gs_pi_wrdata_cs_n                  (gs_pi_wrdata_cs_n)
   ,.gs_pi_rddata_cs_n                  (gs_pi_rddata_cs_n)
   ,.gs_odt_cg_en                       (~dh_gs_lpddr4)
);

assign  dh_gs_refresh_timer_start_values_x32 = {
            dh_gs_refresh_timer1_start_value_x32,
            dh_gs_refresh_timer0_start_value_x32 };



//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(gen_ranks * NUM_BG_BANKS)' found in module 'gs'
//SJ: This coding style is acceptable and there is no plan to change it.

// Generate rank constraints for the appropriate number of ranks
genvar gen_ranks;
generate
    for (gen_ranks=0; gen_ranks<NUM_LRANKS; gen_ranks=gen_ranks+1) begin : rank_constraints
gs_rank_constraints
 #(
     .THIS_RANK_NUMBER                  (gen_ranks),
     .CMD_LEN_BITS                      (CMD_LEN_BITS)
    ) gs_rank_constraints0 (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio),
    .dh_gs_burst_rdwr_int               (dh_gs_burst_rdwr_int),
    .dh_gs_refresh_to_x1_x32            (refresh_to_x1_x32_upd),
    .dh_gs_refresh_burst                (refresh_burst_upd),
    .dh_gs_diff_rank_rd_gap             (dh_gs_diff_rank_rd_gap),
    .dh_gs_diff_rank_wr_gap             (dh_gs_diff_rank_wr_gap),
    .reg_ddrc_rd2wr_dr                  (reg_ddrc_rd2wr_dr),
    .reg_ddrc_wr2rd_dr                  (reg_ddrc_wr2rd_dr),
    .dh_gs_max_rank_rd                  (dh_gs_max_rank_rd),
    .dh_gs_max_rank_wr                  (dh_gs_max_rank_wr),
    .dh_gs_dis_max_rank_wr_opt          (dh_gs_dis_max_rank_wr_opt),
    .dh_gs_dis_max_rank_rd_opt          (dh_gs_dis_max_rank_rd_opt),
    `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
    .block_rd_timer_sva                 (block_rd_timer[gen_ranks]),
    .block_wr_timer_sva                 (block_wr_timer[gen_ranks]),
    .load_diff_rank_dly_for_max_rank_rd_non3ds (load_diff_rank_dly_for_max_rank_rd_non3ds[gen_ranks]),
    .load_diff_rank_dly_for_max_rank_wr_non3ds (load_diff_rank_dly_for_max_rank_wr_non3ds[gen_ranks]),
    `endif // SNPS_ASSERT_ON
    `endif // ~SYNTHESIS
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .dh_gs_t_faw                        (dh_gs_t_faw),
    .dh_gs_t_rfc_min                    (t_rfc_min_upd),
    .dh_gs_t_pbr2pbr                    (t_pbr2pbr_upd),
    .dh_gs_t_pbr2act                    (t_pbr2act_upd),
    .t_refi                             (t_refi),
    .dh_gs_refresh_to_x1_sel            (dh_gs_refresh_to_x1_sel),
    .dh_gs_t_rrd                        (dh_gs_t_rrd),
    .dh_gs_t_rrd_s                      (dh_gs_t_rrd_s),
    .dh_gs_refresh_update_pulse         (dh_gs_refresh_update_pulse),
    .dh_gs_rfm_en                       (dh_gs_rfm_en),
    .dh_gs_dis_mrrw_trfc                (dh_gs_dis_mrrw_trfc),
    .dh_gs_rfmsbc                       (dh_gs_rfmsbc),
    .dh_gs_raaimt                       (dh_gs_raaimt),
    .dh_gs_raamult                      (dh_gs_raamult),
    .dh_gs_raadec                       (dh_gs_raadec),
    .dh_gs_rfmth_rm_thr                 (dh_gs_rfmth_rm_thr),
    .dh_gs_init_raa_cnt                 (dh_gs_init_raa_cnt),
    .dh_gs_t_rfmpb                      (dh_gs_t_rfmpb),
    .dh_gs_dbg_raa_bg_bank              (dh_gs_dbg_raa_bg_bank),
    .rank_dbg_raa_cnt                   (rank_dbg_raa_cnt[gen_ranks*DBG_RAA_CNT_WIDTH+:DBG_RAA_CNT_WIDTH]),
    .gs_dh_rank_raa_cnt_gt0             (gs_dh_rank_raa_cnt_gt0[gen_ranks]),
    .dh_gs_dsm_en                       (reg_ddrc_dsm_en),
    .derate_operating_rm                (derate_operating_rm),
    .wr_mode                            (wr_mode),
    .bank_pgmiss_exvpr_valid            (bank_pgmiss_exvpr_valid[gen_ranks*NUM_BG_BANKS+:NUM_BG_BANKS]),
    .bank_pgmiss_exvpw_valid            (bank_pgmiss_exvpw_valid[gen_ranks*NUM_BG_BANKS+:NUM_BG_BANKS]),
    .rank_rfm_required                  (gs_bs_rank_rfm_required[gen_ranks]),
    .gs_bs_rfmpb_bank                   (gs_bs_rfmpb_bank[(gen_ranks+1)*BANK_BITS-1:gen_ranks*BANK_BITS]),
    .gs_bs_rfmpb_sb0                    (gs_bs_rfmpb_sb0[gen_ranks]),
    .gs_op_is_rfm                       (gs_op_is_rfm),
    .gs_rfm_cs_n                        (gs_rfm_cs_n),
    .rank_nop_after_rfm                 (rank_nop_after_rfm[gen_ranks]),
    .rank_no_load_mr_after_rfm          (rank_no_load_mr_after_rfm[gen_ranks]),
    .gs_bs_rank_block_act_trfm_bk_nxt   (gs_bs_rank_block_act_trfm_bk_nxt[BLK_ACT_TRFM_WDT*gen_ranks+:BLK_ACT_TRFM_WDT]),
    .gs_bs_rank_block_act_raa_expired   (gs_bs_rank_block_act_raa_expired[BLK_ACT_RAAC_WDT*gen_ranks+:BLK_ACT_RAAC_WDT]),
    .gs_pi_ctrlupd_req                  (gs_pi_ctrlupd_req),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    //.gs_pi_stop_clk_ok                  (gs_pi_stop_clk_ok),
    .gs_op_is_enter_powerdown           (gs_op_is_enter_powerdown),
    .gs_op_is_enter_dsm                 (gs_op_is_enter_dsm),
    .gs_op_is_cas_ws_off                (gs_op_is_cas_ws_off),
    .gs_op_is_cas_wck_sus               (gs_op_is_cas_wck_sus),
    .reg_ddrc_wck_on                    (reg_ddrc_wck_on),
    .dh_gs_t_cmdcke                     (dh_gs_t_cmdcke),
    .reg_ddrc_ws_off2ws_fs              (reg_ddrc_ws_off2ws_fs),
    .reg_ddrc_t_wcksus                  (reg_ddrc_t_wcksus),
    .reg_ddrc_ws_fs2wck_sus             (reg_ddrc_ws_fs2wck_sus),
    .reg_ddrc_max_rd_sync               (reg_ddrc_max_rd_sync),
    .reg_ddrc_max_wr_sync               (reg_ddrc_max_wr_sync),
    .gs_dram_st_sr                      (gs_dram_st_sr),
    .derate_refresh_update_pulse        (derate_refresh_update_pulse),
    .derated_t_refi                     (derated_t_refi),
    .derated_t_refie                    (derated_t_refie),
    .dh_gs_derate_enable                (dh_gs_derate_enable),
    .refab_forced                       (refab_forced),
    .max_postponed_ref_cmd              (max_postponed_ref_cmd),
    .max_ref_cmd_within_2trefi          (max_ref_cmd_within_2trefi),
    .enter_selfref_related_state        (enter_selfref_related_state),
    .dh_gs_rank_refresh                 (dh_gs_rank_refresh[gen_ranks]),
    .gs_dh_rank_refresh_busy            (gs_dh_rank_refresh_busy[gen_ranks]),
    .dh_gs_dis_auto_refresh             (dh_gs_dis_auto_refresh),
    .dh_gs_phymstr_en                   (reg_ddrc_dfi_phymstr_en),
    .dh_gs_phymstr_blk_ref_x32          (reg_ddrc_dfi_phymstr_blk_ref_x32),
    .gs_phymstr_sre_req                 (gs_phymstr_sre_req),
    .gs_pi_op_is_load_mr_norm           (gs_pi_op_is_load_mr_norm),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .dh_gs_2t_mode                      (dh_gs_2t_mode),
    .te_gs_rank_wr_pending              (te_gs_rank_wr_pending[gen_ranks]),
    .te_gs_rank_rd_pending              (te_gs_rank_rd_pending[gen_ranks]),
    .te_gs_bank_wr_pending              (te_gs_bank_wr_pending[gen_ranks*NUM_BANKS+:NUM_BANKS]), // discard BG
    .te_gs_bank_rd_pending              (te_gs_bank_rd_pending[gen_ranks*NUM_BANKS+:NUM_BANKS]), // discard BG
    .timer_pulse_x32                    (timer_pulse_x32),
    .dh_gs_per_bank_refresh             (per_bank_refresh),
    .dh_gs_per_bank_refresh_opt_en      (dh_gs_per_bank_refresh_opt_en),
    .dh_gs_fixed_crit_refpb_bank_en     (dh_gs_fixed_crit_refpb_bank_en),
    .init_refresh                       (init_refresh),
    .load_mrw_reset_norm                (load_mrw_reset_norm),
    .gs_bs_refpb                        (gs_bs_refpb_rank_unused[gen_ranks]),
    .gs_bs_refpb_bank                   (gs_bs_refpb_bank[(gen_ranks+1)*BANK_BITS-1:gen_ranks*BANK_BITS]),
    .os_gs_bank_closed                  (i_os_gs_bank_closed[gen_ranks*NUM_BANKS +: NUM_BANKS]),
    .gs_lpddr54_refpb                   (gs_lpddr54_refpb[gen_ranks]),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .reg_ddrc_lpddr5_opt_act_timing     (reg_ddrc_lpddr5_opt_act_timing),
    .reg_ddrc_bank_org                  (reg_ddrc_bank_org),
    .dh_gs_lpddr4_diff_bank_rwa2pre     (dh_gs_lpddr4_diff_bank_rwa2pre),
    .dh_gs_t_ppd                        (dh_gs_t_ppd),
    .pi_gs_noxact                       (pi_gs_noxact),
    .pi_lp5_act2_cmd                    (pi_lp5_act2_cmd),
    .gs_op_is_pre                       (gs_op_is_pre),
    .gs_op_is_exit_sr_lpddr             (gs_op_is_exit_sr_lpddr),
    .gs_bs_rank_act2_invalid_tmg_nxt    (gs_bs_rank_act2_invalid_tmg_nxt[BLK_ACT_TRRD_WDT*gen_ranks+:BLK_ACT_TRRD_WDT]),
    .rank_block_pre                     (rank_block_pre[gen_ranks]),
    .gs_dh_operating_mode               (gs_dh_operating_mode),
    .init_operating_mode                (init_operating_mode),
    .gs_op_is_enter_selfref             (gs_op_is_enter_selfref),
    .gs_op_is_exit_selfref              (gs_op_is_exit_selfref),
    .te_gs_rank_rd_valid                (te_gs_rank_rd_valid),
    .te_gs_rank_wr_valid                (te_gs_rank_wr_valid),
//  .dh_gs_skip_init                    (dh_gs_skip_init),
    .start_refresh_timer                (start_refresh_timer),
    // stagger the refresh timer start values amongst the 4 ranks,
    // so other ranks can handle traffic while 1 is refreshing
    .ref_timer_start_value_x32          (dh_gs_refresh_timer_start_values_x32),
    .dh_gs_refresh_margin               (refresh_margin_upd),

    .gs_op_is_ref                       (gs_op_is_ref),
    .gs_op_is_act                       (gs_op_is_act),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),
    .gsnx_op_is_ref                     (gsnx_op_is_ref),
    .gs_ref_cs_n                        (gs_ref_cs_n),
    .gs_rdwr_cs_n                       (gs_rdwr_cs_n),
    .gs_act_cs_n                        (gs_act_cs_n),
    .gs_other_cs_n                      (gs_other_cs_n),
    .gs_pre_cs_n                        (gs_pre_cs_n),
    .gs_rdwr_rankbank_num               (gs_rdwr_rankbank_num),
    .gs_act_rankbank_num                (gs_act_rankbank_num),

    .refresh_required_early             (refresh_required_early[gen_ranks]),
    .gs_bs_rank_refresh_required        (gs_bs_rank_refresh_required[gen_ranks]),
    .gs_bs_rank_refresh_required_early  (gs_bs_rank_refresh_required_early[gen_ranks]),
    .rank_refresh_required              (rank_refresh_required[gen_ranks]),
    .gsfsm_sr_entry_req                 (gsfsm_sr_entry_req),
    .rank_refresh_pending               (rank_refresh_pending[gen_ranks]),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs and in SVA file. Decided to keep current implementation.
    .rank_speculative_ref               (rank_speculative_ref[gen_ranks]),
//spyglass enable_block W528
    .bank_speculative_ref               (bank_speculative_ref[NUM_BANKS*gen_ranks+:NUM_BANKS]),
    .wck_sync_st                        (wck_sync_st[gen_ranks]),
    .cas_ws_off_req                     (cas_ws_off_req[gen_ranks]),
    .wck_actv_st                        (wck_actv_st[gen_ranks]),
    .wck_sus_en                         (wck_sus_en[gen_ranks]),
    .blk_mrr_after_cas                  (blk_mrr_after_cas[gen_ranks]),
    .blk_pd_after_cas                   (blk_pd_after_cas[gen_ranks]),
    .gs_rank_block_cas_b3_nxt           (gs_rank_block_cas_b3_nxt[gen_ranks]),
    .block_mrr2mrw                      (block_mrr2mrw[gen_ranks]),
    .gs_bs_rank_block_act_nxt           (gs_bs_rank_block_act_nxt[gen_ranks]),
    .gs_bs_rank_block_act_trfc_bk_nxt   (gs_bs_rank_block_act_trfc_bk_nxt[BLK_ACT_TRFC_WDT*gen_ranks+:BLK_ACT_TRFC_WDT]),
    .gs_bs_rank_block_act_trrd_bg_nxt   (gs_bs_rank_block_act_trrd_bg_nxt[BLK_ACT_TRRD_WDT*gen_ranks+:BLK_ACT_TRRD_WDT]),
    .rank_block_act_ref_req             (gs_bs_rank_block_act_ref_req[gen_ranks]),
    .gs_bs_rank_block_rd_nxt            (gs_bs_rank_block_rd_nxt[gen_ranks]),
    .gs_bs_rank_block_wr_nxt            (gs_bs_rank_block_wr_nxt[gen_ranks]),
    .rank_block_mrr                     (rank_block_mrr[gen_ranks]),
    .rank_no_refresh_after_refresh      (rank_no_refresh_after_refresh[gen_ranks]),
    .rank_no_load_mr_after_refresh      (rank_no_load_mr_after_refresh[gen_ranks]),
    .rank_no_rfmpb_for_tpbr2pbr         (rank_no_rfmpb_for_tpbr2pbr[gen_ranks]),
    .rank_no_refpb_after_act            (rank_no_refpb_after_act[gen_ranks]),
    .rank_nop_after_refresh             (rank_nop_after_refresh[gen_ranks]),
//spyglass disable_block W528
//SMD: Variable 'gs_ts_lrank_enable_bits' set but not read
//SJ: Used under different ifdefs.
    .gs_ts_lrank_enable                 (gs_ts_lrank_enable_bits[gen_ranks]),
//spyglass enable_block W528
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
  // Only for MEMC_NUM_RANKS_1 and for assertions.
    .rank_ref_idle_timeout              (rank_ref_idle_timeout[gen_ranks]),
`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON
//----------------------------------------------
    .dh_bs_t_ccd                        (dh_bs_t_ccd),
    .dh_bs_wr2rd                        (dh_bs_wr2rd),
    .dh_bs_t_ccd_s                      (dh_bs_t_ccd_s),
    .dh_bs_wr2rd_s                      (dh_bs_wr2rd_s),
    .dh_gs_rd2wr                        (dh_gs_rd2wr),
    .reg_ddrc_rd2wr_s                   (reg_ddrc_rd2wr_s),
    .reg_ddrc_mrr2rd                    (reg_ddrc_mrr2rd),
    .reg_ddrc_mrr2wr                    (reg_ddrc_mrr2wr),
    .reg_ddrc_mrr2mrw                   (reg_ddrc_mrr2mrw),
    .gs_bs_blk_ccd_timer                (gs_bs_blk_ccd_timer[gen_ranks*NUM_BG_PER_RANK+:NUM_BG_PER_RANK]),
    .gs_bs_blk_wr2rd_timer              (gs_bs_blk_wr2rd_timer[gen_ranks*NUM_BG_PER_RANK+:NUM_BG_PER_RANK]),
    .gs_bs_blk_rd2wr_timer              (gs_bs_blk_rd2wr_timer[gen_ranks*NUM_BG_PER_RANK+:NUM_BG_PER_RANK]),
//----------------------------------------------
    .gsnx_op_is_zqcs                    (zq_calib_mr_cmd),
    .rank_nop_after_zqcs                (rank_nop_after_zqcs),
    .rank_nop_after_load_mr_norm        (rank_nop_after_load_mr_norm),
    .rank_selfref_wait_ref              (rank_selfref_wait_ref[gen_ranks]),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate statement
    .t_rfc_min_timer_bitor              (t_rfc_min_timer_bitor[gen_ranks])
//spyglass enable_block W528
   ,.te_rd_bank_pghit_vld_prefer        (te_rd_bank_pghit_vld_prefer)
   ,.te_wr_bank_pghit_vld_prefer        (te_wr_bank_pghit_vld_prefer)
   ,.te_gs_rank_wr_prefer               (te_gs_rank_wr_prefer[RANK_BITS-1:0])
   ,.te_gs_rank_rd_prefer               (te_gs_rank_rd_prefer[RANK_BITS-1:0])
);
    end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

assign  gs_dh_dbg_raa_cnt = rank_dbg_raa_cnt[dh_gs_dbg_raa_rank*DBG_RAA_CNT_WIDTH+:DBG_RAA_CNT_WIDTH];

gs_global_fsm
 #(
     .CHANNEL_NUM                        (CHANNEL_NUM)
    ,.RANK_BITS                          (RANK_BITS)
    ,.NUM_TOTAL_BANKS                    (NUM_TOTAL_BANKS)
    ,.BCM_VERIF_EN                       (BCM_VERIF_EN)
    ,.BCM_DDRC_N_SYNC                    (BCM_DDRC_N_SYNC)
    ,.NPORTS                             (NPORTS)
    ,.A_SYNC_TABLE                       (A_SYNC_TABLE)
    ,.CMD_DELAY_BITS                     (CMD_DELAY_BITS)
    ,.SELFREF_SW_WIDTH_INT               (SELFREF_SW_WIDTH_INT)
    ,.SELFREF_EN_WIDTH_INT               (SELFREF_EN_WIDTH_INT)
    ,.SELFREF_TYPE_WIDTH_INT             (SELFREF_TYPE_WIDTH_INT)
    ,.POWERDOWN_EN_WIDTH_INT             (POWERDOWN_EN_WIDTH_INT)
    ) gs_global_fsm (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .bsm_clk_en                         (bsm_clk_en    ),
    .bsm_clk_on                         (bsm_clk_on    ),
//  .dh_gs_skip_init                    (dh_gs_skip_init),
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .dh_gs_prefer_write                 (dh_gs_prefer_write),
    .dh_gs_rdwr_idle_gap                (dh_gs_rdwr_idle_gap),
    .dh_gs_powerdown_en                 (dh_gs_powerdown_en),
    .dh_gs_powerdown_to_x32             (dh_gs_powerdown_to_x32),
    .dh_gs_t_xp                         (dh_gs_t_xp),
    .dh_gs_dis_auto_ctrlupd_srx         (dh_gs_dis_auto_ctrlupd_srx),
    .dh_gs_ctrlupd_pre_srx              (dh_gs_ctrlupd_pre_srx),
    .reg_ddrc_selfref_sw                (reg_ddrc_selfref_sw),
    .reg_ddrc_hw_lp_en                  (reg_ddrc_hw_lp_en),
    .reg_ddrc_hw_lp_exit_idle_en        (reg_ddrc_hw_lp_exit_idle_en),
    .reg_ddrc_selfref_to_x32            (reg_ddrc_selfref_to_x32),
    .reg_ddrc_hw_lp_idle_x32            (reg_ddrc_hw_lp_idle_x32),
    .reg_ddrc_skip_dram_init            (reg_ddrc_skip_dram_init),
    .ddrc_reg_selfref_type              (ddrc_reg_selfref_type),
    .ih_busy                            (ih_busy),
    .hif_cmd_valid                      (hif_cmd_valid),
    .gsfsm_sr_co_if_stall               (gsfsm_sr_co_if_stall),
    .reg_ddrc_dfi_t_ctrl_delay          (reg_ddrc_dfi_t_ctrl_delay),
    .phy_dfi_phyupd_req                 (phy_dfi_phyupd_req),
    .reg_ddrc_dfi_phyupd_en             (reg_ddrc_dfi_phyupd_en),
    .phy_dfi_phymstr_req                (phy_dfi_phymstr_req),
    .reg_ddrc_dfi_phymstr_en            (reg_ddrc_dfi_phymstr_en),
    .cactive_in_ddrc_sync_or            (cactive_in_ddrc_sync_or),
    .cactive_in_ddrc_async              (cactive_in_ddrc_async),
    .csysreq_ddrc                       (csysreq_ddrc),
    .csysreq_ddrc_mux                   (csysreq_ddrc_mux),
    .csysmode_ddrc                      (csysmode_ddrc),
    .csysfrequency_ddrc                 (csysfrequency_ddrc),
    .csysdiscamdrain_ddrc               (csysdiscamdrain_ddrc),
    .csysfsp_ddrc                       (csysfsp_ddrc),
    .reg_ddrc_hwffc_mode                (reg_ddrc_hwffc_mode),
    .reg_ddrc_skip_zq_stop_start        (reg_ddrc_skip_zq_stop_start),
    .csysack_ddrc                       (csysack_ddrc),
    .cactive_ddrc                       (cactive_ddrc),
    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio),
    .dh_gs_selfref_en                   (dh_gs_selfref_en),
    .dh_gs_t_xsr                        (dh_gs_t_xsr),
    .reg_ddrc_t_ckesr                   (reg_ddrc_t_ckesr),
    .reg_ddrc_dfi_tlp_resp              (reg_ddrc_dfi_tlp_resp),
    .dfi_cmd_delay                      (dfi_cmd_delay),
    .block_t_xs                         (block_t_xs),
    .block_t_xs_dll                     (block_t_xs_dll),
    .dh_gs_read_latency                 (dh_gs_read_latency),
    .dh_gs_write_latency                (dh_gs_write_latency),
    .dh_gs_dis_dq                       (dh_gs_dis_dq),
    .gs_op_is_ref                       (gs_op_is_ref),
    .ddrc_co_perf_lpr_xact_when_critical(ddrc_co_perf_lpr_xact_when_critical),
    .ddrc_co_perf_hpr_xact_when_critical(ddrc_co_perf_hpr_xact_when_critical),
    .ddrc_co_perf_wr_xact_when_critical (ddrc_co_perf_wr_xact_when_critical),
    .ddrc_co_perf_rdwr_transitions      (ddrc_co_perf_rdwr_transitions),
    .ih_gs_xact_valid                   (ih_gs_xact_valid),
    .te_gs_any_vpr_timed_out            (te_gs_any_vpr_timed_out),
    .ih_gs_any_vpr_timed_out            (ih_gs_any_vpr_timed_out),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in gs_assertions module
    .rdhigh_critical                    (rdhigh_critical),
    .rdlow_critical                     (rdlow_critical),
    .wr_critical                        (wr_critical),
//spyglass enable_block W528
    .te_gs_any_vpw_timed_out            (te_gs_any_vpw_timed_out),
    .ih_gs_any_vpw_timed_out            (ih_gs_any_vpw_timed_out),
    .te_gs_wr_flush                     (te_gs_wr_flush),
    .te_gs_rd_flush                     (te_gs_rd_flush),
    .te_gs_rd_vld                       (te_gs_any_rd_pending),
    .te_gs_wr_vld                       (te_gs_any_wr_pending),
    .te_gs_rd_vld_ref_rdwr_switch       (te_gs_rd_vld_ref_rdwr_switch),
    .te_gs_wr_vld_ref_rdwr_switch       (te_gs_wr_vld_ref_rdwr_switch),
    .reg_ddrc_prefer_read               (reg_ddrc_prefer_read),
    .dh_gs_hpr_xact_run_length          (dh_gs_hpr_xact_run_length),
    .dh_gs_hpr_max_starve               (dh_gs_hpr_max_starve),
    .ih_gs_rdhigh_empty                 (ih_gs_rdhigh_empty),
    .ih_gs_rdlow_empty                  (ih_gs_rdlow_empty),
    .dh_gs_lpr_xact_run_length          (dh_gs_lpr_xact_run_length),
    .dh_gs_lpr_max_starve               (dh_gs_lpr_max_starve),
    .hif_go2critical_lpr                (hif_go2critical_lpr),
    .hif_go2critical_hpr                (hif_go2critical_hpr),
    .dh_gs_w_xact_run_length            (dh_gs_w_xact_run_length),
    .dh_gs_w_max_starve                 (dh_gs_w_max_starve),
    .hif_go2critical_wr                 (hif_go2critical_wr),
    .os_gs_rank_closed                  (os_gs_rank_closed),
    .hif_go2critical_l1_wr              (hif_go2critical_l1_wr ),
    .hif_go2critical_l2_wr              (hif_go2critical_l2_wr ),
    .hif_go2critical_l1_lpr             (hif_go2critical_l1_lpr),
    .hif_go2critical_l2_lpr             (hif_go2critical_l2_lpr),
    .hif_go2critical_l1_hpr             (hif_go2critical_l1_hpr),
    .hif_go2critical_l2_hpr             (hif_go2critical_l2_hpr),
    .os_gs_no_2ck_cmds_after_pre        (os_gs_no_2ck_cmds_after_pre),
    .timer_pulse_x1024                  (timer_pulse_x1024),
    .gs_op_is_rd_hi                     (gs_op_is_rd_hi),
    .gs_op_is_rd_lo                     (gs_op_is_rd_lo),
    .gs_op_is_wr                        (gs_op_is_wr),
    .global_block_cke_change            (global_block_cke_change),
    .rank_nop_after_refresh             (rank_nop_after_refresh),
    .end_init_ddr                       (end_init_ddr),
    .timer_pulse_x32                    (timer_pulse_x32),
    .timer_pulse_x32_dram               (timer_pulse_x32_dram),
    .refresh_required                   (|rank_refresh_required),
    .refresh_pending                    (|rank_refresh_pending),
    .refresh_required_early             (|refresh_required_early),
    .ctrlupd_req                        (ctrlupd_req),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    .wu_gs_enable_wr                    (wu_gs_enable_wr),
    .rank_selfref_wait_ref              (rank_selfref_wait_ref),
    .rank_nop_after_rfm                 (rank_nop_after_rfm),
    .gs_op_is_rfm                       (gs_op_is_rfm),
    .rank_nop_after_zqcs_gfsm           (rank_nop_after_zqcs_gfsm),
    .zq_calib_short_required            (gs_bs_zq_calib_short_required),
    .rank_nop_after_load_mr_norm        (rank_nop_after_load_mr_norm),
    .gs_pi_op_is_load_mr_norm           (gs_pi_op_is_load_mr_norm),
    .load_mr_norm_required              (load_mr_norm_required_to_fsm),
    .gs_os_wr_mode_early                (gs_os_wr_mode_early),
    .gs_bs_wr_mode_early                (gs_bs_wr_mode_early),
    .gs_wr_mode                         (gs_wr_mode),
    .reverse_priority                   (reverse_priority),
    .gs_te_pri_level                    (gs_te_pri_level),
    .gs_dh_hpr_q_state                  (gs_dh_hpr_q_state),
    .gs_dh_lpr_q_state                  (gs_dh_lpr_q_state),
    .gs_dh_w_q_state                    (gs_dh_w_q_state),
    .gs_pi_pads_powerdown               (gs_pi_pads_powerdown),
    .gs_pi_pads_selfref                 (gs_pi_pads_selfref),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .gs_op_is_enter_sr_lpddr            (gs_op_is_enter_sr_lpddr),
    .gs_op_is_exit_sr_lpddr             (gs_op_is_exit_sr_lpddr),
    .gs_op_is_enter_dsm                 (gs_op_is_enter_dsm),
    .gs_op_is_exit_dsm                  (gs_op_is_exit_dsm),
    .normal_ppt2_prepare                (normal_ppt2_prepare),            // Exit automatic lowpower state.
    .gsfsm_asr_to_sre_asr               (gsfsm_asr_to_sre_asr),
    .ddrc_reg_ppt2_burst_busy           (ddrc_reg_ppt2_burst_busy),
    .ppt2_asr_to_sre_asr                (ppt2_asr_to_sre_asr),
    .gsfsm_sr_entry_req                 (gsfsm_sr_entry_req),
    .gs_hw_mr_norm_busy                 (gs_hw_mr_norm_busy),
    .blk_pd_after_cas                   (blk_pd_after_cas),
    .blk_pd_after_wra                   (blk_pd_after_wra),
    .bs_gs_stop_clk_ok                  (bs_gs_stop_clk_ok),
    .gs_pi_stop_clk_ok                  (gs_pi_stop_clk_ok),
    .gs_ppt2_stop_clk_ok_norm           (gs_ppt2_stop_clk_ok_norm),
    .gs_pi_stop_clk_type                (gs_pi_stop_clk_type),
    .clock_stop_exited                  (clock_stop_exited),
    .wr_mode_early                      (wr_mode_early),
    .wr_mode                            (wr_mode),
    .normal_operating_mode              (normal_operating_mode),
    .rdwr_operating_mode                (rdwr_operating_mode_unused), // not used
    .init_operating_mode                (init_operating_mode),
    .gs_op_is_enter_powerdown           (gs_op_is_enter_powerdown),
    .gs_op_is_enter_selfref             (gs_op_is_enter_selfref),
    .gs_op_is_exit_powerdown            (gs_op_is_exit_powerdown),
    .gs_op_is_exit_selfref              (gs_op_is_exit_selfref),
    .enter_powerdown                    (enter_powerdown),
    .enter_selfref                      (enter_selfref),
    .exit_powerdown                     (exit_powerdown),
    .exit_selfref                       (exit_selfref),
    .exit_selfref_ready                 (exit_selfref_ready),
    .gs_dh_selfref_cam_not_empty        (gs_dh_selfref_cam_not_empty),
    .gs_dh_selfref_state                (gs_dh_selfref_state),
    .sr_mrrw_en                         (sr_mrrw_en),
    .enter_selfref_related_state        (enter_selfref_related_state),
    .gs_dh_operating_mode               (gs_dh_operating_mode),
    .gs_dh_global_fsm_state             (gs_dh_global_fsm_state),
    .close_pages                        (gs_bs_close_pages),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in ts_assertions module
    .powerdown_idle_timer               (powerdown_idle_timer),
//spyglass enable_block W528
    // DFI LP I/F
    .reg_ddrc_dfi_lp_en_pd              (reg_ddrc_dfi_lp_en_pd),
    .reg_ddrc_dfi_lp_en_sr              (i_reg_ddrc_dfi_lp_en_sr),
    .reg_ddrc_dfi_lp_en_dsm             (reg_ddrc_dfi_lp_en_dsm),
    .gfsm_dfilp_trig_pde                (gfsm_dfilp_trig_pde),
    .gfsm_dfilp_trig_pdx                (gfsm_dfilp_trig_pdx),
    .gfsm_dfilp_trig_sre                (gfsm_dfilp_trig_sre),
    .gfsm_dfilp_trig_srx                (gfsm_dfilp_trig_srx),
    .gfsm_dfilp_trig_dsme               (gfsm_dfilp_trig_dsme),
    .gfsm_dfilp_trig_dsmx               (gfsm_dfilp_trig_dsmx),
    .dfilp_pde_done                     (dfilp_pde_done),
    .dfilp_pde_aborted                  (dfilp_pde_aborted),
    .dfilp_pdx_aborted                  (dfilp_pdx_aborted),
    .dfilp_pdx_done                     (dfilp_pdx_done),
    .dfilp_sre_done                     (dfilp_sre_done),
    .dfilp_sre_aborted                  (dfilp_sre_aborted),
    .dfilp_srx_done                     (dfilp_srx_done),
    .dfilp_dsme_done                    (dfilp_dsme_done),
    .dfilp_dsme_aborted                 (dfilp_dsme_aborted),
    .dfilp_dsmx_done                    (dfilp_dsmx_done),
    .dfilp_active                       (dfilp_active),
    .gs_pi_dfi_lp_changing              (gs_pi_dfi_lp_changing),
    .gs_pi_data_pipeline_empty          (gs_pi_data_pipeline_empty),
    .gs_pi_odt_pending                  (gs_pi_odt_pending),
    .gs_op_is_rd                        (gs_op_is_rd),
    .dh_gs_rd2wr                        (dh_gs_rd2wr),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .dh_gs_stay_in_selfref              (dh_gs_stay_in_selfref),
    .dh_gs_t_cmdcke                     (dh_gs_t_cmdcke),
    .reg_ddrc_dsm_en                    (reg_ddrc_dsm_en),
    .reg_ddrc_t_pdn                     (reg_ddrc_t_pdn),
    .reg_ddrc_t_xsr_dsm_x1024           (reg_ddrc_t_xsr_dsm_x1024),
    .reg_ddrc_t_csh                     (reg_ddrc_t_csh),
    .gsfsm_dis_dq                       (gsfsm_dis_dq),
    .gs_dram_st_sr                      (gs_dram_st_sr),
    .gs_phymstr_sre_req                 (gs_phymstr_sre_req),
    .gs_phymstr_clr_lp_req              (gs_phymstr_clr_lp_req),
    .dh_gs_dis_cam_drain_selfref        (reg_ddrc_dis_cam_drain_selfref)
    ,.dh_gs_lpddr4_sr_allowed           (reg_ddrc_lpddr4_sr_allowed)
    ,.gs_bs_sre_stall                   (gs_bs_sre_stall)
    ,.gs_bs_sre_hw_sw                   (gs_bs_sre_hw_sw)
    ,.gsfsm_sr_exit_req                 (gsfsm_sr_exit_req)
    ,.hwffc_dfi_init_start              (hwffc_dfi_init_start)
    ,.hwffc_dfi_frequency               (hwffc_dfi_frequency)
    ,.hwffc_dfi_freq_fsp                (hwffc_dfi_freq_fsp)
    ,.dfi_init_complete_hwffc           (dfi_init_complete_hwffc)
    ,.hwffc_in_progress                 (hwffc_in_progress)
    ,.hwffc_freq_change                 (hwffc_freq_change)
    ,.hwffc_operating_mode              (hwffc_operating_mode)
    ,.hwffc_target_freq_en              (hwffc_target_freq_en)
    ,.hwffc_target_freq                 (hwffc_target_freq)
    ,.hwffc_target_freq_init            (hwffc_target_freq_init)
    ,.reg_ddrc_target_vrcg              (reg_ddrc_target_vrcg)
    ,.reg_ddrc_hwffc_en                 (reg_ddrc_hwffc_en)
    ,.reg_ddrc_target_frequency         (reg_ddrc_target_frequency)
    ,.hwffc_vrcg                        (hwffc_vrcg)
    ,.hwffc_no_other_load_mr            (hwffc_no_other_load_mr)
    ,.hwffc_mr_update_done              (hwffc_mr_update_done)
    ,.hwffc_st_mr_vrcg                  (hwffc_st_mr_vrcg)
    ,.hwffc_mr_update_start             (hwffc_mr_update_start)
    ,.reg_ddrc_init_fsp                 (reg_ddrc_init_fsp)
    ,.hwffc_bgzq_stopped                (hwffc_bgzq_stopped)
    ,.hwffc_zq_restart                  (hwffc_zq_restart)
    ,.gs_wck_stop_ok                    (gs_wck_stop_ok)
    ,.phymstr_active                    (phymstr_active)
    ,.reg_ddrc_dvfsq_enable             (reg_ddrc_dvfsq_enable)
    ,.reg_ddrc_dvfsq_enable_next        (reg_ddrc_dvfsq_enable_next)
    ,.reg_ddrc_init_vrcg                (reg_ddrc_init_vrcg)
    ,.hwffc_mask_dfireq                 (hwffc_mask_dfireq)
    ,.hwffc_dis_zq_derate               (hwffc_dis_zq_derate)
    ,.hwffc_refresh_update_pulse        (hwffc_refresh_update_pulse)
    ,.hwffc_hif_wd_stall                (hwffc_hif_wd_stall)
    ,.ddrc_xpi_port_disable_req         (ddrc_xpi_port_disable_req)
    ,.ddrc_xpi_clock_required           (ddrc_xpi_clock_required)
    ,.xpi_ddrc_port_disable_ack         (xpi_ddrc_port_disable_ack)
    ,.xpi_ddrc_wch_locked               (xpi_ddrc_wch_locked)
    ,.reg_ddrc_opt_wrcam_fill_level     (reg_ddrc_opt_wrcam_fill_level)
    ,.reg_ddrc_delay_switch_write       (reg_ddrc_delay_switch_write)
    ,.te_bs_rd_page_hit                 (te_bs_rd_page_hit)       // banks with reads pending to open pages
    ,.te_bs_rd_valid                    (te_bs_rd_valid   )       // banks with reads pending
    ,.te_bs_wr_page_hit                 (te_bs_wr_page_hit)       // banks with writes pending to open pages
    ,.te_bs_wr_valid                    (te_bs_wr_valid   )       // banks with writes pending
    ,.te_ts_vpw_valid                   (te_ts_vpw_valid)        // banks with exvpw pending
    ,.te_ts_vpr_valid                   (te_ts_vpr_valid)        // banks with exvpr pending
    ,.te_rws_wr_col_bank                (te_rws_wr_col_bank)
    ,.te_rws_rd_col_bank                (te_rws_rd_col_bank)
    ,.bank_wr_activated_early           (bank_wr_activated_early)
    ,.bank_activated_early              (bank_activated_early)
    ,.global_block_rd_early             (global_block_rd_early)
    ,.wr_cam_up_highth                  (wr_cam_up_highth)
    ,.wr_cam_up_lowth                   (wr_cam_up_lowth)
    ,.wrecc_cam_up_highth               (wrecc_cam_up_highth)
    ,.wrecc_cam_up_lowth                (wrecc_cam_up_lowth)
    ,.wrecc_cam_up_highth_loaded        (wrecc_cam_up_highth_loaded)
    ,.wr_cam_up_wrecc_highth            (wr_cam_up_wrecc_highth)
    ,.te_gs_wrecc_ntt                   (te_gs_wrecc_ntt)
    ,.gs_te_force_btt                   (gs_te_force_btt)
//    ,.gs_op_is_wr                       (gs_te_op_is_wr)
    ,.wr_pghit_up_thresh                (wr_pghit_up_thresh)
    ,.rd_pghit_up_thresh                (rd_pghit_up_thresh)
    ,.delay_switch_write_state          (delay_switch_write_state)
    ,.rd_more_crit                      (rd_more_crit)
    ,.wr_more_crit                      (wr_more_crit)
    ,.any_vpr_timed_out                 (gs_ts_any_vpr_timed_out)
    ,.any_vpw_timed_out                 (gs_ts_any_vpw_timed_out)
    ,.dqsosc_pd_forbidden               (dqsosc_pd_forbidden)
    ,.dqsosc_required                   (dqsosc_required)
    ,.dqsosc_stopped                    (dqsosc_stopped)
    ,.powerdown_operating_mode          (powerdown_operating_mode)
   ,.ddrc_reg_ctrlupd_burst_busy        (ddrc_reg_ctrlupd_burst_busy)
);

gs_init_ddr_fsm
 #(

    .SHARED_AC                          (SHARED_AC)
   ,.CHANNEL_NUM                        (CHANNEL_NUM)

    )
 gs_init_ddr_fsm (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .dh_gs_mr                           (dh_gs_mr),
    .dh_gs_emr                          (dh_gs_emr),
    .dh_gs_emr2                         (dh_gs_emr2),
    .dh_gs_emr3                         (dh_gs_emr3),
    .reg_ddrc_t_mr                      (reg_ddrc_t_mr),
    .reg_ddrc_dfi_reset_n               (reg_ddrc_dfi_reset_n), // controls dfi_reset_n
    .dh_gs_per_bank_refresh             (per_bank_refresh),

    //.dh_gs_lpddr4                       (dh_gs_lpddr4),
    .dh_gs_lpddr4                       (1'b1),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .gs_dh_operating_mode               (gs_dh_operating_mode),
    .phy_dfi_init_complete              (dfi_init_complete_init),
    .dh_gs_dfi_init_complete_en         (dh_gs_dfi_init_complete_en),
    .dh_gs_t_rfc_min                    (t_rfc_min_upd),
    .dh_gs_pre_cke_x1024                (dh_gs_pre_cke_x1024),
    .dh_gs_post_cke_x1024               (dh_gs_post_cke_x1024),
    .dh_gs_sw_init_int                  (dh_gs_sw_init_int),
    .gs_sw_init_int_possible            (gs_sw_init_int_possible),
    .timer_pulse_x32                    (timer_pulse_x32),
    .timer_pulse_x1024                  (timer_pulse_x1024),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    .gs_pi_ctrlupd_req                  (gs_pi_ctrlupd_req),

    .gs_dh_init_curr_state              (gs_dh_init_curr_state),
    .gs_dh_init_next_state              (gs_dh_init_next_state),
    .init_cs_n                          (init_cs_n),
    .gs_pi_init_cke                     (gs_pi_init_cke),
    .gs_pi_op_is_load_mode              (gs_pi_op_is_load_mode_init),
    .dh_gs_zq_resistor_shared           (dh_gs_zq_resistor_shared),
    .start_zqcs_timer                   (start_zqcs_timer),
    .dfi_reset_n_in                     (dfi_reset_n_in),
    .dfi_reset_n_ref                    (dfi_reset_n_ref),
    .init_mr_done_in                    (init_mr_done_in),
    .init_mr_done_out                   (init_mr_done_out),
    .dh_gs_t_zq_long_nop                (dh_gs_t_zq_long_nop),
    .dh_gs_t_zq_short_nop               (dh_gs_t_zq_short_nop),
    .init_mpc_zq_start                  (init_mpc_zq_start),
    .init_mpc_zq_latch                  (init_mpc_zq_latch),
    .gs_pi_dram_rst_n                   (gs_pi_dram_rst_n), // ddrc to dram active low reset
    .init_refresh                       (init_refresh),
    .gs_pi_mrs_a                        (gs_pi_mrs_a_init),
    .start_refresh_timer                (start_refresh_timer),
    .gs_pi_init_in_progress             (gs_pi_init_in_progress),
    .reg_ddrc_skip_dram_init            (reg_ddrc_skip_dram_init),
    .end_init_ddr                       (end_init_ddr)
);

gs_zq_calib
 # (
      .NUM_RANKS                  (NUM_RANKS)
) gs_zq_calib (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .dh_gs_zq_reset                     (dh_gs_zq_reset),
    .dh_gs_t_zq_reset_nop               (dh_gs_t_zq_reset_nop),
    .gs_dh_zq_reset_busy                (gs_dh_zq_reset_busy),
    .gs_zq_calib_active_ranks           (gs_zq_calib_active_ranks),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .dh_gs_dis_srx_zqcl                 (dh_gs_dis_srx_zqcl),
    .dh_gs_dis_srx_zqcl_hwffc           (dh_gs_dis_srx_zqcl_hwffc),
    .reg_ddrc_dvfsq_enable              (reg_ddrc_dvfsq_enable),
    .dh_gs_zq_resistor_shared           (dh_gs_zq_resistor_shared),
    .gs_dh_global_fsm_state             (gs_dh_global_fsm_state),
    .timer_pulse_x1024_dram             (timer_pulse_x1024_dram),
    .dh_gs_zq_calib_short               (dh_gs_zq_calib_short),
    .gs_dh_zq_calib_short_busy          (gs_dh_zq_calib_short_busy),
    .dh_gs_dis_auto_zq                  (dh_gs_dis_auto_zq),
    .dh_gs_t_zq_long_nop                (dh_gs_t_zq_long_nop),
    .dh_gs_t_zq_short_nop               (dh_gs_t_zq_short_nop),
    .dh_gs_t_zq_short_interval_x1024    (dh_gs_t_zq_short_interval_x1024),
    .start_zqcs_timer                   (start_zqcs_timer),
    .gsnx_op_is_zqcs                    (zq_calib_mr_cmd),
    .gs_other_cs_n                      (gs_other_cs_n),
    .zq_reset_req_on                    (zq_reset_req_on),
    .zq_lat                             (zq_lat),
    .block_zqlat                        (block_zqlat),
    .sr_mrrw_en                         (sr_mrrw_en),
    .dh_gs_odtloff                      (dh_gs_odtloff),
    .gs_op_is_wr                        (gs_op_is_wr),
    .hwffc_zq_restart                   (hwffc_zq_restart),
    .hwffc_bgzq_stopped                 (hwffc_bgzq_stopped),
    .hwffc_in_progress                  (hwffc_in_progress),
    .reg_ddrc_hwffc_mode                (reg_ddrc_hwffc_mode),
    .zqcl_due_to_sr_exit                (zqcl_due_to_sr_exit),
    .zqcl_mask_cmds_zq_resistor_shared  (zqcl_mask_cmds_zq_resistor_shared),
    .zqcl_due_to_sr_exit_ext_block_new_zq      (zqcl_due_to_sr_exit_ext_block_new_zq),

    .rank_nop_after_zqcs                (rank_nop_after_zqcs),
    .rank_nop_after_zqcs_gfsm           (rank_nop_after_zqcs_gfsm),
    .zq_calib_short_required            (gs_bs_zq_calib_short_required)

  , .ppt2_asr_to_sre_asr               (ppt2_asr_to_sre_asr)
    );

gs_load_mr
 #(
    .SHARED_AC                          (SHARED_AC)
   ,.CHANNEL_NUM                        (CHANNEL_NUM)
    )
gs_load_mr (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .reg_ddrc_t_mr                      (reg_ddrc_t_mr),
    .dh_gs_t_vrcg_enable                (reg_ddrc_t_vrcg_enable),
    .dh_gs_t_vrcg_disable               (reg_ddrc_t_vrcg_disable),
    .dh_gs_t_zq_reset_nop               (dh_gs_t_zq_reset_nop),
    .reg_ddrc_t_zq_stop                 (reg_ddrc_t_zq_stop),
    .dh_gs_skip_mrw_odtvref             (reg_ddrc_skip_mrw_odtvref),
    .dh_gs_zq_interval                  (reg_ddrc_zq_interval),
    .dh_gs_mr_wr                        (dh_gs_mr_wr),
    .dh_gs_mr_addr                      (dh_gs_mr_addr),
    .dh_gs_mr_data                      (dh_gs_mr_data),
    .dh_gs_mr_rank                      (dh_gs_mr_rank),
    .gs_dh_mr_wr_busy                   (gs_dh_mr_wr_busy),
    .gs_dh_global_fsm_state             (gs_dh_global_fsm_state),
    .sr_mrrw_en                         (sr_mrrw_en),
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .zqcl_due_to_sr_exit_ext            (zqcl_due_to_sr_exit_ext),
    .zq_calib_short_required            (gs_bs_zq_calib_short_required & {NUM_RANKS{((gs_dh_operating_mode[1:0] != 2'b11) ||(sr_mrrw_en))}}),
    .zq_reset_req_on                    (zq_reset_req_on),
    .zq_calib_mr_cmd                    (zq_calib_mr_cmd),

    .load_mrw_reset_norm                (load_mrw_reset_norm),
    .zq_lat                             (zq_lat),
    .dh_gs_mr_type                      (dh_gs_mr_type),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .mrr_op_on                          (mrr_op_on),
    .dh_gs_derate_enable                (dh_gs_derate_enable),
    .gs_zq_calib_active_ranks           (gs_zq_calib_active_ranks),
    .dh_gs_mr                           (dh_gs_mr),
    .dh_gs_emr                          (dh_gs_emr),
    .dh_gs_emr2                         (dh_gs_emr2),
    .dh_gs_mr6                          (dh_gs_mr6),
    .dh_gs_mr22                         (dh_gs_mr22),
    .dh_gs_emr3                         (dh_gs_emr3),
    .dh_gs_mr4                          (dh_gs_mr4),
    .dh_gs_mr5                          (dh_gs_mr5),
    .dh_gs_dfi_phyupd_en                (reg_ddrc_dfi_phyupd_en),
    .phy_dfi_phyupd_req                 (phy_dfi_phyupd_req_r),
    .ddrc_dfi_phyupd_ack                (ddrc_dfi_phyupd_ack),
    // JIRA___ID: Bug4257 - Connect with gs_global_fsm
    .hwffc_mr_update_done               (hwffc_mr_update_done),
    .hwffc_st_mr_vrcg                   (hwffc_st_mr_vrcg),
    .hwffc_mr_update_start              (hwffc_mr_update_start),
    .hwffc_fsp                          (hwffc_dfi_freq_fsp),
    .reg_ddrc_hwffc_mode                (reg_ddrc_hwffc_mode),
    .hwffc_no_other_load_mr             (hwffc_no_other_load_mr),
    .hwffc_vrcg                         (hwffc_vrcg),
    .gs_hw_mr_norm_busy                 (gs_hw_mr_norm_busy),
    .load_mr_norm                       (load_mr_norm),
    .load_mr_norm_required              (gs_bs_load_mr_norm_required), // goes to gs_next_xact and to bsm
    .load_mr_norm_required_to_fsm       (load_mr_norm_required_to_fsm), // connected to gs_global_fsm
    .dh_gs_mr4_req                      (dh_gs_mr4_req),
    .dh_gs_mr4_req_rank                 (dh_gs_mr4_req_rank),
    .rank_nop_after_load_mr_norm        (rank_nop_after_load_mr_norm),
    .load_mpc_zq_start                  (load_mpc_zq_start),
    .load_mpc_zq_latch                  (load_mpc_zq_latch),
    .mr4_req_o                          (mr4_req_o),
    .dqsosc_loadmr_upd_req_p           (dqsosc_loadmr_upd_req_p),
    .loadmr_dqsosc_upd_done_p          (loadmr_dqsosc_upd_done_p),
    .dqsosc_loadmr_rank                (dqsosc_loadmr_rank),
    .dqsosc_loadmr_a                   (dqsosc_loadmr_a),
    .dqsosc_loadmr_mpc                 (dqsosc_loadmr_mpc),
    .dqsosc_loadmr_mrr                 (dqsosc_loadmr_mrr),
    .dqsosc_loadmr_snoop_en            (dqsosc_loadmr_snoop_en),
    .normal_ppt2_prepare               (normal_ppt2_prepare),
    .gs_pi_mrr_snoop_en                (gs_pi_mrr_snoop_en),
    .load_mpc_dqsosc_start             (gs_mpc_dqsosc_start),
    .ppt2_stop_clk_req                 (ppt2_stop_clk_req),
    .gs_pi_mrs_a_norm                  (gs_pi_mrs_a_norm)
    ,.reg_ddrc_t_pgm_x1_x1024          (reg_ddrc_t_pgm_x1_x1024)
    ,.reg_ddrc_t_pgm_x1_sel            (reg_ddrc_t_pgm_x1_sel)
    ,.reg_ddrc_t_pgmpst_x32            (reg_ddrc_t_pgmpst_x32)
    ,.reg_ddrc_t_pgm_exit              (reg_ddrc_t_pgm_exit)
    ,.reg_ddrc_ppr_en                  (reg_ddrc_ppr_en)
    ,.ddrc_reg_ppr_done                (ddrc_reg_ppr_done)
    ,.reg_ddrc_ppr_pgmpst_en           (reg_ddrc_ppr_pgmpst_en)
    ,.timer_pulse_x1024                (timer_pulse_x1024)

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
    ,.reg_ddrc_ctrlupd_after_dqsosc    (reg_ddrc_ctrlupd_after_dqsosc)
`endif
`endif
);

gs_phymstr
 #(
    .RANK_BITS                             (RANK_BITS)
   ,.SELFREF_SW_WIDTH_INT  (SELFREF_SW_WIDTH_INT)
    )
gs_phymstr (
   .co_yy_clk                              (co_yy_clk),
   .core_ddrc_rstn                         (core_ddrc_rstn),
   .phy_dfi_phymstr_req                    (phy_dfi_phymstr_req),
   .phy_dfi_phymstr_cs_state               (phy_dfi_phymstr_cs_state),
   .phy_dfi_phymstr_state_sel              (phy_dfi_phymstr_state_sel),
   .phy_dfi_phymstr_type                   (phy_dfi_phymstr_type),
   .ddrc_dfi_phymstr_ack                   (ddrc_dfi_phymstr_ack),
   .gs_phymstr_lp_ack                      (dfi_lp_ctrl_ack),
   .st_lp_e_ack_check                      (st_lp_e_ack_check),
   .gs_phymstr_dram_st_sr                  (gs_dram_st_sr),
   .gs_ctrlupd_req                         (ctrlupd_req),
   .gs_phymstr_clr_lp_req                  (gs_phymstr_clr_lp_req),
   .gs_phymstr_sre_req                     (gs_phymstr_sre_req),
   .gs_phymstr_mask_dfilp                  (gs_phymstr_mask_dfilp),
   .dh_gs_phymstr_en                       (reg_ddrc_dfi_phymstr_en),
   .reg_ddrc_selfref_sw                    (reg_ddrc_selfref_sw),
   .reg_ddrc_hw_lp_en                      (reg_ddrc_hw_lp_en),
   .csysreq_ddrc_mux                       (csysreq_ddrc_mux),
   .hwffc_mask_dfireq                      (hwffc_mask_dfireq),
   .dfi_init_start                         (dfi_init_start),
   .reg_ddrc_dfi_t_ctrl_delay              (reg_ddrc_dfi_t_ctrl_delay),
   .clock_stop_exited                      (clock_stop_exited),
   .gs_dfi_t_wrdata_delay_cnt              (gs_dfi_t_wrdata_delay_cnt)
   ,.zqcl_due_to_sr_exit_ext               (zqcl_due_to_sr_exit_ext)
   ,.rank_nop_after_zqcs_gfsm              (rank_nop_after_zqcs_gfsm)
   ,.gs_pi_odt_pending                     (gs_pi_odt_pending)
   ,.gs_pi_op_is_load_mr_norm              (gs_pi_op_is_load_mr_norm)
   ,.rank_nop_after_load_mr_norm           (rank_nop_after_load_mr_norm)
   ,.load_mr_norm_required                 (gs_bs_load_mr_norm_required)
   ,.gs_pi_data_pipeline_empty             (gs_pi_data_pipeline_empty)
   ,.dh_gs_stay_in_selfref                 (dh_gs_stay_in_selfref)
   ,.dh_gs_lpddr4                          (dh_gs_lpddr4)
   ,.gs_wck_stop_ok                        (gs_wck_stop_ok)
   ,.gsfsm_sr_exit_req                     (gsfsm_sr_exit_req)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used only for HWFFC configs in RTL but output must always exist (used in TB)
   ,.phymstr_active                        (phymstr_active)
//spyglass enable_block W528
   ,.no_sr_mrrw_due_to_phymstr             (no_sr_mrrw_due_to_phymstr)
   ,.ddrc_reg_ctrlupd_burst_busy           (ddrc_reg_ctrlupd_burst_busy)
);

gs_wck
 #(
   .NUM_RANKS                       (NUM_RANKS),
   .CMD_DELAY_BITS                  (CMD_DELAY_BITS)
) gs_wck (
   .core_ddrc_core_clk              (co_yy_clk),
   .core_ddrc_rstn                  (core_ddrc_rstn),
   .gs_rdwr_cs_n                    (gs_rdwr_cs_n),
   .gs_other_cs_n                   (gs_other_cs_n),
   .gs_op_is_rd                     (gs_op_is_rd),
   .gs_op_is_wr                     (gs_op_is_wr),
   .gs_cas_ws_req                   (gs_cas_ws_req),
   .gs_op_is_load_mode              (gs_op_is_load_mode),
   .gs_pi_mrr                       (gs_pi_mrr),
   .gs_pi_mrr_ext                   (gs_pi_mrr_ext),
   .gs_op_is_enter_powerdown        (gs_op_is_enter_powerdown),
   .gs_op_is_enter_selfref          (gs_op_is_enter_selfref),
   .gs_op_is_enter_dsm              (gs_op_is_enter_dsm),
   .gs_op_is_cas_ws_off             (gs_op_is_cas_ws_off),
   .dfi_cmd_delay                   (dfi_cmd_delay),
   .dh_gs_read_latency              (dh_gs_read_latency),
   .dh_gs_write_latency             (dh_gs_write_latency),
   .reg_ddrc_lpddr5                 (reg_ddrc_lpddr5),
   .reg_ddrc_bank_org               (reg_ddrc_bank_org),
   .reg_ddrc_frequency_ratio        (dh_gs_frequency_ratio),
   .reg_ddrc_dfi_tphy_wrlat         (reg_ddrc_dfi_tphy_wrlat),
   .reg_ddrc_dfi_t_rddata_en        (reg_ddrc_dfi_t_rddata_en),
   .reg_ddrc_wck_on                 (reg_ddrc_wck_on),
   .reg_ddrc_dfi_twck_delay         (reg_ddrc_dfi_twck_delay),
   .reg_ddrc_dfi_twck_en_rd         (reg_ddrc_dfi_twck_en_rd),
   .reg_ddrc_dfi_twck_en_wr         (reg_ddrc_dfi_twck_en_wr),
   .dh_gs_active_ranks              (dh_gs_active_ranks),
   .reg_ddrc_dfi_twck_en_fs         (reg_ddrc_dfi_twck_en_fs),
   .reg_ddrc_dfi_twck_dis           (reg_ddrc_dfi_twck_dis),
   .reg_ddrc_dfi_twck_fast_toggle   (reg_ddrc_dfi_twck_fast_toggle),
   .reg_ddrc_dfi_twck_toggle        (reg_ddrc_dfi_twck_toggle),
   .reg_ddrc_dfi_twck_toggle_cs     (reg_ddrc_dfi_twck_toggle_cs),
   .reg_ddrc_dfi_twck_toggle_post   (reg_ddrc_dfi_twck_toggle_post),
   .reg_ddrc_dfi_twck_toggle_post_rd_en   (reg_ddrc_dfi_twck_toggle_post_rd_en),
   .reg_ddrc_dfi_twck_toggle_post_rd      (reg_ddrc_dfi_twck_toggle_post_rd),
   .gs_wck_stop_ok                  (gs_wck_stop_ok),
   .gs_dfi_wck_cs                   (gs_dfi_wck_cs),
   .gs_dfi_wck_en                   (gs_dfi_wck_en),
   .gs_dfi_wck_toggle               (gs_dfi_wck_toggle)
);


// In this configuration, physical_rank always equal to logical rank (non 3DS)
assign  physical_rank_refresh_required              = rank_refresh_required;
assign  physical_rank_speculative_ref               = rank_speculative_ref;
assign  physical_rank_no_refresh_after_refresh      = rank_no_refresh_after_refresh;
assign  physical_rank_no_load_mr_after_refresh      = rank_no_load_mr_after_refresh;
assign  physical_rank_os_gs_rank_closed             = os_gs_rank_closed;
assign  logical_rank_os_gs_rank_closed_for_ref      = os_gs_rank_closed;
assign  physical_rank_block_mrr                     = rank_block_mrr;
assign  physical_rank_nop_after_refresh             = rank_nop_after_refresh;

assign  gs_bs_bank_speculative_ref                  = bank_speculative_ref;

  gs_dqsosc
  
    U_gs_dqsosc(
     .co_yy_clk                              (co_yy_clk)
     ,.core_ddrc_rstn                         (core_ddrc_rstn)
     ,.reg_ddrc_lpddr4                        (dh_gs_lpddr4)
     ,.reg_ddrc_lpddr5                        (reg_ddrc_lpddr5)
     ,.reg_ddrc_t_mrr                         (reg_ddrc_t_mr)//
     ,.reg_ddrc_active_ranks                  (dh_gs_active_ranks)// populated DRAM ranks
     ,.reg_ddrc_rank_gap                      (dh_gs_diff_rank_rd_gap)
     ,.reg_ddrc_frequency_ratio               (dh_gs_frequency_ratio)
     ,.reg_ddrc_dqsosc_enable                 (reg_ddrc_dqsosc_enable & ~hwffc_in_progress)
     ,.reg_ddrc_t_osco                        (reg_ddrc_t_osco)
     ,.reg_ddrc_dqsosc_runtime                (reg_ddrc_dqsosc_runtime)
     ,.reg_ddrc_wck2dqo_runtime               (reg_ddrc_wck2dqo_runtime)
     ,.reg_ddrc_dqsosc_interval               (reg_ddrc_dqsosc_interval)
     ,.reg_ddrc_dqsosc_interval_unit          (reg_ddrc_dqsosc_interval_unit)
     ,.reg_ddrc_dis_dqsosc_srx                (reg_ddrc_dis_dqsosc_srx)
     ,.dqsosc_state                           (dqsosc_state)
     ,.dqsosc_running_lpddr5                  (dqsosc_running)
     ,.dqsosc_per_rank_stat                   (dqsosc_per_rank_stat)
     ,.timer_pulse_x1024_p                    (timer_pulse_x1024)
     ,.normal_operating_mode                  (normal_operating_mode)
     ,.gs_dh_global_fsm_state                 (gs_dh_global_fsm_state)
     ,.dqsosc_pd_forbidden                    (dqsosc_pd_forbidden)
     ,.dqsosc_required                        (dqsosc_required)
     ,.powerdown_operating_mode               (powerdown_operating_mode)
     ,.dqsosc_loadmr_upd_req_p                (dqsosc_loadmr_upd_req_p)//Active high pulse
     ,.loadmr_dqsosc_upd_done_p               (loadmr_dqsosc_upd_done_p)
     ,.dqsosc_block_other_cmd                 (dqsosc_block_other_cmd)
     ,.dqsosc_loadmr_rank                     (dqsosc_loadmr_rank)
     ,.ddrc_co_perf_op_is_dqsosc_mpc_w        (ddrc_co_perf_op_is_dqsosc_mpc_w)
     ,.ddrc_co_perf_op_is_dqsosc_mrr_w        (ddrc_co_perf_op_is_dqsosc_mrr_w)

     ,.hwffc_in_progress                      (hwffc_in_progress)
     ,.dqsosc_stopped                         (dqsosc_stopped)
     ,.dqsosc_loadmr_a                        (dqsosc_loadmr_a)
     ,.dqsosc_loadmr_mpc                      (dqsosc_loadmr_mpc)
     ,.dqsosc_loadmr_mrr                      (dqsosc_loadmr_mrr)
     ,.dqsosc_loadmr_snoop_en                 (dqsosc_loadmr_snoop_en)
);


`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
gs_assertions
 # (
) gs_assertions (
    .clk                                (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .gs_dh_operating_mode               (gs_dh_operating_mode),
    .gs_pi_stop_clk_ok                  (gs_pi_stop_clk_ok),

    .pi_gs_ctrlupd_ok                   (pi_gs_ctrlupd_ok),
    .gs_pi_ctrlupd_req                  (gs_pi_ctrlupd_req),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),

    .block_t_xs                         (block_t_xs),
    .block_t_xs_dll                     (block_t_xs_dll),
    .dh_gs_mr_wr                        (dh_gs_mr_wr),
    .dh_gs_mr_type                      (dh_gs_mr_type),
    .dh_gs_mr_addr                      (dh_gs_mr_addr),
    .dh_gs_mr_data                      (dh_gs_mr_data),

    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .dh_gs_rfm_en                       (dh_gs_rfm_en),
    .dh_gs_dis_mrrw_trfc                (dh_gs_dis_mrrw_trfc),
    .t_rfc_min_timer_bitor              (t_rfc_min_timer_bitor),
    .gs_pi_op_is_load_mr_norm           (gs_pi_op_is_load_mr_norm),

    .curr_global_fsm_state              (gs_dh_global_fsm_state),
    .next_global_fsm_state              (gs_global_fsm.next_state),
    .prev_global_fsm_state              (gs_global_fsm.current_state_prev),
    .dh_gs_prefer_write                 (dh_gs_prefer_write),
    .te_gs_any_vpr_timed_out            (te_gs_any_vpr_timed_out),
    .ih_gs_any_vpr_timed_out            (ih_gs_any_vpr_timed_out),
    .rdhigh_critical                    (rdhigh_critical),
    .rdlow_critical                     (rdlow_critical),
    .wr_critical                        (wr_critical),
    .wr_mode                            (wr_mode),
    .te_gs_wr_flush                     (te_gs_wr_flush),
    .te_gs_rd_flush                     (te_gs_rd_flush),
    .gs_dh_hpr_q_state                  (gs_dh_hpr_q_state),
    .gs_dh_w_q_state                    (gs_dh_w_q_state),
    .te_gs_any_vpw_timed_out            (te_gs_any_vpw_timed_out),
    .ih_gs_any_vpw_timed_out            (ih_gs_any_vpw_timed_out),
    .te_gs_rd_vld                       (te_gs_any_rd_pending),
    .te_gs_wr_vld                       (te_gs_any_wr_pending),
    .rt_gs_empty                        (rt_gs_empty),
    .mr_gs_empty                        (mr_gs_empty_w),
    .min_ctrlupd_timer                  (min_ctrlupd_timer),
    .ih_gs_xact_valid                   (ih_gs_xact_valid),

    .refresh_required_early             (refresh_required_early),
    .rank_nop_after_refresh             (rank_nop_after_refresh),
    .rank_speculative_ref               (rank_speculative_ref),
    .os_gs_rank_closed                  (os_gs_rank_closed),
    .os_gs_act_lo_vld                   (os_gs_act_lo_vld),
    .os_gs_act_hi_vld                   (os_gs_act_hi_vld),
    .powerdown_idle_timer               (powerdown_idle_timer),
    .dh_gs_frequency_ratio              (dh_gs_frequency_ratio)
    ,.block_rd_timer                           (block_rd_timer)
    ,.block_wr_timer                           (block_wr_timer)
    ,.load_diff_rank_dly_for_max_rank_rd_non3ds (load_diff_rank_dly_for_max_rank_rd_non3ds)
    ,.load_diff_rank_dly_for_max_rank_wr_non3ds (load_diff_rank_dly_for_max_rank_wr_non3ds)
    ,.gs_ts_lrank_enable_bits                   (gs_ts_lrank_enable_bits)
);
`endif //`ifndef SYNTHESIS
`endif // SNPS_ASSERT_ON


assign zqcl_due_to_sr_exit_ext = zqcl_due_to_sr_exit | zqcl_mask_cmds_zq_resistor_shared;

// flopping the zqcl_due_to_sr_exit_ext signal - to be used in the dimm_stagger_cs_en case
reg     zqcl_due_to_sr_exit_ext_r;

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if(~core_ddrc_rstn) begin
        zqcl_due_to_sr_exit_ext_r   <= 1'b0;
    end else begin
        zqcl_due_to_sr_exit_ext_r   <= zqcl_due_to_sr_exit_ext;
    end
end

assign zqcl_due_to_sr_exit_ext_add_x = zqcl_due_to_sr_exit_ext;

assign zqcl_due_to_sr_exit_ext_add_y = ((pi_gs_noxact) & zqcl_due_to_sr_exit_ext_r)
;


// generate a signal for 1 or 2 cycles that is used to block state m/c in
// gs_zq_calib.v block from going from IDLE to WAIT_FOR_ZQCS immediately while
// still performing previous ZQCL
// Ensure subsequent ZQCS is performed as a ZQCS and correctly ses tZQCS
assign zqcl_due_to_sr_exit_ext_block_new_zq = !zqcl_due_to_sr_exit_ext_add_x & zqcl_due_to_sr_exit_ext_add_y;



assign mr_gs_empty_w = mr_gs_empty;

endmodule  // gs (Global Scheduler)
