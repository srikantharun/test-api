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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/ts.sv#18 $
// -------------------------------------------------------------------------
// Description:
//
// Transaction Scheduler (TS) Unit
//
// This unit is responsible for selecting the operation to issue to DRAM
// next based on the Next Transaction Table's choice for the next
// transaction to each bank and the state of each bank, each rank, and the
// DRAM command and data bus (all tracked within TS).
//
// This unit contains 3 sub-units:
//  * BS - Bank Scheduler ("BSM")
//  * OS - Operation Selection
//  * GS - Global Scheduler
//
// BS and GS are instantiated here, and each OS sub-block is instantiated
// directly here.
// (To answer the obvious question, no, there is no good reason for doing
//  it this way.)
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "ts/DWC_ddrctl_ts_if.svh"
module ts
import DWC_ddrctl_reg_pkg::*;
#(
    //------------------------------- PARAMETERS ----------------------------------
    //  the rank and bank
     parameter   CHANNEL_NUM         = 0
    ,parameter   SHARED_AC           = 0
    ,parameter   RANK_BITS           = `MEMC_RANK_BITS
    ,parameter   LRANK_BITS          = `DDRCTL_DDRC_LRANK_BITS
    ,parameter   BG_BITS             = `MEMC_BG_BITS
    ,parameter   BANK_BITS           = `MEMC_BANK_BITS
    ,parameter   BG_BANK_BITS        = `MEMC_BG_BANK_BITS
    ,parameter   NUM_TOTAL_BANKS     = `DDRCTL_DDRC_NUM_TOTAL_BANKS      // total banks in all ranks in the system
    ,parameter   NUM_TOTAL_BSMS      = `UMCTL2_NUM_BSM
    ,parameter   NUM_RANKS           = `MEMC_NUM_RANKS            // max number of ranks supported
    ,parameter   NUM_BANKS           = 1 << BANK_BITS
    ,parameter   NUM_BG_BANKS        = 1 << BG_BANK_BITS
    ,parameter   PAGE_BITS           = `MEMC_PAGE_BITS            // bit width of a page identifier
    ,parameter   RD_CAM_ADDR_BITS    = `MEMC_RDCMD_ENTRY_BITS
    ,parameter   WR_CAM_ADDR_BITS    = `MEMC_WRCMD_ENTRY_BITS
    ,parameter   WR_CAM_ADDR_BITS_IE = 0
    ,parameter   MAX_CAM_ADDR_BITS   = 0                          // Max (RD_CAM_ADDR_BITS,WR_CAM_ADDR_BITS_IE)
    ,parameter   BCM_VERIF_EN        = 1
    ,parameter   BCM_DDRC_N_SYNC     = 2
    ,parameter   NPORTS              = 1                          // no. of ports (for cactive_in_ddrc width) gets overwritten by toplevel
    ,parameter   A_SYNC_TABLE        = 16'hffff
    ,parameter   MRS_A_BITS          = `MEMC_PAGE_BITS
    ,parameter   MRS_BA_BITS         = `MEMC_BG_BANK_BITS
    ,parameter   NUM_LANES           = 4                          //Number of total byte lanes in PHY - default is 4
    ,parameter   OCPAR_EN            = 0                          // On chip parity enable
    ,parameter   RD_CAM_ENTRIES      = 1<<`MEMC_RDCMD_ENTRY_BITS
    ,parameter   WR_CAM_ENTRIES      = 1<<`MEMC_WRCMD_ENTRY_BITS
    ,parameter   WR_CAM_ENTRIES_IE   = 1<<`MEMC_WRCMD_ENTRY_BITS
    ,parameter  NUM_LRANKS           = `DDRCTL_DDRC_NUM_LRANKS_TOTAL
    ,parameter  RANKBANK_BITS        = LRANK_BITS + BG_BANK_BITS  // bits required to address
    ,parameter  BSM_BITS             = `UMCTL2_BSM_BITS
    ,parameter  CMD_IF_WIDTH         = `MEMC_FREQ_RATIO           // 1 : when DFI is in 1:1 mode
                                                                  // 2 : when DFI is in 1:2 mode
    ,parameter  AUTOPRE_BITS         = 1
    ,parameter   PW_WORD_CNT_WD_MAX  = 2
    ,parameter   PARTIAL_WR_BITS_LOG2 = 1
    ,parameter PFSM_STATE_WIDTH      = 5
    ,parameter  BLK_ACT_TRFC_WDT     = (`MEMC_LPDDR4_EN == 1) ? (1 << BANK_BITS) : 1
    ,parameter  BLK_ACT_TRRD_WDT     = 1 << BG_BITS
    ,parameter  BLK_ACT_TRFM_WDT     = NUM_BANKS
    ,parameter  BLK_ACT_RAAC_WDT     = (`DDRCTL_LPDDR_RFMSBC_EN == 1) ? NUM_BG_BANKS : NUM_BG_BANKS/2
    ,parameter  NUM_BG_PER_RANK      = 1 << BG_BITS
    ,parameter  NUM_TOTAL_BGS        = NUM_BG_PER_RANK * NUM_LRANKS
    ,parameter  IE_TAG_BITS          = 0 // Override
    ,parameter  CMD_LEN_BITS         = 1
    ,parameter  WORD_BITS            = 1
    ,parameter  MWR_BITS             = `DDRCTL_MWR_BITS

    ,parameter MAX_CMD_DELAY         = `UMCTL2_MAX_CMD_DELAY
    ,parameter CMD_DELAY_BITS        = `UMCTL2_CMD_DELAY_BITS
    ,parameter MAX_CMD_NUM           = 2

    ,parameter    SELFREF_SW_WIDTH_INT = SELFREF_SW_WIDTH
    ,parameter    SELFREF_EN_WIDTH_INT = SELFREF_EN_WIDTH
    ,parameter    POWERDOWN_EN_WIDTH_INT = POWERDOWN_EN_WIDTH
    ,parameter    SELFREF_TYPE_WIDTH_INT = SELFREF_TYPE_WIDTH
    )
    (
    //---------------------------- INPUTS AND OUTPUTS ------------------------------
     input                                   co_yy_clk                       // clock
    ,input                                   core_ddrc_rstn                  // asynchronous negative-edge reset
    ,input   [NUM_RANKS-1:0]                 bsm_clk                         // For power saving purpose, bsm instances speficic clock
    ,output  [NUM_RANKS-1:0]                 bsm_clk_en                      // Clock enable for bsm instances
    ,input   [BSM_CLK_ON_WIDTH-1:0]          bsm_clk_on                      // bsm_clk always on
    ,input                                   dh_gs_2t_mode                   // 1- 2T mode, 0 = regular mode
    ,input   [BURST_RDWR_WIDTH-1:0]          dh_gs_burst_rdwr                // 5'b00100=burst of 8 data read/write
                                                                             // 5'b01000=burst of 16 data read/write
                                                                             // 5'b10000=burst of 32 data read/write
    ,input   [T_RAS_MIN_WIDTH-1:0]           dh_bs_t_ras_min                 // tRAS(MIN): ACT to PRE command min
    ,input   [T_RAS_MAX_WIDTH-1:0]           dh_bs_t_ras_max                 // tRAS(MAX): ACT to PRE command max
                                                                            // (programmed tRAS(MAX) time must
                                                                            // account for max delay in issuing
                                                                            // the critical PRE command)
    ,input   [REFRESH_MARGIN_WIDTH-1:0]      dh_gs_refresh_margin            // # of cycles (x32) early to attempt refresh
    ,input   [T_RC_WIDTH-1:0]                dh_bs_t_rc                      // tRC:   ACT to ACT min (bank)
    ,input   [T_RCD_WIDTH-1:0]               dh_bs_t_rcd                     // tRCD:  ACT to read/write delay
    ,input   [T_RCD_WIDTH-1:0]               dh_bs_t_rcd_write               // tRCD:  ACT to write delay (for LPDDR5X)
    ,input   [T_RP_WIDTH-1:0]                dh_bs_t_rp                      // tRP:   PRE command period
    ,input   [T_RRD_WIDTH-1:0]               dh_bs_t_rrd                     // tRRD:  ACT to ACT min (rank)
    ,input   [RD2PRE_WIDTH-1:0]              dh_bs_rd2pre                    // read to PRE command min delay
    ,input   [WR2PRE_WIDTH-1:0]              dh_bs_wr2pre                    // write to PRE command min delay
    ,input   [RDA2PRE_WIDTH-1:0]             reg_ddrc_rda2pre
    ,input   [WRA2PRE_WIDTH-1:0]             reg_ddrc_wra2pre
    ,input                                   dh_bs_pageclose                 // 1=close page as soon as possible
    ,input   [7:0]                           dh_bs_pageclose_timer
    ,input                                   dh_bs_frequency_ratio           // 0 - 1:2 mode, 1 - 1:1 mode
    ,input   [15:0]                          dh_gs_mr                        // mode register
    ,input   [15:0]                          dh_gs_emr                       // extended mode register
    ,input   [15:0]                          dh_gs_emr2                      // extended mode register 2 (ddr2 only)
    ,input   [15:0]                          dh_gs_emr3                      // extended mode register 3 (ddr2 only)
    ,input   [15:0]                          dh_gs_mr4                       // mode register
    ,input   [15:0]                          dh_gs_mr5                       // mode register
    ,input   [15:0]                          dh_gs_mr6                       // mode register
    ,input   [15:0]                          dh_gs_mr22                      // mode register
    ,input   [T_MR_WIDTH-1:0]                reg_ddrc_t_mr                   // time to wait between MRS/MRW to valid command
    ,input   [T_CCD_S_WIDTH-1:0]             dh_bs_t_ccd_s                   // tCCD:  RD/WR to RD/WR min (rank)
    ,input   [T_RRD_S_WIDTH-1:0]             dh_gs_t_rrd_s                   // tRRD:  ACT to ACT min (rank)
    ,input   [WR2RD_S_WIDTH-1:0]             dh_bs_wr2rd_s
    ,input   [RD2WR_WIDTH-1:0]               reg_ddrc_rd2wr_s                // short version for DDR4, the no '_' version is used as Long in DDR4 mode
    ,input   [MRR2RD_WIDTH-1:0]              reg_ddrc_mrr2rd
    ,input   [MRR2WR_WIDTH-1:0]              reg_ddrc_mrr2wr
    ,input   [MRR2MRW_WIDTH-1:0]             reg_ddrc_mrr2mrw
    ,input                                   reg_ddrc_dfi_reset_n            // controls dfi_reset_n
    ,output                                  gs_pi_dram_rst_n                // ddrc to dram active low reset
    ,input   [T_ZQ_LONG_NOP_WIDTH-1:0]       dh_gs_t_zq_long_nop             // time to wait in ZQCL during init sequence
    ,input   [T_ZQ_SHORT_NOP_WIDTH-1:0]      dh_gs_t_zq_short_nop            // time to wait in ZQCS during init sequence
    ,input   [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0]  dh_gs_t_zq_short_interval_x1024 // time interval between ZQCS
    ,input                                   dh_gs_zq_calib_short            // zq calib short command
    ,output                                  gs_dh_zq_calib_short_busy       // if 1: Previous zq calib short has not been initiated
    ,input                                   dh_gs_dis_auto_zq               // disable auto zq calib short from the controller
    ,input                                   dh_gs_dis_srx_zqcl              // when 1, disable zqcl after self-refresh exit
    ,input                                   dh_gs_dis_srx_zqcl_hwffc        // when 1, disable zqcl at hwffc end
    ,input                                   dh_gs_zq_resistor_shared
    ,input   [READ_LATENCY_WIDTH-1:0]        dh_gs_read_latency              // read latency - used to ensure MRR -> PD/SR timing
    ,input   [WRITE_LATENCY_WIDTH-1:0]       dh_gs_write_latency             // write latency - used for rd2pd and rd2mrw
    ,input                                   dh_gs_zq_reset                  // ZQ Reset command
    ,input   [T_ZQ_RESET_NOP_WIDTH-1:0]      dh_gs_t_zq_reset_nop            // ZQ Reset NOP period
    ,output                                  gs_dh_zq_reset_busy
    ,input                                   dh_gs_per_bank_refresh          // per bank refresh allowed for LPDDR4 SDRAM with 8 banks only
    ,input                                   dh_gs_per_bank_refresh_opt_en 
    ,input                                   dh_gs_fixed_crit_refpb_bank_en
    ,output                                  per_bank_refresh_int
    ,output  [BANK_BITS*NUM_RANKS-1:0]       hif_refresh_req_bank            // next bank that will be refreshed
    ,input                                   reg_ddrc_lpddr5x                // LPDDR5X mode
    ,input                                   dh_gs_lpddr4                    // LPDDR4 mode
    ,input                                   reg_ddrc_lpddr5                 // LPDDR5 mode
    ,input   [BANK_ORG_WIDTH-1:0]            reg_ddrc_bank_org
    ,input   [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] dh_gs_lpddr4_diff_bank_rwa2pre
    ,input                                   dh_gs_stay_in_selfref
    ,input   [T_PPD_WIDTH-1:0]               dh_gs_t_ppd                     // tPPD: PRE(A)-to-PRE(A) min delay
    ,input   [T_CMDCKE_WIDTH-1:0]            dh_gs_t_cmdcke
    ,input                                   reg_ddrc_dsm_en
    ,input   [T_PDN_WIDTH-1:0]               reg_ddrc_t_pdn
    ,input   [T_XSR_DSM_X1024_WIDTH-1:0]           reg_ddrc_t_xsr_dsm_x1024
    ,input   [T_CSH_WIDTH-1:0]               reg_ddrc_t_csh
    ,input   [ODTLOFF_WIDTH-1:0]             dh_gs_odtloff
    ,input   [T_CCD_MW_WIDTH-1:0]            dh_bs_t_ccd_mw                  // tCCDMW: CAS-to-CAS min delay masked write
    ,input   [RD2MR_WIDTH-1:0]               reg_ddrc_rd2mr
    ,input   [WR2MR_WIDTH-1:0]               reg_ddrc_wr2mr
    ,input   [PRE_CKE_X1024_WIDTH-1:0]       dh_gs_pre_cke_x1024             // cycles to wait before enabling clock
    ,input   [POST_CKE_X1024_WIDTH-1:0]      dh_gs_post_cke_x1024            // cycles to wait after enabling clock
    ,input   [RD2WR_WIDTH-1:0]               dh_gs_rd2wr                     // read-to-write latency
    ,input   [WR2RD_WIDTH-1:0]               dh_bs_wr2rd                     // write-to-read latency
    ,input   [DIFF_RANK_RD_GAP_WIDTH-1:0]    dh_gs_diff_rank_rd_gap          // cycle gap between reads to different ranks
    ,input   [DIFF_RANK_WR_GAP_WIDTH-1:0]    dh_gs_diff_rank_wr_gap          // cycle gap between writes to different ranks
    ,input   [RD2WR_DR_WIDTH-1:0]          reg_ddrc_rd2wr_dr               // cycle gap between read to write different ranks
    ,input   [WR2RD_DR_WIDTH-1:0]          reg_ddrc_wr2rd_dr               // cycle gap between write to read different ranks
    ,input   [3:0]                           dh_gs_max_rank_rd               // max reads to a ranks before fair re-arb
    ,input   [3:0]                           dh_gs_max_rank_wr               // max writes to a ranks before fair re-arb
    ,input   [NUM_RANKS-1:0]                 dh_gs_active_ranks              // populated DRAM ranks
    ,input                                   dh_gs_dis_max_rank_rd_opt       // Disable max rank read optimization
    ,input                                   dh_gs_dis_max_rank_wr_opt       // Disable max rank write optimization
    ,input   [5:0]                           dh_gs_refresh_burst             // 0 = refresh after each nominal refresh period
                                                                            // 1 = send 2 consecutive refreshes after 2 nominal refresh periods
                                                                            // ...
                                                                            // 7 = send 8 consecutive refreshes after 8 nominal refresh periods
    ,input   [7:0]                           dh_gs_ctrlupd_min_to_x1024      // min time between DFI controller updates
                                                                            //  in units of 1024 clock cycles
    ,input   [7:0]                           dh_gs_ctrlupd_max_to_x1024      // min time between DFI controller updates
                                                                            //  in units of 1024 clock cycles
    ,input   [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0] reg_ddrc_dfi_t_ctrlupd_burst_interval_x8

    ,input   [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]     reg_ddrc_dfi_t_ctrlupd_interval_type1        // max time between controller updates for PPT2.
    ,input   [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]reg_ddrc_dfi_t_ctrlupd_interval_type1_unit   // t_ctrlupd_interval_type1 unit
    ,input   [T_CCD_WIDTH-1:0] dh_bs_t_ccd                     // tCCD:  CAS to CAS delay (rank)
    ,input   [T_CKE_WIDTH-1:0] dh_gs_t_cke                     // tCKE:  min time between CKE
                                                                            //    assertion/de-assertion
    ,input   [T_FAW_WIDTH-1:0] dh_gs_t_faw                     // sliding window size in which 4 ACTs
                                                                            //  to a rank are allowed
    ,input   [T_RFC_MIN_WIDTH-1:0]                           dh_gs_t_rfc_min                 // minimum time between refreshes
    ,input   [T_RFC_MIN_AB_WIDTH-1:0]                       dh_gs_t_rfc_min_ab
    ,input   [T_PBR2PBR_WIDTH-1:0]                          dh_gs_t_pbr2pbr                 // minimum time between LPDDR4 per-bank refresh refreshes different bank
    ,input   [T_PBR2ACT_WIDTH-1:0]                          dh_gs_t_pbr2act                 // minimum time between LPDDR5 per-bank refresh act different bank
    ,input                                                       dh_gs_rfm_en
    ,input                                                       dh_gs_dis_mrrw_trfc        // disable MRR/MRW operation during tRFC
    ,input                                                       dh_gs_rfmsbc
    ,input   [RAAIMT_WIDTH-1:0]                                  dh_gs_raaimt
    ,input   [RAAMULT_WIDTH-1:0]                                 dh_gs_raamult
    ,input   [RAADEC_WIDTH-1:0]                                  dh_gs_raadec
    ,input   [RFMTH_RM_THR_WIDTH-1:0]                            dh_gs_rfmth_rm_thr
    ,input   [INIT_RAA_CNT_WIDTH-1:0]                            dh_gs_init_raa_cnt
    ,input   [T_RFMPB_WIDTH-1:0]                                 dh_gs_t_rfmpb
    ,input   [DBG_RAA_RANK_WIDTH-1:0]                            dh_gs_dbg_raa_rank
    ,input   [DBG_RAA_BG_BANK_WIDTH-1:0]                         dh_gs_dbg_raa_bg_bank
    ,output  [DBG_RAA_CNT_WIDTH-1:0]                             gs_dh_dbg_raa_cnt
    ,output  [NUM_RANKS-1:0]                                     gs_dh_rank_raa_cnt_gt0
    ,input   [4:0]                                               derate_operating_rm
    ,output                                                      gs_op_is_rfm
    ,output  [NUM_RANKS-1:0]                                     gs_rfm_cs_n
    ,output  [BANK_BITS-1:0]                                     gs_pi_rfmpb_bank
    ,output                                                      gs_pi_rfmpb_sb0
    ,input                                   dh_gs_t_refi_x1_sel          // specifies whether reg_ddrc_t_refi_x1_x32 reg is x1 or x32
    ,input                                   dh_gs_refresh_to_x1_sel      // specifies whether reg_ddrc_refresh_to_x1_x32 reg is x1 or x32
    ,input   [T_REFI_X1_X32_WIDTH-1:0]           dh_gs_t_refi_x1_x32          // average periodic refresh interval x1/x32
    ,input   [REFRESH_TO_X1_X32_WIDTH-1:0]   dh_gs_refresh_to_x1_x32         // idle time before issuing refresh x32
    ,input                                   dh_gs_prefer_write              // flush writes
    ,input   [6:0]                           dh_gs_rdwr_idle_gap             // time to wait after reads are down
                                                                            // before switching to writes
                                                                            // (except when prefer_write=1,
                                                                            //  when this will mean the opposite.)
    ,input   [POWERDOWN_EN_WIDTH_INT-1:0]        dh_gs_powerdown_en              // powerdown is enabled
    ,input   [POWERDOWN_TO_X32_WIDTH-1:0]    dh_gs_powerdown_to_x32          // timeout period (cock cycles x 32)
                                                                            //  before initiating powerdown
    ,input   [T_XP_WIDTH-1:0]                dh_gs_t_xp                      // tXP: duration of powerdown exit
    ,input [SELFREF_SW_WIDTH_INT-1:0]            reg_ddrc_selfref_sw
    ,input                                   reg_ddrc_hw_lp_en
    ,input                                   reg_ddrc_hw_lp_exit_idle_en
    ,input   [SELFREF_TO_X32_WIDTH-1:0]      reg_ddrc_selfref_to_x32
    ,input   [HW_LP_IDLE_X32_WIDTH-1:0]      reg_ddrc_hw_lp_idle_x32
    ,output  [SELFREF_TYPE_WIDTH_INT-1:0]        ddrc_reg_selfref_type
    ,input                                   ih_busy
    ,input                                   hif_cmd_valid
    ,output                                  gsfsm_sr_co_if_stall
    ,input                                   cactive_in_ddrc_sync_or
    ,input   [NPORTS-1:0]                    cactive_in_ddrc_async
    ,input                                   csysreq_ddrc
    ,input                                   csysmode_ddrc
    ,input   [4:0]                           csysfrequency_ddrc
    ,input                                   csysdiscamdrain_ddrc
    ,input                                   csysfsp_ddrc
    ,output                                  csysack_ddrc
    ,output                                  cactive_ddrc
    ,input   [SELFREF_EN_WIDTH_INT-1:0]      dh_gs_selfref_en                // self refresh is enabled
    ,input   [T_XSR_WIDTH-1:0] dh_gs_t_xsr                     // SRX to commands (unit of 1 cycle)
    ,input   [NUM_RANKS-1:0]                 dh_gs_mr_rank                   // Software configurable rank input
    ,input   [NUM_RANKS-1:0]                 dh_gs_rank0_wr_odt              // ODT settings for all ranks when writing to rank 0
    ,input   [NUM_RANKS-1:0]                 dh_gs_rank0_rd_odt              // ODT settings for all ranks when reading from rank 0
    ,input                                   dh_gs_refresh_update_level      // toggle this signal if refresh value has to be updated
                                                                            // used when freq is changed on the fly
    ,input                                   derate_refresh_update_level     // refresh_update_level from Derate module
    ,input   [NUM_LRANKS-1:0]                dh_gs_rank_refresh              // cmd issuing refresh to DRAM
    ,output  [NUM_LRANKS-1:0]                gs_dh_rank_refresh_busy         // If 1: Previous dh_gs_rank_refresh has not been stored
    ,input                                   dh_gs_dis_auto_refresh
    ,input                                   dh_gs_ctrlupd
    ,output                                  gs_dh_ctrlupd_busy
    ,input                                   reg_ddrc_ctrlupd_burst
    ,output                                  ddrc_reg_ctrlupd_burst_busy
    ,input                                   dh_gs_dis_auto_ctrlupd
    ,input                                   dh_gs_dis_auto_ctrlupd_srx
    ,input                                   dh_gs_ctrlupd_pre_srx
    ,input                                   dh_gs_mr_wr                     // input from core to write mode register
    ,input   [3:0]                           dh_gs_mr_addr                   // input from core: mode register address
                                                                            // 0000: MR0, 0001: MR1, 0010: MR2, 0011: MR3, 0100: MR4, 0101: MR5, 0110: MR6
    ,input   [MRS_A_BITS-1:0]                dh_gs_mr_data                   // mode register data to be written
    ,output                                  gs_dh_mr_wr_busy                // indicates that mode register write operation is in progress
    ,input                                   dh_gs_sw_init_int               // SW intervention in auto SDRAM initialization
    ,input                                   dh_gs_mr_type                   // input from core to write mode register
    ,output                                  mrr_op_on                       // is high when MRR operation is processed
    ,input                                   dh_gs_derate_enable
    ,input   [T_REFI_X1_X32_WIDTH+4:0]       derate_gs_t_refie
    ,input   [T_REFI_X1_X32_WIDTH+4:0]       derate_gs_t_refi
    ,input                                   derate_force_refab
    ,input   [REFRESH_TO_AB_X32_WIDTH-1:0]   reg_ddrc_refresh_to_ab_x32
    ,input   [5:0]                           max_postponed_ref_cmd
    ,input   [4:0]                           max_ref_cmd_within_2trefi
    ,output                                  ddrc_co_perf_lpr_xact_when_critical     // lpr transaction when lpr q is critical
    ,output                                  ddrc_co_perf_hpr_xact_when_critical     // hpr transaction when hpr q is critical
    ,output                                  ddrc_co_perf_wr_xact_when_critical      // wr transaction when wr q is critical
    ,output                                  ddrc_co_perf_rdwr_transitions           // pulses everytime there is a rd/wr or wr/rd transition in global FSM
    ,output  [4:0]                           gs_dh_init_curr_state           // init state for debug
    ,output  [4:0]                           gs_dh_init_next_state           // init state for debug
    ,input                                   phy_dfi_ctrlupd_ack1
    ,input                                   phy_dfi_init_complete           // PHY initialization complete.All DFI signals that communicate commands or status
                                                                            // must be held at their default values until the dfi_init_complete signal asserts
    ,input                                   dh_gs_dfi_init_complete_en
    ,output                                  ddrc_dfi_ctrlupd_req
    ,output  [1:0]                           ddrc_dfi_ctrlupd_type
    ,output  [1:0]                           ddrc_dfi_ctrlupd_target
    ,input   [9:0]                           dh_gs_dfi_t_ctrlup_min
    ,input   [9:0]                           dh_gs_dfi_t_ctrlup_max
    ,output  [1:0]                           gs_dh_ctrlupd_state
    ,input   [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0]                          dh_gs_refresh_timer0_start_value_x32  // initial timer value (used to stagger refresh timeouts)
    ,input   [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0]                          dh_gs_refresh_timer1_start_value_x32  // initial timer value
    ,input   [NUM_RANKS-1:0]                 dh_gs_rank1_wr_odt              // ODT settings for all ranks when writing to rank 1
    ,input   [NUM_RANKS-1:0]                 dh_gs_rank1_rd_odt              // ODT settings for all ranks when reading from rank 1
    ,input                                   rt_gs_empty                     // read tracking pipeline is empty
    ,input                                   mr_gs_empty                     // write pipeline is empty
    ,input   [7:0]                           dh_gs_hpr_xact_run_length       // # of cycles the high priority queue is guaranteed to be serviced once queue is critical
    ,input   [15:0]                          dh_gs_hpr_max_starve            // # of cycles the high priority queue can be starved before going critical
    ,input                                   ih_gs_rdhigh_empty              // no high priority reads pending
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_rd_hi                     // banks with high priority reads
    ,input                                   te_gs_block_wr
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_wrecc_btt                 // This entry in NTT is WE_BW && BTT==1
    ,input   [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0] te_os_rd_ie_tag_table
    ,input   [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0] te_os_wr_ie_tag_table
    ,output  [IE_TAG_BITS-1:0]               os_te_rdwr_ie_tag
    ,input   [7:0]                           dh_gs_lpr_xact_run_length       // # of cycles the low priority queue is guaranteed to be serviced once queue is critical
    ,input   [15:0]                          dh_gs_lpr_max_starve            // # of cycles the low priority queue can be starved before going critical
    ,input   [7:0]                           dh_gs_w_xact_run_length         // # of transactions to service when the write queue is critical
    ,input   [15:0]                          dh_gs_w_max_starve              // # of cycles the write queue can be starved before going critical
    ,input                                   pi_gs_ctrlupd_ok                // PI indication that a gs_pi_ctrlupd_req request
    ,input  [CMD_DELAY_BITS-1:0]             dfi_cmd_delay
    ,input  [DFI_TWCK_EN_RD_WIDTH-2:0]       mr_lp_data_rd
    ,input  [DFI_TWCK_EN_WR_WIDTH-2:0]       mr_lp_data_wr

    ,input                                   pi_gs_rd_vld                    // PI is scheduling a read transaction
    ,input                                   pi_gs_noxact                    // PI is scheduling a transaction, so GS may not do so
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_rd_page_hit               // banks with reads pending to open pages
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_rd_valid                  // banks with reads pending
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_wr_page_hit               // banks with writes pending to open pages
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_wr_valid                  // banks with writes pending
    ,input   [NUM_TOTAL_BSMS-1:0]            te_ts_vpw_valid                  // banks with writes pending
    ,input   [NUM_TOTAL_BSMS-1:0]            te_ts_vpr_valid                  // banks with writes pending
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_rd_bank_page_hit
    ,input   [NUM_TOTAL_BSMS-1:0]            te_bs_wr_bank_page_hit
    ,input                                   hif_go2critical_lpr             // go to critical lp read after critical_starve time
    ,input                                   hif_go2critical_hpr             // go to critical hp read after critical_starve time
    ,input                                   hif_go2critical_wr              // go to critical read after critical_starve time
    ,input                                   hif_go2critical_l1_wr
    ,input                                   hif_go2critical_l2_wr
    ,input                                   hif_go2critical_l1_lpr
    ,input                                   hif_go2critical_l2_lpr
    ,input                                   hif_go2critical_l1_hpr
    ,input                                   hif_go2critical_l2_hpr
    ,input                                   ih_gs_rdlow_empty               // no low priority reads pending
    ,input   [1:0]                           wu_gs_enable_wr                 // data_enable coming from WU module
                                                                            // if any of these bits are 1, it indicates that a write
                                                                            // operation is going on. This is used in gs_global_fsm
                                                                            // in clock_stop logic and in refresh_time_out logic in gs_glue
    ,input                                   dh_gs_dis_dq                    // disable dequeue of reads and writes (and all bypass paths)
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block
    ,input   [NUM_TOTAL_BSMS*PAGE_BITS-1:0]              be_os_page_table                // entire page table - to be used to select
                                                                                        //  page number through OS selection network
//spyglass enable_block W240
    ,output  [PAGE_BITS-1:0]                             os_te_rdwr_page                 // page number of a read or write only used by pi when OCPAR
                                                                                         //Output also used by XLTR.
    ,input   [NUM_TOTAL_BSMS*RD_CAM_ADDR_BITS-1:0]       te_os_rd_entry_table        // All Read entries in TE next table
    ,input   [NUM_TOTAL_BSMS*WR_CAM_ADDR_BITS_IE-1:0]    te_os_wr_entry_table        // All Write entries in TE next table
    ,input   [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]           te_os_rd_cmd_autopre_table
    ,input   [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]           te_os_wr_cmd_autopre_table
    ,input   [NUM_TOTAL_BSMS*CMD_LEN_BITS-1:0]           te_os_rd_cmd_length_table
    ,input   [NUM_TOTAL_BSMS*WORD_BITS-1:0]              te_os_rd_critical_word_table
    ,input   [NUM_TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0]   te_os_wr_mr_ram_raddr_lsb_first_table
    ,input   [NUM_TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]     te_os_wr_mr_pw_num_beats_m1_table

    ,input   [NUM_TOTAL_BSMS-1:0]                        te_os_rd_pageclose_autopre
    ,input   [NUM_TOTAL_BSMS-1:0]                        te_os_wr_pageclose_autopre
    ,input   [NUM_TOTAL_BSMS*PAGE_BITS-1:0]              te_os_rd_page_table         // All read page numbers in TE next table
    ,input   [NUM_TOTAL_BSMS*PAGE_BITS-1:0]              te_os_wr_page_table         // All read page numbers in TE next table
    ,input   [NUM_TOTAL_BSMS*MWR_BITS-1:0]               te_os_mwr_table             // All masked write entries in TE next table
    ,input   [NUM_TOTAL_BSMS-1:0]                        te_b3_bit                   // burst bit(column bit)[3] in TE next table
    ,output                                              ts_pi_mwr
    ,output  [MAX_CAM_ADDR_BITS-1:0]                     os_te_rdwr_entry                  // CAM entry # for read replacement from selection n/w
    ,output  [CMD_LEN_BITS-1:0]                          gs_pi_rd_length
    ,output  [WORD_BITS-1:0]                             gs_pi_rd_critical_word
    ,output  [PARTIAL_WR_BITS_LOG2-1:0]                  gs_pi_rdwr_ram_raddr_lsb_first
    ,output  [PW_WORD_CNT_WD_MAX-1:0]                    gs_pi_rdwr_pw_num_beats_m1
    ,input                                               ih_yy_xact_valid                // input handler has a valid transaction
    ,input                                               te_gs_any_vpr_timed_out         // Any VPR entry in the TE RD CAM has timed-out. Used in RD/WR switching logic.
    ,input                                               te_gs_any_vpr_timed_out_w       // No flopped version
    ,input                                               ih_gs_any_vpr_timed_out
    ,input                                               te_gs_any_vpw_timed_out         // Any VPW entry in the TE WR CAM has timed-out. Used in RD/WR switching logic.
    ,input                                               te_gs_any_vpw_timed_out_w       // Non flopped version
    ,input                                               ih_gs_any_vpw_timed_out
    ,input                                               te_gs_rd_flush                  // flush reads (for write-hits-read)
    ,input                                               te_gs_wr_flush                  // flush writes (for read-hits-write)
    ,input                                               te_gs_any_rd_pending            // 1 or more valid reads pending
    ,input                                               te_gs_any_wr_pending            // 1 or more valid writes pending
    ,input   [BSM_BITS-1:0]                              te_os_hi_bsm_hint               // bank to prefer for next high priority read
    ,input   [BSM_BITS-1:0]                              te_os_lo_bsm_hint               // bank to prefer for next low priority read
    ,input   [BSM_BITS-1:0]                              te_os_wr_bsm_hint               // bank to prefer for next write
    ,input   [BSM_BITS-1:0]                              te_os_wrecc_bsm_hint            // bank to prefer for next write ECC with BTT=1
    ,input   [BSM_BITS-1:0]                              te_os_lo_act_bsm_hint               // bank to prefer for next low priority read
    ,input   [BSM_BITS-1:0]                              te_os_wr_act_bsm_hint               // bank to prefer for next write
    ,output                                              gs_dh_selfref_cam_not_empty
    ,output  [2:0]                                       gs_dh_selfref_state
    ,output  [2:0]                                       gs_dh_operating_mode            // 00 = uninitialized
                                                                                        // 01 = normal
                                                                                        // 02 = self-refresh
                                                                                        // 03 = powerdown
                                                                                        // 04 = deep powerdown
    ,output                                              gs_pi_ctrlupd_req               // DFI controller update - pulsed with refresh signal
    ,output                                              gs_pi_rd_data_pipeline_empty    // indicates no read/write data flight
    ,output                                              gs_pi_wr_data_pipeline_empty    // indicates no read/write data flight
    ,output                                              gs_pi_data_pipeline_empty       // indicates no read/write data flight
    ,output                                              gs_pi_pads_powerdown            // powerdown many pads for DDR powerdown mode
    ,output                                              gs_pi_pads_selfref              // powerdown more pads for DDR self-refresh mode
    ,output                                              gs_op_is_enter_sr_lpddr         // enter LPDDR4 self-refresh mode
    ,output                                              gs_op_is_exit_sr_lpddr          // exit LPDDR4 self-refresh mode
    ,output                                              gs_op_is_enter_dsm              // enter deep sleep mode
    ,output                                              gs_op_is_exit_dsm               // exit deep sleep mode
    ,output                                              gs_op_is_cas_ws_off
    ,output                                              gs_op_is_cas_wck_sus
    ,output                                              gs_wck_stop_ok
    ,input                                               reg_en_dfi_dram_clk_disable
    ,output                                              gs_pi_stop_clk_ok               // stop the clock to DRAM during self refresh
    ,output  [1:0]                                       gs_pi_stop_clk_type
    ,output                                              dfilp_ctrl_lp
    ,input                                               pi_gs_stop_clk_early            // clock stop signal to PHY - used to inhibit commands
    ,input   [1:0]                                       pi_gs_stop_clk_type
    ,input                                               pi_gs_dfilp_wait
    ,input   [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable
    ,input   [T_CKSRE_WIDTH-1:0] reg_ddrc_t_cksre
    ,input   [T_CKSRX_WIDTH-1:0] reg_ddrc_t_cksrx
    ,input   [T_CKCSX_WIDTH-1:0] reg_ddrc_t_ckcsx
    ,input   [T_CKESR_WIDTH-1:0] reg_ddrc_t_ckesr                // at clock stop exit
    ,output                                              dfi_lp_ctrl_req
    ,output  [DFI_LP_WAKEUP_PD_WIDTH-1:0]                dfi_lp_ctrl_wakeup
    ,input                                               dfi_lp_ctrl_ack
    ,output                                              dfi_lp_data_req
    ,output  [DFI_LP_WAKEUP_PD_WIDTH-1:0]                dfi_lp_data_wakeup
    ,input                                               dfi_lp_data_ack
    ,input                                               dfi_reset_n_in
    ,output                                              dfi_reset_n_ref
    ,input                                               init_mr_done_in
    ,output                                              init_mr_done_out
    ,input                                               reg_ddrc_lpddr4_opt_act_timing
    ,input                                               reg_ddrc_lpddr5_opt_act_timing
    ,input                                               reg_ddrc_dfi_lp_data_req_en
    ,input                                               reg_ddrc_dfi_lp_en_pd
    ,input   [DFI_LP_WAKEUP_PD_WIDTH-1:0]                reg_ddrc_dfi_lp_wakeup_pd
    ,input                                               reg_ddrc_dfi_lp_en_sr
    ,input   [DFI_LP_WAKEUP_SR_WIDTH-1:0]                reg_ddrc_dfi_lp_wakeup_sr
    ,input                                               reg_ddrc_dfi_lp_en_data
    ,input   [DFI_LP_WAKEUP_DATA_WIDTH-1:0]              reg_ddrc_dfi_lp_wakeup_data
    ,input                                               reg_ddrc_dfi_lp_en_dsm
    ,input  [DFI_LP_WAKEUP_DSM_WIDTH-1:0]                reg_ddrc_dfi_lp_wakeup_dsm
    ,input   [DFI_TLP_RESP_WIDTH-1:0]                    reg_ddrc_dfi_tlp_resp

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
    ,input                                              pi_lp5_act2_cmd
    ,input                                              pi_lp5_noxact
    ,input                                              pi_lp5_preref_ok
    ,input                                              pi_col_b3

    ,output                                              gs_wr_mode                      // 1=performing writes  0=reads
    ,output                                              gs_te_wr_possible               // 1=write may be scheduled this cycle
                                                                                         // 0=write may not be scheduled this cycle
    ,output                                              gs_te_pri_level                 // 1=prefer high pri  0=reverse priority
    ,output  [1:0]                                       gs_dh_hpr_q_state               // state of high priority read queue
    ,output  [1:0]                                       gs_dh_lpr_q_state               // state of low priority read queue
    ,output  [1:0]                                       gs_dh_w_q_state                 // state of write queue
    ,output                                              gs_pi_init_in_progress
    ,output  [MRS_A_BITS-1:0]                            gs_pi_mrs_a                     // address for MRS command (load mode)
    ,output                                              gs_mpc_zq_start              // MCP: ZQ Start
    ,output                                              gs_mpc_zq_latch              // MCP: ZQ Latch
    ,output                                              mr4_req_o
    ,output                                              gs_pi_init_cke                  // CKE pin value to drive during init
    ,output  [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]            gs_pi_odt                       // per-rank ODT controls
    ,output                                              gs_pi_odt_pending               // waiting for the ODT command to complete


    ,input  [DFI_TPHY_WRLAT_WIDTH-1:0]                  reg_ddrc_dfi_tphy_wrlat
    ,input  [DFI_T_RDDATA_EN_WIDTH-1:0]                 reg_ddrc_dfi_t_rddata_en
    ,input   [DFI_TPHY_WRCSLAT_WIDTH-1:0]        reg_ddrc_dfi_tphy_wrcslat
    ,input   [6:0]                               reg_ddrc_dfi_tphy_rdcslat
    ,input                                       reg_ddrc_dfi_data_cs_polarity
    ,output  [`MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES-1:0]    gs_pi_wrdata_cs_n
    ,output  [`MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES-1:0]    gs_pi_rddata_cs_n
    ,output                                              gs_pi_mrr
    ,output                                              gs_pi_mrr_ext
    ,input                                               dh_gs_mr4_req
    ,input   [NUM_RANKS-1:0]                             dh_gs_mr4_req_rank
    ,input                                               phy_dfi_phyupd_req              // DFI PHY update request
    ,input                                               phy_dfi_phyupd_req_r            // registered DFI PHY update request
    ,output                                              ddrc_dfi_phyupd_ack             // DFI PHY update acknowledge
    ,input   [DFI_T_CTRL_DELAY_WIDTH-1:0]                                       reg_ddrc_dfi_t_ctrl_delay       // timer value for DFI tctrl_delay
    ,input   [DFI_T_WRDATA_DELAY_WIDTH-1:0]                                       reg_ddrc_dfi_t_wrdata_delay     // timer value for DFI twrdata_delay
    ,input                                               phy_dfi_phymstr_req             // DFI PHY Master request
    ,input [`MEMC_NUM_RANKS-1 : 0]                       phy_dfi_phymstr_cs_state        // DFI PHY Master CS state
    ,input                                               phy_dfi_phymstr_state_sel       // DFI PHY Master state select
    ,input [1:0]                                         phy_dfi_phymstr_type            // DFI PHY Master time type
    ,output                                              ddrc_dfi_phymstr_ack            // DFI PHY Master acknowledge
    ,input                                               reg_ddrc_dfi_phyupd_en          // Enable for DFI PHY update logic
    ,input                                               reg_ddrc_dfi_phymstr_en         // Enable for DFI PHY Master Interface
    ,input  [7:0]                                        reg_ddrc_dfi_phymstr_blk_ref_x32 // Number of 32 DFI cycles that is delayed to block refresh when there is PHY Master
    ,input                                               reg_ddrc_dis_cam_drain_selfref  // Disable CAM draining before entering selfref
    ,input                                               reg_ddrc_lpddr4_sr_allowed      // Allow transition from SR-PD to SR and back to SR-PD when PHY Master request
    ,output                                              gs_pi_phyupd_pause_req          // Sent to rest of uMCTL2 to tell system to pause
    ,input                                               pi_gs_phyupd_pause_ok           // resonse from PI to say alright to ack PHY update request
    ,output  [NUM_LRANKS-1:0]                            os_gs_rank_closed
    ,input   [1:0]                                       reg_ddrc_skip_dram_init
    ,output                                              gs_pi_dfi_lp_changing
    ,output [PAGE_BITS-1:0]                              ts_act_page
    ,output                                              ts_act2_invalid_tmg
    ,output                                              ddrc_co_perf_precharge_for_rdwr     // prechrge done for page miss
    ,output                                              ddrc_co_perf_precharge_for_other    // precharge done for other issues - refresh, mrs, zq, tRAS(max), sre, pde,
    ,output                                              any_refresh_required   // critical refresh required
    ,output                                              any_speculative_ref    // speculative refresh required
    ,input  [TARGET_FREQUENCY_WIDTH-1:0]                                 reg_ddrc_target_frequency

    ,input   [NUM_LRANKS-1:0]                            te_gs_rank_wr_pending // WR command pending in the CAM per rank
    ,input   [NUM_LRANKS-1:0]                            te_gs_rank_rd_pending // RD command pending in the CAM per rank
    ,input   [NUM_TOTAL_BANKS-1:0]                       te_gs_bank_wr_pending // WR command pending in the CAM per rank/bank
    ,input   [NUM_TOTAL_BANKS-1:0]                       te_gs_bank_rd_pending // RD command pending in the CAM per rank/bank
    ,input  [T_VRCG_ENABLE_WIDTH-1:0] reg_ddrc_t_vrcg_enable
    ,input  [T_VRCG_DISABLE_WIDTH-1:0] reg_ddrc_t_vrcg_disable
    ,input                                               reg_ddrc_target_vrcg
    ,input  [1:0]                                        reg_ddrc_hwffc_en
    ,input                                               reg_ddrc_hwffc_mode
    ,input                                               reg_ddrc_init_fsp
    ,input  [6:0]                                        reg_ddrc_t_zq_stop
    ,input  [1:0]                                        reg_ddrc_zq_interval
    ,input                                               reg_ddrc_skip_zq_stop_start
    ,input                                               reg_ddrc_init_vrcg
    ,input                                               reg_ddrc_skip_mrw_odtvref
    ,input                                               reg_ddrc_dvfsq_enable
    ,input                                               reg_ddrc_dvfsq_enable_next
    ,output                                              ddrc_reg_hwffc_in_progress
    ,output [TARGET_FREQUENCY_WIDTH-1:0]                                 ddrc_reg_current_frequency
    ,output                                              ddrc_reg_current_fsp
    ,output                                              ddrc_reg_current_vrcg
    ,output                                              ddrc_reg_hwffc_operating_mode
    ,output                                              hwffc_dis_zq_derate
    ,output                                              hwffc_hif_wd_stall
    ,output                                              ddrc_xpi_port_disable_req
    ,output                                              ddrc_xpi_clock_required
    ,input [NPORTS-1:0]                                  xpi_ddrc_port_disable_ack
    ,input [NPORTS-2:0]                                  xpi_ddrc_wch_locked
    ,input                                               reg_ddrc_opt_vprw_sch
    ,input                                               reg_ddrc_dis_speculative_act
    ,input                                               reg_ddrc_w_starve_free_running
    ,input                                               reg_ddrc_prefer_read

    // Frequency selection
    ,output                                              hwffc_target_freq_en
    ,output  [TARGET_FREQUENCY_WIDTH-1:0]                hwffc_target_freq
    ,output  [TARGET_FREQUENCY_WIDTH-1:0]                hwffc_target_freq_init
    // DFI frequency change I/F
    ,output                                              hwffc_freq_change
    ,output                                              hwffc_dfi_init_start
    ,output  [4:0]                                       hwffc_dfi_frequency
    ,output                                              hwffc_dfi_freq_fsp
    ,input                                               dfi_init_start
    ,input   [NUM_LRANKS-1:0]                            te_gs_rank_rd_valid
    ,input   [NUM_LRANKS-1:0]                            te_gs_rank_wr_valid
    ,input                                               reg_ddrc_opt_wrcam_fill_level
    ,input [3:0]                                         reg_ddrc_delay_switch_write
    ,input [WR_CAM_ADDR_BITS-1:0]                        reg_ddrc_wr_pghit_num_thresh
    ,input [RD_CAM_ADDR_BITS-1:0]                        reg_ddrc_rd_pghit_num_thresh
    ,input [WR_CAM_ADDR_BITS-1:0]                        reg_ddrc_wrcam_highthresh
    ,input [WR_CAM_ADDR_BITS-1:0]                        reg_ddrc_wrcam_lowthresh
    ,input [WR_CAM_ADDR_BITS-2:0]                        reg_ddrc_wrecc_cam_highthresh
    ,input [WR_CAM_ADDR_BITS-2:0]                        reg_ddrc_wrecc_cam_lowthresh
    ,input                                               reg_ddrc_dis_opt_valid_wrecc_cam_fill_level
    ,input                                               reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level
    ,output                                              ts_te_force_btt
    ,input [7:0]                                         reg_ddrc_wr_page_exp_cycles
    ,input [7:0]                                         reg_ddrc_rd_page_exp_cycles
    ,input [7:0]                                         reg_ddrc_wr_act_idle_gap
    ,input [7:0]                                         reg_ddrc_rd_act_idle_gap

    ,output  [NUM_TOTAL_BSMS-1:0]                        ts_te_sel_act_wr         //tell TE the activate command is for write or read.
    ,input [NUM_TOTAL_BSMS-1:0]                          te_rws_wr_col_bank       // entry of colliding bank (1bit for 1bank)
    ,input [NUM_TOTAL_BSMS-1:0]                          te_rws_rd_col_bank       // entry of colliding bank (1bit for 1bank)
//    ,input [WR_CAM_ADDR_BITS:0]                          ih_wr_credit_cnt

   ,input [WR_CAM_ADDR_BITS:0]                           te_wr_entry_avail        // Number of non-valid entries (WRCAM only, not include WRECC CAM) refer to [WR_CAM_ENTRIES-1:WR_CAM_ENTRIES]
   ,input [WR_CAM_ADDR_BITS:0]                           te_wrecc_entry_avail     // Number of non-valid entries (WRECCCAM only, not include WR CAM) refer to [WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]
   ,input [WR_CAM_ADDR_BITS:0]                           te_wrecc_entry_loaded    // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   ,input [WR_CAM_ADDR_BITS_IE:0]                        te_num_wr_pghit_entries
   ,input [RD_CAM_ADDR_BITS:0]                           te_num_rd_pghit_entries
   ,input                                                reg_ddrc_dis_opt_ntt_by_act
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
    ,input   [WR_CAM_ENTRIES_IE-1:0]                    te_ts_wr_entry_valid        // valid write entry in CAM, over entire CAM
    ,input   [RD_CAM_ENTRIES-1:0]                       te_ts_rd_entry_valid        // valid write entry in CAM, over entire CAM
    ,input   [WR_CAM_ENTRIES_IE-1:0]                    te_ts_wr_page_hit_entries   // valid page-hit entry in CAM
    ,input   [RD_CAM_ENTRIES-1:0]                       te_ts_rd_page_hit_entries
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
   ,input                                                te_rd_bank_pghit_vld_prefer  // Page hit and valid information of oldest entry for read
   ,input                                                te_wr_bank_pghit_vld_prefer  // Page hit and valid information of oldest entry for write
   ,input [RANK_BITS-1:0]                                te_gs_rank_wr_prefer         // rank number of oldest entry in te_wr_cam
   ,input [RANK_BITS-1:0]                                te_gs_rank_rd_prefer         // rank number of oldest entry in te_rd_cam
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
    ,output                                               ddrc_co_perf_op_is_dqsosc_mpc_w
    ,output                                               ddrc_co_perf_op_is_dqsosc_mrr_w
    ,output                                               os_te_autopre                   // auto-precharge indication to TE
                                                                                          //  (note: this comes later in the cycle
                                                                                          //         than the other te_bs_rd_* or te_bs_wr_*)
    ,input   [T_PGM_X1_X1024_WIDTH-1:0]                   reg_ddrc_t_pgm_x1_x1024
    ,input                                                reg_ddrc_t_pgm_x1_sel
    ,input   [T_PGMPST_X32_WIDTH-1:0]                     reg_ddrc_t_pgmpst_x32
    ,input   [T_PGM_EXIT_WIDTH-1:0]                       reg_ddrc_t_pgm_exit
    ,input                                                reg_ddrc_ppr_en
    ,output                                               ddrc_reg_ppr_done
    ,input                                                reg_ddrc_ppr_pgmpst_en
    ,input                                               reg_ddrc_ppt2_en
    ,input                                               reg_ddrc_ctrlupd_after_dqsosc
    ,input                                               reg_ddrc_ppt2_wait_ref
    ,input  [PPT2_BURST_NUM_WIDTH-1:0]                   reg_ddrc_ppt2_burst_num
    ,input                                               reg_ddrc_ppt2_burst
    ,output                                              ddrc_reg_ppt2_burst_busy
    ,output [PPT2_STATE_WIDTH-1:0]                       ddrc_reg_ppt2_state
    ,input  [PPT2_CTRLUPD_NUM_DFI_WIDTH-1:0]             reg_ddrc_ppt2_ctrlupd_num_dfi1
    ,input  [PPT2_CTRLUPD_NUM_DFI_WIDTH-1:0]             reg_ddrc_ppt2_ctrlupd_num_dfi0
    ,input                                               reg_ddrc_opt_act_lat
     );

//----------------------------LOCAL PARAMETERS  -------------------------------

    localparam  BANKS_PER_RANK      = NUM_TOTAL_BANKS / NUM_LRANKS;  // banks in each rank
                                                                     // (min banks per rank when sharing)
    localparam  SEL_RDWR_HI_TWDT    = MAX_CAM_ADDR_BITS + 1
                                    + 1 // mwr flag
                                    + CMD_LEN_BITS
                                    + WORD_BITS
                                    +PARTIAL_WR_BITS_LOG2
                                    +PW_WORD_CNT_WD_MAX
                                    + IE_TAG_BITS
                                    ;
    localparam  SEL_RDWR_LO_TWDT    = MAX_CAM_ADDR_BITS + 1
                                    + 1 // mwr flag
                                    + CMD_LEN_BITS
                                    + WORD_BITS
                                    +PARTIAL_WR_BITS_LOG2
                                    +PW_WORD_CNT_WD_MAX
                                    + IE_TAG_BITS
                                    ;
    localparam  SEL_ACT_TWDT        = PAGE_BITS
                                    + 1
                                    ;
    localparam  SEL_PRE_TWDT        = 0
                                    ;

        localparam      RETRY_EN    = 0;

        localparam      DFI_HIF_ADDR_EN    = 0;


        localparam      DYN_NUM_RANKS   = 1;

//---------------------------------- WIRES -------------------------------------
// Signals from BSMs to OpSelect
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_act_hi_vlds;              // banks with high-priority activates pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_rdwr_hi_vlds;             // banks with high-priority reads/writes pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_rdwr_hi_vlds_vpr;          // banks with high-priority VPRs pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_rdwr_lo_vlds_vprw;         // banks with low-priority VPRs/VPWs pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_act_lo_vlds;              // banks with low-priority activates pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_rdwr_lo_vlds;             // banks with low-priority reads/writes pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_pre_crit_vlds;            // banks with critical precharges pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_pre_req_vlds;             // banks with requested precharges pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_act_wr_vlds;          // banks with requested precharges pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_act_wrecc_vlds;          // banks with requested precharges pending
wire    [NUM_TOTAL_BSMS-1:0]            bs_os_pre_req_wr_vlds;          // banks with requested precharges pending

// Signals from Op Select to Global Scheduler
wire                                    os_gs_act_hi_vld;               // high priority activate pending
wire    [BSM_BITS-1:0]                  os_gs_act_hi_bsm;               // BSM number of the chosen hi priority activate
wire                                    os_gs_rdwr_hi_vld;              // low priority read/write pending
wire    [BSM_BITS-1:0]                  os_gs_rdwr_hi_bsm;              // BSM number of the chosen hi priority read/write
wire                                    os_gs_act_lo_vld;               // high priority activate pending
wire    [BSM_BITS-1:0]                  os_gs_act_lo_bsm;               // BSM number of the chosen lo priority activate
wire                                    os_gs_rdwr_lo_vld;              // low priority read/write pending
wire    [BSM_BITS-1:0]                  os_gs_rdwr_lo_bsm;              // BSM number of the chosen lo priority read/write
wire                                    os_gs_pre_crit_vld;             // critical precharge pending
wire    [BSM_BITS-1:0]                  os_gs_pre_crit_bsm;             // BSM number of the chosen critical precharge
wire                                    os_gs_pre_req_vld;              // requested precharge pending
wire    [BSM_BITS-1:0]                  os_gs_pre_req_bsm;              // BSM number of the chosen requested precharge
wire                                    os_gs_pre_req_mux_vld;          // requested precharge pending
wire    [BSM_BITS-1:0]                  os_gs_pre_req_mux_bsm;          // BSM number of the chosen requested precharge
wire                                    os_gs_act_wr_vld;               // requested precharge pending
wire    [BSM_BITS-1:0]                  os_gs_act_wr_bsm;               // BSM number of the chosen requested precharge
wire                                    os_gs_act_wrecc_vld;            // requested precharge pending
wire    [BSM_BITS-1:0]                  os_gs_act_wrecc_bsm;            // BSM number of the chosen requested precharge
wire                                    os_gs_pre_req_wr_vld;           // requested precharge pending
wire    [BSM_BITS-1:0]                  os_gs_pre_req_wr_bsm;           // BSM number of the chosen requested precharge

// Signals from Global Scheduler back to Op Select
wire                                    gs_os_wr_mode_early;            // 1=performing writes; 0=reads

// Signals from Global Scheduler to BSMs
wire    [NUM_LRANKS-1:0]                gs_bs_rank_refresh_required;    // refresh required, per rank
wire    [NUM_LRANKS-1:0]                gs_bs_rank_refresh_required_early;    // refresh required, per rank
wire    [NUM_LRANKS*NUM_BANKS-1:0]      gs_bs_bank_speculative_ref;     // speculative refresh request, per bank
wire    [NUM_LRANKS-1:0]                gs_rank_block_cas_b3_nxt;
wire    [NUM_LRANKS*BLK_ACT_TRRD_WDT-1:0] gs_bs_rank_act2_invalid_tmg_nxt;
wire    [NUM_LRANKS-1:0]                  gs_bs_rank_block_act_nxt;         // no activate allowed next cycle
wire    [NUM_LRANKS*BLK_ACT_TRFC_WDT-1:0] gs_bs_rank_block_act_trfc_bk_nxt; // no activate allowed next cycle
wire    [NUM_LRANKS*BLK_ACT_TRRD_WDT-1:0] gs_bs_rank_block_act_trrd_bg_nxt; // no activate allowed next cycle
wire    [NUM_LRANKS-1:0]                gs_bs_rank_block_act_ref_req;   // no activate allowed next cycle
wire    [NUM_LRANKS-1:0]                gs_bs_rank_block_rd_nxt;        // no read allowed this cycle
wire    [NUM_LRANKS-1:0]                gs_bs_rank_block_wr_nxt;        // no write allowed this cycle
wire                                    gs_bs_wr_mode_early;            // same as above, 1 clock early
wire                                    gs_bs_close_pages;              // global FSM requesting all pages be closed
wire    [NUM_LRANKS-1:0]                gs_bs_rank_rfm_required;
wire    [NUM_LRANKS*BLK_ACT_TRFM_WDT-1:0] gs_bs_rank_block_act_trfm_bk_nxt;
wire    [NUM_LRANKS*BLK_ACT_RAAC_WDT-1:0] gs_bs_rank_block_act_raa_expired;
wire    [NUM_LRANKS*BANK_BITS-1:0]      gs_bs_rfmpb_bank;
wire    [NUM_LRANKS-1:0]                gs_bs_rfmpb_sb0;

// Signals between OS blocks
wire    [BSM_BITS-1:0]                  lo_rdwr_bsm_hint;               // next bank to prefer for low pri read/write
wire    [BSM_BITS-1:0]                  lo_act_bsm_hint;                // next bank to prefer for low pri ACT
wire    [BSM_BITS-1:0]                  hi_rdwr_bsm_hint;               // next bank to prefer for high pri read/write
wire    [BSM_BITS-1:0]                  hi_act_bsm_hint;                // next bank to prefer for high pri ACT
wire    [BSM_BITS-1:0]                  pre_req_bsm_hint;               // next bank to prefer for requested precharge
wire    [BSM_BITS-1:0]                  wrecc_act_bsm_hint;               // next bank to prefer for requested precharge
wire    [BSM_BITS-1:0]                  wr_act_bsm_hint;               // next bank to prefer for requested precharge
wire    [BSM_BITS-1:0]                  wr_pre_req_bsm_hint;               // next bank to prefer for requested precharge
wire    [DYN_NUM_RANKS*NUM_TOTAL_BSMS-1:0]  bs_os_no_2ck_cmds_after_pre;    // blocks 2-cycles commands after PRE or commands w/AP
wire    [NUM_TOTAL_BSMS-1:0]            bm_act2_invalid_tmg;
wire    [NUM_RANKS-1:0]                 os_gs_no_2ck_cmds_after_pre;    // blocks 2-cycles commands after PRE or commands w/AP
wire                                    lpddr4_blk_act_nxt;
wire    [NUM_TOTAL_BSMS-1:0]            bs_gs_stop_clk_ok;              // clk_stop_ok from the BSM to the global FSM

wire    [NUM_RANKS-1:0]                 gs_bs_zq_calib_short_required;  // zqcs calib required, per rank
wire    [NUM_RANKS-1:0]                 gs_bs_load_mr_norm_required;    // load_mr_norm required

wire    [MAX_CAM_ADDR_BITS-1:0]         rdwr_lo_entry;                  // FIXME: which CAM addr bits to use? works only if both cams are same size
wire                                    rdwr_lo_autopre;

wire    [MAX_CAM_ADDR_BITS-1:0]         rdwr_hi_entry;
wire                                    rdwr_hi_autopre;


wire    [CMD_LEN_BITS-1:0]              rdwr_hi_cmd_length;
wire    [CMD_LEN_BITS-1:0]              rdwr_lo_cmd_length;

wire    [WORD_BITS-1:0]                 rdwr_hi_critical_word;
wire    [WORD_BITS-1:0]                 rdwr_lo_critical_word;

wire    [PARTIAL_WR_BITS_LOG2-1:0]      rdwr_hi_ram_raddr_lsb;
wire    [PARTIAL_WR_BITS_LOG2-1:0]      rdwr_lo_ram_raddr_lsb;

wire    [PW_WORD_CNT_WD_MAX-1:0]        rdwr_hi_pw_num_beats_m1;
wire    [PW_WORD_CNT_WD_MAX-1:0]        rdwr_lo_pw_num_beats_m1;

wire                                    rdwr_mwr;
wire                                    rdwr_lo_mwr;
wire    [PW_WORD_CNT_WD_MAX-1:0]        rdwr_lo_pw_num_cols_m1;
wire    [IE_TAG_BITS-1:0]               rdwr_hi_ie_tag;
wire    [IE_TAG_BITS-1:0]               rdwr_lo_ie_tag;
wire                                    rdwr_hi_mwr;

wire    [NUM_LRANKS*BANK_BITS-1:0]      gs_bs_refpb_bank;              // Bank being targetted per rank for current refpb command

assign hif_refresh_req_bank = gs_bs_refpb_bank[BANK_BITS*NUM_RANKS-1:0];// For 3DS confiuration and NUM_LRANKS > NUM_RANKS, higher bits (NUM_LRANKS-NUM_RANKS) are unused.

wire                                    gsfsm_dis_dq;

wire  [T_RFC_MIN_WIDTH-1:0]                             gs_bs_t_rfc_min_upd_unused;
wire  [REFRESH_MARGIN_WIDTH-1:0]                             gs_bs_refresh_margin_upd;

wire  [NUM_TOTAL_BGS-1:0]               gs_bs_blk_ccd_timer;
wire  [NUM_TOTAL_BGS-1:0]               gs_bs_blk_wr2rd_timer;
wire  [NUM_TOTAL_BGS-1:0]               gs_bs_blk_rd2wr_timer;

wire i_reg_ddrc_dis_cam_drain_selfref;

wire  [NUM_TOTAL_BSMS-1:0]              bs_os_mwr_table;
assign bs_os_mwr_table = 
                         te_os_mwr_table
                         ;

wire  rd_more_crit;
wire  wr_more_crit;
wire  gs_ts_any_vpr_timed_out;
wire  gs_ts_any_vpw_timed_out;

reg   gs_act_pre_rd_priority;
always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    gs_act_pre_rd_priority      <= 1'b0;
  end else begin
    gs_act_pre_rd_priority      <= gs_ts_any_vpr_timed_out |
                                 (~gs_ts_any_vpw_timed_out & |te_rws_rd_col_bank & (~|te_rws_wr_col_bank | ~gs_wr_mode)) |
                                 (~gs_ts_any_vpw_timed_out & ~|te_rws_wr_col_bank & (rd_more_crit | (~wr_more_crit & ~gs_wr_mode)))
                                 ;
  end
end


//PoC_RWS
wire delay_switch_write_state;
wire [NUM_TOTAL_BSMS-1:0] bank_activated_early;
wire [NUM_TOTAL_BSMS-1:0] bank_wr_activated_early;
//wire [NUM_TOTAL_BSMS-1:0] bank_activated_in_trd2wr;
wire [NUM_TOTAL_BSMS-1:0] sel_act_wr;
//wire [NUM_TOTAL_BSMS-1:0] sel_act_rd;
assign ts_te_sel_act_wr =  sel_act_wr;


assign i_reg_ddrc_dis_cam_drain_selfref = reg_ddrc_dis_cam_drain_selfref & ~ddrc_reg_hwffc_in_progress;

reg   [NUM_TOTAL_BSMS-1:0]              i_wrecc_entry; // Indicate per NTT's loaded CAM belongs to ECC_ENTRY or not.
reg                                     any_wrecc_r;
reg                                     te_gs_wr_flush_r;


reg te_gs_any_vpr_timed_out_r;
reg te_gs_any_vpw_timed_out_r;

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_gs_any_vpr_timed_out_r <= 1'b0;
    te_gs_any_vpw_timed_out_r <= 1'b0;
  end else begin
    te_gs_any_vpr_timed_out_r <= te_gs_any_vpr_timed_out_w & ((~reg_ddrc_opt_vprw_sch) | (|(te_bs_rd_valid & te_bs_rd_page_hit & te_ts_vpr_valid & bank_activated_early)));
    te_gs_any_vpw_timed_out_r <= te_gs_any_vpw_timed_out_w & ((~reg_ddrc_opt_vprw_sch) | (|(te_bs_wr_valid & te_bs_wr_page_hit & te_ts_vpw_valid & bank_wr_activated_early)));
  end
end


logic [NUM_TOTAL_BSMS-1:0]       bank_pgmiss_exvpr_valid_w;
logic [NUM_TOTAL_BSMS-1:0]       bank_pgmiss_exvpw_valid_w;

assign bank_pgmiss_exvpr_valid_w = te_bs_rd_valid & te_ts_vpr_valid & ~te_bs_rd_page_hit;
assign bank_pgmiss_exvpw_valid_w = te_bs_wr_valid & te_ts_vpw_valid & ~te_bs_wr_page_hit;




wire gs_phymstr_sre_req;
wire ppt2_stop_clk_req;
wire gs_bs_sre_stall;
wire gs_bs_sre_hw_sw;

    wire    [NUM_TOTAL_BANKS-1:0]           bs_os_bank_closed;              // bank is in idle state, ok to refresh
    wire    [NUM_RANKS*8-1:0]               os_gs_bank_closed;
    wire    [NUM_RANKS*16-1:0]              os_gs_bg_bank_closed;
    wire    [NUM_RANKS-1:0]                 dqsosc_block_other_cmd;
//-----------------------------------
// Generate WR CAM status, wr_cam_up_lowth and wr_cam_up_highth
// wr_cam_up_lowth and wr_cam_up_highth refer to [WR_CAM_ENTRIES-1:WR_CAM_ENTRIES]
// wrecc_cam_up_lowth and wrecc_cam_up_highth refer to [WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]
//-----------------------------------
wire wr_cam_up_highth;
wire wr_cam_up_lowth;

wire wrecc_cam_up_highth;        // valid status collection (of course it's loaded status)
wire wrecc_cam_up_lowth;         // valid status collection (of course it's loaded status)
wire wrecc_cam_up_highth_loaded; // loaded status regardless of valid.
wire wr_cam_up_wrecc_highth;     // available WR CAM less than wrecc_cam_high_threshold, used when combine with wrecc_cam_up_highth_loaded
wire wr_pghit_up_thresh;
wire rd_pghit_up_thresh;

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used for tb collect purpose only.
wire wr_cam_up_highth_tb;
wire wr_cam_up_lowth_tb;
wire wrecc_cam_up_highth_tb;
wire wrecc_cam_up_lowth_tb;
wire wrecc_cam_up_highth_loaded_tb;
wire wr_cam_up_wrecc_highth_tb;
//spyglass enable_block W528

reg        wr_cam_thresh_run_length_satisfied;
reg        wr_cam_thresh_run_length_satisfied_d;
reg [7:0]  wr_cam_thresh_run_length_cnt;
reg [15:0] wr_cam_thresh_starve_cnt;


always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    wr_cam_thresh_run_length_cnt          <= 8'h0F;
    wr_cam_thresh_run_length_satisfied    <= 1'b0;
    wr_cam_thresh_starve_cnt              <= 16'h007F;
  end else begin

    if (gs_op_is_rd | (gs_dh_operating_mode!=2'b01) | dh_gs_w_max_starve==16'h0000) begin // execute RD or not in normal mode
      wr_cam_thresh_run_length_cnt <= dh_gs_w_xact_run_length;
    end
    else if (gs_op_is_wr & wr_cam_thresh_run_length_cnt!=8'h00) begin
      wr_cam_thresh_run_length_cnt <= wr_cam_thresh_run_length_cnt - 8'h01;
    end

    if (dh_gs_w_max_starve==16'h0000) begin
      wr_cam_thresh_run_length_satisfied <= 1'b0; // This feature disabled
    end
    else if (wr_cam_thresh_run_length_cnt == 8'h00 & gs_op_is_wr) begin
      wr_cam_thresh_run_length_satisfied <= 1'b1;
    end
    else if (wr_cam_thresh_starve_cnt==16'h0000) begin // based on w_max_starve
      wr_cam_thresh_run_length_satisfied <= 1'b0;
    end

    if (dh_gs_w_max_starve==16'h0000) begin
      wr_cam_thresh_starve_cnt <= 16'h0000;
    end
    else if ((gs_op_is_wr && ~reg_ddrc_w_starve_free_running) || (~wr_cam_thresh_run_length_satisfied && reg_ddrc_w_starve_free_running)) begin
      wr_cam_thresh_starve_cnt <= dh_gs_w_max_starve;
    end
    else if (wr_cam_thresh_run_length_satisfied & (wr_cam_thresh_starve_cnt != 16'h0000)) begin
      wr_cam_thresh_starve_cnt <= wr_cam_thresh_starve_cnt - 16'h0001;
    end
  end
end

   assign wr_pghit_up_thresh = (|reg_ddrc_wr_pghit_num_thresh) & (te_num_wr_pghit_entries > {2'b00,reg_ddrc_wr_pghit_num_thresh});
   // Keep the Register width for Inline ECC

   assign rd_pghit_up_thresh = (|reg_ddrc_rd_pghit_num_thresh) & (te_num_rd_pghit_entries > {1'b0,reg_ddrc_rd_pghit_num_thresh});

   assign wr_cam_up_highth = ~wr_cam_thresh_run_length_satisfied & ((te_wr_entry_avail < {1'b0,reg_ddrc_wrcam_highthresh}) & reg_ddrc_opt_wrcam_fill_level) ? 1'b1 : 1'b0;
   assign wr_cam_up_lowth  = ~wr_cam_thresh_run_length_satisfied & ((te_wr_entry_avail < {1'b0,reg_ddrc_wrcam_lowthresh}) & reg_ddrc_opt_wrcam_fill_level) ? 1'b1 : 1'b0;

   assign wrecc_cam_up_highth = ~wr_cam_thresh_run_length_satisfied & ((te_wrecc_entry_avail < {2'b0,reg_ddrc_wrecc_cam_highthresh}) & reg_ddrc_opt_wrcam_fill_level & ~reg_ddrc_dis_opt_valid_wrecc_cam_fill_level) ? 1'b1 : 1'b0;
   assign wrecc_cam_up_lowth  = ~wr_cam_thresh_run_length_satisfied & ((te_wrecc_entry_avail < {2'b0,reg_ddrc_wrecc_cam_lowthresh}) & reg_ddrc_opt_wrcam_fill_level & ~reg_ddrc_dis_opt_valid_wrecc_cam_fill_level) ? 1'b1 : 1'b0;

   wire [WR_CAM_ADDR_BITS:0] te_wrecc_entry_unloaded_temp; //temp signal, to prevent Spyglass SelfdeterminML error.
   assign te_wrecc_entry_unloaded_temp = {2'b01,{(WR_CAM_ADDR_BITS-1){1'b0}}} - te_wrecc_entry_loaded;

   assign wrecc_cam_up_highth_loaded = ((te_wrecc_entry_unloaded_temp < {2'b0,reg_ddrc_wrecc_cam_highthresh}) & reg_ddrc_opt_wrcam_fill_level & ~reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level) ? 1'b1 : 1'b0;
   assign wr_cam_up_wrecc_highth = ((te_wr_entry_avail < {2'b01,reg_ddrc_wrecc_cam_highthresh}) & reg_ddrc_opt_wrcam_fill_level & ~reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level) ? 1'b1 : 1'b0;

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used for tb "Performance Monitor Metrics" collect purpose only.
   assign wr_cam_up_highth_tb = (te_wr_entry_avail < {1'b0,reg_ddrc_wrcam_highthresh}) ? 1'b1 : 1'b0;
   assign wr_cam_up_lowth_tb  = (te_wr_entry_avail < {1'b0,reg_ddrc_wrcam_lowthresh}) ? 1'b1 : 1'b0;
   assign wrecc_cam_up_highth_tb = (te_wrecc_entry_avail < {2'b0,reg_ddrc_wrecc_cam_highthresh}) ? 1'b1 : 1'b0;
   assign wrecc_cam_up_lowth_tb  = (te_wrecc_entry_avail < {2'b0,reg_ddrc_wrecc_cam_lowthresh}) ? 1'b1 : 1'b0;
   assign wrecc_cam_up_highth_loaded_tb = (te_wrecc_entry_unloaded_temp < {2'b0,reg_ddrc_wrecc_cam_highthresh}) ? 1'b1 : 1'b0;
   assign wr_cam_up_wrecc_highth_tb = (te_wr_entry_avail < {2'b01,reg_ddrc_wrecc_cam_highthresh}) ? 1'b1 : 1'b0;
//spyglass enable_block W528



//------------------------------------
// Performance logging signals
//------------------------------------

assign ddrc_co_perf_precharge_for_rdwr  = |(bs_os_pre_req_vlds | bs_os_pre_req_wr_vlds) & gs_op_is_pre;
assign ddrc_co_perf_precharge_for_other = |bs_os_pre_crit_vlds & gs_op_is_pre;

assign any_refresh_required             = (|gs_bs_rank_refresh_required);
assign any_speculative_ref              =
                                            (|gs_bs_bank_speculative_ref)
                                        ;

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    any_wrecc_r      <= 1'b0;
    te_gs_wr_flush_r <= 1'b0;
  end else begin
    any_wrecc_r      <= |(i_wrecc_entry & bs_os_rdwr_lo_vlds) ;
    te_gs_wr_flush_r <= te_gs_wr_flush;
  end
end

//-------------------------- BLOCK INSTANTIATIONS ------------------------------

generate
genvar bsm_num;
    // generate Bank State Machine units
    for (bsm_num=0; bsm_num<NUM_TOTAL_BSMS; bsm_num=bsm_num+1) begin : bsm_gen
      localparam LPDDR_RANK_THIS_BSM = bsm_num / 16; // both LPDDR5 and LPDDR4 has 16 BSMs per rank. See Bug 9594

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.

        wire [LRANK_BITS-1:0]   lrank_num;
        assign lrank_num = bsm_num[BG_BANK_BITS+:LRANK_BITS];
//spyglass enable_block W528
    
localparam  NUM_BANKS_IDX = `UMCTL_LOG2(NUM_LRANKS*NUM_BANKS);
localparam  BLK_ACT_TRRD_WDT_IDX = `UMCTL_LOG2(NUM_LRANKS*BLK_ACT_TRRD_WDT);
localparam  BLK_ACT_TRFC_WDT_IDX = `UMCTL_LOG2(NUM_LRANKS*BLK_ACT_TRFC_WDT);
localparam  BLK_ACT_TRFM_WDT_IDX = `UMCTL_LOG2(NUM_LRANKS*BLK_ACT_TRFM_WDT);
localparam  BLK_ACT_RAAC_WDT_IDX = `UMCTL_LOG2(NUM_LRANKS*BLK_ACT_RAAC_WDT);
localparam  RFMPB_NUM_BANKS_IDX  = `UMCTL_LOG2(NUM_LRANKS*BANK_BITS);
localparam  RFMPB_NUM_BANKS_POW2 = 2**RFMPB_NUM_BANKS_IDX;
localparam  NUM_BGS_IDX          = `UMCTL_LOG2(NUM_TOTAL_BGS);
localparam  NUM_LRANKS_IDX       = `UMCTL_LOG2(NUM_LRANKS);
localparam  NUM_LRANKS_POW2      = (NUM_LRANKS_IDX == 0) ? 2 : 2**NUM_LRANKS_IDX;

wire [NUM_BANKS_IDX-1:0] gs_bs_bank_speculative_ref_index;
wire [BLK_ACT_TRRD_WDT_IDX-1:0] gs_bs_rank_act2_invalid_tmg_nxt_index;
wire [RFMPB_NUM_BANKS_IDX-1:0]  gs_bs_refpb_bank_index;
wire [RFMPB_NUM_BANKS_POW2-1:0] gs_bs_refpb_bank_tmp;

assign gs_bs_bank_speculative_ref_index = lrank_num*NUM_BANKS+((dh_gs_lpddr4) ? bsm_num[BANK_BITS-1:0] : {bsm_num[0],bsm_num[3:2]}); 
assign gs_bs_rank_act2_invalid_tmg_nxt_index = lrank_num*BLK_ACT_TRRD_WDT + bsm_num[BG_BITS-1:0];
assign gs_bs_refpb_bank_index = lrank_num*BANK_BITS+BANK_BITS-1;
assign gs_bs_refpb_bank_tmp = RFMPB_NUM_BANKS_POW2 == NUM_LRANKS*BANK_BITS ? gs_bs_refpb_bank : {{(RFMPB_NUM_BANKS_POW2-NUM_LRANKS*BANK_BITS){1'b0}},gs_bs_refpb_bank}; 

wire [BLK_ACT_TRFC_WDT_IDX-1:0] gs_bs_rank_block_act_trfc_bk_nxt_index;
assign gs_bs_rank_block_act_trfc_bk_nxt_index = lrank_num*BLK_ACT_TRFC_WDT+((dh_gs_lpddr4) ? bsm_num[BANK_BITS-1:0] : {bsm_num[0],bsm_num[3:2]});
wire [BLK_ACT_TRRD_WDT_IDX-1:0] gs_bs_rank_block_act_trrd_bg_nxt_index;
wire [NUM_BGS_IDX-1:0]          gs_bgs_index;
assign gs_bs_rank_block_act_trrd_bg_nxt_index = lrank_num*BLK_ACT_TRRD_WDT + bsm_num[BG_BITS-1:0];
assign gs_bgs_index                           = lrank_num*NUM_BG_PER_RANK  + bsm_num[BG_BITS-1:0];

wire [BLK_ACT_TRFM_WDT_IDX-1:0] gs_bs_rank_block_act_trfm_bk_nxt_index;
assign gs_bs_rank_block_act_trfm_bk_nxt_index = lrank_num*BLK_ACT_TRFM_WDT + (dh_gs_lpddr4 ? bsm_num[BANK_BITS-1:0] : {bsm_num[0],bsm_num[3:2]});
wire [BLK_ACT_RAAC_WDT_IDX-1:0] gs_bs_rank_block_act_raa_expired_index;
assign gs_bs_rank_block_act_raa_expired_index = lrank_num*BLK_ACT_RAAC_WDT + (dh_gs_lpddr4 ? bsm_num[BANK_BITS-1:0] : {bsm_num[1:0], bsm_num[3:2]});
wire [RFMPB_NUM_BANKS_POW2-1:0] gs_bs_rfmpb_bank_tmp;
assign gs_bs_rfmpb_bank_tmp = RFMPB_NUM_BANKS_POW2 == NUM_LRANKS*BANK_BITS ? gs_bs_rfmpb_bank : {{(RFMPB_NUM_BANKS_POW2-NUM_LRANKS*BANK_BITS){1'b0}},gs_bs_rfmpb_bank}; 

wire [RFMPB_NUM_BANKS_IDX-1:0]  gs_bs_rfmpb_bank_index;
assign gs_bs_rfmpb_bank_index = lrank_num*BANK_BITS+BANK_BITS-1;

wire    [NUM_LRANKS_POW2-1:0] gs_bs_rank_refresh_required_tmp;    // refresh required, per rank
wire    [NUM_LRANKS_POW2-1:0] gs_bs_rank_refresh_required_early_tmp;    // refresh required, per rank
wire    [NUM_LRANKS_POW2-1:0] gs_rank_block_cas_b3_nxt_tmp;
wire    [NUM_LRANKS_POW2-1:0] gs_bs_rank_block_act_nxt_tmp;         // no activate allowed next cycle
wire    [NUM_LRANKS_POW2-1:0] gs_bs_rank_block_act_ref_req_tmp;   // no activate allowed next cycle
wire    [NUM_LRANKS_POW2-1:0] gs_bs_rank_block_rd_nxt_tmp;        // no read allowed this cycle
wire    [NUM_LRANKS_POW2-1:0] gs_bs_rank_block_wr_nxt_tmp;        // no write allowed this cycle

assign gs_bs_rank_refresh_required_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_bs_rank_refresh_required : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_bs_rank_refresh_required};
assign gs_bs_rank_refresh_required_early_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_bs_rank_refresh_required_early : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_bs_rank_refresh_required_early};
assign gs_rank_block_cas_b3_nxt_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_rank_block_cas_b3_nxt : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_rank_block_cas_b3_nxt};

assign gs_bs_rank_block_act_nxt_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_bs_rank_block_act_nxt : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_bs_rank_block_act_nxt};
assign gs_bs_rank_block_act_ref_req_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_bs_rank_block_act_ref_req : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_bs_rank_block_act_ref_req};
assign gs_bs_rank_block_rd_nxt_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_bs_rank_block_rd_nxt : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_bs_rank_block_rd_nxt};
assign gs_bs_rank_block_wr_nxt_tmp = NUM_LRANKS_POW2 == NUM_LRANKS ? gs_bs_rank_block_wr_nxt : {{(NUM_LRANKS_POW2-NUM_LRANKS){1'b0}}, gs_bs_rank_block_wr_nxt};


bsm
 #(
    .THIS_BANK_NUMBER                   (bsm_num),
    .MWR_BITS                           (MWR_BITS),
    .AUTOPRE_BITS                       (AUTOPRE_BITS)
) bsm (
    .co_yy_clk                          (co_yy_clk),
    .bsm_clk_en                         (bsm_clk_en[LPDDR_RANK_THIS_BSM]),
    .bsm_clk                            (bsm_clk[LPDDR_RANK_THIS_BSM]),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .dh_bs_t_ras_max                    (dh_bs_t_ras_max),
    .gs_bs_refresh_margin               (gs_bs_refresh_margin_upd), // connecting the updated value
    .dh_bs_t_ras_min                    (dh_bs_t_ras_min),
    .dh_bs_t_rc                         (dh_bs_t_rc),
    .dh_bs_t_rcd_write                  (dh_bs_t_rcd_write),
    .dh_bs_t_rcd                        (dh_bs_t_rcd),
    .dh_bs_t_rp                         (dh_bs_t_rp),
    .dh_bs_rd2pre                       (dh_bs_rd2pre),
    .dh_bs_wr2pre                       (dh_bs_wr2pre),
    .reg_ddrc_rda2pre                   (reg_ddrc_rda2pre),
    .reg_ddrc_wra2pre                   (reg_ddrc_wra2pre),
    .dh_bs_pageclose                    (dh_bs_pageclose),
    .dh_bs_pageclose_timer              (dh_bs_pageclose_timer),
    .dh_bs_frequency_ratio              (dh_bs_frequency_ratio),
    .gsfsm_dis_dq                       (gsfsm_dis_dq),
    .gs_bs_wr_mode_early                (gs_bs_wr_mode_early),
    .gs_bs_wr_mode                      (gs_wr_mode),
    .gs_act_pre_rd_priority             (gs_act_pre_rd_priority),
    .reg_ddrc_dis_speculative_act      (reg_ddrc_dis_speculative_act),
    .gs_bs_close_pages                  (gs_bs_close_pages),
    .gs_bs_rank_refresh_required        (gs_bs_rank_refresh_required_tmp[lrank_num]),
    .gs_bs_rank_refresh_required_early  (gs_bs_rank_refresh_required_early_tmp[lrank_num]),
    .gs_bs_bank_speculative_ref         (gs_bs_bank_speculative_ref [gs_bs_bank_speculative_ref_index]),
    .gs_rank_block_cas_b3_nxt           (gs_rank_block_cas_b3_nxt_tmp   [lrank_num]),
    .gs_bs_rank_act2_invalid_tmg_nxt    (gs_bs_rank_act2_invalid_tmg_nxt[gs_bs_rank_act2_invalid_tmg_nxt_index]),
    //spyglass disable_block W287a
    //SMD: Input 'gs_bs_rank_block_act_nxt' of instance 'bsm' is undriven.
    //SJ: Confirmed tool bug here (B-STAR 9001122672).
    .gs_bs_rank_block_act_nxt           (gs_bs_rank_block_act_nxt_tmp   [lrank_num]),

    .gs_bs_rank_block_act_trfc_bk_nxt   (gs_bs_rank_block_act_trfc_bk_nxt[gs_bs_rank_block_act_trfc_bk_nxt_index]),
    //spyglass enable_block W287a

    .gs_bs_rank_block_act_trrd_bg_nxt   (gs_bs_rank_block_act_trrd_bg_nxt[gs_bs_rank_block_act_trrd_bg_nxt_index]),
    .gs_bs_blk_ccd_timer                (gs_bs_blk_ccd_timer  [gs_bgs_index]),
    .gs_bs_blk_wr2rd_timer              (gs_bs_blk_wr2rd_timer[gs_bgs_index]),
    .gs_bs_blk_rd2wr_timer              (gs_bs_blk_rd2wr_timer[gs_bgs_index]),
    .gs_bs_rank_block_act_ref_req       (gs_bs_rank_block_act_ref_req_tmp[lrank_num]),
    .gs_bs_rank_block_rd_nxt            (gs_bs_rank_block_rd_nxt_tmp   [lrank_num]),
    .gs_bs_rank_block_wr_nxt            (gs_bs_rank_block_wr_nxt_tmp   [lrank_num]),
    .te_gs_any_vpr_timed_out            (te_gs_any_vpr_timed_out_r),
    .te_gs_any_vpw_timed_out            (te_gs_any_vpw_timed_out_r),
    // RFM related connections below do not consider Dynamic BSM because LPDDR controller does not support
//spyglass disable_block ImproperRangeIndex-ML
//SMD: Index 'lrank_num' of width '1' can have max value '1' which is greater than the required max value '0' of the signal 'gs_bs_rank_rfm_required'
//SJ:  This is no functional issue. Inline waiver has been added for the 1.60a-lca00 release.
    .gs_bs_rank_rfm_required            (gs_bs_rank_rfm_required[lrank_num]),
// spyglass enable_block ImproperRangeIndex-ML
    .gs_bs_rank_block_act_trfm_bk_nxt   (gs_bs_rank_block_act_trfm_bk_nxt[gs_bs_rank_block_act_trfm_bk_nxt_index]),
    .gs_bs_rank_block_act_raa_expired   (gs_bs_rank_block_act_raa_expired[gs_bs_rank_block_act_raa_expired_index]),
    .gs_bs_rfmpb_bank                   (gs_bs_rfmpb_bank_tmp[gs_bs_rfmpb_bank_index-:BANK_BITS]),
    .dh_gs_rfmsbc                       (dh_gs_rfmsbc),
//spyglass disable_block ImproperRangeIndex-ML
//SMD: Index 'lrank_num' of width '1' can have max value '1' which is greater than the required max value '0' of the signal 'gs_bs_rfmpb_sb'
//SJ:  This is no functional issue. Inline waiver has been added for the 1.60a-lca00 release.
    .gs_bs_rfmpb_sb0                    (gs_bs_rfmpb_sb0[lrank_num]),
// spyglass enable_block ImproperRangeIndex-ML
    .gs_bs_zq_calib_short_required      (gs_bs_zq_calib_short_required),
    .gs_bs_load_mr_norm_required        (gs_bs_load_mr_norm_required),

    .gs_bs_phymstr_sre_req              (gs_phymstr_sre_req),
    .ppt2_stop_clk_req                  (ppt2_stop_clk_req),
    .gs_bs_sre_stall                    (gs_bs_sre_stall),
    .gs_bs_sre_hw_sw                    (gs_bs_sre_hw_sw),
    .gs_bs_dis_cam_drain_selfref        (i_reg_ddrc_dis_cam_drain_selfref),
    .te_rd_autopre                      (os_te_autopre), // separate read & write indicators into
    //  BSM for future flexibility
    .te_wr_autopre                      (os_te_autopre), // separate read & write indicators into
    //  BSM for future flexibility
    .te_bs_rd_bank_page_hit             (te_bs_rd_bank_page_hit[bsm_num]),
    .te_bs_wr_bank_page_hit             (te_bs_wr_bank_page_hit[bsm_num]),
    .te_bs_rd_page_hit                  (te_bs_rd_page_hit     [bsm_num]),
    .te_bs_rd_hi                        (te_bs_rd_hi[bsm_num]),
    .te_bs_wrecc_btt                    (te_bs_wrecc_btt[bsm_num]),
    .te_bs_rd_valid                     (te_bs_rd_valid     [bsm_num]),
    .te_bs_wr_page_hit                  (te_bs_wr_page_hit  [bsm_num]),
    .te_bs_wr_valid                     (te_bs_wr_valid     [bsm_num]),
    .te_bs_wrecc_ntt                    (i_wrecc_entry      [bsm_num]),
    .bs_os_act_hi_vlds                  (bs_os_act_hi_vlds  [bsm_num]),
    .bs_os_rdwr_hi_vlds                 (bs_os_rdwr_hi_vlds [bsm_num]),
    .bs_os_act_lo_vlds                  (bs_os_act_lo_vlds  [bsm_num]),
    .bs_os_rdwr_lo_vlds                 (bs_os_rdwr_lo_vlds [bsm_num]),
    .bs_os_pre_crit_vlds                (bs_os_pre_crit_vlds[bsm_num]),
    .bs_os_pre_req_vlds                 (bs_os_pre_req_vlds [bsm_num]),
    .bs_os_act_wr_vlds                  (bs_os_act_wr_vlds [bsm_num]),
    .bs_os_act_wrecc_vlds               (bs_os_act_wrecc_vlds [bsm_num]),
    .bs_os_pre_req_wr_vlds              (bs_os_pre_req_wr_vlds [bsm_num]),
    .bs_gs_stop_clk_ok                  (bs_gs_stop_clk_ok  [bsm_num]),
    .bs_os_bank_closed                  (bs_os_bank_closed  [bsm_num]),
    .gs_bs_refpb_bank                   (gs_bs_refpb_bank_tmp[gs_bs_refpb_bank_index-:BANK_BITS]),
    .dh_gs_per_bank_refresh             (per_bank_refresh_int),
    .reg_ddrc_lpddr5x                   (reg_ddrc_lpddr5x),
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .reg_ddrc_bank_org                  (reg_ddrc_bank_org),
    .dh_bs_t_ccd_mw                     (dh_bs_t_ccd_mw),
    .te_bs_mwr                          (te_os_mwr_table[bsm_num*MWR_BITS+:MWR_BITS]),
    .te_b3_bit                          (te_b3_bit[bsm_num]),
    .pi_lp5_act2_cmd                    (pi_lp5_act2_cmd),
    //spyglass disable_block SelfDeterminedExpr-ML
    //SMD: Self determined expression '(bsm_num * DYN_NUM_RANKS)' found in module 'ts'
    //SJ: This coding style is acceptable and there is no plan to change it.
    .bs_os_no_2ck_cmds_after_pre        (bs_os_no_2ck_cmds_after_pre[bsm_num*DYN_NUM_RANKS+:DYN_NUM_RANKS]),
    //spyglass enable_block SelfDeterminedExpr-ML
    .act2_invalid_tmg                   (bm_act2_invalid_tmg[bsm_num]),
    .lpddr4_blk_act_nxt                 (lpddr4_blk_act_nxt),
    .te_os_rd_cmd_autopre_table         (te_os_rd_cmd_autopre_table[bsm_num*AUTOPRE_BITS+:AUTOPRE_BITS]),
    .te_os_rd_pageclose_autopre         (te_os_rd_pageclose_autopre[bsm_num]),
    .gs_pre_rankbank_num                (gs_pre_rankbank_num),
    .gs_rdwr_rankbank_num               (gs_rdwr_rankbank_num),
    .gs_act_rankbank_num                (gs_act_rankbank_num),
    .gs_op_is_act                       (gs_op_is_act),
    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),
    .gs_op_is_pre                       (gs_op_is_pre)
    ,.reg_ddrc_wr_page_exp_cycles      (reg_ddrc_wr_page_exp_cycles)
    ,.reg_ddrc_rd_page_exp_cycles      (reg_ddrc_rd_page_exp_cycles)
    ,.reg_ddrc_wr_act_idle_gap         (reg_ddrc_wr_act_idle_gap)
    ,.reg_ddrc_rd_act_idle_gap         (reg_ddrc_rd_act_idle_gap)

    ,.bank_activated_early             (bank_activated_early[bsm_num])
    ,.bank_wr_activated_early          (bank_wr_activated_early[bsm_num])
    ,.sel_act_wr                       (sel_act_wr[bsm_num])
//    ,.sel_act_rd                       (sel_act_rd[bsm_num])
    ,.rd_more_crit                     (rd_more_crit)
    ,.wr_more_crit                     (wr_more_crit)
    ,.te_rws_wr_col_bank               (te_rws_wr_col_bank[bsm_num])
    ,.te_rws_rd_col_bank               (te_rws_rd_col_bank[bsm_num])
    ,.te_ts_vpw_valid                  (te_ts_vpw_valid[bsm_num])
    ,.te_ts_vpr_valid                  (te_ts_vpr_valid[bsm_num])
//    ,.dh_gs_rd2wr                      (dh_gs_rd2wr)
//    ,.wr_cam_up_highth                 (wr_cam_up_highth)
//    ,.wr_cam_up_lowth                  (wr_cam_up_lowth)
    ,.delay_switch_write_state         (delay_switch_write_state)
    ,.dqsosc_block_other_cmd           (dqsosc_block_other_cmd)
    ,.reg_ddrc_opt_act_lat             (reg_ddrc_opt_act_lat)

);
    end // generate bsm_num
endgenerate

// Selecting the write or read entry based on the write mode
wire  [NUM_TOTAL_BSMS*PAGE_BITS-1:0]   te_os_page_table; // FIXME: works only if both cams are same size

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(WR_CAM_ADDR_BITS_IE * bsm_idx)' found in module 'ts'
//SJ: This coding style is acceptable and there is no plan to change it.

integer bsm_idx;
reg [NUM_TOTAL_BSMS*MAX_CAM_ADDR_BITS-1:0] i_te_os_wr_entry_table;   // padding
reg [NUM_TOTAL_BSMS*MAX_CAM_ADDR_BITS-1:0] i_te_os_rd_entry_table;   // padding

always @(*) begin
  i_te_os_wr_entry_table = {NUM_TOTAL_BSMS*MAX_CAM_ADDR_BITS{1'b0}};
  i_te_os_rd_entry_table = {NUM_TOTAL_BSMS*MAX_CAM_ADDR_BITS{1'b0}};
  for (bsm_idx=0; bsm_idx<NUM_TOTAL_BSMS; bsm_idx=bsm_idx+1) begin
    i_te_os_wr_entry_table[MAX_CAM_ADDR_BITS*bsm_idx+:WR_CAM_ADDR_BITS_IE] = te_os_wr_entry_table[WR_CAM_ADDR_BITS_IE*bsm_idx+:WR_CAM_ADDR_BITS_IE];
    i_te_os_rd_entry_table[MAX_CAM_ADDR_BITS*bsm_idx+:RD_CAM_ADDR_BITS]    = te_os_rd_entry_table[RD_CAM_ADDR_BITS*bsm_idx+:RD_CAM_ADDR_BITS];
    i_wrecc_entry[bsm_idx]                                                 = te_os_wr_entry_table[WR_CAM_ADDR_BITS_IE*(bsm_idx+1)-1];
  end
end


wire rdwr_pol_sel;
assign rdwr_pol_sel = 1'b1;

genvar poc_i;
generate
   for (poc_i=0; poc_i<NUM_TOTAL_BSMS; poc_i=poc_i+1) begin : rdwr_page_sel
      assign te_os_page_table[poc_i*PAGE_BITS+:PAGE_BITS]  = ( rdwr_pol_sel ? sel_act_wr[poc_i] : gs_wr_mode) ? te_os_wr_page_table[poc_i*PAGE_BITS+:PAGE_BITS] : te_os_rd_page_table[poc_i*PAGE_BITS+:PAGE_BITS];
   end
endgenerate

wire  [NUM_TOTAL_BSMS*MAX_CAM_ADDR_BITS-1:0]   te_os_entry_table; // FIXME: works only if both cams are same size
assign te_os_entry_table    = gs_wr_mode ? i_te_os_wr_entry_table : i_te_os_rd_entry_table;

wire [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]   te_os_cmd_autopre_table;
assign te_os_cmd_autopre_table  = gs_wr_mode ? te_os_wr_cmd_autopre_table : te_os_rd_cmd_autopre_table;
wire [NUM_TOTAL_BSMS-1:0]                te_os_pageclose_autopre;
assign te_os_pageclose_autopre  = gs_wr_mode ? te_os_wr_pageclose_autopre : te_os_rd_pageclose_autopre;

wire [NUM_TOTAL_BSMS-1:0]                te_os_autopre_table;
genvar autopre_idx;
generate
   for (autopre_idx=0; autopre_idx<NUM_TOTAL_BSMS; autopre_idx=autopre_idx+1) begin : rdwr_autopre_gen
      assign te_os_autopre_table[autopre_idx] =    te_os_cmd_autopre_table[autopre_idx*AUTOPRE_BITS  ]
                                              | (  te_os_pageclose_autopre[autopre_idx               ]
 & ~te_os_cmd_autopre_table[autopre_idx*AUTOPRE_BITS+1]);
   end
endgenerate

wire [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0] te_os_ie_tag;
assign te_os_ie_tag = gs_wr_mode ? te_os_wr_ie_tag_table : te_os_rd_ie_tag_table;

wire [NUM_TOTAL_BSMS*CMD_LEN_BITS-1:0] te_os_rd_cmd_length;
assign te_os_rd_cmd_length = gs_wr_mode ?  {(NUM_TOTAL_BSMS*CMD_LEN_BITS){1'b0}} : te_os_rd_cmd_length_table;


wire [NUM_TOTAL_BSMS*WORD_BITS-1:0] te_os_rd_critical_word;
assign te_os_rd_critical_word = gs_wr_mode ?  {(NUM_TOTAL_BSMS*WORD_BITS){1'b0}} : te_os_rd_critical_word_table;


wire [NUM_TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0] te_os_wr_mr_ram_raddr_lsb;
assign te_os_wr_mr_ram_raddr_lsb = gs_wr_mode ? te_os_wr_mr_ram_raddr_lsb_first_table : {(NUM_TOTAL_BSMS*PARTIAL_WR_BITS_LOG2){1'b0}};
wire [NUM_TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]   te_os_wr_mr_pw_num_beats;
assign te_os_wr_mr_pw_num_beats  = gs_wr_mode ? te_os_wr_mr_pw_num_beats_m1_table : {(NUM_TOTAL_BSMS*PW_WORD_CNT_WD_MAX){1'b0}};

// putting the page and cmd_autopre from all the banks into a single bus
// the format is {page[bankN],cmd_autopre[bankN], ... , page[bank1],cmd_autopre[bank1],page[bank0],cmd_autopre[bank0]}
wire [NUM_TOTAL_BSMS*SEL_RDWR_HI_TWDT-1:0]  rdwr_hi_tags;
wire [NUM_TOTAL_BSMS*SEL_RDWR_LO_TWDT-1:0]  rdwr_lo_tags;
wire [SEL_RDWR_HI_TWDT-1:0]                 rdwr_hi_tag_selected;
wire [SEL_RDWR_LO_TWDT-1:0]                 rdwr_lo_tag_selected;

genvar i;
generate
    for (i=0; i<NUM_TOTAL_BSMS; i=i+1) begin : rdwr_tags_gen
assign rdwr_hi_tags[i*SEL_RDWR_HI_TWDT+:SEL_RDWR_HI_TWDT] =
                {te_os_entry_table      [i*MAX_CAM_ADDR_BITS+:MAX_CAM_ADDR_BITS]
                ,te_os_autopre_table    [i]
                ,bs_os_mwr_table        [i]
                ,te_os_ie_tag[i*IE_TAG_BITS +: IE_TAG_BITS]
                ,te_os_rd_cmd_length[i*CMD_LEN_BITS +:CMD_LEN_BITS]
                ,te_os_rd_critical_word[i*WORD_BITS +:WORD_BITS]
                ,te_os_wr_mr_ram_raddr_lsb[i*PARTIAL_WR_BITS_LOG2 +: PARTIAL_WR_BITS_LOG2]
                ,te_os_wr_mr_pw_num_beats[i*PW_WORD_CNT_WD_MAX +: PW_WORD_CNT_WD_MAX]
                };

assign rdwr_lo_tags[i*SEL_RDWR_LO_TWDT+:SEL_RDWR_LO_TWDT] =
                {te_os_entry_table         [i*MAX_CAM_ADDR_BITS  +:MAX_CAM_ADDR_BITS]
                ,te_os_autopre_table       [i]
                ,bs_os_mwr_table           [i]
                ,te_os_ie_tag[i*IE_TAG_BITS +: IE_TAG_BITS]
                ,te_os_rd_cmd_length[i*CMD_LEN_BITS +:CMD_LEN_BITS]
                ,te_os_rd_critical_word[i*WORD_BITS +:WORD_BITS]
                ,te_os_wr_mr_ram_raddr_lsb[i*PARTIAL_WR_BITS_LOG2 +: PARTIAL_WR_BITS_LOG2]
                ,te_os_wr_mr_pw_num_beats[i*PW_WORD_CNT_WD_MAX +: PW_WORD_CNT_WD_MAX]
                };
  end
endgenerate

// The page for rdwr is only required in pi for address loggin when OCPAR
// and in ddrc_capar_retry for address loggin when RETRY
// Page for rdwr is used by address translator to generate HIF address.
generate
  if ((OCPAR_EN==1) || (RETRY_EN==1) || (DFI_HIF_ADDR_EN==1)) begin: OCPAR_OR_RETRY_OR_XLTR_en
    wire   [PAGE_BITS-1:0]       be_page_array [NUM_TOTAL_BSMS-1:0];    // be open page array
    // converting table to array
    for (i=0; i<NUM_TOTAL_BSMS; i=i+1) begin : CONV_BE_PAGE_TABLE_TO_ARRAY
      assign be_page_array[i] = be_os_page_table [((i+1)*PAGE_BITS)-1 : i*PAGE_BITS];
    end
    assign os_te_rdwr_page = be_page_array[gs_rdwr_bsm_num];
  end
  else begin: OCPAR_AND_RETRY_nen
    assign os_te_rdwr_page = {PAGE_BITS{1'b0}};
  end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML


   assign bs_os_rdwr_hi_vlds_vpr = te_gs_any_vpr_timed_out_r & ~gs_wr_mode ? (bs_os_rdwr_hi_vlds & te_ts_vpr_valid) : bs_os_rdwr_hi_vlds;
// Selection network and wall for high priority reads and all writes
// tag selects the high priority page number and entry number
select_net_lite
 #(
    .TAG_BITS           (SEL_RDWR_HI_TWDT),
    .NUM_INPUTS         (NUM_TOTAL_BSMS)
) select_net_rdwr_hi_page_entry (
    .clk                (co_yy_clk),
    .resetb             (core_ddrc_rstn),
    .tags               (rdwr_hi_tags),
    .vlds               (bs_os_rdwr_hi_vlds_vpr),
    .wall_next          (hi_rdwr_bsm_hint),
    .selected_vld       (os_gs_rdwr_hi_vld),
    .tag_selected       (rdwr_hi_tag_selected),
    .selected           (os_gs_rdwr_hi_bsm)
);

assign {rdwr_hi_entry
       ,rdwr_hi_autopre
       ,rdwr_hi_mwr
       ,rdwr_hi_ie_tag
       ,rdwr_hi_cmd_length
       ,rdwr_hi_critical_word
       ,rdwr_hi_ram_raddr_lsb
       ,rdwr_hi_pw_num_beats_m1
       } = rdwr_hi_tag_selected;


// select hi priority when only hi is valid, or when hi valid and hi preferred (gs_te_pri_level=1)
wire    rdwr_hi_select; // selects between hi and lo pri reads
assign rdwr_hi_select         = os_gs_rdwr_hi_vld & (~os_gs_rdwr_lo_vld | (gs_te_pri_level | gs_wr_mode)) ;

assign os_te_rdwr_entry       = rdwr_hi_select ? rdwr_hi_entry : rdwr_lo_entry;
assign os_te_autopre          = (rdwr_hi_select ? rdwr_hi_autopre:rdwr_lo_autopre)
                                ;


assign gs_pi_rd_length         = rdwr_hi_select ? rdwr_hi_cmd_length : rdwr_lo_cmd_length;
assign gs_pi_rd_critical_word  = rdwr_hi_select ? rdwr_hi_critical_word : rdwr_lo_critical_word;


assign gs_pi_rdwr_ram_raddr_lsb_first = rdwr_hi_select ? rdwr_hi_ram_raddr_lsb : rdwr_lo_ram_raddr_lsb;
assign gs_pi_rdwr_pw_num_beats_m1     = rdwr_hi_select ? rdwr_hi_pw_num_beats_m1 : rdwr_lo_pw_num_beats_m1;

assign ts_pi_mwr              = rdwr_mwr;

assign rdwr_mwr               =
                                rdwr_hi_select ? rdwr_hi_mwr :
                                rdwr_lo_mwr;


assign os_te_rdwr_ie_tag      = rdwr_hi_select ? rdwr_hi_ie_tag : rdwr_lo_ie_tag;


//When we make the previous change, we suppose all the exVPR will become high priority and go to rdwr_hi select net,
//just need do nothing (set to 0) for rdwr_lo select net.(refer to bug5910)
//However, it still takes one cycle for asserting te_bs_rd_hi against te_ts_vpr_valid,
//So it is possible that exVPR go to rdwr_lo if it is expired in NTT. If we block exVPR served from rdwr_lo, the exVPR will be served from rdwr_hi in next cycle. but increase latency and waste one cycle.
assign bs_os_rdwr_lo_vlds_vprw =
                                 (te_gs_any_vpw_timed_out_r & gs_wr_mode) ? (bs_os_rdwr_lo_vlds & te_ts_vpw_valid) :
                                 (te_gs_any_vpr_timed_out_r & (~gs_wr_mode)) ? (bs_os_rdwr_lo_vlds & te_ts_vpr_valid) :
                                 (rdwr_pol_sel & rd_more_crit & gs_wr_mode & ~te_gs_wr_flush_r & any_wrecc_r) ? (bs_os_rdwr_lo_vlds & i_wrecc_entry) :
                                                                                 bs_os_rdwr_lo_vlds;

// Selection network and wall for low priority reads and all writes
// tag selects the high priority page number and entry number
select_net_lite
 #(
    .TAG_BITS           (SEL_RDWR_LO_TWDT),
    .NUM_INPUTS         (NUM_TOTAL_BSMS)
) select_net_rdwr_lo_page_entry (
    .clk                (co_yy_clk),
    .resetb             (core_ddrc_rstn),
    .tags               (rdwr_lo_tags),
    .vlds               (bs_os_rdwr_lo_vlds_vprw),
    .wall_next          (lo_rdwr_bsm_hint),
    .selected_vld       (os_gs_rdwr_lo_vld),
    .tag_selected       (rdwr_lo_tag_selected),
    .selected           (os_gs_rdwr_lo_bsm)
);

assign {rdwr_lo_entry
       ,rdwr_lo_autopre
       ,rdwr_lo_mwr
       ,rdwr_lo_ie_tag
       ,rdwr_lo_cmd_length
       ,rdwr_lo_critical_word
       ,rdwr_lo_ram_raddr_lsb
       ,rdwr_lo_pw_num_beats_m1
       } = rdwr_lo_tag_selected;

//------------------
// Activate selection
//-------------------
// select hi priority when only hi is valid, or when hi valid and hi preferred (gs_te_pri_level=1)

wire [NUM_TOTAL_BSMS*SEL_ACT_TWDT-1:0]  act_tags;
wire [SEL_ACT_TWDT-1:0]                 act_hi_tag_selected;
wire [SEL_ACT_TWDT-1:0]                 act_lo_tag_selected;


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * PAGE_BITS)' found in module 'ts'
//SJ: This coding style is acceptable and there is no plan to change it.
generate
    for (i=0; i<NUM_TOTAL_BSMS; i=i+1) begin : act_tags_gen
assign act_tags[i*SEL_ACT_TWDT+:SEL_ACT_TWDT] =
                {te_os_page_table       [i*PAGE_BITS    +:PAGE_BITS]
                ,bm_act2_invalid_tmg[i]
                };
  end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

localparam  PAGE_ACT2_BITS        = PAGE_BITS
                                    + 1
                                    ;
wire act_rd_vld;
wire  [SEL_ACT_TWDT-1:0] act_rd_tag;
wire act_wr_vld;
wire  [SEL_ACT_TWDT-1:0] act_wr_tag;
wire [PAGE_ACT2_BITS-1:0] act_wr_page;
wire [PAGE_ACT2_BITS-1:0] act_rd_page;
wire [SEL_ACT_TWDT-1:0]                 act_wr_tag_selected;
wire [SEL_ACT_TWDT-1:0]                 act_wrecc_tag_selected;

assign act_rd_vld = os_gs_act_hi_vld | os_gs_act_lo_vld ;
assign act_rd_tag = gs_te_pri_level ? (os_gs_act_hi_vld ? act_hi_tag_selected : act_lo_tag_selected) : (os_gs_act_lo_vld ? act_lo_tag_selected : act_hi_tag_selected) ;

assign act_rd_page = act_rd_tag;

assign {ts_act_page
        ,ts_act2_invalid_tmg
       } = gs_act_pre_rd_priority ? (act_rd_vld ? act_rd_page : act_wr_page) :
                                    (act_wr_vld ? act_wr_page : act_rd_page);
// Selection network for row activates for high priority reads
// tag selects the high priority entry number
   select_net_lite
    #(.TAG_BITS(SEL_ACT_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS) )
   select_net_act_hi
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               (act_tags),
      .vlds                               (bs_os_act_hi_vlds),
      .wall_next                          (hi_act_bsm_hint),
      .selected_vld                       (os_gs_act_hi_vld),
      .tag_selected                       (act_hi_tag_selected),
      .selected                           (os_gs_act_hi_bsm)
      );



// Selection network for row activates for low priority reads & writes
// tag selects the low priority entry number
   select_net_lite
    #(.TAG_BITS(SEL_ACT_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS))
   select_net_act_lo
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               (act_tags),
      .vlds                               (bs_os_act_lo_vlds),
      .wall_next                          (lo_act_bsm_hint),
      .selected_vld                       (os_gs_act_lo_vld),
      .tag_selected                       (act_lo_tag_selected),
      .selected                           (os_gs_act_lo_bsm)
      );


assign act_wr_vld = os_gs_act_wrecc_vld |  os_gs_act_wr_vld ;
assign act_wr_tag =
os_gs_act_wrecc_vld ? act_wrecc_tag_selected :
act_wr_tag_selected;

assign {act_wr_page
       } = act_wr_tag;

// Selection network for row activates for high priority reads
// tag selects the high priority entry number
   select_net_lite
    #(.TAG_BITS(SEL_ACT_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS) )
   select_net_act_wr
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               (act_tags),
      .vlds                               (bs_os_act_wr_vlds),
      .wall_next                          (wr_act_bsm_hint),
      .selected_vld                       (os_gs_act_wr_vld),
      .tag_selected                       (act_wr_tag_selected),
      .selected                           (os_gs_act_wr_bsm)
      );

// Selection network for row activates for high priority reads
// tag selects the high priority entry number
   select_net_lite
    #(.TAG_BITS(SEL_ACT_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS) )
   select_net_act_wrecc
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               (act_tags),
      .vlds                               (bs_os_act_wrecc_vlds),
      .wall_next                          (wrecc_act_bsm_hint),
      .selected_vld                       (os_gs_act_wrecc_vld),
      .tag_selected                       (act_wrecc_tag_selected),
      .selected                           (os_gs_act_wrecc_bsm)
      );

// Selection network and wall for precharges requested to peform a read or
//  a write
   wire unused_tag_pre_requested;

   select_net_lite
    #(.TAG_BITS(SEL_PRE_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS))
   select_net_pre_requested
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               ({NUM_TOTAL_BSMS{1'b0}}),
      .vlds                               (bs_os_pre_req_vlds),
      .wall_next                          (pre_req_bsm_hint),
      .selected_vld                       (os_gs_pre_req_vld),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Output unused in this config.
      .tag_selected                       (unused_tag_pre_requested),
//spyglass enable_block W528
      .selected                           (os_gs_pre_req_bsm)
      );


// Selection network and wall for precharges requested to peform a read or
//  a write
   wire unused_tag_pre_wr_requested;

   select_net_lite
    #(.TAG_BITS(SEL_PRE_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS))
   select_net_pre_wr_requested
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               ({NUM_TOTAL_BSMS{1'b0}}),
      .vlds                               (bs_os_pre_req_wr_vlds),
      .wall_next                          (wr_pre_req_bsm_hint),
      .selected_vld                       (os_gs_pre_req_wr_vld),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Output unused in this config.
      .tag_selected                       (unused_tag_pre_wr_requested),
//spyglass enable_block W528
      .selected                           (os_gs_pre_req_wr_bsm)
      );



// Selection network and wall for critical precharges
// ("critical precharge" = precharge to avoid tRAS(max) violations)
    // Don't care much about fairness here - by tying off the wall bits, we're
// essentially making this a priority encoder (with the flexible to alter
// the selection if we ever find a reason to.)
   wire unused_tag_pre_critical;

   select_net_lite
    #(.TAG_BITS(SEL_PRE_TWDT),
                     .NUM_INPUTS (NUM_TOTAL_BSMS))
   select_net_pre_critical
     (
      .clk                                (co_yy_clk),
      .resetb                             (core_ddrc_rstn),
      .tags                               ({NUM_TOTAL_BSMS{1'b0}}),
      .vlds                               (bs_os_pre_crit_vlds),
      .wall_next                          ({BSM_BITS{1'b0}}),
      .selected_vld                       (os_gs_pre_crit_vld),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Output unused in this config.
      .tag_selected                       (unused_tag_pre_critical),
//spyglass enable_block W528
      .selected                           (os_gs_pre_crit_bsm)
      );

os_glue
 os_glue (
    .gs_os_wr_mode_early                (gs_os_wr_mode_early),
    .reg_ddrc_lpddr4                    (dh_gs_lpddr4),
    .bs_os_bank_closed                  (bs_os_bank_closed),
    .os_gs_bank_closed                  (os_gs_bank_closed),
    .os_gs_bg_bank_closed               (os_gs_bg_bank_closed),
    .te_os_hi_bsm_hint                  (te_os_hi_bsm_hint),
    .te_os_lo_bsm_hint                  (te_os_lo_bsm_hint),
    .te_os_wr_bsm_hint                  (te_os_wr_bsm_hint),
    .te_os_lo_act_bsm_hint              (te_os_lo_act_bsm_hint),
    .te_os_wr_act_bsm_hint              (te_os_wr_act_bsm_hint),
    .te_os_wrecc_bsm_hint               (te_os_wrecc_bsm_hint),
    .force_btt                          (ts_te_force_btt),
    .bs_os_no_2ck_cmds_after_pre        (bs_os_no_2ck_cmds_after_pre),
    .os_gs_no_2ck_cmds_after_pre        (os_gs_no_2ck_cmds_after_pre),
    .lo_rdwr_bsm_hint                   (lo_rdwr_bsm_hint[BSM_BITS-1:0]),
    .hi_rdwr_bsm_hint                   (hi_rdwr_bsm_hint[BSM_BITS-1:0]),
    .hi_act_bsm_hint                    (hi_act_bsm_hint[BSM_BITS-1:0]),
      .wrecc_act_bsm_hint               (wrecc_act_bsm_hint[BSM_BITS-1:0]),
    .lo_act_bsm_hint                    (lo_act_bsm_hint[BSM_BITS-1:0]),
    .wr_act_bsm_hint                    (wr_act_bsm_hint[BSM_BITS-1:0]),
    .pre_req_bsm_hint                   (pre_req_bsm_hint[BSM_BITS-1:0]),
    .wr_pre_req_bsm_hint                (wr_pre_req_bsm_hint[BSM_BITS-1:0]),
    .os_gs_rank_closed                  (os_gs_rank_closed[NUM_LRANKS-1:0])
);

assign os_gs_pre_req_mux_vld = os_gs_pre_req_vld  | os_gs_pre_req_wr_vld ;
assign os_gs_pre_req_mux_bsm = gs_act_pre_rd_priority ? (os_gs_pre_req_vld ? os_gs_pre_req_bsm : os_gs_pre_req_wr_bsm) :
                                                        (os_gs_pre_req_wr_vld ? os_gs_pre_req_wr_bsm : os_gs_pre_req_bsm);


wire                                    gs_op_is_enter_selfref_pre;
wire                                    gs_op_is_exit_selfref_pre;

gs
 #(
    .CHANNEL_NUM                        (CHANNEL_NUM),
    .NUM_LANES                          (NUM_LANES),
    .SHARED_AC                          (SHARED_AC),
    .RANK_BITS                          (RANK_BITS),
    .BANK_BITS                          (BANK_BITS),
    .BG_BITS                            (BG_BITS),
    .BG_BANK_BITS                       (BG_BANK_BITS),
    .NUM_TOTAL_BANKS                    (NUM_TOTAL_BANKS),
    .BCM_VERIF_EN                       (BCM_VERIF_EN),
    .BCM_DDRC_N_SYNC                    (BCM_DDRC_N_SYNC),
    .NPORTS                             (NPORTS),
    .A_SYNC_TABLE                       (A_SYNC_TABLE),
    .RD_CAM_ENTRIES                     (RD_CAM_ENTRIES),
    .WR_CAM_ENTRIES                     (WR_CAM_ENTRIES),
    .MAX_CMD_DELAY                      (MAX_CMD_DELAY),
    .CMD_DELAY_BITS                     (CMD_DELAY_BITS),
    .CMD_LEN_BITS                       (CMD_LEN_BITS),
    .SELFREF_SW_WIDTH_INT               (SELFREF_SW_WIDTH_INT),
    .SELFREF_EN_WIDTH_INT               (SELFREF_EN_WIDTH_INT),
    .POWERDOWN_EN_WIDTH_INT             (POWERDOWN_EN_WIDTH_INT),
    .SELFREF_TYPE_WIDTH_INT             (SELFREF_TYPE_WIDTH_INT),
    .MAX_CMD_NUM                        (MAX_CMD_NUM)
    ) gs (
    .co_yy_clk                          (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    .bsm_clk_en                         (bsm_clk_en    ),
    .bsm_clk_on                         (bsm_clk_on    ),
    .dh_gs_2t_mode                      (dh_gs_2t_mode),
    .dh_gs_frequency_ratio              (dh_bs_frequency_ratio),
    .dh_gs_mr                           (dh_gs_mr),
    .dh_gs_emr                          (dh_gs_emr),
    .dh_gs_emr2                         (dh_gs_emr2),
    .dh_gs_emr3                         (dh_gs_emr3),
    .dh_gs_mr4                          (dh_gs_mr4),
    .dh_gs_mr5                          (dh_gs_mr5),
    .dh_gs_mr6                          (dh_gs_mr6),
    .dh_gs_mr22                         (dh_gs_mr22),
    .reg_ddrc_t_mr                      (reg_ddrc_t_mr),
    .reg_ddrc_dfi_reset_n               (reg_ddrc_dfi_reset_n), // controls dfi_reset_n
    .gs_pi_dram_rst_n                   (gs_pi_dram_rst_n), // ddrc to dram active low reset
    .dh_gs_t_zq_long_nop                (dh_gs_t_zq_long_nop), // time to wait in ZQCL during init sequence
    .dh_gs_t_zq_short_nop               (dh_gs_t_zq_short_nop), // time to wait in ZQCS during init sequence
    .dh_gs_t_zq_short_interval_x1024    (dh_gs_t_zq_short_interval_x1024),
    .dh_gs_zq_calib_short               (dh_gs_zq_calib_short),
    .gs_dh_zq_calib_short_busy          (gs_dh_zq_calib_short_busy),
    .dh_gs_dis_auto_zq                  (dh_gs_dis_auto_zq),
    .dh_gs_dis_srx_zqcl                 (dh_gs_dis_srx_zqcl),
    .dh_gs_dis_srx_zqcl_hwffc           (dh_gs_dis_srx_zqcl_hwffc),
    .dh_gs_zq_resistor_shared           (dh_gs_zq_resistor_shared),
    .dh_gs_read_latency                 (dh_gs_read_latency),
    .dh_gs_write_latency                (dh_gs_write_latency),
    .dh_gs_zq_reset                     (dh_gs_zq_reset),
    .dh_gs_t_zq_reset_nop               (dh_gs_t_zq_reset_nop),
    .gs_dh_zq_reset_busy                (gs_dh_zq_reset_busy ),
    .dh_gs_t_rcd                        (dh_bs_t_rcd), // This will be used for LPDDR4. So [4:0] is always enough
    .dh_gs_lpddr4                       (dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .reg_ddrc_bank_org                  (reg_ddrc_bank_org),
    .dh_gs_lpddr4_diff_bank_rwa2pre     (dh_gs_lpddr4_diff_bank_rwa2pre),
    .dh_gs_stay_in_selfref              (dh_gs_stay_in_selfref),
    .dh_gs_t_ppd                        (dh_gs_t_ppd),
    .dh_gs_t_cmdcke                     (dh_gs_t_cmdcke),
    .reg_ddrc_dsm_en                    (reg_ddrc_dsm_en),
    .reg_ddrc_t_pdn                     (reg_ddrc_t_pdn),
    .reg_ddrc_t_xsr_dsm_x1024           (reg_ddrc_t_xsr_dsm_x1024),
    .reg_ddrc_t_csh                     (reg_ddrc_t_csh),
    .dh_gs_odtloff                      (dh_gs_odtloff),
    .reg_ddrc_rd2mr                     (reg_ddrc_rd2mr),
    .reg_ddrc_wr2mr                     (reg_ddrc_wr2mr),
    .os_te_autopre                      (os_te_autopre),
    .reg_ddrc_wra2pre                   (reg_ddrc_wra2pre),
    .dh_gs_mr_wr                        (dh_gs_mr_wr),
    .dh_gs_mr_addr                      (dh_gs_mr_addr),
    .dh_gs_mr_data                      (dh_gs_mr_data),
    .gs_dh_mr_wr_busy                   (gs_dh_mr_wr_busy),
    .dh_gs_sw_init_int                  (dh_gs_sw_init_int),
    .dh_gs_mr_type                      (dh_gs_mr_type),
    .mrr_op_on                          (mrr_op_on),
    .dh_gs_derate_enable                (dh_gs_derate_enable),
    .derate_gs_t_refi                   (derate_gs_t_refi),
    .derate_gs_t_refie                  (derate_gs_t_refie),
    .derate_force_refab                 (derate_force_refab),
    .reg_ddrc_refresh_to_ab_x32         (reg_ddrc_refresh_to_ab_x32),
    .max_postponed_ref_cmd              (max_postponed_ref_cmd),
    .max_ref_cmd_within_2trefi          (max_ref_cmd_within_2trefi),
    .ddrc_co_perf_lpr_xact_when_critical(ddrc_co_perf_lpr_xact_when_critical),
    .ddrc_co_perf_hpr_xact_when_critical(ddrc_co_perf_hpr_xact_when_critical),
    .ddrc_co_perf_wr_xact_when_critical (ddrc_co_perf_wr_xact_when_critical),
    .ddrc_co_perf_rdwr_transitions      (ddrc_co_perf_rdwr_transitions),
    .gs_dh_init_curr_state              (gs_dh_init_curr_state),
    .gs_dh_init_next_state              (gs_dh_init_next_state),

    .dfi_cmd_delay                      (dfi_cmd_delay),
    .mr_lp_data_rd                      (mr_lp_data_rd),
    .mr_lp_data_wr                      (mr_lp_data_wr),

    .phy_dfi_ctrlupd_ack1               (phy_dfi_ctrlupd_ack1),
    .phy_dfi_init_complete              (phy_dfi_init_complete),
    .dh_gs_dfi_init_complete_en         (dh_gs_dfi_init_complete_en),
    .ddrc_dfi_ctrlupd_req               (ddrc_dfi_ctrlupd_req),
    .ddrc_dfi_ctrlupd_type              (ddrc_dfi_ctrlupd_type),
    .ddrc_dfi_ctrlupd_target            (ddrc_dfi_ctrlupd_target),
    .dh_gs_dfi_t_ctrlup_min             (dh_gs_dfi_t_ctrlup_min),
    .dh_gs_dfi_t_ctrlup_max             (dh_gs_dfi_t_ctrlup_max),
    .gs_dh_ctrlupd_state                (gs_dh_ctrlupd_state),
    .dh_gs_burst_rdwr                   (dh_gs_burst_rdwr),
    .dh_gs_rd2wr                        (dh_gs_rd2wr),
    .dh_gs_wr2rd                        (dh_bs_wr2rd),
    .dh_gs_diff_rank_rd_gap             (dh_gs_diff_rank_rd_gap),
    .dh_gs_diff_rank_wr_gap             (dh_gs_diff_rank_wr_gap),
    .reg_ddrc_rd2wr_dr                  (reg_ddrc_rd2wr_dr),
    .reg_ddrc_wr2rd_dr                  (reg_ddrc_wr2rd_dr),
    .dh_gs_max_rank_rd                  (dh_gs_max_rank_rd),
    .dh_gs_max_rank_wr                  (dh_gs_max_rank_wr),
    .dh_gs_active_ranks                 (dh_gs_active_ranks),
    .dh_gs_dis_max_rank_rd_opt          (dh_gs_dis_max_rank_rd_opt),
    .dh_gs_dis_max_rank_wr_opt          (dh_gs_dis_max_rank_wr_opt),
    .dh_gs_rank_refresh                 (dh_gs_rank_refresh),
    .gs_dh_rank_refresh_busy            (gs_dh_rank_refresh_busy),
    .dh_gs_dis_auto_refresh             (dh_gs_dis_auto_refresh),
    .dh_gs_ctrlupd                      (dh_gs_ctrlupd),
    .gs_dh_ctrlupd_busy                 (gs_dh_ctrlupd_busy),
    .reg_ddrc_ctrlupd_burst             (reg_ddrc_ctrlupd_burst),
    .ddrc_reg_ctrlupd_burst_busy        (ddrc_reg_ctrlupd_burst_busy),
    .dh_gs_dis_auto_ctrlupd             (dh_gs_dis_auto_ctrlupd),
    .dh_gs_dis_auto_ctrlupd_srx         (dh_gs_dis_auto_ctrlupd_srx),
    .dh_gs_ctrlupd_pre_srx              (dh_gs_ctrlupd_pre_srx),
    .dh_gs_refresh_burst                (dh_gs_refresh_burst),
    .dh_gs_t_cke                        (dh_gs_t_cke),
    .dh_gs_t_faw                        (dh_gs_t_faw),
    .dh_gs_t_rrd                        (dh_bs_t_rrd),
    .dh_gs_t_rrd_s                      (dh_gs_t_rrd_s),
    .dh_gs_t_rfc_min                    (dh_gs_t_rfc_min),
    .dh_gs_t_rfc_min_ab                 (dh_gs_t_rfc_min_ab),
    .dh_gs_t_pbr2pbr                    (dh_gs_t_pbr2pbr),
    .dh_gs_t_pbr2act                    (dh_gs_t_pbr2act),
    .dh_gs_rfm_en                       (dh_gs_rfm_en),
    .dh_gs_dis_mrrw_trfc                (dh_gs_dis_mrrw_trfc),
    .dh_gs_rfmsbc                       (dh_gs_rfmsbc),
    .dh_gs_raaimt                       (dh_gs_raaimt),
    .dh_gs_raamult                      (dh_gs_raamult),
    .dh_gs_raadec                       (dh_gs_raadec),
    .dh_gs_rfmth_rm_thr                 (dh_gs_rfmth_rm_thr),
    .dh_gs_init_raa_cnt                 (dh_gs_init_raa_cnt),
    .dh_gs_t_rfmpb                      (dh_gs_t_rfmpb),
    .dh_gs_dbg_raa_rank                 (dh_gs_dbg_raa_rank),
    .dh_gs_dbg_raa_bg_bank              (dh_gs_dbg_raa_bg_bank),
    .gs_dh_dbg_raa_cnt                  (gs_dh_dbg_raa_cnt),
    .gs_dh_rank_raa_cnt_gt0             (gs_dh_rank_raa_cnt_gt0),
    .derate_operating_rm                (derate_operating_rm),
    .bank_pgmiss_exvpr_valid            (bank_pgmiss_exvpr_valid_w),
    .bank_pgmiss_exvpw_valid            (bank_pgmiss_exvpw_valid_w),
    .gs_bs_rank_rfm_required            (gs_bs_rank_rfm_required),
    .gs_bs_rfmpb_bank                   (gs_bs_rfmpb_bank),
    .gs_bs_rfmpb_sb0                    (gs_bs_rfmpb_sb0),
    .gs_bs_rank_block_act_trfm_bk_nxt   (gs_bs_rank_block_act_trfm_bk_nxt),
    .gs_bs_rank_block_act_raa_expired   (gs_bs_rank_block_act_raa_expired),
    .gs_op_is_rfm                       (gs_op_is_rfm),
    .gs_rfm_cs_n                        (gs_rfm_cs_n),
    .gs_pi_rfmpb_bank                   (gs_pi_rfmpb_bank),
    .gs_pi_rfmpb_sb0                    (gs_pi_rfmpb_sb0),
    .dh_gs_t_refi_x1_sel             (dh_gs_t_refi_x1_sel),
    .dh_gs_refresh_to_x1_sel         (dh_gs_refresh_to_x1_sel),
    .dh_gs_t_refi_x1_x32             (dh_gs_t_refi_x1_x32),
    .dh_gs_refresh_to_x1_x32            (dh_gs_refresh_to_x1_x32),
    .dh_gs_pre_cke_x1024                (dh_gs_pre_cke_x1024),
    .dh_gs_post_cke_x1024               (dh_gs_post_cke_x1024),
    .dh_gs_prefer_write                 (dh_gs_prefer_write),
    .dh_gs_rdwr_idle_gap                (dh_gs_rdwr_idle_gap),
    .dh_gs_powerdown_en                 (dh_gs_powerdown_en),
    .dh_gs_powerdown_to_x32             (dh_gs_powerdown_to_x32),
    .dh_gs_t_xp                         (dh_gs_t_xp),
    .reg_ddrc_selfref_sw                (reg_ddrc_selfref_sw),
    .reg_ddrc_hw_lp_en                  (reg_ddrc_hw_lp_en),
    .reg_ddrc_hw_lp_exit_idle_en        (reg_ddrc_hw_lp_exit_idle_en),
    .reg_ddrc_selfref_to_x32            (reg_ddrc_selfref_to_x32),
    .reg_ddrc_hw_lp_idle_x32            (reg_ddrc_hw_lp_idle_x32),
    .ddrc_reg_selfref_type              (ddrc_reg_selfref_type),
    .ih_busy                            (ih_busy),
    .hif_cmd_valid                      (hif_cmd_valid),
    .gsfsm_sr_co_if_stall               (gsfsm_sr_co_if_stall),
    .cactive_in_ddrc_sync_or            (cactive_in_ddrc_sync_or),
    .cactive_in_ddrc_async              (cactive_in_ddrc_async),
    .csysreq_ddrc                       (csysreq_ddrc),
    .csysmode_ddrc                      (csysmode_ddrc),
    .csysfrequency_ddrc                 (csysfrequency_ddrc),
    .csysdiscamdrain_ddrc               (csysdiscamdrain_ddrc),
    .csysfsp_ddrc                       (csysfsp_ddrc),
    .csysack_ddrc                       (csysack_ddrc),
    .cactive_ddrc                       (cactive_ddrc),
    .dh_gs_selfref_en                   (dh_gs_selfref_en),
    .dh_gs_mr_rank                      (dh_gs_mr_rank),
    .dh_gs_t_xsr                        (dh_gs_t_xsr),
    .dh_gs_refresh_margin               (dh_gs_refresh_margin),
    .dh_gs_rank0_wr_odt                 (dh_gs_rank0_wr_odt),
    .dh_gs_rank0_rd_odt                 (dh_gs_rank0_rd_odt),
    .dh_gs_refresh_update_level         (dh_gs_refresh_update_level),
    .derate_refresh_update_level        (derate_refresh_update_level),
    .dh_gs_refresh_timer0_start_value_x32 (dh_gs_refresh_timer0_start_value_x32),
    .dh_gs_refresh_timer1_start_value_x32 (dh_gs_refresh_timer1_start_value_x32),
    .dh_gs_rank1_wr_odt                 (dh_gs_rank1_wr_odt),
    .dh_gs_rank1_rd_odt                 (dh_gs_rank1_rd_odt),
    .reg_ddrc_prefer_read               (reg_ddrc_prefer_read),
    .dh_gs_hpr_xact_run_length          (dh_gs_hpr_xact_run_length),
    .dh_gs_hpr_max_starve               (dh_gs_hpr_max_starve),
    .dh_gs_lpr_xact_run_length          (dh_gs_lpr_xact_run_length),
    .dh_gs_lpr_max_starve               (dh_gs_lpr_max_starve),
    .dh_gs_w_xact_run_length            (dh_gs_w_xact_run_length),
    .dh_gs_w_max_starve                 (dh_gs_w_max_starve),
    .dh_gs_ctrlupd_min_to_x1024         (dh_gs_ctrlupd_min_to_x1024),
    .dh_gs_ctrlupd_max_to_x1024         (dh_gs_ctrlupd_max_to_x1024),
    .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8 (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8),
    .reg_ddrc_dfi_t_ctrlupd_interval_type1       (reg_ddrc_dfi_t_ctrlupd_interval_type1),
    .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit  (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit),
    .pi_gs_ctrlupd_ok                   (pi_gs_ctrlupd_ok),
    .pi_gs_rd_vld                       (pi_gs_rd_vld),
    .pi_gs_noxact                       (pi_gs_noxact),
//  .ih_gs_rdlow_almostfull             (ih_gs_rdlow_almostfull),
//  .ih_gs_wr_almostfull                (ih_gs_wr_almostfull),
    .ih_gs_xact_valid                   (ih_yy_xact_valid),
    .hif_go2critical_lpr                (hif_go2critical_lpr),
    .hif_go2critical_hpr                (hif_go2critical_hpr),
    .hif_go2critical_wr                 (hif_go2critical_wr),
    .hif_go2critical_l1_wr              (hif_go2critical_l1_wr ),
    .hif_go2critical_l2_wr              (hif_go2critical_l2_wr ),
    .hif_go2critical_l1_lpr             (hif_go2critical_l1_lpr),
    .hif_go2critical_l2_lpr             (hif_go2critical_l2_lpr),
    .hif_go2critical_l1_hpr             (hif_go2critical_l1_hpr),
    .hif_go2critical_l2_hpr             (hif_go2critical_l2_hpr),
    .wu_gs_enable_wr                    (wu_gs_enable_wr),
    .ih_gs_rdhigh_empty                 (ih_gs_rdhigh_empty),
    .ih_gs_rdlow_empty                  (ih_gs_rdlow_empty),
//  .ih_gs_wr_empty                     (ih_gs_wr_empty),
    .rt_gs_empty                        (rt_gs_empty),
    .mr_gs_empty                        (mr_gs_empty),
    .dh_gs_dis_dq                       (dh_gs_dis_dq),
    .te_gs_any_vpr_timed_out            (te_gs_any_vpr_timed_out),
    .ih_gs_any_vpr_timed_out            (ih_gs_any_vpr_timed_out),
    .te_gs_any_vpw_timed_out            (te_gs_any_vpw_timed_out),
    .ih_gs_any_vpw_timed_out            (ih_gs_any_vpw_timed_out),
    .te_gs_rd_flush                     (te_gs_rd_flush),
    .te_gs_wr_flush                     (te_gs_wr_flush),
    .te_gs_any_rd_pending               (te_gs_any_rd_pending),
    .te_gs_any_wr_pending               (te_gs_any_wr_pending),
    .os_gs_act_hi_vld                   (os_gs_act_hi_vld),
    .os_gs_act_hi_bsm                   (os_gs_act_hi_bsm),
    .os_gs_rdwr_hi_vld                  (os_gs_rdwr_hi_vld),
    .os_gs_rdwr_hi_bsm                  (os_gs_rdwr_hi_bsm),
    .te_gs_block_wr                     (te_gs_block_wr),
    .os_gs_act_lo_vld                   (os_gs_act_lo_vld),
    .os_gs_act_lo_bsm                   (os_gs_act_lo_bsm),
    .os_gs_rdwr_lo_vld                  (os_gs_rdwr_lo_vld),
    .os_gs_rdwr_lo_bsm                  (os_gs_rdwr_lo_bsm),
    .os_gs_pre_crit_vld                 (os_gs_pre_crit_vld),
    .os_gs_pre_crit_bsm                 (os_gs_pre_crit_bsm),
    .os_gs_pre_req_vld                  (os_gs_pre_req_mux_vld),
    .os_gs_pre_req_bsm                  (os_gs_pre_req_mux_bsm),
    .os_gs_act_wr_vld                   (os_gs_act_wr_vld),
    .os_gs_act_wr_bsm                   (os_gs_act_wr_bsm),
    .os_gs_act_wrecc_vld                (os_gs_act_wrecc_vld),
    .os_gs_act_wrecc_bsm                (os_gs_act_wrecc_bsm),
    .gs_act_pre_rd_priority             (gs_act_pre_rd_priority),
    .os_gs_rank_closed                  (os_gs_rank_closed),
    .os_gs_bank_closed                  (os_gs_bank_closed),
    .os_gs_bg_bank_closed               (os_gs_bg_bank_closed),
   .te_gs_rank_rd_valid                 (te_gs_rank_rd_valid),
   .te_gs_rank_wr_valid                 (te_gs_rank_wr_valid),
    .reg_en_dfi_dram_clk_disable        (reg_en_dfi_dram_clk_disable),
    .bs_gs_stop_clk_ok                  (bs_gs_stop_clk_ok),
    .gs_pi_ctrlupd_req                  (gs_pi_ctrlupd_req),
    .gs_pi_rd_data_pipeline_empty       (gs_pi_rd_data_pipeline_empty),
    .gs_pi_wr_data_pipeline_empty       (gs_pi_wr_data_pipeline_empty),
    .gs_pi_data_pipeline_empty          (gs_pi_data_pipeline_empty),
    .gs_pi_pads_powerdown               (gs_pi_pads_powerdown),
    .gs_pi_pads_selfref                 (gs_pi_pads_selfref),
    .gs_pi_stop_clk_ok                  (gs_pi_stop_clk_ok),
    .gs_pi_stop_clk_type                (gs_pi_stop_clk_type),
    .pi_gs_stop_clk_early               (pi_gs_stop_clk_early),
    .dfilp_ctrl_lp                      (dfilp_ctrl_lp),
    .pi_gs_stop_clk_type                (pi_gs_stop_clk_type),
    .pi_gs_dfilp_wait                   (pi_gs_dfilp_wait),
    .reg_ddrc_dfi_t_dram_clk_enable     (reg_ddrc_dfi_t_dram_clk_enable),
    .reg_ddrc_t_cksre                   (reg_ddrc_t_cksre),
    .reg_ddrc_t_cksrx                   (reg_ddrc_t_cksrx),
    .reg_ddrc_t_ckcsx                   (reg_ddrc_t_ckcsx),
    .reg_ddrc_t_ckesr                   (reg_ddrc_t_ckesr),
    .dfi_lp_ctrl_req                    (dfi_lp_ctrl_req),
    .dfi_lp_ctrl_wakeup                 (dfi_lp_ctrl_wakeup),
    .dfi_lp_ctrl_ack                    (dfi_lp_ctrl_ack),
    .dfi_lp_data_req                    (dfi_lp_data_req),
    .dfi_lp_data_wakeup                 (dfi_lp_data_wakeup),
    .dfi_lp_data_ack                    (dfi_lp_data_ack),
    .dfi_reset_n_in                     (dfi_reset_n_in),
    .dfi_reset_n_ref                    (dfi_reset_n_ref),
    .init_mr_done_in                    (init_mr_done_in),
    .init_mr_done_out                   (init_mr_done_out),
    .reg_ddrc_lpddr4_opt_act_timing     (reg_ddrc_lpddr4_opt_act_timing),
    .reg_ddrc_lpddr5_opt_act_timing     (reg_ddrc_lpddr5_opt_act_timing),
    .lpddr4_blk_act_nxt                 (lpddr4_blk_act_nxt),

    .reg_ddrc_dfi_lp_data_req_en        (reg_ddrc_dfi_lp_data_req_en),
    .reg_ddrc_dfi_lp_en_pd              (reg_ddrc_dfi_lp_en_pd),
    .reg_ddrc_dfi_lp_wakeup_pd          (reg_ddrc_dfi_lp_wakeup_pd),
    .reg_ddrc_dfi_lp_en_sr              (reg_ddrc_dfi_lp_en_sr),
    .reg_ddrc_dfi_lp_wakeup_sr          (reg_ddrc_dfi_lp_wakeup_sr),
    .reg_ddrc_dfi_lp_en_data            (reg_ddrc_dfi_lp_en_data),
    .reg_ddrc_dfi_lp_wakeup_data        (reg_ddrc_dfi_lp_wakeup_data),
    .reg_ddrc_dfi_lp_en_dsm             (reg_ddrc_dfi_lp_en_dsm),
    .reg_ddrc_dfi_lp_wakeup_dsm         (reg_ddrc_dfi_lp_wakeup_dsm),
    .reg_ddrc_dfi_tlp_resp              (reg_ddrc_dfi_tlp_resp),
    .gs_dh_selfref_cam_not_empty        (gs_dh_selfref_cam_not_empty),
    .os_gs_no_2ck_cmds_after_pre        (os_gs_no_2ck_cmds_after_pre),
    .gs_dh_selfref_state                (gs_dh_selfref_state),
    .gs_dh_operating_mode               (gs_dh_operating_mode),
    .gs_op_is_enter_sr_lpddr            (gs_op_is_enter_sr_lpddr),
    .gs_op_is_exit_sr_lpddr             (gs_op_is_exit_sr_lpddr),
    .gs_op_is_enter_dsm                 (gs_op_is_enter_dsm),
    .gs_op_is_exit_dsm                  (gs_op_is_exit_dsm),
    .gs_op_is_cas_ws_off                (gs_op_is_cas_ws_off),
    .gs_op_is_cas_wck_sus               (gs_op_is_cas_wck_sus),
    .gs_wck_stop_ok                     (gs_wck_stop_ok),

    .gs_op_is_rd                        (gs_op_is_rd),
    .gs_op_is_wr                        (gs_op_is_wr),
    .gs_op_is_act                       (gs_op_is_act),
    .gs_op_is_pre                       (gs_op_is_pre),
    .gs_op_is_ref                       (gs_op_is_ref),
    .gs_op_is_enter_selfref             (gs_op_is_enter_selfref_pre),
    .gs_op_is_exit_selfref              (gs_op_is_exit_selfref_pre),
    .gs_op_is_enter_powerdown           (gs_op_is_enter_powerdown),
    .gs_op_is_exit_powerdown            (gs_op_is_exit_powerdown),
    .gs_op_is_load_mode                 (gs_op_is_load_mode),

    .gs_rdwr_cs_n                       (gs_rdwr_cs_n),
    .gs_act_cs_n                        (gs_act_cs_n),
    .gs_pre_cs_n                        (gs_pre_cs_n),
    .gs_ref_cs_n                        (gs_ref_cs_n),
    .gs_other_cs_n                      (gs_other_cs_n),
    .gs_rdwr_bsm_num                    (gs_rdwr_bsm_num),
    .gs_act_bsm_num                     (gs_act_bsm_num),
    .gs_pre_bsm_num                     (gs_pre_bsm_num),

    .gs_pre_rankbank_num                (gs_pre_rankbank_num),
    .gs_rdwr_rankbank_num               (gs_rdwr_rankbank_num),
    .gs_act_rankbank_num                (gs_act_rankbank_num),
    .gs_pi_refpb_bank                   (gs_pi_refpb_bank),
    .gs_cas_ws_req                      (gs_cas_ws_req),
    .pi_rdwr_ok                         (pi_rdwr_ok),
    .pi_col_b3                          (pi_col_b3),
    .pi_lp5_act2_cmd                    (pi_lp5_act2_cmd),
    .pi_lp5_noxact                      (pi_lp5_noxact),
    .pi_lp5_preref_ok                   (pi_lp5_preref_ok),

    .gs_wr_mode                         (gs_wr_mode),
    .gs_te_wr_possible                  (gs_te_wr_possible),
    .gs_te_pri_level                    (gs_te_pri_level),
    .gs_dh_hpr_q_state                  (gs_dh_hpr_q_state),
    .gs_dh_lpr_q_state                  (gs_dh_lpr_q_state),
    .gs_dh_w_q_state                    (gs_dh_w_q_state),
    .gs_bs_rank_refresh_required        (gs_bs_rank_refresh_required[NUM_LRANKS-1:0]),
    .gs_bs_rank_refresh_required_early  (gs_bs_rank_refresh_required_early[NUM_LRANKS-1:0]),
    .gs_bs_bank_speculative_ref         (gs_bs_bank_speculative_ref),
    .gs_rank_block_cas_b3_nxt           (gs_rank_block_cas_b3_nxt),
    .gs_bs_rank_act2_invalid_tmg_nxt    (gs_bs_rank_act2_invalid_tmg_nxt),
    .gs_bs_rank_block_act_nxt           (gs_bs_rank_block_act_nxt),
    .gs_bs_rank_block_act_trfc_bk_nxt   (gs_bs_rank_block_act_trfc_bk_nxt),
    .gs_bs_rank_block_act_trrd_bg_nxt   (gs_bs_rank_block_act_trrd_bg_nxt),
    .gs_bs_rank_block_act_ref_req       (gs_bs_rank_block_act_ref_req),
    .gs_bs_rank_block_rd_nxt            (gs_bs_rank_block_rd_nxt),
    .gs_bs_rank_block_wr_nxt            (gs_bs_rank_block_wr_nxt),
    .gs_bs_close_pages                  (gs_bs_close_pages),
    .gs_bs_zq_calib_short_required      (gs_bs_zq_calib_short_required),
    .gs_bs_load_mr_norm_required        (gs_bs_load_mr_norm_required),
    .gs_pi_mrr                          (gs_pi_mrr),
    .gs_pi_mrr_ext                      (gs_pi_mrr_ext),
    .dh_gs_mr4_req                      (dh_gs_mr4_req),
    .dh_gs_mr4_req_rank                 (dh_gs_mr4_req_rank),
    .dh_gs_per_bank_refresh             (dh_gs_per_bank_refresh),
    .dh_gs_per_bank_refresh_opt_en      (dh_gs_per_bank_refresh_opt_en),
    .dh_gs_fixed_crit_refpb_bank_en     (dh_gs_fixed_crit_refpb_bank_en),
    .per_bank_refresh                   (per_bank_refresh_int),
    .gs_bs_refpb_bank                   (gs_bs_refpb_bank),
    .gs_pi_init_cke                     (gs_pi_init_cke),
    .gs_pi_mrs_a                        (gs_pi_mrs_a),
    .gs_mpc_zq_start                    (gs_mpc_zq_start),
    .gs_mpc_zq_latch                    (gs_mpc_zq_latch),
    .mr4_req_o                          (mr4_req_o),
    .gs_pi_init_in_progress             (gs_pi_init_in_progress),
    .gs_pi_odt                          (gs_pi_odt),
    .gs_pi_odt_pending                  (gs_pi_odt_pending),
    .reg_ddrc_dfi_tphy_wrlat                     (reg_ddrc_dfi_tphy_wrlat),
    .reg_ddrc_dfi_t_rddata_en                    (reg_ddrc_dfi_t_rddata_en),
    .reg_ddrc_dfi_tphy_wrcslat          (reg_ddrc_dfi_tphy_wrcslat),
    .reg_ddrc_dfi_tphy_rdcslat          (reg_ddrc_dfi_tphy_rdcslat),
    .gs_pi_wrdata_cs_n                  (gs_pi_wrdata_cs_n),
    .gs_pi_rddata_cs_n                  (gs_pi_rddata_cs_n),
    .reg_ddrc_dfi_data_cs_polarity      (reg_ddrc_dfi_data_cs_polarity),

    .gs_os_wr_mode_early                (gs_os_wr_mode_early),
    .gs_bs_wr_mode_early                (gs_bs_wr_mode_early),

    .gs_bs_t_rfc_min_upd                (gs_bs_t_rfc_min_upd_unused),
    .gs_bs_refresh_margin_upd           (gs_bs_refresh_margin_upd),

    .phy_dfi_phyupd_req                 (phy_dfi_phyupd_req),
    .phy_dfi_phyupd_req_r               (phy_dfi_phyupd_req_r),
    .ddrc_dfi_phyupd_ack                (ddrc_dfi_phyupd_ack),

    .phy_dfi_phymstr_req                (phy_dfi_phymstr_req),
    .phy_dfi_phymstr_cs_state           (phy_dfi_phymstr_cs_state),
    .phy_dfi_phymstr_state_sel          (phy_dfi_phymstr_state_sel),
    .phy_dfi_phymstr_type               (phy_dfi_phymstr_type),
    .ddrc_dfi_phymstr_ack               (ddrc_dfi_phymstr_ack),

    .reg_ddrc_dfi_phyupd_en             (reg_ddrc_dfi_phyupd_en),
    .reg_ddrc_dfi_phymstr_en            (reg_ddrc_dfi_phymstr_en),
    .reg_ddrc_dfi_phymstr_blk_ref_x32   (reg_ddrc_dfi_phymstr_blk_ref_x32),
    .reg_ddrc_dis_cam_drain_selfref     (i_reg_ddrc_dis_cam_drain_selfref),
    .reg_ddrc_lpddr4_sr_allowed         (reg_ddrc_lpddr4_sr_allowed),
    .reg_ddrc_dfi_t_ctrl_delay          (reg_ddrc_dfi_t_ctrl_delay),
    .reg_ddrc_dfi_t_wrdata_delay        (reg_ddrc_dfi_t_wrdata_delay),
    .gs_pi_phyupd_pause_req             (gs_pi_phyupd_pause_req),
    .pi_gs_phyupd_pause_ok              (pi_gs_phyupd_pause_ok),
    .gs_pi_dfi_lp_changing              (gs_pi_dfi_lp_changing),
    .reg_ddrc_skip_dram_init            (reg_ddrc_skip_dram_init),
    .gsfsm_dis_dq                       (gsfsm_dis_dq)



  , .reg_ddrc_target_frequency          (reg_ddrc_target_frequency)
  , .reg_ddrc_t_vrcg_enable             (reg_ddrc_t_vrcg_enable)
  , .reg_ddrc_t_vrcg_disable            (reg_ddrc_t_vrcg_disable)
  , .reg_ddrc_target_vrcg               (reg_ddrc_target_vrcg)
  , .reg_ddrc_hwffc_en                  (reg_ddrc_hwffc_en)
  , .reg_ddrc_init_fsp                  (reg_ddrc_init_fsp)
  , .reg_ddrc_t_zq_stop                 (reg_ddrc_t_zq_stop)
  , .reg_ddrc_zq_interval               (reg_ddrc_zq_interval)
  , .reg_ddrc_skip_zq_stop_start        (reg_ddrc_skip_zq_stop_start)
  , .reg_ddrc_init_vrcg                 (reg_ddrc_init_vrcg)
  , .reg_ddrc_skip_mrw_odtvref          (reg_ddrc_skip_mrw_odtvref)
  , .reg_ddrc_dvfsq_enable              (reg_ddrc_dvfsq_enable)
  , .reg_ddrc_dvfsq_enable_next         (reg_ddrc_dvfsq_enable_next)
  , .ddrc_reg_hwffc_in_progress         (ddrc_reg_hwffc_in_progress)
  , .ddrc_reg_current_frequency         (ddrc_reg_current_frequency)
  , .ddrc_reg_current_fsp               (ddrc_reg_current_fsp)
  , .ddrc_reg_current_vrcg              (ddrc_reg_current_vrcg)
  , .ddrc_reg_hwffc_operating_mode      (ddrc_reg_hwffc_operating_mode)
  , .hwffc_dis_zq_derate                (hwffc_dis_zq_derate)
  , .hwffc_hif_wd_stall                 (hwffc_hif_wd_stall)
  , .ddrc_xpi_port_disable_req          (ddrc_xpi_port_disable_req)
  , .ddrc_xpi_clock_required            (ddrc_xpi_clock_required)
  , .xpi_ddrc_port_disable_ack          (xpi_ddrc_port_disable_ack)
  , .xpi_ddrc_wch_locked                (xpi_ddrc_wch_locked)
  , .te_gs_rank_wr_pending          (te_gs_rank_wr_pending)
  , .te_gs_rank_rd_pending          (te_gs_rank_rd_pending)
  , .te_gs_bank_wr_pending          (te_gs_bank_wr_pending)
  , .te_gs_bank_rd_pending          (te_gs_bank_rd_pending)

  ,.gs_phymstr_sre_req        (gs_phymstr_sre_req)
  ,.gs_bs_sre_stall           (gs_bs_sre_stall)
  ,.gs_bs_sre_hw_sw           (gs_bs_sre_hw_sw)
  ,.reg_ddrc_hwffc_mode       (reg_ddrc_hwffc_mode)

  // Frequency selection
  ,.hwffc_target_freq_en      (hwffc_target_freq_en)
  ,.hwffc_target_freq         (hwffc_target_freq)
  ,.hwffc_target_freq_init    (hwffc_target_freq_init)
  // DFI frequency change I/F
  ,.hwffc_freq_change         (hwffc_freq_change)
  ,.hwffc_dfi_init_start      (hwffc_dfi_init_start)
  ,.hwffc_dfi_frequency       (hwffc_dfi_frequency)
  ,.hwffc_dfi_freq_fsp        (hwffc_dfi_freq_fsp)
    ,.dfi_init_start            (dfi_init_start)
    ,.dh_bs_t_ccd               (dh_bs_t_ccd)
    ,.dh_bs_wr2rd               (dh_bs_wr2rd)
    ,.dh_bs_t_ccd_s             (dh_bs_t_ccd_s)
    ,.dh_bs_wr2rd_s             (dh_bs_wr2rd_s)
    ,.reg_ddrc_rd2wr_s          (reg_ddrc_rd2wr_s)
    ,.reg_ddrc_mrr2rd           (reg_ddrc_mrr2rd)
    ,.reg_ddrc_mrr2wr           (reg_ddrc_mrr2wr)
    ,.reg_ddrc_mrr2mrw          (reg_ddrc_mrr2mrw)
    ,.gs_bs_blk_ccd_timer       (gs_bs_blk_ccd_timer)
    ,.gs_bs_blk_wr2rd_timer     (gs_bs_blk_wr2rd_timer)
    ,.gs_bs_blk_rd2wr_timer     (gs_bs_blk_rd2wr_timer)
    ,.reg_ddrc_opt_wrcam_fill_level   (reg_ddrc_opt_wrcam_fill_level)
    ,.reg_ddrc_delay_switch_write     (reg_ddrc_delay_switch_write)

    ,.te_bs_rd_page_hit        (te_bs_rd_page_hit)       // banks with reads pending to open pages
    ,.te_bs_rd_valid           (te_bs_rd_valid   )       // banks with reads pending
    ,.te_bs_wr_page_hit        (te_bs_wr_page_hit)       // banks with writes pending to open pages
    ,.te_bs_wr_valid           (te_bs_wr_valid   )       // banks with writes pending
    ,.te_ts_vpw_valid          (te_ts_vpw_valid)
    ,.te_ts_vpr_valid          (te_ts_vpr_valid)
    ,.gs_ts_any_vpr_timed_out   (gs_ts_any_vpr_timed_out)
    ,.gs_ts_any_vpw_timed_out   (gs_ts_any_vpw_timed_out)
    ,.rd_more_crit             (rd_more_crit)
    ,.wr_more_crit             (wr_more_crit)
    ,.sel_act_wr               (sel_act_wr)
    ,.bank_activated_early     (bank_activated_early)
    ,.bank_wr_activated_early  (bank_wr_activated_early)
    ,.te_rws_wr_col_bank       (te_rws_wr_col_bank)
    ,.te_rws_rd_col_bank       (te_rws_rd_col_bank)
    ,.wr_cam_up_highth         (wr_cam_up_highth)
    ,.wr_cam_up_lowth          (wr_cam_up_lowth)
    ,.wrecc_cam_up_highth         (wrecc_cam_up_highth)
    ,.wrecc_cam_up_highth_loaded  (wrecc_cam_up_highth_loaded)
    ,.wrecc_cam_up_lowth          (wrecc_cam_up_lowth)
    ,.wr_cam_up_wrecc_highth      (wr_cam_up_wrecc_highth)
    ,.te_gs_wrecc_ntt             (i_wrecc_entry)
    ,.gs_te_force_btt             (ts_te_force_btt)
    ,.wr_pghit_up_thresh       (wr_pghit_up_thresh)
    ,.rd_pghit_up_thresh       (rd_pghit_up_thresh)
    ,.delay_switch_write_state (delay_switch_write_state)
    ,.reg_ddrc_dis_opt_ntt_by_act (reg_ddrc_dis_opt_ntt_by_act)
   ,.te_rd_bank_pghit_vld_prefer  (te_rd_bank_pghit_vld_prefer)
   ,.te_wr_bank_pghit_vld_prefer  (te_wr_bank_pghit_vld_prefer)
   ,.te_gs_rank_wr_prefer         (te_gs_rank_wr_prefer)
   ,.te_gs_rank_rd_prefer         (te_gs_rank_rd_prefer)
   ,.reg_ddrc_wck_on              (reg_ddrc_wck_on)
   ,.reg_ddrc_wck_suspend_en      (reg_ddrc_wck_suspend_en)
   ,.reg_ddrc_ws_off_en           (reg_ddrc_ws_off_en)
   ,.reg_ddrc_ws_off2ws_fs        (reg_ddrc_ws_off2ws_fs)
   ,.reg_ddrc_t_wcksus            (reg_ddrc_t_wcksus)
   ,.reg_ddrc_ws_fs2wck_sus       (reg_ddrc_ws_fs2wck_sus)
   ,.reg_ddrc_max_rd_sync         (reg_ddrc_max_rd_sync)
   ,.reg_ddrc_max_wr_sync         (reg_ddrc_max_wr_sync)
   ,.reg_ddrc_dfi_twck_delay      (reg_ddrc_dfi_twck_delay)
   ,.reg_ddrc_dfi_twck_en_rd      (reg_ddrc_dfi_twck_en_rd)
   ,.reg_ddrc_dfi_twck_en_wr      (reg_ddrc_dfi_twck_en_wr)
   ,.reg_ddrc_dfi_twck_en_fs      (reg_ddrc_dfi_twck_en_fs)
   ,.reg_ddrc_dfi_twck_dis        (reg_ddrc_dfi_twck_dis)
   ,.reg_ddrc_dfi_twck_fast_toggle(reg_ddrc_dfi_twck_fast_toggle)
   ,.reg_ddrc_dfi_twck_toggle     (reg_ddrc_dfi_twck_toggle)
   ,.reg_ddrc_dfi_twck_toggle_cs  (reg_ddrc_dfi_twck_toggle_cs)
   ,.reg_ddrc_dfi_twck_toggle_post(reg_ddrc_dfi_twck_toggle_post)
   ,.reg_ddrc_dfi_twck_toggle_post_rd_en(reg_ddrc_dfi_twck_toggle_post_rd_en)
   ,.reg_ddrc_dfi_twck_toggle_post_rd   (reg_ddrc_dfi_twck_toggle_post_rd)
   ,.gs_dfi_wck_cs                (gs_dfi_wck_cs)
   ,.gs_dfi_wck_en                (gs_dfi_wck_en)
   ,.gs_dfi_wck_toggle            (gs_dfi_wck_toggle)
   ,.reg_ddrc_dqsosc_enable       (reg_ddrc_dqsosc_enable)
   ,.reg_ddrc_t_osco              (reg_ddrc_t_osco)
   ,.reg_ddrc_dqsosc_runtime      (reg_ddrc_dqsosc_runtime)
   ,.reg_ddrc_wck2dqo_runtime     (reg_ddrc_wck2dqo_runtime)
   ,.reg_ddrc_dqsosc_interval     (reg_ddrc_dqsosc_interval)
   ,.reg_ddrc_dqsosc_interval_unit(reg_ddrc_dqsosc_interval_unit)
   ,.reg_ddrc_dis_dqsosc_srx      (reg_ddrc_dis_dqsosc_srx)
   ,.dqsosc_state                 (dqsosc_state)
   ,.dqsosc_running               (dqsosc_running)
   ,.dqsosc_per_rank_stat         (dqsosc_per_rank_stat)
   ,.gs_mpc_dqsosc_start          (gs_mpc_dqsosc_start)
   ,.gs_pi_mrr_snoop_en           (gs_pi_mrr_snoop_en)
   ,.dqsosc_block_other_cmd       (dqsosc_block_other_cmd)
   ,.ddrc_co_perf_op_is_dqsosc_mpc_w        (ddrc_co_perf_op_is_dqsosc_mpc_w)
   ,.ddrc_co_perf_op_is_dqsosc_mrr_w        (ddrc_co_perf_op_is_dqsosc_mrr_w)
    ,.reg_ddrc_t_pgm_x1_x1024  (reg_ddrc_t_pgm_x1_x1024)
    ,.reg_ddrc_t_pgm_x1_sel    (reg_ddrc_t_pgm_x1_sel)
    ,.reg_ddrc_t_pgmpst_x32    (reg_ddrc_t_pgmpst_x32)
    ,.reg_ddrc_t_pgm_exit      (reg_ddrc_t_pgm_exit)
    ,.reg_ddrc_ppr_en          (reg_ddrc_ppr_en)
    ,.ddrc_reg_ppr_done        (ddrc_reg_ppr_done)
    ,.reg_ddrc_ppr_pgmpst_en   (reg_ddrc_ppr_pgmpst_en)
    ,.reg_ddrc_ppt2_en                   (reg_ddrc_ppt2_en)
    ,.reg_ddrc_ctrlupd_after_dqsosc      (reg_ddrc_ctrlupd_after_dqsosc)
    ,.reg_ddrc_ppt2_wait_ref             (reg_ddrc_ppt2_wait_ref)
    ,.reg_ddrc_ppt2_burst_num            (reg_ddrc_ppt2_burst_num)
    ,.reg_ddrc_ppt2_burst                (reg_ddrc_ppt2_burst)
    ,.ddrc_reg_ppt2_burst_busy           (ddrc_reg_ppt2_burst_busy)
    ,.ddrc_reg_ppt2_state                (ddrc_reg_ppt2_state)
    ,.reg_ddrc_ppt2_ctrlupd_num_dfi1     (reg_ddrc_ppt2_ctrlupd_num_dfi1)
    ,.reg_ddrc_ppt2_ctrlupd_num_dfi0     (reg_ddrc_ppt2_ctrlupd_num_dfi0)
    ,.ppt2_stop_clk_req                  (ppt2_stop_clk_req)
);

assign gs_op_is_enter_selfref = gs_op_is_enter_selfref_pre;
assign gs_op_is_exit_selfref  = gs_op_is_exit_selfref_pre;



`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
// ts_assertions instance
// contains TS related assertions and coverage points
ts_assertions
 ts_assertions (
    .clk                                (co_yy_clk),
    .core_ddrc_rstn                     (core_ddrc_rstn),
    // vlds
    .bs_os_rdwr_hi_vlds                 (bs_os_rdwr_hi_vlds_vpr),
    .bs_os_act_hi_vlds                  (bs_os_act_hi_vlds),
    .bs_os_rdwr_lo_vlds                 (bs_os_rdwr_lo_vlds_vprw),
    .bs_os_act_lo_vlds                  (bs_os_act_lo_vlds),
    .bs_os_pre_req_vlds                 (bs_os_pre_req_vlds),
    .bs_os_pre_crit_vlds                (bs_os_pre_crit_vlds),
    .bs_os_act_wr_vlds                  (bs_os_act_wr_vlds),
    .bs_os_act_wrecc_vlds               (bs_os_act_wrecc_vlds),
    .bs_os_pre_req_wr_vlds              (bs_os_pre_req_wr_vlds),
    // wall_next
    .hi_rdwr_bsm_hint                   (hi_rdwr_bsm_hint),
    .hi_act_bsm_hint                    (hi_act_bsm_hint),
    .lo_rdwr_bsm_hint                   (lo_rdwr_bsm_hint),
    .lo_act_bsm_hint                    (lo_act_bsm_hint),
    .pre_req_bsm_hint                   (pre_req_bsm_hint),
    .wr_act_bsm_hint                    (wr_act_bsm_hint),
    .wrecc_act_bsm_hint                 (wrecc_act_bsm_hint),
    .wr_pre_req_bsm_hint                (wr_pre_req_bsm_hint),
    // selected_vld
    .os_gs_rdwr_hi_vld                  (os_gs_rdwr_hi_vld),
    .os_gs_act_hi_vld                   (os_gs_act_hi_vld),
    .os_gs_rdwr_lo_vld                  (os_gs_rdwr_lo_vld),
    .os_gs_act_lo_vld                   (os_gs_act_lo_vld),
    .os_gs_pre_req_vld                  (os_gs_pre_req_vld),
    .os_gs_pre_crit_vld                 (os_gs_pre_crit_vld),
    .os_gs_act_wr_vld                   (os_gs_act_wr_vld),
    .os_gs_act_wrecc_vld                (os_gs_act_wrecc_vld),
    .os_gs_pre_req_wr_vld               (os_gs_pre_req_wr_vld),
    // selected
    .os_gs_rdwr_hi_bsm                  (os_gs_rdwr_hi_bsm),
    .os_gs_act_hi_bsm                   (os_gs_act_hi_bsm),
    .os_gs_rdwr_lo_bsm                  (os_gs_rdwr_lo_bsm),
    .os_gs_act_lo_bsm                   (os_gs_act_lo_bsm),
    .os_gs_pre_req_bsm                  (os_gs_pre_req_bsm),
    .os_gs_pre_crit_bsm                 (os_gs_pre_crit_bsm)
   ,.os_gs_act_wr_bsm                   (os_gs_act_wr_bsm),
    .os_gs_act_wrecc_bsm                (os_gs_act_wrecc_bsm),
    .os_gs_pre_req_wr_bsm               (os_gs_pre_req_wr_bsm),
    .ts_act_page                        (ts_act_page),
    .act_hi_tag_selected                (act_hi_tag_selected),
    .act_lo_tag_selected                (act_lo_tag_selected),
    .act_wrecc_tag_selected             (act_wrecc_tag_selected),
    .act_wr_tag_selected                (act_wr_tag_selected),

    .gs_act_pre_rd_priority             (gs.gs_next_xact.gs_act_pre_rd_priority),
    .reverse_priority                   (gs.gs_next_xact.reverse_priority),
    .no_rdwr_cmd                        (gs.gs_next_xact.no_rdwr_cmd),
    .no_critical_cmd                    (gs.gs_next_xact.no_critical_cmd),
    .dh_gs_per_bank_refresh             (gs.gs_next_xact.dh_gs_per_bank_refresh),
    .no_critical_global_cmd             (gs.gs_next_xact.no_critical_global_cmd),
    .block_t_xs                         (gs.gs_next_xact.block_t_xs),
    .no_ops_allowed                     (gs.gs_next_xact.no_ops_allowed),
    .pi_gs_noxact                       (gs.gs_next_xact.pi_gs_noxact),
    .critical_ref_possible_wo_trrd      (gs.gs_next_xact.critical_ref_possible_wo_trrd),
    .gs_act_cs_n                        (gs.gs_next_xact.gs_act_cs_n),
    .gs_cas_ws_req                      (gs.gs_next_xact.gs_cas_ws_req),
    .wr_mode                            (gs.gs_next_xact.wr_mode),
    .pi_col_b3                          (gs.gs_next_xact.pi_col_b3),
    .gs_hw_mr_norm_busy                 (gs.gs_next_xact.gs_hw_mr_norm_busy),
    .dh_gs_2t_mode                      (gs.gs_next_xact.dh_gs_2t_mode),
    .dh_gs_frequency_ratio              (gs.gs_next_xact.dh_gs_frequency_ratio),
    .dh_gs_lpddr4                       (gs.gs_next_xact.dh_gs_lpddr4),
    .reg_ddrc_lpddr5                    (reg_ddrc_lpddr5),
    .rank_block_pre                     (gs.gs_next_xact.rank_block_pre),
    .choose_ref_req                     (gs.gs_next_xact.choose_ref_req),
    .rank_nop_after_zqcs                (gs.gs_next_xact.rank_nop_after_zqcs),
    .speculative_ref_possible           (gs.gs_next_xact.speculative_ref_possible),
    .critical_ref_possible              (gs.gs_next_xact.critical_ref_possible),
    .rfm_possible                       (gs.gs_next_xact.rfm_possible),
    .no_simul_cmd_pre                   (gs.gs_next_xact.no_simul_cmd_pre),
    .gs_pre_cs_n                        (gs.gs_next_xact.gs_pre_cs_n),
    .gs_ts_any_vpr_timed_out            (gs_ts_any_vpr_timed_out),
    .gs_ts_any_vpw_timed_out            (gs_ts_any_vpw_timed_out),
    .rd_more_crit                       (rd_more_crit),
    .wr_more_crit                       (wr_more_crit),
    .gs_wr_mode                         (gs_wr_mode),
    .gs_te_pri_level                    (gs_te_pri_level)
   ,.gs_op_is_act                       (gs_op_is_act)
   ,.gs_op_is_pre                       (gs_op_is_pre)
   ,.gs_act_bsm_num                     (gs_act_bsm_num)
   ,.gs_pre_bsm_num                     (gs_pre_bsm_num)
   ,.te_gs_rank_rd_valid                (te_gs_rank_rd_valid)
   ,.te_gs_rank_wr_valid                (te_gs_rank_wr_valid)
   ,.gs_op_is_rd                        (gs_op_is_rd)
   ,.gs_op_is_wr                        (gs_op_is_wr)
   ,.gs_rdwr_rankbank_num               (gs_rdwr_rankbank_num)
   ,.gs_pre_rankbank_num                (gs_pre_rankbank_num)
   ,.gs_act_rankbank_num                (gs_act_rankbank_num)
   ,.te_rws_rd_col_bank                 (te_rws_rd_col_bank)
   ,.te_rws_wr_col_bank                 (te_rws_wr_col_bank)
);
`endif // `ifndef SYNTHESIS


`endif // SNPS_ASSERT_ON

`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
property p_wr_cam_up_highth_chk;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        reg_ddrc_opt_wrcam_fill_level && (~wr_cam_thresh_run_length_satisfied) &&  ($countones(te_ts_wr_entry_valid[WR_CAM_ENTRIES-1:0]) + reg_ddrc_wrcam_highthresh)> WR_CAM_ENTRIES |-> wr_cam_up_highth;
endproperty

a_wr_cam_up_highth_chk: assert property (p_wr_cam_up_highth_chk)
    else $error("Inline SVA [%t][%m] FAILED", $time);

property p_wr_cam_up_lowth_chk;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        reg_ddrc_opt_wrcam_fill_level && (~wr_cam_thresh_run_length_satisfied) &&  ($countones(te_ts_wr_entry_valid[WR_CAM_ENTRIES-1:0]) + reg_ddrc_wrcam_lowthresh)> WR_CAM_ENTRIES |-> wr_cam_up_lowth;
endproperty

a_wr_cam_up_lowth_chk: assert property (p_wr_cam_up_lowth_chk)
    else $error("Inline SVA [%t][%m] FAILED", $time);

property p_wrecc_cam_up_highth_chk;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        reg_ddrc_opt_wrcam_fill_level && (~wr_cam_thresh_run_length_satisfied) &&  ~reg_ddrc_dis_opt_valid_wrecc_cam_fill_level && ($countones(te_ts_wr_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]) + reg_ddrc_wrecc_cam_highthresh)> (WR_CAM_ENTRIES_IE - WR_CAM_ENTRIES) |-> wrecc_cam_up_highth;
endproperty

a_wrecc_cam_up_highth_chk: assert property (p_wrecc_cam_up_highth_chk)
    else $error("Inline SVA [%t][%m] FAILED", $time);

property p_wrecc_cam_up_lowth_chk;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        reg_ddrc_opt_wrcam_fill_level && (~wr_cam_thresh_run_length_satisfied) &&  ~reg_ddrc_dis_opt_valid_wrecc_cam_fill_level && ($countones(te_ts_wr_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]) + reg_ddrc_wrecc_cam_lowthresh)> (WR_CAM_ENTRIES_IE - WR_CAM_ENTRIES) |-> wrecc_cam_up_lowth;
endproperty

a_wrecc_cam_up_lowth_chk: assert property (p_wrecc_cam_up_lowth_chk)
    else $error("Inline SVA [%t][%m] FAILED", $time);

property p_wr_cam_thresh_enh_flag_bit_chk;
     @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
       (|dh_gs_w_max_starve) && reg_ddrc_opt_wrcam_fill_level && (($countones(te_ts_wr_entry_valid[WR_CAM_ENTRIES-1:0]) + reg_ddrc_wrcam_lowthresh) > WR_CAM_ENTRIES) && (wr_cam_thresh_run_length_cnt == 8'h00) && gs_op_is_wr |=> wr_cam_thresh_run_length_satisfied;
endproperty

a_wr_cam_thresh_enh_flag_bit_chk: assert property (p_wr_cam_thresh_enh_flag_bit_chk)
    else $error("Inline SVA [%t][%m] FAILED, when WR CAM threshhold Enhance enable, if dh_gs_w_xact_run_length write commands are served and the WR CAM fill-level is still over lowthreshold, flag bit wr_cam_thresh_run_length_satisfied not assert", $time);

property p_wr_cam_thresh_enh_flag_bit_clear_chk;
     @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        (|dh_gs_w_max_starve) && reg_ddrc_opt_wrcam_fill_level && (wr_cam_thresh_starve_cnt == 16'h0000) && wr_cam_thresh_run_length_satisfied && (~gs_op_is_wr | (wr_cam_thresh_run_length_cnt != 8'h00)) |=> ~wr_cam_thresh_run_length_satisfied;
endproperty

a_wr_cam_thresh_enh_flag_bit_clear_chk: assert property (p_wr_cam_thresh_enh_flag_bit_clear_chk)
    else $error("Inline SVA [%t][%m] FAILED, when WR CAM threshhold Enhance enable, if flag bit wr_cam_thresh_run_length_satisfied assert and the timer used for serving read command is timeout, the flag bit hasn't reset", $time);

reg [7:0]  wr_cmd_served_cnt;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
     if(~core_ddrc_rstn) begin
         wr_cmd_served_cnt <= 8'h00;
     end else begin
         if(gs_op_is_rd) begin
                wr_cmd_served_cnt <= 8'h00;
         end else if(wr_cam_up_lowth & gs_op_is_wr & (wr_cmd_served_cnt != dh_gs_w_xact_run_length)) begin
                wr_cmd_served_cnt <= wr_cmd_served_cnt + 8'h01;
         end
     end
end

wire [NUM_TOTAL_BSMS-1:0] wr_col_bank_page_hit;
wire [NUM_TOTAL_BSMS-1:0] rd_col_bank_page_hit;
assign rd_col_bank_page_hit = te_rws_rd_col_bank & te_bs_rd_valid & te_bs_rd_page_hit;
assign wr_col_bank_page_hit = te_rws_wr_col_bank & te_bs_wr_valid & te_bs_wr_page_hit;

wire any_wrecc_pghit;
assign any_wrecc_pghit = |(te_bs_wr_valid & te_bs_wr_page_hit & i_wrecc_entry);

wire any_vpr_pghit;
assign any_vpr_pghit = | (te_ts_vpr_valid & te_bs_rd_valid & te_bs_rd_page_hit);

wire any_vpw_pghit;
assign any_vpw_pghit = | (te_ts_vpw_valid & te_bs_wr_valid & te_bs_wr_page_hit);

wire wr_cam_thresh_enh_wr_to_rd_crit;
assign wr_cam_thresh_enh_wr_to_rd_crit=
     (gs_dh_operating_mode == 2'b01)
     && (|dh_gs_w_max_starve) && reg_ddrc_opt_wrcam_fill_level
     && ((wr_cmd_served_cnt == dh_gs_w_xact_run_length) && te_wr_entry_avail < {1'b0,reg_ddrc_wrcam_lowthresh})
     && ~(any_vpr_pghit)
     && ~(any_vpw_pghit)
     && ~(|wr_col_bank_page_hit)
     && ~(|rd_col_bank_page_hit)
     && ~(wr_more_crit)
     && ~(any_wrecc_pghit)
     && (gs_wr_mode)
     && (te_gs_any_rd_pending & (|(te_bs_rd_valid & te_bs_rd_page_hit)) & rd_more_crit)
     && ~(gs_bs_close_pages);  //This signal used to mask the cases that global state machine entered GS_ST_SELFREF_ENT from GS_ST_NORMAL_WR with rd critical 

property p_wr_cam_thresh_enh_wr_to_rd_crit_chk;
     @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
     wr_cam_thresh_enh_wr_to_rd_crit |=> ~gs_wr_mode;
endproperty

a_wr_cam_thresh_enh_wr_to_rd_crit_chk: assert property (p_wr_cam_thresh_enh_wr_to_rd_crit_chk)
    else $error("Inline SVA [%t][%m] FAILED, when WR CAM threshhold Enhance enable, dh_gs_w_xact_run_length write commands are served and the WR CAM fill-level is still over lowthreshold, flag bit wr_cam_thresh_run_length_satisfied assert, if read cam is critical, wr mode not swith to read mode", $time);


covergroup cg_wrcam_thresh @(posedge co_yy_clk);

    cp_reg_ddrc_opt_wrcam_fill_level: coverpoint ({reg_ddrc_opt_wrcam_fill_level}) iff(core_ddrc_rstn && rdwr_pol_sel) {}

    cp_wrcam_high_low_thresh: coverpoint ({reg_ddrc_wrcam_highthresh, reg_ddrc_wrcam_lowthresh}) iff(core_ddrc_rstn && rdwr_pol_sel) {
                    bins        watermark_0    =   {0, 0                                                     };
                    bins        watermark_1    =   {0, 1                                                     };
                    bins        watermark_2    =   {1, 1                                                     };
                    bins        watermark_3    =   {[1:1<<(WR_CAM_ADDR_BITS-2)], [1<<(WR_CAM_ADDR_BITS-2):1<<(WR_CAM_ADDR_BITS-1)]};
                    bins        watermark_4    =   {{WR_CAM_ADDR_BITS{1'b1}}-1, {RD_CAM_ADDR_BITS{1'b1}}     };
                    bins        watermark_5    =   {{WR_CAM_ADDR_BITS{1'b1}}-1, {RD_CAM_ADDR_BITS{1'b1}}-1   };
                    bins        watermark_6    =   {{WR_CAM_ADDR_BITS{1'b1}}, {RD_CAM_ADDR_BITS{1'b1}}       };
    }

    cp_wrecc_cam_high_low_thresh: coverpoint ({reg_ddrc_wrecc_cam_highthresh, reg_ddrc_wrecc_cam_lowthresh}) iff(core_ddrc_rstn && rdwr_pol_sel) {
                    bins        watermark_1    =   {0, 1                                                     };
                    bins        watermark_2    =   {1, 1                                                     };
                    bins        watermark_0    =   {0, 0                                                     };
                    bins        watermark_3    =   {[1:1<<(WR_CAM_ADDR_BITS-3)], [1<<(WR_CAM_ADDR_BITS-3):1<<(WR_CAM_ADDR_BITS-2)]};
                    bins        watermark_4    =   {{(WR_CAM_ADDR_BITS-1){1'b1}}-1, {(RD_CAM_ADDR_BITS-1){1'b1}}     };
                    bins        watermark_5    =   {{(WR_CAM_ADDR_BITS-1){1'b1}}-1, {(RD_CAM_ADDR_BITS-1){1'b1}}-1   };
                    bins        watermark_6    =   {{(WR_CAM_ADDR_BITS-1){1'b1}},   {(RD_CAM_ADDR_BITS-1){1'b1}}     };
    }

endgroup: cg_wrcam_thresh

covergroup cg_wrcam_thresh_enh @(posedge co_yy_clk);
option.comment = "Coverage group for wr cam thresh enhance";
    cp_reg_w_max_starve: coverpoint ({dh_gs_w_max_starve}) iff(core_ddrc_rstn && rdwr_pol_sel && reg_ddrc_opt_wrcam_fill_level) {
                   bins         value_mark_0 =  {0};
                   bins         value_mark_1 =  {1};
                   bins         value_mark_2 =  {[2:65533]};
                   bins         value_mark_3 =  {65534};
                   bins         value_mark_4 =  {65535};
    }

    cp_reg_w_run_length: coverpoint ({dh_gs_w_xact_run_length}) iff(core_ddrc_rstn && rdwr_pol_sel && reg_ddrc_opt_wrcam_fill_level) {
                   bins         value_mark_0 =  {0};
                   bins         value_mark_1 =  {1};
                   bins         value_mark_2 =  {[2:254]};
                   bins         value_mark_3 =  {255};
    }

endgroup: cg_wrcam_thresh_enh

cg_wrcam_thresh cg_wrcam_thresh_inst = new;

property p_wr_pghit_up_thresh;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        |reg_ddrc_wr_pghit_num_thresh && ($countones(te_ts_wr_entry_valid[WR_CAM_ENTRIES-1:0] & te_ts_wr_page_hit_entries[WR_CAM_ENTRIES-1:0])>reg_ddrc_wr_pghit_num_thresh) |-> ##2 wr_pghit_up_thresh;
endproperty

a_wr_pghit_up_thresh: assert property (p_wr_pghit_up_thresh)
    else $error("Inline SVA [%t][%m] FAILED", $time);

property p_rd_pghit_up_thresh;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~rdwr_pol_sel)
        |reg_ddrc_rd_pghit_num_thresh && ($countones(te_ts_rd_entry_valid[WR_CAM_ENTRIES-1:0] & te_ts_rd_page_hit_entries[WR_CAM_ENTRIES-1:0])>reg_ddrc_rd_pghit_num_thresh) |-> ##2 rd_pghit_up_thresh;
endproperty

a_rd_pghit_up_thresh: assert property (p_rd_pghit_up_thresh)
    else $error("Inline SVA [%t][%m] FAILED", $time);

covergroup cg_pghit_num_thresh @(posedge co_yy_clk);

    cp_wr_page_hit_entries: coverpoint ({|reg_ddrc_wr_pghit_num_thresh, te_num_wr_pghit_entries - reg_ddrc_wr_pghit_num_thresh}) iff(core_ddrc_rstn && rdwr_pol_sel) {
                    bins        satisfied_0 =   {1'b1, {(WR_CAM_ADDR_BITS_IE){1'b0}}};
                    bins        satisfied_1 =   {1'b1, 1                            };
                    // bins        satisfied_2 =   {1'b1, -1                           };
        // wildcard    ignore_bins unsatisfied =   {1'b0, {(WR_CAM_ADDR_BITS_IE){1'b?}}};
    }

    cp_reg_ddrc_wr_pghit_num_thresh: coverpoint ({reg_ddrc_wr_pghit_num_thresh}) iff(core_ddrc_rstn && rdwr_pol_sel) {
                    bins        watermark_0 =   {{WR_CAM_ADDR_BITS{1'b1}}       };
                    // bins        watermark_1 =   {{WR_CAM_ADDR_BITS{1'b1}}-1     };
                    bins        watermark_2 =   {0                              };
                    // bins        watermark_3 =   {1                              };
                    bins        watermark_4 =   {[1:{WR_CAM_ADDR_BITS{1'b1}}-1] };
    }

    cp_rd_page_hit_entries: coverpoint ({|reg_ddrc_rd_pghit_num_thresh, te_num_rd_pghit_entries - reg_ddrc_rd_pghit_num_thresh}) iff(core_ddrc_rstn && rdwr_pol_sel) {
                    bins        satisfied_0 =   {1'b1, {RD_CAM_ADDR_BITS{1'b0}}  };
                    bins        satisfied_1 =   {1'b1, 1                            };
                    // bins        satisfied_2 =   {1'b1, -1                           };
        // wildcard    ignore_bins unsatisfied =   {1'b0, {RD_CAM_ADDR_BITS{1'b?}}  };
    }

    cp_reg_ddrc_rd_pghit_num_thresh: coverpoint ({reg_ddrc_rd_pghit_num_thresh}) iff(core_ddrc_rstn && rdwr_pol_sel) {
                    bins        watermark_0 =   {{RD_CAM_ADDR_BITS{1'b1}}       };
                    // bins        watermark_1 =   {{RD_CAM_ADDR_BITS{1'b1}}-1     };
                    bins        watermark_2 =   {0                              };
                    // bins        watermark_3 =   {1                              };
                    bins        watermark_4 =   {[1:{RD_CAM_ADDR_BITS{1'b1}}-1] };
    }

endgroup: cg_pghit_num_thresh

cg_pghit_num_thresh cg_pghit_num_thresh_inst = new;



property p_wr_mode_no_rd_chk;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn)
        gs_wr_mode |-> ~gs_op_is_rd;
endproperty

a_wr_mode_no_rd_chk: assert property (p_wr_mode_no_rd_chk)
    else $error("Inline SVA [%t][%m] FAILED", $time);

property p_rd_mode_no_wr_chk;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn)
        ~gs_wr_mode |-> ~gs_op_is_wr;
endproperty

a_rd_mode_no_wr_chk: assert property (p_rd_mode_no_wr_chk)
    else $error("Inline SVA [%t][%m] FAILED", $time);

// sva and cp for opt_vprw_sch cross bank cases

wire [NUM_TOTAL_BSMS-1:0] te_bs_vpw_hit1_valid_w;
wire [NUM_TOTAL_BSMS-1:0] te_bs_vpw_hit0_valid_w;
wire [NUM_TOTAL_BSMS-1:0] te_bs_vpw_miss_valid_w;
assign te_bs_vpw_hit1_valid_w = (te_bs_wr_valid & te_bs_wr_page_hit & te_ts_vpw_valid & bank_wr_activated_early);
assign te_bs_vpw_hit0_valid_w = (te_bs_wr_valid & te_bs_wr_page_hit & te_ts_vpw_valid & ~bank_wr_activated_early);
assign te_bs_vpw_miss_valid_w = (te_bs_wr_valid & ~te_bs_wr_page_hit & te_ts_vpw_valid);

// at the time when a NPW is scheduled out, there should be no page-hit(with tRCD) exVPW in other NTTs' output
property p_op_is_wr_no_exvpw_pghit1;
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_wr && ~te_ts_vpw_valid[gs_rdwr_bsm_num] && ~te_bs_wrecc_btt[gs_rdwr_bsm_num] |->
                                                           /* --------------------------------1------------------------------ */
      ~($past(te_gs_any_vpw_timed_out_w,1) && |($past(te_bs_vpw_hit1_valid_w, 1) & ($past(gs_op_is_wr,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} )));
      /* ------------------------------2------------------------------------ */   /* -----------------------------3----------------------------- */
      /* 1. wrecc_btt goes to bs_os_high selnet. Pick out from NPW's scheduling.
         2. te_gs_any_vpw_timed_out_r is the FF output of te_gs_any_vpw_timed_out_w && te_bs_vpw_hit1_valid_w for timing.
            So the consequent should be for the last cycle rather than current cycle.
         3. If there is back-to-back wr, i.e. op_is_wr, blank, op_is_wr,
            the page-hit/vpw/valid info at NTTs' output will be de-asserted at the next cycle of op_is_wr, i.e. at blank.
            In this case, the te_gs_any_vpw_timed_out_r is vacuous if there is another exvpw-miss, blocking one cycle more. */
endproperty

a_op_is_wr_no_exvpw_pghit1: assert property (p_op_is_wr_no_exvpw_pghit1)
  else $error("Inline SVA [%t][%m] FAILED, when a NPW is scheduled out, there are pending exVPW with page-hit with tRCD in other NTTs", $time);

// at the time when a NPW is scheduled out, cover the case that there are page-hit(without tRCD) exVPW in other NTTs' output
cp_op_is_wr_exvpw_pghit0: cover property (
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_wr && ~te_ts_vpw_valid[gs_rdwr_bsm_num] && ~te_bs_wrecc_btt[gs_rdwr_bsm_num] |->
      ($past(te_gs_any_vpw_timed_out_w,1) && |($past(te_bs_vpw_hit0_valid_w, 1) & ($past(gs_op_is_wr,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} ) )));

// at the time when a NPW is scheduled out, cover the case that there are page-miss exVPW in other NTTs' output
cp_op_is_wr_exvpw_pgmiss: cover property (
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_wr && ~te_ts_vpw_valid[gs_rdwr_bsm_num] && ~te_bs_wrecc_btt[gs_rdwr_bsm_num] |->
      ($past(te_gs_any_vpw_timed_out_w,1) && |($past(te_bs_vpw_miss_valid_w, 1) & ($past(gs_op_is_wr,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} ) )));

// at the time when op_is_wr asserted and there are pending te_bs_vpw_hit1_valid_w, the sheduled out bank must be exvpw.
property p_op_is_wr_pending_exvpw_pghit1;
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_wr && $past(te_gs_any_vpw_timed_out_w,1) && |($past(te_bs_vpw_hit1_valid_w, 1) & ($past(gs_op_is_wr,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} )) && ~te_bs_wrecc_btt[gs_rdwr_bsm_num]
      |-> te_ts_vpw_valid[gs_rdwr_bsm_num];
endproperty

a_op_is_wr_pending_exvpw_pghit1: assert property (p_op_is_wr_pending_exvpw_pghit1)
  else $error("Inline SVA [%t][%m] FAILED, when there are pending pghit1-exvpw in BSMs output, the scheduled out bank muast be exvpw.", $time);

// Since the vpw can be expired during any time, so commented below sva now.
// property p_no_exvpw_pghit1_pending_op_is_npw;
//   @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
//     ~|te_bs_vpw_hit1_valid_w ##1 gs_op_is_wr |-> ~te_ts_vpw_valid[gs_rdwr_bsm_num];
// endproperty
//
// a_no_exvpw_pghit1_pending_op_is_npw: assert property (p_no_exvpw_pghit1_pending_op_is_npw)
//   else $error("Inline SVA [%t][%m] FAILED, when there is no exvpw pghit1 pending and there is op_is_wr in the next cycle, the scheduled out cmd must no be exvpw.", $time);

wire [NUM_TOTAL_BSMS-1:0] te_bs_vpr_hit1_valid_w;
wire [NUM_TOTAL_BSMS-1:0] te_bs_vpr_hit0_valid_w;
wire [NUM_TOTAL_BSMS-1:0] te_bs_vpr_miss_valid_w;
assign te_bs_vpr_hit1_valid_w = (te_bs_rd_valid & te_bs_rd_page_hit & te_ts_vpr_valid & bank_activated_early);
assign te_bs_vpr_hit0_valid_w = (te_bs_rd_valid & te_bs_rd_page_hit & te_ts_vpr_valid & ~bank_activated_early);
assign te_bs_vpr_miss_valid_w = (te_bs_rd_valid & ~te_bs_rd_page_hit & te_ts_vpr_valid);

// at the time when a LPR/HPR is scheduled out, there should be no page-hit(with tRCD) exVPR in other NTTs' output
property p_op_is_rd_no_exvpr_pghit1;
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_rd && ~te_ts_vpr_valid[gs_rdwr_bsm_num] |->
      ~($past(te_gs_any_vpr_timed_out_w,1) && |($past(te_bs_vpr_hit1_valid_w, 1) & ($past(gs_op_is_rd,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} )));
endproperty

a_op_is_rd_no_exvpr_pghit1: assert property (p_op_is_rd_no_exvpr_pghit1)
  else $error("Inline SVA [%t][%m] FAILED, when a LPR/HPR is scheduled out, there are pending exVPR with page-hit with tRCD in other NTTs", $time);

// at the time when a LPR/HPR is scheduled out, cover the case that there are page-hit(without tRCD) exVPR in other NTTs' output
cp_op_is_rd_exvpr_pghit0: cover property (
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_rd && ~te_ts_vpr_valid[gs_rdwr_bsm_num] |->
      ~($past(te_gs_any_vpr_timed_out_w,1) && |($past(te_bs_vpr_hit0_valid_w, 1) & ($past(gs_op_is_rd,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} ))));

// at the time when a LPR/HPR is scheduled out, cover the case that there are page-miss exVPR in other NTTs' output
cp_op_is_rd_exvpr_pgmiss: cover property (
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_rd && ~te_ts_vpr_valid[gs_rdwr_bsm_num] |->
      ~($past(te_gs_any_vpr_timed_out_w,1) && |($past(te_bs_vpr_miss_valid_w, 1) & ($past(gs_op_is_rd,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} ))));

// at the time when op_is_rd asserted and there are pending te_bs_vpr_hit1_valid_w, the sheduled out bank must be exvpr.
property p_op_is_rd_pending_exvpr_pghit1;
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
    gs_op_is_rd && $past(te_gs_any_vpr_timed_out_w,1) && |($past(te_bs_vpr_hit1_valid_w, 1) & ($past(gs_op_is_rd,2) ? {{(NUM_TOTAL_BSMS-1){1'b1}}, 1'b0}<<$past(gs_rdwr_bsm_num,2) : {NUM_TOTAL_BSMS{1'b1}} ))
      |-> te_ts_vpr_valid[gs_rdwr_bsm_num];
endproperty

a_op_is_rd_pending_exvpr_pghit1: assert property (p_op_is_rd_pending_exvpr_pghit1)
  else $error("Inline SVA [%t][%m] FAILED, when there are pending pghit1-exvpr in BSMs output, the scheduled out bank muast be exvpr.", $time);

// property p_no_exvpr_pghit1_pending_op_is_rd;
//   @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_vprw_sch)
//     ~|te_bs_vpr_hit1_valid_w ##1 gs_op_is_rd |-> ~te_ts_vpr_valid[gs_rdwr_bsm_num];
// endproperty
//
// a_no_exvpr_pghit1_pending_op_is_rd: assert property (p_no_exvpr_pghit1_pending_op_is_rd)
//   else $error("Inline SVA [%t][%m] FAILED, when there is no exvpr pghit1 pending and there is op_is_rd in the next cycle, the scheduled out cmd must no be exvpr.", $time);


property p_write_starvation_free_running_mode;
  @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || ~reg_ddrc_opt_wrcam_fill_level || ~|dh_gs_w_max_starve)
     $past(gs_op_is_wr,2) && (wr_cam_thresh_starve_cnt == dh_gs_w_max_starve) && reg_ddrc_w_starve_free_running && $past(wr_cam_thresh_run_length_satisfied,1) && !($past(wr_cam_thresh_starve_cnt,1) > dh_gs_w_max_starve) |-> ~|$past(wr_cam_thresh_starve_cnt,1);
endproperty // p_write_starvation_free_running_mode

a_write_starvation_free_running_mode: assert property (p_write_starvation_free_running_mode)
  else $error("Inline SVA [%t][%m] FAILED, starvation timer for enhanced WR CAM fill level is not expcted to be reset by WR command when the timer is not expired while free running mode.", $time);

`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS

endmodule  // TS (Transaction Scheduler)
