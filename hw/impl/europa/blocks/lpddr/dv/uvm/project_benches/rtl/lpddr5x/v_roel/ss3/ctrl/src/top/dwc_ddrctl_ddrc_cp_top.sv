//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cp_top.sv#14 $
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

// ----------------------------------------------------------------------------
//                              DDR Controller
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------

// ----------------------------------------------------------------------------
//                              Description
//
// This is the wrapper for ddrc_ctrl and occap_cmp modules.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "dfi/DWC_ddrctl_dfi_pkg.svh"
`include "top/dwc_ddrctl_ddrc_cpfdp_if.svh"
`include "top/dwc_ddrctl_ddrc_cpedp_if.svh"
`include "ts/DWC_ddrctl_ts_if.svh"

module dwc_ddrctl_ddrc_cp_top
import DWC_ddrctl_reg_pkg::*;
import DWC_ddrctl_dfi_pkg::*;
  #(
//------------------------------------------------------------------------------
// Parameters
//------------------------------------------------------------------------------
parameter       CHANNEL_NUM = 0,
parameter       SHARED_AC = 0,
parameter       SHARED_AC_INTERLEAVE = 0,
parameter       BCM_VERIF_EN = 1,
parameter       BCM_DDRC_N_SYNC = 2,
parameter       BCM_F_SYNC_TYPE_P2C = 2,
parameter       MEMC_ECC_SUPPORT = 0,
parameter       UMCTL2_SEQ_BURST_MODE = 0,                       // Applies MDDR/LPDDR2 like squential burst mode only
parameter       UMCTL2_PHY_SPECIAL_IDLE = 0,                     // A specially encoded "IDLE" command over the DFI bus: {ACT_n,RAS_n,CAS_n,WE_n,BA0}
parameter       OCPAR_EN = 0,                                    // enables on-chip parity
parameter       OCCAP_EN = 0,                                    // enables on-chip command/address path protection
parameter       CP_ASYNC = 0,
parameter       CMP_REG = 0,                                     // enables occap_cmp input registers
parameter       NPORTS = 1,                                      // no. of ports (for cactive_in_ddrc width) gets overwritten by toplevel
parameter       NPORTS_LG2 = 1,                                      // log2 of no. of ports (for ih_dual) gets overwritten by toplevel
parameter       A_SYNC_TABLE = 16'hffff, // AXI sync table
parameter       RD_CAM_ADDR_WIDTH  = `MEMC_RDCMD_ENTRY_BITS,   // bits to address into read CAM
parameter       WR_CAM_ADDR_WIDTH  = `MEMC_WRCMD_ENTRY_BITS,   // bits to address into write CAM
parameter       WR_ECC_CAM_ADDR_WIDTH = 0,
parameter       WR_CAM_ADDR_WIDTH_IE = 0,
parameter       MAX_CAM_ADDR_WIDTH = 0,
parameter       RD_CAM_ENTRIES = 0,
parameter       WR_CAM_ENTRIES = 0,
parameter       WR_ECC_CAM_ENTRIES = 0,
parameter       WR_CAM_ENTRIES_IE =0,
parameter       CORE_DATA_WIDTH = `MEMC_DFI_DATA_WIDTH,        // internal data width
parameter       CORE_ADDR_WIDTH = `MEMC_HIF_ADDR_WIDTH_MAX,
// This is the actual width of the address bus used inside DDRC
parameter       CORE_ADDR_INT_WIDTH = (`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS),
parameter       HIF_ADDR_WIDTH  = `MEMC_HIF_ADDR_WIDTH,
parameter       CORE_TAG_WIDTH  = `MEMC_TAGBITS,                // width of tag

// widths used for some outputs of ddrc_ctrl that would be
// [X-1:0]=>[-1:0]
// wide otherwise as X=0
parameter       RANK_BITS_DUP   = `MEMC_RANK_BITS,
parameter       BG_BITS_DUP     = `MEMC_BG_BITS,
parameter       LRANK_BITS_DUP  = `UMCTL2_LRANK_BITS,
parameter       CID_WIDTH_DUP   = `UMCTL2_CID_WIDTH,
parameter       CORE_ECC_WIDTH_DUP          = (`MEMC_DFI_ECC_WIDTH==0)  ? 1 : `MEMC_DFI_ECC_WIDTH,
parameter       CORE_ECC_MASK_WIDTH_DUP     = (`MEMC_DFI_ECC_WIDTH==0)  ? 1 : `MEMC_DFI_ECC_WIDTH/8,

parameter       RANK_BITS       = `MEMC_RANK_BITS,
parameter       LRANK_BITS      = `UMCTL2_LRANK_BITS,
parameter       CID_WIDTH       = `UMCTL2_CID_WIDTH,
parameter       BG_BITS         = `MEMC_BG_BITS,
parameter       BG_BANK_BITS    = `MEMC_BG_BANK_BITS,
parameter       BANK_BITS       = `MEMC_BANK_BITS,
parameter       PAGE_BITS       = `MEMC_PAGE_BITS,
parameter       WORD_BITS       = `MEMC_WORD_BITS,              // address a word within a burst
parameter       BLK_BITS        = `MEMC_BLK_BITS,               // 2 column bits are critical word
parameter       BSM_BITS        = `UMCTL2_BSM_BITS,

parameter       MRS_A_BITS      = `MEMC_PAGE_BITS,
parameter       MRS_BA_BITS     = `MEMC_BG_BANK_BITS,

parameter       PHY_ADDR_BITS   = `MEMC_DFI_ADDR_WIDTH,

parameter       NUM_TOTAL_BANKS = `MEMC_NUM_TOTAL_BANKS,        // max supported banks
parameter       NUM_RANKS       = `MEMC_NUM_RANKS,              // max supported ranks (chip selects)
parameter       NUM_LRANKS      = `UMCTL2_NUM_LRANKS_TOTAL,     // max supported logical ranks (chip selects * chip ID(for DDR4 3DS))
parameter       NUM_TOTAL_BSMS  = `UMCTL2_NUM_BSM,              // max supported BSMs

parameter       NUM_PHY_DRAM_CLKS = `MEMC_NUM_CLKS,

parameter       PHY_DATA_WIDTH  = `MEMC_DFI_TOTAL_DATA_WIDTH,       // data width to PHY
parameter       PHY_MASK_WIDTH  = `MEMC_DFI_TOTAL_DATA_WIDTH/8,     // data mask width (internal to uMCTL2)


parameter MWR_BITS = `DDRCTL_MWR_BITS,
parameter PARTIAL_WR_BITS = `UMCTL2_PARTIAL_WR_BITS,

parameter       NUM_LANES  = 4, //Number of lanes in PHY - default is 4
parameter       PARITY_IN_WIDTH  = 2,

parameter       RETRY_MAX_ADD_RD_LAT_LG2 = 1,
parameter       CMD_LEN_BITS     = 1,                            // command length bit width
parameter       FATL_CODE_BITS   = 3,

parameter       WRDATA_CYCLES    = 2,

// were localparams but need to parameters as signal widths depend on them
parameter      CMD_TYPE_BITS   = 2,                           // command type bit width
parameter      WDATA_PTR_BITS  = `MEMC_WDATA_PTR_BITS,
parameter      CMD_RMW_BITS    = 1,                            // unused, but '0' breaks things still...
parameter      RMW_TYPE_BITS   = 2,                            // 2-bit RMW type
                                                                //  (partial
                                                                //  write,
                                                                //  scrub,
                                                                //  atomic
                                                                //  RMW, none)


parameter PARTIAL_WR_BITS_LOG2 = `log2(PARTIAL_WR_BITS),
parameter PW_NUM_DB = PARTIAL_WR_BITS,

parameter PW_FACTOR_HBW = 2*`MEMC_FREQ_RATIO,
parameter PW_FACTOR_FBW = 1*`MEMC_FREQ_RATIO,

parameter PW_WORD_VALID_WD_HBW = PW_NUM_DB*PW_FACTOR_HBW,
parameter PW_WORD_VALID_WD_FBW = PW_NUM_DB*PW_FACTOR_FBW,

parameter PW_WORD_VALID_WD_MAX = PW_WORD_VALID_WD_HBW,

parameter PW_WORD_CNT_WD_MAX = `log2(PW_WORD_VALID_WD_MAX),

parameter RANKBANK_BITS_FULL = LRANK_BITS + BG_BITS + BANK_BITS,

parameter RD_LATENCY_BITS   = `UMCTL2_XPI_RQOS_TW,

parameter NO_OF_BT          = `MEMC_NO_OF_BLK_TOKEN,
parameter NO_OF_BWT         = `MEMC_NO_OF_BWT,
parameter NO_OF_BRT         = `MEMC_NO_OF_BRT,
parameter BT_BITS           = `log2(NO_OF_BT),
parameter BWT_BITS          = `log2(NO_OF_BWT),
parameter BRT_BITS          = `log2(NO_OF_BRT),
parameter NO_OF_BLK_CHN     = `MEMC_NO_OF_BLK_CHANNEL,
parameter BLK_CHN_BITS      = `log2(NO_OF_BLK_CHN),
parameter IE_RD_TYPE_BITS   = `IE_RD_TYPE_BITS,
parameter IE_WR_TYPE_BITS   = `IE_WR_TYPE_BITS,
parameter IE_BURST_NUM_BITS = 5,
parameter IE_PW_BITS        = `MEMC_BURST_LENGTH==16 ? 4 : 2

,parameter MAX_CMD_DELAY    = `UMCTL2_MAX_CMD_DELAY
,parameter CMD_DELAY_BITS   = `UMCTL2_CMD_DELAY_BITS
,parameter AM_DCH_WIDTH     = 6
,parameter AM_CS_WIDTH      = 6
,parameter AM_CID_WIDTH     = 6
,parameter AM_BANK_WIDTH    = 6
,parameter AM_BG_WIDTH      = 6
,parameter AM_ROW_WIDTH     = 5
,parameter AM_COL_WIDTH_H   = 5
,parameter AM_COL_WIDTH_L   = 4
,parameter MAX_CMD_NUM      = 2
,parameter DFI_T_CTRLMSG_RESP_WIDTH = 8
,parameter DFI_CTRLMSG_DATA_WIDTH   = 16
,parameter DFI_CTRLMSG_CMD_WIDTH    = 8
,parameter HIF_KEYID_WIDTH  = `DDRCTL_HIF_KEYID_WIDTH
  )
  (
//------------------------------------------------------------------------------
// Input and Output Declarations
//------------------------------------------------------------------------------

input                           core_ddrc_core_clk,
input                           core_ddrc_rstn,




input                           core_ddrc_core_clk_te,
output                          clk_te_en,


input   [NUM_RANKS-1:0]         bsm_clk,
output  [NUM_RANKS-1:0]         bsm_clk_en,
input   [BSM_CLK_ON_WIDTH-1:0]  bsm_clk_on,             // 0: bsm_clk can be removed. 1: bsm_clk is not removed.


//SV interface
//cpfdpif
dwc_ddrctl_ddrc_cpfdp_if.i_rd_ih_mp          i_rd_ih_cpfdpif,
dwc_ddrctl_ddrc_cpfdp_if.i_wu_ih_mp          i_wu_ih_cpfdpif,
dwc_ddrctl_ddrc_cpfdp_if.i_wu_te_mp          i_wu_te_cpfdpif,
dwc_ddrctl_ddrc_cpfdp_if.i_mr_ih_mp          i_mr_ih_cpfdpif,
dwc_ddrctl_ddrc_cpfdp_if.o_ih_mp             o_ih_cpfdpif,
dwc_ddrctl_ddrc_cpfdp_if.o_te_mp             o_te_cpfdpif,

//cpedpif
dwc_ddrctl_ddrc_cpedp_if.i_wu_gs_mp          i_wu_gs_ddrc_cpedpif,
dwc_ddrctl_ddrc_cpedp_if.i_mr_gs_mp          i_mr_gs_ddrc_cpedpif,
dwc_ddrctl_ddrc_cpedp_if.o_gs_mp             o_gs_ddrc_cpedpif,
dwc_ddrctl_ddrc_cpedp_if.o_pi_mp             o_pi_ddrc_cpedpif,

input                           hif_cmd_valid,          // valid command
input   [CMD_TYPE_BITS-1:0]     hif_cmd_type,           // command type:
                                                        //  00 - block write
                                                        //  01 - read
                                                        //  10 - partial write
                                                        //  01 - read-mod-write
input   [1:0]                   hif_cmd_pri,            // priority: // TEMP ONLY - make it 2-bits when ARB is connected
                                                        //  HIF config: 0 - LPR, 1 - HPR
                                                        //  Arbiter config: 00 - LPR, 01 - VPR, 10 - HPR, 11 - Unused
input   [CORE_ADDR_WIDTH-1:0]   hif_cmd_addr,           // address
input   [CMD_LEN_BITS-1:0]      hif_cmd_length,         // length (1 word or 2)
                                                        //  1 - 1 word length
                                                        //  2 - 2 word lengths
                                                        // (where 1 word equals the size of the data transfer
                                                        //  between the core and the controller)
input   [CORE_TAG_WIDTH-1:0]    hif_cmd_token,          // read token,
                                                        //  returned w/ read data
input   [WDATA_PTR_BITS-1:0]    hif_cmd_wdata_ptr,      // incoming wdata ptr


input   [RD_LATENCY_BITS-1:0]   hif_cmd_latency,


input                           hif_cmd_autopre,        // auto precharge enable

input                           hif_cmd_ecc_region,
input  [WRDATA_CYCLES-1:0]      hif_cmd_wdata_mask_full_ie,

input                           hif_go2critical_lpr,
input                           hif_go2critical_hpr,
input                           hif_go2critical_wr,
input                           hif_go2critical_l1_wr,
input                           hif_go2critical_l2_wr,
input                           hif_go2critical_l1_lpr,
input                           hif_go2critical_l2_lpr,
input                           hif_go2critical_l1_hpr,
input                           hif_go2critical_l2_hpr,
input                           reg_ddrc_autopre_rmw,


output                          hif_cmd_stall,            // request stall
output                          hif_rcmd_stall,           // cmd stall
output                          hif_wcmd_stall,           // cmd stall

output                          hif_wdata_ptr_valid,
output  [WDATA_PTR_BITS-1:0]    hif_wdata_ptr,
output                          hif_wdata_ptr_addr_err,   // Indicates that the write was associated with an invalid address
output [`MEMC_HIF_CREDIT_BITS-1:0]  hif_lpr_credit,
output                              hif_wr_credit,
output [`MEMC_HIF_CREDIT_BITS-1:0]  hif_hpr_credit,
output [1:0]                        hif_wrecc_credit,
output [WR_CAM_ADDR_WIDTH:0]    ddrc_reg_dbg_wrecc_q_depth,
output [WR_CAM_ADDR_WIDTH:0]    ddrc_core_reg_dbg_wrecc_q_depth,
output                          perf_ie_blk_hazard,
input                           reg_ddrc_sw_init_int,      // SW intervention in auto SDRAM initialization
input                           reg_ddrc_mr_wr,            // input from core to write mode register
input                           reg_ddrc_mr_type,          // MR Type R/W.
                                                           // 0000: MR0, 0001: MR1, 0010: MR2, 0011: MR3, 0100: MR4, 0101: MR5, 0110: MR6
input   [PAGE_BITS-1:0]         reg_ddrc_mr_data,          // mode register data to be written
input   [3:0]                   reg_ddrc_mr_addr,          // input from core: mode register address
output                          ddrc_reg_mr_wr_busy,       // indicates that mode register write operation is in progress

input                           reg_ddrc_derate_mr4_tuf_dis,
output                          core_derate_temp_limit_intr,
input                           reg_ddrc_derate_temp_limit_intr_clr,
input   [ACTIVE_DERATE_BYTE_RANK_WIDTH-1:0] reg_ddrc_active_derate_byte_rank0,
input   [ACTIVE_DERATE_BYTE_RANK_WIDTH-1:0] reg_ddrc_active_derate_byte_rank1,
input   [DBG_MR4_RANK_SEL_WIDTH-1:0]        reg_ddrc_dbg_mr4_rank_sel,
output  [DBG_MR4_BYTE_WIDTH-1:0]            ddrc_reg_dbg_mr4_byte0,
output  [DBG_MR4_BYTE_WIDTH-1:0]            ddrc_reg_dbg_mr4_byte1,
output  [DBG_MR4_BYTE_WIDTH-1:0]            ddrc_reg_dbg_mr4_byte2,
output  [DBG_MR4_BYTE_WIDTH-1:0]            ddrc_reg_dbg_mr4_byte3,
input                           reg_ddrc_lpddr4_refresh_mode,
input                           reg_ddrc_zq_reset,
input   [T_ZQ_RESET_NOP_WIDTH-1:0]  reg_ddrc_t_zq_reset_nop,
input   [DERATE_ENABLE_WIDTH-1:0]   reg_ddrc_derate_enable,
input   [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd,
input   [DERATED_T_RAS_MIN_WIDTH-1:0] reg_ddrc_derated_t_ras_min,
input   [DERATED_T_RP_WIDTH-1:0]      reg_ddrc_derated_t_rp,
input   [DERATED_T_RRD_WIDTH-1:0]     reg_ddrc_derated_t_rrd,
input   [DERATED_T_RC_WIDTH-1:0]      reg_ddrc_derated_t_rc,
input                               reg_ddrc_derate_mr4_pause_fc,
input   [MR4_READ_INTERVAL_WIDTH-1:0]                 reg_ddrc_mr4_read_interval,
input   [DERATED_T_RCD_WIDTH-1:0]     reg_ddrc_derated_t_rcd_write,
output  [REFRESH_RATE_RANK_WIDTH-1:0]                 ddrc_reg_refresh_rate_rank0,
output  [REFRESH_RATE_RANK_WIDTH-1:0]                 ddrc_reg_refresh_rate_rank1,
output  [REFRESH_RATE_RANK_WIDTH-1:0]                 ddrc_reg_refresh_rate_rank2,
output  [REFRESH_RATE_RANK_WIDTH-1:0]                 ddrc_reg_refresh_rate_rank3,
output  [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank0,
output  [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank1,
output  [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank2,
output  [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank3,
output                                                ddrc_reg_zq_reset_busy,


output                                               hif_cmd_q_not_empty,    // indicates that there are commands pending in the cams

input        [NPORTS-1:0]                            cactive_in_ddrc,
input        [NPORTS-1:0]                            cactive_in_ddrc_async,
input                                                csysreq_ddrc,
input                                                csysmode_ddrc,
input   [4:0]                                        csysfrequency_ddrc,
input                                                csysdiscamdrain_ddrc,
input                                                csysfsp_ddrc,

output                                               csysack_ddrc,
output                                               cactive_ddrc,

output [SELFREF_TYPE_WIDTH-1:0]                      stat_ddrc_reg_selfref_type,
output [3:0]                                         stat_ddrc_reg_retry_current_state,

output                                               dbg_dfi_in_retry,

output [2:0]                                         dbg_dfi_ie_cmd_type,
output    [BSM_BITS:0]                               ddrc_reg_num_alloc_bsm,

output [BSM_BITS:0]                                  ddrc_reg_max_num_alloc_bsm,
output [RD_CAM_ADDR_WIDTH+1:0]                       ddrc_reg_max_num_unalloc_entries,

output    perf_hif_rd_or_wr,
output    perf_hif_wr,
output    perf_hif_rd,
output    perf_hif_rmw,
output    perf_hif_hi_pri_rd,

output    perf_read_bypass,
output    perf_act_bypass,

output    perf_hpr_xact_when_critical, // hpr transaction when hpr q is critical
output    perf_lpr_xact_when_critical, // lpr transaction when lpr q is critical
output    perf_wr_xact_when_critical,  // wr transaction when wr q is critical

output    perf_op_is_activate,
output    perf_op_is_rd_or_wr,
output    perf_op_is_rd_activate,
output    perf_op_is_rd,
output    perf_op_is_wr,
output    perf_op_is_mwr,
output    perf_op_is_wr16,
output    perf_op_is_wr32,
output    perf_op_is_rd16,
output    perf_op_is_rd32,
output    perf_op_is_cas,
output    perf_op_is_cas_ws,
output    perf_op_is_cas_ws_off,
output    perf_op_is_cas_wck_sus,
output    perf_op_is_enter_dsm,
output    perf_op_is_rfm,
output    perf_op_is_precharge,
output    perf_precharge_for_rdwr,
output    perf_precharge_for_other,

output    perf_rdwr_transitions,

output    perf_write_combine,
output    perf_write_combine_noecc,
output    perf_write_combine_wrecc,
output    perf_war_hazard,
output    perf_raw_hazard,
output    perf_waw_hazard,

output    [NUM_RANKS-1:0] perf_op_is_enter_selfref,
output    [NUM_RANKS-1:0] perf_op_is_enter_powerdown,
output    [NUM_RANKS-1:0] perf_op_is_enter_mpsm,
output    [NUM_RANKS-1:0] perf_selfref_mode,

output    perf_op_is_refresh,
output    perf_op_is_load_mode,
output    perf_op_is_zqcl,
output    perf_op_is_zqcs,

output    [RANK_BITS_DUP-1:0]   perf_rank,
output    [`MEMC_BANK_BITS-1:0] perf_bank,
output    [BG_BITS_DUP-1:0]     perf_bg,
output    [CID_WIDTH_DUP-1:0]   perf_cid,
output    [RANK_BITS_DUP-1:0]   perf_bypass_rank,
output    [`MEMC_BANK_BITS-1:0] perf_bypass_bank,
output    [BG_BITS_DUP-1:0]     perf_bypass_bg,
output    [CID_WIDTH_DUP-1:0]   perf_bypass_cid,
output                          perf_bsm_alloc,
output                          perf_bsm_starvation,
output    [BSM_BITS:0]          perf_num_alloc_bsm,
output                          perf_visible_window_limit_reached_rd,
output                          perf_visible_window_limit_reached_wr,
output                          perf_op_is_dqsosc_mpc,
output                          perf_op_is_dqsosc_mrr,
output                          perf_op_is_tcr_mrr,
output                          perf_op_is_zqstart,
output                          perf_op_is_zqlatch,

output  [2:0]   ddrc_core_reg_dbg_operating_mode,
output  [4:0]   ddrc_core_reg_dbg_global_fsm_state,

output  [4:0]   ddrc_core_reg_dbg_init_curr_state,
output  [4:0]   ddrc_core_reg_dbg_init_next_state,

output  [1:0]   ddrc_core_reg_dbg_ctrlupd_state,

output  [1:0]  ddrc_core_reg_dbg_lpr_q_state,
output  [1:0]  ddrc_core_reg_dbg_hpr_q_state,
output  [1:0]  ddrc_core_reg_dbg_wr_q_state,


output  [RD_CAM_ADDR_WIDTH:0]  ddrc_core_reg_dbg_lpr_q_depth,
output  [RD_CAM_ADDR_WIDTH:0]  ddrc_core_reg_dbg_hpr_q_depth,
output  [WR_CAM_ADDR_WIDTH:0]  ddrc_core_reg_dbg_wr_q_depth,

output         ddrc_core_reg_dbg_hif_cmd_stall,

output         ddrc_core_reg_dbg_hif_rcmd_stall,
output         ddrc_core_reg_dbg_hif_wcmd_stall,



output  [NUM_TOTAL_BANKS-1:0]  ddrc_core_reg_dbg_rd_valid_rank,     // each bit indicates a bank
output  [NUM_TOTAL_BANKS-1:0]  ddrc_core_reg_dbg_rd_page_hit_rank,  // each bit indicates a bank
output  [NUM_TOTAL_BANKS-1:0]  ddrc_core_reg_dbg_rd_pri_rank,       // each bit indicates a bank
output  [NUM_TOTAL_BANKS-1:0]  ddrc_core_reg_dbg_wr_valid_rank,     // each bit indicates a bank
output  [NUM_TOTAL_BANKS-1:0]  ddrc_core_reg_dbg_wr_page_hit_rank,  // each bit indicates a bank

output      [7:0]                           ddrc_core_reg_dbg_wr_cam_7_0_valid, // 1-bit per cam location
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_7_0_valid, // 1-bit per cam location
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_15_8_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_15_8_valid,
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_23_16_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_23_16_valid,
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_31_24_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_31_24_valid,
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_39_32_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_39_32_valid,
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_47_40_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_47_40_valid,
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_55_48_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_55_48_valid,
output      [7:0]                           ddrc_core_reg_dbg_wr_cam_63_56_valid,
output      [7:0]                           ddrc_core_reg_dbg_rd_cam_63_56_valid,

dwc_ddrctl_ddrc_cpedfi_if.cp_dfi_mp       cp_dfiif, // DFI interface

input  [DFI_TPHY_WRLAT_WIDTH-1:0]           reg_ddrc_dfi_tphy_wrlat,
input  [DFI_T_RDDATA_EN_WIDTH-1:0]          reg_ddrc_dfi_t_rddata_en,
input  [DFI_TPHY_WRCSLAT_WIDTH-1:0]             reg_ddrc_dfi_tphy_wrcslat,
input  [6:0]                    reg_ddrc_dfi_tphy_rdcslat,
input                           reg_ddrc_dfi_data_cs_polarity,

output [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]   dfi_wck_cs,
output [`MEMC_FREQ_RATIO-1:0]             dfi_wck_en,
output [2*`MEMC_FREQ_RATIO-1:0]           dfi_wck_toggle,

input                           reg_ddrc_dfi_reset_n,
input                           reg_ddrc_dfi_init_start,
input [DFI_FREQ_FSP_WIDTH-1:0]  reg_ddrc_dfi_freq_fsp,
input   [4:0]                   reg_ddrc_dfi_frequency,
input                           dfi_reset_n_in,
input                           init_mr_done_in,
output                          dfi_reset_n_ref,
output                          init_mr_done_out,


input   [T_PGM_X1_X1024_WIDTH-1:0]             reg_ddrc_t_pgm_x1_x1024,
input                                          reg_ddrc_t_pgm_x1_sel,
input   [T_PGMPST_X32_WIDTH-1:0]               reg_ddrc_t_pgmpst_x32,
input   [T_PGM_EXIT_WIDTH-1:0]                 reg_ddrc_t_pgm_exit,
input                                          reg_ddrc_ppr_en,
output                                         ddrc_reg_ppr_done,
input                                          reg_ddrc_ppr_pgmpst_en,


output                                       retryram_din,
output                                       retryram_waddr,
output                                       retryram_raddr,
output                                       retryram_re,
output                                       retryram_we,
output                                       retryram_mask,


input                           reg_ddrc_dfi_init_complete_en,
input                           reg_ddrc_frequency_ratio,      // Frequency ratio, 1 - 1:1 mode, 0 - 1:2 mode
input                           reg_ddrc_frequency_ratio_next, // Frequency ratio, 1 - 1:1 mode, 0 - 1:2 mode
input                           reg_ddrc_en_dfi_dram_clk_disable,       // 1=allow controller+PHY to stop the clock to DRAM

//---- register inputs ----
input   [BURST_RDWR_WIDTH-1:0]  reg_ddrc_burst_rdwr,            // 5'b00010=burst of 4 data read/write
                                                                // 5'b00100=burst of 8 data read/write
                                                                // 5'b01000=burst of 16 data read/write
                                                                // 5'b10000=burst of 32 data read/write

input                           reg_ddrc_dis_dq,                // 1=disable dequeue (stall scheduler), 0=normal operation
input                           reg_ddrc_dis_hif,               // 1=disable to accept rd/wr on hif (stall hif), 0=normal operation
input                           reg_ddrc_dis_wc,                // 1=disable write combine, 0=allow write combine

input   [NUM_LRANKS-1:0]        reg_ddrc_rank_refresh,         // cmd issuing refresh to rank
output  [NUM_LRANKS-1:0]        ddrc_reg_rank_refresh_busy,    // If 1: Previous dh_gs_rank_refresh has not been stored
input                           reg_ddrc_dis_auto_refresh,      // 1= disable auto_refresh issued by
                                                                // the controller. Issue refresh based only
                                                                // on the rankX_refresh command from reg_ddrc_rankX_refresh, where X = 0, 1, 2, 3
input                           reg_ddrc_dis_auto_ctrlupd,      // 1 = disable ctrlupd issued by the controller
                                                                // 0 = enable ctrlupd issued by the controller
input                           reg_ddrc_ctrlupd,               // ctrlupd command
input                           reg_ddrc_ctrlupd_burst,
output                          ddrc_reg_ctrlupd_burst_busy,
output                          ddrc_reg_ctrlupd_busy,          // If 1: Previous ctrlupd from APB register reg_ddrc_ctrlupd has not been initiated
input                           reg_ddrc_dis_auto_ctrlupd_srx,  // 1 = disable ctrlupd issued by the controller following a self-refresh exit
                                                                // ctrlupd command will be issued by APB register reg_ddrc_ctrlupd
                                                                // 0 = enable ctrlupd issued by the controller following a self-refresh exit
input                           reg_ddrc_ctrlupd_pre_srx,       // 1 = ctrlupd sent before SRX
                                                                // 0 = ctrlupd sent after SRX
input                           reg_ddrc_opt_vprw_sch,
input                           reg_ddrc_dis_speculative_act,
input                           reg_ddrc_w_starve_free_running,
input                           reg_ddrc_prefer_read,
input                           reg_ddrc_opt_act_lat,  
input   [RD_CAM_ADDR_WIDTH-1:0] reg_ddrc_lpr_num_entries,       // number of entries in low priority read queue
input                           reg_ddrc_lpr_num_entries_changed, // lpr_num_entries register has been changed
input   [15:0]                  reg_ddrc_mr,                    // mode register (MR) value written in init
input   [15:0]                  reg_ddrc_emr,                   // extended mode register (EMR) value written in init
input   [15:0]                  reg_ddrc_emr2,                  // extended mode register 2 (EMR2) value written in init
input   [15:0]                  reg_ddrc_emr3,                  // extended mode register 3 (EMR3) value written in init
input   [15:0]                  reg_ddrc_mr4,                   // mode register (MR4) value written in init
input   [15:0]                  reg_ddrc_mr5,                   // mode register (MR5) value written in init
input   [15:0]                  reg_ddrc_mr6,                   // mode register (MR6) value written in init
input   [15:0]                  reg_ddrc_mr22,                  // mode register (MR22) value written in init
input   [T_RCD_WIDTH-1:0] reg_ddrc_t_rcd,                 // tRCD: RAS-to-CAS delay
input   [T_RCD_WIDTH-1:0] reg_ddrc_t_rcd_write,           // tRCD: RAS-to-CAS delay - Write version for LPDDR5X
input   [T_RAS_MIN_WIDTH-1:0] reg_ddrc_t_ras_min,             // tRAS(min): minimum page open time
input   [T_RAS_MAX_WIDTH-1:0] reg_ddrc_t_ras_max,             // tRAS(max): maximum page open time
input   [T_RC_WIDTH-1:0] reg_ddrc_t_rc,                  // tRC: row cycle time
input   [T_RP_WIDTH-1:0] reg_ddrc_t_rp,                  // tRP: row precharge time
input   [T_RRD_WIDTH-1:0] reg_ddrc_t_rrd,                 // tRRD: RAS-to-RAS min delay
input   [T_RRD_S_WIDTH-1:0] reg_ddrc_t_rrd_s,               // tRRD_S: RAS-to-RAS min delay (short)
input   [RD2PRE_WIDTH-1:0] reg_ddrc_rd2pre,                // min read-to-precharge command delay
input   [WR2PRE_WIDTH-1:0] reg_ddrc_wr2pre,                // min write-to-precharge command delay
input   [RDA2PRE_WIDTH-1:0] reg_ddrc_rda2pre,               // min read-to-precharge command delay
input   [WRA2PRE_WIDTH-1:0] reg_ddrc_wra2pre,               // min write-to-precharge command delay
input                           reg_ddrc_pageclose,             // close open pages by default
input   [7:0]                   reg_ddrc_pageclose_timer,       // timer for close open pages by default
input   [2:0]                   reg_ddrc_page_hit_limit_rd,     // page-hit limiter for rd
input   [2:0]                   reg_ddrc_page_hit_limit_wr,     // page-hit limiter for wr
input                           reg_ddrc_opt_hit_gt_hpr,        // 0 - page-miss HPR > page-hit LPR; 1 - page-hit LPR > page-miss HPR
input   [2:0]                   reg_ddrc_visible_window_limit_rd,  // visible window limiter for rd
input   [2:0]                   reg_ddrc_visible_window_limit_wr,  // visible window limiter for wr
input   [REFRESH_MARGIN_WIDTH-1:0]        reg_ddrc_refresh_margin,        // how early to start trying to refresh or

input                                     reg_ddrc_force_clk_te_en,
                                                                          //  close a page for tRAS(max)
input   [PRE_CKE_X1024_WIDTH-1:0]         reg_ddrc_pre_cke_x1024,         // wait time at start of init sequence
                                                                          //  (in pulses of 1024-cycle timer)
input   [POST_CKE_X1024_WIDTH-1:0]        reg_ddrc_post_cke_x1024,        // wait time after asserting CKE in init sequence
                                                                          //  (in pulses of 1024-cycle timer)
input   [RD2WR_WIDTH-1:0]                 reg_ddrc_rd2wr,                 // min read-to-write command delay
input   [WR2RD_WIDTH-1:0]                 reg_ddrc_wr2rd,                 // min write-to-read command delay
input   [WR2RD_S_WIDTH-1:0]               reg_ddrc_wr2rd_s,               // min write-to-read command delay (short)
input   [5:0]                             reg_ddrc_refresh_burst,         // this + 1 = # of refreshes to burst
input   [T_CCD_WIDTH-1:0]            reg_ddrc_t_ccd,                 // tCCD: CAS-to-CAS min delay
input   [T_CCD_S_WIDTH-1:0]          reg_ddrc_t_ccd_s,               // tCCD_S: CAS-to-CAS min delay (short)
input   [ODTLOFF_WIDTH-1:0]          reg_ddrc_odtloff,               // ODTLoff: This is latency from CAS-2 command to tODToff reference.
input   [T_CCD_MW_WIDTH-1:0]         reg_ddrc_t_ccd_mw,              // tCCDMW: CAS-to-CAS min delay masked write
input   [RD2MR_WIDTH-1:0]            reg_ddrc_rd2mr,
input   [WR2MR_WIDTH-1:0]            reg_ddrc_wr2mr,
input                                reg_ddrc_use_slow_rm_in_low_temp,
input                                reg_ddrc_dis_trefi_x6x8,
input                                reg_ddrc_dis_trefi_x0125,
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: the inputs are not used in legacy ddr4 configurations
input   [T_PPD_WIDTH-1:0]            reg_ddrc_t_ppd,                 // tPPD: PRE(A)-to-PRE(A) min delay
//spyglass enable_block W240
input   [RD2WR_WIDTH-1:0]            reg_ddrc_rd2wr_s,
input   [MRR2RD_WIDTH-1:0]           reg_ddrc_mrr2rd,
input   [MRR2WR_WIDTH-1:0]           reg_ddrc_mrr2wr,
input   [MRR2MRW_WIDTH-1:0]          reg_ddrc_mrr2mrw,
input                                reg_ddrc_wck_on,
input                                reg_ddrc_wck_suspend_en,
input                                reg_ddrc_ws_off_en,
input   [WS_OFF2WS_FS_WIDTH-1:0]     reg_ddrc_ws_off2ws_fs,
input   [T_WCKSUS_WIDTH-1:0]         reg_ddrc_t_wcksus,
input   [WS_FS2WCK_SUS_WIDTH-1:0]    reg_ddrc_ws_fs2wck_sus,
input   [MAX_RD_SYNC_WIDTH-1:0]      reg_ddrc_max_rd_sync,
input   [MAX_WR_SYNC_WIDTH-1:0]      reg_ddrc_max_wr_sync,
input   [DFI_TWCK_DELAY_WIDTH-1:0]   reg_ddrc_dfi_twck_delay,
input   [DFI_TWCK_EN_RD_WIDTH-1:0]       reg_ddrc_dfi_twck_en_rd,
input   [DFI_TWCK_EN_WR_WIDTH-1:0]       reg_ddrc_dfi_twck_en_wr,
input   [DFI_TWCK_EN_FS_WIDTH-1:0]       reg_ddrc_dfi_twck_en_fs,
input   [DFI_TWCK_DIS_WIDTH-1:0]         reg_ddrc_dfi_twck_dis,
input   [DFI_TWCK_FAST_TOGGLE_WIDTH-1:0] reg_ddrc_dfi_twck_fast_toggle,
input   [DFI_TWCK_TOGGLE_WIDTH-1:0]      reg_ddrc_dfi_twck_toggle,
input   [DFI_TWCK_TOGGLE_CS_WIDTH-1:0]   reg_ddrc_dfi_twck_toggle_cs,
input   [DFI_TWCK_TOGGLE_POST_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post,
input                                    reg_ddrc_dfi_twck_toggle_post_rd_en,
input   [DFI_TWCK_TOGGLE_POST_RD_WIDTH-1:0] reg_ddrc_dfi_twck_toggle_post_rd,
input   [T_CKE_WIDTH-1:0] reg_ddrc_t_cke,                 // tCKE: min CKE transition times
input   [T_FAW_WIDTH-1:0] reg_ddrc_t_faw,                 // tFAW: rolling window of 4 activates allowed
                                                                //       to a given rank
input   [T_RFC_MIN_WIDTH-1:0]                   reg_ddrc_t_rfc_min,             // tRC(min): min time between refreshes
input   [T_RFC_MIN_AB_WIDTH-1:0] reg_ddrc_t_rfc_min_ab,
input   [T_PBR2PBR_WIDTH-1:0]    reg_ddrc_t_pbr2pbr,             // tpbR2pbR: min time between LPDDR4 per-bank refreshes different bank
input   [T_PBR2ACT_WIDTH-1:0]    reg_ddrc_t_pbr2act,             // tpbR2pbR: min time between LPDDR5 per-bank refreshes and act different bank
input                                     reg_ddrc_rfm_en,
input                                     reg_ddrc_dis_mrrw_trfc,
input                                     reg_ddrc_rfmsbc,
input   [RAAIMT_WIDTH-1:0]                reg_ddrc_raaimt,
input   [RAAMULT_WIDTH-1:0]               reg_ddrc_raamult,
input   [RAADEC_WIDTH-1:0]                reg_ddrc_raadec,
input   [RFMTH_RM_THR_WIDTH-1:0]          reg_ddrc_rfmth_rm_thr,
input   [INIT_RAA_CNT_WIDTH-1:0]          reg_ddrc_init_raa_cnt,
input   [T_RFMPB_WIDTH-1:0]               reg_ddrc_t_rfmpb,
input   [DBG_RAA_RANK_WIDTH-1:0]          reg_ddrc_dbg_raa_rank,
input   [DBG_RAA_BG_BANK_WIDTH-1:0]       reg_ddrc_dbg_raa_bg_bank,
output  [DBG_RAA_CNT_WIDTH-1:0]           ddrc_reg_dbg_raa_cnt,
output  [NUM_RANKS-1:0]                   ddrc_reg_rank_raa_cnt_gt0,
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: the inputs are not used in legacy ddr4 configurations
input                           reg_ddrc_t_refi_x1_sel,      // specifies whether reg_ddrc_t_refi_x1_x32 reg is x1 or x32
//spyglass enable_block W240
input                           reg_ddrc_refresh_to_x1_sel, // specifies whether reg_ddrc_refresh_to_x1_x32 reg is x1 or x32
input   [T_REFI_X1_X32_WIDTH-1:0]                  reg_ddrc_t_refi_x1_x32,      // tRFC(nom): nominal avg. required refresh period
input   [T_MR_WIDTH-1:0]        reg_ddrc_t_mr,                  // tMRD: recorvery time for mode register update
input   [REFRESH_TO_X1_X32_WIDTH-1:0]                   reg_ddrc_refresh_to_x1_x32,     // idle period before doing speculative refresh
input                           reg_ddrc_en_2t_timing_mode,     // Enable 2T timing mode in the controller
input                           reg_ddrc_opt_wrcam_fill_level,
input [3:0]                     reg_ddrc_delay_switch_write,
input [WR_CAM_ADDR_WIDTH-1:0]   reg_ddrc_wr_pghit_num_thresh,
input [RD_CAM_ADDR_WIDTH-1:0]   reg_ddrc_rd_pghit_num_thresh,
input [WR_CAM_ADDR_WIDTH-1:0]   reg_ddrc_wrcam_highthresh,
input [WR_CAM_ADDR_WIDTH-1:0]   reg_ddrc_wrcam_lowthresh,
input [WRECC_CAM_LOWTHRESH_WIDTH-1:0] reg_ddrc_wrecc_cam_lowthresh,
input [WRECC_CAM_HIGHTHRESH_WIDTH-1:0] reg_ddrc_wrecc_cam_highthresh,
input                           reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level,
input                           reg_ddrc_dis_opt_valid_wrecc_cam_fill_level,
input [7:0]                     reg_ddrc_wr_page_exp_cycles,
input [7:0]                     reg_ddrc_rd_page_exp_cycles,
input [7:0]                     reg_ddrc_wr_act_idle_gap,
input [7:0]                     reg_ddrc_rd_act_idle_gap,
input                           reg_ddrc_dis_opt_ntt_by_act,
input                           reg_ddrc_dis_opt_ntt_by_pre,
input                           reg_ddrc_dis_opt_wrecc_collision_flush,
input                           reg_ddrc_prefer_write,          // prefer writes (debug feature)
input   [6:0]                   reg_ddrc_rdwr_idle_gap,         // idle period before switching from reads to writes
input   [POWERDOWN_EN_WIDTH-1:0]     reg_ddrc_powerdown_en,          // enable powerdown during idle periods
input   [POWERDOWN_TO_X32_WIDTH-1:0] reg_ddrc_powerdown_to_x32,      // powerdown timeout: idle period before entering
                                                                     //  powerdown (if reg_ddrc_powerdown_en=1)
                                                                     //  (in pulses of 32-cycle timer)
input   [T_XP_WIDTH-1:0] reg_ddrc_t_xp,                  // tXP: powerdown exit time

input [SELFREF_SW_WIDTH-1:0]    reg_ddrc_selfref_sw,
input                           reg_ddrc_hw_lp_en,
input                           reg_ddrc_hw_lp_exit_idle_en,
input   [SELFREF_TO_X32_WIDTH-1:0]                   reg_ddrc_selfref_to_x32,
input   [HW_LP_IDLE_X32_WIDTH-1:0]                  reg_ddrc_hw_lp_idle_x32,

input   [DFI_T_CTRLUPD_INTERVAL_MIN_X1024_WIDTH-1:0]                   reg_ddrc_dfi_t_ctrlupd_interval_min_x1024,
input   [DFI_T_CTRLUPD_INTERVAL_MAX_X1024_WIDTH-1:0]                   reg_ddrc_dfi_t_ctrlupd_interval_max_x1024,
input   [DFI_T_CTRLUPD_BURST_INTERVAL_X8_WIDTH-1:0]                    reg_ddrc_dfi_t_ctrlupd_burst_interval_x8,
input  [DFI_T_CTRLUPD_INTERVAL_TYPE1_WIDTH-1:0]                        reg_ddrc_dfi_t_ctrlupd_interval_type1,       // max time between controller updates for PPT2.
input  [DFI_T_CTRLUPD_INTERVAL_TYPE1_UNIT_WIDTH-1:0]                   reg_ddrc_dfi_t_ctrlupd_interval_type1_unit,  // t_ctrlupd_interval_type1 unit

input [SELFREF_EN_WIDTH-1:0]    reg_ddrc_selfref_en,            // self refresh enable


input   [NUM_RANKS-1:0]         reg_ddrc_mr_rank,               //   register i/p for software configuarble rank selection
input   [T_XSR_WIDTH-1:0] reg_ddrc_t_xsr,                 // SRX to commands (unit of 1 cycle)


input                           reg_ddrc_refresh_update_level,  // toggle this signal if refresh value has to be updated
                                                                // used when freq is changed on the fly

input   [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0]                  reg_ddrc_refresh_timer0_start_value_x32,        // rank 0 refresh time start value
input   [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0]                  reg_ddrc_refresh_timer1_start_value_x32,        // rank 1 refresh timer start value

input   [NUM_RANKS-1:0]         reg_ddrc_rank0_wr_odt,  // ODT settings for 4 ranks + controller when writing to rank 0
input   [NUM_RANKS-1:0]         reg_ddrc_rank0_rd_odt,  // ODT settings for 4 ranks + controller when reading from rank 0
input   [NUM_RANKS-1:0]         reg_ddrc_rank1_wr_odt,  // ODT settings for 4 ranks + controller when writing to rank 1
input   [NUM_RANKS-1:0]         reg_ddrc_rank1_rd_odt,  // ODT settings for 4 ranks + controller when reading from rank 1
input   [7:0]                   reg_ddrc_hpr_xact_run_length,
input   [15:0]                  reg_ddrc_hpr_max_starve,
input   [7:0]                   reg_ddrc_lpr_xact_run_length,
input   [15:0]                  reg_ddrc_lpr_max_starve,
input   [7:0]                   reg_ddrc_w_xact_run_length,
input   [15:0]                  reg_ddrc_w_max_starve,

input   [DFI_T_CTRLUP_MIN_WIDTH-1:0]                   reg_ddrc_dfi_t_ctrlup_min, // min time for which the ctrlup request should stay high
input   [DFI_T_CTRLUP_MAX_WIDTH-1:0]                   reg_ddrc_dfi_t_ctrlup_max, // max time for which the ctrlup request can stay high

input   [READ_LATENCY_WIDTH-1:0] reg_ddrc_read_latency,  // read latency as seen by controller
input   [WRITE_LATENCY_WIDTH-1:0]rl_plus_cmd_len,

input   [DIFF_RANK_RD_GAP_WIDTH-1:0]                   reg_ddrc_diff_rank_rd_gap,  // cycle gap between reads to different ranks
input   [DIFF_RANK_WR_GAP_WIDTH-1:0]                   reg_ddrc_diff_rank_wr_gap,  // cycle gap between writes to different ranks
input   [RD2WR_DR_WIDTH-1:0]                         reg_ddrc_rd2wr_dr,
input   [WR2RD_DR_WIDTH-1:0]                         reg_ddrc_wr2rd_dr,
input   [3:0]                   reg_ddrc_max_rank_rd,   // max reasd to a given rank before allowing other ranks
                                                        // a fair chance
input   [3:0]                   reg_ddrc_max_rank_wr,   // max writes to a given rank before allowing other ranks
                                                        // a fair chance

input   [1:0]                   reg_ddrc_active_ranks,

input                           reg_ddrc_dis_max_rank_rd_opt,   //
input                           reg_ddrc_dis_max_rank_wr_opt,   //
input                           reg_ddrc_ecc_type,
input   [2:0]                   reg_ddrc_ecc_mode,        // ECC mode indicator
input                           reg_ddrc_ecc_ap_en,
input                           reg_ddrc_ecc_region_remap_en,
input   [6:0]                   reg_ddrc_ecc_region_map,
input   [1:0]                   reg_ddrc_ecc_region_map_granu,
input                           reg_ddrc_ecc_region_map_other,
input                           reg_ddrc_ecc_region_parity_lock,
input                           reg_ddrc_ecc_region_waste_lock,
input   [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0]                   reg_ddrc_blk_channel_idle_time_x32,
input   [4:0]                   reg_ddrc_active_blk_channel,
input                           reg_ddrc_blk_channel_active_term,

//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: the inputs are notused in some configurations
input                           reg_ddrc_data_poison_en,  // Enables ECC data poisoning
input   [`MEMC_RANK_BITS-1:0]   reg_ddrc_ecc_poison_rank,
input   [`MEMC_BG_BITS-1:0]     reg_ddrc_ecc_poison_bg,
input   [`MEMC_BANK_BITS-1:0]   reg_ddrc_ecc_poison_bank,
input   [`MEMC_PAGE_BITS-1:0]   reg_ddrc_ecc_poison_row,
input   [11:0]                  reg_ddrc_ecc_poison_col,
//spyglass enable_block W240

                                                        // data is passed on the ECC bits

output                          ddrc_reg_capar_poison_complete,



// for address mapper
input   [AM_BANK_WIDTH-1:0]     reg_ddrc_addrmap_bank_b0,
input   [AM_BANK_WIDTH-1:0]     reg_ddrc_addrmap_bank_b1,
input   [AM_BANK_WIDTH-1:0]     reg_ddrc_addrmap_bank_b2,
input   [AM_BG_WIDTH-1:0]       reg_ddrc_addrmap_bg_b0,
input   [AM_BG_WIDTH-1:0]       reg_ddrc_addrmap_bg_b1,
input   [AM_CS_WIDTH-1:0]       reg_ddrc_addrmap_cs_bit0,
input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b3,
input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b4,
input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b5,
input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b6,
input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b7,
input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b8,
input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b9,
input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b10,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b0,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b1,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b2,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b3,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b4,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b5,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b6,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b7,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b8,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b9,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b10,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b11,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b12,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b13,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b14,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b15,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b16,
input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b17,



input                           reg_ddrc_bank_hash_en,
// outputs to status & interrupt registers
// outputs to debug registers
output  [RD_CAM_ADDR_WIDTH:0]   ddrc_reg_dbg_hpr_q_depth,
output  [RD_CAM_ADDR_WIDTH:0]   ddrc_reg_dbg_lpr_q_depth,
output  [WR_CAM_ADDR_WIDTH:0]   ddrc_reg_dbg_w_q_depth,
output                          ddrc_reg_dbg_stall,             // stall
output                          ddrc_reg_dbg_stall_rd,             // stall
output                          ddrc_reg_dbg_stall_wr,             // stall
output                          ddrc_reg_selfref_cam_not_empty,
output [2:0]                    ddrc_reg_selfref_state,
output [2:0]                    ddrc_reg_operating_mode,        // global schedule FSM state

output [SELFREF_TYPE_WIDTH-1:0] ddrc_reg_selfref_type,
output                          ddrc_reg_wr_q_empty,
output                          ddrc_reg_rd_q_empty,
output                          ddrc_reg_wr_data_pipeline_empty,
output                          ddrc_reg_rd_data_pipeline_empty,

input                           reg_ddrc_dis_auto_zq,           // when 1: disable auto zqcs
input                           reg_ddrc_dis_srx_zqcl,          // when 1: disable zqcl after self-refresh exit
input                           reg_ddrc_dis_srx_zqcl_hwffc,    // when 1, disable zqcl at hwffc end
input                           reg_ddrc_zq_resistor_shared,
input [T_ZQ_LONG_NOP_WIDTH-1:0]                    reg_ddrc_t_zq_long_nop,         // time to wait in ZQCL during init sequence
input [T_ZQ_SHORT_NOP_WIDTH-1:0]                     reg_ddrc_t_zq_short_nop,        // time to wait in ZQCS during init sequence
input [T_ZQ_SHORT_INTERVAL_X1024_WIDTH-1:0]                    reg_ddrc_t_zq_short_interval_x1024,  // interval between auto ZQCS commands
input                           reg_ddrc_zq_calib_short,            // zq calib short command
output                          ddrc_reg_zq_calib_short_busy,       // If 1: Previous zq calib short has not been initiated



input                   reg_ddrc_lpddr5x,
input                   reg_ddrc_per_bank_refresh,      // REF Per bank//Added by Naveen B
input                   reg_ddrc_per_bank_refresh_opt_en,
input                   reg_ddrc_fixed_crit_refpb_bank_en,
input [1:0]             reg_ddrc_auto_refab_en,
input [REFRESH_TO_AB_X32_WIDTH-1:0] reg_ddrc_refresh_to_ab_x32,
input                   reg_ddrc_lpddr4,
input                   reg_ddrc_lpddr5,
input [BANK_ORG_WIDTH-1:0]             reg_ddrc_bank_org,
input [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre,
input                   reg_ddrc_stay_in_selfref,
input [T_CMDCKE_WIDTH-1:0] reg_ddrc_t_cmdcke,
input                         reg_ddrc_dsm_en,
input  [T_PDN_WIDTH-1:0]      reg_ddrc_t_pdn,
input  [T_XSR_DSM_X1024_WIDTH-1:0]  reg_ddrc_t_xsr_dsm_x1024,
input  [T_CSH_WIDTH-1:0]      reg_ddrc_t_csh,
output [BANK_BITS*NUM_RANKS-1:0]  hif_refresh_req_bank,


output [NUM_RANKS-1:0]    hif_refresh_req,
output [6*NUM_RANKS-1:0]  hif_refresh_req_cnt,
output [2:0]              hif_refresh_req_derate,
output [NUM_RANKS-1:0]    hif_refresh_active,


//
input [2:0]             reg_ddrc_nonbinary_device_density,
input                   reg_ddrc_dfi_phyupd_en,         // Enable for DFI PHY update logic
input                   reg_ddrc_dfi_phymstr_en,        // Enable for PHY Master Interface
input  [7:0]            reg_ddrc_dfi_phymstr_blk_ref_x32,// Number of 32 DFI cycles that is delayed to block refresh when there is PHY Master
input                   reg_ddrc_dis_cam_drain_selfref, // Disable CAM draining before entering selfref
input                   reg_ddrc_lpddr4_sr_allowed,     // Allow transition from SR-PD to SR and back to SR-PD when PHY Master request
input                   reg_ddrc_lpddr4_opt_act_timing,
input                   reg_ddrc_lpddr5_opt_act_timing,
input  [DFI_T_CTRL_DELAY_WIDTH-1:0]            reg_ddrc_dfi_t_ctrl_delay,  // timer value for DFI tctrl_delay
input  [DFI_T_WRDATA_DELAY_WIDTH-1:0]            reg_ddrc_dfi_t_wrdata_delay,// timer value for DFI twrdata_delay

input  [DFI_T_DRAM_CLK_DISABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_disable,
input  [DFI_T_DRAM_CLK_ENABLE_WIDTH-1:0]  reg_ddrc_dfi_t_dram_clk_enable,
input  [T_CKSRE_WIDTH-1:0] reg_ddrc_t_cksre,
input  [T_CKSRX_WIDTH-1:0] reg_ddrc_t_cksrx,
input  [T_CKCSX_WIDTH-1:0] reg_ddrc_t_ckcsx,
input  [T_CKESR_WIDTH-1:0] reg_ddrc_t_ckesr,

input                                  reg_ddrc_dfi_lp_data_req_en,
input                                  reg_ddrc_dfi_lp_en_data,
input  [DFI_LP_WAKEUP_DATA_WIDTH-1:0]  reg_ddrc_dfi_lp_wakeup_data,

input                                  reg_ddrc_dfi_lp_en_pd,
input  [DFI_LP_WAKEUP_PD_WIDTH-1:0]    reg_ddrc_dfi_lp_wakeup_pd,
input                                  reg_ddrc_dfi_lp_en_sr,
input  [DFI_LP_WAKEUP_SR_WIDTH-1:0]    reg_ddrc_dfi_lp_wakeup_sr,
input                                  reg_ddrc_dfi_lp_en_dsm,
input  [DFI_LP_WAKEUP_DSM_WIDTH-1:0]   reg_ddrc_dfi_lp_wakeup_dsm,


input  [1:0]            reg_ddrc_skip_dram_init,
input  [DFI_TLP_RESP_WIDTH-1:0]            reg_ddrc_dfi_tlp_resp,

input  [TARGET_FREQUENCY_WIDTH-1:0]     reg_ddrc_target_frequency,
// Frequency selection
// From/To APB (register)
input  [T_VRCG_ENABLE_WIDTH-1:0] reg_ddrc_t_vrcg_enable,
input  [T_VRCG_DISABLE_WIDTH-1:0] reg_ddrc_t_vrcg_disable,
input                   reg_ddrc_target_vrcg,
input  [1:0]            reg_ddrc_hwffc_en,
input                   reg_ddrc_hwffc_mode,
input                   reg_ddrc_init_fsp,
input   [6:0]           reg_ddrc_t_zq_stop,
input   [1:0]           reg_ddrc_zq_interval,
input                   reg_ddrc_skip_zq_stop_start,
input                   reg_ddrc_init_vrcg,
input                   reg_ddrc_skip_mrw_odtvref,
input                   reg_ddrc_dvfsq_enable,
input                   reg_ddrc_dvfsq_enable_next,
input [NPORTS-1:0]      xpi_ddrc_port_disable_ack,
input [NPORTS-2:0]      xpi_ddrc_wch_locked,

// This signal can be typeof DWC_ddrctl_hwffcmrw_if.at_hwffcmrw_op, but instead employ typeof structure hwffcmrw_if_at_hwffcmrw_op_s intentionally.
// 'output' signature is needed for occap automation.
output hwffcmrw_if_at_hwffcmrw_op_s                hwffcmrw_op_s,    

output                  hwffc_target_freq_en,
output  [TARGET_FREQUENCY_WIDTH-1:0]    hwffc_target_freq,
output  [TARGET_FREQUENCY_WIDTH-1:0]    hwffc_target_freq_init,

output                  ddrc_reg_hwffc_in_progress,
output [TARGET_FREQUENCY_WIDTH-1:0]     ddrc_reg_current_frequency,
output                  ddrc_reg_current_fsp,
output                  ddrc_reg_current_vrcg,
output                  ddrc_reg_hwffc_operating_mode,
output                  ddrc_xpi_port_disable_req,
output                  ddrc_xpi_clock_required,
// to WU
output                  hwffc_hif_wd_stall,
output                  hwffc_i_reg_ddrc_dis_auto_zq,




//registers for DDR5

// new i/os not in ddrc.v i/o list
// connects ddrc_ctrl.v sub-blocks to rest of ddrc.v e.g. mr/rd/rt etc
input                              rd_ih_ie_re_rdy,

output [IE_PW_BITS-1:0]            ih_mr_ie_pw,

// TE to MR

// PI to RT


//signals for look up BT table
output                             ih_rd_lkp_brt_vld,
input [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0]    hif_mrr_data,

input                    rd_mr4_data_valid,
input                    rt_rd_rd_mrr_ext,


output                                 ih_te_rd_valid,
output                                 ih_te_wr_valid,

//--------------------------------------------------------------
//---------------- MR -> IH/WU Interface --------------------------
//--------------------------------------------------------------

//--------------------------------------------------------------
//---------------- MR -> TS Interface --------------------------
//--------------------------------------------------------------
input                                  dfi_wr_q_empty,

//--------------------------------------------------------------
//---------------- PI -> TS Interface --------------------------
//--------------------------------------------------------------
output                                 pi_gs_geardown_mode_on, // to MR etc

//--------------------------------------------------------------
//---------------- PI -> RT Interface --------------------------
//--------------------------------------------------------------

//--------------------------------------------------------------
//---------------- RT -> TS Interface --------------------------
//--------------------------------------------------------------
input                                  rt_gs_empty,            // RT has no read in its FIFO
input                                  rt_gs_empty_delayed,    // RT has no read in its FIFO - delayed version for clock gating logic

//--------------------------------------------------------------
//---------------- TE -> WU Interface --------------------------
//--------------------------------------------------------------
output                                 te_wu_wrdata_stall_req,

//--------------------------------------------------------------
//---------------- TE -> MR Interface --------------------------
//--------------------------------------------------------------
output                                    ts_pi_mwr,                      // masked write information
output                                    ts_pi_wr32,
output                                    ts_pi_2nd_half,
output                                    ts_cam_clear_en,

//--------------------------------------------------------------
//---------------- TE -> WU Interface --------------------------
//--------------------------------------------------------------

//--------------------------------------------------------------
//---------------- TS -> MR Interface --------------------------
//--------------------------------------------------------------
output [MAX_CMD_NUM*NUM_RANKS-1:0]        gs_pi_cs_n,


//--------------------------------------------------------------
//---------------- WU -> IH Interface --------------------------
//--------------------------------------------------------------

//--------------------------------------------------------------
//---------------- WU -> TE Interface --------------------------
//--------------------------------------------------------------

//--------------------------------------------------------------
//---------------- WU -> TS Interface --------------------------
//--------------------------------------------------------------

output                                        retry_fifo_empty,
output                                        retry_rt_rdatavld_gate_en,
output                                        retry_rt_fifo_init_n,
output                                        retry_rt_fatl_err_pulse,
output                                        retry_rt_now_sw_intervention,
output [7:0]                                  retry_rt_rd_timeout_value,

//--------------------------------------------------------------
//------------- Retry -> DFI Interface -------------------------
//--------------------------------------------------------------
output                                        retry_dfi_sel,
output [PHY_MASK_WIDTH-1:0]                   retry_phy_dm,
output [PHY_DATA_WIDTH-1:0]                   retry_phy_wdata,
output                                        retry_phy_wdata_vld_early,
output                                        retry_dfi_rddata_en,
output [`MEMC_FREQ_RATIO-1:0]                 retry_dfi_wrdata_en,


// active_ranks_int
output   [`MEMC_NUM_RANKS-1:0]                reg_ddrc_active_ranks_int,
input                                         ddrc_cg_en,
output                                        gs_pi_data_pipeline_empty,

output                                        mrr_op_on, // to ddrc_cg_en
output                                        pi_gs_mpr_mode, // to RT

output                                        ih_busy, // to ddrc_cg_en


input   [DFI_TPHY_WRLAT_WIDTH-1:0]            mr_t_wrlat,           // write latency (command to data latency)
input   [5:0]                                 mr_t_wrdata,          // tphy_wrdata parameter from dfi spec
input   [6:0]                                 mr_t_rddata_en,       // t_rddata_en parameter from dfi spec
input   [DFI_TWCK_EN_RD_WIDTH-2:0]            mr_lp_data_rd,
input   [DFI_TWCK_EN_WR_WIDTH-2:0]            mr_lp_data_wr,



//input dfi_cmd_delay_1r,
//input dfi_cmd_delay_2r,
input [CMD_DELAY_BITS-1:0]     dfi_cmd_delay,

output                         pi_gs_dll_off_mode,

output [2:0]                   reg_ddrc_fgr_mode_gated,

output                         ddrc_phy_cal_dl_enable,

output                         gs_pi_op_is_exit_selfref,
output                         ih_ie_busy,

output                         perf_op_is_crit_ref,
output                         perf_op_is_spec_ref,

// occap specific input/output

//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used in generate blocks
input                      ddrc_cmp_en,
input                      ddrc_ctrl_cmp_poison,
input                      ddrc_ctrl_cmp_poison_full,
input                      ddrc_ctrl_cmp_poison_err_inj,
//spyglass enable_block W240
output                     ddrc_ctrl_cmp_error,
output                     ddrc_ctrl_cmp_error_full,
output                     ddrc_ctrl_cmp_error_seq,
output                     ddrc_ctrl_cmp_poison_complete,

input                      reg_ddrc_dis_dqsosc_srx,
input                      reg_ddrc_dqsosc_enable,                 // DQSOSC enable
input  [T_OSCO_WIDTH-1:0]  reg_ddrc_t_osco,                        // t_osco timing
input  [7:0]               reg_ddrc_dqsosc_runtime,                // Oscillator runtime
input  [7:0]               reg_ddrc_wck2dqo_runtime,               // Oscillator runtime only for LPDDR5
input  [11:0]              reg_ddrc_dqsosc_interval,               // DQSOSC inverval
input                      reg_ddrc_dqsosc_interval_unit,          // DQSOSC interval unit
output [2:0]               dqsosc_state,
output [NUM_RANKS-1:0]     dqsosc_per_rank_stat,
//output [3:0]               pi_ph_snoop_en,
//output                     pi_rt_rd_mrr_snoop,

`ifdef SNPS_ASSERT_ON
input  [1:0]                             reg_ddrc_data_bus_width,
`endif // SNPS_ASSERT_ON
`ifndef SYNTHESIS
  `ifdef SNPS_ASSERT_ON
input                                   reg_ddrc_rd_link_ecc_enable,
  `endif // SNPS_ASSERT_ON
`endif // SYNTHESIS



// additional outputs for ddrc_assertions.sv
output [NUM_LRANKS-1:0]        reg_ddrc_ext_rank_refresh
,input                                          reg_ddrc_ppt2_en
,input                                          reg_ddrc_ppt2_override
,input                                          reg_ddrc_ctrlupd_after_dqsosc
,input                                          reg_ddrc_ppt2_wait_ref
,input  [PPT2_BURST_NUM_WIDTH-1:0]              reg_ddrc_ppt2_burst_num
,input                                          reg_ddrc_ppt2_burst
,output                                         ddrc_reg_ppt2_burst_busy
,output [PPT2_STATE_WIDTH-1:0]                  ddrc_reg_ppt2_state
,input  [PPT2_CTRLUPD_NUM_DFI_WIDTH-1:0]        reg_ddrc_ppt2_ctrlupd_num_dfi1
,input  [PPT2_CTRLUPD_NUM_DFI_WIDTH-1:0]        reg_ddrc_ppt2_ctrlupd_num_dfi0


//--------------------------------------------------------------
//---------------- XLTR -> RT Interface ------------------------
//--------------------------------------------------------------

);

wire [NPORTS-1:0] i_cactive_in_ddrc_sync;


genvar gen_cactive_in_ddrc_sync;
generate
// generate individual BCM21 for each bit of cactive_in_ddrc
for (gen_cactive_in_ddrc_sync=0; gen_cactive_in_ddrc_sync<NPORTS; gen_cactive_in_ddrc_sync=gen_cactive_in_ddrc_sync+1)
begin : cactive_in_ddrc_sync

   if (A_SYNC_TABLE[gen_cactive_in_ddrc_sync]==0) begin: A_async
   // this branch is taken even when there is no arbiter. Default value for nports is 1 and default value for a_sync is 0
   // Each bit of cactive_in_ddrc could be on diff clock domain
      DWC_ddr_umctl2_bitsync
      
      #( .BCM_SYNC_TYPE   (BCM_DDRC_N_SYNC),
         .BCM_VERIF_EN    (BCM_VERIF_EN))
      cactive_in_ddrc_sync
      (  .clk_d          (core_ddrc_core_clk),
         .rst_d_n        (core_ddrc_rstn),
         .data_s         (cactive_in_ddrc[gen_cactive_in_ddrc_sync]),
         .data_d         (i_cactive_in_ddrc_sync[gen_cactive_in_ddrc_sync]));

   end
   else begin: A_sync

      reg cactive_in_ddrc_r;

      always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
         if(!core_ddrc_rstn) begin
            cactive_in_ddrc_r <= 1'b0;
         end else begin
            cactive_in_ddrc_r <= cactive_in_ddrc[gen_cactive_in_ddrc_sync];
         end
      end

      assign i_cactive_in_ddrc_sync[gen_cactive_in_ddrc_sync] = cactive_in_ddrc_r;

   end
end // generate cactive_in_ddrc_sync

endgenerate

wire cactive_in_ddrc_sync_or = |i_cactive_in_ddrc_sync;

//----------------------- OCCAP-related parameters ----------------------------

localparam NUM_INST = OCCAP_EN==1 ? 2 : 1;
localparam NUM_OUTS = 523;// WARNING: update whenever a new output is added/removed

localparam PW       = 32;

localparam OUT0_W   = 1; // hif_cmd_stall
localparam OUT1_W   = 1; // hif_rcmd_stall
localparam OUT2_W   = 1; // hif_wcmd_stall
localparam OUT3_W   = 1; // hif_wdata_ptr_valid
localparam OUT4_W   = WDATA_PTR_BITS; // hif_wdata_ptr
localparam OUT5_W   = 1; // hif_wdata_ptr_addr_err
localparam OUT6_W   = `MEMC_HIF_CREDIT_BITS; // hif_lpr_credit
localparam OUT7_W   = 1; // hif_wr_credit
localparam OUT8_W   = `MEMC_HIF_CREDIT_BITS; // hif_hpr_credit
localparam OUT9_W   = 1; // ddrc_reg_mr_wr_busy
localparam OUT10_W  = 1; // ddrc_reg_pda_done
localparam OUT11_W  = 1; // ddrc_reg_zq_reset_busy
localparam OUT12_W  = 1; // hif_cmd_q_not_empty
localparam OUT13_W  = 1; // csysack_ddrc
localparam OUT14_W  = SELFREF_TYPE_WIDTH; // stat_ddrc_reg_selfref_type
localparam OUT15_W  = 4; // stat_ddrc_reg_retry_current_state
localparam OUT16_W  = 3; // dbg_dfi_ie_cmd_type
localparam OUT17_W  = BSM_BITS+1; // ddrc_reg_num_alloc_bsm
localparam OUT18_W  = 1; // perf_hif_rd_or_wr
localparam OUT19_W  = 1; // perf_hif_wr
localparam OUT20_W  = 1; // perf_hif_rd
localparam OUT21_W  = 1; // perf_hif_rmw
localparam OUT22_W  = 1; // perf_hif_hi_pri_rd
localparam OUT23_W  = 1; // perf_read_bypass
localparam OUT24_W  = 1; // perf_act_bypass
localparam OUT25_W  = 1; // perf_hpr_xact_when_critical
localparam OUT26_W  = 1; // perf_lpr_xact_when_critical
localparam OUT27_W  = 1; // perf_wr_xact_when_critical
localparam OUT28_W  = 1; // perf_op_is_activate
localparam OUT29_W  = 1; // perf_op_is_rd_or_wr
localparam OUT30_W  = 1; // perf_op_is_rd_activate
localparam OUT31_W  = 1; // perf_op_is_rd
localparam OUT32_W  = 1; // perf_op_is_wr
localparam OUT33_W  = 1; // perf_op_is_mwr
localparam OUT34_W  = 1; // perf_op_is_precharge
localparam OUT35_W  = 1; // perf_precharge_for_rdwr
localparam OUT36_W  = 1; // perf_precharge_for_other
localparam OUT37_W  = 1; // perf_rdwr_transitions
localparam OUT38_W  = 1; // perf_write_combine
localparam OUT39_W  = 1; // perf_war_hazard
localparam OUT40_W  = 1; // perf_raw_hazard
localparam OUT41_W  = 1; // perf_waw_hazard
localparam OUT42_W  = NUM_RANKS; // perf_op_is_enter_selfref
localparam OUT43_W  = NUM_RANKS; // perf_op_is_enter_powerdown
localparam OUT44_W  = NUM_RANKS; // perf_op_is_enter_mpsm
localparam OUT45_W  = NUM_RANKS; // perf_selfref_mode
localparam OUT46_W  = 1; // perf_op_is_refresh
localparam OUT47_W  = 1; // perf_op_is_load_mode
localparam OUT48_W  = 1; // perf_op_is_zqcl
localparam OUT49_W  = 1; // perf_op_is_zqcs
localparam OUT50_W  = RANK_BITS_DUP; // perf_rank
localparam OUT51_W  = BANK_BITS; // perf_bank
localparam OUT52_W  = BG_BITS_DUP; // perf_bg
localparam OUT53_W  = CID_WIDTH_DUP; // perf_cid
localparam OUT54_W  = RANK_BITS_DUP; // perf_bypass_rank
localparam OUT55_W  = BANK_BITS; // perf_bypass_bank
localparam OUT56_W  = BG_BITS_DUP; // perf_bypass_bg
localparam OUT57_W  = CID_WIDTH_DUP; // perf_bypass_cid
localparam OUT58_W  = 1; // perf_bsm_alloc
localparam OUT59_W  = 1; // perf_bsm_starvation
localparam OUT60_W  = BSM_BITS+1; // perf_num_alloc_bsm
localparam OUT61_W  = 3; // ddrc_core_reg_dbg_operating_mode
localparam OUT62_W  = 5; // ddrc_core_reg_dbg_global_fsm_state
localparam OUT63_W  = 5; // ddrc_core_reg_dbg_init_curr_state
localparam OUT64_W  = 5; // ddrc_core_reg_dbg_init_next_state
localparam OUT65_W  = 2; // ddrc_core_reg_dbg_ctrlupd_state
localparam OUT66_W  = 2; // ddrc_core_reg_dbg_lpr_q_state
localparam OUT67_W  = 2; // ddrc_core_reg_dbg_hpr_q_state
localparam OUT68_W  = 2; // ddrc_core_reg_dbg_wr_q_state
localparam OUT69_W  = RD_CAM_ADDR_WIDTH+1; // ddrc_core_reg_dbg_lpr_q_depth
localparam OUT70_W  = RD_CAM_ADDR_WIDTH+1; // ddrc_core_reg_dbg_hpr_q_depth
localparam OUT71_W  = WR_CAM_ADDR_WIDTH+1; // ddrc_core_reg_dbg_wr_q_depth
localparam OUT72_W  = 1; // ddrc_core_reg_dbg_hif_cmd_stall
localparam OUT73_W  = 1; // ddrc_core_reg_dbg_hif_rcmd_stall
localparam OUT74_W  = 1; // ddrc_core_reg_dbg_hif_wcmd_stall
localparam OUT75_W  = NUM_TOTAL_BANKS; // ddrc_core_reg_dbg_rd_valid_rank
localparam OUT76_W  = NUM_TOTAL_BANKS; // ddrc_core_reg_dbg_rd_page_hit_rank
localparam OUT77_W  = NUM_TOTAL_BANKS; // ddrc_core_reg_dbg_rd_pri_rank
localparam OUT78_W  = NUM_TOTAL_BANKS; // ddrc_core_reg_dbg_wr_valid_rank
localparam OUT79_W  = NUM_TOTAL_BANKS; // ddrc_core_reg_dbg_wr_page_hit_rank
localparam OUT80_W  = 8; // ddrc_core_reg_dbg_wr_cam_7_0_valid
localparam OUT81_W  = 8; // ddrc_core_reg_dbg_rd_cam_7_0_valid
localparam OUT82_W  = 8; // ddrc_core_reg_dbg_wr_cam_15_8_valid
localparam OUT83_W  = 8; // ddrc_core_reg_dbg_rd_cam_15_8_valid
localparam OUT84_W  = 8; // ddrc_core_reg_dbg_wr_cam_23_16_valid
localparam OUT85_W  = 8; // ddrc_core_reg_dbg_rd_cam_23_16_valid
localparam OUT86_W  = 8; // ddrc_core_reg_dbg_wr_cam_31_24_valid
localparam OUT87_W  = 8; // ddrc_core_reg_dbg_rd_cam_31_24_valid
localparam OUT88_W  = 8; // ddrc_core_reg_dbg_wr_cam_39_32_valid
localparam OUT89_W  = 8; // ddrc_core_reg_dbg_rd_cam_39_32_valid
localparam OUT90_W  = 8; // ddrc_core_reg_dbg_wr_cam_47_40_valid
localparam OUT91_W  = 8; // ddrc_core_reg_dbg_rd_cam_47_40_valid
localparam OUT92_W  = 8; // ddrc_core_reg_dbg_wr_cam_55_48_valid
localparam OUT93_W  = 8; // ddrc_core_reg_dbg_rd_cam_55_48_valid
localparam OUT94_W  = 8; // ddrc_core_reg_dbg_wr_cam_63_56_valid
localparam OUT95_W  = 8; // ddrc_core_reg_dbg_rd_cam_63_56_valid
localparam OUT96_W  = `MEMC_FREQ_RATIO*BG_BITS_DUP; // dfi_bg
localparam OUT97_W  = `MEMC_FREQ_RATIO; // dfi_act_n
localparam OUT98_W  = `MEMC_FREQ_RATIO*CID_WIDTH_DUP; // dfi_cid
localparam OUT99_W  = $bits(dfi_address_s); // dfi_address
localparam OUT100_W = `MEMC_FREQ_RATIO*BANK_BITS; // dfi_bank
localparam OUT101_W = `MEMC_FREQ_RATIO; // dfi_cas_n
localparam OUT102_W = `MEMC_FREQ_RATIO; // dfi_ras_n
localparam OUT103_W = `MEMC_FREQ_RATIO; // dfi_we_n
localparam OUT104_W = `MEMC_FREQ_RATIO*NUM_RANKS; // dfi_cke
localparam OUT105_W = `MEMC_FREQ_RATIO*NUM_RANKS; // dfi_cs
localparam OUT106_W = `MEMC_FREQ_RATIO*NUM_RANKS; // dfi_odt
localparam OUT107_W = `UMCTL2_RESET_WIDTH; // dfi_reset_n
localparam OUT108_W = `MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES; // dfi_wrdata_cs
localparam OUT109_W = `MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES; // dfi_rddata_cs
localparam OUT110_W = 1; // dfi_ctrlupd_req
localparam OUT111_W = NUM_PHY_DRAM_CLKS; // dfi_dram_clk_disable
localparam OUT112_W = `MEMC_FREQ_RATIO*PARITY_IN_WIDTH; // dfi_parity_in
localparam OUT113_W = 1; // dfi_init_start
localparam OUT114_W = 2; // dfi_freq_fsp
localparam OUT115_W = 5; // dfi_frequency
localparam OUT116_W = 1; // dfi_geardown_en
localparam OUT117_W = 1; // dfi_reset_n_ref
localparam OUT118_W = 1; // init_mr_done_out
localparam OUT119_W = 1; // ddrc_reg_capar_err_intr
localparam OUT120_W = CAPAR_ERR_CNT_WIDTH; // ddrc_reg_capar_err_cnt
localparam OUT121_W = 1; // ddrc_reg_capar_err_max_reached_intr
localparam OUT122_W = 1; // ddrc_reg_capar_fatl_err_intr
localparam OUT123_W = WR_CRC_ERR_CNT_WIDTH; // ddrc_reg_wr_crc_err_cnt
localparam OUT124_W = 1; // ddrc_reg_wr_crc_err_intr
localparam OUT125_W = 1; // ddrc_reg_wr_crc_err_max_reached_intr
localparam OUT126_W = RETRY_FIFO_FILL_LEVEL_WIDTH; // ddrc_reg_retry_fifo_fill_level
localparam OUT127_W = RETRY_STAT_WIDTH; // ddrc_reg_retry_stat
localparam OUT128_W = 1; // retryram_din
localparam OUT129_W = 1; // retryram_waddr
localparam OUT130_W = 1; // retryram_raddr
localparam OUT131_W = 1; // retryram_re
localparam OUT132_W = 1; // retryram_we
localparam OUT133_W = 1; // retryram_mask
localparam OUT134_W = NUM_LRANKS; // ddrc_reg_rank_refresh_busy
localparam OUT135_W = 1; // ddrc_reg_ctrlupd_busy
localparam OUT136_W = 1; // ddrc_reg_capar_poison_complete
localparam OUT137_W = 1; // dbg_dfi_parity_poison
localparam OUT138_W = RD_CAM_ADDR_WIDTH+1; // ddrc_reg_dbg_hpr_q_depth
localparam OUT139_W = RD_CAM_ADDR_WIDTH+1; // ddrc_reg_dbg_lpr_q_depth
localparam OUT140_W = WR_CAM_ADDR_WIDTH+1; // ddrc_reg_dbg_w_q_depth
localparam OUT141_W = 1; // ddrc_reg_dbg_stall
localparam OUT142_W = 1; // ddrc_reg_dbg_stall_rd
localparam OUT143_W = 1; // ddrc_reg_dbg_stall_wr
localparam OUT144_W = 1; // ddrc_reg_selfref_cam_not_empty
localparam OUT145_W = 3; // ddrc_reg_selfref_state
localparam OUT146_W = 3; // ddrc_reg_operating_mode
localparam OUT147_W = SELFREF_TYPE_WIDTH; // ddrc_reg_selfref_type
localparam OUT148_W = 1; // ddrc_reg_wr_q_empty
localparam OUT149_W = 1; // ddrc_reg_rd_q_empty
localparam OUT150_W = 1; // ddrc_reg_wr_data_pipeline_empty
localparam OUT151_W = 1; // ddrc_reg_rd_data_pipeline_empty
localparam OUT152_W = 1; // ddrc_reg_zq_calib_short_busy
localparam OUT153_W = BANK_BITS*NUM_RANKS; // hif_refresh_req_bank
localparam OUT154_W = NUM_RANKS; // hif_refresh_req
localparam OUT155_W = 6*NUM_RANKS; // hif_refresh_req_cnt
localparam OUT156_W = 3; // hif_refresh_req_derate
localparam OUT157_W = NUM_RANKS; // hif_refresh_active
localparam OUT158_W = 1; // dfi_phyupd_ack
localparam OUT159_W = 1; // dfi_phymstr_ack
localparam OUT160_W = 1; // dfi_lp_ctrl_req
localparam OUT161_W = DFI_LP_WAKEUP_PD_WIDTH; // dfi_lp_ctrl_wakeup
localparam OUT162_W = 1; // hwffc_target_freq_en
localparam OUT163_W = TARGET_FREQUENCY_WIDTH; // hwffc_target_freq
localparam OUT164_W = TARGET_FREQUENCY_WIDTH; // hwffc_target_freq_init
localparam OUT165_W = 1; // ddrc_reg_hwffc_in_progress
localparam OUT166_W = TARGET_FREQUENCY_WIDTH; // ddrc_reg_current_frequency
localparam OUT167_W = 1; // ddrc_reg_current_fsp
localparam OUT168_W = 1; // ddrc_reg_current_vrcg
localparam OUT169_W = 1; // ddrc_reg_hwffc_operating_mode
localparam OUT170_W = 1; // ddrc_xpi_port_disable_req
localparam OUT171_W = 1; // ddrc_xpi_clock_required
localparam OUT172_W = 1; // hwffc_hif_wd_stall
localparam OUT173_W = 1; // hwffc_i_reg_ddrc_dis_auto_zq
localparam OUT174_W = 1; // o_ih_cpfdpif.ih_mr_ie_blk_wr_end
localparam OUT175_W = IE_PW_BITS; // ih_mr_ie_pw
localparam OUT176_W = BRT_BITS; // o_ih_cpfdpif.ih_rd_ie_brt
localparam OUT177_W = 1; // o_ih_cpfdpif.ih_rd_ie_rd_cnt_inc
localparam OUT178_W = 1; // o_ih_cpfdpif.ih_rd_ie_blk_rd_end
localparam OUT179_W = 1; // o_ih_cpfdpif.ih_mr_ie_wr_cnt_inc
localparam OUT180_W = BWT_BITS; // o_ih_cpfdpif.ih_mr_ie_bwt
localparam OUT181_W = BRT_BITS; // o_ih_cpfdpif.ih_mr_ie_brt
localparam OUT182_W = 1; // o_ih_cpfdpif.ih_mr_ie_brt_vld
localparam OUT183_W = BT_BITS; // o_te_cpfdpif.te_mr_ie_bt
localparam OUT184_W = IE_WR_TYPE_BITS; // o_te_cpfdpif.te_mr_ie_wr_type
localparam OUT185_W = IE_BURST_NUM_BITS; // o_te_cpfdpif.te_mr_ie_blk_burst_num
localparam OUT186_W = BT_BITS; // o_pi_ddrc_cpedpif.pi_rt_ie_bt
localparam OUT187_W = IE_RD_TYPE_BITS; // o_pi_ddrc_cpedpif.pi_rt_ie_rd_type
localparam OUT188_W = IE_BURST_NUM_BITS; // o_pi_ddrc_cpedpif.pi_rt_ie_blk_burst_num
localparam OUT189_W = BWT_BITS; // o_ih_cpfdpif.ih_mr_lkp_bwt
localparam OUT190_W = 1; // o_ih_cpfdpif.ih_mr_lkp_bwt_vld
localparam OUT191_W = BRT_BITS; // o_ih_cpfdpif.ih_mr_lkp_brt
localparam OUT192_W = 1; // o_ih_cpfdpif.ih_mr_lkp_brt_vld
localparam OUT193_W = BRT_BITS; // o_ih_cpfdpif.ih_rd_lkp_brt
localparam OUT194_W = 1; // ih_rd_lkp_brt_vld
localparam OUT195_W = BWT_BITS; // o_ih_cpfdpif.ih_rd_lkp_bwt
localparam OUT196_W = 1; // o_ih_cpfdpif.ih_rd_lkp_bwt_vld
localparam OUT197_W = 1; // o_te_cpfdpif.te_mr_eccap
localparam OUT198_W = 1; // o_pi_ddrc_cpedpif.pi_rt_eccap
localparam OUT199_W = `MEMC_DCERRBITS; // o_ih_cpfdpif.ih_wu_cerr
localparam OUT200_W = 1; // o_pi_ddrc_cpedpif.pi_rt_rd_mrr
localparam OUT201_W = 1; // o_pi_ddrc_cpedpif.pi_rt_rd_mrr_ext
localparam OUT202_W = 1; // o_pi_ddrc_cpedpif.pi_ph_dfi_rddata_en
localparam OUT203_W = 1; // o_ih_cpfdpif.ih_wu_wr_valid
localparam OUT204_W = 1; // o_ih_cpfdpif.ih_wu_wr_valid_addr_err
localparam OUT205_W = 1; // ih_te_rd_valid
localparam OUT206_W = 1; // ih_te_wr_valid
localparam OUT207_W = RMW_TYPE_BITS; // o_ih_cpfdpif.ih_wu_rmw_type
localparam OUT208_W = WR_CAM_ADDR_WIDTH; // o_ih_cpfdpif.ih_wu_wr_entry
localparam OUT209_W = WORD_BITS; // o_ih_cpfdpif.ih_wu_critical_word
localparam OUT210_W = 1; // pi_gs_geardown_mode_on
localparam OUT211_W = CMD_LEN_BITS; // o_pi_ddrc_cpedpif.pi_rt_rd_partial
localparam OUT212_W = 1; // o_pi_ddrc_cpedpif.pi_rt_rd_vld
localparam OUT213_W = CORE_TAG_WIDTH; // o_pi_ddrc_cpedpif.pi_rt_rd_tag
localparam OUT214_W = 1; // o_pi_ddrc_cpedpif.pi_rt_rd_addr_err
localparam OUT215_W = WR_CAM_ADDR_WIDTH; // o_pi_ddrc_cpedpif.pi_rt_wr_ram_addr
localparam OUT216_W = CMD_RMW_BITS; // o_pi_ddrc_cpedpif.pi_rt_rmwcmd
localparam OUT217_W = RMW_TYPE_BITS; // o_pi_ddrc_cpedpif.pi_rt_rmwtype
localparam OUT218_W = RANKBANK_BITS_FULL; // o_pi_ddrc_cpedpif.pi_rt_rankbank_num
localparam OUT219_W = PAGE_BITS; // o_pi_ddrc_cpedpif.pi_rt_page_num
localparam OUT220_W = BLK_BITS; // o_pi_ddrc_cpedpif.pi_rt_block_num
localparam OUT221_W = WORD_BITS; // o_pi_ddrc_cpedpif.pi_rt_critical_word
localparam OUT222_W = 1; // te_yy_wr_combine
localparam OUT223_W = 1; // ts_pi_mwr
localparam OUT224_W = PARTIAL_WR_BITS; // te_pi_wr_word_valid
localparam OUT225_W = 3; // gs_pi_rdwr_bc_sel
localparam OUT226_W = PARTIAL_WR_BITS_LOG2; // gs_pi_rdwr_ram_raddr_lsb_first
localparam OUT227_W = PW_WORD_CNT_WD_MAX; // gs_pi_rdwr_pw_num_beats_m1
localparam OUT228_W = WR_CAM_ADDR_WIDTH_IE; // o_te_cpfdpif.te_mr_wr_ram_addr
localparam OUT229_W = WR_CAM_ADDR_WIDTH; // o_te_cpfdpif.te_wu_entry_num
localparam OUT230_W = 1; // o_te_cpfdpif.te_wu_wr_retry
localparam OUT231_W = 1; // o_gs_ddrc_cpedpif.gs_mr_write
localparam OUT232_W = 1; // o_gs_ddrc_cpedpif.gs_mr_load_mode_pda
localparam OUT233_W = 2; // o_gs_ddrc_cpedpif.gs_mr_pda_data_sel
localparam OUT234_W = 1; // pda_mode
localparam OUT235_W = 1; // pda_mode_pre
localparam OUT236_W = MAX_CMD_NUM*NUM_RANKS; // gs_pi_cs_n
localparam OUT237_W = 1; // retry_fifo_empty
localparam OUT238_W = 1; // retry_rt_rdatavld_gate_en
localparam OUT239_W = 1; // retry_rt_fifo_init_n
localparam OUT240_W = 1; // retry_rt_fatl_err_pulse
localparam OUT241_W = 1; // retry_rt_now_sw_intervention
localparam OUT242_W = 8; // retry_rt_rd_timeout_value
localparam OUT243_W = 1; // retry_dfi_sel
localparam OUT244_W = PHY_MASK_WIDTH; // retry_phy_dm
localparam OUT245_W = PHY_DATA_WIDTH; // retry_phy_wdata
localparam OUT246_W = 1; // retry_phy_wdata_vld_early
localparam OUT247_W = 1; // retry_dfi_rddata_en
localparam OUT248_W = NUM_RANKS; // reg_ddrc_active_ranks_int
localparam OUT249_W = 1; // gs_pi_data_pipeline_empty
localparam OUT250_W = 1; // mrr_op_on
localparam OUT251_W = 1; // pi_gs_mpr_mode
localparam OUT252_W = 1; // ih_busy
localparam OUT253_W = NUM_LRANKS; // reg_ddrc_ext_rank_refresh
localparam OUT254_W = 1; // pi_gs_dll_off_mode
localparam OUT255_W = 3; // reg_ddrc_fgr_mode_gated
localparam OUT256_W = 1; // ddrc_phy_cal_dl_enable
localparam OUT257_W = 1; // gs_pi_op_is_exit_selfref
localparam OUT258_W = 1; // o_te_cpfdpif.te_wu_ie_flowctrl_req
localparam OUT259_W = 1; // ih_ie_busy
localparam OUT260_W = 2; // hif_wrecc_credit
localparam OUT261_W = WR_CAM_ADDR_WIDTH+1; // ddrc_reg_dbg_wrecc_q_depth
localparam OUT262_W = WR_CAM_ADDR_WIDTH+1; // ddrc_core_reg_dbg_wrecc_q_depth
localparam OUT263_W = 1; // perf_ie_blk_hazard
localparam OUT264_W = `MEMC_FREQ_RATIO; // o_pi_cpedpif.pi_ph_dfi_wrdata_en
localparam OUT265_W = `MEMC_FREQ_RATIO; // retry_dfi_wrdata_en
localparam OUT266_W = 1; // perf_op_is_crit_ref
localparam OUT267_W = 1; // perf_op_is_spec_ref
localparam OUT268_W = 1; // core_derate_temp_limit_intr
localparam OUT269_W = NO_OF_BWT; // o_ih_cpfdpif.ih_mr_ie_wr_cnt_dec_vct
localparam OUT270_W = 2; // dfi_freq_ratio
localparam OUT271_W = 1; // perf_visible_window_limit_reached_wr
localparam OUT272_W = 1; // perf_visible_window_limit_reached_rd
localparam OUT273_W = `MEMC_FREQ_RATIO*NUM_RANKS;  // dfi_wck_cs
localparam OUT274_W = `MEMC_FREQ_RATIO;   // dfi_wck_en
localparam OUT275_W = 2*`MEMC_FREQ_RATIO; // dfi_wck_toggle
localparam OUT276_W = 4; // o_pi_cpedpif.pi_ph_snoop_en
localparam OUT277_W = 1; // o_pi_cpedpif.pi_rt_rd_mrr_snoop
localparam OUT278_W = 3; //dqsosc_state
localparam OUT279_W = NUM_RANKS; // dqsosc_per_rank_stat
localparam OUT280_W = 1;                  // o_pi_pas_cpedpif.pi_rd_vld
localparam OUT281_W = CMD_LEN_BITS;       // o_pi_pas_cpedpif.pi_rd_partial
localparam OUT282_W = CORE_TAG_WIDTH;     // o_pi_pas_cpedpif.pi_rd_tag
localparam OUT283_W = 1;                  // o_pi_pas_cpedpif.pi_rd_addr_err
localparam OUT284_W = RMW_TYPE_BITS;      // o_pi_pas_cpedpif.pi_rd_rmw_type
localparam OUT285_W = WR_CAM_ADDR_WIDTH;  // o_pi_pas_cpedpif.pi_rd_wr_ram_addr
localparam OUT286_W = PAGE_BITS;          // o_pi_pas_cpedpif.pi_rd_page
localparam OUT287_W = BLK_BITS;           // o_pi_pas_cpedpif.pi_rd_blk
localparam OUT288_W = WORD_BITS;          // o_pi_pas_cpedpif.pi_rd_critical_word
localparam OUT289_W = RANKBANK_BITS_FULL; // o_pi_pas_cpedpif.pi_rd_rankbank
localparam OUT290_W = 1;                  // o_pi_pas_cpedpif.pi_wr_vld_nxt
localparam OUT291_W = 2;                  // o_pi_pas_cpedpif.pi_wr_ph_nxt
localparam OUT292_W = NUM_RANKS;          // o_pi_pas_cpedpif.pi_wr_cs_nxt
localparam OUT293_W = 1;                  // o_pi_pas_cpedpif.pi_rd_vld_nxt
localparam OUT294_W = 2;                  // o_pi_pas_cpedpif.pi_rd_ph_nxt
localparam OUT295_W = `MEMC_FREQ_RATIO;   // o_pi_pas_cpedpif.pi_dfi_wrdata_en
localparam OUT296_W = `MEMC_FREQ_RATIO;   // o_pi_pas_cpedpif.pi_dfi_rddata_en
localparam OUT297_W = 1;                  // o_pi_pas_cpedpif.pi_rd_mrr_ext
localparam OUT298_W = 1;                  // o_pi_pas_cpedpif.pi_rd_mrr_snoop
localparam OUT299_W = 4;                  // o_pi_pas_cpedpif.pi_phy_snoop_en
localparam OUT300_W = 1;                  // ddrc_reg_cmd_err
localparam OUT301_W = 1;                  // ddrc_reg_cmd_done
localparam OUT302_W = CMD_MRR_DATA_WIDTH; // ddrc_reg_cmd_mrr_data
localparam OUT303_W = 1; // perf_write_combine_noecc,
localparam OUT304_W = 1; // perf_write_combine_wrecc,
localparam OUT305_W = 1;                  // ddrc_reg_ctrlupd_err_intr
localparam OUT306_W = 1;                  // ddrc_reg_mrr_data_vld
localparam OUT307_W = DU_CFGBUF_RDATA_WIDTH;    // ddrc_reg_du_cfgbuf_rdata,
localparam OUT308_W = DU_CMDBUF_RDATA_WIDTH;    // ddrc_reg_du_cmdbuf_rdata,
localparam OUT309_W = LP_CMDBUF_RDATA_WIDTH;    // ddrc_reg_lp_cmdbuf_rdata,
localparam OUT310_W = 1;                        // ddrc_reg_du_cur_blk_set
localparam OUT311_W = DU_CUR_BLK_INDEX_WIDTH;   // ddrc_reg_du_cur_blk_index
localparam OUT312_W = DU_CUR_BLK_ADDR_WIDTH;    // ddrc_reg_du_cur_blk_addr
localparam OUT313_W = DU_CUR_BLK_UCODE_WIDTH;   // ddrc_reg_du_cur_blk_addr
localparam OUT314_W = DU_MAIN_FSM_STATE_WIDTH;  // ddrc_reg_du_main_fsm_state
localparam OUT315_W = 1;                        // ddrc_reg_lccmd_err_intr
localparam OUT316_W = 1;                        // ddrc_reg_ducmd_err_intr
localparam OUT317_W = 1;                        // ddrc_reg_swcmd_err_intr
localparam OUT318_W = SWCMD_ERR_STS_WIDTH;      // ddrc_reg_swcmd_err_sts
localparam OUT319_W = DUCMD_ERR_STS_WIDTH;      // ddrc_reg_ducmd_err_sts
localparam OUT320_W = LCCMD_ERR_STS_WIDTH;      // ddrc_reg_lccmd_err_sts
localparam OUT321_W = 1; //ddrc_reg_dfi0_ctrlmsg_req_busy
localparam OUT322_W = 1; //ddrc_reg_dfi0_ctrlmsg_resp_tout
localparam OUT323_W = 1; //dfi0_ctrlmsg_req
localparam OUT324_W = 8; //dfi0_ctrlmsg
localparam OUT325_W = 16; //dfi0_ctrlmsg_data
localparam OUT326_W = REFRESH_RATE_RANK_WIDTH; // ddrc_reg_refresh_rate_rank0
localparam OUT327_W = REFRESH_RATE_RANK_WIDTH; // ddrc_reg_refresh_rate_rank1
localparam OUT328_W = REFRESH_RATE_RANK_WIDTH; // ddrc_reg_refresh_rate_rank2
localparam OUT329_W = REFRESH_RATE_RANK_WIDTH; // ddrc_reg_refresh_rate_rank3
localparam OUT330_W = POWERDOWN_STATE_WIDTH; // ddrc_reg_powerdown_state
localparam OUT331_W = DBG_MR4_BYTE_WIDTH;   //ddrc_reg_dbg_mr4_byte0
localparam OUT332_W = DBG_MR4_BYTE_WIDTH;   //ddrc_reg_dbg_mr4_byte1
localparam OUT333_W = DBG_MR4_BYTE_WIDTH;   //ddrc_reg_dbg_mr4_byte2
localparam OUT334_W = DBG_MR4_BYTE_WIDTH;   //ddrc_reg_dbg_mr4_byte3
localparam OUT335_W = PRANK_MODE_WIDTH;  //ddrc_reg_pasds_prank3_mode
localparam OUT336_W = PRANK_MODE_WIDTH;  //ddrc_reg_pasds_prank2_mode
localparam OUT337_W = PRANK_MODE_WIDTH;  //ddrc_reg_pasds_prank1_mode
localparam OUT338_W = PRANK_MODE_WIDTH;  //ddrc_reg_pasds_prank0_mode
localparam OUT339_W = DBG_STAT3_WIDTH;    //ddrc_reg_pasds_debug_status3
localparam OUT340_W = DBG_STAT2_WIDTH;    //ddrc_reg_pasds_debug_status2
localparam OUT341_W = DBG_STAT1_WIDTH;    //ddrc_reg_pasds_debug_status1
localparam OUT342_W = DBG_STAT0_WIDTH;    //ddrc_reg_pasds_debug_status0
localparam OUT343_W = CMD_RSLT_WIDTH;    //ddrc_reg_cmd_rslt
localparam OUT344_W = 1;                 //rank_idle_state_o
localparam OUT345_W = 1;                 //rank_selfref_state_o
localparam OUT346_W = 1;                 //selfref_idle_entry_o
localparam OUT347_W = 1;                 //selfref_sw_entry_o
localparam OUT348_W = 1;                 //selfref_hw_entry_o
localparam OUT349_W = 1;                 //selfref_sw_o
localparam OUT350_W = 1;                 //selfref_idle_exit_o
localparam OUT351_W = 1;                 //selfref_sw_exit_o
localparam OUT352_W = 4;                 //channel_message_o
localparam OUT353_W = 1;                 //rank_selfref_operating_mode_o
localparam OUT354_W = 1;                 //rank_selfref_swhw_state_o
localparam OUT355_W = 1;                 //rank_selfref_tctrl_delay_ack_o
localparam OUT356_W = 1;                 //dfi_lp_selfref_tlp_resp_ack_o
localparam OUT357_W = 1;                 //hw_lp_exit_idle_o
localparam OUT358_W = 1;                 //hw_lp_selfref_hw_o
localparam OUT359_W = 1;                 // dfi_data_lp_req
localparam OUT360_W = DFI_LP_WAKEUP_PD_WIDTH; // dfi_lp_data_wakeup
localparam OUT361_W = 1;                 // perf_op_is_cas
localparam OUT362_W = 1;                 // perf_op_is_cas_ws
localparam OUT363_W = 1;                 // perf_op_is_enter_dsm
localparam OUT364_W = 1;                 // perf_op_is_dqsosc_mpc
localparam OUT365_W = 1;                 // perf_op_is_dqsosc_mrr
localparam OUT366_W = 1;                 // perf_op_is_tcr_mrr
localparam OUT367_W = 1;                 // perf_op_is_zqstart
localparam OUT368_W = 1;                 // perf_op_is_zqlatch
localparam OUT369_W = 1;                 // ddrc_reg_2n_mode
localparam OUT370_W = POWERDOWN_ONGOING_WIDTH;           // ddrc_reg_powerdown_ongoing,
localparam OUT371_W = SELFREF_ONGOING_WIDTH;             // ddrc_reg_selfref_ongoing,
localparam OUT372_W = 1;                                 // sw_wr_data_valid_w
localparam OUT373_W = CORE_DATA_WIDTH;                   // sw_wr_data_w
localparam OUT374_W = CORE_DATA_WIDTH/8;                 // sw_wr_data_mask_w
localparam OUT375_W = 1;                                 // ci_manual_wr_mode_w
localparam OUT376_W = 1;                                 // ci_manual_rd_mode_w
localparam OUT377_W = CORE_ECC_WIDTH_DUP;                // sw_wr_ecc_w
localparam OUT378_W = CORE_ECC_MASK_WIDTH_DUP;           // sw_wr_ecc_mask_w
localparam OUT379_W = RD_DATA_DQ0_WIDTH;                 // ddrc_reg_rd_data_dq0
localparam OUT380_W = RD_DATA_DQ1_WIDTH;                 // ddrc_reg_rd_data_dq1
localparam OUT381_W = 1;                                 // ddrc_reg_rd_data_vld
localparam OUT382_W = 1;                                 // dch_sync_mode_o
localparam OUT383_W = BSM_BITS+1;                        // ddrc_reg_max_num_alloc_bsm
localparam OUT384_W = RD_CAM_ADDR_WIDTH+2;               // ddrc_reg_max_num_unalloc_entries
localparam OUT385_W = GLB_BLK_EVENTS_ONGOING_WIDTH;      // ddrc_reg_glb_blk_events_ongoing
localparam OUT386_W = RANK_BLK_EVENTS_ONGOING_WIDTH;     // ddrc_reg_rank_blk_events_ongoing
localparam OUT387_W = ADDRMAP_LUT_RDATA1_WIDTH;          // ddrc_reg_addrmap_lut_rdata1
localparam OUT388_W = ADDRMAP_LUT_RDATA0_WIDTH;          // ddrc_reg_addrmap_lut_rdata0
localparam OUT389_W = ADDRMAP_RANK_VALID_WIDTH;          // ddrc_reg_addrmap_rank_valid
localparam OUT390_W = MPSM_STATE_WIDTH;                  // ddrc_reg_mpsm_state
localparam OUT391_W = HIF_ADDR_WIDTH;                    // dfi_hif_cmd_addr
localparam OUT392_W = `DDRCTL_DFI_HIF_CMD_WDATA_PTR_RANGE; //dfi_hif_cmd_wdata_ptr
localparam OUT393_W = 1;                                 // ih_wu_is_retry_wr
localparam OUT394_W = PW_WORD_CNT_WD_MAX;                // ih_wu_wr_pw_num_beats_m1
localparam OUT395_W = 1;                                 // dbg_dfi_in_retry
localparam OUT396_W = 1;
localparam OUT397_W = DBG_RANK_CTRL_MC_CODE_0_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_code_0
localparam OUT398_W = DBG_RANK_CTRL_MC_ADDR_0_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_addr_0
localparam OUT399_W = DBG_RANK_CTRL_STATE_RSM_0_WIDTH;     // ddrc_reg_dbg_rank_ctrl_state_rsm_0
localparam OUT400_W = DBG_MCEU_CTRL_STATE_MCEU_0_WIDTH;    // ddrc_reg_dbg_mceu_ctrl_state_mceu_0
localparam OUT401_W = DBG_SCEU_CTRL_STATE_SCEU_0_WIDTH;    // ddrc_reg_dbg_sceu_ctrl_state_sceu_0
localparam OUT402_W = DBG_RANK_CTRL_MC_CODE_1_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_code_1
localparam OUT403_W = DBG_RANK_CTRL_MC_ADDR_1_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_addr_1
localparam OUT404_W = DBG_RANK_CTRL_STATE_RSM_1_WIDTH;     // ddrc_reg_dbg_rank_ctrl_state_rsm_1
localparam OUT405_W = DBG_MCEU_CTRL_STATE_MCEU_1_WIDTH;    // ddrc_reg_dbg_mceu_ctrl_state_mceu_1
localparam OUT406_W = DBG_SCEU_CTRL_STATE_SCEU_1_WIDTH;    // ddrc_reg_dbg_sceu_ctrl_state_sceu_1
localparam OUT407_W = DBG_RANK_CTRL_MC_CODE_2_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_code_2
localparam OUT408_W = DBG_RANK_CTRL_MC_ADDR_2_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_addr_2
localparam OUT409_W = DBG_RANK_CTRL_STATE_RSM_2_WIDTH;     // ddrc_reg_dbg_rank_ctrl_state_rsm_2
localparam OUT410_W = DBG_MCEU_CTRL_STATE_MCEU_2_WIDTH;    // ddrc_reg_dbg_mceu_ctrl_state_mceu_2
localparam OUT411_W = DBG_SCEU_CTRL_STATE_SCEU_2_WIDTH;    // ddrc_reg_dbg_sceu_ctrl_state_sceu_2
localparam OUT412_W = DBG_RANK_CTRL_MC_CODE_3_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_code_3
localparam OUT413_W = DBG_RANK_CTRL_MC_ADDR_3_WIDTH;       // ddrc_reg_dbg_rank_ctrl_mc_addr_3
localparam OUT414_W = DBG_RANK_CTRL_STATE_RSM_3_WIDTH;     // ddrc_reg_dbg_rank_ctrl_state_rsm_3
localparam OUT415_W = DBG_MCEU_CTRL_STATE_MCEU_3_WIDTH;    // ddrc_reg_dbg_mceu_ctrl_state_mceu_3
localparam OUT416_W = DBG_SCEU_CTRL_STATE_SCEU_3_WIDTH;    // ddrc_reg_dbg_sceu_ctrl_state_sceu_3
localparam OUT417_W = DBG_HW_LP_STATE_HSM_WIDTH;           // ddrc_reg_dbg_hw_lp_state_hsm
localparam OUT418_W = 1;                                   // ddrc_reg_dbg_dfi_lp_ctrl_ack
localparam OUT419_W = 1;                                   // ddrc_reg_dbg_dfi_lp_data_ack
localparam OUT420_W = DBG_DFI_LP_STATE_DSM_WIDTH;          // ddrc_reg_dbg_dfi_lp_state_dsm
localparam OUT421_W = DU_MCEU_FSM_STATE_WIDTH;             // ddrc_reg_du_mceu_fsm_state
localparam OUT422_W = DU_SCEU_FSM_STATE_WIDTH;             // ddrc_reg_du_sceu_fsm_state
localparam OUT423_W = 1;                                   // ddrc_reg_dfi_lp_state
localparam OUT424_W = NUM_LRANKS;                          // ext_rank_refresh_busy
localparam OUT425_W = 1;                                   // ddrc_reg_rfm_alert_intr
localparam OUT426_W = RFM_CMD_LOG_WIDTH;                   // ddrc_reg_rfm_cmd_log
localparam OUT427_W = 3;                                   // gs_wr_bc_sel
localparam OUT428_W = PARTIAL_WR_BITS_LOG2;                // gs_mr_ram_raddr_lsb_first
localparam OUT429_W = PW_WORD_CNT_WD_MAX;                  // gs_mr_pw_num_beats_m1
localparam OUT430_W = 1;                                   // ddrc_reg_caparcmd_err_intr
localparam OUT431_W = CAPARCMD_ERR_STS_WIDTH;              // ddrc_reg_caparcmd_err_sts
localparam OUT432_W = 1;                                   // ddrc_reg_wr_crc_retry_limit_intr 
localparam OUT433_W = 1;                                   // ddrc_reg_rd_retry_limit_intr 
localparam OUT434_W = 1;                                   // ddrc_reg_rd_crc_retry_limit_reached
localparam OUT435_W = 1;                                   // ddrc_reg_rd_ue_retry_limit_reached
localparam OUT436_W = 1;                                   // dbg_wr_crc_retry_pulse
localparam OUT437_W = 1;                                   // dbg_rd_crc_retry_pulse
localparam OUT438_W = 1;                                   // dbg_rd_ue_retry_pulse
localparam OUT439_W = 1;                                   // o_pi_pas_cpedpif.pi_rd_crc_retry_limit_reach_pre
localparam OUT440_W = CAPAR_CMDBUF_RDATA_WIDTH;            // ddrc_reg_capar_cmdbuf_rdata
localparam OUT441_W = DBG_CAPAR_RETRY_MC_CODE_WIDTH;       // ddrc_reg_dbg_capar_retry_mc_code
localparam OUT442_W = DBG_CAPAR_RETRY_MC_ADDR_WIDTH;       // ddrc_reg_dbg_capar_retry_mc_addr
localparam OUT443_W = DBG_CAPAR_RETRY_STATE_CSM_WIDTH;     // ddrc_reg_dbg_capar_retry_state_csm
localparam OUT444_W = DBG_CAPAR_RETRY_STATE_MCEU_WIDTH;    // ddrc_reg_dbg_capar_retry_state_mceu
localparam OUT445_W = DBG_CAPAR_RETRY_STATE_SCEU_WIDTH;    // ddrc_reg_dbg_capar_retry_state_sceu
localparam OUT446_W = CAPAR_FATL_ERR_CODE_WIDTH;           // ddrc_reg_capar_fatl_err_code,
localparam OUT447_W = 1;                                   // ddrc_reg_capar_retry_limit_intr,
localparam OUT448_W = CMDFIFO_RD_DATA_WIDTH;               // ddrc_reg_cmdfifo_rd_data
localparam OUT449_W = 1;                                   // ddrc_reg_cmdfifo_overflow
localparam OUT450_W = CMDFIFO_RECORDED_CMD_NUM_WIDTH;      // ddrc_reg_cmdfifo_recorded_cmd_num
localparam OUT451_W = CMDFIFO_WINDOW_CMD_NUM_WIDTH;        // ddrc_reg_cmdfifo_window_cmd_num
localparam OUT452_W = 1;                                   // capar_retry_start
localparam OUT453_W = 1;                                   // capar_rd_expired
localparam OUT454_W = 1;                                   // o_pi_ddrc_cpedpif.pi_rt_rd_retry_limit_reach_pre
localparam OUT455_W = 1;                                   // capar_rddata_en
localparam OUT456_W = LRANK_BITS_DUP;                      // dbg_rd_retry_rank
localparam OUT457_W = 1;                                   // o_pi_pas_cpedpif.pi_rd_ue_retry_limit_reach_pre
localparam OUT458_W = 1;                                   // o_pi_ddrc_cpedpif.pi_rt_rd_ue_retry_limit_reach_pre
localparam OUT459_W = NUM_RANKS;                           // bsm_clk_en
localparam OUT460_W = NUM_RANKS;                           // dbg_prank_act_pd
localparam OUT461_W = NUM_RANKS;                           // dbg_prank_pre_pd
localparam OUT462_W = `DDRCTL_EAPAR_SIZE;                  // ih_wu_wr_eapar
localparam OUT463_W = 1;                                   // dbg_capar_retry_pulse
localparam OUT464_W = 1;                                   // ddrc_reg_ppr_done
localparam OUT465_W = 2;                                   // dfi_ctrlupd_type
localparam OUT466_W = 2;                                   // dfi_ctrlupd_target
localparam OUT467_W = 1;                                   // ddrc_reg_ppt2_burst_busy
localparam OUT468_W = PPT2_STATE_WIDTH;                    // ddrc_reg_ppt2_state
localparam OUT469_W = 1;                                   // perf_op_is_cas_ws_off
localparam OUT470_W = 1;                                   // perf_op_is_cas_wck_sus
localparam OUT471_W = 1;                                   // perf_op_is_rfm
localparam OUT472_W = 1;                                   // ci_wr_crc_enable_mask_n
localparam OUT473_W = 1;                                   // dbg_du_ucode_seq_ongoing
localparam OUT474_W = 1;                                   // dbg_lp_ucode_seq_ongoing
localparam OUT475_W = 1;                                   // ddrc_reg_swcmd_lock
localparam OUT476_W = 1;                                   // ddrc_reg_ducmd_lock
localparam OUT477_W = 1;                                   // ddrc_reg_lccmd_lock
localparam OUT478_W = BT_BITS;                             // o_pi_ddrc_cpedpif.pi_rd_ie_bt
localparam OUT479_W = IE_RD_TYPE_BITS;                     // o_pi_ddrc_cpedpif.pi_rd_ie_rd_type
localparam OUT480_W = IE_BURST_NUM_BITS;                   // o_pi_ddrc_cpedpif.pi_rd_ie_blk_burst_num 
localparam OUT481_W = 1;                                   // o_pi_pas_cpedpif.pi_rd_eccap = pi_rd_eccap_w
localparam OUT482_W = DBG_RAA_CNT_WIDTH;                   // ddrc_reg_dbg_raa_cnt
localparam OUT483_W = NUM_RANKS;                           // ddrc_reg_rank_raa_cnt_gt0
localparam OUT484_W = ECS_MR16_WIDTH;                      // ddrc_reg_ecs_mr16
localparam OUT485_W = ECS_MR17_WIDTH;                      // ddrc_reg_ecs_mr17
localparam OUT486_W = ECS_MR18_WIDTH;                      // ddrc_reg_ecs_mr18
localparam OUT487_W = ECS_MR19_WIDTH;                      // ddrc_reg_ecs_mr19
localparam OUT488_W = ECS_MR20_WIDTH;                      // ddrc_reg_ecs_mr20
localparam OUT489_W = HIF_KEYID_WIDTH;                     // dfi_hif_cmd_keyid
localparam OUT490_W = 1;                                   // prmw_wr_expired 
localparam OUT491_W = 1;                                   // o_pi_pas_cpedpif.pi_rd_tweak_index
localparam OUT492_W = `MEMC_HIF_ADDR_WIDTH;                // t_hif_addr
localparam OUT493_W = 1;                                   // o_ih_cpfdpif.ih_wu_wr_tweak_index
localparam OUT494_W = DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH;// ddrc_reg_derate_temp_limit_intr_sts_rank0
localparam OUT495_W = DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH;// ddrc_reg_derate_temp_limit_intr_sts_rank1
localparam OUT496_W = DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH;// ddrc_reg_derate_temp_limit_intr_sts_rank2
localparam OUT497_W = DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH;// ddrc_reg_derate_temp_limit_intr_sts_rank3
localparam OUT498_W = 1;                                    // ddrc_reg_ctrlupd_burst_busy
localparam OUT499_W = 1;                                   // ddrc_reg_dfi_error_intr
localparam OUT500_W = DFI_ERROR_INFO_WIDTH;                // ddrc_reg_dfi_error_info
localparam OUT501_W = 1;                                   // ddrc_reg_dfi_sideband_timer_err_intr
localparam OUT502_W = 1;                                   // ddrc_reg_dfi_tctrlupd_min_error
localparam OUT503_W = 1;                                   // ddrc_reg_dfi_tctrlupd_max_error
localparam OUT504_W = 1;                                   // ddrc_reg_dfi_tinit_start_error
localparam OUT505_W = 1;                                   // ddrc_reg_dfi_tinit_complete_error
localparam OUT506_W = 1;                                   // ddrc_reg_dfi_tlp_ctrl_resp_error
localparam OUT507_W = 1;                                   // ddrc_reg_dfi_tlp_data_resp_error
localparam OUT508_W = 1;                                   // ddrc_reg_dfi_tlp_ctrl_wakeup_error
localparam OUT509_W = 1;                                   // ddrc_reg_dfi_tlp_data_wakeup_error
localparam OUT510_W = $bits(hwffcmrw_if_at_hwffcmrw_op_s); // HWFFC MRW buffer register output
localparam OUT511_W = 1;                                   // dfi_snoop_running
localparam OUT512_W = HIF_KEYID_WIDTH;                     // pi_rd_keyid
localparam OUT513_W = 1;                                   // ts_pi_wr32,
localparam OUT514_W = 1;                                   // ts_pi_2nd_half,
localparam OUT515_W = 1;                                   // ts_cam_clear_en
localparam OUT516_W = 1;                                   // te_wu_wrdata_stall_req
localparam OUT517_W = 1;                                   // perf_op_is_wr16
localparam OUT518_W = 1;                                   // perf_op_is_wr32
localparam OUT519_W = 1;                                   // perf_op_is_rd16
localparam OUT520_W = 1;                                   // perf_op_is_rd32
localparam OUT521_W = 1;                                   // clk_te_en
localparam OUT522_W = 35;                                  // o_te_cpfdpif.te_mr_addr_info

//////////////////////////////////////////////////////////////////
// Offsets    
//////////////////////////////////////////////////////////////////
              
localparam OUT0_OFF = OUT0_W;
localparam OUT1_OFF = OUT0_OFF + OUT1_W;
localparam OUT2_OFF = OUT1_OFF + OUT2_W;
localparam OUT3_OFF = OUT2_OFF + OUT3_W;
localparam OUT4_OFF = OUT3_OFF + OUT4_W;
localparam OUT5_OFF = OUT4_OFF + OUT5_W;
localparam OUT6_OFF = OUT5_OFF + OUT6_W;
localparam OUT7_OFF = OUT6_OFF + OUT7_W;
localparam OUT8_OFF = OUT7_OFF + OUT8_W;
localparam OUT9_OFF = OUT8_OFF + OUT9_W;

localparam OUT10_OFF = OUT9_OFF + OUT10_W;
localparam OUT11_OFF = OUT10_OFF + OUT11_W;
localparam OUT12_OFF = OUT11_OFF + OUT12_W;
localparam OUT13_OFF = OUT12_OFF + OUT13_W;
localparam OUT14_OFF = OUT13_OFF + OUT14_W;
localparam OUT15_OFF = OUT14_OFF + OUT15_W;
localparam OUT16_OFF = OUT15_OFF + OUT16_W;
localparam OUT17_OFF = OUT16_OFF + OUT17_W;
localparam OUT18_OFF = OUT17_OFF + OUT18_W;
localparam OUT19_OFF = OUT18_OFF + OUT19_W;

localparam OUT20_OFF = OUT19_OFF + OUT20_W;
localparam OUT21_OFF = OUT20_OFF + OUT21_W;
localparam OUT22_OFF = OUT21_OFF + OUT22_W;
localparam OUT23_OFF = OUT22_OFF + OUT23_W;
localparam OUT24_OFF = OUT23_OFF + OUT24_W;
localparam OUT25_OFF = OUT24_OFF + OUT25_W;
localparam OUT26_OFF = OUT25_OFF + OUT26_W;
localparam OUT27_OFF = OUT26_OFF + OUT27_W;
localparam OUT28_OFF = OUT27_OFF + OUT28_W;
localparam OUT29_OFF = OUT28_OFF + OUT29_W;

localparam OUT30_OFF = OUT29_OFF + OUT30_W;
localparam OUT31_OFF = OUT30_OFF + OUT31_W;
localparam OUT32_OFF = OUT31_OFF + OUT32_W;
localparam OUT33_OFF = OUT32_OFF + OUT33_W;
localparam OUT34_OFF = OUT33_OFF + OUT34_W;
localparam OUT35_OFF = OUT34_OFF + OUT35_W;
localparam OUT36_OFF = OUT35_OFF + OUT36_W;
localparam OUT37_OFF = OUT36_OFF + OUT37_W;
localparam OUT38_OFF = OUT37_OFF + OUT38_W;
localparam OUT39_OFF = OUT38_OFF + OUT39_W;

localparam OUT40_OFF = OUT39_OFF + OUT40_W;
localparam OUT41_OFF = OUT40_OFF + OUT41_W;
localparam OUT42_OFF = OUT41_OFF + OUT42_W;
localparam OUT43_OFF = OUT42_OFF + OUT43_W;
localparam OUT44_OFF = OUT43_OFF + OUT44_W;
localparam OUT45_OFF = OUT44_OFF + OUT45_W;
localparam OUT46_OFF = OUT45_OFF + OUT46_W;
localparam OUT47_OFF = OUT46_OFF + OUT47_W;
localparam OUT48_OFF = OUT47_OFF + OUT48_W;
localparam OUT49_OFF = OUT48_OFF + OUT49_W;

localparam OUT50_OFF = OUT49_OFF + OUT50_W;
localparam OUT51_OFF = OUT50_OFF + OUT51_W;
localparam OUT52_OFF = OUT51_OFF + OUT52_W;
localparam OUT53_OFF = OUT52_OFF + OUT53_W;
localparam OUT54_OFF = OUT53_OFF + OUT54_W;
localparam OUT55_OFF = OUT54_OFF + OUT55_W;
localparam OUT56_OFF = OUT55_OFF + OUT56_W;
localparam OUT57_OFF = OUT56_OFF + OUT57_W;
localparam OUT58_OFF = OUT57_OFF + OUT58_W;
localparam OUT59_OFF = OUT58_OFF + OUT59_W;

localparam OUT60_OFF = OUT59_OFF + OUT60_W;
localparam OUT61_OFF = OUT60_OFF + OUT61_W;
localparam OUT62_OFF = OUT61_OFF + OUT62_W;
localparam OUT63_OFF = OUT62_OFF + OUT63_W;
localparam OUT64_OFF = OUT63_OFF + OUT64_W;
localparam OUT65_OFF = OUT64_OFF + OUT65_W;
localparam OUT66_OFF = OUT65_OFF + OUT66_W;
localparam OUT67_OFF = OUT66_OFF + OUT67_W;
localparam OUT68_OFF = OUT67_OFF + OUT68_W;
localparam OUT69_OFF = OUT68_OFF + OUT69_W;

localparam OUT70_OFF = OUT69_OFF + OUT70_W;
localparam OUT71_OFF = OUT70_OFF + OUT71_W;
localparam OUT72_OFF = OUT71_OFF + OUT72_W;
localparam OUT73_OFF = OUT72_OFF + OUT73_W;
localparam OUT74_OFF = OUT73_OFF + OUT74_W;
localparam OUT75_OFF = OUT74_OFF + OUT75_W;
localparam OUT76_OFF = OUT75_OFF + OUT76_W;
localparam OUT77_OFF = OUT76_OFF + OUT77_W;
localparam OUT78_OFF = OUT77_OFF + OUT78_W;
localparam OUT79_OFF = OUT78_OFF + OUT79_W;

localparam OUT80_OFF = OUT79_OFF + OUT80_W;
localparam OUT81_OFF = OUT80_OFF + OUT81_W;
localparam OUT82_OFF = OUT81_OFF + OUT82_W;
localparam OUT83_OFF = OUT82_OFF + OUT83_W;
localparam OUT84_OFF = OUT83_OFF + OUT84_W;
localparam OUT85_OFF = OUT84_OFF + OUT85_W;
localparam OUT86_OFF = OUT85_OFF + OUT86_W;
localparam OUT87_OFF = OUT86_OFF + OUT87_W;
localparam OUT88_OFF = OUT87_OFF + OUT88_W;
localparam OUT89_OFF = OUT88_OFF + OUT89_W;

localparam OUT90_OFF = OUT89_OFF + OUT90_W;
localparam OUT91_OFF = OUT90_OFF + OUT91_W;
localparam OUT92_OFF = OUT91_OFF + OUT92_W;
localparam OUT93_OFF = OUT92_OFF + OUT93_W;
localparam OUT94_OFF = OUT93_OFF + OUT94_W;
localparam OUT95_OFF = OUT94_OFF + OUT95_W;
localparam OUT96_OFF = OUT95_OFF + OUT96_W;
localparam OUT97_OFF = OUT96_OFF + OUT97_W;
localparam OUT98_OFF = OUT97_OFF + OUT98_W;
localparam OUT99_OFF = OUT98_OFF + OUT99_W;

localparam OUT100_OFF = OUT99_OFF + OUT100_W;
localparam OUT101_OFF = OUT100_OFF + OUT101_W;
localparam OUT102_OFF = OUT101_OFF + OUT102_W;
localparam OUT103_OFF = OUT102_OFF + OUT103_W;
localparam OUT104_OFF = OUT103_OFF + OUT104_W;
localparam OUT105_OFF = OUT104_OFF + OUT105_W;
localparam OUT106_OFF = OUT105_OFF + OUT106_W;
localparam OUT107_OFF = OUT106_OFF + OUT107_W;
localparam OUT108_OFF = OUT107_OFF + OUT108_W;
localparam OUT109_OFF = OUT108_OFF + OUT109_W;

localparam OUT110_OFF = OUT109_OFF + OUT110_W;
localparam OUT111_OFF = OUT110_OFF + OUT111_W;
localparam OUT112_OFF = OUT111_OFF + OUT112_W;
localparam OUT113_OFF = OUT112_OFF + OUT113_W;
localparam OUT114_OFF = OUT113_OFF + OUT114_W;
localparam OUT115_OFF = OUT114_OFF + OUT115_W;
localparam OUT116_OFF = OUT115_OFF + OUT116_W;
localparam OUT117_OFF = OUT116_OFF + OUT117_W;
localparam OUT118_OFF = OUT117_OFF + OUT118_W;
localparam OUT119_OFF = OUT118_OFF + OUT119_W;

localparam OUT120_OFF = OUT119_OFF + OUT120_W;
localparam OUT121_OFF = OUT120_OFF + OUT121_W;
localparam OUT122_OFF = OUT121_OFF + OUT122_W;
localparam OUT123_OFF = OUT122_OFF + OUT123_W;
localparam OUT124_OFF = OUT123_OFF + OUT124_W;
localparam OUT125_OFF = OUT124_OFF + OUT125_W;
localparam OUT126_OFF = OUT125_OFF + OUT126_W;
localparam OUT127_OFF = OUT126_OFF + OUT127_W;
localparam OUT128_OFF = OUT127_OFF + OUT128_W;
localparam OUT129_OFF = OUT128_OFF + OUT129_W;

localparam OUT130_OFF = OUT129_OFF + OUT130_W;
localparam OUT131_OFF = OUT130_OFF + OUT131_W;
localparam OUT132_OFF = OUT131_OFF + OUT132_W;
localparam OUT133_OFF = OUT132_OFF + OUT133_W;
localparam OUT134_OFF = OUT133_OFF + OUT134_W;
localparam OUT135_OFF = OUT134_OFF + OUT135_W;
localparam OUT136_OFF = OUT135_OFF + OUT136_W;
localparam OUT137_OFF = OUT136_OFF + OUT137_W;
localparam OUT138_OFF = OUT137_OFF + OUT138_W;
localparam OUT139_OFF = OUT138_OFF + OUT139_W;

localparam OUT140_OFF = OUT139_OFF + OUT140_W;
localparam OUT141_OFF = OUT140_OFF + OUT141_W;
localparam OUT142_OFF = OUT141_OFF + OUT142_W;
localparam OUT143_OFF = OUT142_OFF + OUT143_W;
localparam OUT144_OFF = OUT143_OFF + OUT144_W;
localparam OUT145_OFF = OUT144_OFF + OUT145_W;
localparam OUT146_OFF = OUT145_OFF + OUT146_W;
localparam OUT147_OFF = OUT146_OFF + OUT147_W;
localparam OUT148_OFF = OUT147_OFF + OUT148_W;
localparam OUT149_OFF = OUT148_OFF + OUT149_W;

localparam OUT150_OFF = OUT149_OFF + OUT150_W;
localparam OUT151_OFF = OUT150_OFF + OUT151_W;
localparam OUT152_OFF = OUT151_OFF + OUT152_W;
localparam OUT153_OFF = OUT152_OFF + OUT153_W;
localparam OUT154_OFF = OUT153_OFF + OUT154_W;
localparam OUT155_OFF = OUT154_OFF + OUT155_W;
localparam OUT156_OFF = OUT155_OFF + OUT156_W;
localparam OUT157_OFF = OUT156_OFF + OUT157_W;
localparam OUT158_OFF = OUT157_OFF + OUT158_W;
localparam OUT159_OFF = OUT158_OFF + OUT159_W;

localparam OUT160_OFF = OUT159_OFF + OUT160_W;
localparam OUT161_OFF = OUT160_OFF + OUT161_W;
localparam OUT162_OFF = OUT161_OFF + OUT162_W;
localparam OUT163_OFF = OUT162_OFF + OUT163_W;
localparam OUT164_OFF = OUT163_OFF + OUT164_W;
localparam OUT165_OFF = OUT164_OFF + OUT165_W;
localparam OUT166_OFF = OUT165_OFF + OUT166_W;
localparam OUT167_OFF = OUT166_OFF + OUT167_W;
localparam OUT168_OFF = OUT167_OFF + OUT168_W;
localparam OUT169_OFF = OUT168_OFF + OUT169_W;

localparam OUT170_OFF = OUT169_OFF + OUT170_W;
localparam OUT171_OFF = OUT170_OFF + OUT171_W;
localparam OUT172_OFF = OUT171_OFF + OUT172_W;
localparam OUT173_OFF = OUT172_OFF + OUT173_W;
localparam OUT174_OFF = OUT173_OFF + OUT174_W;
localparam OUT175_OFF = OUT174_OFF + OUT175_W;
localparam OUT176_OFF = OUT175_OFF + OUT176_W;
localparam OUT177_OFF = OUT176_OFF + OUT177_W;
localparam OUT178_OFF = OUT177_OFF + OUT178_W;
localparam OUT179_OFF = OUT178_OFF + OUT179_W;

localparam OUT180_OFF = OUT179_OFF + OUT180_W;
localparam OUT181_OFF = OUT180_OFF + OUT181_W;
localparam OUT182_OFF = OUT181_OFF + OUT182_W;
localparam OUT183_OFF = OUT182_OFF + OUT183_W;
localparam OUT184_OFF = OUT183_OFF + OUT184_W;
localparam OUT185_OFF = OUT184_OFF + OUT185_W;
localparam OUT186_OFF = OUT185_OFF + OUT186_W;
localparam OUT187_OFF = OUT186_OFF + OUT187_W;
localparam OUT188_OFF = OUT187_OFF + OUT188_W;
localparam OUT189_OFF = OUT188_OFF + OUT189_W;

localparam OUT190_OFF = OUT189_OFF + OUT190_W;
localparam OUT191_OFF = OUT190_OFF + OUT191_W;
localparam OUT192_OFF = OUT191_OFF + OUT192_W;
localparam OUT193_OFF = OUT192_OFF + OUT193_W;
localparam OUT194_OFF = OUT193_OFF + OUT194_W;
localparam OUT195_OFF = OUT194_OFF + OUT195_W;
localparam OUT196_OFF = OUT195_OFF + OUT196_W;
localparam OUT197_OFF = OUT196_OFF + OUT197_W;
localparam OUT198_OFF = OUT197_OFF + OUT198_W;
localparam OUT199_OFF = OUT198_OFF + OUT199_W;

localparam OUT200_OFF = OUT199_OFF + OUT200_W;
localparam OUT201_OFF = OUT200_OFF + OUT201_W;
localparam OUT202_OFF = OUT201_OFF + OUT202_W;
localparam OUT203_OFF = OUT202_OFF + OUT203_W;
localparam OUT204_OFF = OUT203_OFF + OUT204_W;
localparam OUT205_OFF = OUT204_OFF + OUT205_W;
localparam OUT206_OFF = OUT205_OFF + OUT206_W;
localparam OUT207_OFF = OUT206_OFF + OUT207_W;
localparam OUT208_OFF = OUT207_OFF + OUT208_W;
localparam OUT209_OFF = OUT208_OFF + OUT209_W;

localparam OUT210_OFF = OUT209_OFF + OUT210_W;
localparam OUT211_OFF = OUT210_OFF + OUT211_W;
localparam OUT212_OFF = OUT211_OFF + OUT212_W;
localparam OUT213_OFF = OUT212_OFF + OUT213_W;
localparam OUT214_OFF = OUT213_OFF + OUT214_W;
localparam OUT215_OFF = OUT214_OFF + OUT215_W;
localparam OUT216_OFF = OUT215_OFF + OUT216_W;
localparam OUT217_OFF = OUT216_OFF + OUT217_W;
localparam OUT218_OFF = OUT217_OFF + OUT218_W;
localparam OUT219_OFF = OUT218_OFF + OUT219_W;

localparam OUT220_OFF = OUT219_OFF + OUT220_W;
localparam OUT221_OFF = OUT220_OFF + OUT221_W;
localparam OUT222_OFF = OUT221_OFF + OUT222_W;
localparam OUT223_OFF = OUT222_OFF + OUT223_W;
localparam OUT224_OFF = OUT223_OFF + OUT224_W;
localparam OUT225_OFF = OUT224_OFF + OUT225_W;
localparam OUT226_OFF = OUT225_OFF + OUT226_W;
localparam OUT227_OFF = OUT226_OFF + OUT227_W;
localparam OUT228_OFF = OUT227_OFF + OUT228_W;
localparam OUT229_OFF = OUT228_OFF + OUT229_W;

localparam OUT230_OFF = OUT229_OFF + OUT230_W;
localparam OUT231_OFF = OUT230_OFF + OUT231_W;
localparam OUT232_OFF = OUT231_OFF + OUT232_W;
localparam OUT233_OFF = OUT232_OFF + OUT233_W;
localparam OUT234_OFF = OUT233_OFF + OUT234_W;
localparam OUT235_OFF = OUT234_OFF + OUT235_W;
localparam OUT236_OFF = OUT235_OFF + OUT236_W;
localparam OUT237_OFF = OUT236_OFF + OUT237_W;
localparam OUT238_OFF = OUT237_OFF + OUT238_W;
localparam OUT239_OFF = OUT238_OFF + OUT239_W;

localparam OUT240_OFF = OUT239_OFF + OUT240_W;
localparam OUT241_OFF = OUT240_OFF + OUT241_W;
localparam OUT242_OFF = OUT241_OFF + OUT242_W;
localparam OUT243_OFF = OUT242_OFF + OUT243_W;
localparam OUT244_OFF = OUT243_OFF + OUT244_W;
localparam OUT245_OFF = OUT244_OFF + OUT245_W;
localparam OUT246_OFF = OUT245_OFF + OUT246_W;
localparam OUT247_OFF = OUT246_OFF + OUT247_W;
localparam OUT248_OFF = OUT247_OFF + OUT248_W;
localparam OUT249_OFF = OUT248_OFF + OUT249_W;

localparam OUT250_OFF = OUT249_OFF + OUT250_W;
localparam OUT251_OFF = OUT250_OFF + OUT251_W;
localparam OUT252_OFF = OUT251_OFF + OUT252_W;
localparam OUT253_OFF = OUT252_OFF + OUT253_W;
localparam OUT254_OFF = OUT253_OFF + OUT254_W;
localparam OUT255_OFF = OUT254_OFF + OUT255_W;
localparam OUT256_OFF = OUT255_OFF + OUT256_W;
localparam OUT257_OFF = OUT256_OFF + OUT257_W;
localparam OUT258_OFF = OUT257_OFF + OUT258_W;
localparam OUT259_OFF = OUT258_OFF + OUT259_W;

localparam OUT260_OFF = OUT259_OFF + OUT260_W;
localparam OUT261_OFF = OUT260_OFF + OUT261_W;
localparam OUT262_OFF = OUT261_OFF + OUT262_W;
localparam OUT263_OFF = OUT262_OFF + OUT263_W;
localparam OUT264_OFF = OUT263_OFF + OUT264_W;
localparam OUT265_OFF = OUT264_OFF + OUT265_W;
localparam OUT266_OFF = OUT265_OFF + OUT266_W;
localparam OUT267_OFF = OUT266_OFF + OUT267_W;
localparam OUT268_OFF = OUT267_OFF + OUT268_W;
localparam OUT269_OFF = OUT268_OFF + OUT269_W;

localparam OUT270_OFF = OUT269_OFF + OUT270_W;
localparam OUT271_OFF = OUT270_OFF + OUT271_W;
localparam OUT272_OFF = OUT271_OFF + OUT272_W;
localparam OUT273_OFF = OUT272_OFF + OUT273_W;
localparam OUT274_OFF = OUT273_OFF + OUT274_W;
localparam OUT275_OFF = OUT274_OFF + OUT275_W;
localparam OUT276_OFF = OUT275_OFF + OUT276_W;
localparam OUT277_OFF = OUT276_OFF + OUT277_W;
localparam OUT278_OFF = OUT277_OFF + OUT278_W;
localparam OUT279_OFF = OUT278_OFF + OUT279_W;

localparam OUT280_OFF = OUT279_OFF + OUT280_W;
localparam OUT281_OFF = OUT280_OFF + OUT281_W;
localparam OUT282_OFF = OUT281_OFF + OUT282_W;
localparam OUT283_OFF = OUT282_OFF + OUT283_W;
localparam OUT284_OFF = OUT283_OFF + OUT284_W;
localparam OUT285_OFF = OUT284_OFF + OUT285_W;
localparam OUT286_OFF = OUT285_OFF + OUT286_W;
localparam OUT287_OFF = OUT286_OFF + OUT287_W;
localparam OUT288_OFF = OUT287_OFF + OUT288_W;
localparam OUT289_OFF = OUT288_OFF + OUT289_W;

localparam OUT290_OFF = OUT289_OFF + OUT290_W;
localparam OUT291_OFF = OUT290_OFF + OUT291_W;
localparam OUT292_OFF = OUT291_OFF + OUT292_W;
localparam OUT293_OFF = OUT292_OFF + OUT293_W;
localparam OUT294_OFF = OUT293_OFF + OUT294_W;
localparam OUT295_OFF = OUT294_OFF + OUT295_W;
localparam OUT296_OFF = OUT295_OFF + OUT296_W;
localparam OUT297_OFF = OUT296_OFF + OUT297_W;
localparam OUT298_OFF = OUT297_OFF + OUT298_W;
localparam OUT299_OFF = OUT298_OFF + OUT299_W;

localparam OUT300_OFF = OUT299_OFF + OUT300_W;
localparam OUT301_OFF = OUT300_OFF + OUT301_W;
localparam OUT302_OFF = OUT301_OFF + OUT302_W;
localparam OUT303_OFF = OUT302_OFF + OUT303_W;
localparam OUT304_OFF = OUT303_OFF + OUT304_W;
localparam OUT305_OFF = OUT304_OFF + OUT305_W;
localparam OUT306_OFF = OUT305_OFF + OUT306_W;
localparam OUT307_OFF = OUT306_OFF + OUT307_W;
localparam OUT308_OFF = OUT307_OFF + OUT308_W;
localparam OUT309_OFF = OUT308_OFF + OUT309_W;

localparam OUT310_OFF = OUT309_OFF + OUT310_W;
localparam OUT311_OFF = OUT310_OFF + OUT311_W;
localparam OUT312_OFF = OUT311_OFF + OUT312_W;
localparam OUT313_OFF = OUT312_OFF + OUT313_W;
localparam OUT314_OFF = OUT313_OFF + OUT314_W;
localparam OUT315_OFF = OUT314_OFF + OUT315_W;
localparam OUT316_OFF = OUT315_OFF + OUT316_W;
localparam OUT317_OFF = OUT316_OFF + OUT317_W;
localparam OUT318_OFF = OUT317_OFF + OUT318_W;
localparam OUT319_OFF = OUT318_OFF + OUT319_W;

localparam OUT320_OFF = OUT319_OFF + OUT320_W;
localparam OUT321_OFF = OUT320_OFF + OUT321_W;
localparam OUT322_OFF = OUT321_OFF + OUT322_W;
localparam OUT323_OFF = OUT322_OFF + OUT323_W;
localparam OUT324_OFF = OUT323_OFF + OUT324_W;
localparam OUT325_OFF = OUT324_OFF + OUT325_W;
localparam OUT326_OFF = OUT325_OFF + OUT326_W;
localparam OUT327_OFF = OUT326_OFF + OUT327_W;
localparam OUT328_OFF = OUT327_OFF + OUT328_W;
localparam OUT329_OFF = OUT328_OFF + OUT329_W;

localparam OUT330_OFF = OUT329_OFF + OUT330_W;
localparam OUT331_OFF = OUT330_OFF + OUT331_W;
localparam OUT332_OFF = OUT331_OFF + OUT332_W;
localparam OUT333_OFF = OUT332_OFF + OUT333_W;
localparam OUT334_OFF = OUT333_OFF + OUT334_W;
localparam OUT335_OFF = OUT334_OFF + OUT335_W;
localparam OUT336_OFF = OUT335_OFF + OUT336_W;
localparam OUT337_OFF = OUT336_OFF + OUT337_W;
localparam OUT338_OFF = OUT337_OFF + OUT338_W;
localparam OUT339_OFF = OUT338_OFF + OUT339_W;

localparam OUT340_OFF = OUT339_OFF + OUT340_W;
localparam OUT341_OFF = OUT340_OFF + OUT341_W;
localparam OUT342_OFF = OUT341_OFF + OUT342_W;
localparam OUT343_OFF = OUT342_OFF + OUT343_W;
localparam OUT344_OFF = OUT343_OFF + OUT344_W;
localparam OUT345_OFF = OUT344_OFF + OUT345_W;
localparam OUT346_OFF = OUT345_OFF + OUT346_W;
localparam OUT347_OFF = OUT346_OFF + OUT347_W;
localparam OUT348_OFF = OUT347_OFF + OUT348_W;
localparam OUT349_OFF = OUT348_OFF + OUT349_W;

localparam OUT350_OFF = OUT349_OFF + OUT350_W;
localparam OUT351_OFF = OUT350_OFF + OUT351_W;
localparam OUT352_OFF = OUT351_OFF + OUT352_W;
localparam OUT353_OFF = OUT352_OFF + OUT353_W;
localparam OUT354_OFF = OUT353_OFF + OUT354_W;
localparam OUT355_OFF = OUT354_OFF + OUT355_W;
localparam OUT356_OFF = OUT355_OFF + OUT356_W;
localparam OUT357_OFF = OUT356_OFF + OUT357_W;
localparam OUT358_OFF = OUT357_OFF + OUT358_W;
localparam OUT359_OFF = OUT358_OFF + OUT359_W;

localparam OUT360_OFF = OUT359_OFF + OUT360_W;
localparam OUT361_OFF = OUT360_OFF + OUT361_W;
localparam OUT362_OFF = OUT361_OFF + OUT362_W;
localparam OUT363_OFF = OUT362_OFF + OUT363_W;
localparam OUT364_OFF = OUT363_OFF + OUT364_W;

localparam OUT365_OFF = OUT364_OFF + OUT365_W;
localparam OUT366_OFF = OUT365_OFF + OUT366_W;
localparam OUT367_OFF = OUT366_OFF + OUT367_W;
localparam OUT368_OFF = OUT367_OFF + OUT368_W;
localparam OUT369_OFF = OUT368_OFF + OUT369_W;
localparam OUT370_OFF = OUT369_OFF + OUT370_W;
localparam OUT371_OFF = OUT370_OFF + OUT371_W;
localparam OUT372_OFF = OUT371_OFF + OUT372_W;
localparam OUT373_OFF = OUT372_OFF + OUT373_W;
localparam OUT374_OFF = OUT373_OFF + OUT374_W;
localparam OUT375_OFF = OUT374_OFF + OUT375_W;
localparam OUT376_OFF = OUT375_OFF + OUT376_W;
localparam OUT377_OFF = OUT376_OFF + OUT377_W;
localparam OUT378_OFF = OUT377_OFF + OUT378_W;
localparam OUT379_OFF = OUT378_OFF + OUT379_W;
localparam OUT380_OFF = OUT379_OFF + OUT380_W;
localparam OUT381_OFF = OUT380_OFF + OUT381_W;
localparam OUT382_OFF = OUT381_OFF + OUT382_W;
localparam OUT383_OFF = OUT382_OFF + OUT383_W;
localparam OUT384_OFF = OUT383_OFF + OUT384_W;
localparam OUT385_OFF = OUT384_OFF + OUT385_W;
localparam OUT386_OFF = OUT385_OFF + OUT386_W;
localparam OUT387_OFF = OUT386_OFF + OUT387_W;
localparam OUT388_OFF = OUT387_OFF + OUT388_W;
localparam OUT389_OFF = OUT388_OFF + OUT389_W;
localparam OUT390_OFF = OUT389_OFF + OUT390_W;
localparam OUT391_OFF = OUT390_OFF + OUT391_W;
localparam OUT392_OFF = OUT391_OFF + OUT392_W;
localparam OUT393_OFF = OUT392_OFF + OUT393_W;
localparam OUT394_OFF = OUT393_OFF + OUT394_W;
localparam OUT395_OFF = OUT394_OFF + OUT395_W;
localparam OUT396_OFF = OUT395_OFF + OUT396_W;
localparam OUT397_OFF = OUT396_OFF + OUT397_W;
localparam OUT398_OFF = OUT397_OFF + OUT398_W;
localparam OUT399_OFF = OUT398_OFF + OUT399_W;
localparam OUT400_OFF = OUT399_OFF + OUT400_W;
localparam OUT401_OFF = OUT400_OFF + OUT401_W;
localparam OUT402_OFF = OUT401_OFF + OUT402_W;
localparam OUT403_OFF = OUT402_OFF + OUT403_W;
localparam OUT404_OFF = OUT403_OFF + OUT404_W;
localparam OUT405_OFF = OUT404_OFF + OUT405_W;
localparam OUT406_OFF = OUT405_OFF + OUT406_W;
localparam OUT407_OFF = OUT406_OFF + OUT407_W;
localparam OUT408_OFF = OUT407_OFF + OUT408_W;
localparam OUT409_OFF = OUT408_OFF + OUT409_W;
localparam OUT410_OFF = OUT409_OFF + OUT410_W;
localparam OUT411_OFF = OUT410_OFF + OUT411_W;
localparam OUT412_OFF = OUT411_OFF + OUT412_W;
localparam OUT413_OFF = OUT412_OFF + OUT413_W;
localparam OUT414_OFF = OUT413_OFF + OUT414_W;
localparam OUT415_OFF = OUT414_OFF + OUT415_W;
localparam OUT416_OFF = OUT415_OFF + OUT416_W;
localparam OUT417_OFF = OUT416_OFF + OUT417_W;
localparam OUT418_OFF = OUT417_OFF + OUT418_W;
localparam OUT419_OFF = OUT418_OFF + OUT419_W;
localparam OUT420_OFF = OUT419_OFF + OUT420_W;
localparam OUT421_OFF = OUT420_OFF + OUT421_W;
localparam OUT422_OFF = OUT421_OFF + OUT422_W;
localparam OUT423_OFF = OUT422_OFF + OUT423_W;
localparam OUT424_OFF = OUT423_OFF + OUT424_W;
localparam OUT425_OFF = OUT424_OFF + OUT425_W;
localparam OUT426_OFF = OUT425_OFF + OUT426_W;
localparam OUT427_OFF = OUT426_OFF + OUT427_W;
localparam OUT428_OFF = OUT427_OFF + OUT428_W;
localparam OUT429_OFF = OUT428_OFF + OUT429_W;
localparam OUT430_OFF = OUT429_OFF + OUT430_W;
localparam OUT431_OFF = OUT430_OFF + OUT431_W;
localparam OUT432_OFF = OUT431_OFF + OUT432_W;
localparam OUT433_OFF = OUT432_OFF + OUT433_W;
localparam OUT434_OFF = OUT433_OFF + OUT434_W;
localparam OUT435_OFF = OUT434_OFF + OUT435_W;
localparam OUT436_OFF = OUT435_OFF + OUT436_W;
localparam OUT437_OFF = OUT436_OFF + OUT437_W;
localparam OUT438_OFF = OUT437_OFF + OUT438_W;
localparam OUT439_OFF = OUT438_OFF + OUT439_W;
localparam OUT440_OFF = OUT439_OFF + OUT440_W;
localparam OUT441_OFF = OUT440_OFF + OUT441_W;
localparam OUT442_OFF = OUT441_OFF + OUT442_W;
localparam OUT443_OFF = OUT442_OFF + OUT443_W;
localparam OUT444_OFF = OUT443_OFF + OUT444_W;
localparam OUT445_OFF = OUT444_OFF + OUT445_W;
localparam OUT446_OFF = OUT445_OFF + OUT446_W;
localparam OUT447_OFF = OUT446_OFF + OUT447_W;
localparam OUT448_OFF = OUT447_OFF + OUT448_W;
localparam OUT449_OFF = OUT448_OFF + OUT449_W;
localparam OUT450_OFF = OUT449_OFF + OUT450_W;
localparam OUT451_OFF = OUT450_OFF + OUT451_W;
localparam OUT452_OFF = OUT451_OFF + OUT452_W;
localparam OUT453_OFF = OUT452_OFF + OUT453_W;
localparam OUT454_OFF = OUT453_OFF + OUT454_W;
localparam OUT455_OFF = OUT454_OFF + OUT455_W;
localparam OUT456_OFF = OUT455_OFF + OUT456_W;
localparam OUT457_OFF = OUT456_OFF + OUT457_W;
localparam OUT458_OFF = OUT457_OFF + OUT458_W;
localparam OUT459_OFF = OUT458_OFF + OUT459_W;
localparam OUT460_OFF = OUT459_OFF + OUT460_W;
localparam OUT461_OFF = OUT460_OFF + OUT461_W;
localparam OUT462_OFF = OUT461_OFF + OUT462_W;
localparam OUT463_OFF = OUT462_OFF + OUT463_W;
localparam OUT464_OFF = OUT463_OFF + OUT464_W;
localparam OUT465_OFF = OUT464_OFF + OUT465_W;
localparam OUT466_OFF = OUT465_OFF + OUT466_W;
localparam OUT467_OFF = OUT466_OFF + OUT467_W;
localparam OUT468_OFF = OUT467_OFF + OUT468_W;
localparam OUT469_OFF = OUT468_OFF + OUT469_W;
localparam OUT470_OFF = OUT469_OFF + OUT470_W;
localparam OUT471_OFF = OUT470_OFF + OUT471_W;
localparam OUT472_OFF = OUT471_OFF + OUT472_W;
localparam OUT473_OFF = OUT472_OFF + OUT473_W;

localparam OUT474_OFF = OUT473_OFF + OUT474_W;
localparam OUT475_OFF = OUT474_OFF + OUT475_W;
localparam OUT476_OFF = OUT475_OFF + OUT476_W;
localparam OUT477_OFF = OUT476_OFF + OUT477_W;
localparam OUT478_OFF = OUT477_OFF + OUT478_W;
localparam OUT479_OFF = OUT478_OFF + OUT479_W;
localparam OUT480_OFF = OUT479_OFF + OUT480_W;
localparam OUT481_OFF = OUT480_OFF + OUT481_W;
localparam OUT482_OFF = OUT481_OFF + OUT482_W;
localparam OUT483_OFF = OUT482_OFF + OUT483_W;
localparam OUT484_OFF = OUT483_OFF + OUT484_W;
localparam OUT485_OFF = OUT484_OFF + OUT485_W;
localparam OUT486_OFF = OUT485_OFF + OUT486_W;
localparam OUT487_OFF = OUT486_OFF + OUT487_W;
localparam OUT488_OFF = OUT487_OFF + OUT488_W;
localparam OUT489_OFF = OUT488_OFF + OUT489_W;
localparam OUT490_OFF = OUT489_OFF + OUT490_W;
localparam OUT491_OFF = OUT490_OFF + OUT491_W;
localparam OUT492_OFF = OUT491_OFF + OUT492_W;
localparam OUT493_OFF = OUT492_OFF + OUT493_W;
localparam OUT494_OFF = OUT493_OFF + OUT494_W;
localparam OUT495_OFF = OUT494_OFF + OUT495_W;
localparam OUT496_OFF = OUT495_OFF + OUT496_W;
localparam OUT497_OFF = OUT496_OFF + OUT497_W;
localparam OUT498_OFF = OUT497_OFF + OUT498_W;
localparam OUT499_OFF = OUT498_OFF + OUT499_W;
localparam OUT500_OFF = OUT499_OFF + OUT500_W;
localparam OUT501_OFF = OUT500_OFF + OUT501_W;
localparam OUT502_OFF = OUT501_OFF + OUT502_W;
localparam OUT503_OFF = OUT502_OFF + OUT503_W;
localparam OUT504_OFF = OUT503_OFF + OUT504_W;
localparam OUT505_OFF = OUT504_OFF + OUT505_W;
localparam OUT506_OFF = OUT505_OFF + OUT506_W;
localparam OUT507_OFF = OUT506_OFF + OUT507_W;
localparam OUT508_OFF = OUT507_OFF + OUT508_W;
localparam OUT509_OFF = OUT508_OFF + OUT509_W;
localparam OUT510_OFF = OUT509_OFF + OUT510_W;
localparam OUT511_OFF = OUT510_OFF + OUT511_W;
localparam OUT512_OFF = OUT511_OFF + OUT512_W;
localparam OUT513_OFF = OUT512_OFF + OUT513_W;
localparam OUT514_OFF = OUT513_OFF + OUT514_W;
localparam OUT515_OFF = OUT514_OFF + OUT515_W;
localparam OUT516_OFF = OUT515_OFF + OUT516_W;
localparam OUT517_OFF = OUT516_OFF + OUT517_W;
localparam OUT518_OFF = OUT517_OFF + OUT518_W;
localparam OUT519_OFF = OUT518_OFF + OUT519_W;
localparam OUT520_OFF = OUT519_OFF + OUT520_W;
localparam OUT521_OFF = OUT520_OFF + OUT521_W;
localparam OUT522_OFF = OUT521_OFF + OUT522_W;

localparam OUT_TOTW = OUT522_OFF; // WARNING: update whenever a new output is added/removed
localparam [NUM_OUTS*PW-1:0] WIDTH_OFFSET =
                                            (OUT522_OFF<<522*PW)+
                                            (OUT521_OFF<<521*PW)+
                                            (OUT520_OFF<<520*PW)+
                                            (OUT519_OFF<<519*PW)+
                                            (OUT518_OFF<<518*PW)+
                                            (OUT517_OFF<<517*PW)+
                                            (OUT516_OFF<<516*PW)+
                                            (OUT515_OFF<<515*PW)+
                                            (OUT514_OFF<<514*PW)+
                                            (OUT513_OFF<<513*PW)+
                                            (OUT512_OFF<<512*PW)+
                                            (OUT511_OFF<<511*PW)+
                                            (OUT510_OFF<<510*PW)+
                                            (OUT509_OFF<<509*PW)+
                                            (OUT508_OFF<<508*PW)+
                                            (OUT507_OFF<<507*PW)+
                                            (OUT506_OFF<<506*PW)+
                                            (OUT505_OFF<<505*PW)+
                                            (OUT504_OFF<<504*PW)+
                                            (OUT503_OFF<<503*PW)+
                                            (OUT502_OFF<<502*PW)+
                                            (OUT501_OFF<<501*PW)+
                                            (OUT500_OFF<<500*PW)+
                                            (OUT499_OFF<<499*PW)+
                                            (OUT498_OFF<<498*PW)+
                                            (OUT497_OFF<<497*PW)+
                                            (OUT496_OFF<<496*PW)+
                                            (OUT495_OFF<<495*PW)+
                                            (OUT494_OFF<<494*PW)+
                                            (OUT493_OFF<<493*PW)+
                                            (OUT492_OFF<<492*PW)+
                                            (OUT491_OFF<<491*PW)+
                                            (OUT490_OFF<<490*PW)+
                                            (OUT489_OFF<<489*PW)+
                                            (OUT488_OFF<<488*PW)+
                                            (OUT487_OFF<<487*PW)+
                                            (OUT486_OFF<<486*PW)+
                                            (OUT485_OFF<<485*PW)+
                                            (OUT484_OFF<<484*PW)+
                                            (OUT483_OFF<<483*PW)+
                                            (OUT482_OFF<<482*PW)+
                                            (OUT481_OFF<<481*PW)+
                                            (OUT480_OFF<<480*PW)+
                                            (OUT479_OFF<<479*PW)+
                                            (OUT478_OFF<<478*PW)+
                                            (OUT477_OFF<<477*PW)+
                                            (OUT476_OFF<<476*PW)+
                                            (OUT475_OFF<<475*PW)+
                                            (OUT474_OFF<<474*PW)+
                                            (OUT473_OFF<<473*PW)+
                                            (OUT472_OFF<<472*PW)+
                                            (OUT471_OFF<<471*PW)+
                                            (OUT470_OFF<<470*PW)+
                                            (OUT469_OFF<<469*PW)+
                                            (OUT468_OFF<<468*PW)+
                                            (OUT467_OFF<<467*PW)+
                                            (OUT466_OFF<<466*PW)+
                                            (OUT465_OFF<<465*PW)+
                                            (OUT464_OFF<<464*PW)+
                                            (OUT463_OFF<<463*PW)+
                                            (OUT462_OFF<<462*PW)+
                                            (OUT461_OFF<<461*PW)+
                                            (OUT460_OFF<<460*PW)+
                                            (OUT459_OFF<<459*PW)+
                                            (OUT458_OFF<<458*PW)+
                                            (OUT457_OFF<<457*PW)+
                                            (OUT456_OFF<<456*PW)+
                                            (OUT455_OFF<<455*PW)+
                                            (OUT454_OFF<<454*PW)+
                                            (OUT453_OFF<<453*PW)+
                                            (OUT452_OFF<<452*PW)+
                                            (OUT451_OFF<<451*PW)+
                                            (OUT450_OFF<<450*PW)+
                                            (OUT449_OFF<<449*PW)+
                                            (OUT448_OFF<<448*PW)+
                                            (OUT447_OFF<<447*PW)+
                                            (OUT446_OFF<<446*PW)+
                                            (OUT445_OFF<<445*PW)+
                                            (OUT444_OFF<<444*PW)+
                                            (OUT443_OFF<<443*PW)+
                                            (OUT442_OFF<<442*PW)+
                                            (OUT441_OFF<<441*PW)+
                                            (OUT440_OFF<<440*PW)+
                                            (OUT439_OFF<<439*PW)+
                                            (OUT438_OFF<<438*PW)+
                                            (OUT437_OFF<<437*PW)+
                                            (OUT436_OFF<<436*PW)+
                                            (OUT435_OFF<<435*PW)+
                                            (OUT434_OFF<<434*PW)+
                                            (OUT433_OFF<<433*PW)+
                                            (OUT432_OFF<<432*PW)+
                                            (OUT431_OFF<<431*PW)+
                                            (OUT430_OFF<<430*PW)+
                                            (OUT429_OFF<<429*PW)+
                                            (OUT428_OFF<<428*PW)+
                                            (OUT427_OFF<<427*PW)+
                                            (OUT426_OFF<<426*PW)+
                                            (OUT425_OFF<<425*PW)+
                                            (OUT424_OFF<<424*PW)+
                                            (OUT423_OFF<<423*PW)+
                                            (OUT422_OFF<<422*PW)+
                                            (OUT421_OFF<<421*PW)+
                                            (OUT420_OFF<<420*PW)+
                                            (OUT419_OFF<<419*PW)+
                                            (OUT418_OFF<<418*PW)+
                                            (OUT417_OFF<<417*PW)+
                                            (OUT416_OFF<<416*PW)+
                                            (OUT415_OFF<<415*PW)+
                                            (OUT414_OFF<<414*PW)+
                                            (OUT413_OFF<<413*PW)+
                                            (OUT412_OFF<<412*PW)+
                                            (OUT411_OFF<<411*PW)+
                                            (OUT410_OFF<<410*PW)+
                                            (OUT409_OFF<<409*PW)+
                                            (OUT408_OFF<<408*PW)+
                                            (OUT407_OFF<<407*PW)+
                                            (OUT406_OFF<<406*PW)+
                                            (OUT405_OFF<<405*PW)+
                                            (OUT404_OFF<<404*PW)+
                                            (OUT403_OFF<<403*PW)+
                                            (OUT402_OFF<<402*PW)+
                                            (OUT401_OFF<<401*PW)+
                                            (OUT400_OFF<<400*PW)+
                                            (OUT399_OFF<<399*PW)+
                                            (OUT398_OFF<<398*PW)+
                                            (OUT397_OFF<<397*PW)+
                                            (OUT396_OFF<<396*PW)+
                                            (OUT395_OFF<<395*PW)+
                                            (OUT394_OFF<<394*PW)+
                                            (OUT393_OFF<<393*PW)+
                                            (OUT392_OFF<<392*PW)+
                                            (OUT391_OFF<<391*PW)+
                                            (OUT390_OFF<<390*PW)+
                                            (OUT389_OFF<<389*PW)+
                                            (OUT388_OFF<<388*PW)+
                                            (OUT387_OFF<<387*PW)+
                                            (OUT386_OFF<<386*PW)+
                                            (OUT385_OFF<<385*PW)+
                                            (OUT384_OFF<<384*PW)+
                                            (OUT383_OFF<<383*PW)+
                                            (OUT382_OFF<<382*PW)+
                                            (OUT381_OFF<<381*PW)+
                                            (OUT380_OFF<<380*PW)+
//
                                            (OUT379_OFF<<379*PW)+
                                            (OUT378_OFF<<378*PW)+
                                            (OUT377_OFF<<377*PW)+
                                            (OUT376_OFF<<376*PW)+
                                            (OUT375_OFF<<375*PW)+
                                            (OUT374_OFF<<374*PW)+
                                            (OUT373_OFF<<373*PW)+
                                            (OUT372_OFF<<372*PW)+
                                            (OUT371_OFF<<371*PW)+
                                            (OUT370_OFF<<370*PW)+
                                            (OUT369_OFF<<369*PW)+
                                            (OUT368_OFF<<368*PW)+
                                            (OUT367_OFF<<367*PW)+
                                            (OUT366_OFF<<366*PW)+
                                            (OUT365_OFF<<365*PW)+
                                            (OUT364_OFF<<364*PW)+
                                            (OUT363_OFF<<363*PW)+
                                            (OUT362_OFF<<362*PW)+
                                            (OUT361_OFF<<361*PW)+
                                            (OUT360_OFF<<360*PW)+

                                            (OUT359_OFF<<359*PW)+
                                            (OUT358_OFF<<358*PW)+
                                            (OUT357_OFF<<357*PW)+
                                            (OUT356_OFF<<356*PW)+
                                            (OUT355_OFF<<355*PW)+
                                            (OUT354_OFF<<354*PW)+
                                            (OUT353_OFF<<353*PW)+
                                            (OUT352_OFF<<352*PW)+
                                            (OUT351_OFF<<351*PW)+
                                            (OUT350_OFF<<350*PW)+

                                            (OUT349_OFF<<349*PW)+
                                            (OUT348_OFF<<348*PW)+
                                            (OUT347_OFF<<347*PW)+
                                            (OUT346_OFF<<346*PW)+
                                            (OUT345_OFF<<345*PW)+
                                            (OUT344_OFF<<344*PW)+
                                            (OUT343_OFF<<343*PW)+
                                            (OUT342_OFF<<342*PW)+
                                            (OUT341_OFF<<341*PW)+
                                            (OUT340_OFF<<340*PW)+

                                            (OUT339_OFF<<339*PW)+
                                            (OUT338_OFF<<338*PW)+
                                            (OUT337_OFF<<337*PW)+
                                            (OUT336_OFF<<336*PW)+
                                            (OUT335_OFF<<335*PW)+
                                            (OUT334_OFF<<334*PW)+
                                            (OUT333_OFF<<333*PW)+
                                            (OUT332_OFF<<332*PW)+
                                            (OUT331_OFF<<331*PW)+
                                            (OUT330_OFF<<330*PW)+

                                            (OUT329_OFF<<329*PW)+
                                            (OUT328_OFF<<328*PW)+
                                            (OUT327_OFF<<327*PW)+
                                            (OUT326_OFF<<326*PW)+
                                            (OUT325_OFF<<325*PW)+
                                            (OUT324_OFF<<324*PW)+
                                            (OUT323_OFF<<323*PW)+
                                            (OUT322_OFF<<322*PW)+
                                            (OUT321_OFF<<321*PW)+
                                            (OUT320_OFF<<320*PW)+

                                            (OUT319_OFF<<319*PW)+
                                            (OUT318_OFF<<318*PW)+
                                            (OUT317_OFF<<317*PW)+
                                            (OUT316_OFF<<316*PW)+
                                            (OUT315_OFF<<315*PW)+
                                            (OUT314_OFF<<314*PW)+
                                            (OUT313_OFF<<313*PW)+
                                            (OUT312_OFF<<312*PW)+
                                            (OUT311_OFF<<311*PW)+
                                            (OUT310_OFF<<310*PW)+

                                            (OUT309_OFF<<309*PW)+
                                            (OUT308_OFF<<308*PW)+
                                            (OUT307_OFF<<307*PW)+
                                            (OUT306_OFF<<306*PW)+
                                            (OUT305_OFF<<305*PW)+
                                            (OUT304_OFF<<304*PW)+
                                            (OUT303_OFF<<303*PW)+
                                            (OUT302_OFF<<302*PW)+
                                            (OUT301_OFF<<301*PW)+
                                            (OUT300_OFF<<300*PW)+

                                            (OUT299_OFF<<299*PW)+
                                            (OUT298_OFF<<298*PW)+
                                            (OUT297_OFF<<297*PW)+
                                            (OUT296_OFF<<296*PW)+
                                            (OUT295_OFF<<295*PW)+
                                            (OUT294_OFF<<294*PW)+
                                            (OUT293_OFF<<293*PW)+
                                            (OUT292_OFF<<292*PW)+
                                            (OUT291_OFF<<291*PW)+
                                            (OUT290_OFF<<290*PW)+

                                            (OUT289_OFF<<289*PW)+
                                            (OUT288_OFF<<288*PW)+
                                            (OUT287_OFF<<287*PW)+
                                            (OUT286_OFF<<286*PW)+
                                            (OUT285_OFF<<285*PW)+
                                            (OUT284_OFF<<284*PW)+
                                            (OUT283_OFF<<283*PW)+
                                            (OUT282_OFF<<282*PW)+
                                            (OUT281_OFF<<281*PW)+
                                            (OUT280_OFF<<280*PW)+

                                            (OUT279_OFF<<279*PW)+
                                            (OUT278_OFF<<278*PW)+
                                            (OUT277_OFF<<277*PW)+
                                            (OUT276_OFF<<276*PW)+
                                            (OUT275_OFF<<275*PW)+
                                            (OUT274_OFF<<274*PW)+
                                            (OUT273_OFF<<273*PW)+
                                            (OUT272_OFF<<272*PW)+
                                            (OUT271_OFF<<271*PW)+
                                            (OUT270_OFF<<270*PW)+

                                            (OUT269_OFF<<269*PW)+
                                            (OUT268_OFF<<268*PW)+
                                            (OUT267_OFF<<267*PW)+
                                            (OUT266_OFF<<266*PW)+
                                            (OUT265_OFF<<265*PW)+
                                            (OUT264_OFF<<264*PW)+
                                            (OUT263_OFF<<263*PW)+
                                            (OUT262_OFF<<262*PW)+
                                            (OUT261_OFF<<261*PW)+
                                            (OUT260_OFF<<260*PW)+

                                            (OUT259_OFF<<259*PW)+
                                            (OUT258_OFF<<258*PW)+
                                            (OUT257_OFF<<257*PW)+
                                            (OUT256_OFF<<256*PW)+
                                            (OUT255_OFF<<255*PW)+
                                            (OUT254_OFF<<254*PW)+
                                            (OUT253_OFF<<253*PW)+
                                            (OUT252_OFF<<252*PW)+
                                            (OUT251_OFF<<251*PW)+
                                            (OUT250_OFF<<250*PW)+

                                            (OUT249_OFF<<249*PW)+
                                            (OUT248_OFF<<248*PW)+
                                            (OUT247_OFF<<247*PW)+
                                            (OUT246_OFF<<246*PW)+
                                            (OUT245_OFF<<245*PW)+
                                            (OUT244_OFF<<244*PW)+
                                            (OUT243_OFF<<243*PW)+
                                            (OUT242_OFF<<242*PW)+
                                            (OUT241_OFF<<241*PW)+
                                            (OUT240_OFF<<240*PW)+

                                            (OUT239_OFF<<239*PW)+
                                            (OUT238_OFF<<238*PW)+
                                            (OUT237_OFF<<237*PW)+
                                            (OUT236_OFF<<236*PW)+
                                            (OUT235_OFF<<235*PW)+
                                            (OUT234_OFF<<234*PW)+
                                            (OUT233_OFF<<233*PW)+
                                            (OUT232_OFF<<232*PW)+
                                            (OUT231_OFF<<231*PW)+
                                            (OUT230_OFF<<230*PW)+

                                            (OUT229_OFF<<229*PW)+
                                            (OUT228_OFF<<228*PW)+
                                            (OUT227_OFF<<227*PW)+
                                            (OUT226_OFF<<226*PW)+
                                            (OUT225_OFF<<225*PW)+
                                            (OUT224_OFF<<224*PW)+
                                            (OUT223_OFF<<223*PW)+
                                            (OUT222_OFF<<222*PW)+
                                            (OUT221_OFF<<221*PW)+
                                            (OUT220_OFF<<220*PW)+

                                            (OUT219_OFF<<219*PW)+
                                            (OUT218_OFF<<218*PW)+
                                            (OUT217_OFF<<217*PW)+
                                            (OUT216_OFF<<216*PW)+
                                            (OUT215_OFF<<215*PW)+
                                            (OUT214_OFF<<214*PW)+
                                            (OUT213_OFF<<213*PW)+
                                            (OUT212_OFF<<212*PW)+
                                            (OUT211_OFF<<211*PW)+
                                            (OUT210_OFF<<210*PW)+

                                            (OUT209_OFF<<209*PW)+
                                            (OUT208_OFF<<208*PW)+
                                            (OUT207_OFF<<207*PW)+
                                            (OUT206_OFF<<206*PW)+
                                            (OUT205_OFF<<205*PW)+
                                            (OUT204_OFF<<204*PW)+
                                            (OUT203_OFF<<203*PW)+
                                            (OUT202_OFF<<202*PW)+
                                            (OUT201_OFF<<201*PW)+
                                            (OUT200_OFF<<200*PW)+

                                            (OUT199_OFF<<199*PW)+
                                            (OUT198_OFF<<198*PW)+
                                            (OUT197_OFF<<197*PW)+
                                            (OUT196_OFF<<196*PW)+
                                            (OUT195_OFF<<195*PW)+
                                            (OUT194_OFF<<194*PW)+
                                            (OUT193_OFF<<193*PW)+
                                            (OUT192_OFF<<192*PW)+
                                            (OUT191_OFF<<191*PW)+
                                            (OUT190_OFF<<190*PW)+

                                            (OUT189_OFF<<189*PW)+
                                            (OUT188_OFF<<188*PW)+
                                            (OUT187_OFF<<187*PW)+
                                            (OUT186_OFF<<186*PW)+
                                            (OUT185_OFF<<185*PW)+
                                            (OUT184_OFF<<184*PW)+
                                            (OUT183_OFF<<183*PW)+
                                            (OUT182_OFF<<182*PW)+
                                            (OUT181_OFF<<181*PW)+
                                            (OUT180_OFF<<180*PW)+

                                            (OUT179_OFF<<179*PW)+
                                            (OUT178_OFF<<178*PW)+
                                            (OUT177_OFF<<177*PW)+
                                            (OUT176_OFF<<176*PW)+
                                            (OUT175_OFF<<175*PW)+
                                            (OUT174_OFF<<174*PW)+
                                            (OUT173_OFF<<173*PW)+
                                            (OUT172_OFF<<172*PW)+
                                            (OUT171_OFF<<171*PW)+
                                            (OUT170_OFF<<170*PW)+

                                            (OUT169_OFF<<169*PW)+
                                            (OUT168_OFF<<168*PW)+
                                            (OUT167_OFF<<167*PW)+
                                            (OUT166_OFF<<166*PW)+
                                            (OUT165_OFF<<165*PW)+
                                            (OUT164_OFF<<164*PW)+
                                            (OUT163_OFF<<163*PW)+
                                            (OUT162_OFF<<162*PW)+
                                            (OUT161_OFF<<161*PW)+
                                            (OUT160_OFF<<160*PW)+

                                            (OUT159_OFF<<159*PW)+
                                            (OUT158_OFF<<158*PW)+
                                            (OUT157_OFF<<157*PW)+
                                            (OUT156_OFF<<156*PW)+
                                            (OUT155_OFF<<155*PW)+
                                            (OUT154_OFF<<154*PW)+
                                            (OUT153_OFF<<153*PW)+
                                            (OUT152_OFF<<152*PW)+
                                            (OUT151_OFF<<151*PW)+
                                            (OUT150_OFF<<150*PW)+

                                            (OUT149_OFF<<149*PW)+
                                            (OUT148_OFF<<148*PW)+
                                            (OUT147_OFF<<147*PW)+
                                            (OUT146_OFF<<146*PW)+
                                            (OUT145_OFF<<145*PW)+
                                            (OUT144_OFF<<144*PW)+
                                            (OUT143_OFF<<143*PW)+
                                            (OUT142_OFF<<142*PW)+
                                            (OUT141_OFF<<141*PW)+
                                            (OUT140_OFF<<140*PW)+

                                            (OUT139_OFF<<139*PW)+
                                            (OUT138_OFF<<138*PW)+
                                            (OUT137_OFF<<137*PW)+
                                            (OUT136_OFF<<136*PW)+
                                            (OUT135_OFF<<135*PW)+
                                            (OUT134_OFF<<134*PW)+
                                            (OUT133_OFF<<133*PW)+
                                            (OUT132_OFF<<132*PW)+
                                            (OUT131_OFF<<131*PW)+
                                            (OUT130_OFF<<130*PW)+

                                            (OUT129_OFF<<129*PW)+
                                            (OUT128_OFF<<128*PW)+
                                            (OUT127_OFF<<127*PW)+
                                            (OUT126_OFF<<126*PW)+
                                            (OUT125_OFF<<125*PW)+
                                            (OUT124_OFF<<124*PW)+
                                            (OUT123_OFF<<123*PW)+
                                            (OUT122_OFF<<122*PW)+
                                            (OUT121_OFF<<121*PW)+
                                            (OUT120_OFF<<120*PW)+

                                            (OUT119_OFF<<119*PW)+
                                            (OUT118_OFF<<118*PW)+
                                            (OUT117_OFF<<117*PW)+
                                            (OUT116_OFF<<116*PW)+
                                            (OUT115_OFF<<115*PW)+
                                            (OUT114_OFF<<114*PW)+
                                            (OUT113_OFF<<113*PW)+
                                            (OUT112_OFF<<112*PW)+
                                            (OUT111_OFF<<111*PW)+
                                            (OUT110_OFF<<110*PW)+

                                            (OUT109_OFF<<109*PW)+
                                            (OUT108_OFF<<108*PW)+
                                            (OUT107_OFF<<107*PW)+
                                            (OUT106_OFF<<106*PW)+
                                            (OUT105_OFF<<105*PW)+
                                            (OUT104_OFF<<104*PW)+
                                            (OUT103_OFF<<103*PW)+
                                            (OUT102_OFF<<102*PW)+
                                            (OUT101_OFF<<101*PW)+
                                            (OUT100_OFF<<100*PW)+

                                            (OUT99_OFF<<99*PW)+
                                            (OUT98_OFF<<98*PW)+
                                            (OUT97_OFF<<97*PW)+
                                            (OUT96_OFF<<96*PW)+
                                            (OUT95_OFF<<95*PW)+
                                            (OUT94_OFF<<94*PW)+
                                            (OUT93_OFF<<93*PW)+
                                            (OUT92_OFF<<92*PW)+
                                            (OUT91_OFF<<91*PW)+
                                            (OUT90_OFF<<90*PW)+

                                            (OUT89_OFF<<89*PW)+
                                            (OUT88_OFF<<88*PW)+
                                            (OUT87_OFF<<87*PW)+
                                            (OUT86_OFF<<86*PW)+
                                            (OUT85_OFF<<85*PW)+
                                            (OUT84_OFF<<84*PW)+
                                            (OUT83_OFF<<83*PW)+
                                            (OUT82_OFF<<82*PW)+
                                            (OUT81_OFF<<81*PW)+
                                            (OUT80_OFF<<80*PW)+

                                            (OUT79_OFF<<79*PW)+
                                            (OUT78_OFF<<78*PW)+
                                            (OUT77_OFF<<77*PW)+
                                            (OUT76_OFF<<76*PW)+
                                            (OUT75_OFF<<75*PW)+
                                            (OUT74_OFF<<74*PW)+
                                            (OUT73_OFF<<73*PW)+
                                            (OUT72_OFF<<72*PW)+
                                            (OUT71_OFF<<71*PW)+
                                            (OUT70_OFF<<70*PW)+

                                            (OUT69_OFF<<69*PW)+
                                            (OUT68_OFF<<68*PW)+
                                            (OUT67_OFF<<67*PW)+
                                            (OUT66_OFF<<66*PW)+
                                            (OUT65_OFF<<65*PW)+
                                            (OUT64_OFF<<64*PW)+
                                            (OUT63_OFF<<63*PW)+
                                            (OUT62_OFF<<62*PW)+
                                            (OUT61_OFF<<61*PW)+
                                            (OUT60_OFF<<60*PW)+

                                            (OUT59_OFF<<59*PW)+
                                            (OUT58_OFF<<58*PW)+
                                            (OUT57_OFF<<57*PW)+
                                            (OUT56_OFF<<56*PW)+
                                            (OUT55_OFF<<55*PW)+
                                            (OUT54_OFF<<54*PW)+
                                            (OUT53_OFF<<53*PW)+
                                            (OUT52_OFF<<52*PW)+
                                            (OUT51_OFF<<51*PW)+
                                            (OUT50_OFF<<50*PW)+

                                            (OUT49_OFF<<49*PW)+
                                            (OUT48_OFF<<48*PW)+
                                            (OUT47_OFF<<47*PW)+
                                            (OUT46_OFF<<46*PW)+
                                            (OUT45_OFF<<45*PW)+
                                            (OUT44_OFF<<44*PW)+
                                            (OUT43_OFF<<43*PW)+
                                            (OUT42_OFF<<42*PW)+
                                            (OUT41_OFF<<41*PW)+
                                            (OUT40_OFF<<40*PW)+

                                            (OUT39_OFF<<39*PW)+
                                            (OUT38_OFF<<38*PW)+
                                            (OUT37_OFF<<37*PW)+
                                            (OUT36_OFF<<36*PW)+
                                            (OUT35_OFF<<35*PW)+
                                            (OUT34_OFF<<34*PW)+
                                            (OUT33_OFF<<33*PW)+
                                            (OUT32_OFF<<32*PW)+
                                            (OUT31_OFF<<31*PW)+
                                            (OUT30_OFF<<30*PW)+

                                            (OUT29_OFF<<29*PW)+
                                            (OUT28_OFF<<28*PW)+
                                            (OUT27_OFF<<27*PW)+
                                            (OUT26_OFF<<26*PW)+
                                            (OUT25_OFF<<25*PW)+
                                            (OUT24_OFF<<24*PW)+
                                            (OUT23_OFF<<23*PW)+
                                            (OUT22_OFF<<22*PW)+
                                            (OUT21_OFF<<21*PW)+
                                            (OUT20_OFF<<20*PW)+

                                            (OUT19_OFF<<19*PW)+
                                            (OUT18_OFF<<18*PW)+
                                            (OUT17_OFF<<17*PW)+
                                            (OUT16_OFF<<16*PW)+
                                            (OUT15_OFF<<15*PW)+
                                            (OUT14_OFF<<14*PW)+
                                            (OUT13_OFF<<13*PW)+
                                            (OUT12_OFF<<12*PW)+
                                            (OUT11_OFF<<11*PW)+
                                            (OUT10_OFF<<10*PW)+

                                            (OUT9_OFF<<9*PW)+
                                            (OUT8_OFF<<8*PW)+
                                            (OUT7_OFF<<7*PW)+
                                            (OUT6_OFF<<6*PW)+
                                            (OUT5_OFF<<5*PW)+
                                            (OUT4_OFF<<4*PW)+
                                            (OUT3_OFF<<3*PW)+
                                            (OUT2_OFF<<2*PW)+
                                            (OUT1_OFF<<1*PW)+
                                            OUT0_OFF;

localparam [NUM_OUTS*PW-1:0] WIDTH_ARRAY =
                                            (OUT522_W<<522*PW)+
                                            (OUT521_W<<521*PW)+
                                            (OUT520_W<<520*PW)+
                                            (OUT519_W<<519*PW)+
                                            (OUT518_W<<518*PW)+
                                            (OUT517_W<<517*PW)+
                                            (OUT516_W<<516*PW)+
                                            (OUT515_W<<515*PW)+
                                            (OUT514_W<<514*PW)+
                                            (OUT513_W<<513*PW)+
                                            (OUT512_W<<512*PW)+
                                            (OUT511_W<<511*PW)+
                                            (OUT510_W<<510*PW)+
                                            (OUT509_W<<509*PW)+
                                            (OUT508_W<<508*PW)+
                                            (OUT507_W<<507*PW)+
                                            (OUT506_W<<506*PW)+
                                            (OUT505_W<<505*PW)+
                                            (OUT504_W<<504*PW)+
                                            (OUT503_W<<503*PW)+
                                            (OUT502_W<<502*PW)+
                                            (OUT501_W<<501*PW)+
                                            (OUT500_W<<500*PW)+
                                            (OUT499_W<<499*PW)+
                                            (OUT498_W<<498*PW)+
                                            (OUT497_W<<497*PW)+
                                            (OUT496_W<<496*PW)+
                                            (OUT495_W<<495*PW)+
                                            (OUT494_W<<494*PW)+
                                            (OUT493_W<<493*PW)+
                                            (OUT492_W<<492*PW)+
                                            (OUT491_W<<491*PW)+
                                            (OUT490_W<<490*PW)+
                                            (OUT489_W<<489*PW)+
                                            (OUT488_W<<488*PW)+
                                            (OUT487_W<<487*PW)+
                                            (OUT486_W<<486*PW)+
                                            (OUT485_W<<485*PW)+
                                            (OUT484_W<<484*PW)+
                                            (OUT483_W<<483*PW)+
                                            (OUT482_W<<482*PW)+
                                            (OUT481_W<<481*PW)+
                                            (OUT480_W<<480*PW)+
                                            (OUT479_W<<479*PW)+
                                            (OUT478_W<<478*PW)+
                                            (OUT477_W<<477*PW)+
                                            (OUT476_W<<476*PW)+
                                            (OUT475_W<<475*PW)+
                                            (OUT474_W<<474*PW)+
                                            (OUT473_W<<473*PW)+
                                            (OUT472_W<<472*PW)+
                                            (OUT471_W<<471*PW)+
                                            (OUT470_W<<470*PW)+
                                            (OUT469_W<<469*PW)+
                                            (OUT468_W<<468*PW)+
                                            (OUT467_W<<467*PW)+
                                            (OUT466_W<<466*PW)+
                                            (OUT465_W<<465*PW)+
                                            (OUT464_W<<464*PW)+
                                            (OUT463_W<<463*PW)+
                                            (OUT462_W<<462*PW)+
                                            (OUT461_W<<461*PW)+
                                            (OUT460_W<<460*PW)+
                                            (OUT459_W<<459*PW)+
                                            (OUT458_W<<458*PW)+
                                            (OUT457_W<<457*PW)+
                                            (OUT456_W<<456*PW)+
                                            (OUT455_W<<455*PW)+
                                            (OUT454_W<<454*PW)+
                                            (OUT453_W<<453*PW)+
                                            (OUT452_W<<452*PW)+
                                            (OUT451_W<<451*PW)+
                                            (OUT450_W<<450*PW)+
                                            (OUT449_W<<449*PW)+
                                            (OUT448_W<<448*PW)+
                                            (OUT447_W<<447*PW)+
                                            (OUT446_W<<446*PW)+
                                            (OUT445_W<<445*PW)+
                                            (OUT444_W<<444*PW)+
                                            (OUT443_W<<443*PW)+
                                            (OUT442_W<<442*PW)+
                                            (OUT441_W<<441*PW)+
                                            (OUT440_W<<440*PW)+
                                            (OUT439_W<<439*PW)+
                                            (OUT438_W<<438*PW)+
                                            (OUT437_W<<437*PW)+
                                            (OUT436_W<<436*PW)+
                                            (OUT435_W<<435*PW)+
                                            (OUT434_W<<434*PW)+
                                            (OUT433_W<<433*PW)+
                                            (OUT432_W<<432*PW)+
                                            (OUT431_W<<431*PW)+
                                            (OUT430_W<<430*PW)+
                                            (OUT429_W<<429*PW)+
                                            (OUT428_W<<428*PW)+
                                            (OUT427_W<<427*PW)+
                                            (OUT426_W<<426*PW)+
                                            (OUT425_W<<425*PW)+
                                            (OUT424_W<<424*PW)+
                                            (OUT423_W<<423*PW)+
                                            (OUT422_W<<422*PW)+
                                            (OUT421_W<<421*PW)+
                                            (OUT420_W<<420*PW)+
                                            (OUT419_W<<419*PW)+
                                            (OUT418_W<<418*PW)+
                                            (OUT417_W<<417*PW)+
                                            (OUT416_W<<416*PW)+
                                            (OUT415_W<<415*PW)+
                                            (OUT414_W<<414*PW)+
                                            (OUT413_W<<413*PW)+
                                            (OUT412_W<<412*PW)+
                                            (OUT411_W<<411*PW)+
                                            (OUT410_W<<410*PW)+
                                            (OUT409_W<<409*PW)+
                                            (OUT408_W<<408*PW)+
                                            (OUT407_W<<407*PW)+
                                            (OUT406_W<<406*PW)+
                                            (OUT405_W<<405*PW)+
                                            (OUT404_W<<404*PW)+
                                            (OUT403_W<<403*PW)+
                                            (OUT402_W<<402*PW)+
                                            (OUT401_W<<401*PW)+
                                            (OUT400_W<<400*PW)+
                                            (OUT399_W<<399*PW)+
                                            (OUT398_W<<398*PW)+
                                            (OUT397_W<<397*PW)+
                                            (OUT396_W<<396*PW)+
                                            (OUT395_W<<395*PW)+
                                            (OUT394_W<<394*PW)+
                                            (OUT393_W<<393*PW)+
                                            (OUT392_W<<392*PW)+
                                            (OUT391_W<<391*PW)+
                                            (OUT390_W<<390*PW)+
                                            (OUT389_W<<389*PW)+
                                            (OUT388_W<<388*PW)+
                                            (OUT387_W<<387*PW)+
                                            (OUT386_W<<386*PW)+
                                            (OUT385_W<<385*PW)+
                                            (OUT384_W<<384*PW)+
                                            (OUT383_W<<383*PW)+
                                            (OUT382_W<<382*PW)+
                                            (OUT381_W<<381*PW)+
                                            (OUT380_W<<380*PW)+

                                            (OUT379_W<<379*PW)+
                                            (OUT378_W<<378*PW)+
                                            (OUT377_W<<377*PW)+
                                            (OUT376_W<<376*PW)+
                                            (OUT375_W<<375*PW)+
                                            (OUT374_W<<374*PW)+
                                            (OUT373_W<<373*PW)+
                                            (OUT372_W<<372*PW)+
                                            (OUT371_W<<371*PW)+
                                            (OUT370_W<<370*PW)+

                                            (OUT369_W<<369*PW)+
                                            (OUT368_W<<368*PW)+
                                            (OUT367_W<<367*PW)+
                                            (OUT366_W<<366*PW)+
                                            (OUT365_W<<365*PW)+
                                            (OUT364_W<<364*PW)+
                                            (OUT363_W<<363*PW)+
                                            (OUT362_W<<362*PW)+
                                            (OUT361_W<<361*PW)+
                                            (OUT360_W<<360*PW)+

                                            (OUT359_W<<359*PW)+
                                            (OUT358_W<<358*PW)+
                                            (OUT357_W<<357*PW)+
                                            (OUT356_W<<356*PW)+
                                            (OUT355_W<<355*PW)+
                                            (OUT354_W<<354*PW)+
                                            (OUT353_W<<353*PW)+
                                            (OUT352_W<<352*PW)+
                                            (OUT351_W<<351*PW)+
                                            (OUT350_W<<350*PW)+

                                            (OUT349_W<<349*PW)+
                                            (OUT348_W<<348*PW)+
                                            (OUT347_W<<347*PW)+
                                            (OUT346_W<<346*PW)+
                                            (OUT345_W<<345*PW)+
                                            (OUT344_W<<344*PW)+
                                            (OUT343_W<<343*PW)+
                                            (OUT342_W<<342*PW)+
                                            (OUT341_W<<341*PW)+
                                            (OUT340_W<<340*PW)+

                                            (OUT339_W<<339*PW)+
                                            (OUT338_W<<338*PW)+
                                            (OUT337_W<<337*PW)+
                                            (OUT336_W<<336*PW)+
                                            (OUT335_W<<335*PW)+
                                            (OUT334_W<<334*PW)+
                                            (OUT333_W<<333*PW)+
                                            (OUT332_W<<332*PW)+
                                            (OUT331_W<<331*PW)+
                                            (OUT330_W<<330*PW)+

                                            (OUT329_W<<329*PW)+
                                            (OUT328_W<<328*PW)+
                                            (OUT327_W<<327*PW)+
                                            (OUT326_W<<326*PW)+
                                            (OUT325_W<<325*PW)+
                                            (OUT324_W<<324*PW)+
                                            (OUT323_W<<323*PW)+
                                            (OUT322_W<<322*PW)+
                                            (OUT321_W<<321*PW)+
                                            (OUT320_W<<320*PW)+

                                            (OUT319_W<<319*PW)+
                                            (OUT318_W<<318*PW)+
                                            (OUT317_W<<317*PW)+
                                            (OUT316_W<<316*PW)+
                                            (OUT315_W<<315*PW)+
                                            (OUT314_W<<314*PW)+
                                            (OUT313_W<<313*PW)+
                                            (OUT312_W<<312*PW)+
                                            (OUT311_W<<311*PW)+
                                            (OUT310_W<<310*PW)+

                                            (OUT309_W<<309*PW)+
                                            (OUT308_W<<308*PW)+
                                            (OUT307_W<<307*PW)+
                                            (OUT306_W<<306*PW)+
                                            (OUT305_W<<305*PW)+
                                            (OUT304_W<<304*PW)+
                                            (OUT303_W<<303*PW)+
                                            (OUT302_W<<302*PW)+
                                            (OUT301_W<<301*PW)+
                                            (OUT300_W<<300*PW)+

                                            (OUT299_W<<299*PW)+
                                            (OUT298_W<<298*PW)+
                                            (OUT297_W<<297*PW)+
                                            (OUT296_W<<296*PW)+
                                            (OUT295_W<<295*PW)+
                                            (OUT294_W<<294*PW)+
                                            (OUT293_W<<293*PW)+
                                            (OUT292_W<<292*PW)+
                                            (OUT291_W<<291*PW)+
                                            (OUT290_W<<290*PW)+

                                            (OUT289_W<<289*PW)+
                                            (OUT288_W<<288*PW)+
                                            (OUT287_W<<287*PW)+
                                            (OUT286_W<<286*PW)+
                                            (OUT285_W<<285*PW)+
                                            (OUT284_W<<284*PW)+
                                            (OUT283_W<<283*PW)+
                                            (OUT282_W<<282*PW)+
                                            (OUT281_W<<281*PW)+
                                            (OUT280_W<<280*PW)+

                                            (OUT279_W<<279*PW)+
                                            (OUT278_W<<278*PW)+
                                            (OUT277_W<<277*PW)+
                                            (OUT276_W<<276*PW)+
                                            (OUT275_W<<275*PW)+
                                            (OUT274_W<<274*PW)+
                                            (OUT273_W<<273*PW)+
                                            (OUT272_W<<272*PW)+
                                            (OUT271_W<<271*PW)+
                                            (OUT270_W<<270*PW)+

                                            (OUT269_W<<269*PW)+
                                            (OUT268_W<<268*PW)+
                                            (OUT267_W<<267*PW)+
                                            (OUT266_W<<266*PW)+
                                            (OUT265_W<<265*PW)+
                                            (OUT264_W<<264*PW)+
                                            (OUT263_W<<263*PW)+
                                            (OUT262_W<<262*PW)+
                                            (OUT261_W<<261*PW)+
                                            (OUT260_W<<260*PW)+

                                            (OUT259_W<<259*PW)+
                                            (OUT258_W<<258*PW)+
                                            (OUT257_W<<257*PW)+
                                            (OUT256_W<<256*PW)+
                                            (OUT255_W<<255*PW)+
                                            (OUT254_W<<254*PW)+
                                            (OUT253_W<<253*PW)+
                                            (OUT252_W<<252*PW)+
                                            (OUT251_W<<251*PW)+
                                            (OUT250_W<<250*PW)+

                                            (OUT249_W<<249*PW)+
                                            (OUT248_W<<248*PW)+
                                            (OUT247_W<<247*PW)+
                                            (OUT246_W<<246*PW)+
                                            (OUT245_W<<245*PW)+
                                            (OUT244_W<<244*PW)+
                                            (OUT243_W<<243*PW)+
                                            (OUT242_W<<242*PW)+
                                            (OUT241_W<<241*PW)+
                                            (OUT240_W<<240*PW)+

                                            (OUT239_W<<239*PW)+
                                            (OUT238_W<<238*PW)+
                                            (OUT237_W<<237*PW)+
                                            (OUT236_W<<236*PW)+
                                            (OUT235_W<<235*PW)+
                                            (OUT234_W<<234*PW)+
                                            (OUT233_W<<233*PW)+
                                            (OUT232_W<<232*PW)+
                                            (OUT231_W<<231*PW)+
                                            (OUT230_W<<230*PW)+

                                            (OUT229_W<<229*PW)+
                                            (OUT228_W<<228*PW)+
                                            (OUT227_W<<227*PW)+
                                            (OUT226_W<<226*PW)+
                                            (OUT225_W<<225*PW)+
                                            (OUT224_W<<224*PW)+
                                            (OUT223_W<<223*PW)+
                                            (OUT222_W<<222*PW)+
                                            (OUT221_W<<221*PW)+
                                            (OUT220_W<<220*PW)+

                                            (OUT219_W<<219*PW)+
                                            (OUT218_W<<218*PW)+
                                            (OUT217_W<<217*PW)+
                                            (OUT216_W<<216*PW)+
                                            (OUT215_W<<215*PW)+
                                            (OUT214_W<<214*PW)+
                                            (OUT213_W<<213*PW)+
                                            (OUT212_W<<212*PW)+
                                            (OUT211_W<<211*PW)+
                                            (OUT210_W<<210*PW)+

                                            (OUT209_W<<209*PW)+
                                            (OUT208_W<<208*PW)+
                                            (OUT207_W<<207*PW)+
                                            (OUT206_W<<206*PW)+
                                            (OUT205_W<<205*PW)+
                                            (OUT204_W<<204*PW)+
                                            (OUT203_W<<203*PW)+
                                            (OUT202_W<<202*PW)+
                                            (OUT201_W<<201*PW)+
                                            (OUT200_W<<200*PW)+

                                            (OUT199_W<<199*PW)+
                                            (OUT198_W<<198*PW)+
                                            (OUT197_W<<197*PW)+
                                            (OUT196_W<<196*PW)+
                                            (OUT195_W<<195*PW)+
                                            (OUT194_W<<194*PW)+
                                            (OUT193_W<<193*PW)+
                                            (OUT192_W<<192*PW)+
                                            (OUT191_W<<191*PW)+
                                            (OUT190_W<<190*PW)+

                                            (OUT189_W<<189*PW)+
                                            (OUT188_W<<188*PW)+
                                            (OUT187_W<<187*PW)+
                                            (OUT186_W<<186*PW)+
                                            (OUT185_W<<185*PW)+
                                            (OUT184_W<<184*PW)+
                                            (OUT183_W<<183*PW)+
                                            (OUT182_W<<182*PW)+
                                            (OUT181_W<<181*PW)+
                                            (OUT180_W<<180*PW)+

                                            (OUT179_W<<179*PW)+
                                            (OUT178_W<<178*PW)+
                                            (OUT177_W<<177*PW)+
                                            (OUT176_W<<176*PW)+
                                            (OUT175_W<<175*PW)+
                                            (OUT174_W<<174*PW)+
                                            (OUT173_W<<173*PW)+
                                            (OUT172_W<<172*PW)+
                                            (OUT171_W<<171*PW)+
                                            (OUT170_W<<170*PW)+

                                            (OUT169_W<<169*PW)+
                                            (OUT168_W<<168*PW)+
                                            (OUT167_W<<167*PW)+
                                            (OUT166_W<<166*PW)+
                                            (OUT165_W<<165*PW)+
                                            (OUT164_W<<164*PW)+
                                            (OUT163_W<<163*PW)+
                                            (OUT162_W<<162*PW)+
                                            (OUT161_W<<161*PW)+
                                            (OUT160_W<<160*PW)+

                                            (OUT159_W<<159*PW)+
                                            (OUT158_W<<158*PW)+
                                            (OUT157_W<<157*PW)+
                                            (OUT156_W<<156*PW)+
                                            (OUT155_W<<155*PW)+
                                            (OUT154_W<<154*PW)+
                                            (OUT153_W<<153*PW)+
                                            (OUT152_W<<152*PW)+
                                            (OUT151_W<<151*PW)+
                                            (OUT150_W<<150*PW)+

                                            (OUT149_W<<149*PW)+
                                            (OUT148_W<<148*PW)+
                                            (OUT147_W<<147*PW)+
                                            (OUT146_W<<146*PW)+
                                            (OUT145_W<<145*PW)+
                                            (OUT144_W<<144*PW)+
                                            (OUT143_W<<143*PW)+
                                            (OUT142_W<<142*PW)+
                                            (OUT141_W<<141*PW)+
                                            (OUT140_W<<140*PW)+

                                            (OUT139_W<<139*PW)+
                                            (OUT138_W<<138*PW)+
                                            (OUT137_W<<137*PW)+
                                            (OUT136_W<<136*PW)+
                                            (OUT135_W<<135*PW)+
                                            (OUT134_W<<134*PW)+
                                            (OUT133_W<<133*PW)+
                                            (OUT132_W<<132*PW)+
                                            (OUT131_W<<131*PW)+
                                            (OUT130_W<<130*PW)+

                                            (OUT129_W<<129*PW)+
                                            (OUT128_W<<128*PW)+
                                            (OUT127_W<<127*PW)+
                                            (OUT126_W<<126*PW)+
                                            (OUT125_W<<125*PW)+
                                            (OUT124_W<<124*PW)+
                                            (OUT123_W<<123*PW)+
                                            (OUT122_W<<122*PW)+
                                            (OUT121_W<<121*PW)+
                                            (OUT120_W<<120*PW)+

                                            (OUT119_W<<119*PW)+
                                            (OUT118_W<<118*PW)+
                                            (OUT117_W<<117*PW)+
                                            (OUT116_W<<116*PW)+
                                            (OUT115_W<<115*PW)+
                                            (OUT114_W<<114*PW)+
                                            (OUT113_W<<113*PW)+
                                            (OUT112_W<<112*PW)+
                                            (OUT111_W<<111*PW)+
                                            (OUT110_W<<110*PW)+

                                            (OUT109_W<<109*PW)+
                                            (OUT108_W<<108*PW)+
                                            (OUT107_W<<107*PW)+
                                            (OUT106_W<<106*PW)+
                                            (OUT105_W<<105*PW)+
                                            (OUT104_W<<104*PW)+
                                            (OUT103_W<<103*PW)+
                                            (OUT102_W<<102*PW)+
                                            (OUT101_W<<101*PW)+
                                            (OUT100_W<<100*PW)+

                                            (OUT99_W<<99*PW)+
                                            (OUT98_W<<98*PW)+
                                            (OUT97_W<<97*PW)+
                                            (OUT96_W<<96*PW)+
                                            (OUT95_W<<95*PW)+
                                            (OUT94_W<<94*PW)+
                                            (OUT93_W<<93*PW)+
                                            (OUT92_W<<92*PW)+
                                            (OUT91_W<<91*PW)+
                                            (OUT90_W<<90*PW)+

                                            (OUT89_W<<89*PW)+
                                            (OUT88_W<<88*PW)+
                                            (OUT87_W<<87*PW)+
                                            (OUT86_W<<86*PW)+
                                            (OUT85_W<<85*PW)+
                                            (OUT84_W<<84*PW)+
                                            (OUT83_W<<83*PW)+
                                            (OUT82_W<<82*PW)+
                                            (OUT81_W<<81*PW)+
                                            (OUT80_W<<80*PW)+

                                            (OUT79_W<<79*PW)+
                                            (OUT78_W<<78*PW)+
                                            (OUT77_W<<77*PW)+
                                            (OUT76_W<<76*PW)+
                                            (OUT75_W<<75*PW)+
                                            (OUT74_W<<74*PW)+
                                            (OUT73_W<<73*PW)+
                                            (OUT72_W<<72*PW)+
                                            (OUT71_W<<71*PW)+
                                            (OUT70_W<<70*PW)+

                                            (OUT69_W<<69*PW)+
                                            (OUT68_W<<68*PW)+
                                            (OUT67_W<<67*PW)+
                                            (OUT66_W<<66*PW)+
                                            (OUT65_W<<65*PW)+
                                            (OUT64_W<<64*PW)+
                                            (OUT63_W<<63*PW)+
                                            (OUT62_W<<62*PW)+
                                            (OUT61_W<<61*PW)+
                                            (OUT60_W<<60*PW)+

                                            (OUT59_W<<59*PW)+
                                            (OUT58_W<<58*PW)+
                                            (OUT57_W<<57*PW)+
                                            (OUT56_W<<56*PW)+
                                            (OUT55_W<<55*PW)+
                                            (OUT54_W<<54*PW)+
                                            (OUT53_W<<53*PW)+
                                            (OUT52_W<<52*PW)+
                                            (OUT51_W<<51*PW)+
                                            (OUT50_W<<50*PW)+

                                            (OUT49_W<<49*PW)+
                                            (OUT48_W<<48*PW)+
                                            (OUT47_W<<47*PW)+
                                            (OUT46_W<<46*PW)+
                                            (OUT45_W<<45*PW)+
                                            (OUT44_W<<44*PW)+
                                            (OUT43_W<<43*PW)+
                                            (OUT42_W<<42*PW)+
                                            (OUT41_W<<41*PW)+
                                            (OUT40_W<<40*PW)+

                                            (OUT39_W<<39*PW)+
                                            (OUT38_W<<38*PW)+
                                            (OUT37_W<<37*PW)+
                                            (OUT36_W<<36*PW)+
                                            (OUT35_W<<35*PW)+
                                            (OUT34_W<<34*PW)+
                                            (OUT33_W<<33*PW)+
                                            (OUT32_W<<32*PW)+
                                            (OUT31_W<<31*PW)+
                                            (OUT30_W<<30*PW)+

                                            (OUT29_W<<29*PW)+
                                            (OUT28_W<<28*PW)+
                                            (OUT27_W<<27*PW)+
                                            (OUT26_W<<26*PW)+
                                            (OUT25_W<<25*PW)+
                                            (OUT24_W<<24*PW)+
                                            (OUT23_W<<23*PW)+
                                            (OUT22_W<<22*PW)+
                                            (OUT21_W<<21*PW)+
                                            (OUT20_W<<20*PW)+

                                            (OUT19_W<<19*PW)+
                                            (OUT18_W<<18*PW)+
                                            (OUT17_W<<17*PW)+
                                            (OUT16_W<<16*PW)+
                                            (OUT15_W<<15*PW)+
                                            (OUT14_W<<14*PW)+
                                            (OUT13_W<<13*PW)+
                                            (OUT12_W<<12*PW)+
                                            (OUT11_W<<11*PW)+
                                            (OUT10_W<<10*PW)+

                                            (OUT9_W<<9*PW)+
                                            (OUT8_W<<8*PW)+
                                            (OUT7_W<<7*PW)+
                                            (OUT6_W<<6*PW)+
                                            (OUT5_W<<5*PW)+
                                            (OUT4_W<<4*PW)+
                                            (OUT3_W<<3*PW)+
                                            (OUT2_W<<2*PW)+
                                            (OUT1_W<<1*PW)+
                                            OUT0_W;

//------------------------------------------------------------------------------
// ddrc_ctrl
//------------------------------------------------------------------------------

  genvar n;

  wire                              hif_cmd_stall_w [NUM_INST-1:0];
  wire                              hif_rcmd_stall_w [NUM_INST-1:0];
  wire                              hif_wcmd_stall_w [NUM_INST-1:0];
  wire                              hif_wdata_ptr_valid_w [NUM_INST-1:0];
  wire [WDATA_PTR_BITS-1:0]         hif_wdata_ptr_w [NUM_INST-1:0];
  wire                              hif_wdata_ptr_addr_err_w [NUM_INST-1:0];
  wire [`MEMC_HIF_CREDIT_BITS-1:0]  hif_lpr_credit_w [NUM_INST-1:0];
  wire                              hif_wr_credit_w [NUM_INST-1:0];
  wire [`MEMC_HIF_CREDIT_BITS-1:0]  hif_hpr_credit_w [NUM_INST-1:0];
  wire                              ddrc_reg_mr_wr_busy_w [NUM_INST-1:0];
  wire                              ddrc_reg_pda_done_w [NUM_INST-1:0];
  wire                              ddrc_reg_zq_reset_busy_w [NUM_INST-1:0];
  wire                              hif_cmd_q_not_empty_w [NUM_INST-1:0];
  wire                              csysack_ddrc_w [NUM_INST-1:0];
  wire                              cactive_ddrc_w [NUM_INST-1:0];
  wire [SELFREF_TYPE_WIDTH-1:0]     stat_ddrc_reg_selfref_type_w [NUM_INST-1:0];
  wire [3:0]                        stat_ddrc_reg_retry_current_state_w [NUM_INST-1:0];
  wire [2:0]                        dbg_dfi_ie_cmd_type_w [NUM_INST-1:0];
  wire                              dbg_dfi_in_retry_w [NUM_INST-1:0];
  wire                              dbg_wr_crc_retry_pulse_w [NUM_INST-1:0];
  wire                              dbg_rd_crc_retry_pulse_w [NUM_INST-1:0];
  wire                              dbg_rd_ue_retry_pulse_w [NUM_INST-1:0];
  wire [LRANK_BITS_DUP-1:0]         dbg_rd_retry_rank_w [NUM_INST-1:0];
  wire                              pi_rd_crc_retry_limit_reach_pre_w [NUM_INST-1:0];
  wire                              pi_rt_rd_crc_retry_limit_reach_pre_w [NUM_INST-1:0];
  wire                              pi_rd_ue_retry_limit_reach_pre_w [NUM_INST-1:0];
  wire                              pi_rt_rd_ue_retry_limit_reach_pre_w [NUM_INST-1:0];
  wire [BSM_BITS:0]                 ddrc_reg_num_alloc_bsm_w [NUM_INST-1:0];
  wire                              perf_hif_rd_or_wr_w [NUM_INST-1:0];
  wire                              perf_hif_wr_w [NUM_INST-1:0];
  wire                              perf_hif_rd_w [NUM_INST-1:0];
  wire                              perf_hif_rmw_w [NUM_INST-1:0];
  wire                              perf_hif_hi_pri_rd_w [NUM_INST-1:0];
  wire                              perf_read_bypass_w [NUM_INST-1:0];
  wire                              perf_act_bypass_w [NUM_INST-1:0];
  wire                              perf_hpr_xact_when_critical_w [NUM_INST-1:0];
  wire                              perf_lpr_xact_when_critical_w [NUM_INST-1:0];
  wire                              perf_wr_xact_when_critical_w [NUM_INST-1:0];
  wire                              perf_op_is_activate_w [NUM_INST-1:0];
  wire                              perf_op_is_rd_or_wr_w [NUM_INST-1:0];
  wire                              perf_op_is_rd_activate_w [NUM_INST-1:0];
  wire                              perf_op_is_rd_w [NUM_INST-1:0];
  wire                              perf_op_is_wr_w [NUM_INST-1:0];
  wire                              perf_op_is_mwr_w [NUM_INST-1:0];
  wire                              perf_op_is_wr16_w [NUM_INST-1:0];
  wire                              perf_op_is_wr32_w [NUM_INST-1:0];
  wire                              perf_op_is_rd16_w [NUM_INST-1:0];
  wire                              perf_op_is_rd32_w [NUM_INST-1:0];
  wire                              perf_op_is_cas_w [NUM_INST-1:0];
  wire                              perf_op_is_cas_ws_w [NUM_INST-1:0];
  wire                              perf_op_is_cas_ws_off_w [NUM_INST-1:0];
  wire                              perf_op_is_cas_wck_sus_w [NUM_INST-1:0];
  wire                              perf_op_is_enter_dsm_w [NUM_INST-1:0];
  wire                              perf_op_is_rfm_w [NUM_INST-1:0];
  wire                              perf_op_is_precharge_w [NUM_INST-1:0];
  wire                              perf_precharge_for_rdwr_w [NUM_INST-1:0];
  wire                              perf_precharge_for_other_w [NUM_INST-1:0];
  wire                              perf_rdwr_transitions_w [NUM_INST-1:0];
  wire                              perf_write_combine_w [NUM_INST-1:0];
  wire                              perf_write_combine_noecc_w [NUM_INST-1:0];
  wire                              perf_write_combine_wrecc_w [NUM_INST-1:0];
  wire                              perf_war_hazard_w [NUM_INST-1:0];
  wire                              perf_raw_hazard_w [NUM_INST-1:0];
  wire                              perf_waw_hazard_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              perf_op_is_enter_selfref_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              perf_op_is_enter_powerdown_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              perf_op_is_enter_mpsm_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              perf_selfref_mode_w [NUM_INST-1:0];
  wire                              perf_op_is_refresh_w [NUM_INST-1:0];
  wire                              perf_op_is_load_mode_w [NUM_INST-1:0];
  wire                              perf_op_is_zqcl_w [NUM_INST-1:0];
  wire                              perf_op_is_zqcs_w [NUM_INST-1:0];
  wire [RANK_BITS_DUP-1:0]          perf_rank_w [NUM_INST-1:0];
  wire [`MEMC_BANK_BITS-1:0]        perf_bank_w [NUM_INST-1:0];
  wire [BG_BITS_DUP-1:0]            perf_bg_w [NUM_INST-1:0];
  wire [CID_WIDTH_DUP-1:0]          perf_cid_w [NUM_INST-1:0];
  wire [RANK_BITS_DUP-1:0]          perf_bypass_rank_w [NUM_INST-1:0];
  wire [`MEMC_BANK_BITS-1:0]        perf_bypass_bank_w [NUM_INST-1:0];
  wire [BG_BITS_DUP-1:0]            perf_bypass_bg_w [NUM_INST-1:0];
  wire [CID_WIDTH_DUP-1:0]          perf_bypass_cid_w [NUM_INST-1:0];
  wire                              perf_bsm_alloc_w [NUM_INST-1:0];
  wire                              perf_bsm_starvation_w [NUM_INST-1:0];
  wire [BSM_BITS:0]                 perf_num_alloc_bsm_w [NUM_INST-1:0];
  wire                              perf_visible_window_limit_reached_rd_w[NUM_INST-1:0];
  wire                              perf_visible_window_limit_reached_wr_w[NUM_INST-1:0];
  wire                              perf_op_is_dqsosc_mpc_w[NUM_INST-1:0];
  wire                              perf_op_is_dqsosc_mrr_w[NUM_INST-1:0];
  wire                              perf_op_is_tcr_mrr_w[NUM_INST-1:0];
  wire                              perf_op_is_zqstart_w[NUM_INST-1:0];
  wire                              perf_op_is_zqlatch_w[NUM_INST-1:0];
  wire [2:0]                        ddrc_core_reg_dbg_operating_mode_w [NUM_INST-1:0];
  wire [4:0]                        ddrc_core_reg_dbg_global_fsm_state_w [NUM_INST-1:0];
  wire [4:0]                        ddrc_core_reg_dbg_init_curr_state_w [NUM_INST-1:0];
  wire [4:0]                        ddrc_core_reg_dbg_init_next_state_w [NUM_INST-1:0];
  wire [1:0]                        ddrc_core_reg_dbg_ctrlupd_state_w [NUM_INST-1:0];
  wire [1:0]                        ddrc_core_reg_dbg_lpr_q_state_w [NUM_INST-1:0];
  wire [1:0]                        ddrc_core_reg_dbg_hpr_q_state_w [NUM_INST-1:0];
  wire [1:0]                        ddrc_core_reg_dbg_wr_q_state_w [NUM_INST-1:0];
  wire [RD_CAM_ADDR_WIDTH+1-1:0]    ddrc_core_reg_dbg_lpr_q_depth_w [NUM_INST-1:0];
  wire [RD_CAM_ADDR_WIDTH+1-1:0]    ddrc_core_reg_dbg_hpr_q_depth_w [NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH+1-1:0]    ddrc_core_reg_dbg_wr_q_depth_w [NUM_INST-1:0];
  wire                              ddrc_core_reg_dbg_hif_cmd_stall_w [NUM_INST-1:0];
  wire                              ddrc_core_reg_dbg_hif_rcmd_stall_w [NUM_INST-1:0];
  wire                              ddrc_core_reg_dbg_hif_wcmd_stall_w [NUM_INST-1:0];

  wire [NUM_TOTAL_BANKS-1:0]        ddrc_core_reg_dbg_rd_valid_rank_w [NUM_INST-1:0];
  wire [NUM_TOTAL_BANKS-1:0]        ddrc_core_reg_dbg_rd_page_hit_rank_w [NUM_INST-1:0];
  wire [NUM_TOTAL_BANKS-1:0]        ddrc_core_reg_dbg_rd_pri_rank_w [NUM_INST-1:0];
  wire [NUM_TOTAL_BANKS-1:0]        ddrc_core_reg_dbg_wr_valid_rank_w [NUM_INST-1:0];
  wire [NUM_TOTAL_BANKS-1:0]        ddrc_core_reg_dbg_wr_page_hit_rank_w [NUM_INST-1:0];

  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_7_0_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_7_0_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_15_8_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_15_8_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_23_16_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_23_16_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_31_24_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_31_24_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_39_32_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_39_32_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_47_40_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_47_40_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_55_48_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_55_48_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_wr_cam_63_56_valid_w [NUM_INST-1:0];
  wire [7:0]                        ddrc_core_reg_dbg_rd_cam_63_56_valid_w [NUM_INST-1:0];

  wire [(`MEMC_FREQ_RATIO*BG_BITS_DUP)-1:0]       dfi_bg_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]                     dfi_act_n_w [NUM_INST-1:0];
  wire [(`MEMC_FREQ_RATIO*CID_WIDTH_DUP)-1:0]     dfi_cid_w [NUM_INST-1:0];
  dfi_address_s                                   dfi_address_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*BANK_BITS-1:0]           dfi_bank_w [NUM_INST-1:0];
  wire [1:0]                                      dfi_freq_ratio_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]                     dfi_cas_n_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]                     dfi_ras_n_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]                     dfi_we_n_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]           dfi_cke_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]           dfi_cs_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]           dfi_odt_w [NUM_INST-1:0];
  wire [`UMCTL2_RESET_WIDTH-1:0]                  dfi_reset_n_w [NUM_INST-1:0];
  wire [`MEMC_HIF_ADDR_WIDTH-1:0]                 dfi_hif_cmd_addr_w[NUM_INST-1:0];
  wire [`DDRCTL_DFI_HIF_CMD_WDATA_PTR_RANGE-1:0]  dfi_hif_cmd_wdata_ptr_w[NUM_INST-1:0];
  wire [HIF_KEYID_WIDTH-1:0]                      dfi_hif_cmd_keyid_w[NUM_INST-1:0];

  wire [`MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES-1:0] dfi_wrdata_cs_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*NUM_RANKS*NUM_LANES-1:0] dfi_rddata_cs_w [NUM_INST-1:0];

  wire                                            dfi_ctrlupd_req_w [NUM_INST-1:0];
  wire [1:0]                                      dfi_ctrlupd_type_w [NUM_INST-1:0];
  wire [1:0]                                      dfi_ctrlupd_target_w [NUM_INST-1:0];
  wire                                            ddrc_reg_ppt2_burst_busy_w [NUM_INST-1:0];
  wire [PPT2_STATE_WIDTH-1:0]                     ddrc_reg_ppt2_state_w [NUM_INST-1:0];
  wire [NUM_PHY_DRAM_CLKS-1:0]                    dfi_dram_clk_disable_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*PARITY_IN_WIDTH-1:0]     dfi_parity_in_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO*NUM_RANKS-1:0]   dfi_wck_cs_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]             dfi_wck_en_w [NUM_INST-1:0];
  wire [2*`MEMC_FREQ_RATIO-1:0]           dfi_wck_toggle_w [NUM_INST-1:0];


  wire                              dfi_init_start_w [NUM_INST-1:0];
  wire [1:0]                        dfi_freq_fsp_w [NUM_INST-1:0];
  wire [4:0]                        dfi_frequency_w [NUM_INST-1:0];
  wire                              dfi_2n_mode_w [NUM_INST-1:0];
  wire                              dfi_reset_n_ref_w [NUM_INST-1:0];
  wire                              init_mr_done_out_w [NUM_INST-1:0];
  wire                              ddrc_reg_capar_err_intr_w [NUM_INST-1:0];
  wire [CAPAR_ERR_CNT_WIDTH-1:0]                       ddrc_reg_capar_err_cnt_w [NUM_INST-1:0];

  wire                              ddrc_reg_dfi_error_intr_w [NUM_INST-1:0];
  wire [DFI_ERROR_INFO_WIDTH-1:0]   ddrc_reg_dfi_error_info_w [NUM_INST-1:0];  
  wire                              ddrc_reg_dfi_sideband_timer_err_intr_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tctrlupd_min_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tctrlupd_max_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tinit_start_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tinit_complete_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tlp_ctrl_resp_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tlp_data_resp_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tlp_ctrl_wakeup_error_w [NUM_INST-1:0];
  wire                              ddrc_reg_dfi_tlp_data_wakeup_error_w [NUM_INST-1:0];

  wire                              ddrc_reg_capar_err_max_reached_intr_w [NUM_INST-1:0];
  wire                              ddrc_reg_capar_retry_limit_intr_w [NUM_INST-1:0];
  wire                              ddrc_reg_capar_fatl_err_intr_w [NUM_INST-1:0];
  wire [CAPAR_FATL_ERR_CODE_WIDTH-1:0] ddrc_reg_capar_fatl_err_code_w [NUM_INST-1:0];
  wire [WR_CRC_ERR_CNT_WIDTH-1:0]   ddrc_reg_wr_crc_err_cnt_w [NUM_INST-1:0];
  wire                              ddrc_reg_wr_crc_err_intr_w [NUM_INST-1:0];
  wire                              ddrc_reg_wr_crc_err_max_reached_intr_w [NUM_INST-1:0];
  wire [RETRY_FIFO_FILL_LEVEL_WIDTH-1:0]     ddrc_reg_retry_fifo_fill_level_w [NUM_INST-1:0];
  wire [RETRY_STAT_WIDTH-1:0]                ddrc_reg_retry_stat_w [NUM_INST-1:0];

  wire                              retryram_din_w [NUM_INST-1:0];
  wire                              retryram_waddr_w [NUM_INST-1:0];
  wire                              retryram_raddr_w [NUM_INST-1:0];
  wire                              retryram_re_w [NUM_INST-1:0];
  wire                              retryram_we_w [NUM_INST-1:0];
  wire                              retryram_mask_w [NUM_INST-1:0];

  wire                              ddrc_reg_wr_crc_retry_limit_intr_w [NUM_INST-1:0];                        
  wire                              ddrc_reg_rd_retry_limit_intr_w [NUM_INST-1:0];                        
  wire                              ddrc_reg_rd_crc_retry_limit_reached_w [NUM_INST-1:0];                        
  wire                              ddrc_reg_rd_ue_retry_limit_reached_w [NUM_INST-1:0];                        

  wire [NUM_LRANKS-1:0]             ddrc_reg_rank_refresh_busy_w [NUM_INST-1:0];
  wire [NUM_LRANKS-1:0]             ext_rank_refresh_busy_w [NUM_INST-1:0];

  wire                              ddrc_reg_ctrlupd_busy_w [NUM_INST-1:0];
  wire                              ddrc_reg_ctrlupd_burst_busy_w [NUM_INST-1:0];

  wire                              ddrc_reg_capar_poison_complete_w [NUM_INST-1:0];
  wire                              dbg_dfi_parity_poison_w [NUM_INST-1:0];

  wire [RD_CAM_ADDR_WIDTH:0]        ddrc_reg_dbg_hpr_q_depth_w [NUM_INST-1:0];
  wire [RD_CAM_ADDR_WIDTH:0]        ddrc_reg_dbg_lpr_q_depth_w [NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH:0]        ddrc_reg_dbg_w_q_depth_w [NUM_INST-1:0];
  wire                              ddrc_reg_dbg_stall_w [NUM_INST-1:0];
  wire                              ddrc_reg_dbg_stall_rd_w [NUM_INST-1:0];
  wire                              ddrc_reg_dbg_stall_wr_w [NUM_INST-1:0];
  wire                              ddrc_reg_selfref_cam_not_empty_w [NUM_INST-1:0];
  wire [2:0]                        ddrc_reg_selfref_state_w [NUM_INST-1:0];
  wire [2:0]                        ddrc_reg_operating_mode_w [NUM_INST-1:0];

  wire [SELFREF_TYPE_WIDTH-1:0]     ddrc_reg_selfref_type_w [NUM_INST-1:0];
  wire                              ddrc_reg_wr_q_empty_w [NUM_INST-1:0];
  wire                              ddrc_reg_rd_q_empty_w [NUM_INST-1:0];
  wire                              ddrc_reg_wr_data_pipeline_empty_w [NUM_INST-1:0];
  wire                              ddrc_reg_rd_data_pipeline_empty_w [NUM_INST-1:0];

  wire                              ddrc_reg_zq_calib_short_busy_w [NUM_INST-1:0];
  wire [BANK_BITS*NUM_RANKS-1:0]    hif_refresh_req_bank_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              hif_refresh_req_w [NUM_INST-1:0];
  wire [6*NUM_RANKS-1:0]            hif_refresh_req_cnt_w [NUM_INST-1:0];
  wire [2:0]                        hif_refresh_req_derate_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              hif_refresh_active_w [NUM_INST-1:0];

  wire                              dfi_phyupd_ack_w [NUM_INST-1:0];
  wire                              dfi_phymstr_ack_w [NUM_INST-1:0];
  wire                              dfi_lp_ctrl_req_w [NUM_INST-1:0];
  wire [DFI_LP_WAKEUP_PD_WIDTH-1:0] dfi_lp_ctrl_wakeup_w [NUM_INST-1:0];
  wire                              dfi_lp_data_req_w [NUM_INST-1:0];
  wire [DFI_LP_WAKEUP_PD_WIDTH-1:0] dfi_lp_data_wakeup_w [NUM_INST-1:0];

  hwffcmrw_if_at_hwffcmrw_op_s      hwffcmrw_op_s_w[NUM_INST-1:0];
  wire                              hwffc_target_freq_en_w [NUM_INST-1:0];
  wire [TARGET_FREQUENCY_WIDTH-1:0] hwffc_target_freq_w [NUM_INST-1:0];
  wire [TARGET_FREQUENCY_WIDTH-1:0] hwffc_target_freq_init_w [NUM_INST-1:0];

  wire                              ddrc_reg_hwffc_in_progress_w [NUM_INST-1:0];
  wire [TARGET_FREQUENCY_WIDTH-1:0]                 ddrc_reg_current_frequency_w [NUM_INST-1:0];
  wire                              ddrc_reg_current_fsp_w [NUM_INST-1:0];
  wire                              ddrc_reg_current_vrcg_w [NUM_INST-1:0];
  wire                              ddrc_reg_hwffc_operating_mode_w [NUM_INST-1:0];
  wire                              ddrc_xpi_port_disable_req_w [NUM_INST-1:0];
  wire                              ddrc_xpi_clock_required_w [NUM_INST-1:0];

  wire                              hwffc_hif_wd_stall_w [NUM_INST-1:0];
  wire                              hwffc_i_reg_ddrc_dis_auto_zq_w [NUM_INST-1:0];

  wire                              ih_mr_ie_blk_wr_end_w [NUM_INST-1:0];
  wire [IE_PW_BITS-1:0]             ih_mr_ie_pw_w [NUM_INST-1:0];
  wire [BRT_BITS-1:0]               ih_rd_ie_brt_w [NUM_INST-1:0];
  wire                              ih_rd_ie_rd_cnt_inc_w [NUM_INST-1:0];
  wire                              ih_rd_ie_blk_rd_end_w [NUM_INST-1:0];
  wire                              ih_mr_ie_wr_cnt_inc_w [NUM_INST-1:0];
  wire [NO_OF_BWT-1:0]              ih_mr_ie_wr_cnt_dec_vct_w [NUM_INST-1:0];
  wire [BWT_BITS-1:0]               ih_mr_ie_bwt_w [NUM_INST-1:0];
  wire [BRT_BITS-1:0]               ih_mr_ie_brt_w [NUM_INST-1:0];
  wire                              ih_mr_ie_brt_vld_w [NUM_INST-1:0];

  wire [BT_BITS-1:0]                te_mr_ie_bt_w [NUM_INST-1:0];
  wire [IE_WR_TYPE_BITS-1:0]        te_mr_ie_wr_type_w [NUM_INST-1:0];
  wire [IE_BURST_NUM_BITS-1:0]      te_mr_ie_blk_burst_num_w [NUM_INST-1:0];
  wire [34:0]                       te_mr_addr_info_w [NUM_INST-1:0];

  wire [BT_BITS-1:0]                pi_rt_ie_bt_w [NUM_INST-1:0];
  wire [IE_RD_TYPE_BITS-1:0]        pi_rt_ie_rd_type_w [NUM_INST-1:0];
  wire [IE_BURST_NUM_BITS-1:0]      pi_rt_ie_blk_burst_num_w [NUM_INST-1:0];

  wire [BWT_BITS-1:0]               ih_mr_lkp_bwt_w [NUM_INST-1:0];
  wire                              ih_mr_lkp_bwt_vld_w [NUM_INST-1:0];
  wire [BRT_BITS-1:0]               ih_mr_lkp_brt_w [NUM_INST-1:0];
  wire                              ih_mr_lkp_brt_vld_w [NUM_INST-1:0];

  wire [BRT_BITS-1:0]               ih_rd_lkp_brt_w [NUM_INST-1:0];
  wire                              ih_rd_lkp_brt_vld_w [NUM_INST-1:0];
  wire [BWT_BITS-1:0]               ih_rd_lkp_bwt_w [NUM_INST-1:0];
  wire                              ih_rd_lkp_bwt_vld_w [NUM_INST-1:0];

  wire                              te_mr_eccap_w [NUM_INST-1:0];
  wire                              pi_rt_eccap_w [NUM_INST-1:0];
  wire                              pi_rd_eccap_w [NUM_INST-1:0];

  wire [`MEMC_DCERRBITS-1:0]        ih_wu_cerr_w [NUM_INST-1:0];

  wire                              pi_rt_rd_mrr_w [NUM_INST-1:0];
  wire                              pi_rt_rd_mrr_ext_w [NUM_INST-1:0];
  wire                              pi_ph_dfi_rddata_en_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]       pi_ph_dfi_wrdata_en_w [NUM_INST-1:0];
  wire                              ih_wu_wr_valid_w [NUM_INST-1:0];
  wire                              ih_wu_wr_valid_addr_err_w [NUM_INST-1:0];
  wire [`DDRCTL_EAPAR_SIZE-1:0]     ih_wu_wr_eapar_w [NUM_INST-1:0];
  wire                              ih_te_rd_valid_w [NUM_INST-1:0];
  wire                              ih_te_wr_valid_w [NUM_INST-1:0];
  wire [RMW_TYPE_BITS-1:0]          ih_wu_rmw_type_w [NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH-1:0]      ih_wu_wr_entry_w [NUM_INST-1:0];
  wire [WORD_BITS-1:0]              ih_wu_critical_word_w [NUM_INST-1:0];
  wire                              pi_gs_geardown_mode_on_w [NUM_INST-1:0];

  wire [CMD_LEN_BITS-1:0]           pi_rt_rd_partial_w [NUM_INST-1:0];
  wire                              pi_rt_rd_vld_w [NUM_INST-1:0];

  wire [CORE_TAG_WIDTH-1:0]         pi_rt_rd_tag_w [NUM_INST-1:0];

  wire                              pi_rt_rd_addr_err_w [NUM_INST-1:0];

  wire [WR_CAM_ADDR_WIDTH-1:0]      pi_rt_wr_ram_addr_w [NUM_INST-1:0];
  wire [CMD_RMW_BITS-1:0]           pi_rt_rmwcmd_w [NUM_INST-1:0];
  wire [RMW_TYPE_BITS-1:0]          pi_rt_rmwtype_w [NUM_INST-1:0];

  wire [RANKBANK_BITS_FULL-1:0]     pi_rt_rankbank_num_w [NUM_INST-1:0];
  wire [PAGE_BITS-1:0]              pi_rt_page_num_w [NUM_INST-1:0];
  wire [BLK_BITS-1:0]               pi_rt_block_num_w [NUM_INST-1:0];
  wire [WORD_BITS-1:0]              pi_rt_critical_word_w [NUM_INST-1:0];

  wire                              te_yy_wr_combine_w [NUM_INST-1:0];
  wire                              te_wu_wrdata_stall_req_w [NUM_INST-1:0];

  wire                              ts_pi_mwr_w [NUM_INST-1:0];
  wire                              ts_pi_wr32_w [NUM_INST-1:0];
  wire                              ts_pi_2nd_half_w [NUM_INST-1:0];
  wire                              ts_cam_clear_en_w [NUM_INST-1:0];
  wire [PARTIAL_WR_BITS-1:0]        te_pi_wr_word_valid_w [NUM_INST-1:0];
  wire [2:0]                        gs_pi_rdwr_bc_sel_w [NUM_INST-1:0];
  wire [PARTIAL_WR_BITS_LOG2-1:0]   gs_pi_rdwr_ram_raddr_lsb_first_w [NUM_INST-1:0];
  wire [PW_WORD_CNT_WD_MAX-1:0]     gs_pi_rdwr_pw_num_beats_m1_w [NUM_INST-1:0];

  wire [2:0]                        gs_wr_bc_sel_w[NUM_INST-1:0];
  wire [PARTIAL_WR_BITS_LOG2-1:0]   gs_mr_ram_raddr_lsb_first_w[NUM_INST-1:0];
  wire [PW_WORD_CNT_WD_MAX-1:0]     gs_mr_pw_num_beats_m1_w[NUM_INST-1:0];

  wire [WR_CAM_ADDR_WIDTH_IE-1:0]   te_mr_wr_ram_addr_w [NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH-1:0]      te_wu_entry_num_w [NUM_INST-1:0];
  wire                              te_wu_wr_retry_w [NUM_INST-1:0];
  wire                              gs_mr_write_w [NUM_INST-1:0];
  wire                              gs_mr_load_mode_pda_w [NUM_INST-1:0];
  wire [1:0]                        gs_mr_pda_data_sel_w [NUM_INST-1:0];
  wire                              pda_mode_w [NUM_INST-1:0];
  wire                              pda_mode_pre_w [NUM_INST-1:0];
  wire [MAX_CMD_NUM*NUM_RANKS-1:0]  gs_pi_cs_n_w [NUM_INST-1:0];
  wire                              retry_fifo_empty_w [NUM_INST-1:0];
  wire                              retry_rt_rdatavld_gate_en_w [NUM_INST-1:0];
  wire                              retry_rt_fifo_init_n_w [NUM_INST-1:0];
  wire                              retry_rt_fatl_err_pulse_w [NUM_INST-1:0];
  wire                              retry_rt_now_sw_intervention_w [NUM_INST-1:0];
  wire [7:0]                        retry_rt_rd_timeout_value_w [NUM_INST-1:0];

  wire                              retry_dfi_sel_w [NUM_INST-1:0];
  wire [PHY_MASK_WIDTH-1:0]         retry_phy_dm_w [NUM_INST-1:0];
  wire [PHY_DATA_WIDTH-1:0]         retry_phy_wdata_w [NUM_INST-1:0];
  wire                              retry_phy_wdata_vld_early_w [NUM_INST-1:0];
  wire                              retry_dfi_rddata_en_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]       retry_dfi_wrdata_en_w [NUM_INST-1:0];
  wire [`MEMC_NUM_RANKS-1:0]        reg_ddrc_active_ranks_int_w [NUM_INST-1:0];
  wire                              gs_pi_data_pipeline_empty_w [NUM_INST-1:0];
  wire                              mrr_op_on_w [NUM_INST-1:0];
  wire                              pi_gs_mpr_mode_w [NUM_INST-1:0];

  wire                              ih_busy_w [NUM_INST-1:0];
  wire [NUM_LRANKS-1:0]             reg_ddrc_ext_rank_refresh_w [NUM_INST-1:0];
  wire                              pi_gs_dll_off_mode_w [NUM_INST-1:0];
  wire [2:0]                        reg_ddrc_fgr_mode_gated_w [NUM_INST-1:0];
  wire                              ddrc_phy_cal_dl_enable_w [NUM_INST-1:0];
  wire                              gs_pi_op_is_exit_selfref_w [NUM_INST-1:0];
  wire                              te_wu_ie_flowctrl_req_w [NUM_INST-1:0];
  wire                              ih_ie_busy_w[NUM_INST-1:0];
  wire [1:0]                        hif_wrecc_credit_w[NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH:0]        ddrc_reg_dbg_wrecc_q_depth_w[NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH:0]        ddrc_core_reg_dbg_wrecc_q_depth_w[NUM_INST-1:0];
  wire                              perf_ie_blk_hazard_w[NUM_INST-1:0];

  wire                              perf_op_is_crit_ref_w [NUM_INST-1:0];
  wire                              perf_op_is_spec_ref_w [NUM_INST-1:0];
  wire                              core_derate_temp_limit_intr_w [NUM_INST-1:0];
  wire [BSM_BITS:0]                 ddrc_reg_max_num_alloc_bsm_w [NUM_INST-1:0];
  wire [RD_CAM_ADDR_WIDTH+1:0]      ddrc_reg_max_num_unalloc_entries_w [NUM_INST-1:0];

  wire [REFRESH_RATE_RANK_WIDTH-1:0]   ddrc_reg_refresh_rate_rank0_w [NUM_INST-1:0];
  wire [REFRESH_RATE_RANK_WIDTH-1:0]   ddrc_reg_refresh_rate_rank1_w [NUM_INST-1:0];
  wire [REFRESH_RATE_RANK_WIDTH-1:0]   ddrc_reg_refresh_rate_rank2_w [NUM_INST-1:0];
  wire [REFRESH_RATE_RANK_WIDTH-1:0]   ddrc_reg_refresh_rate_rank3_w [NUM_INST-1:0];
  wire [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank0_w [NUM_INST-1:0];
  wire [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank1_w [NUM_INST-1:0];
  wire [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank2_w [NUM_INST-1:0];
  wire [DERATE_TEMP_LIMIT_INTR_STS_RANK_WIDTH-1:0]   ddrc_reg_derate_temp_limit_intr_sts_rank3_w [NUM_INST-1:0];

   wire [2:0]                       dqsosc_state_w [NUM_INST-1:0];
   wire                             dfi_snoop_running_w [NUM_INST-1:0];
   wire [NUM_RANKS-1:0]             dqsosc_per_rank_stat_w [NUM_INST-1:0];
   wire                             pi_rt_rd_mrr_snoop_w [NUM_INST-1:0];
   wire [3:0]                       pi_ph_snoop_en_w [NUM_INST-1:0];
   wire                             ddrc_reg_dfi0_ctrlmsg_req_busy_w [NUM_INST-1:0];
   wire                             ddrc_reg_dfi0_ctrlmsg_resp_tout_w [NUM_INST-1:0];
   wire                             dfi_ctrlmsg_req_w [NUM_INST-1:0];
   wire [DFI_CTRLMSG_CMD_WIDTH-1:0] dfi_ctrlmsg_w [NUM_INST-1:0];
   wire [DFI_CTRLMSG_DATA_WIDTH-1:0] dfi_ctrlmsg_data_w [NUM_INST-1:0];

   wire                              ih_wu_is_retry_wr_w [NUM_INST-1:0];
   wire [PW_WORD_CNT_WD_MAX-1:0]     ih_wu_wr_pw_num_beats_m1_w [NUM_INST-1:0];
   wire                              retryctrl_head_exp_w [NUM_INST-1:0];
   wire                              capar_retry_start_w [NUM_INST-1:0];
   wire                              capar_rd_expired_w [NUM_INST-1:0];
   wire                              capar_rddata_en_w [NUM_INST-1:0];

   wire [DBG_MR4_BYTE_WIDTH-1:0]    ddrc_reg_dbg_mr4_byte0_w [NUM_INST-1:0];
   wire [DBG_MR4_BYTE_WIDTH-1:0]    ddrc_reg_dbg_mr4_byte1_w [NUM_INST-1:0];
   wire [DBG_MR4_BYTE_WIDTH-1:0]    ddrc_reg_dbg_mr4_byte2_w [NUM_INST-1:0];
   wire [DBG_MR4_BYTE_WIDTH-1:0]    ddrc_reg_dbg_mr4_byte3_w [NUM_INST-1:0];

   wire [DBG_RAA_CNT_WIDTH-1:0]     ddrc_reg_dbg_raa_cnt_w [NUM_INST-1:0];
   wire [NUM_RANKS-1:0]             ddrc_reg_rank_raa_cnt_gt0_w [NUM_INST-1:0];

   wire [NUM_RANKS-1:0]             bsm_clk_en_w [NUM_INST-1:0];
   wire                             dbg_capar_retry_pulse_w [NUM_INST-1:0];
   wire                             ddrc_reg_ppr_done_w [NUM_INST-1:0];


   assign dqsosc_state = dqsosc_state_w[0];
   assign dqsosc_per_rank_stat = dqsosc_per_rank_stat_w[0];
   assign o_pi_ddrc_cpedpif.pi_rt_rd_mrr_snoop = pi_rt_rd_mrr_snoop_w[0];
   assign o_pi_ddrc_cpedpif.pi_ph_snoop_en     = pi_ph_snoop_en_w[0];
   //assign o_pi_cpedpif.pi_ph_dfi_rddata_en = pi_ph_dfi_rddata_en_w[0];

assign ddrc_reg_dbg_mr4_byte0 = ddrc_reg_dbg_mr4_byte0_w[0];
assign ddrc_reg_dbg_mr4_byte1 = ddrc_reg_dbg_mr4_byte1_w[0];
assign ddrc_reg_dbg_mr4_byte2 = ddrc_reg_dbg_mr4_byte2_w[0];
assign ddrc_reg_dbg_mr4_byte3 = ddrc_reg_dbg_mr4_byte3_w[0];

assign ddrc_reg_dbg_raa_cnt = ddrc_reg_dbg_raa_cnt_w[0];
assign ddrc_reg_rank_raa_cnt_gt0 = ddrc_reg_rank_raa_cnt_gt0_w[0];

assign bsm_clk_en = bsm_clk_en_w[0];

  wire [CMD_RSLT_WIDTH-1:0]         ddrc_reg_cmd_rslt_w    [NUM_INST-1:0];
  wire                              ddrc_reg_swcmd_lock_w  [NUM_INST-1:0];
  wire                              ddrc_reg_ducmd_lock_w  [NUM_INST-1:0];
  wire                              ddrc_reg_lccmd_lock_w  [NUM_INST-1:0];
  wire [PRANK_MODE_WIDTH-1:0]       ddrc_reg_prank3_mode_w [NUM_INST-1:0];
  wire [PRANK_MODE_WIDTH-1:0]       ddrc_reg_prank2_mode_w [NUM_INST-1:0];
  wire [PRANK_MODE_WIDTH-1:0]       ddrc_reg_prank1_mode_w [NUM_INST-1:0];
  wire [PRANK_MODE_WIDTH-1:0]       ddrc_reg_prank0_mode_w [NUM_INST-1:0];
  wire [DBG_STAT3_WIDTH-1:0]        ddrc_reg_dbg_stat3_w [NUM_INST-1:0];
  wire [DBG_STAT2_WIDTH-1:0]        ddrc_reg_dbg_stat2_w [NUM_INST-1:0];
  wire [DBG_STAT1_WIDTH-1:0]        ddrc_reg_dbg_stat1_w [NUM_INST-1:0];
  wire [DBG_STAT0_WIDTH-1:0]        ddrc_reg_dbg_stat0_w [NUM_INST-1:0];

  wire                              dch_sync_mode_o_w               [NUM_INST-1:0];
  wire                              rank_idle_state_o_w             [NUM_INST-1:0];
  wire                              rank_selfref_state_o_w          [NUM_INST-1:0];
  wire                              selfref_idle_entry_o_w          [NUM_INST-1:0];
  wire                              selfref_sw_entry_o_w            [NUM_INST-1:0];
  wire                              selfref_hw_entry_o_w            [NUM_INST-1:0];
  wire                              selfref_sw_o_w                  [NUM_INST-1:0];
  wire                              selfref_idle_exit_o_w           [NUM_INST-1:0];
  wire                              selfref_sw_exit_o_w             [NUM_INST-1:0];
  wire [3:0]                        channel_message_o_w             [NUM_INST-1:0];
  wire                              rank_selfref_operating_mode_o_w [NUM_INST-1:0];
  wire                              rank_selfref_swhw_state_o_w     [NUM_INST-1:0];
  wire                              rank_selfref_tctrl_delay_ack_o_w[NUM_INST-1:0];
  wire                              dfi_lp_selfref_tlp_resp_ack_o_w [NUM_INST-1:0];
  wire                              hw_lp_exit_idle_o_w             [NUM_INST-1:0];
  wire                              hw_lp_selfref_hw_o_w            [NUM_INST-1:0];

  wire                              pi_rd_vld_w [NUM_INST-1:0];
  wire [CMD_LEN_BITS-1:0]           pi_rd_partial_w [NUM_INST-1:0];
  wire [CORE_TAG_WIDTH-1:0]         pi_rd_tag_w [NUM_INST-1:0];
  wire                              pi_rd_mrr_ext_w [NUM_INST-1:0];
  wire                              pi_rd_addr_err_w [NUM_INST-1:0];
  wire [RMW_TYPE_BITS-1:0]          pi_rd_rmw_type_w [NUM_INST-1:0];
  wire [WR_CAM_ADDR_WIDTH-1:0]      pi_rd_wr_ram_addr_w [NUM_INST-1:0];
  wire [PAGE_BITS-1:0]              pi_rd_page_w [NUM_INST-1:0];
  wire [BLK_BITS-1:0]               pi_rd_blk_w [NUM_INST-1:0];
  wire [WORD_BITS-1:0]              pi_rd_critical_word_w [NUM_INST-1:0];
  wire [RANKBANK_BITS_FULL-1:0]     pi_rd_rankbank_w [NUM_INST-1:0];
  wire [BT_BITS-1:0]                pi_rd_ie_bt_w[NUM_INST-1:0];
  wire [IE_RD_TYPE_BITS-1:0]        pi_rd_ie_rd_type_w[NUM_INST-1:0];
  wire [IE_BURST_NUM_BITS-1:0]      pi_rd_ie_blk_burst_num_w[NUM_INST-1:0];
  wire                              pi_wr_vld_nxt_w [NUM_INST-1:0];
  wire [1:0]                        pi_wr_ph_nxt_w [NUM_INST-1:0];
  wire [NUM_RANKS-1:0]              pi_wr_cs_nxt_w [NUM_INST-1:0];
  wire                              pi_rd_vld_nxt_w [NUM_INST-1:0];
  wire [1:0]                        pi_rd_ph_nxt_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]       pi_dfi_wrdata_en_w [NUM_INST-1:0];
  wire [`MEMC_FREQ_RATIO-1:0]       pi_dfi_rddata_en_w [NUM_INST-1:0];
  wire                              pi_rd_mrr_snoop_w [NUM_INST-1:0];
  wire [3:0]                        pi_phy_snoop_en_w [NUM_INST-1:0];

  wire                              ddrc_reg_ctrlupd_err_intr_w[NUM_INST-1:0];
  wire                              ddrc_reg_mrr_data_vld_w[NUM_INST-1:0];
  wire                              ddrc_reg_rd_data_vld_w[NUM_INST-1:0];
  wire                              ddrc_reg_cmd_err_w[NUM_INST-1:0];
  wire                              ddrc_reg_cmd_done_w[NUM_INST-1:0];
  wire [CMD_MRR_DATA_WIDTH-1:0]     ddrc_reg_cmd_mrr_data_w[NUM_INST-1:0];

  wire [DU_CFGBUF_RDATA_WIDTH-1:0]    ddrc_reg_du_cfgbuf_rdata_w[NUM_INST-1:0];
  wire [DU_CMDBUF_RDATA_WIDTH-1:0]    ddrc_reg_du_cmdbuf_rdata_w[NUM_INST-1:0];
  wire [LP_CMDBUF_RDATA_WIDTH-1:0]    ddrc_reg_lp_cmdbuf_rdata_w[NUM_INST-1:0];
  wire [CAPAR_CMDBUF_RDATA_WIDTH-1:0] ddrc_reg_capar_cmdbuf_rdata_w[NUM_INST-1:0];

  wire [POWERDOWN_ONGOING_WIDTH-1:0]  ddrc_reg_powerdown_ongoing_w[NUM_INST-1:0];
  wire [SELFREF_ONGOING_WIDTH-1:0]    ddrc_reg_selfref_ongoing_w[NUM_INST-1:0];
  wire [NUM_RANKS-1:0]                dbg_prank_act_pd_w[NUM_INST-1:0];
  wire [NUM_RANKS-1:0]                dbg_prank_pre_pd_w[NUM_INST-1:0];
  wire                                dbg_du_ucode_seq_ongoing_w[NUM_INST-1:0];
  wire                                dbg_lp_ucode_seq_ongoing_w[NUM_INST-1:0];

  wire                              ddrc_reg_dfi_lp_state_w[NUM_INST-1:0];
  wire [MPSM_STATE_WIDTH-1:0]       ddrc_reg_mpsm_state_w[NUM_INST-1:0];
  wire [POWERDOWN_STATE_WIDTH-1:0]  ddrc_reg_powerdown_state_w[NUM_INST-1:0];

  wire                              ddrc_reg_du_cur_blk_set_w[NUM_INST-1:0];
  wire [DU_CUR_BLK_INDEX_WIDTH-1:0] ddrc_reg_du_cur_blk_index_w[NUM_INST-1:0];
  wire [DU_CUR_BLK_ADDR_WIDTH-1:0]  ddrc_reg_du_cur_blk_addr_w[NUM_INST-1:0];
  wire [DU_CUR_BLK_UCODE_WIDTH-1:0] ddrc_reg_du_cur_blk_ucode_w[NUM_INST-1:0];
  wire [DU_MAIN_FSM_STATE_WIDTH-1:0]          ddrc_reg_du_main_fsm_state_w[NUM_INST-1:0];

  wire [GLB_BLK_EVENTS_ONGOING_WIDTH-1:0]     ddrc_reg_glb_blk_events_ongoing_w[NUM_INST-1:0];
  wire [RANK_BLK_EVENTS_ONGOING_WIDTH-1:0]    ddrc_reg_rank_blk_events_ongoing_w[NUM_INST-1:0];
  wire [DU_MCEU_FSM_STATE_WIDTH-1:0]          ddrc_reg_du_mceu_fsm_state_w[NUM_INST-1:0];
  wire [DU_SCEU_FSM_STATE_WIDTH-1:0]          ddrc_reg_du_sceu_fsm_state_w[NUM_INST-1:0];

  wire                              ddrc_reg_caparcmd_err_intr_w[NUM_INST-1:0];
  wire [CAPARCMD_ERR_STS_WIDTH-1:0] ddrc_reg_caparcmd_err_sts_w[NUM_INST-1:0];
  wire                              ddrc_reg_lccmd_err_intr_w[NUM_INST-1:0];
  wire                              ddrc_reg_ducmd_err_intr_w[NUM_INST-1:0];
  wire                              ddrc_reg_swcmd_err_intr_w[NUM_INST-1:0];
  wire [SWCMD_ERR_STS_WIDTH-1:0]    ddrc_reg_swcmd_err_sts_w[NUM_INST-1:0];
  wire [DUCMD_ERR_STS_WIDTH-1:0]    ddrc_reg_ducmd_err_sts_w[NUM_INST-1:0];
  wire [LCCMD_ERR_STS_WIDTH-1:0]    ddrc_reg_lccmd_err_sts_w[NUM_INST-1:0];
  wire                              ddrc_reg_rfm_alert_intr_w[NUM_INST-1:0];
  wire [RFM_CMD_LOG_WIDTH-1:0]      ddrc_reg_rfm_cmd_log_w[NUM_INST-1:0];
  wire                              ddrc_reg_2n_mode_w[NUM_INST-1:0];
  wire [ECS_MR16_WIDTH-1:0]         ddrc_reg_ecs_mr16_w[NUM_INST-1:0];
  wire [ECS_MR17_WIDTH-1:0]         ddrc_reg_ecs_mr17_w[NUM_INST-1:0];
  wire [ECS_MR18_WIDTH-1:0]         ddrc_reg_ecs_mr18_w[NUM_INST-1:0];
  wire [ECS_MR19_WIDTH-1:0]         ddrc_reg_ecs_mr19_w[NUM_INST-1:0];
  wire [ECS_MR20_WIDTH-1:0]         ddrc_reg_ecs_mr20_w[NUM_INST-1:0];

  wire                                  sw_wr_data_valid_w[NUM_INST-1:0];
  wire [CORE_DATA_WIDTH-1:0]            sw_wr_data_w[NUM_INST-1:0];
  wire [CORE_DATA_WIDTH/8-1:0]          sw_wr_data_mask_w[NUM_INST-1:0];
  wire                                  ci_manual_wr_mode_w[NUM_INST-1:0];
  wire                                  ci_manual_rd_mode_w[NUM_INST-1:0];
  wire [CORE_ECC_WIDTH_DUP-1:0]         sw_wr_ecc_w[NUM_INST-1:0];
  wire [CORE_ECC_MASK_WIDTH_DUP-1:0]    sw_wr_ecc_mask_w[NUM_INST-1:0];
  wire                                  ci_wr_crc_enable_mask_n_w[NUM_INST-1:0];

  wire [RD_DATA_DQ0_WIDTH-1:0]         ddrc_reg_rd_data_dq0_w[NUM_INST-1:0];
  wire [RD_DATA_DQ1_WIDTH-1:0]         ddrc_reg_rd_data_dq1_w[NUM_INST-1:0];

  wire [ADDRMAP_LUT_RDATA1_WIDTH-1:0]  ddrc_reg_addrmap_lut_rdata1_w[NUM_INST-1:0];
  wire [ADDRMAP_LUT_RDATA0_WIDTH-1:0]  ddrc_reg_addrmap_lut_rdata0_w[NUM_INST-1:0];
  wire [ADDRMAP_RANK_VALID_WIDTH-1:0]  ddrc_reg_addrmap_rank_valid_w[NUM_INST-1:0];

  wire [DBG_RANK_CTRL_MC_CODE_0_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_code_0_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_ADDR_0_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_addr_0_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_STATE_RSM_0_WIDTH-1:0]   ddrc_reg_dbg_rank_ctrl_state_rsm_0_w [NUM_INST-1:0];
  wire [DBG_MCEU_CTRL_STATE_MCEU_0_WIDTH-1:0]  ddrc_reg_dbg_mceu_ctrl_state_mceu_0_w[NUM_INST-1:0];
  wire [DBG_SCEU_CTRL_STATE_SCEU_0_WIDTH-1:0]  ddrc_reg_dbg_sceu_ctrl_state_sceu_0_w[NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_CODE_1_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_code_1_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_ADDR_1_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_addr_1_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_STATE_RSM_1_WIDTH-1:0]   ddrc_reg_dbg_rank_ctrl_state_rsm_1_w [NUM_INST-1:0];
  wire [DBG_MCEU_CTRL_STATE_MCEU_1_WIDTH-1:0]  ddrc_reg_dbg_mceu_ctrl_state_mceu_1_w[NUM_INST-1:0];
  wire [DBG_SCEU_CTRL_STATE_SCEU_1_WIDTH-1:0]  ddrc_reg_dbg_sceu_ctrl_state_sceu_1_w[NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_CODE_2_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_code_2_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_ADDR_2_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_addr_2_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_STATE_RSM_2_WIDTH-1:0]   ddrc_reg_dbg_rank_ctrl_state_rsm_2_w [NUM_INST-1:0];
  wire [DBG_MCEU_CTRL_STATE_MCEU_2_WIDTH-1:0]  ddrc_reg_dbg_mceu_ctrl_state_mceu_2_w[NUM_INST-1:0];
  wire [DBG_SCEU_CTRL_STATE_SCEU_2_WIDTH-1:0]  ddrc_reg_dbg_sceu_ctrl_state_sceu_2_w[NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_CODE_3_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_code_3_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_MC_ADDR_3_WIDTH-1:0]     ddrc_reg_dbg_rank_ctrl_mc_addr_3_w   [NUM_INST-1:0];
  wire [DBG_RANK_CTRL_STATE_RSM_3_WIDTH-1:0]   ddrc_reg_dbg_rank_ctrl_state_rsm_3_w [NUM_INST-1:0];
  wire [DBG_MCEU_CTRL_STATE_MCEU_3_WIDTH-1:0]  ddrc_reg_dbg_mceu_ctrl_state_mceu_3_w[NUM_INST-1:0];
  wire [DBG_SCEU_CTRL_STATE_SCEU_3_WIDTH-1:0]  ddrc_reg_dbg_sceu_ctrl_state_sceu_3_w[NUM_INST-1:0];
  wire [DBG_HW_LP_STATE_HSM_WIDTH-1:0]         ddrc_reg_dbg_hw_lp_state_hsm_w       [NUM_INST-1:0];
  wire                                         ddrc_reg_dbg_dfi_lp_ctrl_ack_w       [NUM_INST-1:0];
  wire                                         ddrc_reg_dbg_dfi_lp_data_ack_w       [NUM_INST-1:0];
  wire [DBG_DFI_LP_STATE_DSM_WIDTH-1:0]        ddrc_reg_dbg_dfi_lp_state_dsm_w      [NUM_INST-1:0];
  wire [DBG_CAPAR_RETRY_MC_CODE_WIDTH-1:0]     ddrc_reg_dbg_capar_retry_mc_code_w   [NUM_INST-1:0];
  wire [DBG_CAPAR_RETRY_MC_ADDR_WIDTH-1:0]     ddrc_reg_dbg_capar_retry_mc_addr_w   [NUM_INST-1:0];
  wire [DBG_CAPAR_RETRY_STATE_CSM_WIDTH-1:0]   ddrc_reg_dbg_capar_retry_state_csm_w [NUM_INST-1:0];
  wire [DBG_CAPAR_RETRY_STATE_MCEU_WIDTH-1:0]  ddrc_reg_dbg_capar_retry_state_mceu_w[NUM_INST-1:0];
  wire [DBG_CAPAR_RETRY_STATE_SCEU_WIDTH-1:0]  ddrc_reg_dbg_capar_retry_state_sceu_w[NUM_INST-1:0];
  wire [CMDFIFO_RD_DATA_WIDTH-1:0]             ddrc_reg_cmdfifo_rd_data_w           [NUM_INST-1:0];
  wire                                         ddrc_reg_cmdfifo_overflow_w          [NUM_INST-1:0];
  wire [CMDFIFO_RECORDED_CMD_NUM_WIDTH-1:0]    ddrc_reg_cmdfifo_recorded_cmd_num_w  [NUM_INST-1:0];
  wire [CMDFIFO_WINDOW_CMD_NUM_WIDTH-1:0]      ddrc_reg_cmdfifo_window_cmd_num_w    [NUM_INST-1:0];
  wire                                         prmw_wr_expired_w [NUM_INST-1:0];

  wire [`MEMC_HIF_ADDR_WIDTH-1:0]              t_hif_addr_w[NUM_INST-1:0];

  wire                                         clk_te_en_w [NUM_INST-1:0]; 



//////////////////////////////////////////////////////////////////////////////////////
// assign outputs
//////////////////////////////////////////////////////////////////////////////////////

  assign hif_cmd_stall = hif_cmd_stall_w[0];
  assign hif_rcmd_stall = hif_rcmd_stall_w[0];
  assign hif_wcmd_stall = hif_wcmd_stall_w[0];
  assign hif_wdata_ptr_valid = hif_wdata_ptr_valid_w[0];
  assign hif_wdata_ptr = hif_wdata_ptr_w[0];
  assign hif_wdata_ptr_addr_err = hif_wdata_ptr_addr_err_w[0];
  assign hif_lpr_credit = hif_lpr_credit_w[0];
  assign hif_wr_credit = hif_wr_credit_w[0];
  assign hif_hpr_credit = hif_hpr_credit_w[0];
  assign ddrc_reg_mr_wr_busy = ddrc_reg_mr_wr_busy_w[0];
  assign ddrc_reg_zq_reset_busy = ddrc_reg_zq_reset_busy_w[0];
  assign hif_cmd_q_not_empty = hif_cmd_q_not_empty_w[0];
  assign csysack_ddrc = csysack_ddrc_w[0];
  assign cactive_ddrc = cactive_ddrc_w[0];
  assign stat_ddrc_reg_selfref_type = stat_ddrc_reg_selfref_type_w[0];
  assign stat_ddrc_reg_retry_current_state = stat_ddrc_reg_retry_current_state_w[0];
  assign dbg_dfi_ie_cmd_type = dbg_dfi_ie_cmd_type_w[0];
  assign dbg_dfi_in_retry = dbg_dfi_in_retry_w[0];
  assign ddrc_reg_num_alloc_bsm = ddrc_reg_num_alloc_bsm_w[0];
  assign perf_hif_rd_or_wr = perf_hif_rd_or_wr_w[0];
  assign perf_hif_wr = perf_hif_wr_w[0];
  assign perf_hif_rd = perf_hif_rd_w[0];
  assign perf_hif_rmw = perf_hif_rmw_w[0];
  assign perf_hif_hi_pri_rd = perf_hif_hi_pri_rd_w[0];
  assign perf_read_bypass = perf_read_bypass_w[0];
  assign perf_act_bypass = perf_act_bypass_w[0];
  assign perf_hpr_xact_when_critical = perf_hpr_xact_when_critical_w[0];
  assign perf_lpr_xact_when_critical = perf_lpr_xact_when_critical_w[0];
  assign perf_wr_xact_when_critical = perf_wr_xact_when_critical_w[0];
  assign perf_op_is_activate = perf_op_is_activate_w[0];
  assign perf_op_is_rd_or_wr = perf_op_is_rd_or_wr_w[0];
  assign perf_op_is_rd_activate = perf_op_is_rd_activate_w[0];
  assign perf_op_is_rd = perf_op_is_rd_w[0];
  assign perf_op_is_wr = perf_op_is_wr_w[0];
  assign perf_op_is_mwr = perf_op_is_mwr_w[0];
  assign perf_op_is_wr16 = perf_op_is_wr16_w[0];
  assign perf_op_is_wr32 = perf_op_is_wr32_w[0];
  assign perf_op_is_rd16 = perf_op_is_rd16_w[0];
  assign perf_op_is_rd32 = perf_op_is_rd32_w[0];
  assign perf_op_is_cas = perf_op_is_cas_w[0];
  assign perf_op_is_cas_ws = perf_op_is_cas_ws_w[0];
  assign perf_op_is_cas_ws_off  = perf_op_is_cas_ws_off_w[0];
  assign perf_op_is_cas_wck_sus = perf_op_is_cas_wck_sus_w[0];
  assign perf_op_is_enter_dsm = perf_op_is_enter_dsm_w[0];
  assign perf_op_is_rfm = perf_op_is_rfm_w[0];
  assign perf_op_is_precharge = perf_op_is_precharge_w[0];
  assign perf_precharge_for_rdwr = perf_precharge_for_rdwr_w[0];
  assign perf_precharge_for_other = perf_precharge_for_other_w[0];
  assign perf_rdwr_transitions = perf_rdwr_transitions_w[0];
  assign perf_write_combine = perf_write_combine_w[0];
  assign perf_write_combine_noecc = perf_write_combine_noecc_w[0];
  assign perf_write_combine_wrecc = perf_write_combine_wrecc_w[0];
  assign perf_war_hazard = perf_war_hazard_w[0];
  assign perf_raw_hazard = perf_raw_hazard_w[0];
  assign perf_waw_hazard = perf_waw_hazard_w[0];
  assign perf_op_is_enter_selfref = perf_op_is_enter_selfref_w[0];
  assign perf_op_is_enter_powerdown = perf_op_is_enter_powerdown_w[0];
  assign perf_op_is_enter_mpsm = perf_op_is_enter_mpsm_w[0];
  assign perf_selfref_mode = perf_selfref_mode_w[0];
  assign perf_op_is_refresh = perf_op_is_refresh_w[0];
  assign perf_op_is_load_mode = perf_op_is_load_mode_w[0];
  assign perf_op_is_zqcl = perf_op_is_zqcl_w[0];
  assign perf_op_is_zqcs = perf_op_is_zqcs_w[0];
  assign perf_rank = perf_rank_w[0];
  assign perf_bank = perf_bank_w[0];
  assign perf_bg = perf_bg_w[0];
  assign perf_cid = perf_cid_w[0];
  assign perf_bypass_rank = perf_bypass_rank_w[0];
  assign perf_bypass_bank = perf_bypass_bank_w[0];
  assign perf_bypass_bg = perf_bypass_bg_w[0];
  assign perf_bypass_cid = perf_bypass_cid_w[0];
  assign perf_bsm_alloc = perf_bsm_alloc_w[0];
  assign perf_bsm_starvation = perf_bsm_starvation_w[0];
  assign perf_num_alloc_bsm = perf_num_alloc_bsm_w[0];
  assign perf_visible_window_limit_reached_rd = perf_visible_window_limit_reached_rd_w[0];
  assign perf_visible_window_limit_reached_wr = perf_visible_window_limit_reached_wr_w[0];
  assign perf_op_is_dqsosc_mpc = perf_op_is_dqsosc_mpc_w[0];
  assign perf_op_is_dqsosc_mrr = perf_op_is_dqsosc_mrr_w[0];
  assign perf_op_is_tcr_mrr    = perf_op_is_tcr_mrr_w[0];
  assign perf_op_is_zqstart    = perf_op_is_zqstart_w[0];
  assign perf_op_is_zqlatch    = perf_op_is_zqlatch_w[0];
  assign ddrc_core_reg_dbg_operating_mode = ddrc_core_reg_dbg_operating_mode_w[0];
  assign ddrc_core_reg_dbg_global_fsm_state = ddrc_core_reg_dbg_global_fsm_state_w[0];
  assign ddrc_core_reg_dbg_init_curr_state = ddrc_core_reg_dbg_init_curr_state_w[0];
  assign ddrc_core_reg_dbg_init_next_state = ddrc_core_reg_dbg_init_next_state_w[0];
  assign ddrc_core_reg_dbg_ctrlupd_state = ddrc_core_reg_dbg_ctrlupd_state_w[0];
  assign ddrc_core_reg_dbg_lpr_q_state = ddrc_core_reg_dbg_lpr_q_state_w[0];
  assign ddrc_core_reg_dbg_hpr_q_state = ddrc_core_reg_dbg_hpr_q_state_w[0];
  assign ddrc_core_reg_dbg_wr_q_state = ddrc_core_reg_dbg_wr_q_state_w[0];
  assign ddrc_core_reg_dbg_lpr_q_depth = ddrc_core_reg_dbg_lpr_q_depth_w[0];
  assign ddrc_core_reg_dbg_hpr_q_depth = ddrc_core_reg_dbg_hpr_q_depth_w[0];
  assign ddrc_core_reg_dbg_wr_q_depth = ddrc_core_reg_dbg_wr_q_depth_w[0];
  assign ddrc_core_reg_dbg_hif_cmd_stall = ddrc_core_reg_dbg_hif_cmd_stall_w[0];
  assign ddrc_core_reg_dbg_hif_rcmd_stall = ddrc_core_reg_dbg_hif_rcmd_stall_w[0];
  assign ddrc_core_reg_dbg_hif_wcmd_stall = ddrc_core_reg_dbg_hif_wcmd_stall_w[0];

  assign ddrc_core_reg_dbg_rd_valid_rank = ddrc_core_reg_dbg_rd_valid_rank_w[0];
  assign ddrc_core_reg_dbg_rd_page_hit_rank = ddrc_core_reg_dbg_rd_page_hit_rank_w[0];
  assign ddrc_core_reg_dbg_rd_pri_rank = ddrc_core_reg_dbg_rd_pri_rank_w[0];
  assign ddrc_core_reg_dbg_wr_valid_rank = ddrc_core_reg_dbg_wr_valid_rank_w[0];
  assign ddrc_core_reg_dbg_wr_page_hit_rank = ddrc_core_reg_dbg_wr_page_hit_rank_w[0];

  assign ddrc_core_reg_dbg_wr_cam_7_0_valid = ddrc_core_reg_dbg_wr_cam_7_0_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_7_0_valid = ddrc_core_reg_dbg_rd_cam_7_0_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_15_8_valid = ddrc_core_reg_dbg_wr_cam_15_8_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_15_8_valid = ddrc_core_reg_dbg_rd_cam_15_8_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_23_16_valid = ddrc_core_reg_dbg_wr_cam_23_16_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_23_16_valid = ddrc_core_reg_dbg_rd_cam_23_16_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_31_24_valid = ddrc_core_reg_dbg_wr_cam_31_24_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_31_24_valid = ddrc_core_reg_dbg_rd_cam_31_24_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_39_32_valid = ddrc_core_reg_dbg_wr_cam_39_32_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_39_32_valid = ddrc_core_reg_dbg_rd_cam_39_32_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_47_40_valid = ddrc_core_reg_dbg_wr_cam_47_40_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_47_40_valid = ddrc_core_reg_dbg_rd_cam_47_40_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_55_48_valid = ddrc_core_reg_dbg_wr_cam_55_48_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_55_48_valid = ddrc_core_reg_dbg_rd_cam_55_48_valid_w[0];
  assign ddrc_core_reg_dbg_wr_cam_63_56_valid = ddrc_core_reg_dbg_wr_cam_63_56_valid_w[0];
  assign ddrc_core_reg_dbg_rd_cam_63_56_valid = ddrc_core_reg_dbg_rd_cam_63_56_valid_w[0];

  assign cp_dfiif.dfi_address = dfi_address_w[0];
  assign cp_dfiif.dfi_freq_ratio = dfi_freq_ratio_w[0];
  assign cp_dfiif.dfi_cke = dfi_cke_w[0];
  assign cp_dfiif.dfi_cs = dfi_cs_w[0];
  assign cp_dfiif.dfi_reset_n = dfi_reset_n_w[0];

  assign cp_dfiif.dfi_wrdata_cs = dfi_wrdata_cs_w[0];
  assign cp_dfiif.dfi_rddata_cs = dfi_rddata_cs_w[0];

  assign cp_dfiif.dfi_ctrlupd_req = dfi_ctrlupd_req_w[0];
  assign cp_dfiif.dfi_ctrlupd_type = dfi_ctrlupd_type_w[0];
  assign cp_dfiif.dfi_ctrlupd_target = dfi_ctrlupd_target_w[0];
  assign ddrc_reg_ppt2_burst_busy = ddrc_reg_ppt2_burst_busy_w[0];
  assign ddrc_reg_ppt2_state = ddrc_reg_ppt2_state_w[0];
  assign cp_dfiif.dfi_dram_clk_disable = dfi_dram_clk_disable_w[0];
  assign dfi_wck_cs = dfi_wck_cs_w [0];
  assign dfi_wck_en = dfi_wck_en_w [0];
  assign dfi_wck_toggle = dfi_wck_toggle_w [0];

  assign cp_dfiif.dfi_init_start = dfi_init_start_w[0];
  assign cp_dfiif.dfi_freq_fsp  = dfi_freq_fsp_w[0];
  assign cp_dfiif.dfi_frequency = dfi_frequency_w[0];
  assign cp_dfiif.dfi_snoop_running = dfi_snoop_running_w[0];
  assign dfi_reset_n_ref = dfi_reset_n_ref_w[0];
  assign init_mr_done_out = init_mr_done_out_w[0];



  assign retryram_din = retryram_din_w[0];
  assign retryram_waddr = retryram_waddr_w[0];
  assign retryram_raddr = retryram_raddr_w[0];
  assign retryram_re = retryram_re_w[0];
  assign retryram_we = retryram_we_w[0];
  assign retryram_mask = retryram_mask_w[0];

  assign ddrc_reg_rank_refresh_busy = ddrc_reg_rank_refresh_busy_w[0];

  assign ddrc_reg_ctrlupd_busy = ddrc_reg_ctrlupd_busy_w[0];
  assign ddrc_reg_ctrlupd_burst_busy = ddrc_reg_ctrlupd_burst_busy_w[0];
  assign ddrc_reg_capar_poison_complete = ddrc_reg_capar_poison_complete_w[0];

  assign ddrc_reg_dbg_hpr_q_depth = ddrc_reg_dbg_hpr_q_depth_w[0];
  assign ddrc_reg_dbg_lpr_q_depth = ddrc_reg_dbg_lpr_q_depth_w[0];
  assign ddrc_reg_dbg_w_q_depth = ddrc_reg_dbg_w_q_depth_w[0];
  assign ddrc_reg_dbg_stall = ddrc_reg_dbg_stall_w[0];
  assign ddrc_reg_dbg_stall_rd = ddrc_reg_dbg_stall_rd_w[0];
  assign ddrc_reg_dbg_stall_wr = ddrc_reg_dbg_stall_wr_w[0];
  assign ddrc_reg_selfref_cam_not_empty = ddrc_reg_selfref_cam_not_empty_w[0];
  assign ddrc_reg_selfref_state = ddrc_reg_selfref_state_w[0];
  assign ddrc_reg_operating_mode = ddrc_reg_operating_mode_w[0];

  assign ddrc_reg_selfref_type = ddrc_reg_selfref_type_w[0];
  assign ddrc_reg_wr_q_empty = ddrc_reg_wr_q_empty_w[0];
  assign ddrc_reg_rd_q_empty = ddrc_reg_rd_q_empty_w[0];
  assign ddrc_reg_wr_data_pipeline_empty = ddrc_reg_wr_data_pipeline_empty_w[0];
  assign ddrc_reg_rd_data_pipeline_empty = ddrc_reg_rd_data_pipeline_empty_w[0];

  assign ddrc_reg_zq_calib_short_busy = ddrc_reg_zq_calib_short_busy_w[0];
  assign hif_refresh_req_bank = hif_refresh_req_bank_w[0];
  assign hif_refresh_req = hif_refresh_req_w[0];
  assign hif_refresh_req_cnt = hif_refresh_req_cnt_w[0];
  assign hif_refresh_req_derate = hif_refresh_req_derate_w[0];
  assign hif_refresh_active = hif_refresh_active_w[0];

  assign cp_dfiif.dfi_phyupd_ack = dfi_phyupd_ack_w[0];
  assign cp_dfiif.dfi_phymstr_ack = dfi_phymstr_ack_w[0];
  assign cp_dfiif.dfi_lp_ctrl_req = dfi_lp_ctrl_req_w[0];
  assign cp_dfiif.dfi_lp_ctrl_wakeup = dfi_lp_ctrl_wakeup_w[0];
  assign cp_dfiif.dfi_lp_data_req = dfi_lp_data_req_w[0];
  assign cp_dfiif.dfi_lp_data_wakeup = dfi_lp_data_wakeup_w[0];

  assign hwffcmrw_op_s = hwffcmrw_op_s_w[0];
  assign hwffc_target_freq_en = hwffc_target_freq_en_w[0];
  assign hwffc_target_freq = hwffc_target_freq_w[0];
  assign hwffc_target_freq_init = hwffc_target_freq_init_w[0];

  assign ddrc_reg_hwffc_in_progress = ddrc_reg_hwffc_in_progress_w[0];
  assign ddrc_reg_current_frequency = ddrc_reg_current_frequency_w[0];
  assign ddrc_reg_current_fsp = ddrc_reg_current_fsp_w[0];
  assign ddrc_reg_current_vrcg = ddrc_reg_current_vrcg_w[0];
  assign ddrc_reg_hwffc_operating_mode = ddrc_reg_hwffc_operating_mode_w[0];
  assign ddrc_xpi_port_disable_req = ddrc_xpi_port_disable_req_w[0];
  assign ddrc_xpi_clock_required = ddrc_xpi_clock_required_w[0];

  assign hwffc_hif_wd_stall = hwffc_hif_wd_stall_w[0];
  assign hwffc_i_reg_ddrc_dis_auto_zq = hwffc_i_reg_ddrc_dis_auto_zq_w[0];


//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire                             ih_mr_ie_blk_wr_end;
  //wire [IE_PW_BITS-1:0]            ih_mr_ie_pw;
  wire [BRT_BITS-1:0]              ih_rd_ie_brt;
  wire                             ih_rd_ie_rd_cnt_inc;
  wire                             ih_rd_ie_blk_rd_end;
  wire [NO_OF_BWT-1:0]             ih_mr_ie_wr_cnt_dec_vct;
  wire                             ih_mr_ie_wr_cnt_inc;
  wire [BWT_BITS-1:0]              ih_mr_ie_bwt;
  wire [BRT_BITS-1:0]              ih_mr_ie_brt;
  wire                             ih_mr_ie_brt_vld;

  assign ih_mr_ie_blk_wr_end = ih_mr_ie_blk_wr_end_w[0];
  assign ih_mr_ie_pw = ih_mr_ie_pw_w[0];
  assign ih_rd_ie_brt = ih_rd_ie_brt_w[0];
  assign ih_rd_ie_rd_cnt_inc = ih_rd_ie_rd_cnt_inc_w[0];
  assign ih_rd_ie_blk_rd_end = ih_rd_ie_blk_rd_end_w[0];
  assign ih_mr_ie_wr_cnt_inc = ih_mr_ie_wr_cnt_inc_w[0];
  assign ih_mr_ie_wr_cnt_dec_vct = ih_mr_ie_wr_cnt_dec_vct_w[0];
  assign ih_mr_ie_bwt = ih_mr_ie_bwt_w[0];
  assign ih_mr_ie_brt = ih_mr_ie_brt_w[0];
  assign ih_mr_ie_brt_vld = ih_mr_ie_brt_vld_w[0];
//spyglass enable_block W528

  assign o_ih_cpfdpif.ih_mr_ie_blk_wr_end = ih_mr_ie_blk_wr_end_w[0];
  //assign ih_mr_ie_pw = ih_mr_ie_pw_w[0];
  assign o_ih_cpfdpif.ih_rd_ie_brt = ih_rd_ie_brt_w[0];
  assign o_ih_cpfdpif.ih_rd_ie_rd_cnt_inc = ih_rd_ie_rd_cnt_inc_w[0];
  assign o_ih_cpfdpif.ih_rd_ie_blk_rd_end = ih_rd_ie_blk_rd_end_w[0];
  assign o_ih_cpfdpif.ih_mr_ie_wr_cnt_inc = ih_mr_ie_wr_cnt_inc_w[0];
  assign o_ih_cpfdpif.ih_mr_ie_wr_cnt_dec_vct = ih_mr_ie_wr_cnt_dec_vct_w[0];
  assign o_ih_cpfdpif.ih_mr_ie_bwt = ih_mr_ie_bwt_w[0];
  assign o_ih_cpfdpif.ih_mr_ie_brt = ih_mr_ie_brt_w[0];
  assign o_ih_cpfdpif.ih_mr_ie_brt_vld = ih_mr_ie_brt_vld_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire [BT_BITS-1:0]               te_mr_ie_bt;
  wire [IE_WR_TYPE_BITS-1:0]       te_mr_ie_wr_type;
  wire [IE_BURST_NUM_BITS-1:0]     te_mr_ie_blk_burst_num;  //only for the Data command
  wire [34:0]                      te_mr_addr_info;

  assign te_mr_ie_bt = te_mr_ie_bt_w[0];
  assign te_mr_ie_wr_type = te_mr_ie_wr_type_w[0];
  assign te_mr_ie_blk_burst_num = te_mr_ie_blk_burst_num_w[0];
  assign te_mr_addr_info = te_mr_addr_info_w[0];
//spyglass enable_block W528

  assign o_te_cpfdpif.te_mr_ie_bt = te_mr_ie_bt_w[0];
  assign o_te_cpfdpif.te_mr_ie_wr_type = te_mr_ie_wr_type_w[0];
  assign o_te_cpfdpif.te_mr_ie_blk_burst_num = te_mr_ie_blk_burst_num_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire  [BT_BITS-1:0]              pi_rt_ie_bt;
  wire  [IE_RD_TYPE_BITS-1:0]      pi_rt_ie_rd_type;
  wire  [IE_BURST_NUM_BITS-1:0]    pi_rt_ie_blk_burst_num;  //only for the Data command

  assign pi_rt_ie_bt = pi_rt_ie_bt_w[0];
  assign pi_rt_ie_rd_type = pi_rt_ie_rd_type_w[0];
  assign pi_rt_ie_blk_burst_num = pi_rt_ie_blk_burst_num_w[0];
//spyglass enable_block W528

  assign o_pi_ddrc_cpedpif.pi_rt_ie_bt = pi_rt_ie_bt_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_ie_rd_type = pi_rt_ie_rd_type_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_ie_blk_burst_num = pi_rt_ie_blk_burst_num_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire [BWT_BITS-1:0]              ih_mr_lkp_bwt;
  wire                             ih_mr_lkp_bwt_vld;
  wire [BRT_BITS-1:0]              ih_mr_lkp_brt;
  wire                             ih_mr_lkp_brt_vld;
  wire [BRT_BITS-1:0]              ih_rd_lkp_brt;
//  wire                             ih_rd_lkp_brt_vld;
  wire [BWT_BITS-1:0]              ih_rd_lkp_bwt;
  wire                             ih_rd_lkp_bwt_vld;

  assign ih_mr_lkp_bwt = ih_mr_lkp_bwt_w[0];
  assign ih_mr_lkp_bwt_vld = ih_mr_lkp_bwt_vld_w[0];
  assign ih_mr_lkp_brt = ih_mr_lkp_brt_w[0];
  assign ih_mr_lkp_brt_vld = ih_mr_lkp_brt_vld_w[0];
  assign ih_rd_lkp_brt = ih_rd_lkp_brt_w[0];
  assign ih_rd_lkp_brt_vld = ih_rd_lkp_brt_vld_w[0];
  assign ih_rd_lkp_bwt = ih_rd_lkp_bwt_w[0];
  assign ih_rd_lkp_bwt_vld = ih_rd_lkp_bwt_vld_w[0];
//spyglass enable_block W528

  assign o_ih_cpfdpif.ih_mr_lkp_bwt = ih_mr_lkp_bwt_w[0];
  assign o_ih_cpfdpif.ih_mr_lkp_bwt_vld = ih_mr_lkp_bwt_vld_w[0];
  assign o_ih_cpfdpif.ih_mr_lkp_brt = ih_mr_lkp_brt_w[0];
  assign o_ih_cpfdpif.ih_mr_lkp_brt_vld = ih_mr_lkp_brt_vld_w[0];
  assign o_ih_cpfdpif.ih_rd_lkp_brt = ih_rd_lkp_brt_w[0];
  //assign ih_rd_lkp_brt_vld = ih_rd_lkp_brt_vld_w[0];
  assign o_ih_cpfdpif.ih_rd_lkp_bwt = ih_rd_lkp_bwt_w[0];
  assign o_ih_cpfdpif.ih_rd_lkp_bwt_vld = ih_rd_lkp_bwt_vld_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire                             te_mr_eccap;
  wire                             pi_rt_eccap;

  assign te_mr_eccap = te_mr_eccap_w[0];
  assign pi_rt_eccap = pi_rt_eccap_w[0];
//spyglass enable_block W528

  assign o_te_cpfdpif.te_mr_eccap = te_mr_eccap_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_eccap = pi_rt_eccap_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire  [`MEMC_DCERRFIELD]         ih_wu_cerr;
  assign ih_wu_cerr = ih_wu_cerr_w[0];
//spyglass enable_block W528


//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire                                 ih_wu_wr_valid_addr_err;
  wire [`DDRCTL_EAPAR_SIZE-1:0]        ih_wu_wr_eapar;
  wire                                 pi_rt_rd_addr_err;

  assign ih_wu_wr_valid_addr_err = ih_wu_wr_valid_addr_err_w[0];
  assign ih_wu_wr_eapar = ih_wu_wr_eapar_w[0];
  assign pi_rt_rd_addr_err = pi_rt_rd_addr_err_w[0];
//spyglass enable_block W528

  assign o_pi_ddrc_cpedpif.pi_rt_rd_mrr = pi_rt_rd_mrr_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_rd_mrr_ext = pi_rt_rd_mrr_ext_w[0];
  assign o_pi_ddrc_cpedpif.pi_ph_dfi_rddata_en = pi_ph_dfi_rddata_en_w[0];
  assign o_pi_ddrc_cpedpif.pi_ph_dfi_wrdata_en = pi_ph_dfi_wrdata_en_w[0];
  assign o_ih_cpfdpif.ih_wu_wr_valid = ih_wu_wr_valid_w[0];
  assign o_ih_cpfdpif.ih_wu_wr_valid_addr_err = ih_wu_wr_valid_addr_err_w[0];

  assign ih_te_rd_valid = ih_te_rd_valid_w[0];
  assign ih_te_wr_valid = ih_te_wr_valid_w[0];
  assign o_ih_cpfdpif.ih_wu_rmw_type = ih_wu_rmw_type_w[0];
  assign o_ih_cpfdpif.ih_wu_wr_entry = ih_wu_wr_entry_w[0];
  assign o_ih_cpfdpif.ih_wu_critical_word = ih_wu_critical_word_w[0];
  assign pi_gs_geardown_mode_on = pi_gs_geardown_mode_on_w[0];

  assign o_pi_ddrc_cpedpif.pi_rt_rd_partial = pi_rt_rd_partial_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_rd_vld = pi_rt_rd_vld_w[0];

  assign o_pi_ddrc_cpedpif.pi_rt_rd_tag = pi_rt_rd_tag_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_rd_addr_err = pi_rt_rd_addr_err_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire [WR_CAM_ADDR_WIDTH-1:0]         pi_rt_wr_ram_addr;
  wire [CMD_RMW_BITS-1:0]              pi_rt_rmwcmd;           // atomic RMW command instruction
  wire [RMW_TYPE_BITS-1:0]             pi_rt_rmwtype;          // RMW type (scrub, partial write, atomic RMW cmd, none)

  assign pi_rt_wr_ram_addr = pi_rt_wr_ram_addr_w[0];
  assign pi_rt_rmwcmd = pi_rt_rmwcmd_w[0];
  assign pi_rt_rmwtype = pi_rt_rmwtype_w[0];
//spyglass enable_block W528

  assign o_pi_ddrc_cpedpif.pi_rt_wr_ram_addr = pi_rt_wr_ram_addr_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_rmwcmd = pi_rt_rmwcmd_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_rmwtype = pi_rt_rmwtype_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_rankbank_num = pi_rt_rankbank_num_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_page_num = pi_rt_page_num_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_block_num = pi_rt_block_num_w[0];
  assign o_pi_ddrc_cpedpif.pi_rt_critical_word = pi_rt_critical_word_w[0];



//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire                                 te_yy_wr_combine;       // also goes to IH/WU
  assign te_yy_wr_combine = te_yy_wr_combine_w[0];
//spyglass enable_block W528
  assign o_te_cpfdpif.te_yy_wr_combine = te_yy_wr_combine_w[0];

  assign ts_pi_mwr = ts_pi_mwr_w[0];

  assign ts_pi_wr32     = ts_pi_wr32_w[0];
  assign ts_pi_2nd_half = ts_pi_2nd_half_w[0];
  assign ts_cam_clear_en = ts_cam_clear_en_w[0];

  assign te_wu_wrdata_stall_req = te_wu_wrdata_stall_req_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire [PARTIAL_WR_BITS-1:0]              te_pi_wr_word_valid;

  assign te_pi_wr_word_valid = te_pi_wr_word_valid_w[0];
//spyglass enable_block W528

  assign o_te_cpfdpif.te_pi_wr_word_valid = te_pi_wr_word_valid_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire [2:0]                              gs_pi_rdwr_bc_sel;
  wire [PARTIAL_WR_BITS_LOG2-1:0]         gs_pi_rdwr_ram_raddr_lsb_first;
  wire [PW_WORD_CNT_WD_MAX-1:0]           gs_pi_rdwr_pw_num_beats_m1;

  assign gs_pi_rdwr_bc_sel = gs_pi_rdwr_bc_sel_w[0];

  assign gs_pi_rdwr_ram_raddr_lsb_first = gs_pi_rdwr_ram_raddr_lsb_first_w[0];
  assign gs_pi_rdwr_pw_num_beats_m1     = gs_pi_rdwr_pw_num_beats_m1_w[0];
//spyglass enable_block W528

  assign o_gs_ddrc_cpedpif.gs_pi_rdwr_ram_raddr_lsb_first = gs_pi_rdwr_ram_raddr_lsb_first_w[0];
  assign o_gs_ddrc_cpedpif.gs_pi_rdwr_pw_num_beats_m1     = gs_pi_rdwr_pw_num_beats_m1_w[0];

  assign o_te_cpfdpif.te_mr_wr_ram_addr = te_mr_wr_ram_addr_w[0];
  assign o_te_cpfdpif.te_wu_entry_num = te_wu_entry_num_w[0];
  assign o_te_cpfdpif.te_wu_wr_retry = te_wu_wr_retry_w[0];
  assign o_gs_ddrc_cpedpif.gs_mr_write = gs_mr_write_w[0];

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire                                    gs_mr_load_mode_pda;
  wire   [1:0]                            gs_mr_pda_data_sel;  // 00:Normal data  01: MRS to enter PDA mode  10: MRS in PDA mode  11: MRS to exit PDA mode

  assign gs_mr_load_mode_pda = gs_mr_load_mode_pda_w[0];
  assign gs_mr_pda_data_sel = gs_mr_pda_data_sel_w[0];
//spyglass enable_block W528


//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
  wire                                    pda_mode;            // PDA mode (between 1st MRS and last MRS's tMod)
  wire                                    pda_mode_pre;        // PDA mode (between 1st MRS and last MRS's t_mod) assert 1cycle earlier than pda_mode

  assign pda_mode = pda_mode_w[0];
  assign pda_mode_pre = pda_mode_pre_w[0];
//spyglass enable_block W528










  assign gs_pi_cs_n = gs_pi_cs_n_w[0];
  assign retry_fifo_empty = retry_fifo_empty_w[0];
  assign retry_rt_rdatavld_gate_en = retry_rt_rdatavld_gate_en_w[0];
  assign retry_rt_fifo_init_n = retry_rt_fifo_init_n_w[0];
  assign retry_rt_fatl_err_pulse = retry_rt_fatl_err_pulse_w[0];
  assign retry_rt_now_sw_intervention = retry_rt_now_sw_intervention_w[0];
  assign retry_rt_rd_timeout_value = retry_rt_rd_timeout_value_w[0];

  assign retry_dfi_sel = retry_dfi_sel_w[0];
  assign retry_phy_dm = retry_phy_dm_w[0];
  assign retry_phy_wdata = retry_phy_wdata_w[0];
  assign retry_phy_wdata_vld_early = retry_phy_wdata_vld_early_w[0];
  assign retry_dfi_rddata_en = retry_dfi_rddata_en_w[0];
  assign retry_dfi_wrdata_en = retry_dfi_wrdata_en_w[0];
  assign reg_ddrc_active_ranks_int = reg_ddrc_active_ranks_int_w[0];
  assign gs_pi_data_pipeline_empty = gs_pi_data_pipeline_empty_w[0];
  assign mrr_op_on = mrr_op_on_w[0];
  assign pi_gs_mpr_mode = pi_gs_mpr_mode_w[0];

  assign ih_busy = ih_busy_w[0];
  assign reg_ddrc_ext_rank_refresh = reg_ddrc_ext_rank_refresh_w[0];
  assign pi_gs_dll_off_mode = pi_gs_dll_off_mode_w[0];
  assign reg_ddrc_fgr_mode_gated = reg_ddrc_fgr_mode_gated_w[0];
  assign ddrc_phy_cal_dl_enable = ddrc_phy_cal_dl_enable_w[0];
  assign gs_pi_op_is_exit_selfref = gs_pi_op_is_exit_selfref_w[0];


  assign perf_op_is_crit_ref = perf_op_is_crit_ref_w[0];
  assign perf_op_is_spec_ref = perf_op_is_spec_ref_w[0];

  assign core_derate_temp_limit_intr = core_derate_temp_limit_intr_w[0];

  assign ddrc_reg_refresh_rate_rank0 = ddrc_reg_refresh_rate_rank0_w[0];
  assign ddrc_reg_refresh_rate_rank1 = ddrc_reg_refresh_rate_rank1_w[0];
  assign ddrc_reg_refresh_rate_rank2 = ddrc_reg_refresh_rate_rank2_w[0];
  assign ddrc_reg_refresh_rate_rank3 = ddrc_reg_refresh_rate_rank3_w[0];
  assign ddrc_reg_derate_temp_limit_intr_sts_rank0 = ddrc_reg_derate_temp_limit_intr_sts_rank0_w[0];
  assign ddrc_reg_derate_temp_limit_intr_sts_rank1 = ddrc_reg_derate_temp_limit_intr_sts_rank1_w[0];
  assign ddrc_reg_derate_temp_limit_intr_sts_rank2 = ddrc_reg_derate_temp_limit_intr_sts_rank2_w[0];
  assign ddrc_reg_derate_temp_limit_intr_sts_rank3 = ddrc_reg_derate_temp_limit_intr_sts_rank3_w[0];

  assign o_te_cpfdpif.te_wu_ie_flowctrl_req = te_wu_ie_flowctrl_req_w[0];
  assign ih_ie_busy = ih_ie_busy_w[0];
  assign hif_wrecc_credit = hif_wrecc_credit_w[0];
  assign ddrc_reg_dbg_wrecc_q_depth = ddrc_reg_dbg_wrecc_q_depth_w[0];
  assign ddrc_core_reg_dbg_wrecc_q_depth = ddrc_core_reg_dbg_wrecc_q_depth_w[0];
  assign perf_ie_blk_hazard = perf_ie_blk_hazard_w[0];

  assign ddrc_reg_max_num_alloc_bsm        = ddrc_reg_max_num_alloc_bsm_w[0];
  assign ddrc_reg_max_num_unalloc_entries  = ddrc_reg_max_num_unalloc_entries_w[0];
  assign ddrc_reg_ppr_done                    = ddrc_reg_ppr_done_w[0];
  assign clk_te_en                            = clk_te_en_w[0];


  generate
    for (n=0; n<NUM_INST; n=n+1) begin: ddrc_ctrl_inst
    dwc_ddrctl_ddrc_cp
    
        #(

          .CHANNEL_NUM                    (CHANNEL_NUM),
          .SHARED_AC                      (SHARED_AC),
          .SHARED_AC_INTERLEAVE           (SHARED_AC_INTERLEAVE),
          .BCM_VERIF_EN                   (BCM_VERIF_EN),
          .BCM_DDRC_N_SYNC                (BCM_DDRC_N_SYNC),
          .MEMC_ECC_SUPPORT               (MEMC_ECC_SUPPORT),
          .UMCTL2_SEQ_BURST_MODE          (UMCTL2_SEQ_BURST_MODE),
          .UMCTL2_PHY_SPECIAL_IDLE        (UMCTL2_PHY_SPECIAL_IDLE),
          .OCPAR_EN                       (OCPAR_EN),
          .NPORTS                         (NPORTS),
          .NPORTS_LG2                     (NPORTS_LG2),
          .A_SYNC_TABLE                   (A_SYNC_TABLE),
          .RD_CAM_ADDR_WIDTH              (RD_CAM_ADDR_WIDTH),
          .WR_CAM_ADDR_WIDTH              (WR_CAM_ADDR_WIDTH),
          .WR_ECC_CAM_ADDR_WIDTH          (WR_ECC_CAM_ADDR_WIDTH),
          .WR_CAM_ADDR_WIDTH_IE           (WR_CAM_ADDR_WIDTH_IE),
          .MAX_CAM_ADDR_WIDTH             (MAX_CAM_ADDR_WIDTH),
          .RD_CAM_ENTRIES                 (RD_CAM_ENTRIES),
          .WR_CAM_ENTRIES                 (WR_CAM_ENTRIES),
          .WR_ECC_CAM_ENTRIES             (WR_ECC_CAM_ENTRIES),
          .WR_CAM_ENTRIES_IE              (WR_CAM_ENTRIES_IE),

          .CORE_DATA_WIDTH                (CORE_DATA_WIDTH),
          .CORE_ADDR_WIDTH                (CORE_ADDR_WIDTH),
          .CORE_ADDR_INT_WIDTH            (CORE_ADDR_INT_WIDTH),
          .CORE_TAG_WIDTH                 (CORE_TAG_WIDTH),

          // widths used for some outputs of ddrc_ctrl that would be
          // [X-1:0]=>[-1:0]
          // wide otherwise as X=0
          .RANK_BITS_DUP                  (RANK_BITS_DUP),
          .LRANK_BITS_DUP                 (LRANK_BITS_DUP),
          .BG_BITS_DUP                    (BG_BITS_DUP),
          .CID_WIDTH_DUP                  (CID_WIDTH_DUP),

          .RANK_BITS                      (RANK_BITS),
          .LRANK_BITS                     (LRANK_BITS),
          .CID_WIDTH                      (CID_WIDTH),
          .BG_BITS                        (BG_BITS),
          .BG_BANK_BITS                   (BG_BANK_BITS),
          .BANK_BITS                      (BANK_BITS),
          .PAGE_BITS                      (PAGE_BITS),
          .WORD_BITS                      (WORD_BITS),
          .BLK_BITS                       (BLK_BITS),
          .BSM_BITS                       (BSM_BITS),

          .MRS_A_BITS                     (MRS_A_BITS),
          .MRS_BA_BITS                    (MRS_BA_BITS),
          .PHY_ADDR_BITS                  (PHY_ADDR_BITS),

          .NUM_TOTAL_BANKS                (NUM_TOTAL_BANKS),
          .NUM_RANKS                      (NUM_RANKS),
          .NUM_LRANKS                     (NUM_LRANKS),
          .NUM_TOTAL_BSMS                 (NUM_TOTAL_BSMS),
          .NUM_PHY_DRAM_CLKS              (NUM_PHY_DRAM_CLKS),

          .PHY_DATA_WIDTH                 (PHY_DATA_WIDTH),
          .PHY_MASK_WIDTH                 (PHY_MASK_WIDTH),

          .CORE_ECC_WIDTH_DUP             (CORE_ECC_WIDTH_DUP),
          .CORE_ECC_MASK_WIDTH_DUP        (CORE_ECC_MASK_WIDTH_DUP),

          .MWR_BITS                       (MWR_BITS),

          .PARTIAL_WR_BITS                (PARTIAL_WR_BITS),

          .NUM_LANES                      (NUM_LANES),
          .PARITY_IN_WIDTH                (PARITY_IN_WIDTH),

          .RETRY_MAX_ADD_RD_LAT_LG2       (RETRY_MAX_ADD_RD_LAT_LG2),
          .CMD_LEN_BITS                   (CMD_LEN_BITS),
          .FATL_CODE_BITS                 (FATL_CODE_BITS),

          .WRDATA_CYCLES                  (WRDATA_CYCLES),
          // localparams in ddrc.v
          .CMD_TYPE_BITS (CMD_TYPE_BITS),
          .WDATA_PTR_BITS (WDATA_PTR_BITS),
          .CMD_RMW_BITS (CMD_RMW_BITS),
          .RMW_TYPE_BITS (RMW_TYPE_BITS),

          .PARTIAL_WR_BITS_LOG2 (PARTIAL_WR_BITS_LOG2),
          .PW_NUM_DB (PW_NUM_DB),

          .PW_FACTOR_HBW (PW_FACTOR_HBW),
          .PW_FACTOR_FBW (PW_FACTOR_FBW),

          .PW_WORD_VALID_WD_HBW (PW_WORD_VALID_WD_HBW),
          .PW_WORD_VALID_WD_FBW (PW_WORD_VALID_WD_FBW),

          .PW_WORD_VALID_WD_MAX (PW_WORD_VALID_WD_MAX),

          .PW_WORD_CNT_WD_MAX (PW_WORD_CNT_WD_MAX),

          .RANKBANK_BITS_FULL (RANKBANK_BITS_FULL),
          .RD_LATENCY_BITS (RD_LATENCY_BITS),
          .NO_OF_BT               (NO_OF_BT         ),
          .NO_OF_BWT              (NO_OF_BWT        ),
          .NO_OF_BRT              (NO_OF_BRT        ),
          .BT_BITS                (BT_BITS          ),
          .BWT_BITS               (BWT_BITS         ),
          .BRT_BITS               (BRT_BITS         ),
          .NO_OF_BLK_CHN          (NO_OF_BLK_CHN    ),
          .BLK_CHN_BITS           (BLK_CHN_BITS     ),
          .IE_RD_TYPE_BITS        (IE_RD_TYPE_BITS  ),
          .IE_WR_TYPE_BITS        (IE_WR_TYPE_BITS  ),
          .IE_BURST_NUM_BITS      (IE_BURST_NUM_BITS),

          .MAX_CMD_DELAY          (MAX_CMD_DELAY    ),
          .AM_DCH_WIDTH           (AM_DCH_WIDTH     ),
          .AM_CS_WIDTH            (AM_CS_WIDTH      ),
          .AM_CID_WIDTH           (AM_CID_WIDTH     ),
          .AM_BANK_WIDTH          (AM_BANK_WIDTH    ),
          .AM_BG_WIDTH            (AM_BG_WIDTH      ),
          .AM_ROW_WIDTH           (AM_ROW_WIDTH     ),
          .AM_COL_WIDTH_H         (AM_COL_WIDTH_H   ),
          .AM_COL_WIDTH_L         (AM_COL_WIDTH_L   ),
          .CMD_DELAY_BITS         (CMD_DELAY_BITS   ),
          .HIF_KEYID_WIDTH        (HIF_KEYID_WIDTH  )
         )
   U_ddrc_cp(

    // outputs
    .hif_cmd_stall (hif_cmd_stall_w[n]),
    .hif_rcmd_stall (hif_rcmd_stall_w[n]),
    .hif_wcmd_stall (hif_wcmd_stall_w[n]),
    .hif_wdata_ptr_valid (hif_wdata_ptr_valid_w[n]),
    .hif_wdata_ptr (hif_wdata_ptr_w[n]),
    .hif_wdata_ptr_addr_err (hif_wdata_ptr_addr_err_w[n]),
    .hif_lpr_credit (hif_lpr_credit_w[n]),
    .hif_wr_credit (hif_wr_credit_w[n]),
    .hif_hpr_credit (hif_hpr_credit_w[n]),
    //spyglass disable_block W528
    //SMD: A signal or variable is set but never read
    //SJ: Used in generate block
    .ddrc_reg_addrmap_lut_rdata1 (ddrc_reg_addrmap_lut_rdata1_w[n]),
    .ddrc_reg_addrmap_lut_rdata0 (ddrc_reg_addrmap_lut_rdata0_w[n]),
    .ddrc_reg_addrmap_rank_valid (ddrc_reg_addrmap_rank_valid_w[n]),
    .ddrc_reg_pda_done (ddrc_reg_pda_done_w[n]),
    //spyglass enable_block W528
    .ddrc_reg_mr_wr_busy (ddrc_reg_mr_wr_busy_w[n]),
    .ddrc_reg_zq_reset_busy (ddrc_reg_zq_reset_busy_w[n]),
    .hif_cmd_q_not_empty (hif_cmd_q_not_empty_w[n]),
    .csysack_ddrc (csysack_ddrc_w[n]),
    .cactive_ddrc (cactive_ddrc_w[n]),
    .stat_ddrc_reg_selfref_type (stat_ddrc_reg_selfref_type_w[n]),
    .stat_ddrc_reg_retry_current_state (stat_ddrc_reg_retry_current_state_w[n]),
    .dbg_dfi_ie_cmd_type (dbg_dfi_ie_cmd_type_w[n]),
    .dbg_dfi_in_retry (dbg_dfi_in_retry_w[n]),
    //spyglass disable_block W528
    //SMD: A signal or variable is set but never read
    //SJ: Used in generate block
    .pi_rd_crc_retry_limit_reach_pre (pi_rd_crc_retry_limit_reach_pre_w[n]),
    .pi_rt_rd_crc_retry_limit_reach_pre (pi_rt_rd_crc_retry_limit_reach_pre_w[n]),
    .pi_rd_ue_retry_limit_reach_pre (pi_rd_ue_retry_limit_reach_pre_w[n]),
    .pi_rt_rd_ue_retry_limit_reach_pre (pi_rt_rd_ue_retry_limit_reach_pre_w[n]),
    //spyglass enable_block W528
    .ddrc_reg_num_alloc_bsm (ddrc_reg_num_alloc_bsm_w[n]),
    .perf_hif_rd_or_wr (perf_hif_rd_or_wr_w[n]),
    .perf_hif_wr (perf_hif_wr_w[n]),
    .perf_hif_rd (perf_hif_rd_w[n]),
    .perf_hif_rmw (perf_hif_rmw_w[n]),
    .perf_hif_hi_pri_rd (perf_hif_hi_pri_rd_w[n]),
    .perf_read_bypass (perf_read_bypass_w[n]),
    .perf_act_bypass (perf_act_bypass_w[n]),
    .perf_hpr_xact_when_critical (perf_hpr_xact_when_critical_w[n]),
    .perf_lpr_xact_when_critical (perf_lpr_xact_when_critical_w[n]),
    .perf_wr_xact_when_critical (perf_wr_xact_when_critical_w[n]),
    .perf_op_is_activate (perf_op_is_activate_w[n]),
    .perf_op_is_rd_or_wr (perf_op_is_rd_or_wr_w[n]),
    .perf_op_is_rd_activate (perf_op_is_rd_activate_w[n]),
    .perf_op_is_rd (perf_op_is_rd_w[n]),
    .perf_op_is_wr (perf_op_is_wr_w[n]),
    .perf_op_is_mwr (perf_op_is_mwr_w[n]),
    .perf_op_is_wr16 (perf_op_is_wr16_w[n]),
    .perf_op_is_wr32 (perf_op_is_wr32_w[n]),
    .perf_op_is_rd16 (perf_op_is_rd16_w[n]),
    .perf_op_is_rd32 (perf_op_is_rd32_w[n]),
    .perf_op_is_cas (perf_op_is_cas_w[n]),
    .perf_op_is_cas_ws (perf_op_is_cas_ws_w[n]),
    .perf_op_is_cas_ws_off  (perf_op_is_cas_ws_off_w[n]),
    .perf_op_is_cas_wck_sus (perf_op_is_cas_wck_sus_w[n]),
    .perf_op_is_enter_dsm (perf_op_is_enter_dsm_w[n]),
    .perf_op_is_rfm (perf_op_is_rfm_w[n]),
    .perf_op_is_precharge (perf_op_is_precharge_w[n]),
    .perf_precharge_for_rdwr (perf_precharge_for_rdwr_w[n]),
    .perf_precharge_for_other (perf_precharge_for_other_w[n]),
    .perf_rdwr_transitions (perf_rdwr_transitions_w[n]),
    .perf_write_combine (perf_write_combine_w[n]),
    .perf_write_combine_noecc (perf_write_combine_noecc_w[n]),
    .perf_write_combine_wrecc (perf_write_combine_wrecc_w[n]),
    .perf_war_hazard (perf_war_hazard_w[n]),
    .perf_raw_hazard (perf_raw_hazard_w[n]),
    .perf_waw_hazard (perf_waw_hazard_w[n]),
    .perf_op_is_enter_selfref (perf_op_is_enter_selfref_w[n]),
    .perf_op_is_enter_powerdown (perf_op_is_enter_powerdown_w[n]),
    .perf_op_is_enter_mpsm (perf_op_is_enter_mpsm_w[n]),
    .perf_selfref_mode (perf_selfref_mode_w[n]),
    .perf_op_is_refresh (perf_op_is_refresh_w[n]),
    .perf_op_is_load_mode (perf_op_is_load_mode_w[n]),
    .perf_op_is_zqcl (perf_op_is_zqcl_w[n]),
    .perf_op_is_zqcs (perf_op_is_zqcs_w[n]),
    .perf_rank (perf_rank_w[n]),
    .perf_bank (perf_bank_w[n]),
    .perf_bg (perf_bg_w[n]),
    .perf_cid (perf_cid_w[n]),
    .perf_bypass_rank (perf_bypass_rank_w[n]),
    .perf_bypass_bank (perf_bypass_bank_w[n]),
    .perf_bypass_bg (perf_bypass_bg_w[n]),
    .perf_bypass_cid (perf_bypass_cid_w[n]),
    .perf_bsm_alloc (perf_bsm_alloc_w[n]),
    .perf_bsm_starvation (perf_bsm_starvation_w[n]),
    .perf_num_alloc_bsm (perf_num_alloc_bsm_w[n]),
    .perf_visible_window_limit_reached_rd (perf_visible_window_limit_reached_rd_w[n]),
    .perf_visible_window_limit_reached_wr (perf_visible_window_limit_reached_wr_w[n]),
    .perf_op_is_dqsosc_mpc   (perf_op_is_dqsosc_mpc_w[n]),
    .perf_op_is_dqsosc_mrr   (perf_op_is_dqsosc_mrr_w[n]),
    .perf_op_is_tcr_mrr      (perf_op_is_tcr_mrr_w[n]),
    .perf_op_is_zqstart      (perf_op_is_zqstart_w[n]),
    .perf_op_is_zqlatch      (perf_op_is_zqlatch_w[n]),
    .ddrc_core_reg_dbg_operating_mode (ddrc_core_reg_dbg_operating_mode_w[n]),
    .ddrc_core_reg_dbg_global_fsm_state (ddrc_core_reg_dbg_global_fsm_state_w[n]),
    .ddrc_core_reg_dbg_init_curr_state (ddrc_core_reg_dbg_init_curr_state_w[n]),
    .ddrc_core_reg_dbg_init_next_state (ddrc_core_reg_dbg_init_next_state_w[n]),
    .ddrc_core_reg_dbg_ctrlupd_state (ddrc_core_reg_dbg_ctrlupd_state_w[n]),
    .ddrc_core_reg_dbg_lpr_q_state (ddrc_core_reg_dbg_lpr_q_state_w[n]),
    .ddrc_core_reg_dbg_hpr_q_state (ddrc_core_reg_dbg_hpr_q_state_w[n]),
    .ddrc_core_reg_dbg_wr_q_state (ddrc_core_reg_dbg_wr_q_state_w[n]),
    .ddrc_core_reg_dbg_lpr_q_depth (ddrc_core_reg_dbg_lpr_q_depth_w[n]),
    .ddrc_core_reg_dbg_hpr_q_depth (ddrc_core_reg_dbg_hpr_q_depth_w[n]),
    .ddrc_core_reg_dbg_wr_q_depth (ddrc_core_reg_dbg_wr_q_depth_w[n]),
    .ddrc_core_reg_dbg_hif_cmd_stall (ddrc_core_reg_dbg_hif_cmd_stall_w[n]),
    .ddrc_core_reg_dbg_hif_rcmd_stall (ddrc_core_reg_dbg_hif_rcmd_stall_w[n]),
    .ddrc_core_reg_dbg_hif_wcmd_stall (ddrc_core_reg_dbg_hif_wcmd_stall_w[n]),
    .ddrc_core_reg_dbg_rd_valid_rank (ddrc_core_reg_dbg_rd_valid_rank_w[n]),
    .ddrc_core_reg_dbg_rd_page_hit_rank (ddrc_core_reg_dbg_rd_page_hit_rank_w[n]),
    .ddrc_core_reg_dbg_rd_pri_rank (ddrc_core_reg_dbg_rd_pri_rank_w[n]),
    .ddrc_core_reg_dbg_wr_valid_rank (ddrc_core_reg_dbg_wr_valid_rank_w[n]),
    .ddrc_core_reg_dbg_wr_page_hit_rank (ddrc_core_reg_dbg_wr_page_hit_rank_w[n]),
    .ddrc_core_reg_dbg_wr_cam_7_0_valid (ddrc_core_reg_dbg_wr_cam_7_0_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_7_0_valid (ddrc_core_reg_dbg_rd_cam_7_0_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_15_8_valid (ddrc_core_reg_dbg_wr_cam_15_8_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_15_8_valid (ddrc_core_reg_dbg_rd_cam_15_8_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_23_16_valid (ddrc_core_reg_dbg_wr_cam_23_16_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_23_16_valid (ddrc_core_reg_dbg_rd_cam_23_16_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_31_24_valid (ddrc_core_reg_dbg_wr_cam_31_24_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_31_24_valid (ddrc_core_reg_dbg_rd_cam_31_24_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_39_32_valid (ddrc_core_reg_dbg_wr_cam_39_32_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_39_32_valid (ddrc_core_reg_dbg_rd_cam_39_32_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_47_40_valid (ddrc_core_reg_dbg_wr_cam_47_40_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_47_40_valid (ddrc_core_reg_dbg_rd_cam_47_40_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_55_48_valid (ddrc_core_reg_dbg_wr_cam_55_48_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_55_48_valid (ddrc_core_reg_dbg_rd_cam_55_48_valid_w[n]),
    .ddrc_core_reg_dbg_wr_cam_63_56_valid (ddrc_core_reg_dbg_wr_cam_63_56_valid_w[n]),
    .ddrc_core_reg_dbg_rd_cam_63_56_valid (ddrc_core_reg_dbg_rd_cam_63_56_valid_w[n]),
//spyglass disable_block W528
//SMD: Variable set but only read in DDRCTL_DDR4
//SJ: Used in only certain configurations
    .dfi_bg (dfi_bg_w[n]),
    .dfi_act_n (dfi_act_n_w[n]),
    .dfi_cid (dfi_cid_w[n]),
//spyglass enable_block W528
    .dfi_address (dfi_address_w[n]),
//spyglass disable_block W528
//SMD: Variable set but only read in DDRCTL_DDR4
//SJ: Used in only certain configurations
    .dfi_bank (dfi_bank_w[n]),
//spyglass enable_block W528
    .dfi_freq_ratio (dfi_freq_ratio_w[n]),
//spyglass disable_block W528
//SMD: Variable set but only read in DDRCTL_DDR4
//SJ: Used in only certain configurations
    .dfi_cas_n (dfi_cas_n_w[n]),
    .dfi_ras_n (dfi_ras_n_w[n]),
    .dfi_we_n (dfi_we_n_w[n]),
    .dfi_cke (dfi_cke_w[n]),
//spyglass enable_block W528
    .dfi_cs (dfi_cs_w[n]),
//spyglass disable_block W528
//SMD: Variable set but only read in DDRCTL_DDR4
//SJ: Used in only certain configurations
    .dfi_odt (dfi_odt_w[n]),
//spyglass enable_block W528
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only certain configurations
    .dfi_hif_cmd_addr (dfi_hif_cmd_addr_w[n]),
    .dfi_hif_cmd_wdata_ptr (dfi_hif_cmd_wdata_ptr_w[n]),
    .dfi_hif_cmd_keyid (dfi_hif_cmd_keyid_w[n]),
//spyglass enable_block W528
    .dfi_reset_n (dfi_reset_n_w[n]),
    .dfi_wrdata_cs (dfi_wrdata_cs_w[n]),
    .dfi_rddata_cs (dfi_rddata_cs_w[n]),
    .dfi_ctrlupd_req (dfi_ctrlupd_req_w[n]),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under DDRCTL_PPT2 in this file but signal should always exist for OCCAP
    .dfi_ctrlupd_type (dfi_ctrlupd_type_w[n]),
    .dfi_ctrlupd_target (dfi_ctrlupd_target_w[n]),
//spyglass enable_block W528
    .dfi_dram_clk_disable (dfi_dram_clk_disable_w[n]),
    .dfi_parity_in (dfi_parity_in_w[n]),
    .dfi_wck_cs (dfi_wck_cs_w[n]),
    .dfi_wck_en (dfi_wck_en_w[n]),
    .dfi_wck_toggle (dfi_wck_toggle_w[n]),
    .dfi_init_start (dfi_init_start_w[n]),
    .dfi_freq_fsp (dfi_freq_fsp_w[n]),
    .dfi_frequency (dfi_frequency_w[n]),
    .dfi_2n_mode (dfi_2n_mode_w[n]),
    .dfi_reset_n_ref (dfi_reset_n_ref_w[n]),
    .init_mr_done_out (init_mr_done_out_w[n]),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under Write CRC Retry in this file but signal should always exist for OCCAP
    .ddrc_reg_capar_err_intr (ddrc_reg_capar_err_intr_w[n]),
    .ddrc_reg_capar_err_cnt (ddrc_reg_capar_err_cnt_w[n]),
    .ddrc_reg_capar_err_max_reached_intr (ddrc_reg_capar_err_max_reached_intr_w[n]),
    .ddrc_reg_capar_retry_limit_intr (ddrc_reg_capar_retry_limit_intr_w[n]),
    .ddrc_reg_capar_fatl_err_intr (ddrc_reg_capar_fatl_err_intr_w[n]),
    .ddrc_reg_capar_fatl_err_code (ddrc_reg_capar_fatl_err_code_w[n]),
    .ddrc_reg_wr_crc_err_cnt (ddrc_reg_wr_crc_err_cnt_w[n]),
    .ddrc_reg_wr_crc_err_intr (ddrc_reg_wr_crc_err_intr_w[n]),
    .ddrc_reg_wr_crc_err_max_reached_intr (ddrc_reg_wr_crc_err_max_reached_intr_w[n]),
    .ddrc_reg_retry_fifo_fill_level (ddrc_reg_retry_fifo_fill_level_w[n]),
    .ddrc_reg_retry_stat (ddrc_reg_retry_stat_w[n]),
    .ddrc_reg_wr_crc_retry_limit_intr (ddrc_reg_wr_crc_retry_limit_intr_w[n]),
    .ddrc_reg_rd_retry_limit_intr (ddrc_reg_rd_retry_limit_intr_w[n]),
    .ddrc_reg_rd_crc_retry_limit_reached (ddrc_reg_rd_crc_retry_limit_reached_w[n]),
    .ddrc_reg_rd_ue_retry_limit_reached (ddrc_reg_rd_ue_retry_limit_reached_w[n]),
    .dbg_wr_crc_retry_pulse (dbg_wr_crc_retry_pulse_w[n]),
    .dbg_rd_crc_retry_pulse (dbg_rd_crc_retry_pulse_w[n]),
    .dbg_rd_ue_retry_pulse (dbg_rd_ue_retry_pulse_w[n]),
    .dbg_rd_retry_rank (dbg_rd_retry_rank_w[n]),
//spyglass enable_block W528
    .retryram_din (retryram_din_w[n]),
    .retryram_waddr (retryram_waddr_w[n]),
    .retryram_raddr (retryram_raddr_w[n]),
    .retryram_re (retryram_re_w[n]),
    .retryram_we (retryram_we_w[n]),
    .retryram_mask (retryram_mask_w[n]),
    .ddrc_reg_rank_refresh_busy (ddrc_reg_rank_refresh_busy_w[n]),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only certain configurations
    .ext_rank_refresh_busy (ext_rank_refresh_busy_w[n]),
//spyglass enable_block W528
    .ddrc_reg_ctrlupd_busy (ddrc_reg_ctrlupd_busy_w[n]),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under DDRCTL_LPDDR in this file but signal should always exist for OCCAP
    .ddrc_reg_ctrlupd_burst_busy (ddrc_reg_ctrlupd_burst_busy_w[n]),
//spyglass enable_block W528
    .ddrc_reg_capar_poison_complete (ddrc_reg_capar_poison_complete_w[n]),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
    .dbg_dfi_parity_poison (dbg_dfi_parity_poison_w[n]),
//spyglass enable_block W528
    .ddrc_reg_dbg_hpr_q_depth (ddrc_reg_dbg_hpr_q_depth_w[n]),
    .ddrc_reg_dbg_lpr_q_depth (ddrc_reg_dbg_lpr_q_depth_w[n]),
    .ddrc_reg_dbg_w_q_depth (ddrc_reg_dbg_w_q_depth_w[n]),
    .ddrc_reg_dbg_stall (ddrc_reg_dbg_stall_w[n]),
    .ddrc_reg_dbg_stall_rd (ddrc_reg_dbg_stall_rd_w[n]),
    .ddrc_reg_dbg_stall_wr (ddrc_reg_dbg_stall_wr_w[n]),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in generate
    .ddrc_reg_dfi_lp_state (ddrc_reg_dfi_lp_state_w[n]),
    .ddrc_reg_mpsm_state (ddrc_reg_mpsm_state_w[n]),
    .ddrc_reg_powerdown_state (ddrc_reg_powerdown_state_w[n]),
    .ddrc_reg_selfref_cam_not_empty (ddrc_reg_selfref_cam_not_empty_w[n]),
//spyglass enable_block W528
    .ddrc_reg_selfref_state (ddrc_reg_selfref_state_w[n]),
    .ddrc_reg_operating_mode (ddrc_reg_operating_mode_w[n]),
    .ddrc_reg_selfref_type (ddrc_reg_selfref_type_w[n]),
    .ddrc_reg_wr_q_empty (ddrc_reg_wr_q_empty_w[n]),
    .ddrc_reg_rd_q_empty (ddrc_reg_rd_q_empty_w[n]),
    .ddrc_reg_wr_data_pipeline_empty (ddrc_reg_wr_data_pipeline_empty_w[n]),
    .ddrc_reg_rd_data_pipeline_empty (ddrc_reg_rd_data_pipeline_empty_w[n]),
    .ddrc_reg_zq_calib_short_busy (ddrc_reg_zq_calib_short_busy_w[n]),
    .hif_refresh_req_bank (hif_refresh_req_bank_w[n]),
    .hif_refresh_req (hif_refresh_req_w[n]),
    .hif_refresh_req_cnt (hif_refresh_req_cnt_w[n]),
    .hif_refresh_req_derate (hif_refresh_req_derate_w[n]),
    .hif_refresh_active (hif_refresh_active_w[n]),
    .dfi_phyupd_ack (dfi_phyupd_ack_w[n]),
    .dfi_phymstr_ack (dfi_phymstr_ack_w[n]),
    .dfi_lp_ctrl_req (dfi_lp_ctrl_req_w[n]),
    .dfi_lp_ctrl_wakeup (dfi_lp_ctrl_wakeup_w[n]),
    .dfi_lp_data_req (dfi_lp_data_req_w[n]),
    .dfi_lp_data_wakeup (dfi_lp_data_wakeup_w[n]),
    .hwffcmrw_op_s(hwffcmrw_op_s_w[n]),
    .hwffc_target_freq_en (hwffc_target_freq_en_w[n]),
    .hwffc_target_freq (hwffc_target_freq_w[n]),
    .hwffc_target_freq_init (hwffc_target_freq_init_w[n]),
    .ddrc_reg_hwffc_in_progress (ddrc_reg_hwffc_in_progress_w[n]),
    .ddrc_reg_current_frequency (ddrc_reg_current_frequency_w[n]),
    .ddrc_reg_current_fsp (ddrc_reg_current_fsp_w[n]),
    .ddrc_reg_current_vrcg (ddrc_reg_current_vrcg_w[n]),
    .ddrc_reg_hwffc_operating_mode (ddrc_reg_hwffc_operating_mode_w[n]),
    .ddrc_xpi_port_disable_req (ddrc_xpi_port_disable_req_w[n]),
    .ddrc_xpi_clock_required (ddrc_xpi_clock_required_w[n]),
    .hwffc_hif_wd_stall (hwffc_hif_wd_stall_w[n]),
    .hwffc_i_reg_ddrc_dis_auto_zq (hwffc_i_reg_ddrc_dis_auto_zq_w[n]),
//spyglass disable_block W287b
//SMD: Instance output port 'ih_mr_ie_pw' is not connected
//SJ: ih_mr_ie_pw is removed from IH and MR, but it is kept to avoid modifying the signal number in ddrc wrapper module
    .ih_mr_ie_pw(),
//spyglass enable_block W287b
    .ih_mr_ie_blk_wr_end (ih_mr_ie_blk_wr_end_w[n]),
    .ih_rd_ie_brt (ih_rd_ie_brt_w[n]),
    .ih_rd_ie_rd_cnt_inc (ih_rd_ie_rd_cnt_inc_w[n]),
    .ih_rd_ie_blk_rd_end (ih_rd_ie_blk_rd_end_w[n]),
    .ih_mr_ie_wr_cnt_inc (ih_mr_ie_wr_cnt_inc_w[n]),
    .ih_mr_ie_wr_cnt_dec_vct (ih_mr_ie_wr_cnt_dec_vct_w[n]),
    .ih_mr_ie_bwt (ih_mr_ie_bwt_w[n]),
    .ih_mr_ie_brt (ih_mr_ie_brt_w[n]),
    .ih_mr_ie_brt_vld (ih_mr_ie_brt_vld_w[n]),
    .te_mr_ie_bt (te_mr_ie_bt_w[n]),
    .te_mr_ie_wr_type (te_mr_ie_wr_type_w[n]),
    .te_mr_ie_blk_burst_num (te_mr_ie_blk_burst_num_w[n]),
    .te_mr_addr_info (te_mr_addr_info_w[n]),
    .pi_rt_ie_bt (pi_rt_ie_bt_w[n]),
    .pi_rt_ie_rd_type (pi_rt_ie_rd_type_w[n]),
    .pi_rt_ie_blk_burst_num (pi_rt_ie_blk_burst_num_w[n]),
    .ih_mr_lkp_bwt (ih_mr_lkp_bwt_w[n]),
    .ih_mr_lkp_bwt_vld (ih_mr_lkp_bwt_vld_w[n]),
    .ih_mr_lkp_brt (ih_mr_lkp_brt_w[n]),
    .ih_mr_lkp_brt_vld (ih_mr_lkp_brt_vld_w[n]),
    .ih_rd_lkp_brt (ih_rd_lkp_brt_w[n]),
    .ih_rd_lkp_brt_vld (ih_rd_lkp_brt_vld_w[n]),
    .ih_rd_lkp_bwt (ih_rd_lkp_bwt_w[n]),
    .ih_rd_lkp_bwt_vld (ih_rd_lkp_bwt_vld_w[n]),
    .te_mr_eccap (te_mr_eccap_w[n]),
    .pi_rt_eccap (pi_rt_eccap_w[n]),
    .ih_wu_cerr (ih_wu_cerr_w[n]),
    .pi_rt_rd_mrr (pi_rt_rd_mrr_w[n]),
    .pi_rt_rd_mrr_ext (pi_rt_rd_mrr_ext_w[n]),
    .pi_ph_dfi_rddata_en (pi_ph_dfi_rddata_en_w[n]),
    .pi_ph_dfi_wrdata_en (pi_ph_dfi_wrdata_en_w[n]),
    .ih_wu_wr_valid (ih_wu_wr_valid_w[n]),
    .ih_wu_wr_valid_addr_err (ih_wu_wr_valid_addr_err_w[n]),
    .ih_te_rd_valid (ih_te_rd_valid_w[n]),
    .ih_te_wr_valid (ih_te_wr_valid_w[n]),
    .ih_wu_rmw_type (ih_wu_rmw_type_w[n]),
    .ih_wu_wr_entry (ih_wu_wr_entry_w[n]),
    .ih_wu_critical_word (ih_wu_critical_word_w[n]),
    .pi_gs_geardown_mode_on (pi_gs_geardown_mode_on_w[n]),
    .pi_rt_rd_partial (pi_rt_rd_partial_w[n]),
    .pi_rt_rd_vld (pi_rt_rd_vld_w[n]),
    .pi_rt_rd_tag (pi_rt_rd_tag_w[n]),
    .pi_rt_rd_addr_err (pi_rt_rd_addr_err_w[n]),
    .pi_rt_wr_ram_addr (pi_rt_wr_ram_addr_w[n]),
    .pi_rt_rmwcmd (pi_rt_rmwcmd_w[n]),
    .pi_rt_rmwtype (pi_rt_rmwtype_w[n]),
    .pi_rt_rankbank_num (pi_rt_rankbank_num_w[n]),
    .pi_rt_page_num (pi_rt_page_num_w[n]),
    .pi_rt_block_num (pi_rt_block_num_w[n]),
    .pi_rt_critical_word (pi_rt_critical_word_w[n]),
    .te_yy_wr_combine (te_yy_wr_combine_w[n]),
    .te_wu_wrdata_stall_req (te_wu_wrdata_stall_req_w[n]),
    .ts_pi_mwr (ts_pi_mwr_w[n]),
    .ts_pi_wr32 (ts_pi_wr32_w[n]),
    .ts_pi_2nd_half (ts_pi_2nd_half_w[n]),
    .ts_cam_clear_en (ts_cam_clear_en_w[n]),
    .te_pi_wr_word_valid (te_pi_wr_word_valid_w[n]),
    .gs_pi_rdwr_bc_sel (gs_pi_rdwr_bc_sel_w[n]),
    .gs_pi_rdwr_ram_raddr_lsb_first (gs_pi_rdwr_ram_raddr_lsb_first_w[n]),
    .gs_pi_rdwr_pw_num_beats_m1 (gs_pi_rdwr_pw_num_beats_m1_w[n]),
    .te_mr_wr_ram_addr (te_mr_wr_ram_addr_w[n]),
    .te_wu_entry_num (te_wu_entry_num_w[n]),
    .te_wu_wr_retry (te_wu_wr_retry_w[n]),
    .gs_mr_write (gs_mr_write_w[n]),
    .gs_mr_load_mode_pda (gs_mr_load_mode_pda_w[n]),
    .gs_mr_pda_data_sel (gs_mr_pda_data_sel_w[n]),
    .pda_mode (pda_mode_w[n]),
    .pda_mode_pre (pda_mode_pre_w[n]),
    .gs_pi_cs_n (gs_pi_cs_n_w[n]),
    .retry_fifo_empty (retry_fifo_empty_w[n]),
    .retry_rt_rdatavld_gate_en (retry_rt_rdatavld_gate_en_w[n]),
    .retry_rt_fifo_init_n (retry_rt_fifo_init_n_w[n]),
    .retry_rt_fatl_err_pulse (retry_rt_fatl_err_pulse_w[n]),
    .retry_rt_now_sw_intervention (retry_rt_now_sw_intervention_w[n]),
    .retry_rt_rd_timeout_value (retry_rt_rd_timeout_value_w[n]),
    .retry_dfi_sel (retry_dfi_sel_w[n]),
    .retry_phy_dm (retry_phy_dm_w[n]),
    .retry_phy_wdata (retry_phy_wdata_w[n]),
    .retry_phy_wdata_vld_early (retry_phy_wdata_vld_early_w[n]),
    .retry_dfi_rddata_en (retry_dfi_rddata_en_w[n]),
    .retry_dfi_wrdata_en (retry_dfi_wrdata_en_w[n]),
    .reg_ddrc_active_ranks_int (reg_ddrc_active_ranks_int_w[n]),
    .gs_pi_data_pipeline_empty (gs_pi_data_pipeline_empty_w[n]),
    .mrr_op_on (mrr_op_on_w[n]),
    .pi_gs_mpr_mode (pi_gs_mpr_mode_w[n]),
    .ih_busy (ih_busy_w[n]),
    .reg_ddrc_ext_rank_refresh (reg_ddrc_ext_rank_refresh_w[n]),
    .pi_gs_dll_off_mode (pi_gs_dll_off_mode_w[n]),
    .reg_ddrc_fgr_mode_gated (reg_ddrc_fgr_mode_gated_w[n]),
    .ddrc_phy_cal_dl_enable (ddrc_phy_cal_dl_enable_w[n]),
    .gs_pi_op_is_exit_selfref (gs_pi_op_is_exit_selfref_w[n]),
    .perf_op_is_crit_ref (perf_op_is_crit_ref_w[n]),
    .perf_op_is_spec_ref (perf_op_is_spec_ref_w[n]),
    .te_wu_ie_flowctrl_req (te_wu_ie_flowctrl_req_w[n]),
    .ih_ie_busy (ih_ie_busy_w[n]),
    .hif_wrecc_credit (hif_wrecc_credit_w[n]),
    .ddrc_reg_dbg_wrecc_q_depth (ddrc_reg_dbg_wrecc_q_depth_w[n]),
    .ddrc_core_reg_dbg_wrecc_q_depth (ddrc_core_reg_dbg_wrecc_q_depth_w[n]),
    .perf_ie_blk_hazard (perf_ie_blk_hazard_w[n]),
    //spyglass disable_block W528
    //SMD: A signal or variable is set but never read
    //SJ: Used in generate block
    .core_derate_temp_limit_intr (core_derate_temp_limit_intr_w[n]),
    .ddrc_reg_max_num_alloc_bsm             (ddrc_reg_max_num_alloc_bsm_w[n]),
    .ddrc_reg_max_num_unalloc_entries       (ddrc_reg_max_num_unalloc_entries_w[n]),
    .ddrc_reg_refresh_rate_rank0 (ddrc_reg_refresh_rate_rank0_w[n]),
    .ddrc_reg_refresh_rate_rank1 (ddrc_reg_refresh_rate_rank1_w[n]),
    .ddrc_reg_refresh_rate_rank2 (ddrc_reg_refresh_rate_rank2_w[n]),
    .ddrc_reg_refresh_rate_rank3 (ddrc_reg_refresh_rate_rank3_w[n]),
    .ddrc_reg_derate_temp_limit_intr_sts_rank0 (ddrc_reg_derate_temp_limit_intr_sts_rank0_w[n]),
    .ddrc_reg_derate_temp_limit_intr_sts_rank1 (ddrc_reg_derate_temp_limit_intr_sts_rank1_w[n]),
    .ddrc_reg_derate_temp_limit_intr_sts_rank2 (ddrc_reg_derate_temp_limit_intr_sts_rank2_w[n]),
    .ddrc_reg_derate_temp_limit_intr_sts_rank3 (ddrc_reg_derate_temp_limit_intr_sts_rank3_w[n]),
    .pi_rd_eccap (pi_rd_eccap_w[n]),
    .pi_rd_vld (pi_rd_vld_w[n]),
    .pi_rd_partial (pi_rd_partial_w[n]),
    .pi_rd_tag (pi_rd_tag_w[n]),
    .pi_rd_mrr_ext (pi_rd_mrr_ext_w[n]),
    .pi_rd_addr_err (pi_rd_addr_err_w[n]),
    .pi_rd_rmw_type (pi_rd_rmw_type_w[n]),
    .pi_rd_wr_ram_addr (pi_rd_wr_ram_addr_w[n]),
    .pi_rd_page (pi_rd_page_w[n]),
    .pi_rd_blk (pi_rd_blk_w[n]),
    .pi_rd_critical_word (pi_rd_critical_word_w[n]),
    .pi_rd_rankbank (pi_rd_rankbank_w[n]),
    .pi_rd_ie_bt(pi_rd_ie_bt_w[n]),
    .pi_rd_ie_rd_type(pi_rd_ie_rd_type_w[n]),
    .pi_rd_ie_blk_burst_num(pi_rd_ie_blk_burst_num_w[n]),
    .pi_wr_vld_nxt (pi_wr_vld_nxt_w[n]),
    .pi_wr_ph_nxt (pi_wr_ph_nxt_w[n]),
    .pi_wr_cs_nxt (pi_wr_cs_nxt_w[n]),
    .pi_rd_vld_nxt (pi_rd_vld_nxt_w[n]),
    .pi_rd_ph_nxt (pi_rd_ph_nxt_w[n]),
    .pi_dfi_wrdata_en (pi_dfi_wrdata_en_w[n]),
    .pi_dfi_rddata_en (pi_dfi_rddata_en_w[n]),
    .pi_rd_mrr_snoop  (pi_rd_mrr_snoop_w[n]),
    .pi_phy_snoop_en  (pi_phy_snoop_en_w[n]),
    .ddrc_reg_prank3_mode                  (ddrc_reg_prank3_mode_w[n]),
    .ddrc_reg_prank2_mode                  (ddrc_reg_prank2_mode_w[n]),
    .ddrc_reg_prank1_mode                  (ddrc_reg_prank1_mode_w[n]),
    .ddrc_reg_prank0_mode                  (ddrc_reg_prank0_mode_w[n]),
    .ddrc_reg_dbg_stat3                    (ddrc_reg_dbg_stat3_w[n]  ),
    .ddrc_reg_dbg_stat2                    (ddrc_reg_dbg_stat2_w[n]  ),
    .ddrc_reg_dbg_stat1                    (ddrc_reg_dbg_stat1_w[n]  ),
    .ddrc_reg_dbg_stat0                    (ddrc_reg_dbg_stat0_w[n]  ),

    .dch_sync_mode_o                       (dch_sync_mode_o_w[n]               ),
    .rank_idle_state_o                     (rank_idle_state_o_w[n]             ),
    .rank_selfref_state_o                  (rank_selfref_state_o_w[n]          ),
    .selfref_idle_entry_o                  (selfref_idle_entry_o_w[n]          ),
    .selfref_sw_entry_o                    (selfref_sw_entry_o_w[n]            ),
    .selfref_hw_entry_o                    (selfref_hw_entry_o_w[n]            ),
    .selfref_sw_o                          (selfref_sw_o_w[n]                  ),
    .selfref_idle_exit_o                   (selfref_idle_exit_o_w[n]           ),
    .selfref_sw_exit_o                     (selfref_sw_exit_o_w[n]             ),
    .channel_message_o                     (channel_message_o_w[n]             ),
    .rank_selfref_operating_mode_o         (rank_selfref_operating_mode_o_w[n] ),
    .rank_selfref_swhw_state_o             (rank_selfref_swhw_state_o_w[n]     ),
    .rank_selfref_tctrl_delay_ack_o        (rank_selfref_tctrl_delay_ack_o_w[n]),
    .dfi_lp_selfref_tlp_resp_ack_o         (dfi_lp_selfref_tlp_resp_ack_o_w[n] ),
    .hw_lp_exit_idle_o                     (hw_lp_exit_idle_o_w[n]             ),
    .hw_lp_selfref_hw_o                    (hw_lp_selfref_hw_o_w[n]            ),

    .ddrc_reg_cmd_rslt                     (ddrc_reg_cmd_rslt_w   [n]),
    .ddrc_reg_swcmd_lock                   (ddrc_reg_swcmd_lock_w [n]),
    .ddrc_reg_ducmd_lock                   (ddrc_reg_ducmd_lock_w [n]),
    .ddrc_reg_lccmd_lock                   (ddrc_reg_lccmd_lock_w [n]),
    .ddrc_reg_ctrlupd_err_intr             (ddrc_reg_ctrlupd_err_intr_w[n]),
    .ddrc_reg_mrr_data_vld                 (ddrc_reg_mrr_data_vld_w[n]),
    .ddrc_reg_rd_data_vld                  (ddrc_reg_rd_data_vld_w[n]),
    .ddrc_reg_cmd_err                      (ddrc_reg_cmd_err_w[n]),
    .ddrc_reg_cmd_done                     (ddrc_reg_cmd_done_w[n]),
    .ddrc_reg_cmd_mrr_data                 (ddrc_reg_cmd_mrr_data_w[n]),
    .ddrc_reg_du_cfgbuf_rdata              (ddrc_reg_du_cfgbuf_rdata_w[n]),
    .ddrc_reg_du_cmdbuf_rdata              (ddrc_reg_du_cmdbuf_rdata_w[n]),
    .ddrc_reg_lp_cmdbuf_rdata              (ddrc_reg_lp_cmdbuf_rdata_w[n]),
    .ddrc_reg_capar_cmdbuf_rdata           (ddrc_reg_capar_cmdbuf_rdata_w[n]),
    .ddrc_reg_powerdown_ongoing            (ddrc_reg_powerdown_ongoing_w[n]),
    .ddrc_reg_selfref_ongoing              (ddrc_reg_selfref_ongoing_w[n]),
    .dbg_prank_act_pd                      (dbg_prank_act_pd_w[n]),
    .dbg_prank_pre_pd                      (dbg_prank_pre_pd_w[n]),
    .dbg_du_ucode_seq_ongoing              (dbg_du_ucode_seq_ongoing_w[n]),
    .dbg_lp_ucode_seq_ongoing              (dbg_lp_ucode_seq_ongoing_w[n]),
    .ddrc_reg_du_cur_blk_set               (ddrc_reg_du_cur_blk_set_w[n]),
    .ddrc_reg_du_cur_blk_index             (ddrc_reg_du_cur_blk_index_w[n]),
    .ddrc_reg_du_cur_blk_addr              (ddrc_reg_du_cur_blk_addr_w[n]),
    .ddrc_reg_du_cur_blk_ucode             (ddrc_reg_du_cur_blk_ucode_w[n]),
    .ddrc_reg_du_main_fsm_state            (ddrc_reg_du_main_fsm_state_w[n]),
    .ddrc_reg_glb_blk_events_ongoing       (ddrc_reg_glb_blk_events_ongoing_w[n]),
    .ddrc_reg_rank_blk_events_ongoing      (ddrc_reg_rank_blk_events_ongoing_w[n]),
    .ddrc_reg_du_mceu_fsm_state            (ddrc_reg_du_mceu_fsm_state_w[n]),
    .ddrc_reg_du_sceu_fsm_state            (ddrc_reg_du_sceu_fsm_state_w[n]),
    .ddrc_reg_caparcmd_err_intr            (ddrc_reg_caparcmd_err_intr_w[n]),
    .ddrc_reg_caparcmd_err_sts             (ddrc_reg_caparcmd_err_sts_w[n]),
    .ddrc_reg_lccmd_err_intr               (ddrc_reg_lccmd_err_intr_w[n]),
    .ddrc_reg_ducmd_err_intr               (ddrc_reg_ducmd_err_intr_w[n]),
    .ddrc_reg_swcmd_err_intr               (ddrc_reg_swcmd_err_intr_w[n]),
    .ddrc_reg_swcmd_err_sts                (ddrc_reg_swcmd_err_sts_w[n]),
    .ddrc_reg_ducmd_err_sts                (ddrc_reg_ducmd_err_sts_w[n]),
    .ddrc_reg_lccmd_err_sts                (ddrc_reg_lccmd_err_sts_w[n]),
    .ddrc_reg_rfm_alert_intr               (ddrc_reg_rfm_alert_intr_w[n]),
    .ddrc_reg_rfm_cmd_log                  (ddrc_reg_rfm_cmd_log_w[n]),
    .ddrc_reg_2n_mode                      (ddrc_reg_2n_mode_w[n]),
    .ddrc_reg_ecs_mr16                     (ddrc_reg_ecs_mr16_w[n]),
    .ddrc_reg_ecs_mr17                     (ddrc_reg_ecs_mr17_w[n]),
    .ddrc_reg_ecs_mr18                     (ddrc_reg_ecs_mr18_w[n]),
    .ddrc_reg_ecs_mr19                     (ddrc_reg_ecs_mr19_w[n]),
    .ddrc_reg_ecs_mr20                     (ddrc_reg_ecs_mr20_w[n]),
    .gs_wr_bc_sel                          (gs_wr_bc_sel_w[n]),
    .gs_mr_ram_raddr_lsb_first             (gs_mr_ram_raddr_lsb_first_w[n]),
    .gs_mr_pw_num_beats_m1                 (gs_mr_pw_num_beats_m1_w[n]),
    //spyglass enable_block W528

    // inputs
    .core_ddrc_core_clk                    (core_ddrc_core_clk),
    .core_ddrc_rstn                        (core_ddrc_rstn),


           .core_ddrc_core_clk_te          (core_ddrc_core_clk_te),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only LPDDR54 but signal should always exist for OCCAP
    .clk_te_en                             (clk_te_en_w[n]),
//spyglass enable_block W528

    .bsm_clk                               (bsm_clk                ),
    .bsm_clk_on                            (bsm_clk_on             ),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only LPDDR54 but signal should always exist for OCCAP
    .bsm_clk_en                            (bsm_clk_en_w[n]        ),
//spyglass enable_block W528


    .hif_cmd_valid                         (hif_cmd_valid),
    .hif_cmd_type                          (hif_cmd_type),
    .hif_cmd_pri                           (hif_cmd_pri),
    .hif_cmd_addr                          (hif_cmd_addr),
    .hif_cmd_length                        (hif_cmd_length),
    .hif_cmd_token                         (hif_cmd_token),
    .hif_cmd_wdata_ptr                     (hif_cmd_wdata_ptr),
          .hif_cmd_latency                       (hif_cmd_latency),
          .hif_cmd_autopre                       (hif_cmd_autopre),
          .hif_cmd_ecc_region                    (hif_cmd_ecc_region),
          .hif_cmd_wdata_mask_full_ie            (hif_cmd_wdata_mask_full_ie),
          .hif_go2critical_lpr                    (hif_go2critical_lpr),
          .hif_go2critical_hpr                    (hif_go2critical_hpr),
          .hif_go2critical_wr                     (hif_go2critical_wr),
          .hif_go2critical_l1_wr                  (hif_go2critical_l1_wr ),
          .hif_go2critical_l2_wr                  (hif_go2critical_l2_wr ),
          .hif_go2critical_l1_lpr                 (hif_go2critical_l1_lpr),
          .hif_go2critical_l2_lpr                 (hif_go2critical_l2_lpr),
          .hif_go2critical_l1_hpr                 (hif_go2critical_l1_hpr),
          .hif_go2critical_l2_hpr                 (hif_go2critical_l2_hpr),
           .reg_ddrc_autopre_rmw                   (reg_ddrc_autopre_rmw),

          .reg_ddrc_sw_init_int                   (reg_ddrc_sw_init_int),
          .reg_ddrc_mr_wr                         (reg_ddrc_mr_wr),
          .reg_ddrc_mr_type                       (reg_ddrc_mr_type),
          .reg_ddrc_mr_data                       (reg_ddrc_mr_data),
          .reg_ddrc_mr_addr                       (reg_ddrc_mr_addr),
          .reg_ddrc_derate_mr4_tuf_dis            (reg_ddrc_derate_mr4_tuf_dis),
          .reg_ddrc_derate_temp_limit_intr_clr    (reg_ddrc_derate_temp_limit_intr_clr),
         .reg_ddrc_active_derate_byte_rank0       (reg_ddrc_active_derate_byte_rank0),
         .reg_ddrc_active_derate_byte_rank1       (reg_ddrc_active_derate_byte_rank1),

         .reg_ddrc_dbg_mr4_rank_sel               (reg_ddrc_dbg_mr4_rank_sel),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only DDR5 and LPDDR45C in this file but signal should always exist for OCCAP
          .ddrc_reg_dbg_mr4_byte0                 (ddrc_reg_dbg_mr4_byte0_w[n]),
          .ddrc_reg_dbg_mr4_byte1                 (ddrc_reg_dbg_mr4_byte1_w[n]),
          .ddrc_reg_dbg_mr4_byte2                 (ddrc_reg_dbg_mr4_byte2_w[n]),
          .ddrc_reg_dbg_mr4_byte3                 (ddrc_reg_dbg_mr4_byte3_w[n]),
//spyglass enable_block W528
          .reg_ddrc_lpddr4_refresh_mode           (reg_ddrc_lpddr4_refresh_mode),
          .reg_ddrc_zq_reset                      (reg_ddrc_zq_reset),
          .reg_ddrc_t_zq_reset_nop                (reg_ddrc_t_zq_reset_nop),
          .reg_ddrc_derate_enable                 (reg_ddrc_derate_enable),
          .reg_ddrc_derated_t_rcd                 (reg_ddrc_derated_t_rcd),
          .reg_ddrc_derated_t_ras_min             (reg_ddrc_derated_t_ras_min),
          .reg_ddrc_derated_t_rp                  (reg_ddrc_derated_t_rp),
          .reg_ddrc_derated_t_rrd                 (reg_ddrc_derated_t_rrd),
          .reg_ddrc_derated_t_rc                  (reg_ddrc_derated_t_rc),
          .reg_ddrc_derate_mr4_pause_fc           (reg_ddrc_derate_mr4_pause_fc),
          .reg_ddrc_mr4_read_interval             (reg_ddrc_mr4_read_interval),
          .reg_ddrc_derated_t_rcd_write           (reg_ddrc_derated_t_rcd_write),
          .cactive_in_ddrc_sync_or                (cactive_in_ddrc_sync_or),
          .cactive_in_ddrc_async                  (cactive_in_ddrc_async),
          .csysreq_ddrc                           (csysreq_ddrc),
          .csysmode_ddrc                          (csysmode_ddrc),
          .csysfrequency_ddrc                     (csysfrequency_ddrc),
          .csysdiscamdrain_ddrc                   (csysdiscamdrain_ddrc),
          .csysfsp_ddrc                           (csysfsp_ddrc),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under DDRCTL_DFI_SB_WDT or DDRCTL_DFI_ERROR in this file but signal should always exist for OCCAP
          .ddrc_reg_dfi_sideband_timer_err_intr   (ddrc_reg_dfi_sideband_timer_err_intr_w[n]),
          .ddrc_reg_dfi_tctrlupd_min_error        (ddrc_reg_dfi_tctrlupd_min_error_w[n]),
          .ddrc_reg_dfi_tctrlupd_max_error        (ddrc_reg_dfi_tctrlupd_max_error_w[n]),
          .ddrc_reg_dfi_tinit_start_error         (ddrc_reg_dfi_tinit_start_error_w[n]),
          .ddrc_reg_dfi_tinit_complete_error      (ddrc_reg_dfi_tinit_complete_error_w[n]),
          .ddrc_reg_dfi_tlp_ctrl_resp_error       (ddrc_reg_dfi_tlp_ctrl_resp_error_w[n]),
          .ddrc_reg_dfi_tlp_data_resp_error       (ddrc_reg_dfi_tlp_data_resp_error_w[n]),
          .ddrc_reg_dfi_tlp_ctrl_wakeup_error     (ddrc_reg_dfi_tlp_ctrl_wakeup_error_w[n]),
          .ddrc_reg_dfi_tlp_data_wakeup_error     (ddrc_reg_dfi_tlp_data_wakeup_error_w[n]),
          .ddrc_reg_dfi_error_intr                (ddrc_reg_dfi_error_intr_w[n]),
          .ddrc_reg_dfi_error_info                (ddrc_reg_dfi_error_info_w[n]),
//spyglass enable_block W528
          .reg_ddrc_dfi_tphy_wrlat                (reg_ddrc_dfi_tphy_wrlat),
          .reg_ddrc_dfi_t_rddata_en               (reg_ddrc_dfi_t_rddata_en),
          .reg_ddrc_dfi_tphy_wrcslat              (reg_ddrc_dfi_tphy_wrcslat),
          .reg_ddrc_dfi_tphy_rdcslat              (reg_ddrc_dfi_tphy_rdcslat),
          .reg_ddrc_dfi_data_cs_polarity          (reg_ddrc_dfi_data_cs_polarity),
          .dfi_ctrlupd_ack                        (cp_dfiif.dfi_ctrlupd_ack),
          .reg_ddrc_dfi_reset_n                   (reg_ddrc_dfi_reset_n),
          .reg_ddrc_dfi_init_start                (reg_ddrc_dfi_init_start),
          .reg_ddrc_dfi_freq_fsp                  (reg_ddrc_dfi_freq_fsp),
          .reg_ddrc_dfi_frequency                 (reg_ddrc_dfi_frequency),
          .dfi_init_complete                      (cp_dfiif.dfi_init_complete),
          .dfi_reset_n_in                         (dfi_reset_n_in),
          .init_mr_done_in                        (init_mr_done_in),


          .reg_ddrc_t_pgm_x1_x1024                    (reg_ddrc_t_pgm_x1_x1024),
          .reg_ddrc_t_pgm_x1_sel                      (reg_ddrc_t_pgm_x1_sel),
          .reg_ddrc_t_pgmpst_x32                      (reg_ddrc_t_pgmpst_x32),
          .reg_ddrc_t_pgm_exit                        (reg_ddrc_t_pgm_exit),
          .reg_ddrc_ppr_en                            (reg_ddrc_ppr_en),
          .reg_ddrc_ppr_pgmpst_en                     (reg_ddrc_ppr_pgmpst_en),

          .reg_ddrc_dfi_init_complete_en          (reg_ddrc_dfi_init_complete_en),
          .reg_ddrc_frequency_ratio               (reg_ddrc_frequency_ratio),
          .reg_ddrc_frequency_ratio_next          (reg_ddrc_frequency_ratio_next),
          .reg_ddrc_en_dfi_dram_clk_disable       (reg_ddrc_en_dfi_dram_clk_disable),
          .reg_ddrc_burst_rdwr                    (reg_ddrc_burst_rdwr),
          .reg_ddrc_dis_dq                        (reg_ddrc_dis_dq),
          .reg_ddrc_dis_hif                       (reg_ddrc_dis_hif),
          .reg_ddrc_dis_wc                        (reg_ddrc_dis_wc),
          .reg_ddrc_rank_refresh                  (reg_ddrc_rank_refresh),
          .reg_ddrc_dis_auto_refresh              (reg_ddrc_dis_auto_refresh),
          .reg_ddrc_dis_auto_ctrlupd              (reg_ddrc_dis_auto_ctrlupd),
          .reg_ddrc_ctrlupd                       (reg_ddrc_ctrlupd),
          .reg_ddrc_ctrlupd_burst                 (reg_ddrc_ctrlupd_burst),
          .reg_ddrc_dis_auto_ctrlupd_srx          (reg_ddrc_dis_auto_ctrlupd_srx),
          .reg_ddrc_ctrlupd_pre_srx               (reg_ddrc_ctrlupd_pre_srx),
           .reg_ddrc_opt_vprw_sch                  (reg_ddrc_opt_vprw_sch),
          .reg_ddrc_dis_speculative_act          (reg_ddrc_dis_speculative_act),
          .reg_ddrc_w_starve_free_running         (reg_ddrc_w_starve_free_running),
           .reg_ddrc_prefer_read                  (reg_ddrc_prefer_read),
           .reg_ddrc_opt_act_lat                  (reg_ddrc_opt_act_lat),  
          .reg_ddrc_lpr_num_entries               (reg_ddrc_lpr_num_entries),
          .reg_ddrc_lpr_num_entries_changed       (reg_ddrc_lpr_num_entries_changed),
          .reg_ddrc_mr                            (reg_ddrc_mr),
          .reg_ddrc_emr                           (reg_ddrc_emr),
          .reg_ddrc_emr2                          (reg_ddrc_emr2),
          .reg_ddrc_emr3                          (reg_ddrc_emr3),
          .reg_ddrc_mr4                           (reg_ddrc_mr4),
          .reg_ddrc_mr5                           (reg_ddrc_mr5),
          .reg_ddrc_mr6                           (reg_ddrc_mr6),
          .reg_ddrc_mr22                          (reg_ddrc_mr22),
          .reg_ddrc_t_rcd                         (reg_ddrc_t_rcd),
          .reg_ddrc_t_rcd_write                   (reg_ddrc_t_rcd_write),
          .reg_ddrc_t_ras_min                     (reg_ddrc_t_ras_min),
          .reg_ddrc_t_ras_max                     (reg_ddrc_t_ras_max),
          .reg_ddrc_t_rc                          (reg_ddrc_t_rc),
          .reg_ddrc_t_rp                          (reg_ddrc_t_rp),
          .reg_ddrc_t_rrd                         (reg_ddrc_t_rrd),
          .reg_ddrc_t_rrd_s                       (reg_ddrc_t_rrd_s),
          .reg_ddrc_rd2pre                        (reg_ddrc_rd2pre),
          .reg_ddrc_wr2pre                        (reg_ddrc_wr2pre),
          .reg_ddrc_rda2pre                       (reg_ddrc_rda2pre),
          .reg_ddrc_wra2pre                       (reg_ddrc_wra2pre),
          .reg_ddrc_pageclose                     (reg_ddrc_pageclose),
          .reg_ddrc_pageclose_timer               (reg_ddrc_pageclose_timer),
          .reg_ddrc_page_hit_limit_rd             (reg_ddrc_page_hit_limit_rd),
          .reg_ddrc_page_hit_limit_wr             (reg_ddrc_page_hit_limit_wr),
          .reg_ddrc_opt_hit_gt_hpr                (reg_ddrc_opt_hit_gt_hpr),
          .reg_ddrc_visible_window_limit_rd       (reg_ddrc_visible_window_limit_rd),
          .reg_ddrc_visible_window_limit_wr       (reg_ddrc_visible_window_limit_wr),
          .reg_ddrc_refresh_margin                (reg_ddrc_refresh_margin),
          .reg_ddrc_force_clk_te_en               (reg_ddrc_force_clk_te_en),
          .reg_ddrc_pre_cke_x1024                 (reg_ddrc_pre_cke_x1024),
          .reg_ddrc_post_cke_x1024                (reg_ddrc_post_cke_x1024),
          .reg_ddrc_rd2wr                         (reg_ddrc_rd2wr),
          .reg_ddrc_wr2rd                         (reg_ddrc_wr2rd),
          .reg_ddrc_wr2rd_s                       (reg_ddrc_wr2rd_s),
          .reg_ddrc_refresh_burst                 (reg_ddrc_refresh_burst),
          .reg_ddrc_t_ccd                         (reg_ddrc_t_ccd),
          .reg_ddrc_t_ccd_s                       (reg_ddrc_t_ccd_s),
          .reg_ddrc_odtloff                       (reg_ddrc_odtloff),
          .reg_ddrc_t_ccd_mw                      (reg_ddrc_t_ccd_mw),
          .reg_ddrc_rd2mr                         (reg_ddrc_rd2mr),
          .reg_ddrc_wr2mr                         (reg_ddrc_wr2mr),
          .reg_ddrc_use_slow_rm_in_low_temp       (reg_ddrc_use_slow_rm_in_low_temp),
          .reg_ddrc_dis_trefi_x6x8                (reg_ddrc_dis_trefi_x6x8),
          .reg_ddrc_dis_trefi_x0125               (reg_ddrc_dis_trefi_x0125),
          .reg_ddrc_t_ppd                         (reg_ddrc_t_ppd),
          .reg_ddrc_rd2wr_s                       (reg_ddrc_rd2wr_s),
          .reg_ddrc_mrr2rd                        (reg_ddrc_mrr2rd),
          .reg_ddrc_mrr2wr                        (reg_ddrc_mrr2wr),
          .reg_ddrc_mrr2mrw                       (reg_ddrc_mrr2mrw),
          .reg_ddrc_wck_on                        (reg_ddrc_wck_on),
          .reg_ddrc_wck_suspend_en                (reg_ddrc_wck_suspend_en),
          .reg_ddrc_ws_off_en                     (reg_ddrc_ws_off_en),
          .reg_ddrc_ws_off2ws_fs                  (reg_ddrc_ws_off2ws_fs),
          .reg_ddrc_t_wcksus                      (reg_ddrc_t_wcksus),
          .reg_ddrc_ws_fs2wck_sus                 (reg_ddrc_ws_fs2wck_sus),
          .reg_ddrc_max_rd_sync                   (reg_ddrc_max_rd_sync),
          .reg_ddrc_max_wr_sync                   (reg_ddrc_max_wr_sync),
          .reg_ddrc_dfi_twck_delay                (reg_ddrc_dfi_twck_delay),
          .reg_ddrc_dfi_twck_en_rd                (reg_ddrc_dfi_twck_en_rd),
          .reg_ddrc_dfi_twck_en_wr                (reg_ddrc_dfi_twck_en_wr),
          .reg_ddrc_dfi_twck_en_fs                (reg_ddrc_dfi_twck_en_fs),
          .reg_ddrc_dfi_twck_dis                  (reg_ddrc_dfi_twck_dis),
          .reg_ddrc_dfi_twck_fast_toggle          (reg_ddrc_dfi_twck_fast_toggle),
          .reg_ddrc_dfi_twck_toggle               (reg_ddrc_dfi_twck_toggle),
          .reg_ddrc_dfi_twck_toggle_cs            (reg_ddrc_dfi_twck_toggle_cs),
          .reg_ddrc_dfi_twck_toggle_post          (reg_ddrc_dfi_twck_toggle_post),
          .reg_ddrc_dfi_twck_toggle_post_rd_en    (reg_ddrc_dfi_twck_toggle_post_rd_en),
          .reg_ddrc_dfi_twck_toggle_post_rd       (reg_ddrc_dfi_twck_toggle_post_rd),
          .reg_ddrc_t_cke                         (reg_ddrc_t_cke),
          .reg_ddrc_t_faw                         (reg_ddrc_t_faw),
          .reg_ddrc_t_rfc_min                     (reg_ddrc_t_rfc_min),
          .reg_ddrc_t_rfc_min_ab                  (reg_ddrc_t_rfc_min_ab),
          .reg_ddrc_t_pbr2pbr                     (reg_ddrc_t_pbr2pbr),
          .reg_ddrc_t_pbr2act                     (reg_ddrc_t_pbr2act),
          .reg_ddrc_rfm_en                        (reg_ddrc_rfm_en),
          .reg_ddrc_dis_mrrw_trfc                 (reg_ddrc_dis_mrrw_trfc),
          .reg_ddrc_rfmsbc                        (reg_ddrc_rfmsbc),
          .reg_ddrc_raaimt                        (reg_ddrc_raaimt),
          .reg_ddrc_raamult                       (reg_ddrc_raamult),
          .reg_ddrc_raadec                        (reg_ddrc_raadec),
          .reg_ddrc_rfmth_rm_thr                  (reg_ddrc_rfmth_rm_thr),
          .reg_ddrc_init_raa_cnt                  (reg_ddrc_init_raa_cnt),
          .reg_ddrc_t_rfmpb                       (reg_ddrc_t_rfmpb),
          .reg_ddrc_dbg_raa_rank                  (reg_ddrc_dbg_raa_rank),
          .reg_ddrc_dbg_raa_bg_bank               (reg_ddrc_dbg_raa_bg_bank),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
          .ddrc_reg_dbg_raa_cnt                   (ddrc_reg_dbg_raa_cnt_w[n]),
          .ddrc_reg_rank_raa_cnt_gt0              (ddrc_reg_rank_raa_cnt_gt0_w[n]),
//spyglass enable_block W528
          .reg_ddrc_t_refi_x1_sel                 (reg_ddrc_t_refi_x1_sel),
          .reg_ddrc_refresh_to_x1_sel             (reg_ddrc_refresh_to_x1_sel),
          .reg_ddrc_t_refi_x1_x32                 (reg_ddrc_t_refi_x1_x32),
          .reg_ddrc_t_mr                          (reg_ddrc_t_mr),
          .reg_ddrc_refresh_to_x1_x32             (reg_ddrc_refresh_to_x1_x32),
          .reg_ddrc_en_2t_timing_mode             (reg_ddrc_en_2t_timing_mode),
          .reg_ddrc_opt_wrcam_fill_level          (reg_ddrc_opt_wrcam_fill_level),
          .reg_ddrc_delay_switch_write            (reg_ddrc_delay_switch_write),
          .reg_ddrc_wr_pghit_num_thresh           (reg_ddrc_wr_pghit_num_thresh),
          .reg_ddrc_rd_pghit_num_thresh           (reg_ddrc_rd_pghit_num_thresh),
          .reg_ddrc_wrcam_highthresh              (reg_ddrc_wrcam_highthresh),
          .reg_ddrc_wrcam_lowthresh               (reg_ddrc_wrcam_lowthresh),
          .reg_ddrc_wrecc_cam_highthresh                   (reg_ddrc_wrecc_cam_highthresh),
          .reg_ddrc_wrecc_cam_lowthresh                    (reg_ddrc_wrecc_cam_lowthresh),
          .reg_ddrc_dis_opt_valid_wrecc_cam_fill_level     (reg_ddrc_dis_opt_valid_wrecc_cam_fill_level),
          .reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level    (reg_ddrc_dis_opt_loaded_wrecc_cam_fill_level),
          .reg_ddrc_wr_page_exp_cycles            (reg_ddrc_wr_page_exp_cycles),
          .reg_ddrc_rd_page_exp_cycles            (reg_ddrc_rd_page_exp_cycles),
          .reg_ddrc_wr_act_idle_gap               (reg_ddrc_wr_act_idle_gap),
          .reg_ddrc_rd_act_idle_gap               (reg_ddrc_rd_act_idle_gap),
          .reg_ddrc_dis_opt_ntt_by_act            (reg_ddrc_dis_opt_ntt_by_act),
          .reg_ddrc_dis_opt_ntt_by_pre            (reg_ddrc_dis_opt_ntt_by_pre),
          .reg_ddrc_dis_opt_wrecc_collision_flush (reg_ddrc_dis_opt_wrecc_collision_flush),
          .reg_ddrc_prefer_write                  (reg_ddrc_prefer_write),
          .reg_ddrc_rdwr_idle_gap                 (reg_ddrc_rdwr_idle_gap),
          .reg_ddrc_powerdown_en                  (reg_ddrc_powerdown_en),
          .reg_ddrc_powerdown_to_x32              (reg_ddrc_powerdown_to_x32),
          .reg_ddrc_t_xp                          (reg_ddrc_t_xp),
          .reg_ddrc_selfref_sw                    (reg_ddrc_selfref_sw),
          .reg_ddrc_hw_lp_en                      (reg_ddrc_hw_lp_en),
          .reg_ddrc_hw_lp_exit_idle_en            (reg_ddrc_hw_lp_exit_idle_en),
          .reg_ddrc_selfref_to_x32                (reg_ddrc_selfref_to_x32),
          .reg_ddrc_hw_lp_idle_x32                (reg_ddrc_hw_lp_idle_x32),
          .reg_ddrc_dfi_t_ctrlupd_interval_min_x1024  (reg_ddrc_dfi_t_ctrlupd_interval_min_x1024),
          .reg_ddrc_dfi_t_ctrlupd_interval_max_x1024  (reg_ddrc_dfi_t_ctrlupd_interval_max_x1024),
          .reg_ddrc_dfi_t_ctrlupd_burst_interval_x8   (reg_ddrc_dfi_t_ctrlupd_burst_interval_x8),
          .reg_ddrc_dfi_t_ctrlupd_interval_type1      (reg_ddrc_dfi_t_ctrlupd_interval_type1),
          .reg_ddrc_dfi_t_ctrlupd_interval_type1_unit (reg_ddrc_dfi_t_ctrlupd_interval_type1_unit),
          .reg_ddrc_selfref_en                    (reg_ddrc_selfref_en),

          .reg_ddrc_mr_rank                       (reg_ddrc_mr_rank),
          .reg_ddrc_t_xsr                         (reg_ddrc_t_xsr),

          .reg_ddrc_refresh_update_level          (reg_ddrc_refresh_update_level),
          .reg_ddrc_refresh_timer0_start_value_x32  (reg_ddrc_refresh_timer0_start_value_x32),
          .reg_ddrc_refresh_timer1_start_value_x32  (reg_ddrc_refresh_timer1_start_value_x32),
          .reg_ddrc_rank0_wr_odt                  (reg_ddrc_rank0_wr_odt),
          .reg_ddrc_rank0_rd_odt                  (reg_ddrc_rank0_rd_odt),
          .reg_ddrc_rank1_wr_odt                  (reg_ddrc_rank1_wr_odt),
          .reg_ddrc_rank1_rd_odt                  (reg_ddrc_rank1_rd_odt),
          .reg_ddrc_hpr_xact_run_length           (reg_ddrc_hpr_xact_run_length),
          .reg_ddrc_hpr_max_starve                (reg_ddrc_hpr_max_starve),
          .reg_ddrc_lpr_xact_run_length           (reg_ddrc_lpr_xact_run_length),
          .reg_ddrc_lpr_max_starve                (reg_ddrc_lpr_max_starve),
          .reg_ddrc_w_xact_run_length             (reg_ddrc_w_xact_run_length),
          .reg_ddrc_w_max_starve                  (reg_ddrc_w_max_starve),
          .reg_ddrc_dfi_t_ctrlup_min              (reg_ddrc_dfi_t_ctrlup_min),
          .reg_ddrc_dfi_t_ctrlup_max              (reg_ddrc_dfi_t_ctrlup_max),
          .reg_ddrc_read_latency                  (reg_ddrc_read_latency),
          .rl_plus_cmd_len                        (rl_plus_cmd_len),
          .reg_ddrc_diff_rank_rd_gap              (reg_ddrc_diff_rank_rd_gap),
          .reg_ddrc_diff_rank_wr_gap              (reg_ddrc_diff_rank_wr_gap),
          .reg_ddrc_rd2wr_dr                      (reg_ddrc_rd2wr_dr),
          .reg_ddrc_wr2rd_dr                      (reg_ddrc_wr2rd_dr),
          .reg_ddrc_max_rank_rd                   (reg_ddrc_max_rank_rd),
          .reg_ddrc_max_rank_wr                   (reg_ddrc_max_rank_wr),
          .reg_ddrc_active_ranks                  (reg_ddrc_active_ranks),
          .reg_ddrc_dis_max_rank_rd_opt           (reg_ddrc_dis_max_rank_rd_opt),
          .reg_ddrc_dis_max_rank_wr_opt           (reg_ddrc_dis_max_rank_wr_opt),
          .reg_ddrc_ecc_type                      (reg_ddrc_ecc_type),
          .reg_ddrc_ecc_mode                      (reg_ddrc_ecc_mode),
          .reg_ddrc_ecc_ap_en                     (reg_ddrc_ecc_ap_en),
          .reg_ddrc_ecc_region_remap_en           (reg_ddrc_ecc_region_remap_en),
          .reg_ddrc_ecc_region_map                (reg_ddrc_ecc_region_map),
          .reg_ddrc_ecc_region_map_granu          (reg_ddrc_ecc_region_map_granu),
          .reg_ddrc_ecc_region_map_other          (reg_ddrc_ecc_region_map_other),
          .reg_ddrc_ecc_region_parity_lock        (reg_ddrc_ecc_region_parity_lock),
          .reg_ddrc_ecc_region_waste_lock         (reg_ddrc_ecc_region_waste_lock),
          .reg_ddrc_blk_channel_idle_time_x32     (reg_ddrc_blk_channel_idle_time_x32),
          .reg_ddrc_active_blk_channel            (reg_ddrc_active_blk_channel),
          .reg_ddrc_blk_channel_active_term       (reg_ddrc_blk_channel_active_term),
          .reg_ddrc_addrmap_bank_b0               (reg_ddrc_addrmap_bank_b0),
          .reg_ddrc_addrmap_bank_b1               (reg_ddrc_addrmap_bank_b1),
          .reg_ddrc_addrmap_bank_b2               (reg_ddrc_addrmap_bank_b2),
          .reg_ddrc_addrmap_bg_b0                 (reg_ddrc_addrmap_bg_b0),
          .reg_ddrc_addrmap_bg_b1                 (reg_ddrc_addrmap_bg_b1),
          .reg_ddrc_addrmap_cs_bit0               (reg_ddrc_addrmap_cs_bit0),
          .reg_ddrc_addrmap_col_b3                (reg_ddrc_addrmap_col_b3),
          .reg_ddrc_addrmap_col_b4                (reg_ddrc_addrmap_col_b4),
          .reg_ddrc_addrmap_col_b5                (reg_ddrc_addrmap_col_b5),
          .reg_ddrc_addrmap_col_b6                (reg_ddrc_addrmap_col_b6),
          .reg_ddrc_addrmap_col_b7                (reg_ddrc_addrmap_col_b7),
          .reg_ddrc_addrmap_col_b8                (reg_ddrc_addrmap_col_b8),
          .reg_ddrc_addrmap_col_b9                (reg_ddrc_addrmap_col_b9),
          .reg_ddrc_addrmap_col_b10               (reg_ddrc_addrmap_col_b10),
          .reg_ddrc_addrmap_row_b0                (reg_ddrc_addrmap_row_b0),
          .reg_ddrc_addrmap_row_b1                (reg_ddrc_addrmap_row_b1),
          .reg_ddrc_addrmap_row_b2                (reg_ddrc_addrmap_row_b2),
          .reg_ddrc_addrmap_row_b3                (reg_ddrc_addrmap_row_b3),
          .reg_ddrc_addrmap_row_b4                (reg_ddrc_addrmap_row_b4),
          .reg_ddrc_addrmap_row_b5                (reg_ddrc_addrmap_row_b5),
          .reg_ddrc_addrmap_row_b6                (reg_ddrc_addrmap_row_b6),
          .reg_ddrc_addrmap_row_b7                (reg_ddrc_addrmap_row_b7),
          .reg_ddrc_addrmap_row_b8                (reg_ddrc_addrmap_row_b8),
          .reg_ddrc_addrmap_row_b9                (reg_ddrc_addrmap_row_b9),
          .reg_ddrc_addrmap_row_b10               (reg_ddrc_addrmap_row_b10),
          .reg_ddrc_addrmap_row_b11               (reg_ddrc_addrmap_row_b11),
          .reg_ddrc_addrmap_row_b12               (reg_ddrc_addrmap_row_b12),
          .reg_ddrc_addrmap_row_b13               (reg_ddrc_addrmap_row_b13),
          .reg_ddrc_addrmap_row_b14               (reg_ddrc_addrmap_row_b14),
          .reg_ddrc_addrmap_row_b15               (reg_ddrc_addrmap_row_b15),
          .reg_ddrc_addrmap_row_b16               (reg_ddrc_addrmap_row_b16),
          .reg_ddrc_addrmap_row_b17               (reg_ddrc_addrmap_row_b17),
          .reg_ddrc_bank_hash_en                           (reg_ddrc_bank_hash_en),
          .reg_ddrc_dis_auto_zq                   (reg_ddrc_dis_auto_zq),
          .reg_ddrc_dis_srx_zqcl                  (reg_ddrc_dis_srx_zqcl),
          .reg_ddrc_dis_srx_zqcl_hwffc            (reg_ddrc_dis_srx_zqcl_hwffc),
          .reg_ddrc_zq_resistor_shared            (reg_ddrc_zq_resistor_shared),
          .reg_ddrc_t_zq_long_nop                 (reg_ddrc_t_zq_long_nop),
          .reg_ddrc_t_zq_short_nop                (reg_ddrc_t_zq_short_nop),
          .reg_ddrc_t_zq_short_interval_x1024     (reg_ddrc_t_zq_short_interval_x1024),
          .reg_ddrc_zq_calib_short                (reg_ddrc_zq_calib_short),
          .reg_ddrc_lpddr5x                       (reg_ddrc_lpddr5x),
          .reg_ddrc_per_bank_refresh              (reg_ddrc_per_bank_refresh),
          .reg_ddrc_per_bank_refresh_opt_en       (reg_ddrc_per_bank_refresh_opt_en),
          .reg_ddrc_fixed_crit_refpb_bank_en      (reg_ddrc_fixed_crit_refpb_bank_en),
          .reg_ddrc_auto_refab_en                 (reg_ddrc_auto_refab_en),
          .reg_ddrc_refresh_to_ab_x32             (reg_ddrc_refresh_to_ab_x32),          
          .reg_ddrc_lpddr4                        (reg_ddrc_lpddr4),
          .reg_ddrc_lpddr5                        (reg_ddrc_lpddr5),
          .reg_ddrc_bank_org                      (reg_ddrc_bank_org),
          .reg_ddrc_lpddr4_diff_bank_rwa2pre      (reg_ddrc_lpddr4_diff_bank_rwa2pre),
          .reg_ddrc_stay_in_selfref               (reg_ddrc_stay_in_selfref),
          .reg_ddrc_t_cmdcke                      (reg_ddrc_t_cmdcke),
          .reg_ddrc_dsm_en                        (reg_ddrc_dsm_en),
          .reg_ddrc_t_pdn                         (reg_ddrc_t_pdn),
          .reg_ddrc_t_xsr_dsm_x1024               (reg_ddrc_t_xsr_dsm_x1024),
          .reg_ddrc_t_csh                         (reg_ddrc_t_csh),
          .reg_ddrc_nonbinary_device_density      (reg_ddrc_nonbinary_device_density),
          .dfi_phyupd_req                         (cp_dfiif.dfi_phyupd_req),
          .dfi_phymstr_req                        (cp_dfiif.dfi_phymstr_req),
          .dfi_phymstr_cs_state                   (cp_dfiif.dfi_phymstr_cs_state),
          .dfi_phymstr_state_sel                  (cp_dfiif.dfi_phymstr_state_sel),
          .dfi_phymstr_type                       (cp_dfiif.dfi_phymstr_type),
          .reg_ddrc_dfi_phyupd_en                 (reg_ddrc_dfi_phyupd_en),
          .reg_ddrc_dfi_phymstr_en                (reg_ddrc_dfi_phymstr_en),
          .reg_ddrc_dfi_phymstr_blk_ref_x32       (reg_ddrc_dfi_phymstr_blk_ref_x32),
          .reg_ddrc_dis_cam_drain_selfref         (reg_ddrc_dis_cam_drain_selfref),
          .reg_ddrc_lpddr4_sr_allowed             (reg_ddrc_lpddr4_sr_allowed),
          .reg_ddrc_lpddr4_opt_act_timing         (reg_ddrc_lpddr4_opt_act_timing),
          .reg_ddrc_lpddr5_opt_act_timing         (reg_ddrc_lpddr5_opt_act_timing),
          .reg_ddrc_dfi_t_ctrl_delay              (reg_ddrc_dfi_t_ctrl_delay),
          .reg_ddrc_dfi_t_wrdata_delay            (reg_ddrc_dfi_t_wrdata_delay),
          .reg_ddrc_dfi_t_dram_clk_disable        (reg_ddrc_dfi_t_dram_clk_disable),
          .reg_ddrc_dfi_t_dram_clk_enable         (reg_ddrc_dfi_t_dram_clk_enable),
          .reg_ddrc_t_cksre                       (reg_ddrc_t_cksre),
          .reg_ddrc_t_cksrx                       (reg_ddrc_t_cksrx),
          .reg_ddrc_t_ckcsx                       (reg_ddrc_t_ckcsx),
          .reg_ddrc_t_ckesr                       (reg_ddrc_t_ckesr),
          .dfi_lp_ctrl_ack                        (cp_dfiif.dfi_lp_ctrl_ack),
          .dfi_lp_data_ack                        (cp_dfiif.dfi_lp_data_ack),
          .reg_ddrc_dfi_lp_data_req_en            (reg_ddrc_dfi_lp_data_req_en),
          .reg_ddrc_dfi_lp_en_data                (reg_ddrc_dfi_lp_en_data),
          .reg_ddrc_dfi_lp_wakeup_data            (reg_ddrc_dfi_lp_wakeup_data),
          .reg_ddrc_dfi_lp_en_pd                  (reg_ddrc_dfi_lp_en_pd),
          .reg_ddrc_dfi_lp_wakeup_pd              (reg_ddrc_dfi_lp_wakeup_pd),
          .reg_ddrc_dfi_lp_en_sr                  (reg_ddrc_dfi_lp_en_sr),
          .reg_ddrc_dfi_lp_wakeup_sr              (reg_ddrc_dfi_lp_wakeup_sr),
          .reg_ddrc_dfi_lp_en_dsm                 (reg_ddrc_dfi_lp_en_dsm),
          .reg_ddrc_dfi_lp_wakeup_dsm             (reg_ddrc_dfi_lp_wakeup_dsm),
          .reg_ddrc_skip_dram_init                (reg_ddrc_skip_dram_init),
          .reg_ddrc_dfi_tlp_resp                  (reg_ddrc_dfi_tlp_resp),
          .reg_ddrc_target_frequency              (reg_ddrc_target_frequency),
          .reg_ddrc_t_vrcg_enable                 (reg_ddrc_t_vrcg_enable),
          .reg_ddrc_t_vrcg_disable                (reg_ddrc_t_vrcg_disable),
          .reg_ddrc_target_vrcg                   (reg_ddrc_target_vrcg),
          .reg_ddrc_hwffc_en                      (reg_ddrc_hwffc_en),
          .reg_ddrc_hwffc_mode                    (reg_ddrc_hwffc_mode),
          .reg_ddrc_init_fsp                      (reg_ddrc_init_fsp),
          .reg_ddrc_t_zq_stop                     (reg_ddrc_t_zq_stop),
          .reg_ddrc_zq_interval                   (reg_ddrc_zq_interval),
          .reg_ddrc_skip_zq_stop_start            (reg_ddrc_skip_zq_stop_start),
          .reg_ddrc_init_vrcg                     (reg_ddrc_init_vrcg),
          .reg_ddrc_skip_mrw_odtvref              (reg_ddrc_skip_mrw_odtvref),
          .reg_ddrc_dvfsq_enable                  (reg_ddrc_dvfsq_enable),
          .reg_ddrc_dvfsq_enable_next             (reg_ddrc_dvfsq_enable_next),
          .xpi_ddrc_port_disable_ack              (xpi_ddrc_port_disable_ack),
          .xpi_ddrc_wch_locked                    (xpi_ddrc_wch_locked),




          .mr_ih_free_bwt_vld                     (i_mr_ih_cpfdpif.mr_ih_free_bwt_vld),
          .mr_ih_free_bwt                         (i_mr_ih_cpfdpif.mr_ih_free_bwt),
          .rd_ih_free_brt_vld                     (i_rd_ih_cpfdpif.rd_ih_free_brt_vld),
          .rd_ih_free_brt                         (i_rd_ih_cpfdpif.rd_ih_free_brt),
          .mr_ih_lkp_brt_by_bt                    (i_mr_ih_cpfdpif.mr_ih_lkp_brt_by_bt),
          .mr_ih_lkp_bwt_by_bt                    (i_mr_ih_cpfdpif.mr_ih_lkp_bwt_by_bt),
          .rd_ih_lkp_brt_by_bt                    (i_rd_ih_cpfdpif.rd_ih_lkp_brt_by_bt),
          .rd_ih_lkp_bwt_by_bt                    (i_rd_ih_cpfdpif.rd_ih_lkp_bwt_by_bt),
          .rd_ih_ie_re_rdy                        (rd_ih_ie_re_rdy),
          .hif_mrr_data                           (hif_mrr_data),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in DDR5
          .sw_wr_data_valid                       (sw_wr_data_valid_w[n]                 ),
          .sw_wr_data                             (sw_wr_data_w[n]                       ),
          .sw_wr_data_mask                        (sw_wr_data_mask_w[n]                  ),
          .ci_manual_wr_mode                      (ci_manual_wr_mode_w[n]                ), // used for open ddrc_cg_en
          .ci_manual_rd_mode                      (ci_manual_rd_mode_w[n]                ), // used for open ddrc_cg_en
          .sw_wr_ecc                              (sw_wr_ecc_w[n]                        ),
          .sw_wr_ecc_mask                         (sw_wr_ecc_mask_w[n]                   ),
          .ddrc_reg_rd_data_dq0                   (ddrc_reg_rd_data_dq0_w[n]             ),
          .ddrc_reg_rd_data_dq1                   (ddrc_reg_rd_data_dq1_w[n]             ),
          .ci_wr_crc_enable_mask_n                (ci_wr_crc_enable_mask_n_w[n]          ),
//spyglass enable_block W528
          .rd_mr4_data_valid                      (rd_mr4_data_valid),
          .rt_rd_rd_mrr_ext                       (rt_rd_rd_mrr_ext),
          .mr_yy_free_wr_entry_valid              (i_mr_ih_cpfdpif.mr_yy_free_wr_entry_valid),
          .mr_yy_free_wr_entry                    (i_mr_ih_cpfdpif.mr_yy_free_wr_entry),
          .mr_gs_empty                            (i_mr_gs_ddrc_cpedpif.mr_gs_empty),
          .dfi_wr_q_empty                         (dfi_wr_q_empty),
          .rt_gs_empty                            (rt_gs_empty),
          .rt_gs_empty_delayed                    (rt_gs_empty_delayed),
          .wu_ih_flow_cntrl_req                   (i_wu_ih_cpfdpif.wu_ih_flow_cntrl_req),
          .wu_te_enable_wr                        (i_wu_te_cpfdpif.wu_te_enable_wr),
          .wu_te_entry_num                        (i_wu_te_cpfdpif.wu_te_entry_num),
          .wu_te_mwr                              (i_wu_te_cpfdpif.wu_te_mwr),
          .wu_te_wr_word_valid                    (i_wu_te_cpfdpif.wu_te_wr_word_valid),
          .wu_te_ram_raddr_lsb_first              (i_wu_te_cpfdpif.wu_te_ram_raddr_lsb_first),
          .wu_te_pw_num_beats_m1                  (i_wu_te_cpfdpif.wu_te_pw_num_beats_m1),
          .wu_te_pw_num_cols_m1                   (i_wu_te_cpfdpif.wu_te_pw_num_cols_m1),
          .wu_gs_enable_wr                        (i_wu_gs_ddrc_cpedpif.wu_gs_enable_wr),
          .ddrc_cg_en                             (ddrc_cg_en),
          .mr_t_wrlat                             (mr_t_wrlat),
          .mr_t_wrdata                            (mr_t_wrdata),
          .mr_t_rddata_en                         (mr_t_rddata_en),
          .mr_lp_data_rd                          (mr_lp_data_rd),
          .mr_lp_data_wr                          (mr_lp_data_wr),
          .dfi_cmd_delay                          (dfi_cmd_delay),
          .reg_ddrc_dis_dqsosc_srx      (reg_ddrc_dis_dqsosc_srx),
          .reg_ddrc_dqsosc_enable       (reg_ddrc_dqsosc_enable),
          .reg_ddrc_t_osco              (reg_ddrc_t_osco),
          .reg_ddrc_dqsosc_runtime      (reg_ddrc_dqsosc_runtime),
          .reg_ddrc_wck2dqo_runtime     (reg_ddrc_wck2dqo_runtime),
          .reg_ddrc_dqsosc_interval     (reg_ddrc_dqsosc_interval),
          .reg_ddrc_dqsosc_interval_unit(reg_ddrc_dqsosc_interval_unit),
`ifdef SNPS_ASSERT_ON
          .reg_ddrc_data_bus_width                 (reg_ddrc_data_bus_width),
`endif // SNPS_ASSERT_ON
`ifndef SYNTHESIS
  `ifdef SNPS_ASSERT_ON
          .reg_ddrc_rd_link_ecc_enable  (reg_ddrc_rd_link_ecc_enable),
  `endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under LPDDR45_DQSOSC in this file but signal should always exist for OCCAP
          .dqsosc_state                 (dqsosc_state_w[n]),
          .dfi_snoop_running            (dfi_snoop_running_w[n]),
          .dqsosc_per_rank_stat         (dqsosc_per_rank_stat_w[n]),
          .pi_ph_snoop_en               (pi_ph_snoop_en_w[n]),
          .pi_rt_rd_mrr_snoop           (pi_rt_rd_mrr_snoop_w[n]),
//spyglass enable_block W528
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only DDR5 in this file but signal should always exist for OCCAP
          .ddrc_reg_dbg_rank_ctrl_mc_code_0        (ddrc_reg_dbg_rank_ctrl_mc_code_0_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_addr_0        (ddrc_reg_dbg_rank_ctrl_mc_addr_0_w[n]),
          .ddrc_reg_dbg_rank_ctrl_state_rsm_0      (ddrc_reg_dbg_rank_ctrl_state_rsm_0_w[n]),
          .ddrc_reg_dbg_mceu_ctrl_state_mceu_0     (ddrc_reg_dbg_mceu_ctrl_state_mceu_0_w[n]),
          .ddrc_reg_dbg_sceu_ctrl_state_sceu_0     (ddrc_reg_dbg_sceu_ctrl_state_sceu_0_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_code_1        (ddrc_reg_dbg_rank_ctrl_mc_code_1_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_addr_1        (ddrc_reg_dbg_rank_ctrl_mc_addr_1_w[n]),
          .ddrc_reg_dbg_rank_ctrl_state_rsm_1      (ddrc_reg_dbg_rank_ctrl_state_rsm_1_w[n]),
          .ddrc_reg_dbg_mceu_ctrl_state_mceu_1     (ddrc_reg_dbg_mceu_ctrl_state_mceu_1_w[n]),
          .ddrc_reg_dbg_sceu_ctrl_state_sceu_1     (ddrc_reg_dbg_sceu_ctrl_state_sceu_1_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_code_2        (ddrc_reg_dbg_rank_ctrl_mc_code_2_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_addr_2        (ddrc_reg_dbg_rank_ctrl_mc_addr_2_w[n]),
          .ddrc_reg_dbg_rank_ctrl_state_rsm_2      (ddrc_reg_dbg_rank_ctrl_state_rsm_2_w[n]),
          .ddrc_reg_dbg_mceu_ctrl_state_mceu_2     (ddrc_reg_dbg_mceu_ctrl_state_mceu_2_w[n]),
          .ddrc_reg_dbg_sceu_ctrl_state_sceu_2     (ddrc_reg_dbg_sceu_ctrl_state_sceu_2_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_code_3        (ddrc_reg_dbg_rank_ctrl_mc_code_3_w[n]),
          .ddrc_reg_dbg_rank_ctrl_mc_addr_3        (ddrc_reg_dbg_rank_ctrl_mc_addr_3_w[n]),
          .ddrc_reg_dbg_rank_ctrl_state_rsm_3      (ddrc_reg_dbg_rank_ctrl_state_rsm_3_w[n]),
          .ddrc_reg_dbg_mceu_ctrl_state_mceu_3     (ddrc_reg_dbg_mceu_ctrl_state_mceu_3_w[n]),
          .ddrc_reg_dbg_sceu_ctrl_state_sceu_3     (ddrc_reg_dbg_sceu_ctrl_state_sceu_3_w[n]),
          .ddrc_reg_dbg_hw_lp_state_hsm            (ddrc_reg_dbg_hw_lp_state_hsm_w[n]),
          .ddrc_reg_dbg_dfi_lp_ctrl_ack            (ddrc_reg_dbg_dfi_lp_ctrl_ack_w[n]),
          .ddrc_reg_dbg_dfi_lp_data_ack            (ddrc_reg_dbg_dfi_lp_data_ack_w[n]),
          .ddrc_reg_dbg_dfi_lp_state_dsm           (ddrc_reg_dbg_dfi_lp_state_dsm_w[n]),
          .ddrc_reg_dbg_capar_retry_mc_code        (ddrc_reg_dbg_capar_retry_mc_code_w[n]),
          .ddrc_reg_dbg_capar_retry_mc_addr        (ddrc_reg_dbg_capar_retry_mc_addr_w[n]),
          .ddrc_reg_dbg_capar_retry_state_csm      (ddrc_reg_dbg_capar_retry_state_csm_w[n]),
          .ddrc_reg_dbg_capar_retry_state_mceu     (ddrc_reg_dbg_capar_retry_state_mceu_w[n]),
          .ddrc_reg_dbg_capar_retry_state_sceu     (ddrc_reg_dbg_capar_retry_state_sceu_w[n]),
          .ddrc_reg_cmdfifo_rd_data                (ddrc_reg_cmdfifo_rd_data_w[n]),
          .ddrc_reg_cmdfifo_overflow               (ddrc_reg_cmdfifo_overflow_w[n]),
          .ddrc_reg_cmdfifo_recorded_cmd_num       (ddrc_reg_cmdfifo_recorded_cmd_num_w[n]),
          .ddrc_reg_cmdfifo_window_cmd_num         (ddrc_reg_cmdfifo_window_cmd_num_w[n]),
//spyglass enable_block W528
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under DDRCTL_DFI_CTRLMSG in this file but signal should always exist for OCCAP
          .ddrc_reg_dfi0_ctrlmsg_req_busy          (ddrc_reg_dfi0_ctrlmsg_req_busy_w[n]),
          .ddrc_reg_dfi0_ctrlmsg_resp_tout         (ddrc_reg_dfi0_ctrlmsg_resp_tout_w[n]),
          .dfi_ctrlmsg_req                         (dfi_ctrlmsg_req_w[n]),
          .dfi_ctrlmsg                             (dfi_ctrlmsg_w[n]),
          .dfi_ctrlmsg_data                        (dfi_ctrlmsg_data_w[n])
//spyglass enable_block W528
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under Write CRC Retry in this file but signal should always exist for OCCAP
          ,.ih_wu_is_retry_wr                      (ih_wu_is_retry_wr_w[n])
          ,.ih_wu_wr_pw_num_beats_m1               (ih_wu_wr_pw_num_beats_m1_w[n])
          ,.retryctrl_head_exp                     (retryctrl_head_exp_w[n])
          ,.capar_retry_start                      (capar_retry_start_w[n])
          ,.capar_rd_expired                       (capar_rd_expired_w[n])
          ,.capar_rddata_en                        (capar_rddata_en_w[n])
          ,.dbg_capar_retry_pulse                  (dbg_capar_retry_pulse_w[n])
          ,.ddrc_reg_ppr_done                      (ddrc_reg_ppr_done_w[n])
//spyglass enable_block W528
         ,.ih_wu_wr_eapar                          (ih_wu_wr_eapar_w[n])
         ,.reg_ddrc_ppt2_en                        (reg_ddrc_ppt2_en)
         ,.reg_ddrc_ppt2_override                  (reg_ddrc_ppt2_override)
         ,.reg_ddrc_ctrlupd_after_dqsosc           (reg_ddrc_ctrlupd_after_dqsosc)
         ,.reg_ddrc_ppt2_wait_ref                  (reg_ddrc_ppt2_wait_ref)
         ,.reg_ddrc_ppt2_burst_num                 (reg_ddrc_ppt2_burst_num)
         ,.reg_ddrc_ppt2_burst                     (reg_ddrc_ppt2_burst)
         ,.reg_ddrc_ppt2_ctrlupd_num_dfi1          (reg_ddrc_ppt2_ctrlupd_num_dfi1)
         ,.reg_ddrc_ppt2_ctrlupd_num_dfi0          (reg_ddrc_ppt2_ctrlupd_num_dfi0)
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under DDRCTL_PPT2 in this file but signal should always exist for OCCAP
         ,.ddrc_reg_ppt2_burst_busy                (ddrc_reg_ppt2_burst_busy_w[n])
         ,.ddrc_reg_ppt2_state                     (ddrc_reg_ppt2_state_w[n])
//spyglass enable_block W528
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in only under DDRCTL_SECURE in this file but signal should always exist for OCCAP
         ,.t_hif_addr                              (t_hif_addr_w[n])
//spyglass enable_block W528
    );

    //JIRA___ID: those signals are removed from IH and MR, but just keep here to avoid modify the signals's number
         // ih_mr_ie_pw is removed from IH and MR,
         assign ih_mr_ie_pw_w[n]      = {IE_PW_BITS{1'b0}};

    end // ddrc_ctrl_inst

    if (OCCAP_EN==1) begin: CMP_en

// spyglass disable_block W164b
// SMD: LHS: 'cmp_in0' width 2903 is greater than RHS:
// SJ: Waived for Backward compatibility
      // drive vectored inputs to comparator
      wire [OUT_TOTW-1:0] cmp_in0, cmp_in1;

      assign cmp_in0 = {
                        clk_te_en_w[0],
                        t_hif_addr_w[0],
                        dfi_hif_cmd_keyid_w[0],
                        pi_rd_eccap_w[0],
                        ddrc_reg_ppr_done_w[0],
                        dbg_capar_retry_pulse_w[0],
                        ih_wu_wr_eapar,
                        bsm_clk_en_w[0],
                        gs_mr_pw_num_beats_m1_w[0],
                        gs_mr_ram_raddr_lsb_first_w[0],
                        gs_wr_bc_sel_w[0],
                        ih_wu_is_retry_wr_w[0],
                        ih_wu_wr_pw_num_beats_m1_w[0],
                        retryctrl_head_exp_w[0],
                        capar_retry_start_w[0],
                        capar_rd_expired_w[0],
                        capar_rddata_en_w[0],
                        ddrc_reg_max_num_alloc_bsm,
                        ddrc_reg_max_num_unalloc_entries,
                        ddrc_reg_cmd_rslt_w   [0],
                        ddrc_reg_swcmd_lock_w [0],
                        ddrc_reg_ducmd_lock_w [0],
                        ddrc_reg_lccmd_lock_w [0],
                        ddrc_reg_prank3_mode_w[0],
                        ddrc_reg_prank2_mode_w[0],
                        ddrc_reg_prank1_mode_w[0],
                        ddrc_reg_prank0_mode_w[0],
                        ddrc_reg_dbg_stat3_w[0],
                        ddrc_reg_dbg_stat2_w[0],
                        ddrc_reg_dbg_stat1_w[0],
                        ddrc_reg_dbg_stat0_w[0],
                        dch_sync_mode_o_w[0],
                        rank_idle_state_o_w[0],
                        rank_selfref_state_o_w[0],
                        selfref_idle_entry_o_w[0],
                        selfref_sw_entry_o_w[0],
                        selfref_hw_entry_o_w[0],
                        selfref_sw_o_w[0],
                        selfref_idle_exit_o_w[0],
                        selfref_sw_exit_o_w[0],
                        channel_message_o_w[0],
                        rank_selfref_operating_mode_o_w[0],
                        rank_selfref_swhw_state_o_w[0],
                        rank_selfref_tctrl_delay_ack_o_w[0],
                        dfi_lp_selfref_tlp_resp_ack_o_w[0],
                        hw_lp_exit_idle_o_w[0],
                        hw_lp_selfref_hw_o_w[0],

                        ddrc_reg_dfi_lp_state_w[0],
                        ddrc_reg_mpsm_state_w[0],
                        ddrc_reg_powerdown_state_w[0],
                        ddrc_reg_du_cfgbuf_rdata_w[0],
                        ddrc_reg_du_cmdbuf_rdata_w[0],
                        ddrc_reg_lp_cmdbuf_rdata_w[0],
                        ddrc_reg_capar_cmdbuf_rdata_w[0],
                        ddrc_reg_powerdown_ongoing_w[0],
                        ddrc_reg_selfref_ongoing_w[0],
                        dbg_prank_act_pd_w[0],
                        dbg_prank_pre_pd_w[0],
                        dbg_du_ucode_seq_ongoing_w[0],
                        dbg_lp_ucode_seq_ongoing_w[0],
                        ddrc_reg_du_cur_blk_set_w[0],
                        ddrc_reg_du_cur_blk_index_w[0],
                        ddrc_reg_du_cur_blk_addr_w[0],
                        ddrc_reg_du_cur_blk_ucode_w[0],
                        ddrc_reg_du_main_fsm_state_w[0],
                        ddrc_reg_glb_blk_events_ongoing_w[0],
                        ddrc_reg_rank_blk_events_ongoing_w[0],
                        ddrc_reg_du_mceu_fsm_state_w[0],
                        ddrc_reg_du_sceu_fsm_state_w[0],
                        ddrc_reg_caparcmd_err_intr_w[0],
                        ddrc_reg_caparcmd_err_sts_w[0],
                        ddrc_reg_lccmd_err_intr_w[0],
                        ddrc_reg_ducmd_err_intr_w[0],
                        ddrc_reg_swcmd_err_intr_w[0],
                        ddrc_reg_swcmd_err_sts_w[0],
                        ddrc_reg_ducmd_err_sts_w[0],
                        ddrc_reg_lccmd_err_sts_w[0],
                        ddrc_reg_rfm_alert_intr_w[0],
                        ddrc_reg_rfm_cmd_log_w[0],
                        ddrc_reg_2n_mode_w[0],
                        ddrc_reg_ecs_mr16_w[0],
                        ddrc_reg_ecs_mr17_w[0],
                        ddrc_reg_ecs_mr18_w[0],
                        ddrc_reg_ecs_mr19_w[0],
                        ddrc_reg_ecs_mr20_w[0],

                        perf_write_combine_noecc,
                        perf_write_combine_wrecc,
                        ddrc_reg_cmd_mrr_data_w[0],
                        ddrc_reg_cmd_done_w[0],
                        ddrc_reg_cmd_err_w[0],
                        ddrc_reg_ctrlupd_err_intr_w[0],
                        ddrc_reg_mrr_data_vld_w[0],
                        ddrc_reg_rd_data_vld_w[0],
                        pi_dfi_rddata_en_w[0],
                        pi_dfi_wrdata_en_w[0],
                        pi_rd_mrr_snoop_w[0],
                        pi_phy_snoop_en_w[0],
                        pi_rd_ph_nxt_w[0],
                        pi_rd_vld_nxt_w[0],
                        pi_wr_cs_nxt_w[0],
                        pi_wr_ph_nxt_w[0],
                        pi_wr_vld_nxt_w[0],
                        pi_rd_ie_blk_burst_num_w[0],
                        pi_rd_ie_rd_type_w[0],
                        pi_rd_ie_bt_w[0],
                        pi_rd_rankbank_w[0],
                        pi_rd_critical_word_w[0],
                        pi_rd_blk_w[0],
                        pi_rd_page_w[0],
                        pi_rd_wr_ram_addr_w[0],
                        pi_rd_rmw_type_w[0],
                        pi_rd_addr_err_w[0],
                        pi_rd_tag_w[0],
                        {HIF_KEYID_WIDTH{1'b0}},
                        pi_rd_mrr_ext_w[0],
                        pi_rd_partial_w[0],
                        pi_rd_vld_w[0],

                        dqsosc_per_rank_stat_w[0],
                        dqsosc_state_w[0],
                        dfi_snoop_running_w[0],
                        pi_rt_rd_mrr_snoop_w[0],
                        pi_ph_snoop_en_w[0],

                        dfi_wck_cs,
                        dfi_wck_en,
                        dfi_wck_toggle,
                        ih_mr_ie_wr_cnt_dec_vct,
                        core_derate_temp_limit_intr,
                        perf_op_is_spec_ref,
                        perf_op_is_crit_ref,
                        retry_dfi_wrdata_en,
                        o_pi_ddrc_cpedpif.pi_ph_dfi_wrdata_en,
                        perf_ie_blk_hazard,
                        ddrc_core_reg_dbg_wrecc_q_depth,
                        ddrc_reg_dbg_wrecc_q_depth,
                        hif_wrecc_credit,
                        ih_ie_busy,
                        o_te_cpfdpif.te_wu_ie_flowctrl_req,
                        gs_pi_op_is_exit_selfref,
                        ddrc_phy_cal_dl_enable,
                        reg_ddrc_fgr_mode_gated,
                        pi_gs_dll_off_mode,
                        reg_ddrc_ext_rank_refresh,
                        ih_busy,
                        pi_gs_mpr_mode,
                        mrr_op_on,
                        gs_pi_data_pipeline_empty,
                        reg_ddrc_active_ranks_int,
                        retry_dfi_rddata_en,
                        retry_phy_wdata_vld_early,
                        retry_phy_wdata,
                        retry_phy_dm,
                        retry_dfi_sel,
                        retry_rt_rd_timeout_value,
                        retry_rt_now_sw_intervention,
                        retry_rt_fatl_err_pulse,
                        retry_rt_fifo_init_n,
                        retry_rt_rdatavld_gate_en,
                        retry_fifo_empty,
                        gs_pi_cs_n,
                        pda_mode_pre,
                        pda_mode,
                        gs_mr_pda_data_sel,
                        gs_mr_load_mode_pda,
                        o_gs_ddrc_cpedpif.gs_mr_write,
                        o_te_cpfdpif.te_wu_wr_retry,
                        o_te_cpfdpif.te_wu_entry_num,
                        o_te_cpfdpif.te_mr_wr_ram_addr,
                        gs_pi_rdwr_pw_num_beats_m1,
                        gs_pi_rdwr_ram_raddr_lsb_first,
                        gs_pi_rdwr_bc_sel,
                        te_pi_wr_word_valid,
                        ts_pi_mwr,
                        ts_pi_wr32,
                        ts_pi_2nd_half,
                        ts_cam_clear_en,
                        te_yy_wr_combine,
                        te_wu_wrdata_stall_req,
                        o_pi_ddrc_cpedpif.pi_rt_critical_word,
                        o_pi_ddrc_cpedpif.pi_rt_block_num,
                        o_pi_ddrc_cpedpif.pi_rt_page_num,
                        o_pi_ddrc_cpedpif.pi_rt_rankbank_num,
                        pi_rt_rmwtype,
                        pi_rt_rmwcmd,
                        pi_rt_wr_ram_addr,
                        pi_rt_rd_addr_err,
                        o_pi_ddrc_cpedpif.pi_rt_rd_tag,
                        o_pi_ddrc_cpedpif.pi_rt_rd_vld,
                        o_pi_ddrc_cpedpif.pi_rt_rd_partial,
                        pi_gs_geardown_mode_on,
                        o_ih_cpfdpif.ih_wu_critical_word,
                        o_ih_cpfdpif.ih_wu_wr_entry,
                        o_ih_cpfdpif.ih_wu_rmw_type,
                        ih_te_wr_valid,
                        ih_te_rd_valid,
                        ih_wu_wr_valid_addr_err,
                        o_ih_cpfdpif.ih_wu_wr_valid,
                        o_pi_ddrc_cpedpif.pi_ph_dfi_rddata_en,
                        o_pi_ddrc_cpedpif.pi_rt_rd_mrr_ext,
                        o_pi_ddrc_cpedpif.pi_rt_rd_mrr,
                        ih_wu_cerr,
                        pi_rt_eccap,
                        te_mr_eccap,
                        ih_rd_lkp_bwt_vld,
                        ih_rd_lkp_bwt,
                        ih_rd_lkp_brt_vld,
                        ih_rd_lkp_brt,
                        ih_mr_lkp_brt_vld,
                        ih_mr_lkp_brt,
                        ih_mr_lkp_bwt_vld,
                        ih_mr_lkp_bwt,
                        pi_rt_ie_blk_burst_num,
                        pi_rt_ie_rd_type,
                        pi_rt_ie_bt,
                        te_mr_ie_blk_burst_num,
                        te_mr_ie_wr_type,
                        te_mr_ie_bt,
                        ih_mr_ie_brt_vld,
                        ih_mr_ie_brt,
                        ih_mr_ie_bwt,
                        ih_mr_ie_wr_cnt_inc,
                        ih_rd_ie_blk_rd_end,
                        ih_rd_ie_rd_cnt_inc,
                        ih_rd_ie_brt,
                        ih_mr_ie_pw,
                        ih_mr_ie_blk_wr_end,
                        hwffc_i_reg_ddrc_dis_auto_zq,
                        hwffc_hif_wd_stall,
                        ddrc_xpi_clock_required,
                        ddrc_xpi_port_disable_req,
                        ddrc_reg_hwffc_operating_mode,
                        ddrc_reg_current_vrcg,
                        ddrc_reg_current_fsp,
                        ddrc_reg_current_frequency,
                        ddrc_reg_hwffc_in_progress,
                        hwffc_target_freq_init,
                        hwffc_target_freq,
                        hwffc_target_freq_en,
                        dfi_lp_ctrl_wakeup_w[0],
                        dfi_lp_ctrl_req_w[0],
                        dfi_lp_data_wakeup_w[0],
                        dfi_lp_data_req_w[0],
                        dfi_phymstr_ack_w[0],
                        dfi_phyupd_ack_w[0],
                        hif_refresh_active,
                        hif_refresh_req_derate,
                        hif_refresh_req_cnt,
                        hif_refresh_req,
                        hif_refresh_req_bank,
                        ddrc_reg_zq_calib_short_busy,
                        ddrc_reg_rd_data_pipeline_empty,
                        ddrc_reg_wr_data_pipeline_empty,
                        ddrc_reg_rd_q_empty,
                        ddrc_reg_wr_q_empty,
                        ddrc_reg_selfref_type,
                        ddrc_reg_operating_mode,
                        ddrc_reg_selfref_state,
                        ddrc_reg_selfref_cam_not_empty_w[0],
                        ddrc_reg_dbg_stall_wr,
                        ddrc_reg_dbg_stall_rd,
                        ddrc_reg_dbg_stall,
                        ddrc_reg_dbg_w_q_depth,
                        ddrc_reg_dbg_lpr_q_depth,
                        ddrc_reg_dbg_hpr_q_depth,
                        dbg_dfi_parity_poison_w[0],
                        ddrc_reg_capar_poison_complete,
                        ddrc_reg_ctrlupd_busy,
                        ddrc_reg_ctrlupd_burst_busy_w[0],
                        ddrc_reg_rank_refresh_busy,
                        retryram_mask,
                        retryram_we,
                        retryram_re,
                        retryram_raddr,
                        retryram_waddr,
                        retryram_din_w[0],
                        ddrc_reg_retry_stat_w[0],
                        ddrc_reg_retry_fifo_fill_level_w[0],
                        ddrc_reg_wr_crc_err_max_reached_intr_w[0],
                        ddrc_reg_wr_crc_err_intr_w[0],
                        ddrc_reg_wr_crc_err_cnt_w[0],
                        ddrc_reg_capar_retry_limit_intr_w[0],
                        ddrc_reg_capar_fatl_err_intr_w[0],
                        ddrc_reg_capar_fatl_err_code_w[0],
                        ddrc_reg_capar_err_max_reached_intr_w[0],
                        ddrc_reg_capar_err_cnt_w[0],
                        ddrc_reg_capar_err_intr_w[0],
                        init_mr_done_out,
                        dfi_reset_n_ref,
                        dfi_2n_mode_w[0],
                        dfi_freq_fsp_w[0],
                        dfi_frequency_w[0],
                        dfi_init_start_w[0],
                        dfi_parity_in_w[0],
                        dfi_dram_clk_disable_w[0],
                        dfi_ctrlupd_req_w[0],
                        dfi_ctrlupd_type_w[0],
                        dfi_ctrlupd_target_w[0],
                        dfi_rddata_cs_w[0],
                        dfi_wrdata_cs_w[0],
                        dfi_reset_n_w[0],
                        dfi_odt_w[0],
                        dfi_cs_w[0],
                        dfi_cke_w[0],
                        dfi_we_n_w[0],
                        dfi_ras_n_w[0],
                        dfi_cas_n_w[0],
                        dfi_bank_w[0],
                        dfi_freq_ratio_w[0],
                        dfi_address_w[0],
                        dfi_cid_w[0],
                        dfi_act_n_w[0],
                        dfi_bg_w[0],
                        dfi_hif_cmd_addr_w[0],
                        dfi_hif_cmd_wdata_ptr_w[0],
                        ddrc_core_reg_dbg_rd_cam_63_56_valid,
                        ddrc_core_reg_dbg_wr_cam_63_56_valid,
                        ddrc_core_reg_dbg_rd_cam_55_48_valid,
                        ddrc_core_reg_dbg_wr_cam_55_48_valid,
                        ddrc_core_reg_dbg_rd_cam_47_40_valid,
                        ddrc_core_reg_dbg_wr_cam_47_40_valid,
                        ddrc_core_reg_dbg_rd_cam_39_32_valid,
                        ddrc_core_reg_dbg_wr_cam_39_32_valid,
                        ddrc_core_reg_dbg_rd_cam_31_24_valid,
                        ddrc_core_reg_dbg_wr_cam_31_24_valid,
                        ddrc_core_reg_dbg_rd_cam_23_16_valid,
                        ddrc_core_reg_dbg_wr_cam_23_16_valid,
                        ddrc_core_reg_dbg_rd_cam_15_8_valid,
                        ddrc_core_reg_dbg_wr_cam_15_8_valid,
                        ddrc_core_reg_dbg_rd_cam_7_0_valid,
                        ddrc_core_reg_dbg_wr_cam_7_0_valid,
                        ddrc_core_reg_dbg_wr_page_hit_rank_w[0],
                        ddrc_core_reg_dbg_wr_valid_rank_w[0],
                        ddrc_core_reg_dbg_rd_pri_rank_w[0],
                        ddrc_core_reg_dbg_rd_page_hit_rank_w[0],
                        ddrc_core_reg_dbg_rd_valid_rank_w[0],
                        ddrc_core_reg_dbg_hif_wcmd_stall,
                        ddrc_core_reg_dbg_hif_rcmd_stall,
                        ddrc_core_reg_dbg_hif_cmd_stall,
                        ddrc_core_reg_dbg_wr_q_depth,
                        ddrc_core_reg_dbg_hpr_q_depth,
                        ddrc_core_reg_dbg_lpr_q_depth,
                        ddrc_core_reg_dbg_wr_q_state,
                        ddrc_core_reg_dbg_hpr_q_state,
                        ddrc_core_reg_dbg_lpr_q_state,
                        ddrc_core_reg_dbg_ctrlupd_state,
                        ddrc_core_reg_dbg_init_next_state,
                        ddrc_core_reg_dbg_init_curr_state,
                        ddrc_core_reg_dbg_global_fsm_state,
                        ddrc_core_reg_dbg_operating_mode,
                        perf_num_alloc_bsm,
                        perf_visible_window_limit_reached_rd,
                        perf_visible_window_limit_reached_wr,
                        perf_bsm_starvation,
                        perf_bsm_alloc,
                        perf_bypass_cid,
                        perf_bypass_bg,
                        perf_bypass_bank,
                        perf_bypass_rank,
                        perf_cid,
                        perf_bg,
                        perf_bank,
                        perf_rank,
                        perf_op_is_zqcs,
                        perf_op_is_zqcl,
                        perf_op_is_load_mode,
                        perf_op_is_refresh,
                        perf_selfref_mode,
                        perf_op_is_enter_mpsm,
                        perf_op_is_enter_powerdown,
                        perf_op_is_enter_selfref,
                        perf_waw_hazard,
                        perf_raw_hazard,
                        perf_war_hazard,
                        perf_write_combine,
                        perf_rdwr_transitions,
                        perf_precharge_for_other,
                        perf_precharge_for_rdwr,
                        perf_op_is_precharge,
                        perf_op_is_mwr,
                        perf_op_is_wr16,
                        perf_op_is_wr32,
                        perf_op_is_rd16,
                        perf_op_is_rd32,
                        perf_op_is_cas,
                        perf_op_is_cas_ws,
                        perf_op_is_cas_ws_off,
                        perf_op_is_cas_wck_sus,
                        perf_op_is_enter_dsm,
                        perf_op_is_rfm,
                        perf_op_is_wr,
                        perf_op_is_rd,
                        perf_op_is_rd_activate,
                        perf_op_is_rd_or_wr,
                        perf_op_is_activate,
                        perf_wr_xact_when_critical,
                        perf_lpr_xact_when_critical,
                        perf_hpr_xact_when_critical,
                        perf_act_bypass,
                        perf_read_bypass,
                        perf_hif_hi_pri_rd,
                        perf_hif_rmw,
                        perf_hif_rd,
                        perf_hif_wr,
                        perf_hif_rd_or_wr,
                        ddrc_reg_num_alloc_bsm,
                        dbg_dfi_ie_cmd_type,
                        dbg_dfi_in_retry,
                        stat_ddrc_reg_retry_current_state,
                        stat_ddrc_reg_selfref_type,
                        csysack_ddrc,
                        hif_cmd_q_not_empty,
                        ddrc_reg_zq_reset_busy,
                        ddrc_reg_pda_done_w[0],
                        ddrc_reg_mr_wr_busy,
                        hif_hpr_credit,
                        hif_wr_credit,
                        hif_lpr_credit,
                        hif_wdata_ptr_addr_err,
                        hif_wdata_ptr,
                        hif_wdata_ptr_valid,
                        hif_wcmd_stall,
                        hif_rcmd_stall,
                        hif_cmd_stall,
                        ddrc_reg_addrmap_lut_rdata1_w[0],
                        ddrc_reg_addrmap_lut_rdata0_w[0],
                        ddrc_reg_addrmap_rank_valid_w[0],
                        ddrc_reg_dfi0_ctrlmsg_req_busy_w[0],
                        ddrc_reg_dfi0_ctrlmsg_resp_tout_w[0],
                        dfi_ctrlmsg_req_w[0],
                        dfi_ctrlmsg_w[0],
                        dfi_ctrlmsg_data_w[0],
                        ddrc_reg_refresh_rate_rank0,
                        ddrc_reg_refresh_rate_rank1,
                        ddrc_reg_refresh_rate_rank2,
                        ddrc_reg_refresh_rate_rank3,
                        ddrc_reg_derate_temp_limit_intr_sts_rank0,
                        ddrc_reg_derate_temp_limit_intr_sts_rank1,
                        ddrc_reg_derate_temp_limit_intr_sts_rank2,
                        ddrc_reg_derate_temp_limit_intr_sts_rank3,
                        sw_wr_data_valid_w[0],
                        sw_wr_data_w[0],
                        sw_wr_data_mask_w[0],
                        ci_manual_wr_mode_w[0],
                        ci_manual_rd_mode_w[0],
                        sw_wr_ecc_w[0],
                        sw_wr_ecc_mask_w[0],
                        ci_wr_crc_enable_mask_n_w[0],
                        ddrc_reg_rd_data_dq0_w[0],
                        ddrc_reg_rd_data_dq1_w[0],
                        ddrc_reg_dbg_mr4_byte0_w[0],
                        ddrc_reg_dbg_mr4_byte1_w[0],
                        ddrc_reg_dbg_mr4_byte2_w[0],
                        ddrc_reg_dbg_mr4_byte3_w[0],
                        ddrc_reg_dbg_raa_cnt_w[0],
                        ddrc_reg_rank_raa_cnt_gt0_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_code_0_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_0_w[0],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_0_w[0],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_0_w[0],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_0_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_code_1_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_1_w[0],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_1_w[0],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_1_w[0],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_1_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_code_2_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_2_w[0],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_2_w[0],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_2_w[0],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_2_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_code_3_w[0],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_3_w[0],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_3_w[0],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_3_w[0],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_3_w[0],
                        ddrc_reg_dbg_hw_lp_state_hsm_w[0],
                        ddrc_reg_dbg_dfi_lp_ctrl_ack_w[0],
                        ddrc_reg_dbg_dfi_lp_data_ack_w[0],
                        ddrc_reg_dbg_dfi_lp_state_dsm_w[0],
                        ddrc_reg_wr_crc_retry_limit_intr_w[0], 
                        ddrc_reg_rd_retry_limit_intr_w[0],
                        ddrc_reg_rd_crc_retry_limit_reached_w[0],
                        ddrc_reg_rd_ue_retry_limit_reached_w[0],
                        dbg_wr_crc_retry_pulse_w[0],
                        dbg_rd_crc_retry_pulse_w[0],
                        dbg_rd_ue_retry_pulse_w[0],
                        pi_rd_crc_retry_limit_reach_pre_w[0],
                        ddrc_reg_dbg_capar_retry_mc_code_w[0],
                        ddrc_reg_dbg_capar_retry_mc_addr_w[0],
                        ddrc_reg_dbg_capar_retry_state_csm_w[0],
                        ddrc_reg_dbg_capar_retry_state_mceu_w[0],
                        ddrc_reg_dbg_capar_retry_state_sceu_w[0],
                        ddrc_reg_cmdfifo_rd_data_w[0],
                        ddrc_reg_cmdfifo_overflow_w[0],
                        ddrc_reg_cmdfifo_recorded_cmd_num_w[0],
                        ddrc_reg_cmdfifo_window_cmd_num_w[0],
                        ext_rank_refresh_busy_w[0],
                        pi_rt_rd_crc_retry_limit_reach_pre_w[0],
                        dbg_rd_retry_rank_w[0],
                        pi_rd_ue_retry_limit_reach_pre_w[0],
                        pi_rt_rd_ue_retry_limit_reach_pre_w[0],
                        ddrc_reg_ppt2_burst_busy_w[0],
                        ddrc_reg_ppt2_state_w[0],
                        ddrc_reg_dfi_error_intr_w[0],
                        ddrc_reg_dfi_error_info_w[0],
                        ddrc_reg_dfi_sideband_timer_err_intr_w[0],
                        ddrc_reg_dfi_tctrlupd_min_error_w[0],
                        ddrc_reg_dfi_tctrlupd_max_error_w[0],
                        ddrc_reg_dfi_tinit_start_error_w[0],
                        ddrc_reg_dfi_tinit_complete_error_w[0],
                        ddrc_reg_dfi_tlp_ctrl_resp_error_w[0],
                        ddrc_reg_dfi_tlp_data_resp_error_w[0],
                        ddrc_reg_dfi_tlp_ctrl_wakeup_error_w[0],
                        ddrc_reg_dfi_tlp_data_wakeup_error_w[0],
                        hwffcmrw_op_s_w[0],
                        te_mr_addr_info
                        };
// spyglass enable_block W164b

// spyglass disable_block W164b
// SMD: LHS: 'cmp_in1' width 2903 is greater than RHS:
// SJ: Waived for Backward compatibility
      assign cmp_in1 = {
                        clk_te_en_w[NUM_INST-1],
                        t_hif_addr_w[NUM_INST-1],
                        dfi_hif_cmd_keyid_w[NUM_INST-1],
                        pi_rd_eccap_w[NUM_INST-1],
                        ddrc_reg_ppr_done_w[NUM_INST-1],
                        dbg_capar_retry_pulse_w[NUM_INST-1],
                        ih_wu_wr_eapar_w[NUM_INST-1],
                        bsm_clk_en_w[NUM_INST-1],
                        gs_mr_pw_num_beats_m1_w[NUM_INST-1],
                        gs_mr_ram_raddr_lsb_first_w[NUM_INST-1],
                        gs_wr_bc_sel_w[NUM_INST-1],
                        ih_wu_is_retry_wr_w[NUM_INST-1],
                        ih_wu_wr_pw_num_beats_m1_w[NUM_INST-1],
                        retryctrl_head_exp_w[NUM_INST-1],
                        capar_retry_start_w[NUM_INST-1],
                        capar_rd_expired_w[NUM_INST-1],
                        capar_rddata_en_w[NUM_INST-1],
                        ddrc_reg_max_num_alloc_bsm_w[NUM_INST-1],
                        ddrc_reg_max_num_unalloc_entries_w[NUM_INST-1],
                        ddrc_reg_cmd_rslt_w   [NUM_INST-1],
                        ddrc_reg_swcmd_lock_w [NUM_INST-1],
                        ddrc_reg_ducmd_lock_w [NUM_INST-1],
                        ddrc_reg_lccmd_lock_w [NUM_INST-1],
                        ddrc_reg_prank3_mode_w[NUM_INST-1],
                        ddrc_reg_prank2_mode_w[NUM_INST-1],
                        ddrc_reg_prank1_mode_w[NUM_INST-1],
                        ddrc_reg_prank0_mode_w[NUM_INST-1],
                        ddrc_reg_dbg_stat3_w[NUM_INST-1],
                        ddrc_reg_dbg_stat2_w[NUM_INST-1],
                        ddrc_reg_dbg_stat1_w[NUM_INST-1],
                        ddrc_reg_dbg_stat0_w[NUM_INST-1],
                        dch_sync_mode_o_w[NUM_INST-1],
                        rank_idle_state_o_w[NUM_INST-1],
                        rank_selfref_state_o_w[NUM_INST-1],
                        selfref_idle_entry_o_w[NUM_INST-1],
                        selfref_sw_entry_o_w[NUM_INST-1],
                        selfref_hw_entry_o_w[NUM_INST-1],
                        selfref_sw_o_w[NUM_INST-1],
                        selfref_idle_exit_o_w[NUM_INST-1],
                        selfref_sw_exit_o_w[NUM_INST-1],
                        channel_message_o_w[NUM_INST-1],
                        rank_selfref_operating_mode_o_w[NUM_INST-1],
                        rank_selfref_swhw_state_o_w[NUM_INST-1],
                        rank_selfref_tctrl_delay_ack_o_w[NUM_INST-1],
                        dfi_lp_selfref_tlp_resp_ack_o_w[NUM_INST-1],
                        hw_lp_exit_idle_o_w[NUM_INST-1],
                        hw_lp_selfref_hw_o_w[NUM_INST-1],

                        ddrc_reg_dfi_lp_state_w[NUM_INST-1],
                        ddrc_reg_mpsm_state_w[NUM_INST-1],
                        ddrc_reg_powerdown_state_w[NUM_INST-1],
                        ddrc_reg_du_cfgbuf_rdata_w[NUM_INST-1],
                        ddrc_reg_du_cmdbuf_rdata_w[NUM_INST-1],
                        ddrc_reg_lp_cmdbuf_rdata_w[NUM_INST-1],
                        ddrc_reg_capar_cmdbuf_rdata_w[NUM_INST-1],
                        ddrc_reg_powerdown_ongoing_w[NUM_INST-1],
                        ddrc_reg_selfref_ongoing_w[NUM_INST-1],
                        dbg_prank_act_pd_w[NUM_INST-1],
                        dbg_prank_pre_pd_w[NUM_INST-1],
                        dbg_du_ucode_seq_ongoing_w[NUM_INST-1],
                        dbg_lp_ucode_seq_ongoing_w[NUM_INST-1],
                        ddrc_reg_du_cur_blk_set_w[NUM_INST-1],
                        ddrc_reg_du_cur_blk_index_w[NUM_INST-1],
                        ddrc_reg_du_cur_blk_addr_w[NUM_INST-1],
                        ddrc_reg_du_cur_blk_ucode_w[NUM_INST-1],
                        ddrc_reg_du_main_fsm_state_w[NUM_INST-1],
                        ddrc_reg_glb_blk_events_ongoing_w[NUM_INST-1],
                        ddrc_reg_rank_blk_events_ongoing_w[NUM_INST-1],
                        ddrc_reg_du_mceu_fsm_state_w[NUM_INST-1],
                        ddrc_reg_du_sceu_fsm_state_w[NUM_INST-1],
                        ddrc_reg_caparcmd_err_intr_w[NUM_INST-1],
                        ddrc_reg_caparcmd_err_sts_w[NUM_INST-1],
                        ddrc_reg_lccmd_err_intr_w[NUM_INST-1],
                        ddrc_reg_ducmd_err_intr_w[NUM_INST-1],
                        ddrc_reg_swcmd_err_intr_w[NUM_INST-1],
                        ddrc_reg_swcmd_err_sts_w[NUM_INST-1],
                        ddrc_reg_ducmd_err_sts_w[NUM_INST-1],
                        ddrc_reg_lccmd_err_sts_w[NUM_INST-1],
                        ddrc_reg_rfm_alert_intr_w[NUM_INST-1],
                        ddrc_reg_rfm_cmd_log_w[NUM_INST-1],
                        ddrc_reg_2n_mode_w[NUM_INST-1],
                        ddrc_reg_ecs_mr16_w[NUM_INST-1],
                        ddrc_reg_ecs_mr17_w[NUM_INST-1],
                        ddrc_reg_ecs_mr18_w[NUM_INST-1],
                        ddrc_reg_ecs_mr19_w[NUM_INST-1],
                        ddrc_reg_ecs_mr20_w[NUM_INST-1],
                        perf_write_combine_noecc_w[NUM_INST-1],
                        perf_write_combine_wrecc_w[NUM_INST-1],
                        ddrc_reg_cmd_mrr_data_w[NUM_INST-1],
                        ddrc_reg_cmd_done_w[NUM_INST-1],
                        ddrc_reg_cmd_err_w[NUM_INST-1],
                        ddrc_reg_ctrlupd_err_intr_w[NUM_INST-1],
                        ddrc_reg_mrr_data_vld_w[NUM_INST-1],
                        ddrc_reg_rd_data_vld_w[NUM_INST-1],
                        pi_dfi_rddata_en_w[NUM_INST-1],
                        pi_dfi_wrdata_en_w[NUM_INST-1],
                        pi_rd_mrr_snoop_w[NUM_INST-1],
                        pi_phy_snoop_en_w[NUM_INST-1],
                        pi_rd_ph_nxt_w[NUM_INST-1],
                        pi_rd_vld_nxt_w[NUM_INST-1],
                        pi_wr_cs_nxt_w[NUM_INST-1],
                        pi_wr_ph_nxt_w[NUM_INST-1],
                        pi_wr_vld_nxt_w[NUM_INST-1],
                        pi_rd_ie_blk_burst_num_w[NUM_INST-1],
                        pi_rd_ie_rd_type_w[NUM_INST-1],
                        pi_rd_ie_bt_w[NUM_INST-1],
                        pi_rd_rankbank_w[NUM_INST-1],
                        pi_rd_critical_word_w[NUM_INST-1],
                        pi_rd_blk_w[NUM_INST-1],
                        pi_rd_page_w[NUM_INST-1],
                        pi_rd_wr_ram_addr_w[NUM_INST-1],
                        pi_rd_rmw_type_w[NUM_INST-1],
                        pi_rd_addr_err_w[NUM_INST-1],
                        pi_rd_tag_w[NUM_INST-1],
                        {HIF_KEYID_WIDTH{1'b0}},
                        pi_rd_mrr_ext_w[NUM_INST-1],
                        pi_rd_partial_w[NUM_INST-1],
                        pi_rd_vld_w[NUM_INST-1],

                        dqsosc_per_rank_stat_w[NUM_INST-1],
                        dqsosc_state_w[NUM_INST-1],
                        dfi_snoop_running_w[NUM_INST-1],
                        pi_rt_rd_mrr_snoop_w[NUM_INST-1],
                        pi_ph_snoop_en_w[NUM_INST-1],

                        dfi_wck_cs_w[NUM_INST-1],
                        dfi_wck_en_w[NUM_INST-1],
                        dfi_wck_toggle_w[NUM_INST-1],
                        ih_mr_ie_wr_cnt_dec_vct_w[NUM_INST-1],
                        core_derate_temp_limit_intr_w[NUM_INST-1],
                        perf_op_is_spec_ref_w[NUM_INST-1],
                        perf_op_is_crit_ref_w[NUM_INST-1],
                        retry_dfi_wrdata_en_w[NUM_INST-1],
                        pi_ph_dfi_wrdata_en_w[NUM_INST-1],
                        perf_ie_blk_hazard_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wrecc_q_depth_w[NUM_INST-1],
                        ddrc_reg_dbg_wrecc_q_depth_w[NUM_INST-1],
                        hif_wrecc_credit_w[NUM_INST-1],
                        ih_ie_busy_w[NUM_INST-1],
                        te_wu_ie_flowctrl_req_w[NUM_INST-1],
                        gs_pi_op_is_exit_selfref_w[NUM_INST-1],
                        ddrc_phy_cal_dl_enable_w[NUM_INST-1],
                        reg_ddrc_fgr_mode_gated_w[NUM_INST-1],
                        pi_gs_dll_off_mode_w[NUM_INST-1],
                        reg_ddrc_ext_rank_refresh_w[NUM_INST-1],
                        ih_busy_w[NUM_INST-1],
                        pi_gs_mpr_mode_w[NUM_INST-1],
                        mrr_op_on_w[NUM_INST-1],
                        gs_pi_data_pipeline_empty_w[NUM_INST-1],
                        reg_ddrc_active_ranks_int_w[NUM_INST-1],
                        retry_dfi_rddata_en_w[NUM_INST-1],
                        retry_phy_wdata_vld_early_w[NUM_INST-1],
                        retry_phy_wdata_w[NUM_INST-1],
                        retry_phy_dm_w[NUM_INST-1],
                        retry_dfi_sel_w[NUM_INST-1],
                        retry_rt_rd_timeout_value_w[NUM_INST-1],
                        retry_rt_now_sw_intervention_w[NUM_INST-1],
                        retry_rt_fatl_err_pulse_w[NUM_INST-1],
                        retry_rt_fifo_init_n_w[NUM_INST-1],
                        retry_rt_rdatavld_gate_en_w[NUM_INST-1],
                        retry_fifo_empty_w[NUM_INST-1],
                        gs_pi_cs_n_w[NUM_INST-1],
                        pda_mode_pre_w[NUM_INST-1],
                        pda_mode_w[NUM_INST-1],
                        gs_mr_pda_data_sel_w[NUM_INST-1],
                        gs_mr_load_mode_pda_w[NUM_INST-1],
                        gs_mr_write_w[NUM_INST-1],
                        te_wu_wr_retry_w[NUM_INST-1],
                        te_wu_entry_num_w[NUM_INST-1],
                        te_mr_wr_ram_addr_w[NUM_INST-1],
                        gs_pi_rdwr_pw_num_beats_m1_w[NUM_INST-1],
                        gs_pi_rdwr_ram_raddr_lsb_first_w[NUM_INST-1],
                        gs_pi_rdwr_bc_sel_w[NUM_INST-1],
                        te_pi_wr_word_valid_w[NUM_INST-1],
                        ts_pi_mwr_w[NUM_INST-1],
                        ts_pi_wr32_w[NUM_INST-1],
                        ts_pi_2nd_half_w[NUM_INST-1],
                        ts_cam_clear_en_w[NUM_INST-1],
                        te_yy_wr_combine_w[NUM_INST-1],
                        te_wu_wrdata_stall_req_w [NUM_INST-1],
                        pi_rt_critical_word_w[NUM_INST-1],
                        pi_rt_block_num_w[NUM_INST-1],
                        pi_rt_page_num_w[NUM_INST-1],
                        pi_rt_rankbank_num_w[NUM_INST-1],
                        pi_rt_rmwtype_w[NUM_INST-1],
                        pi_rt_rmwcmd_w[NUM_INST-1],
                        pi_rt_wr_ram_addr_w[NUM_INST-1],
                        pi_rt_rd_addr_err_w[NUM_INST-1],
                        pi_rt_rd_tag_w[NUM_INST-1],
                        pi_rt_rd_vld_w[NUM_INST-1],
                        pi_rt_rd_partial_w[NUM_INST-1],
                        pi_gs_geardown_mode_on_w[NUM_INST-1],
                        ih_wu_critical_word_w[NUM_INST-1],
                        ih_wu_wr_entry_w[NUM_INST-1],
                        ih_wu_rmw_type_w[NUM_INST-1],
                        ih_te_wr_valid_w[NUM_INST-1],
                        ih_te_rd_valid_w[NUM_INST-1],
                        ih_wu_wr_valid_addr_err_w[NUM_INST-1],
                        ih_wu_wr_valid_w[NUM_INST-1],
                        pi_ph_dfi_rddata_en_w[NUM_INST-1],
                        pi_rt_rd_mrr_ext_w[NUM_INST-1],
                        pi_rt_rd_mrr_w[NUM_INST-1],
                        ih_wu_cerr_w[NUM_INST-1],
                        pi_rt_eccap_w[NUM_INST-1],
                        te_mr_eccap_w[NUM_INST-1],
                        ih_rd_lkp_bwt_vld_w[NUM_INST-1],
                        ih_rd_lkp_bwt_w[NUM_INST-1],
                        ih_rd_lkp_brt_vld_w[NUM_INST-1],
                        ih_rd_lkp_brt_w[NUM_INST-1],
                        ih_mr_lkp_brt_vld_w[NUM_INST-1],
                        ih_mr_lkp_brt_w[NUM_INST-1],
                        ih_mr_lkp_bwt_vld_w[NUM_INST-1],
                        ih_mr_lkp_bwt_w[NUM_INST-1],
                        pi_rt_ie_blk_burst_num_w[NUM_INST-1],
                        pi_rt_ie_rd_type_w[NUM_INST-1],
                        pi_rt_ie_bt_w[NUM_INST-1],
                        te_mr_ie_blk_burst_num_w[NUM_INST-1],
                        te_mr_ie_wr_type_w[NUM_INST-1],
                        te_mr_ie_bt_w[NUM_INST-1],
                        ih_mr_ie_brt_vld_w[NUM_INST-1],
                        ih_mr_ie_brt_w[NUM_INST-1],
                        ih_mr_ie_bwt_w[NUM_INST-1],
                        ih_mr_ie_wr_cnt_inc_w[NUM_INST-1],
                        ih_rd_ie_blk_rd_end_w[NUM_INST-1],
                        ih_rd_ie_rd_cnt_inc_w[NUM_INST-1],
                        ih_rd_ie_brt_w[NUM_INST-1],
                        ih_mr_ie_pw_w[NUM_INST-1],
                        ih_mr_ie_blk_wr_end_w[NUM_INST-1],
                        hwffc_i_reg_ddrc_dis_auto_zq_w[NUM_INST-1],
                        hwffc_hif_wd_stall_w[NUM_INST-1],
                        ddrc_xpi_clock_required_w[NUM_INST-1],
                        ddrc_xpi_port_disable_req_w[NUM_INST-1],
                        ddrc_reg_hwffc_operating_mode_w[NUM_INST-1],
                        ddrc_reg_current_vrcg_w[NUM_INST-1],
                        ddrc_reg_current_fsp_w[NUM_INST-1],
                        ddrc_reg_current_frequency_w[NUM_INST-1],
                        ddrc_reg_hwffc_in_progress_w[NUM_INST-1],
                        hwffc_target_freq_init_w[NUM_INST-1],
                        hwffc_target_freq_w[NUM_INST-1],
                        hwffc_target_freq_en_w[NUM_INST-1],
                        dfi_lp_ctrl_wakeup_w[NUM_INST-1],
                        dfi_lp_ctrl_req_w[NUM_INST-1],
                        dfi_lp_data_wakeup_w[NUM_INST-1],
                        dfi_lp_data_req_w[NUM_INST-1],
                        dfi_phymstr_ack_w[NUM_INST-1],
                        dfi_phyupd_ack_w[NUM_INST-1],
                        hif_refresh_active_w[NUM_INST-1],
                        hif_refresh_req_derate_w[NUM_INST-1],
                        hif_refresh_req_cnt_w[NUM_INST-1],
                        hif_refresh_req_w[NUM_INST-1],
                        hif_refresh_req_bank_w[NUM_INST-1],
                        ddrc_reg_zq_calib_short_busy_w[NUM_INST-1],
                        ddrc_reg_rd_data_pipeline_empty_w[NUM_INST-1],
                        ddrc_reg_wr_data_pipeline_empty_w[NUM_INST-1],
                        ddrc_reg_rd_q_empty_w[NUM_INST-1],
                        ddrc_reg_wr_q_empty_w[NUM_INST-1],
                        ddrc_reg_selfref_type_w[NUM_INST-1],
                        ddrc_reg_operating_mode_w[NUM_INST-1],
                        ddrc_reg_selfref_state_w[NUM_INST-1],
                        ddrc_reg_selfref_cam_not_empty_w[NUM_INST-1],
                        ddrc_reg_dbg_stall_wr_w[NUM_INST-1],
                        ddrc_reg_dbg_stall_rd_w[NUM_INST-1],
                        ddrc_reg_dbg_stall_w[NUM_INST-1],
                        ddrc_reg_dbg_w_q_depth_w[NUM_INST-1],
                        ddrc_reg_dbg_lpr_q_depth_w[NUM_INST-1],
                        ddrc_reg_dbg_hpr_q_depth_w[NUM_INST-1],
                        dbg_dfi_parity_poison_w[NUM_INST-1],
                        ddrc_reg_capar_poison_complete_w[NUM_INST-1],
                        ddrc_reg_ctrlupd_busy_w[NUM_INST-1],
                        ddrc_reg_ctrlupd_burst_busy_w[NUM_INST-1],
                        ddrc_reg_rank_refresh_busy_w[NUM_INST-1],
                        retryram_mask_w[NUM_INST-1],
                        retryram_we_w[NUM_INST-1],
                        retryram_re_w[NUM_INST-1],
                        retryram_raddr_w[NUM_INST-1],
                        retryram_waddr_w[NUM_INST-1],
                        retryram_din_w[NUM_INST-1],
                        ddrc_reg_retry_stat_w[NUM_INST-1],
                        ddrc_reg_retry_fifo_fill_level_w[NUM_INST-1],
                        ddrc_reg_wr_crc_err_max_reached_intr_w[NUM_INST-1],
                        ddrc_reg_wr_crc_err_intr_w[NUM_INST-1],
                        ddrc_reg_wr_crc_err_cnt_w[NUM_INST-1],
                        ddrc_reg_capar_retry_limit_intr_w[NUM_INST-1],
                        ddrc_reg_capar_fatl_err_intr_w[NUM_INST-1],
                        ddrc_reg_capar_fatl_err_code_w[NUM_INST-1],
                        ddrc_reg_capar_err_max_reached_intr_w[NUM_INST-1],
                        ddrc_reg_capar_err_cnt_w[NUM_INST-1],
                        ddrc_reg_capar_err_intr_w[NUM_INST-1],
                        init_mr_done_out_w[NUM_INST-1],
                        dfi_reset_n_ref_w[NUM_INST-1],
                        dfi_2n_mode_w[NUM_INST-1],
                        dfi_freq_fsp_w[NUM_INST-1],
                        dfi_frequency_w[NUM_INST-1],
                        dfi_init_start_w[NUM_INST-1],
                        dfi_parity_in_w[NUM_INST-1],
                        dfi_dram_clk_disable_w[NUM_INST-1],
                        dfi_ctrlupd_req_w[NUM_INST-1],
                        dfi_ctrlupd_type_w[NUM_INST-1],
                        dfi_ctrlupd_target_w[NUM_INST-1],
                        dfi_rddata_cs_w[NUM_INST-1],
                        dfi_wrdata_cs_w[NUM_INST-1],
                        dfi_reset_n_w[NUM_INST-1],
                        dfi_odt_w[NUM_INST-1],
                        dfi_cs_w[NUM_INST-1],
                        dfi_cke_w[NUM_INST-1],
                        dfi_we_n_w[NUM_INST-1],
                        dfi_ras_n_w[NUM_INST-1],
                        dfi_cas_n_w[NUM_INST-1],
                        dfi_bank_w[NUM_INST-1],
                        dfi_freq_ratio_w[NUM_INST-1],
                        dfi_address_w[NUM_INST-1],
                        dfi_cid_w[NUM_INST-1],
                        dfi_act_n_w[NUM_INST-1],
                        dfi_bg_w[NUM_INST-1],
                        dfi_hif_cmd_addr_w[NUM_INST-1],
                        dfi_hif_cmd_wdata_ptr_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_63_56_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_63_56_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_55_48_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_55_48_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_47_40_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_47_40_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_39_32_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_39_32_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_31_24_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_31_24_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_23_16_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_23_16_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_15_8_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_15_8_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_cam_7_0_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_cam_7_0_valid_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_page_hit_rank_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_valid_rank_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_pri_rank_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_page_hit_rank_w[NUM_INST-1],
                        ddrc_core_reg_dbg_rd_valid_rank_w[NUM_INST-1],
                        ddrc_core_reg_dbg_hif_wcmd_stall_w[NUM_INST-1],
                        ddrc_core_reg_dbg_hif_rcmd_stall_w[NUM_INST-1],
                        ddrc_core_reg_dbg_hif_cmd_stall_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_q_depth_w[NUM_INST-1],
                        ddrc_core_reg_dbg_hpr_q_depth_w[NUM_INST-1],
                        ddrc_core_reg_dbg_lpr_q_depth_w[NUM_INST-1],
                        ddrc_core_reg_dbg_wr_q_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_hpr_q_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_lpr_q_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_ctrlupd_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_init_next_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_init_curr_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_global_fsm_state_w[NUM_INST-1],
                        ddrc_core_reg_dbg_operating_mode_w[NUM_INST-1],
                        perf_num_alloc_bsm_w[NUM_INST-1],
                        perf_visible_window_limit_reached_rd_w[NUM_INST-1],
                        perf_visible_window_limit_reached_wr_w[NUM_INST-1],
                        perf_bsm_starvation_w[NUM_INST-1],
                        perf_bsm_alloc_w[NUM_INST-1],
                        perf_bypass_cid_w[NUM_INST-1],
                        perf_bypass_bg_w[NUM_INST-1],
                        perf_bypass_bank_w[NUM_INST-1],
                        perf_bypass_rank_w[NUM_INST-1],
                        perf_cid_w[NUM_INST-1],
                        perf_bg_w[NUM_INST-1],
                        perf_bank_w[NUM_INST-1],
                        perf_rank_w[NUM_INST-1],
                        perf_op_is_zqcs_w[NUM_INST-1],
                        perf_op_is_zqcl_w[NUM_INST-1],
                        perf_op_is_load_mode_w[NUM_INST-1],
                        perf_op_is_refresh_w[NUM_INST-1],
                        perf_selfref_mode_w[NUM_INST-1],
                        perf_op_is_enter_mpsm_w[NUM_INST-1],
                        perf_op_is_enter_powerdown_w[NUM_INST-1],
                        perf_op_is_enter_selfref_w[NUM_INST-1],
                        perf_waw_hazard_w[NUM_INST-1],
                        perf_raw_hazard_w[NUM_INST-1],
                        perf_war_hazard_w[NUM_INST-1],
                        perf_write_combine_w[NUM_INST-1],
                        perf_rdwr_transitions_w[NUM_INST-1],
                        perf_precharge_for_other_w[NUM_INST-1],
                        perf_precharge_for_rdwr_w[NUM_INST-1],
                        perf_op_is_precharge_w[NUM_INST-1],
                        perf_op_is_mwr_w[NUM_INST-1],
                        perf_op_is_wr16_w[NUM_INST-1],
                        perf_op_is_wr32_w[NUM_INST-1],
                        perf_op_is_rd16_w[NUM_INST-1],
                        perf_op_is_rd32_w[NUM_INST-1],
                        perf_op_is_cas_w[NUM_INST-1],
                        perf_op_is_cas_ws_w[NUM_INST-1],
                        perf_op_is_cas_ws_off_w[NUM_INST-1],
                        perf_op_is_cas_wck_sus_w[NUM_INST-1],
                        perf_op_is_enter_dsm_w[NUM_INST-1],
                        perf_op_is_rfm_w[NUM_INST-1],
                        perf_op_is_wr_w[NUM_INST-1],
                        perf_op_is_rd_w[NUM_INST-1],
                        perf_op_is_rd_activate_w[NUM_INST-1],
                        perf_op_is_rd_or_wr_w[NUM_INST-1],
                        perf_op_is_activate_w[NUM_INST-1],
                        perf_wr_xact_when_critical_w[NUM_INST-1],
                        perf_lpr_xact_when_critical_w[NUM_INST-1],
                        perf_hpr_xact_when_critical_w[NUM_INST-1],
                        perf_act_bypass_w[NUM_INST-1],
                        perf_read_bypass_w[NUM_INST-1],
                        perf_hif_hi_pri_rd_w[NUM_INST-1],
                        perf_hif_rmw_w[NUM_INST-1],
                        perf_hif_rd_w[NUM_INST-1],
                        perf_hif_wr_w[NUM_INST-1],
                        perf_hif_rd_or_wr_w[NUM_INST-1],
                        ddrc_reg_num_alloc_bsm_w[NUM_INST-1],
                        dbg_dfi_ie_cmd_type_w[NUM_INST-1],
                        dbg_dfi_in_retry_w[NUM_INST-1],
                        stat_ddrc_reg_retry_current_state_w[NUM_INST-1],
                        stat_ddrc_reg_selfref_type_w[NUM_INST-1],
                        csysack_ddrc_w[NUM_INST-1],
                        hif_cmd_q_not_empty_w[NUM_INST-1],
                        ddrc_reg_zq_reset_busy_w[NUM_INST-1],
                        ddrc_reg_pda_done_w[NUM_INST-1],
                        ddrc_reg_mr_wr_busy_w[NUM_INST-1],
                        hif_hpr_credit_w[NUM_INST-1],
                        hif_wr_credit_w[NUM_INST-1],
                        hif_lpr_credit_w[NUM_INST-1],
                        hif_wdata_ptr_addr_err_w[NUM_INST-1],
                        hif_wdata_ptr_w[NUM_INST-1],
                        hif_wdata_ptr_valid_w[NUM_INST-1],
                        hif_wcmd_stall_w[NUM_INST-1],
                        hif_rcmd_stall_w[NUM_INST-1],
                        hif_cmd_stall_w[NUM_INST-1],
                        ddrc_reg_addrmap_lut_rdata1_w[NUM_INST-1],
                        ddrc_reg_addrmap_lut_rdata0_w[NUM_INST-1],
                        ddrc_reg_addrmap_rank_valid_w[NUM_INST-1],
                        ddrc_reg_dfi0_ctrlmsg_req_busy_w[NUM_INST-1],
                        ddrc_reg_dfi0_ctrlmsg_resp_tout_w[NUM_INST-1],
                        dfi_ctrlmsg_req_w[NUM_INST-1],
                        dfi_ctrlmsg_w[NUM_INST-1],
                        dfi_ctrlmsg_data_w[NUM_INST-1],
                        ddrc_reg_refresh_rate_rank0_w[NUM_INST-1],
                        ddrc_reg_refresh_rate_rank1_w[NUM_INST-1],
                        ddrc_reg_refresh_rate_rank2_w[NUM_INST-1],
                        ddrc_reg_refresh_rate_rank3_w[NUM_INST-1],
                        ddrc_reg_derate_temp_limit_intr_sts_rank0_w[NUM_INST-1],
                        ddrc_reg_derate_temp_limit_intr_sts_rank1_w[NUM_INST-1],
                        ddrc_reg_derate_temp_limit_intr_sts_rank2_w[NUM_INST-1],
                        ddrc_reg_derate_temp_limit_intr_sts_rank3_w[NUM_INST-1],
                        sw_wr_data_valid_w[NUM_INST-1],
                        sw_wr_data_w[NUM_INST-1],
                        sw_wr_data_mask_w[NUM_INST-1],
                        ci_manual_wr_mode_w[NUM_INST-1],
                        ci_manual_rd_mode_w[NUM_INST-1],
                        sw_wr_ecc_w[NUM_INST-1],
                        sw_wr_ecc_mask_w[NUM_INST-1],
                        ci_wr_crc_enable_mask_n_w[NUM_INST-1],
                        ddrc_reg_rd_data_dq0_w[NUM_INST-1],
                        ddrc_reg_rd_data_dq1_w[NUM_INST-1],
                        ddrc_reg_dbg_mr4_byte0_w[NUM_INST-1],
                        ddrc_reg_dbg_mr4_byte1_w[NUM_INST-1],
                        ddrc_reg_dbg_mr4_byte2_w[NUM_INST-1],
                        ddrc_reg_dbg_mr4_byte3_w[NUM_INST-1],
                        ddrc_reg_dbg_raa_cnt_w[NUM_INST-1],
                        ddrc_reg_rank_raa_cnt_gt0_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_code_0_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_0_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_0_w[NUM_INST-1],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_0_w[NUM_INST-1],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_0_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_code_1_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_1_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_1_w[NUM_INST-1],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_1_w[NUM_INST-1],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_1_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_code_2_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_2_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_2_w[NUM_INST-1],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_2_w[NUM_INST-1],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_2_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_code_3_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_mc_addr_3_w[NUM_INST-1],
                        ddrc_reg_dbg_rank_ctrl_state_rsm_3_w[NUM_INST-1],
                        ddrc_reg_dbg_mceu_ctrl_state_mceu_3_w[NUM_INST-1],
                        ddrc_reg_dbg_sceu_ctrl_state_sceu_3_w[NUM_INST-1],
                        ddrc_reg_dbg_hw_lp_state_hsm_w[NUM_INST-1],
                        ddrc_reg_dbg_dfi_lp_ctrl_ack_w[NUM_INST-1],
                        ddrc_reg_dbg_dfi_lp_data_ack_w[NUM_INST-1],
                        ddrc_reg_dbg_dfi_lp_state_dsm_w[NUM_INST-1],
                        ddrc_reg_wr_crc_retry_limit_intr_w[NUM_INST-1], 
                        ddrc_reg_rd_retry_limit_intr_w[NUM_INST-1],
                        ddrc_reg_rd_crc_retry_limit_reached_w[NUM_INST-1],
                        ddrc_reg_rd_ue_retry_limit_reached_w[NUM_INST-1],
                        dbg_wr_crc_retry_pulse_w[NUM_INST-1],
                        dbg_rd_crc_retry_pulse_w[NUM_INST-1],
                        dbg_rd_ue_retry_pulse_w[NUM_INST-1],
                        pi_rd_crc_retry_limit_reach_pre_w[NUM_INST-1],
                        ddrc_reg_dbg_capar_retry_mc_code_w[NUM_INST-1],
                        ddrc_reg_dbg_capar_retry_mc_addr_w[NUM_INST-1],
                        ddrc_reg_dbg_capar_retry_state_csm_w[NUM_INST-1],
                        ddrc_reg_dbg_capar_retry_state_mceu_w[NUM_INST-1],
                        ddrc_reg_dbg_capar_retry_state_sceu_w[NUM_INST-1],
                        ddrc_reg_cmdfifo_rd_data_w[NUM_INST-1],
                        ddrc_reg_cmdfifo_overflow_w[NUM_INST-1],
                        ddrc_reg_cmdfifo_recorded_cmd_num_w[NUM_INST-1],
                        ddrc_reg_cmdfifo_window_cmd_num_w[NUM_INST-1],
                        ext_rank_refresh_busy_w[NUM_INST-1],
                        pi_rt_rd_crc_retry_limit_reach_pre_w[NUM_INST-1],
                        dbg_rd_retry_rank_w[NUM_INST-1],
                        pi_rd_ue_retry_limit_reach_pre_w[NUM_INST-1],
                        pi_rt_rd_ue_retry_limit_reach_pre_w[NUM_INST-1],
                        ddrc_reg_ppt2_burst_busy_w[NUM_INST-1],
                        ddrc_reg_ppt2_state_w[NUM_INST-1],
                        ddrc_reg_dfi_error_intr_w[NUM_INST-1],
                        ddrc_reg_dfi_error_info_w[NUM_INST-1],
                        ddrc_reg_dfi_sideband_timer_err_intr_w[NUM_INST-1],
                        ddrc_reg_dfi_tctrlupd_min_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tctrlupd_max_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tinit_start_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tinit_complete_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tlp_ctrl_resp_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tlp_data_resp_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tlp_ctrl_wakeup_error_w[NUM_INST-1],
                        ddrc_reg_dfi_tlp_data_wakeup_error_w[NUM_INST-1],
                        hwffcmrw_op_s_w[NUM_INST-1],
                        te_mr_addr_info_w[NUM_INST-1]
                        };
// spyglass enable_block W164b


    occap_cmp
    
      #(
         .CMP_REG       (CMP_REG),
         .NUM_INS       (NUM_OUTS),
         .IN_WIDTH      (OUT_TOTW),
         .PW            (PW),
         .WIDTH_OFFSET  (WIDTH_OFFSET),
         .WIDTH_ARRAY   (WIDTH_ARRAY),
         .SVA_X_Z_CHECK_EN (1) // enable check on X/Z
        )
      ddrc_ctrl_cmp
      (
         .clk                 (core_ddrc_core_clk),
         .rst_n               (core_ddrc_rstn),
         .in0                 (cmp_in0),
         .in1                 (cmp_in1),
         .cmp_en              (ddrc_cmp_en),
         .cmp_poison          (ddrc_ctrl_cmp_poison),
         .cmp_poison_full     (ddrc_ctrl_cmp_poison_full),
         .cmp_poison_err_inj  (ddrc_ctrl_cmp_poison_err_inj),
         .cmp_err             (ddrc_ctrl_cmp_error),
         .cmp_err_full        (ddrc_ctrl_cmp_error_full),
         .cmp_err_seq         (ddrc_ctrl_cmp_error_seq),
         .cmp_poison_complete (ddrc_ctrl_cmp_poison_complete)
      );

   end // CMP_en
   else begin: OCCAP_dis

      assign ddrc_ctrl_cmp_error           = 1'b0;
      assign ddrc_ctrl_cmp_error_full      = 1'b0;
      assign ddrc_ctrl_cmp_error_seq       = 1'b0;
      assign ddrc_ctrl_cmp_poison_complete = 1'b0;

   end // OCCAP_dis

endgenerate

endmodule
