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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/teengine.sv#7 $
// -------------------------------------------------------------------------
// Description:
//
// ---------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module teengine
import DWC_ddrctl_reg_pkg::*;
#(
   //-------------------------------- PARAMETERS ----------------------------------    
    parameter  CHANNEL_NUM             = 0
   ,parameter  RD_CAM_ADDR_BITS        = 0
   ,parameter  WR_CAM_ADDR_BITS        = 0
   ,parameter  WR_ECC_CAM_ADDR_BITS    = 0
   ,parameter  WR_CAM_ADDR_BITS_IE     = 0
   ,parameter  MAX_CAM_ADDR_BITS       = 0
   ,parameter  RANK_BITS               = `MEMC_RANK_BITS
   ,parameter  LRANK_BITS              = `UMCTL2_LRANK_BITS        // max supported of ranks in the system 
                                                                   // This depends on number of Logical rank not Physical rank.
                                                                   // This is the same for non 3DS configuration.
   ,parameter  BG_BITS                 = `MEMC_BG_BITS             // max supported bank groups per rank
   ,parameter  BANK_BITS               = `MEMC_BANK_BITS           // max supported banks per rank
   ,parameter  BG_BANK_BITS            = `MEMC_BG_BANK_BITS        // max supported banks groups per rank
   ,parameter  PAGE_BITS               = `MEMC_PAGE_BITS
   ,parameter  BLK_BITS                = `MEMC_BLK_BITS            // write CAM only
   ,parameter  BSM_BITS                = `UMCTL2_BSM_BITS          // max supported BSM
   ,parameter  ECC_INFO_WIDTH          = 35
   ,parameter  CMD_LEN_BITS            = 1
   ,parameter  OTHER_RD_ENTRY_BITS     = 30                        // override: # of other bits to track in read CAM
   ,parameter  OTHER_WR_ENTRY_BITS     = 2                         // override: # of other bits to track in write CAM
   ,parameter  OTHER_RD_RMW_LSB        = `MEMC_TAGBITS                         // LSB of RMW type for RD_OTHER field
   ,parameter  OTHER_RD_RMW_TYPE_BITS  = 2                         // no if bits of RMW type for RD_OTHER field
   ,parameter  PARTIAL_WR_BITS         = `UMCTL2_PARTIAL_WR_BITS   // bits for PARTIAL_WR logic
   ,parameter  PARTIAL_WR_BITS_LOG2    = `log2(PARTIAL_WR_BITS)     // bits for PARTIAL_WR logic
   ,parameter  PW_WORD_CNT_WD_MAX      = 2
   ,parameter  PW_BC_SEL_BITS          = 3
   ,parameter  AUTOPRE_BITS            = 1
   ,parameter  RANKBANK_BITS           = LRANK_BITS + BG_BANK_BITS
   ,parameter  TOTAL_LRANKS            = 1 << LRANK_BITS
   ,parameter  TOTAL_BANKS             = 1 << (LRANK_BITS + BG_BANK_BITS)
   ,parameter  RD_CAM_ENTRIES          = 0
   ,parameter  WR_CAM_ENTRIES          = 0
   ,parameter  WR_CAM_ENTRIES_IE       = 0
   ,parameter  WR_ECC_CAM_ENTRIES      = 0
   ,parameter  TOTAL_BSMS              = `UMCTL2_NUM_BSM
   ,parameter  RD_LATENCY_BITS         = `UMCTL2_XPI_RQOS_TW
   ,parameter  WR_LATENCY_BITS         = `UMCTL2_XPI_WQOS_TW
   ,parameter  MWR_BITS                = 1
   ,parameter  BT_BITS                 = `MEMC_BLK_TOKEN_BITS  // Override
   ,parameter  NO_OF_BT                = `MEMC_NO_OF_BLK_TOKEN // Override
   ,parameter  IE_RD_TYPE_BITS         = 2 // Override
   ,parameter  IE_WR_TYPE_BITS         = 2 // Override
   ,parameter  IE_BURST_NUM_BITS       = 3
   ,parameter  HI_PRI_BITS             = 2
   ,parameter  IE_MASKED_BITS          = 1
   ,parameter  ECCAP_BITS              = 1
   ,parameter  WORD_BITS               = `MEMC_WORD_BITS
   ,parameter  RETRY_TIMES_WIDTH       = 3
   ,parameter  BANK_ORG_WIDTH          = 2
   ,parameter  ENTRY_RETRY_TIMES_WIDTH = 4
   ,parameter   RETRY_WR_BITS          = 1
   ,parameter   RETRY_RD_BITS          = 1
   ,parameter  DDR4_COL3_BITS          = 1
   ,parameter  LP_COL4_BITS            = 1
   ,parameter  IE_TAG_BITS             = IE_RD_TYPE_BITS + IE_BURST_NUM_BITS + BT_BITS + ECCAP_BITS
   ,parameter  RMW_BITS                = 1
   ,parameter  CID_WIDTH               = `UMCTL2_CID_WIDTH
   ,parameter  AM_COL_WIDTH_H          = 5
   ,parameter  AM_COL_WIDTH_L          = 4
   ,parameter  WP_BITS                 = 1
   ,parameter  HIF_KEYID_WIDTH         = `DDRCTL_HIF_KEYID_WIDTH
   )
   (
   //---------------------------- INPUTS AND OUTPUTS ------------------------------
    input                                       core_ddrc_rstn
   ,input                                       dh_te_pageclose
   ,input   [7:0]                               dh_te_pageclose_timer
   ,input                                       co_te_clk
   ,input                                       ddrc_cg_en
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in te_assertions
   ,input                                       dh_te_dis_wc
//spyglass enable_block W240
   ,output  [TOTAL_BANKS-1:0]                   te_dh_rd_valid
   ,output  [TOTAL_BANKS-1:0]                   te_dh_rd_page_hit
   ,output  [TOTAL_BANKS-1:0]                   te_dh_wr_valid
   ,output  [TOTAL_BANKS-1:0]                   te_dh_wr_page_hit
//    ,input                                       dh_te_dis_autopre_collide_opt     // by default, auto-precharge will
//                                                                                   //  not be used when issuing a colliding
//                                                                                   //  read/write, to allow the subsequent
//                                                                                   //  write/read to take advantage of the
//                                                                                   //  open page.
//                                                                                   // set this bit to '1' to disable this
//                                                                                   //  performance optimization
   ,output  [TOTAL_BANKS-1:0]                   te_dh_rd_hi
   ,input   [RD_CAM_ADDR_BITS-1:0]              ih_te_rd_entry_num
   ,input                                       ih_te_rd_valid
   ,input   [WR_CAM_ADDR_BITS_IE-1:0]           ih_te_wr_entry_num
   ,input                                       ih_te_wr_valid
   ,input                                       ih_te_rd_autopre
   ,input                                       ih_te_wr_autopre
   ,input   [1:0]                               ih_te_rd_hi_pri
   ,input   [1:0]                               ih_te_wr_hi_pri
   ,input  [WR_LATENCY_BITS-1:0]                ih_te_wr_latency
   ,output                                      te_gs_any_vpw_timed_out
   ,output                                      te_gs_any_vpw_timed_out_w // No flopped version to be flopped in ts with some combo logic 
   ,input  [RD_LATENCY_BITS-1:0]                ih_te_rd_latency
   ,output                                      te_gs_any_vpr_timed_out
   ,output                                      te_gs_any_vpr_timed_out_w // No flopped version to be flopped in ts with some combo logic 
   ,input                                       reg_ddrc_autopre_rmw
   ,input                                       reg_ddrc_dis_opt_ntt_by_act
   ,input                                       reg_ddrc_dis_opt_ntt_by_pre
   ,input                                       reg_ddrc_dis_opt_wrecc_collision_flush
   ,input                                       ih_te_rd_rmw
   ,input  [LRANK_BITS-1:0]                      ih_te_rd_rank_num
   ,input  [LRANK_BITS-1:0]                      ih_te_wr_rank_num
   ,input  [BG_BANK_BITS-1:0]                   ih_te_rd_bg_bank_num
   ,input  [BG_BANK_BITS-1:0]                   ih_te_wr_bg_bank_num
   ,input  [PAGE_BITS-1:0]                      ih_te_rd_page_num
   ,input  [PAGE_BITS-1:0]                      ih_te_wr_page_num
   ,input  [BLK_BITS-1:0]                       ih_te_rd_block_num
   ,input  [BLK_BITS-1:0]                       ih_te_wr_block_num
   ,input  [CMD_LEN_BITS-1:0]                   ih_te_rd_length
   ,input  [WORD_BITS-1:0]                      ih_te_critical_dword

   ,input  [OTHER_RD_ENTRY_BITS-1:0]            ih_te_rd_other_fields             // everything else TE needs to track in the read CAM
   ,input  [OTHER_WR_ENTRY_BITS-1:0]            ih_te_wr_other_fields             // everything else TE needs to track in the read CAM
   ,output                                      te_ih_retry
   ,output                                      te_wu_wr_retry
   ,output                                      te_ih_free_rd_entry_valid
   ,output [RD_CAM_ADDR_BITS-1:0]               te_ih_free_rd_entry
   ,input  [1:0]                                wu_te_enable_wr
   ,input  [WR_CAM_ADDR_BITS-1:0]               wu_te_entry_num
   ,input  [PARTIAL_WR_BITS-1:0]                wu_te_wr_word_valid
   ,input  [PARTIAL_WR_BITS_LOG2-1:0]           wu_te_ram_raddr_lsb_first
   ,input  [PW_WORD_CNT_WD_MAX-1:0]             wu_te_pw_num_beats_m1
   ,input  [PW_WORD_CNT_WD_MAX-1:0]             wu_te_pw_num_cols_m1
   ,output [TOTAL_BSMS*IE_TAG_BITS-1:0]         te_os_wr_ie_tag_table             // Entire ie_tag contents of the NTT
   ,output [TOTAL_BSMS*IE_TAG_BITS-1:0]         te_os_rd_ie_tag_table             // Entire ie_tag contents of the NTT
   ,input  [IE_TAG_BITS-1:0]                    os_te_rdwr_ie_tag
   ,output [WR_CAM_ADDR_BITS_IE-1:0]            te_mr_wr_ram_addr
   ,output                                      te_yy_wr_combine                  // write from IH being combined with existing entry
   ,output                                      te_yy_wr_combine_noecc
   ,output                                      te_yy_wr_combine_wrecc
   ,output [WR_CAM_ADDR_BITS-1:0]               te_wu_entry_num
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in uPCTL2
   ,input                                       be_te_page_hit
   ,input                                       be_te_wr_page_hit
//spyglass enable_block W240
   ,input                                       be_wr_page_hit
   ,output [BSM_BITS-1:0]                       te_be_bsm_num
   ,output [PAGE_BITS-1:0]                      te_be_page_num
   ,input                                       ts_te_autopre                     // auto-precharge indicator 
   ,input  [BSM_BITS-1:0]                       gs_te_bsm_num4pre
   ,input  [BSM_BITS-1:0]                       gs_te_bsm_num4rdwr
   ,input  [BSM_BITS-1:0]                       gs_te_bsm_num4act
   ,input                                       gs_te_op_is_rd
   ,input                                       gs_te_op_is_wr
   ,input                                       gs_te_op_is_precharge
   ,input                                       gs_te_op_is_activate
   ,input                                       gs_te_wr_mode
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
  ,input  logic [CMD_LEN_BITS-1:0]              gs_te_rd_length
  ,input  logic [WORD_BITS-1:0]                 gs_te_rd_word
  ,input  logic [PARTIAL_WR_BITS_LOG2-1:0]      gs_te_raddr_lsb_first
  ,input  logic [PW_WORD_CNT_WD_MAX-1:0]        gs_te_pw_num_beats_m1      
`endif
`endif

   ,input  [WP_BITS-1:0]                        gs_te_wr_possible                 // write MAY be issued this cycle
                                                                                  //  clean off flop; before we know if it WILL be issued this cycle
   ,input                                       gs_te_pri_level
   ,output [TOTAL_BSMS-1:0]                     te_bs_rd_hi
   ,output [TOTAL_BSMS-1:0]                     te_ts_vpw_valid
   ,output [TOTAL_BSMS-1:0]                     te_ts_vpr_valid
   ,output                                      te_gs_hi_rd_page_hit_vld
   ,output [BSM_BITS-1:0]                       te_os_hi_bsm_hint
   ,output [BSM_BITS-1:0]                       te_os_lo_bsm_hint
   ,output [BSM_BITS-1:0]                       te_os_wr_bsm_hint
   ,output [BSM_BITS-1:0]                       te_os_wrecc_bsm_hint
   ,output                                      te_gs_block_wr 
   ,output [BSM_BITS-1:0]                       te_os_lo_act_bsm_hint
   ,output [BSM_BITS-1:0]                       te_os_wr_act_bsm_hint
   ,output [TOTAL_BSMS-1:0]                     te_bs_rd_page_hit
   ,output [TOTAL_BSMS-1:0]                     te_bs_rd_valid
   ,output [TOTAL_BSMS-1:0]                     te_bs_wr_page_hit
   ,output [TOTAL_BSMS-1:0]                     te_bs_wr_valid
   ,output  [TOTAL_BSMS-1:0]                    te_bs_rd_bank_page_hit
   ,output  [TOTAL_BSMS-1:0]                    te_bs_wr_bank_page_hit
   ,output                                      te_gs_rd_flush
   ,output                                      te_gs_wr_flush
   ,output                                      te_gs_any_rd_pending
   ,output                                      te_gs_any_wr_pending
   //,output [`MEMC_RD_ENTRY_ADDR]               te_pi_rd_addr
   ,output  [PAGE_BITS-1:0]                     te_pi_rd_addr_ecc_row             // row addr to be used for ecc error tracking
   ,output  [BLK_BITS-1:0]                      te_pi_rd_addr_blk                 // was part of te_pi_rd_addr
   ,output  [OTHER_RD_ENTRY_BITS-1:0]           te_pi_rd_other_fields_rd
   ,output  [BLK_BITS-1:0]                      te_pi_wr_addr_blk                 // was part of te_pi_wr_addr
   ,output  [OTHER_WR_ENTRY_BITS-1:0]           te_pi_wr_other_fields_wr          // everything else we need to keep track of in the CAM - writes

   ,output  [PARTIAL_WR_BITS-1:0]               te_pi_wr_word_valid
   ,output [TOTAL_BSMS*RD_CAM_ADDR_BITS-1:0]    te_os_rd_entry_table             // All Read entry numbers in TE next table 
   ,output [TOTAL_BSMS*WR_CAM_ADDR_BITS_IE-1:0] te_os_wr_entry_table             // All write entry numbers in TE next table
   ,output [TOTAL_BSMS*PAGE_BITS-1:0]           te_os_rd_page_table              // All read page numbers in TE next table
   ,output [TOTAL_BSMS*PAGE_BITS-1:0]           te_os_wr_page_table              // All read page numbers in TE next table   
   ,output [TOTAL_BSMS*AUTOPRE_BITS-1:0]        te_os_rd_cmd_autopre_table
   ,output [TOTAL_BSMS*AUTOPRE_BITS-1:0]        te_os_wr_cmd_autopre_table       
   ,output [TOTAL_BSMS*CMD_LEN_BITS-1:0]        te_os_rd_length_table             // All Read Length Field in TE Next Table
   ,output [TOTAL_BSMS*WORD_BITS-1:0]           te_os_rd_critical_word_table      // All Read Critical Word in TE Next Table
//    `ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
   ,output [TOTAL_BSMS-1:0]                     te_os_rd_pageclose_autopre
//    `endif
   ,output [TOTAL_BSMS-1:0]                     te_os_wr_pageclose_autopre
   ,output [TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0]  te_os_wr_mr_ram_raddr_lsb_first_table
   ,output [TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]    te_os_wr_mr_pw_num_beats_m1_table
   ,input  [MAX_CAM_ADDR_BITS-1:0]              os_te_rdwr_entry                 // CAM entry # for read write replacement from selection n/w
//    ,input  [AUTOPRE_BITS-1:0]                   ts_rdwr_cmd_autopre
   ,input  [BT_BITS-1:0]                        ih_te_ie_bt 
   ,input  [IE_RD_TYPE_BITS-1:0]                ih_te_ie_rd_type
   ,input  [IE_WR_TYPE_BITS-1:0]                ih_te_ie_wr_type
   ,input  [IE_BURST_NUM_BITS-1:0]              ih_te_ie_blk_burst_num
   ,output [BT_BITS-1:0]                        te_mr_ie_bt
   ,output [IE_WR_TYPE_BITS-1:0]                te_mr_ie_wr_type
   ,output [IE_BURST_NUM_BITS-1:0]              te_mr_ie_blk_burst_num
   ,output [BT_BITS-1:0]                        te_pi_ie_bt
   ,output [IE_RD_TYPE_BITS-1:0]                te_pi_ie_rd_type
   ,output [IE_BURST_NUM_BITS-1:0]              te_pi_ie_blk_burst_num
   ,input  [BLK_BITS-1:0]                       ih_te_ie_block_num
   ,input  [NO_OF_BT-1:0]                       ih_te_ie_re_vct
   ,input  [NO_OF_BT-1:0]                       ih_te_ie_btt_vct
   ,output [TOTAL_BSMS-1:0]                     te_bs_wrecc_btt
   ,input  [ECCAP_BITS-1:0]                     ih_te_rd_eccap
   ,input  [ECCAP_BITS-1:0]                     ih_te_wr_eccap
   ,output [ECCAP_BITS-1:0]                     te_pi_eccap  // For read 
   ,output [ECCAP_BITS-1:0]                     te_mr_eccap  // For write
   ,output                                      ddrc_co_perf_war_hazard
   ,output                                      ddrc_co_perf_raw_hazard
   ,output                                      ddrc_co_perf_waw_hazard
   ,output                                      ddrc_co_perf_ie_blk_hazard
   ,output                                      ddrc_co_perf_vlimit_reached_rd
   ,output                                      ddrc_co_perf_vlimit_reached_wr
   ,input [PAGE_BITS-1:0]                       ts_act_page                      // Activate page  
   ,input   [MWR_BITS-1:0]                      wu_te_mwr                        // Masked write information
   ,output  [TOTAL_BSMS*MWR_BITS-1:0]           te_os_mwr_table                  // Masked write entry in CAM, over entire banks
   ,output  [TOTAL_BSMS-1:0]                    te_b3_bit                        // burst bit(column bit)[3] in TE next table
   ,output [TOTAL_LRANKS-1:0]                   te_gs_rank_wr_pending            // WR command pending in the CAM per rank
   ,output [TOTAL_LRANKS-1:0]                   te_gs_rank_rd_pending            // RD command pending in the CAM per rank
   ,output [TOTAL_BANKS-1:0]                    te_gs_bank_wr_pending            // WR command pending in the CAM per rank/bank
   ,output [TOTAL_BANKS-1:0]                    te_gs_bank_rd_pending            // RD command pending in the CAM per rank/bank
   `ifdef SNPS_ASSERT_ON
   `ifndef SYNTHESIS
   ,input                                       reg_ddrc_ecc_type               // used in te_assertions
   ,input  [2:0]                                reg_ddrc_ecc_mode
   ,input  [BURST_RDWR_WIDTH-1:0]               reg_ddrc_burst_rdwr
   ,input  [AM_COL_WIDTH_L-1:0]                 reg_ddrc_addrmap_col_b3
   ,input  [AM_COL_WIDTH_L-1:0]                 reg_ddrc_addrmap_col_b4
   ,input  [AM_COL_WIDTH_L-1:0]                 reg_ddrc_addrmap_col_b5
   ,input  [AM_COL_WIDTH_L-1:0]                 reg_ddrc_addrmap_col_b6
   ,input  [AM_COL_WIDTH_H-1:0]                 reg_ddrc_addrmap_col_b7
   ,input  [AM_COL_WIDTH_H-1:0]                 reg_ddrc_addrmap_col_b8
   ,input  [AM_COL_WIDTH_H-1:0]                 reg_ddrc_addrmap_col_b9
   ,input  [AM_COL_WIDTH_H-1:0]                 reg_ddrc_addrmap_col_b10
   ,input                                       wu_ih_flow_cntrl_req
   `endif // SYNTHESIS
   `endif // SNPS_ASSERT_ON
   ,input [MWR_BITS-1:0]                        ih_te_mwr
   ,input [PARTIAL_WR_BITS-1:0]                 ih_te_wr_word_valid
   ,input [PARTIAL_WR_BITS_LOG2-1:0]            ih_te_wr_ram_raddr_lsb_first
   ,input [PW_WORD_CNT_WD_MAX-1:0]              ih_te_wr_pw_num_beats_m1
   ,input [PW_WORD_CNT_WD_MAX-1:0]              ih_te_wr_pw_num_cols_m1
   ,output [TOTAL_LRANKS-1:0]                           te_gs_rank_rd_valid
   ,output [TOTAL_LRANKS-1:0]                           te_gs_rank_wr_valid
   ,input  [2:0]                                        reg_ddrc_page_hit_limit_rd
   ,input  [2:0]                                        reg_ddrc_page_hit_limit_wr
   ,input                                               reg_ddrc_opt_hit_gt_hpr
   ,input   [2:0]                                       reg_ddrc_visible_window_limit_rd
   ,input   [2:0]                                       reg_ddrc_visible_window_limit_wr
   ,input  [TOTAL_BSMS-1:0]                             ts_te_sel_act_wr         //tell TE the activate command is for write or read.
   ,output [TOTAL_BSMS-1:0]                             te_rws_wr_col_bank                     // entry of colliding bank (1bit for 1bank)
   ,output [TOTAL_BSMS-1:0]                             te_rws_rd_col_bank                     // entry of colliding bank (1bit for 1bank)
   ,output [WR_CAM_ADDR_BITS_IE:0]                      te_num_wr_pghit_entries
   ,output [RD_CAM_ADDR_BITS:0]                         te_num_rd_pghit_entries
   ,output reg [WR_CAM_ADDR_BITS:0]                     te_wr_entry_avail         // Number of non-valid entries (WRCAM only, not include WRECC CAM)
   ,output reg [WR_CAM_ADDR_BITS:0]                     te_wrecc_entry_avail      // Number of non-valid entries (WRECCCAM only, not include WR CAM), valid status
   ,output reg [WR_CAM_ADDR_BITS:0]                     te_wrecc_entry_loaded     // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   ,input                                               ts_te_force_btt
   `ifndef SYNTHESIS
   `ifdef SNPS_ASSERT_ON
   ,output [WR_CAM_ENTRIES_IE-1:0]                      te_wr_entry_valid         // valid write entry in CAM, over entire CAM
   ,output [RD_CAM_ENTRIES-1:0]                         te_rd_entry_valid         // valid write entry in CAM, over entire CAM
   ,output [WR_CAM_ENTRIES_IE-1:0]                      te_wr_page_hit_entries    // valid page-hit entry in CAM
   ,output [RD_CAM_ENTRIES-1:0]                         te_rd_page_hit
   ,input [1:0]                                         reg_ddrc_data_bus_width
   `endif // SNPS_ASSERT_ON
   `endif // SYNTHESIS
   ,input                                               reg_ddrc_lpddr4
   ,input                                              ih_gs_rdhigh_empty                  // no high priority reads pending
   ,input                                              ih_gs_rdlow_empty                   // no low priority reads pending
   ,output reg                                         te_rd_bank_pghit_vld_prefer         // Page hit and valid information of oldest entry for read
   ,output                                             te_wr_bank_pghit_vld_prefer         // Page hit and valid information of oldest entry for write selected between WR CAM and WRECC CMAN
   ,output [RANK_BITS-1:0]                             te_gs_rank_rd_prefer                // rank number of oldest entry in te_rd_cam
   ,output [RANK_BITS-1:0]                             te_gs_rank_wr_prefer                // rank number of oldest entry in te_wr_cam
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
    ,input                                            reg_ddrc_opt_vprw_sch
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
   );

//---------------------------------- WIRES -------------------------------------
wire [RD_CAM_ENTRIES*RANKBANK_BITS-1:0]       te_rd_entry_rankbank;      // rankbank addresses of all CAM entries
wire [WR_CAM_ENTRIES_IE*RANKBANK_BITS-1:0]    te_wr_entry_rankbank;      // rankbank addresses of all CAM entries

wire [RD_CAM_ENTRIES*BSM_BITS-1:0]            te_rd_entry_bsm_num;       // bsm number addresses of all CAM entries
wire [WR_CAM_ENTRIES_IE*BSM_BITS-1:0]         te_wr_entry_bsm_num;       // bsm number of all CAM entries
wire [RD_CAM_ENTRIES -1:0]                    te_vpr_valid;
wire [RD_CAM_ENTRIES -1:0]                    te_vpr_valid_d;
wire [RD_CAM_ENTRIES -1:0]                    te_vpr_page_hit;
wire [RD_CAM_ADDR_BITS-1:0]                   te_sel_vpr_entry;
wire                                          te_sel_vpr_valid;
wire [PAGE_BITS-1:0]                          te_sel_vpr_page;
wire [AUTOPRE_BITS-1:0]                       te_sel_vpr_cmd_autopre;
wire [CMD_LEN_BITS-1:0]                       te_sel_vpr_length;
wire [WORD_BITS-1:0]                          te_sel_vpr_critical_word;
wire [IE_TAG_BITS-1:0]                        te_sel_vpr_ie_tag;

wire [WR_CAM_ENTRIES_IE -1:0]                 te_vpw_valid;
wire [WR_CAM_ENTRIES_IE -1:0]                 te_vpw_valid_d;
wire [WR_CAM_ENTRIES_IE -1:0]                 te_vpw_page_hit;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_sel_vpw_entry;
wire [PAGE_BITS-1:0]                          te_sel_vpw_page;
wire [AUTOPRE_BITS-1:0]                       te_sel_vpw_cmd_autopre;
wire                                          te_sel_vpw_valid;
wire [PARTIAL_WR_BITS_LOG2-1:0]               te_sel_vpw_mr_ram_raddr_lsb;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_vpw_pw_num_beats_m1;
wire [WR_CAM_ENTRIES_IE -1:0]                 te_bank_hit_wrecc_in_vpw;      //bank-hit in entries of vpw with te_sel_wrecc_btt_bank
wire [BSM_BITS-1:0]                           te_sel_wrecc_btt_bank;         //bank# from wrecc_btt replace logic
wire [WR_CAM_ENTRIES_IE -1:0]                 te_bank_hit_vpw_in_wrecc;      //bank-hit in entries of wrecc_btt with te_sel_vpw_bank
wire [BSM_BITS-1:0]                           te_sel_vpw_bank;               //bank# from vpw replace logic
wire [WR_CAM_ENTRIES_IE -1:0]                 te_bank_hit_inc_vpw_in_wrecc;        //bank-hit in entries of wrecc_btt with incoming vpw
wire [BSM_BITS-1:0]                           incoming_vpw_bank;                   //bank# of incoming vpw
wire [MWR_BITS-1:0]                           te_sel_vpw_mwr;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_vpw_pw_num_cols_m1;
wire [IE_TAG_BITS-1:0]                        te_sel_vpw_ie_tag;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_sel_wrecc_btt_entry;            // entry # of selected WRECC  CAM entry for replacement
wire [PAGE_BITS-1:0]                          te_sel_wrecc_btt_page; 
wire [AUTOPRE_BITS-1:0]                       te_sel_wrecc_btt_cmd_autopre; 
wire                                          te_sel_wrecc_btt_valid;            // valid for the selected wrecc btt entry
wire [MWR_BITS-1:0]                            te_sel_wrecc_btt_mwr; 
wire [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_wrecc_btt_pw_num_cols_m1; 
wire [PARTIAL_WR_BITS_LOG2-1:0]               te_sel_wrecc_btt_mr_ram_raddr_lsb;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_wrecc_btt_pw_num_beats_m1;
wire [IE_TAG_BITS-1:0]                         te_sel_wrecc_btt_ie_tag;
wire                                           te_sel_wrecc_btt_ie_btt;
wire                                           te_sel_wrecc_btt_ie_re;
wire [WR_LATENCY_BITS-1:0]                    te_vpw_latency;
wire [1:0]                                    te_vpw_pri;
wire [RD_CAM_ADDR_BITS-1:0]                   te_hi_rd_prefer;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_wrecc_prefer;
wire                                          te_sel_ie_btt;   
wire                                          te_sel_ie_re;   
wire [WR_CAM_ENTRIES_IE-1:0]                  te_wr_col_entries;
wire [RD_CAM_ADDR_BITS-1:0]                   te_lo_rd_prefer;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_wr_prefer;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_pw_num_cols_m1;     // partial write of selected CAM entry
wire [WR_CAM_ENTRIES_IE*PW_WORD_CNT_WD_MAX -1:0] te_pw_num_cols_m1_table;   // partial write of all CAM entries
// wire                                          te_pi_rd_autopre;
// wire                                          te_wr_autopre;
wire [RD_CAM_ENTRIES -1:0]                    te_rd_bank_hit;            // valid read entry matching bank from CAM search
wire [RD_CAM_ENTRIES -1:0]                    te_rd_bank_hit_filtred;    // valid read entry matching bank from CAM search excluding entries already in NTT
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_bank_hit;            // valid write entry matching bank from CAM search
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_bank_hit_filtred;    // valid write entry matching bank from CAM search excluding entries already in NTT 
`ifdef SYNTHESIS
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_entry_valid;         // valid write entry in CAM, over entire CAM
wire [RD_CAM_ENTRIES -1:0]                    te_rd_entry_valid;         // valid read entry in CAM, over entire CAM
`elsif SNPS_ASSERT_ON
`else
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_entry_valid;         // valid write entry in CAM, over entire CAM
wire [RD_CAM_ENTRIES -1:0]                    te_rd_entry_valid;         // valid read entry in CAM, over entire CAM
`endif
wire [RD_CAM_ENTRIES -1:0]                    te_rd_entry_loaded;        // loaded read entry in CAM, over entire CAM
wire [RD_CAM_ENTRIES*PAGE_BITS-1:0]           te_rd_page_table;          // page addresses of all CAM entries
wire [WR_CAM_ENTRIES_IE*PAGE_BITS-1:0]        te_wr_page_table;          // page addresses of all CAM entries
wire [RD_CAM_ENTRIES*AUTOPRE_BITS-1:0]        te_rd_cmd_autopre_table ;  // cmd_autopre  of all CAM entries   
wire [WR_CAM_ENTRIES_IE*AUTOPRE_BITS-1:0]     te_wr_cmd_autopre_table ;  // cmd_autopre  of all CAM entries
wire [RD_CAM_ENTRIES*CMD_LEN_BITS-1:0]        te_rd_cmd_length_table;  // read tag, anything else required - during reads
wire [RD_CAM_ENTRIES*WORD_BITS-1:0]           te_rd_critical_word_table;  // read tag, anything else required - during reads

wire [WR_CAM_ENTRIES_IE*MWR_BITS -1:0]        te_mwr_table;              // masked write of all CAM entries
wire [RD_CAM_ENTRIES*IE_TAG_BITS-1:0]         te_rd_ie_tag_table;        // Inline ECC Tag table for read
wire [WR_CAM_ENTRIES_IE*IE_TAG_BITS-1:0]      te_wr_ie_tag_table;        // Inline ECC Tag table for write
wire [WR_CAM_ENTRIES_IE*PARTIAL_WR_BITS_LOG2-1:0] te_wr_mr_ram_raddr_lsb_first_table;
wire [WR_CAM_ENTRIES_IE*PW_WORD_CNT_WD_MAX-1:0]   te_wr_mr_pw_num_beats_m1_table;
`ifdef SYNTHESIS
wire [RD_CAM_ENTRIES -1:0]                    te_rd_page_hit;
`elsif SNPS_ASSERT_ON
`else
wire [RD_CAM_ENTRIES -1:0]                    te_rd_page_hit;
`endif // SYNTHESIS
wire                                          te_sel_rd_valid;
wire                                          te_sel_wr_valid;
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_page_hit;
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_cam_page_hit;
wire [RD_CAM_ENTRIES -1:0]                    te_rd_page_hit_filtred;    //considered page-hit limiter 
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_page_hit_filtred;    //considered page-hit limiter
wire [RD_CAM_ENTRIES -1:0]                    te_vpr_page_hit_filtred;   //considered page-hit limiter
wire [WR_CAM_ENTRIES_IE -1:0]                 te_vpw_page_hit_filtred;   //considered page-hit limiter
wire [RD_CAM_ENTRIES -1:0]                    te_rd_entry_pri;
wire [RD_CAM_ENTRIES -1:0]                    te_rd_entry_hpr;           //HPR or HPRL
wire                                          te_rd_flush;
wire                                          te_wr_flush;
wire                                          te_rd_flush_due_rd;
wire                                          te_rd_flush_due_wr;
wire                                          te_wr_nxt_wr_combine;
wire                                          te_wr_flush_due_rd;
wire                                          te_wr_flush_due_wr;
wire                                          te_rd_flush_started;     // read flush started (clean off flop)
wire                                          te_wr_flush_started;     // write flush started (clean off flop)
wire [RD_CAM_ADDR_BITS -1:0]                  te_rd_col_entry;         // flopped version of collided entry number
wire [WR_CAM_ADDR_BITS_IE -1:0]               te_wr_col_entry;         // flopped version of collided entry number
wire [TOTAL_BSMS  -1:0]                       te_wr_col_bank;          // flopped version of collided entry number
wire                                          te_wr_ie_blk_collision;  // Block address collision
wire [RD_CAM_ADDR_BITS-1:0]                   te_sel_rd_entry;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_sel_wr_entry;
wire [PAGE_BITS-1:0]                          te_sel_wr_page;           // Row address of selected CAM entry
wire [PAGE_BITS-1:0]                          te_sel_rd_page;           // Row address of selected CAM entry
wire [AUTOPRE_BITS-1:0]                       te_sel_wr_cmd_autopre;    // cmd_autopre of selected CAM entry
wire [AUTOPRE_BITS-1:0]                       te_sel_rd_cmd_autopre;    // cmd_autopre of selected CAM entry
wire [CMD_LEN_BITS-1:0]                       te_sel_rd_length;          // Read Other fields of selected CAM entry
wire [WORD_BITS-1:0]                          te_sel_rd_critical_word;   // Read Other fields of selected CAM entry
wire [MWR_BITS-1:0]                           te_sel_mwr;               // masked write of selected CAM entry
wire [PARTIAL_WR_BITS_LOG2-1:0]               te_sel_wr_mr_ram_raddr_lsb;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_wr_mr_pw_num_beats_m1;      
wire [IE_TAG_BITS-1:0]                        te_sel_rd_ie_tag;
wire [IE_TAG_BITS-1:0]                        te_sel_wr_ie_tag;
wire                                          te_rdwr_autopre;         // indicates a read or write from GS w/ auto-precharge
wire [TOTAL_BSMS-1:0]                         te_wr_pghit_vld;         // one or more valid write page hits
wire                                          rd_pghit_vld_unused;      // unused next table output
wire                                          i_load_ntt;

wire                                          i_load_ntt_ie;           
wire                                          i_unload_ntt_ie;
wire [BT_BITS-1:0]                            i_unload_ntt_ie_bt_reg;
wire                                          i_unload_ntt_ie_bt_reg_vld;
wire [BT_BITS-1:0]                            i_unload_ntt_ie_bt_reg2;
wire                                          i_unload_ntt_ie_bt_reg2_vld;
wire                                          i_load_cam_ie;
wire                                          i_unload_cam_ie;
wire [WR_CAM_ENTRIES_IE-1:0]                  wr_nxt_entry_in_ntt;     // vector indicating entries in NTT
wire [RD_CAM_ENTRIES-1:0]                     rd_nxt_entry_in_ntt;     // vector indicating entries in NTT


wire                                          te_wr_collision_vld_due_rd;
wire                                          te_wr_collision_vld_due_wr;
`ifdef SYNTHESIS
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_page_hit_entries;
`elsif SNPS_ASSERT_ON
`else
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_page_hit_entries;
`endif // SNPS_ASSERT_ON

`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
  wire [CMD_LEN_BITS-1:0]                       te_pi_rd_length_int;
  wire [WORD_BITS-1:0]                          te_pi_rd_word_int;
      wire  [PARTIAL_WR_BITS_LOG2-1:0]          te_mr_ram_raddr_lsb_first_int;
      wire  [PW_WORD_CNT_WD_MAX-1:0]            te_mr_pw_num_beats_m1_int;
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON
`ifdef SNPS_ASSERT_ON
`endif // SNPS_ASSERT_ON
// rd_nxt_entry_in_ntt in masking te_wr_bank_hit depending on command inside rd cam to avoid filtering it for ACT
// don't need consider bm_te_rd_bank_hit_mask (entry is allocated or not) because te_rd_bank_hit_filtred
// is used for normal replace that is based on a read is scheduled from this bank.
assign te_rd_bank_hit_filtred = te_rd_bank_hit // te_rd_bank_hit is already filtered 
////   `ifdef  UMCTL2_DYN_BSM
////     & (~bm_te_rd_bank_hit_mask)
////   `endif // UMCTL2_DYN_BSM
   ;
// wr_nxt_entry_in_ntt in masking te_wr_bank_hit inside wr cam to avoid filtering write combine valid
// don't need consider bm_te_wr_bank_hit_mask (entry is allocated or not) because te_wr_bank_hit_filtred
// is used for normal replace that is based on a write/combine is scheduled from this bank.
assign te_wr_bank_hit_filtred = te_wr_bank_hit
////   `ifdef  UMCTL2_DYN_BSM
////     & (~bm_te_wr_bank_hit_mask)
////   `endif // UMCTL2_DYN_BSM
   ;

wire [TOTAL_BSMS-1:0]                         te_dh_rd_bsm_valid;
wire [TOTAL_BSMS-1:0]                         te_dh_rd_bsm_page_hit;
wire [TOTAL_BSMS-1:0]                         te_dh_wr_bsm_valid;
wire [TOTAL_BSMS-1:0]                         te_dh_wr_bsm_page_hit;

wire                                          ih_te_rd_autopre_i;
// When reg_ddrc_autopre_rmw==1, AP is not applied to read part of RMW 
assign ih_te_rd_autopre_i = (reg_ddrc_autopre_rmw & ih_te_rd_rmw)? 1'b0 :ih_te_rd_autopre;

wire [WR_ECC_CAM_ENTRIES-1:0] te_wrecc_btt_valid;
wire [WR_CAM_ENTRIES_IE-1:0]  te_wrecc_btt_valid_filtred;
wire                           te_any_wrecc_btt_valid;

wire [RD_CAM_ADDR_BITS-1:0]                   i_ih_te_lo_rd_prefer;
wire [RD_CAM_ADDR_BITS-1:0]                   i_ih_te_hi_rd_prefer;
wire [BSM_BITS-1:0]                           te_bypass_rank_bg_bank_num;
wire [WR_CAM_ADDR_BITS-1:0]                   i_ih_te_wr_prefer;

wire [WR_ECC_CAM_ADDR_BITS-1:0]               i_ih_te_wrecc_prefer;


  
wire i_gs_te_op_is_wr;
assign i_gs_te_op_is_wr = gs_te_op_is_wr;





wire                 te_rd_flush_started_replace;
wire                 te_wr_flush_started_replace;
wire                 te_rd_flush_started_replace_pre;
wire                 te_wr_flush_started_replace_pre;



//----------------------------------------------
// Interface for replace logic triggered by PRE
//----------------------------------------------

wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_bank_hit_pre;        // valid write entry matching bank from CAM search excluding entries already in NTT 
wire [RD_CAM_ENTRIES -1:0]                    te_rd_bank_hit_pre;        // valid write entry matching bank from CAM search excluding entries already in NTT 
wire [RD_CAM_ADDR_BITS-1:0]                   te_sel_rd_entry_pre;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_sel_wr_entry_pre;
wire [PAGE_BITS-1:0]                          te_sel_wr_page_pre;           // Row address of selected CAM entry
wire [PAGE_BITS-1:0]                          te_sel_rd_page_pre;           // Row address of selected CAM entry
wire [AUTOPRE_BITS-1:0]                       te_sel_wr_cmd_autopre_pre;    // cmd_autopre of selected CAM entry
wire [AUTOPRE_BITS-1:0]                       te_sel_rd_cmd_autopre_pre;    // cmd_autopre of selected CAM entry
wire [CMD_LEN_BITS-1:0]                       te_sel_rd_cmd_length_pre;   // Other Fields of selected CAM entry
wire [WORD_BITS-1:0]                          te_sel_rd_critical_word_pre;   // Other Fields of selected CAM entry
wire [MWR_BITS-1:0]                           te_sel_mwr_pre;               // masked write of selected CAM entry
wire                                          te_sel_rd_valid_pre_unused;
wire                                          te_sel_wr_valid_pre_unused;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_pw_num_cols_m1_pre;     // partial write of selected CAM entry
wire [PARTIAL_WR_BITS_LOG2-1:0]               te_sel_wr_mr_ram_raddr_lsb_pre;         // ram addr of selected CAM entry
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_wr_mr_pw_num_beats_m1_pre;         // num beats of selected CAM entry
wire [IE_TAG_BITS-1:0]                        te_sel_rd_ie_tag_pre;
wire [IE_TAG_BITS-1:0]                        te_sel_wr_ie_tag_pre;
wire                                          te_sel_ie_btt_pre;   
wire                                          te_sel_ie_re_pre;   
wire [IE_TAG_BITS-1:0]                        te_sel_rd_ie_tag_pre_unused;
wire [IE_TAG_BITS-1:0]                        te_sel_wr_ie_tag_pre_unused;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_sel_wrecc_btt_entry_pre_unused;
wire [PAGE_BITS-1:0]                          te_sel_wrecc_btt_page_pre_unused; 
wire [AUTOPRE_BITS-1:0]                       te_sel_wrecc_btt_cmd_autopre_pre_unused; 
wire                                          te_sel_wrecc_btt_valid_pre_unused;
wire [MWR_BITS-1:0]                            te_sel_wrecc_btt_mwr_pre_unused; 
wire [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_wrecc_btt_pw_num_cols_m1_pre_unused; 
wire [IE_TAG_BITS-1:0]                         te_sel_wrecc_btt_ie_tag_pre_unused;
wire                                           te_sel_wrecc_btt_ie_btt_pre_unused;
wire                                           te_sel_wrecc_btt_ie_re_pre_unused;
wire [PARTIAL_WR_BITS_LOG2-1:0]               te_sel_wrecc_btt_mr_ram_raddr_lsb_pre_unused;         // ram addr of selected CAM entry
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_wrecc_btt_mr_pw_num_beats_m1_pre_unused;         // num beats of selected CAM entry
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_wrecc_prefer_pre_unused;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_wr_prefer_pre_unused;
wire [RD_CAM_ADDR_BITS-1:0]                   te_sel_rd_entry_pre_unused;
wire [WR_CAM_ADDR_BITS_IE-1:0]                te_sel_wr_entry_pre_unused;
wire [PAGE_BITS-1:0]                          te_sel_wr_page_pre_unused;           // Row address of selected CAM entry
wire [PAGE_BITS-1:0]                          te_sel_rd_page_pre_unused;           // Row address of selected CAM entry
wire [AUTOPRE_BITS-1:0]                       te_sel_wr_cmd_autopre_pre_unused;    // cmd_autopre of selected CAM entry
wire [AUTOPRE_BITS-1:0]                       te_sel_rd_cmd_autopre_pre_unused;    // cmd_autopre of selected CAM entry
wire [CMD_LEN_BITS-1:0]                       te_sel_vpr_cmd_length_pre_unused;
wire [WORD_BITS-1:0]                          te_sel_vpr_critical_word_pre_unused;

wire                                          te_sel_vpr_valid_pre_unused;
wire                                          te_sel_vpw_valid_pre_unused;
wire [MWR_BITS-1:0]                           te_sel_mwr_pre_unused;               // masked write of selected CAM entry
wire [PARTIAL_WR_BITS_LOG2-1:0]               te_sel_vpw_mr_ram_raddr_lsb_pre_unused;         // ram addr of selected CAM entry
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_vpw_mr_pw_num_beats_m1_pre_unused;         // num beats of selected CAM entry
wire [RD_CAM_ADDR_BITS-1:0]                   te_lo_rd_prefer_pre_unused;
wire [RD_CAM_ADDR_BITS-1:0]                   te_hi_rd_prefer_pre_unused;
wire [PW_WORD_CNT_WD_MAX-1:0]                 te_sel_pw_num_cols_m1_pre_unused;     // partial write of selected CAM entry



wire [RD_CAM_ENTRIES -1:0]                    upd_to_vpr_due_ie_unused;

//--------ifndef DDRCTL_LLC_4CYCSCH-------------------------------------
// Localparam for hmatrix
//---------------------------------------------
// For Enhanced CAM pointer feature
// Number of comparator sets for each hmatrix
localparam RD_NUM_COMPS    = 1 + 1 + 2 ; 
localparam WR_NUM_COMPS    = 1 + 1 + 2 ; 
localparam WRECC_NUM_COMPS = 1 + 1 + 2;
localparam ORG_BG  = 2'b00 ;
localparam ORG_16B = 2'b10 ;

//---------------------------------------
// Interface between replace and hmatrix
//---------------------------------------
wire [RD_CAM_ENTRIES*RD_NUM_COMPS-1:0]        hmx_rd_masks;
wire [RD_CAM_ENTRIES*RD_NUM_COMPS-1:0]        hmx_rd_oldest_ohs;

wire [WR_CAM_ENTRIES*WR_NUM_COMPS-1:0]        hmx_wr_masks;
wire [WR_CAM_ENTRIES*WR_NUM_COMPS-1:0]        hmx_wr_oldest_ohs;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_mask;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_oldest_oh;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_mask;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_oldest_oh;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_pre_mask;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_pre_oldest_oh;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_pre_mask;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_pre_oldest_oh;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_pre_mask_vpr_unused;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_pre_mask_vpw_unused;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_btt_mask_pre_unused;

wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_vpr_mask;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_vpr_oldest_oh;
wire [RD_CAM_ENTRIES-1:0]                     hmx_rd_vpr_abso_oldest_oh; // Absolute oldest entry within exVPR 
wire [RD_CAM_ADDR_BITS-1:0]                   te_vpr_prefer;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_vpw_mask;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_vpw_oldest_oh;
wire [WR_CAM_ENTRIES-1:0]                     hmx_wr_vpw_abso_oldest_oh; // Absolute oldest entry within exVPW 
wire [WR_CAM_ADDR_BITS-1:0]                   te_vpw_prefer;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_btt_mask_act_unused;


wire [WR_ECC_CAM_ENTRIES*WRECC_NUM_COMPS-1:0] hmx_wrecc_masks;
wire [WR_ECC_CAM_ENTRIES*WRECC_NUM_COMPS-1:0] hmx_wrecc_oldest_ohs;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_btt_mask;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_btt_oldest_oh;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_btt_abso_oldest_oh; // Absolute oldest entry within WRECC BTT1
wire [WR_ECC_CAM_ADDR_BITS-1:0]               te_wrecc_btt_prefer;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_mask;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_oldest_oh;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_pre_mask;
wire [WR_ECC_CAM_ENTRIES-1:0]                 hmx_wrecc_pre_oldest_oh;

// For Visible window limiter
wire [RD_CAM_ENTRIES-1:0]                     te_rd_vlimit_decr;
wire [WR_CAM_ENTRIES-1:0]                     te_wr_vlimit_decr;
wire [WR_ECC_CAM_ENTRIES-1:0]                 te_wrecc_vlimit_decr_unused;

//----------
// CAM push      
//----------
wire                                          push_rd_cam;     // Push an entry into RDCAM(LPR or HPR)
wire                                          push_lpr_cam;    // Push an entry into LPR CAM
wire                                          push_hpr_cam;    // Push an entry into HPR CAM
wire                                          push_wr_cam;     // Push an entry into WR CAM

wire                                          pop_rd_cam;      // Pop an entry into RDCAM(LPR or HPR)
wire                                          pop_lpr_cam;     // Pop an entry into LPR CAM
wire                                          pop_hpr_cam;     // Pop an entry into HPR CAM
wire                                          pop_wr_cam;      // Pop an entry into WR CAM
wire                                          push_wrecc_cam;  // Push an entry into WRECC CAM
wire                                          pop_wrecc_cam;   // Pop an entry into WRECC CAM

// Page-hit Limiter
wire [WR_CAM_ENTRIES_IE -1:0]                 te_wr_entry_critical_early;
wire [TOTAL_BSMS -1:0]                        te_wr_entry_critical_per_bsm;
wire [RD_CAM_ENTRIES -1:0]                    te_rd_entry_critical_early;
wire [TOTAL_BSMS -1:0]                        te_rd_entry_critical_per_bsm;
wire                                          te_wr_entry_critical_currnt_bsm;



wire                                          te_wr_rme_pas_viol;
//----------------------------
// Mask assignment for hmatrix
//----------------------------
assign hmx_rd_masks = 
    {
       te_vpr_valid_d,
       hmx_rd_vpr_mask,
       hmx_rd_pre_mask,
       hmx_rd_mask
    };

assign hmx_wr_masks = 
    {
       te_vpw_valid_d[WR_CAM_ENTRIES-1:0],
       hmx_wr_vpw_mask,
       hmx_wr_pre_mask,
       hmx_wr_mask
    };


wire [RD_CAM_ENTRIES*RD_NUM_COMPS-1:0]        hmx_rd_oldest_ohs_w;
assign hmx_rd_oldest_ohs_w = hmx_rd_oldest_ohs;
wire [WR_CAM_ENTRIES*WR_NUM_COMPS-1:0]        hmx_wr_oldest_ohs_w;
assign hmx_wr_oldest_ohs_w = hmx_wr_oldest_ohs;


assign 
    {
       hmx_rd_vpr_abso_oldest_oh,
       hmx_rd_vpr_oldest_oh,
       hmx_rd_pre_oldest_oh,
       hmx_rd_oldest_oh
    } 
    = hmx_rd_oldest_ohs_w;

assign
    {
       hmx_wr_vpw_abso_oldest_oh,
       hmx_wr_vpw_oldest_oh,
       hmx_wr_pre_oldest_oh,
       hmx_wr_oldest_oh
    }  
    = hmx_wr_oldest_ohs_w;

assign hmx_wrecc_masks = 
    {
       te_wrecc_btt_valid,
       hmx_wrecc_btt_mask,
       hmx_wrecc_pre_mask,
       hmx_wrecc_mask
    };

assign
    {
       hmx_wrecc_btt_abso_oldest_oh,
       hmx_wrecc_btt_oldest_oh,
       hmx_wrecc_pre_oldest_oh,
       hmx_wrecc_oldest_oh
    } 
    = hmx_wrecc_oldest_ohs;



wire                                          te_ih_rd_retry_int;
wire                                          te_ih_wr_retry_int;

assign te_rd_page_hit_filtred = te_rd_page_hit & (~te_rd_entry_critical_early) ;
assign te_wr_page_hit_filtred = te_wr_page_hit & (~te_wr_entry_critical_early) ;
assign te_vpr_page_hit_filtred = te_vpr_page_hit & (~te_rd_entry_critical_early) ;
assign te_vpw_page_hit_filtred = te_vpw_page_hit & (~te_wr_entry_critical_early) ;


wire [RD_CAM_ENTRIES -1:0]                    te_vpr_valid_filtred;
wire [WR_CAM_ENTRIES_IE -1:0]                 te_vpw_valid_filtred;
assign te_vpr_valid_filtred = te_vpr_valid_d &
                                (~rd_nxt_entry_in_ntt)
                              ;
assign te_vpw_valid_filtred = te_vpw_valid_d &
                                (~wr_nxt_entry_in_ntt)
                              ;



wire                                          ih_te_rd_link_to_write;

//spyglass disable_block W528
//SMD: A signal or variable is set but never read - ih_te_rd_link_to_write
//SJ: Signal gets different values depending on config. Used only for uMCTL2. Decided to keep current implementation.
// te_ih_rd_retry_int/te_ih_wr_retry_int used by subblocks in 
// tengine, but use same retry signal
assign te_ih_rd_retry_int = te_ih_retry;
assign te_ih_wr_retry_int = te_ih_retry;

// for ih_te_rd_valid only high at same time as ih_te_wr_valid for RMW 
assign ih_te_rd_link_to_write = ih_te_rd_valid;
//spyglass enable_block W528

wire [TOTAL_BSMS*PAGE_BITS -1:0]              rd_nxt_page_table;       // rd NTT next xact page for each rank/bank
wire [TOTAL_BSMS*PAGE_BITS -1:0]              wr_nxt_page_table;       // wr NTT next xact page for each rank/bank

wire [TOTAL_BSMS*AUTOPRE_BITS-1:0]            rd_nxt_cmd_autopre_table;
wire [TOTAL_BSMS*AUTOPRE_BITS-1:0]            wr_nxt_cmd_autopre_table;

wire [TOTAL_BSMS*CMD_LEN_BITS-1:0]            rd_nxt_length_table;
wire [TOTAL_BSMS*WORD_BITS-1:0]               rd_nxt_word_table;
wire [TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0]    wr_nxt_mr_ram_raddr_lsb_first_table;
wire [TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]      wr_nxt_mr_pw_num_beats_m1_table;
 
assign te_os_rd_page_table = rd_nxt_page_table;                       // All read page numbers in TE next table
assign te_os_wr_page_table = wr_nxt_page_table;                       // All write page numbers in TE next table   

assign te_os_wr_cmd_autopre_table = wr_nxt_cmd_autopre_table;
assign te_os_rd_cmd_autopre_table = rd_nxt_cmd_autopre_table;


assign te_os_rd_length_table        = rd_nxt_length_table;
assign te_os_rd_critical_word_table = rd_nxt_word_table;


assign te_os_wr_mr_ram_raddr_lsb_first_table = wr_nxt_mr_ram_raddr_lsb_first_table;
assign te_os_wr_mr_pw_num_beats_m1_table     = wr_nxt_mr_pw_num_beats_m1_table;

 
wire                                          be_op_is_activate_bypass;

   assign be_op_is_activate_bypass= 1'b0;   

//localparam IE_UNIQ_BLK_BITS  = (`MEMC_INLINE_ECC_EN==0)? 0 : (`MEMC_BURST_LENGTH==16)? 5 : 4; 
//Can be reduced: need to 3 highest columun bits number.
localparam IE_UNIQ_BLK_BITS  = (`MEMC_INLINE_ECC_EN==0)? 0 : BLK_BITS; 
localparam IE_UNIQ_BLK_LSB   = 0;
localparam IE_UNIQ_CID_BITS  = (`MEMC_BURST_LENGTH==16)? `UMCTL2_CID_WIDTH : 0;
localparam IE_UNIQ_RBK_BITS  = (`MEMC_INLINE_ECC_EN==0)? 0 : BG_BANK_BITS+IE_UNIQ_CID_BITS;

// Overwrite ie_cmd_type to all 1 (reserved) when these are invalid
// so that Don't care value can be ignored for collision detection
wire [IE_WR_TYPE_BITS-1:0] ih_te_ie_wr_type_int;
wire [IE_RD_TYPE_BITS-1:0] ih_te_ie_rd_type_int; 

assign ih_te_ie_wr_type_int = {IE_WR_TYPE_BITS{(~ih_te_wr_valid)}} | ih_te_ie_wr_type;
// i.e.) assign ih_te_ie_wr_type_int = (ih_te_wr_valid)? ih_te_ie_wr_type : {IE_WR_TYPE_BITS{1'b1}};
assign ih_te_ie_rd_type_int = {IE_RD_TYPE_BITS{(~ih_te_rd_valid)}} | ih_te_ie_rd_type;
// i.e.) assign ih_te_ie_rd_type_int = (ih_te_rd_valid)? ih_te_ie_rd_type : {IE_RD_TYPE_BITS{1'b1}};


// Generate unique bits for Inline-ECC
wire [IE_UNIQ_BLK_BITS-1:0] ie_ecc_uniq_block_num;

assign ie_ecc_uniq_block_num    = ih_te_ie_block_num[IE_UNIQ_BLK_LSB+:IE_UNIQ_BLK_BITS];

// i_rd_ecc_status: Indicates this incoming RD command cannot get scheduled for now 
wire                       i_rd_ecc_status;


wire [WR_CAM_ENTRIES_IE-1:0]                  te_wr_entry_ie_btt;
wire [WR_CAM_ENTRIES_IE-1:0]                  te_wr_entry_ie_re;

  wire   ddrc_co_perf_ie_blk_hazard_wr;
  wire   ddrc_co_perf_ie_blk_hazard_rd;
  assign ddrc_co_perf_ie_blk_hazard = ddrc_co_perf_ie_blk_hazard_wr | ddrc_co_perf_ie_blk_hazard_rd;


//----------------------------------------------
// Generate te_mr, te_pi signals for Inline ECC
//----------------------------------------------
assign {
  te_pi_eccap,
  te_pi_ie_rd_type,
  te_pi_ie_bt,
  te_pi_ie_blk_burst_num
  } = os_te_rdwr_ie_tag;

assign {
  te_mr_eccap,
  te_mr_ie_wr_type,
  te_mr_ie_bt,
  te_mr_ie_blk_burst_num
  } = os_te_rdwr_ie_tag;


wire                        te_entry_valid_clr_by_wc; // Only apply for [WR_CAM_ENTRIES-1:0]

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_wr_entry_avail <= {1'b1,{WR_CAM_ADDR_BITS{1'b0}}};
    te_wrecc_entry_avail <= {2'b01,{(WR_CAM_ADDR_BITS-1){1'b0}}};
    te_wrecc_entry_loaded <= {1'b0,{WR_CAM_ADDR_BITS{1'b0}}};
  end
  else begin
    // te_wr_entry_avail calculation
    if (i_load_ntt & ~(te_entry_valid_clr_by_wc | (i_gs_te_op_is_wr & (te_mr_ie_wr_type!=`IE_WR_TYPE_WE_BW ) ))) begin
      te_wr_entry_avail <= te_wr_entry_avail - 1'b1;
    end
    else if (~i_load_ntt & (te_entry_valid_clr_by_wc | (i_gs_te_op_is_wr & (te_mr_ie_wr_type!=`IE_WR_TYPE_WE_BW) ))) begin
      te_wr_entry_avail <= te_wr_entry_avail + 1'b1;
    end
    // te_wrecc_entry_avail calculation
    // Factors to increase/decrease te_wrecc_entry_avail counter
    // A. i_load_ntt_ie (Indicate WD_E is scheduled out and WE_BW is enabled.)
    // B. gs_te_op_is_wr && (te_mr_ie_wr_type == `IE_WR_TYPE_WE_BW)
    //    B1. ~i_unload_ntt_ie_bt_reg_vld && ~i_unload_ntt_ie_bt_reg2_vld
    //    B2. i_unload_ntt_ie_bt_reg_vld && (te_mr_ie_bt == i_unload_ntt_ie_bt_reg)
    //    B3. i_unload_ntt_ie_bt_reg_vld && (te_mr_ie_bt != i_unload_ntt_ie_bt_reg) && ~i_unload_ntt_ie_bt_reg2_vld
    //    B4. i_unload_ntt_ie_bt_reg2_vld && (te_mr_ie_bt == i_unload_ntt_ie_bt_reg2)
    //    B5. i_unload_ntt_ie_bt_reg2_vld && (te_mr_ie_bt != i_unload_ntt_ie_bt_reg2) && ~i_unload_ntt_ie_bt_reg_vld
    //    B6. i_unload_ntt_ie_bt_reg_vld && i_unload_ntt_ie_bt_reg2_vld && (te_mr_ie_bt != i_unload_ntt_ie_bt_reg) && (te_mr_ie_bt != i_unload_ntt_ie_bt_reg2)
    // C. i_unload_ntt_ie (Indicate IH incomes a WD_E with same BT, so NTT will be invalid; or i_combine_match for RMW case)
    // It's impossible for A and B happening at the same time.
    // ~A && ~B  && ~C : same
    // ~A && ~B  &&  C : +1
    // ~A &&  B1 && ~C : +1
    // ~A &&  B2 && ~C : same
    // ~A &&  B3 && ~C : +1
    // ~A &&  B4 && ~C : impossible
    // ~A &&  B5 && ~C : +1
    // ~A &&  B6 && ~C : +1
    // ~A &&  B1 &&  C : +2
    // ~A &&  B2 &&  C : impossible
    // ~A &&  B3 &&  C : +2
    // ~A &&  B4 &&  C : impossible
    // ~A &&  B5 &&  C : +2
    // ~A &&  B6 &&  C : impossible for i_unload_ntt_ie asserted for consecutive 3 clks.
    //  A && ~B  && ~C : -1 (if A==1, B must be 0)
    //  A && ~B  &&  C : same
    //  A &&  B  && ~C : impossible
    //  A &&  B  &&  C : impossible
    if (i_load_ntt_ie && ~i_unload_ntt_ie)
      te_wrecc_entry_avail <= te_wrecc_entry_avail - 1'b1; // -1 case
    else if (~i_load_ntt_ie && (
      (~(i_gs_te_op_is_wr & (te_mr_ie_wr_type == `IE_WR_TYPE_WE_BW)) && i_unload_ntt_ie) || (i_gs_te_op_is_wr & (te_mr_ie_wr_type == `IE_WR_TYPE_WE_BW) && (
        (~i_unload_ntt_ie_bt_reg_vld && ~i_unload_ntt_ie_bt_reg2_vld && ~i_unload_ntt_ie) ||
        ((i_unload_ntt_ie_bt_reg_vld & (te_mr_ie_bt!=i_unload_ntt_ie_bt_reg)) && ~i_unload_ntt_ie_bt_reg2_vld && ~i_unload_ntt_ie) ||
        ((i_unload_ntt_ie_bt_reg_vld & (te_mr_ie_bt!=i_unload_ntt_ie_bt_reg)) && (i_unload_ntt_ie_bt_reg2_vld & (te_mr_ie_bt!=i_unload_ntt_ie_bt_reg2))) ||
        (~i_unload_ntt_ie_bt_reg_vld && (i_unload_ntt_ie_bt_reg2_vld & (te_mr_ie_bt!=i_unload_ntt_ie_bt_reg2)) && ~i_unload_ntt_ie)
        ))))
      te_wrecc_entry_avail <= te_wrecc_entry_avail + 1'b1; // +1 case
    else if (i_unload_ntt_ie && (i_gs_te_op_is_wr & (te_mr_ie_wr_type == `IE_WR_TYPE_WE_BW)))
      te_wrecc_entry_avail <= te_wrecc_entry_avail + 2'b10; // +2 case
    // te_wrecc_entry_loaded calculation
    if (i_load_cam_ie && ~i_unload_cam_ie)
      te_wrecc_entry_loaded <= te_wrecc_entry_loaded + 1'b1;
    else if (i_unload_cam_ie && ~i_load_cam_ie)
      te_wrecc_entry_loaded <= te_wrecc_entry_loaded - 1'b1;
  end
end

`ifdef SNPS_ASSERT_ON
wire [BT_BITS-1:0]                    i_te_mr_ie_bt;
wire [IE_WR_TYPE_BITS-1:0]            i_te_mr_ie_wr_type;
wire [IE_BURST_NUM_BITS-1:0]          i_te_mr_ie_blk_burst_num;
wire [BT_BITS-1:0]                    i_te_pi_ie_bt;
wire [IE_RD_TYPE_BITS-1:0]            i_te_pi_ie_rd_type;
wire [IE_BURST_NUM_BITS-1:0]          i_te_pi_ie_blk_burst_num;
wire [WR_CAM_ENTRIES_IE-1:0]          i_ie_wr_blk_addr_collision;
wire [RD_CAM_ENTRIES   -1:0]          i_ie_rd_blk_addr_collision;
wire [ECCAP_BITS-1:0]                 i_te_pi_eccap;
wire [ECCAP_BITS-1:0]                 i_te_mr_eccap;
`ifndef SYNTHESIS
wire [WR_CAM_ENTRIES_IE-1:0]          i_wr_entry_we_bw_loaded;
`endif
`endif


// Max rank wr/rd logic
reg [TOTAL_BSMS-1:0]          te_rd_bank_pghit_vld;              // Page hit and valid information for read (per bank)
reg [TOTAL_BSMS-1:0]          te_wr_bank_pghit_vld;              // Page hit and valid information for write (per bank)

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_rd_bank_pghit_vld <= {TOTAL_BSMS{1'b0}};
    te_wr_bank_pghit_vld <= {TOTAL_BSMS{1'b0}};
  end
  else begin
    te_rd_bank_pghit_vld <= te_bs_rd_valid & te_bs_rd_page_hit;
    te_wr_bank_pghit_vld <= te_bs_wr_valid & te_bs_wr_page_hit;
  end
end

wire [RANKBANK_BITS-1:0]      te_rd_rankbank_prefer;             // cid and rank number of oldest entry
wire [RANKBANK_BITS-1:0]      te_wr_rankbank_prefer;             // cid and rank number of oldest entry
reg                           te_norm_wr_bank_pghit_vld_prefer;  // Page hit and valid information of oldest entry in WRCAM

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_rd_bank_pghit_vld_prefer      <= 1'b0;
    te_norm_wr_bank_pghit_vld_prefer <= 1'b0;
  end
  else begin
    te_rd_bank_pghit_vld_prefer      <= te_rd_bank_pghit_vld[te_rd_rankbank_prefer];
    te_norm_wr_bank_pghit_vld_prefer <= te_wr_bank_pghit_vld[te_wr_rankbank_prefer];
  end
end

reg [TOTAL_BSMS-1:0] te_wrecc_bank_pghit_btt_vld;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_wrecc_bank_pghit_btt_vld <= {TOTAL_BSMS{1'b0}};
  end
  else begin
    te_wrecc_bank_pghit_btt_vld <= te_bs_wr_valid & te_bs_wr_page_hit & te_bs_wrecc_btt;
  end
end

reg [BSM_BITS-1:0] te_os_wrecc_bsm_hint_r;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
     te_os_wrecc_bsm_hint_r <= {BSM_BITS{1'b0}};
  end
  else begin
     te_os_wrecc_bsm_hint_r <= te_os_wrecc_bsm_hint;
  end
end

wire te_wrecc_bank_pghit_btt_vld_prefer;     // Page hit and valid information of oldest entry in ECCWR CAM
assign te_wrecc_bank_pghit_btt_vld_prefer = te_wrecc_bank_pghit_btt_vld[te_os_wrecc_bsm_hint_r];

assign te_wr_bank_pghit_vld_prefer = te_norm_wr_bank_pghit_vld_prefer
                                     | te_wrecc_bank_pghit_btt_vld_prefer
                                     ;



assign te_wrecc_btt_valid = te_wr_entry_valid[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES] & te_wr_entry_ie_btt[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES];
assign te_wrecc_btt_valid_filtred = te_wr_entry_valid & te_wr_entry_ie_btt & ~wr_nxt_entry_in_ntt
                              ;
assign te_any_wrecc_btt_valid = |te_wrecc_btt_valid; 
// JIRA___ID: temporary assignment
// burst bit(column bit)[3] in TE next table
assign te_b3_bit = {TOTAL_BSMS{1'b0}};

//------------------------------- INSTANTIATIONS -------------------------------
  te_rd_cam
   #(
    .RD_CAM_ADDR_BITS       (RD_CAM_ADDR_BITS), 
    .RANK_BITS              (LRANK_BITS), 
    .BG_BITS                (BG_BITS), 
    .BANK_BITS              (BANK_BITS), 
    .BG_BANK_BITS           (BG_BANK_BITS), 
    .PAGE_BITS              (PAGE_BITS), 
    .BLK_BITS               (BLK_BITS), 
    .BSM_BITS               (BSM_BITS), 
    .OTHER_RD_RMW_LSB       (OTHER_RD_RMW_LSB), 
    .OTHER_RD_RMW_TYPE_BITS (OTHER_RD_RMW_TYPE_BITS),
    .WORD_BITS              (WORD_BITS),
    .CMD_LEN_BITS           (CMD_LEN_BITS),
    .OTHER_RD_ENTRY_BITS    (OTHER_RD_ENTRY_BITS),
    .BT_BITS                (BT_BITS),
    .NO_OF_BT               (NO_OF_BT),
    .IE_WR_TYPE_BITS        (IE_WR_TYPE_BITS),
    .IE_RD_TYPE_BITS        (IE_RD_TYPE_BITS),
    .IE_BURST_NUM_BITS      (IE_BURST_NUM_BITS),
    .IE_TAG_BITS            (IE_TAG_BITS),
    .IE_UNIQ_BLK_BITS       (IE_UNIQ_BLK_BITS),
    .IE_UNIQ_BLK_LSB        (IE_UNIQ_BLK_LSB),
    .IE_MASKED_BITS         (IE_MASKED_BITS),
    .ENTRY_AUTOPRE_BITS     (AUTOPRE_BITS),
    .ECCAP_BITS             (ECCAP_BITS),
    .DDR4_COL3_BITS         (DDR4_COL3_BITS),
    .LP_COL4_BITS           (LP_COL4_BITS),
    .RETRY_RD_BITS          (RETRY_RD_BITS),
    .RETRY_TIMES_WIDTH      (RETRY_TIMES_WIDTH),
    .CRC_RETRY_TIMES_WIDTH  (0),
    .UE_RETRY_TIMES_WIDTH   (0),
    .RD_CRC_RETRY_LIMIT_REACH_BITS (0),
    .RD_UE_RETRY_LIMIT_REACH_BITS (0),
    .RMW_BITS               (RMW_BITS)
  )
  RDcam (
              .core_ddrc_rstn            (core_ddrc_rstn) 
             ,.dh_te_pageclose           (dh_te_pageclose) 
             ,.dh_te_pageclose_timer     (dh_te_pageclose_timer) 
             ,.co_te_clk                 (co_te_clk)
             ,.ddrc_cg_en                (ddrc_cg_en) 
             ,.i_rd_command              (ih_te_rd_valid) 
             ,.i_wr_command              (ih_te_wr_valid) 
             ,.ih_te_rd_rank_num         (ih_te_rd_rank_num [LRANK_BITS-1:0]) 
             ,.ih_te_rd_bg_bank_num      (ih_te_rd_bg_bank_num [BG_BANK_BITS-1:0]) 
             ,.ih_te_rd_page_num         (ih_te_rd_page_num [PAGE_BITS-1:0]) 
             ,.ih_te_rd_block_num        (ih_te_rd_block_num [BLK_BITS-1:0]) 
             ,.ih_te_rd_autopre          (ih_te_rd_autopre_i) 
             ,.ih_te_rmw                 (ih_te_rd_rmw) 
             ,.rd_nxt_entry_in_ntt       (rd_nxt_entry_in_ntt)
             ,.gs_te_wr_mode             (gs_te_wr_mode)
             ,.reg_ddrc_dis_opt_ntt_by_act (reg_ddrc_dis_opt_ntt_by_act)
             ,.ih_te_ie_bt               (ih_te_ie_bt)
             ,.ih_te_ie_rd_type          (ih_te_ie_rd_type_int)
             ,.ih_te_ie_wr_type          (ih_te_ie_wr_type_int)
             ,.ih_te_ie_blk_burst_num    (ih_te_ie_blk_burst_num)
             ,.ie_ecc_uniq_block_num     (ie_ecc_uniq_block_num)
             ,.ih_te_rd_eccap            (ih_te_rd_eccap)
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
`endif
`endif
             ,.ts_bsm_num4pre            (gs_te_bsm_num4pre [BSM_BITS-1:0]) 
             ,.ts_bsm_num4act            (gs_te_bsm_num4act [BSM_BITS-1:0]) 
             ,.te_rdwr_autopre           (te_rdwr_autopre) 
             ,.ts_op_is_precharge        (gs_te_op_is_precharge) 
             ,.ts_op_is_activate         (gs_te_op_is_activate) 
             ,.be_te_page_hit            (be_te_page_hit)            
             ,.ts_act_page               (ts_act_page) 
             ,.ih_te_rd_length           (ih_te_rd_length)
             ,.ih_te_critical_dword      (ih_te_critical_dword)
             ,.ih_te_rd_other_fields     (ih_te_rd_other_fields[OTHER_RD_ENTRY_BITS-1:0]) 
             ,.ih_te_rd_entry_num        (ih_te_rd_entry_num [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_rd_entry_rankbank      (te_rd_entry_rankbank)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs but output must always exist
             ,.te_rd_entry_bsm_num       (te_rd_entry_bsm_num) 
//spyglass enable_block W528
             ,.te_lo_rd_prefer           (te_lo_rd_prefer [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_hi_rd_prefer           (te_hi_rd_prefer [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_yy_wr_combine          (te_yy_wr_combine) 
             ,.te_ih_rd_retry            (te_ih_rd_retry_int)   
             ,.ih_te_hi_pri              (ih_te_rd_hi_pri) 
             ,.ih_te_rd_latency          (ih_te_rd_latency) 
             ,.te_gs_any_vpr_timed_out   (te_gs_any_vpr_timed_out) 
             ,.te_gs_any_vpr_timed_out_w (te_gs_any_vpr_timed_out_w) 
             ,.te_vpr_valid              (te_vpr_valid) 
             ,.te_vpr_valid_d            (te_vpr_valid_d) 
             ,.te_vpr_page_hit           (te_vpr_page_hit)
             ,.upd_to_vpr_due_ie         (upd_to_vpr_due_ie_unused)
             ,.te_ts_hi_bsm_hint         (te_os_hi_bsm_hint [BSM_BITS-1:0]) 
             ,.te_ts_lo_bsm_hint         (te_os_lo_bsm_hint [BSM_BITS-1:0]) 
             ,.te_entry_pri              (te_rd_entry_pri [RD_CAM_ENTRIES -1:0]) 
             ,.te_entry_hpr              (te_rd_entry_hpr [RD_CAM_ENTRIES -1:0]) 
             ,.te_rd_flush               (te_rd_flush) 
             ,.te_rd_flush_due_rd        (te_rd_flush_due_rd) 
             ,.te_rd_flush_due_wr        (te_rd_flush_due_wr) 
             ,.te_rd_flush_started       (te_rd_flush_started) 
             ,.te_rd_col_entry           (te_rd_col_entry)
             ,.ddrc_co_perf_war_hazard   (ddrc_co_perf_war_hazard) 
             ,.ddrc_co_perf_ie_blk_hazard_rd (ddrc_co_perf_ie_blk_hazard_rd) 
             ,.ddrc_co_perf_vlimit_reached_rd (ddrc_co_perf_vlimit_reached_rd)
             ,.be_op_is_activate_bypass  (be_op_is_activate_bypass) 

             ,.te_ts_act_bsm_hint        (te_os_lo_act_bsm_hint [BSM_BITS-1:0]) 
             ,.ts_bsm_num4rdwr           (gs_te_bsm_num4rdwr [BSM_BITS-1:0]) 
             ,.ts_op_is_rd               (gs_te_op_is_rd) 
             ,.te_rd_page_table          (te_rd_page_table) 
             ,.te_rd_cmd_autopre_table   (te_rd_cmd_autopre_table) 
             ,.te_rd_cmd_length_table    (te_rd_cmd_length_table)
             ,.te_rd_critical_word_table (te_rd_critical_word_table)
             ,.te_rd_ie_tag_table        (te_rd_ie_tag_table)
             ,.te_rd_entry               (os_te_rdwr_entry [RD_CAM_ADDR_BITS -1:0]) 
             ,.te_pi_rd_addr_ecc_row     (te_pi_rd_addr_ecc_row) 
             ,.te_pi_rd_addr_blk         (te_pi_rd_addr_blk)
             ,.te_pi_rd_other_fields_rd  (te_pi_rd_other_fields_rd) 
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
             ,.te_pi_rd_length_int       (te_pi_rd_length_int)
             ,.te_pi_rd_word_int         (te_pi_rd_word_int) 
`endif
`endif 
//              ,.te_pi_rd_autopre          (te_pi_rd_autopre ) 
// `ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
             ,.te_os_rd_pageclose_autopre(te_os_rd_pageclose_autopre)
// `endif
             ,.te_bank_hit               (te_rd_bank_hit [RD_CAM_ENTRIES -1:0]) 
             ,.te_bank_hit_pre           (te_rd_bank_hit_pre [RD_CAM_ENTRIES -1:0]) 
             ,.te_page_hit               (te_rd_page_hit [RD_CAM_ENTRIES -1:0]) 
             ,.te_entry_valid            (te_rd_entry_valid [RD_CAM_ENTRIES -1:0]) 
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs and in te_assertions module
             ,.te_entry_loaded           (te_rd_entry_loaded [RD_CAM_ENTRIES -1:0]) 
//spyglass enable_block W528
//              ,.ts_rdwr_cmd_autopre       (ts_rdwr_cmd_autopre)           
             ,.te_pi_ie_bt               (te_pi_ie_bt) 
             ,.te_pi_ie_rd_type          (te_pi_ie_rd_type)
             ,.i_rd_ecc_status           (i_rd_ecc_status)
             ,.te_entry_critical_per_bsm (te_rd_entry_critical_per_bsm)
             ,.te_entry_critical_early   (te_rd_entry_critical_early)
             ,.reg_ddrc_page_hit_limit_rd(reg_ddrc_page_hit_limit_rd)
             ,.reg_ddrc_visible_window_limit_rd (reg_ddrc_visible_window_limit_rd)
             ,.te_rd_vlimit_decr         (te_rd_vlimit_decr)
//             ,.te_rd_vlimit_reached      ()
`ifdef SNPS_ASSERT_ON
             ,.i_te_pi_ie_bt             (i_te_pi_ie_bt) 
             ,.i_te_pi_ie_rd_type        (i_te_pi_ie_rd_type)
             ,.i_te_pi_ie_blk_burst_num  (i_te_pi_ie_blk_burst_num)
             ,.i_ie_rd_blk_addr_collision(i_ie_rd_blk_addr_collision) 
             ,.i_te_pi_eccap             (i_te_pi_eccap)
  `ifndef SYNTHESIS
     // for assertions
             ,.te_ih_retry              (te_ih_retry) 
             ,.ih_te_wr_valid           (ih_te_wr_valid) 
             ,.gs_te_op_is_wr           (i_gs_te_op_is_wr) 
             ,.te_mr_ie_wr_type         (te_mr_ie_wr_type)
             ,.te_mr_ie_bt              (te_mr_ie_bt)
  `endif
`endif
             ,.ts_te_sel_act_wr           (ts_te_sel_act_wr)
             ,.ih_gs_rdhigh_empty         (ih_gs_rdhigh_empty)
             ,.ih_gs_rdlow_empty          (ih_gs_rdlow_empty)
             ,.gs_te_pri_level            (gs_te_pri_level) 
             ,.te_rd_rankbank_prefer      (te_rd_rankbank_prefer[RANKBANK_BITS-1:0])
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
             ,.reg_ddrc_opt_vprw_sch      (reg_ddrc_opt_vprw_sch)
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
            );




assign te_rd_flush_started_replace = te_rd_flush_started;
assign te_wr_flush_started_replace = te_wr_flush_started;
assign te_rd_flush_started_replace_pre = te_rd_flush_started;
assign te_wr_flush_started_replace_pre = te_wr_flush_started;





  te_rd_replace
   #( .RD_CAM_ADDR_BITS    (RD_CAM_ADDR_BITS), 
                   .RD_CAM_ENTRIES      (RD_CAM_ENTRIES),
                   .WORD_BITS           (WORD_BITS),
                   .CMD_LEN_BITS        (CMD_LEN_BITS),
                   .AUTOPRE_BITS        (AUTOPRE_BITS),
                   .IE_TAG_BITS         (IE_TAG_BITS)
                 )
          RDreplace (
              .co_te_clk                 (co_te_clk) 
             ,.core_ddrc_rstn            (core_ddrc_rstn) 
             ,.ih_te_lo_rd_prefer        (i_ih_te_lo_rd_prefer) 
             ,.te_rd_page_table          (te_rd_page_table) 
             ,.te_rd_cmd_autopre_table   (te_rd_cmd_autopre_table)  
             ,.te_rd_cmd_length_table    (te_rd_cmd_length_table)
             ,.te_rd_critical_word_table (te_rd_critical_word_table)
             ,.te_rd_ie_tag_table        (te_rd_ie_tag_table)
             ,.te_rd_bank_hit           (te_rd_bank_hit_filtred[RD_CAM_ENTRIES-1:0]) 
             ,.ddrc_cg_en               (ddrc_cg_en)
             ,.te_lo_rd_prefer          (te_lo_rd_prefer [RD_CAM_ADDR_BITS-1:0]) 
             ,.ih_te_hi_rd_prefer       (i_ih_te_hi_rd_prefer) 
             ,.te_rd_entry_pri          (te_rd_entry_pri [RD_CAM_ENTRIES -1:0]) 
             ,.te_rd_page_hit           (te_rd_page_hit_filtred [RD_CAM_ENTRIES-1:0]) 
             ,.te_rd_flush_started      (te_rd_flush_started_replace) 
             ,.te_rd_col_entry          (te_rd_col_entry) 
             ,.gs_te_pri_level          (gs_te_pri_level) 
             ,.te_hi_rd_prefer          (te_hi_rd_prefer [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_any_vpr_timed_out     (te_gs_any_vpr_timed_out) 
             ,.te_vpr_valid             (te_vpr_valid) 
             ,.te_vpr_valid_for_flush   (te_vpr_valid) // same as te_vpr_valid for this instance
             ,.te_vpr_valid_filtred     (te_vpr_valid_filtred) 
             ,.te_vpr_page_hit          (te_vpr_page_hit_filtred) 
             ,.te_sel_vpr_entry         (te_sel_vpr_entry) 
             ,.te_sel_vpr_page          (te_sel_vpr_page) 
             ,.te_sel_vpr_cmd_autopre   (te_sel_vpr_cmd_autopre)           
             ,.te_sel_vpr_length        (te_sel_vpr_length)
             ,.te_sel_vpr_critical_word (te_sel_vpr_critical_word)
             ,.te_sel_vpr_valid         (te_sel_vpr_valid) 
             ,.te_sel_vpr_ie_tag        (te_sel_vpr_ie_tag)
             ,.te_sel_rd_ie_tag         (te_sel_rd_ie_tag)
             ,.hmx_mask                 (hmx_rd_mask)
             ,.hmx_oldest_oh            (hmx_rd_oldest_oh)
             ,.reg_ddrc_opt_hit_gt_hpr  (reg_ddrc_opt_hit_gt_hpr)
             ,.te_vpr_prefer            (te_vpr_prefer)
             ,.hmx_mask_vpr             (hmx_rd_vpr_mask)
             ,.hmx_oldest_oh_vpr        (hmx_rd_vpr_oldest_oh)
             ,.te_sel_rd_entry          (te_sel_rd_entry [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_sel_rd_page           (te_sel_rd_page)        
             ,.te_sel_rd_valid          (te_sel_rd_valid)
             ,.te_sel_rd_length         (te_sel_rd_length)
             ,.te_sel_rd_critical_word  (te_sel_rd_critical_word)
             ,.te_sel_rd_cmd_autopre    (te_sel_rd_cmd_autopre)
             );

  te_rd_replace
   #( .RD_CAM_ADDR_BITS    (RD_CAM_ADDR_BITS), 
                   .RD_CAM_ENTRIES      (RD_CAM_ENTRIES),
                   .WORD_BITS           (WORD_BITS),
                   .CMD_LEN_BITS        (CMD_LEN_BITS),
                   .AUTOPRE_BITS        (AUTOPRE_BITS),
                   .IE_TAG_BITS         (IE_TAG_BITS)
                 )
          RDreplace_pre (
              .co_te_clk                (co_te_clk) 
             ,.core_ddrc_rstn           (core_ddrc_rstn) 
             ,.ih_te_lo_rd_prefer       (i_ih_te_lo_rd_prefer) 
             ,.te_rd_page_table         (te_rd_page_table) 
             ,.te_rd_cmd_autopre_table  (te_rd_cmd_autopre_table)  
             ,.te_rd_cmd_length_table   (te_rd_cmd_length_table)
             ,.te_rd_critical_word_table (te_rd_critical_word_table)
             ,.te_rd_ie_tag_table       (te_rd_ie_tag_table)
             ,.te_rd_bank_hit           (te_rd_bank_hit_pre[RD_CAM_ENTRIES-1:0]) 
             ,.ddrc_cg_en               (1'b1) // PRE can be served out side of traffic
            ,.te_lo_rd_prefer          (te_lo_rd_prefer_pre_unused) 
             ,.ih_te_hi_rd_prefer       (i_ih_te_hi_rd_prefer) 
             ,.te_rd_entry_pri          (te_rd_entry_pri [RD_CAM_ENTRIES -1:0]) 
             ,.te_rd_page_hit           ({RD_CAM_ENTRIES{1'b0}}) 
             ,.te_rd_flush_started      (te_rd_flush_started_replace_pre) 
             ,.te_rd_col_entry          (te_rd_col_entry) 
             ,.gs_te_pri_level          (gs_te_pri_level) 
             ,.te_hi_rd_prefer          (te_hi_rd_prefer_pre_unused) 
             ,.te_any_vpr_timed_out     (te_gs_any_vpr_timed_out) 
             ,.te_vpr_valid             (te_vpr_valid)
             ,.te_vpr_valid_for_flush   (te_vpr_valid) // same as te_vpr_valid for this instance
             ,.te_vpr_valid_filtred     ({RD_CAM_ENTRIES{1'b0}})  // used only in VPR selenet
             ,.te_vpr_page_hit          ({RD_CAM_ENTRIES{1'b0}})
             ,.te_sel_vpr_entry         (te_sel_rd_entry_pre_unused) 
             ,.te_sel_vpr_page          (te_sel_rd_page_pre_unused) 
             ,.te_sel_vpr_cmd_autopre   (te_sel_rd_cmd_autopre_pre_unused)           
             ,.te_sel_vpr_length        (te_sel_vpr_cmd_length_pre_unused)
             ,.te_sel_vpr_critical_word (te_sel_vpr_critical_word_pre_unused)
             ,.te_sel_vpr_valid         (te_sel_vpr_valid_pre_unused) 
             ,.te_sel_vpr_ie_tag        (te_sel_rd_ie_tag_pre_unused)
             ,.te_sel_rd_ie_tag         (te_sel_rd_ie_tag_pre)
             ,.hmx_mask                 (hmx_rd_pre_mask)
             ,.hmx_oldest_oh            (hmx_rd_pre_oldest_oh)
             ,.reg_ddrc_opt_hit_gt_hpr  (reg_ddrc_opt_hit_gt_hpr)
             ,.te_vpr_prefer            ({RD_CAM_ADDR_BITS{1'b0}})
             ,.hmx_mask_vpr             (hmx_rd_pre_mask_vpr_unused)
             ,.hmx_oldest_oh_vpr        ({RD_CAM_ENTRIES{1'b0}})
             ,.te_sel_rd_entry          (te_sel_rd_entry_pre [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_sel_rd_page           (te_sel_rd_page_pre)        
             ,.te_sel_rd_length         (te_sel_rd_cmd_length_pre)
             ,.te_sel_rd_critical_word  (te_sel_rd_critical_word_pre)
             ,.te_sel_rd_valid          (te_sel_rd_valid_pre_unused) 
             ,.te_sel_rd_cmd_autopre    (te_sel_rd_cmd_autopre_pre)
             );

  te_rd_nxt
   
  #(.AUTOPRE_BITS        (AUTOPRE_BITS),
    .WORD_BITS           (WORD_BITS),
    .CMD_LEN_BITS        (CMD_LEN_BITS),
    .NUM_CAM_ENTRIES     (RD_CAM_ENTRIES),
    .IE_TAG_BITS         (IE_TAG_BITS) 
   )
  RDnxt (
              .core_ddrc_rstn             (core_ddrc_rstn) 
             ,.co_te_clk                  (co_te_clk) 
             ,.ih_te_rd_valid             (ih_te_rd_valid) 
             ,.te_sel_entry               (te_sel_rd_entry [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_sel_rd_page             (te_sel_rd_page) 
             ,.te_sel_rd_cmd_autopre      (te_sel_rd_cmd_autopre)
             ,.te_sel_rd_length           (te_sel_rd_length)                       
             ,.te_sel_rd_critical_word    (te_sel_rd_critical_word)                       
             ,.te_sel_valid               (te_sel_rd_valid) 
 
             ,.te_page_hit                (te_rd_page_hit [RD_CAM_ENTRIES -1:0]) 
             ,.te_entry_pri               (te_rd_entry_pri [RD_CAM_ENTRIES -1:0]) 
             ,.ih_te_hi_pri               (ih_te_rd_hi_pri)    // hooking up both prority bits to NTT
                                                              // It will be changed to the upper bit only inside NTT
                                                              // this is done to not touch the logic in NTT as the 
                                                              // original design uses 1-bit priority
                                                              // pri=00(LPR) 01(VPR) will be marked as pri=0(LPR) in NTT
                                                              // pri=10(HPR) will be marked as pri=1(HPR) in NTT
                                                              // VPR to HPR conversion can happen only through the CAM
                                                              // Timed-out VPR entries that come in from IH into NTT are
                                                              // blocked in NTT
             ,.ih_te_rd_latency           (ih_te_rd_latency) 
             ,.te_sel_vpr_entry           (te_sel_vpr_entry) 
             ,.te_sel_vpr_page            (te_sel_vpr_page) 
             ,.te_sel_vpr_cmd_autopre     (te_sel_vpr_cmd_autopre)          
             ,.te_sel_vpr_length          (te_sel_vpr_length)                       
             ,.te_sel_vpr_critical_word   (te_sel_vpr_critical_word)                       
             ,.te_sel_vpr_valid           (te_sel_vpr_valid) 
             ,.te_vpr_page_hit            (te_vpr_page_hit) 
             ,.te_vpr_valid               (te_vpr_valid)        
             ,.te_vpr_entry               (te_ts_vpr_valid [TOTAL_BSMS-1:0]) 
             ,.te_sel_vpr_ie_tag          (te_sel_vpr_ie_tag)
             ,.te_rd_entry_bsm_num        (te_rd_entry_bsm_num)       
             ,.te_ih_rd_retry             (te_ih_rd_retry_int)   
             ,.ts_pri_level               (gs_te_pri_level) 
             ,.te_ts_hi_xact              (te_bs_rd_hi [TOTAL_BSMS-1:0]) 
             ,.te_ts_valid                (te_bs_rd_valid [TOTAL_BSMS-1:0]) 
             ,.te_gs_hi_xact_page_hit_vld (te_gs_hi_rd_page_hit_vld) 
             ,.rd_nxt_entry_in_ntt        (rd_nxt_entry_in_ntt)   
             ,.be_te_page_hit             (be_te_page_hit)                     
             ,.ts_act_page                (ts_act_page)
             ,.ih_te_bsm_num              ({
                                         ih_te_rd_rank_num, 
                                         ih_te_rd_bg_bank_num}) 
             ,.ih_te_bsm_alloc            (1'b1)
             ,.ih_te_entry_num            (ih_te_rd_entry_num [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_bs_rd_bank_page_hit     (te_bs_rd_bank_page_hit) 
             ,.te_rd_page_table           (te_rd_page_table) 
             ,.te_rd_cmd_autopre_table    (te_rd_cmd_autopre_table)                 
             ,.te_rd_cmd_length_table     (te_rd_cmd_length_table)
             ,.te_rd_critical_word_table  (te_rd_critical_word_table)
             ,.te_rd_ie_tag_table         (te_rd_ie_tag_table)
             ,.ts_bsm_num4pre             (gs_te_bsm_num4pre [BSM_BITS-1:0]) 
             ,.ts_bsm_num4act             (gs_te_bsm_num4act [BSM_BITS-1:0]) 
             ,.ts_bsm_num4rdwr            (gs_te_bsm_num4rdwr [BSM_BITS-1:0]) 
             ,.te_rdwr_autopre            (te_rdwr_autopre) 
             ,.ts_op_is_rd                (gs_te_op_is_rd) 
             ,.ts_op_is_precharge         (gs_te_op_is_precharge) 
             ,.ts_op_is_activate          (gs_te_op_is_activate) 
             ,.ts_wr_mode                 (gs_te_wr_mode) 
             ,.te_ts_page_hit             (te_bs_rd_page_hit [TOTAL_BSMS-1:0]) 
             ,.te_dh_valid                (te_dh_rd_bsm_valid) 
             ,.te_dh_page_hit             (te_dh_rd_bsm_page_hit) 
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((TOTAL_BSMS * RD_CAM_ADDR_BITS) - 1)' found in module 'teengine'
//SJ: This coding style is acceptable and there is no plan to change it.
             ,.te_os_rd_entry_table       (te_os_rd_entry_table[TOTAL_BSMS*RD_CAM_ADDR_BITS-1:0]) 
             ,.te_pghit_vld               (rd_pghit_vld_unused) 
             ,.rd_nxt_page_table          (rd_nxt_page_table[TOTAL_BSMS*PAGE_BITS-1:0]) 
             ,.rd_nxt_cmd_autopre_table   (rd_nxt_cmd_autopre_table[TOTAL_BSMS*AUTOPRE_BITS-1:0])           
             ,.rd_nxt_length_table        (rd_nxt_length_table[TOTAL_BSMS*CMD_LEN_BITS-1:0])
             ,.rd_nxt_word_table          (rd_nxt_word_table[TOTAL_BSMS*WORD_BITS-1:0])
//spyglass enable_block SelfDeterminedExpr-ML
             ,.te_os_rd_ie_tag_table      (te_os_rd_ie_tag_table)
             ,.i_rd_ecc_status            (i_rd_ecc_status)
             ,.te_sel_rd_ie_tag           (te_sel_rd_ie_tag)
             ,.te_sel_entry_pre           (te_sel_rd_entry_pre [RD_CAM_ADDR_BITS-1:0]) 
             ,.te_sel_rd_page_pre         (te_sel_rd_page_pre)        
             ,.te_sel_rd_cmd_autopre_pre  (te_sel_rd_cmd_autopre_pre)
             ,.te_sel_rd_cmd_length_pre    (te_sel_rd_cmd_length_pre)
             ,.te_sel_rd_critical_word_pre (te_sel_rd_critical_word_pre)
             ,.te_sel_rd_ie_tag_pre       (te_sel_rd_ie_tag_pre)
             ,.te_entry_critical_per_bsm  (te_rd_entry_critical_per_bsm)
             ,.reg_ddrc_opt_hit_gt_hpr    (reg_ddrc_opt_hit_gt_hpr)
             ,.reg_ddrc_dis_opt_ntt_by_act (reg_ddrc_dis_opt_ntt_by_act)
             ,.reg_ddrc_dis_opt_ntt_by_pre (reg_ddrc_dis_opt_ntt_by_pre)
             ,.ts_te_sel_act_wr           (ts_te_sel_act_wr)
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
             ,.ts_te_act_page            (ts_act_page) 
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
            );


  te_wr_cam
   #(
    .WR_CAM_ADDR_BITS     (WR_CAM_ADDR_BITS), 
    .WR_CAM_ADDR_BITS_IE  (WR_CAM_ADDR_BITS_IE), 
    .WR_CAM_ENTRIES       (WR_CAM_ENTRIES),
    .WR_ECC_CAM_ENTRIES   (WR_ECC_CAM_ENTRIES),
    .WR_ECC_CAM_ADDR_BITS (WR_ECC_CAM_ADDR_BITS),
    .WR_CAM_ENTRIES_IE    (WR_CAM_ENTRIES_IE),
    .RANK_BITS            (LRANK_BITS), 
    .BG_BITS              (BG_BITS), 
    .BANK_BITS            (BANK_BITS), 
    .BG_BANK_BITS         (BG_BANK_BITS), 
    .PAGE_BITS            (PAGE_BITS), 
    .BLK_BITS             (BLK_BITS), 
    .BSM_BITS             (BSM_BITS), 
    .MWR_BITS             (MWR_BITS), 
    .PARTIAL_WR_BITS      (PARTIAL_WR_BITS), 
    .PARTIAL_WR_BITS_LOG2 (PARTIAL_WR_BITS_LOG2), 
    .PW_WORD_CNT_WD_MAX   (PW_WORD_CNT_WD_MAX), 
    .BT_BITS              (BT_BITS),
    .NO_OF_BT             (NO_OF_BT),
    .IE_WR_TYPE_BITS      (IE_WR_TYPE_BITS),
    .IE_RD_TYPE_BITS      (IE_RD_TYPE_BITS),
    .IE_BURST_NUM_BITS    (IE_BURST_NUM_BITS),
    .IE_TAG_BITS          (IE_TAG_BITS),
    .IE_UNIQ_BLK_BITS     (IE_UNIQ_BLK_BITS),
    .IE_UNIQ_BLK_LSB      (IE_UNIQ_BLK_LSB),
    .ECCAP_BITS           (ECCAP_BITS),
    .RETRY_WR_BITS        (RETRY_WR_BITS),
    .ENTRY_RETRY_TIMES_WIDTH(0),
    .WORD_BITS              (0),
    .DDR4_COL3_BITS       (DDR4_COL3_BITS),
    .LP_COL4_BITS         (LP_COL4_BITS),
    .ENTRY_AUTOPRE_BITS   (AUTOPRE_BITS), 
    .HI_PRI_BITS          (HI_PRI_BITS),
    .WR_LATENCY_BITS      (WR_LATENCY_BITS),
    .PW_BC_SEL_BITS       (PW_BC_SEL_BITS),
    .WP_BITS              (WP_BITS),
    .OTHER_WR_ENTRY_BITS  (OTHER_WR_ENTRY_BITS))      // unused; can't go lower than 1
  WRcam (
             .core_ddrc_rstn               (core_ddrc_rstn) 
             ,.dh_te_pageclose              (dh_te_pageclose) 
             ,.dh_te_pageclose_timer        (dh_te_pageclose_timer) 
             ,.co_te_clk                    (co_te_clk) 
             ,.ddrc_cg_en                   (ddrc_cg_en)
             ,.ih_te_rd_valid               (ih_te_rd_valid) 
             ,.ih_te_wr_valid               (ih_te_wr_valid) 
             ,.ih_te_wr_rank_num            (ih_te_wr_rank_num) 
             ,.ih_te_rd_rank_num            (ih_te_rd_rank_num) 
             ,.ih_te_wr_bg_bank_num         (ih_te_wr_bg_bank_num) 
             ,.ih_te_wr_page_num            (ih_te_wr_page_num) 
             ,.ih_te_wr_block_num           (ih_te_wr_block_num) 
             ,.ih_te_wr_autopre             (ih_te_wr_autopre) 
             ,.ih_te_rd_bg_bank_num         (ih_te_rd_bg_bank_num) 
             ,.ih_te_rd_page_num            (ih_te_rd_page_num) 
             ,.ih_te_wr_entry_num           (ih_te_wr_entry_num [WR_CAM_ADDR_BITS_IE-1:0]) 
             ,.ih_te_wr_other_fields        (ih_te_wr_other_fields[OTHER_WR_ENTRY_BITS-1:0]) 
             ,.ih_te_ie_bt                  (ih_te_ie_bt)
             ,.ih_te_ie_wr_type             (ih_te_ie_wr_type_int)
             ,.ih_te_ie_rd_type             (ih_te_ie_rd_type_int)
             ,.ih_te_ie_blk_burst_num       (ih_te_ie_blk_burst_num)
             ,.ie_ecc_uniq_block_num        (ie_ecc_uniq_block_num)
             ,.te_mr_ie_bt                  (te_mr_ie_bt)
             ,.te_mr_ie_wr_type             (te_mr_ie_wr_type)
             ,.ih_te_ie_btt_vct             (ih_te_ie_btt_vct)
             ,.ih_te_ie_re_vct              (ih_te_ie_re_vct)
             ,.te_wr_entry_ie_btt           (te_wr_entry_ie_btt)
             ,.te_wr_entry_ie_re            (te_wr_entry_ie_re)
             ,.te_wrecc_prefer              (te_wrecc_prefer)
             ,.ih_te_wr_eccap               (ih_te_wr_eccap)
             ,.te_wr_prefer                 (te_wr_prefer) 
             ,.ts_bsm_num4pre               (gs_te_bsm_num4pre [BSM_BITS-1:0]) 
             ,.ts_bsm_num4act               (gs_te_bsm_num4act [BSM_BITS-1:0]) 
             ,.te_rdwr_autopre              (te_rdwr_autopre) 
             ,.ts_op_is_precharge           (gs_te_op_is_precharge) 
             ,.ts_op_is_activate            (gs_te_op_is_activate) 
             ,.be_te_page_hit               (be_wr_page_hit)            
             ,.te_wr_entry_rankbank         (te_wr_entry_rankbank)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs but output must always exist
             ,.te_wr_entry_bsm_num          (te_wr_entry_bsm_num) 
//spyglass enable_block W528
             ,.gs_te_wr_mode                (gs_te_wr_mode)
             ,.reg_ddrc_dis_opt_ntt_by_act  (reg_ddrc_dis_opt_ntt_by_act)
             ,.te_bypass_rank_bg_bank_num   (te_bypass_rank_bg_bank_num)
             ,.ih_te_link_to_write          (ih_te_rd_link_to_write)  // ???_PT
             ,.ih_te_wr_latency             (ih_te_wr_latency) 
             ,.ih_te_hi_pri                 (ih_te_wr_hi_pri) 
             ,.te_gs_any_vpw_timed_out      (te_gs_any_vpw_timed_out) 
             ,.te_gs_any_vpw_timed_out_w    (te_gs_any_vpw_timed_out_w) 
             ,.te_vpw_valid                 (te_vpw_valid) 
             ,.te_vpw_valid_d               (te_vpw_valid_d) 
             ,.te_vpw_page_hit              (te_vpw_page_hit) 
             ,.te_vpw_latency               (te_vpw_latency) 
             ,.te_vpw_pri                   (te_vpw_pri) 
             ,.te_bank_hit_wrecc_in_vpw     (te_bank_hit_wrecc_in_vpw)      //bank-hit in entries of vpw with te_sel_wrecc_btt_bank
             ,.te_sel_wrecc_btt_bank        (te_sel_wrecc_btt_bank   )      //bank# from wrecc_btt replace logic
             ,.te_bank_hit_vpw_in_wrecc     (te_bank_hit_vpw_in_wrecc)      //bank-hit in entries of wrecc_btt with te_sel_vpw_bank
             ,.te_sel_vpw_bank              (te_sel_vpw_bank         )      //bank# from vpw replace logic
             ,.te_bank_hit_inc_vpw_in_wrecc (te_bank_hit_inc_vpw_in_wrecc) //bank-hit in entries of wrecc_btt with incoming vpw.
             ,.incoming_vpw_bank            (incoming_vpw_bank) //bank# of incoming vpw
             ,.te_wr_col_entries            (te_wr_col_entries)
             ,.te_wr_ie_blk_collision       (te_wr_ie_blk_collision)
             ,.dh_te_dis_wc                 (dh_te_dis_wc) 
             ,.te_wr_pghit_vld              (te_wr_pghit_vld) 
             ,.te_ih_wr_retry               (te_ih_wr_retry_int) 
             ,.i_enc_entry                  (te_wu_entry_num [WR_CAM_ADDR_BITS-1:0]) 
             ,.wu_te_entry_num              (wu_te_entry_num [WR_CAM_ADDR_BITS-1:0]) 
             ,.te_yy_wr_combine             (te_yy_wr_combine) 
             ,.te_yy_wr_combine_noecc       (te_yy_wr_combine_noecc)
             ,.te_yy_wr_combine_wrecc       (te_yy_wr_combine_wrecc)
             ,.te_wr_nxt_wr_combine         (te_wr_nxt_wr_combine) 
             ,.te_flush_due_rd              (te_wr_flush_due_rd) 
             ,.te_flush_due_wr              (te_wr_flush_due_wr) 
             ,.te_flush                     (te_wr_flush) 
             ,.te_flush_started             (te_wr_flush_started) 
             ,.te_wr_col_entry              (te_wr_col_entry) 
             ,.te_wr_col_bank               (te_wr_col_bank)
             ,.ddrc_co_perf_raw_hazard      (ddrc_co_perf_raw_hazard) 
             ,.ddrc_co_perf_waw_hazard      (ddrc_co_perf_waw_hazard) 
             ,.ddrc_co_perf_ie_blk_hazard_wr(ddrc_co_perf_ie_blk_hazard_wr) 
             ,.ddrc_co_perf_vlimit_reached_wr (ddrc_co_perf_vlimit_reached_wr)
             ,.be_op_is_activate_bypass     (be_op_is_activate_bypass) 
             ,.ih_te_mwr                    (ih_te_mwr)
             ,.ih_te_wr_word_valid          (ih_te_wr_word_valid)
             ,.ih_te_wr_ram_raddr_lsb_first (ih_te_wr_ram_raddr_lsb_first)
             ,.ih_te_wr_pw_num_beats_m1     (ih_te_wr_pw_num_beats_m1)
             ,.ih_te_wr_pw_num_cols_m1      (ih_te_wr_pw_num_cols_m1)
             ,.wu_te_enable_wr              (wu_te_enable_wr [1:0]) 
             ,.wu_te_mwr                    (wu_te_mwr) 
             ,.wu_te_wr_word_valid          (wu_te_wr_word_valid) 
             ,.wu_te_ram_raddr_lsb_first    (wu_te_ram_raddr_lsb_first) 
             ,.wu_te_pw_num_beats_m1        (wu_te_pw_num_beats_m1) 
             ,.wu_te_pw_num_cols_m1         (wu_te_pw_num_cols_m1) 
             ,.i_load_ntt                   (i_load_ntt) 
             ,.i_load_ntt_ie                (i_load_ntt_ie)
             ,.i_unload_ntt_ie              (i_unload_ntt_ie)
             ,.r_unload_ntt_ie_bt_reg       (i_unload_ntt_ie_bt_reg)
             ,.r_unload_ntt_ie_bt_reg_vld   (i_unload_ntt_ie_bt_reg_vld)
             ,.r_unload_ntt_ie_bt_reg2      (i_unload_ntt_ie_bt_reg2)
             ,.r_unload_ntt_ie_bt_reg2_vld  (i_unload_ntt_ie_bt_reg2_vld)
             ,.ts_te_force_btt              (ts_te_force_btt)
             ,.i_load_cam_ie                (i_load_cam_ie)
             ,.i_unload_cam_ie              (i_unload_cam_ie)
    `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
             ,.te_wrecc_entry_avail         (te_wrecc_entry_avail)
             ,.te_wrecc_entry_loaded        (te_wrecc_entry_loaded)
    `endif // SNPS_ASSERT_ON
    `endif // SYNTHESIS
             ,.ts_op_is_wr                  (gs_te_op_is_wr) 
             ,.ts_bsm_num4rdwr              (gs_te_bsm_num4rdwr [BSM_BITS-1:0]) 
             ,.te_be_bsm_num                (te_be_bsm_num [BSM_BITS-1:0]) 
             ,.te_be_page_num               (te_be_page_num [PAGE_BITS-1:0]) 
             ,.ts_wr_possible               (gs_te_wr_possible) 
             ,.te_gs_block_wr               (te_gs_block_wr) 
             ,.te_ts_wr_bsm_hint            (te_os_wr_bsm_hint [BSM_BITS-1:0]) 
             ,.te_ts_wrecc_bsm_hint         (te_os_wrecc_bsm_hint [BSM_BITS-1:0])
             ,.te_wr_cam_page_hit           (te_wr_cam_page_hit)
             ,.te_ts_wr_act_bsm_hint        (te_os_wr_act_bsm_hint [BSM_BITS-1:0]) 
             ,.te_wr_page_table             (te_wr_page_table) 
             ,.te_wr_cmd_autopre_table      (te_wr_cmd_autopre_table)  
             ,.te_wr_entry                  (os_te_rdwr_entry [WR_CAM_ADDR_BITS_IE -1:0]) 
             ,.te_mr_wr_ram_addr            (te_mr_wr_ram_addr [WR_CAM_ADDR_BITS_IE-1:0]) 
             ,.te_pi_wr_addr_blk            (te_pi_wr_addr_blk) 
             ,.te_pi_wr_other_fields_wr     (te_pi_wr_other_fields_wr)
//             ,.te_wr_autopre                (te_wr_autopre) 
             ,.te_mwr_table                 (te_mwr_table) 
             ,.te_wr_ie_tag_table           (te_wr_ie_tag_table)
             ,.te_pw_num_cols_m1_table      (te_pw_num_cols_m1_table) 
             ,.te_pi_wr_word_valid          (te_pi_wr_word_valid)   
             ,.te_wr_mr_ram_raddr_lsb_first_table (te_wr_mr_ram_raddr_lsb_first_table)
             ,.te_wr_mr_pw_num_beats_m1_table     (te_wr_mr_pw_num_beats_m1_table)
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
             ,.te_mr_ram_raddr_lsb_first_int  (te_mr_ram_raddr_lsb_first_int) 
             ,.te_mr_pw_num_beats_m1_int      (te_mr_pw_num_beats_m1_int) 
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON
             ,.te_bank_hit                  (te_wr_bank_hit [WR_CAM_ENTRIES_IE-1:0]) 
             ,.te_bank_hit_pre              (te_wr_bank_hit_pre [WR_CAM_ENTRIES_IE-1:0]) 
             ,.te_page_hit                  (te_wr_page_hit [WR_CAM_ENTRIES_IE-1:0]) 
             ,.te_entry_valid               (te_wr_entry_valid  [WR_CAM_ENTRIES_IE-1:0]) 
             ,.ts_act_page                  (ts_act_page) 
//              ,.ts_rdwr_cmd_autopre          (ts_rdwr_cmd_autopre) 
             ,.wr_nxt_entry_in_ntt          (wr_nxt_entry_in_ntt)                   
             ,.te_entry_critical_early      (te_wr_entry_critical_early)
             ,.te_entry_critical_per_bsm    (te_wr_entry_critical_per_bsm)
             ,.te_entry_critical_currnt_bsm (te_wr_entry_critical_currnt_bsm)
             ,.reg_ddrc_page_hit_limit_wr   (reg_ddrc_page_hit_limit_wr)
             ,.reg_ddrc_visible_window_limit_wr (reg_ddrc_visible_window_limit_wr)
             ,.te_wr_vlimit_decr            (te_wr_vlimit_decr)
//             ,.te_wr_vlimit_reached         () 
             ,.te_entry_valid_clr_by_wc     (te_entry_valid_clr_by_wc)
             ,.te_page_hit_entries          (te_wr_page_hit_entries [WR_CAM_ENTRIES_IE-1:0]) 
             ,.te_wr_collision_vld_due_rd   (te_wr_collision_vld_due_rd)
             ,.te_wr_collision_vld_due_wr   (te_wr_collision_vld_due_wr)
             ,.ts_te_sel_act_wr             (ts_te_sel_act_wr)
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
             ,.i_entry_we_bw_loaded         (i_wr_entry_we_bw_loaded)
             ,.wu_ih_flow_cntrl_req         (wu_ih_flow_cntrl_req)
             ,.i_te_mr_ie_bt                (i_te_mr_ie_bt)
             ,.i_te_mr_ie_wr_type           (i_te_mr_ie_wr_type)
             ,.i_te_mr_ie_blk_burst_num     (i_te_mr_ie_blk_burst_num)
             ,.i_ie_wr_blk_addr_collision   (i_ie_wr_blk_addr_collision)
             ,.i_te_mr_eccap                (i_te_mr_eccap) 
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
             ,.te_wr_rankbank_prefer       (te_wr_rankbank_prefer[RANKBANK_BITS-1:0])
             ,.te_os_wr_pageclose_autopre  (te_os_wr_pageclose_autopre)

`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
            ,.reg_ddrc_opt_vprw_sch        (reg_ddrc_opt_vprw_sch    )
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
            );



  te_wr_replace
   #(
             .WR_CAM_ADDR_BITS          (WR_CAM_ADDR_BITS),
             .WR_ECC_CAM_ADDR_BITS      (WR_ECC_CAM_ADDR_BITS),
             .WR_CAM_ADDR_BITS_IE       (WR_CAM_ADDR_BITS_IE),
             .WR_CAM_ENTRIES            (WR_CAM_ENTRIES),
             .WR_CAM_ENTRIES_IE         (WR_CAM_ENTRIES_IE),
             .WR_ECC_CAM_ENTRIES        (WR_ECC_CAM_ENTRIES),
             .MWR_BITS                  (MWR_BITS), 
             .PW_WORD_CNT_WD_MAX        (PW_WORD_CNT_WD_MAX), 
             .PARTIAL_WR_BITS_LOG2      (PARTIAL_WR_BITS_LOG2),
             .AUTOPRE_BITS              (AUTOPRE_BITS),
             .IE_TAG_BITS               (IE_TAG_BITS)
              )
         WRreplace (
              .co_te_clk                 (co_te_clk) 
             ,.core_ddrc_rstn            (core_ddrc_rstn) 
             ,.reg_ddrc_dis_opt_wrecc_collision_flush (reg_ddrc_dis_opt_wrecc_collision_flush)
             ,.ih_te_wr_prefer           (i_ih_te_wr_prefer) 
             ,.te_wr_entry_valid         (te_wr_bank_hit_filtred[WR_CAM_ENTRIES_IE-1:0]) 
             ,.ddrc_cg_en               (ddrc_cg_en)
             ,.te_wr_page_hit            (te_wr_page_hit_filtred [WR_CAM_ENTRIES_IE-1:0]) 
             ,.te_wr_flush_started       (te_wr_flush_started_replace) 
             ,.te_wr_col_entry           (te_wr_col_entry) 
             ,.te_any_vpw_timed_out      (te_gs_any_vpw_timed_out) 
             ,.te_vpw_valid              (te_vpw_valid[WR_CAM_ENTRIES-1:0]) 
             ,.te_vpw_valid_for_flush    (te_vpw_valid[WR_CAM_ENTRIES-1:0])  // Same as te_vpw_valid for this instance 
             ,.te_vpw_valid_filtred      (te_vpw_valid_filtred[WR_CAM_ENTRIES-1:0]) 
             ,.te_vpw_page_hit           (te_vpw_page_hit_filtred[WR_CAM_ENTRIES_IE-1:0]) 
             ,.te_sel_vpw_entry          (te_sel_vpw_entry) 
             ,.te_sel_vpw_page           (te_sel_vpw_page) 
             ,.te_sel_vpw_cmd_autopre    (te_sel_vpw_cmd_autopre) 
             ,.te_sel_vpw_valid          (te_sel_vpw_valid) 
             ,.te_sel_vpw_mwr            (te_sel_vpw_mwr) 
             ,.te_sel_vpw_pw_num_cols_m1 (te_sel_vpw_pw_num_cols_m1) 
             ,.te_sel_vpw_mr_ram_raddr_lsb (te_sel_vpw_mr_ram_raddr_lsb)
             ,.te_sel_vpw_pw_num_beats_m1  (te_sel_vpw_pw_num_beats_m1)
             ,.te_sel_vpw_ie_tag         (te_sel_vpw_ie_tag)
             ,.te_sel_wrecc_btt_entry    (te_sel_wrecc_btt_entry) 
             ,.te_sel_wrecc_btt_page     (te_sel_wrecc_btt_page)
             ,.te_sel_wrecc_btt_cmd_autopre (te_sel_wrecc_btt_cmd_autopre)
             ,.te_sel_wrecc_btt_valid    (te_sel_wrecc_btt_valid)
             ,.te_sel_wrecc_btt_mwr      (te_sel_wrecc_btt_mwr)
             ,.te_sel_wrecc_btt_pw_num_cols_m1 (te_sel_wrecc_btt_pw_num_cols_m1)
             ,.te_sel_wrecc_btt_mr_ram_raddr_lsb (te_sel_wrecc_btt_mr_ram_raddr_lsb)
             ,.te_sel_wrecc_btt_pw_num_beats_m1  (te_sel_wrecc_btt_pw_num_beats_m1)
             ,.te_sel_wrecc_btt_ie_tag   (te_sel_wrecc_btt_ie_tag)
             ,.te_sel_wrecc_btt_ie_btt   (te_sel_wrecc_btt_ie_btt)
             ,.te_sel_wrecc_btt_ie_re    (te_sel_wrecc_btt_ie_re)

             ,.te_wrecc_btt_valid_filtred (te_wrecc_btt_valid_filtred [WR_CAM_ENTRIES +: WR_ECC_CAM_ENTRIES]) // except entries already in NTT
             ,.te_any_wrecc_btt_valid     (te_any_wrecc_btt_valid)
             ,.te_wr_col_entries         (te_wr_col_entries)
             ,.te_wr_page_table          (te_wr_page_table) 
             ,.te_wr_cmd_autopre_table   (te_wr_cmd_autopre_table) 
             ,.te_mwr_table              (te_mwr_table) 
             ,.te_pw_num_cols_m1_table   (te_pw_num_cols_m1_table) 
             ,.te_sel_pw_num_cols_m1     (te_sel_pw_num_cols_m1) 
             ,.te_wr_ie_tag_table        (te_wr_ie_tag_table)
             ,.te_sel_wr_ie_tag          (te_sel_wr_ie_tag)
             ,.te_wr_mr_ram_raddr_lsb_first_table (te_wr_mr_ram_raddr_lsb_first_table)
             ,.te_wr_mr_pw_num_beats_m1_table     (te_wr_mr_pw_num_beats_m1_table)
             ,.te_wr_prefer              (te_wr_prefer) 
             ,.te_sel_wr_entry           (te_sel_wr_entry) 
             ,.te_sel_wr_page            (te_sel_wr_page) 
             ,.te_sel_wr_cmd_autopre     (te_sel_wr_cmd_autopre) 
             ,.te_sel_mwr                (te_sel_mwr) 
             ,.te_sel_wr_mr_ram_raddr_lsb (te_sel_wr_mr_ram_raddr_lsb)
             ,.te_sel_wr_mr_pw_num_beats_m1  (te_sel_wr_mr_pw_num_beats_m1)
             ,.te_sel_wr_valid           (te_sel_wr_valid)
             ,.te_wr_entry_ie_btt        (te_wr_entry_ie_btt)
             ,.te_wr_entry_ie_re         (te_wr_entry_ie_re)
             ,.ih_te_wrecc_prefer        (i_ih_te_wrecc_prefer)
             ,.te_wrecc_prefer           (te_wrecc_prefer)
             ,.te_sel_ie_btt             (te_sel_ie_btt)
             ,.te_sel_ie_re              (te_sel_ie_re)
             ,.hmx_mask_wrecc            (hmx_wrecc_mask)
             ,.hmx_oldest_oh_wrecc       (hmx_wrecc_oldest_oh)
             ,.hmx_wrecc_btt_mask        (hmx_wrecc_btt_mask)
             ,.hmx_wrecc_btt_oldest_oh   (hmx_wrecc_btt_oldest_oh)
             ,.te_wrecc_btt_prefer       (te_wrecc_btt_prefer)
             ,.hmx_mask                  (hmx_wr_mask)
             ,.hmx_oldest_oh             (hmx_wr_oldest_oh)
             ,.te_vpw_prefer             (te_vpw_prefer)
             ,.hmx_mask_vpw              (hmx_wr_vpw_mask)
             ,.hmx_oldest_oh_vpw         (hmx_wr_vpw_oldest_oh)
             ,.te_entry_critical_currnt_bsm (te_wr_entry_critical_currnt_bsm)
             );

  te_wr_replace
   #(
             .WR_CAM_ADDR_BITS          (WR_CAM_ADDR_BITS),
             .WR_ECC_CAM_ADDR_BITS      (WR_ECC_CAM_ADDR_BITS),
             .WR_CAM_ADDR_BITS_IE       (WR_CAM_ADDR_BITS_IE),
             .WR_CAM_ENTRIES            (WR_CAM_ENTRIES),
             .WR_CAM_ENTRIES_IE         (WR_CAM_ENTRIES_IE),
             .WR_ECC_CAM_ENTRIES        (WR_ECC_CAM_ENTRIES),
             .MWR_BITS                  (MWR_BITS), 
             .PW_WORD_CNT_WD_MAX        (PW_WORD_CNT_WD_MAX), 
             .PARTIAL_WR_BITS_LOG2      (PARTIAL_WR_BITS_LOG2),
             .AUTOPRE_BITS              (AUTOPRE_BITS),
             .IE_TAG_BITS               (IE_TAG_BITS)
              )
         WRreplace_pre (
             .co_te_clk                  (co_te_clk) 
             ,.core_ddrc_rstn            (core_ddrc_rstn) 
             ,.ih_te_wr_prefer           (i_ih_te_wr_prefer) 
             ,.te_wr_entry_valid         (te_wr_bank_hit_pre[WR_CAM_ENTRIES_IE-1:0]) 
             ,.reg_ddrc_dis_opt_wrecc_collision_flush (reg_ddrc_dis_opt_wrecc_collision_flush)
             ,.ddrc_cg_en                (1'b1)
             ,.te_wr_page_hit            ({WR_CAM_ENTRIES_IE{1'b0}}) 
             ,.te_wr_flush_started       (te_wr_flush_started_replace_pre) 
             ,.te_wr_col_entry           (te_wr_col_entry) 
             ,.te_any_vpw_timed_out      (te_gs_any_vpw_timed_out) 
             ,.te_vpw_valid              (te_vpw_valid[WR_CAM_ENTRIES-1:0]) 
             ,.te_vpw_valid_for_flush    (te_vpw_valid[WR_CAM_ENTRIES-1:0])  // Same as te_vpw_valid for this instance 
             ,.te_vpw_valid_filtred      ({WR_CAM_ENTRIES{1'b0}}) // Only used in VPW selnet
             ,.te_vpw_page_hit           ({WR_CAM_ENTRIES_IE{1'b0}}) 
             ,.te_sel_vpw_entry          (te_sel_wr_entry_pre_unused) 
             ,.te_sel_vpw_page           (te_sel_wr_page_pre_unused) 
             ,.te_sel_vpw_cmd_autopre    (te_sel_wr_cmd_autopre_pre_unused) 
             ,.te_sel_vpw_valid          (te_sel_vpw_valid_pre_unused) 
             ,.te_sel_vpw_mwr            (te_sel_mwr_pre_unused) 
             ,.te_sel_vpw_pw_num_cols_m1 (te_sel_pw_num_cols_m1_pre_unused) 
             ,.te_sel_vpw_mr_ram_raddr_lsb  (te_sel_vpw_mr_ram_raddr_lsb_pre_unused)
             ,.te_sel_vpw_pw_num_beats_m1   (te_sel_vpw_mr_pw_num_beats_m1_pre_unused)
             ,.te_sel_vpw_ie_tag         (te_sel_wr_ie_tag_pre_unused)
             ,.te_sel_wrecc_btt_entry    (te_sel_wrecc_btt_entry_pre_unused) 
             ,.te_sel_wrecc_btt_page     (te_sel_wrecc_btt_page_pre_unused)
             ,.te_sel_wrecc_btt_cmd_autopre (te_sel_wrecc_btt_cmd_autopre_pre_unused)
             ,.te_sel_wrecc_btt_valid    (te_sel_wrecc_btt_valid_pre_unused)
             ,.te_sel_wrecc_btt_mwr      (te_sel_wrecc_btt_mwr_pre_unused)
             ,.te_sel_wrecc_btt_pw_num_cols_m1 (te_sel_wrecc_btt_pw_num_cols_m1_pre_unused)
             ,.te_sel_wrecc_btt_mr_ram_raddr_lsb (te_sel_wrecc_btt_mr_ram_raddr_lsb_pre_unused)
             ,.te_sel_wrecc_btt_pw_num_beats_m1  (te_sel_wrecc_btt_mr_pw_num_beats_m1_pre_unused)
             ,.te_sel_wrecc_btt_ie_tag   (te_sel_wrecc_btt_ie_tag_pre_unused)
             ,.te_sel_wrecc_btt_ie_btt   (te_sel_wrecc_btt_ie_btt_pre_unused)
             ,.te_sel_wrecc_btt_ie_re    (te_sel_wrecc_btt_ie_re_pre_unused)
             ,.te_wrecc_btt_valid_filtred ({WR_ECC_CAM_ENTRIES{1'b0}}) // except entries already in NTT
             ,.te_any_wrecc_btt_valid     (1'b0)
             ,.te_wr_col_entries         (te_wr_col_entries)
             ,.te_wr_page_table          (te_wr_page_table) 
             ,.te_wr_cmd_autopre_table   (te_wr_cmd_autopre_table) 
             ,.te_mwr_table              (te_mwr_table) 
             ,.te_pw_num_cols_m1_table   (te_pw_num_cols_m1_table) 
             ,.te_sel_pw_num_cols_m1     (te_sel_pw_num_cols_m1_pre) 
             ,.te_wr_ie_tag_table        (te_wr_ie_tag_table)
             ,.te_sel_wr_ie_tag          (te_sel_wr_ie_tag_pre)
             ,.te_wr_mr_ram_raddr_lsb_first_table (te_wr_mr_ram_raddr_lsb_first_table)
             ,.te_wr_mr_pw_num_beats_m1_table     (te_wr_mr_pw_num_beats_m1_table)
             ,.te_wr_prefer              (te_wr_prefer_pre_unused) 
             ,.te_sel_wr_entry           (te_sel_wr_entry_pre) 
             ,.te_sel_wr_page            (te_sel_wr_page_pre) 
             ,.te_sel_wr_cmd_autopre     (te_sel_wr_cmd_autopre_pre) 
             ,.te_sel_mwr                (te_sel_mwr_pre) 
             ,.te_sel_wr_mr_ram_raddr_lsb (te_sel_wr_mr_ram_raddr_lsb_pre)
             ,.te_sel_wr_mr_pw_num_beats_m1 (te_sel_wr_mr_pw_num_beats_m1_pre)
             ,.te_sel_wr_valid           (te_sel_wr_valid_pre_unused)
             ,.te_wr_entry_ie_btt        (te_wr_entry_ie_btt)
             ,.te_wr_entry_ie_re         (te_wr_entry_ie_re)
             ,.ih_te_wrecc_prefer        (i_ih_te_wrecc_prefer)
             ,.te_wrecc_prefer           (te_wrecc_prefer_pre_unused)
             ,.te_sel_ie_btt             (te_sel_ie_btt_pre)
             ,.te_sel_ie_re              (te_sel_ie_re_pre)
             ,.hmx_mask_wrecc            (hmx_wrecc_pre_mask)
             ,.hmx_oldest_oh_wrecc       (hmx_wrecc_pre_oldest_oh)
             ,.hmx_wrecc_btt_mask        (hmx_wrecc_btt_mask_pre_unused)
             ,.hmx_wrecc_btt_oldest_oh   ({WR_ECC_CAM_ENTRIES{1'b0}})
             ,.te_wrecc_btt_prefer       ({WR_ECC_CAM_ADDR_BITS{1'b0}})
             ,.hmx_mask                  (hmx_wr_pre_mask)
             ,.hmx_oldest_oh             (hmx_wr_pre_oldest_oh)
             ,.te_vpw_prefer             ({WR_CAM_ADDR_BITS{1'b0}})
             ,.hmx_mask_vpw              (hmx_wr_pre_mask_vpw_unused)
             ,.hmx_oldest_oh_vpw         ({WR_CAM_ENTRIES{1'b0}})
             ,.te_entry_critical_currnt_bsm (1'b0) // by PRE, all are page-miss
             );


    te_wr_nxt
    
        #(
            .MWR_BITS                   (MWR_BITS), 
            .PW_WORD_CNT_WD_MAX         (PW_WORD_CNT_WD_MAX),
            .PARTIAL_WR_BITS_LOG2       (PARTIAL_WR_BITS_LOG2),
            .CMD_ENTRY_BITS             (WR_CAM_ADDR_BITS_IE), // Including WR ECC CAM if it's there
            .NUM_CAM_ENTRIES            (WR_CAM_ENTRIES_IE), // Including WR ECC CAM if it's there
            .AUTOPRE_BITS               (AUTOPRE_BITS),
            .IE_TAG_BITS                (IE_TAG_BITS)
        )
    WRnxt (
             .core_ddrc_rstn            (core_ddrc_rstn) 
             ,.co_te_clk                 (co_te_clk) 
             ,.i_wr_enabled              (i_load_ntt) 
             ,.te_sel_entry              (te_sel_wr_entry) 
             ,.te_sel_wr_page            (te_sel_wr_page) 
             ,.te_sel_wr_cmd_autopre     (te_sel_wr_cmd_autopre) 
             ,.te_sel_mwr                (te_sel_mwr) 
             ,.te_sel_wr_mr_ram_raddr_lsb (te_sel_wr_mr_ram_raddr_lsb)
             ,.te_sel_wr_mr_pw_num_beats_m1  (te_sel_wr_mr_pw_num_beats_m1)
             ,.te_sel_pw_num_cols_m1     (te_sel_pw_num_cols_m1) 
             ,.te_pw_num_cols_m1_table     (te_pw_num_cols_m1_table) 
             ,.te_sel_wr_ie_tag          (te_sel_wr_ie_tag)
             ,.te_os_wr_ie_tag_table     (te_os_wr_ie_tag_table)
             ,.te_sel_valid              (te_sel_wr_valid) 
             ,.te_page_hit               (te_wr_page_hit) 
             ,.te_wr_cam_page_hit        (te_wr_cam_page_hit)
             ,.i_wr_en_bsm_num           (te_be_bsm_num[BSM_BITS-1:0]) 
             ,.i_wr_en_bsm_alloc         (1'b1)
             ,.ih_te_rd_page_num         (ih_te_rd_page_num)
             ,.be_op_is_activate_bypass  (be_op_is_activate_bypass)
             ,.te_bypass_rank_bg_bank_num(te_bypass_rank_bg_bank_num)  
             ,.i_wr_en_entry_num         ({ 1'b0, wu_te_entry_num [WR_CAM_ADDR_BITS-1:0]}) 
             ,.te_wr_col_bank            (te_wr_col_bank)
             ,.te_gs_block_wr            (te_gs_block_wr)
             ,.te_sel_vpw_entry          (te_sel_vpw_entry) 
             ,.te_sel_vpw_page           (te_sel_vpw_page) 
             ,.te_sel_vpw_cmd_autopre    (te_sel_vpw_cmd_autopre) 
             ,.te_sel_vpw_valid          (te_sel_vpw_valid) 
             ,.te_sel_vpw_mwr            (te_sel_vpw_mwr) 
             ,.te_sel_vpw_pw_num_cols_m1 (te_sel_vpw_pw_num_cols_m1) 
             ,.te_sel_vpw_mr_ram_raddr_lsb (te_sel_vpw_mr_ram_raddr_lsb)
             ,.te_sel_vpw_pw_num_beats_m1  (te_sel_vpw_pw_num_beats_m1)
             ,.te_sel_vpw_ie_tag         (te_sel_vpw_ie_tag)
             ,.te_sel_wrecc_btt_entry    (te_sel_wrecc_btt_entry) 
             ,.te_sel_wrecc_btt_page     (te_sel_wrecc_btt_page)
             ,.te_sel_wrecc_btt_cmd_autopre (te_sel_wrecc_btt_cmd_autopre)
             ,.te_sel_wrecc_btt_valid    (te_sel_wrecc_btt_valid)
             ,.te_sel_wrecc_btt_mwr      (te_sel_wrecc_btt_mwr)
             ,.te_sel_wrecc_btt_pw_num_cols_m1 (te_sel_wrecc_btt_pw_num_cols_m1)
             ,.te_sel_wrecc_btt_ie_tag   (te_sel_wrecc_btt_ie_tag)
             ,.te_sel_wrecc_btt_ie_btt   (te_sel_wrecc_btt_ie_btt)
             ,.te_sel_wrecc_btt_ie_re    (te_sel_wrecc_btt_ie_re)
             ,.te_sel_wrecc_btt_mr_ram_raddr_lsb (te_sel_wrecc_btt_mr_ram_raddr_lsb)
             ,.te_sel_wrecc_btt_pw_num_beats_m1  (te_sel_wrecc_btt_pw_num_beats_m1)

             ,.te_bank_hit_wrecc_in_vpw     (te_bank_hit_wrecc_in_vpw)      //bank-hit in entries of vpw with te_sel_wrecc_btt_bank
             ,.te_sel_wrecc_btt_bank        (te_sel_wrecc_btt_bank   )      //bank# from wrecc_btt replace logic
             ,.te_bank_hit_vpw_in_wrecc     (te_bank_hit_vpw_in_wrecc)      //bank-hit in entries of wrecc_btt with te_sel_vpw_bank
             ,.te_sel_vpw_bank              (te_sel_vpw_bank         )      //bank# from vpw replace logic
             ,.te_bank_hit_inc_vpw_in_wrecc (te_bank_hit_inc_vpw_in_wrecc) //bank-hit in entries of wrecc_btt with incoming vpw.
             ,.incoming_vpw_bank            (incoming_vpw_bank) //bank# of incoming vpw
             ,.te_vpw_page_hit           (te_vpw_page_hit) 
             ,.te_wr_entry_bsm_num       (te_wr_entry_bsm_num) 
             ,.te_vpw_latency            (te_vpw_latency) 
             ,.te_vpw_pri                (te_vpw_pri) 
             ,.te_vpw_valid              (te_vpw_valid) 
             ,.te_sel_ie_btt             (te_sel_ie_btt)
             ,.te_sel_ie_re              (te_sel_ie_re)
             ,.te_ih_wr_retry            (te_ih_wr_retry_int) // because new transactions are loaded
              //  when new writes are enabled  and not
              //  when write commands arrive from IH 
              //  there is no need for retry here
             ,.ih_te_bsm_num             ({
                                         ih_te_wr_rank_num, 
                                         ih_te_wr_bg_bank_num}) 
             ,.ih_te_bsm_alloc           (1'b1)
             ,.te_yy_wr_combine          (te_wr_nxt_wr_combine) 
             ,.te_ts_valid               (te_bs_wr_valid [TOTAL_BSMS-1:0]) 
             ,.te_vpw_entry              (te_ts_vpw_valid [TOTAL_BSMS-1:0]) 
             ,.wr_nxt_entry_in_ntt       (wr_nxt_entry_in_ntt) 
             ,.be_te_page_hit            (be_te_wr_page_hit) 
             ,.ts_act_page               (ts_act_page)
             ,.ts_bsm_num4pre            (gs_te_bsm_num4pre [BSM_BITS-1:0]) 
             ,.ts_bsm_num4act            (gs_te_bsm_num4act [BSM_BITS-1:0]) 
             ,.ts_bsm_num4rdwr           (gs_te_bsm_num4rdwr [BSM_BITS-1:0]) 
             ,.te_rdwr_autopre           (te_rdwr_autopre) 
             ,.ts_op_is_rdwr             (gs_te_op_is_wr) 
             ,.ts_op_is_precharge        (gs_te_op_is_precharge) 
             ,.ts_op_is_activate         (gs_te_op_is_activate) 
             ,.ts_wr_mode                (gs_te_wr_mode) 
             ,.te_ts_page_hit            (te_bs_wr_page_hit [TOTAL_BSMS-1:0])
             ,.te_wr_entry_valid_cam     (te_wr_entry_valid) 
             ,.te_bs_wr_bank_page_hit    (te_bs_wr_bank_page_hit) 
             ,.te_wr_page_table          (te_wr_page_table) 
             ,.te_wr_cmd_autopre_table   (te_wr_cmd_autopre_table)       
             ,.te_wr_ie_tag_table        (te_wr_ie_tag_table)
             ,.te_wr_entry_ie_btt        (te_wr_entry_ie_btt)
             ,.te_wr_entry_ie_re         (te_wr_entry_ie_re)
             ,.te_ts_wrecc_btt           (te_bs_wrecc_btt)
             ,.te_wr_mr_ram_raddr_lsb_first_table (te_wr_mr_ram_raddr_lsb_first_table)
             ,.te_wr_mr_pw_num_beats_m1_table     (te_wr_mr_pw_num_beats_m1_table)
             ,.te_mwr_table              (te_mwr_table) 
             ,.te_os_mwr_table           (te_os_mwr_table) 
             ,.te_dh_valid               (te_dh_wr_bsm_valid) 
             ,.te_dh_page_hit            (te_dh_wr_bsm_page_hit) 
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((TOTAL_BSMS * WR_CAM_ADDR_BITS_IE) - 1)' found in module 'teengine'
//SJ: This coding style is acceptable and there is no plan to change it.
             ,.te_os_wr_entry_table      (te_os_wr_entry_table[TOTAL_BSMS*WR_CAM_ADDR_BITS_IE-1:0]) 
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used only for uMCTL2, but output always declared in te_wr_nxt module
             ,.te_pghit_vld              (te_wr_pghit_vld) 
//spyglass enable_block W528
             ,.wr_nxt_page_table         (wr_nxt_page_table[TOTAL_BSMS*PAGE_BITS-1:0])      
             ,.wr_nxt_cmd_autopre_table  (wr_nxt_cmd_autopre_table[TOTAL_BSMS*AUTOPRE_BITS-1:0])
//spyglass enable_block SelfDeterminedExpr-ML
             ,.wr_nxt_mr_ram_raddr_lsb_first_table (wr_nxt_mr_ram_raddr_lsb_first_table[TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0])
             ,.wr_nxt_mr_pw_num_beats_m1_table     (wr_nxt_mr_pw_num_beats_m1_table[TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0])
             ,.te_sel_entry_pre          (te_sel_wr_entry_pre) 
             ,.te_sel_wr_page_pre        (te_sel_wr_page_pre) 
             ,.te_sel_wr_cmd_autopre_pre (te_sel_wr_cmd_autopre_pre) 
             ,.te_sel_mwr_pre            (te_sel_mwr_pre) 
             ,.te_sel_wr_mr_ram_raddr_lsb_pre (te_sel_wr_mr_ram_raddr_lsb_pre)
             ,.te_sel_wr_mr_pw_num_beats_m1_pre (te_sel_wr_mr_pw_num_beats_m1_pre)
             ,.te_sel_pw_num_cols_m1_pre (te_sel_pw_num_cols_m1_pre) 
             ,.te_sel_wr_ie_tag_pre      (te_sel_wr_ie_tag_pre)
             ,.te_sel_ie_btt_pre         (te_sel_ie_btt_pre)
             ,.te_sel_ie_re_pre          (te_sel_ie_re_pre)
             ,.te_wr_entry_critical_per_bsm (te_wr_entry_critical_per_bsm)
             ,.reg_ddrc_dis_opt_ntt_by_act    (reg_ddrc_dis_opt_ntt_by_act)
             ,.reg_ddrc_dis_opt_ntt_by_pre    (reg_ddrc_dis_opt_ntt_by_pre)
             ,.ts_te_sel_act_wr             (ts_te_sel_act_wr)
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
             ,.ts_te_act_page            (ts_act_page) 
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
            );

  te_misc
   #(  .RD_CAM_ADDR_BITS (RD_CAM_ADDR_BITS), 
              .WR_CAM_ADDR_BITS (WR_CAM_ADDR_BITS_IE),
              .MAX_CAM_ADDR_BITS(MAX_CAM_ADDR_BITS),
              .RD_CAM_ENTRIES   (RD_CAM_ENTRIES),
              .WR_CAM_ENTRIES   (WR_CAM_ENTRIES_IE), 
              .WR_ECC_CAM_ENTRIES(WR_ECC_CAM_ENTRIES),
              .WR_ECC_CAM_ADDR_BITS(WR_ECC_CAM_ADDR_BITS),
              .RANK_BITS        (RANK_BITS), 
              .LRANK_BITS       (LRANK_BITS), 
              .BG_BITS          (BG_BITS), 
              .BANK_BITS        (BANK_BITS), 
              .BG_BANK_BITS     (BG_BANK_BITS), 
              .PAGE_BITS        (PAGE_BITS),
              .BSM_BITS         (BSM_BITS),
              .IE_WR_TYPE_BITS  (IE_WR_TYPE_BITS)
           )
    te_misc (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.co_te_clk                 (co_te_clk) 
                       ,.ddrc_cg_en                (ddrc_cg_en) 
//                        ,.te_wr_autopre             (te_wr_autopre ) 
//                        ,.te_pi_rd_autopre          (te_pi_rd_autopre ) 
//                        ,.dh_te_dis_autopre_collide_opt (dh_te_dis_autopre_collide_opt) 
                       ,.dh_te_dis_wc              (dh_te_dis_wc) 
//  `ifdef UMCTL2_DUAL_HIF_1_OR_DDRCTL_RD_CRC_RETRY
                       ,.te_wr_ie_blk_collision   (te_wr_ie_blk_collision)
                       ,.te_ts_rd_flush           (te_gs_rd_flush) 
                       ,.te_ts_wr_flush           (te_gs_wr_flush) 
                       ,.te_rd_flush              (te_rd_flush) 
                       ,.te_rd_flush_due_rd       (te_rd_flush_due_rd) 
                       ,.te_rd_flush_due_wr       (te_rd_flush_due_wr) 
                       ,.te_wr_flush_due_rd       (te_wr_flush_due_rd) 
                       ,.te_wr_flush_due_wr       (te_wr_flush_due_wr) 
                       ,.te_wr_flush              (te_wr_flush) 
//                        ,.te_rd_flush_started      (te_rd_flush_started) 
//                        ,.te_wr_flush_started      (te_wr_flush_started) 
                       ,.te_wu_wr_retry           (te_wu_wr_retry) 
                       ,.te_ih_retry              (te_ih_retry) 
//                        ,.ts_bsm_num4rdwr           (gs_te_bsm_num4rdwr) 
                       ,.te_ih_free_rd_entry_valid (te_ih_free_rd_entry_valid) 
                       ,.te_ih_free_rd_entry       (te_ih_free_rd_entry [RD_CAM_ADDR_BITS-1:0]) 
                       ,.ts_op_is_rd               (gs_te_op_is_rd) 
                       ,.ts_op_is_wr               (i_gs_te_op_is_wr) 
//                        ,.ts_wr_mode                (gs_te_wr_mode) 
                       ,.te_rdwr_autopre           (te_rdwr_autopre) 
                       ,.te_rdwr_entry             (os_te_rdwr_entry) 
                       ,.ts_te_autopre             (ts_te_autopre) 
                       ,.te_dh_rd_bsm_valid        (te_dh_rd_bsm_valid) 
                       ,.te_dh_rd_bsm_page_hit     (te_dh_rd_bsm_page_hit) 
                       ,.te_dh_wr_bsm_valid        (te_dh_wr_bsm_valid) 
                       ,.te_dh_wr_bsm_page_hit     (te_dh_wr_bsm_page_hit) 
                       ,.te_dh_rd_valid            (te_dh_rd_valid) 
                       ,.te_dh_rd_page_hit         (te_dh_rd_page_hit) 
                       ,.te_dh_wr_valid            (te_dh_wr_valid) 
                       ,.te_dh_wr_page_hit         (te_dh_wr_page_hit) 
                       ,.te_bs_rd_hi               (te_bs_rd_hi)
                       ,.te_dh_rd_hi               (te_dh_rd_hi)
                       ,.te_gs_rank_rd_valid       (te_gs_rank_rd_valid)
                       ,.te_gs_rank_wr_valid       (te_gs_rank_wr_valid)
                       ,.te_wr_entry_valid         (te_wr_entry_valid)
                       ,.te_rd_entry_valid         (te_rd_entry_valid)
                       ,.te_wr_entry_rankbank      (te_wr_entry_rankbank)
                       ,.te_rd_entry_rankbank      (te_rd_entry_rankbank)
                       ,.te_gs_any_wr_pending      (te_gs_any_wr_pending)
                       ,.te_gs_any_rd_pending      (te_gs_any_rd_pending)
                       ,.te_gs_rank_wr_pending     (te_gs_rank_wr_pending)
                       ,.te_gs_rank_rd_pending     (te_gs_rank_rd_pending)
                       ,.te_gs_bank_wr_pending     (te_gs_bank_wr_pending)
                       ,.te_gs_bank_rd_pending     (te_gs_bank_rd_pending)
                       ,.ih_te_wr_rank_num         (ih_te_wr_rank_num) 
                       ,.ih_te_rd_rank_num         (ih_te_rd_rank_num) 
                       ,.ih_te_wr_bg_bank_num      (ih_te_wr_bg_bank_num) 
                       ,.ih_te_rd_bg_bank_num      (ih_te_rd_bg_bank_num) 
                       ,.te_wr_collision_vld_due_rd   (te_wr_collision_vld_due_rd)
                       ,.te_wr_collision_vld_due_wr   (te_wr_collision_vld_due_wr)
                       ,.te_rws_wr_col_bank        (te_rws_wr_col_bank)
                       ,.te_rws_rd_col_bank        (te_rws_rd_col_bank)
                       ,.te_rd_page_hit            (te_rd_page_hit)
                       ,.te_wr_page_hit_entries    (te_wr_page_hit_entries)
                       ,.te_num_wr_pghit_entries   (te_num_wr_pghit_entries)
                       ,.te_num_rd_pghit_entries   (te_num_rd_pghit_entries)
                       ,.te_vpr_prefer             (te_vpr_prefer) 
                       ,.hmx_rd_vpr_abso_oldest_oh (hmx_rd_vpr_abso_oldest_oh)
                       ,.te_vpw_prefer             (te_vpw_prefer) 
                       ,.hmx_wr_vpw_abso_oldest_oh (hmx_wr_vpw_abso_oldest_oh)
                       ,.te_wrecc_btt_prefer          (te_wrecc_btt_prefer) 
                       ,.hmx_wrecc_btt_abso_oldest_oh (hmx_wrecc_btt_abso_oldest_oh)
                       ,.reg_ddrc_lpddr4           (reg_ddrc_lpddr4)
                       ,.te_rd_rankbank_prefer     (te_rd_rankbank_prefer[RANKBANK_BITS-1:0])
                       ,.te_wr_rankbank_prefer     (te_wr_rankbank_prefer[RANKBANK_BITS-1:0])
                       ,.te_gs_rank_rd_prefer      (te_gs_rank_rd_prefer[RANK_BITS-1:0])
                       ,.te_gs_rank_wr_prefer      (te_gs_rank_wr_prefer[RANK_BITS-1:0])

                      );

//--------------
// Push/Pop CAM
//--------------
assign push_rd_cam = ih_te_rd_valid 
                  & ~te_ih_retry 
;

assign push_lpr_cam = push_rd_cam & ~ih_te_rd_hi_pri[1]; // LPR/VPR
assign push_hpr_cam = push_rd_cam &  ih_te_rd_hi_pri[1]; // HPR/HPRL

assign push_wr_cam = ih_te_wr_valid 
                  & ~te_yy_wr_combine 
                  & ~te_ih_retry 
                  & ~ih_te_wr_entry_num[WR_CAM_ADDR_BITS] 
;

assign push_wrecc_cam = ih_te_wr_valid 
                     & ~te_yy_wr_combine 
                     & ~te_ih_retry 
                     & ih_te_wr_entry_num[WR_CAM_ADDR_BITS] 
; 

assign pop_rd_cam     = gs_te_op_is_rd;
assign pop_lpr_cam    = pop_rd_cam & ~te_rd_entry_hpr[os_te_rdwr_entry[RD_CAM_ADDR_BITS-1:0]];
assign pop_hpr_cam    = pop_rd_cam & te_rd_entry_hpr[os_te_rdwr_entry[RD_CAM_ADDR_BITS-1:0]];

assign pop_wr_cam     = i_gs_te_op_is_wr & (te_mr_ie_wr_type!= 2'b10) ;
assign pop_wrecc_cam  = i_gs_te_op_is_wr & (te_mr_ie_wr_type== 2'b10);

// hmatrix for RD(LPR+HPR)
  te_hmatrix
   #(  
              .CAM_ADDR_BITS (RD_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (RD_CAM_ENTRIES),
              .NUM_COMPS     (RD_NUM_COMPS)
           )
  te_rd_hmatrix (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.ddrc_cg_en                (ddrc_cg_en)
                       ,.push                      (push_rd_cam)
                       ,.push_entry                (ih_te_rd_entry_num)
                       ,.pop                       (pop_rd_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[RD_CAM_ADDR_BITS-1:0])
                       ,.masks                     (hmx_rd_masks)
                       ,.oldest_ohs                (hmx_rd_oldest_ohs)
                       ,.te_vlimit_decr            (te_rd_vlimit_decr)
                );

// hmatrix for WR
  te_hmatrix
   #(  
              .CAM_ADDR_BITS (WR_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (WR_CAM_ENTRIES),
              .NUM_COMPS     (WR_NUM_COMPS)
           )
  te_wr_hmatrix (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.ddrc_cg_en                (ddrc_cg_en)
                       ,.push                      (push_wr_cam)
                       ,.push_entry                (ih_te_wr_entry_num[WR_CAM_ADDR_BITS-1:0])
                       ,.pop                       (pop_wr_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[WR_CAM_ADDR_BITS-1:0])
                       ,.masks                     (hmx_wr_masks)
                       ,.oldest_ohs                (hmx_wr_oldest_ohs)
                       ,.te_vlimit_decr            (te_wr_vlimit_decr)
                );

// hmatrix for WRECC
  te_hmatrix
   #(  
              .CAM_ADDR_BITS (WR_ECC_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (WR_ECC_CAM_ENTRIES),
              .NUM_COMPS     (WRECC_NUM_COMPS)
           )
  te_wrecc_hmatrix (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.ddrc_cg_en                (ddrc_cg_en)
                       ,.push                      (push_wrecc_cam)
                       ,.push_entry                (ih_te_wr_entry_num[WR_ECC_CAM_ADDR_BITS-1:0])
                       ,.pop                       (pop_wrecc_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[WR_ECC_CAM_ADDR_BITS-1:0])
                       ,.masks                     (hmx_wrecc_masks)
                       ,.oldest_ohs                (hmx_wrecc_oldest_ohs)
                       ,.te_vlimit_decr            (te_wrecc_vlimit_decr_unused)
                );


// te_lpr_oldest_tracker
  te_oldest_tracker
   #(  
              .CAM_ADDR_BITS (RD_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (RD_CAM_ENTRIES)
           )
  te_lpr_oldest_tracker (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.push                      (push_lpr_cam)
                       ,.push_entry                (ih_te_rd_entry_num)
                       ,.pop                       (pop_lpr_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[RD_CAM_ADDR_BITS-1:0])
                       ,.oldest_entry              (i_ih_te_lo_rd_prefer)
           );

// te_hpr_oldest_tracker
  te_oldest_tracker
   #(  
              .CAM_ADDR_BITS (RD_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (RD_CAM_ENTRIES)
           )
  te_hpr_oldest_tracker (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.push                      (push_hpr_cam)
                       ,.push_entry                (ih_te_rd_entry_num)
                       ,.pop                       (pop_hpr_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[RD_CAM_ADDR_BITS-1:0])
                       ,.oldest_entry              (i_ih_te_hi_rd_prefer)
           );

// te_wr_oldest_tracker
  te_oldest_tracker
   #(  
              .CAM_ADDR_BITS (WR_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (WR_CAM_ENTRIES)
           )
  te_wr_oldest_tracker (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.push                      (push_wr_cam)
                       ,.push_entry                (ih_te_wr_entry_num[WR_CAM_ADDR_BITS-1:0])
                       ,.pop                       (pop_wr_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[WR_CAM_ADDR_BITS-1:0])
                       ,.oldest_entry              (i_ih_te_wr_prefer)
           );

// te_wrecc_oldest_tracker
  te_oldest_tracker
   #(  
              .CAM_ADDR_BITS (WR_ECC_CAM_ADDR_BITS), 
              .CAM_ENTRIES   (WR_ECC_CAM_ENTRIES)
           )
  te_wrecc_oldest_tracker (
                        .core_ddrc_rstn            (core_ddrc_rstn) 
                       ,.core_ddrc_core_clk        (co_te_clk) 
                       ,.push                      (push_wrecc_cam)
                       ,.push_entry                (ih_te_wr_entry_num[WR_ECC_CAM_ADDR_BITS-1:0])
                       ,.pop                       (pop_wrecc_cam)
                       ,.pop_entry                 (os_te_rdwr_entry[WR_ECC_CAM_ADDR_BITS-1:0])
                       ,.oldest_entry              (i_ih_te_wrecc_prefer)
           );






`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
te_assertions
 #(
      .CHANNEL_NUM            (CHANNEL_NUM), 
      .RANKBANK_BITS          (RANKBANK_BITS), 
      .RD_CAM_ADDR_BITS       (RD_CAM_ADDR_BITS), 
      .WR_CAM_ADDR_BITS       (WR_CAM_ADDR_BITS_IE),
      .WR_CAM_ENTRIES         (WR_CAM_ENTRIES_IE), 
      .MAX_CAM_ADDR_BITS      (MAX_CAM_ADDR_BITS),
      .PAGE_BITS              (PAGE_BITS), 
      .BLK_BITS               (BLK_BITS), 
      .OTHER_RD_ENTRY_BITS    (OTHER_RD_ENTRY_BITS), 
      .OTHER_WR_ENTRY_BITS    (OTHER_WR_ENTRY_BITS), 
      .OTHER_RD_RMW_LSB       (OTHER_RD_RMW_LSB), 
      .OTHER_RD_RMW_TYPE_BITS (OTHER_RD_RMW_TYPE_BITS),
      .IE_RD_TYPE_BITS        (IE_RD_TYPE_BITS),
      .IE_WR_TYPE_BITS        (IE_WR_TYPE_BITS),
      .BT_BITS                (BT_BITS),
      .NO_OF_BT               (NO_OF_BT),
      .IE_BURST_NUM_BITS      (IE_BURST_NUM_BITS), 
      .IE_UNIQ_BLK_BITS       (IE_UNIQ_BLK_BITS),
      .IE_UNIQ_RBK_BITS       (IE_UNIQ_RBK_BITS),
      .IE_UNIQ_BLK_LSB        (IE_UNIQ_BLK_LSB),
      .RANK_BITS              (LRANK_BITS),
      .AM_COL_WIDTH_H         (AM_COL_WIDTH_H),
      .AM_COL_WIDTH_L         (AM_COL_WIDTH_L),
      .BG_BANK_BITS           (BG_BANK_BITS)
    )
  te_assertions (
     .core_ddrc_rstn           (core_ddrc_rstn) 
    ,.co_te_clk                (co_te_clk) 
    ,.ih_te_rd_entry_num       (ih_te_rd_entry_num) 
    ,.ih_te_rd_valid           (ih_te_rd_valid) 
    ,.ih_te_wr_entry_num       (ih_te_wr_entry_num) 
    ,.ih_te_wr_valid           (ih_te_wr_valid) 
    ,.ih_te_wr_rankbank_num    ({
                                 ih_te_wr_rank_num, 
                                 ih_te_wr_bg_bank_num}) 
    ,.ih_te_wr_page_num        (ih_te_wr_page_num) 
    ,.ih_te_wr_block_num       (ih_te_wr_block_num) 
    ,.ih_te_rd_rankbank_num    ({
                                 ih_te_rd_rank_num, 
                                 ih_te_rd_bg_bank_num}) 
    ,.ih_te_rd_page_num        (ih_te_rd_page_num) 
    ,.ih_te_rd_block_num       (ih_te_rd_block_num) 
    ,.ih_te_rd_other_fields    (ih_te_rd_other_fields) 
    ,.ih_te_wr_other_fields    (ih_te_wr_other_fields) 
    ,.ih_te_ie_rd_type         (ih_te_ie_rd_type)
    ,.ih_te_ie_wr_type         (ih_te_ie_wr_type)
    ,.ih_te_ie_bt              (ih_te_ie_bt)
    ,.ih_te_ie_blk_burst_num   (ih_te_ie_blk_burst_num)
    ,.ie_ecc_uniq_block_num    (ie_ecc_uniq_block_num)
    ,.reg_ddrc_ecc_type        (reg_ddrc_ecc_type)
    ,.reg_ddrc_ecc_mode        (reg_ddrc_ecc_mode)
    ,.reg_ddrc_burst_rdwr      (reg_ddrc_burst_rdwr)
    ,.te_mr_ie_wr_type         (te_mr_ie_wr_type)
    ,.te_pi_ie_rd_type         (te_pi_ie_rd_type)
    ,.ih_te_ie_re_vct          (ih_te_ie_re_vct)
    ,.ih_te_ie_btt_vct         (ih_te_ie_btt_vct)
    ,.ih_te_ie_block_num       (ih_te_ie_block_num)
    ,.dh_te_dis_wc             (dh_te_dis_wc) 
    ,.reg_ddrc_addrmap_col_b3  (reg_ddrc_addrmap_col_b3)
    ,.reg_ddrc_addrmap_col_b4  (reg_ddrc_addrmap_col_b4)
    ,.reg_ddrc_addrmap_col_b5  (reg_ddrc_addrmap_col_b5)
    ,.reg_ddrc_addrmap_col_b6  (reg_ddrc_addrmap_col_b6)
    ,.reg_ddrc_addrmap_col_b7  (reg_ddrc_addrmap_col_b7)
    ,.reg_ddrc_addrmap_col_b8  (reg_ddrc_addrmap_col_b8)
    ,.reg_ddrc_addrmap_col_b9  (reg_ddrc_addrmap_col_b9)
    ,.reg_ddrc_addrmap_col_b10 (reg_ddrc_addrmap_col_b10)
    ,.i_ie_wr_blk_addr_collision(i_ie_wr_blk_addr_collision) 
    ,.i_ie_rd_blk_addr_collision(i_ie_rd_blk_addr_collision) 
    ,.te_gs_any_vpr_timed_out  (te_gs_any_vpr_timed_out) 
    ,.te_vpr_valid             (te_vpr_valid) // per CAM, loaded and expired VPR
    ,.te_vpw_valid             (te_vpw_valid) // per CAM, loaded and expired VPW
    ,.te_gs_any_vpw_timed_out  (te_gs_any_vpw_timed_out) 
    ,.te_rd_flush              (te_rd_flush) 
    ,.te_rd_flush_due_wr       (te_rd_flush_due_wr)        
    ,.te_rd_flush_due_rd       (te_rd_flush_due_rd) 
    ,.te_rd_col_entry          (te_rd_col_entry) 
    ,.te_wr_flush              (te_wr_flush) 
    ,.te_wr_flush_due_wr       (te_wr_flush_due_wr)        
    ,.te_wr_flush_due_rd       (te_wr_flush_due_rd) 
    ,.te_wr_flush_started      (te_wr_flush_started) 
    ,.te_wr_col_entry          (te_wr_col_entry) 
    ,.te_os_hi_bsm_hint        (te_os_hi_bsm_hint) 
    ,.te_os_lo_bsm_hint        (te_os_lo_bsm_hint) 
    ,.te_os_wr_bsm_hint        (te_os_wr_bsm_hint) 
    ,.te_ih_rd_retry           (te_ih_rd_retry_int) 
    ,.te_ih_wr_retry           (te_ih_wr_retry_int) 
    ,.te_bs_rd_valid           (te_bs_rd_valid) 
    ,.te_bs_wr_valid           (te_bs_wr_valid) 
//     ,.dh_te_dis_autopre_collide_opt (dh_te_dis_autopre_collide_opt) 
    ,.te_rd_entry_valid        (te_rd_bank_hit_filtred) 
    ,.te_sel_rd_entry          (te_sel_rd_entry) 
    ,.os_te_rdwr_entry         (os_te_rdwr_entry) 
    ,.te_wr_entry_valid        (te_wr_bank_hit_filtred) 
    ,.te_rd_act_entry          (/*os_te_rd_act_entry*/) 
    ,.te_wr_act_entry          (/*os_te_wr_act_entry*/) 
    ,.te_sel_wr_entry          (te_sel_wr_entry) 
    ,.te_yy_wr_combine         (te_yy_wr_combine) 
    ,.te_wr_entry_we_bw_loaded (i_wr_entry_we_bw_loaded)
    ,.gs_te_op_is_rd           (gs_te_op_is_rd) 
    ,.gs_te_op_is_wr           (i_gs_te_op_is_wr) 
    ,.gs_te_op_is_precharge    (gs_te_op_is_precharge) 
    ,.gs_te_op_is_activate     (gs_te_op_is_activate) 
    ,.gs_te_bsm_num4pre        (gs_te_bsm_num4pre) 
    ,.gs_te_bsm_num4act        (gs_te_bsm_num4act) 
    ,.gs_te_bsm_num4rdwr       (gs_te_bsm_num4rdwr) 
    ,.te_rd_entry_bsm_num      (te_rd_entry_bsm_num)
    ,.te_wr_entry_bsm_num      (te_wr_entry_bsm_num)
    ,.te_pi_rd_addr_blk        (te_pi_rd_addr_blk) 
    ,.te_pi_rd_other_fields_rd (te_pi_rd_other_fields_rd)
    ,.ts_act_page              (ts_act_page) 
    ,.te_pi_wr_addr_blk        (te_pi_wr_addr_blk) 
    ,.te_pi_wr_other_fields_wr (te_pi_wr_other_fields_wr) 
    ,.te_rd_page_hit           (te_rd_page_hit) 
    ,.te_wr_page_hit           (te_wr_page_hit) 
    ,.ts_te_autopre            (ts_te_autopre) 
    ,.rd_nxt_page_table        (rd_nxt_page_table) 
    ,.wr_nxt_page_table        (wr_nxt_page_table) 
    ,.gs_te_wr_mode            (gs_te_wr_mode) 
    ,.rd_nxt_entry_in_ntt      (rd_nxt_entry_in_ntt) 
    ,.wr_nxt_entry_in_ntt      (wr_nxt_entry_in_ntt) 
    ,.te_os_rd_entry_table     (te_os_rd_entry_table) 
    ,.te_os_wr_entry_table     (te_os_wr_entry_table) 
    ,.te_rd_entry_valid_cam    (te_rd_entry_valid) 
    ,.te_rd_entry_loaded_cam   (te_rd_entry_loaded)
    ,.te_wr_entry_valid_cam    (te_wr_entry_valid) 
    ,.ih_te_rd_autopre         (ih_te_rd_autopre_i)       
    ,.ih_te_rd_autopre_org      (ih_te_rd_autopre) 
    ,.reg_ddrc_autopre_rmw      (reg_ddrc_autopre_rmw)
    ,.ih_te_rd_rmw              (ih_te_rd_rmw) 
    ,.ih_te_wr_autopre         (ih_te_wr_autopre)       
    ,.dh_te_pageclose          (dh_te_pageclose)        
    ,.dh_te_pageclose_timer    (dh_te_pageclose_timer)  
//     ,.te_pi_rd_autopre         (te_pi_rd_autopre)       
//     ,.te_wr_autopre            (te_wr_autopre) 
    ,.te_be_bsm_num            (te_be_bsm_num)
    ,.rd_cam_delayed_autopre_update_fe (RDcam.delayed_autopre_update_fe)
    ,.wr_cam_delayed_autopre_update_fe (WRcam.delayed_autopre_update_fe)
    ,.wr_cam_rd_and_wr_data_rdy        (WRcam.rd_and_wr_data_rdy)
    ,.wr_cam_i_combine_match           (WRcam.i_combine_match | WRcam.ie_disable_entry_valid)
    ,.ddrc_co_perf_raw_hazard          (ddrc_co_perf_raw_hazard)
    ,.ddrc_co_perf_waw_hazard          (ddrc_co_perf_waw_hazard)
    ,.ddrc_co_perf_war_hazard          (ddrc_co_perf_war_hazard)
    ,.ddrc_co_perf_ie_blk_hazard       (ddrc_co_perf_ie_blk_hazard)
    ,.reg_ddrc_data_bus_width          (reg_ddrc_data_bus_width)
    ,.te_ts_rd_page_hit         (te_bs_rd_page_hit)
    ,.te_ts_rd_valid            (te_bs_rd_valid)
    ,.te_ts_wr_page_hit         (te_bs_wr_page_hit)
    ,.te_ts_wr_valid            (te_bs_wr_valid)
    ,.te_ts_vpr_valid           (te_ts_vpr_valid)
    ,.te_ts_vpw_valid           (te_ts_vpw_valid)
    ,.te_wr_bank_num_table      (te_wr_entry_bsm_num)
    ,.te_rd_bank_num_table      (te_rd_entry_bsm_num)
);


// Checkers for te_pi, te_mr signals for Inline ECC
  property p_ie_te_pi_ie_rd_type_correct;       @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> (te_pi_ie_rd_type       == i_te_pi_ie_rd_type      ); endproperty
  property p_ie_te_pi_ie_bt_correct;            @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> (te_pi_ie_bt            == i_te_pi_ie_bt           ); endproperty
  property p_ie_te_pi_ie_blk_burst_num_correct; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> (te_pi_ie_blk_burst_num == i_te_pi_ie_blk_burst_num); endproperty
  property p_ie_te_mr_ie_wr_type_correct;       @(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_gs_te_op_is_wr |-> (te_mr_ie_wr_type       == i_te_mr_ie_wr_type      ); endproperty
  property p_ie_te_mr_ie_bt_correct;            @(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_gs_te_op_is_wr |-> (te_mr_ie_bt            == i_te_mr_ie_bt           ); endproperty
  property p_ie_te_mr_ie_blk_burst_num_correct; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_gs_te_op_is_wr |-> (te_mr_ie_blk_burst_num == i_te_mr_ie_blk_burst_num); endproperty

  // Check that te_pi_ie_rd_type is correct
  a_ie_te_pi_ie_rd_type_correct       : assert property (p_ie_te_pi_ie_rd_type_correct      ) 
  else $display ("%0t ERROR : te_pi_ie_rd_type       mismatch exp %0d act %0d",$realtime,i_te_pi_ie_rd_type      ,te_pi_ie_rd_type      );

  // Check that te_pi_ie_bt is correct
  a_ie_te_pi_ie_bt_correct            : assert property (p_ie_te_pi_ie_bt_correct           ) 
  else $display ("%0t ERROR : te_pi_ie_bt            mismatch exp %0d act %0d",$realtime,i_te_pi_ie_bt           ,te_pi_ie_bt           );   

  // Check that te_pi_ie_blk_burst_num is correct
  a_ie_te_pi_ie_blk_burst_num_correct : assert property (p_ie_te_pi_ie_blk_burst_num_correct) 
  else $display ("%0t ERROR : te_pi_ie_blk_burst_num mismatch exp %0d act %0d",$realtime,i_te_pi_ie_blk_burst_num,te_pi_ie_blk_burst_num);

  // Check that te_mr_ie_wr_type is correct
  a_ie_te_mr_ie_wr_type_correct       : assert property (p_ie_te_mr_ie_wr_type_correct      ) 
  else $display ("%0t ERROR : te_mr_ie_wr_type       mismatch exp %0d act %0d",$realtime,i_te_mr_ie_wr_type      ,te_mr_ie_wr_type      );

  // Check that te_mr_ie_bt is correct
  a_ie_te_mr_ie_bt_correct            : assert property (p_ie_te_mr_ie_bt_correct           ) 
  else $display ("%0t ERROR : te_mr_ie_bt            mismatch exp %0d act %0d",$realtime,i_te_mr_ie_bt           ,te_mr_ie_bt           );

  // Check that te_mr_ie_blk_burst_num is correct
  a_ie_te_mr_ie_blk_burst_num_correct : assert property (p_ie_te_mr_ie_blk_burst_num_correct) 
  else $display ("%0t ERROR : te_mr_ie_blk_burst_num mismatch exp %0d act %0d",$realtime,i_te_mr_ie_blk_burst_num,te_mr_ie_blk_burst_num);

  property p_ie_te_pi_eccap_correct;            @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> (te_pi_eccap            == i_te_pi_eccap           ); endproperty
  property p_ie_te_mr_eccap_correct;            @(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_gs_te_op_is_wr |-> (te_mr_eccap            == i_te_mr_eccap           ); endproperty

  // Check that te_pi_eccap is correct
  a_ie_te_pi_eccap_correct            : assert property (p_ie_te_pi_eccap_correct           ) 
  else $display ("%0t ERROR : te_pi_eccap            mismatch exp %0d act %0d",$realtime,i_te_pi_eccap           ,te_pi_eccap           );

  // Check that te_mr_eccap is correct
  a_ie_te_mr_eccap_correct            : assert property (p_ie_te_mr_eccap_correct           ) 
  else $display ("%0t ERROR : te_mr_eccap            mismatch exp %0d act %0d",$realtime,i_te_mr_eccap           ,te_mr_eccap           );


  // If te_gs_wr_flush=1, the collision should not be solved by combine (in Dual HIF, combine can happen, but it should not solve collision  
  property p_te_gs_wr_flush_check;              @(posedge co_te_clk) disable iff(!core_ddrc_rstn) te_gs_wr_flush |-> ~te_yy_wr_combine; endproperty

  a_te_gs_wr_flush_check            : assert property (p_te_gs_wr_flush_check) 
  else $display ("%0t ERROR : te_gs_wr_flush is asserted but the collision is solved by write combine",$realtime);


//Length Comparison
//`ifdef DDRCTL_LLC_4CYCSCH
// property p_te_rd_length_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> ($past(gs_te_rd_length,1) == te_pi_rd_length_int) ; endproperty
//`else  // DDRCTL_LLC_4CYCSCH
 property p_te_rd_length_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> (gs_te_rd_length == te_pi_rd_length_int) ; endproperty
//`endif // DDRCTL_LLC_4CYCSCH

  a_te_rd_length_check : assert property (p_te_rd_length_check)
  else $display ("%0t ERROR : the length field is mismatching gs_te_rd_length = %h te_pi_rd_length_int = %h ", $realtime,gs_te_rd_length, te_pi_rd_length_int);


//`ifdef DDRCTL_LLC_4CYCSCH
// property p_te_rd_word_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> ($past(gs_te_rd_word,1) == te_pi_rd_word_int) ; endproperty
//`else  // DDRCTL_LLC_4CYCSCH
 property p_te_rd_word_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_rd |-> (gs_te_rd_word == te_pi_rd_word_int) ; endproperty
//`endif // DDRCTL_LLC_4CYCSCH

  a_te_rd_word_check : assert property (p_te_rd_word_check)
  else $display ("%0t ERROR : the critical word field is mismatching gs_te_rd_word = %h te_pi_rd_word_int = %h ", $realtime,gs_te_rd_word, te_pi_rd_word_int);


//`ifdef DDRCTL_LLC_4CYCSCH
// property p_te_wr_ram_raddr_lsb_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_wr |-> ($past(gs_te_raddr_lsb_first,1) == te_mr_ram_raddr_lsb_first_int) ; endproperty
//`else  // DDRCTL_LLC_4CYCSCH
 property p_te_wr_ram_raddr_lsb_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_gs_te_op_is_wr |-> (gs_te_raddr_lsb_first == te_mr_ram_raddr_lsb_first_int) ; endproperty
//`endif // DDRCTL_LLC_4CYCSCH

  a_te_wr_ram_raddr_lsb_check : assert property (p_te_wr_ram_raddr_lsb_check)
  else $display ("%0t ERROR : the ram_raddr_lsb_first field is mismatching  gs_te_raddr_lsb_first = %h te_mr_ram_raddr_lsb_first_int = %h ", $realtime,gs_te_raddr_lsb_first,te_mr_ram_raddr_lsb_first_int);


//`ifdef DDRCTL_LLC_4CYCSCH
// property p_te_wr_pw_num_beats_m1_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) gs_te_op_is_wr |-> ($past(gs_te_pw_num_beats_m1,1) == te_mr_pw_num_beats_m1_int) ; endproperty
//`else  // DDRCTL_LLC_4CYCSCH
 property p_te_wr_pw_num_beats_m1_check; @(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_gs_te_op_is_wr |-> (gs_te_pw_num_beats_m1 == te_mr_pw_num_beats_m1_int) ; endproperty
//`endif // DDRCTL_LLC_4CYCSCH

  a_te_wr_pw_num_beats_m1_check : assert property (p_te_wr_pw_num_beats_m1_check)
  else $display ("%0t ERROR : the pw_num_beats_m1 field is mismatching gs_te_pw_num_beats_m1 = %h te_mr_pw_num_beats_m1_int = %h ", $realtime,gs_te_pw_num_beats_m1, te_mr_pw_num_beats_m1_int);

// Original logic before timing optimization
wire push_lpr_cam_for_assertion;
wire push_hpr_cam_for_assertion;

// REMOVE FOLLOWING as well as XVP
//assign push_lpr_cam_for_assertion = push_rd_cam & (ih_te_rd_entry_num[RD_CAM_ADDR_BITS-1:0] <= reg_ddrc_lpr_num_entries);
//assign push_hpr_cam_for_assertion = push_rd_cam & (reg_ddrc_lpr_num_entries                 <  ih_te_rd_entry_num[RD_CAM_ADDR_BITS-1:0]);

// Check the value is always same as previous one
//  a_te_push_lpr_check : assert property ( @(posedge co_te_clk) disable iff (~core_ddrc_rstn) push_lpr_cam_for_assertion == push_lpr_cam);
//  a_te_push_hpr_check : assert property ( @(posedge co_te_clk) disable iff (~core_ddrc_rstn) push_hpr_cam_for_assertion == push_hpr_cam);

// Check the write schedule timing.
   property p_wr_schedule_check; @(posedge co_te_clk) disable iff(~core_ddrc_rstn) (i_gs_te_op_is_wr==1'b1) |-> (gs_te_wr_possible[gs_te_bsm_num4rdwr]==1'b1) ; endproperty

   a_wr_schedule_check : assert property (p_wr_schedule_check)
   else $display ("%0t ERROR : a write is schedule while i_wr_possible==0. This is protocol violation in CPE module.", $realtime);


`endif // SNPS_ASSERT_ON
`endif // `ifndef SYNTHESIS
endmodule
