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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_wr_cam.sv#8 $
// -------------------------------------------------------------------------
// Description:
//
// This module handles the entry insertion and deletion of a write cam,
//   and also the flush request if there is collision.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_wr_cam #(
    //---------------------------- PARAMETERS --------------------------------------
     parameter   WR_CAM_ADDR_BITS           = 0
    ,parameter   WR_CAM_ADDR_BITS_IE        = 0
    ,parameter   WR_ECC_CAM_ADDR_BITS       = 0
    ,parameter   WR_CAM_ENTRIES             = 0
    ,parameter   WR_ECC_CAM_ENTRIES         = 0
    ,parameter   WR_CAM_ENTRIES_IE          = 0
    ,parameter   RANK_BITS                  = `UMCTL2_LRANK_BITS
    ,parameter   BG_BITS                    = `MEMC_BG_BITS
    ,parameter   BANK_BITS                  = `MEMC_BANK_BITS
    ,parameter   BG_BANK_BITS               = `MEMC_BG_BANK_BITS
    ,parameter   PAGE_BITS                  = `MEMC_PAGE_BITS
    ,parameter   BLK_BITS                   = `MEMC_BLK_BITS
    ,parameter   BSM_BITS                   = `UMCTL2_BSM_BITS
    ,parameter   OTHER_WR_ENTRY_BITS        = 2                            // override this
    ,parameter   ALLOC_BITS                 = 1
    ,parameter   PARTIAL_WR_BITS            = `UMCTL2_PARTIAL_WR_BITS      // bits for PARTIAL_WR logic
    ,parameter   PARTIAL_WR_BITS_LOG2       = `log2(PARTIAL_WR_BITS)        // bits for PARTIAL_WR logic
    ,parameter   PW_WORD_CNT_WD_MAX         = 2
    ,parameter   PW_BC_SEL_BITS             = 3
    ,parameter   HI_PRI_BITS                = 2
    ,parameter   WR_LATENCY_BITS            = `UMCTL2_XPI_WQOS_TW
    ,parameter   MWR_BITS                   = 1
    ,parameter   HALF_VLD_BITS              = 2
    ,parameter   BT_BITS                    = `MEMC_BLK_TOKEN_BITS   
    ,parameter   NO_OF_BT                   = `MEMC_NO_OF_BLK_TOKEN   
    ,parameter   IE_WR_TYPE_BITS            = 2
    ,parameter   IE_RD_TYPE_BITS            = 2
    ,parameter   IE_BURST_NUM_BITS          = 3
    // write command priority encoding
    ,parameter   CMD_PRI_NPW                = `MEMC_CMD_PRI_NPW
    ,parameter   CMD_PRI_VPW                = `MEMC_CMD_PRI_VPW
    ,parameter   CMD_PRI_RSVD               = `MEMC_CMD_PRI_RSVD
    ,parameter   CMD_PRI_XVPW               = `MEMC_CMD_PRI_XVPW
    ,parameter   RANKBANK_BITS              = RANK_BITS + BG_BANK_BITS
    ,parameter   ENTRY_AUTOPRE_BITS         = 1
    ,parameter   IE_UNIQ_BLK_BITS           = 4
    ,parameter   IE_UNIQ_BLK_LSB            = 3
    ,parameter   ECCAP_BITS                 = 1
    ,parameter   WORD_BITS                  = `MEMC_WORD_BITS
    ,parameter   RETRY_WR_BITS              = 1
    ,parameter   ENTRY_RETRY_TIMES_WIDTH    = 4
    ,parameter   DDR4_COL3_BITS             = 1
    ,parameter   LP_COL4_BITS               = 1
    ,parameter   NUM_RANKS                  = `MEMC_NUM_RANKS
    ,parameter   NUM_TOTAL_BANKS            = 1 << RANKBANK_BITS
    ,parameter   NUM_TOTAL_BSMS             = 1 << BSM_BITS
    ,parameter   IE_TAG_BITS                = IE_WR_TYPE_BITS + IE_BURST_NUM_BITS + BT_BITS + ECCAP_BITS
    ,parameter   WP_BITS                    = 1
    ,parameter   HIF_KEYID_WIDTH            = `DDRCTL_HIF_KEYID_WIDTH
    )
    (      
    //----------------------- INPUTS AND OUTPUTS -----------------------------------
     input                                             core_ddrc_rstn                     // reset
    ,input                                             dh_te_pageclose                    // when 1: use the pageclose feature
    ,input   [7:0]                                     dh_te_pageclose_timer 
    ,input                                             co_te_clk                          // main clock
    ,input                                             ddrc_cg_en                         // clock gating enable
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL assertions
    ,input                                             dh_te_dis_wc                       // disable write combine
//spyglass enable_block W240
    ,input                                             ih_te_rd_valid                     // valid read command
    ,input                                             ih_te_wr_valid                     // valid write command
    ,input [RANK_BITS-1:0]                             ih_te_wr_rank_num                  // rank number
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in uMCTL2 and DYN_BSM uPCTL2 configs. Decided to keep the current implementation.
    ,input [RANK_BITS-1:0]                             ih_te_rd_rank_num                  // rank number
//spyglass enable_block W240
    ,input [BG_BANK_BITS-1:0]                          ih_te_wr_bg_bank_num               // bank number
    ,input [PAGE_BITS-1:0]                             ih_te_wr_page_num                  // page number
    ,input [BLK_BITS-1:0]                              ih_te_wr_block_num                 // block number
    ,input                                             ih_te_wr_autopre                   // auto precharge bit
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in uMCTL2 and DYN_BSM uPCTL2 configs. Decided to keep the current implementation.
    ,input [BG_BANK_BITS-1:0]                          ih_te_rd_bg_bank_num               // bank number
//spyglass enable_block W240
    ,input [PAGE_BITS-1:0]                             ih_te_rd_page_num                  // page number
    ,input  [OTHER_WR_ENTRY_BITS-1:0]                  ih_te_wr_other_fields              // any other data for write command
    ,input  [WR_CAM_ADDR_BITS_IE -1:0]                 ih_te_wr_entry_num                 // allocated entry number
    ,input  [WR_CAM_ADDR_BITS_IE -1:0]                 te_wr_prefer                       // wr page hint index
    ,input  [BSM_BITS-1:0]                             ts_bsm_num4pre
    ,input  [BSM_BITS-1:0]                             ts_bsm_num4act
    ,input                                             te_rdwr_autopre
    ,input                                             ts_op_is_precharge
    ,input                                             ts_op_is_activate
    ,input                                             be_te_page_hit                     // the incoming entry from IH has a current page hit, used to update the page status bit
    ,output [WR_CAM_ENTRIES_IE*RANKBANK_BITS-1:0]      te_wr_entry_rankbank               // rankbank number of all CAM entries to BM
    ,output [WR_CAM_ENTRIES_IE*BSM_BITS-1:0]           te_wr_entry_bsm_num                // BSM number of all CAM entries
    ,output [WR_CAM_ENTRIES_IE-1:0]                    te_wr_cam_page_hit 
    ,input                                             gs_te_wr_mode                      // 1: Write mode 0: Read mode
    ,input                                             reg_ddrc_dis_opt_ntt_by_act
    ,output [BSM_BITS-1:0]                             te_bypass_rank_bg_bank_num         // BSM number for incoming command used in wr_nxt to know #BSM for bypadd
    ,input                                             ih_te_link_to_write                // rmw operation
    ,input  [WR_LATENCY_BITS-1:0]                      ih_te_wr_latency                   // read latency for VPW commands
    ,input  [1:0]                                      ih_te_hi_pri                       // 00 - NPW, 01 - VPW, 10, 11 - reserved
    ,output reg                                        te_gs_any_vpw_timed_out            // signal indicating that any of the VPW entries have timed-out
                                                                                          // this signal goes to the GS - gs_global_fsm.v - module
                                                                                          // and is used for switching from WR to RD state, if the FSM is in WR state
    ,output                                            te_gs_any_vpw_timed_out_w
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_vpw_valid                       // indicates the valid expired-vpr commands to VPW selection n/w
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_vpw_valid_d                     // indicates the valid expired-vpr commands to VPW selection n/w
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_vpw_page_hit                    // indicates the page hit status of the expired-vpr cmds to VPW selection n/w
    ,output [WR_LATENCY_BITS -1:0]                     te_vpw_latency                     // indicates the write latency value of the entry going out on the i_wr_en interface
    ,output [1:0]                                      te_vpw_pri                         // indicates the priority value of the entry going out on the i_wr_en interface
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_bank_hit_wrecc_in_vpw           //bank-hit in entries of vpw with te_sel_wrecc_btt_bank
    ,input  [BSM_BITS-1:0]                             te_sel_wrecc_btt_bank              //bank# from wrecc_btt replace logic
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_bank_hit_vpw_in_wrecc           //bank-hit in entries of wrecc_btt with te_sel_vpw_bank
    ,input  [BSM_BITS-1:0]                             te_sel_vpw_bank                    //bank# from vpw replace logic
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_bank_hit_inc_vpw_in_wrecc         //bank-hit in entries of wrecc_btt with incoming vpw
    ,input  [BSM_BITS-1:0]                             incoming_vpw_bank                    //bank# of incoming vpw
    ,output   [WR_CAM_ENTRIES_IE -1:0]                 te_wr_col_entries                  // Indicate colliding entry (has to be qualified by te_flush_started) 
    ,output reg                                        te_wr_ie_blk_collision             // Block Address collision is happening
                                                                                          // (te_rd_replace computes this)
    ,input                                             be_op_is_activate_bypass
    ,input                                             te_ih_wr_retry                     // collision detected
    ,input   [NUM_TOTAL_BSMS-1:0]                      te_wr_pghit_vld                    // one or more writes ready to be serviced
    ,output  reg [WR_CAM_ADDR_BITS -1:0]               i_enc_entry                        // write combine entry number
    ,output                                            te_yy_wr_combine                   // entry number to wu is valid
    ,output                                            te_yy_wr_combine_noecc
    ,output                                            te_yy_wr_combine_wrecc
    ,output                                            te_wr_nxt_wr_combine               // entry number to wu is valid
    ,output                                            te_flush_due_rd                    // flush for collision
    ,output                                            te_flush_due_wr                    // flush for collision
    ,output                                            te_flush                           // flush for collision
    ,output                                            te_flush_started                   // flush underway for collision (clean off a flop)
    ,output  reg [WR_CAM_ADDR_BITS_IE-1:0]             te_wr_col_entry                    // entry of colliding entry
    ,output  reg [NUM_TOTAL_BSMS-1:0]                  te_wr_col_bank                     // entry of colliding bank (1bit for 1bank)
    ,output                                            ddrc_co_perf_raw_hazard            // pulses for every raw collision
    ,output                                            ddrc_co_perf_waw_hazard            // pulses for every waw collision if wr_combine is disabled
    ,output                                            ddrc_co_perf_ie_blk_hazard_wr      // pulse for every block address collision.
    ,output                                            ddrc_co_perf_vlimit_reached_wr
    ,input [MWR_BITS-1:0]                              ih_te_mwr
    ,input [PARTIAL_WR_BITS-1:0]                       ih_te_wr_word_valid
    ,input [PARTIAL_WR_BITS_LOG2-1:0]                  ih_te_wr_ram_raddr_lsb_first
    ,input [PW_WORD_CNT_WD_MAX-1:0]                    ih_te_wr_pw_num_beats_m1
    ,input [PW_WORD_CNT_WD_MAX-1:0]                    ih_te_wr_pw_num_cols_m1
    ,input  [BT_BITS-1:0]                              ih_te_ie_bt
    ,input  [IE_WR_TYPE_BITS-1:0]                      ih_te_ie_wr_type
    ,input  [IE_RD_TYPE_BITS-1:0]                      ih_te_ie_rd_type
    ,input  [IE_BURST_NUM_BITS-1:0]                    ih_te_ie_blk_burst_num
    ,input  [IE_UNIQ_BLK_BITS-1:0]                     ie_ecc_uniq_block_num
    ,input  [NO_OF_BT-1:0]                             ih_te_ie_btt_vct
    ,input  [NO_OF_BT-1:0]                             ih_te_ie_re_vct
    ,input  [BT_BITS-1:0]                              te_mr_ie_bt
    ,input  [IE_WR_TYPE_BITS-1:0]                      te_mr_ie_wr_type
    ,output [WR_CAM_ENTRIES_IE*IE_TAG_BITS-1:0]        te_wr_ie_tag_table                 // Inline ECC Tag table for wr_replace
    ,output [WR_CAM_ENTRIES_IE-1:0]                    te_wr_entry_ie_btt                 // Block token is terminated for WE_BW
    ,output [WR_CAM_ENTRIES_IE-1:0]                    te_wr_entry_ie_re                  // Read ECC is already read (MWR is not needed)
    ,input  [WR_CAM_ADDR_BITS_IE-1:0]                  te_wrecc_prefer                    // Write ECC prefer entry
    ,input   [ECCAP_BITS-1:0]                          ih_te_wr_eccap
    ,input   [1:0]                                     wu_te_enable_wr                    // enable write signal
    ,input   [WR_CAM_ADDR_BITS -1:0]                   wu_te_entry_num                    // enable write entry number
    ,input   [MWR_BITS-1:0]                            wu_te_mwr                          // Masked write information
    ,input   [PARTIAL_WR_BITS-1:0]                     wu_te_wr_word_valid
    ,input   [PARTIAL_WR_BITS_LOG2-1:0]                wu_te_ram_raddr_lsb_first
    ,input   [PW_WORD_CNT_WD_MAX-1:0]                  wu_te_pw_num_beats_m1
    ,input   [PW_WORD_CNT_WD_MAX-1:0]                  wu_te_pw_num_cols_m1
    ,output                                            i_load_ntt                         // load next transaction table enable
    ,output                                            i_load_ntt_ie                      // Indicate a WRECC entry is invalid -> valid (i_enable && ~ie_disable)
    ,output                                            i_unload_ntt_ie                    // Indicate a WRECC entry is valid -> invalid (ie_disable || i_combine_match)
    ,output  reg                                       r_unload_ntt_ie_bt_reg_vld         // Registered the BT num if i_unload_ntt_ie
    ,output  reg  [BT_BITS-1:0]                        r_unload_ntt_ie_bt_reg
    ,output  reg                                       r_unload_ntt_ie_bt_reg2_vld
    ,output  reg  [BT_BITS-1:0]                        r_unload_ntt_ie_bt_reg2
    ,input                                             ts_te_force_btt
    ,output                                            i_load_cam_ie                      // Indicate a WRECC entry is unload -> load (i_load_en)
    ,output                                            i_unload_cam_ie                    // Indicate a WRECC entry is load -> unload (i_del_en)
          `ifdef SNPS_ASSERT_ON
    ,input        [WR_CAM_ADDR_BITS:0]                 te_wrecc_entry_avail
    ,input        [WR_CAM_ADDR_BITS:0]                 te_wrecc_entry_loaded
          `endif // SNPS_ASSERT_ON
    ,input                                             ts_op_is_wr                        // DRAM op is write
    ,input   [WP_BITS-1:0]                             ts_wr_possible                     // write command MAY be issued this cycle;
                                                                                          //  clean off flop indicator used to disable write combine
    ,input                                             te_gs_block_wr                     // Write is not allowed this cycle
    ,input   [BSM_BITS -1:0]                           ts_bsm_num4rdwr                    // DRAM op BSM number
    ,output  [BSM_BITS-1:0]                            te_be_bsm_num                      // write update BSM number
    ,output  [PAGE_BITS-1:0]                           te_be_page_num                     // write update page number
    ,output  [WR_CAM_ENTRIES_IE*PAGE_BITS-1:0]         te_wr_page_table                   // page addresses of all CAM entries
    ,output  [WR_CAM_ENTRIES_IE*ENTRY_AUTOPRE_BITS-1:0]  te_wr_cmd_autopre_table          // cmd_autopre of all CAM entries
    ,input   [WR_CAM_ADDR_BITS_IE -1:0]                te_wr_entry                        // next transaction entry for write only
    ,output  [BSM_BITS -1:0]                           te_ts_wr_bsm_hint                  // wr BSM hint
    ,output  [BSM_BITS -1:0]                           te_ts_wrecc_bsm_hint               // wrecc BSM hint
    ,output  [BSM_BITS -1:0]                           te_ts_wr_act_bsm_hint              // wr BSM hint
    ,output  [WR_CAM_ADDR_BITS_IE -1:0]                te_mr_wr_ram_addr                  // write buffer read address
    ,output  [BLK_BITS-1:0]                            te_pi_wr_addr_blk                  // block(column) address
    ,output  [OTHER_WR_ENTRY_BITS-1:0]                 te_pi_wr_other_fields_wr           // anything else required during writes
//    ,output                                            te_wr_autopre                      // auto precharge bit
    ,output  [WR_CAM_ENTRIES_IE*MWR_BITS-1:0]          te_mwr_table                       // Masked write entry in CAM, over entire CAM
    ,output  [WR_CAM_ENTRIES_IE*PW_WORD_CNT_WD_MAX-1:0] te_pw_num_cols_m1_table           // Partial write entry in CAM, over entire CAM
    ,output  [PARTIAL_WR_BITS-1:0]                     te_pi_wr_word_valid
    ,output  [WR_CAM_ENTRIES_IE*PARTIAL_WR_BITS_LOG2-1:0] te_wr_mr_ram_raddr_lsb_first_table
    ,output  [WR_CAM_ENTRIES_IE*PW_WORD_CNT_WD_MAX-1:0]   te_wr_mr_pw_num_beats_m1_table
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
      ,output  [PARTIAL_WR_BITS_LOG2-1:0]                te_mr_ram_raddr_lsb_first_int
      ,output  [PW_WORD_CNT_WD_MAX-1:0]                  te_mr_pw_num_beats_m1_int   
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON
    ,output  [WR_CAM_ENTRIES_IE -1:0]                  te_page_hit                        // entries with page hit
    ,output  [WR_CAM_ENTRIES_IE -1:0]                  te_bank_hit                        // valid bank hits from CAM search   
    ,output  [WR_CAM_ENTRIES_IE -1:0]                  te_bank_hit_pre                    // valid bank hits from CAM search   
    ,output  [WR_CAM_ENTRIES_IE -1:0]                  te_entry_valid                     // valid write entry in CAM, over entire CAM 
    ,input [PAGE_BITS-1:0]                             ts_act_page                        // Activate page
//     ,input [ENTRY_AUTOPRE_BITS-1:0]                    ts_rdwr_cmd_autopre
    ,input [WR_CAM_ENTRIES_IE -1:0]                    wr_nxt_entry_in_ntt      
    ,output  [WR_CAM_ENTRIES_IE -1:0]                  te_entry_critical_early            // This entry expires page-hit limiter (early version)
    ,output  [NUM_TOTAL_BSMS -1:0]                     te_entry_critical_per_bsm
    ,output                                            te_entry_critical_currnt_bsm       // to select page-hit WRECC in te_wr_replace even page-hit limiter expires
    ,input [2:0]                                       reg_ddrc_page_hit_limit_wr
    ,input [2:0]                                       reg_ddrc_visible_window_limit_wr   
    ,input [WR_CAM_ENTRIES-1:0]                        te_wr_vlimit_decr
    `ifdef SNPS_ASSERT_ON
       `ifndef SYNTHESIS
    ,output [WR_CAM_ENTRIES_IE-1:0]                    i_entry_we_bw_loaded
    ,output [BT_BITS-1:0]                              i_te_mr_ie_bt
    ,output [IE_WR_TYPE_BITS-1:0]                      i_te_mr_ie_wr_type
    ,output [IE_BURST_NUM_BITS-1:0]                    i_te_mr_ie_blk_burst_num
    ,output [WR_CAM_ENTRIES_IE -1:0]                   i_ie_wr_blk_addr_collision         // For coverpoint  
    ,output  [ECCAP_BITS-1:0]                          i_te_mr_eccap
    ,input                                             wu_ih_flow_cntrl_req
       `endif // SYNTHESIS
    `endif // SYSTEM_VERILOG_ASSERT
    ,output                                            te_entry_valid_clr_by_wc           // entry valid clear by combine
    ,input  [NUM_TOTAL_BSMS-1:0]                       ts_te_sel_act_wr                   //tell TE the activate command is for write or read.
    ,output [WR_CAM_ENTRIES_IE -1:0]                   te_page_hit_entries       
    ,output                                            te_wr_collision_vld_due_rd
    ,output                                            te_wr_collision_vld_due_wr
   ,output reg [RANKBANK_BITS-1:0]                     te_wr_rankbank_prefer   // cid and rank number of oldest entry
   ,output [NUM_TOTAL_BSMS-1:0]                        te_os_wr_pageclose_autopre // bug 7584


`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
    ,input                                     reg_ddrc_opt_vprw_sch
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
    );

    //------------------------- LOCAL PARAMETERS -----------------------------------
    // Entry fields to CAM: all data, omit the valid indicators in entry.v
    localparam  ENTRY_AUTOPRE_LSB         = 0;
    localparam  ENTRY_AUTOPRE_MSB         = ENTRY_AUTOPRE_LSB + ENTRY_AUTOPRE_BITS - 1;
    localparam  ENTRY_HI_PRI_LSB          = ENTRY_AUTOPRE_MSB + 1;
    localparam  ENTRY_HI_PRI_MSB          = ENTRY_HI_PRI_LSB + HI_PRI_BITS - 1;
    localparam  ENTRY_VPW_LAT_LSB         = ENTRY_HI_PRI_MSB + 1;
    localparam  ENTRY_VPW_LAT_MSB         = ENTRY_VPW_LAT_LSB + WR_LATENCY_BITS - 1;
    localparam  ENTRY_BLK_LSB             = ENTRY_VPW_LAT_MSB + 1;
    localparam  ENTRY_BLK_MSB             = ENTRY_BLK_LSB + BLK_BITS - 1;
    localparam  ENTRY_ROW_LSB             = ENTRY_BLK_MSB + 1;
    localparam  ENTRY_ROW_MSB             = ENTRY_ROW_LSB + PAGE_BITS - 1;
    localparam  ENTRY_RANKBANK_LSB        = ENTRY_ROW_MSB + 1;
    localparam  ENTRY_RANKBANK_MSB        = ENTRY_RANKBANK_LSB + RANKBANK_BITS - 1;
    localparam  ENTRY_BANK_LSB            = ENTRY_ROW_MSB + 1;
    localparam  ENTRY_BANK_MSB            = ENTRY_BANK_LSB + BG_BANK_BITS - 1;
    localparam  ENTRY_RANK_LSB            = ENTRY_BANK_MSB + 1;
    localparam  ENTRY_RANK_MSB            = ENTRY_RANK_LSB + RANK_BITS - 1;
    localparam  ENTRY_MWR_LSB             = ENTRY_RANK_MSB + 1;
    localparam  ENTRY_MWR_MSB             = ENTRY_MWR_LSB + MWR_BITS - 1;
    localparam  ENTRY_PW_WORD_VALID_LSB   = ENTRY_MWR_MSB + 1;
    localparam  ENTRY_PW_WORD_VALID_MSB   = ENTRY_PW_WORD_VALID_LSB + PARTIAL_WR_BITS - 1;
    localparam  ENTRY_PW_BC_SEL_LSB       = ENTRY_PW_WORD_VALID_MSB + 1;
    localparam  ENTRY_PW_BC_SEL_MSB       = ENTRY_PW_BC_SEL_LSB + PW_BC_SEL_BITS - 1; 
    localparam  ENTRY_PW_RAM_RADDR_LSB    = ENTRY_PW_BC_SEL_MSB + 1;
    localparam  ENTRY_PW_RAM_RADDR_MSB    = ENTRY_PW_RAM_RADDR_LSB + PARTIAL_WR_BITS_LOG2 - 1;
    localparam  ENTRY_PW_NUM_BEATS_M1_LSB = ENTRY_PW_RAM_RADDR_MSB + 1;
    localparam  ENTRY_PW_NUM_BEATS_M1_MSB = ENTRY_PW_NUM_BEATS_M1_LSB + PW_WORD_CNT_WD_MAX - 1; 
    localparam  ENTRY_PW_NUM_COLS_M1_LSB  = ENTRY_PW_NUM_BEATS_M1_MSB + 1;
    localparam  ENTRY_PW_NUM_COLS_M1_MSB  = ENTRY_PW_NUM_COLS_M1_LSB + PW_WORD_CNT_WD_MAX - 1; 
    localparam  ENTRY_IE_BT_LSB           = ENTRY_PW_NUM_COLS_M1_MSB + 1;
    localparam  ENTRY_IE_BT_MSB           = ENTRY_IE_BT_LSB + BT_BITS - 1;
    localparam  ENTRY_IE_WR_TYPE_LSB      = ENTRY_IE_BT_MSB + 1;
    localparam  ENTRY_IE_WR_TYPE_MSB      = ENTRY_IE_WR_TYPE_LSB + IE_WR_TYPE_BITS - 1;
    localparam  ENTRY_IE_BURST_NUM_LSB    = ENTRY_IE_WR_TYPE_MSB + 1;
    localparam  ENTRY_IE_BURST_NUM_MSB    = ENTRY_IE_BURST_NUM_LSB + IE_BURST_NUM_BITS - 1;
    localparam  ENTRY_IE_UNIQ_BLK_LSB     = ENTRY_IE_BURST_NUM_MSB + 1;
    localparam  ENTRY_IE_UNIQ_BLK_MSB     = ENTRY_IE_UNIQ_BLK_LSB + IE_UNIQ_BLK_BITS - 1;
    localparam  ENTRY_ECCAP_LSB           = ENTRY_IE_UNIQ_BLK_MSB + 1;
    localparam  ENTRY_ECCAP_MSB           = ENTRY_ECCAP_LSB + ECCAP_BITS - 1;
    localparam  ENTRY_RETRY_WR_LSB        = ENTRY_ECCAP_MSB + 1;
    localparam  ENTRY_RETRY_WR_MSB        = ENTRY_RETRY_WR_LSB + RETRY_WR_BITS - 1;
    localparam  ENTRY_RETRY_TIMES_LSB     = ENTRY_RETRY_WR_MSB + 1;
    localparam  ENTRY_RETRY_TIMES_MSB     = ENTRY_RETRY_TIMES_LSB + ENTRY_RETRY_TIMES_WIDTH -1;
    localparam  ENTRY_DWORD_LSB           = ENTRY_RETRY_TIMES_MSB + 1;
    localparam  ENTRY_DWORD_MSB           = ENTRY_DWORD_LSB + WORD_BITS - 1;
    localparam  ENTRY_DDR4_COL3_LSB       = ENTRY_DWORD_MSB + 1;
    localparam  ENTRY_DDR4_COL3_MSB       = ENTRY_DDR4_COL3_LSB + DDR4_COL3_BITS - 1;
    localparam  ENTRY_LP_COL4_LSB         = ENTRY_DDR4_COL3_MSB + 1;
    localparam  ENTRY_LP_COL4_MSB         = ENTRY_LP_COL4_LSB + LP_COL4_BITS - 1;
    localparam  ENTRY_OTHER_LSB           = ENTRY_LP_COL4_MSB + 1;
    localparam  ENTRY_OTHER_MSB           = ENTRY_OTHER_LSB + OTHER_WR_ENTRY_BITS - 1;
    localparam  ENTRY_BITS                = ENTRY_OTHER_MSB + 1;

    localparam  CATEGORY                  = 5;
    localparam  WR_CAM_ENTRIES_IE_POW2    = 2**WR_CAM_ADDR_BITS_IE;

//---------------------- REGISTERS AND WIRES -----------------------------------
wire [(WR_CAM_ENTRIES_IE*2)-1:0]           i_entry_out_pri;                    // individual priority signals from entries
wire [WR_CAM_ENTRIES_IE-1:0]               i_entry_vpw_timed_out;              // individual VPW time-out signals from entries
wire                                       any_vpw_timed_out;
wire                                       i_collision;                        // write collision (causing flush situation detected)
wire                                       i_collision_due_rd;                 // write collision (causing flush situation detected)
wire                                       i_collision_due_wr;                 // write collision (causing flush situation detected)
wire [WR_CAM_ENTRIES_IE -1:0]              i_combine_match;                    // write combine situation detected
wire [WR_CAM_ENTRIES_IE -1:0]              i_combine_match_w;                  // write combine situation detected
wire [WR_CAM_ENTRIES_IE -1:0]              i_wr_combine_replace_bank_match;    // incoming write rank & bank matches existing write address
wire [WR_CAM_ENTRIES_IE -1:0]              i_same_addr_wr;                     // incoming write address matches existing write address
wire  [WR_CAM_ADDR_BITS_IE -1:0]           i_enc_entry_ie;                     // encode the collision entry number (only for collision, not for write combine
wire                                       i_valid_col_entry;                  // There is valid colliding entry
wire [WR_CAM_ENTRIES_IE -1:0]              i_ie_bt_hit;                        // BT hit for scheduled write
wire [WR_CAM_ENTRIES_IE -1:0]              i_ie_bt_hit_filtered;               // BT hit for scheduled write
wire [WR_CAM_ENTRIES_IE -1:0]              i_entry_ie_we_bw_unused;
wire [WR_CAM_ENTRIES_IE -1:0]              i_combine_match_wecc;               // write combine situation detected for WE_BW special case (when entry_valid == 0)
wire [WR_CAM_ENTRIES_IE -1:0]              ie_disable_entry_valid;             // Indiate a entry is valid->invalid due to same bt combine. Not include RMW case.
wire [WR_CAM_ENTRIES_IE -1:0]              ie_enable_entry_valid;              // Indicatea entry is invalid->valid and ~ie_disable at this time.
wire [BSM_BITS-1:0]                        i_wrecc_bsm_hint;                   // BSM hint for WRECC
wire                                       ie_enable_we_bw;                    // Enable WE_BW entry (for inline ECC)   
wire                                       ie_enable_we_bw_wo_op_is_wr;        // Enable WE_BW entry (without op_is_wr for bank_hit)
wire [WR_CAM_ENTRIES_IE -1:0]              i_ie_blk_addr_collision;            // Block Address Collision is being detected
reg                                        r_flush;                            // reg to signal the flush until collided entry is services
wire                                       i_flush_enable;                     // enable a write flush
wire                                       be_op_is_activate_bypass_int = be_op_is_activate_bypass;
  `ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
wire [WR_CAM_ENTRIES_IE -1:0]              te_wr_entry_ie_btt_stickey_sva;     // Indicate entries that have ever been to BTT=1.
    `endif
wire [WR_CAM_ENTRIES_IE -1:0]              te_entry_loaded_sva;                // Indicate entries that are loaded, for assertion check only.
  `endif // SNPS_ASSERT_ON
wire [WR_CAM_ENTRIES_IE -1:0]              i_page_hit;                         // page hit for scheduled write replacement in next table,
                                                                               //  valid only when i_wr_combine_replace_bank_match=1
//spyglass disable_block W528
//SMD: A signal or variable is set but never read - ih_te_rd_rank_bg_bank_num
//SJ: Used for uMCTL2 only or uPCLT2 with _POSTED_WRITE_EN 
wire [BSM_BITS-1:0]                        ih_te_wr_rank_bg_bank_num; 
//spyglass enable_block W528
wire [BSM_BITS-1:0]                        ih_te_rd_rank_bg_bank_num;
// wire                                       autopre_for_pageclose;              // auto-pre generated for pageclose feature
reg  [WR_CAM_ENTRIES_IE -1:0]              i_load_en;                          // load incoming command to the selected entry
reg  [WR_CAM_ENTRIES_IE -1:0]              i_del_en;                           // delete selected stored entry
reg  [WR_CAM_ENTRIES_IE -1:0]              i_write0_en;                        // write portion of a RMW, enable the write portion of the selected RMW entry
reg  [WR_CAM_ENTRIES_IE -1:0]              i_write1_en;                        // read portion of a RMW, enable the write portion of the selected RMW entry
wire [WR_CAM_ENTRIES_IE -1:0]              rd_and_wr_data_rdy;                 // both write data and read data complete (i_wr_data_rdy_wr_en and i_rd_data_rdy_wr_en pulses occured in any order)
wire [(WR_CAM_ENTRIES_IE * ENTRY_BITS) -1:0]  i_entry;                            // contents of all the entries
wire [WR_CAM_ENTRIES_IE -1:0]              i_ld_ntt_en;                        // load next transaction table enable
wire  [WR_CAM_ENTRIES_IE -1:0]             i_bank_hit;                         // entries to the same bank that is being written to - XVPW not considered - to be sent thru NPW n/w
wire  [WR_CAM_ENTRIES_IE -1:0]             i_bank_hit_act;                     // entries to the same bank that is being ACT for RD
wire  [WR_CAM_ENTRIES_IE -1:0]             i_bank_hit_pre;                     // entries to the same bank that is being PRE
wire [PAGE_BITS-1:0]                       i_page;                             // page for BE
wire [BSM_BITS-1:0]                        i_rank_bank;                        // rank and bank for BE
wire [BSM_BITS+PAGE_BITS-1:0]              rank_bank_page;                     // rank, bank, and page for BE
wire [BSM_BITS-1:0]                        i_bsm_hint;                         // BSM hint
wire [BSM_BITS-1:0]                        i_act_bsm_hint;                     // WR ACT BSM hint
//reg  [7:0]       count;      // for loop dummy variable
reg  [BSM_BITS-1:0]                        r_ts_bsm_num4pre;                   // BSM numer of the precharge cmd selected by the scheduler
reg [BSM_BITS-1:0]                         r_ts_bsm_num4any;                   // BSM number for ACT, ACT bypass, PRE or RDWR
reg [BSM_BITS-1:0]                         r_ts_bsm_num4act;                   // BSM number for ACT, ACT bypass
reg [BSM_BITS-1:0]                         r_ts_bsm_num4rdwr;                  // BSM number for RDWR
reg                                        update_pageclose_autopre;           // refresh the auto pre per bank array after operations ACT, ACT bypass or RDWR and after CAM load
reg                                        ts_op_is_activate_delay;            // For LPDDR5. When ACT/WR are issued at the same cycle, updating r_pageclose_autopre for bank of ACT is done in next cycle.
reg                                        r_te_rdwr_autopre;                  // autopre this cycle
reg                                        r_ts_op_is_precharge;               // precharge scheduled this cycle
reg                                        r_ts_op_is_activate;                // activate scheduled this cycle
reg  [PAGE_BITS-1:0]                       r_ts_act_page;                      // Row address of the activated page    
wire [WR_CAM_ENTRIES_IE -1:0]              pages_open_for_bank;                // page is open if same bank of ACT, RDWR one cycle earlier
wire                                       only_one_page_open_for_bank;        // there is exactly one entry with page open for the bank of ACT, RDWR one cycle earlier
reg [NUM_TOTAL_BSMS-1:0]                   r_pageclose_autopre;                // per bank autopre flag 
wire                                       load_cam;
wire  [WR_CAM_ENTRIES_IE -1:0]             i_entry_critical_early;
wire  [WR_CAM_ENTRIES_IE -1:0]             i_entry_critical;
reg  [4:0]                                 page_hit_limit_int;                                      
reg  [4:0]                                 page_hit_limit_cnt [NUM_TOTAL_BSMS-1:0];
reg                                        page_hit_limit_reached;
reg  [NUM_TOTAL_BSMS-1:0]                  i_entry_critical_per_bsm;
reg  [NUM_TOTAL_BSMS-1:0]                  i_entry_critical_per_bsm_next;
reg  [NUM_TOTAL_BSMS-1:0]                  i_entry_critical_per_bsm_early;
wire [NUM_TOTAL_BSMS-1:0]                  i_entry_critical_per_bsm_early_next;
wire                                       page_hit_limit_incoming;
wire                                       page_hit_limit_reached_incoming;
reg  [8:0]                                 vlimit_int;
wire [WR_CAM_ENTRIES_IE-1:0]               te_wr_vlimit_decr_i;
assign te_wr_vlimit_decr_i[WR_CAM_ENTRIES-1:0] = te_wr_vlimit_decr;
assign te_wr_vlimit_decr_i[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES] = {WR_ECC_CAM_ENTRIES{1'b0}};
wire [WR_CAM_ENTRIES_IE-1:0]               te_wr_vlimit_reached;

reg                                        r_ts_op_is_activate_for_rd;         // activate for read is scheduled

wire rdwr_pol_sel;
assign rdwr_pol_sel = 1'b1; 

wire i_ts_op_is_wr;
assign i_ts_op_is_wr = ts_op_is_wr ;



assign only_one_page_open_for_bank = /*|pages_open_for_bank &*/ ~|(pages_open_for_bank&(pages_open_for_bank -1));
 

// Update the per bank auto pre one cycle after every ACT,ACT bypass, PRE or RDWR operation  
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    r_pageclose_autopre    <= {NUM_TOTAL_BSMS{1'b0}};
  end
  else begin
    if (update_pageclose_autopre)
      r_pageclose_autopre[r_ts_bsm_num4any]  <= only_one_page_open_for_bank;
  end
end
   

//--------------------------- MAINLINE CODE ------------------------------------

assign i_combine_match = i_combine_match_w;



genvar cam_slot;
generate
    for (cam_slot = 0; cam_slot < WR_CAM_ENTRIES_IE; cam_slot=cam_slot+1) begin: te_wr_entry_row_GEN
      assign te_wr_page_table[cam_slot*PAGE_BITS +: PAGE_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_ROW_LSB +: PAGE_BITS];
      assign te_wr_cmd_autopre_table[cam_slot*ENTRY_AUTOPRE_BITS +: ENTRY_AUTOPRE_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_AUTOPRE_LSB +: ENTRY_AUTOPRE_BITS];

      assign te_wr_entry_rankbank[cam_slot*RANKBANK_BITS +: RANKBANK_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS];
      assign te_wr_entry_bsm_num[cam_slot*BSM_BITS +: BSM_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS];

      assign te_mwr_table[cam_slot*MWR_BITS +: MWR_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_MWR_LSB +: MWR_BITS];
      assign te_pw_num_cols_m1_table[cam_slot*PW_WORD_CNT_WD_MAX +: PW_WORD_CNT_WD_MAX] = i_entry[cam_slot*ENTRY_BITS + ENTRY_PW_NUM_COLS_M1_LSB +: PW_WORD_CNT_WD_MAX];
      assign te_wr_ie_tag_table[cam_slot*IE_TAG_BITS +: IE_TAG_BITS] = 
      {
        i_entry[cam_slot*ENTRY_BITS + ENTRY_ECCAP_LSB +: ECCAP_BITS],
        i_entry[cam_slot*ENTRY_BITS + ENTRY_IE_WR_TYPE_LSB +: IE_WR_TYPE_BITS],
        i_entry[cam_slot*ENTRY_BITS + ENTRY_IE_BT_LSB +: BT_BITS],
        i_entry[cam_slot*ENTRY_BITS + ENTRY_IE_BURST_NUM_LSB +: IE_BURST_NUM_BITS]
      };
      assign te_wr_mr_ram_raddr_lsb_first_table[cam_slot*PARTIAL_WR_BITS_LOG2 +: PARTIAL_WR_BITS_LOG2] = i_entry[cam_slot*ENTRY_BITS+ENTRY_PW_RAM_RADDR_LSB +: PARTIAL_WR_BITS_LOG2];
      assign te_wr_mr_pw_num_beats_m1_table[cam_slot*PW_WORD_CNT_WD_MAX +: PW_WORD_CNT_WD_MAX]     = i_entry[cam_slot*ENTRY_BITS+ENTRY_PW_NUM_BEATS_M1_LSB +: PW_WORD_CNT_WD_MAX];

    end
endgenerate

assign te_bypass_rank_bg_bank_num = ih_te_rd_rank_bg_bank_num;                 // used in we_nxt   
// decoder with enable to select the entry to store incoming transaction
assign load_cam = ih_te_wr_valid 
                  & (~te_ih_wr_retry)
                  & (~(|i_combine_match))
                  & (~(|i_combine_match_wecc))
;
assign i_load_cam_ie = |i_load_en[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES];
assign i_unload_cam_ie = |i_del_en[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES];


always @(*)
begin: BLK_A
  i_load_en = {WR_CAM_ENTRIES_IE{1'b0}};
  for(int i=0;i<WR_CAM_ENTRIES_IE;i=i+1) begin
    if($unsigned(i) == ih_te_wr_entry_num [WR_CAM_ADDR_BITS_IE -1:0]) begin
      i_load_en [i] = load_cam;
    end
  end
end
// decoder with enable to select the entry to delete the transaction
always @(i_ts_op_is_wr or te_wr_entry)
begin: BLK_B
  i_del_en = {WR_CAM_ENTRIES_IE{1'b0}};
  if (i_ts_op_is_wr) begin
    for(int i=0;i<WR_CAM_ENTRIES_IE;i=i+1) begin
      if($unsigned(i) == te_wr_entry[WR_CAM_ADDR_BITS_IE -1:0]) begin
        i_del_en [i] = 1'b1;
      end
    end
  end
end


   
//***********************************************************************************
//
// because ncverilog doesnt support 2-D wire declaration
// we need to regroup each bit of all the entries as a group
// in order to implement a mux
//
//***********************************************************************************

reg     [(WR_CAM_ENTRIES_IE * ENTRY_BITS) -1:0]   bit_entry;  // group 1 bit of all the entry together

integer                        bit_pos;        // counter variable
integer                        entry;      // counter variable

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((entry * ENTRY_BITS) + bit_pos)' found in module 'te_wr_cam'/Self determined expression '(bit_loc + 1)' found in module 'te_wr_cam'
//SJ: This coding style is acceptable and there is no plan to change it.

always @(i_entry)
  for (bit_pos=0; bit_pos<ENTRY_BITS; bit_pos=bit_pos +1)
    for (entry=0; entry<WR_CAM_ENTRIES_IE; entry=entry +1)
      bit_entry [bit_pos * WR_CAM_ENTRIES_IE + entry] = i_entry [entry * ENTRY_BITS + bit_pos];

// inferring the muxes
// block address to PI
genvar bit_loc;
generate

  // mux out block address for PI
  for (bit_loc=ENTRY_BLK_LSB; bit_loc<=ENTRY_BLK_MSB; bit_loc=bit_loc+1)
  begin : pi_addr_blk
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
          ) pi_addr_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (te_pi_wr_addr_blk [bit_loc - ENTRY_BLK_LSB])
                      );
  end



// "other fields" to PI - for writes
  for (bit_loc=ENTRY_OTHER_LSB; bit_loc<=ENTRY_OTHER_MSB; bit_loc=bit_loc+1)
// selected by the NTT for service
  begin : pi_addr_other_fields_wr
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
         ) pi_addr_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (te_pi_wr_other_fields_wr [bit_loc - ENTRY_OTHER_LSB])
                      );
  end

  // rank/bank/page number to BE to get page hit info
  for (bit_loc=ENTRY_ROW_LSB; bit_loc<=ENTRY_ROW_MSB; bit_loc=bit_loc+1)
  begin : mux21
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS),
          .NUM_ENTRIES (WR_CAM_ENTRIES)
         ) mux (
                       .in_port   (bit_entry [(bit_loc * WR_CAM_ENTRIES_IE) +: WR_CAM_ENTRIES]),
                       .sel  (wu_te_entry_num [WR_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_page [bit_loc - ENTRY_ROW_LSB])
                       );
  end

  // bank hint
  for (bit_loc=ENTRY_BANK_LSB; bit_loc<=ENTRY_RANK_MSB; bit_loc=bit_loc+1)
  begin : mux_bank
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS),
          .NUM_ENTRIES (WR_CAM_ENTRIES)
         ) mux (
    
                       .in_port   (bit_entry [(bit_loc * WR_CAM_ENTRIES_IE) +: WR_CAM_ENTRIES]),
                       .sel  (wu_te_entry_num [WR_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_rank_bank [bit_loc - ENTRY_BANK_LSB])
                      );
  end

// bsm alloc info


  assign    rank_bank_page     = {i_rank_bank, i_page};

//spyglass disable_block W528
//SMD: A signal or variable is set but never read - i_bsm_hint
//SJ: Used for uMCTL2 only
  for (bit_loc=ENTRY_BANK_LSB; bit_loc<=ENTRY_RANK_MSB; bit_loc=bit_loc+1)
  begin : bank_hint
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
         ) mux (
                       .in_port   (bit_entry [(bit_loc * WR_CAM_ENTRIES_IE) +: WR_CAM_ENTRIES_IE]),
                       .sel       (te_wr_prefer [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (i_bsm_hint [bit_loc - ENTRY_BANK_LSB])
                      );
  end
//spyglass enable_block W528

  for (bit_loc=ENTRY_BANK_LSB; bit_loc<=ENTRY_RANK_MSB; bit_loc=bit_loc+1)
  begin : wrecc_bank_hint
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
         ) mux (
                       .in_port   (bit_entry [(bit_loc * WR_CAM_ENTRIES_IE) +: WR_CAM_ENTRIES_IE]),
                       .sel       (te_wrecc_prefer [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (i_wrecc_bsm_hint [bit_loc - ENTRY_BANK_LSB])
                      );
  end

  // VPW latency to te_wr_nxt - selected based on wu_te_entry_num
  for (bit_loc=ENTRY_VPW_LAT_LSB; bit_loc<=ENTRY_VPW_LAT_MSB; bit_loc=bit_loc+1)
  begin : vpw_wr_latency
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS),
          .NUM_ENTRIES (WR_CAM_ENTRIES)
         ) mux (
                       .in_port   (bit_entry [(bit_loc * WR_CAM_ENTRIES_IE) +: WR_CAM_ENTRIES]),
                       .sel       (wu_te_entry_num [WR_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_vpw_latency [bit_loc - ENTRY_VPW_LAT_LSB])
                      );
  end
  // priority of the write command - selected based on wu_te_entry_num
  for (bit_loc=ENTRY_HI_PRI_LSB; bit_loc<=ENTRY_HI_PRI_MSB; bit_loc=bit_loc+1)
  begin : vpw_pri
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS),
          .NUM_ENTRIES (WR_CAM_ENTRIES)
         ) mux (
                       .in_port   (bit_entry [(bit_loc * WR_CAM_ENTRIES_IE) +: WR_CAM_ENTRIES]),
                       .sel       (wu_te_entry_num [WR_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_vpw_pri [bit_loc - ENTRY_HI_PRI_LSB])
                      );
  end


  assign    te_ts_wr_act_bsm_hint = te_ts_wr_bsm_hint;
   

  // wr_word_valid information
  for (bit_loc=ENTRY_PW_WORD_VALID_LSB; bit_loc<=ENTRY_PW_WORD_VALID_MSB; bit_loc=bit_loc+1)
  begin : pi_wr_word_valid
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
         ) pi_wr_word_valid_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (te_pi_wr_word_valid [bit_loc - ENTRY_PW_WORD_VALID_LSB])
                      );
  end
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS

   // logic  [PARTIAL_WR_BITS_LOG2-1:0]                te_mr_ram_raddr_lsb_first_int;
   // logic  [PW_WORD_CNT_WD_MAX-1:0]                  te_mr_pw_num_beats_m1_int;
  // ram_raddr_lsb_first  information
  for (bit_loc=ENTRY_PW_RAM_RADDR_LSB; bit_loc<=ENTRY_PW_RAM_RADDR_MSB; bit_loc=bit_loc+1)
  begin : mr_wr_ram_raddr_lsb_first
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
         ) mr_wr_ram_raddr_lsb_first_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (te_mr_ram_raddr_lsb_first_int [bit_loc - ENTRY_PW_RAM_RADDR_LSB])
                      );
  end

  // pw_num_beats_m1  information
  for (bit_loc=ENTRY_PW_NUM_BEATS_M1_LSB; bit_loc<=ENTRY_PW_NUM_BEATS_M1_MSB; bit_loc=bit_loc+1)
  begin : mr_wr_num_beats_m1
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
         ) mr_wr_num_beats_m1_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       //.out_port  (te_mr_pw_num_beats_eq1 ) // only one bit
                       .out_port  (te_mr_pw_num_beats_m1_int [bit_loc - ENTRY_PW_NUM_BEATS_M1_LSB])
                      );
  end

`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS

endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

assign {te_be_bsm_num, te_be_page_num} = rank_bank_page;

assign te_mr_wr_ram_addr [WR_CAM_ADDR_BITS_IE -1:0] = te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0];


assign te_ts_wr_bsm_hint [BSM_BITS-1:0] = i_bsm_hint [BSM_BITS-1:0];
assign te_ts_wrecc_bsm_hint [BSM_BITS-1:0] = i_wrecc_bsm_hint [BSM_BITS-1:0];

//spyglass disable_block W468
//SMD: Variable/Signal 'i_ld_ntt_en' is indexed by 'wu_te_entry_num[(WR_CAM_ADDR_BITS - 1):0] ' which cannot index the full range of this vector.
//SJ: This happens only in inline ECC configurations and it is intentional.

// load into the next transaction enable
wire [WR_CAM_ENTRIES_IE_POW2-1:0] i_ld_ntt_en_extend;                        // load next transaction table enable
assign i_ld_ntt_en_extend = WR_CAM_ENTRIES_IE_POW2 == WR_CAM_ENTRIES_IE ? i_ld_ntt_en : {{(WR_CAM_ENTRIES_IE_POW2-WR_CAM_ENTRIES_IE){1'b0}},i_ld_ntt_en};
assign i_load_ntt = i_ld_ntt_en_extend [wu_te_entry_num [WR_CAM_ADDR_BITS -1:0]];
//spyglass enable_block W468

// both i_load_ntt_ie and i_unload_ntt_ie should be onehot value if ~0.
assign i_load_ntt_ie = |ie_enable_entry_valid;
assign i_unload_ntt_ie = |((ie_disable_entry_valid | i_combine_match) & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}} & ~i_del_en);

always @ (posedge co_te_clk or negedge core_ddrc_rstn)
  if(~core_ddrc_rstn) begin
    r_unload_ntt_ie_bt_reg_vld <= 1'b0;
    r_unload_ntt_ie_bt_reg     <= {BT_BITS{1'b0}};
  end else begin
    r_unload_ntt_ie_bt_reg_vld <= i_unload_ntt_ie;
    r_unload_ntt_ie_bt_reg     <= ih_te_ie_bt;
  end

always @ (posedge co_te_clk or negedge core_ddrc_rstn)
  if(~core_ddrc_rstn) begin
    r_unload_ntt_ie_bt_reg2_vld <= 1'b0;
    r_unload_ntt_ie_bt_reg2     <= {BT_BITS{1'b0}};
  end else begin
    r_unload_ntt_ie_bt_reg2_vld <= r_unload_ntt_ie_bt_reg_vld;
    r_unload_ntt_ie_bt_reg2     <= r_unload_ntt_ie_bt_reg    ;
  end


// block write combine if a write may be serviced this cycle OR
//  for any RMW operations (link-to address will be wrong if RMW write combine happened)
wire i_wr_possible;

generate
  if (WP_BITS==1) begin : TS_WR_POSSIBLE_SINGLE_BIT

    // ts_wr_possible is single bit, te_wr_pghit_vld is per BSM
    assign i_wr_possible    =  (ts_wr_possible & |te_wr_pghit_vld) & (~te_gs_block_wr);
  end else begin : TS_WR_POSSIBLE_MULTI_BIT

    // both ts_wr_possible and te_wr_pghit_vld are per BSM
    assign i_wr_possible    =  |(ts_wr_possible & te_wr_pghit_vld) & (~te_gs_block_wr);
  end
endgenerate

wire ih_te_link_to_write_w;

assign ih_te_link_to_write_w = ih_te_link_to_write;

wire i_combine_ok_int = (~i_wr_possible) & (~ih_te_link_to_write_w) & (~te_gs_block_wr)
     & (~r_ts_op_is_activate_for_rd) // Write combine is prohibitted in next cycle of ACT for RD as replace logic is shered 
;

wire [WR_CAM_ENTRIES_IE-1:0] i_combine_ok = {(WR_CAM_ENTRIES_IE){i_combine_ok_int}};


//spyglass disable_block W468
//SMD: Variable/Signal 'i_write0_en'/'i_write1_en' is indexed by 'wu_te_entry_num[(WR_CAM_ADDR_BITS - 1):0] ' which cannot index the full range of this vector.
//SJ: This happens only in inline ECC configurations and it is intentional.

// decoder with enable to select the entry to permit write transaction
always @(wu_te_enable_wr or wu_te_entry_num)
begin: BLK_C
  i_write0_en = {WR_CAM_ENTRIES_IE{1'b0}};
  i_write1_en = {WR_CAM_ENTRIES_IE{1'b0}};
  for(int i=0;i<WR_CAM_ENTRIES_IE;i=i+1) begin
     if($unsigned(i)== wu_te_entry_num [WR_CAM_ADDR_BITS -1:0]) begin
       if (wu_te_enable_wr [0])
         i_write0_en [i] = 1'b1;
       if (wu_te_enable_wr [1])
         i_write1_en [i] = 1'b1;
     end
  end 
end
//spyglass enable_block W468

// instantiate the entries
genvar entry_num;
generate
// _replace_P80001562-505275_: Change this for Synopsys
for (entry_num=0; entry_num<WR_CAM_ENTRIES_IE; entry_num=entry_num+1)
begin: u0
  te_wr_entry
   #(.IE_WR_ECC_ENTRY     ((entry_num<WR_CAM_ENTRIES)? 1'b0 : 1'b1), // Indicate this is WR ECC CAM or not
                .RANK_BITS           (RANK_BITS),
                .BG_BITS             (BG_BITS),
                .BANK_BITS           (BANK_BITS),
                .BG_BANK_BITS        (BG_BANK_BITS),
                .RANKBANK_BITS       (RANKBANK_BITS),
                .PAGE_BITS           (PAGE_BITS),
                .BLK_BITS            (BLK_BITS),
                .BSM_BITS            (BSM_BITS),
                .NUM_TOTAL_BSMS      (NUM_TOTAL_BSMS),
                .ENTRY_AUTOPRE_BITS  (ENTRY_AUTOPRE_BITS),
                .OTHER_ENTRY_BITS    (OTHER_WR_ENTRY_BITS),
                .HI_PRI_BITS         (HI_PRI_BITS),
                .BT_BITS             (BT_BITS),
                .NO_OF_BT            (NO_OF_BT),
                .IE_WR_TYPE_BITS     (IE_WR_TYPE_BITS),
                .IE_RD_TYPE_BITS     (IE_RD_TYPE_BITS),
                .IE_BURST_NUM_BITS   (IE_BURST_NUM_BITS),
                .IE_UNIQ_BLK_BITS    (IE_UNIQ_BLK_BITS),
                .IE_UNIQ_BLK_LSB     (IE_UNIQ_BLK_LSB),
                .ECCAP_BITS          (ECCAP_BITS),
                .WORD_BITS           (WORD_BITS),
                .RETRY_WR_BITS       (RETRY_WR_BITS),
                .ENTRY_RETRY_TIMES_WIDTH (ENTRY_RETRY_TIMES_WIDTH),
                .DDR4_COL3_BITS      (DDR4_COL3_BITS),
                .LP_COL4_BITS        (LP_COL4_BITS),
                .PARTIAL_WR_BITS     (PARTIAL_WR_BITS),
                .PARTIAL_WR_BITS_LOG2(PARTIAL_WR_BITS_LOG2), 
                .PW_WORD_CNT_WD_MAX  (PW_WORD_CNT_WD_MAX),
                .WR_LATENCY_BITS     (WR_LATENCY_BITS),
                .PW_BC_SEL_BITS      (PW_BC_SEL_BITS),
                .MWR_BITS            (MWR_BITS),
                .CMD_PRI_NPW         (CMD_PRI_NPW),
                .CMD_PRI_VPW         (CMD_PRI_VPW),
                .CMD_PRI_RSVD        (CMD_PRI_RSVD),
                .CMD_PRI_XVPW        (CMD_PRI_XVPW)
                )
   entry (
                .core_ddrc_rstn                      (core_ddrc_rstn) 
                ,.co_te_clk                          (co_te_clk) 
                ,.ddrc_cg_en                         (ddrc_cg_en)
                ,.ih_te_wr_rank_num                  (ih_te_wr_rank_num) 
                ,.ih_te_wr_autopre                   (ih_te_wr_autopre) 
                ,.ih_te_wr_bg_bank_num               (ih_te_wr_bg_bank_num) 
                ,.ih_te_wr_page_num                  (ih_te_wr_page_num) 
                ,.ih_te_wr_block_num                 (ih_te_wr_block_num) 
                ,.ih_te_ie_bt                        (ih_te_ie_bt)
                ,.ih_te_ie_wr_type                   (ih_te_ie_wr_type)
                ,.ih_te_ie_rd_type                   (ih_te_ie_rd_type)
                ,.ih_te_ie_blk_burst_num             (ih_te_ie_blk_burst_num)
                ,.ih_te_ie_btt_vct                   (ih_te_ie_btt_vct)
                ,.ih_te_ie_re_vct                    (ih_te_ie_re_vct)
                ,.ie_ecc_uniq_block_num              (ie_ecc_uniq_block_num)
                ,.te_mr_ie_bt                        (te_mr_ie_bt)
                ,.ie_enable_we_bw                    (ie_enable_we_bw)
                ,.ie_enable_we_bw_wo_op_is_wr        (ie_enable_we_bw_wo_op_is_wr)
                ,.ih_te_wr_eccap                     (ih_te_wr_eccap)
                ,.ih_te_wr_other_fields              (ih_te_wr_other_fields) 
                ,.ts_bsm_num4rdwr                    (ts_bsm_num4rdwr [BSM_BITS-1:0]) 
                ,.ih_te_mwr                          (ih_te_mwr) 
                ,.ih_te_wr_word_valid                (ih_te_wr_word_valid) 
                ,.ih_te_wr_ram_raddr_lsb_first       (ih_te_wr_ram_raddr_lsb_first) 
                ,.ih_te_wr_pw_num_beats_m1           (ih_te_wr_pw_num_beats_m1)     
                ,.ih_te_wr_pw_num_cols_m1            (ih_te_wr_pw_num_cols_m1)     
                ,.dh_te_dis_wc                       (dh_te_dis_wc) 
                ,.i_combine_ok                       (i_combine_ok [entry_num]) 
                ,.i_mwr                              (wu_te_mwr) 
                ,.i_wr_word_valid                    (wu_te_wr_word_valid) 
                ,.i_wr_ram_raddr_lsb_first           (wu_te_ram_raddr_lsb_first) 
                ,.i_wr_pw_num_beats_m1               (wu_te_pw_num_beats_m1)     
                ,.i_wr_pw_num_cols_m1                (wu_te_pw_num_cols_m1)     
                ,.ih_te_wr_latency                   (ih_te_wr_latency) 
                ,.ih_te_hi_pri                       (ih_te_hi_pri) 
                ,.i_same_addr_wr                     (i_same_addr_wr [entry_num]) 
                ,.i_wr_combine_replace_bank_match    (i_wr_combine_replace_bank_match [entry_num]) 
                ,.i_combine_match                    (i_combine_match_w [entry_num])   // out
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((entry_num * 2) + 1)' found in module 'te_wr_cam'
//SJ: This coding style is acceptable and there is no plan to change it.
                ,.i_entry_out_pri                    (i_entry_out_pri [(entry_num*2)+1: (entry_num*2)  ]) 
//spyglass enable_block SelfDeterminedExpr-ML
//spyglass enable_block W528
                ,.i_entry_vpw_timed_out              (i_entry_vpw_timed_out [entry_num]) 
                ,.i_entry_vpw_valid                  (te_vpw_valid[entry_num]) 
                ,.i_entry_vpw_valid_d                (te_vpw_valid_d[entry_num]) 
                ,.i_entry_vpw_page_hit               (te_vpw_page_hit[entry_num]) 
                ,.i_bank_hit_wrecc_in_vpw            (te_bank_hit_wrecc_in_vpw[entry_num]) //bank-hit in entries of vpw with te_sel_wrecc_btt_bank
                ,.te_sel_wrecc_btt_bank              (te_sel_wrecc_btt_bank   ) //bank# from wrecc_btt replace logic
                ,.i_bank_hit_vpw_in_wrecc            (te_bank_hit_vpw_in_wrecc[entry_num]) //bank-hit in entries of wrecc_btt with te_sel_vpw_bank
                ,.te_sel_vpw_bank                    (te_sel_vpw_bank         ) //bank# from vpw replace logic
                ,.i_bank_hit_inc_vpw_in_wrecc        (te_bank_hit_inc_vpw_in_wrecc[entry_num]) //bank-hit in entries of wrecc_btt with incoming vpw.
                ,.incoming_vpw_bank                  (incoming_vpw_bank) //bank# of incoming vpw

                ,.i_page_hit                         (i_page_hit [entry_num]) 
                ,.i_ie_bt_hit                        (i_ie_bt_hit[entry_num])
                ,.i_entry_ie_we_bw                   (i_entry_ie_we_bw_unused[entry_num]) // not used
                ,.i_entry_ie_btt                     (te_wr_entry_ie_btt[entry_num])
                ,.i_entry_ie_re                      (te_wr_entry_ie_re[entry_num])
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in teengine.v module               
                ,.ie_disable_entry_valid             (ie_disable_entry_valid[entry_num])
                ,.ie_enable_entry_valid              (ie_enable_entry_valid[entry_num])
                ,.ts_te_force_btt                    (ts_te_force_btt)
//spyglass enable_block W528
                ,.i_combine_match_wecc               (i_combine_match_wecc [entry_num])   // out
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
                ,.i_ie_blk_addr_collision            (i_ie_blk_addr_collision[entry_num])
//spyglass enable_block W528
                ,.ih_te_wr_valid                     (ih_te_wr_valid) 
                ,.i_load                             (i_load_en [entry_num]) 
                ,.i_entry_del                        (i_del_en [entry_num]) 
                ,.i_wr_data_rdy_wr_en                (i_write0_en [entry_num]) 
                ,.i_rd_data_rdy_wr_en                (i_write1_en [entry_num]) 
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(entry_num + 1)' found in module 'te_wr_cam'
//SJ: This coding style is acceptable and there is no plan to change it.
                ,.i_entry_out                        (i_entry [ENTRY_BITS*(entry_num +1) -1:ENTRY_BITS*entry_num]) 
//spyglass enable_block SelfDeterminedExpr-ML
                ,.r_ts_bsm_num4pre                   (r_ts_bsm_num4pre [BSM_BITS-1:0]) 
                ,.r_ts_bsm_num4any                   (r_ts_bsm_num4any[BSM_BITS-1:0]) 
                ,.r_ts_bsm_num4act                   (r_ts_bsm_num4act [BSM_BITS-1:0]) 
                ,.r_ts_bsm_num4rdwr                  (r_ts_bsm_num4rdwr[BSM_BITS-1:0]) 
                ,.r_te_rdwr_autopre                  (r_te_rdwr_autopre) 
                ,.r_ts_op_is_precharge               (r_ts_op_is_precharge) 
                ,.r_ts_op_is_activate                (r_ts_op_is_activate) 
                ,.be_te_page_hit                     (be_te_page_hit) 
                ,.r_ts_act_page                      (r_ts_act_page[PAGE_BITS-1:0])
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
                ,.i_load_ntt                         (i_ld_ntt_en [entry_num]) 
//spyglass enable_block W528
                ,.i_bank_hit                         (i_bank_hit [entry_num]) 
                ,.i_bank_hit_act                     (i_bank_hit_act [entry_num]) 
                ,.i_bank_hit_pre                     (i_bank_hit_pre [entry_num]) 
                ,.ts_bsm_num4pre                     (ts_bsm_num4pre)
                ,.i_entry_critical_early             (i_entry_critical_early [entry_num])
                ,.i_entry_critical                   (i_entry_critical [entry_num])
                ,.page_hit_limit_reached             (page_hit_limit_reached)
                ,.page_hit_limit_incoming            (page_hit_limit_incoming) 
                ,.page_hit_limit_reached_incoming    (page_hit_limit_reached_incoming) 
                ,.ts_op_is_wr                        (i_ts_op_is_wr)
                ,.i_vlimit_decr                      (te_wr_vlimit_decr_i[entry_num])
                ,.vlimit_int                         (vlimit_int)
                ,.te_wr_vlimit_reached               (te_wr_vlimit_reached[entry_num])    

                ,.i_entry_valid                      (te_entry_valid [entry_num]) 
                ,.page_open_any_op                   (pages_open_for_bank[entry_num]) 
                ,.rd_and_wr_data_rdy                 (rd_and_wr_data_rdy[entry_num])
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
               ,.i_entry_we_bw_loaded                (i_entry_we_bw_loaded[entry_num])
               ,.i_entry_ie_btt_sticky_sva           (te_wr_entry_ie_btt_stickey_sva[entry_num]) 
`endif
               ,.i_entry_loaded_sva                  (te_entry_loaded_sva[entry_num])
`endif // SNPS_ASSERT_ON
               );
end
endgenerate


 wire delayed_autopre_update_fe;
 wire [BSM_BITS-1 :0] delayed_autopre_update_bsm;
 assign ih_te_rd_rank_bg_bank_num = {ih_te_rd_rank_num,ih_te_rd_bg_bank_num};




// Flopping the activate and precharge inputs from the GS module before using inside the CAM entry
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    update_pageclose_autopre   <= 1'b0;
    ts_op_is_activate_delay    <= 1'b0;
    r_ts_act_page              <= {PAGE_BITS{1'b0}};
    r_ts_bsm_num4any           <= {BSM_BITS{1'b0}};
    r_ts_bsm_num4act           <= {BSM_BITS{1'b0}};     
    r_ts_bsm_num4rdwr          <= {BSM_BITS{1'b0}};     
    r_ts_bsm_num4pre           <= {BSM_BITS{1'b0}};
    r_te_rdwr_autopre          <= 1'b0;
    r_ts_op_is_precharge       <= 1'b0;
    r_ts_op_is_activate        <= 1'b0;
    r_ts_op_is_activate_for_rd <= 1'b0;
  end
  else begin
    update_pageclose_autopre   <= ts_op_is_activate | be_op_is_activate_bypass_int | i_ts_op_is_wr | ts_op_is_activate_delay | ~delayed_autopre_update_fe | (|rd_and_wr_data_rdy);
    ts_op_is_activate_delay    <= (ts_op_is_activate | be_op_is_activate_bypass_int) & i_ts_op_is_wr; // If WR and ACT are issued at the same cycle, delay updating bank of ACT (for LPDDR5)
    r_ts_bsm_num4any           <= i_ts_op_is_wr                ? ts_bsm_num4rdwr:
                                  ts_op_is_activate            ? ts_bsm_num4act :
                                  be_op_is_activate_bypass_int ? ih_te_rd_rank_bg_bank_num :
                                  ts_op_is_activate_delay      ? r_ts_bsm_num4act:
                                  ~delayed_autopre_update_fe   ? delayed_autopre_update_bsm :
                                  /*(|rd_and_wr_data_rdy) ?*/    
                           (r_ts_bsm_num4any != te_be_bsm_num) ? te_be_bsm_num :
                                  r_ts_bsm_num4any;
    r_ts_bsm_num4act           <= ts_op_is_activate            ? ts_bsm_num4act :
                                  be_op_is_activate_bypass_int ? ih_te_rd_rank_bg_bank_num :
                                  r_ts_bsm_num4act;
    if (r_ts_bsm_num4rdwr != ts_bsm_num4rdwr) begin
       r_ts_bsm_num4rdwr          <= ts_bsm_num4rdwr; // For both RD/WR (RD is only for AP)
    end
    if (|(r_ts_bsm_num4pre ^ ts_bsm_num4pre)) begin
      r_ts_bsm_num4pre           <= ts_bsm_num4pre;
    end
    r_te_rdwr_autopre          <= te_rdwr_autopre;
    r_ts_op_is_precharge       <= ts_op_is_precharge;
    r_ts_op_is_activate        <= ts_op_is_activate | be_op_is_activate_bypass_int ;
    r_ts_act_page              <= be_op_is_activate_bypass_int ? ih_te_rd_page_num: 
                                  (r_ts_act_page != ts_act_page) ? ts_act_page :
                                  r_ts_act_page;  
       // This signal is used to block write combine after ACT for RD and select bank_hit. So this can be always 0 when the feature is disabled
    r_ts_op_is_activate_for_rd  <= ((ts_op_is_activate & ( rdwr_pol_sel ? ~ts_te_sel_act_wr[ts_bsm_num4act] : ~gs_te_wr_mode)) | be_op_is_activate_bypass_int)  & (~reg_ddrc_dis_opt_ntt_by_act);
  end
end
    
   wire delayed_autopre_update_wr;
   wire delayed_autopre_update_rd;
   wire delayed_autopre_update_ff;
   //A depth of 8 is sufficient to keep delayed_autopre_update_q never full
   localparam DELAYED_AUTOPRE_QD = 8;
   wire [`UMCTL_LOG2(DELAYED_AUTOPRE_QD):0] wcount_unused;

   wire par_err_unused;
   
   assign delayed_autopre_update_wr = (|rd_and_wr_data_rdy) & (ts_op_is_activate | be_op_is_activate_bypass_int | i_ts_op_is_wr | ~delayed_autopre_update_fe | ts_op_is_activate_delay );
   assign delayed_autopre_update_rd = ~(ts_op_is_activate | be_op_is_activate_bypass_int | i_ts_op_is_wr | ts_op_is_activate_delay );
   // When CAM load occurs simultaniously with updates due to ACT or RDWR the bank is stored in delayed_autopre_update_q to trigger an update later

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(1024 * 8)' found in module 'te_wr_cam'
//SJ: This coding style is acceptable and there is no plan to change it. - refers to `UMCTL_LOG2

   //DWC_ddr_umctl2_retime #(RANKBANK_BITS)
   DWC_ddr_umctl2_gfifo
    #(
     .WIDTH           (BSM_BITS),
     .DEPTH           (DELAYED_AUTOPRE_QD),
     .ADDR_WIDTH      (`UMCTL_LOG2(DELAYED_AUTOPRE_QD)),
     .COUNT_WIDTH     (`UMCTL_LOG2(DELAYED_AUTOPRE_QD)+1),
     .OCCAP_EN        (0), // not supported
     .OCCAP_PIPELINE_EN (0)) // Balancing for check_occap_en_cmp_occap_pipeline_en check in preprocess script
   delayed_autopre_update_q (
     .clk         (co_te_clk),    
     .rst_n       (core_ddrc_rstn),    
     .d           (te_be_bsm_num),
     .wr          (delayed_autopre_update_wr),
     .rd          (delayed_autopre_update_rd),
     .par_en      (1'b0), // not supported
     .init_n      (1'b1),
     .wcount      (wcount_unused),              
     .q           (delayed_autopre_update_bsm),
     .fe          (delayed_autopre_update_fe),
     //spyglass disable_block W528
     //SMD: A signal or variable is set but never read
     //SJ: Used in RTL assertions
     .ff          (delayed_autopre_update_ff),
     //spyglass enable_block W528
     .par_err     (par_err_unused)
    `ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
    ,.disable_sva_fifo_checker_rd (1'b1) // read data (delayed_autopre_update_bsm) is validated by ~delayed_autopre_update_fe in this module
    ,.disable_sva_fifo_checker_wr (1'b1) // assertion disabled due to bug 3892; the FIFO can overflow.
    `endif // SYNTHESIS
    `endif // SNPS_ASSERT_ON
   );
//spyglass enable_block SelfDeterminedExpr-ML

// Generating a single-bit signal indicating if there are any timed-out VPW entries in the CAM
assign any_vpw_timed_out         = |i_entry_vpw_timed_out;

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_gs_any_vpw_timed_out <= 1'b0;
  end
  else begin
    te_gs_any_vpw_timed_out <= any_vpw_timed_out;
  end
end

assign te_gs_any_vpw_timed_out_w = any_vpw_timed_out; // Non flopped version

// note: following codes are commented out for bug 7584
// Auto-pre for pageclose feature is asserted if there are NO pending commands with a bank/page hit
// and the pageclose feature is enabled
// wire autopre_for_pageclose_int = r_pageclose_autopre[ts_bsm_num4rdwr];

// Auto-pre only if dh_te_pageclose_timer==0 and dh_te_pageclose=1 
// assign autopre_for_pageclose = (dh_te_pageclose_timer==8'h00 && dh_te_pageclose) ? autopre_for_pageclose_int : 1'b0;
assign te_os_wr_pageclose_autopre = (dh_te_pageclose_timer==8'h00 && dh_te_pageclose) ? r_pageclose_autopre : {NUM_TOTAL_BSMS{1'b0}};

// Auto-pre to PI is an OR of the auto-pre from the CAM and the page close autopre
// For WD_E, this should not be AP=1 because there are pagehit WE_BW is always there. 
// ts_rdwr_cmd_autopre[0] Force AP=1 
// ts_rdwr_cmd_autopre[1] Force AP=0 (for Inline ECC only, WD_E)         
// assign te_wr_autopre      = ts_rdwr_cmd_autopre[0] | (autopre_for_pageclose `ifdef MEMC_USE_RMW_OR_MEMC_INLINE_ECC & (~ts_rdwr_cmd_autopre[1]) `endif );
// The following is a non functional change to approximate timing the anticipated autopre enhancement 
/*always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    te_wr_autopre <= 1'b0;
  else
    te_wr_autopre <= autopre_for_pageclose;
*/
// entry to participate in selection should be any operations to the same bank that
//  is being written to; or entry to the same bank as a write combine
// Note: write combine not allowed when i_wr_possible=1
// XVPW not considered as XVPW entries have to go through its own selection n/w

assign te_bank_hit = 
         (                     r_ts_op_is_activate_for_rd | 
                     te_gs_block_wr) ? i_bank_hit_act : // Activate for RD / Write combine with ACT at the same time (so ACT bank compare works)
                                       i_wr_possible ? i_bank_hit&(~wr_nxt_entry_in_ntt 
                                                                  )                    :  // write command bank match
                                                       i_wr_combine_replace_bank_match;   // write combine bank match

assign te_bank_hit_pre = i_bank_hit_pre;
assign te_page_hit = i_page_hit;

assign te_page_hit_entries = i_page_hit;

assign te_wr_cam_page_hit = i_page_hit;
assign i_ie_bt_hit_filtered = i_ie_bt_hit & (~wr_nxt_entry_in_ntt);

// set status fields according to the CAM and transaction
// +-----------+----------------------------------------+-----------------------------+
// | incoming  |            rd CAM                      |        wr CAM               |
// +-----------+----------------------------------------+-----------------------------+
// |    rd     |                                        |       wr flush              |
// |    wr     | rd flush                               | wr combine (return pointer) |
// +-----------+----------------------------------------+-----------------------------+


// start flushing write entries when there is a collision, UNLESS:
//  - read is already flushing (let that complete first to avoid issues w/ RMWs)
//  - write combine is occuring or will occur for this collision
assign i_flush_enable = i_collision & (~(|i_combine_match)) & (~(|i_combine_match_wecc));
assign te_yy_wr_combine      = (|i_combine_match) | (|i_combine_match_wecc);
assign te_yy_wr_combine_noecc   =   (|(i_combine_match[WR_CAM_ENTRIES-1:0])) | (|(i_combine_match_wecc[WR_CAM_ENTRIES-1:0]));
assign te_yy_wr_combine_wrecc   =   (|(i_combine_match_wecc[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES])) | (|(i_combine_match[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]));
assign te_wr_nxt_wr_combine  = |i_combine_match & (~(|i_combine_match_wecc));

assign te_entry_valid_clr_by_wc = |(i_combine_match[WR_CAM_ENTRIES-1:0] & te_entry_valid[WR_CAM_ENTRIES-1:0]);
assign te_wr_collision_vld_due_rd = ih_te_rd_valid & (|(i_same_addr_wr & te_entry_valid));
assign te_wr_collision_vld_due_wr = (ih_te_wr_valid & (|(i_same_addr_wr & te_entry_valid)) & (~te_yy_wr_combine));

// collision (flush) cases:
//  - address must be the same AND
//  - either of the following:
//       - incoming read, OR
//       - incoming write and not a write combine
//RD part of rmw retry should not be collided with it's WR part.
assign i_collision_due_rd = (ih_te_rd_valid & (|i_same_addr_wr));
assign i_collision_due_wr = (ih_te_wr_valid & (|i_same_addr_wr) & (~te_yy_wr_combine));
assign i_collision = i_collision_due_rd | i_collision_due_wr;


wire ddrc_co_perf_raw_hazard_int;   // signal that stays high during raw collision
wire ddrc_co_perf_waw_hazard_int;   // signal that stays high during waw collision with write_combine disabled

reg  ddrc_co_perf_raw_hazard_int_r; // flop of the above signals
reg  ddrc_co_perf_waw_hazard_int_r; // flop of the above signals

assign ddrc_co_perf_raw_hazard_int = i_collision_due_rd;
assign ddrc_co_perf_waw_hazard_int = i_collision_due_wr;

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
     ddrc_co_perf_raw_hazard_int_r <= 1'b0;
     ddrc_co_perf_waw_hazard_int_r <= 1'b0;
  end
  else if(ddrc_cg_en) begin
     ddrc_co_perf_raw_hazard_int_r <= ddrc_co_perf_raw_hazard_int;
     ddrc_co_perf_waw_hazard_int_r <= ddrc_co_perf_waw_hazard_int;
  end
end

// generating pulse at the posedge of these signals
// the number of pulses indicates the number of collisions in each case
assign ddrc_co_perf_raw_hazard = ddrc_co_perf_raw_hazard_int & (~ddrc_co_perf_raw_hazard_int_r);
assign ddrc_co_perf_waw_hazard = ddrc_co_perf_waw_hazard_int & (~ddrc_co_perf_waw_hazard_int_r);

  wire ddrc_co_perf_ie_blk_hazard_int;
  reg  ddrc_co_perf_ie_blk_hazard_r;

  assign ddrc_co_perf_ie_blk_hazard_int = |i_ie_blk_addr_collision & i_collision;

  always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
       ddrc_co_perf_ie_blk_hazard_r <= 1'b0;
    end
    else if(ddrc_cg_en) begin
       ddrc_co_perf_ie_blk_hazard_r <= ddrc_co_perf_ie_blk_hazard_int;
    end
  end

  // generating pulse at the posedge of these signals
  // the number of pulses indicates the number of collisions in each case
  assign ddrc_co_perf_ie_blk_hazard_wr = ddrc_co_perf_ie_blk_hazard_int & (~ddrc_co_perf_ie_blk_hazard_r);
  reg [WR_CAM_ENTRIES-1:0] te_wr_vlimit_reached_d;
  always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
       te_wr_vlimit_reached_d <= {WR_CAM_ENTRIES{1'b0}};
    end
    else if(ddrc_cg_en) begin
       te_wr_vlimit_reached_d <= te_wr_vlimit_reached[WR_CAM_ENTRIES-1:0]; // Ignore WRECC CAM as there are not VPW
    end
  end

  // Flop is in top module 
  assign ddrc_co_perf_vlimit_reached_wr = |(te_wr_vlimit_reached[WR_CAM_ENTRIES-1:0] & (~te_wr_vlimit_reached_d[WR_CAM_ENTRIES-1:0])); // Edge detection;


// This is the more conservative version of the equation below.  This would require
//  write combine to be disabled when r_flush=1

// r_flush indicates that a flush is underway and the offending entry has not
//  yet been purged.
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_flush <= 1'b0;
  else if(ddrc_cg_en)
  begin
    // clear flush when the read is issued, or when a write combine is suddenly possible
    // the latter happens when combine does not occur initially b/c write is not present
    //  yet from the previous write it is colliding/combining with
    r_flush <= i_flush_enable
             & i_valid_col_entry // Flush is only started with valid collided entry
             ;
  end

//assign te_flush         = i_collision | r_flush;
assign te_flush_due_rd  = i_collision_due_rd;
assign te_flush_due_wr  = i_collision_due_wr;
assign te_flush         = i_collision;
assign te_flush_started = r_flush;

// save the collided entry number
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    te_wr_col_entry [WR_CAM_ADDR_BITS_IE -1:0] <= {WR_CAM_ADDR_BITS_IE{1'b0}};
  else if(ddrc_cg_en)
  begin
    if (i_collision)
      te_wr_col_entry [WR_CAM_ADDR_BITS_IE -1:0] <=   i_enc_entry_ie [WR_CAM_ADDR_BITS_IE -1:0];
  end

// save the collided bank number for read
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_wr_col_bank    <= {NUM_TOTAL_BSMS{1'b0}}; 
  end  
  else if(ddrc_cg_en)
  begin
    // If there is colliding entry to be scheduled immediately
    if (i_flush_enable & i_valid_col_entry & te_flush_started)
    begin
      begin
         if(i_collision_due_rd)
            te_wr_col_bank[ih_te_rd_rank_bg_bank_num] <= 1'b1;
      end
    end 
    else begin
      te_wr_col_bank <= {NUM_TOTAL_BSMS{1'b0}};
    end     
  end  
end
integer   i0;
integer   i1;
integer   i2;
integer   i3;
integer   i4;
integer   i5;
integer   i6;
integer   i7;

reg [3:0] i_enc_entry_0;
reg [3:0] i_enc_entry_1;
reg [3:0] i_enc_entry_2;
reg [3:0] i_enc_entry_3;
reg [3:0] i_enc_entry_4;
reg [3:0] i_enc_entry_5;
reg [3:0] i_enc_entry_6;
reg [3:0] i_enc_entry_7;
reg [5:0] i_enc_entry_8;

//spyglass disable_block W415a
//SMD: Signal i_enc_entry_* is being assigned multiple times in same always block. 
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
//spyglass disable_block W216
//SMD: Inappropriate range select for int_part_sel variable: "i0[2:0] "
//SJ: All occurences of W216 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)

// retrieve the write combine or collision entry number
always @(i_same_addr_wr)
begin
   i_enc_entry_0 [3:0] = 4'b0_000;
   i_enc_entry_1 [3:0] = 4'b0_000;
   i_enc_entry_2 [3:0] = 4'b0_000;
   i_enc_entry_3 [3:0] = 4'b0_000;
   i_enc_entry_4 [3:0] = 4'b0_000;
   i_enc_entry_5 [3:0] = 4'b0_000;
   i_enc_entry_6 [3:0] = 4'b0_000;
   i_enc_entry_7 [3:0] = 4'b0_000;
  
        for (i0=7; i0>=0; i0=i0-1)
            if (i_same_addr_wr [i0])
                i_enc_entry_0 [3:0] = {1'b1, i0 [2:0]};
        for (i1=15; i1>=8 ; i1=i1-1)
            if (i_same_addr_wr [i1])
                i_enc_entry_1 [3:0] = {1'b1, i1 [2:0]};
        for (i2=23; i2>=16 ; i2=i2-1)
            if (i_same_addr_wr [i2])
                i_enc_entry_2 [3:0] = {1'b1, i2 [2:0]};
        for (i3=31; i3>=24 ; i3=i3-1)
            if (i_same_addr_wr [i3])
                i_enc_entry_3 [3:0] = {1'b1, i3 [2:0]};
        for (i4=39; i4>=32 ; i4=i4-1)
            if (i_same_addr_wr [i4])
                i_enc_entry_4 [3:0] = {1'b1, i4 [2:0]};
        for (i5=47; i5>=40 ; i5=i5-1)
            if (i_same_addr_wr [i5])
                i_enc_entry_5 [3:0] = {1'b1, i5 [2:0]};
        for (i6=55; i6>=48 ; i6=i6-1)
            if (i_same_addr_wr [i6])
                i_enc_entry_6 [3:0] = {1'b1, i6 [2:0]};
        for (i7=63; i7>=56 ; i7=i7-1)
            if (i_same_addr_wr [i7])
                i_enc_entry_7 [3:0] = {1'b1, i7 [2:0]};

end
//spyglass enable_block W216
//spyglass enable_block W415a

always @(*)
begin
  casez ({i_enc_entry_0 [3], i_enc_entry_1 [3], i_enc_entry_2 [3], i_enc_entry_3 [3],
          i_enc_entry_4 [3], i_enc_entry_5 [3], i_enc_entry_6 [3], i_enc_entry_7 [3]})
    8'b1??????? : i_enc_entry_8 [5:0] = {3'b000, i_enc_entry_0 [2:0]};
    8'b01?????? : i_enc_entry_8 [5:0] = {3'b001, i_enc_entry_1 [2:0]};
    8'b001????? : i_enc_entry_8 [5:0] = {3'b010, i_enc_entry_2 [2:0]};
    8'b0001???? : i_enc_entry_8 [5:0] = {3'b011, i_enc_entry_3 [2:0]};
    8'b00001??? : i_enc_entry_8 [5:0] = {3'b100, i_enc_entry_4 [2:0]};
    8'b000001?? : i_enc_entry_8 [5:0] = {3'b101, i_enc_entry_5 [2:0]};
    8'b0000001? : i_enc_entry_8 [5:0] = {3'b110, i_enc_entry_6 [2:0]};
    8'b00000001 : i_enc_entry_8 [5:0] = {3'b111, i_enc_entry_7 [2:0]};
    default     : i_enc_entry_8 [5:0] = 6'b000000;
  endcase
end

//spyglass disable_block W415a
//SMD: Signal i_enc_entry is being assigned multiple times in same always block. 
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
always @(*)
begin
  i_enc_entry [WR_CAM_ADDR_BITS -1:0] = {WR_CAM_ADDR_BITS{1'b0}};
  i_enc_entry [WR_CAM_ADDR_BITS -1:0] = i_enc_entry_8 [WR_CAM_ADDR_BITS -1:0];
end
//spyglass enable_block W415a



//---------------------------------------------------------------------------------------------------------------
// Search colliding "valid" entry 
// In case of inlineECC, not only one entry is colliding to incoming one (block address collision)
// In this case, select one entry from valid entry (i.e. data is ready)
// i_enc_entry is still needed only for write combine (write combine can be done with entry which waits for data)
// ---------------------------------------------------------------------------------------------------------------

wire [WR_CAM_ENTRIES_IE-1:0]   i_same_addr_wr_filtered; 

assign i_valid_col_entry = |i_same_addr_wr_filtered & (ih_te_rd_valid | ih_te_wr_valid);

assign i_same_addr_wr_filtered = i_same_addr_wr & te_entry_valid; // valid colliding entry
wire [WR_CAM_ADDR_BITS-1:0]       i_enc_entry_ie_wr;
wire                              i_enc_entry_ie_wr_vld;
wire [WR_ECC_CAM_ADDR_BITS-1:-0]  i_enc_entry_ie_wrecc;
wire i_enc_entry_ie_wr_tag_selected_unused;
wire i_enc_entry_ie_wrecc_selected_vld_unused;
wire i_enc_entry_ie_wrecc_tag_selected_unused;

assign i_enc_entry_ie = (i_enc_entry_ie_wr_vld)? {1'b0,i_enc_entry_ie_wr} : {2'b10,i_enc_entry_ie_wrecc};


select_net_lite
 #(
    .TAG_BITS           (1'b0),
    .NUM_INPUTS         (WR_CAM_ENTRIES)
) select_net_ie_col_entry_wr (
    .clk                (co_te_clk),
    .resetb             (core_ddrc_rstn),
    .tags               ({WR_CAM_ENTRIES{1'b0}}),
    .vlds               (i_same_addr_wr_filtered[WR_CAM_ENTRIES-1:0]),
    .wall_next          ({WR_CAM_ADDR_BITS{1'b0}}),
    .selected_vld       (i_enc_entry_ie_wr_vld),
    .tag_selected       (i_enc_entry_ie_wr_tag_selected_unused), // unused
    .selected           (i_enc_entry_ie_wr)
);

select_net_lite
 #(
    .TAG_BITS           (1'b0),
    .NUM_INPUTS         (WR_ECC_CAM_ENTRIES)
) select_net_ie_col_entry_wrecc (
    .clk                (co_te_clk),
    .resetb             (core_ddrc_rstn),
    .tags               ({WR_ECC_CAM_ENTRIES{1'b0}}),
    .vlds               (i_same_addr_wr_filtered[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES]),
    .wall_next          ({WR_ECC_CAM_ADDR_BITS{1'b0}}),
    .selected_vld       (i_enc_entry_ie_wrecc_selected_vld_unused), // unused
    .tag_selected       (i_enc_entry_ie_wrecc_tag_selected_unused), // unused
    .selected           (i_enc_entry_ie_wrecc)
);
/*

integer   k0;
integer   k1;
`ifdef MEMC_NO_OF_WR_ENTRY_GT16
integer   k2;
integer   k3;
`endif // MEMC_NO_OF_WR_ENTRY_GT16
`ifdef MEMC_NO_OF_WR_ENTRY_GT32
integer   k4;
integer   k5;
integer   k6;
integer   k7;
`endif // MEMC_NO_OF_WR_ENTRY_GT32

reg [3:0] i_enc_entry_ie_0;
reg [3:0] i_enc_entry_ie_1;
reg [3:0] i_enc_entry_ie_2;
reg [3:0] i_enc_entry_ie_3;
reg [3:0] i_enc_entry_ie_4;
reg [3:0] i_enc_entry_ie_5;
reg [3:0] i_enc_entry_ie_6;
reg [3:0] i_enc_entry_ie_7;
reg [5:0] i_enc_entry_ie_8;

// retrieve the write combine or collision entry number


//spyglass disable_block W216
//SMD: Inappropriate range select for int_part_sel variable: "i0[2:0] "
//SJ: All occurences of W216 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)
always @(i_same_addr_wr_filtered)
begin
   i_enc_entry_ie_0 [3:0] = 4'b0_000;
   i_enc_entry_ie_1 [3:0] = 4'b0_000;
   i_enc_entry_ie_2 [3:0] = 4'b0_000;
   i_enc_entry_ie_3 [3:0] = 4'b0_000;
   i_enc_entry_ie_4 [3:0] = 4'b0_000;
   i_enc_entry_ie_5 [3:0] = 4'b0_000;
   i_enc_entry_ie_6 [3:0] = 4'b0_000;
   i_enc_entry_ie_7 [3:0] = 4'b0_000;
  
        for (i0=7; i0>=0; i0=i0-1)
            if (i_same_addr_wr_filtered [i0])
                i_enc_entry_ie_0 [3:0] = {1'b1, i0 [2:0]};
        for (i1=15; i1>=8 ; i1=i1-1)
            if (i_same_addr_wr_filtered [i1])
                i_enc_entry_ie_1 [3:0] = {1'b1, i1 [2:0]};
    `ifndef MEMC_NO_OF_WR_ENTRY_16
        for (i2=23; i2>=16 ; i2=i2-1)
            if (i_same_addr_wr_filtered [i2])
                i_enc_entry_ie_2 [3:0] = {1'b1, i2 [2:0]};
        for (i3=31; i3>=24 ; i3=i3-1)
            if (i_same_addr_wr_filtered [i3])
                i_enc_entry_ie_3 [3:0] = {1'b1, i3 [2:0]};
    `ifndef MEMC_NO_OF_WR_ENTRY_32
        for (i4=39; i4>=32 ; i4=i4-1)
            if (i_same_addr_wr_filtered [i4])
                i_enc_entry_ie_4 [3:0] = {1'b1, i4 [2:0]};
        for (i5=47; i5>=40 ; i5=i5-1)
            if (i_same_addr_wr_filtered [i5])
                i_enc_entry_ie_5 [3:0] = {1'b1, i5 [2:0]};
        for (i6=55; i6>=48 ; i6=i6-1)
            if (i_same_addr_wr_filtered [i6])
                i_enc_entry_ie_6 [3:0] = {1'b1, i6 [2:0]};
        for (i7=63; i7>=56 ; i7=i7-1)
            if (i_same_addr_wr_filtered [i7])
                i_enc_entry_ie_7 [3:0] = {1'b1, i7 [2:0]};
    `endif // MEMC_NO_OF_WR_ENTRY_32
    `endif // MEMC_NO_OF_WR_ENTRY_16

end
//spyglass enable_block W216

always @(*)
begin
  casez ({i_enc_entry_ie_0 [3], i_enc_entry_ie_1 [3], i_enc_entry_ie_2 [3], i_enc_entry_ie_3 [3],
          i_enc_entry_ie_4 [3], i_enc_entry_ie_5 [3], i_enc_entry_ie_6 [3], i_enc_entry_ie_7 [3]})
    8'b1??????? : i_enc_entry_ie_8 [5:0] = {3'b000, i_enc_entry_ie_0 [2:0]};
    8'b01?????? : i_enc_entry_ie_8 [5:0] = {3'b001, i_enc_entry_ie_1 [2:0]};
    `ifndef MEMC_NO_OF_WR_ENTRY_16
    8'b001????? : i_enc_entry_ie_8 [5:0] = {3'b010, i_enc_entry_ie_2 [2:0]};
    8'b0001???? : i_enc_entry_ie_8 [5:0] = {3'b011, i_enc_entry_ie_3 [2:0]};
    `ifndef MEMC_NO_OF_WR_ENTRY_32
    8'b00001??? : i_enc_entry_ie_8 [5:0] = {3'b100, i_enc_entry_ie_4 [2:0]};
    8'b000001?? : i_enc_entry_ie_8 [5:0] = {3'b101, i_enc_entry_ie_5 [2:0]};
    8'b0000001? : i_enc_entry_ie_8 [5:0] = {3'b110, i_enc_entry_ie_6 [2:0]};
    8'b00000001 : i_enc_entry_ie_8 [5:0] = {3'b111, i_enc_entry_ie_7 [2:0]};
    `endif // MEMC_NO_OF_WR_ENTRY_32
    `endif // MEMC_NO_OF_WR_ENTRY_16
    default     : i_enc_entry_ie_8 [5:0] = 6'b000000;
  endcase
end

always @(*)
begin
  i_enc_entry_ie [WR_CAM_ADDR_BITS -1:0] = {WR_CAM_ADDR_BITS{1'b0}};
  i_enc_entry_ie [WR_CAM_ADDR_BITS -1:0] = (i_enc_entry_ie_8 [WR_CAM_ADDR_BITS -1:0]);
end
*/
//-----------------
// BT-ENTRY table
//-----------------

assign ie_enable_we_bw = i_ts_op_is_wr & (te_mr_ie_wr_type == `IE_WR_TYPE_WD_E) & (i_ie_bt_hit_filtered[WR_CAM_ENTRIES-1:0] == {WR_CAM_ENTRIES{1'b0}}); 
assign ie_enable_we_bw_wo_op_is_wr = (te_mr_ie_wr_type == `IE_WR_TYPE_WD_E) & (i_ie_bt_hit_filtered[WR_CAM_ENTRIES-1:0] == {WR_CAM_ENTRIES{1'b0}}); // For bank_hit in WE_BW entry

assign te_wr_col_entries = i_same_addr_wr; // For write replace


//----------------------------
// page hit limiter logic
//----------------------------

// Decode register
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    page_hit_limit_int <= 5'b0_0000;
  end
  else begin
    case (reg_ddrc_page_hit_limit_wr)
         3'd1 : page_hit_limit_int <= 5'd3 ; // 4
         3'd2 : page_hit_limit_int <= 5'd7 ; // 8
         3'd3 : page_hit_limit_int <= 5'd15; // 16
         3'd4 : page_hit_limit_int <= 5'd31; // 32
      default : page_hit_limit_int <= 5'd0 ; // Disable
    endcase
  end
end

integer bsm_idx;

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    for (bsm_idx=0;bsm_idx<NUM_TOTAL_BSMS;bsm_idx=bsm_idx+1) begin
      page_hit_limit_cnt[bsm_idx]    <= 5'b1_1111;
    end  
    page_hit_limit_reached         <= 1'b0;
    i_entry_critical_per_bsm       <= {NUM_TOTAL_BSMS{1'b0}};
    i_entry_critical_per_bsm_early <= {NUM_TOTAL_BSMS{1'b0}};
  end  
  else begin
    // Page-hit counter(per bank)
    for (bsm_idx=0;bsm_idx<NUM_TOTAL_BSMS;bsm_idx=bsm_idx+1) begin
      if (r_ts_op_is_activate & (r_ts_bsm_num4act == bsm_idx)) begin
          page_hit_limit_cnt[bsm_idx]     <= page_hit_limit_int;
      end
      else if (i_ts_op_is_wr & (ts_bsm_num4rdwr == bsm_idx) & (page_hit_limit_cnt[bsm_idx] != 5'b0_0000)) begin
          page_hit_limit_cnt[bsm_idx] <=  page_hit_limit_cnt[bsm_idx] - 5'b0_0001;
      end
    end

     // generating event of page hit limit reached
    if (i_ts_op_is_wr & page_hit_limit_cnt[ts_bsm_num4rdwr] == 5'b0_0001) begin
      page_hit_limit_reached <= 1'b1;
    end
    else begin
      page_hit_limit_reached <= 1'b0;
    end

    // generating i_entry_critical_per_bsm
    for (bsm_idx=0;bsm_idx<NUM_TOTAL_BSMS;bsm_idx=bsm_idx+1) begin
      i_entry_critical_per_bsm_early [bsm_idx] <= i_entry_critical_per_bsm_early_next[bsm_idx];
      i_entry_critical_per_bsm       [bsm_idx] <= i_entry_critical_per_bsm_next[bsm_idx];
    end

  end
end 

always @ *
begin
    for (bsm_idx=0;bsm_idx<NUM_TOTAL_BSMS;bsm_idx=bsm_idx+1) begin
     i_entry_critical_per_bsm_next[bsm_idx] = (((r_ts_bsm_num4rdwr == bsm_idx) & r_te_rdwr_autopre) | ((r_ts_bsm_num4pre==bsm_idx) & r_ts_op_is_precharge)
 )? 1'b0 :
                                              (i_entry_critical_per_bsm_early [bsm_idx] & i_ts_op_is_wr & (ts_bsm_num4rdwr == bsm_idx))? 1'b1 : 
                                                                                                                                            i_entry_critical_per_bsm [bsm_idx];
    end
end

generate
genvar gen_bsm_idx;
    for (gen_bsm_idx=0; gen_bsm_idx<NUM_TOTAL_BSMS; gen_bsm_idx=gen_bsm_idx+1) begin: i_entry_critical_per_bsm_early_next_gen
        te_entry_crit
        
        #(
            .BSM_BITS                               (BSM_BITS)
           ,.GEN_BSM_IDX                            (gen_bsm_idx)
        )
        u_te_entry_crit (
            .entry_critical_per_bsm_early_next      (i_entry_critical_per_bsm_early_next[gen_bsm_idx]),
            .ts_bsm_num4rdwr                        (r_ts_bsm_num4rdwr),
            .te_rdwr_autopre                        (r_te_rdwr_autopre),
            .ts_bsm_num4pre                         (r_ts_bsm_num4pre),
            .ts_op_is_precharge                     (r_ts_op_is_precharge),
            .page_hit_limit_reached                 (page_hit_limit_reached),
            .entry_critical_per_bsm_early           (i_entry_critical_per_bsm_early[gen_bsm_idx])
        );
    end // generate gen_bsm_idx
endgenerate    

assign page_hit_limit_incoming = i_entry_critical_per_bsm_early_next [{ih_te_wr_rank_num,ih_te_wr_bg_bank_num}];
assign page_hit_limit_reached_incoming = i_entry_critical_per_bsm_next [{ih_te_wr_rank_num,ih_te_wr_bg_bank_num}];

// Output assignment
assign te_entry_critical_per_bsm = i_entry_critical_per_bsm;
////`ifdef UMCTL2_DYN_BSM
////assign te_entry_critical_early[WR_CAM_ENTRIES-1:0] = (i_wr_possible)? i_entry_critical_early[WR_CAM_ENTRIES-1:0] : {WR_CAM_ENTRIES{(te_entry_critical_per_bsm[bm_te_inc_wr_bsm_num] & bm_te_inc_wr_bsm_alloc)}};
////`elsif UMCTL2_NUM_LRANKS_TOTAL_GT_1
////assign te_entry_critical_early[WR_CAM_ENTRIES-1:0] = (i_wr_possible)? i_entry_critical_early[WR_CAM_ENTRIES-1:0] : {WR_CAM_ENTRIES{te_entry_critical_per_bsm[{ih_te_wr_rank_num,ih_te_wr_bg_bank_num}]}};
////`else
////assign te_entry_critical_early[WR_CAM_ENTRIES-1:0] = (i_wr_possible)? i_entry_critical_early[WR_CAM_ENTRIES-1:0] : {WR_CAM_ENTRIES{te_entry_critical_per_bsm[ih_te_wr_bg_bank_num]}};
////`endif 

assign te_entry_critical_early[WR_CAM_ENTRIES-1:0] = (i_wr_possible)? i_entry_critical_early[WR_CAM_ENTRIES-1:0] : i_entry_critical[WR_CAM_ENTRIES-1:0];

assign te_entry_critical_early[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES] = {WR_ECC_CAM_ENTRIES{1'b0}}; //WRECC entries don't expires page-hit limiter.
                                // In case of NTT update by write combine, we should not use critical signal as nothing is scheduled-out
assign te_entry_critical_currnt_bsm = i_entry_critical_per_bsm_early[ts_bsm_num4rdwr];

// Visible window limiter
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    vlimit_int <= 9'b0_0000_0000;
  end
  else begin
    case (reg_ddrc_visible_window_limit_wr)
         3'd1 : vlimit_int <= 9'd31; 
         3'd2 : vlimit_int <= 9'd63;
         3'd3 : vlimit_int <= 9'd127;
         3'd4 : vlimit_int <= 9'd255;
      default : vlimit_int <= 9'd0;
    endcase
  end
end

// Block address collision indicator (used in te_misc for te_ts_rd_flush
// If this is, write combine is not possible and hence switch  
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_wr_ie_blk_collision <= 1'b0;
  end
  else begin
    te_wr_ie_blk_collision <= (|i_ie_blk_addr_collision) & i_collision;
  end
end


always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_wr_rankbank_prefer <= {RANKBANK_BITS{1'b0}};
  end
  else begin
     if (|(te_wr_rankbank_prefer ^ i_bsm_hint)) begin
        te_wr_rankbank_prefer <= i_bsm_hint;
     end
  end
end

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Unsynthesized signals to debug with waveform viewer
//------------------------------------------------------------------------------
wire                                        wcam_valid [WR_CAM_ENTRIES_IE];
wire    [ENTRY_AUTOPRE_BITS-1:0]            wcam_autopre [WR_CAM_ENTRIES_IE];
wire    [1:0]                               wcam_hi_pri [WR_CAM_ENTRIES_IE];
wire    [WR_LATENCY_BITS-1:0]               wcam_vpw_lat [WR_CAM_ENTRIES_IE];
wire    [BLK_BITS-1:0]                      wcam_blk [WR_CAM_ENTRIES_IE];
wire    [PAGE_BITS-1:0]                     wcam_row [WR_CAM_ENTRIES_IE];
wire    [BG_BANK_BITS-1:0]                  wcam_bank [WR_CAM_ENTRIES_IE];
wire    [RANK_BITS-1:0]                     wcam_rank [WR_CAM_ENTRIES_IE];
wire    [MWR_BITS-1:0]                      wcam_mwr [WR_CAM_ENTRIES_IE];
wire    [PARTIAL_WR_BITS-1:0]               wcam_pw_word_valid [WR_CAM_ENTRIES_IE];
wire    [PARTIAL_WR_BITS_LOG2-1:0]          wcam_pw_ram_raddr [WR_CAM_ENTRIES_IE];
wire    [PW_WORD_CNT_WD_MAX-1:0]            wcam_pw_num_beats_m1 [WR_CAM_ENTRIES_IE];
wire    [PW_WORD_CNT_WD_MAX-1:0]            wcam_pw_num_cols_m1 [WR_CAM_ENTRIES_IE];
wire    [OTHER_WR_ENTRY_BITS-1:0]           wcam_other [WR_CAM_ENTRIES_IE];
wire                                        wcam_rd_data_pending [WR_CAM_ENTRIES_IE];
wire                                        wcam_wr_data_pending [WR_CAM_ENTRIES_IE];
wire    [BT_BITS-1:0]                       wcam_ie_bt [WR_CAM_ENTRIES_IE];
wire    [IE_WR_TYPE_BITS-1:0]               wcam_ie_wr_type [WR_CAM_ENTRIES_IE];
wire    [IE_BURST_NUM_BITS-1:0]             wcam_ie_blk_burst_num [WR_CAM_ENTRIES_IE];
wire    [IE_UNIQ_BLK_BITS-1:0]              wcam_ie_ecc_uniq_block_num [WR_CAM_ENTRIES_IE];

genvar entry_idx;
generate
    for (entry_idx=0; entry_idx<WR_CAM_ENTRIES_IE; entry_idx++) begin
        assign wcam_valid[entry_idx]            = u0[entry_idx].entry.r_entry[u0[entry_idx].entry.ENTRY_VALID];
        assign wcam_autopre[entry_idx]          = i_entry[entry_idx*ENTRY_BITS+ENTRY_AUTOPRE_LSB +: ENTRY_AUTOPRE_BITS];
        assign wcam_hi_pri[entry_idx]           = i_entry[entry_idx*ENTRY_BITS+ENTRY_HI_PRI_LSB +: 2];
        assign wcam_vpw_lat[entry_idx]          = i_entry[entry_idx*ENTRY_BITS+ENTRY_VPW_LAT_LSB +: WR_LATENCY_BITS];
        assign wcam_blk[entry_idx]              = i_entry[entry_idx*ENTRY_BITS+ENTRY_BLK_LSB +: BLK_BITS];
        assign wcam_row[entry_idx]              = i_entry[entry_idx*ENTRY_BITS+ENTRY_ROW_LSB +: PAGE_BITS];
        assign wcam_bank[entry_idx]             = i_entry[entry_idx*ENTRY_BITS+ENTRY_BANK_LSB +: BG_BANK_BITS];
        assign wcam_rank[entry_idx]             = i_entry[entry_idx*ENTRY_BITS+ENTRY_RANK_LSB +: RANK_BITS];
        assign wcam_mwr[entry_idx]              = i_entry[entry_idx*ENTRY_BITS+ENTRY_MWR_LSB +: MWR_BITS];
        assign wcam_pw_word_valid[entry_idx]    = i_entry[entry_idx*ENTRY_BITS+ENTRY_PW_WORD_VALID_LSB +: PARTIAL_WR_BITS];
        assign wcam_pw_ram_raddr[entry_idx]     = i_entry[entry_idx*ENTRY_BITS+ENTRY_PW_RAM_RADDR_LSB +: PARTIAL_WR_BITS_LOG2];
        assign wcam_pw_num_beats_m1[entry_idx]  = i_entry[entry_idx*ENTRY_BITS+ENTRY_PW_NUM_BEATS_M1_LSB +: PW_WORD_CNT_WD_MAX];
        assign wcam_pw_num_cols_m1[entry_idx]   = i_entry[entry_idx*ENTRY_BITS+ENTRY_PW_NUM_COLS_M1_LSB +: PW_WORD_CNT_WD_MAX];
        assign wcam_other[entry_idx]            = i_entry[entry_idx*ENTRY_BITS+ENTRY_OTHER_LSB +: OTHER_WR_ENTRY_BITS];
        assign wcam_rd_data_pending[entry_idx]  = u0[entry_idx].entry.r_entry[u0[entry_idx].entry.ENTRY_RD_DATA_PENDING];
        assign wcam_wr_data_pending[entry_idx]  = u0[entry_idx].entry.r_entry[u0[entry_idx].entry.ENTRY_WR_DATA_PENDING];
        assign wcam_ie_bt [entry_idx]                    = i_entry[entry_idx*ENTRY_BITS+ENTRY_IE_BT_LSB +: BT_BITS];
        assign wcam_ie_wr_type [entry_idx]               = i_entry[entry_idx*ENTRY_BITS+ENTRY_IE_WR_TYPE_LSB +: IE_WR_TYPE_BITS];
        assign wcam_ie_blk_burst_num [entry_idx]         = i_entry[entry_idx*ENTRY_BITS+ENTRY_IE_BURST_NUM_LSB +: IE_BURST_NUM_BITS];
        assign wcam_ie_ecc_uniq_block_num [entry_idx]    = i_entry[entry_idx*ENTRY_BITS+ENTRY_IE_UNIQ_BLK_LSB +: IE_UNIQ_BLK_BITS];
    end
endgenerate


//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON
// disable coverage collection as this is a check in SVA only        
// VCS coverage off


wire  [RANKBANK_BITS-1:0] ts_bank_num4rdwr;
wire                      bank_alloc;
    assign  ts_bank_num4rdwr = ts_bsm_num4rdwr;
    assign  bank_alloc       = 1'b1;

wire any_wrecc_btt;
assign any_wrecc_btt =  |(te_wr_entry_ie_btt & te_entry_valid);

reg [NUM_TOTAL_BANKS-1:0] wrecc_btt_per_bank ;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
   integer wr_entry;
  if (~core_ddrc_rstn) begin
    wrecc_btt_per_bank <= {NUM_TOTAL_BANKS{1'b0}}; 
  end else begin
    for(wr_entry=0; wr_entry<WR_CAM_ENTRIES_IE; wr_entry=wr_entry+1) begin : wrecc_entry_gen
      if( i_del_en[wr_entry] && (te_wr_entry_ie_btt[wr_entry] && te_entry_valid[wr_entry]) ) begin
        wrecc_btt_per_bank[i_entry[wr_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b0;
      end else if(te_wr_entry_ie_btt[wr_entry] & (~i_del_en[wr_entry]) & te_entry_valid[wr_entry]) begin
        wrecc_btt_per_bank[i_entry[wr_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b1;
      end
    end
  end
end


// selecting the priority bits from the entry of the read commands that is scheduled
wire [1:0] pri_of_wr_op_cmd = {i_entry_out_pri[te_wr_entry*2+1],
                               i_entry_out_pri[te_wr_entry*2]  };
// Assertion for ex-VPW - when non-expiredVPW/NPW executed to expired-VPW bank
reg [NUM_TOTAL_BANKS-1:0] expired_vpw_per_bank ;
reg [NUM_TOTAL_BANKS-1:0] xvpw_serviced_per_bank ;
reg [15:0] num_of_non_vpw_serviced_per_bank[NUM_TOTAL_BANKS-1:0];


integer wr_entry;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    expired_vpw_per_bank <= {NUM_TOTAL_BANKS{1'b0}}; 
  end else begin
    for(wr_entry=0; wr_entry<WR_CAM_ENTRIES_IE; wr_entry=wr_entry+1) begin : wr_entry_gen
      if( i_del_en[wr_entry] && (i_entry_out_pri[wr_entry*2+:2]==CMD_PRI_XVPW) ) begin
        expired_vpw_per_bank[i_entry[wr_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b0;
      end else if(te_vpw_valid[wr_entry] & (~i_del_en[wr_entry]) & i_entry_vpw_timed_out[wr_entry]) begin
        expired_vpw_per_bank[i_entry[wr_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b1;
      end
    end
  end
end


// Set flag when expired-vpr serviced for a given bank and there are still expired-vpr present in the CAM for same bank
// Calculate number of non-xvpr serviced for a given bank when expired-vpr present for that bank
integer wbank;

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    for(wbank=0; wbank<NUM_TOTAL_BANKS; wbank=wbank+1) begin
      xvpw_serviced_per_bank[wbank]           <= 1'b0; 
      num_of_non_vpw_serviced_per_bank[wbank] <= {16{1'b0}};
    end
  end else begin
    for(wbank=0; wbank<NUM_TOTAL_BANKS; wbank=wbank+1) begin
      if(expired_vpw_per_bank[wbank] && i_ts_op_is_wr && pri_of_wr_op_cmd == CMD_PRI_XVPW && ts_bank_num4rdwr==wbank) begin 
         xvpw_serviced_per_bank[wbank]           <= 1'b1;
         num_of_non_vpw_serviced_per_bank[wbank] <= 16'h0;
      end else if (expired_vpw_per_bank[wbank] && i_ts_op_is_wr && pri_of_wr_op_cmd != CMD_PRI_XVPW && ts_bank_num4rdwr==wbank) begin
         num_of_non_vpw_serviced_per_bank[wbank] <= num_of_non_vpw_serviced_per_bank[wbank] + 1'b1;
      end else if (~expired_vpw_per_bank[wbank]) begin
         xvpw_serviced_per_bank[wbank]           <= 1'b0;
         num_of_non_vpw_serviced_per_bank[wbank] <= 16'h0;
      end
    end
  end
end

property p_non_expired_vpw_scheduled_for_expired_vpw_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn | (~dh_te_dis_wc)) 
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num)
        && expired_vpw_per_bank[bank_num] 
        && ( (te_mr_ie_wr_type!=`IE_WR_TYPE_WE_BW) || (~te_page_hit[te_wr_entry]) ) // WR ECC page-hit commands get serviced ahead of ex-VPWs
        && (xvpw_serviced_per_bank[bank_num] || (~xvpw_serviced_per_bank[bank_num] && num_of_non_vpw_serviced_per_bank[bank_num]>0))
      ) |-> (pri_of_wr_op_cmd == CMD_PRI_XVPW);
endproperty

genvar wr_bank;
generate 
for(wr_bank=0; wr_bank<NUM_TOTAL_BANKS; wr_bank=wr_bank+1) begin : a_non_xvpw_sch_wr_bank_gen
  a_non_expired_vpw_scheduled_for_expired_vpw_bank : assert property (p_non_expired_vpw_scheduled_for_expired_vpw_bank(wr_bank))
  else $display("[%t][%m] ERROR: Non-expired VPW command is scheduled when there are expired-vpw for bank =%0d ", $time,wr_bank);
end
endgenerate



// Calculation for non-expired VPW scheduled when expired-VPW present inside CAM

reg [15:0] num_of_non_vpw_cmds_sched_w_exp_vpw_on; // max num of banks in a system is in ddr4 case
reg [15:0] total_num_of_non_xvpw_sched_w_exp_vpw_on; // total num of non-ex-vpw cmds executed when ex-vpw present in CAM
reg [15:0] max_num_of_non_xvpw_sched_w_exp_vpw_on;   // max value of num of non-ex-vpw cmds executed when ex-vpw present in CAM

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    num_of_non_vpw_cmds_sched_w_exp_vpw_on   <= 16'h0;
    max_num_of_non_xvpw_sched_w_exp_vpw_on   <= 16'h0;
    total_num_of_non_xvpw_sched_w_exp_vpw_on <= 16'h0;
  end else begin
    if(any_vpw_timed_out & i_ts_op_is_wr & |te_vpw_valid) begin
      if(pri_of_wr_op_cmd == CMD_PRI_XVPW) begin // if expired-VPW command executed with any_vpw_timed_out high, then reset the counter
        // Check max value of non_xvpw with current value of non_xvpw
        if(max_num_of_non_xvpw_sched_w_exp_vpw_on<num_of_non_vpw_cmds_sched_w_exp_vpw_on) begin
          max_num_of_non_xvpw_sched_w_exp_vpw_on <= num_of_non_vpw_cmds_sched_w_exp_vpw_on;
        end
        num_of_non_vpw_cmds_sched_w_exp_vpw_on <= 16'h0;
      end else begin // if non-VPW commands executed with any_vpw_timed_out high, then increment the counter
        num_of_non_vpw_cmds_sched_w_exp_vpw_on   <= num_of_non_vpw_cmds_sched_w_exp_vpw_on + 1'b1;
        total_num_of_non_xvpw_sched_w_exp_vpw_on <= total_num_of_non_xvpw_sched_w_exp_vpw_on + 1'b1;
      end
    end else if(i_ts_op_is_wr) begin
      num_of_non_vpw_cmds_sched_w_exp_vpw_on <= 16'h0;
    end
  end
end

// Assertion to check Collided write command to a given bank get serviced ahead of other
// commands to that bank
// Collided entry present for a given bank
// te_flush_started is needed for inline ECC as te_wr_col_entry is don't care when te_flush_started==0.

reg [NUM_TOTAL_BANKS-1:0] entry_collided_per_bank ;
reg [WR_CAM_ENTRIES_IE-1:0] collided_cmd_per_entry;
reg te_flush_due_rd_r;
reg te_flush_due_wr_r;
integer w_entry;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_flush_due_rd_r       <= 1'b0;
    te_flush_due_wr_r       <= 1'b0;
    entry_collided_per_bank <= {NUM_TOTAL_BANKS{1'b0}}; 
    collided_cmd_per_entry  <= {WR_CAM_ENTRIES_IE{1'b0}};        
  end else begin
    te_flush_due_rd_r       <= te_flush_due_rd;
    te_flush_due_wr_r       <= te_flush_due_wr;
    for(w_entry=0; w_entry<WR_CAM_ENTRIES_IE; w_entry=w_entry+1) begin : wr_collided_entry_gen
      if(i_del_en[w_entry] & collided_cmd_per_entry[w_entry]
        ) begin
        entry_collided_per_bank[i_entry[w_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b0 ;
        collided_cmd_per_entry[w_entry] <= 1'b0;
      end else if( (((i_del_en[w_entry]|| (te_flush_due_wr_r&&te_yy_wr_combine)) 
                    && ((te_wr_col_entry==w_entry))
)

                    )
                    && entry_collided_per_bank[i_entry[w_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]]) begin
        entry_collided_per_bank[i_entry[w_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b0;
        collided_cmd_per_entry[w_entry] <= 1'b0;
      end else if(te_entry_valid[w_entry] && (~i_del_en[w_entry]) && 
                  (te_flush_due_rd_r && (~(te_flush_due_wr_r&&te_yy_wr_combine)))  
        && (te_flush_started)
        && ((te_wr_col_entry==w_entry))) begin
        entry_collided_per_bank[i_entry[w_entry*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b1;
        collided_cmd_per_entry[w_entry] <= 1'b1;
      end
    end
  end
end
// Number of non-collided commands serviced ahead when collided command present inside CAM
reg [15:0] num_of_non_collided_wcmds_sched_w_collision;
reg [15:0] max_num_of_non_collided_wcmds_sched_w_collision;
reg [15:0] total_num_of_non_collided_wcmds_sched_w_collision;
reg [15:0] num_of_non_collided_cmds_serviced_per_bank[NUM_TOTAL_BANKS-1:0];
genvar w_bank;

generate
for(w_bank=0; w_bank<NUM_TOTAL_BANKS; w_bank=w_bank+1) begin : wr_num_non_col_rst_gen
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    num_of_non_collided_cmds_serviced_per_bank[w_bank] <= {16{1'b0}};
  end else begin
    if(wu_ih_flow_cntrl_req) begin // Temporary disabled assertion if wu_ih_flow_cntrl_req==1
       num_of_non_collided_cmds_serviced_per_bank[w_bank] <= 16'h0;
    end
    else if(entry_collided_per_bank[w_bank] && i_ts_op_is_wr 
            && ((te_wr_col_entry==te_wr_entry)) 
            && (ts_bank_num4rdwr==w_bank) && bank_alloc) begin 
       num_of_non_collided_cmds_serviced_per_bank[w_bank] <= 16'h0;
    end else if(expired_vpw_per_bank[w_bank] && i_ts_op_is_wr && (pri_of_wr_op_cmd==CMD_PRI_XVPW) && (ts_bank_num4rdwr==w_bank) && bank_alloc) begin 
       num_of_non_collided_cmds_serviced_per_bank[w_bank] <= 16'h0;
    end else if(wrecc_btt_per_bank[w_bank] && i_ts_op_is_wr && (ts_bank_num4rdwr==w_bank) && bank_alloc) begin 
       num_of_non_collided_cmds_serviced_per_bank[w_bank] <= 16'h0;
    end else if (entry_collided_per_bank[w_bank] && i_ts_op_is_wr 
                 && (te_wr_col_entry!=te_wr_entry) 
                 && (ts_bank_num4rdwr==w_bank) && bank_alloc) begin
       num_of_non_collided_cmds_serviced_per_bank[w_bank] <= num_of_non_collided_cmds_serviced_per_bank[w_bank] + 1'b1;
    end else if (~entry_collided_per_bank[w_bank]) begin
       num_of_non_collided_cmds_serviced_per_bank[w_bank] <= 16'h0;
    end
  end
end
end
endgenerate

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    num_of_non_collided_wcmds_sched_w_collision       <= 16'h0;
    max_num_of_non_collided_wcmds_sched_w_collision   <= 16'h0;
    total_num_of_non_collided_wcmds_sched_w_collision <= 16'h0;
  end else begin
    // Collision logic
    if((|entry_collided_per_bank) && i_ts_op_is_wr) begin
      if( te_wr_col_entry==te_wr_entry 
        || (pri_of_wr_op_cmd==CMD_PRI_XVPW) 
      ) begin
        if(max_num_of_non_collided_wcmds_sched_w_collision<num_of_non_collided_wcmds_sched_w_collision) begin
          max_num_of_non_collided_wcmds_sched_w_collision <= num_of_non_collided_wcmds_sched_w_collision;
        end
        num_of_non_collided_wcmds_sched_w_collision <= 16'h0;
      end else begin
        num_of_non_collided_wcmds_sched_w_collision <= num_of_non_collided_wcmds_sched_w_collision + 1'b1;
        total_num_of_non_collided_wcmds_sched_w_collision <= total_num_of_non_collided_wcmds_sched_w_collision + 1'b1;
      end
    end else if(i_ts_op_is_wr) begin
      num_of_non_collided_wcmds_sched_w_collision <= 16'h0;
    end
  end
end

reg [NUM_TOTAL_BANKS-1:0] entry_collided_iecc_blk_per_bank ;
reg [WR_CAM_ENTRIES_IE-1:0] collided_iecc_blk_per_entry;
reg [BT_BITS-1:0]           collided_iecc_bt_num_per_bank[NUM_TOTAL_BANKS-1:0];
integer wr_entry_ie, wrbank;

bit [NUM_TOTAL_BANKS-1:0] [WR_CAM_ENTRIES_IE-1:0] wcam_wr_d_n_valid_per_bank;
bit [NUM_TOTAL_BANKS-1:0] [WR_CAM_ENTRIES_IE-1:0] wr_ecc_cmd_pghit_per_bank;

bit [NO_OF_BT-1:0] [WR_CAM_ENTRIES_IE-1:0] ie_we_bw_entries_for_assertion;
bit [NO_OF_BT-1:0] [WR_CAM_ENTRIES_IE-1:0] ie_wd_e_entries_for_assertion;
reg [NO_OF_BT-1:0] [WR_CAM_ENTRIES_IE-1:0] ie_wd_e_entries_for_assertion_r;
reg [NO_OF_BT-1:0] [WR_CAM_ENTRIES_IE-1:0] ie_we_bw_vpw_entries_for_assertion;

bit [NO_OF_BT-1:0] [(2**IE_BURST_NUM_BITS)-1:0] ie_wd_e_burst_num_for_assertion;
reg [NO_OF_BT-1:0] [(2**IE_BURST_NUM_BITS)-1:0] ie_wd_e_burst_num_for_assertion_r;

// Array for assertion
genvar ie_bt_idx;
genvar ie_entry_idx;
genvar ie_burstnum_idx;
generate
for (ie_bt_idx=0;ie_bt_idx<NO_OF_BT;ie_bt_idx=ie_bt_idx+1) begin : IEBT_IDX

  for (ie_entry_idx=0;ie_entry_idx<WR_CAM_ENTRIES_IE;ie_entry_idx=ie_entry_idx+1) begin : IEENTRY_IDX

    always @(*) begin
      ie_we_bw_entries_for_assertion[ie_bt_idx][ie_entry_idx] = 1'b0;
      ie_wd_e_entries_for_assertion[ie_bt_idx][ie_entry_idx]  = 1'b0;
      if (wcam_ie_bt[ie_entry_idx] == ie_bt_idx & wcam_valid[ie_entry_idx]) begin
        if (wcam_ie_wr_type[ie_entry_idx]==`IE_WR_TYPE_WE_BW) begin
          ie_we_bw_entries_for_assertion[ie_bt_idx][ie_entry_idx] = 1'b1; // Loaded regardless of valid
        end
        if (wcam_ie_wr_type[ie_entry_idx]==`IE_WR_TYPE_WD_E) begin
          ie_wd_e_entries_for_assertion[ie_bt_idx][ie_entry_idx]  = 1'b1;
        end
      end
    end

    always@(posedge co_te_clk or negedge core_ddrc_rstn) begin
      if(~core_ddrc_rstn) begin
        ie_wd_e_entries_for_assertion_r[ie_bt_idx][ie_entry_idx] <= 1'b0;
      end else begin
        ie_wd_e_entries_for_assertion_r[ie_bt_idx][ie_entry_idx] <= ie_wd_e_entries_for_assertion[ie_bt_idx][ie_entry_idx];
      end
    end

    always@(posedge co_te_clk or negedge core_ddrc_rstn) begin
      if(~core_ddrc_rstn) begin
        ie_we_bw_vpw_entries_for_assertion[ie_bt_idx][ie_entry_idx] <= 1'b0;
      end else begin
        if(i_ts_op_is_wr & (te_mr_ie_bt == ie_bt_idx) & (te_mr_ie_wr_type==`IE_WR_TYPE_WD_E) & (pri_of_wr_op_cmd==CMD_PRI_XVPW) & (wcam_ie_wr_type[ie_entry_idx]==`IE_WR_TYPE_WE_BW))
          ie_we_bw_vpw_entries_for_assertion[ie_bt_idx][ie_entry_idx] <= 1'b1;
        else if(i_ts_op_is_wr & (te_mr_ie_bt == ie_bt_idx) & (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) & (te_wr_entry==ie_entry_idx) )
          ie_we_bw_vpw_entries_for_assertion[ie_bt_idx][ie_entry_idx] <= 1'b0;
      end
    end

  end

  for (ie_burstnum_idx=0;ie_burstnum_idx<(2**IE_BURST_NUM_BITS);ie_burstnum_idx=ie_burstnum_idx+1) begin : IEBURSTNUM_IDX
    always @(*) begin
      ie_wd_e_burst_num_for_assertion[ie_bt_idx][ie_burstnum_idx]  = 1'b0;
      if(i_ts_op_is_wr & (te_mr_ie_bt == ie_bt_idx) & (te_mr_ie_wr_type==`IE_WR_TYPE_WD_E) & (i_te_mr_ie_blk_burst_num==ie_burstnum_idx) ) begin
        ie_wd_e_burst_num_for_assertion[ie_bt_idx][ie_burstnum_idx]  = 1'b1;
      end else if( (|ie_we_bw_entries_for_assertion[ie_bt_idx]) & ie_wd_e_burst_num_for_assertion[ie_bt_idx][ie_burstnum_idx]) begin
        ie_wd_e_burst_num_for_assertion[ie_bt_idx][ie_burstnum_idx]  = 1'b1;
      end
    end

    always@(posedge co_te_clk or negedge core_ddrc_rstn) begin
      if(~core_ddrc_rstn) begin
        ie_wd_e_burst_num_for_assertion_r[ie_bt_idx][ie_burstnum_idx] <= 1'b0;
      end else begin
      //  if( (ts_op_is_wr & (te_mr_ie_bt == ie_bt_idx) & (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) & (&ie_wd_e_burst_num_for_assertion_r[ie_bt_idx]) ) 
      //     || (!(&ie_wd_e_burst_num_for_assertion_r[ie_bt_idx])) ) 
      begin
          ie_wd_e_burst_num_for_assertion_r[ie_bt_idx][ie_burstnum_idx] <= ie_wd_e_burst_num_for_assertion[ie_bt_idx][ie_burstnum_idx];
      end
      end
    end
  end

end


endgenerate    

property p_ie_we_bw_must_be_there_if_wd_e_is_there(bt);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      |(ie_wd_e_entries_for_assertion[bt]) |-> ##[1:2] (|ie_we_bw_entries_for_assertion[bt]); 
endproperty

property p_ie_a_bt_never_has_two_or_more_we_bw(bt);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ($countones(ie_we_bw_entries_for_assertion[bt])<2); 
endproperty

property p_ie_wr_ecc_cmd_serviced_ahead_of_wr_data_cmd_to_same_blk(bt_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      ( i_ts_op_is_wr && (te_mr_ie_bt==bt_num)
        && (|(ie_wd_e_entries_for_assertion_r[bt_num]))
        && (~te_ih_wr_retry || (te_wr_col_entry!=te_wr_entry)) // Colliding WR ECC entry has higher priority
       )  |-> (te_mr_ie_wr_type==`IE_WR_TYPE_WD_E || te_mr_ie_wr_type==`IE_WR_TYPE_WD_N) ;
endproperty

property p_ie_wr_ecc_entry_not_valid_when_all_wd_e_cmds_serviced_to_that_blk(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      (   wcam_valid[entry_num]
      && (wcam_ie_wr_type[entry_num]==`IE_WR_TYPE_WE_BW)
      && (!te_flush_due_wr_r) // consider collision case 
      && (!(|ie_wd_e_entries_for_assertion[te_mr_ie_bt]))
      && (&ie_wd_e_burst_num_for_assertion_r[wcam_ie_bt[entry_num]])
      )  |-> (wcam_rd_data_pending[entry_num]==1'b0) ;
endproperty

generate
for (ie_bt_idx=0;ie_bt_idx<NO_OF_BT;ie_bt_idx=ie_bt_idx+1) begin : IEBT_IDX2
  // Check that WE_BW for BT=X is there as long as WD_E for BT=X is there
  a_ie_we_bw_must_be_there_if_wd_e_is_there : assert property (p_ie_we_bw_must_be_there_if_wd_e_is_there(ie_bt_idx))
  else $display("[%t][%m] ERROR:[InlineECC] One WE_BW for BT=%d must be there in WR_CAM as WD_E is there", $time,ie_bt_idx);

  // Check that two or more WE_BW are never there for a BT 
  a_ie_a_bt_never_has_two_or_more_we_bw : assert property (p_ie_a_bt_never_has_two_or_more_we_bw(ie_bt_idx))
  else $display("[%t][%m] ERROR:[InlineECC] There are two or more WE_BW belongs to BT=%d", $time,ie_bt_idx);

  // Check that all WR DATA commands are serviced ahead of WR ECC command to that block
  a_ie_wr_ecc_cmd_serviced_ahead_of_wr_data_cmd_to_same_blk : assert property (p_ie_wr_ecc_cmd_serviced_ahead_of_wr_data_cmd_to_same_blk(ie_bt_idx))
  else $display("[%t][%m] ERROR:[InlineECC] Write ECC command is serviced when there are Write DATA commands present in the CAM for a block with BWT=%0d ", $time,ie_bt_idx);
end
endgenerate

generate
for (ie_entry_idx=0;ie_entry_idx<WR_CAM_ENTRIES_IE;ie_entry_idx=ie_entry_idx+1) begin : IEENTRY_IDX2
  // Check that WE_BW for ENTRY=X becomes valid once all WD commands to that block are serviced
  a_ie_wr_ecc_entry_not_valid_when_all_wd_e_cmds_serviced_to_that_blk : assert property (p_ie_wr_ecc_entry_not_valid_when_all_wd_e_cmds_serviced_to_that_blk(ie_entry_idx))
  else $display("[%t][%m] ERROR:[InlineECC] Write ECC entry=%0d is not valid when all Write DATA commands to that block are serviced for BWT=%0d ", $time,ie_entry_idx,wcam_ie_bt[ie_entry_idx]);
end
endgenerate

// Check that i_combine_match | i_combine_match_wecc is one hot or less
a_ie_combine_match_must_be_one_hot_or_less:
  assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
  ($countones(i_combine_match | i_combine_match_wecc)<2))
  else $error("[%t][%m] error: i_combine_match asserted more than one bit", $time);
        
// Check that if te_yy_wr_combine=1, i_same_addr_wr must be one hot
a_ie_combine_happens_with_block_address_collision:
  assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
  (te_yy_wr_combine |-> $countones(i_same_addr_wr)==1))
  else $error("[%t][%m] error: write combine happens with block address collision", $time);


genvar banknum,wrentry_num;
generate
for(wrentry_num=0; wrentry_num<WR_CAM_ENTRIES_IE; wrentry_num=wrentry_num+1) begin : wrentry_num_gen
  for(banknum=0;banknum<NUM_TOTAL_BANKS;banknum=banknum+1) begin : banknum_gen
    always @(*) begin
      wr_ecc_cmd_pghit_per_bank[banknum][wrentry_num]  = 1'b0;
      wcam_wr_d_n_valid_per_bank[banknum][wrentry_num] = 1'b0;
      if( (wcam_bank[wrentry_num]==banknum) & wcam_valid[wrentry_num] & (wcam_ie_wr_type[wrentry_num]!=`IE_WR_TYPE_WE_BW) ) begin
        wcam_wr_d_n_valid_per_bank[banknum][wrentry_num] = 1'b1;
      end
      if( (wcam_bank[wrentry_num]==banknum) & wcam_valid[wrentry_num] & (wcam_ie_wr_type[wrentry_num]==`IE_WR_TYPE_WE_BW) & (i_page_hit[wrentry_num])) begin
        wr_ecc_cmd_pghit_per_bank[banknum][wrentry_num] = 1'b1;
      end
    end
  end
end
endgenerate



// Generate entry number of collided WR IECC block 
// Generate per bank version of collied WR IECC block 
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    entry_collided_iecc_blk_per_bank <= {NUM_TOTAL_BANKS{1'b0}}; 
    collided_iecc_blk_per_entry      <= {WR_CAM_ENTRIES_IE{1'b0}};
    for(wrbank=0; wrbank<NUM_TOTAL_BANKS; wrbank=wrbank+1) begin : wr_ie_blk_collided_bank_gen
      collided_iecc_bt_num_per_bank[wrbank] <= {BT_BITS{1'b0}};
    end
  end else begin
    for(wr_entry_ie=0; wr_entry_ie<WR_CAM_ENTRIES_IE; wr_entry_ie=wr_entry_ie+1) begin : wr_ie_blk_collided_entry_gen



      if (i_ie_blk_addr_collision[wr_entry_ie] && i_collision && (~i_del_en[wr_entry_ie]) && (wcam_ie_wr_type[wr_entry_ie]==`IE_WR_TYPE_WE_BW))
        collided_iecc_blk_per_entry[wr_entry_ie] <= 1'b1;
      else if (collided_iecc_blk_per_entry[wr_entry_ie] && i_del_en[wr_entry_ie])
        collided_iecc_blk_per_entry[wr_entry_ie] <= 1'b0;

      if( (i_del_en[wr_entry_ie] ) && (collided_iecc_blk_per_entry[wr_entry_ie]) && entry_collided_iecc_blk_per_bank[i_entry[wr_entry_ie*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]]) begin
        entry_collided_iecc_blk_per_bank[i_entry[wr_entry_ie*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b0;
      end else if(te_entry_valid[wr_entry_ie] && (wcam_ie_wr_type[wr_entry_ie]==`IE_WR_TYPE_WE_BW) && (collided_iecc_blk_per_entry[wr_entry_ie]) && (~i_del_en[wr_entry_ie])) begin
        entry_collided_iecc_blk_per_bank[i_entry[wr_entry_ie*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= 1'b1;
        collided_iecc_bt_num_per_bank[i_entry[wr_entry_ie*ENTRY_BITS + ENTRY_BANK_LSB +: RANKBANK_BITS]] <= wcam_ie_bt[wr_entry_ie];
      end
    end

  end
end

reg [15:0] num_of_non_collided_iecc_bt_serviced_per_bank[NUM_TOTAL_BANKS-1:0];
integer bankwr;

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    for(bankwr=0; bankwr<NUM_TOTAL_BANKS; bankwr=bankwr+1) begin : wr_num_non_col_bt_rst_gen
      num_of_non_collided_iecc_bt_serviced_per_bank[bankwr] <= {16{1'b0}};
    end
  end else begin
    for(bankwr=0; bankwr<NUM_TOTAL_BANKS; bankwr=bankwr+1) begin : wr_num_non_col_bt_cmd_gen
      if(entry_collided_iecc_blk_per_bank[bankwr] && i_ts_op_is_wr && (te_mr_ie_bt==collided_iecc_bt_num_per_bank[bankwr]) && (ts_bank_num4rdwr==bankwr) && bank_alloc) begin 
         num_of_non_collided_iecc_bt_serviced_per_bank[bankwr] <= 16'h0;
      end else if (entry_collided_iecc_blk_per_bank[bankwr] && i_ts_op_is_wr
        && (pri_of_wr_op_cmd!=CMD_PRI_XVPW) 
        && (te_mr_ie_bt!=collided_iecc_bt_num_per_bank[bankwr]) && (ts_bank_num4rdwr==bankwr) && bank_alloc) begin
         num_of_non_collided_iecc_bt_serviced_per_bank[bankwr] <= num_of_non_collided_iecc_bt_serviced_per_bank[bankwr] + 1'b1;
      end else if (~entry_collided_iecc_blk_per_bank[bankwr]) begin
         num_of_non_collided_iecc_bt_serviced_per_bank[bankwr] <= 16'h0;
      end
    end
  end
end

property p_ie_non_collided_iecc_blk_wr_serviced_for_collided_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( (~te_wr_entry_ie_btt[te_wr_entry]) && (~$past(te_wr_entry_ie_btt[$past(te_wr_entry)]))) //the purpose to check if have btt in prevous cycle is because btt could be changed from 1 to 0 (dut to WRECC CAM is drain less than threshold), the state of NTT has one cycle delay.
        && ( (~te_wr_entry_ie_btt_stickey_sva[te_wr_entry]) && (~$past(te_wr_entry_ie_btt_stickey_sva[$past(te_wr_entry)]))) //Added sticky version of above, it is 1 once the entry becomes BTT=1 regardless of current BTT. This line is for Bugzilla 7730
        && (entry_collided_iecc_blk_per_bank[bank_num])
        && (~expired_vpw_per_bank[bank_num]) // No expired VPW
        && (~(ie_we_bw_vpw_entries_for_assertion[te_mr_ie_bt][te_wr_entry]) ) //expired-VPW's WR ECC command may get scheduled ahead 
        && (num_of_non_collided_iecc_bt_serviced_per_bank[bank_num]>0)
       )  |-> (te_mr_ie_bt==collided_iecc_bt_num_per_bank[bank_num]) ;
endproperty

property p_ie_wr_pgmiss_not_serviced_ahead_wr_ecc_pgmiss_when_no_btt_for_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( |wcam_wr_d_n_valid_per_bank[bank_num] )
        && ( !entry_collided_iecc_blk_per_bank[bank_num] )
        && ( !(|wr_ecc_cmd_pghit_per_bank[bank_num]) )
        && ( !te_wr_entry_ie_btt[te_wr_entry] )
       )  |-> (te_mr_ie_wr_type!=`IE_WR_TYPE_WE_BW) ;
endproperty


property p_ie_wr_ecc_pghit_with_btt_not_serviced_ahead_other_pgmiss_cmds_for_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( !entry_collided_per_bank[bank_num] ) 
        && ( |wr_ecc_cmd_pghit_per_bank[bank_num] )
        && ( !expired_vpw_per_bank[bank_num] )
        && ( te_wr_entry_ie_btt[te_wr_entry] )
       )  |-> (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) ;
endproperty

property p_ie_wr_ecc_pghit_not_serviced_ahead_other_cmds_for_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( !entry_collided_per_bank[bank_num] ) 
        && ( |wr_ecc_cmd_pghit_per_bank[bank_num] )
        && ( !expired_vpw_per_bank[bank_num] )
        && ( te_wr_entry_ie_btt[te_wr_entry] )
       )  |-> (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) ;
endproperty

property p_ie_wr_ecc_pgmiss_with_btt_not_serviced_ahead_other_pgmiss_cmd_for_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( !entry_collided_per_bank[bank_num] ) 
        && ( !(|wr_ecc_cmd_pghit_per_bank[bank_num]) )
        && ( !entry_collided_iecc_blk_per_bank[bank_num] )
        && ( !expired_vpw_per_bank[bank_num] )
        && ( te_wr_entry_ie_btt[te_wr_entry] )
       )  |-> (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) ;
endproperty

property p_ie_wr_ecc_not_serviced_next_when_all_wd_e_cmds_of_blk_done_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn)
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( !entry_collided_per_bank[bank_num] ) 
        && ( |wr_ecc_cmd_pghit_per_bank[bank_num] )
        && ( !expired_vpw_per_bank[bank_num] )
        && (!(|ie_wd_e_entries_for_assertion[te_mr_ie_bt]))
        && (&ie_wd_e_burst_num_for_assertion_r[te_mr_ie_bt])
       )  |-> (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) ;
endproperty

// Single HIF - 1 normal command to collided bank can be serviced ahead of collided command.
// Dual HIF - No normal command should be serviced ahead of collided command.
property p_non_collided_wr_serviced_for_collided_bank(bank_num);
@(posedge co_te_clk) disable iff (~core_ddrc_rstn ) 
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && (wu_ih_flow_cntrl_req==0) // temporarily check this only when wu_ih_flow_cntrl_req==0.
        && (~any_vpw_timed_out) // temporarily enable this check only if no expired-VPWs
        && (~any_wrecc_btt ) // temporarily enable this check only if no wrecc_btt 
        && (entry_collided_per_bank[bank_num] && (num_of_non_collided_cmds_serviced_per_bank[bank_num]> 1))
       )  |-> (te_wr_col_entry==te_wr_entry);
endproperty

// Check Expired-VPW get serviced ahead of collided entry
// disabled these 2 assertions for write combine because of RTL issue Bug 3628/Bug 3555comment#30
property p_collided_wr_serviced_for_non_collided_xvpw_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn | (~dh_te_dis_wc))
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( entry_collided_per_bank[bank_num] && expired_vpw_per_bank[bank_num]  )
        && (~i_entry_vpw_timed_out[te_wr_col_entry])
        && (~(te_wr_entry_ie_btt[te_wr_col_entry] & te_entry_valid[te_wr_col_entry]))  //the WRECC w/BTT is not colliding.
        && (num_of_non_vpw_serviced_per_bank[bank_num]>0)
       )  |-> (te_wr_col_entry!=te_wr_entry) ;
endproperty

reg [WR_CAM_ENTRIES_IE-1:0] te_vpw_valid_d2;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn)
      te_vpw_valid_d2 <= {WR_CAM_ENTRIES_IE{1'b0}};
   else
      te_vpw_valid_d2 <= te_vpw_valid_d;
end

property p_non_collided_wr_serviced_for_collided_xvpw_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn | (~dh_te_dis_wc) )
      ( i_ts_op_is_wr && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( entry_collided_per_bank[bank_num] && expired_vpw_per_bank[bank_num]  )
        && (i_entry_vpw_timed_out[te_wr_col_entry] && te_vpw_valid_d2[te_wr_col_entry]) //from expire to load_vp in NTT ,there are 2 cycles.
        && (~i_entry_vpw_timed_out[te_wr_entry])
        && (~(te_wr_entry_ie_btt[te_wr_entry] & te_entry_valid[te_wr_entry]))  //the scheduled entry is not WRECC w/BTT
        && ( (~te_wr_entry_ie_btt_stickey_sva[te_wr_entry]) && (~$past(te_wr_entry_ie_btt_stickey_sva[$past(te_wr_entry)]))) //Added sticky version of above, it is 1 once the entry becomes BTT=1 regardless of current BTT. This line is for Bugzilla 7730
        && (num_of_non_collided_cmds_serviced_per_bank[bank_num]>0)
       )  |-> (te_wr_col_entry==te_wr_entry) ;
endproperty


genvar bank_wr;
generate 
for(bank_wr=0; bank_wr<NUM_TOTAL_BANKS; bank_wr=bank_wr+1) begin : a_non_collided_serviced_bank_wr_gen
  a_non_collided_wr_serviced_for_collided_bank : assert property (p_non_collided_wr_serviced_for_collided_bank(bank_wr))
  else $display("[%t][%m] WARNING: Non-collided write command is serviced when there is collided write present in the CAM for bank=%0d ", $time,bank_wr);

  a_collided_wr_serviced_for_non_collided_xpvw_bank : assert property (p_collided_wr_serviced_for_non_collided_xvpw_bank(bank_wr))
  else $display("[%t][%m] ERROR: Collided write serviced when Non-collided XVPW command in the CAM for bank=%0d ", $time,bank_wr);

  a_non_collided_wr_serviced_for_collided_xpvw_bank : assert property (p_non_collided_wr_serviced_for_collided_xvpw_bank(bank_wr))
  else $display("[%t][%m] ERROR: Non-collided write serviced when Collided XVPW command in the CAM for bank=%0d ", $time,bank_wr);

cp_num_non_collided_cmds_serviced_per_bank:
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn) (num_of_non_collided_cmds_serviced_per_bank[bank_wr]> 2) )
    $display("[%t][%m] ERROR: Number of Non-collided commands scheduled when there is collided command for bank %0d present is greater than 1. Current Value is: %0d", $time, bank_wr,num_of_non_collided_cmds_serviced_per_bank[bank_wr]);

  //Check that WR ECC command for collided block get serviced ahead of non-collided commands to a given bank
  a_ie_non_collided_iecc_blk_wr_serviced_for_collided_bank : assert property (p_ie_non_collided_iecc_blk_wr_serviced_for_collided_bank(bank_wr))
  else $display("[%t][%m] ERROR:[Inline ECC] Non-collided write serviced when collided blk in the CAM for bank=%0d BT=%0d ", $time,bank_wr,te_mr_ie_bt);

  // Check that WR ECC pagehit with BTT get serviced ahead of other page miss commands to a given bank
  a_ie_wr_ecc_pghit_with_btt_not_serviced_ahead_other_pgmiss_cmds_for_bank : assert property (p_ie_wr_ecc_pghit_with_btt_not_serviced_ahead_other_pgmiss_cmds_for_bank(bank_wr))
  else $display("[%t][%m] ERROR:[Inline ECC] WR ECC pagehit command not serviced when BT is terminated for bank=%0d BT=%0d ", $time,bank_wr,te_mr_ie_bt);

  // Check that WR ECC pagehit with BTT get serviced ahead of other commands to a given bank
  a_ie_wr_ecc_pghit_with_btt_not_serviced_ahead_other_cmds_for_bank : assert property (p_ie_wr_ecc_pghit_not_serviced_ahead_other_cmds_for_bank(bank_wr))
  else $display("[%t][%m] ERROR:[Inline ECC] WR ECC pagehit command not serviced when BT is terminated for bank=%0d BT=%0d ", $time,bank_wr,te_mr_ie_bt);

  // Check that WR ECC pagemiss get serviced ahead of other page miss commands to a given bank
  a_ie_wr_pgmiss_not_serviced_ahead_wr_ecc_pgmiss_when_no_btt_for_bank : assert property (p_ie_wr_pgmiss_not_serviced_ahead_wr_ecc_pgmiss_when_no_btt_for_bank(bank_wr))
  else $display("[%t][%m] ERROR:[Inline ECC] WR DATA/NORMAL pagemiss command not serviced when WR ECC BT is not terminated for bank=%0d BT=%0d ", $time,bank_wr,te_mr_ie_bt);

  // Check that WR ECC pagemiss with BTT get serviced ahead of other commands to a given bank
  a_ie_wr_ecc_pgmiss_with_btt_not_serviced_ahead_when_btt_for_bank : assert property (p_ie_wr_ecc_pgmiss_with_btt_not_serviced_ahead_other_pgmiss_cmd_for_bank(bank_wr))
  else $display("[%t][%m] ERROR:[Inline ECC] WR ECC pagemiss command not serviced when BT is terminated for bank=%0d BT=%0d ", $time,bank_wr,te_mr_ie_bt);

  // Check that WR ECC get serviced when all WR DATA commands to that block are done for a given bank
  a_ie_wr_ecc_not_serviced_next_when_all_wd_e_cmds_of_blk_done_bank : assert property (p_ie_wr_ecc_not_serviced_next_when_all_wd_e_cmds_of_blk_done_bank(bank_wr))
  else $display("[%t][%m] ERROR:[Inline ECC] WR ECC command not serviced next when all WR DATA of that block are serviced for bank=%0d BT=%0d ", $time,bank_wr,te_mr_ie_bt);
end
endgenerate


cp_num_non_vpw_cmds_sched_gt_exp:
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn | reg_ddrc_opt_vprw_sch) (num_of_non_vpw_cmds_sched_w_exp_vpw_on > 16) )
    $display("[%t][%m] WARNING: Number of Non-VPW commands scheduled when there is an expired-VPW command present is greater than 16. Current Value is: %0d", $time, num_of_non_vpw_cmds_sched_w_exp_vpw_on);

cp_num_non_collided_wcmds_sched_gt_exp:
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn) (i_ts_op_is_wr && num_of_non_collided_wcmds_sched_w_collision > 16) )
    $display("[%t][%m] WARNING: Total number of Non-collided commands scheduled when there is collided command present is greater than 16. Current Value is: %0d", $time, num_of_non_collided_wcmds_sched_w_collision);

/*

 //-------------
 // Cover points associated with the expired VPW logic
 // Checking that the number of non-VPW commands that are executed before VPW is executed reaches
 //-------------

  wire vpw_read_w_expired_vpw_high = any_vpw_timed_out & ts_op_is_wr & (pri_of_wr_op_cmd == 2'b10);
    
// Coverage group
  covergroup cg_expired_vpw @(posedge co_te_clk);
    
    // number of non-vpw commands executed before executing a vpw cmd, when there are expired VPW commands
    cp_num_non_vpw_cmds : coverpoint ({vpw_read_w_expired_vpw_high, num_of_non_vpw_cmds_sched_w_exp_vpw_on}) iff(core_ddrc_rstn) {
                           bins vpw_0     = {9'b1_0000_0000};
                           bins vpw_1     = {9'b1_0000_0001};
                           bins vpw_2     = {9'b1_0000_0010};
                           bins vpw_3     = {9'b1_0000_0011};
                           bins vpw_4     = {9'b1_0000_0100};
                           bins vpw_5     = {9'b1_0000_0101};
                           bins vpw_6     = {9'b1_0000_0110};
                           bins vpw_7     = {9'b1_0000_0111};
                           bins vpw_8     = {9'b1_0000_1000};
                           bins vpw_9     = {9'b1_0000_1001};
                           bins vpw_10    = {9'b1_0000_1010};
                           bins vpw_11    = {9'b1_0000_1011};
                           bins vpw_12    = {9'b1_0000_1100};
                           bins vpw_13    = {9'b1_0000_1101};
                           bins vpw_14    = {9'b1_0000_1110};
                           bins vpw_15    = {9'b1_0000_1111};
                   illegal_bins vpw_ill   = {[9'h110:9'h1FF]};
    }

  endgroup

// Coverage group instantiation
  cg_expired_vpw cg_expired_vpw_inst = new;

*/
   

// note: following codes are commented out for bug 7584
// Check that auto-pre is issued for pageclose feature
// cover_wr_autopre_w_pageclose_check :
// cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (ts_op_is_wr && dh_te_pageclose && (dh_te_pageclose_timer==8'h00) && autopre_for_pageclose));


// wire  [ENTRY_AUTOPRE_BITS-1:0]        te_pi_wr_autopre_int;   // auto precharge bit
// generate
//  // mux out auto precharge bit for PI
//   for (bit_loc=ENTRY_AUTOPRE_LSB; bit_loc<=ENTRY_AUTOPRE_MSB; bit_loc=bit_loc+1)
//   begin : pi_autopre
//     te_wr_mux #(
//           .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
//           .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
//          ) pi_autopre_mux (
//                        .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
//                        .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
//                        .out_port  (te_pi_wr_autopre_int [bit_loc - ENTRY_AUTOPRE_LSB])
//                       );
//   end
// 
// endgenerate
  
// Check the propagation of cmd_autopre through NTT and TS by comparing the stored CAM flag 
// property p_cmd_autopre_mismatch;
//   @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
//     (ts_op_is_wr) |-> (ts_rdwr_cmd_autopre==te_pi_wr_autopre_int);
// endproperty 
// a_cmd_autopre_mismatch : assert property (p_cmd_autopre_mismatch) else 
//   $display("-> %0t ERROR: WR CAM cmd_autopre mismatch CAM value:%0d, OS value:%0d", $realtime,te_pi_wr_autopre_int,ts_rdwr_cmd_autopre);
   

// WR CAM delayed autopre update queue overflow
property p_delayed_autopre_update_overflow;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (delayed_autopre_update_wr) |-> (!delayed_autopre_update_ff);
  
endproperty 
//a_delayed_autopre_update_overflow : assert property (p_delayed_autopre_update_overflow) else 
//  $display("-> %0t ERROR: WR CAM delayed autopre update queue overflow !!", $realtime);


generate
  // ie_bt information for assertion
  for (bit_loc=ENTRY_IE_BT_LSB; bit_loc<=ENTRY_IE_BT_MSB; bit_loc=bit_loc+1)
  begin : mr_ie_bt
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
            ) mr_ie_bt_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (i_te_mr_ie_bt [bit_loc - ENTRY_IE_BT_LSB])
                      );
  end

  // ie_wr_type information for assertion
  for (bit_loc=ENTRY_IE_WR_TYPE_LSB; bit_loc<=ENTRY_IE_WR_TYPE_MSB; bit_loc=bit_loc+1)
  begin : mr_ie_wr_type
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
            ) te_mr_ie_wr_type_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (i_te_mr_ie_wr_type [bit_loc - ENTRY_IE_WR_TYPE_LSB])
                      );
  end

  // ie_blk_burst_num information for assertion
  for (bit_loc=ENTRY_IE_BURST_NUM_LSB; bit_loc<=ENTRY_IE_BURST_NUM_MSB; bit_loc=bit_loc+1)
  begin : mr_ie_blk_burst_num
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
            ) mr_ie_blk_burst_num_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (i_te_mr_ie_blk_burst_num [bit_loc - ENTRY_IE_BURST_NUM_LSB])
                      );
  end

  // ie_bt information for assertion
  for (bit_loc=ENTRY_ECCAP_LSB; bit_loc<=ENTRY_ECCAP_MSB; bit_loc=bit_loc+1)
  begin : mr_eccap
    te_wr_mux
     #(
          .ADDR_BITS   (WR_CAM_ADDR_BITS_IE),
          .NUM_ENTRIES (WR_CAM_ENTRIES_IE)
            ) mr_eccap_mux (
                       .in_port   (bit_entry [((bit_loc +1) * WR_CAM_ENTRIES_IE) -1: (bit_loc * WR_CAM_ENTRIES_IE)]),
                       .sel  (te_wr_entry [WR_CAM_ADDR_BITS_IE -1:0]),
                       .out_port  (i_te_mr_eccap[bit_loc - ENTRY_ECCAP_LSB])
                      );
  end
endgenerate

assign i_ie_wr_blk_addr_collision = i_ie_blk_addr_collision; // For coverpoint

property p_wr_is_not_allowed_after_act_for_nxt_cycle;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (~(r_ts_op_is_activate_for_rd & i_ts_op_is_wr)); 
endproperty

a_wr_is_not_allowed_after_act_for_nxt_cycle : assert property (p_wr_is_not_allowed_after_act_for_nxt_cycle) else 
  $display("-> %0t ERROR: WR is scheduled-out in next cycle of ACT for RD!!, this is prohibitted in this HW configuration", $realtime);



property p_wr_pghit_limit_check;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    ((i_ts_op_is_wr & i_entry_critical_per_bsm_early[ts_bsm_num4rdwr]) |-> ((te_entry_critical_early[WR_CAM_ENTRIES-1:0] & te_bank_hit[WR_CAM_ENTRIES-1:0]) == te_bank_hit[WR_CAM_ENTRIES-1:0])); 
endproperty

// When the bsm is expired in terms of page_hit limiter, te_entry_critical_early is asserted as same as bank_hit 
a_wr_pghit_limit_check : assert property (p_wr_pghit_limit_check) else 
  $display("-> %0t ERROR: When the bsm is expired in terms of page_hit limiter, te_entry_critical_early is asserted as same as bank_hit", $realtime);

property p_wr_critical_early_same_for_bank_hit;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    |(te_bank_hit[WR_CAM_ENTRIES-1:0] & te_entry_critical_early[WR_CAM_ENTRIES-1:0]) |-> te_bank_hit[WR_CAM_ENTRIES-1:0] == (te_bank_hit[WR_CAM_ENTRIES-1:0] & te_entry_critical_early[WR_CAM_ENTRIES-1:0]);
endproperty

// All the entries to this bank should keep same value for critical_early
a_wr_critical_early_same_for_bank_hit : assert property (p_wr_critical_early_same_for_bank_hit) else 
  $display("-> %0t ERROR:  te_entry_critical_early is not same among bank_hit entries", $realtime);

  
property p_cam_load_valid_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    |(i_load_en[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES] & ie_enable_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]) == 0;
endproperty

a_cam_load_valid_chk: assert property (p_cam_load_valid_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

property p_ie_unload_onehot_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    i_unload_ntt_ie |-> $onehot((ie_disable_entry_valid | i_combine_match) & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}} & ~i_del_en);
endproperty

a_ie_unload_onehot_chk: assert property (p_ie_unload_onehot_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

property p_ie_load_onehot_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    i_load_ntt_ie |-> $onehot(ie_enable_entry_valid);
endproperty

a_ie_load_onehot_chk: assert property (p_ie_load_onehot_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

property p_ie_load_avail_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    $countones(te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]) == WR_CAM_ENTRIES_IE - WR_CAM_ENTRIES - te_wrecc_entry_avail;
endproperty

a_ie_load_avail_chk: assert property (p_ie_load_avail_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

property p_ie_load_used_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    $countones(te_entry_loaded_sva[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES]) == te_wrecc_entry_loaded;
endproperty

a_ie_load_used_chk: assert property (p_ie_load_used_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

// Below assertions are used to check te_wrecc_entry_avail, the name formality and its function are related to A/B/C listed in teengine te_wrecc_entry_avail calculation comments. 
property p_wrecc_entry_nA_nB_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && ~(i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail);
endproperty

property p_wrecc_entry_nA_nB_C1_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && ~(i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    |(ie_disable_entry_valid & ~i_combine_match & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}}) |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 1;
endproperty

property p_wrecc_entry_nA_nB_C2_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && ~(i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    |(~ie_disable_entry_valid & i_combine_match & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}}) |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 1;
endproperty

property p_wrecc_entry_nA_B1_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    ~r_unload_ntt_ie_bt_reg_vld && ~r_unload_ntt_ie_bt_reg2_vld && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 1;
endproperty

property p_wrecc_entry_nA_B2_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    r_unload_ntt_ie_bt_reg_vld && (te_mr_ie_bt==r_unload_ntt_ie_bt_reg) && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail);
endproperty

property p_wrecc_entry_nA_B3_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    r_unload_ntt_ie_bt_reg_vld && (te_mr_ie_bt!=r_unload_ntt_ie_bt_reg) && ~r_unload_ntt_ie_bt_reg2_vld && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 1;
endproperty

property p_wrecc_entry_nA_B5_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    r_unload_ntt_ie_bt_reg2_vld && (te_mr_ie_bt!=r_unload_ntt_ie_bt_reg2) && ~r_unload_ntt_ie_bt_reg_vld && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 1;
endproperty

property p_wrecc_entry_nA_B6_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    r_unload_ntt_ie_bt_reg2_vld && (te_mr_ie_bt!=r_unload_ntt_ie_bt_reg2) && r_unload_ntt_ie_bt_reg_vld && (te_mr_ie_bt!=r_unload_ntt_ie_bt_reg) && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 1;
endproperty

property p_wrecc_entry_nA_B1_C1_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    ~r_unload_ntt_ie_bt_reg_vld && ~r_unload_ntt_ie_bt_reg2_vld &&
    |(ie_disable_entry_valid & ~i_combine_match & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}} & ~i_del_en) |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 2;
endproperty

property p_wrecc_entry_nA_B3_C1_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    r_unload_ntt_ie_bt_reg_vld && (te_mr_ie_bt!=r_unload_ntt_ie_bt_reg) && ~r_unload_ntt_ie_bt_reg2_vld &&
    |(ie_disable_entry_valid & ~i_combine_match & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}} & ~i_del_en) |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 2;
endproperty

property p_wrecc_entry_nA_B5_C1_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    ~i_load_ntt_ie && (i_ts_op_is_wr && (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW)) &&
    r_unload_ntt_ie_bt_reg2_vld && (te_mr_ie_bt!=r_unload_ntt_ie_bt_reg2) && ~r_unload_ntt_ie_bt_reg_vld &&
    |(ie_disable_entry_valid & ~i_combine_match & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}} & ~i_del_en) |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) + 2;
endproperty

property p_wrecc_entry_A_nB_nC_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    i_load_ntt_ie && ~i_unload_ntt_ie |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail) - 1;
endproperty

property p_wrecc_entry_A_nB_C1_chk;
  @(posedge co_te_clk) disable iff(~core_ddrc_rstn)
    i_load_ntt_ie && |(ie_disable_entry_valid & ~i_combine_match & {te_entry_valid[WR_CAM_ENTRIES_IE-1:WR_CAM_ENTRIES],{WR_CAM_ENTRIES{1'b0}}}) |->
      ##1 te_wrecc_entry_avail == $past(te_wrecc_entry_avail);
endproperty

a_wrecc_entry_nA_nB_nC_chk: assert property (p_wrecc_entry_nA_nB_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_nB_C1_chk: assert property (p_wrecc_entry_nA_nB_C1_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_nB_C2_chk: assert property (p_wrecc_entry_nA_nB_C2_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B1_nC_chk: assert property (p_wrecc_entry_nA_B1_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B2_nC_chk: assert property (p_wrecc_entry_nA_B2_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B3_nC_chk: assert property (p_wrecc_entry_nA_B3_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B5_nC_chk: assert property (p_wrecc_entry_nA_B5_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B6_nC_chk: assert property (p_wrecc_entry_nA_B6_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B1_C1_chk: assert property (p_wrecc_entry_nA_B1_C1_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B3_C1_chk: assert property (p_wrecc_entry_nA_B3_C1_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_nA_B5_C1_chk: assert property (p_wrecc_entry_nA_B5_C1_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_A_nB_nC_chk: assert property (p_wrecc_entry_A_nB_nC_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);

a_wrecc_entry_A_nB_C1_chk: assert property (p_wrecc_entry_A_nB_C1_chk)
  else $error("Inline SVA [%t][%m] FAILED", $time);


// For intelligent Autopre 
property p_lpddr5_act_wr_check;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (((ts_op_is_activate | be_op_is_activate_bypass_int) & i_ts_op_is_wr) |=> (~ts_op_is_activate & ~be_op_is_activate_bypass_int & ~i_ts_op_is_wr));
endproperty

a_lpddr5_act_wr_check : assert property (p_lpddr5_act_wr_check) else 
  $display("-> %0t ERROR: LPDDR5: When ACT and WR are issued on a cycle, ACT or WR is not allowd in the next cycle", $realtime);



// VCS coverage on
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS


endmodule // te_wr_cam
