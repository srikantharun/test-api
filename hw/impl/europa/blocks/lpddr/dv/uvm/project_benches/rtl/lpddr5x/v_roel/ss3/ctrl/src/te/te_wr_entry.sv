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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_wr_entry.sv#6 $
// -------------------------------------------------------------------------
// Description:
//
// 1. entry contents of the write CAM
// 2. returns participation and page hit on cam search
// 3. collision detection
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_wr_entry #(
    //---------------------------- PARAMETERS --------------------------------------
    // bit widths; should be overridden from read CAM
     parameter   IE_WR_ECC_ENTRY           = 1'b0 // 1 means this entry is dedicated for WR ECC Entry   
    ,parameter   RANK_BITS                 = `UMCTL2_LRANK_BITS
    ,parameter   BG_BITS                   = `MEMC_BG_BITS
    ,parameter   BANK_BITS                 = `MEMC_BANK_BITS
    ,parameter   BG_BANK_BITS              = `MEMC_BG_BANK_BITS
    ,parameter   RANKBANK_BITS             = RANK_BITS + BG_BANK_BITS
    ,parameter   PAGE_BITS                 = `MEMC_PAGE_BITS
    ,parameter   BLK_BITS                  = 13
    ,parameter   BSM_BITS                  = `UMCTL2_BSM_BITS
    ,parameter   NUM_TOTAL_BSMS            = 1 << BSM_BITS
    ,parameter   OTHER_ENTRY_BITS          = 1
    ,parameter   HI_PRI_BITS               = 2
    ,parameter   BT_BITS                   = `MEMC_BLK_TOKEN_BITS         // override
    ,parameter   NO_OF_BT                  = 1 // override
    ,parameter   IE_WR_TYPE_BITS           = 2
    ,parameter   IE_RD_TYPE_BITS           = 2
    ,parameter   IE_BURST_NUM_BITS         = 3
    ,parameter   IE_UNIQ_BLK_BITS          = 4
    ,parameter   IE_UNIQ_BLK_LSB           = 3
    ,parameter   ECCAP_BITS                = 1
    ,parameter   DDR4_COL3_BITS            = 1
    ,parameter   LP_COL4_BITS              = 1
    ,parameter   WORD_BITS                 = `MEMC_WORD_BITS
    ,parameter   RETRY_WR_BITS             = 1
    ,parameter   ENTRY_RETRY_TIMES_WIDTH   = 4
    ,parameter   ENTRY_AUTOPRE_BITS        = 1
    ,parameter   HIF_KEYID_WIDTH           = `DDRCTL_HIF_KEYID_WIDTH
    // fields of entry
    ,parameter   PARTIAL_WR_BITS           = `UMCTL2_PARTIAL_WR_BITS      // bits for PARTIAL_WR logic
    ,parameter   PARTIAL_WR_BITS_LOG2      = `log2(PARTIAL_WR_BITS)        // bits for PARTIAL_WR logic
    ,parameter   PW_WORD_CNT_WD_MAX        = 2
    ,parameter   WR_LATENCY_BITS           = `UMCTL2_XPI_WQOS_TW
    ,parameter   PW_BC_SEL_BITS            = 3
    ,parameter   MWR_BITS                  = 1
    // write command priority encoding
    ,parameter   CMD_PRI_NPW               = `MEMC_CMD_PRI_NPW
    ,parameter   CMD_PRI_VPW               = `MEMC_CMD_PRI_VPW
    ,parameter   CMD_PRI_RSVD              = `MEMC_CMD_PRI_RSVD
    ,parameter   CMD_PRI_XVPW              = `MEMC_CMD_PRI_XVPW
    // Entry Fields (Not override)
    ,parameter  ENTRY_VALID                = 0
    ,parameter  ENTRY_AUTOPRE_LSB          = 1
    ,parameter  ENTRY_AUTOPRE_MSB          = ENTRY_AUTOPRE_LSB+ENTRY_AUTOPRE_BITS - 1
    ,parameter  ENTRY_HI_PRI_LSB           = ENTRY_AUTOPRE_MSB+1
    ,parameter  ENTRY_HI_PRI_MSB           = ENTRY_HI_PRI_LSB + HI_PRI_BITS - 1
    ,parameter  ENTRY_VPW_LAT_LSB          = ENTRY_HI_PRI_MSB + 1
    ,parameter  ENTRY_VPW_LAT_MSB          = ENTRY_VPW_LAT_LSB + WR_LATENCY_BITS - 1
    ,parameter  ENTRY_BLK_LSB              = ENTRY_VPW_LAT_MSB + 1
    ,parameter  ENTRY_BLK_MSB              = ENTRY_BLK_LSB + BLK_BITS - 1
    ,parameter  ENTRY_ROW_LSB              = ENTRY_BLK_MSB + 1
    ,parameter  ENTRY_ROW_MSB              = ENTRY_ROW_LSB + PAGE_BITS - 1
    ,parameter  ENTRY_BANK_LSB             = ENTRY_ROW_MSB + 1
    ,parameter  ENTRY_BANK_MSB             = ENTRY_BANK_LSB + BG_BANK_BITS - 1
    ,parameter  ENTRY_RANK_LSB             = ENTRY_BANK_MSB + 1
    ,parameter  ENTRY_RANK_MSB             = ENTRY_RANK_LSB + RANK_BITS - 1
    ,parameter  ENTRY_MWR_LSB              = ENTRY_RANK_MSB + 1 
    ,parameter  ENTRY_MWR_MSB              = ENTRY_MWR_LSB + MWR_BITS - 1
    ,parameter  ENTRY_PW_WORD_VALID_LSB    = ENTRY_MWR_MSB + 1
    ,parameter  ENTRY_PW_WORD_VALID_MSB    = ENTRY_PW_WORD_VALID_LSB + PARTIAL_WR_BITS - 1
    ,parameter  ENTRY_PW_BC_SEL_LSB        = ENTRY_PW_WORD_VALID_MSB + 1
    ,parameter  ENTRY_PW_BC_SEL_MSB        = ENTRY_PW_BC_SEL_LSB + PW_BC_SEL_BITS - 1 
    ,parameter  ENTRY_PW_RAM_RADDR_LSB     = ENTRY_PW_BC_SEL_MSB + 1
    ,parameter  ENTRY_PW_RAM_RADDR_MSB     = ENTRY_PW_RAM_RADDR_LSB + PARTIAL_WR_BITS_LOG2 - 1
    ,parameter  ENTRY_PW_NUM_BEATS_M1_LSB  = ENTRY_PW_RAM_RADDR_MSB + 1
    ,parameter  ENTRY_PW_NUM_BEATS_M1_MSB  = ENTRY_PW_NUM_BEATS_M1_LSB + PW_WORD_CNT_WD_MAX - 1 
    ,parameter  ENTRY_PW_NUM_COLS_M1_LSB   = ENTRY_PW_NUM_BEATS_M1_MSB + 1
    ,parameter  ENTRY_PW_NUM_COLS_M1_MSB   = ENTRY_PW_NUM_COLS_M1_LSB + PW_WORD_CNT_WD_MAX - 1 
    ,parameter  ENTRY_IE_BT_LSB            = ENTRY_PW_NUM_COLS_M1_MSB + 1
    ,parameter  ENTRY_IE_BT_MSB            = ENTRY_IE_BT_LSB + BT_BITS - 1
    ,parameter  ENTRY_IE_WR_TYPE_LSB       = ENTRY_IE_BT_MSB + 1
    ,parameter  ENTRY_IE_WR_TYPE_MSB       = ENTRY_IE_WR_TYPE_LSB + IE_WR_TYPE_BITS - 1
    ,parameter  ENTRY_IE_BURST_NUM_LSB     = ENTRY_IE_WR_TYPE_MSB + 1
    ,parameter  ENTRY_IE_BURST_NUM_MSB     = ENTRY_IE_BURST_NUM_LSB + IE_BURST_NUM_BITS - 1
    ,parameter  ENTRY_IE_UNIQ_BLK_LSB      = ENTRY_IE_BURST_NUM_MSB + 1
    ,parameter  ENTRY_IE_UNIQ_BLK_MSB      = ENTRY_IE_UNIQ_BLK_LSB + IE_UNIQ_BLK_BITS - 1
    ,parameter  ENTRY_ECCAP_LSB            = ENTRY_IE_UNIQ_BLK_MSB + 1
    ,parameter  ENTRY_ECCAP_MSB            = ENTRY_ECCAP_LSB + ECCAP_BITS - 1
    ,parameter  ENTRY_RETRY_WR_LSB         = ENTRY_ECCAP_MSB + 1
    ,parameter  ENTRY_RETRY_WR_MSB         = ENTRY_RETRY_WR_LSB + RETRY_WR_BITS - 1
    ,parameter  ENTRY_RETRY_TIMES_LSB      = ENTRY_RETRY_WR_MSB + 1
    ,parameter  ENTRY_RETRY_TIMES_MSB      = ENTRY_RETRY_TIMES_LSB + ENTRY_RETRY_TIMES_WIDTH -1 
    ,parameter  ENTRY_DWORD_LSB            = ENTRY_RETRY_TIMES_MSB + 1
    ,parameter  ENTRY_DWORD_MSB            = ENTRY_DWORD_LSB + WORD_BITS - 1
    ,parameter  ENTRY_DDR4_COL3_LSB        = ENTRY_DWORD_MSB + 1
    ,parameter  ENTRY_DDR4_COL3_MSB        = ENTRY_DDR4_COL3_LSB + DDR4_COL3_BITS - 1
    ,parameter  ENTRY_LP_COL4_LSB          = ENTRY_DDR4_COL3_MSB + 1
    ,parameter  ENTRY_LP_COL4_MSB          = ENTRY_LP_COL4_LSB + LP_COL4_BITS - 1
    ,parameter  ENTRY_OTHER_LSB            = ENTRY_LP_COL4_MSB + 1
    ,parameter  ENTRY_OTHER_MSB            = ENTRY_OTHER_LSB + OTHER_ENTRY_BITS - 1
    ,parameter  ENTRY_RD_DATA_PENDING      = ENTRY_OTHER_MSB + 1
    ,parameter  ENTRY_WR_DATA_PENDING      = ENTRY_RD_DATA_PENDING + 1
    ,parameter  ENTRY_BITS                 = ENTRY_WR_DATA_PENDING + 1

    )
    (
    //---------------------------- INPUTS AND OUTPUTS ------------------------------
     input                                    core_ddrc_rstn                    // reset
    ,input                                    co_te_clk                         // main clock
    ,input                                    ddrc_cg_en                        // clock gate enable
    ,input  [RANK_BITS-1:0]                   ih_te_wr_rank_num                 // rank number
    ,input  [BG_BANK_BITS-1:0]                ih_te_wr_bg_bank_num              // bank number
    ,input  [PAGE_BITS-1:0]                   ih_te_wr_page_num                 // page number
    ,input  [BLK_BITS-1:0]                    ih_te_wr_block_num                // block number
    ,input                                    ih_te_wr_autopre                  // auto precharege bit
    ,input  [OTHER_ENTRY_BITS-1:0]            ih_te_wr_other_fields             // starting Dword location
    ,input  [PAGE_BITS-1:0]                   r_ts_act_page                     // Row address of the activated page
    ,input  [1:0]                             ih_te_hi_pri                      // priority of the incoming command. 00 - NPW, 01 - VPW, 10,11 - reserved
    ,input  [WR_LATENCY_BITS-1:0]             ih_te_wr_latency                  // wr_latency input from IH module
    ,input  [BT_BITS-1:0]                     ih_te_ie_bt
    ,input  [IE_WR_TYPE_BITS-1:0]             ih_te_ie_wr_type
    ,input  [IE_RD_TYPE_BITS-1:0]             ih_te_ie_rd_type
    ,input  [IE_BURST_NUM_BITS-1:0]           ih_te_ie_blk_burst_num
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL assertion and/or in generate block.
    ,input  [NO_OF_BT-1:0]                    ih_te_ie_btt_vct
    ,input  [NO_OF_BT-1:0]                    ih_te_ie_re_vct    
//spyglass enable_block W240
    ,input  [IE_UNIQ_BLK_BITS-1:0]            ie_ecc_uniq_block_num
    ,input  [BT_BITS-1:0]                     te_mr_ie_bt
    ,input                                    ie_enable_we_bw
    ,input                                    ie_enable_we_bw_wo_op_is_wr      // Only for bank_hit with WE_BW entry. To improve timing, use this one (without op_is_wr)
    ,input                                    ih_te_wr_eccap
    ,input  [BSM_BITS-1:0]                    r_ts_bsm_num4pre                  // BSM numer of the precharge cmd selected by the scheduler
    ,input  [BSM_BITS-1:0]                    r_ts_bsm_num4any                  // BSM number of the ACT , ACT bypass, PRE or RDWR (registered)
    ,input  [BSM_BITS-1:0]                    r_ts_bsm_num4act                  // BSM number of the ACT , ACT bypass
    ,input  [BSM_BITS-1:0]                    r_ts_bsm_num4rdwr                 // BSM number of the RDWR (registered)
    ,input                                    r_te_rdwr_autopre                 // autopre this cycle
    ,input                                    r_ts_op_is_precharge              // precharge scheduled this cycle
    ,input                                    r_ts_op_is_activate               // activate scheduled this cycle
    ,input                                    be_te_page_hit                    // the incoming command from IH has a current page hit
    ,input  [BSM_BITS-1:0]                    ts_bsm_num4rdwr                   // BSM number on cam search    
    ,input                                    dh_te_dis_wc                      // disable write combine
    ,input                                    i_combine_ok                      // OK to write combine this cycle
    ,output                                   i_wr_combine_replace_bank_match   // incoming rank & bank matches address of current write combine with all data ready
    ,output                                   i_same_addr_wr                    // incoming address matches address of current write
    ,output                                   i_combine_match                   // incoming xaction may be combined with this pending xaction
    ,output                                   i_combine_match_wecc              // combine match for WR ECC (WE_BW) this is used only for the case entry_valid=0
    ,output [1:0]                             i_entry_out_pri                   // priority
    ,output                                   i_entry_vpw_timed_out             // VPW entry timed-out
    ,output                                   i_entry_vpw_valid                 // goes high for all entries that are expired-VPW commands
    ,output                                   i_entry_vpw_valid_d               // Flopped version of i_entry_vpw_valid. Falling edge is aligned with i_entry_vpw_valid
    ,output                                   i_entry_vpw_page_hit              // page hit indicator to VPW selection n/w in wr_replace module
    ,output                                   i_bank_hit_wrecc_in_vpw            //bank-hit in entries of vpw with te_sel_wrecc_btt_bank
    ,input  [BSM_BITS-1:0]                    te_sel_wrecc_btt_bank              //bank# from wrecc_btt replace logic
    ,output                                   i_bank_hit_vpw_in_wrecc            //bank-hit in entries of wrecc_btt with te_sel_vpw_bank
    ,input  [BSM_BITS-1:0]                    te_sel_vpw_bank                    //bank# from vpw replace logic
    ,output                                   i_bank_hit_inc_vpw_in_wrecc         //bank-hit in entries of wrecc_btt with incoming vpw.
    ,input  [BSM_BITS-1:0]                    incoming_vpw_bank                  //bank# of incoming vpw
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL assertion.
    ,input                                    ih_te_wr_valid                    // incoming is a valid write command
//spyglass enable_block W240
    ,input                                    i_load                            // store entry signal
    ,input                                    i_entry_del                       // delete entry signal
    ,input                                    i_wr_data_rdy_wr_en               // enable write signal, write data complete
    ,input                                    i_rd_data_rdy_wr_en               // enable write signal, read data complete
    ,input   [MWR_BITS-1:0]                   i_mwr                             // Masked write information
    ,input  [PARTIAL_WR_BITS-1:0]             i_wr_word_valid
    ,input  [PARTIAL_WR_BITS_LOG2-1:0]        i_wr_ram_raddr_lsb_first
    ,input  [PW_WORD_CNT_WD_MAX-1:0]          i_wr_pw_num_beats_m1
    ,input  [PW_WORD_CNT_WD_MAX-1:0]          i_wr_pw_num_cols_m1
    // IH->TE interface for Inline ECC, for WE_BW commands, the following infomation is provided by IH 
    ,input   [MWR_BITS-1:0]                   ih_te_mwr                             // Masked write information
    ,input  [PARTIAL_WR_BITS-1:0]             ih_te_wr_word_valid
    ,input  [PARTIAL_WR_BITS_LOG2-1:0]        ih_te_wr_ram_raddr_lsb_first
    ,input  [PW_WORD_CNT_WD_MAX-1:0]          ih_te_wr_pw_num_beats_m1
    ,input  [PW_WORD_CNT_WD_MAX-1:0]          ih_te_wr_pw_num_cols_m1

    ,output [ENTRY_OTHER_MSB-ENTRY_AUTOPRE_LSB:0] i_entry_out                       // entry_contents, excludes data ready signals
    ,output                                   i_load_ntt                        // load NTT enable
    ,output                                   i_entry_valid                     // entry is valid
    ,output                                   i_bank_hit                        // bank match for autopre calculation
    ,output                                   i_bank_hit_act                    // bank match for activate
    ,output                                   i_bank_hit_pre                    // bank match for activate
    ,input  [BSM_BITS-1:0]                    ts_bsm_num4pre                    // BSM numer of the precharge cmd selected by the scheduler
    ,output                                   i_page_hit                        // open page hit info during cam search, only valid when i_bank_hit=1
    ,output                                   page_open_any_op                  // page is open for this entry if same bank of ACT, RDWR, or PRE one cycle earlier
    ,output                                   rd_and_wr_data_rdy                // both write data and read data complete (i_wr_data_rdy_wr_en and i_rd_data_rdy_wr_en pulses occured in any order) 
    ,output                                   i_ie_bt_hit                       // BT match for executing transaction   
    ,output                                   i_entry_ie_we_bw
    ,output                                   i_entry_ie_btt                    // Block Token is already terminated in block channel
    ,output                                   i_entry_ie_re                     // Read ECC is read in the block channel. Masked write is no longer needed.
    ,output                                   ie_disable_entry_valid            // Disable this entry if this entry is WE_BW and incoming entry is WD_E with same BT (for assertion)
    ,output                                   ie_enable_entry_valid             // Enable this entry if i_enable_this_entry && ~ie_disable_entry_valid
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL assertion and/or in generate block.
    ,input                                    ts_te_force_btt
//spyglass enable_block W240
    ,output                                   i_ie_blk_addr_collision           // Block address collision is happening (only for debug port)
    ,output reg                               i_entry_critical_early
    ,output reg                               i_entry_critical
    ,input                                    page_hit_limit_reached            // Pulse signal
    ,input                                    page_hit_limit_incoming           // Incoming bank has page-hit_limiter expired
    ,input                                    page_hit_limit_reached_incoming   // Incoming bank has page-hit_limiter expired
    ,input                                    ts_op_is_wr                       // BSM number on cam search    
    ,input                                    i_vlimit_decr
    ,input  [8:0]                             vlimit_int 
    ,output                                   te_wr_vlimit_reached
    `ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
    ,output                                   i_entry_we_bw_loaded
    ,output                                   i_entry_ie_btt_sticky_sva         // This entry has ever been BTT=1 (only for assertion.)
    `endif
    ,output                                   i_entry_loaded_sva         // Indicate this entry is i_entry_loaded for assertion use only
   `endif //  `ifdef SNPS_ASSERT_ON
    );


    localparam        CATEGORY =5;


//------------------------------------------------------------------------------
// Wire and Register Declarations
//------------------------------------------------------------------------------
//spyglass disable_block W497
//SMD: Not all bits of bus 'r_entry'(11 bits) are set
//SJ: Expected to happen in inline ECC configs which have VPR/VPW enabled (bits driven in WRCAM_ENTRY3 generate block)
reg  [ENTRY_BITS-1:0]                  r_entry;                         // actual storage
//spyglass enable_block W497

reg                                    r_combine_dis;                   // disable write combine
wire                                   i_flag_nxt;                      // next value of 2 write datas pending flags
reg                                    r_flag;                          // awaiting write data for both a combined write and
                                                                        //  the first pre-combined write
wire                                   i_combine_cmd_ok;                // For inline ECC. combine is only allowed for non-protected resion command.  
wire                                   i_combine_match_norm;            // Indicate this is normal combine (not the special case for WE_BW).  
wire                                   i_entry_loaded;
wire                                   i_same_addr_wr_int;              // intermediate i_same_addr_wr
wire                                   i_same_page_blk_wr;              // matching rank/bank addr with incoming xaction
wire                                   i_same_bank_wr4combine;          // matching rank/bank addr with incoming xaction (for wr combine)
wire                                   i_same_bank_wr;                  // matching rank/bank addr with incoming xaction
wire                                   i_combine_match_all;             // Indicate this is normal combine or special combine for WE_BW
wire                                   i_same_addr_wr_ie;               // Additional condition for i_same_addr_wr for INLINE_ECC
wire                                   i_diff_bt_wr;                    // Different BT value with incoming xaction
wire                                   i_same_bt_wr;                    // Different BT value with incoming xaction
wire                                   i_same_ie_blk_burst_num;         // Same ie_blk_burst_num for normal collision within an ECC block
wire                                   i_enable_this_entry;             // entry_valid bacomes 1 with this signal
wire                                   i_same_bank_as_rdwr_op;
wire [RANKBANK_BITS-1:0]               ih_te_wr_rankbank_num;
reg  [WR_LATENCY_BITS-1:0]             r_entry_wr_latency_ns;
wire                                   valid_entry_is_vpw;
wire                                   latency_timer_zero;
wire                                   vpw_to_exp_vpw;
wire [WR_LATENCY_BITS-1:0]             i_entry_vpw_latency;             // write latency value of this entry
reg  [8:0]                             visible_window_counter;
reg                                    visible_window_reached;
wire                                   i_vlimit_decr_w;
wire [PAGE_BITS-1:0]                   i_entry_out_page;                // entry contents
wire [RANKBANK_BITS-1:0]               i_entry_out_rankbank;            // entry contents
wire                                   i_entry_rd_data_pending;
wire                                   i_entry_wr_data_pending;

// Internal address signal for collision detection

// CAM entry
reg  [RANKBANK_BITS-1:0]               i_entry_rankbank;
reg  [BLK_BITS-1:0]                    i_entry_blk;
reg  [PAGE_BITS-1:0]                   i_entry_page;

// Incomiing command
reg  [RANKBANK_BITS-1:0]               i_wr_incoming_rankbank;
reg  [BLK_BITS-1:0]                    i_wr_incoming_blk;
reg  [PAGE_BITS-1:0]                   i_wr_incoming_page;

reg  [IE_WR_TYPE_BITS-1:0]             i_entry_wr_type;
reg  [BT_BITS-1:0]                     i_entry_bt;
reg  [IE_BURST_NUM_BITS-1:0]           i_entry_ie_blk_burst_num;
reg  [BT_BITS-1:0]                     i_wr_incoming_bt;

reg                                    i_entry_valid_1d;   
reg                                    i_entry_valid_2d;   

wire                                   i_entry_ie_wd_e;
wire                                   i_entry_ie_wd_n;

wire                                   ie_compare_ecc;
wire                                   ie_compare_data;
wire                                   ie_compare_ie_bt;
wire                                   ie_compare_blk_burst; 
wire                                   ie_wecc_combine;

wire                                   ie_incoming_is_we_bw;
// This is used only for WRECC CAM, otherwise tied to 0.  
assign ie_incoming_is_we_bw = (IE_WR_ECC_ENTRY==0)? 1'b0 : (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW);

// This entry is WE_BW and last WD_E is scheduled-out now. This entry becomes valid. 
// ie_enable_we_bw : This is the last WD_E scheduled-out with a BT, and no incoming command with the BT. 
// If the WD_E with the same BT is incoming, this is cancelled. (can be removed if this is critical path) 
assign i_enable_this_entry = i_entry_ie_we_bw & ie_enable_we_bw & (i_entry_bt == te_mr_ie_bt);

//-----------------------------
// Inline ECC Collision Matrix 
//-----------------------------
//
//+-----------------+----------+---------+-------+--------+----+
//| i_entry_wr_type | Incoming | Compare | BT    | Offset |Type|
//|                 | type     | Address | check | Check  |    |
//+-----------------+----------+---------+-------+--------+----+
//|                 | RD_N     | Data    |       |        |Norm|
//|                 | RD_E     | ECC     |       |        |Blk | ECC hole access only.
//| WD_N            | RE_B     | ECC(*)  |       |        |Blk | ECC hole access only
//|                 | WD_N     | Data    |       |        |Norm| 
//|                 | WD_E     | ECC     |       |        |Blk | ECC hole access only.
//|                 | WE_BW    | ECC(*)  |       |        |Blk | This shoud never happens because collision must be resolved by previous WD_E.
//+-----------------+----------+---------+-------+--------+----+
//|                 | RD_N     | ECC     |       |        |Blk | ECC hole access only.
//|                 | RD_E     | ECC     | same  | same   |Norm|
//|                 |          | ECC     | diff  |        |Blk |
//| WD_E            | RE_B     | ECC     | diff  |        |Blk |
//|                 | WD_N     | ECC     |       |        |Blk | ECC hole access only.
//|                 | WD_E     | ECC     | same  | same   |Norm|
//|                 |          | ECC     | diff  |        |Blk |
//|                 | WE_BW    | ECC     | diff  |        |Blk | This shoud never happens because collision must be resolved by previous WD_E.
//+-----------------+----------+---------+-------+--------+----+
//|                 | RD_N     | ECC(*)  |       |        |Blk | ECC hole access only. 
//|                 | RD_E     | ECC     | diff  |        |Blk |
//| WE_BW           | RE_B     | ECC     | diff  |        |Blk |
//|                 | WD_N     | ECC(*)  |       |        |Blk | ECC hole access only.
//|                 | WD_E     | ECC     | diff  |        |Blk |
//|                 | WE_BW    | ECC     | diff  |        |Blk | This shoud never happens because collision must be resolved by previous WD_E.
//+-----------------+----------+---------+-------+--------+----+
// (*) Either Data or ECC is Okay because of the following
// For WD_N/RD_N on ECC region, ECC address == Data address
// For WE_*/RE_*, ECC address == Data address


assign ie_compare_ecc    =  ~ie_compare_data;

assign ie_compare_data   =  (i_entry_ie_wd_n & ((ih_te_ie_rd_type == `IE_RD_TYPE_RD_N) | (ih_te_ie_wr_type == `IE_WR_TYPE_WD_N)));

assign ie_compare_ie_bt  =  (
                               (~i_entry_ie_wd_n)  // == (i_entry_ie_wd_e || i_entry_ie_we_bw)
                            )
                          & (
                               (ih_te_ie_rd_type == `IE_RD_TYPE_RD_E)
                             | (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B)
                             | (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E)
                             | (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW)
                            );

assign ie_compare_blk_burst = (i_entry_ie_wd_e) & ((ih_te_ie_rd_type == `IE_RD_TYPE_RD_E) | (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E));

assign ie_wecc_combine   =  i_entry_ie_we_bw & (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW) & i_same_bt_wr;
// ih_te_ie_wr_type == IE_WR_TYPE_WE_BW contains ih_te_wr_valid (otherwise ih_te_ie_wr_type is masked to 11b)

// Indicate any block address collision (for debug port)
assign i_ie_blk_addr_collision = i_same_addr_wr & ie_compare_ecc & ~(ie_compare_ie_bt & i_same_bt_wr);

 

//--------------------------------------------------------------------------------------------
// Wire assignments based on the value of the entries in the CAM location
//--------------------------------------------------------------------------------------------

assign  i_entry_loaded           = r_entry [ENTRY_VALID];
generate
   if (IE_WR_ECC_ENTRY==1) begin : WRECCCAM_ENTRY0 
      assign  i_entry_out_pri          = {HI_PRI_BITS{1'b0}};
   end else begin : WRCAM_ENTRY0
      assign  i_entry_out_pri          = r_entry [ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB];
   end
endgenerate
assign  i_entry_out_page         = r_entry [ENTRY_ROW_MSB  : ENTRY_ROW_LSB  ];
assign  i_entry_out_rankbank     = r_entry [ENTRY_RANK_MSB : ENTRY_BANK_LSB ];
assign  i_entry_rd_data_pending  = r_entry [ENTRY_RD_DATA_PENDING];
assign  i_entry_wr_data_pending  = r_entry [ENTRY_WR_DATA_PENDING];

// valid indication - goes high after the entry is loaded and both the write and read data (if any) has arrived
wire   i_entry_valid_data;
assign i_entry_valid_data = i_entry_loaded & (~r_entry[ENTRY_WR_DATA_PENDING]) & (~r_entry[ENTRY_RD_DATA_PENDING]);
assign i_entry_valid = i_entry_valid_data;

// assign output entry, excluding data ready and valid indicators
assign i_entry_out [ENTRY_AUTOPRE_MSB-ENTRY_AUTOPRE_LSB:ENTRY_AUTOPRE_LSB-ENTRY_AUTOPRE_LSB] = r_entry [ENTRY_AUTOPRE_MSB:ENTRY_AUTOPRE_LSB];
assign i_entry_out [ENTRY_OTHER_MSB-ENTRY_AUTOPRE_LSB:ENTRY_BLK_LSB-ENTRY_AUTOPRE_LSB]       = r_entry [ENTRY_OTHER_MSB:ENTRY_BLK_LSB];

generate
   if (IE_WR_ECC_ENTRY) begin :WRECCCAM_ENTRY1 
      assign i_entry_out [ENTRY_VPW_LAT_MSB-ENTRY_AUTOPRE_LSB:ENTRY_VPW_LAT_LSB-ENTRY_AUTOPRE_LSB] = {WR_LATENCY_BITS{1'b1}};
      assign i_entry_out [ENTRY_HI_PRI_MSB-ENTRY_AUTOPRE_LSB:ENTRY_HI_PRI_LSB-ENTRY_AUTOPRE_LSB]   = {HI_PRI_BITS{1'b0}};
   end else begin : WRCAM_ENTRY1
      assign i_entry_out [ENTRY_VPW_LAT_MSB-ENTRY_AUTOPRE_LSB:ENTRY_HI_PRI_LSB-ENTRY_AUTOPRE_LSB] = r_entry [ENTRY_VPW_LAT_MSB:ENTRY_HI_PRI_LSB];
   end
endgenerate


// rank/bank of the entry same as the rank/bank of the rd/wr command
assign i_same_bank_as_rdwr_op           = &(i_entry_out_rankbank ~^ ts_bsm_num4rdwr);

//-------------------------   r_page_open ---------------------------------------
reg   r_page_open;
wire  r_page_hit_act;
wire  set_page_open_for_act;
wire  set_page_close_for_pre;
wire  page_open_next;
wire  page_open;

//---------------------------
// comparators to decide bank and page hit for act and pre commands
// need this to generate the page_hit flag per-entry
//--------------------------- 
wire r_same_bank_any_op;
wire r_same_bank_act_op;
wire r_same_bank_rdwr_op;
wire r_same_pre_bank;
   
assign r_same_bank_any_op   = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4any));
assign r_same_bank_act_op   = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4act));
assign r_same_bank_rdwr_op  = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4rdwr));
assign r_same_pre_bank      = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4pre));
assign page_open_any_op     = page_open_next & r_same_bank_any_op & i_entry_valid;
   
assign r_page_hit_act       = (& (i_entry_out_page      ~^ r_ts_act_page )) & r_same_bank_act_op;

assign set_page_open_for_act  = r_ts_op_is_activate & r_page_hit_act;
assign set_page_close_for_pre = (r_te_rdwr_autopre & r_same_bank_rdwr_op) | (r_ts_op_is_precharge & r_same_pre_bank);
reg r_be_te_page_hit;
reg r_load;

assign page_open = set_page_open_for_act  ? 1'b1 :
                   set_page_close_for_pre  ? 1'b0 :
           r_load ? r_be_te_page_hit :r_page_open;
assign page_open_next = page_open & i_entry_loaded;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
     r_page_open        <= 1'b0;
     r_be_te_page_hit   <= 1'b0;
     r_load             <= 1'b0;
     i_entry_valid_1d   <= 1'b0;
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
     i_entry_valid_2d   <= 1'b0;
//spyglass enable_block W528
  end
  else begin
     r_page_open        <= page_open_next;
     r_be_te_page_hit   <= be_te_page_hit;
     r_load             <= i_load;
     i_entry_valid_1d   <= i_entry_valid | i_enable_this_entry;
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
     i_entry_valid_2d   <= i_entry_valid_1d | i_enable_this_entry;
//spyglass enable_block W528
     // For race condition (set and clear happens for i_entry_valid in the same cycle) 
  end
end // always @ (posedge co_te_clk or negedge core_ddrc_rstn)


//------------------------------------------------------------------------------
// Logic
//------------------------------------------------------------------------------

assign ih_te_wr_rankbank_num = {
                               ih_te_wr_rank_num,
                               ih_te_wr_bg_bank_num
                            };



//spyglass disable_block W552
//SMD: Bus 'r_entry' is driven inside more than one sequential block
//SJ: 'r_entry' is driven per-bit based on parameter values which do not overlap

// entry valid
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_VALID] <= 1'b0;
  else if(ddrc_cg_en)
  begin
    if (i_load)
      r_entry [ENTRY_VALID] <= 1'b1;
    else if (i_entry_del)
      r_entry [ENTRY_VALID] <= 1'b0;
  end


// combine possible if:
//  - write command to the same address as this entry
//  - write combine not disabled (for register bit or for too many write combines outstanding to this entry)
//assign i_combine_match    = ih_te_wr_valid & i_same_addr_wr & (~r_combine_dis) & i_combine_ok & i_combine_cmd_ok `ifdef UMCTL2_DYN_BSM & (~i_bsm_alloc) `endif;

wire i_combine_match_w;
assign i_combine_match = i_combine_match_w;


assign i_combine_match_w  = ih_te_wr_valid & i_same_addr_wr & (~r_combine_dis) & i_combine_cmd_ok
                                  & i_combine_ok 
                                  ;


assign i_flag_nxt = (r_entry [ENTRY_WR_DATA_PENDING] & i_combine_match_norm & (~i_wr_data_rdy_wr_en)) |
                    (r_flag & (~i_wr_data_rdy_wr_en));
assign rd_and_wr_data_rdy = ~i_entry_wr_data_pending & i_rd_data_rdy_wr_en |
                            ~i_entry_rd_data_pending & i_wr_data_rdy_wr_en & (~r_flag)|
                            (i_wr_data_rdy_wr_en & (~i_combine_match) & (~r_flag) & i_rd_data_rdy_wr_en);   


// For inline ECC 
// Write combine is only allowed between WD_N and WD_N (non-protected region only)
// When inline ECC is disabled, all write command are WD_N

//----------+---------------+-----------------------------------+-----+-----
// Combine  | i_entry_valid | signals to indicate               | NTT | WU
//----------+---------------+-----------------------------------+-----+-----
// WD_N/E   | Don't case    | i_combine_match_norm              | UPD | UPD
// WE_BW    | 1             | ie_wecc_combine & i_entry_valid   | UPD | No
// WE_BW    | 0             | i_combine_match_wecc              | No  | No
//----------+---------------+-----------------------------------+-----+-----
assign i_combine_cmd_ok      = (i_entry_wr_type == ih_te_ie_wr_type) & (i_same_bt_wr | i_entry_ie_wd_n);
assign i_combine_match_all   = i_combine_match | i_combine_match_wecc;
assign i_combine_match_wecc  = (IE_WR_ECC_ENTRY==1'b0)? 1'b0 : (ie_wecc_combine & ~i_entry_valid & ~i_entry_valid_2d);  // For WE_BW special case (no comunication is needed to wr_nxt) 
assign i_combine_match_norm  = i_combine_match & ~ie_wecc_combine; // 

// Disable this entry by asserting ENTRY_RD_DATA_PENDING (RMW is not supported for WE_BW)
assign ie_disable_entry_valid = (IE_WR_ECC_ENTRY==1'b0)? 1'b0 : ((ih_te_ie_wr_type==`IE_WR_TYPE_WD_E & ih_te_ie_rd_type!=`IE_RD_TYPE_RD_E & i_entry_ie_we_bw & i_same_bt_wr) | i_combine_match_wecc);
assign ie_enable_entry_valid = i_enable_this_entry && ~ie_disable_entry_valid && ~i_combine_match;

// set flag when write data is NOT ready and there occurs a write combine
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    r_flag <= 1'b0;
    r_combine_dis <= 1'b1;
  end
  else if(ddrc_cg_en) begin
    r_flag <= i_flag_nxt;
    r_combine_dis <= i_flag_nxt | (dh_te_dis_wc & (~i_entry_ie_we_bw)); // For WE_BW, combine is always enabled 
  end
end //always

// enable write for this entry (write data ready)
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_WR_DATA_PENDING] <= 1'b0;
  else if(ddrc_cg_en)
  begin
    if (i_load)
      r_entry [ENTRY_WR_DATA_PENDING] <= 1'b1;
    else if (i_combine_match)
      r_entry [ENTRY_WR_DATA_PENDING] <= 1'b1;
    else if (i_wr_data_rdy_wr_en & (~r_flag) | i_enable_this_entry)
      r_entry [ENTRY_WR_DATA_PENDING] <= 1'b0;
    end


// enable write for this entry (read data ready)
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_RD_DATA_PENDING] <= 1'b0;
  else if(ddrc_cg_en)
  begin
    if (i_load)
      r_entry [ENTRY_RD_DATA_PENDING] <= 1'b1;
    // ENTRY_RD_DATA_PENDING is not used for WE_BW as no RMW is supported. Just used to active withdrawn. (to make entry_valid=0)
    // This is not for RMW : This is Active NTT withdrawn, NTT is just withdrawn until WD_E is served.
    // But if WD_E is part of RMW, RD is required to serve WR and there may be no reason to switch to RD mode then nothing can be scheduled out.
    // [ | i_combine_match_wecc] To avoid i_entry_valid=1 if i_rd_data_rdy_wr_en & i_combine_match_wecc
    else if (ie_disable_entry_valid)
      r_entry [ENTRY_RD_DATA_PENDING] <= 1'b1;
    else if (i_rd_data_rdy_wr_en | i_enable_this_entry)
      r_entry [ENTRY_RD_DATA_PENDING] <= 1'b0;
  end

// masked write for this entry, that is set by i_load_ntt
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_MWR_MSB:ENTRY_MWR_LSB] <= {MWR_BITS{1'b0}};
  else if(ddrc_cg_en)
  begin
    if ((i_load | i_combine_match_all) & ie_incoming_is_we_bw)
        r_entry [ENTRY_MWR_MSB:ENTRY_MWR_LSB] <= ih_te_mwr[MWR_BITS-1:0];
    else if (i_entry_ie_we_bw) // If this entry is WE_BW, this field is not updated with i_load_ntt event
        r_entry [ENTRY_MWR_MSB:ENTRY_MWR_LSB] <= r_entry [ENTRY_MWR_MSB:ENTRY_MWR_LSB];
    else
    if (i_load & (IE_WR_ECC_ENTRY==1'b0)) // Exclude this condition for WRECC CAM
        r_entry [ENTRY_MWR_MSB:ENTRY_MWR_LSB] <= {MWR_BITS{1'b0}};
    else if (i_load_ntt)
      r_entry [ENTRY_MWR_MSB:ENTRY_MWR_LSB] <= i_mwr[MWR_BITS-1:0];
  end


// wr_word_valid for this entry, that is set by i_load_ntt
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_PW_WORD_VALID_MSB:ENTRY_PW_WORD_VALID_LSB] <= {PARTIAL_WR_BITS{1'b0}};
  else if(ddrc_cg_en)
  begin
    if ((i_load | i_combine_match_all) & ie_incoming_is_we_bw)
        r_entry [ENTRY_PW_WORD_VALID_MSB:ENTRY_PW_WORD_VALID_LSB] <= ih_te_wr_word_valid[PARTIAL_WR_BITS-1:0];
    else if (i_entry_ie_we_bw) // If this entry is WE_BW, this field is not updated with i_load_ntt event
        r_entry [ENTRY_PW_WORD_VALID_MSB:ENTRY_PW_WORD_VALID_LSB] <= r_entry [ENTRY_PW_WORD_VALID_MSB:ENTRY_PW_WORD_VALID_LSB];
    else
    if (i_load)
        r_entry [ENTRY_PW_WORD_VALID_MSB:ENTRY_PW_WORD_VALID_LSB] <=
                                                                     {PARTIAL_WR_BITS{1'b0}}; // set to 0 to flag that no bits are valid
    else if (i_load_ntt)
      r_entry [ENTRY_PW_WORD_VALID_MSB:ENTRY_PW_WORD_VALID_LSB] <= i_wr_word_valid[PARTIAL_WR_BITS-1:0]
                                                                   ;
  end


  // ram_raddr_lsb_first for this entry, that is set by i_load_ntt
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_PW_RAM_RADDR_MSB:ENTRY_PW_RAM_RADDR_LSB] <= {PARTIAL_WR_BITS_LOG2{1'b0}};
  else if(ddrc_cg_en)
  begin
    if ((i_load | i_combine_match_all) & ie_incoming_is_we_bw)
        r_entry [ENTRY_PW_RAM_RADDR_MSB:ENTRY_PW_RAM_RADDR_LSB] <= ih_te_wr_ram_raddr_lsb_first[PARTIAL_WR_BITS_LOG2-1:0];
    else if (i_entry_ie_we_bw) // If this entry is WE_BW, this field is not updated with i_load_ntt event
        r_entry [ENTRY_PW_RAM_RADDR_MSB:ENTRY_PW_RAM_RADDR_LSB] <= r_entry [ENTRY_PW_RAM_RADDR_MSB:ENTRY_PW_RAM_RADDR_LSB];
    else
    if (i_load)
        r_entry [ENTRY_PW_RAM_RADDR_MSB:ENTRY_PW_RAM_RADDR_LSB] <= {PARTIAL_WR_BITS_LOG2{1'b0}}; // set to 0 to flag that no bits are valid
    else if (i_load_ntt)
      r_entry [ENTRY_PW_RAM_RADDR_MSB:ENTRY_PW_RAM_RADDR_LSB] <= i_wr_ram_raddr_lsb_first[PARTIAL_WR_BITS_LOG2-1:0];
  end

    // pw_num_beats_m1 for this entry, that is set by i_load_ntt
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_PW_NUM_BEATS_M1_MSB:ENTRY_PW_NUM_BEATS_M1_LSB] <= {PW_WORD_CNT_WD_MAX{1'b0}};
  else if(ddrc_cg_en)
  begin
    if ((i_load | i_combine_match_all) & ie_incoming_is_we_bw)
        r_entry [ENTRY_PW_NUM_BEATS_M1_MSB:ENTRY_PW_NUM_BEATS_M1_LSB] <= ih_te_wr_pw_num_beats_m1;
    else if (i_entry_ie_we_bw) // If this entry is WE_BW, this field is not updated with i_load_ntt event
        r_entry [ENTRY_PW_NUM_BEATS_M1_MSB:ENTRY_PW_NUM_BEATS_M1_LSB] <= r_entry [ENTRY_PW_NUM_BEATS_M1_MSB:ENTRY_PW_NUM_BEATS_M1_LSB];
    else
    if (i_load)
      r_entry [ENTRY_PW_NUM_BEATS_M1_MSB:ENTRY_PW_NUM_BEATS_M1_LSB] <= {PW_WORD_CNT_WD_MAX{1'b0}}; // set to 0 to flag that no bits are valid
    else if (i_load_ntt)
      r_entry [ENTRY_PW_NUM_BEATS_M1_MSB:ENTRY_PW_NUM_BEATS_M1_LSB] <= i_wr_pw_num_beats_m1;
  end

  // pw_num_cols_m1 for this entry, that is set by i_load_ntt
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    r_entry [ENTRY_PW_NUM_COLS_M1_MSB:ENTRY_PW_NUM_COLS_M1_LSB] <= {PW_WORD_CNT_WD_MAX{1'b0}};
  else if(ddrc_cg_en)
  begin
    if ((i_load | i_combine_match_all) & ie_incoming_is_we_bw)
        r_entry [ENTRY_PW_NUM_COLS_M1_MSB:ENTRY_PW_NUM_COLS_M1_LSB] <= ih_te_wr_pw_num_cols_m1;
    else if (i_entry_ie_we_bw) // If this entry is WE_BW, this field is not updated with i_load_ntt event
        r_entry [ENTRY_PW_NUM_COLS_M1_MSB:ENTRY_PW_NUM_COLS_M1_LSB] <= r_entry [ENTRY_PW_NUM_COLS_M1_MSB:ENTRY_PW_NUM_COLS_M1_LSB]; 
    else
    if (i_load)
      r_entry [ENTRY_PW_NUM_COLS_M1_MSB:ENTRY_PW_NUM_COLS_M1_LSB] <= {PW_WORD_CNT_WD_MAX{1'b0}}; // set to 0 to flag that no bits are valid
    else if (i_load_ntt)
      r_entry [ENTRY_PW_NUM_COLS_M1_MSB:ENTRY_PW_NUM_COLS_M1_LSB] <= i_wr_pw_num_cols_m1;
  end





// entry contents (excluding valid and ready indicators)
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
  begin
    r_entry[ENTRY_AUTOPRE_MSB:ENTRY_AUTOPRE_LSB]           <= {ENTRY_AUTOPRE_BITS{1'b0}};
    r_entry[ENTRY_BLK_MSB:ENTRY_BLK_LSB]                   <= {BLK_BITS{1'b0}};
    r_entry[ENTRY_ROW_MSB:ENTRY_ROW_LSB]                   <= {PAGE_BITS{1'b0}};
    r_entry[ENTRY_BANK_MSB:ENTRY_BANK_LSB]                 <= {BG_BANK_BITS{1'b0}};
    r_entry[ENTRY_RANK_MSB:ENTRY_RANK_LSB]                 <= {RANK_BITS{1'b0}};
    r_entry[ENTRY_IE_BT_MSB:ENTRY_IE_BT_LSB]               <= {BT_BITS{1'b0}};
    r_entry[ENTRY_IE_WR_TYPE_MSB:ENTRY_IE_WR_TYPE_LSB]     <= {IE_WR_TYPE_BITS{1'b0}};
    r_entry[ENTRY_IE_BURST_NUM_MSB:ENTRY_IE_BURST_NUM_LSB] <= {IE_BURST_NUM_BITS{1'b0}};
    r_entry[ENTRY_IE_UNIQ_BLK_MSB:ENTRY_IE_UNIQ_BLK_LSB]   <= {IE_UNIQ_BLK_BITS{1'b0}};
    r_entry[ENTRY_ECCAP_MSB:ENTRY_ECCAP_LSB]    <= {ECCAP_BITS{1'b0}};
    r_entry[ENTRY_OTHER_MSB:ENTRY_OTHER_LSB]    <= {OTHER_ENTRY_BITS{1'b0}};
  end
  else if(ddrc_cg_en)
  begin
    if (i_load)
    begin
      r_entry[ENTRY_AUTOPRE_LSB]                <= ih_te_wr_autopre;
      r_entry[ENTRY_AUTOPRE_MSB]                <= (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E); // For WD_E, AP is not applied
      r_entry[ENTRY_BLK_MSB:ENTRY_BLK_LSB]      <= ih_te_wr_block_num;     // block number
      r_entry[ENTRY_ROW_MSB:ENTRY_ROW_LSB]      <= ih_te_wr_page_num;      // page number
      r_entry[ENTRY_BANK_MSB:ENTRY_BANK_LSB]    <= ih_te_wr_bg_bank_num;   // bank number
      r_entry[ENTRY_RANK_MSB:ENTRY_RANK_LSB]    <= ih_te_wr_rank_num;      // rank number
      r_entry[ENTRY_IE_BT_MSB:ENTRY_IE_BT_LSB]               <= ih_te_ie_bt;
      r_entry[ENTRY_IE_WR_TYPE_MSB:ENTRY_IE_WR_TYPE_LSB]     <= ih_te_ie_wr_type;
      r_entry[ENTRY_IE_BURST_NUM_MSB:ENTRY_IE_BURST_NUM_LSB] <= ih_te_ie_blk_burst_num;
      r_entry[ENTRY_IE_UNIQ_BLK_MSB:ENTRY_IE_UNIQ_BLK_LSB]   <= ie_ecc_uniq_block_num;
      r_entry[ENTRY_ECCAP_MSB:ENTRY_ECCAP_LSB]  <= ih_te_wr_eccap;
      r_entry[ENTRY_OTHER_MSB:ENTRY_OTHER_LSB]  <= ih_te_wr_other_fields;
    end
  end
  

// comparators// cam search
// this signal goes high for all the entries that have a bank-hit to the currently scheduled command
// this is used in the logic that determined whether to do autopre for pageclose feature or not
// this logic needs to see bank match from all entries (NPW, VPW and XVPW)
assign i_bank_hit     = (i_entry_valid 
                      & i_same_bank_as_rdwr_op
                        & (~i_combine_match)
                        )
                      | (i_entry_ie_we_bw & ie_enable_we_bw_wo_op_is_wr & ~ie_disable_entry_valid & (i_entry_bt == te_mr_ie_bt)) // This is valid only on the cycle of op_is_wr, so i_combine_match is never asserted at the same time.
                        ; 
// i_bank_hit_act 
assign i_bank_hit_act       = r_same_bank_act_op & i_entry_valid ;

assign i_bank_hit_pre       = (ts_bsm_num4pre == i_entry_out_rankbank) & i_entry_valid ;
// CAM search page hit (based on page for read/write replacement, or base on page from IH for write combine)
assign i_page_hit = page_open_next; 

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current implementation

// Assign Existing address to be compared
always @(*) begin
  // For existing entry
  i_entry_rankbank       = r_entry [ENTRY_RANK_MSB:ENTRY_BANK_LSB];
  i_entry_blk            = r_entry [ENTRY_BLK_MSB:ENTRY_BLK_LSB];
  i_entry_page           = r_entry [ENTRY_ROW_MSB:ENTRY_ROW_LSB];
  // For incoming entry
  i_wr_incoming_rankbank   = ih_te_wr_rankbank_num;
  i_wr_incoming_blk        = ih_te_wr_block_num;
  i_wr_incoming_page       = ih_te_wr_page_num;
  // For Inline ECC specific
  i_entry_bt               = r_entry[ENTRY_IE_BT_MSB:ENTRY_IE_BT_LSB];
  i_entry_wr_type          = r_entry[ENTRY_IE_WR_TYPE_MSB:ENTRY_IE_WR_TYPE_LSB];
  i_entry_ie_blk_burst_num = r_entry[ENTRY_IE_BURST_NUM_MSB:ENTRY_IE_BURST_NUM_LSB];
  i_wr_incoming_bt         = ih_te_ie_bt;

  if (ie_compare_ecc) begin
  // For existing entry (Replace corresponding addres bits to ECC address)
  i_entry_blk         [IE_UNIQ_BLK_LSB+:IE_UNIQ_BLK_BITS] = r_entry [ENTRY_IE_UNIQ_BLK_MSB:ENTRY_IE_UNIQ_BLK_LSB];
  // For incoming entry
  i_wr_incoming_blk      [IE_UNIQ_BLK_LSB+:IE_UNIQ_BLK_BITS] = ie_ecc_uniq_block_num;
  end
end
//spyglass enable_block W528
                         
assign i_diff_bt_wr            = (i_entry_bt != i_wr_incoming_bt);
assign i_same_bt_wr            = ~i_diff_bt_wr;
assign i_same_ie_blk_burst_num = (ih_te_ie_blk_burst_num == i_entry_ie_blk_burst_num);

assign i_ie_bt_hit = (i_entry_ie_wd_e) & (i_entry_bt == te_mr_ie_bt);

// rank_msb to bank_lsb used - appropriate bits will be selected based on UMCTL2_NUM_LRANKS_TOTAL_1 and MEMC_DDR4
assign i_same_bank_wr = (& (i_entry_rankbank ~^ i_wr_incoming_rankbank[RANKBANK_BITS-1:0]));

assign i_same_page_blk_wr = (& (i_entry_page ~^ i_wr_incoming_page [PAGE_BITS-1:0])) &
                            (& (i_entry_blk ~^ i_wr_incoming_blk [BLK_BITS-1:0]))  ;

assign i_same_addr_wr_int = i_same_bank_wr & i_same_page_blk_wr & r_entry[ENTRY_VALID];
assign i_same_addr_wr_ie  = (i_diff_bt_wr | (ie_compare_ie_bt==1'b0))  // BT check enabled by ie_compare_ie_bt
                          | (ie_compare_blk_burst & i_same_ie_blk_burst_num); // compare ie_blk_burst_num for detecting normal address collision within an ECC block 
assign i_same_addr_wr     = (i_same_addr_wr_int & i_same_addr_wr_ie) | ie_wecc_combine;
// This signal is only used for i_wr_combine_replace_bank_match
// For inline ECC, i_same_bank_wr does not always compare ih_te_wr_rankbank_num with i_entry_rankbank
// because ECC address is used for comparation. So created dedicated comparator.
assign i_same_bank_wr4combine = (& (i_entry_out_rankbank ~^ ih_te_wr_rankbank_num[RANKBANK_BITS-1:0]));





// combine only done for writes  -does not use i_same_*_rd
assign i_wr_combine_replace_bank_match  = i_same_bank_wr4combine  & // bank match with incoming one
            r_entry[ENTRY_VALID]                &          // entry is valid      
            (~r_entry[ENTRY_RD_DATA_PENDING])   &          // entry has all read data, if any
            (~r_entry[ENTRY_WR_DATA_PENDING])   &          // entry has all write data    
            (~(i_same_page_blk_wr & i_combine_match));     // entry is not being combined    



// both read and write data have come
assign i_load_ntt =  (IE_WR_ECC_ENTRY==1'b1)? 1'b0 :
                     (~i_combine_match & 
                                        ((i_wr_data_rdy_wr_en & (~r_flag) & (~r_entry [ENTRY_RD_DATA_PENDING])) |
                                        (i_rd_data_rdy_wr_en & (~r_entry [ENTRY_WR_DATA_PENDING]))              |
                                        (i_wr_data_rdy_wr_en & (~r_flag) & i_rd_data_rdy_wr_en)));



// write latency output from the WR CAM entries
generate
  if (IE_WR_ECC_ENTRY==1) begin : WRECCCAM_ENTRY2 
    assign i_entry_vpw_latency = {WR_LATENCY_BITS{1'b1}};
  end else begin : WRCAM_ENTRY2
    assign i_entry_vpw_latency = r_entry[ENTRY_VPW_LAT_MSB:ENTRY_VPW_LAT_LSB];
  end
endgenerate
// entry priority
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    r_entry [ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB] <= 2'b00;
  end
  else if(ddrc_cg_en)
  begin
    if (i_load)
      r_entry [ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB] <= (IE_WR_ECC_ENTRY==1'b1)? 2'b00 : ih_te_hi_pri;  // load value from IH
    else if (vpw_to_exp_vpw)
      r_entry [ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB] <= (IE_WR_ECC_ENTRY==1'b1)? 2'b00 : CMD_PRI_XVPW;  // all expired-VPW cmds switch to 2'b11 priority

  end


// latency counter logic
// If the incoming value is 0, then keep it as it is
// If not, decrement by 1 while loading to the register
wire [WR_LATENCY_BITS-1:0] init_wr_latency_value;
assign init_wr_latency_value =  (ih_te_wr_latency == {WR_LATENCY_BITS{1'b0}}) ?
                                               {WR_LATENCY_BITS{1'b0}} : (ih_te_wr_latency - {{(WR_LATENCY_BITS-1){1'b0}},1'b1});

//---------------------------
// Wr Latency timer decrement logic
//   - Load the incoming wr_latency value from IH
//   - Decrement every cycle by 1 until the value is 0
//   - Generate i_entry_vpw_timed_out when the entry times-out
//---------------------------
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
always @(*)
  begin 
     r_entry_wr_latency_ns  = i_entry_vpw_latency;
     // load the incoming value of valid cmd and VPW
     if(i_load && (ih_te_hi_pri == CMD_PRI_VPW))
        r_entry_wr_latency_ns  = init_wr_latency_value;
     // reset the value to  all 1's when entry not valid
     else if(i_entry_del)
        r_entry_wr_latency_ns = {WR_LATENCY_BITS{1'b1}};
     // reset the value to all 0's if the entry has been promoted to expired-VPW even though this timer has not counted down to 0
     else if(i_entry_loaded && (i_entry_out_pri == CMD_PRI_XVPW))
        r_entry_wr_latency_ns  = {WR_LATENCY_BITS{1'b0}};
     // decrement by 1, when entry is valid VPW and count not 0
     else if(i_entry_loaded && (i_entry_out_pri == CMD_PRI_VPW) && (i_entry_vpw_latency != {WR_LATENCY_BITS{1'b0}}))
        r_entry_wr_latency_ns  = i_entry_vpw_latency - {{(WR_LATENCY_BITS-1){1'b0}},1'b1};
  end
//spyglass enable_block W528

//---------------------------
// change VPW to expired-VPW when any VPW entry has timed-out and the latency timer entry of this entry is LTE to the vpw range register
// this is generated one cycle before priority flop (i_entry_out_pri) is set to 2'b11
//---------------------------
assign vpw_to_exp_vpw      = (valid_entry_is_vpw & latency_timer_zero) | visible_window_reached;

// Output assignment indicating that this entry has timed-out
// Goes high when all bits in i_entry_vpw_latency = 0 and when the command is valid (data has arrived)
assign i_entry_vpw_timed_out = (latency_timer_zero | visible_window_reached) & i_entry_valid
                                & (~i_combine_match)
                               ;

// goes high when the entry is valid and the priority is exp-VPW
assign i_entry_vpw_valid     = i_entry_valid & (vpw_to_exp_vpw || (i_entry_out_pri == CMD_PRI_XVPW))
                                & (~i_combine_match)
                               ;

//---------------------------
// Generating the page hit combinationally 
//   - page_hit status is updated on every activate and precharge command to the bank in this entry
//   - When the entry is loaded into the CAM, the page_hit input from BE is used to set this signal
//   - Note: the flopped version of load, act and pre are used in this logic in order to avoid long combinational path from Bypass and gs_next_xact modules
//--------------------------- 
assign i_entry_vpw_page_hit = page_open_next;

//---------------------------
//flops for the above logic and
//signals indicating that this entry has stored a valid VPW or NPW command
//---------------------------
generate
   if (IE_WR_ECC_ENTRY==1) begin : WRECCCAM_ENTRY3 

      assign valid_entry_is_vpw  = 1'b0;
      assign latency_timer_zero  = 1'b0;
      assign i_entry_vpw_valid_d = 1'b0;

   end else begin : WRCAM_ENTRY3

      reg    valid_entry_is_vpw_r;
      reg    latency_timer_zero_r;
      reg    i_entry_vpw_valid_d_r;
      assign valid_entry_is_vpw = valid_entry_is_vpw_r;
      assign latency_timer_zero = latency_timer_zero_r;
      assign i_entry_vpw_valid_d = i_entry_vpw_valid_d_r & (~i_combine_match);

      always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
        if(~core_ddrc_rstn) begin
           r_entry[ENTRY_VPW_LAT_MSB:ENTRY_VPW_LAT_LSB] <= {WR_LATENCY_BITS{1'b1}}; // reset to all 1's as all 0's is the timeout condition
           latency_timer_zero_r     <= 1'b0;
           valid_entry_is_vpw_r     <= 1'b0;
           i_entry_vpw_valid_d_r    <= 1'b0;
        end
        else begin
          if(i_load || i_entry_loaded) begin
           r_entry[ENTRY_VPW_LAT_MSB:ENTRY_VPW_LAT_LSB] <= r_entry_wr_latency_ns;
           latency_timer_zero_r                         <= ~|r_entry_wr_latency_ns;
          end
      
          if(i_load && (ih_te_hi_pri == CMD_PRI_VPW))
            valid_entry_is_vpw_r <= (IE_WR_ECC_ENTRY==1'b1)? 1'b0: 1'b1;
          else if(i_entry_del && ((i_entry_out_pri == CMD_PRI_VPW) || (i_entry_out_pri == CMD_PRI_XVPW)))
            valid_entry_is_vpw_r <= 1'b0;

          if(i_entry_del)
            i_entry_vpw_valid_d_r <= 1'b0;
          else if(i_entry_loaded)  
            i_entry_vpw_valid_d_r <= i_entry_vpw_valid;

        end
      end
  end
endgenerate

//spyglass disable_block W528
//SMD: Variable 'i_same_bank_sel_vpw'  'i_same_bank_sel_wrecc' is set but never read
//SJ: Used in generate block
 wire i_same_bank_sel_vpw;
 wire i_same_bank_sel_wrecc;
 wire i_same_bank_inc_vpw;
assign i_same_bank_sel_vpw   = (i_entry_out_rankbank == te_sel_vpw_bank);
assign i_same_bank_sel_wrecc = (i_entry_out_rankbank == te_sel_wrecc_btt_bank);
assign i_same_bank_inc_vpw    = (i_entry_out_rankbank == incoming_vpw_bank);
//spyglass enable_block W528

//spyglass enable_block W552

localparam NO_OF_BT_POW2 = 2**(BT_BITS);
wire [NO_OF_BT_POW2-1:0] ih_te_ie_btt_vct_tmp;
wire [NO_OF_BT_POW2-1:0] ih_te_ie_re_vct_tmp;
//NO_OF_BT_POW2 >= NO_OF_BT
generate
  if(NO_OF_BT_POW2 == NO_OF_BT) begin:NO_OF_BT_pow2
assign ih_te_ie_btt_vct_tmp =  ih_te_ie_btt_vct;
assign ih_te_ie_re_vct_tmp  =  ih_te_ie_re_vct;
  end else begin:NO_OF_BT_pow2
assign ih_te_ie_btt_vct_tmp =  {{(NO_OF_BT_POW2-NO_OF_BT){1'b0}},ih_te_ie_btt_vct};
assign ih_te_ie_re_vct_tmp  =  {{(NO_OF_BT_POW2-NO_OF_BT){1'b0}},ih_te_ie_re_vct};

  end
endgenerate

generate
   if (IE_WR_ECC_ENTRY==1) begin : WRECCCAM_ENTRY4 
      reg i_entry_ie_we_bw_r;
      reg i_entry_ie_btt_r;
      reg i_entry_ie_re_r;

      assign i_entry_ie_we_bw = i_entry_ie_we_bw_r;
      assign i_entry_ie_wd_n  = 1'b0;
      assign i_entry_ie_wd_e  = 1'b0;
      assign i_entry_ie_btt   = i_entry_ie_btt_r | ts_te_force_btt; 
      assign i_entry_ie_re    = i_entry_ie_re_r;

      assign i_bank_hit_wrecc_in_vpw = 1'b0;
      assign i_bank_hit_vpw_in_wrecc = i_same_bank_sel_vpw & i_entry_ie_btt_r & i_entry_valid;
      assign i_bank_hit_inc_vpw_in_wrecc = i_same_bank_inc_vpw & i_entry_ie_btt_r & i_entry_valid;

      // i_entry_we_bw/wd_e/wd_n  
      always @(posedge co_te_clk or negedge core_ddrc_rstn)
        if (~core_ddrc_rstn) begin
          i_entry_ie_we_bw_r <= 1'b0;
        end
        else if(ddrc_cg_en)
        begin
          if (i_load) begin
            i_entry_ie_we_bw_r <= 1'b1; // = (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW);
          end
          else if (i_entry_del) begin
            i_entry_ie_we_bw_r <= 1'b0;
          end
        end
      
      // BTT/RE(MWR)
      always @(posedge co_te_clk or negedge core_ddrc_rstn)
        if (~core_ddrc_rstn) begin
          i_entry_ie_btt_r <= 1'b0;
          i_entry_ie_re_r  <= 1'b0;
        end
        else 
        begin
          if (i_entry_del) begin
            i_entry_ie_btt_r <= 1'b0;
            i_entry_ie_re_r  <= 1'b0;
          end
          else if (i_entry_ie_we_bw) begin
            i_entry_ie_btt_r <= ih_te_ie_btt_vct_tmp[i_entry_bt];
            i_entry_ie_re_r  <= ih_te_ie_re_vct_tmp[i_entry_bt];
          end
        end
  
  end else begin : WRCAM_ENTRY4
      reg i_entry_ie_wd_n_r;
      reg i_entry_ie_wd_e_r;

      assign i_entry_ie_we_bw = 1'b0;
      assign i_entry_ie_wd_n  = i_entry_ie_wd_n_r;
      assign i_entry_ie_wd_e  = i_entry_ie_wd_e_r;
      assign i_entry_ie_btt   = 1'b0;
      assign i_entry_ie_re    = 1'b0;

      assign i_bank_hit_wrecc_in_vpw = i_same_bank_sel_wrecc & i_entry_vpw_valid;
      assign i_bank_hit_vpw_in_wrecc = 1'b0;
      assign i_bank_hit_inc_vpw_in_wrecc = 1'b0;

      // i_entry_we_bw/wd_e/wd_n  
      always @(posedge co_te_clk or negedge core_ddrc_rstn)
        if (~core_ddrc_rstn) begin
          i_entry_ie_wd_n_r  <= 1'b0;
          i_entry_ie_wd_e_r  <= 1'b0;
        end
        else if(ddrc_cg_en)
        begin
          if (i_load) begin
            i_entry_ie_wd_n_r  <= (ih_te_ie_wr_type == `IE_WR_TYPE_WD_N);
            i_entry_ie_wd_e_r  <= (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E);
          end
          else if (i_entry_del) begin
            i_entry_ie_wd_n_r  <= 1'b0;
            i_entry_ie_wd_e_r  <= 1'b0;
          end
        end
  end
endgenerate


// i_entry_critical_early version
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    i_entry_critical_early <= 1'b0;
  end
  else begin
    if (i_load & page_hit_limit_incoming) begin
      i_entry_critical_early <= (IE_WR_ECC_ENTRY==1)? 1'b0 : 1'b1;
    end
    else if (i_entry_del) begin        
      i_entry_critical_early <= 1'b0;
    end
    else if(i_entry_loaded) begin
      // For WRECC entry, page_hit_limiter does not apply to make sure WRECC command has to be issued before page is closed
      i_entry_critical_early <= (set_page_close_for_pre | (IE_WR_ECC_ENTRY==1))? 1'b0 : (r_same_bank_rdwr_op & page_hit_limit_reached)? 1'b1 : i_entry_critical_early;
    end
  end
end

// i_entry_critical version
// it indicated the entry already exceed pagehit limite after the write operation scheduled out.
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    i_entry_critical <= 1'b0;
  end
  else begin
    if (i_load & page_hit_limit_reached_incoming) begin
      i_entry_critical <= 1'b1;
    end else if (i_entry_del) begin        
      i_entry_critical <= 1'b0;
    // For WRECC entry, page_hit_limiter does not apply to make sure WRECC command has to be issued before page is closed
    end else if (set_page_close_for_pre | (IE_WR_ECC_ENTRY==1)) begin
      i_entry_critical <= 1'b0;
    end else if (i_same_bank_as_rdwr_op & ts_op_is_wr & i_entry_critical_early)begin
      i_entry_critical <= 1'b1;
    end 
  end
end

assign i_vlimit_decr_w = i_vlimit_decr; 
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    visible_window_counter <= 9'h00;
    visible_window_reached <= 1'b0;
  end
  else begin
    if (i_load | i_entry_del) begin        
      visible_window_counter <= vlimit_int; 
      visible_window_reached <= 1'b0;
    end
    else if (i_entry_loaded & i_vlimit_decr_w & visible_window_counter != 9'h00) begin
      visible_window_counter <= visible_window_counter - 9'h01;
      if (visible_window_counter==9'h01) begin
        visible_window_reached <= 1'b1;
      end
    end
  end
end

assign te_wr_vlimit_reached = visible_window_reached;


//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
wire retry_fatl_err_detected = 1'b0;
// Observe CAM is deleted with i_entry_valid==0 (only for WE_BW)
cp_ie_camDEL_with_non_valid://------------------------------------------------
    cover  property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(!i_entry_valid & i_entry_del & i_entry_ie_we_bw)) );

// Observe CAM is deleted with i_entry_valid_1d==0 (only for WE_BW)
cp_ie_camDEL_with_non_valid_1d://---------------------------------------------
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(!i_entry_valid_1d & i_entry_del & i_entry_ie_we_bw)) );

// Observe BTT is asserted during BTT is active
cp_ie_BTT_assert://---------------------------------------------
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (i_entry_ie_we_bw & $rose(ih_te_ie_btt_vct[i_entry_bt])));

// Check that CAM is never deleted with i_entry_valid_2d==0 (only for WE_BW)
a_ie_camDEL_with_non_valid_2d://------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(!i_entry_valid_2d & i_entry_del & i_entry_ie_we_bw)) )
    else $error("[%t][%m] ERROR: CAM is deleted without valid      ", $time);

// Check that CAM is never deleted with i_entry_valid==0 (except WE_BW)
a_ie_camDEL_with_non_valid://------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(!i_entry_valid & i_entry_del & ~i_entry_ie_we_bw)) )
    else $error("[%t][%m] ERROR: CAM is deleted without valid status except WE_BW", $time);

// Check that BTT is never changed from 1 to 0 while i_entry_ie_we_bw==1
a_ie_BTT_never_deassert_while_i_entry_iewe_bw://--------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (i_entry_ie_we_bw & $past(i_entry_ie_we_bw,1) |-> $fell(ih_te_ie_btt_vct[i_entry_bt])==0) )
    else $error("[%t][%m] ERROR: ih_te_btt_vct goes 0 during BT is active", $time);

// Check that cmd_type signals are one hot or zero
a_ie_wrcam_cmd_type_check://--------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    ($onehot0({i_entry_ie_we_bw,i_entry_ie_wd_n,i_entry_ie_wd_e})))
    else $error("[%t][%m] ERROR: i_entry_ie_we_bw/i_entry_ie_wd_e/i_entry_ie_wd_n must be one hot or zero", $time);

// Check that combine happens only with same command type
a_ie_wrcam_write_combine_cmd_type_check://--------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (i_combine_match_all & ih_te_wr_valid |-> ih_te_ie_wr_type == i_entry_wr_type))
    else $error("[%t][%m] ERROR: Write combine happened between different command type", $time);
camEntryOverwritten: //------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(r_entry[ENTRY_VALID] & i_load)) )
    else $error("[%t][%m] ERROR: Write CAM entry gets overwritten.", $time);

invalidTransactionScheduled: //----------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(~r_entry[ENTRY_VALID] & i_entry_del)) )
    else $error("[%t][%m] ERROR: Invalid Transaction Scheduled.", $time);

tooManyWriteCombine: //------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(i_combine_match & r_flag)) )
    else $error("[%t][%m] ERROR: Write combine with write data already pending for 2 previous writes.  TE cannot deal with this; please fix IH.", $time);

writeEntryRdDataEn: //------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn | retry_fatl_err_detected) //Disable the assertion once retry fatl error is detected
    (!(i_rd_data_rdy_wr_en & (~r_entry [ENTRY_RD_DATA_PENDING] & (i_entry_wr_type != `IE_WR_TYPE_WE_BW) ))) )
    else $error("[%t][%m] ERROR: Write CAM entry gets read data ready twice.", $time);
    // For inline ECC, WE_BW is never RMW, and ENTRY_RD_DATA_PENDING is no effect.

writeEntryWrDataEn: //------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(i_wr_data_rdy_wr_en & (~r_entry [ENTRY_WR_DATA_PENDING] & (i_entry_wr_type != `IE_WR_TYPE_WE_BW) ))) )
    else $error("[%t][%m] ERROR: Write CAM entry gets write data ready twice.", $time);

  // Check that write combine happens in the same cycle in which NTT is getting re-loaded due to a scheduled WR
  cp_wr_combine_happens_w_ntt_reload :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid & ~i_entry_del & i_same_bank_as_rdwr_op & i_combine_match));

  // Check that write combine happens when the entry is valid
  cp_wr_combine_happens_w_entry_valid :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid & i_combine_match));
//------------------------------------------------------------------------------

reg wr_cam_overwr;
reg wr_cam_dup;

initial
begin
  wr_cam_overwr = 1'b0;
  wr_cam_dup    = 1'b0;
end

// disable coverage collection as this is a check in SVA only        
// VCS coverage off 

always @(posedge co_te_clk)
begin
  if (r_entry [ENTRY_VALID] && i_load)
  begin
    $display ("%m: at %t ERROR: CAM entry gets overwritten.", $time);
    wr_cam_overwr = 1'b1;
  end
  if (~r_entry [ENTRY_VALID] && i_entry_del)
  begin
    $display ("%m: at %t ERROR: CAM entry gets duplicated transaction.", $time);
    wr_cam_dup = 1'b1;
  end
  // Added by Raj 7/8/06 to ensure IH/WU behave
  if (i_combine_match && r_flag)
  begin
    $display ("%m: at %t ERROR: Write combine with write data already pending for 2 previous writes.  TE is not equipped to handle this case.", $time);
  end
end
// VCS coverage on

  // Generate sticky version of i_entry_ie_btt_r for assertion
  // As entry has ever been to BTT=1 can have priority over others in wr_replace
  reg i_entry_ie_btt_sticky_r;
  always @(posedge co_te_clk or negedge core_ddrc_rstn)
    if (~core_ddrc_rstn) begin
      i_entry_ie_btt_sticky_r <= 1'b0;
    end
    else begin
      if (i_entry_del) begin
        i_entry_ie_btt_sticky_r <= 1'b0;
      end
      else if (i_entry_ie_we_bw) begin
        i_entry_ie_btt_sticky_r <= (ih_te_ie_btt_vct[i_entry_bt] | ts_te_force_btt)? 1'b1 : i_entry_ie_btt_sticky_r;
      end
    end
assign i_entry_we_bw_loaded      = i_entry_ie_we_bw;
assign i_entry_ie_btt_sticky_sva = i_entry_ie_btt_sticky_r | (ts_te_force_btt & i_entry_ie_we_bw) ;



//----------------------
// Cover Points and assertions related to VPW logic
//----------------------

Check_latency_timer_zero: //----------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (latency_timer_zero == (i_entry_vpw_latency==0)))
    else $error("[%t][%m] ERROR: latency_timer_zero is not matched to i_entry_vpw_latency.", $time);

Check_i_entry_vpw_timed_out: //------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (i_entry_vpw_timed_out |-> i_entry_valid))
    else $error("[%t][%m] ERROR: i_entry_vpw_timed_out is 1 but i_entry_valid is 0.", $time);

  // When there are expired-VPW commands, the valid from that entry should only be sent through the VPW selection n/w and
  // not through the LPR/HPR network.
//  assert_exp_vpw_only_thru_vpw_nw:
//    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
//    (!(i_entry_valid && (i_entry_out_pri == CMD_PRI_XVPW) && i_bank_hit)))
//    else $error("[%t][%m] ERROR: Valid sent through NPW selection network, when the entry is in expired VPW state.", $time);

  // Load CAM and Activate to any bank/row happening in the same cycle
  cp_wr_cam_load_w_activate_any :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_load && r_ts_op_is_activate);

  // Load CAM and Precharge to any bank/row happening in the same cycle
  cp_wr_cam_load_w_pre_any :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_load && (r_te_rdwr_autopre | r_ts_op_is_precharge));

  // When CAM entry is valid, an ACT happens to the same bank / diff page as this entry
  cp_wr_cam_entry_valid_act_w_same_bank_diff_row :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && r_ts_op_is_activate && r_same_bank_act_op && (~r_page_hit_act)));

  // When CAM entry is valid, an ACT happens to the same bank / same page as this entry
  cp_wr_cam_entry_valid_act_w_same_bank_same_row :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && r_ts_op_is_activate && r_same_bank_act_op && r_page_hit_act));

  // When CAM entry is valid, a PRE happens to diff bank as this entry
  cp_wr_cam_entry_valid_pre_w_diff_bank :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && ((r_te_rdwr_autopre && ~r_same_bank_rdwr_op) || (r_ts_op_is_precharge && ~r_same_pre_bank))));

  // When CAM entry is valid, a PRE happens to the same bank as this entry
  cp_wr_cam_entry_valid_pre_w_same_bank :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && ((r_te_rdwr_autopre && r_same_bank_rdwr_op) || (r_ts_op_is_precharge && r_same_pre_bank))));

generate
  // In inline ECC configuration, 1/3 WR CAM is dedicated for WR ECC, and these WR ECC CAM has no VPRW.
  // So in te_wr_entry.sv, if IE_WR_ECC_ENTRY=1, this coverpoints must be disabled.
  if (IE_WR_ECC_ENTRY==0) begin : CP_WR_CAM

  // Check that the entry goes to expired VPW at some point
  cp_wr_cam_vpw_to_exp_vpw :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_out_pri == CMD_PRI_XVPW));

  // Check that the entry load happens with latency at 0
  cp_wr_cam_entry_load_w_latency_0 :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_load && (ih_te_wr_latency == {WR_LATENCY_BITS{1'b0}}));

  // Check that the entry delete happens with latency at 0
  cp_wr_cam_entry_delete_w_latency_0 :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_entry_del && (i_entry_vpw_latency == {WR_LATENCY_BITS{1'b0}}));

  // Check that the entry delete happens with latency at 1
  cp_wr_cam_entry_delete_w_latency_1 :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_entry_del && (i_entry_vpw_latency == {{(WR_LATENCY_BITS-1){1'b0}},1'b1}));

  // Removing cp_wr_cam_wr_combine_w_xvpw, looks obsolete since MEMC_NO_COL was removed, i_combine_match & ~i_combine_match == 0 always
  // Check that write combine happens when the entry is in EXP-VPW state
  //cp_wr_cam_wr_combine_w_xvpw :
  //cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_vpw_timed_out & i_combine_match));

  end
endgenerate

//---------
// Monitor code for the VPW and expired-VPW entries in the CAM  - Keeps count on how many cycles the entry stays in CAM
//
// Counter keeps a count of the number of clocks VPW and expired-VPW commands stays in the CAM. 
// When an entry is deleted, the final number saved in a register. When a new command is loaded in the CAM entry, 
// the counting is done again. When this entry is removed, the final count of the new value is compared with the 
// value of the previous command, and the larger of the two values is preserved. This is continued until the 
// end of the test. When the test ends, each CAM entry that had a VPW and/or expired-VPW command, will have a 
// number that gives the maximum number of clocks these command spent in that entry in VPW or expired-VPW status.
//---------

// disable coverage collection as this is a check in SVA only        
// VCS coverage off
reg [9:0] num_clks_spent_as_exp_vpw;
reg [9:0] max_num_clks_spent_as_exp_vpw;

reg [15:0] num_clks_spent_as_vpw_or_expvpw;
reg [15:0] max_num_clks_spent_as_vpw_or_expvpw;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
    num_clks_spent_as_exp_vpw     <= 10'h0;
    max_num_clks_spent_as_exp_vpw <= 10'h0;
    num_clks_spent_as_vpw_or_expvpw <= 16'h0;
    max_num_clks_spent_as_vpw_or_expvpw <= 16'h0;
  end
  else begin

    if(i_entry_del)
       num_clks_spent_as_exp_vpw <= 10'h0;
    else if(i_entry_valid & (i_entry_out_pri == CMD_PRI_XVPW))
       num_clks_spent_as_exp_vpw <= num_clks_spent_as_exp_vpw + 1'b1;

    if(i_entry_del)
       max_num_clks_spent_as_exp_vpw <= (num_clks_spent_as_exp_vpw >= max_num_clks_spent_as_exp_vpw) ? num_clks_spent_as_exp_vpw : max_num_clks_spent_as_exp_vpw;



    if(i_entry_del)
       num_clks_spent_as_vpw_or_expvpw <= 16'h0;
    else if(i_entry_valid & ((i_entry_out_pri == CMD_PRI_VPW) || (i_entry_out_pri == CMD_PRI_XVPW)))
       num_clks_spent_as_vpw_or_expvpw <= num_clks_spent_as_vpw_or_expvpw + 1'b1;

    if(i_entry_del)
       max_num_clks_spent_as_vpw_or_expvpw <= (num_clks_spent_as_vpw_or_expvpw >= max_num_clks_spent_as_vpw_or_expvpw) ?
                                           num_clks_spent_as_vpw_or_expvpw : max_num_clks_spent_as_vpw_or_expvpw;

  end
end
// VCS coverage on





covergroup cg_wr_entry_ie_cmd_type @(posedge co_te_clk); 

  // Observe all Inline ECC command type are stored
  cp_ie_cmd_type: coverpoint (i_entry_wr_type) iff(core_ddrc_rstn & i_entry_loaded) {
            bins WD_N   = {`IE_WR_TYPE_WD_N  };
            bins WD_E   = {`IE_WR_TYPE_WD_E  };
            bins WE_BW  = {`IE_WR_TYPE_WE_BW };
    illegal_bins OTHER  = default;
  }


  // Observe all Priority are stored
  cp_ie_pri : coverpoint (i_entry_out_pri) iff (core_ddrc_rstn & i_entry_loaded) {
            bins NPW    = {CMD_PRI_NPW}; 
            bins VPW    = {CMD_PRI_VPW}; 
            bins XVPW   = {CMD_PRI_XVPW};
    illegal_bins RSVD   = {CMD_PRI_RSVD};
  }

  // Observe all allowed Priority VS Inline ECC command type are stored
  cx_ie_cmd_type_pri : cross cp_ie_cmd_type, cp_ie_pri {
    illegal_bins WE_BW_VPW  = binsof(cp_ie_cmd_type.WE_BW)  && binsof(cp_ie_pri.VPW);
    illegal_bins WE_BW_XVPW = binsof(cp_ie_cmd_type.WE_BW)  && binsof(cp_ie_pri.XVPW);
  }

  cp_ie_wr_entry_collision: coverpoint({i_entry_wr_type,ih_te_ie_rd_type,ih_te_ie_wr_type}) iff (core_ddrc_rstn & i_same_addr_wr) {
   wildcard         bins WD_N_vs_RD_N   = {{`IE_WR_TYPE_WD_N ,`IE_RD_TYPE_RD_N  ,2'b??             }};
   wildcard         bins WD_N_vs_RD_E   = {{`IE_WR_TYPE_WD_N ,`IE_RD_TYPE_RD_E  ,2'b??             }};
   wildcard         bins WD_N_vs_RE_B   = {{`IE_WR_TYPE_WD_N ,`IE_RD_TYPE_RE_B  ,2'b??             }};
   wildcard         bins WD_N_vs_WD_N   = {{`IE_WR_TYPE_WD_N ,2'b??             ,`IE_WR_TYPE_WD_N  }};
   wildcard         bins WD_N_vs_WD_E   = {{`IE_WR_TYPE_WD_N ,2'b??             ,`IE_WR_TYPE_WD_E  }};
   wildcard illegal_bins WD_N_vs_WE_BW  = {{`IE_WR_TYPE_WD_N ,2'b??             ,`IE_WR_TYPE_WE_BW }};
   wildcard         bins WD_E_vs_RD_N   = {{`IE_WR_TYPE_WD_E ,`IE_RD_TYPE_RD_N  ,2'b??             }};
   wildcard         bins WD_E_vs_RD_E   = {{`IE_WR_TYPE_WD_E ,`IE_RD_TYPE_RD_E  ,2'b??             }};
   wildcard         bins WD_E_vs_RE_B   = {{`IE_WR_TYPE_WD_E ,`IE_RD_TYPE_RE_B  ,2'b??             }};
   wildcard         bins WD_E_vs_WD_N   = {{`IE_WR_TYPE_WD_E ,2'b??             ,`IE_WR_TYPE_WD_N  }};
   wildcard         bins WD_E_vs_WD_E   = {{`IE_WR_TYPE_WD_E ,2'b??             ,`IE_WR_TYPE_WD_E  }};
   wildcard illegal_bins WD_E_vs_WE_BW  = {{`IE_WR_TYPE_WD_E ,2'b??             ,`IE_WR_TYPE_WE_BW }};
   wildcard         bins WE_BW_vs_RD_N  = {{`IE_WR_TYPE_WE_BW,`IE_RD_TYPE_RD_N  ,2'b??             }};
   wildcard         bins WE_BW_vs_RD_E  = {{`IE_WR_TYPE_WE_BW,`IE_RD_TYPE_RD_E  ,2'b??             }}; // For col3 collision case
   wildcard         bins WE_BW_vs_RE_B  = {{`IE_WR_TYPE_WE_BW,`IE_RD_TYPE_RE_B  ,2'b??             }};
   wildcard         bins WE_BW_vs_WD_N  = {{`IE_WR_TYPE_WE_BW,2'b??             ,`IE_WR_TYPE_WD_N  }};
   wildcard         bins WE_BW_vs_WD_E  = {{`IE_WR_TYPE_WE_BW,2'b??             ,`IE_WR_TYPE_WD_E  }};
   wildcard         bins WE_BW_vs_WE_BW = {{`IE_WR_TYPE_WE_BW,2'b??             ,`IE_WR_TYPE_WE_BW }};
   }

endgroup: cg_wr_entry_ie_cmd_type

// Coverage group instantiation
cg_wr_entry_ie_cmd_type cg_wr_entry_ie_cmd_type_inst = new;


  // Check that ECCAP must be 0 for overhead ECC command
  property p_eccap_wrcam_must_be_zero_for_overhead_command;
    @ (posedge co_te_clk) disable iff (!core_ddrc_rstn)
    (i_entry_loaded && (i_entry_wr_type==`IE_WR_TYPE_WE_BW)) |->
        (r_entry[ENTRY_ECCAP_MSB:ENTRY_ECCAP_LSB]==1'b0);
  endproperty

  a_eccap_wrcam_must_be_zero_for_overhead_command : assert property (p_eccap_wrcam_must_be_zero_for_overhead_command)
    else $error("%0t ERROR: ECC AP field must be 0 for overhead ECC command.", $time);



  
wire i_load_when_page_hit_limit_reached;
wire i_load_when_page_hit_limit_reaching;
wire i_sch_when_entry_critical_early; //entry was already loaded
wire i_same_bank_inc_as_rdwr_op;
wire r_same_bank_inc_as_pre;
wire r_same_bank_inc_as_any_op1;

assign i_same_bank_inc_as_rdwr_op    = &(ih_te_wr_rankbank_num ~^ ts_bsm_num4rdwr);
assign r_same_bank_inc_as_pre        = &(ih_te_wr_rankbank_num ~^ r_ts_bsm_num4pre);
assign r_same_bank_inc_as_any_op1    = &(ih_te_wr_rankbank_num ~^ r_ts_bsm_num4rdwr);

assign i_load_when_page_hit_limit_reached = i_load & (page_hit_limit_reached_incoming);
assign i_load_when_page_hit_limit_reaching = i_load &  (page_hit_limit_incoming & ts_op_is_wr & i_same_bank_inc_as_rdwr_op);
assign i_sch_when_entry_critical_early = !i_entry_del & i_entry_loaded & (i_same_bank_as_rdwr_op & ts_op_is_wr & i_entry_critical_early);
assign i_set_page_close_when_load  = i_load & ( (r_te_rdwr_autopre & r_same_bank_inc_as_any_op1) | (r_ts_op_is_precharge & r_same_bank_inc_as_pre) );

//Assertion to check critical assert when the entry is loading and page_hit_limiter is reached
property p_i_load_when_page_hit_limit_reached;
  @ (negedge co_te_clk) disable iff (~core_ddrc_rstn || (IE_WR_ECC_ENTRY==1))
    i_load_when_page_hit_limit_reached |=> i_entry_critical==1'b1;
endproperty

//Assertion to check critical assert when the entry is loading and page_hit_limiter is just reaching and a pagehit is scheduled
property p_i_load_when_page_hit_limit_reaching;
  @ (negedge co_te_clk) disable iff (~core_ddrc_rstn || (IE_WR_ECC_ENTRY==1))
    i_load_when_page_hit_limit_reaching |=> i_entry_critical==1'b1;
endproperty

//Assertion to check critical assert when the entry is set to critical early and a pagehit is scheduled
property p_i_sch_when_entry_critical_early;
  @ (negedge co_te_clk) disable iff (~core_ddrc_rstn || (IE_WR_ECC_ENTRY==1))
    i_sch_when_entry_critical_early |=> i_entry_critical==1'b1;
endproperty

//Assertion to check critical de-assert when the a precharge or aoto-pre command to the bank of this entry
property p_set_page_close_for_pre_clr_critical;
  @ (negedge co_te_clk) disable iff (~core_ddrc_rstn || (IE_WR_ECC_ENTRY==1))
    set_page_close_for_pre & i_entry_loaded |=> i_entry_critical==1'b0;
endproperty

//Assertion to check critical_early de-assert when the a precharge or aoto-pre command to the bank of this entry
property p_set_page_close_for_pre_clr_critical_early;
  @ (negedge co_te_clk) disable iff (~core_ddrc_rstn)
    set_page_close_for_pre & i_entry_loaded |=> i_entry_critical_early==1'b0;
endproperty
//when the entry is loaded, and set page close for the bank of this entry, page_hit_limit_incoming and page_hit_limit_reached_incoming should not asserted to set entry_critical or entry_critical_early.
property p_set_page_close_when_load_no_page_hit_limit;
  @ (negedge co_te_clk) disable iff (~core_ddrc_rstn)
    i_set_page_close_when_load |-> ~page_hit_limit_incoming & ~page_hit_limit_reached_incoming;
endproperty

generate
  if (IE_WR_ECC_ENTRY==0) begin : WRCAM_ENTRY5
a_i_load_when_page_hit_limit_reached : assert property (p_i_load_when_page_hit_limit_reached);
a_i_load_when_page_hit_limit_reaching : assert property (p_i_load_when_page_hit_limit_reaching);
a_i_sch_when_entry_critical_early : assert property (p_i_sch_when_entry_critical_early);
a_set_page_close_for_pre_clr_critical: assert property (p_set_page_close_for_pre_clr_critical);
a_set_page_close_for_pre_clr_critical_early: assert property (p_set_page_close_for_pre_clr_critical_early);
a_set_page_close_when_load_no_page_hit_limit: assert property (p_set_page_close_when_load_no_page_hit_limit);
  end
endgenerate


covergroup cg_pagehit_limit @(posedge co_te_clk); 

  cp_entry_critical: coverpoint ({i_load_when_page_hit_limit_reached,i_load_when_page_hit_limit_reaching, i_set_page_close_when_load, i_sch_when_entry_critical_early, set_page_close_for_pre}) iff(core_ddrc_rstn) {
            bins  load_reached       = {5'b10000};
            bins  load_reaching      = {5'b01000};
            bins  load_pre           = {5'b00100};
            bins  sch_to_reached     = {5'b00010};
            bins  pre_to_clr         = {5'b00001};
  }
endgroup: cg_pagehit_limit

cg_pagehit_limit cg_pagehit_limit_inst = new;




assign i_entry_loaded_sva = i_entry_loaded;






`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS

endmodule // te_wr_entry
