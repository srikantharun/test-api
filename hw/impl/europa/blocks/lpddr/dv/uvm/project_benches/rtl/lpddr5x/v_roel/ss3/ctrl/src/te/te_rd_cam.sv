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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_rd_cam.sv#6 $
// -------------------------------------------------------------------------
// Description:
//
// This module handles the entry insertion and deletion of a read cam,
//   and also the flush i_page_hit request if there is collision.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_rd_cam #(
   //---------------------------- PARAMETERS --------------------------------------
    parameter         RD_CAM_ADDR_BITS       = `MEMC_RDCMD_ENTRY_BITS
   ,parameter         RD_CAM_ENTRIES         = `MEMC_NO_OF_RD_ENTRY 
   ,parameter         RANK_BITS              = 2
   ,parameter         BG_BITS                = 2
   ,parameter         BANK_BITS              = 3
   ,parameter         BG_BANK_BITS           = 4
   ,parameter         RANKBANK_BITS          = RANK_BITS + BG_BANK_BITS
   ,parameter         PAGE_BITS              = 16
   ,parameter         BLK_BITS               = 10
   ,parameter         BSM_BITS               = `UMCTL2_BSM_BITS
   ,parameter         OTHER_RD_RMW_LSB       = `MEMC_TAGBITS 
   ,parameter         OTHER_RD_RMW_TYPE_BITS = 2
   ,parameter         OTHER_RD_ENTRY_BITS    = 31                               // override this
   ,parameter         ENTRY_AUTOPRE_BITS     = 1
   ,parameter         RD_LATENCY_BITS        = `UMCTL2_XPI_RQOS_TW
   ,parameter         BT_BITS                = `MEMC_BLK_TOKEN_BITS // Override
   ,parameter         NO_OF_BT               = `MEMC_NO_OF_BLK_TOKEN // Override
   ,parameter         IE_WR_TYPE_BITS        = 2 // Override
   ,parameter         IE_RD_TYPE_BITS        = 2 // Override
   ,parameter         IE_BURST_NUM_BITS      = 3
   ,parameter         IE_UNIQ_BLK_BITS       = 4
   ,parameter         IE_UNIQ_BLK_LSB        = 3
   ,parameter         IE_MASKED_BITS         = 1
   ,parameter         ECCAP_BITS             = 1
   ,parameter         DDR4_COL3_BITS         = 1
   ,parameter         LP_COL4_BITS           = 1
   ,parameter         RMW_BITS               = 1
   ,parameter         NUM_RANKS              = `MEMC_NUM_RANKS
    // 2-bit read priority encoding
   ,parameter         CMD_PRI_LPR            = `MEMC_CMD_PRI_LPR
   ,parameter         CMD_PRI_VPR            = `MEMC_CMD_PRI_VPR
   ,parameter         CMD_PRI_HPR            = `MEMC_CMD_PRI_HPR
   ,parameter         CMD_PRI_XVPR           = `MEMC_CMD_PRI_XVPR
   ,parameter         NUM_TOTAL_BSMS         = `UMCTL2_NUM_BSM
   ,parameter         ALLOC_BITS             = 1
   ,parameter         NUM_TOTAL_BANKS        = 1 << RANKBANK_BITS
   ,parameter         IE_TAG_BITS            = IE_RD_TYPE_BITS + IE_BURST_NUM_BITS + BT_BITS + ECCAP_BITS 
   ,parameter         CMD_LEN_BITS           = 1
   ,parameter         WORD_BITS              = `MEMC_WORD_BITS
   ,parameter         RETRY_RD_BITS          = 1
   ,parameter         RETRY_TIMES_WIDTH      = 3
   ,parameter         CRC_RETRY_TIMES_WIDTH  = 4
   ,parameter         UE_RETRY_TIMES_WIDTH   = 4
   ,parameter         RD_CRC_RETRY_LIMIT_REACH_BITS = 1
   ,parameter         RD_UE_RETRY_LIMIT_REACH_BITS = 1
  )
  (
   //----------------------- INPUTS AND OUTPUTS -----------------------------------
    input                                            core_ddrc_rstn             // reset
   ,input                                            dh_te_pageclose            // when 1: use the pageclose feature
   ,input   [7:0]                                    dh_te_pageclose_timer 
   ,input                                            co_te_clk                  // main clock
   ,input                                            ddrc_cg_en                 // clock gating enable signal - used in all the flops
   ,input                                            i_rd_command               // valid read command
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used under different `ifdefs. Decided to keep current coding style for now.
   ,input                                            i_wr_command               // valid write command
//spyglass enable_block W240
   ,output [RD_CAM_ENTRIES*RANKBANK_BITS-1:0]        te_rd_entry_rankbank       // rankbank number of all CAM entries to BM
   ,output [RD_CAM_ENTRIES*BSM_BITS-1:0]             te_rd_entry_bsm_num        // BSM number of all CAM entries
   ,input  [RANK_BITS-1:0]                           ih_te_rd_rank_num          // rank number
   ,input  [BG_BANK_BITS-1:0]                        ih_te_rd_bg_bank_num       // bank number
   ,input  [PAGE_BITS-1:0]                           ih_te_rd_page_num          // page number
   ,input  [BLK_BITS-1:0]                            ih_te_rd_block_num         // block (column) number
   ,input                                            ih_te_rd_autopre           // 1=auto precharge enabled on current request
   ,input  [CMD_LEN_BITS-1:0]                        ih_te_rd_length
   ,input  [WORD_BITS-1:0]                           ih_te_critical_dword
   ,input  [OTHER_RD_ENTRY_BITS-1:0]                 ih_te_rd_other_fields      // everything else TE needs to track in the read CAM
   ,input                                            ih_te_rmw                  // 1=read is part of a read-modify-write
   ,input  [RD_CAM_ENTRIES-1:0]                      rd_nxt_entry_in_ntt        // this entry is in NTT
   ,input                                            reg_ddrc_dis_opt_ntt_by_act 
   ,input                                            gs_te_wr_mode              // 1: Write mode 0: Read mode
   ,input  [RD_CAM_ADDR_BITS -1:0]                   te_lo_rd_prefer            // low priority read prefer location
   ,input  [1:0]                                     ih_te_hi_pri               // 1=read is high priority
   ,input  [RD_CAM_ADDR_BITS -1:0]                   te_hi_rd_prefer            // high priority read prefer location
   ,input  [RD_LATENCY_BITS-1:0]                     ih_te_rd_latency           // read latency for VPR commands
   ,output reg                                       te_gs_any_vpr_timed_out    // signal indicating that any of the VPR entries have timed-out
                                                                                // this signal goes to the GS - gs_global_fsm.v - module
                                                                                // and is used for switching from WR to RD state, if the FSM is in WR state
   ,output                                           te_gs_any_vpr_timed_out_w
   ,output [RD_CAM_ENTRIES -1:0]                     te_vpr_valid               // indicates the valid expired-vpr commands to VPR selection n/w
   ,output [RD_CAM_ENTRIES -1:0]                     te_vpr_valid_d             // indicates the valid expired-vpr commands to VPR selection n/w
   ,output [RD_CAM_ENTRIES -1:0]                     te_vpr_page_hit            // indicates the page hit status of the expired-vpr cmds to VPR selection n/w 
   ,output [RD_CAM_ENTRIES -1:0]                     upd_to_vpr_due_ie          // indicates the entry to vpr due to inline ecc, only used for assertion  
   ,input                                            te_yy_wr_combine           // write combine this cycle; don't flush
   ,input                                            te_ih_rd_retry             // collision detected
   ,output [BSM_BITS -1:0]                           te_ts_hi_bsm_hint          // high priority BSM hint
   ,output [BSM_BITS -1:0]                           te_ts_lo_bsm_hint          // low priority BSM hint
   ,output reg[RD_CAM_ENTRIES -1:0]                  te_entry_pri               // entries with high priority
   ,output [RD_CAM_ENTRIES -1:0]                     te_entry_hpr               // entries with HPR | HPRL
   ,output                                           te_rd_flush_due_rd
   ,output                                           te_rd_flush_due_wr
   ,output                                           te_rd_flush                // flush for write colliding with read address
   ,output                                           te_rd_flush_started        // flush has started (clean off a flop)
   ,output reg[RD_CAM_ADDR_BITS -1:0]                te_rd_col_entry            // flopped version of collided entry number
   ,input                                            be_op_is_activate_bypass   // ACT initiated from BE 
   ,output                                           ddrc_co_perf_war_hazard    // pulses for every war collision
   ,output                                           ddrc_co_perf_ie_blk_hazard_rd    // pulses for every block address collision
   ,output                                           ddrc_co_perf_vlimit_reached_rd
   ,output [BSM_BITS -1:0]                           te_ts_act_bsm_hint         // low priority BSM hint
   ,input                                            be_te_page_hit             // the incoming entry from IH has a current page hit, used to update the page status bit
   ,input  [BSM_BITS-1:0]                            ts_bsm_num4pre
   ,input  [BSM_BITS-1:0]                            ts_bsm_num4act
   ,input                                            te_rdwr_autopre
   ,input                                            ts_op_is_precharge
   ,input                                            ts_op_is_activate
   ,input  [PAGE_BITS-1:0]                           ts_act_page                // row address
   ,input  [RD_CAM_ADDR_BITS -1:0]                   ih_te_rd_entry_num         // allocated entry number
   ,input  [BT_BITS-1:0]                             ih_te_ie_bt
   ,input  [IE_WR_TYPE_BITS-1:0]                     ih_te_ie_wr_type
   ,input  [IE_RD_TYPE_BITS-1:0]                     ih_te_ie_rd_type
   ,input  [IE_BURST_NUM_BITS-1:0]                   ih_te_ie_blk_burst_num
   ,input  [IE_UNIQ_BLK_BITS-1:0]                    ie_ecc_uniq_block_num
   ,input  [ECCAP_BITS-1:0]                          ih_te_rd_eccap
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
`endif
`endif
   ,input  [BSM_BITS -1:0]                           ts_bsm_num4rdwr            // DRAM op BSM number
   ,input                                            ts_op_is_rd                // DRAM op is read
   ,output [RD_CAM_ENTRIES*PAGE_BITS-1:0]            te_rd_page_table           // page addresses of all CAM entries
   ,input  [RD_CAM_ADDR_BITS -1:0]                   te_rd_entry                // next transaction entry for read only (not act/pre)
   ,output [RD_CAM_ENTRIES*ENTRY_AUTOPRE_BITS-1:0]   te_rd_cmd_autopre_table    // cmd_autopre of all CAM entries
   ,output [RD_CAM_ENTRIES*CMD_LEN_BITS-1:0]         te_rd_cmd_length_table
   ,output [RD_CAM_ENTRIES*WORD_BITS-1:0]            te_rd_critical_word_table
   ,output [PAGE_BITS-1:0]                           te_pi_rd_addr_ecc_row      // row address to be used for ECC error tracking
   ,output [BLK_BITS-1:0]                            te_pi_rd_addr_blk          // block(column) address
   ,output [OTHER_RD_ENTRY_BITS-1:0]                 te_pi_rd_other_fields_rd   // read tag, anything else required - during reads
//    ,output                                           te_pi_rd_autopre           // auto precharge bit
//    `ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
   ,output [CMD_LEN_BITS-1:0]                        te_pi_rd_length_int
   ,output [WORD_BITS-1:0]                           te_pi_rd_word_int
`endif
`endif
   ,output [NUM_TOTAL_BSMS-1:0]                      te_os_rd_pageclose_autopre
//    `endif                                                                       // this gives the correct row address for rd cmds, not for activates like the te_pi_rd_addr_row

   ,output [RD_CAM_ENTRIES -1:0]                     te_bank_hit                // entries with bank hit to the scheduled RD
   ,output [RD_CAM_ENTRIES -1:0]                     te_bank_hit_pre            // entries with bank hit to the scheduled PRE
   ,output [RD_CAM_ENTRIES -1:0]                     te_page_hit                // entries with page hit to the scheduled RD
   ,output [RD_CAM_ENTRIES -1:0]                     te_entry_valid             // valid read entry in CAM, over entire CAM 
   ,output [RD_CAM_ENTRIES -1:0]                     te_entry_loaded            // loaded read entry in CAM, over entire CAM 
//    ,input  [ENTRY_AUTOPRE_BITS-1:0]                  ts_rdwr_cmd_autopre
   ,output [RD_CAM_ENTRIES*IE_TAG_BITS-1:0]          te_rd_ie_tag_table
   ,input  [BT_BITS-1:0]                             te_pi_ie_bt
   ,input  [IE_RD_TYPE_BITS-1:0]                     te_pi_ie_rd_type
   ,output                                           i_rd_ecc_status            // Indicate this incoming RD command cannot get scheduled for now
   ,input  [2:0]                                     reg_ddrc_page_hit_limit_rd
   ,output [RD_CAM_ENTRIES-1:0]                      te_entry_critical_early
   ,output  [NUM_TOTAL_BSMS -1:0]                    te_entry_critical_per_bsm
   ,input  [2:0]                                     reg_ddrc_visible_window_limit_rd
   ,input  [RD_CAM_ENTRIES-1:0]                      te_rd_vlimit_decr
  
`ifdef SNPS_ASSERT_ON
   ,output [BT_BITS-1:0]                             i_te_pi_ie_bt
   ,output [IE_RD_TYPE_BITS-1:0]                     i_te_pi_ie_rd_type
   ,output [IE_BURST_NUM_BITS-1:0]                   i_te_pi_ie_blk_burst_num
   ,output [RD_CAM_ENTRIES-1:0]                      i_ie_rd_blk_addr_collision  // For coverpoint
   ,output [ECCAP_BITS-1:0]                          i_te_pi_eccap
  `ifndef SYNTHESIS
   // for assertions
   ,input                                            te_ih_retry
   ,input                                            ih_te_wr_valid
   ,input                                            gs_te_op_is_wr
   ,input [IE_WR_TYPE_BITS-1:0]                      te_mr_ie_wr_type
   ,input [BT_BITS-1:0]                              te_mr_ie_bt
  `endif
`endif
   ,input  [NUM_TOTAL_BSMS-1:0]                      ts_te_sel_act_wr         //tell TE the activate command is for write or read.
   ,input                                            ih_gs_rdhigh_empty       // no high priority reads pending
   ,input                                            ih_gs_rdlow_empty        // no low priority reads pending
   ,input                                            gs_te_pri_level          // 1=prefer high priority  0=prefer low
   ,output reg [RANKBANK_BITS-1:0]                   te_rd_rankbank_prefer    // cid and rank number of oldest entry
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
   ,input                                            reg_ddrc_opt_vprw_sch
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
  );

  //------------------------- LOCAL PARAMETERS -----------------------------------
  localparam         ENTRY_AUTOPRE_LSB      = 0;
  localparam         ENTRY_AUTOPRE_MSB      = ENTRY_AUTOPRE_LSB + ENTRY_AUTOPRE_BITS - 1;
  localparam         ENTRY_BLK_LSB          = ENTRY_AUTOPRE_MSB + 1;
  localparam         ENTRY_BLK_MSB          = ENTRY_BLK_LSB + BLK_BITS - 1;
  localparam         ENTRY_ROW_LSB          = ENTRY_BLK_MSB + 1;
  localparam         ENTRY_ROW_MSB          = ENTRY_ROW_LSB + PAGE_BITS - 1;
  localparam         ENTRY_RANKBANK_LSB     = ENTRY_ROW_MSB + 1;
  localparam         ENTRY_RANKBANK_MSB     = ENTRY_RANKBANK_LSB + RANKBANK_BITS - 1;
  localparam         ENTRY_BANK_LSB         = ENTRY_ROW_MSB + 1;
  localparam         ENTRY_BANK_MSB         = ENTRY_BANK_LSB + BG_BANK_BITS - 1;
  localparam         ENTRY_RANK_LSB         = ENTRY_BANK_MSB + 1;
  localparam         ENTRY_RANK_MSB         = ENTRY_RANK_LSB + RANK_BITS - 1;
  localparam         ENTRY_IE_BT_LSB        = ENTRY_RANKBANK_MSB + 1;
  localparam         ENTRY_IE_BT_MSB        = ENTRY_IE_BT_LSB + BT_BITS - 1;
  localparam         ENTRY_IE_RD_TYPE_LSB   = ENTRY_IE_BT_MSB + 1;
  localparam         ENTRY_IE_RD_TYPE_MSB   = ENTRY_IE_RD_TYPE_LSB + IE_RD_TYPE_BITS - 1;
  localparam         ENTRY_IE_BURST_NUM_LSB = ENTRY_IE_RD_TYPE_MSB + 1;
  localparam         ENTRY_IE_BURST_NUM_MSB = ENTRY_IE_BURST_NUM_LSB + IE_BURST_NUM_BITS - 1;
  localparam         ENTRY_ECCAP_LSB        = ENTRY_IE_BURST_NUM_MSB + 1;
  localparam         ENTRY_ECCAP_MSB        = ENTRY_ECCAP_LSB + ECCAP_BITS - 1;
  localparam         ENTRY_RETRY_RD_LSB     = ENTRY_ECCAP_MSB + 1;
  localparam         ENTRY_RETRY_RD_MSB     = ENTRY_RETRY_RD_LSB + RETRY_RD_BITS - 1;
  localparam         ENTRY_CRC_RETRY_TIMES_LSB  = ENTRY_RETRY_RD_MSB + 1;
  localparam         ENTRY_CRC_RETRY_TIMES_MSB  = ENTRY_CRC_RETRY_TIMES_LSB + CRC_RETRY_TIMES_WIDTH -1;
  localparam         ENTRY_UE_RETRY_TIMES_LSB   = ENTRY_CRC_RETRY_TIMES_MSB + 1;
  localparam         ENTRY_UE_RETRY_TIMES_MSB   = ENTRY_UE_RETRY_TIMES_LSB + UE_RETRY_TIMES_WIDTH -1;
  localparam         ENTRY_RD_CRC_RETRY_LIMIT_REACH_LSB = ENTRY_UE_RETRY_TIMES_MSB + 1;
  localparam         ENTRY_RD_CRC_RETRY_LIMIT_REACH_MSB = ENTRY_RD_CRC_RETRY_LIMIT_REACH_LSB + RD_CRC_RETRY_LIMIT_REACH_BITS -1;
  localparam         ENTRY_RD_UE_RETRY_LIMIT_REACH_LSB = ENTRY_RD_CRC_RETRY_LIMIT_REACH_MSB + 1;
  localparam         ENTRY_RD_UE_RETRY_LIMIT_REACH_MSB = ENTRY_RD_UE_RETRY_LIMIT_REACH_LSB + RD_UE_RETRY_LIMIT_REACH_BITS -1;
  localparam         ENTRY_DDR4_COL3_LSB    = ENTRY_RD_UE_RETRY_LIMIT_REACH_MSB + 1;
  localparam         ENTRY_DDR4_COL3_MSB    = ENTRY_DDR4_COL3_LSB + DDR4_COL3_BITS - 1;
  localparam         ENTRY_LP_COL4_LSB      = ENTRY_DDR4_COL3_MSB + 1;
  localparam         ENTRY_LP_COL4_MSB      = ENTRY_LP_COL4_LSB + LP_COL4_BITS - 1;
  localparam         ENTRY_OTHER_LSB        = ENTRY_LP_COL4_MSB + 1;
  localparam         ENTRY_OTHER_MSB        = ENTRY_OTHER_LSB + OTHER_RD_ENTRY_BITS - 1;
  localparam         ENTRY_LENGTH_LSB       = ENTRY_OTHER_MSB + 1;
  localparam         ENTRY_LENGTH_MSB       = ENTRY_LENGTH_LSB + CMD_LEN_BITS - 1;
  localparam         ENTRY_WORD_LSB         = ENTRY_LENGTH_MSB + 1;
  localparam         ENTRY_WORD_MSB         = ENTRY_WORD_LSB + WORD_BITS - 1;
  localparam         ENTRY_BITS             = ENTRY_WORD_MSB  + 1;
  
  //localparam         ENTRY_RD_DATA_READY = ENTRY_OTHER_MSB + 1;         // for writes only
  //localparam         ENTRY_WR_DATA_READY = ENTRY_RD_DATA_READY + 1;     // for writes only

//---------------------------- REGS AND WIRES ----------------------------------

wire [RD_CAM_ENTRIES-1:0]              i_entry_vpr_timed_out;                // individual VPR time-out signals from entries
wire                                   any_vpr_timed_out;
// wire                                   autopre_for_pageclose;                // auto-pre generated for pageclose feature
reg  [RD_CAM_ENTRIES-1:0]              i_load_en;                            // load incoming command to the selected entry
reg  [RD_CAM_ENTRIES-1:0]              i_del_en;                             // delete selected stored entry
wire [(RD_CAM_ENTRIES*ENTRY_BITS)-1:0] i_entry;                              // contents of all the entries
wire [RD_CAM_ENTRIES-1:0]              i_same_addr_rd;                       // stored xact has the same addr as incoming command
wire [RD_CAM_ENTRIES-1:0]              i_same_addr_rmw;                      // stored xact has the same addr as incoming command
wire [RD_CAM_ENTRIES*2-1:0]            i_entry_pri;                          // internal signal of the priority of the entry
wire                                   te_rd_flush_enable;                   // flush enable
wire [RD_CAM_ADDR_BITS -1:0]           i_col_entry;
wire [BSM_BITS-1:0]                    i_lo_bsm_hint;
wire [BSM_BITS-1:0]                    i_hi_bsm_hint;
reg                                    r_flush;  // reg to signal the flush until collided entry is services
wire                                   be_op_is_activate_bypass_int = be_op_is_activate_bypass;
wire [BSM_BITS-1:0]                    i_act_bsm_hint;
reg  [PAGE_BITS-1:0]                   r_ts_act_page;                        // Row address of the activated page during read mode
reg                                    r_ts_op_is_precharge;                 // precharge scheduled this cycle
reg                                    r_ts_op_is_activate;                  // activate scheduled this cycle
reg                                    r_te_rdwr_autopre;
reg  [BSM_BITS-1:0]                    r_ts_bsm_num4pre;                     // BSM numer of the precharge cmd selected by the scheduler   
reg  [BSM_BITS-1:0]                    r_ts_bsm_num4any;                     // BSM number for ACT, ACT bypass (uMCTL2), PRE or RDWR
reg  [BSM_BITS-1:0]                    r_ts_bsm_num4act;                     // BSM number for ACT, ACT bypass
reg  [BSM_BITS-1:0]                    r_ts_bsm_num4rdwr;                    // BSM number for RDWR   
reg                                    update_pageclose_autopre;             // operation ACT, ACT bypass, PRE or RDWR
reg                                    ts_op_is_activate_delay;              // For LPDDR5. When ACT/RD are issued at the same cycle, updating r_pageclose_autopre for bank of ACT is done in next cycle.
wire                                   load_cam;
wire [RD_CAM_ENTRIES -1:0]             pages_open_for_bank;                  // page is open if same bank of ACT, RDWR, or PRE one cycle earlier
wire                                   only_one_page_open_for_bank;          // there is exactly one entry with page open for the bank of ACT, RDWR, or PRE one cycle earlier
reg [NUM_TOTAL_BSMS-1:0]               r_pageclose_autopre;                  // per bank autopre flag 

wire [RD_CAM_ENTRIES-1:0]              i_same_addr_rd_filtered;
wire [RD_CAM_ENTRIES-1:0]              i_bank_hit;
wire [RD_CAM_ENTRIES-1:0]              i_bank_hit_act;
reg                                    r_ts_op_is_activate_wr;               // activate scheduled this cycle for WR
wire [RD_CAM_ENTRIES-1:0]              i_bank_hit_pre;
wire [RD_CAM_ENTRIES-1:0]              i_entry_critical_early;
reg  [4:0]                             page_hit_limit_int;
reg  [4:0]                             page_hit_limit_cnt [NUM_TOTAL_BSMS-1:0];
reg                                    page_hit_limit_reached;
reg  [NUM_TOTAL_BSMS-1:0]              i_entry_critical_per_bsm;
reg  [NUM_TOTAL_BSMS-1:0]              i_entry_critical_per_bsm_early;
wire [NUM_TOTAL_BSMS-1:0]              i_entry_critical_per_bsm_early_next;
wire                                   page_hit_limit_incoming;
reg  [8:0]                             vlimit_int;
wire [RD_CAM_ENTRIES-1:0]              te_rd_vlimit_reached;

wire rdwr_pol_sel;
assign rdwr_pol_sel = 1'b1; 


// te_bank_hit (filtered version)
assign te_bank_hit = 
                     r_ts_op_is_activate_wr  ? i_bank_hit_act : // Not filterd version as nothing is scheduled
                                              i_bank_hit & (~rd_nxt_entry_in_ntt); // Filterd version, entry already in ntt is served this cycle 


// te_bank_hit_pre
assign te_bank_hit_pre = i_bank_hit_pre;

reg  [NO_OF_BT-1:0]                    r_rd_ecc_status_bit;                  // RD ECC command status per bt. 0: RD_ECC has been served. 1: RD ECC has not been served.
localparam NO_OF_BT_POW2 = 2**(BT_BITS);
wire [NO_OF_BT_POW2-1:0] r_rd_ecc_status_bit_w;
//NO_OF_BT_POW2 >= NO_OF_BT
generate
  if(NO_OF_BT_POW2 == NO_OF_BT) begin:NO_OF_BT_pow2
assign r_rd_ecc_status_bit_w = r_rd_ecc_status_bit;
  end else begin:NO_OF_BT_pow2
assign r_rd_ecc_status_bit_w = {{(NO_OF_BT_POW2-NO_OF_BT){1'b0}},r_rd_ecc_status_bit};
  end
endgenerate

assign i_rd_ecc_status = r_rd_ecc_status_bit_w[ih_te_ie_bt]  // Flag (1 means corresponding RE_E has not been served)
                         & (ih_te_ie_rd_type == `IE_RD_TYPE_RD_E) // incoming command is RD_E which require the force ordering
                         & (~(ts_op_is_rd & (te_pi_ie_rd_type == `IE_RD_TYPE_RE_B) & (ih_te_ie_bt==te_pi_ie_bt))); // Serve RE_B this cycle. 

reg                                    te_normal_col_win_blk;                // Indicate there is normal collision within a block (OR'd and flopped)
wire [RD_CAM_ENTRIES-1:0]              i_ie_normal_col_win_blk;              // Indicate there is normal collision within a block

genvar bt_num;
generate
  for (bt_num=0;bt_num<NO_OF_BT;bt_num=bt_num+1) begin : rd_ecc_status_bit_GEN
   always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
     if (~core_ddrc_rstn) begin
       r_rd_ecc_status_bit[bt_num] <= 1'b0;
     end
     else begin
       // When RE_B command is entered to CAM, set corresponding bit = 1. 
       if (load_cam & (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B) & (bt_num == ih_te_ie_bt)) begin
         r_rd_ecc_status_bit[bt_num] <= 1'b1;
       end
       // When RE_B command is served, set corresponding bit = 0. This is exclusive event in terms of specific bit of r_rd_ecc_status_bit.
       else if (ts_op_is_rd & ((te_pi_ie_rd_type == `IE_RD_TYPE_RE_B) | (te_pi_ie_rd_type == `IE_RD_TYPE_RE_B)) & (bt_num == te_pi_ie_bt)) begin
         r_rd_ecc_status_bit[bt_num] <= 1'b0;
       end
     end
   end
 end
endgenerate

// OR'd i_ie_normal_col_win_blk
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_normal_col_win_blk <= 1'b0;
  end
  else begin
    te_normal_col_win_blk <= (|i_ie_normal_col_win_blk) // Normal address collision is detected within a ECC block 
                          & ((i_wr_command & (~te_yy_wr_combine)) | ((| i_same_addr_rmw [RD_CAM_ENTRIES -1:0]) & i_rd_command)); // RMW -> RD or R(RMW) -> W (except combine)
  end
end


wire [RD_CAM_ENTRIES-1:0] i_ie_blk_addr_collision;
reg                       i_ie_blk_addr_collision_or_r;

assign ddrc_co_perf_ie_blk_hazard_rd = (|i_ie_blk_addr_collision & te_rd_flush_enable & (~i_ie_blk_addr_collision_or_r) & (~r_flush));

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    i_ie_blk_addr_collision_or_r    <= 1'b0;
  end
  else begin
    i_ie_blk_addr_collision_or_r <= |i_ie_blk_addr_collision & te_rd_flush_enable;
  end
end



assign only_one_page_open_for_bank = /*|pages_open_for_bank &*/~|(pages_open_for_bank&(pages_open_for_bank -{{(RD_CAM_ENTRIES-1){1'b0}},1'b1}));   
 
// Update the per bank auto pre one cycle after every ACT, ACT bypass (uMCTL2), PRE or RDWR operation  
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    r_pageclose_autopre    <= {NUM_TOTAL_BSMS{1'b0}};
  end
  else begin
    if (update_pageclose_autopre)
      r_pageclose_autopre[r_ts_bsm_num4any]  <= only_one_page_open_for_bank;
  end
end


//----------------------------- MAINLINE CODE ----------------------------------

genvar cam_slot;
generate
    for (cam_slot = 0; cam_slot < RD_CAM_ENTRIES; cam_slot=cam_slot+1) begin : te_rd_entry_row_GEN
        assign te_rd_page_table[cam_slot*PAGE_BITS +: PAGE_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_ROW_LSB +: PAGE_BITS];
        assign te_rd_cmd_autopre_table[cam_slot*ENTRY_AUTOPRE_BITS +: ENTRY_AUTOPRE_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_AUTOPRE_LSB +: ENTRY_AUTOPRE_BITS];
        assign te_rd_entry_rankbank[cam_slot*RANKBANK_BITS +: RANKBANK_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS];
        assign te_rd_entry_bsm_num[cam_slot*BSM_BITS +: BSM_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS];
        assign te_rd_ie_tag_table[cam_slot*IE_TAG_BITS +: IE_TAG_BITS] =
        {
          i_entry[cam_slot*ENTRY_BITS + ENTRY_ECCAP_LSB +: ECCAP_BITS],
          i_entry[cam_slot*ENTRY_BITS + ENTRY_IE_RD_TYPE_LSB +: IE_RD_TYPE_BITS],
          i_entry[cam_slot*ENTRY_BITS + ENTRY_IE_BT_LSB +: BT_BITS],
          i_entry[cam_slot*ENTRY_BITS + ENTRY_IE_BURST_NUM_LSB +: IE_BURST_NUM_BITS]
        };
        assign te_rd_cmd_length_table[cam_slot*CMD_LEN_BITS +: CMD_LEN_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_LENGTH_LSB +: CMD_LEN_BITS];
                      

        assign te_rd_critical_word_table[cam_slot*WORD_BITS +: WORD_BITS] = i_entry[cam_slot*ENTRY_BITS + ENTRY_WORD_LSB +: WORD_BITS]; 
                     
    end
endgenerate



// decoder with enable to select the entry to store incoming transaction

assign load_cam = i_rd_command 
                  & (~te_ih_rd_retry)
;

always @(*)
begin: BLK_A
  i_load_en = {RD_CAM_ENTRIES{1'b0}};
  i_load_en [ih_te_rd_entry_num [RD_CAM_ADDR_BITS -1:0]] = load_cam;
end


// decoder with enable to select the entry to delete the transaction
always @(ts_op_is_rd or te_rd_entry)
begin: BLK_B
  i_del_en = {RD_CAM_ENTRIES{1'b0}};
  if (ts_op_is_rd)
    i_del_en [te_rd_entry [RD_CAM_ADDR_BITS -1:0]] = 1'b1;
end




reg [(RD_CAM_ENTRIES * ENTRY_BITS) -1:0]  bit_entry;  // group 1 bit of all the entry together

integer                                 bit_pos;
integer                                 entry;
wire [PAGE_BITS -1:0]           i_act_addr_ecc;                // address for activate commands
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((entry * ENTRY_BITS) + bit_pos)' found in module 'te_rd_cam'
//SJ: This coding style is acceptable and there is no plan to change it.

// reorder the bit position
always @(i_entry)
  for (bit_pos=0; bit_pos<ENTRY_BITS; bit_pos=bit_pos +1)
    for (entry=0; entry<RD_CAM_ENTRIES; entry=entry +1)
      bit_entry [bit_pos * RD_CAM_ENTRIES + entry] = i_entry [entry * ENTRY_BITS + bit_pos];

// inferring the muxes
genvar bit_loc;
generate    
  // mux out block address for PI
  for (bit_loc=ENTRY_BLK_LSB; bit_loc<=ENTRY_BLK_MSB; bit_loc=bit_loc+1)
  begin : pi_addr_blk
    te_rd_mux
     pi_addr_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_pi_rd_addr_blk [bit_loc-ENTRY_BLK_LSB])
                      );
  end

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
  // "Length Field" - during reads
  for (bit_loc=ENTRY_LENGTH_LSB; bit_loc<=ENTRY_LENGTH_MSB; bit_loc=bit_loc+1)
  begin : pi_length_int
    te_rd_mux
     pi_length_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_pi_rd_length_int [bit_loc-ENTRY_LENGTH_LSB])
                      );
  end

//Word Field during Reads
  for (bit_loc=ENTRY_WORD_LSB; bit_loc<=ENTRY_WORD_MSB; bit_loc=bit_loc+1)
  begin : pi_word_int
    te_rd_mux
     pi_word_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_pi_rd_word_int [bit_loc-ENTRY_WORD_LSB])
                      );
  end

`endif
`endif




  // "other fields" to PI - during reads
  for (bit_loc=ENTRY_OTHER_LSB; bit_loc<=ENTRY_OTHER_MSB; bit_loc=bit_loc+1)
  begin : pi_addr_other_fields_rd
    te_rd_mux
     pi_addr_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_pi_rd_other_fields_rd [bit_loc-ENTRY_OTHER_LSB])
                      );
  end

  // row address to PI and te_misc for ECC error updates
  for (bit_loc=ENTRY_ROW_LSB; bit_loc<=ENTRY_ROW_MSB; bit_loc=bit_loc+1)
  begin : pi_addr_ecc_row
    te_rd_mux
     act_ecc_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_act_addr_ecc [bit_loc-ENTRY_ROW_LSB])
                      );
  end
   
  // bank hint selection
  for (bit_loc=ENTRY_RANKBANK_LSB; bit_loc<=ENTRY_RANKBANK_MSB; bit_loc=bit_loc+1)
  begin : bsm_hint
    te_rd_mux
     lo_rd (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_lo_rd_prefer [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_lo_bsm_hint [bit_loc - ENTRY_RANKBANK_LSB])
                      );
    te_rd_mux
     hi_rd (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_hi_rd_prefer [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_hi_bsm_hint [bit_loc - ENTRY_RANKBANK_LSB])
                      );
  end

  assign te_ts_act_bsm_hint = te_ts_lo_bsm_hint; 



endgenerate
//spyglass enable_block SelfDeterminedExpr-ML
assign te_pi_rd_addr_ecc_row  = i_act_addr_ecc[PAGE_BITS-1:0];
   
// bank hint
  assign te_ts_hi_bsm_hint [BSM_BITS -1:0] = i_hi_bsm_hint [BSM_BITS -1:0];
  assign te_ts_lo_bsm_hint [BSM_BITS -1:0] = i_lo_bsm_hint [BSM_BITS -1:0];

// instantiate the entries
genvar entry_num;
generate
// _replace_P80001562-505275_: Need to change this for Synopsys
for (entry_num=0; entry_num<RD_CAM_ENTRIES; entry_num=entry_num+1)
begin: u0
  te_rd_entry
     #(.RANKBANK_BITS          (RANKBANK_BITS),
                  .PAGE_BITS              (PAGE_BITS),
                  .BLK_BITS               (BLK_BITS),
                  .BSM_BITS               (BSM_BITS),
                  .BG_BANK_BITS           (BG_BANK_BITS),
                  .RANK_BITS              (RANK_BITS),
                  .OTHER_ENTRY_BITS       (OTHER_RD_ENTRY_BITS),
                  .RMW_BITS               (RMW_BITS),
                  .BANK_BITS              (BANK_BITS),
                  .BG_BITS                (BG_BITS),
                  .RD_LATENCY_BITS        (RD_LATENCY_BITS),
                  .BT_BITS                (BT_BITS),
                  .IE_WR_TYPE_BITS        (IE_WR_TYPE_BITS),
                  .IE_RD_TYPE_BITS        (IE_RD_TYPE_BITS),
                  .IE_BURST_NUM_BITS      (IE_BURST_NUM_BITS),
                  .IE_UNIQ_BLK_BITS       (IE_UNIQ_BLK_BITS),
                  .IE_UNIQ_BLK_LSB        (IE_UNIQ_BLK_LSB),
                  .IE_MASKED_BITS         (IE_MASKED_BITS),
                  .ECCAP_BITS             (ECCAP_BITS), 
                  .RETRY_TIMES_WIDTH      (RETRY_TIMES_WIDTH),
                  .RETRY_RD_BITS          (RETRY_RD_BITS),
                  .CRC_RETRY_TIMES_WIDTH  (CRC_RETRY_TIMES_WIDTH),
                  .UE_RETRY_TIMES_WIDTH   (UE_RETRY_TIMES_WIDTH),
                  .RD_CRC_RETRY_LIMIT_REACH_BITS (RD_CRC_RETRY_LIMIT_REACH_BITS),
                  .RD_UE_RETRY_LIMIT_REACH_BITS (RD_UE_RETRY_LIMIT_REACH_BITS),
                  .DDR4_COL3_BITS         (DDR4_COL3_BITS),
                  .LP_COL4_BITS           (LP_COL4_BITS),
                  .AUTOPRE_BITS           (ENTRY_AUTOPRE_BITS),
                  .CMD_PRI_LPR            (CMD_PRI_LPR),
                  .CMD_PRI_VPR            (CMD_PRI_VPR),
                  .CMD_PRI_HPR            (CMD_PRI_HPR),
                  .CMD_PRI_XVPR           (CMD_PRI_XVPR),
                  .CMD_LEN_BITS           (CMD_LEN_BITS),
                  .WORD_BITS              (WORD_BITS)
                 )
           entry (
                 .core_ddrc_rstn           (core_ddrc_rstn)
                ,.co_te_clk                (co_te_clk)
                ,.ddrc_cg_en               (ddrc_cg_en)
                ,.ih_te_rmw                (ih_te_rmw)
                ,.i_same_addr_rmw          (i_same_addr_rmw [entry_num]) 
                ,.ih_te_hi_pri             (ih_te_hi_pri)
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((entry_num * 2) + 1)' found in module 'te_rd_cam'
//SJ: This coding style is acceptable and there is no plan to change it.
                ,.i_entry_out_pri          (i_entry_pri [(entry_num*2)+1:     // changed 1-bit pri to 2-bits
                                                        (entry_num*2)  ])
//spyglass enable_block SelfDeterminedExpr-ML
                ,.i_entry_out_hpr          (te_entry_hpr [entry_num]) 
                ,.r_ts_act_page            (r_ts_act_page[PAGE_BITS-1:0]) 
                ,.r_ts_bsm_num4pre         (r_ts_bsm_num4pre [BSM_BITS-1:0]) 
                ,.r_ts_bsm_num4any         (r_ts_bsm_num4any [BSM_BITS-1:0]) 
                ,.r_ts_bsm_num4act         (r_ts_bsm_num4act  [BSM_BITS-1:0])           
                ,.r_ts_bsm_num4rdwr        (r_ts_bsm_num4rdwr [BSM_BITS-1:0])           
                ,.r_te_rdwr_autopre        (r_te_rdwr_autopre) 
                ,.r_ts_op_is_precharge     (r_ts_op_is_precharge) 
                ,.r_ts_op_is_activate      (r_ts_op_is_activate) 
                ,.be_te_page_hit           (be_te_page_hit) 
                ,.ih_te_rd_autopre         (ih_te_rd_autopre) 
                ,.ih_te_rd_rankbank_num    ({
                                         ih_te_rd_rank_num, 
                                         ih_te_rd_bg_bank_num}) 
                ,.ih_te_rd_page_num        (ih_te_rd_page_num) 
                ,.ih_te_rd_block_num       (ih_te_rd_block_num) 
                ,.page_hit_limit_reached   (page_hit_limit_reached)
                ,.i_entry_critical_early   (i_entry_critical_early [entry_num])
                ,.page_hit_limit_incoming  (page_hit_limit_incoming)
                ,.i_vlimit_decr            (te_rd_vlimit_decr[entry_num]) 
                ,.vlimit_int               (vlimit_int)
                ,.te_rd_vlimit_reached     (te_rd_vlimit_reached[entry_num])
                ,.load_cam_any             (load_cam)
                ,.ih_te_ie_bt              (ih_te_ie_bt)
                ,.ih_te_ie_wr_type         (ih_te_ie_wr_type)
                ,.ih_te_ie_rd_type         (ih_te_ie_rd_type)
                ,.ih_te_ie_blk_burst_num   (ih_te_ie_blk_burst_num)
                ,.te_pi_ie_bt              (te_pi_ie_bt)
                ,.ie_ecc_uniq_block_num    (ie_ecc_uniq_block_num)
                ,.i_rd_ecc_status          (i_rd_ecc_status)
                ,.te_pi_ie_rd_type         (te_pi_ie_rd_type)
                ,.te_normal_col_win_blk    (te_normal_col_win_blk)
                ,.ih_te_rd_eccap           (ih_te_rd_eccap)
                ,.ih_te_rd_length          (ih_te_rd_length)
                ,.ih_te_critical_dword     (ih_te_critical_dword)
                ,.ih_te_other_fields       (ih_te_rd_other_fields) 
                ,.ts_bsm_num4rdwr          (ts_bsm_num4rdwr [BSM_BITS -1:0]) 
                ,.ts_op_is_rd              (ts_op_is_rd) 
                ,.i_load                   (i_load_en [entry_num]) 
                ,.i_entry_del              (i_del_en [entry_num]) 
                ,.i_entry_out_rankbank     (i_entry[(ENTRY_BITS*entry_num)+ENTRY_RANKBANK_MSB:
                                                   (ENTRY_BITS*entry_num)+ENTRY_RANKBANK_LSB ]) 
                ,.i_entry_out_page         (i_entry[(ENTRY_BITS*entry_num)+ENTRY_ROW_MSB:
                                                   (ENTRY_BITS*entry_num)+ENTRY_ROW_LSB ]) 
                ,.i_entry_out_blk          (i_entry[(ENTRY_BITS*entry_num)+ENTRY_BLK_MSB:
                                                   (ENTRY_BITS*entry_num)+ENTRY_BLK_LSB ]) 
                ,.i_entry_out_rd_length    (i_entry[(ENTRY_BITS*entry_num)+ENTRY_LENGTH_MSB:
                                                   (ENTRY_BITS*entry_num)+ENTRY_LENGTH_LSB ])
                ,.i_entry_out_critical_dword    (i_entry[(ENTRY_BITS*entry_num)+ENTRY_WORD_MSB:
                                                   (ENTRY_BITS*entry_num)+ENTRY_WORD_LSB ])
                ,.i_entry_out_other_fields (i_entry[(ENTRY_BITS*entry_num)+ENTRY_OTHER_MSB:
                                                   (ENTRY_BITS*entry_num)+ENTRY_OTHER_LSB ]) 
                ,.i_entry_out_autopre      (i_entry[(ENTRY_BITS*entry_num)+ENTRY_AUTOPRE_MSB:  
                                                   (ENTRY_BITS*entry_num)+ENTRY_AUTOPRE_LSB])
                ,.i_entry_out_ie_bt            (i_entry[(ENTRY_BITS*entry_num)+ENTRY_IE_BT_LSB+:BT_BITS])
                ,.i_entry_out_ie_rd_type       (i_entry[(ENTRY_BITS*entry_num)+ENTRY_IE_RD_TYPE_LSB+:IE_RD_TYPE_BITS])
                ,.i_entry_out_ie_blk_burst_num (i_entry[(ENTRY_BITS*entry_num)+ENTRY_IE_BURST_NUM_LSB+:IE_BURST_NUM_BITS])
                ,.i_ie_normal_col_win_blk      (i_ie_normal_col_win_blk[entry_num])
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion
                ,.i_ie_blk_addr_collision      (i_ie_blk_addr_collision[entry_num])
//spyglass enable_block W528
                ,.i_entry_out_eccap        (i_entry[(ENTRY_BITS*entry_num)+ENTRY_ECCAP_LSB+:ECCAP_BITS])
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs and in RTL assertion.
                ,.i_same_addr_rd           (i_same_addr_rd [entry_num]) 
//spyglass enable_block W528
                ,.ih_te_rd_latency         (ih_te_rd_latency) 
                ,.i_entry_vpr_timed_out    (i_entry_vpr_timed_out [entry_num]) 
                ,.i_entry_vpr_valid        (te_vpr_valid[entry_num]) 
                ,.i_entry_vpr_valid_d      (te_vpr_valid_d[entry_num]) 
                ,.i_entry_vpr_page_hit     (te_vpr_page_hit[entry_num])
                ,.i_entry_upd_to_vpr_due_ie (upd_to_vpr_due_ie[entry_num])
                ,.i_bank_hit               (i_bank_hit [entry_num]) 
                ,.i_bank_hit_act           (i_bank_hit_act [entry_num]) 
                ,.i_bank_hit_pre           (i_bank_hit_pre [entry_num])
                ,.ts_bsm_num4pre           (ts_bsm_num4pre)
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
`endif
`endif
                ,.i_page_hit               (te_page_hit [entry_num]) 
                ,.i_entry_valid            (te_entry_valid [entry_num]) 
                ,.i_entry_loaded           (te_entry_loaded [entry_num]) 
                ,.page_open_any_op         (pages_open_for_bank[entry_num])   
               );
end
endgenerate


// Generating a single-bit signal indicating if there are any timed-out VPR entries in the CAM
assign any_vpr_timed_out         = |(te_entry_valid & i_entry_vpr_timed_out);
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_gs_any_vpr_timed_out <= 1'b0;
  end
  else begin
    te_gs_any_vpr_timed_out <= any_vpr_timed_out;
  end
end

assign te_gs_any_vpr_timed_out_w = any_vpr_timed_out; 
 wire delayed_autopre_update_fe;
 wire [BSM_BITS-1 :0] delayed_autopre_update_bank;
 wire [BSM_BITS-1:0] ih_te_rd_rank_bg_bank_num;
 assign ih_te_rd_rank_bg_bank_num = {ih_te_rd_rank_num,ih_te_rd_bg_bank_num};
 
// Flopping the activate and precharge inputs from the GS module before using inside the CAM entry
   
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    update_pageclose_autopre <= 1'b0;
    ts_op_is_activate_delay  <= 1'b0;
    
    r_ts_bsm_num4any     <= {BSM_BITS{1'b0}};
    r_ts_bsm_num4act     <= {BSM_BITS{1'b0}};     
    r_ts_bsm_num4rdwr    <= {BSM_BITS{1'b0}};     
    r_ts_bsm_num4pre     <= {BSM_BITS{1'b0}};
    r_ts_act_page        <= {PAGE_BITS{1'b0}};
    r_ts_op_is_precharge <= 1'b0;
    r_ts_op_is_activate  <= 1'b0;
    r_te_rdwr_autopre    <= 1'b0;     
    r_ts_op_is_activate_wr <= 1'b0;
  end
  else begin
    update_pageclose_autopre <= ts_op_is_activate | be_op_is_activate_bypass_int | ts_op_is_rd | ts_op_is_activate_delay | ~delayed_autopre_update_fe | load_cam;
    ts_op_is_activate_delay  <= (ts_op_is_activate | be_op_is_activate_bypass_int) & ts_op_is_rd; // If WR and ACT are issued at the same cycle, delay updating bank of ACT (for LPDDR5)
    r_ts_bsm_num4any         <= ts_op_is_rd                  ? ts_bsm_num4rdwr:
                                ts_op_is_activate            ? ts_bsm_num4act :
                                be_op_is_activate_bypass_int ? ih_te_rd_rank_bg_bank_num :
                                ts_op_is_activate_delay      ? r_ts_bsm_num4act :
                                ~delayed_autopre_update_fe   ? delayed_autopre_update_bank :
                               /*load_cam ?*/                 
             (r_ts_bsm_num4any != ih_te_rd_rank_bg_bank_num) ? ih_te_rd_rank_bg_bank_num : 
                                r_ts_bsm_num4any;
    r_ts_bsm_num4act         <= ts_op_is_activate            ? ts_bsm_num4act :
                                be_op_is_activate_bypass_int ? ih_te_rd_rank_bg_bank_num :
                                r_ts_bsm_num4act;        
    r_ts_bsm_num4rdwr        <= (r_ts_bsm_num4rdwr != ts_bsm_num4rdwr) ? ts_bsm_num4rdwr :
                                r_ts_bsm_num4rdwr; // For both RD and WR (WR for AP)
    r_ts_bsm_num4pre         <= (r_ts_bsm_num4pre != ts_bsm_num4pre) ? ts_bsm_num4pre :
                                r_ts_bsm_num4pre ;
    r_ts_act_page            <= be_op_is_activate_bypass_int ? ih_te_rd_page_num: 
                              (r_ts_act_page != ts_act_page) ? ts_act_page : 
                                r_ts_act_page  ;          
    r_ts_op_is_precharge     <= ts_op_is_precharge;
    r_ts_op_is_activate      <= ts_op_is_activate | be_op_is_activate_bypass_int ;
    r_te_rdwr_autopre        <= te_rdwr_autopre;     
    r_ts_op_is_activate_wr   <= ts_op_is_activate & ( rdwr_pol_sel ? ts_te_sel_act_wr[ts_bsm_num4act] : gs_te_wr_mode) & (~reg_ddrc_dis_opt_ntt_by_act);
    // This signal is used to select bank_hit. So this can be always 0 when the feature is disabled

  end
end
   wire delayed_autopre_update_wr;
   wire delayed_autopre_update_rd;
   wire delayed_autopre_update_ff;
   //A depth of 8 is sufficient to keep delayed_autopre_update_q never full
   localparam DELAYED_AUTOPRE_QD = 8;
   wire [`UMCTL_LOG2(DELAYED_AUTOPRE_QD):0] wcount_unused;   

   wire par_err_unused;
 
   assign delayed_autopre_update_wr = load_cam & (ts_op_is_activate | be_op_is_activate_bypass_int | ts_op_is_rd | ts_op_is_activate_delay | ~delayed_autopre_update_fe);
   assign delayed_autopre_update_rd = ~(ts_op_is_activate | be_op_is_activate_bypass_int | ts_op_is_rd | ts_op_is_activate_delay );

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(1024 * 8)' found in module 'te_rd_cam'
//SJ: This coding style is acceptable and there is no plan to change it - reported for `UMCTL_LOG2.

   // When CAM load occurs simultaniously with updates due to ACT or RDWR the bank is stored in delayed_autopre_update_q to trigger an update later
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
    .d           (ih_te_rd_rank_bg_bank_num),
    .wr          (delayed_autopre_update_wr),
    .rd          (delayed_autopre_update_rd),
    .par_en      (1'b0), // not supported here
    .init_n      (1'b1),
    .wcount      (wcount_unused),               
    .q           (delayed_autopre_update_bank),
    .fe          (delayed_autopre_update_fe),
    //spyglass disable_block W528
    //SMD: A signal or variable is set but never read
    //SJ: Used in RTL assertions
    .ff          (delayed_autopre_update_ff),
    //spyglass enable_block W528
    .par_err     (par_err_unused)
    `ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
    ,.disable_sva_fifo_checker_rd (1'b1) // read data (delayed_autopre_update_bank) is validated by ~delayed_autopre_update_fe in this module
    ,.disable_sva_fifo_checker_wr (1'b1) // assertion disabled due to bug 3892; the FIFO can overflow.
    `endif // SYNTHESIS
    `endif // SNPS_ASSERT_ON
  );
//spyglass enable_block SelfDeterminedExpr-ML

// note: following codes are commented out for bug 7584   
// wire autopre_for_pageclose_int =  r_pageclose_autopre[ts_bsm_num4rdwr]; 

// Auto-pre only if dh_te_pageclose_timer==0 and dh_te_pageclose and nor the read part of an RMW
// assign autopre_for_pageclose = (dh_te_pageclose_timer==8'h00 && dh_te_pageclose) ? autopre_for_pageclose_int : 1'b0;

// Auto-pre to PI is an OR of the auto-pre from the CAM and the page close autopre
// assign te_pi_rd_autopre      = te_pi_rd_autopre_int | autopre_for_pageclose;
// ts_rdwr_cmd_autopre[0] Force AP=1 
// ts_rdwr_cmd_autopre[1] Force AP=0 (for Inline ECC, RE_B or read part of RMW)         
// assign te_pi_rd_autopre      = ts_rdwr_cmd_autopre[0] | (autopre_for_pageclose `ifdef MEMC_USE_RMW_OR_MEMC_INLINE_ECC & (~ts_rdwr_cmd_autopre[1]) `endif );
// `ifdef DDRCTL_DDR_OR_MEMC_LPDDR4
assign te_os_rd_pageclose_autopre = (dh_te_pageclose_timer==8'h00 && dh_te_pageclose) ? r_pageclose_autopre : {NUM_TOTAL_BSMS{1'b0}};
// `endif


// The following is a non functional change to approximate timing the anticipated autopre enhancement 
/*always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    te_pi_rd_autopre <= 1'b0;
  else
    te_pi_rd_autopre <= autopre_for_pageclose;
*/
// set status fields according to the CAM and transaction
// +-----------+----------------------------------------+-----------------------------+
// | incoming  |            rd CAM                      |        wr CAM               |
// +-----------+----------------------------------------+-----------------------------+
// |    rd     | rd flush if collide with RMW           |       wr flush              |
// |    wr     | rd flush                               | wr combine (return pointer) |
// +-----------+----------------------------------------+-----------------------------+
//
// need to flush when a read of a rmw collides with a read
// because the write of this rmw will not generate a collision
//


wire i_collision_due_rd;
wire i_collision_due_wr;

assign i_collision_due_rd = ((| i_same_addr_rmw [RD_CAM_ENTRIES -1:0]) & i_rd_command);

assign i_collision_due_wr = (| i_same_addr_rd [RD_CAM_ENTRIES -1:0]) & (i_wr_command & (~te_yy_wr_combine));

assign te_rd_flush_due_rd = i_collision_due_rd;
assign te_rd_flush_due_wr = i_collision_due_wr;

assign te_rd_flush = (i_collision_due_rd | i_collision_due_wr)
                     & (|i_same_addr_rd_filtered) 
                     // If only RE_BR is colliding due to normal collisioin within block RMW
                     // there is one cycle gap between them.
                     // Note: DUAL HIF is not supported with MEMC_INLINE_ECC 
;

assign te_rd_flush_enable = te_rd_flush;

// continue to flush until the collided entry is serviced
always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin 
      r_flush <= 1'b0; 
   end        
   else if(ddrc_cg_en) begin 
      r_flush <= te_rd_flush_enable; 
   end // else
end // always

assign te_rd_flush_started = r_flush;



// the number of pulses indicates the number of collisions in each case
assign ddrc_co_perf_war_hazard = te_rd_flush_enable & (~r_flush);


  reg [RD_CAM_ENTRIES-1:0] te_rd_vlimit_reached_d;
  always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
       te_rd_vlimit_reached_d <= {RD_CAM_ENTRIES{1'b0}};
    end
    else if(ddrc_cg_en) begin
       te_rd_vlimit_reached_d <= te_rd_vlimit_reached[RD_CAM_ENTRIES-1:0];
    end
  end

  // Flop is in top module 
  assign ddrc_co_perf_vlimit_reached_rd = |(te_rd_vlimit_reached & (~te_rd_vlimit_reached_d)); // Edge detection;



// saving the collided entry number
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn)
    te_rd_col_entry [RD_CAM_ADDR_BITS -1:0] <= {RD_CAM_ADDR_BITS{1'b0}};
  else if(ddrc_cg_en)
  begin
    if (te_rd_flush_enable)
      te_rd_col_entry [RD_CAM_ADDR_BITS -1:0] <= i_col_entry;
  end


// Priority assignment to the output ports
// 2-bit priority coming from the CAM is converted to 1-bit when giving to the RD Replace engine
// 2-bit priroity encoding: 00 - LPR, 01 - VPR, 10 - HPR, 11 - Unused
// bit[1] of the priority signal from CAM is connected to the priroity bit going to RD Replace engine
// That means, LPR and VPR are mapped as te_entry_pri = 1'b0 and HPR and Unused are mapped as te_entry_pri = 1'b1
// When there are expired VPR commands, they pass through their own selection n/w. No priroity bit is needed in the rd_replce engine
// In the NTT, the VPR commands are set to HPR priroity

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((count * 2) + 1)' found in module 'te_rd_cam'
//SJ: This coding style is acceptable and there is no plan to change it.

always @(i_entry_pri)
begin: BLK_D
integer                     count;                     // for loop dummy variable
   for (count=0; count<RD_CAM_ENTRIES; count=count+1)
    te_entry_pri [count] = i_entry_pri [count*2+1]; // assigning bit[1] of i_entry_pri to bit[0] to te_entry_pri
end
//spyglass enable_block SelfDeterminedExpr-ML

// Start search at ih_te_rd_entry_num and work upwards.  This will give the oldest matching CAM entry

// To achieve this, easiest to
// - create a bus {i_same_addr_rd, i_same_addr_rd}
// - shift i_same_addr_rd right by ih_te_rd_entry_num
// - perform search
// - add ih_te_rd_entry_num to answer

// In case of Inline ECC, some entry with same_addr_rd=1 might be not valid at that time, so filtered by valid in order to select valid colliding entry.
assign i_same_addr_rd_filtered = i_same_addr_rd & te_entry_valid;


  // Colliding entry search just select one of the colliding entry
  // As all colliding entries are page-hit on the same bank, execution order is not so important
  wire [RD_CAM_ENTRIES-1:0]   i_same_addr_final;
  wire                        selected_vld_unused;
  wire                        tag_selected_unused;

  assign i_same_addr_final = 
                                                i_same_addr_rd_filtered;
localparam RD_CAM_ENTRIES_EXTEND = (RD_CAM_ENTRIES >128) ? 256: ((RD_CAM_ENTRIES>64) ? 128 : RD_CAM_ENTRIES);

  select_net_lite
   #(
    .TAG_BITS           (1'b0),
    .NUM_INPUTS         (RD_CAM_ENTRIES_EXTEND)
  ) select_net_col_entry_rd (
    .clk                (co_te_clk),
    .resetb             (core_ddrc_rstn),
    .tags               ({RD_CAM_ENTRIES_EXTEND{1'b0}}),
    .vlds               ({{RD_CAM_ENTRIES_EXTEND - RD_CAM_ENTRIES{1'b0}},i_same_addr_final [RD_CAM_ENTRIES -1:0]}),
    .wall_next          ({RD_CAM_ADDR_BITS{1'b0}}),
    .selected_vld       (selected_vld_unused),
    .tag_selected       (tag_selected_unused), // unused
    .selected           (i_col_entry)
);

//----------------------------
// page hit limiter logic
//----------------------------

// Decode register
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    page_hit_limit_int <= 5'b0_0000;
  end
  else begin
    case (reg_ddrc_page_hit_limit_rd)
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
      else if (ts_op_is_rd & (ts_bsm_num4rdwr == bsm_idx) & (page_hit_limit_cnt[bsm_idx] != 5'b0_0000)) begin
          page_hit_limit_cnt[bsm_idx] <=  page_hit_limit_cnt[bsm_idx] - 5'b0_0001;
      end
    end

    // generating event of page hit limit reached
    if (ts_op_is_rd & page_hit_limit_cnt[ts_bsm_num4rdwr] == 5'b0_0001) begin
      page_hit_limit_reached <= 1'b1;
    end
    else begin
      page_hit_limit_reached <= 1'b0;
    end

    // generating i_entry_critical_per_bsm
    for (bsm_idx=0;bsm_idx<NUM_TOTAL_BSMS;bsm_idx=bsm_idx+1) begin
      i_entry_critical_per_bsm_early [bsm_idx] <= i_entry_critical_per_bsm_early_next[bsm_idx];
      i_entry_critical_per_bsm       [bsm_idx] <= (((r_ts_bsm_num4rdwr == bsm_idx) & r_te_rdwr_autopre) | (r_ts_bsm_num4pre==bsm_idx & r_ts_op_is_precharge) 
 
 )? 1'b0 : 
                                                                      (i_entry_critical_per_bsm_early [bsm_idx] & ts_op_is_rd & (ts_bsm_num4rdwr == bsm_idx))? 1'b1 : 
                                                                                                                                                               i_entry_critical_per_bsm [bsm_idx];
    end
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
        u_te_entry_crit
        (
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

assign page_hit_limit_incoming = i_entry_critical_per_bsm_early_next[ih_te_rd_rank_bg_bank_num];

// Output assignment
assign te_entry_critical_per_bsm = i_entry_critical_per_bsm;
assign te_entry_critical_early   = i_entry_critical_early;

// Visible window limiter
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    vlimit_int <= 9'b0_0000_0000;
  end
  else begin
    case (reg_ddrc_visible_window_limit_rd)
         3'd1 : vlimit_int <= 9'd31; 
         3'd2 : vlimit_int <= 9'd63;
         3'd3 : vlimit_int <= 9'd127;
         3'd4 : vlimit_int <= 9'd255;
      default : vlimit_int <= 9'd0;
    endcase
  end
end

//----------------------------
// Max rank wr/rd logic
//----------------------------

//  Priority encoder

wire   sel_rd_pri_prefer;
assign sel_rd_pri_prefer = (ih_gs_rdhigh_empty | ~(gs_te_pri_level | ih_gs_rdlow_empty))
                              & ~te_gs_any_vpr_timed_out
                           ;

wire   [RD_CAM_ADDR_BITS-1:0] te_rd_prefer;
assign te_rd_prefer = (sel_rd_pri_prefer) ? te_lo_rd_prefer : te_hi_rd_prefer;

wire [RANKBANK_BITS-1:0]                         te_rd_rankbank_prefer_w;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(bit_loc + 1)' found in module 'te_wr_cam'
//SJ: This coding style is acceptable and there is no plan to change it. - refers to `UMCTL_LOG2
generate
for (bit_loc=ENTRY_RANKBANK_LSB; bit_loc<=ENTRY_RANKBANK_MSB; bit_loc=bit_loc+1)
begin : mux_rankbank_prefer
  te_rd_mux
   rd_rankbank_prefer (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel       (te_rd_prefer [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (te_rd_rankbank_prefer_w [bit_loc - ENTRY_RANKBANK_LSB])
                      );
end
endgenerate

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    te_rd_rankbank_prefer <= {RANKBANK_BITS{1'b0}};
  end
  else begin
     if (|(te_rd_rankbank_prefer ^ te_rd_rankbank_prefer_w)) begin
        te_rd_rankbank_prefer <= te_rd_rankbank_prefer_w;
     end
  end
end

//spyglass enable_block SelfDeterminedExpr-ML

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Unsynthesized signals to debug with waveform viewer
//------------------------------------------------------------------------------
wire                                        rcam_valid [RD_CAM_ENTRIES];
wire                                        rcam_entry_valid[RD_CAM_ENTRIES];
wire    [ENTRY_AUTOPRE_BITS-1:0]            rcam_autopre [RD_CAM_ENTRIES];
wire    [1:0]                               rcam_pri [RD_CAM_ENTRIES];
wire                                        rcam_rmw [RD_CAM_ENTRIES];
wire    [RD_LATENCY_BITS-1:0]               rcam_latency[RD_CAM_ENTRIES];
wire    [BT_BITS-1:0]                       rcam_ie_bt[RD_CAM_ENTRIES];
wire    [IE_RD_TYPE_BITS-1:0]               rcam_ie_rd_type[RD_CAM_ENTRIES];
wire    [BLK_BITS-1:0]                      rcam_blk [RD_CAM_ENTRIES];
wire    [PAGE_BITS-1:0]                     rcam_row [RD_CAM_ENTRIES];
wire    [BG_BANK_BITS-1:0]                  rcam_bank [RD_CAM_ENTRIES];
wire    [RANK_BITS-1:0]                     rcam_rank [RD_CAM_ENTRIES];
wire    [CMD_LEN_BITS-1:0]                  rcam_length[RD_CAM_ENTRIES];
wire    [WORD_BITS-1:0]                     rcam_word[RD_CAM_ENTRIES];
wire    [OTHER_RD_ENTRY_BITS-1:0]           rcam_other [RD_CAM_ENTRIES];

genvar entry_idx;
generate
    for (entry_idx=0; entry_idx<RD_CAM_ENTRIES; entry_idx++) begin
        assign rcam_valid[entry_idx]            = u0[entry_idx].entry.r_entry[0];
        assign rcam_entry_valid[entry_idx]      = u0[entry_idx].entry.i_entry_valid;
        assign rcam_autopre[entry_idx]          = i_entry[entry_idx*ENTRY_BITS+ENTRY_AUTOPRE_LSB +: ENTRY_AUTOPRE_BITS];
        assign rcam_pri[entry_idx]              = i_entry_pri[entry_idx*2 +: 2];
        assign rcam_rmw[entry_idx]              = u0[entry_idx].entry.r_entry[2];
        assign rcam_ie_bt[entry_idx]            = i_entry[(entry_idx*ENTRY_BITS)+ENTRY_IE_BT_LSB+:BT_BITS];
        assign rcam_ie_rd_type[entry_idx]       = i_entry[(entry_idx*ENTRY_BITS)+ENTRY_IE_RD_TYPE_LSB+:IE_RD_TYPE_BITS];
        assign rcam_latency[entry_idx]          = u0[entry_idx].entry.r_entry_rd_latency;
        assign rcam_blk[entry_idx]              = i_entry[entry_idx*ENTRY_BITS+ENTRY_BLK_LSB +: BLK_BITS];
        assign rcam_row[entry_idx]              = i_entry[entry_idx*ENTRY_BITS+ENTRY_ROW_LSB +: PAGE_BITS];
        assign rcam_bank[entry_idx]             = i_entry[entry_idx*ENTRY_BITS+ENTRY_RANKBANK_LSB +: BG_BANK_BITS];
        assign rcam_rank[entry_idx]             = i_entry[entry_idx*ENTRY_BITS+ENTRY_RANKBANK_LSB+BG_BANK_BITS +: RANK_BITS];
        assign rcam_length[entry_idx]           = i_entry[entry_idx*ENTRY_BITS+ENTRY_LENGTH_LSB +: CMD_LEN_BITS];
        assign rcam_word[entry_idx]             = i_entry[entry_idx*ENTRY_BITS+ENTRY_WORD_LSB +: WORD_BITS];
        assign rcam_other[entry_idx]            = i_entry[entry_idx*ENTRY_BITS+ENTRY_OTHER_LSB +: OTHER_RD_ENTRY_BITS];
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

// selecting the priority bits from the entry of the read commands that is scheduled
reg [NUM_TOTAL_BANKS-1:0] expired_vpr_per_bank ;
reg [NUM_TOTAL_BANKS-1:0] xvpr_serviced_per_bank ;
reg [15:0] num_of_non_vpr_serviced_per_bank[NUM_TOTAL_BANKS-1:0];

wire [1:0] pri_of_rd_op_cmd = {i_entry_pri[te_rd_entry*2+1],
                               i_entry_pri[te_rd_entry*2]  };

integer rd_entry;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    expired_vpr_per_bank <= {NUM_TOTAL_BANKS{1'b0}}; 
  end else begin
    for(rd_entry=0; rd_entry<RD_CAM_ENTRIES; rd_entry=rd_entry+1) begin : rd_entry_gen
      if(i_del_en[rd_entry] & i_entry_vpr_timed_out[rd_entry]) begin
          expired_vpr_per_bank[i_entry[rd_entry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]] <= 1'b0;
      end else if(te_vpr_valid[rd_entry] & (~i_del_en[rd_entry]) & i_entry_vpr_timed_out[rd_entry]) begin
          expired_vpr_per_bank[i_entry[rd_entry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]] <= 1'b1;
      end
    end
  end
end

wire[RD_LATENCY_BITS-1:0]  rd_ecc_actual_latency[NO_OF_BT-1:0];

reg [NUM_TOTAL_BANKS-1:0]  expired_vpr_ecc_cmd_per_bank ;
reg [NUM_TOTAL_BANKS-1:0]  xvpr_ecc_cmd_serviced_per_bank ;
reg [RD_CAM_ENTRIES-1:0]   rd_data_cmd_expired;
reg [RD_CAM_ENTRIES-1:0]   rd_ecc_cmd_expired;

reg [1:0]                  r_rd_ecc_highest_pri[NO_OF_BT-1:0];
reg [RD_CAM_ADDR_BITS-1:0] r_rd_ecc_entry[NO_OF_BT-1:0];
reg                        r_rd_ecc_rmw[NO_OF_BT-1:0];
reg                        r_wr_ecc_cmd_pending[NO_OF_BT-1:0];
reg [1:0]                  r_rd_ecc_pri[NO_OF_BT-1:0];

genvar rbt_num;
generate
  for (rbt_num=0;rbt_num<NO_OF_BT;rbt_num=rbt_num+1) begin : rd_ecc_cmd_GEN
   always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
     if (~core_ddrc_rstn) begin
       r_rd_ecc_entry[rbt_num]       <= {RD_CAM_ADDR_BITS{1'b0}};
       r_rd_ecc_rmw[rbt_num]         <= 1'b0;
       r_rd_ecc_pri[rbt_num]         <= 2'b00;
       r_rd_ecc_highest_pri[rbt_num] <= 2'b00;
       r_wr_ecc_cmd_pending[rbt_num] <= 1'b0;
     end else begin

       // Generate Read ECC command's pri, entry number and RMW status
       if(load_cam & (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B) & (rbt_num == ih_te_ie_bt) ) begin
         r_rd_ecc_entry[rbt_num] <= ih_te_rd_entry_num;
         r_rd_ecc_rmw[rbt_num]   <= ih_te_rmw;
         // HPR block is not terminated if WR pending for that block, so HPR pri is not changed to other pri 
         r_rd_ecc_pri[rbt_num]   <= (ih_te_hi_pri==`MEMC_CMD_PRI_HPR & r_wr_ecc_cmd_pending[rbt_num]) 
                                    ? `MEMC_CMD_PRI_HPR 
                                    : ( ih_te_hi_pri==`MEMC_CMD_PRI_VPR ? `MEMC_CMD_PRI_VPR : `MEMC_CMD_PRI_LPR ) ;
       end

       // Generate highest expected priority of Read ECC command 
       // Do not update highest pri if commmand is RMW(incase of RMW, block is not terminated and also priority not changed) 
       if( load_cam & ((ih_te_ie_rd_type == `IE_RD_TYPE_RE_B)|(ih_te_ie_rd_type == `IE_RD_TYPE_RD_E)) & (rbt_num == ih_te_ie_bt) 
            & (r_rd_ecc_highest_pri[rbt_num]<=ih_te_hi_pri)
            & ( (!(ih_te_rmw && ih_te_hi_pri==`MEMC_CMD_PRI_HPR)) 
              | (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B) )
          ) begin
         r_rd_ecc_highest_pri[rbt_num] <= ih_te_hi_pri;
       end else if (ts_op_is_rd & ((te_pi_ie_rd_type == `IE_RD_TYPE_RE_B) | (te_pi_ie_rd_type == `IE_RD_TYPE_RD_E)) & (rbt_num == te_pi_ie_bt)) begin
         r_rd_ecc_highest_pri[rbt_num] <= 2'b00;
       end


       // Generate Write BT status, this is used to identify block gets terminated or not
       if(ih_te_wr_valid & (ih_te_ie_wr_type !=`IE_WR_TYPE_WD_N) & (~te_ih_retry) & (rbt_num == ih_te_ie_bt) ) begin
         r_wr_ecc_cmd_pending[rbt_num] <= 1'b1;
       end else if(gs_te_op_is_wr & (te_mr_ie_wr_type==`IE_WR_TYPE_WE_BW) & (rbt_num == te_mr_ie_bt) ) begin
         r_wr_ecc_cmd_pending[rbt_num] <= 1'b0;
       end

     end
   end
   // Read ECC command's actual VPR latency from CAM
   assign rd_ecc_actual_latency[rbt_num] = (r_rd_ecc_status_bit[rbt_num]) ? rcam_latency[r_rd_ecc_entry[rbt_num]] : {RD_LATENCY_BITS{1'b1}};
 end
endgenerate

integer rdentry;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    expired_vpr_ecc_cmd_per_bank <= {NUM_TOTAL_BANKS{1'b0}};
    rd_data_cmd_expired          <= {RD_CAM_ENTRIES{1'b0}};
    rd_ecc_cmd_expired           <= {RD_CAM_ENTRIES{1'b0}};
  end else begin
    for(rdentry=0; rdentry<RD_CAM_ENTRIES; rdentry=rdentry+1) begin : rdentry_gen
      if(i_del_en[rdentry] & i_entry_vpr_timed_out[rdentry]) begin
          if(i_entry[(ENTRY_BITS*rdentry)+ENTRY_IE_RD_TYPE_LSB+:IE_RD_TYPE_BITS]==`IE_RD_TYPE_RE_B) begin
            expired_vpr_ecc_cmd_per_bank[i_entry[rdentry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]] <= 1'b0;
          end
      end else if(te_vpr_valid[rdentry] & (~i_del_en[rdentry]) & i_entry_vpr_timed_out[rdentry]) begin
          if(i_entry[(ENTRY_BITS*rdentry)+ENTRY_IE_RD_TYPE_LSB+:IE_RD_TYPE_BITS]==`IE_RD_TYPE_RE_B) begin
            expired_vpr_ecc_cmd_per_bank[i_entry[rdentry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]] <= 1'b1;
          end
      end
      if(i_del_en[rdentry]) begin
          if(rd_data_cmd_expired[rdentry]) rd_data_cmd_expired[rdentry] <= 1'b0;
          if(i_entry[(ENTRY_BITS*rdentry)+ENTRY_IE_RD_TYPE_LSB+:IE_RD_TYPE_BITS]==`IE_RD_TYPE_RE_B) begin
            if(rd_ecc_cmd_expired[rdentry]) rd_ecc_cmd_expired[rdentry] <= 1'b0;
          end
      end else if(te_entry_loaded[rdentry] & ((i_entry_pri[rdentry*2 +: 2]==CMD_PRI_VPR)||(i_entry_pri[rdentry*2 +: 2]==CMD_PRI_XVPR)) & (~i_del_en[rdentry]) & (~(|rcam_latency[rdentry]))) begin
          rd_data_cmd_expired[rdentry] <= 1'b1;
          if(i_entry[(ENTRY_BITS*rdentry)+ENTRY_IE_RD_TYPE_LSB+:IE_RD_TYPE_BITS]==`IE_RD_TYPE_RE_B) begin
            rd_ecc_cmd_expired[rdentry] <= 1'b1;
          end
      end
    end
  end
end


// Set flag when expired-vpr serviced for a given bank and there are still expired-vpr present in the CAM for same bank
// Calculate number of non-xvpr serviced for a given bank when expired-vpr present for that bank
integer rbank;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    for(rbank=0; rbank<NUM_TOTAL_BANKS; rbank=rbank+1) begin
      xvpr_serviced_per_bank[rbank]           <= 1'b0; 
      num_of_non_vpr_serviced_per_bank[rbank] <= {16{1'b0}};
      xvpr_ecc_cmd_serviced_per_bank[rbank]   <= 1'b0; 
    end
  end else begin
    for(rbank=0; rbank<NUM_TOTAL_BANKS; rbank=rbank+1) begin
      if(expired_vpr_per_bank[rbank] && ts_op_is_rd && pri_of_rd_op_cmd == CMD_PRI_XVPR && ts_bank_num4rdwr==rbank) begin 
         xvpr_serviced_per_bank[rbank]           <= 1'b1;
         num_of_non_vpr_serviced_per_bank[rbank] <= 16'h0;
      end else if (expired_vpr_per_bank[rbank] && ts_op_is_rd && pri_of_rd_op_cmd != CMD_PRI_XVPR && ts_bank_num4rdwr==rbank) begin
         num_of_non_vpr_serviced_per_bank[rbank] <= num_of_non_vpr_serviced_per_bank[rbank] + 1'b1;
      end else if (~expired_vpr_per_bank[rbank]) begin
         xvpr_serviced_per_bank[rbank]           <= 1'b0;
         num_of_non_vpr_serviced_per_bank[rbank] <= 16'h0;
      end
      
      if(expired_vpr_ecc_cmd_per_bank[rbank] && (te_pi_ie_rd_type == `IE_RD_TYPE_RE_B) && ts_op_is_rd && pri_of_rd_op_cmd == CMD_PRI_XVPR && ts_bank_num4rdwr==rbank) begin 
         xvpr_ecc_cmd_serviced_per_bank[rbank]   <= 1'b1;
      end else if (~expired_vpr_ecc_cmd_per_bank[rbank])
         xvpr_ecc_cmd_serviced_per_bank[rbank]   <= 1'b0;
    end
  end
end

property p_non_expired_vpr_scheduled_for_expired_vpr_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( ts_op_is_rd && (ts_bank_num4rdwr==bank_num) 
        && expired_vpr_per_bank[bank_num] 
        && (xvpr_serviced_per_bank[bank_num] || (~xvpr_serviced_per_bank[bank_num] && num_of_non_vpr_serviced_per_bank[bank_num]>0))
      ) |-> (pri_of_rd_op_cmd == CMD_PRI_XVPR) ;
endproperty

property p_ie_non_expired_vpr_scheduled_for_expired_vpr_ecc_cmd_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( ts_op_is_rd && (ts_bank_num4rdwr==bank_num) 
        && expired_vpr_ecc_cmd_per_bank[bank_num] 
        && (xvpr_ecc_cmd_serviced_per_bank[bank_num] || (~xvpr_ecc_cmd_serviced_per_bank[bank_num] && num_of_non_vpr_serviced_per_bank[bank_num]>0))
      ) |-> (pri_of_rd_op_cmd == CMD_PRI_XVPR) ;
endproperty

genvar rd_bank;
generate 
for(rd_bank=0; rd_bank<NUM_TOTAL_BANKS; rd_bank=rd_bank+1) begin : a_non_xvpr_sch_rd_bank_gen
  a_non_expired_vpr_scheduled_for_expired_vpr_bank : assert property (p_non_expired_vpr_scheduled_for_expired_vpr_bank(rd_bank))
  else $display("[%t][%m] ERROR: Non-expired VPR command is scheduled when there are expired-VPR for bank = %0d ", $time,rd_bank);

  a_ie_non_expired_vpr_scheduled_for_expired_vpr_ecc_cmd_bank : assert property (p_ie_non_expired_vpr_scheduled_for_expired_vpr_ecc_cmd_bank(rd_bank))
  else $display("[%t][%m] ERROR:[Inline ECC] Non-expired VPR command is scheduled when there are expired-VPR ECC commands for bank = %0d ", $time,rd_bank);
end
endgenerate


// 
property p_ie_rd_ecc_cmd_pri_not_highest_as_data_cmd(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( (r_rd_ecc_status_bit[rcam_ie_bt[entry_num]] && (!r_rd_ecc_rmw[rcam_ie_bt[entry_num]]) && (!r_wr_ecc_cmd_pending[rcam_ie_bt[entry_num]]) && rcam_valid[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RE_B) && (rcam_pri[entry_num]!=CMD_PRI_XVPR))
      ) |-> (rcam_pri[entry_num]==r_rd_ecc_highest_pri[rcam_ie_bt[entry_num]]) ;
endproperty

property p_ie_rd_ecc_cmd_pri_change_from_hpr_is_not_expected(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( (r_rd_ecc_status_bit[rcam_ie_bt[entry_num]] && (r_rd_ecc_pri[rcam_ie_bt[entry_num]]==CMD_PRI_HPR)
         && rcam_valid[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RE_B) )
      ) |-> (rcam_pri[entry_num]==CMD_PRI_HPR) ;
endproperty

property p_ie_rd_ecc_cmd_pri_change_from_vpr_is_not_expected(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( ( r_rd_ecc_status_bit[rcam_ie_bt[entry_num]] && (r_rd_ecc_pri[rcam_ie_bt[entry_num]]==CMD_PRI_VPR)
         && rcam_valid[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RE_B) && (rcam_pri[entry_num]!=CMD_PRI_XVPR) )
      ) |-> (rcam_pri[entry_num]==CMD_PRI_VPR) ;
endproperty


property p_ie_rd_ecc_cmd_latency_not_same_as_data_cmd(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( (r_rd_ecc_status_bit[rcam_ie_bt[entry_num]] && rcam_valid[entry_num] && (rcam_pri[entry_num]==CMD_PRI_VPR || rcam_pri[entry_num]==CMD_PRI_XVPR) && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RD_E))
      ) |-> (rd_ecc_actual_latency[rcam_ie_bt[entry_num]] <= rcam_latency[entry_num]) ;
     // Compare entry_num's latency against corresponding RD ECC's latency if it's still there 
endproperty

property p_ie_rd_ecc_cmd_is_not_expired_when_data_cmd_expired(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( (rcam_valid[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RD_E) && (r_rd_ecc_pri[rcam_ie_bt[entry_num]]!=CMD_PRI_HPR) && r_rd_ecc_status_bit[rcam_ie_bt[entry_num]] && (~(|rcam_latency[entry_num])) )
      ) |-> (rd_ecc_actual_latency[rcam_ie_bt[entry_num]]=={RD_LATENCY_BITS{1'b0}}) ;
endproperty


property p_ie_rd_non_protected_cmd_is_not_valid_immediately_after_load(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( (rcam_valid[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RD_N))
      ) |-> (rcam_entry_valid[entry_num]==1'b1) ;
endproperty


property p_ie_rd_data_cmd_is_not_valid_immediately_after_rd_ecc_serviced(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( (rcam_valid[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RD_E) && (~r_rd_ecc_status_bit[rcam_ie_bt[entry_num]]))
      ) |-> (rcam_entry_valid[entry_num]==1'b1) ;
endproperty

property p_ie_rd_ecc_cmd_changed_from_expired_to_non_expired(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( rd_ecc_cmd_expired[entry_num] && (rcam_ie_rd_type[entry_num]==`IE_RD_TYPE_RE_B) 
      ) |-> (i_entry_vpr_timed_out[entry_num]==1'b1) ;
endproperty

property p_ie_rd_data_cmd_changed_from_expired_to_non_expired(entry_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) 
      ( rd_data_cmd_expired[entry_num] && (rcam_ie_rd_type[entry_num]!=`IE_RD_TYPE_RE_B) 
      ) |-> (rcam_latency[entry_num]=={RD_LATENCY_BITS{1'b0}}) ;
endproperty


genvar rd_entry_num;
generate 
for(rd_entry_num=0; rd_entry_num<RD_CAM_ENTRIES; rd_entry_num=rd_entry_num+1) begin : a_ie_rd_ecc_cmd
  // JIRA___ID: fix this assertion to adapt V3 architecture.
  // a_ie_rd_ecc_cmd_pri_not_highest_as_data_cmd : assert property (p_ie_rd_ecc_cmd_pri_not_highest_as_data_cmd(rd_entry_num))
  // else $display("[%t][%m] ERROR:[Inline ECC] Priority of RD ECC cmd is not the highest priority as of RD DATA cmd for entry %0d ", $time,rd_entry_num);

  // JIRA___ID: Comment out this assertion until RTL is fixed for issue in Bug 4919 Comment #24.
  //a_ie_rd_ecc_cmd_pri_change_from_hpr_is_not_expected : assert property (p_ie_rd_ecc_cmd_pri_change_from_hpr_is_not_expected(rd_entry_num))
  //else $display("[%t][%m] ERROR:[Inline ECC] Priority of RD ECC cmd is changed from HPR to other priority for entry %0d - this is not expected.", $time,rd_entry_num);

  a_ie_rd_ecc_cmd_pri_change_from_vpr_is_not_expected : assert property (p_ie_rd_ecc_cmd_pri_change_from_vpr_is_not_expected(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] Priority of RD ECC cmd is changed from VPR to other priority for entry %0d - this is not expected.", $time,rd_entry_num);

  a_ie_rd_ecc_cmd_latency_not_same_as_data_cmd: assert property (p_ie_rd_ecc_cmd_latency_not_same_as_data_cmd(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] Latency of RD ECC cmd is not less than or equal to RD DATA cmd for entry %0d ", $time,rd_entry_num);

  a_ie_rd_ecc_cmd_is_not_expired_when_data_cmd_expired: assert property (p_ie_rd_ecc_cmd_is_not_expired_when_data_cmd_expired(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] RD ECC cmd is not expired when RD DATA cmd of that block is expired for RD DATA cmd entry %0d ", $time,rd_entry_num);

  a_ie_rd_non_protected_cmd_is_not_valid_immediately_after_load: assert property (p_ie_rd_non_protected_cmd_is_not_valid_immediately_after_load(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] RD cmd to non-protected region is not become valid immediately after loading for entry %0d ", $time,rd_entry_num);

  a_ie_rd_data_cmd_is_not_valid_immediately_after_rd_ecc_serviced: assert property (p_ie_rd_data_cmd_is_not_valid_immediately_after_rd_ecc_serviced(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] RD DATA cmd is not become valid immediately after RD ECC cmd serviced for entry %0d ", $time,rd_entry_num);

  a_ie_rd_ecc_cmd_changed_from_expired_to_non_expired: assert property (p_ie_rd_ecc_cmd_changed_from_expired_to_non_expired(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] RD DATA cmd is changed from expired to non-expired VPR for entry %0d ", $time,rd_entry_num);

  a_ie_rd_data_cmd_changed_from_expired_to_non_expired: assert property (p_ie_rd_data_cmd_changed_from_expired_to_non_expired(rd_entry_num))
  else $display("[%t][%m] ERROR:[Inline ECC] RD DATA cmd is changed from expired to non-expired VPR for entry %0d ", $time,rd_entry_num);
end
endgenerate


  
// Calculation for non-expired VPR scheduled when expired-VPR present inside CAM
reg [15:0] num_of_non_vpr_cmds_sched_w_exp_vpr_on; // max num of banks in a system is in ddr4 case
reg [15:0] total_num_of_non_xvpr_sched_w_exp_vpr_on; // total num of non-ex-vpr cmds executed when ex-vpr present in CAM
reg [15:0] max_num_of_non_xvpr_sched_w_exp_vpr_on;   // max value of num of non-ex-vpr cmds executed when ex-vpr present in CAM

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    num_of_non_vpr_cmds_sched_w_exp_vpr_on   <= 16'h0;
    max_num_of_non_xvpr_sched_w_exp_vpr_on   <= 16'h0;
    total_num_of_non_xvpr_sched_w_exp_vpr_on <= 16'h0;
  end else begin
    if(any_vpr_timed_out & ts_op_is_rd & |te_vpr_valid) begin
      if(pri_of_rd_op_cmd == CMD_PRI_XVPR) begin // if expired-VPR command executed with any_vpr_timed_out high, then reset the counter
        // Check max value of non_xvpr with current value of non_xvpr
        if(max_num_of_non_xvpr_sched_w_exp_vpr_on<num_of_non_vpr_cmds_sched_w_exp_vpr_on) begin
          max_num_of_non_xvpr_sched_w_exp_vpr_on <= num_of_non_vpr_cmds_sched_w_exp_vpr_on;
        end
        num_of_non_vpr_cmds_sched_w_exp_vpr_on <= 16'h0;
      end else begin // if non-VPR commands executed with any_vpr_timed_out high, then increment the counter
        num_of_non_vpr_cmds_sched_w_exp_vpr_on   <= num_of_non_vpr_cmds_sched_w_exp_vpr_on + 1'b1;
        total_num_of_non_xvpr_sched_w_exp_vpr_on <= total_num_of_non_xvpr_sched_w_exp_vpr_on + 1'b1;
      end
    end else if(ts_op_is_rd) begin
      num_of_non_vpr_cmds_sched_w_exp_vpr_on <= 16'h0;
    end
  end
end


// Assertion to check - Collided read command to given bank get serviced ahead of other
// commands to that bank

reg [NUM_TOTAL_BANKS-1:0] rd_entry_collided_per_bank ;
reg te_rd_flush_r, i_collision_due_wr_r;
integer r_entry;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    rd_entry_collided_per_bank <= {NUM_TOTAL_BANKS{1'b0}}; 
    te_rd_flush_r              <= 1'b0;
    i_collision_due_wr_r       <= 1'b0;
  end else begin
    te_rd_flush_r              <= te_rd_flush;
    i_collision_due_wr_r       <= i_collision_due_wr;
    for(r_entry=0; r_entry<RD_CAM_ENTRIES; r_entry=r_entry+1) begin : rd_collided_entry_gen
      if((((i_del_en[r_entry]|| (i_collision_due_wr_r&&te_yy_wr_combine)) 
           && ((te_rd_col_entry==r_entry))
          )


         )
         && rd_entry_collided_per_bank[i_entry[r_entry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]]) begin
        rd_entry_collided_per_bank[i_entry[r_entry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]] <= 1'b0;
      end else if(te_entry_valid[r_entry] && (~i_del_en[r_entry]) && (te_rd_flush_r&&(~(i_collision_due_wr_r&&te_yy_wr_combine))) 
                  && ((te_rd_col_entry==r_entry) )) begin
        rd_entry_collided_per_bank[i_entry[r_entry*ENTRY_BITS + ENTRY_RANKBANK_LSB +: RANKBANK_BITS]] <= 1'b1;
      end
    end
  end
end

integer r_bank;
integer r_bsm;


// Number of non-collided commands serviced ahead when collided command present inside CAM
reg [15:0] num_of_non_collided_rds_serviced_per_bank[NUM_TOTAL_BANKS-1:0];
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    for(r_bank=0; r_bank<NUM_TOTAL_BANKS; r_bank=r_bank+1) begin : rd_num_non_col_rst_gen
      num_of_non_collided_rds_serviced_per_bank[r_bank] <= {16{1'b0}};
    end
  end else begin
    for(r_bank=0; r_bank<NUM_TOTAL_BANKS; r_bank=r_bank+1) begin : rd_num_non_col_cmd_gen
      if(rd_entry_collided_per_bank[r_bank] && ts_op_is_rd && ((te_rd_col_entry==te_rd_entry))
         && (ts_bank_num4rdwr==r_bank) && bank_alloc) begin 
         num_of_non_collided_rds_serviced_per_bank[r_bank] <= 16'h0;
      end else if(expired_vpr_per_bank[r_bank] && ts_op_is_rd && (pri_of_rd_op_cmd == CMD_PRI_XVPR) && (ts_bank_num4rdwr==r_bank) && bank_alloc) begin 
         num_of_non_collided_rds_serviced_per_bank[r_bank] <= 16'h0;
      end else if (rd_entry_collided_per_bank[r_bank] && ts_op_is_rd 
                   && (te_rd_col_entry!=te_rd_entry) 
                   && (ts_bank_num4rdwr==r_bank) && bank_alloc)begin
         num_of_non_collided_rds_serviced_per_bank[r_bank] <= num_of_non_collided_rds_serviced_per_bank[r_bank] + 1'b1;
      end else if (~rd_entry_collided_per_bank[r_bank]) begin
         num_of_non_collided_rds_serviced_per_bank[r_bank] <= 16'h0;
      end
    end
  end
end

// Calculation for non-collided cmds scheduled when collision present inside CAM
reg [15:0] num_of_non_collided_rcmds_sched_w_collision;
reg [15:0] total_num_of_non_collided_rcmds_sched_w_collision;
reg [15:0] max_num_of_non_collided_rcmds_sched_w_collision;

always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    num_of_non_collided_rcmds_sched_w_collision       <= 16'h0;
    max_num_of_non_collided_rcmds_sched_w_collision   <= 16'h0;
    total_num_of_non_collided_rcmds_sched_w_collision <= 16'h0;
  end else begin
    // Collision logic
    if((|rd_entry_collided_per_bank) && ts_op_is_rd) begin
      if(te_rd_col_entry==te_rd_entry
        || (pri_of_rd_op_cmd==CMD_PRI_XVPR)
      ) begin
        if(max_num_of_non_collided_rcmds_sched_w_collision<num_of_non_collided_rcmds_sched_w_collision) begin
          max_num_of_non_collided_rcmds_sched_w_collision <= num_of_non_collided_rcmds_sched_w_collision;
        end
        num_of_non_collided_rcmds_sched_w_collision <= 16'h0;
      end else begin
        num_of_non_collided_rcmds_sched_w_collision <= num_of_non_collided_rcmds_sched_w_collision + 1'b1;
        total_num_of_non_collided_rcmds_sched_w_collision <= total_num_of_non_collided_rcmds_sched_w_collision + 1'b1;
      end
    end else if(ts_op_is_rd) begin
      num_of_non_collided_rcmds_sched_w_collision <= 16'h0;
    end

  end
end

// Single HIF - 1 normal command to collided bank can be serviced ahead of collided command.
// Dual HIF - No normal command should be serviced ahead of collided command.
property p_non_collided_rd_serviced_for_collided_bank(bank_num);
@(posedge co_te_clk) disable iff (~core_ddrc_rstn ) 
      ( ts_op_is_rd && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && (rd_entry_collided_per_bank[bank_num] && (num_of_non_collided_rds_serviced_per_bank[bank_num]> 1))
      ) |-> (te_rd_col_entry==te_rd_entry);
endproperty

// Check expired-VPR get serviced ahead of collided entry
property p_non_collided_xvpr_serviced_for_collided_bank(bank_num);
   @(posedge co_te_clk) disable iff (~core_ddrc_rstn) // This fix is enabled by reg_ddrc_assert_both_cmd_stall 
      ( ts_op_is_rd && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( rd_entry_collided_per_bank[bank_num] && expired_vpr_per_bank[bank_num]  )
        && (!i_entry_vpr_timed_out[te_rd_col_entry])
        && (num_of_non_vpr_serviced_per_bank[bank_num]>0)
       )  |-> (te_rd_col_entry!=te_rd_entry) ;
endproperty

reg [RD_CAM_ENTRIES-1:0] te_vpr_valid_d2;
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn)
      te_vpr_valid_d2 <= {RD_CAM_ENTRIES{1'b0}};
   else
      te_vpr_valid_d2 <= te_vpr_valid_d;
end

property p_non_collided_serviced_for_collided_xvpr_bank(bank_num);
@(posedge co_te_clk) disable iff (~core_ddrc_rstn ) // This fix is enabled by reg_ddrc_assert_both_cmd_stall 
      ( ts_op_is_rd && (ts_bank_num4rdwr==bank_num) && bank_alloc
        && ( rd_entry_collided_per_bank[bank_num] && expired_vpr_per_bank[bank_num]  )
        && (i_entry_vpr_timed_out[te_rd_col_entry] && te_vpr_valid_d2[te_rd_col_entry]) //from expire to load_vp in NTT ,there are 2 cycles.
        && (!i_entry_vpr_timed_out[te_rd_entry])
        && (num_of_non_collided_rds_serviced_per_bank[bank_num]>0)
       )  |-> (te_rd_col_entry==te_rd_entry) ;
endproperty

// VCS coverage on
genvar bank_rd;
generate 
for(bank_rd=0; bank_rd<NUM_TOTAL_BANKS; bank_rd=bank_rd+1) begin : a_non_collided_serviced_bank_rd_gen
  a_non_collided_rd_serviced_for_collided_bank : cover property (p_non_collided_rd_serviced_for_collided_bank(bank_rd))
  $display("[%t][%m] WARNING: Non-collided read command is serviced when there is collided read present in the CAM for bank=%0d ", $time,bank_rd);

  a_non_collided_xpvr_serviced_for_collided_bank : assert property (p_non_collided_xvpr_serviced_for_collided_bank(bank_rd))
  else $display("[%t][%m] ERROR: Collided cmd serviced when Non-collided XVPR command in the CAM for bank=%0d ", $time,bank_rd);

  a_non_collided_serviced_for_collided_xpvr_bank : assert property (p_non_collided_serviced_for_collided_xvpr_bank(bank_rd))
  else $display("[%t][%m] ERROR: Non-collided cmd serviced when Collided XVPR command in the CAM for bank=%0d ", $time,bank_rd);

cp_num_non_collided_cmds_serviced_per_bank:
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn) (num_of_non_collided_rds_serviced_per_bank[bank_rd]> 1) )
    $display("[%t][%m] WARNING: Number of Non-collided commands scheduled when there is collided command present is greater than 1. Current Value is: %0d", $time, num_of_non_collided_rds_serviced_per_bank[bank_rd]);
end
endgenerate

cp_num_non_vpr_cmds_sched_gt_exp:
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn | reg_ddrc_opt_vprw_sch) (num_of_non_vpr_cmds_sched_w_exp_vpr_on > 16) )
    $display("[%t][%m] WARNING: Number of Non-VPR commands scheduled when there is an expired-VPR command present is greater than 16. Current Value is: %0d", $time, num_of_non_vpr_cmds_sched_w_exp_vpr_on);

cp_num_non_collided_rcmds_sched_gt_exp:
    cover property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn) (ts_op_is_rd && num_of_non_collided_rcmds_sched_w_collision > 16) )
    $display("[%t][%m] WARNING: Total number of Non-collided commands scheduled when there is collided command present is greater than 16. Current Value is: %0d", $time, num_of_non_collided_rcmds_sched_w_collision);

/*

 //-------------
 // Cover points associated with the expired VPR logic
 // Checking that the number of non-VPR commands that are executed before VPR is executed reaches
 //-------------

  wire vpr_read_w_expired_vpr_high = any_vpr_timed_out & ts_op_is_rd & (pri_of_rd_op_cmd == 2'b10);

// Coverage group
  covergroup cg_expired_vpr @(posedge co_te_clk);

    // number of non-vpr commands executed before executing a vpr cmd, when there are expired VPR commands
    cp_num_non_vpr_cmds : coverpoint ({vpr_read_w_expired_vpr_high, num_of_non_vpr_cmds_sched_w_exp_vpr_on}) iff(core_ddrc_rstn) {
                           bins vpr_0     = {9'b1_0000_0000};
                           bins vpr_1     = {9'b1_0000_0001};
                           bins vpr_2     = {9'b1_0000_0010};
                           bins vpr_3     = {9'b1_0000_0011};
                           bins vpr_4     = {9'b1_0000_0100};
                           bins vpr_5     = {9'b1_0000_0101};
                           bins vpr_6     = {9'b1_0000_0110};
                           bins vpr_7     = {9'b1_0000_0111};
                           bins vpr_8     = {9'b1_0000_1000};
                           bins vpr_9     = {9'b1_0000_1001};
                           bins vpr_10    = {9'b1_0000_1010};
                           bins vpr_11    = {9'b1_0000_1011};
                           bins vpr_12    = {9'b1_0000_1100};
                           bins vpr_13    = {9'b1_0000_1101};
                           bins vpr_14    = {9'b1_0000_1110};
                           bins vpr_15    = {9'b1_0000_1111};
                   illegal_bins vpr_ill   = {[9'h110:9'h1FF]};
    }

  endgroup

// Coverage group instantiation
  cg_expired_vpr cg_expired_vpr_inst = new;

*/



// note: following codes are commented out for bug 7584
// Check that auto-pre is issued for pageclose feature
// cover_rd_autopre_w_pageclose_check :
// cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (ts_op_is_rd && dh_te_pageclose && (dh_te_pageclose_timer==8'h00) && autopre_for_pageclose));


// wire  [ENTRY_AUTOPRE_BITS-1:0]        te_pi_rd_autopre_int;   // auto precharge bit
// generate
//  // mux out auto precharge bit for PI
//   for (bit_loc=ENTRY_AUTOPRE_LSB; bit_loc<=ENTRY_AUTOPRE_MSB; bit_loc=bit_loc+1)
//   begin : pi_autopre
//     te_rd_mux pi_autopre_mux (
//                        .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
//                        .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
//                        .out_port  (te_pi_rd_autopre_int [bit_loc-ENTRY_AUTOPRE_LSB])
//                       );
//   end
// 
// endgenerate

// Check the propagation of cmd_autopre through NTT and TS by comparing the stored CAM flag 
// property p_cmd_autopre_mismatch;
//   @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
//     (ts_op_is_rd) |-> (ts_rdwr_cmd_autopre==te_pi_rd_autopre_int);
// endproperty 
// a_cmd_autopre_mismatch : assert property (p_cmd_autopre_mismatch) else 
//   $display("-> %0t ERROR: RD CAM cmd_autopre mismatch CAM value:%0d, OS value:%0d", $realtime,te_pi_rd_autopre_int,ts_rdwr_cmd_autopre);



// RD CAM delayed autopre update queue overflow
property p_delayed_autopre_update_overflow;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (delayed_autopre_update_wr) |-> (!delayed_autopre_update_ff);
  
endproperty 
//a_delayed_autopre_update_overflow : assert property (p_delayed_autopre_update_overflow) else 
//  $display("-> %0t ERROR: RD CAM delayed autopre update queue overflow !!", $realtime);


  // mux out ie_bt for PI for assertion
  for (bit_loc=ENTRY_IE_BT_LSB; bit_loc<=ENTRY_IE_BT_MSB; bit_loc=bit_loc+1)
  begin : pi_ie_bt
    te_rd_mux
     pi_ie_bt_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_te_pi_ie_bt [bit_loc-ENTRY_IE_BT_LSB])
                      );
  end

  // mux out ie_rd_type for PI for assertion
  for (bit_loc=ENTRY_IE_RD_TYPE_LSB; bit_loc<=ENTRY_IE_RD_TYPE_MSB; bit_loc=bit_loc+1)
  begin : pi_ie_rd_type
    te_rd_mux
     pi_ie_rd_type_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_te_pi_ie_rd_type [bit_loc-ENTRY_IE_RD_TYPE_LSB])
                      );
  end

  // mux out ie_blk_burst_num for PI for assertion
  for (bit_loc=ENTRY_IE_BURST_NUM_LSB; bit_loc<=ENTRY_IE_BURST_NUM_MSB; bit_loc=bit_loc+1)
  begin : pi_ie_blk_burst_num
    te_rd_mux
     pi_ie_blk_burst_num_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_te_pi_ie_blk_burst_num [bit_loc-ENTRY_IE_BURST_NUM_LSB])
                      );
  end
  // mux out eccap for PI for assertion
  for (bit_loc=ENTRY_ECCAP_LSB; bit_loc<=ENTRY_ECCAP_MSB; bit_loc=bit_loc+1)
  begin : pi_eccap
    te_rd_mux
     pi_eccap_mux (
                       .in_port   (bit_entry [((bit_loc +1) * RD_CAM_ENTRIES) -1: (bit_loc * RD_CAM_ENTRIES)]),
                       .sel  (te_rd_entry [RD_CAM_ADDR_BITS -1:0]),
                       .out_port  (i_te_pi_eccap[bit_loc-ENTRY_ECCAP_LSB])
                      );
  end

covergroup cg_ie_normal_collision_within_block @(posedge co_te_clk);

  // Observe if normal collision is detected within a block  
  cp_ie_normal_collision_within_block : coverpoint (|i_ie_normal_col_win_blk) iff (core_ddrc_rstn) {
     bins normal_col_win_blk = {1'b1};
  }
  
  endgroup : cg_ie_normal_collision_within_block

cg_ie_normal_collision_within_block cg_ie_normal_collision_within_block_inst = new;

// Check that when one of i_same_addr_rd is asserted, there is at least one valid entry or i_ie_normal_col_win_blk
// This is implemented based on this assumption, so check the assumption.
property p_ie_i_same_addr_rd_filtered_check;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (|i_same_addr_rd & ((i_collision_due_rd | i_collision_due_wr))) |-> ((|i_same_addr_rd_filtered) | (|i_ie_normal_col_win_blk));
endproperty 
a_ie_i_same_addr_rd_filtered_check : assert property (p_ie_i_same_addr_rd_filtered_check) else 
  $display("-> %0t ERROR: When i_same_addr_rd is asserted there must be at least one valid colliding entry", $realtime);


assign i_ie_rd_blk_addr_collision = i_ie_blk_addr_collision; // For coverpoint

property p_rd_is_not_allowed_after_act_for_nxt_cycle;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (~(r_ts_op_is_activate_wr & ts_op_is_rd)); 
endproperty

a_rd_is_not_allowed_after_act_for_nxt_cycle : assert property (p_rd_is_not_allowed_after_act_for_nxt_cycle) else 
  $display("-> %0t ERROR: RD is scheduled-out in next cycle of ACT for WR!!, this is prohibitted in this HW configuration", $realtime);


property p_rd_pghit_limit_check;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    ((ts_op_is_rd & i_entry_critical_per_bsm_early[ts_bsm_num4rdwr]) |-> ((te_entry_critical_early & te_bank_hit) == te_bank_hit)); 
endproperty

// When the bsm is expired in terms of page_hit limiter, te_entry_critical_early is asserted as same as bank_hit 
a_rd_pghit_limit_check : assert property (p_rd_pghit_limit_check) else 
  $display("-> %0t ERROR: When the bsm is expired in terms of page_hit limiter, te_entry_critical_early is asserted as same as bank_hit", $realtime);


// note: following codes are commented out for bug 7584   
// `ifdef MEMC_USE_RMW 
// This is original code before synthesis improvement on bug 6494
// wire rmw_type_no_rmw;
// assign rmw_type_no_rmw= (te_pi_rd_other_fields_rd[OTHER_RD_RMW_LSB+:OTHER_RD_RMW_TYPE_BITS] == `MEMC_RMW_TYPE_NO_RMW) ? 1'b1:1'b0;
// 
// property p_ts_rdwr_cmd_autopre_1_is_always_1_for_rmw;
//   @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
//     ((ts_op_is_rd & rmw_type_no_rmw==0) |-> ts_rdwr_cmd_autopre[1]==1);
// endproperty
// 
// a_ts_rdwr_cmd_autopre_1_is_always_1_for_rmw : assert property (p_ts_rdwr_cmd_autopre_1_is_always_1_for_rmw) else 
//   $display("-> %0t ERROR: ts_rdwr_cmd_autopre[1] must be 1 for read part of RMW", $realtime);
// 
// 
//   `ifndef MEMC_INLINE_ECC
// property p_ts_rdwr_cmd_autopre_1_is_always_0_for_non_rmw;
//   @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
//     ((ts_op_is_rd & rmw_type_no_rmw==1) |-> ts_rdwr_cmd_autopre[1]==0);
// endproperty
// 
// a_ts_rdwr_cmd_autopre_1_is_always_0_for_non_rmw : assert property (p_ts_rdwr_cmd_autopre_1_is_always_0_for_non_rmw) else 
//   $display("-> %0t ERROR: ts_rdwr_cmd_autopre[1] must be 0 for non-read part of RMW", $realtime);
// 
//   `endif // !MEMC_INLINE_ECC
// `endif // MEMC_USE_RMW

// For intelligent Autopre 
property p_lpddr5_act_rd_check;
  @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (((ts_op_is_activate | be_op_is_activate_bypass_int) & ts_op_is_rd) |=> (~ts_op_is_activate & ~be_op_is_activate_bypass_int & ~ts_op_is_rd));
endproperty

a_lpddr5_act_rd_check : assert property (p_lpddr5_act_rd_check) else 
  $display("-> %0t ERROR: LPDDR5: When ACT and RD are issued on a cycle, ACT or RD is not allowd in the next cycle", $realtime);

`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule // te_rd_cam
