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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_rd_entry.sv#5 $
// -------------------------------------------------------------------------
// Description:
// 1. entry contents of the read CAM
// 2. returns participation and page hit on cam search
// 3. collision detection
//
// -------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_rd_entry #(
    //-------------------------------- PARAMETERS ----------------------------------
    // bit widths; should be overridden from read CAM
     parameter       RANKBANK_BITS      = 5
    ,parameter       PAGE_BITS          = 16
    ,parameter       BLK_BITS           = 10
    ,parameter       BG_BANK_BITS       = 4
    ,parameter       RANK_BITS          = 0
    ,parameter       BSM_BITS           = `UMCTL2_BSM_BITS
    ,parameter       OTHER_ENTRY_BITS   = 31
    ,parameter       BANK_BITS          = 3
    ,parameter       BG_BITS            = 2
    // fields of entry
    ,parameter       RMW_BITS           = 1
    ,parameter       RD_LATENCY_BITS    = `UMCTL2_XPI_RQOS_TW
    ,parameter       BT_BITS            = `MEMC_BLK_TOKEN_BITS // Override
    ,parameter       IE_WR_TYPE_BITS    = 2
    ,parameter       IE_RD_TYPE_BITS    = 2
    ,parameter       IE_BURST_NUM_BITS  = 3
    ,parameter       IE_UNIQ_BLK_BITS   = 4
    ,parameter       IE_UNIQ_BLK_LSB    = 3
    ,parameter       IE_MASKED_BITS     = 1
    ,parameter       ECCAP_BITS         = 1
    ,parameter       RETRY_RD_BITS      = 1
    ,parameter       RETRY_TIMES_WIDTH  = 3
    ,parameter       CRC_RETRY_TIMES_WIDTH  = 4
    ,parameter       UE_RETRY_TIMES_WIDTH  = 4
    ,parameter       RD_CRC_RETRY_LIMIT_REACH_BITS = 1
    ,parameter       RD_UE_RETRY_LIMIT_REACH_BITS = 1
    ,parameter       DDR4_COL3_BITS     = 1
    ,parameter       LP_COL4_BITS       = 1
    ,parameter       WORD_BITS          = 1
    ,parameter       CMD_LEN_BITS       = 1
    // 2-bit read priority encoding
    ,parameter       CMD_PRI_LPR        = `MEMC_CMD_PRI_LPR     
    ,parameter       CMD_PRI_VPR        = `MEMC_CMD_PRI_VPR      
    ,parameter       CMD_PRI_HPR        = `MEMC_CMD_PRI_HPR      
    ,parameter       CMD_PRI_XVPR       = `MEMC_CMD_PRI_XVPR      
    ,parameter       ENTRY_VALID        = 0                  // bit 0 of entry is the valid bit
    ,parameter       AUTOPRE_BITS       = 1                  // bit 1 of entry is auto pre-charge bit
    ,parameter       NUM_TOTAL_BANKS    = 1 << RANKBANK_BITS
    ,parameter       IME_WR_TWEAK_BITS = 0
    )
    (
    //---------------------------- INPUTS AND OUTPUTS ------------------------------
     input                         core_ddrc_rstn            // reset
    ,input                         co_te_clk                 // main clock
    ,input                         ddrc_cg_en                // clock gating enable
    ,input  [1:0]                  ih_te_hi_pri              // incoming is a high priority read command
    ,output [1:0]                  i_entry_out_pri           // priority
    ,output                        i_entry_out_hpr           // HPR or HPRL 
    ,input  [PAGE_BITS-1:0]        r_ts_act_page             // Row address of the activated page during read mode
    ,input  [RD_LATENCY_BITS-1:0]  ih_te_rd_latency          // rd_latency input from IH module
    ,input                         r_te_rdwr_autopre         // autopre this cycle
    ,input  [BSM_BITS-1:0]         r_ts_bsm_num4pre          // BSM numer of the precharge cmd selected by the scheduler
    ,input  [BSM_BITS-1:0]         r_ts_bsm_num4any          // BSM number of the ACT , ACT bypass, PRE or RDWR (registered)
    ,input  [BSM_BITS-1:0]         r_ts_bsm_num4act          // BSM number of the ACT , ACT bypass (registered)      
    ,input  [BSM_BITS-1:0]         r_ts_bsm_num4rdwr         // BSM number of the RDWR (registered)      
    ,input                         r_ts_op_is_precharge      // precharge scheduled this cycle
    ,input                         r_ts_op_is_activate       // activate scheduled this cycle
    ,input                         be_te_page_hit            // the incoming command from IH has a current page hit    
    ,input                         ih_te_rmw                 // incoming is a read-modify-write
    ,input                         ih_te_rd_autopre          // auto precharge enable
    ,input  [RANKBANK_BITS-1:0]    ih_te_rd_rankbank_num     // bank number
    ,input  [PAGE_BITS-1:0]        ih_te_rd_page_num         // page number
    ,input  [BLK_BITS-1:0]         ih_te_rd_block_num        // page number
    ,input                         load_cam_any              // load CAM for any entry 
    ,input  [BT_BITS-1:0]          ih_te_ie_bt
    ,input  [IE_WR_TYPE_BITS-1:0]  ih_te_ie_wr_type
    ,input  [IE_RD_TYPE_BITS-1:0]  ih_te_ie_rd_type
    ,input  [IE_BURST_NUM_BITS-1:0]ih_te_ie_blk_burst_num
    ,input  [IE_UNIQ_BLK_BITS-1:0] ie_ecc_uniq_block_num
    ,input  [BT_BITS-1:0]          te_pi_ie_bt
    ,input                         i_rd_ecc_status
    ,input  [IE_RD_TYPE_BITS-1:0]  te_pi_ie_rd_type
    ,input                         te_normal_col_win_blk     // Normal address collision within a block 
    ,input                         ih_te_rd_eccap

    ,input  [CMD_LEN_BITS-1:0]     ih_te_rd_length
    ,input  [WORD_BITS-1:0]        ih_te_critical_dword
    ,input  [OTHER_ENTRY_BITS-1:0] ih_te_other_fields        // everything else
    ,input  [BSM_BITS-1:0]         ts_bsm_num4rdwr           // BSM number on DRAM access
    ,input                         ts_op_is_rd               // current DRAM op is a read
    ,input                         i_load                    // store entry signal
    ,input                         i_entry_del               // delete entry signal
    ,output [RANKBANK_BITS-1:0]    i_entry_out_rankbank      // entry contents
    ,output [PAGE_BITS-1:0]        i_entry_out_page          // entry contents
    ,output [BLK_BITS-1:0]         i_entry_out_blk           // entry contents
    ,output [CMD_LEN_BITS-1:0]     i_entry_out_rd_length     // entry contents
    ,output [WORD_BITS-1:0]        i_entry_out_critical_dword //entry contents   
    ,output [OTHER_ENTRY_BITS-1:0] i_entry_out_other_fields  // entry contents
    ,output [AUTOPRE_BITS-1:0]     i_entry_out_autopre       // entry contents
    ,output [BT_BITS-1:0]          i_entry_out_ie_bt
    ,output [IE_RD_TYPE_BITS-1:0]  i_entry_out_ie_rd_type
    ,output [IE_BURST_NUM_BITS-1:0]i_entry_out_ie_blk_burst_num
    ,output                        i_ie_normal_col_win_blk    // Detect normal address collision within a block
    ,output                        i_ie_blk_addr_collision        
    ,output                        i_entry_out_eccap
    ,output                        i_same_addr_rd            // same address as incoming xaction address
    ,output                        i_same_addr_rmw           // same address as incoming xaction address
    ,output                        i_entry_vpr_timed_out     // VPR entry timed-out
    ,output                        i_entry_vpr_valid         // goes high for all entries that are expired-VPR commands
    ,output reg                    i_entry_vpr_valid_d       // one cycle delay version (posedge only) of expired-VPR command
    ,output                        i_entry_vpr_page_hit      // page hit indicator to VPR selection n/w in rd_replace module 
    ,output                        i_entry_upd_to_vpr_due_ie // for assertion use 
    ,output                        i_bank_hit                // same rank/bank number on cam search but asserted only if this entry is not expired-VPR
                                                             // in designs where UMCTL2_VPR_EN is not defined, this will be same as i_bank_hit
    ,output                        i_bank_hit_act            // same rank/bank number with ACT 
    ,input  [BSM_BITS-1:0]         ts_bsm_num4pre            // BSM numer of the precharge cmd selected by the scheduler
    ,output                        i_bank_hit_pre            // same rank/bank number with PRE 
    ,output                        i_page_hit                // same page number as in open page table in BE module
    ,output                        i_entry_valid             // entry is valid
    ,output                        i_entry_loaded            // entry is loaded
    ,output                        page_open_any_op          // page is open for this entry if same bank of ACT, RDWR, or PRE one cycle earlier
    ,input                         page_hit_limit_reached
    ,input                         page_hit_limit_incoming   // Incoming bank has page-hit_limiter expired
    ,output reg                    i_entry_critical_early
    ,input [8:0]                   vlimit_int
    ,input                         i_vlimit_decr
    ,output                        te_rd_vlimit_reached
    `ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
    `endif
    `endif

    );

    //------------------------- LOCAL PARAMETERS -----------------------------------
    localparam        ENTRY_AUTOPRE_LSB      = 1;
    localparam        ENTRY_AUTOPRE_MSB      = ENTRY_AUTOPRE_LSB + AUTOPRE_BITS - 1; 
    localparam        ENTRY_HI_PRI_LSB       = ENTRY_AUTOPRE_MSB+1;
    localparam        ENTRY_HI_PRI_MSB       = ENTRY_HI_PRI_LSB + 2 - 1;
    localparam        ENTRY_RMW              = ENTRY_HI_PRI_MSB + RMW_BITS;
    localparam        ENTRY_BLK_LSB          = ENTRY_RMW + 1;
    localparam        ENTRY_BLK_MSB          = ENTRY_BLK_LSB + BLK_BITS - 1;
    localparam        ENTRY_ROW_LSB          = ENTRY_BLK_MSB + 1;
    localparam        ENTRY_ROW_MSB          = ENTRY_ROW_LSB + PAGE_BITS - 1;
    localparam        ENTRY_RANKBANK_LSB     = ENTRY_ROW_MSB + 1;
    localparam        ENTRY_RANKBANK_MSB     = ENTRY_RANKBANK_LSB + RANKBANK_BITS - 1;
    localparam        ENTRY_IE_BT_LSB        = ENTRY_RANKBANK_MSB + 1;
    localparam        ENTRY_IE_BT_MSB        = ENTRY_IE_BT_LSB + BT_BITS - 1;
    localparam        ENTRY_IE_RD_TYPE_LSB   = ENTRY_IE_BT_MSB + 1;
    localparam        ENTRY_IE_RD_TYPE_MSB   = ENTRY_IE_RD_TYPE_LSB + IE_RD_TYPE_BITS - 1;
    localparam        ENTRY_IE_BURST_NUM_LSB = ENTRY_IE_RD_TYPE_MSB + 1;
    localparam        ENTRY_IE_BURST_NUM_MSB = ENTRY_IE_BURST_NUM_LSB + IE_BURST_NUM_BITS - 1;
    localparam        ENTRY_IE_UNIQ_BLK_LSB  = ENTRY_IE_BURST_NUM_MSB + 1;
    localparam        ENTRY_IE_UNIQ_BLK_MSB  = ENTRY_IE_UNIQ_BLK_LSB + IE_UNIQ_BLK_BITS - 1;
    localparam        ENTRY_IE_MASKED_LSB    = ENTRY_IE_UNIQ_BLK_MSB + 1;
    localparam        ENTRY_IE_MASKED_MSB    = ENTRY_IE_MASKED_LSB + IE_MASKED_BITS - 1;
    localparam        ENTRY_ECCAP_LSB        = ENTRY_IE_MASKED_MSB + 1;
    localparam        ENTRY_ECCAP_MSB        = ENTRY_ECCAP_LSB + ECCAP_BITS - 1;
    localparam        ENTRY_RETRY_RD_LSB     = ENTRY_ECCAP_MSB + 1;
    localparam        ENTRY_RETRY_RD_MSB     = ENTRY_RETRY_RD_LSB + RETRY_RD_BITS - 1;
    localparam        ENTRY_CRC_RETRY_TIMES_LSB  = ENTRY_RETRY_RD_MSB + 1;
    localparam        ENTRY_CRC_RETRY_TIMES_MSB  = ENTRY_CRC_RETRY_TIMES_LSB + CRC_RETRY_TIMES_WIDTH -1;
    localparam        ENTRY_UE_RETRY_TIMES_LSB   = ENTRY_CRC_RETRY_TIMES_MSB + 1;
    localparam        ENTRY_UE_RETRY_TIMES_MSB   = ENTRY_UE_RETRY_TIMES_LSB + UE_RETRY_TIMES_WIDTH -1;
    localparam        ENTRY_RD_CRC_RETRY_LIMIT_REACH_LSB = ENTRY_UE_RETRY_TIMES_MSB + 1;
    localparam        ENTRY_RD_CRC_RETRY_LIMIT_REACH_MSB = ENTRY_RD_CRC_RETRY_LIMIT_REACH_LSB + RD_CRC_RETRY_LIMIT_REACH_BITS -1;
    localparam        ENTRY_RD_UE_RETRY_LIMIT_REACH_LSB = ENTRY_RD_CRC_RETRY_LIMIT_REACH_MSB + 1;
    localparam        ENTRY_RD_UE_RETRY_LIMIT_REACH_MSB = ENTRY_RD_UE_RETRY_LIMIT_REACH_LSB + RD_UE_RETRY_LIMIT_REACH_BITS -1;
    localparam        ENTRY_DDR4_COL3_LSB    = ENTRY_RD_UE_RETRY_LIMIT_REACH_MSB + 1;
    localparam        ENTRY_DDR4_COL3_MSB    = ENTRY_DDR4_COL3_LSB + DDR4_COL3_BITS - 1;
    localparam        ENTRY_LP_COL4_LSB      = ENTRY_DDR4_COL3_MSB + 1;
    localparam        ENTRY_LP_COL4_MSB      = ENTRY_LP_COL4_LSB + LP_COL4_BITS - 1;
    localparam        ENTRY_OTHER_LSB        = ENTRY_LP_COL4_MSB + 1;
    localparam        ENTRY_OTHER_MSB        = ENTRY_OTHER_LSB + OTHER_ENTRY_BITS - 1;
    localparam        ENTRY_LENGTH_LSB       = ENTRY_OTHER_MSB + 1;
    localparam        ENTRY_LENGTH_MSB       = ENTRY_LENGTH_LSB + CMD_LEN_BITS - 1;
    localparam        ENTRY_WORD_LSB         = ENTRY_LENGTH_MSB + 1;
    localparam        ENTRY_WORD_MSB         = ENTRY_WORD_LSB + WORD_BITS - 1;
    localparam        ENTRY_TWEAK_LSB        = ENTRY_WORD_MSB + 1;
    localparam        ENTRY_TWEAK_MSB        = ENTRY_TWEAK_LSB + IME_WR_TWEAK_BITS - 1;
    localparam        ENTRY_HPR_LSB          = ENTRY_TWEAK_MSB + 1;
    localparam        ENTRY_BITS             = ENTRY_HPR_LSB + 1;
    localparam        CATEGORY =5;

//----------------------------- REGS AND WIRES ---------------------------------

reg  [ENTRY_BITS-1:0]         r_entry;                  // actual storage

assign                        i_entry_out_pri = r_entry [ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB];
assign                        i_entry_out_hpr = r_entry [ENTRY_HPR_LSB];

reg  [RD_LATENCY_BITS-1:0]    r_entry_rd_latency,r_entry_rd_latency_ns;
reg                           r_entry_rd_latency_zero;
reg                           valid_entry_is_vpr;
wire                          vpr_to_exp_vpr;
reg  [8:0]                    visible_window_counter;
reg                           visible_window_reached;
wire                          i_same_rdwr_bank;

wire                          i_entry_ie_masked;
wire                          i_entry_ie_mask_clr;
// i_entry_ie_mask_clr : When ts_op_is_rd=1 & i_entry_ie_mask_clr, i_entry_ie_mask is cleared. 
// This means corresponding RE_B is scheduled this cycle. 
assign i_entry_ie_mask_clr = (te_pi_ie_rd_type == `IE_RD_TYPE_RE_B) & (te_pi_ie_bt==i_entry_out_ie_bt);

reg                           i_entry_ie_rd_n;
reg                           i_entry_ie_rd_e;
reg                           i_entry_ie_re_b;


wire                          upd_to_vpr_due_ie; // RD_E are incomming and RE_B are exsisting and BT is same. Then update to VPR 
assign upd_to_vpr_due_ie  = (load_cam_any & i_entry_loaded) & (ih_te_hi_pri == CMD_PRI_VPR) & 
                            (ih_te_ie_rd_type==`IE_RD_TYPE_RD_E && i_entry_out_ie_rd_type==`IE_RD_TYPE_RE_B && i_entry_out_ie_bt == ih_te_ie_bt);

assign i_entry_upd_to_vpr_due_ie = upd_to_vpr_due_ie;


//------------------------------ MAINLINE CODE ---------------------------------
assign i_entry_out_ie_bt            = r_entry[ENTRY_IE_BT_MSB        : ENTRY_IE_BT_LSB];
assign i_entry_out_ie_rd_type       = r_entry[ENTRY_IE_RD_TYPE_MSB   : ENTRY_IE_RD_TYPE_LSB];
assign i_entry_out_ie_blk_burst_num = r_entry[ENTRY_IE_BURST_NUM_MSB : ENTRY_IE_BURST_NUM_LSB];
assign i_entry_ie_masked            = r_entry[ENTRY_IE_MASKED_LSB];
assign i_entry_out_eccap            = r_entry[ENTRY_ECCAP_MSB:ENTRY_ECCAP_LSB];
assign i_entry_out_autopre          = r_entry [ENTRY_AUTOPRE_MSB:ENTRY_AUTOPRE_LSB];
assign i_entry_out_rd_length        = r_entry [ENTRY_LENGTH_MSB      : ENTRY_LENGTH_LSB];
assign i_entry_out_critical_dword   = r_entry [ENTRY_WORD_MSB        : ENTRY_WORD_LSB];
assign i_entry_out_other_fields     = r_entry [ENTRY_OTHER_MSB       : ENTRY_OTHER_LSB];
assign i_entry_out_rankbank         = r_entry [ENTRY_RANKBANK_MSB    : ENTRY_RANKBANK_LSB ];
assign i_entry_out_page             = r_entry [ENTRY_ROW_MSB         : ENTRY_ROW_LSB  ];
assign i_entry_out_blk              = r_entry [ENTRY_BLK_MSB         : ENTRY_BLK_LSB  ];
assign i_entry_loaded               = r_entry [ENTRY_VALID];
assign i_entry_valid                = i_entry_loaded
                                      & (~i_entry_ie_masked)
;


//-------------------------   r_page_open ---------------------------------------
reg   r_page_open;
wire  r_page_hit_act;
wire  set_page_open_for_act;
wire  set_page_close_for_pre;
wire  page_open_next;
wire  page_open;

   
//---------------------------
// comparators to decide bank and page hit for act and pre commands
// need this to generate the r_page_open flag per-entry
//---------------------------
wire r_same_bank_any_op;
wire r_same_bank_act_op;   
wire r_same_bank_rdwr_op;   
wire r_same_pre_bank;
wire i_entry_valid_same_bank = `UPCTL2_EN ? i_entry_valid : 1'b1; // wire used in uMCTL2/uPCTL2 combined logic


//Combine with r_same_pre_rank for the comparison of Rank.

assign r_same_bank_any_op   = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4any))  & i_entry_valid_same_bank;
assign r_same_bank_act_op   = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4act))  & i_entry_valid_same_bank;
assign r_same_bank_rdwr_op  = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4rdwr)) & i_entry_valid_same_bank;
assign r_same_pre_bank      = (& (i_entry_out_rankbank ~^ r_ts_bsm_num4pre))  & i_entry_valid_same_bank;
assign page_open_any_op     = `UPCTL2_EN ? page_open_next & r_same_bank_any_op :  page_open_next & r_same_bank_any_op & i_entry_loaded;  
   
assign r_page_hit_act       = (& (i_entry_out_page      ~^ r_ts_act_page   )) & r_same_bank_act_op;

assign set_page_open_for_act  = r_ts_op_is_activate & r_page_hit_act;

assign set_page_close_for_pre = (r_te_rdwr_autopre & r_same_bank_rdwr_op) | (r_ts_op_is_precharge & r_same_pre_bank)
;


wire   i_be_te_page_hit;
assign i_be_te_page_hit = be_te_page_hit;

reg r_be_te_page_hit;
reg r_load;
assign  page_open = set_page_open_for_act ? 1'b1 :
                    set_page_close_for_pre ? 1'b0 :
        r_load ? r_be_te_page_hit :r_page_open;

assign page_open_next = `UPCTL2_EN ? page_open : (page_open & i_entry_loaded);
   
always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
     r_page_open        <= 1'b0;
     r_be_te_page_hit   <= 1'b0;
     r_load             <= 1'b0;
  end
  else begin
     r_page_open        <= page_open_next;
     r_be_te_page_hit   <= i_be_te_page_hit;
     r_load             <= i_load;
  end
end // always @ (posedge co_te_clk or negedge core_ddrc_rstn)
   


// entry valid contents
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    r_entry [ENTRY_BITS-1:0] <= {ENTRY_BITS{1'b0}};
  end
  else if(ddrc_cg_en)
  begin
    if (i_load) begin
      r_entry[ENTRY_LENGTH_MSB:ENTRY_LENGTH_LSB]   <= ih_te_rd_length;
      r_entry[ENTRY_WORD_MSB: ENTRY_WORD_LSB]      <= ih_te_critical_dword;

      r_entry[ENTRY_OTHER_MSB:ENTRY_OTHER_LSB]     <= ih_te_other_fields; // read tag
      r_entry[ENTRY_RMW]                           <= ih_te_rmw;          // RMW type
      r_entry[ENTRY_AUTOPRE_LSB]                    <= ih_te_rd_autopre;      // auto precharge enable
      r_entry[ENTRY_AUTOPRE_MSB]                    <= (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B) | ih_te_rmw; // For RE_B or read part of RMW, AP is not applied      
      r_entry[ENTRY_RANKBANK_MSB:ENTRY_RANKBANK_LSB]<= ih_te_rd_rankbank_num;// bank number
      r_entry[ENTRY_ROW_MSB:ENTRY_ROW_LSB]         <= ih_te_rd_page_num;     // page number
      r_entry[ENTRY_BLK_MSB:ENTRY_BLK_LSB]         <= ih_te_rd_block_num;    // block number
      r_entry[ENTRY_IE_UNIQ_BLK_MSB:ENTRY_IE_UNIQ_BLK_LSB]   <= ie_ecc_uniq_block_num;
      r_entry[ENTRY_IE_BT_MSB:ENTRY_IE_BT_LSB]               <= ih_te_ie_bt;
      r_entry[ENTRY_IE_RD_TYPE_MSB:ENTRY_IE_RD_TYPE_LSB]     <= ih_te_ie_rd_type[IE_RD_TYPE_BITS-1:0];
      r_entry[ENTRY_IE_BURST_NUM_MSB:ENTRY_IE_BURST_NUM_LSB] <= ih_te_ie_blk_burst_num;
      r_entry[ENTRY_ECCAP_MSB:ENTRY_ECCAP_LSB]     <= ih_te_rd_eccap;
    end



    if (i_load)
       r_entry[ENTRY_VALID] <= 1'b1;
    else if (i_entry_del)
      r_entry[ENTRY_VALID]  <= 1'b0;
     if (i_load) begin
      r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB]   <= ih_te_hi_pri[1]? CMD_PRI_HPR : ih_te_hi_pri;  // load value from IH
      // From IH, following two type HPRs     
      // ih_te_hi_pri==2'b11 : HPRL (HPR consumes HPR credit)
      // ih_te_hi_pri==2'b10 : HPR  (HPR consumes LPR credit)
      // However, 2'b11 is used exVPR, so both above are pushed as HPR
      // Then recode HPR into ENTRY_HPR_LSB for age tracker push/pop purpose
      r_entry[ENTRY_HPR_LSB]                       <= ih_te_hi_pri[1];  // HPR | HPRL  
     end
     else if(vpr_to_exp_vpr) begin
      r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB]   <= CMD_PRI_XVPR;         // all expired-VPR cmds switch to 2'b11 priority
     end
     else if(upd_to_vpr_due_ie & r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB]!= CMD_PRI_XVPR) begin
         r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB]   <= CMD_PRI_VPR;  // update to VPR
     end
    if (i_load) begin
       r_entry[ENTRY_IE_MASKED_LSB] <= i_rd_ecc_status;
    end
    else if (ts_op_is_rd & i_entry_ie_mask_clr) begin
       r_entry[ENTRY_IE_MASKED_LSB] <= 1'b0;
    end

  end

// comparators
assign i_same_rdwr_bank=(& (r_entry [ENTRY_RANKBANK_MSB:ENTRY_RANKBANK_LSB] ~^ ts_bsm_num4rdwr [BSM_BITS-1:0]));

// cam search
// this signal goes high for all the entries that have a bank-hit to the currently scheduled command
// this is used as the valid signal going to the filter n/w in the te_rd_replace module
assign i_bank_hit =   (ts_op_is_rd & i_same_rdwr_bank 
                      & (i_entry_valid   // This entry is valid
                         | (i_entry_loaded & i_entry_ie_mask_clr) // This entry is valid in next cycle.
                        )); 

// cam serch by ACT for WR
assign i_bank_hit_act = r_same_bank_act_op & i_entry_valid;
// cam serch by PRE
assign i_bank_hit_pre       = (ts_bsm_num4pre==i_entry_out_rankbank) & i_entry_valid;


// page hit 
// no need to check rank/bank as the the page hit info will be used only for entries with i_bank_hit in te_rd_replce module
assign i_page_hit = page_open_next;   

// collision detection
// Internal address signal for collision detection

// CAM entry
reg  [RANKBANK_BITS-1:0]               i_entry_rankbank;
reg  [BLK_BITS-1:0]                    i_entry_blk;
reg  [PAGE_BITS-1:0]                   i_entry_page;

// Incomiing command
reg  [RANKBANK_BITS-1:0]               i_rd_incoming_rankbank;
reg  [BLK_BITS-1:0]                    i_rd_incoming_blk;
reg  [PAGE_BITS-1:0]                   i_rd_incoming_page;

reg  [BT_BITS-1:0]                     i_entry_bt;
reg  [BT_BITS-1:0]                     i_incoming_bt;

wire                                   ie_compare_ecc;
wire                                   ie_compare_data;
wire                                   ie_compare_ie_bt;
wire                                   ie_compare_blk_burst;

//-----------------------------
// Inline ECC Collision Matrix 
//-----------------------------
//
//+-----------------+----------+---------+-------+--------+----+
//| i_entry_rd_type | Incoming | Compare | BT    | Offset |Type|
//|                 | type     | Address | check | Check  |    |
//+-----------------+----------+---------+-------+--------+----+
//|                 | RD_N     | Data    |       |        |Norm|
//|                 | RD_E     | ECC     |       |        |Blk | ECC hole access only.
//| RD_N            | RE_B     | ECC(*)  |       |        |Blk | ECC hole access only
//|                 | WD_N     | Data    |       |        |Norm| 
//|                 | WD_E     | ECC     |       |        |Blk | ECC hole access only.
//|                 | WE_BW    | ECC(*)  |       |        |Blk | This shoud never happens because collision must be resolved by previous WD_E.
//+-----------------+----------+---------+-------+--------+----+
//|                 | RD_N     | ECC     |       |        |Blk | ECC hole access only.
//|                 | RD_E     | ECC     | same  | same   |Norm|
//|                 |          | ECC     | diff  |        |Blk |
//| RD_E            | RE_B     | ECC     | diff  |        |Blk |
//|                 | WD_N     | ECC     |       |        |Blk | ECC hole access only.
//|                 | WD_E     | ECC     | same  | same   |Norm|
//|                 |          | ECC     | diff  |        |Blk |
//|                 | WE_BW    | ECC     | diff  |        |Blk | This shoud never happens because collision must be resolved by previous WD_E.
//+-----------------+----------+---------+-------+--------+----+
//|                 | RD_N     | ECC(*)  |       |        |Blk | ECC hole access only. 
//|                 | RD_E     | ECC     | diff  |        |Blk |
//| RE_B            | RE_B     | ECC     | diff  |        |Blk |
//|                 | WD_N     | ECC(*)  |       |        |Blk | ECC hole access only.
//|                 | WD_E     | ECC     | diff  |        |Blk |
//|                 | WE_BW    | ECC     | diff  |        |Blk | This shoud never happens because collision must be resolved by previous WD_E.
//+-----------------+----------+---------+-------+--------+----+
// (*) Either Data or ECC is Okay because of the following
// For WD_N/RD_N on ECC region, ECC address == Data address
// For WE_*/RE_*, ECC address == Data address

assign ie_compare_ecc    = ~ie_compare_data;
assign ie_compare_data   =  i_entry_ie_rd_n & ((ih_te_ie_rd_type == `IE_RD_TYPE_RD_N) | (ih_te_ie_wr_type == `IE_WR_TYPE_WD_N));

assign ie_compare_ie_bt  =  (
                               (~i_entry_ie_rd_n) // == (i_entry_ie_rd_e | i_entry_ie_re_b)
                            )
                          & (
                               (ih_te_ie_rd_type == `IE_RD_TYPE_RD_E)
                             | (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B)
                             | (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E)
                             | (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW)
                            )
                          & (
                             // If normal collision is detected within block and this entry is RE_B, disable BT compare
                             // so that this RE_B is candidate of flush
                             ~(te_normal_col_win_blk & i_entry_ie_re_b) 
                            )
;


assign ie_compare_blk_burst = (
                               i_entry_ie_rd_e  
                              )
                            & (
                               (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E)
                             | (ih_te_ie_rd_type == `IE_RD_TYPE_RD_E)
                              );  
// If normal collision is detected in a block, and this entry is RD_E, assert this signal.
// in te_rd_cam, this is OR'd and flopped
assign i_ie_normal_col_win_blk  = (i_entry_ie_rd_e) & // This entry is RD_E 
                                  ((ih_te_ie_rd_type == `IE_RD_TYPE_RD_E) | (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E)) &
                                  (i_entry_bt == i_incoming_bt) & // Same block 
                                  i_same_addr_rd; // Collision is detected

// Indicate any block address collision (for debug port)
assign i_ie_blk_addr_collision = i_same_addr_rd & ie_compare_ecc & ~(ie_compare_ie_bt & (i_entry_bt == i_incoming_bt)) & ~te_normal_col_win_blk;

// Assign Existing address to be compared
always @(*) begin
  // For existing entry
  i_entry_rankbank       = r_entry [ENTRY_RANKBANK_MSB:ENTRY_RANKBANK_LSB];
  i_entry_blk            = r_entry [ENTRY_BLK_MSB:ENTRY_BLK_LSB];
  i_entry_page           = r_entry [ENTRY_ROW_MSB:ENTRY_ROW_LSB];
  // For incoming entry
  i_rd_incoming_rankbank = ih_te_rd_rankbank_num;
  i_rd_incoming_blk      = ih_te_rd_block_num;
  i_rd_incoming_page     = ih_te_rd_page_num;
  i_entry_bt             = r_entry[ENTRY_IE_BT_MSB:ENTRY_IE_BT_LSB];  
  i_incoming_bt          = ih_te_ie_bt;
  if (ie_compare_ecc) begin
  // For existing entry (Replace corresponding addres bits to ECC address)
  i_entry_blk         [IE_UNIQ_BLK_LSB+:IE_UNIQ_BLK_BITS] = r_entry [ENTRY_IE_UNIQ_BLK_MSB:ENTRY_IE_UNIQ_BLK_LSB];
  // For incoming entry
  i_rd_incoming_blk      [IE_UNIQ_BLK_LSB+:IE_UNIQ_BLK_BITS] = ie_ecc_uniq_block_num;
  end
end


assign
  i_same_addr_rd = i_entry_loaded 
                   & (& (i_entry_rankbank ~^ i_rd_incoming_rankbank [RANKBANK_BITS-1:0])) 
                   & (& (i_entry_page     ~^ i_rd_incoming_page     [PAGE_BITS-1:0]))     
                   & (& (i_entry_blk      ~^ i_rd_incoming_blk      [BLK_BITS-1:0]))
                   & ((i_entry_bt != i_incoming_bt) | (ie_compare_blk_burst & (ih_te_ie_blk_burst_num == i_entry_out_ie_blk_burst_num)) | (ie_compare_ie_bt==1'b0)) // BT check enabled by ie_compare_ie_bt
 ;

assign i_same_addr_rmw = i_same_addr_rd & r_entry[ENTRY_RMW];

                 



// latency counter logic
// If the incoming value is 0, then keep it as it is
// If not, decrement by 1 while loading to the register
wire [RD_LATENCY_BITS-1:0] init_rd_latency_value;
assign init_rd_latency_value =  (ih_te_rd_latency == {RD_LATENCY_BITS{1'b0}}) ?
                                               {RD_LATENCY_BITS{1'b0}} : (ih_te_rd_latency - {{(RD_LATENCY_BITS-1){1'b0}},1'b1});

wire upd_rd_latency_value_ie;
assign upd_rd_latency_value_ie = (r_entry_rd_latency > init_rd_latency_value);

//---------------------------
// Rd Latency timer decrement logic
//   - Load the incoming rd_latency value from IH
//   - Decrement every cycle by 1 until the value is 0
//   - Generate i_entry_vpr_timed_out when the entry times-out
//---------------------------
always @(*)
  begin
     r_entry_rd_latency_ns  = r_entry_rd_latency;
     // load the incoming value of valid cmd and VPR
     if(i_load && (ih_te_hi_pri == CMD_PRI_VPR))
        r_entry_rd_latency_ns  = init_rd_latency_value;
     // reset the value to  all 1's when entry not valid
     else if(i_entry_del)
        r_entry_rd_latency_ns = {RD_LATENCY_BITS{1'b1}};
     // reset the value to all 0's if the entry has been promoted to expired-VPR even though this timer has not counted down to 0
     else if((i_entry_loaded==1'b1) && (r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB] == CMD_PRI_XVPR))
        r_entry_rd_latency_ns  = {RD_LATENCY_BITS{1'b0}};
     // If this is RE_B and RD_E is incoming and BT is match and incoming latency_value is less than current value
     else if(upd_to_vpr_due_ie & upd_rd_latency_value_ie) 
        r_entry_rd_latency_ns  = init_rd_latency_value;
     // decrement by 1, when entry is valid VPR and count not 0
     else if((i_entry_loaded==1'b1) && (r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB] == CMD_PRI_VPR) && (~r_entry_rd_latency_zero))
        r_entry_rd_latency_ns  = r_entry_rd_latency - {{(RD_LATENCY_BITS-1){1'b0}},1'b1};
  end

// Output assignment indicating that this entry has timed-out
// Goes high when all bits in r_entry_rd_latency = 0
assign i_entry_vpr_timed_out = (r_entry_rd_latency_zero | visible_window_reached)
                               & i_entry_valid
;


// goes high when the entry is valid, the priority is exp-VPR and any VPR entry has timed-out and promote_vpr_to_expired_vpr is high
assign i_entry_vpr_valid     = i_entry_loaded & (vpr_to_exp_vpr || (i_entry_out_pri == CMD_PRI_XVPR)) ;


//---------------------------
// change VPR to expired-VPR when any VPR entry has timed-out
//---------------------------
assign vpr_to_exp_vpr      = (valid_entry_is_vpr & i_entry_vpr_timed_out) | visible_window_reached ;


//---------------------------
// Generating the page hit combinationally 
//   - page_hit status is updated on every activate and precharge command to the bank in this entry
//   - When the entry is loaded into the CAM, the page_hit input from BE is used to set this signal
//   - Note: the flopped version of load, act and pre are used in this logic in order to avoid long combinational path from Bypass and gs_next_xact modules
//---------------------------
assign i_entry_vpr_page_hit = page_open_next;

//---------------------------
// flops for the above logic and
//signals indicating that this entry has stored a valid HPR, VPR or LPR command
//---------------------------
always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
     r_entry_rd_latency <= {RD_LATENCY_BITS{1'b1}}; // reset to all 1's as all 0's is the timeout condition
     r_entry_rd_latency_zero <= 1'b0;
     valid_entry_is_vpr <= 1'b0;
     i_entry_vpr_valid_d <= 1'b0;
  end
  else begin
    if(i_load || i_entry_loaded) begin
      r_entry_rd_latency <= r_entry_rd_latency_ns;
      r_entry_rd_latency_zero <= ~(|r_entry_rd_latency_ns);
    end
    if(i_load && (ih_te_hi_pri == CMD_PRI_VPR))
      valid_entry_is_vpr <= 1'b1;
    else if(i_entry_del && ((i_entry_out_pri == CMD_PRI_VPR) || (i_entry_out_pri == CMD_PRI_XVPR)))
      valid_entry_is_vpr <= 1'b0;
    else if (upd_to_vpr_due_ie & ~i_entry_del) 
       valid_entry_is_vpr <= 1'b1;

   if (i_entry_del) begin
     i_entry_vpr_valid_d <= 1'b0;
   end
   else if(i_entry_loaded) begin
     i_entry_vpr_valid_d <= (vpr_to_exp_vpr || (i_entry_out_pri == CMD_PRI_XVPR))
                            & (i_entry_valid 
                         | (i_entry_loaded & i_entry_ie_mask_clr & ts_op_is_rd) // This entry is valid in next cycle.
                             );
   end
  end

end


// i_entry_rd_n/rd_e/re_b  
always @(posedge co_te_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    i_entry_ie_rd_n  <= 1'b0;
    i_entry_ie_rd_e  <= 1'b0;
    i_entry_ie_re_b  <= 1'b0;
  end
  else if(ddrc_cg_en)
  begin
    if (i_load) begin
      i_entry_ie_rd_n  <= (ih_te_ie_rd_type == `IE_RD_TYPE_RD_N);
      i_entry_ie_rd_e  <= (ih_te_ie_rd_type == `IE_RD_TYPE_RD_E);
      i_entry_ie_re_b  <= (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B);
    end
    else if (i_entry_del) begin
      i_entry_ie_rd_n  <= 1'b0;
      i_entry_ie_rd_e  <= 1'b0;
      i_entry_ie_re_b  <= 1'b0;
    end
  end

//------------------
// page hit limiter
//------------------
always @(posedge co_te_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    i_entry_critical_early <= 1'b0;
  end
  else begin
    if (i_load & page_hit_limit_incoming) begin
      i_entry_critical_early <= 1'b1;
    end
    else if (i_entry_del) begin        
      i_entry_critical_early <= 1'b0;
    end
    else if(i_entry_loaded) begin
      i_entry_critical_early <= (set_page_close_for_pre)? 1'b0 : (r_same_bank_rdwr_op & page_hit_limit_reached)? 1'b1 : i_entry_critical_early;
    end
  end
end
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
    else if (i_entry_loaded & i_vlimit_decr & visible_window_counter != 9'h00) begin
      visible_window_counter <= visible_window_counter - 9'h01;
      if (visible_window_counter==9'h01) begin
        visible_window_reached <= 1'b1;
      end
    end
  end
end

   
assign te_rd_vlimit_reached = visible_window_reached;


//-------------------

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

// Check that command type signals is one hot or zero
a_ie_rdcam_cmd_type_check://--------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    ($onehot0({i_entry_ie_rd_n,i_entry_ie_rd_e,i_entry_ie_re_b})))
    else $error("[%t][%m] ERROR: i_entry_ie_rd_n/i_entry_ie_rd_e/i_entry_ie_re_b must be one hot or zero", $time);


camEntryOverwritten: //---------------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(i_entry_loaded & i_load)) )
    else $error("[%t][%m] ERROR: Read CAM entry gets overwritten.", $time);

invalidTransactionScheduled: //-------------------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (!(~i_entry_loaded & i_entry_del)) )
    else $error("[%t][%m] ERROR: Invalid Transaction Scheduled.", $time);


reg rd_cam_overwr;
reg rd_cam_dup;

initial
begin
  rd_cam_overwr = 1'b0;
  rd_cam_dup    = 1'b0;
end

// disable coverage collection as this is a check in SVA only        
// VCS coverage off 

always @(posedge co_te_clk)
begin
  if (r_entry [0] && i_load)
  begin
    $display ("%m: at %t ERROR: CAM entry gets overwritten.", $time);
    rd_cam_overwr = 1'b1;
  end
  if (~r_entry [0] && i_entry_del)
  begin
    $display ("%m: at %t ERROR: CAM entry gets duplicated transaction.", $time);
    rd_cam_dup = 1'b1;
  end
end

// VCS coverage on


//----------------------
// Cover Points and assertions related to VPR logic
//----------------------

  // When there are expired-VPR commands, the valid from that entry should only be sent through the VPR selection n/w and
  // not through the LPR/HPR network.
//  assert_exp_vpr_only_thru_vpr_nw:
//    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
//    (!(i_entry_valid && (i_entry_out_pri == CMD_PRI_XVPR) && i_bank_hit)))
//    else $error("[%t][%m] ERROR: Valid sent through LPR/HPR selection network, when the entry is in expired VPR state.", $time);

  Check_r_entry_rd_latency_zero: //----------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (r_entry_rd_latency_zero == (r_entry_rd_latency==0)))
    else $error("[%t][%m] ERROR: r_entry_rd_latency_zero is not matched to r_entry_rd_latency.", $time);

Check_i_entry_vpr_timed_out: //------------------------------------
    assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
    (i_entry_vpr_timed_out |-> i_entry_valid))
    else $error("[%t][%m] ERROR: i_entry_vpr_timed_out is 1 but i_entry_valid is 0.", $time);

  // Load CAM and Activate to any bank/row happening in the same cycle
  cp_rd_cam_load_w_activate_any :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_load && r_ts_op_is_activate);

  // Load CAM and Precharge to any bank/row happening in the same cycle
  cp_rd_cam_load_w_pre_any :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_load && (r_te_rdwr_autopre | r_ts_op_is_precharge));

  // When CAM entry is valid, an ACT happens to the same bank / diff page as this entry
  cp_rd_cam_entry_valid_act_w_same_bank_diff_row :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && r_ts_op_is_activate && r_ts_bsm_num4act && ~r_page_hit_act));

  // When CAM entry is valid, an ACT happens to the same bank / same page as this entry
  cp_rd_cam_entry_valid_act_w_same_bank_same_row :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && r_ts_op_is_activate && r_ts_bsm_num4act && r_page_hit_act));

  // When CAM entry is valid, a PRE happens to diff bank as this entry
  cp_rd_cam_entry_valid_pre_w_diff_bank :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && ((r_te_rdwr_autopre && ~r_ts_bsm_num4rdwr) || (r_ts_op_is_precharge & ~r_same_pre_bank))));

  // When CAM entry is valid, a PRE happens to the same bank as this entry
  cp_rd_cam_entry_valid_pre_w_same_bank :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_valid && ((r_te_rdwr_autopre && r_ts_bsm_num4rdwr) || (r_ts_op_is_precharge & r_same_pre_bank))));

  // Check that the entry goes to expired VPR at some point
  cp_rd_cam_vpr_to_exp_vpr :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) (i_entry_out_pri == CMD_PRI_XVPR));

  // Check that the entry load happens with latency at 0
  cp_rd_cam_entry_load_w_latency_0 :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_load && (ih_te_rd_latency == {RD_LATENCY_BITS{1'b0}}));

  // Check that the entry delete happens with latency at 0
  cp_rd_cam_entry_delete_w_latency_0 :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_entry_del && (r_entry_rd_latency == {RD_LATENCY_BITS{1'b0}}));

  // Check that the entry delete happens with latency at 1
  cp_rd_cam_entry_delete_w_latency_1 :
  cover property (@(posedge co_te_clk) disable iff(!core_ddrc_rstn) i_entry_del && (r_entry_rd_latency == {{(RD_LATENCY_BITS-1){1'b0}},1'b1}));


//---------
// Monitor code for the VPR and expired-VPR entries in the CAM  - Keeps count on how many cycles the entry stays in CAM
//
// Counter keeps a count of the number of clocks VPR and expired-VPR commands stays in the CAM. 
// When an entry is deleted, the final number saved in a register. When a new command is loaded in the CAM entry, 
// the counting is done again. When this entry is removed, the final count of the new value is compared with the 
// value of the previous command, and the larger of the two values is preserved. This is continued until the 
// end of the test. When the test ends, each CAM entry that had a VPR and/or expired-VPR command, will have a 
// number that gives the maximum number of clocks these command spent in that entry in VPR or expired-VPR status.
//---------
reg [9:0] num_clks_spent_as_exp_vpr;
reg [9:0] max_num_clks_spent_as_exp_vpr;

reg [15:0] num_clks_spent_as_vpr_or_expvpr;
reg [15:0] max_num_clks_spent_as_vpr_or_expvpr;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
    num_clks_spent_as_exp_vpr     <= 10'h0;
    max_num_clks_spent_as_exp_vpr <= 10'h0;
    num_clks_spent_as_vpr_or_expvpr <= 16'h0;
    max_num_clks_spent_as_vpr_or_expvpr <= 16'h0;
  end
  else begin

    if(i_entry_del)
       num_clks_spent_as_exp_vpr <= 10'h0;
    else if(i_entry_valid & (i_entry_out_pri == CMD_PRI_XVPR))
       num_clks_spent_as_exp_vpr <= num_clks_spent_as_exp_vpr + 1'b1;

    if(i_entry_del)
       max_num_clks_spent_as_exp_vpr <= (num_clks_spent_as_exp_vpr >= max_num_clks_spent_as_exp_vpr) ? num_clks_spent_as_exp_vpr : max_num_clks_spent_as_exp_vpr;



    if(i_entry_del)
       num_clks_spent_as_vpr_or_expvpr <= 16'h0;
    else if(i_entry_valid & ((i_entry_out_pri == CMD_PRI_VPR) || (i_entry_out_pri == CMD_PRI_XVPR)))
       num_clks_spent_as_vpr_or_expvpr <= num_clks_spent_as_vpr_or_expvpr + 1'b1;

    if(i_entry_del)
       max_num_clks_spent_as_vpr_or_expvpr <= (num_clks_spent_as_vpr_or_expvpr >= max_num_clks_spent_as_vpr_or_expvpr) ? 
                                           num_clks_spent_as_vpr_or_expvpr : max_num_clks_spent_as_vpr_or_expvpr;

  end
end




covergroup cg_rd_entry_ie_cmd_type @(posedge co_te_clk);

  // Observe all Inline ECC command type are stored
  cp_ie_existing_cmd_type: coverpoint (i_entry_out_ie_rd_type) iff(core_ddrc_rstn & i_entry_loaded) {
            bins RD_N   = {`IE_RD_TYPE_RD_N  };
            bins RD_E   = {`IE_RD_TYPE_RD_E  };
            bins RE_B   = {`IE_RD_TYPE_RE_B  };
    illegal_bins OTHER  = default;
  }

  cp_ie_rd_entry_collision: coverpoint({i_entry_out_ie_rd_type,ih_te_ie_rd_type,ih_te_ie_wr_type}) iff (core_ddrc_rstn & i_same_addr_rd) {
   wildcard         bins RD_N_vs_RD_N   = {{`IE_RD_TYPE_RD_N ,`IE_RD_TYPE_RD_N  ,2'b??             }};
   wildcard         bins RD_N_vs_RD_E   = {{`IE_RD_TYPE_RD_N ,`IE_RD_TYPE_RD_E  ,2'b??             }};
   wildcard         bins RD_N_vs_RE_B   = {{`IE_RD_TYPE_RD_N ,`IE_RD_TYPE_RE_B  ,2'b??             }};
   wildcard         bins RD_N_vs_WD_N   = {{`IE_RD_TYPE_RD_N ,2'b??             ,`IE_WR_TYPE_WD_N  }};
   wildcard         bins RD_N_vs_WD_E   = {{`IE_RD_TYPE_RD_N ,2'b??             ,`IE_WR_TYPE_WD_E  }};
   wildcard illegal_bins RD_N_vs_WE_BW  = {{`IE_RD_TYPE_RD_N ,2'b??             ,`IE_WR_TYPE_WE_BW }};
   wildcard         bins RD_E_vs_RD_N   = {{`IE_RD_TYPE_RD_E ,`IE_RD_TYPE_RD_N  ,2'b??             }};
   wildcard         bins RD_E_vs_RD_E   = {{`IE_RD_TYPE_RD_E ,`IE_RD_TYPE_RD_E  ,2'b??             }};
   wildcard         bins RD_E_vs_RE_B   = {{`IE_RD_TYPE_RD_E ,`IE_RD_TYPE_RE_B  ,2'b??             }};
   wildcard         bins RD_E_vs_WD_N   = {{`IE_RD_TYPE_RD_E ,2'b??             ,`IE_WR_TYPE_WD_N  }};
   wildcard         bins RD_E_vs_WD_E   = {{`IE_RD_TYPE_RD_E ,2'b??             ,`IE_WR_TYPE_WD_E  }};
   wildcard illegal_bins RD_E_vs_WE_BW  = {{`IE_RD_TYPE_RD_E ,2'b??             ,`IE_WR_TYPE_WE_BW }};
   wildcard         bins RE_B_vs_RD_N   = {{`IE_RD_TYPE_RE_B ,`IE_RD_TYPE_RD_N  ,2'b??             }};
   wildcard         bins RE_B_vs_RD_E   = {{`IE_RD_TYPE_RE_B ,`IE_RD_TYPE_RD_E  ,2'b??             }};
   wildcard         bins RE_B_vs_RE_B   = {{`IE_RD_TYPE_RE_B ,`IE_RD_TYPE_RE_B  ,2'b??             }};
   wildcard         bins RE_B_vs_WD_N   = {{`IE_RD_TYPE_RE_B ,2'b??             ,`IE_WR_TYPE_WD_N  }};
   wildcard         bins RE_B_vs_WD_E   = {{`IE_RD_TYPE_RE_B ,2'b??             ,`IE_WR_TYPE_WD_E  }};
   wildcard illegal_bins RE_B_vs_WE_BW  = {{`IE_RD_TYPE_RE_B ,2'b??             ,`IE_WR_TYPE_WE_BW }};
   }

  // Observe all Priority are stored
  cp_ie_pri : coverpoint (i_entry_out_pri) iff (core_ddrc_rstn & i_entry_loaded) {
            bins LPR    = {CMD_PRI_LPR}; 
            bins HPR    = {CMD_PRI_HPR}; 
            bins VPR    = {CMD_PRI_VPR}; 
            bins XVPR   = {CMD_PRI_XVPR};
 
  }


endgroup: cg_rd_entry_ie_cmd_type

// Coverage group instantiation
cg_rd_entry_ie_cmd_type cg_rd_entry_ie_cmd_type_inst = new;

// === Will move to te_assertion because WR CAM information is now needed ===
// // Check that no VPR is issued within HPR block
// IE_VPR_in_HPR_block :
//     assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
//             !(
//               (load_cam_any & i_entry_loaded) & 
//               (ih_te_hi_pri == CMD_PRI_VPR)   & 
//               (r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB]==CMD_PRI_HPR) & 
//               (ih_te_ie_rd_type==`IE_RD_TYPE_RD_E && i_entry_out_ie_rd_type==`IE_RD_TYPE_RE_B && i_entry_out_ie_bt == ih_te_ie_bt)
//              ))
//     else $error("[%t][%m] ERROR: [InlineECC] VPR command are received within HPR read block.", $time);
// 
// // Check that no HPR is issued within LPR/VPR block
// IE_HPR_in_VPR_block :
//     assert property ( @ (posedge co_te_clk) disable iff (~core_ddrc_rstn)
//             !(
//               (load_cam_any & i_entry_loaded) & 
//               (ih_te_hi_pri == CMD_PRI_HPR)   & 
//               (r_entry[ENTRY_HI_PRI_MSB:ENTRY_HI_PRI_LSB]!=CMD_PRI_HPR) & 
//               (ih_te_ie_rd_type==`IE_RD_TYPE_RD_E && i_entry_out_ie_rd_type==`IE_RD_TYPE_RE_B && i_entry_out_ie_bt == ih_te_ie_bt)
//              ))
//     else $error("[%t][%m] ERROR: [InlineECC] HPR command are received within LPR/VPR read block.", $time);


  // Check that ECCAP must be 0 for overhead ECC command
  property p_eccap_rdcam_must_be_zero_for_overhead_command;
    @ (posedge co_te_clk) disable iff (!core_ddrc_rstn)
    (i_entry_loaded && (i_entry_out_ie_rd_type==`IE_RD_TYPE_RE_B)) |->
        (i_entry_out_eccap == 1'b0);
  endproperty

  a_eccap_rdcam_must_be_zero_for_overhead_command : assert property (p_eccap_rdcam_must_be_zero_for_overhead_command)
    else $error("%0t ERROR: ECC AP field must be 0 for overhead ECC command.", $time);





`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule // te_rd_entry
