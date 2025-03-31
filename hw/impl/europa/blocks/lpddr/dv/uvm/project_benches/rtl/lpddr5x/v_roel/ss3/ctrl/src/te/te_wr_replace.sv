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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_wr_replace.sv#5 $
// -------------------------------------------------------------------------
// Description:
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_wr_replace #(
    //-------------------------------- PARAMETERS ----------------------------------
     parameter  WR_CAM_ADDR_BITS    = 0
    ,parameter  WR_ECC_CAM_ADDR_BITS = 0
    ,parameter  WR_CAM_ADDR_BITS_IE = 0
    ,parameter  WR_CAM_ENTRIES      = 0 
    ,parameter  WR_CAM_ENTRIES_IE   = 0
    ,parameter  WR_ECC_CAM_ENTRIES  = 0 
    ,parameter  PAGE_BITS           = `MEMC_PAGE_BITS 
    ,parameter  AUTOPRE_BITS        = 1 
    ,parameter   MWR_BITS            = 1 
    ,parameter   PW_WORD_CNT_WD_MAX  = 2
    ,parameter   PARTIAL_WR_BITS_LOG2  = 1 
    ,parameter  IE_TAG_BITS         = 0 // Overridden
    ,parameter  WRSEL_TAG_BITS      = PAGE_BITS
                                    + AUTOPRE_BITS
                                    + MWR_BITS
                                    + PW_WORD_CNT_WD_MAX
                                    + PW_WORD_CNT_WD_MAX
                                    + PARTIAL_WR_BITS_LOG2
                                    + IE_TAG_BITS
    ,parameter  WRECCSEL_TAG_BITS   = WRSEL_TAG_BITS + 2 // Inluding BTT/RE
    )
    (    
    //--------------------------- INPUTS AND OUTPUTS -------------------------------
     input                                             core_ddrc_rstn 
    ,input                                             co_te_clk 
    ,input                                             reg_ddrc_dis_opt_wrecc_collision_flush
    ,input   [WR_CAM_ADDR_BITS-1:0]                    ih_te_wr_prefer 
    ,input   [WR_CAM_ENTRIES_IE -1:0]                  te_wr_entry_valid           // valid read entry matching bank from CAM search
    ,input                                             ddrc_cg_en
    ,input   [WR_CAM_ENTRIES_IE -1:0]                  te_wr_page_hit              // read entries matching bank and page from CAM search
    ,input                                             te_wr_flush_started         // indicates a collision causing read entries to be flushed
    ,input   [WR_CAM_ADDR_BITS_IE-1:0]                 te_wr_col_entry             // entry # to be flushed from read CAM
    ,input   [WR_CAM_ENTRIES_IE-1:0]                   te_wr_col_entries
    ,output  [WR_CAM_ADDR_BITS_IE-1:0]                 te_wr_prefer                // low priority read prefer location
    ,output  [WR_CAM_ADDR_BITS_IE-1:0]                 te_sel_wr_entry             // entry # of selected CAM entry for replacement
    ,output  [PAGE_BITS-1:0]                           te_sel_wr_page              // Row address of selected CAM entry
    ,output  [AUTOPRE_BITS-1:0]                        te_sel_wr_cmd_autopre       // cmd_autopre of selected CAM entry
    ,output  [MWR_BITS-1:0]                            te_sel_mwr                  // masked write of selected CAM entry
    ,input   [WR_CAM_ENTRIES_IE*MWR_BITS-1:0]          te_mwr_table                // masked write of all CAM entries
    ,output  [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_pw_num_cols_m1       // partial write of selected CAM entry
    ,input   [WR_CAM_ENTRIES_IE*PW_WORD_CNT_WD_MAX-1:0]te_pw_num_cols_m1_table     // partial write of all CAM entries
    ,output  [PARTIAL_WR_BITS_LOG2-1:0]                te_sel_wr_mr_ram_raddr_lsb
    ,output  [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_wr_mr_pw_num_beats_m1
    ,output                                            te_sel_wr_valid             // selected read entry for replacement
    ,input   [WR_CAM_ENTRIES_IE*PAGE_BITS-1:0]         te_wr_page_table            // page addresses of all CAM entries
    ,input   [WR_CAM_ENTRIES_IE*AUTOPRE_BITS-1:0]      te_wr_cmd_autopre_table     // cmd_autopre of all CAM entries
    ,input                                             te_any_vpw_timed_out        // Any VPW entry has timed-out
    ,input   [WR_CAM_ENTRIES -1:0]                     te_vpw_valid                // all entries that have expired-VPW commands in them
    ,input   [WR_CAM_ENTRIES -1:0]                     te_vpw_valid_for_flush      // To check there are exVPW within candidates for collision
    ,input   [WR_CAM_ENTRIES -1:0]                     te_vpw_valid_filtred        // all entries that have expired-VPW commands in them except entries in NTT
    ,input   [WR_CAM_ENTRIES_IE -1:0]                  te_vpw_page_hit             // page hit status of all the entries
    ,output  [WR_CAM_ADDR_BITS_IE-1:0]                 te_sel_vpw_entry            // entry # of selected VPW CAM entry for replacement
    ,output  [PAGE_BITS-1:0]                           te_sel_vpw_page 
    ,output  [AUTOPRE_BITS-1:0]                        te_sel_vpw_cmd_autopre 
    ,output                                            te_sel_vpw_valid            // valid for the selected VPW entry
    ,output  [MWR_BITS-1:0]                            te_sel_vpw_mwr 
    ,output  [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_vpw_pw_num_cols_m1 
    ,output [PARTIAL_WR_BITS_LOG2-1:0]                 te_sel_vpw_mr_ram_raddr_lsb
    ,output [PW_WORD_CNT_WD_MAX-1:0]                   te_sel_vpw_pw_num_beats_m1 

    ,output  [IE_TAG_BITS-1:0]                         te_sel_vpw_ie_tag
    ,output  [WR_CAM_ADDR_BITS_IE-1:0]                 te_sel_wrecc_btt_entry            // entry # of selected WRECC  CAM entry for replacement
    ,output  [PAGE_BITS-1:0]                           te_sel_wrecc_btt_page 
    ,output  [AUTOPRE_BITS-1:0]                        te_sel_wrecc_btt_cmd_autopre 
    ,output                                            te_sel_wrecc_btt_valid            // valid for the selected wrecc btt entry
    ,output  [MWR_BITS-1:0]                            te_sel_wrecc_btt_mwr 
    ,output  [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_wrecc_btt_pw_num_cols_m1 
    ,output  [PARTIAL_WR_BITS_LOG2-1:0]                te_sel_wrecc_btt_mr_ram_raddr_lsb
    ,output  [PW_WORD_CNT_WD_MAX-1:0]                  te_sel_wrecc_btt_pw_num_beats_m1
    ,output  [IE_TAG_BITS-1:0]                         te_sel_wrecc_btt_ie_tag
    ,output                                            te_sel_wrecc_btt_ie_btt
    ,output                                            te_sel_wrecc_btt_ie_re

    ,input   [WR_ECC_CAM_ENTRIES-1:0]                  te_wrecc_btt_valid_filtred   // all WRECC entries that has BTT1 except entries in NTT.
    ,input                                             te_any_wrecc_btt_valid
    ,input   [WR_CAM_ENTRIES_IE*PARTIAL_WR_BITS_LOG2-1:0] te_wr_mr_ram_raddr_lsb_first_table
    ,input   [WR_CAM_ENTRIES_IE*PW_WORD_CNT_WD_MAX-1:0]   te_wr_mr_pw_num_beats_m1_table
    ,input   [WR_CAM_ENTRIES-1:0]                    hmx_oldest_oh
    ,output  [WR_CAM_ENTRIES-1:0]                    hmx_mask
    ,input   [WR_CAM_ADDR_BITS-1:0]                  te_vpw_prefer
    ,output  [WR_CAM_ENTRIES-1:0]                    hmx_mask_vpw
    ,input   [WR_CAM_ENTRIES-1:0]                    hmx_oldest_oh_vpw
    ,input                                           te_entry_critical_currnt_bsm
    ,input   [WR_CAM_ENTRIES_IE*IE_TAG_BITS-1:0]     te_wr_ie_tag_table
    ,output  [IE_TAG_BITS-1:0]                       te_sel_wr_ie_tag
    ,input   [WR_CAM_ENTRIES_IE-1:0]                 te_wr_entry_ie_btt
    ,input   [WR_CAM_ENTRIES_IE-1:0]                 te_wr_entry_ie_re
    ,input   [WR_ECC_CAM_ADDR_BITS-1:0]              ih_te_wrecc_prefer 
    ,output                                          te_sel_ie_btt
    ,output                                          te_sel_ie_re
    ,output  [WR_CAM_ADDR_BITS_IE-1:0]               te_wrecc_prefer 
    ,output  [WR_ECC_CAM_ENTRIES-1:0]                hmx_mask_wrecc
    ,input   [WR_ECC_CAM_ENTRIES-1:0]                hmx_oldest_oh_wrecc
    ,output  [WR_ECC_CAM_ENTRIES-1:0]                hmx_wrecc_btt_mask
    ,input   [WR_ECC_CAM_ENTRIES-1:0]                hmx_wrecc_btt_oldest_oh
    ,input  [WR_ECC_CAM_ADDR_BITS-1:0]               te_wrecc_btt_prefer

);

//----------------------------- WIRES AND REGS ---------------------------------

reg     [WR_CAM_ENTRIES_IE-1:0]     r_wr_entry_valid;               // flopped version of all entries
wire    [WR_CAM_ENTRIES-1:0]        te_wr_entry_participate;
wire    [WR_CAM_ADDR_BITS-1:0]      i_sel_wr_entry;                 // entry # from selection network for CAM replacement
                                                                    //  (this may be over-ridden for collision cases)
wire                                i_sel_wr_valid;              // valid for the selected 
reg                                 i_sel_wr_valid_r;            // valid for the selected 
  `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
wire                                i_sel_wr_valid_sva;
    `endif
  `endif
wire    [WRSEL_TAG_BITS-1:0]        i_sel_wr_tag;                   // Tag of selected CAM entry
wire    [PAGE_BITS-1:0]             i_sel_wr_page;
wire    [AUTOPRE_BITS-1:0]          i_sel_wr_cmd_autopre;
wire    [MWR_BITS-1:0]              i_sel_wr_mwr;
wire    [PW_WORD_CNT_WD_MAX-1:0]    i_sel_wr_pw_num_cols_m1;
wire    [IE_TAG_BITS-1:0]           i_sel_wr_ie_tag;
wire    [PARTIAL_WR_BITS_LOG2-1:0]  i_sel_wr_mr_raddr_lsb_first;
wire    [PW_WORD_CNT_WD_MAX-1:0]    i_sel_wr_pw_num_beats_m1;

// For inline ECC

wire                                i_sel_wrecc;                    // Select one from WR ECC selnet 

wire    [WR_ECC_CAM_ENTRIES-1:0]    te_wrecc_entry_participate;
wire                                i_sel_wrecc_valid;              // valid for the selected 
reg                                 i_sel_wrecc_valid_r;            // valid for the selected 
  `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
wire                                i_sel_wrecc_valid_sva;
    `endif
  `endif
wire    [WR_ECC_CAM_ADDR_BITS-1:0]  i_sel_wrecc_entry;              // entry # from selection network for CAM replacement
                                                                    //  (this may be over-ridden for collision cases)
wire    [WRECCSEL_TAG_BITS-1:0]     i_sel_wrecc_tag;                // Tag of selected CAM entry (including BTT/RE)
wire    [PAGE_BITS-1:0]             i_sel_wrecc_page;
wire    [AUTOPRE_BITS-1:0]          i_sel_wrecc_cmd_autopre;
wire    [MWR_BITS-1:0]              i_sel_wrecc_mwr;
wire    [PW_WORD_CNT_WD_MAX-1:0]    i_sel_wrecc_pw_num_cols_m1;
wire    [IE_TAG_BITS-1:0]           i_sel_wrecc_ie_tag;
wire                                i_sel_wrecc_ie_btt;
wire                                i_sel_wrecc_ie_re;
wire    [PARTIAL_WR_BITS_LOG2-1:0]  i_sel_wrecc_mr_raddr_lsb_first;
wire    [PW_WORD_CNT_WD_MAX-1:0]    i_sel_wrecc_pw_num_beats_m1;



wire                            i_sel_colliding;
wire [WR_CAM_ADDR_BITS_IE-1:0]  i_te_wr_col_entry;
wire [PAGE_BITS-1:0]            i_wr_col_page;
wire [AUTOPRE_BITS-1:0]         i_wr_col_cmd_autopre;
wire [MWR_BITS-1:0]             i_wr_col_mwr;
wire [PARTIAL_WR_BITS_LOG2-1:0] i_wr_mr_raddr_lsb_first;
wire [PW_WORD_CNT_WD_MAX-1:0]   i_wr_mr_pw_num_beats_m1;
wire [PW_WORD_CNT_WD_MAX-1:0]   i_wr_col_pw_num_cols_m1;




//---------------------------------- LOGIC -------------------------------------


   reg     r_te_any_vpw_timed_out;

   reg     r_te_any_wrecc_btt_valid;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin 
   if (~core_ddrc_rstn) begin 
      r_wr_entry_valid <= {WR_CAM_ENTRIES_IE{1'b0}};
      r_te_any_vpw_timed_out <= 1'b0;
      r_te_any_wrecc_btt_valid <= 1'b0;
   end
   else if(ddrc_cg_en) begin 
//spyglass disable_block FlopEConst
//SMD: Enable pin EN on Flop (master RTL_FDCE) is always enabled
//SJ: ddrc_cg_en is fixed to 1 (always disable clock gating) because this module is reused in the block not supporting clock gating
      r_wr_entry_valid <= te_wr_entry_valid;
      r_te_any_vpw_timed_out <= |(te_wr_entry_valid[WR_CAM_ENTRIES-1:0] & te_vpw_valid_for_flush[WR_CAM_ENTRIES-1:0]);
                                // This means VPW per bank
                                // As WR ECC never becomes exVPW, WR_CAM_ENTRIES is enough
      r_te_any_wrecc_btt_valid <= |(te_wr_entry_ie_btt[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES] & te_wr_entry_valid[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES]);
//spyglass enable_block FlopEConst
   end  
end
localparam NUM_CAM_ENTRIES_POW2 = 2**(WR_CAM_ADDR_BITS_IE);  
wire [NUM_CAM_ENTRIES_POW2-1:0] r_wr_entry_valid_tmp;
generate
  if(NUM_CAM_ENTRIES_POW2 == WR_CAM_ENTRIES_IE) begin:wr_entry_valid_pow2
assign r_wr_entry_valid_tmp = r_wr_entry_valid;
  end else begin:wr_entry_valid_pow2
assign r_wr_entry_valid_tmp = {{(NUM_CAM_ENTRIES_POW2-WR_CAM_ENTRIES_IE){1'b0}},r_wr_entry_valid};
  end
endgenerate
// override selection network choice with colliding entry if colliding entry is valid replacement
wire sel_colliding = te_wr_flush_started & r_wr_entry_valid_tmp[te_wr_col_entry] & ~r_te_any_vpw_timed_out
   //reg_ddrc_dis_opt_wrecc_collision_flush is a chicken bit to reverse priority between colliding entry and wrecc_btt when there are no expVPW
   // 1: wrecc_btt is higher priority than colliding
   // 0: colliding is higher priority than wrecc_btt
   // refer to bug6437 for the detail.
                     & (~r_te_any_wrecc_btt_valid | ~reg_ddrc_dis_opt_wrecc_collision_flush)
                     ;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(1024 * 8)' found in module 'te_wr_replace'
//SJ: This coding style is acceptable and there is no plan to change it. - refers to `UMCTL_LOG2

wire [PAGE_BITS-1:0] wr_col_page;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (PAGE_BITS)
  )
  rd_col_page_mux (
    .in_port   (te_wr_page_table),
    .sel       (te_wr_col_entry),
    .out_port  (wr_col_page)
  );   
   
wire [AUTOPRE_BITS-1:0] wr_col_cmd_autopre;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (AUTOPRE_BITS)
  )
  rd_col_cmd_autopre_mux (
    .in_port   (te_wr_cmd_autopre_table),
    .sel       (te_wr_col_entry),
    .out_port  (wr_col_cmd_autopre)
  );   

wire [MWR_BITS-1:0] wr_col_mwr;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (MWR_BITS)
  )
  rd_col_mwr_mux (
    .in_port    (te_mwr_table),
    .sel        (te_wr_col_entry),
    .out_port   (wr_col_mwr)
  );
wire [PARTIAL_WR_BITS_LOG2-1:0] wr_mr_raddr_lsb_first;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (PARTIAL_WR_BITS_LOG2)
  )
  wr_col_pi_wr_mr_raddr_mux (
    .in_port    (te_wr_mr_ram_raddr_lsb_first_table),
    .sel        (te_wr_col_entry),
    .out_port   (wr_mr_raddr_lsb_first)
  );

wire [PW_WORD_CNT_WD_MAX-1:0] wr_mr_pw_num_beats_m1;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (PW_WORD_CNT_WD_MAX)
  )
  wr_col_pi_wr_mr_pw_num_beats_mux (
    .in_port    (te_wr_mr_pw_num_beats_m1_table),
    .sel        (te_wr_col_entry),
    .out_port   (wr_mr_pw_num_beats_m1)
  );


wire [PW_WORD_CNT_WD_MAX-1:0] wr_col_pw_num_cols_m1;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (PW_WORD_CNT_WD_MAX)
  )
  rd_col_pw_num_cols_m1_mux (
    .in_port    (te_pw_num_cols_m1_table),
    .sel        (te_wr_col_entry),
    .out_port   (wr_col_pw_num_cols_m1)
  );

wire [IE_TAG_BITS-1:0] wr_col_ie_tag;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (IE_TAG_BITS)
  )
  wr_col_ie_tag_mux (
    .in_port    (te_wr_ie_tag_table),
    .sel        (te_wr_col_entry),
    .out_port   (wr_col_ie_tag)
  );

wire wr_col_ie_btt;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (1)
  )
  wr_col_ie_btt_mux (
    .in_port    (te_wr_entry_ie_btt),
    .sel        (te_wr_col_entry),
    .out_port   (wr_col_ie_btt)
  );
  
wire wr_col_ie_re;
  te_mux
   #(
    .ADDRW      (`UMCTL_LOG2 (WR_CAM_ENTRIES_IE)),
    .NUM_INPUTS (WR_CAM_ENTRIES_IE),
    .DATAW      (1)
  )
  wr_col_ie_re_mux (
    .in_port    (te_wr_entry_ie_re),
    .sel        (te_wr_col_entry),
    .out_port   (wr_col_ie_re)
  );

//spyglass enable_block SelfDeterminedExpr-ML



assign i_sel_colliding         = sel_colliding;
assign i_te_wr_col_entry       = te_wr_col_entry;
assign i_wr_col_page           = wr_col_page;
assign i_wr_col_cmd_autopre    = wr_col_cmd_autopre;
assign i_wr_col_mwr            = wr_col_mwr;
assign i_wr_mr_raddr_lsb_first = wr_mr_raddr_lsb_first;
assign i_wr_mr_pw_num_beats_m1 = wr_mr_pw_num_beats_m1;
assign i_wr_col_pw_num_cols_m1 = wr_col_pw_num_cols_m1;



// MSB is decided by i_sel_wrecc with non collision case
assign te_sel_wr_entry[WR_CAM_ADDR_BITS_IE-1] = sel_colliding ? te_wr_col_entry[WR_CAM_ADDR_BITS_IE-1] :
                                                                i_sel_wrecc;


assign te_sel_wr_entry[WR_CAM_ADDR_BITS-1:0]  = i_sel_colliding ? i_te_wr_col_entry[WR_CAM_ADDR_BITS-1:0] : 
                                                  i_sel_wrecc ? {1'b0,i_sel_wrecc_entry} : 
                                                                i_sel_wr_entry;

assign te_sel_wr_page        = i_sel_colliding ? i_wr_col_page :
                                 i_sel_wrecc ? i_sel_wrecc_page :
                                               i_sel_wr_page;

assign te_sel_wr_cmd_autopre = i_sel_colliding ? i_wr_col_cmd_autopre :
                                 i_sel_wrecc ? i_sel_wrecc_cmd_autopre :
                                               i_sel_wr_cmd_autopre;

assign te_sel_mwr            = i_sel_colliding ? i_wr_col_mwr : 
                                 i_sel_wrecc ? i_sel_wrecc_mwr :
                                               i_sel_wr_mwr;
assign te_sel_pw_num_cols_m1 = i_sel_colliding ? i_wr_col_pw_num_cols_m1 : 
                                 i_sel_wrecc ? i_sel_wrecc_pw_num_cols_m1 :
                                               i_sel_wr_pw_num_cols_m1;

assign te_sel_wr_mr_ram_raddr_lsb = i_sel_colliding ? i_wr_mr_raddr_lsb_first : 
                                     i_sel_wrecc ? i_sel_wrecc_mr_raddr_lsb_first : 
                                                   i_sel_wr_mr_raddr_lsb_first;

assign te_sel_wr_mr_pw_num_beats_m1 = i_sel_colliding ? i_wr_mr_pw_num_beats_m1 : 
                                       i_sel_wrecc ? i_sel_wrecc_pw_num_beats_m1: 
                                                     i_sel_wr_pw_num_beats_m1;

assign te_sel_wr_ie_tag = sel_colliding ? wr_col_ie_tag : 
                            i_sel_wrecc ? i_sel_wrecc_ie_tag :
                                          i_sel_wr_ie_tag;

assign te_sel_ie_btt = sel_colliding ? wr_col_ie_btt :
                         i_sel_wrecc ? i_sel_wrecc_ie_btt :
                                       1'b0; // btt=0 for non WE_BW.

assign te_sel_ie_re  = sel_colliding ? wr_col_ie_re :
                         i_sel_wrecc ? i_sel_wrecc_ie_re :
                                       1'b0; // re=0 for non WE_BW.

wire [WR_CAM_ADDR_BITS-1:0] i_te_vpw_prefer;
assign i_te_vpw_prefer = te_vpw_prefer; // Use oldest entry within exVPW




// for bank preference, select the colliding bank during a collision
assign te_wr_prefer[WR_CAM_ADDR_BITS_IE-1] = 
                             te_any_vpw_timed_out  ? 1'b0 : // MSB=1 indicates WR ECC CAM 
                             te_wr_flush_started   ? te_wr_col_entry[WR_CAM_ADDR_BITS_IE-1] : 1'b0; // MSB=1 indicates WR ECC CAM

assign te_wr_prefer[WR_CAM_ADDR_BITS-1:0]  = 
                             te_any_vpw_timed_out  ? i_te_vpw_prefer :
                             te_wr_flush_started   ? te_wr_col_entry[WR_CAM_ADDR_BITS-1:0] : ih_te_wr_prefer;


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(((i + 1) * PAGE_BITS) - 1)' found in module 'te_wr_replace'
//SJ: This coding style is acceptable and there is no plan to change it.

// putting the page, cmd_autopre and mwr from all the banks into a single bus
// the format is {page[bankN],cmd_autopre[bankN],mwr[bankN] ... , page[bank1],cmd_autopre[bank1],mwr[bank1],page[bank0],cmd_autopre[bank0],mwr[bank0]}
wire [WRSEL_TAG_BITS*WR_CAM_ENTRIES-1:0] wr_selnet_tags_in;
genvar i;
generate
    for (i=0; i<WR_CAM_ENTRIES; i=i+1) begin : wr_selnet_tags_in_gen
assign  wr_selnet_tags_in[((i+1)*WRSEL_TAG_BITS)-1:i*WRSEL_TAG_BITS] =
            {te_wr_page_table[((i+1)*PAGE_BITS)-1:i*PAGE_BITS]
            ,te_wr_cmd_autopre_table[((i+1)*AUTOPRE_BITS)-1:i*AUTOPRE_BITS]
            ,te_mwr_table[((i+1)*MWR_BITS)-1:i*MWR_BITS]
            ,te_pw_num_cols_m1_table[((i+1)*PW_WORD_CNT_WD_MAX)-1:i*PW_WORD_CNT_WD_MAX]
            ,te_wr_ie_tag_table[((i+1)*IE_TAG_BITS)-1:i*IE_TAG_BITS]
            ,te_wr_mr_ram_raddr_lsb_first_table[((i+1)*PARTIAL_WR_BITS_LOG2)-1:i*PARTIAL_WR_BITS_LOG2]
            ,te_wr_mr_pw_num_beats_m1_table[((i+1)*PW_WORD_CNT_WD_MAX)-1:i*PW_WORD_CNT_WD_MAX]
            };
    end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

wire [WRECCSEL_TAG_BITS*WR_ECC_CAM_ENTRIES-1:0] wrecc_selnet_tags_in;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((i + WR_CAM_ENTRIES) * PAGE_BITS)' found in module 'te_wr_replace'
//SJ: This coding style is acceptable and there is no plan to change it. 
generate
    for (i=0; i<WR_ECC_CAM_ENTRIES; i=i+1) begin : wrecc_selnet_tags_in_gen
assign  wrecc_selnet_tags_in[i*WRECCSEL_TAG_BITS+:WRECCSEL_TAG_BITS] =
            {te_wr_page_table[(i+WR_CAM_ENTRIES)*PAGE_BITS+:PAGE_BITS]
            ,te_wr_cmd_autopre_table[(i+WR_CAM_ENTRIES)*AUTOPRE_BITS+:AUTOPRE_BITS]
            ,te_mwr_table[(i+WR_CAM_ENTRIES)*MWR_BITS+:MWR_BITS]
            ,te_pw_num_cols_m1_table[(i+WR_CAM_ENTRIES)*PW_WORD_CNT_WD_MAX+:PW_WORD_CNT_WD_MAX]
            ,te_wr_mr_ram_raddr_lsb_first_table[((i+WR_CAM_ENTRIES)*PARTIAL_WR_BITS_LOG2)+:PARTIAL_WR_BITS_LOG2]
            ,te_wr_mr_pw_num_beats_m1_table[((i+WR_CAM_ENTRIES)*PW_WORD_CNT_WD_MAX)+:PW_WORD_CNT_WD_MAX]
            ,te_wr_ie_tag_table[(i+WR_CAM_ENTRIES)*IE_TAG_BITS+:IE_TAG_BITS]
            ,te_wr_entry_ie_btt[i+WR_CAM_ENTRIES]
            ,te_wr_entry_ie_re[i+WR_CAM_ENTRIES]
            };
    end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

//------------------------------- INSTANTIATIONS -------------------------------


   te_filter_vp
    #( .CAM_ENTRIES           (WR_CAM_ENTRIES) )
  WRfilter_vp (
                   .te_vp_expired         (te_vpw_valid [WR_CAM_ENTRIES -1:0]) ,
                   .te_bank_hit           (te_wr_entry_valid [WR_CAM_ENTRIES -1:0]),
                   .te_page_hit           (te_wr_page_hit [WR_CAM_ENTRIES -1:0]),
                   .te_entry_participate  (te_wr_entry_participate [WR_CAM_ENTRIES -1:0])
                  );

wire  [WR_CAM_ENTRIES-1:0]        i_hmx_oldest_oh;
assign i_hmx_oldest_oh = hmx_oldest_oh;

select_net_hmatrix
             #(
    .TAG_BITS               (WRSEL_TAG_BITS),
    .NUM_INPUTS             (WR_CAM_ENTRIES)
  )
  WRselnet (
    .tags                   (wr_selnet_tags_in),
    .vlds                   (te_wr_entry_participate [WR_CAM_ENTRIES -1:0]),
    .selected               (i_sel_wr_entry [WR_CAM_ADDR_BITS-1:0]),
  `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
    .clk                    (co_te_clk),
    .resetb                 (core_ddrc_rstn),
    .selected_vld           (i_sel_wr_valid_sva),
    `endif
  `endif
    .mask                   (hmx_mask),
    .selected_in_oh         (i_hmx_oldest_oh),
    .tag_selected           (i_sel_wr_tag)
  );

assign {i_sel_wr_page
       ,i_sel_wr_cmd_autopre
       ,i_sel_wr_mwr
       ,i_sel_wr_pw_num_cols_m1
       ,i_sel_wr_ie_tag
       ,i_sel_wr_mr_raddr_lsb_first
       ,i_sel_wr_pw_num_beats_m1
    } = i_sel_wr_tag;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      i_sel_wr_valid_r   <= 1'b0;
   end
   else begin
      i_sel_wr_valid_r   <= |te_wr_entry_valid[WR_CAM_ENTRIES -1:0];
   end
end
assign i_sel_wr_valid = i_sel_wr_valid_r; 

//-----------------------------------
// Begin VPW section
//-----------------------------------

wire [WR_CAM_ENTRIES -1:0]     te_vpw_entry_participate;
wire [WR_CAM_ADDR_BITS-1:0]    i_sel_vpw_entry;            // entry # from VPW selection network for expired VPW commands
wire                           i_sel_vpw_valid;            // valid for the selected VPW entry
reg                            i_sel_vpw_valid_r; 
  `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
wire                           i_sel_vpw_valid_sva;
    `endif
  `endif

wire [WR_ECC_CAM_ENTRIES-1:0]     te_wrecc_btt_entry_participate;
wire [WR_ECC_CAM_ADDR_BITS-1:0]   i_sel_wrecc_btt_entry;            // entry # from WRECC BTT selection network for WRECC BTT commands
wire                              i_sel_wrecc_btt_valid;            // valid for the selected WRECC BTT
reg                               i_sel_wrecc_btt_valid_r;
  `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
wire                              i_sel_wrecc_btt_valid_sva;
    `endif
  `endif
wire i_sel_wrecc_btt;


// ---------------------
// VPW filter module
// ---------------------
// All the expired-VPW command entries in the CAM will put their bit high on the te_vpw_valid signal
// te_vpw_page_hit is coming from the page_hit status bit in the CAM entry. It shows whether the 
// page-address in the CAM entry is same as the opened page stored in the page table in BE module
// te_vpw_entry_participate: if there is any page_hit command at the input of the filter, then all the page_hit bits will be set high
// on te_vpw_entry_participate signal. if there are no page_hit commands at the input, then all the page_miss entry bits will be set high
// ---------------------
  te_filter
   #( .CAM_ENTRIES   (WR_CAM_ENTRIES) )
   WR_vpw_filter (
                   .te_bank_hit           (te_vpw_valid_filtred [WR_CAM_ENTRIES -1:0]), // except entries already in NTT
                   .te_page_hit           (te_vpw_page_hit [WR_CAM_ENTRIES -1:0]),
                   .te_entry_participate  (te_vpw_entry_participate [WR_CAM_ENTRIES -1:0])
                  );

//-------------------------------
//VPW selnet module
//-------------------------------
// Picks one entry from among the those entries that have their bit set on the te_vpw_entry_participate signal
// The selection is done on a round-robin basis
// The start of the round-robin search is set by the wall_direction_next signal - in this case vpw_prefer 
//-------------------------------
   wire [WRSEL_TAG_BITS-1:0]      i_sel_vpw_wr_tag;

wire  [WR_CAM_ENTRIES-1:0]        i_hmx_oldest_oh_vpw;
assign i_hmx_oldest_oh_vpw = hmx_oldest_oh_vpw;

select_net_hmatrix
             #(   
    .TAG_BITS               (WRSEL_TAG_BITS),
    .NUM_INPUTS             (WR_CAM_ENTRIES)
  )
  WR_vpw_selnet (
                   .tags                     (wr_selnet_tags_in),            
                   .vlds                     (te_vpw_entry_participate [WR_CAM_ENTRIES -1:0]),
                   .selected                 (i_sel_vpw_entry [WR_CAM_ADDR_BITS-1:0]),
                   `ifndef SYNTHESIS
                     `ifdef SNPS_ASSERT_ON
                   .clk                      (co_te_clk),
                   .resetb                   (core_ddrc_rstn),
                   .selected_vld             (i_sel_vpw_valid_sva),
                     `endif 
                   `endif 
                   .mask                     (hmx_mask_vpw),
                   .selected_in_oh           (i_hmx_oldest_oh_vpw),
                   .tag_selected             (i_sel_vpw_wr_tag)  
                  );


assign {te_sel_vpw_page
       ,te_sel_vpw_cmd_autopre
       ,te_sel_vpw_mwr
       ,te_sel_vpw_pw_num_cols_m1
       ,te_sel_vpw_ie_tag
      ,te_sel_vpw_mr_ram_raddr_lsb
      ,te_sel_vpw_pw_num_beats_m1
       } = i_sel_vpw_wr_tag; 

assign te_sel_vpw_valid = i_sel_vpw_valid; // entry

assign te_sel_vpw_entry[WR_CAM_ADDR_BITS_IE-1] = 1'b0;
assign te_sel_vpw_entry[WR_CAM_ADDR_BITS-1:0]  = i_sel_vpw_entry;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      i_sel_vpw_valid_r   <= 1'b0;
   end
   else begin
      i_sel_vpw_valid_r   <= |te_vpw_valid_filtred[WR_CAM_ENTRIES -1:0];
   end
end
assign i_sel_vpw_valid = i_sel_vpw_valid_r; 

//-----------------------------------
// Begin WRECC btt1 section
// that is existing when UMCTL2_VPW_EN is defined
// that is enabled when exp-vpw is existing
//-----------------------------------

// ---------------------
// WRECC btt filter module
// ---------------------
// All the WRECC w/btt1 command entries in the CAM will put their bit high on the te_wr_entry_ie_btt & te_wr_entry_valid signal
// te_vpw_page_hit is coming from the page_hit status bit in the CAM entry. It shows whether the 
// page-address in the CAM entry is same as the opened page stored in the page table in BE module
// te_wrecc_btt_entry_participate: if there is any page_hit command at the input of the filter, then all the page_hit bits will be set high
// on te_wrecc_btt_entry_participate signal. if there are no page_hit commands at the input, then all the page_miss entry bits will be set high
// ---------------------
  te_filter
   #( .CAM_ENTRIES   (WR_ECC_CAM_ENTRIES) )
   WRECC_btt_filter (
                   .te_bank_hit           (te_wrecc_btt_valid_filtred [WR_ECC_CAM_ENTRIES -1:0]), // except entries already in NTT
                   .te_page_hit           (te_vpw_page_hit [WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES]),
                   .te_entry_participate  (te_wrecc_btt_entry_participate[WR_ECC_CAM_ENTRIES-1:0])
                  );

//-------------------------------
//WRECC btt selnet module
//-------------------------------
// Picks one entry from among the those entries that have their bit set on the te_wrecc_btt_entry_participate signal
// The selection is done on a round-robin basis
// The start of the round-robin search is set by the wall_direction_next signal 
//-------------------------------
wire [WRECCSEL_TAG_BITS-1:0]      i_sel_wrecc_btt_wr_tag;
select_net_hmatrix
             #(   
    .TAG_BITS               (WRECCSEL_TAG_BITS),
    .NUM_INPUTS             (WR_ECC_CAM_ENTRIES)
  )
  WRECC_btt_selnet (
                   .tags                     (wrecc_selnet_tags_in),            
                   .vlds                     (te_wrecc_btt_entry_participate[WR_ECC_CAM_ENTRIES -1:0]),
                   .selected                 (i_sel_wrecc_btt_entry [WR_ECC_CAM_ADDR_BITS-1:0]),
                   `ifndef SYNTHESIS
                      `ifdef SNPS_ASSERT_ON
                   .clk                      (co_te_clk),
                   .resetb                   (core_ddrc_rstn),
                   .selected_vld             (i_sel_wrecc_btt_valid_sva),
                      `endif
                   `endif
                   .mask                     (hmx_wrecc_btt_mask),
                   .selected_in_oh           (hmx_wrecc_btt_oldest_oh),
                   .tag_selected             (i_sel_wrecc_btt_wr_tag)  
                  );

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      i_sel_wrecc_btt_valid_r   <= 1'b0;
   end
   else begin
      i_sel_wrecc_btt_valid_r   <= |te_wrecc_btt_valid_filtred;
   end
end
assign i_sel_wrecc_btt_valid = i_sel_wrecc_btt_valid_r; 

//------------------------------------
// Output assignment
//------------------------------------

assign {te_sel_wrecc_btt_page
       ,te_sel_wrecc_btt_cmd_autopre
       ,te_sel_wrecc_btt_mwr
       ,te_sel_wrecc_btt_pw_num_cols_m1
       ,te_sel_wrecc_btt_mr_ram_raddr_lsb
       ,te_sel_wrecc_btt_pw_num_beats_m1
//`ifdef MEMC_INLINE_ECC
       ,te_sel_wrecc_btt_ie_tag
       ,te_sel_wrecc_btt_ie_btt
       ,te_sel_wrecc_btt_ie_re
//`endif
       } = i_sel_wrecc_btt_wr_tag; 

assign te_sel_wrecc_btt_valid = i_sel_wrecc_btt_valid & i_sel_vpw_valid; //wrecc_btt selnet is valid only when vpw selnet is valid.

assign te_sel_wrecc_btt_entry[WR_CAM_ADDR_BITS_IE-1] = 1'b1;
assign te_sel_wrecc_btt_entry[WR_CAM_ADDR_BITS-1:0]  = {1'b0,i_sel_wrecc_btt_entry};

//--------------------------------------



//-----------------------------------
// Begin INLINE ECC section
//-----------------------------------
// ---------------------
// WR ECC filter module
// ---------------------
// 1. Entries have BTT=1 are highest priority
// 2. Entries have page-hit are 2nd highest priroity 
// ---------------------
  te_filter_vp
   #( .CAM_ENTRIES           (WR_ECC_CAM_ENTRIES) )
  WR_wrecc_filter (
                   .te_vp_expired         (te_wr_entry_ie_btt [WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES]) ,
                   .te_bank_hit           (te_wr_entry_valid [WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES]),
                   .te_page_hit           (te_wr_page_hit [WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES]),
                   .te_entry_participate  (te_wrecc_entry_participate [WR_ECC_CAM_ENTRIES -1:0])
                  );

//-------------------------------
//VPW selnet module
//-------------------------------
// Picks one entry from among the those entries that have their bit set on the te_vpw_entry_participate signal
// The selection is done on a round-robin basis
// The start of the round-robin search is set by the wall_direction_next signal - in this case vpw_prefer 
//-------------------------------
   wire [WRECCSEL_TAG_BITS-1:0]      i_sel_wrecc_wr_tag;
select_net_hmatrix
             #(   
    .TAG_BITS               (WRECCSEL_TAG_BITS),
    .NUM_INPUTS             (WR_ECC_CAM_ENTRIES)
  )
  WR_wrecc_selnet (
                   .tags                     (wrecc_selnet_tags_in),            
                   .vlds                     (te_wrecc_entry_participate [WR_ECC_CAM_ENTRIES -1:0]),
                   .selected                 (i_sel_wrecc_entry [WR_ECC_CAM_ADDR_BITS-1:0]),
                   `ifndef SYNTHESIS
                     `ifdef SNPS_ASSERT_ON
                   .clk                      (co_te_clk),
                   .resetb                   (core_ddrc_rstn),
                   .selected_vld             (i_sel_wrecc_valid_sva),
                     `endif
                   `endif
                   .mask                     (hmx_mask_wrecc),
                   .selected_in_oh           (hmx_oldest_oh_wrecc),
                   .tag_selected             (i_sel_wrecc_wr_tag)            
                  );

assign {i_sel_wrecc_page
       ,i_sel_wrecc_cmd_autopre
       ,i_sel_wrecc_mwr
       ,i_sel_wrecc_pw_num_cols_m1
       ,i_sel_wrecc_mr_raddr_lsb_first
       ,i_sel_wrecc_pw_num_beats_m1
       ,i_sel_wrecc_ie_tag
       ,i_sel_wrecc_ie_btt
       ,i_sel_wrecc_ie_re
       } = i_sel_wrecc_wr_tag;

always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      i_sel_wrecc_valid_r   <= 1'b0;
   end
   else begin
      i_sel_wrecc_valid_r   <= |te_wr_entry_valid[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES];
   end
end
assign i_sel_wrecc_valid = i_sel_wrecc_valid_r; 

wire [WR_ECC_CAM_ADDR_BITS-1:0] i_te_wrecc_btt_prefer;
assign i_te_wrecc_btt_prefer = te_wrecc_btt_prefer; // Use oldest entry within exVPW

assign te_wrecc_prefer = 
                            te_any_wrecc_btt_valid ? {2'b10, i_te_wrecc_btt_prefer} :
                            te_wr_flush_started   ? te_wr_col_entry : {2'b10,ih_te_wrecc_prefer};

// There is BTT candidate -> select from wrecc selnet
// There is page-hit candidate in WRECC and there is not in WR, select from wrecc selnet  
//-------------------------------------------------------------------
//when to select WRECC
//-------------------------------------------------------------------
// 1.NO eVPW in WR entry &&  no collided entry in WR entry
//   (1) WREECC page hit  && (WR no page hit || bsm critical)
//   (2) collied entries in WRECC
// 2. WRECC BTT page-hit |( WRECC BTT && no exVPW in WR entry)
//     (1) reg_ddrc_dis_opt_wrecc_collision_flush =1
//     (2) no no collided entry in WR entry

//so  the priority will be
// when reg_ddrc_dis_opt_wrecc_collision_flush = 1
//   WRECC BTT page hit > WR exVPW > WRECC BTT > WR collsion > WRECC collison > WR page hit > WRECC page hit > WR > WRECC
// when reg_ddrc_dis_opt_wrecc_collision_flush = 0
//   WR exVPW > WR collsion > WRECC BTT(page hit or not) ==??  WRECC collison > WR page hit > WRECC page hit > WR > WRECC


reg pre_wrecc_sel;
//reg pre_wrecc_btt;
always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin 
   if (~core_ddrc_rstn) begin 
      pre_wrecc_sel <= 1'b0;
//      pre_wrecc_btt <= 1'b0;
   end
   else begin 
      pre_wrecc_sel <= ((((|(te_wr_entry_valid[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES] & te_wr_page_hit[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES])) & ( (~|(te_wr_entry_valid[WR_CAM_ENTRIES-1:0] & te_wr_page_hit[WR_CAM_ENTRIES-1:0])) | te_entry_critical_currnt_bsm )))
                     // (----------- Page hit in WRECC selent ------------------------  &   ( ------------- No Page hit in WR selnet ----------------- | --- page_hit_limiter expires --- )) 
                     // `ifdef MEMC_OPT_MULTI_COL || collision in WRECC selnet `endif
                     & ~( te_wr_flush_started & (|(te_wr_col_entries[WR_CAM_ENTRIES-1:0] & te_wr_entry_valid[WR_CAM_ENTRIES-1:0])))
                     // ----------------------------- No Collided entry is in WR CAM ---------------------------------
                     & ~(|(te_wr_entry_valid[WR_CAM_ENTRIES-1:0] & te_vpw_valid))
                     // -------- No VPW candidate ------- 
 ) | 
                     (((|(te_wr_entry_ie_btt[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES] & te_wr_entry_valid[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES] & te_wr_page_hit[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES])) | // There is any page-hit BTT candidate 
                     (|(te_wr_entry_ie_btt[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES] & te_wr_entry_valid[WR_CAM_ENTRIES+:WR_ECC_CAM_ENTRIES])  
                     & ~(|(te_wr_entry_valid[WR_CAM_ENTRIES-1:0] & te_vpw_valid))
                     // -------- No VPW candidate ------- 
)) // There is BTT candidate while no expVPW.
                     );
//      pre_wrecc_btt <= (|(te_wr_entry_ie_btt & te_wr_entry_valid));
   end  
end

assign i_sel_wrecc     = pre_wrecc_sel | (~i_sel_wr_valid);
// assign te_sel_ie_btt   = i_sel_wrecc_valid & pre_wrecc_btt; 

// Output assignment 

assign te_sel_wr_valid = i_sel_wr_valid | i_sel_wrecc_valid;

`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
  property p_values_always_same(a,b); 
    @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (a == b); 
  endproperty


  a_check_i_sel_wr_valid        : assert property (p_values_always_same(i_sel_wr_valid,i_sel_wr_valid_sva)); 
  a_check_i_sel_wrecc_valid     : assert property (p_values_always_same(i_sel_wrecc_valid,i_sel_wrecc_valid_sva));
  a_check_i_sel_vpw_valid       : assert property (p_values_always_same(i_sel_vpw_valid,i_sel_vpw_valid_sva)); 
  a_check_i_sel_wrecc_btt_valid : assert property (p_values_always_same(i_sel_wrecc_btt_valid,i_sel_wrecc_btt_valid_sva)); 

`endif
`endif



endmodule // te_wr_replace
