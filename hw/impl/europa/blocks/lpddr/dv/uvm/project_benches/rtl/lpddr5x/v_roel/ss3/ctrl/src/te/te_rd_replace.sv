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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_rd_replace.sv#3 $
// -------------------------------------------------------------------------
// Description:
//
`include "DWC_ddrctl_all_defs.svh"
module te_rd_replace #(
    //-------------------------------- PARAMETERS ----------------------------------
     parameter RD_CAM_ADDR_BITS  = `MEMC_RDCMD_ENTRY_BITS 
    ,parameter RD_CAM_ENTRIES    = 1 << RD_CAM_ADDR_BITS 
    ,parameter PAGE_BITS         = `MEMC_PAGE_BITS       
    ,parameter AUTOPRE_BITS      = 1
    ,parameter IE_TAG_BITS       = 0
    ,parameter CMD_LEN_BITS      = 1
    ,parameter WORD_BITS         = 1 
    ,parameter RDSEL_TAG_BITS    = PAGE_BITS + AUTOPRE_BITS + IE_TAG_BITS + CMD_LEN_BITS + WORD_BITS 
    )
    (
    //---------------------------- INPUTS AND OUTPUTS ------------------------------
     input                                       core_ddrc_rstn 
    ,input                                       co_te_clk 
    ,input   [RD_CAM_ADDR_BITS-1:0]              ih_te_lo_rd_prefer 
    ,input                                       ddrc_cg_en                   // clock gate enable
    ,input   [RD_CAM_ADDR_BITS-1:0]              ih_te_hi_rd_prefer 
    ,input   [RD_CAM_ENTRIES -1:0]               te_rd_entry_pri              // priority of every entry in CAM
    ,input   [RD_CAM_ENTRIES -1:0]               te_rd_page_hit               // read entries matching bank and page from CAM search
    ,input                                       te_rd_flush_started          // indicates a collision causing read entries to be flushed
                                                                              //  this indication starts 1 cycle late,
                                                                              //  but it's clean off a flop for better timing than
                                                                              //  the te_rd_flush signal
    ,input   [RD_CAM_ADDR_BITS-1:0]              te_rd_col_entry              // entry # to be flushed from read CAM
    ,input                                       gs_te_pri_level              // 1=prefer high priority  0=prefer low
    ,output  [RD_CAM_ADDR_BITS -1:0]             te_hi_rd_prefer              // high priority read prefer location
    ,output  [RD_CAM_ADDR_BITS -1:0]             te_lo_rd_prefer              // low priority read prefer location
    ,input   [RD_CAM_ENTRIES -1:0]               te_rd_bank_hit               // valid read entry matching bank from CAM search
    ,output  [RD_CAM_ADDR_BITS-1:0]              te_sel_rd_entry              // entry # of selected CAM entry for replacement
    ,output  [AUTOPRE_BITS-1:0]                  te_sel_rd_cmd_autopre        // cmd_autopre of selected CAM entry
    ,output  [PAGE_BITS-1:0]                     te_sel_rd_page
    ,output  [CMD_LEN_BITS-1:0]                  te_sel_rd_length               //Other Fields of Read of selected CAM entry
    ,output  [WORD_BITS-1:0]                     te_sel_rd_critical_word       //Other Fields of Read of selected CAM entry

    ,output                                      te_sel_rd_valid              // selected read entry for replacement
    ,input   [RD_CAM_ENTRIES*PAGE_BITS-1:0]      te_rd_page_table             // page addresses of all CAM entries
    ,input   [RD_CAM_ENTRIES*AUTOPRE_BITS-1:0]   te_rd_cmd_autopre_table      // cmd_autopre of all CAM entries    
    ,input   [RD_CAM_ENTRIES*CMD_LEN_BITS-1:0]   te_rd_cmd_length_table           //Length Fields of all CAM Entries. 
    ,input   [RD_CAM_ENTRIES*WORD_BITS-1:0]      te_rd_critical_word_table    //Critical Word of all CAM Entries. 
    ,input   [RD_CAM_ENTRIES*IE_TAG_BITS-1:0]    te_rd_ie_tag_table           // Inline ECC specific tag (BT/TYPE/OFFSET/ECCAP)
    ,output  [IE_TAG_BITS-1:0]                   te_sel_rd_ie_tag             // selected ie_tag
    ,input                                       te_any_vpr_timed_out         // Any VPR entry has timed-out
    ,input   [RD_CAM_ENTRIES -1:0]               te_vpr_valid                 // all entries that have expired-VPR commands in them
    ,input   [RD_CAM_ENTRIES -1:0]               te_vpr_valid_for_flush       // To check there are exVPR within candidates for collision
    ,input   [RD_CAM_ENTRIES -1:0]               te_vpr_valid_filtred         // all entries that have expired-VPR commands in them except entries already in NTT
    ,input   [RD_CAM_ENTRIES -1:0]               te_vpr_page_hit              // page hit status of all the entries
    ,output  [RD_CAM_ADDR_BITS-1:0]              te_sel_vpr_entry             // entry # of selected VPR CAM entry for replacement
    ,output  [PAGE_BITS-1:0]                     te_sel_vpr_page 
    ,output  [AUTOPRE_BITS-1:0]                  te_sel_vpr_cmd_autopre             
    ,output                                      te_sel_vpr_valid             // valid for the selected VPR entry
    ,output  [IE_TAG_BITS-1:0]                   te_sel_vpr_ie_tag            // selected ie_tag for VPR
    ,output  [CMD_LEN_BITS-1:0]                  te_sel_vpr_length            // Length for VPR Entry
    ,output  [WORD_BITS-1:0]                     te_sel_vpr_critical_word     // Critical Word for VPR Entry
    ,output  [RD_CAM_ENTRIES -1:0]               hmx_mask 
    ,input   [RD_CAM_ENTRIES -1:0]               hmx_oldest_oh
    ,input                                       reg_ddrc_opt_hit_gt_hpr
    ,input   [RD_CAM_ADDR_BITS -1:0]             te_vpr_prefer  
    ,output  [RD_CAM_ENTRIES -1:0]               hmx_mask_vpr
    ,input   [RD_CAM_ENTRIES -1:0]               hmx_oldest_oh_vpr
    );

//------------------------------- WIRES AND REGS -------------------------------
reg  [RD_CAM_ENTRIES-1:0]      r_rd_entry_valid;             // flopped version of all entries
                                                             //  participating in CAM search
wire [RD_CAM_ENTRIES -1:0]     te_rd_hi_entry_participate;
wire [RD_CAM_ADDR_BITS-1:0]    i_sel_rd_hi_entry;            // entry # from high priority selection network for CAM replacement
                                                             //  (this may be over-ridden for collision cases)
wire                           i_sel_rd_hi_valid;            // selected high priority read entry for replacement
wire [RD_CAM_ENTRIES -1:0]     te_rd_lo_entry_participate;
wire [RD_CAM_ADDR_BITS-1:0]    i_sel_rd_lo_entry;            // entry # from low priority selection network for CAM replacement
                                                             //  (this may be over-ridden for collision cases)
wire                           i_sel_rd_lo_valid;            // selected low priority read entry for replacement
reg                            i_sel_rd_valid_r;             // selected Read valid for replacement
    `ifndef SYNTHESIS
      `ifdef SNPS_ASSERT_ON
wire                           i_sel_rd_lo_valid_sva;
      `endif
    `endif

wire                           i_sel_colliding;
wire [RD_CAM_ADDR_BITS-1:0]    i_te_rd_col_entry;
wire [PAGE_BITS-1:0]           i_rd_col_page;
wire [AUTOPRE_BITS-1:0]        i_rd_col_cmd_autopre;
wire [CMD_LEN_BITS-1:0]        i_rd_length;
wire [WORD_BITS-1:0]           i_rd_critical_word;

wire [RD_CAM_ADDR_BITS-1:0]    i_sel_rd_entry;               // muxed from high and low priority
wire [PAGE_BITS-1:0]           i_sel_rd_page;
wire [AUTOPRE_BITS-1:0]        i_sel_rd_cmd_autopre;
wire [IE_TAG_BITS-1:0]         i_sel_rd_ie_tag;
reg                            r_te_any_vpr_timed_out;       // any_vpr_timed_out per bank
wire [RD_CAM_ADDR_BITS -1:0]   i_te_vpr_prefer;              // Read Prefer when exVPR is there
wire [CMD_LEN_BITS-1:0]        i_sel_rd_length; 
wire [WORD_BITS-1:0]           i_sel_rd_critical_word; 
//---------------------------------- LOGIC -------------------------------------
always @ (posedge co_te_clk or negedge core_ddrc_rstn)
   if (~core_ddrc_rstn) begin
      r_rd_entry_valid <= {RD_CAM_ENTRIES{1'b0}};
      r_te_any_vpr_timed_out <= 1'b0;
   end
   else if(ddrc_cg_en) begin
//spyglass disable_block FlopEConst
//SMD: Enable pin EN on Flop (master RTL_FDCE) is always enabled
//SJ: ddrc_cg_en is fixed to 1 (always disable clock gating) because this module is reused in the block not supporting clock gating
      r_rd_entry_valid <= te_rd_bank_hit;
      r_te_any_vpr_timed_out <= |(te_rd_bank_hit & te_vpr_valid_for_flush);
      // te_rd_bank_hit & te_vpr_valid indicates there is exVPR for the bank to be replaced
//spyglass enable_block FlopEConst
   end

// assign outputs to CAMs based on preferences. These will be used to set bank hints to TS.
// (NOTE: Priority is what it is here - gs_te_pri_level has no effect.
//        This signal does not affect priority indicator from next table, so selection
//        in OS is done based on actual priority bit, not which priority is favored)

assign i_te_vpr_prefer = te_vpr_prefer; // Oldest exVPR entry from HMATRIX



assign te_lo_rd_prefer = te_rd_flush_started ? te_rd_col_entry : ih_te_lo_rd_prefer; 

assign te_hi_rd_prefer =
                             te_any_vpr_timed_out  ? i_te_vpr_prefer :
                             te_rd_flush_started   ? te_rd_col_entry : ih_te_hi_rd_prefer;

// override selection network choice with colliding entry if colliding entry is valid replacement
wire sel_colliding = te_rd_flush_started & r_rd_entry_valid[te_rd_col_entry]

                    &~r_te_any_vpr_timed_out
   ;



   assign te_sel_rd_entry = i_sel_colliding ? i_te_rd_col_entry : i_sel_rd_entry;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(1024 * 8)' found in module 'te_rd_replace'
//SJ: This coding style is acceptable and there is no plan to change it. - refers to `UMCTL_LOG2
wire [PAGE_BITS-1:0] rd_col_page;
  te_mux
   #(
     .ADDRW      (`UMCTL_LOG2 (RD_CAM_ENTRIES)),
     .NUM_INPUTS (RD_CAM_ENTRIES),
     .DATAW      (PAGE_BITS)
   )
   rd_col_page_mux (
     .in_port   (te_rd_page_table),
     .sel       (te_rd_col_entry),
     .out_port  (rd_col_page)
   );   
   
assign te_sel_rd_page  = i_sel_colliding ? i_rd_col_page:
                                         i_sel_rd_page;
wire [AUTOPRE_BITS-1:0] rd_col_cmd_autopre;
  te_mux
   #(
     .ADDRW      (`UMCTL_LOG2 (RD_CAM_ENTRIES)),
     .NUM_INPUTS (RD_CAM_ENTRIES),
     .DATAW      (AUTOPRE_BITS)
   )
   rd_col_cmd_autopre_mux (
     .in_port   (te_rd_cmd_autopre_table),
     .sel       (te_rd_col_entry),
     .out_port  (rd_col_cmd_autopre)
   );   

assign te_sel_rd_cmd_autopre = i_sel_colliding ? i_rd_col_cmd_autopre:
                                               i_sel_rd_cmd_autopre;      
wire [IE_TAG_BITS-1:0] rd_col_ie_tag;
  te_mux
   #(
     .ADDRW      (`UMCTL_LOG2 (RD_CAM_ENTRIES)),
     .NUM_INPUTS (RD_CAM_ENTRIES),
     .DATAW      (IE_TAG_BITS)
   )
   rd_col_ie_tag_mux (
     .in_port   (te_rd_ie_tag_table),
     .sel       (te_rd_col_entry),
     .out_port  (rd_col_ie_tag)
   );   

assign te_sel_rd_ie_tag = sel_colliding ? rd_col_ie_tag:
                                          i_sel_rd_ie_tag;      
//spyglass enable_block SelfDeterminedExpr-ML

wire [CMD_LEN_BITS-1:0] rd_length;
  te_mux
   #(
     .ADDRW      (`UMCTL_LOG2 (RD_CAM_ENTRIES)),
     .NUM_INPUTS (RD_CAM_ENTRIES),
     .DATAW      (CMD_LEN_BITS)
   )
   rd_length_mux (
     .in_port   (te_rd_cmd_length_table),
     .sel       (te_rd_col_entry),
     .out_port  (rd_length)
   );   

assign te_sel_rd_length = i_sel_colliding ? i_rd_length :
                                          i_sel_rd_length;      

wire [WORD_BITS-1:0] rd_critical_word;
  te_mux
   #(
     .ADDRW      (`UMCTL_LOG2 (RD_CAM_ENTRIES)),
     .NUM_INPUTS (RD_CAM_ENTRIES),
     .DATAW      (WORD_BITS)
   )
   rd_critical_word_mux (
     .in_port   (te_rd_critical_word_table),
     .sel       (te_rd_col_entry),
     .out_port  (rd_critical_word)
   );   

assign te_sel_rd_critical_word = i_sel_colliding ? i_rd_critical_word :
                                                 i_sel_rd_critical_word;

assign i_sel_colliding       = sel_colliding;
assign i_te_rd_col_entry     = te_rd_col_entry;
assign i_rd_col_page         = rd_col_page;
assign i_rd_col_cmd_autopre  = rd_col_cmd_autopre;
assign i_rd_length           = rd_length;
assign i_rd_critical_word    = rd_critical_word;



//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(((i + 1) * PAGE_BITS) - 1)' found in module 'te_rd_replace'
//SJ: This coding style is acceptable and there is no plan to change it.

// putting the page and cmd_autopre from all the banks into a single bus
// the format is {page[bankN],cmd_autopre[bankN], ... , page[bank1],cmd_autopre[bank1],page[bank0],cmd_autopre[bank0]}
wire [RD_CAM_ENTRIES*RDSEL_TAG_BITS-1:0] rd_selnet_tags_in;
genvar i;
generate
    for (i=0; i<RD_CAM_ENTRIES; i=i+1) begin : page_and_cmd_autopre_table_gen
assign  rd_selnet_tags_in[((i+1)*RDSEL_TAG_BITS)-1:i*RDSEL_TAG_BITS] =
            {
            te_rd_ie_tag_table[((i+1)*IE_TAG_BITS)-1:i*IE_TAG_BITS],
            te_rd_cmd_length_table[((i+1)*CMD_LEN_BITS)-1:i*CMD_LEN_BITS],
            te_rd_critical_word_table[((i+1)*WORD_BITS)-1:i*WORD_BITS],
            te_rd_page_table[((i+1)*PAGE_BITS)-1:i*PAGE_BITS],
            te_rd_cmd_autopre_table[((i+1)*AUTOPRE_BITS)-1:i*AUTOPRE_BITS]};
    end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

//------------------------------- INSTANTIATIONS -------------------------------
   wire [RDSEL_TAG_BITS-1:0] sel_rd_tag_lo;

   wire [PAGE_BITS-1:0]              sel_rd_page_lo;
   wire [AUTOPRE_BITS-1:0]           sel_rd_cmd_autopre_lo;   
   wire [CMD_LEN_BITS-1:0]           sel_rd_cmd_length_lo;
   wire [WORD_BITS-1:0]              sel_rd_critical_word_lo;


wire  [RD_CAM_ENTRIES-1:0]        i_hmx_oldest_oh;
assign i_hmx_oldest_oh = hmx_oldest_oh;


localparam RD_CAM_ENTRIES_EXTEND = (RD_CAM_ENTRIES >128) ? 256: ((RD_CAM_ENTRIES>64) ? 128 : RD_CAM_ENTRIES);
localparam RD_CAM_ENTRIES_TAG_EXTEND = (RD_CAM_ENTRIES_EXTEND-RD_CAM_ENTRIES)*RDSEL_TAG_BITS;       
wire  [RD_CAM_ENTRIES_EXTEND-1:0] hmx_mask_w;
assign hmx_mask = hmx_mask_w[RD_CAM_ENTRIES-1:0];
wire  [RD_CAM_ENTRIES_EXTEND-1:0] hmx_mask_vpr_w;
assign hmx_mask_vpr = hmx_mask_vpr_w[RD_CAM_ENTRIES-1:0];
select_net_hmatrix
               #(.TAG_BITS(RDSEL_TAG_BITS),
               .NUM_INPUTS (RD_CAM_ENTRIES_EXTEND))           
    RD_lo_selnet (
                   .tags                     (({{RD_CAM_ENTRIES_TAG_EXTEND{1'b0}},rd_selnet_tags_in})),           
                   .vlds                     ({{RD_CAM_ENTRIES_EXTEND - RD_CAM_ENTRIES{1'b0}},te_rd_lo_entry_participate [RD_CAM_ENTRIES -1:0]}),
                   .selected                 (i_sel_rd_lo_entry [RD_CAM_ADDR_BITS-1:0]),
                  `ifndef SYNTHESIS
                    `ifdef SNPS_ASSERT_ON
                   .clk                      (co_te_clk),
                   .resetb                   (core_ddrc_rstn),
                   .selected_vld             (i_sel_rd_lo_valid_sva),
                    `endif
                  `endif
                   .mask                     (hmx_mask_w),
                   .selected_in_oh           ({{RD_CAM_ENTRIES_EXTEND - RD_CAM_ENTRIES{1'b0}},i_hmx_oldest_oh[RD_CAM_ENTRIES -1:0]}),
                   .tag_selected             (sel_rd_tag_lo)
                  );
assign sel_rd_cmd_autopre_lo = sel_rd_tag_lo[AUTOPRE_BITS-1:0];
assign sel_rd_page_lo = sel_rd_tag_lo[PAGE_BITS+AUTOPRE_BITS-1:AUTOPRE_BITS];
assign sel_rd_critical_word_lo = sel_rd_tag_lo[PAGE_BITS+AUTOPRE_BITS+WORD_BITS-1:PAGE_BITS+AUTOPRE_BITS];
assign sel_rd_cmd_length_lo    = sel_rd_tag_lo[PAGE_BITS+AUTOPRE_BITS+WORD_BITS+CMD_LEN_BITS-1:PAGE_BITS+AUTOPRE_BITS+WORD_BITS];

// Generate i_sel_rd_lo_valid from te_rd_bank_hit directly to reduce logic level
always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      i_sel_rd_valid_r <= 1'b0;
   end
   else begin
      i_sel_rd_valid_r <= |te_rd_bank_hit;
   end
end

assign i_sel_rd_lo_valid = i_sel_rd_valid_r;
   
te_filter_vp_2lv #(
  .CAM_ENTRIES  (RD_CAM_ENTRIES) )
  RD_lo_filter (
                   .te_vp_expired         (te_vpr_valid [RD_CAM_ENTRIES -1:0]) ,
                   .te_bank_hit        (te_rd_bank_hit),
                   .te_entry_pri       (te_rd_entry_pri),
                   .pri_level          (gs_te_pri_level),   
                   .reg_ddrc_opt_hit_gt_hpr (reg_ddrc_opt_hit_gt_hpr),
                   .te_page_hit           (te_rd_page_hit [RD_CAM_ENTRIES -1:0]),
                   .te_entry_participate  (te_rd_lo_entry_participate [RD_CAM_ENTRIES -1:0])
                  );
  
   wire [PAGE_BITS-1:0]       sel_rd_page_hi;
   wire [AUTOPRE_BITS-1:0]   sel_rd_cmd_autopre_hi;
   wire [CMD_LEN_BITS-1:0]   sel_rd_cmd_length_hi;
   wire [WORD_BITS-1:0]      sel_rd_critical_word_hi;
   
   wire [RDSEL_TAG_BITS-1:0] sel_rd_tag_hi;     // Row address and cmd_autopre of selected CAM entry


assign te_sel_rd_valid = i_sel_rd_lo_valid;
assign i_sel_rd_entry     = 
                            i_sel_rd_lo_entry                                             ;

assign i_sel_rd_page     = 
                            sel_rd_page_lo;

assign i_sel_rd_cmd_autopre = 
                            sel_rd_cmd_autopre_lo;


assign i_sel_rd_length = 
                            sel_rd_cmd_length_lo;



assign i_sel_rd_critical_word = 
                            sel_rd_critical_word_lo;

wire [IE_TAG_BITS-1:0]     sel_rd_ie_tag_lo;
assign sel_rd_ie_tag_lo = sel_rd_tag_lo[RDSEL_TAG_BITS-1-:IE_TAG_BITS];


assign i_sel_rd_ie_tag = 
                         sel_rd_ie_tag_lo;

wire [RD_CAM_ENTRIES -1:0]     te_vpr_entry_participate;
wire [RD_CAM_ADDR_BITS-1:0]    i_sel_vpr_entry;            // entry # from VPR selection network for expired VPR commands
wire                           i_sel_vpr_valid;            // valid for the selected VPR entry
reg                            i_sel_vpr_valid_r;
  `ifndef SYNTHESIS
    `ifdef SNPS_ASSERT_ON
wire                           i_sel_vpr_valid_sva;            
    `endif
  `endif



// ---------------------
// VPR filter module
// ---------------------
// All the expired-VPR command entries in the CAM will put their bit high on the te_vpr_valid signal
// te_vpr_page_hit is coming from the page_hit status bit in the CAM entry. It shows whether the 
// page-address in the CAM entry is same as the opened page stored in the page table in BE module
// te_vpr_entry_participate: if there is any page_hit command at the input of the filter, then all the page_hit bits will be set high
// on te_vpr_entry_participate signal. if there are no page_hit commands at the input, then all the page_miss entry bits will be set high
// ---------------------
  te_filter
   #( .CAM_ENTRIES   (RD_CAM_ENTRIES) )
   RD_vpr_filter (
                   .te_bank_hit           (te_vpr_valid_filtred [RD_CAM_ENTRIES -1:0]), // Except entries already in NTT
                   .te_page_hit           (te_vpr_page_hit [RD_CAM_ENTRIES -1:0]),
                   .te_entry_participate  (te_vpr_entry_participate [RD_CAM_ENTRIES -1:0])
                  );

//-------------------------------
//VPR selnet module
//-------------------------------
// Picks one entry from among the those entries that have their bit set on the te_vpr_entry_participate signal
// The selection is done on a round-robin basis
// The start of the round-robin search is set by the wall_direction_next signal - in this case vpr_prefer 
//-------------------------------
  wire [RDSEL_TAG_BITS-1:0]      i_sel_vpr_tag;   

wire  [RD_CAM_ENTRIES-1:0]        i_hmx_oldest_oh_vpr;
assign i_hmx_oldest_oh_vpr = hmx_oldest_oh_vpr;


select_net_hmatrix
             #(.TAG_BITS(RDSEL_TAG_BITS),
              .NUM_INPUTS (RD_CAM_ENTRIES_EXTEND))         
  RD_vpr_selnet (
                   .tags                     (({{RD_CAM_ENTRIES_TAG_EXTEND{1'b0}},rd_selnet_tags_in})),      
                   .vlds                     ({{RD_CAM_ENTRIES_EXTEND - RD_CAM_ENTRIES{1'b0}},te_vpr_entry_participate [RD_CAM_ENTRIES -1:0]}),
                   .selected                 (i_sel_vpr_entry [RD_CAM_ADDR_BITS-1:0]),
                  `ifndef SYNTHESIS
                    `ifdef SNPS_ASSERT_ON
                   .clk                      (co_te_clk),
                   .resetb                   (core_ddrc_rstn),
                   .selected_vld             (i_sel_vpr_valid_sva),
                    `endif
                  `endif
                   .mask                     (hmx_mask_vpr_w),
                   .selected_in_oh           ({{RD_CAM_ENTRIES_EXTEND - RD_CAM_ENTRIES{1'b0}},i_hmx_oldest_oh_vpr[RD_CAM_ENTRIES -1:0]}),
                   .tag_selected             (i_sel_vpr_tag)
                  );

assign te_sel_vpr_cmd_autopre = i_sel_vpr_tag[AUTOPRE_BITS-1:0];
assign te_sel_vpr_page = i_sel_vpr_tag[PAGE_BITS+AUTOPRE_BITS-1:AUTOPRE_BITS];
assign te_sel_vpr_critical_word = i_sel_vpr_tag[PAGE_BITS+AUTOPRE_BITS+WORD_BITS-1:PAGE_BITS+AUTOPRE_BITS];
assign te_sel_vpr_length        = i_sel_vpr_tag[PAGE_BITS+AUTOPRE_BITS+WORD_BITS+CMD_LEN_BITS-1:PAGE_BITS+AUTOPRE_BITS+WORD_BITS];

// Generate i_sel_rd_lo_valid from te_vpr_valid_filtred directly to reduce logic level
always @ (posedge co_te_clk or negedge core_ddrc_rstn) begin
   if (~core_ddrc_rstn) begin
      i_sel_vpr_valid_r <= 1'b0;
   end
   else begin
      i_sel_vpr_valid_r <= |te_vpr_valid_filtred;
   end
end

assign i_sel_vpr_valid = i_sel_vpr_valid_r;
assign te_sel_vpr_ie_tag = i_sel_vpr_tag[RDSEL_TAG_BITS-1-:IE_TAG_BITS];

// Output assignment
assign te_sel_vpr_valid = i_sel_vpr_valid ; // entry
assign te_sel_vpr_entry = i_sel_vpr_entry;





`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
  property p_values_always_same(a,b); 
    @(posedge co_te_clk) disable iff(!core_ddrc_rstn) 
    (a == b); 
  endproperty

  a_check_i_sel_rd_lo_valid     : assert property (p_values_always_same(i_sel_rd_lo_valid,i_sel_rd_lo_valid_sva)); 
  a_check_i_sel_vpr_valid       : assert property (p_values_always_same(i_sel_vpr_valid,i_sel_vpr_valid_sva)); 

`endif
`endif
endmodule // te_rd_replace
