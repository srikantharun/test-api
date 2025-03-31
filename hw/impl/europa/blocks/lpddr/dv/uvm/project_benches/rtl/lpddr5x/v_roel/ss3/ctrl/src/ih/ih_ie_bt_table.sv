//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_ie_bt_table.sv#3 $
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
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
module ih_ie_bt_table
#(
    parameter NO_OF_BT       = 16
   ,parameter BT_BITS        = 4
   ,parameter BWT_BITS       = 4
   ,parameter BRT_BITS       = 4
)
(  
    input                    core_ddrc_core_clk
   ,input                    core_ddrc_rstn
   ,input                    ddrc_cg_en

   //signals to generate BT table
   ,input                    alloc_bwt_vld
   ,input                    alloc_brt_vld
   ,input  [BT_BITS-1:0]     ie_bt
   ,input  [BWT_BITS-1:0]    allocated_bwt
   ,input  [BWT_BITS-1:0]    allocated_brt

   //signals to free BT table
   ,input                    free_bwt_vld_i
   ,input                    free_brt_vld_i
   ,input  [BWT_BITS-1:0]    free_bwt_i
   ,input  [BRT_BITS-1:0]    free_brt_i
   ,output                   free_bt_vld_o
   ,output                   free_brt_vld_o
   ,output                   free_bwt_vld_o
   ,output [BT_BITS-1:0]     free_bt_o
   ,output [BWT_BITS-1:0]    free_bwt_o
   ,output [BWT_BITS-1:0]    free_brt_o
   //signals for BTT and RE_RDY
   ,input                    ie_blk_end
   ,input  [BT_BITS-1:0]     ie_blk_end_bt
   ,output [NO_OF_BT-1:0]    ie_btt_vct
   ,input                    rd_ih_ie_re_rdy
   ,output [NO_OF_BT-1:0]    ie_re_vct
   //signals for look up BT table
   ,input  [BT_BITS-1:0]     mr_ih_lkp_bwt_by_bt
   ,input  [BT_BITS-1:0]     mr_ih_lkp_brt_by_bt
   ,input  [BT_BITS-1:0]     rd_ih_lkp_brt_by_bt
   ,input  [BT_BITS-1:0]     rd_ih_lkp_bwt_by_bt
   ,output [BWT_BITS-1:0]    ih_mr_lkp_bwt
   ,output                   ih_mr_lkp_bwt_vld
   ,output [BRT_BITS-1:0]    ih_mr_lkp_brt
   ,output                   ih_mr_lkp_brt_vld
   ,output [BRT_BITS-1:0]    ih_rd_lkp_brt
   ,output                   ih_rd_lkp_brt_vld
   ,output [BWT_BITS-1:0]    ih_rd_lkp_bwt
   ,output                   ih_rd_lkp_bwt_vld
);

//---------------
// Declarations
//---------------

genvar idx;
integer i;

wire [BT_BITS-1:0]            sel_bt;
reg  [NO_OF_BT-1:0]           free_bt_ack_vct;
wire [NO_OF_BT-1:0]           free_bt_req_vct;
wire [NO_OF_BT*BT_BITS-1:0]   bt_o_vct;
wire [NO_OF_BT*BWT_BITS-1:0]  bwt_o_vct;
wire [NO_OF_BT*BRT_BITS-1:0]  brt_o_vct;
wire [NO_OF_BT-1:0]           bwt_vld_o_vct;
wire [NO_OF_BT-1:0]           brt_vld_o_vct;
wire [NO_OF_BT-1:0]           bwt_free_o_vct_unused;
wire [NO_OF_BT-1:0]           brt_free_o_vct_unused;

reg  [BT_BITS-1:0]            ie_re_bt;

//-----------------------------------------------------------------
// SCH BT to release
//-----------------------------------------------------------------

localparam NO_OF_BT_POW2 = 2**BT_BITS; 
wire [NO_OF_BT_POW2-1:0] free_req_vct_pow2;
generate 
   if(NO_OF_BT_POW2>NO_OF_BT) begin: NOTPOW2
      assign free_req_vct_pow2 = {{(NO_OF_BT_POW2-NO_OF_BT){1'b0}}, free_bt_req_vct};
   end else begin: ISPOW2
      assign free_req_vct_pow2 = free_bt_req_vct;
   end
endgenerate

wire req_vct_selected_vld_unused;
wire req_vct_tag_selected_unused;
select_net_lite

#(
   .TAG_BITS(0),
   .NUM_INPUTS (NO_OF_BT_POW2))
U_req_vct_selnet 
(
   .clk                   (core_ddrc_core_clk),
   .resetb                (core_ddrc_rstn),
   .tags                  ({NO_OF_BT_POW2{1'b0}}),
   .vlds                  (free_req_vct_pow2),
   .wall_next             ({BT_BITS{1'b0}}),  //set to 0
   .selected_vld          (req_vct_selected_vld_unused),  //selected_vld is same as |vlds;
   .tag_selected          (req_vct_tag_selected_unused), //not used
   .selected              (sel_bt)
);

always @ (*) begin
   free_bt_ack_vct = {NO_OF_BT{1'b0}};
   for(int i=0;i<NO_OF_BT;i=i+1) begin
     if($unsigned(i) == sel_bt[BT_BITS-1:0] ) begin
       free_bt_ack_vct[i] = 1'b1;
     end
   end
end

wire [NO_OF_BT_POW2*BT_BITS-1:0]   bt_o_vct_tmp;
wire [NO_OF_BT_POW2*BWT_BITS-1:0]  bwt_o_vct_tmp;
wire [NO_OF_BT_POW2*BRT_BITS-1:0]  brt_o_vct_tmp;
wire [NO_OF_BT_POW2-1:0]           bwt_vld_o_vct_tmp;
wire [NO_OF_BT_POW2-1:0]           brt_vld_o_vct_tmp;

//NO_OF_BT_POW2>= NO_OF_BT
generate
  if(NO_OF_BT_POW2 == NO_OF_BT) begin:NO_OF_BT_pow2
assign bt_o_vct_tmp      = bt_o_vct;
assign bwt_o_vct_tmp     = bwt_o_vct;
assign brt_o_vct_tmp     = brt_o_vct;
assign bwt_vld_o_vct_tmp = bwt_vld_o_vct;
assign brt_vld_o_vct_tmp = brt_vld_o_vct;
  end else begin:NO_OF_BT_pow2
assign bt_o_vct_tmp      = {{(NO_OF_BT_POW2-NO_OF_BT)*BT_BITS{1'b0}},bt_o_vct};
assign bwt_o_vct_tmp     = {{(NO_OF_BT_POW2-NO_OF_BT)*BWT_BITS{1'b0}},bwt_o_vct};
assign brt_o_vct_tmp     = {{(NO_OF_BT_POW2-NO_OF_BT)*BRT_BITS{1'b0}},brt_o_vct};
assign bwt_vld_o_vct_tmp = {{(NO_OF_BT_POW2-NO_OF_BT){1'b0}},bwt_vld_o_vct};
assign brt_vld_o_vct_tmp = {{(NO_OF_BT_POW2-NO_OF_BT){1'b0}},brt_vld_o_vct};
  end
endgenerate

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(sel_bt * BT_BITS)' found in module 'ih_ie_bt_table'
//SJ: This coding style is acceptable and there is no plan to change it.


//free_bt_o should same as free_bt_i;
assign free_bt_vld_o = |free_bt_req_vct;
assign free_bt_o     = bt_o_vct_tmp[sel_bt*BT_BITS+:BT_BITS];
assign free_bwt_vld_o= free_bt_vld_o & bwt_vld_o_vct_tmp[sel_bt];
assign free_bwt_o    = bwt_o_vct_tmp[sel_bt*BWT_BITS+:BWT_BITS];
assign free_brt_vld_o= free_bt_vld_o & brt_vld_o_vct_tmp[sel_bt];
assign free_brt_o    = brt_o_vct_tmp[sel_bt*BRT_BITS+:BRT_BITS];

//------------------------------------------------------------------
// Look up BWT/BRT by BT

//------------------------------------------------------------------

assign ih_mr_lkp_bwt     = bwt_o_vct_tmp[mr_ih_lkp_bwt_by_bt*BWT_BITS+:BWT_BITS];
assign ih_mr_lkp_bwt_vld = bwt_vld_o_vct_tmp[mr_ih_lkp_bwt_by_bt];
assign ih_mr_lkp_brt     = brt_o_vct_tmp[mr_ih_lkp_brt_by_bt*BRT_BITS+:BRT_BITS];
assign ih_mr_lkp_brt_vld = brt_vld_o_vct_tmp[mr_ih_lkp_brt_by_bt];

assign ih_rd_lkp_bwt     = bwt_o_vct_tmp[rd_ih_lkp_bwt_by_bt*BWT_BITS+:BWT_BITS];
assign ih_rd_lkp_bwt_vld = bwt_vld_o_vct_tmp[rd_ih_lkp_bwt_by_bt];
assign ih_rd_lkp_brt     = brt_o_vct_tmp[rd_ih_lkp_brt_by_bt*BRT_BITS+:BRT_BITS];
assign ih_rd_lkp_brt_vld = brt_vld_o_vct_tmp[rd_ih_lkp_brt_by_bt];
//spyglass enable_block SelfDeterminedExpr-ML

// regiser rd_ih_lkp_brt_by_bt as ie_re_bt to make it aligned with ie_re_rdy
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ie_re_bt <= {BT_BITS{1'b0}};
   end else if(ddrc_cg_en) begin
      ie_re_bt <= rd_ih_lkp_brt_by_bt;
   end
end
//------------------------------------------------------------------
// instantiate number of BT_ITEMS
//------------------------------------------------------------------
generate
for(idx=0; idx<NO_OF_BT; idx=idx+1) begin: BT_TABLE
   ih_ie_bt_item
   
   #(
       .BT_ID      (idx    )
      ,.BT_BITS    (BT_BITS  )
      ,.BWT_BITS   (BWT_BITS )
      ,.BRT_BITS   (BRT_BITS )
   ) bt_item
   (  
       .core_ddrc_core_clk (core_ddrc_core_clk)
      ,.core_ddrc_rstn     (core_ddrc_rstn    )
      ,.ddrc_cg_en         (ddrc_cg_en        )
   
      //signals to generate BT table
      ,.alloc_bwt_vld      (alloc_bwt_vld)
      ,.alloc_brt_vld      (alloc_brt_vld)
      ,.ie_bt              (ie_bt)
      ,.allocated_bwt      (allocated_bwt)
      ,.allocated_brt      (allocated_brt)
   
      //signals to free BT table
      ,.free_bwt_vld_i     (free_bwt_vld_i)
      ,.free_brt_vld_i     (free_brt_vld_i)
      ,.free_bwt_i         (free_bwt_i)
      ,.free_brt_i         (free_brt_i)
      ,.free_bt_ack        (free_bt_ack_vct[idx])
      ,.free_bt_req        (free_bt_req_vct[idx])
      //signals for BTT and RDECC_RDY
      ,.ie_blk_end         (ie_blk_end)
      ,.ie_blk_end_bt      (ie_blk_end_bt)
      ,.ie_btt             (ie_btt_vct[idx])
      ,.ie_re_rdy          (rd_ih_ie_re_rdy)
      ,.ie_re_bt           (ie_re_bt)
      ,.ie_re              (ie_re_vct[idx])
      //all the status
      ,.bt_o               (bt_o_vct[idx*BT_BITS+:BT_BITS])
      ,.bwt_o              (bwt_o_vct[idx*BWT_BITS+:BWT_BITS])
      ,.brt_o              (brt_o_vct[idx*BRT_BITS+:BRT_BITS])
      ,.bwt_vld_o          (bwt_vld_o_vct[idx])
      ,.brt_vld_o          (brt_vld_o_vct[idx])
      ,.bwt_free_o         (bwt_free_o_vct_unused[idx])
      ,.brt_free_o         (brt_free_o_vct_unused[idx])
   );
end
endgenerate


endmodule
