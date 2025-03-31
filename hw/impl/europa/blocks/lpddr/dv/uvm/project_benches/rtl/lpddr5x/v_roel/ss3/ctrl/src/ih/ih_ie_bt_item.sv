//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_ie_bt_item.sv#1 $
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
module ih_ie_bt_item
#(
    parameter BT_ID        = 0
   ,parameter BT_BITS      = 4
   ,parameter BWT_BITS     = 4
   ,parameter BRT_BITS     = 4
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
   ,input  [BRT_BITS-1:0]    allocated_brt

   //signals to free BT table
   ,input                    free_bwt_vld_i
   ,input                    free_brt_vld_i
   ,input  [BWT_BITS-1:0]    free_bwt_i
   ,input  [BRT_BITS-1:0]    free_brt_i
   ,input                    free_bt_ack
   ,output reg               free_bt_req
   //signals for BTT
   ,input                    ie_blk_end
   ,input  [BT_BITS-1:0]     ie_blk_end_bt
   ,output reg               ie_btt
   //signals for BTT
   ,input                    ie_re_rdy
   ,input  [BT_BITS-1:0]     ie_re_bt
   ,output reg               ie_re

   //all the status
   ,output [BT_BITS-1:0]     bt_o
   ,output [BWT_BITS-1:0]    bwt_o
   ,output [BWT_BITS-1:0]    brt_o
   ,output                   bwt_vld_o
   ,output                   brt_vld_o
   ,output                   bwt_free_o
   ,output                   brt_free_o
);

//---------------
// Declarations
//---------------

// BWT/BRT 
reg  [BWT_BITS-1:0]  bwt;
reg  [BRT_BITS-1:0]  brt;
reg                  bwt_vld;
reg                  brt_vld;
reg                  bwt_free;
reg                  brt_free;
wire                 free_bt_vld;

assign bt_o  = BT_ID;
assign bwt_o = bwt;
assign brt_o = brt;
assign bwt_vld_o = bwt_vld;
assign brt_vld_o = brt_vld;
assign bwt_free_o = bwt_free;
assign brt_free_o = brt_free;
assign free_bt_vld = free_bt_req & free_bt_ack;
//------------------------------------------------------------------
//  generate bwt/brt information
//------------------------------------------------------------------
//BWT and BWT_vld
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      bwt      <= {BWT_BITS{1'b0}};
      bwt_vld  <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(alloc_bwt_vld & ie_bt==BT_ID) begin
         bwt      <= allocated_bwt;
         bwt_vld  <= 1'b1;
      end else if(free_bt_vld)begin
         bwt_vld  <= 1'b0;
      end
   end
end

//BRT and BRT_vld
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      brt      <= {BRT_BITS{1'b0}};
      brt_vld  <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(alloc_brt_vld & ie_bt==BT_ID) begin
         brt      <= allocated_brt;
         brt_vld  <= 1'b1;
      end else if(free_bt_vld)begin
         brt_vld  <= 1'b0;
      end
   end
end

//BWT_free
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      bwt_free  <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_bwt_vld_i & free_bwt_i==bwt & bwt_vld) begin
         bwt_free  <= 1'b1;
      end else if(free_bt_vld)begin
         bwt_free  <= 1'b0;
      end
   end
end

//BRT_free
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      brt_free  <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_brt_vld_i & free_brt_i==brt & brt_vld) begin
         brt_free  <= 1'b1;
      end else if(free_bt_vld)begin
         brt_free   <= 1'b0;
      end
   end
end

always @ (*) begin
   case({bwt_vld, brt_vld})
      2'b01: free_bt_req = brt_free;
      2'b10: free_bt_req = bwt_free;
      2'b11: free_bt_req = bwt_free & brt_free; 
      default: free_bt_req = 1'b0;
   endcase
end

//-----------------------------------
//generate BTT status 
//when token is not be allocated, BTT=0
//when token is allocated, BTT=0 at the beginning
//when token is terminated by ie_blk_end, BTT=1
//when token is released, BTT=0.
//-----------------------------------
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ie_btt <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_bt_vld)begin
         ie_btt   <= 1'b0;
      end else if(ie_blk_end & (ie_blk_end_bt == BT_ID) & (brt_vld | bwt_vld)) begin
         ie_btt  <= 1'b1;
      end
   end
end

//-----------------------------------
//generate RE_RDY status 
//when token is not be allocated, re_rdy=0
//when token is allocated, re_rdy=0 at the beginning
//when read ecc for this token is return, re_rdy=1
//when token is released, re_rdy=0.
//-----------------------------------
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ie_re <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(ie_re_rdy & (ie_re_bt == BT_ID)) begin
         ie_re <= 1'b1;
      end else if(free_bt_vld)begin
         ie_re <= 1'b0;
      end
   end
end
`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON

// check when ie_btt=1, bt_vld(bwt_vld|brt_vld) must be 1
  property p_bt_must_vld_when_ie_btt;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (ie_btt) |-> (bwt_vld | brt_vld);
  endproperty
  
  a_bt_must_vld_when_ie_btt: assert property (p_bt_must_vld_when_ie_btt)
      else $error("%m @ %t Error : when ie_btt assert, bt must be valid (bwt_vld or brt_vld is 1)", $time);

// check when bt(both bwt_vld and brt_vld are 0) is released, ie_btt must be 0
  property p_btt_must_0_when_bt_invalid;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (bwt_vld==0 && brt_vld==0) |-> (ie_btt==0);
  endproperty
  
  a_btt_must_0_when_bt_invalid: assert property (p_btt_must_0_when_bt_invalid)
      else $error("%m @ %t Error : when bt is released (both bwt_vld and brt_vld are 0), ie_btt must be 0", $time);

// check when ie_re=1, brt_vld must be 1
  property p_brt_must_vld_when_ie_re;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (ie_re) |->  (brt_vld);
  endproperty
  
  a_brt_must_vld_when_ie_re: assert property (p_brt_must_vld_when_ie_re)
      else $error("%m @ %t Error : when ie_re assert, brt must be valid", $time);

// check when bt(both bwt_vld and brt_vld are 0) is released, ie_re must be 0
  property p_re_must_0_when_bt_invalid;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (bwt_vld==0 && brt_vld==0) |-> (ie_re==0);
  endproperty
  
  a_re_must_0_when_bt_invalid: assert property (p_re_must_0_when_bt_invalid)
      else $error("%m @ %t Error : when bt is released (both bwt_vld and brt_vld are 0), ie_re must be 0", $time);

property p_before_allocate_brt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (alloc_brt_vld & ie_bt==BT_ID) |-> ~brt_vld & ~brt_free;
endproperty

property p_after_allocate_brt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (alloc_brt_vld & ie_bt==BT_ID) |-> ##1 (brt_vld & ~brt_free);
endproperty

property p_before_free_brt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (free_brt_vld_i & free_brt_i==brt & brt_vld) |-> (~brt_free );
endproperty

property p_after_free_brt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (free_brt_vld_i & free_brt_i==brt & brt_vld) |-> ##1 (brt_free);
endproperty

property p_before_allocate_bwt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (alloc_bwt_vld & ie_bt==BT_ID) |-> ~bwt_vld & ~bwt_free;
endproperty

property p_after_allocate_bwt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (alloc_bwt_vld & ie_bt==BT_ID) |-> ##1 (bwt_vld & ~bwt_free);
endproperty

property p_before_free_bwt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (free_bwt_vld_i & free_bwt_i==bwt & bwt_vld) |-> (~bwt_free);
endproperty

property p_after_free_bwt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (free_bwt_vld_i & free_bwt_i==bwt & bwt_vld) |-> ##1 (bwt_free);
endproperty

property p_free_bt; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  free_bt_req |->((bwt_vld & bwt_free & ~brt_vld) |
                  (brt_vld & brt_free & ~bwt_vld) |
                  (brt_vld & brt_free & bwt_vld & bwt_free));
endproperty

property p_free_bt_one_cycle; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  free_bt_req&free_bt_ack |-> ##1 ~free_bt_req;
endproperty

property p_free_bt_req_win_cycles; 
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  free_bt_req |-> ##[0:(1<<BT_BITS)] free_bt_ack;
endproperty

// Check that table state before allocate BRT
a_before_allocate_brt: assert property (p_before_allocate_brt);

// Check that table state after allocate BRT
a_after_allocate_brt: assert property (p_after_allocate_brt);

// Check that table state before free BRT
a_before_free_brt: assert property (p_before_free_brt);

// Check that table state after free BRT
a_after_free_brt: assert property (p_after_free_brt);

// Check that table state before allocate bwt
a_before_allocate_bwt: assert property (p_before_allocate_bwt);

// Check that table state after allocate bwt
a_after_allocate_bwt: assert property (p_after_allocate_bwt);

// Check that table state before free bwt
a_before_free_bwt: assert property (p_before_free_bwt);

// Check that table state after free bwt
a_after_free_bwt: assert property (p_after_free_bwt);

// Check that table state when free BT
a_free_bt: assert property (p_free_bt);

// Check that free BT for one cycle only
a_free_bt_one_cycle: assert property (p_free_bt_one_cycle);

// Check that free BT req within number of cycles
a_free_bt_req_win_cycles: assert property (p_free_bt_req_win_cycles);
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
