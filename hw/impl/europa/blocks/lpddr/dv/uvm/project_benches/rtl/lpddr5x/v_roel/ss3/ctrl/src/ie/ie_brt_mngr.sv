//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ie/ie_brt_mngr.sv#2 $
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
module ie_brt_mngr
#(
    parameter TOKEN_ID        = 0
   ,parameter TOKEN_BITS      = 4
)
(  
    input                      core_ddrc_core_clk
   ,input                      core_ddrc_rstn
   ,input                      ddrc_cg_en 

   // increase counter of the token
   // for write token, TE to MR
   // for read token, RT to RD
   ,input                      new_cmd      //from mr_ram_rd_pipeline, used to increment counter
   ,input   [TOKEN_BITS-1:0]   cmd_token_id //from mr_ram_rd_pipeline, used to increment counter
   // number of access in one block
   // from IH
   ,input   [TOKEN_BITS-1:0]   ie_token_id  // token ID
   ,input                      ie_cnt_inc   // increment pulse to the counter
   ,input                      ie_blk_end   // qualify signal

   ,input                      free_ack     // ack for acc_req
   ,output                     free_req     // request to free 
);

//------------------------------ LOCAL PARAMETERS ------------------------------------
localparam BLK_NUM_BITS    = 7;

reg [BLK_NUM_BITS-1:0] counter;
reg                    blk_end;

//-------------------------------------------------------------------
// counter access for this IE_BWT in one block
//------------------------------------------------------------------
// Token_mnger & counters code for one token
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      counter <= {(BLK_NUM_BITS){1'b0}};
   end else if(ddrc_cg_en) begin
      if(free_req & free_ack)begin
         counter <= {(BLK_NUM_BITS){1'b0}};
      end else if(ie_cnt_inc & ie_token_id==TOKEN_ID & new_cmd & cmd_token_id==TOKEN_ID) begin
         counter <= counter;
      end else if(ie_cnt_inc & ie_token_id==TOKEN_ID) begin
         counter <= counter + 1'b1;
      end else if(new_cmd & cmd_token_id==TOKEN_ID) begin
         counter <= counter - 1'b1;
      end
   end
end

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      blk_end <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_req & free_ack)begin
         blk_end <= 1'b0;
      end else if(ie_blk_end & ie_token_id==TOKEN_ID) begin
         blk_end <= 1'b1;
      end
   end
end

//free this token when blk_end and counter==0
assign free_req = ~|counter & blk_end;


`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON
// within ~100 cycles free_req must be assert after blk_end.
// the number "100" should be replaced by "CAM depth * (BL/2) / Freq_ratio + WL/RL + margin"
//localparam DUATION = `MEMC_NO_OF_ENTRY * 8 / `MEMC_FREQ_RATIO + 100;
//
// consider the worst case of schedule and maintian command, set a big value 500, (just for check every token has been requested to free.
// the assertion can be removed after develop
////localparam DUATION = 1000;
////  property p_free_req_win_num_cycles_blk_end;
////    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
////       ($rose(blk_end)) |-> ##[0:DUATION] free_req;
////  endproperty
////  
////  a_free_req_win_num_cycles_blk_end: assert property (p_free_req_win_num_cycles_blk_end)
////      else $error("%m @ %t Error : free_req has not assert within (CAM depth*4/freq_ratio+50) cycles after blk_end", $time);

  property p_no_cnt_inc_or_blk_end_aft_blk_end;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (blk_end) |-> ~( (ie_cnt_inc | ie_blk_end) & (ie_token_id==TOKEN_ID));
  endproperty
  
  a_no_cnt_inc_or_blk_end_aft_blk_end: assert property (p_no_cnt_inc_or_blk_end_aft_blk_end)
      else $error("%m @ %t Error : cannot assert ie_cnt_inc or ie_blk_end druing waiting process previous ie_blk_end", $time);

// within ~20 cycles free_ack must be assert after free_req.
//
///  property p_free_ack_win_100_free_req;
///    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
///       ($rose(free_req)) |-> ##[0:20] free_ack;
///  endproperty
///  
///  a_free_ack_win_100_free_req: assert property (p_free_ack_win_100_free_req)
///      else $error("%m @ %t Error : free_ack has not assert within 20 cycle after free_req", $time);

// counter cannot be overflow
  property p_counter_overflow;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (ie_cnt_inc & ie_token_id==TOKEN_ID) |-> ~&counter;
  endproperty
  
  a_counter_overflow: assert property (p_counter_overflow)
      else $error("%m @ %t Error : counter is overflow", $time);
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
