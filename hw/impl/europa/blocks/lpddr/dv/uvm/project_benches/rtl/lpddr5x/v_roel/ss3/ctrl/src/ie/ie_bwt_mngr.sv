//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ie/ie_bwt_mngr.sv#1 $
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
module ie_bwt_mngr
#(
    parameter TOKEN_ID        = 0
   ,parameter TOKEN_BITS      = 4

)
(  
    input                      core_ddrc_core_clk
   ,input                      core_ddrc_rstn
   ,input                      ddrc_cg_en

   ,input                      new_cmd           //from TE without pipeline, indicate a WD_E command
   ,input                      wr_ecc_cmd        //from mr.ie_wrdata_ctl, after pipeline and write ecc cycles, indicate data for WE_BW command is completed.
   ,input   [TOKEN_BITS-1:0]   cmd_token_id      //from mr.ie_wrdata_ctl, token id.
   // number of access in one block
   // from IH
   ,input   [TOKEN_BITS-1:0]   ie_token_id  // token ID
   ,input   [TOKEN_BITS-1:0]   ie_ass_token_id
   ,input                      ie_ass_token_id_vld
   ,input                      ie_cnt_inc   // increment pulse to the counter
   ,input                      ie_blk_end   // qualify signal
   ,input                      ie_cnt_dec   // decrement pulse to the counter
   //bwt and brt 
   ,input                      free_ass_token_vld
   ,input   [TOKEN_BITS-1:0]   free_ass_token

   ,input                      free_ack     // ack for acc_req
   ,output                     free_req     // request to free
);

//------------------------------ LOCAL PARAMETERS ------------------------------------
localparam BLK_NUM_BITS = 7;

wire [BLK_NUM_BITS-1:0] counter;
reg  [BLK_NUM_BITS:0]   counter_wider; //used to check that no overflow occurs
reg                    blk_end;
reg                    wr_ecc_done;

wire                    ass_token_freed;
reg [TOKEN_BITS-1:0]    ass_token_id_r;
reg                     ass_token_id_vld_r;

reg  ass_token_freed_r;

always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ass_token_id_r     <= {TOKEN_BITS{1'b0}};
      ass_token_id_vld_r <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_req & free_ack)begin
         ass_token_id_r     <= {TOKEN_BITS{1'b0}};
         ass_token_id_vld_r <= 1'b0;
      end else if(ie_blk_end & ie_token_id==TOKEN_ID) begin  //lock the ecc_entry.
         ass_token_id_r     <= ie_ass_token_id;
         ass_token_id_vld_r <= ie_ass_token_id_vld;
      end
   end
end


always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ass_token_freed_r <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_req & free_ack)begin
         ass_token_freed_r <= 1'b0;
      end else if(free_ass_token_vld & ass_token_id_vld_r & (free_ass_token==ass_token_id_r)) begin //ass_token and ass_token_vld only valid after blk_end become 1
         ass_token_freed_r <= 1'b1;
      end
   end
end

assign ass_token_freed= ass_token_id_vld_r ? ass_token_freed_r : 1'b1;

//-------------------------------------------------------------------
// counter access for this IE_BWT in one block
//------------------------------------------------------------------
wire  counter_inc;
wire  counter_dec_a;
wire  counter_dec_b;

assign counter_inc   = ie_cnt_inc & (ie_token_id==TOKEN_ID); 
assign counter_dec_a = new_cmd & (cmd_token_id==TOKEN_ID); 
assign counter_dec_b = ie_cnt_dec;

// Token_mnger & counters code for one token
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      counter_wider <= {(BLK_NUM_BITS+1){1'b0}};
   end else if(ddrc_cg_en) begin
      if(free_req & free_ack)begin
         counter_wider <= {(BLK_NUM_BITS+1){1'b0}};
      end else begin
         counter_wider <= counter_wider[BLK_NUM_BITS-1:0] + counter_inc - counter_dec_a - counter_dec_b;
      end
   end
end

assign counter = counter_wider[BLK_NUM_BITS-1:0];

//generate block end flag
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
//generate write write ecc done flag
always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      wr_ecc_done <= 1'b0;
   end else if(ddrc_cg_en) begin
      if(free_req & free_ack)begin
         wr_ecc_done <= 1'b0;
      end else if(new_cmd & cmd_token_id ==TOKEN_ID)begin
         wr_ecc_done <= 1'b0;
      end else if(wr_ecc_cmd & cmd_token_id==TOKEN_ID) begin
         wr_ecc_done <= 1'b1;
      end
   end
end

//free this token when blk_end and counter==0
assign free_req = ~|counter & wr_ecc_done & blk_end & ass_token_freed;
//free this token when blk_end and bwt_state==IDLE and brt freed if have a brt
///assign free_req =  (bwt_state==IDLE) & blk_end & ass_token_freed;

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
      else $error("%m @ %t Error : cannot assert ie_cnt_inc or ie_blk_end during waiting process previous ie_blk_end ", $time);

  property p_free_ass_token_aft_blk_end;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
       (ass_token_id_vld_r && free_ass_token_vld && (free_ass_token==ass_token_id_r)) |-> (blk_end);
  endproperty
  
  a_free_ass_token_aft_blk_end : assert property (p_free_ass_token_aft_blk_end)
      else $error("%m @ %t Error : free_ass_token should be assert after blk_end=1", $time);

// within ~20 cycles free_ack must be assert after free_req.
//
///  property p_free_ack_win_100_free_req;
///    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
///       ($rose(free_req)) |-> ##[0:20] free_ack;
///  endproperty
///  
///  a_free_ack_win_100_free_req: assert property (p_free_ack_win_100_free_req)
///      else $error("%m @ %t Error : free_ack has not assert within 20 cycle after free_req", $time);

// counter  cannot be overflow
  property p_counter_overflow;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (counter_inc & ~counter_dec_a & ~counter_dec_b) |-> ~&counter;
  endproperty
  
  a_counter_overflow: assert property (p_counter_overflow)
      else $error("%m @ %t Error : counter is overflow", $time);

  property p_counter_underflow;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (~counter_inc & (counter_dec_a | counter_dec_b))  |-> |counter;
  endproperty
  
  a_counter_underflow: assert property (p_counter_underflow)
      else $error("%m @ %t Error : counter is underflow", $time);

  property p_counter_underflow_2;
    @(negedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      (~counter_inc & (counter_dec_a & counter_dec_b))  |-> (counter>1);
  endproperty
  
  a_counter_underflow_2: assert property (p_counter_underflow_2)
      else $error("%m @ %t Error : counter is underflow", $time);
      
  localparam CATEGORY = 5; // Allows groups of assertions to be enabled/disabled at the same time

  // counter overflow
  assert_never #(0, 0, "counter overflow", CATEGORY) a_counter_overflow_chk
    (core_ddrc_core_clk, core_ddrc_rstn, (counter_wider[BLK_NUM_BITS]==1'b1));
          
`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
