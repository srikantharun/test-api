//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_assertions.sv#4 $
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
// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------


`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

`include "DWC_ddrctl_all_defs.svh"
module gs_assertions (
        clk,
        core_ddrc_rstn,
        gs_dh_operating_mode,
        gs_pi_stop_clk_ok,

        gs_pi_ctrlupd_req,
        pi_gs_ctrlupd_ok,
        gs_pi_phyupd_pause_req,
        gs_op_is_rd,
        gs_op_is_wr,



        block_t_xs,
        block_t_xs_dll,

        dh_gs_mr_wr,
        dh_gs_mr_type,
        dh_gs_mr_addr,
        dh_gs_mr_data,

        reg_ddrc_lpddr5,
        dh_gs_rfm_en,
        dh_gs_dis_mrrw_trfc,
        t_rfc_min_timer_bitor,
        gs_pi_op_is_load_mr_norm,

        curr_global_fsm_state,
        next_global_fsm_state,
        prev_global_fsm_state,
        dh_gs_prefer_write,
        te_gs_any_vpr_timed_out,
        ih_gs_any_vpr_timed_out,
        rdhigh_critical,
        rdlow_critical,
        wr_critical,
        wr_mode,
        te_gs_wr_flush,
        te_gs_rd_flush,
        gs_dh_hpr_q_state,
        gs_dh_w_q_state,
        te_gs_any_vpw_timed_out,
        ih_gs_any_vpw_timed_out,

        te_gs_rd_vld,
        te_gs_wr_vld,
        rt_gs_empty,
        mr_gs_empty,
        min_ctrlupd_timer,
        ih_gs_xact_valid,
        refresh_required_early,
        rank_nop_after_refresh,
        rank_speculative_ref,
        os_gs_rank_closed,
        os_gs_act_lo_vld,
        os_gs_act_hi_vld,
        powerdown_idle_timer,
        dh_gs_frequency_ratio
        ,block_rd_timer
        ,block_wr_timer
        ,load_diff_rank_dly_for_max_rank_rd_non3ds
        ,load_diff_rank_dly_for_max_rank_wr_non3ds
        ,gs_ts_lrank_enable_bits
);

parameter RANK_BITS = `MEMC_RANK_BITS;
parameter NUM_RANKS = 1 << RANK_BITS;
parameter NUM_LRANKS = `DDRCTL_DDRC_NUM_LRANKS_TOTAL;
parameter NUM_PRANKS = `DDRCTL_DDRC_NUM_PR_CONSTRAINTS;
parameter CID_WIDTH  = `DDRCTL_DDRC_CID_WIDTH;

   // RANKCTL
parameter DIFF_RANK_RD_GAP_WIDTH     = `REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_RD_GAP;
parameter DIFF_RANK_WR_GAP_WIDTH     = `REGB_FREQ0_CH0_SIZE_RANKTMG0_DIFF_RANK_WR_GAP;

localparam pFSM_STATE_WIDTH = 5;


    localparam GS_ST_RESET                = 5'b00000;
    localparam GS_ST_INIT_DDR             = 5'b00010;
    localparam GS_ST_NORMAL_RD            = 5'b00100;
    localparam GS_ST_NORMAL_WR            = 5'b00101;
    localparam GS_ST_POWERDOWN_ENT        = 5'b00110;    // powerdown pads then DDR
    localparam GS_ST_POWERDOWN_ENT_DFILP  = 5'b00001;    // DFI LP I/F entry PD
    localparam GS_ST_POWERDOWN            = 5'b01000;    // in powerdown
    localparam GS_ST_POWERDOWN_EX_DFILP   = 5'b01001;    // DFI LP I/F exit PD
    localparam GS_ST_POWERDOWN_EX1        = 5'b01010;    // power up pads
    localparam GS_ST_POWERDOWN_EX2        = 5'b01011;    // power up DDR
    localparam GS_ST_SELFREF_ENT          = 5'b00111;    // put DDR in self-refresh then power down pads
    localparam GS_ST_SELFREF_ENT2         = 5'b10101;    // Disable C/A Parity before SR if C/A parity had been enabled 
    localparam GS_ST_SELFREF_ENT_DFILP    = 5'b00011;    // DFI LP I/F entry SR
    localparam GS_ST_SELFREF              = 5'b01100;    // DDR is in self-refresh
    localparam GS_ST_SELFREF_EX_DFILP     = 5'b01101;    // DFI LP I/F exit SR
    localparam GS_ST_SELFREF_EX1          = 5'b01110;    // power up pads
    localparam GS_ST_SELFREF_EX2          = 5'b01111;    // bring DDR out of self-refresh

        localparam GS_ST_DSM_ENT_DFILP    = 5'b11000;    // DFI LP I/F entry DSM
        localparam GS_ST_DSM              = 5'b11001;    // DDR is in deep sleep mode
        localparam GS_ST_DSM_EX_DFILP     = 5'b11010;    // DFI LP I/F exit DSM
    localparam STACK_MONO             = 2'b00;       // 3DS monolithic

input                   clk;
input                   core_ddrc_rstn;
input [2:0] gs_dh_operating_mode;   // 00 = uninitialized
input[NUM_LRANKS-1:0] rank_nop_after_refresh; // block everything after refresh (rank)
input           gs_pi_stop_clk_ok;

input                   gs_pi_ctrlupd_req;
input                   pi_gs_ctrlupd_ok;
input                   gs_pi_phyupd_pause_req;
input                   gs_op_is_rd;
input                   gs_op_is_wr;



input                   block_t_xs;
input                   block_t_xs_dll;
input                           dh_gs_mr_wr;
input                           dh_gs_mr_type;
input   [3:0]                   dh_gs_mr_addr;
input   [`MEMC_PAGE_BITS-1:0]   dh_gs_mr_data;

input                           reg_ddrc_lpddr5;
input                           dh_gs_rfm_en;
input                           dh_gs_dis_mrrw_trfc;
input   [NUM_LRANKS-1:0]        t_rfc_min_timer_bitor;
input                           gs_pi_op_is_load_mr_norm;

input   [pFSM_STATE_WIDTH-1:0]  curr_global_fsm_state;
input   [pFSM_STATE_WIDTH-1:0]  next_global_fsm_state;
input   [pFSM_STATE_WIDTH-1:0]  prev_global_fsm_state;
input                   dh_gs_prefer_write;
input                   te_gs_any_vpr_timed_out;
input                   ih_gs_any_vpr_timed_out;
input                   rdhigh_critical;
input                   rdlow_critical;
input                   wr_critical;
input                   wr_mode;
input                   te_gs_wr_flush;
input                   te_gs_rd_flush;
input  [1:0]            gs_dh_hpr_q_state;
input  [1:0]            gs_dh_w_q_state;
input                   te_gs_any_vpw_timed_out;
input                   ih_gs_any_vpw_timed_out;

input                   te_gs_rd_vld;
input                   te_gs_wr_vld;
input                   rt_gs_empty;
input                   mr_gs_empty;
input                   ih_gs_xact_valid;

input   [NUM_LRANKS-1:0] refresh_required_early;
input   [NUM_LRANKS-1:0] rank_speculative_ref;   // refresh timer expired at least once
input   [NUM_LRANKS-1:0] os_gs_rank_closed;      // '1' for each rank with all banks closed
input                   os_gs_act_lo_vld;       // high priority activate pending
input                   os_gs_act_hi_vld;       // high priority activate pending

input [7:0]             min_ctrlupd_timer;
input [7:0]             powerdown_idle_timer;   // powerdown idle timer
input          dh_gs_frequency_ratio;

reg[2:0]   gs_dh_operating_mode_r;   // 00 = uninitialized

input [8:0]             block_rd_timer    [NUM_LRANKS-1:0];
input [8:0]             block_wr_timer    [NUM_LRANKS-1:0];
input [NUM_LRANKS-1:0]  load_diff_rank_dly_for_max_rank_rd_non3ds;
input [NUM_LRANKS-1:0]  load_diff_rank_dly_for_max_rank_wr_non3ds;
input [NUM_LRANKS-1:0]  gs_ts_lrank_enable_bits;

// Get physical/logical rank number of each instances shown in "Example for PhysicalRank/CID for this instance" in gs_rank_constraints.v 
reg  [RANK_BITS-1:0]  this_physical_rank [NUM_LRANKS-1:0];

genvar gv_pr;
generate 
  for (gv_pr = 0; gv_pr < NUM_LRANKS; gv_pr++) begin: this_physical_rank_gen
    assign this_physical_rank[gv_pr] = 
    gv_pr;
  end
endgenerate


always @ (posedge clk)
        gs_dh_operating_mode_r <= gs_dh_operating_mode;

// no transaction on gs_dh_operating_mode if rank_nop_after_refresh is asserted
property gs_stop_clk_check1;
        @(posedge clk) disable iff (~core_ddrc_rstn) (|rank_nop_after_refresh) |-> (~(gs_dh_operating_mode ^ gs_dh_operating_mode_r));
endproperty

a_gs_stop_clk_check1: assert property (gs_stop_clk_check1)
        else $error("%m %t there should not be a transsition in gs_dh_operating_mode when rank_nop_after_refresh is asserted", $time);


// gs_pi_stop_clk_ok does not assert when any rank_nop_after_refresh is asserted
property gs_stop_clk_check2;
        @(posedge clk) disable iff (~core_ddrc_rstn) (|rank_nop_after_refresh) |-> (~gs_pi_stop_clk_ok);
endproperty

a_gs_stop_clk_check2: assert property (gs_stop_clk_check2)
        else $error("%m %t gs_pi_stop_clk_ok should not be asserted when rank_nop_after_refresh is asserted", $time);




// Ensure that DFI controller update never happens with any read or write
// _replace_P80001562-505275_: Add other commands here: act, pre, refresh, ZQ, etc.
property no_rdwr_with_ctrlupd_check;
        @(posedge clk) disable iff (~core_ddrc_rstn)
              (gs_pi_ctrlupd_req & pi_gs_ctrlupd_ok) |->
              !(gs_op_is_rd | gs_op_is_wr |
              0 );
endproperty

a_no_rdwr_with_ctrlupd: assert property (no_rdwr_with_ctrlupd_check)
         else $error("%m %t DFI controller update should never be issued at the same time as any read or write command", $time);


// Check the perf traffic in case of consecutive NORMAL_RD<->NORMAL_WR transitions of the global_fsm
 integer rd_to_wr__wr_to_rd_cnt;
 always @(negedge clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) rd_to_wr__wr_to_rd_cnt = 0;
    else
      if (gs_op_is_rd || gs_op_is_wr)
         rd_to_wr__wr_to_rd_cnt = 0;
      else if ((curr_global_fsm_state == GS_ST_NORMAL_RD && next_global_fsm_state == GS_ST_NORMAL_WR) ||
               (curr_global_fsm_state == GS_ST_NORMAL_WR && next_global_fsm_state == GS_ST_NORMAL_RD))
         rd_to_wr__wr_to_rd_cnt = (rd_to_wr__wr_to_rd_cnt+1)%1025;
      else rd_to_wr__wr_to_rd_cnt = 0;
 end
 
 property p_rd_to_wr_wr_to_rd;
    @(posedge clk) disable iff (~core_ddrc_rstn)
    rd_to_wr__wr_to_rd_cnt==1024 |-> (1'b0);
 endproperty
 
 a_rd_to_wr_wr_to_rd : assert property (p_rd_to_wr_wr_to_rd)
    else $error("%m @ %t Error : 1024 consecutive NORMAL_RD<->NORMAL_WR transitions without any RD/WR traffic on DFI", $time);

// 
// ----------------------------------------------
// Assertions for Max rank read/write feature.
// -----------------------------------------------
// Checks the behavior of the feature across ranks below.
//  1) The feature can not be activated in different physical ranks at same cycle.
//  2) When the feature is activated, blocking cycles for each rank are set to same value.
// The following 2 signals are used as the criteria.
//  - load_diff_rank_dly_for_max_rank_rd/wr_non3ds/phy: Flag indicating the feature is activated.
//  - block_rd/wr_timer_non3ds/phy                    : Cycles blocking a rank to issue next RD/WR.
// 
// This feature is owned in either gs_rank_constraints.v or gs_physical_rank_constraints.v depending on the parameters below.
// gs_rank_constraints.v : MEMC_NUM_RANKS_GT_1 &
//                         (
//                           (!DDRCTL_DDRC_CID_EN & (MSTR.active_ranks != 1)) ||                                                                      --- CONFIG_1: Multi-physical ranks with no logical ranks.
//                           ( DDRCTL_DDRC_CID_EN & (MSTR.active_ranks != 1) & (MSTR.active_logical_ranks == 0))                                      --- CONFIG_2: Multi-physical ranks and multi-logical ranks with monolithic 3DS setting. 
//                         )
// gs_physical_rank_constraints.v: DDRCTL_DDRC_NUM_PR_CONSTRAINTS_GT_1 & DDRCTL_DDRC_CID_EN & (MSTR.active_ranks != 1) & (MSTR.active_logical_ranks != 0)  --- CONFIG_3: Multi-physical ranks and Multi-logical ranks as enabling 3DS. 
//
// Expectations for 1) in each configurations are below.
//  - CONFIG_1: load_diff_rank_dly_for_max_rank_rd/wr_non3ds should be always onehot.
//  - CONFIG_2: load_diff_rank_dly_for_max_rank_rd/wr_non3ds can be high in some logical ranks at same cycle only if that logical ranks are belonging to same physical rank.
//  - CONFIG_3: load_diff_rank_dly_for_max_rank_rd/wr_phy should be always onehot.
// Expectations for 2) in each configurations are below
//  - CONFIG_1: block_rd/wr_timer should be set to same value in all physical ranks.
//  - CONFIG_2: block_rd/wr_timer should be set to same value in all logical ranks which load_diff_rank_dly_for_max_rank_rd/wr_non3ds asserted. 
//              Also block_rd/wr_timer of logical ranks which is belonging to different physical rank is set to same value.
//  - CONFIG_3: block_rd/wr_timer of logical ranks which is belonging to different physical rank should be set to same value with block_rd/wr_timer_phy which load_diff_rank_dly_for_max_rank_rd/wr_3ds asserted.


// Get the index of the first occurrence of 1 in load_diff_rank_dly_for_max_rank_rd/wr_non3ds 
integer load_rd_non3ds_idx;
integer load_rd_non3ds_idx_r;
 
assign load_rd_non3ds_idx = (|load_diff_rank_dly_for_max_rank_rd_non3ds) ? $countones((load_diff_rank_dly_for_max_rank_rd_non3ds & (~load_diff_rank_dly_for_max_rank_rd_non3ds + 1'b1)) - 1'b1) : 0;

always @(posedge clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn)  begin
    load_rd_non3ds_idx_r <= 0;
  end else begin
    load_rd_non3ds_idx_r <= load_rd_non3ds_idx;
  end
end

integer load_wr_non3ds_idx;
integer load_wr_non3ds_idx_r;

assign load_wr_non3ds_idx = (|load_diff_rank_dly_for_max_rank_wr_non3ds) ? $countones((load_diff_rank_dly_for_max_rank_wr_non3ds & (~load_diff_rank_dly_for_max_rank_wr_non3ds + 1'b1))  - 1'b1) : 0;

always @(posedge clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn)  begin
    load_wr_non3ds_idx_r <= 0;
  end else begin
    load_wr_non3ds_idx_r <= load_wr_non3ds_idx;
  end
end


// Check if only one bit of load_diff_rank_dly_for_max_rank_rd_non3ds can be high at a cycle
property p_onehot_load_rd_non3ds;
   @(posedge clk) disable iff (~core_ddrc_rstn)
   $onehot0(load_diff_rank_dly_for_max_rank_rd_non3ds & gs_ts_lrank_enable_bits);
endproperty

a_onehot_load_rd_non3ds : assert property(p_onehot_load_rd_non3ds)
  else $error("%m %t load_diff_rank_dly_for_max_rank_rd_non3ds must be onehot", $time);

// Check if only one bit of load_diff_rank_dly_for_max_rank_wr_non3ds can be high at a cycle
property p_onehot_load_wr_non3ds;
   @(posedge clk) disable iff (~core_ddrc_rstn)
   $onehot0(load_diff_rank_dly_for_max_rank_wr_non3ds & gs_ts_lrank_enable_bits);
endproperty

a_onehot_load_wr_non3ds : assert property(p_onehot_load_wr_non3ds)
  else $error("%m %t load_diff_rank_dly_for_max_rank_wr_non3ds must be onehot", $time);


// Check if max rank read blocks ranks the same cycles until any rank can issue next RD command.
// When load_diff_rank_dly_for_max_rank_rd_non3ds is high, block_rd_timer must be equal in all physical ranks
genvar gv_r_non3ds;
generate
   for (gv_r_non3ds=0; gv_r_non3ds<NUM_RANKS; gv_r_non3ds=gv_r_non3ds+1) begin: max_rank_rd_non3ds_check_rank_gen
     property block_rd_non3ds_time_check;
        @(posedge clk) disable iff ((~core_ddrc_rstn)
                                    || (~gs_ts_lrank_enable_bits[gv_r_non3ds])
                                    || (~gs_ts_lrank_enable_bits[load_rd_non3ds_idx_r]))
         (|load_diff_rank_dly_for_max_rank_rd_non3ds && (this_physical_rank[load_rd_non3ds_idx] != this_physical_rank[gv_r_non3ds]))
         |=>
             (block_rd_timer[gv_r_non3ds] == block_rd_timer[load_rd_non3ds_idx_r]);
     endproperty 

     a_block_rd_non3ds_time_check: assert property (block_rd_non3ds_time_check)
         else $error("%m %t Max rank read blocked ranks unequally", $time);
   end
endgenerate

// Check if max rank read blocks ranks the same cycles until any rank can issue next WR command.
// When load_diff_rank_dly_for_max_rank_wr_non3ds is high, block_wr_timer must be equal in all physical ranks
genvar gv_w_non3ds;
generate
   for (gv_w_non3ds=0; gv_w_non3ds<NUM_RANKS; gv_w_non3ds=gv_w_non3ds+1) begin: max_rank_wr_non3ds_check_rank_gen
     property block_wr_non3ds_time_check;
        @(posedge clk) disable iff ((~core_ddrc_rstn)
                                    || (~gs_ts_lrank_enable_bits[gv_w_non3ds])
                                    || (~gs_ts_lrank_enable_bits[load_wr_non3ds_idx_r]))
         (|load_diff_rank_dly_for_max_rank_wr_non3ds && (this_physical_rank[load_wr_non3ds_idx] != this_physical_rank[gv_w_non3ds]))
         |=>
             (block_wr_timer[gv_w_non3ds] == block_wr_timer[load_wr_non3ds_idx_r]);
     endproperty 

     a_block_wr_non3ds_time_check: assert property (block_wr_non3ds_time_check)
         else $error("%m %t Max rank read blocked ranks unequally", $time);
   end
endgenerate



///////////////////////
// Coverage points
///////////////////////

// coverage for speculative refresh request, ranks closed and activate_lo request
cover_spec_refresh_and_lo_act: cover property (@(posedge clk) disable iff (~core_ddrc_rstn) 
    (rank_speculative_ref & os_gs_rank_closed & ~rank_nop_after_refresh & {NUM_LRANKS{os_gs_act_lo_vld}}));


// coverage for speculative refresh request, ranks closed and activate_hi request
cover_spec_refresh_and_hi_act: cover property (@(posedge clk) disable iff (~core_ddrc_rstn)
    (rank_speculative_ref & os_gs_rank_closed & ~rank_nop_after_refresh & {NUM_LRANKS{os_gs_act_hi_vld}}));

// coverage for speculative refresh request, ranks closed and any request from IH
cover_spec_refresh_and_ih_xact_vld: cover property (@(posedge clk) disable iff (~core_ddrc_rstn)
    (rank_speculative_ref & os_gs_rank_closed & ~rank_nop_after_refresh & {NUM_LRANKS{ih_gs_xact_valid}}));


///////////////
// coverage for speculative refresh request, ranks closed and bypass match
///////////////







// When powerdown_idle_timeout happens, checking to make sure that the following events happen
// 1. An activate_lo command comes
// 2. An activate hi command comes

cover_act_lo_when_pd_idle_timeout: cover property (@(posedge clk) disable iff(~core_ddrc_rstn)
          (os_gs_act_lo_vld && (powerdown_idle_timer==8'h0) && (&os_gs_rank_closed)));

cover_act_hi_when_pd_idle_timeout: cover property (@(posedge clk) disable iff(~core_ddrc_rstn)
          (os_gs_act_hi_vld && (powerdown_idle_timer==8'h0) && (&os_gs_rank_closed)));



// WHen ctrlupd timeout happens and when controller is idle,
// checking to make sure that the following events happen
// 1. some transaction from IH comes

// WHen ctrlupd timeout happens ,
// checking to make sure that the following events happen (see bugzilla 4674 #2)
// 2. An activate_lo command comes
// 3. An activate hi command comes

wire    ddrc_idle;
assign ddrc_idle = !te_gs_rd_vld && !te_gs_wr_vld && rt_gs_empty && mr_gs_empty;

cover_ih_xact_when_ctrlupd_timeout: cover property (@(posedge clk) disable iff(~core_ddrc_rstn)
                                        (ih_gs_xact_valid && (min_ctrlupd_timer==8'h0) && ddrc_idle));

cover_act_lo_when_ctrlupd_timeout: cover property (@(posedge clk) disable iff(~core_ddrc_rstn)
                                        (os_gs_act_lo_vld && (min_ctrlupd_timer==8'h0) ));

cover_act_hi_when_ctrlupd_timeout: cover property (@(posedge clk) disable iff(~core_ddrc_rstn)
                                        (os_gs_act_hi_vld && (min_ctrlupd_timer==8'h0) ));



`ifdef VCS
`endif // VCS



//-------------------------
// Fast Self-Refresh Exit
//-------------------------
// coverage points for the bypass commands



//---------------------
// MRR/MRW operation
//---------------------
// coverage point to check the global FSM state when Software executes a MRR and MRW via MRCTRL
covergroup cg_global_fsm_when_mrctrl_access2 @(posedge clk);

    cp_curr_fsm : coverpoint (curr_global_fsm_state) iff (core_ddrc_rstn) {
        bins norm                   = {GS_ST_NORMAL_RD, GS_ST_NORMAL_WR};
        bins sre                    = {GS_ST_SELFREF_ENT};
        bins sre2                   = {GS_ST_SELFREF_ENT2};
        bins sre_dfilp              = {GS_ST_SELFREF_ENT_DFILP};
        bins srx                    = {GS_ST_SELFREF_EX1};
        bins srx2                   = {GS_ST_SELFREF_EX2};
        bins srx_dfilp              = {GS_ST_SELFREF_EX_DFILP};
        bins srpd                   = {GS_ST_SELFREF};
        bins pde                    = {GS_ST_POWERDOWN_ENT};
        bins others                 = default;
        type_option.weight          = 0;
    }

    cp_next_fsm : coverpoint (next_global_fsm_state) iff (core_ddrc_rstn) {
        bins norm                   = {GS_ST_NORMAL_RD, GS_ST_NORMAL_WR};
        bins sre                    = {GS_ST_SELFREF_ENT};
        bins sre2                   = {GS_ST_SELFREF_ENT2};
        bins sre_dfilp              = {GS_ST_SELFREF_ENT_DFILP};
        bins srx                    = {GS_ST_SELFREF_EX1};
        bins srx2                   = {GS_ST_SELFREF_EX2};
        bins srx_dfilp              = {GS_ST_SELFREF_EX_DFILP};
        bins srpd                   = {GS_ST_SELFREF};
        bins pde                    = {GS_ST_POWERDOWN_ENT};
        bins others                 = default;
        type_option.weight          = 0;
    }

    cp_prev_fsm : coverpoint (prev_global_fsm_state) iff (core_ddrc_rstn) {
        bins norm                   = {GS_ST_NORMAL_RD, GS_ST_NORMAL_WR};
        bins sre                    = {GS_ST_SELFREF_ENT};
        bins sre2                   = {GS_ST_SELFREF_ENT2};
        bins sre_dfilp              = {GS_ST_SELFREF_ENT_DFILP};
        bins srx                    = {GS_ST_SELFREF_EX1};
        bins srx2                   = {GS_ST_SELFREF_EX2};
        bins srx_dfilp              = {GS_ST_SELFREF_EX_DFILP};
        bins srpd                   = {GS_ST_SELFREF};
        bins pde                    = {GS_ST_POWERDOWN_ENT};
        bins others                 = default;
        type_option.weight          = 0;
    }

    // MRCTRL access
    cp_mrctrl : coverpoint ({dh_gs_mr_wr, dh_gs_mr_type}) iff (core_ddrc_rstn) {
        bins mrr                    = {2'b11};
        bins mrw                    = {2'b10};
        bins others                 = default;
        type_option.weight          = 0;
    }

    cx_global_fsm_when_mr_access : cross cp_mrctrl, cp_curr_fsm, cp_next_fsm, cp_prev_fsm {
        bins mrw_norm               = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.norm);
        bins mrw_pde                = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.pde);
        bins mrw_srpd               = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.srpd);
        bins mrw_sre                = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.sre);
        bins mrw_sre2               = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.sre2);
        bins mrw_sre_dfilp          = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.sre_dfilp);
        bins mrw_srx                = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.srx);
        bins mrw_srx2               = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.srx2);
        bins mrw_srx_dfilp          = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.srx_dfilp);

        bins mrr_norm               = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.norm);
        bins mrr_pde                = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.pde);
        bins mrr_srpd               = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.srpd);
        bins mrr_sre                = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.sre);
        bins mrr_sre2               = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.sre2);
        bins mrr_sre_dfilp          = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.sre_dfilp);
        bins mrr_srx                = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.srx);
        bins mrr_srx2               = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.srx2);
        bins mrr_srx_dfilp          = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.srx_dfilp);

        bins mrw_norm_to_sre        = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.norm) && binsof(cp_next_fsm.sre);
        bins mrw_just_sre           = binsof(cp_mrctrl.mrw) && binsof(cp_prev_fsm.norm) && binsof(cp_curr_fsm.sre);
        bins mrw_sre_to_sre2        = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.sre ) && binsof(cp_next_fsm.sre2);
        bins mrw_just_sre2          = binsof(cp_mrctrl.mrw) && binsof(cp_prev_fsm.sre ) && binsof(cp_curr_fsm.sre2);
        bins mrw_sre2_to_srpd       = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.sre2) && binsof(cp_next_fsm.srpd);
        bins mrw_just_srpd          = binsof(cp_mrctrl.mrw) && binsof(cp_prev_fsm.sre2) && binsof(cp_curr_fsm.srpd);
        bins mrw_sre2_to_sre_dfilp  = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.sre2) && binsof(cp_next_fsm.sre_dfilp);
        bins mrw_just_sre_dfilp     = binsof(cp_mrctrl.mrw) && binsof(cp_prev_fsm.sre2) && binsof(cp_curr_fsm.sre_dfilp);
        bins mrw_norm_to_pde        = binsof(cp_mrctrl.mrw) && binsof(cp_curr_fsm.norm) && binsof(cp_next_fsm.pde);
        bins mrw_just_pde           = binsof(cp_mrctrl.mrw) && binsof(cp_prev_fsm.norm) && binsof(cp_curr_fsm.pde);

        bins mrr_norm_to_sre        = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.norm) && binsof(cp_next_fsm.sre);
        bins mrr_just_sre           = binsof(cp_mrctrl.mrr) && binsof(cp_prev_fsm.norm) && binsof(cp_curr_fsm.sre);
        bins mrr_sre_to_sre2        = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.sre ) && binsof(cp_next_fsm.sre2);
        bins mrr_just_sre2          = binsof(cp_mrctrl.mrr) && binsof(cp_prev_fsm.sre ) && binsof(cp_curr_fsm.sre2);
        bins mrr_sre2_to_srpd       = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.sre2) && binsof(cp_next_fsm.srpd);
        bins mrr_just_srpd          = binsof(cp_mrctrl.mrr) && binsof(cp_prev_fsm.sre2) && binsof(cp_curr_fsm.srpd);
        bins mrr_sre2_to_sre_dfilp  = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.sre2) && binsof(cp_next_fsm.sre_dfilp);
        bins mrr_just_sre_dfilp     = binsof(cp_mrctrl.mrr) && binsof(cp_prev_fsm.sre2) && binsof(cp_curr_fsm.sre_dfilp);
        bins mrr_norm_to_pde        = binsof(cp_mrctrl.mrr) && binsof(cp_curr_fsm.norm) && binsof(cp_next_fsm.pde);
        bins mrr_just_pde           = binsof(cp_mrctrl.mrr) && binsof(cp_prev_fsm.norm) && binsof(cp_curr_fsm.pde);
    }

endgroup : cg_global_fsm_when_mrctrl_access2

// Coverage group instantiation
cg_global_fsm_when_mrctrl_access2 cg_global_fsm_when_mrctrl_access2_inst = new;
//---------------------
// RFM related assertions/cover propertys
//---------------------
// Check that changing LPDDR5 ARFM (MRW to MR57:OP[7:6] is requested while MRCTRL0.dis_mrrw_trfc==1
property p_arfm_mrw_with_dis_mrrw_trfc;
   @(posedge clk) disable iff (~core_ddrc_rstn)
   reg_ddrc_lpddr5 && dh_gs_rfm_en && dh_gs_mr_wr && !dh_gs_mr_type && (dh_gs_mr_data[15:8] == 57)
   |-> dh_gs_dis_mrrw_trfc;
endproperty : p_arfm_mrw_with_dis_mrrw_trfc

a_arfm_mrw_with_dis_mrrw_trfc: assert property (p_arfm_mrw_with_dis_mrrw_trfc)
   else $error("%m %t Changing LPDDR5 ARFM (MRW to MR57:OP[7:6] needs to be requested while MRCTRL0.dis_mrrw_trfc==1", $time);

// Check that MRCTRL0.mr_wr together with MRCTRL0.dis_mrrw_trfc=1 is only for LPDDR5 ARFM
property p_dis_mrrw_trfc_only_for_arfm;
   @(posedge clk) disable iff (~core_ddrc_rstn)
   dh_gs_dis_mrrw_trfc && dh_gs_mr_wr && !dh_gs_mr_type
   |-> reg_ddrc_lpddr5 && dh_gs_rfm_en && (dh_gs_mr_data[15:8] == 57);
endproperty : p_dis_mrrw_trfc_only_for_arfm

a_dis_mrrw_trfc_only_for_arfm: assert property (p_dis_mrrw_trfc_only_for_arfm)
   else $error("%m %t MRCTRL0.mr_wr together with MRCTRL0.dis_mrrw_trfc=1 is not for LPDDR5 ARFM", $time);

// Observe that changing LPDDR5 ARFM (MRW to MR57:OP[7:6] is requested in tRFC period
property p_arfm_mrw_requested_in_trfc;
   @(posedge clk) disable iff (~core_ddrc_rstn)
   reg_ddrc_lpddr5 && dh_gs_rfm_en && dh_gs_mr_wr && !dh_gs_mr_type && (dh_gs_mr_data[15:8] == 57)
   |-> (|t_rfc_min_timer_bitor);
endproperty : p_arfm_mrw_requested_in_trfc

cp_arfm_mrw_requested_in_trfc: cover property (p_arfm_mrw_requested_in_trfc);

// Observe that any other MRR/MRW/MPC is issued in tRFC period while MRCTRL0.dis_mrrw_trfc==0
property p_any_mrrw_issued_in_trfc;
   @(posedge clk) disable iff (~core_ddrc_rstn)
   gs_pi_op_is_load_mr_norm && !dh_gs_dis_mrrw_trfc
   |-> (|t_rfc_min_timer_bitor);
endproperty : p_any_mrrw_issued_in_trfc

cp_any_mrrw_issued_in_trfc: cover property (p_any_mrrw_issued_in_trfc);

//---------------------
// All assertions and cover-points related to the VPR related logic in GS
//---------------------


wire   any_vpr_timed_out;
assign any_vpr_timed_out = te_gs_any_vpr_timed_out || ih_gs_any_vpr_timed_out;


//----------------------
// Cover Points related to VPR logic
//----------------------

  // Write Queue Critical when there are expired VPR entries
  cp_wr_critical_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && wr_critical);

  // LPR Queue Critical when there are expired VPR entries
  cp_lpr_critical_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && rdlow_critical);

  // HPR Queue Critical when there are expired VPR entries
  cp_hpr_critical_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && rdhigh_critical);

  // Write mode when there are expired VPR entries
  cp_wr_mode_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && wr_mode);

  // Read mode when there are expired VPR entries
  cp_rd_mode_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && ~wr_mode);

  // Write collision is high when there are expired VPR entries
  cp_wr_flush_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && te_gs_wr_flush);

  // Read collision is high when there are expired VPR entries
  cp_rd_flush_w_expired_vpr :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out && te_gs_rd_flush);

  // expired_vpr when the HPR Q is in normal state
  cp_expired_vpr_when_q_is_normal :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out & (gs_dh_hpr_q_state == 2'b00)); // Normal state

  // Removing cp_expired_vpr_when_q_is_go_to_critial, go2critical state has been removed in change 4940964
  // expired_vpr when the HPR Q is in GO_TO_CRITICAL state
  //cp_expired_vpr_when_q_is_go_to_critial :
  //cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out & (gs_dh_hpr_q_state == 2'b01)); // Go_to_critical state

  // expired_vpr when the HPR Q is in critical state
  cp_expired_vpr_when_q_is_critical :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpr_timed_out & (gs_dh_hpr_q_state == 2'b10)); // critical state



//---------------------
// All assertions and cover-points related to the VPW related logic in GS
//---------------------


wire   any_vpw_timed_out;
assign any_vpw_timed_out = te_gs_any_vpw_timed_out || ih_gs_any_vpw_timed_out;


//----------------------
// Cover Points related to VPW logic
//----------------------

  // Write Queue Critical when there are expired VPW entries
  cp_wr_critical_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && wr_critical);

  // LPR Queue Critical when there are expired VPR entries
  cp_lpr_critical_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && rdlow_critical);

  // HPR Queue Critical when there are expired VPR entries
  cp_hpr_critical_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && rdhigh_critical);

  // Write mode when there are expired VPR entries
  cp_wr_mode_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && wr_mode);

  // Read mode when there are expired VPR entries
  cp_rd_mode_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && ~wr_mode);

  // Write collision is high when there are expired VPR entries
  cp_wr_flush_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && te_gs_wr_flush);

  // Read collision is high when there are expired VPR entries
  cp_rd_flush_w_expired_vpw :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out && te_gs_rd_flush);

  // expired_vpw when the WR Q is in normal state
  cp_expired_vpw_when_q_is_normal :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out & (gs_dh_w_q_state == 2'b00)); // Normal state

  // Removing cp_expired_vpw_when_q_is_go_to_critial, go2critical state has been removed in change 4940964
  // expired_vpw when the WR Q is in GO_TO_CRITICAL state
  //cp_expired_vpw_when_q_is_go_to_critial :
  //cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out & (gs_dh_w_q_state == 2'b01)); // Go_to_critical state

  // expired_vpw when the WR Q is in critical state
  cp_expired_vpw_when_q_is_critical :
  cover property (@(posedge clk) disable iff(!core_ddrc_rstn) any_vpw_timed_out & (gs_dh_w_q_state == 2'b10)); // critical state



endmodule  // gs (Global Scheduler)
`endif // `ifndef SYNTHESIS
`endif // SNPS_ASSERT_ON
