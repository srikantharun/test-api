//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_load_mr_hwffc_seq.sv#5 $
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

// -----------------------------------------------------------------------------
// -----------------------------------------------------------------------------
// Filename    :    gs_load_mr_hwffc_seq.v
// Description :    Auto MRW sequencer for Hardware Fast Frequency Change (HWFFC)
//                  This module is instantiated in gs_load_mr, requests load MR
//                  commands for HWFFC based on a state machine.
// -----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "ts/DWC_ddrctl_ts_if.svh"


module gs_load_mr_hwffc_seq 
import DWC_ddrctl_reg_pkg::*;
#(
//------------------------------- PARAMETERS -----------------------------------
     parameter  MRW_A_BITS          = `MEMC_PAGE_BITS
    ,parameter  TIMER_BITS                 = 1
    ,parameter  NUM_RANKS                  = 1
)
(
//--------------------------- INPUTS AND OUTPUTS -------------------------------
     input                          clk                             // clock
    ,input                          rstn                            // asynchronous reset

    ,input      [15:0]              i_mr1_data                      // INIT3.mr
    ,input      [15:0]              i_mr2_data                      // INIT3.emr
    ,input      [15:0]              i_mr3_data                      // INIT4.emr2
    ,input      [15:0]              i_mr11_data                     // INIT6.mr4
    ,input      [15:0]              i_mr12_data                     // INIT6.mr5
    ,input      [15:0]              i_mr13_data                     // INIT4.emr3
    ,input      [15:0]              i_mr14_data                     // INIT7.mr6
    ,input      [15:0]              i_mr22_data                     // INIT7.mr22
    ,input      [NUM_RANKS-1:0]     dh_gs_active_ranks              // populated DRAM ranks
    ,input      [T_MR_WIDTH-1:0]    i_t_mr                          // delay from load MR to other valid commands
    ,input      [T_VRCG_ENABLE_WIDTH-1:0]  i_t_vrcg_enable          // tVRCG_ENABLE
    ,input      [T_VRCG_DISABLE_WIDTH-1:0] i_t_vrcg_disable         // tVRCG_DISABLE
    ,input      [T_ZQ_RESET_NOP_WIDTH-1:0] i_t_zq_reset_nop         // tZQRESET
    ,input      [T_ZQ_STOP_WIDTH-1:0]      i_t_zq_stop              // tZQSTOP
    ,input                          i_skip_mrw_odtvref              // skip MRW to MR11/12/14/22

    ,input      [3:0]               i_mr_update_start               // start auto load MR sequence (pulse)
    ,output                         o_mr_update_done                // auto load MR sequence finished (pulse)
    ,input                          i_curr_fsp                      // current FSP
    ,input                          i_curr_vrcg                     // current VRCG

    ,input      [1:0]               i_zq_interval                   // HWFFCCTL.zq_interval
    ,input                          i_hwffc_mode                    // indicate HWFFC mode 0:legacy 1:new

    ,output                         o_load_mr_req                   // request for load MR
    ,input                          i_load_mr_ack                   // acknowledge of load MR
    ,output reg [MRW_A_BITS-1:0]    o_load_mr_a                     // MR address and data
    ,output logic[NUM_RANKS-1:0]    o_load_mr_rank                  // MR rank
    ,output     [TIMER_BITS-1:0]    o_nop_timer_value               // initial value of external NOP timer
    ,output                         o_st_mr_vrcg                    // state flag of MR13 VRCG0
);

//---------------------------- LOCAL PARAMETERS --------------------------------
// internal states
localparam  ST_IDLE             = 4'b0000;      // Idle
localparam  ST_MR13_FSPWR       = 4'b0001;      // Before SRPD: send MRW to MR13 to invert FSP-WR (OP[6])
localparam  ST_MR1              = 4'b0010;      // Before SRPD: send MRW to MR1
localparam  ST_MR2              = 4'b0011;      // Before SRPD: send MRW to MR2
localparam  ST_MR3              = 4'b0100;      // Before SRPD: send MRW to MR3
localparam  ST_MR11             = 4'b0101;      // Before SRPD: send MRW to MR11
localparam  ST_MR12             = 4'b0110;      // Before SRPD: send MRW to MR12
localparam  ST_MR14             = 4'b0111;      // Before SRPD: send MRW to MR14
localparam  ST_MR22             = 4'b1000;      // Before SRPD: send MRW to MR11
localparam  ST_MR13_FSPOP       = 4'b1001;      // Before SRPD: send MRW to MR13 to set VRCG (OP[3]) to 1
localparam  ST_MR13_VRCG0       = 4'b1010;      // After SRPD:  send MRW to MR13 to set VRCG (OP[3]) to 0
localparam  ST_MR28_ZQRESET     = 4'b1101;      // Before DVFSQ High-to-Low: send MRW to MR28 to set ZQ_Reset (OP[0]) to 1
localparam  ST_MR28_ZQSTOP      = 4'b1011;      // Before SRPD: send MRW to MR28 to set ZQ_Stop (OP[1]) to 1
localparam  ST_MR28_ZQSTART     = 4'b1100;      // After SRPD:  send MRW to MR28 to set ZQ_Stop (OP[1]) to 0
localparam  ST_MRW_SEQUENCER_DLY= 4'b1110;      // Before SRPD: send MRW
localparam  ST_MRW_SEQUENCER    = 4'b1111;      // Before SRPD: send MRW


//------------------------------ WIRES AND REGISTERS ---------------------------
reg     [3:0]                   w_next_state;
reg     [3:0]                   r_curr_state;

wire    [7:0]                   w_mr13_fspwr_data;
wire    [7:0]                   w_mr13_fspop_data;
wire    [7:0]                   w_mr13_vrcg0_data;

wire    [7:0]                   w_mr28_zqreset_data;
wire    [7:0]                   w_mr28_zqstop_data;
wire    [7:0]                   w_mr28_zqstart_data;



//-------------------------------- MAIN CODE BLOCK -----------------------------
//------------------------------------------
//  State machine
//------------------------------------------
always @(*) begin
    casez (r_curr_state)
        ST_IDLE:
            w_next_state    = i_hwffc_mode ? 
                             (
                              (i_mr_update_start[0]) ?                      ST_MR28_ZQSTOP
                            : (i_mr_update_start[1]) ?                      ST_MR28_ZQSTART
                            : (i_mr_update_start[2]) ?                      ST_MR28_ZQRESET
                            :                                               ST_IDLE
                            ) : (
                              (i_mr_update_start[0]) ?                      ST_MR13_FSPWR
                            : (i_mr_update_start[1]) ?                      ST_MR13_VRCG0
                            :                                               ST_IDLE
                            ) ;
        ST_MR13_FSPWR:
            w_next_state    = i_load_mr_ack ? ST_MR1 : ST_MR13_FSPWR;
        ST_MR1:
            w_next_state    = i_load_mr_ack ? ST_MR2 : ST_MR1;
        ST_MR2:
            w_next_state    = i_load_mr_ack ? ST_MR3 : ST_MR2;
        ST_MR3:
            w_next_state    = i_load_mr_ack ? (i_skip_mrw_odtvref ? ST_MR13_FSPOP : ST_MR11) : ST_MR3;
        ST_MR11:
            w_next_state    = i_load_mr_ack ? ST_MR12 : ST_MR11;
        ST_MR12:
            w_next_state    = i_load_mr_ack ? ST_MR14 : ST_MR12;
        ST_MR14:
            w_next_state    = i_load_mr_ack ? ST_MR22 : ST_MR14;
        ST_MR22:
            w_next_state    = i_load_mr_ack ? ST_MR13_FSPOP : ST_MR22;
        ST_MR13_FSPOP:
            w_next_state    = i_load_mr_ack ? ST_IDLE : ST_MR13_FSPOP;
        ST_MR13_VRCG0:
            w_next_state    = i_load_mr_ack ? ST_IDLE : ST_MR13_VRCG0;
        ST_MR28_ZQRESET:
            w_next_state    = i_load_mr_ack ? ST_MR28_ZQSTOP : ST_MR28_ZQRESET;
        ST_MR28_ZQSTOP:
            w_next_state    = i_load_mr_ack ? ST_IDLE : ST_MR28_ZQSTOP;
        ST_MR28_ZQSTART:
            w_next_state    = i_load_mr_ack ? ST_IDLE : ST_MR28_ZQSTART;
        default:
            w_next_state    = ST_IDLE;
    endcase
end

always @(posedge clk or negedge rstn) begin
    if (!rstn) begin
        r_curr_state <= ST_IDLE;
    end else begin
        r_curr_state <= w_next_state;
    end
end

//------------------------------------------
//  Request for load MR
//------------------------------------------
assign o_load_mr_req    = (r_curr_state != ST_IDLE) && (r_curr_state != ST_MRW_SEQUENCER_DLY);
assign o_mr_update_done = (r_curr_state != ST_IDLE) && (w_next_state == ST_IDLE);

// MR13 data                   -- FSP-OP -- -- FSP-WR --                   -- VRCG --
assign w_mr13_fspwr_data    = { i_curr_fsp, ~i_curr_fsp, i_mr13_data[5:4], i_curr_vrcg, i_mr13_data[2:0]};
assign w_mr13_fspop_data    = {~i_curr_fsp, ~i_curr_fsp, i_mr13_data[5:4], 1'b1,        i_mr13_data[2:0]};
assign w_mr13_vrcg0_data    = { i_curr_fsp,  i_curr_fsp, i_mr13_data[5:4], 1'b0,        i_mr13_data[2:0]};

// MR28 data                    RFU    Mode  RFU   Interval       Stop  Reset
assign w_mr28_zqreset_data  = { 2'b00, 1'b0, 1'b0, i_zq_interval, 1'b0, 1'b1};  // ZQReset=1 resets ZQStop to '0' as its functionality so writing '0' here along with reset.
assign w_mr28_zqstop_data   = { 2'b00, 1'b0, 1'b0, i_zq_interval, 1'b1, 1'b0};
assign w_mr28_zqstart_data  = { 2'b00, 1'b0, 1'b0, i_zq_interval, 1'b0, 1'b0};

always @(*) begin
    o_load_mr_a = {MRW_A_BITS{1'b0}};

    casez (r_curr_state)
        ST_MR1:
            o_load_mr_a[15:0] = {8'd1, i_mr1_data[7:0]};
        ST_MR2:
            o_load_mr_a[15:0] = {8'd2, i_mr2_data[7:0]};
        ST_MR3:
            o_load_mr_a[15:0] = {8'd3, i_mr3_data[7:0]};
        ST_MR11:
            o_load_mr_a[15:0] = {8'd11, i_mr11_data[7:0]};
        ST_MR12:
            o_load_mr_a[15:0] = {8'd12, i_mr12_data[7:0]};
        ST_MR13_FSPWR:
            o_load_mr_a[15:0] = {8'd13, w_mr13_fspwr_data[7:0]};
        ST_MR13_FSPOP:
            o_load_mr_a[15:0] = {8'd13, w_mr13_fspop_data[7:0]};
        ST_MR13_VRCG0:
            o_load_mr_a[15:0] = {8'd13, w_mr13_vrcg0_data[7:0]};
        ST_MR14:
            o_load_mr_a[15:0] = {8'd14, i_mr14_data[7:0]};
        ST_MR22:
            o_load_mr_a[15:0] = {8'd22, i_mr22_data[7:0]};
        ST_MR28_ZQRESET:
            o_load_mr_a[15:0] = {8'd28, w_mr28_zqreset_data[7:0]};
        ST_MR28_ZQSTOP:
            o_load_mr_a[15:0] = {8'd28, w_mr28_zqstop_data[7:0]};
        ST_MR28_ZQSTART:
            o_load_mr_a[15:0] = {8'd28, w_mr28_zqstart_data[7:0]};
        default:
            o_load_mr_a[15:0] = 16'h0000;
    endcase
end

always_comb begin
        o_load_mr_rank = dh_gs_active_ranks;
end

// LPDDR4 MRW command is 4-cycles length, thus do +2 in FR1 or +1 in FR2
//
//  DFI clock   _|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|_|~|
//  OP is MRW   _____|~~~|__________________________________________________________
//                       |<----------------------------->| t_mwr+2
//  OP is ANY   _____________________________________|~~~|__________________________
//  DFI command              X_MRW-1_X_MRW-2_X               X__ANY__X
//                                           |<--------------------->| t_mwr
//
reg [$bits(o_nop_timer_value):0]    o_nop_timer_value_wider;
always @(*) begin
    if ((r_curr_state == ST_MR13_FSPOP) && !i_curr_vrcg) begin // after changing VRCG from 0 to 1
        // load Max(t_vrcg_enable, t_mrs_to_other), basically t_vrcg_enable should be greater
        o_nop_timer_value_wider   = (({{($bits(i_t_vrcg_enable)-$bits(i_t_mr)){1'b0}}, i_t_mr} >  i_t_vrcg_enable) ? 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_mr)-1){1'b0}}, i_t_mr} : 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_vrcg_enable)-1){1'b0}}, i_t_vrcg_enable})
                                    + {{($bits(o_nop_timer_value_wider)-2){1'b0}},2'b10};
    end else if (r_curr_state == ST_MR13_VRCG0) begin // after changing VRCG from 1 to 0
        // load Max(t_vrcg_disable, t_mrs_to_other), basically t_vrcg_disable should be greater
        o_nop_timer_value_wider   = (({{($bits(i_t_vrcg_enable)-$bits(i_t_mr)){1'b0}}, i_t_mr} > i_t_vrcg_disable) ? 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_mr)-1){1'b0}}, i_t_mr} : 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_vrcg_disable)-1){1'b0}},i_t_vrcg_disable})
                                    + {{($bits(o_nop_timer_value_wider)-2){1'b0}},2'b10};
    end else if (r_curr_state == ST_MR28_ZQRESET) begin // before DVFSQ High-to-Low
        // load Max(t_zq_reset_nop, t_mrs_to_other)
        o_nop_timer_value_wider   = (({{($bits(i_t_zq_reset_nop)-$bits(i_t_mr)){1'b0}}, i_t_mr} > i_t_zq_reset_nop) ? 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_mr)-1){1'b0}}, i_t_mr} : 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_zq_reset_nop)-1){1'b0}},i_t_zq_reset_nop})
                                    + {{($bits(o_nop_timer_value_wider)-2){1'b0}},2'b10};
    end else if (r_curr_state == ST_MR28_ZQSTOP) begin // HWLP driven LP2 enter or before DVFSQ High-to-Low
        // load Max(t_zq_stop, t_mrs_to_other)
        o_nop_timer_value_wider   = (({{($bits(i_t_zq_stop)-$bits(i_t_mr)){1'b0}}, i_t_mr} > i_t_zq_stop) ? 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_mr)-1){1'b0}}, i_t_mr} : 
                                                                                              {{($bits(o_nop_timer_value_wider)-$bits(i_t_zq_stop)-1){1'b0}},i_t_zq_stop})
                                    + {{($bits(o_nop_timer_value_wider)-2){1'b0}},2'b10};
    end else if (r_curr_state != ST_IDLE) begin
        o_nop_timer_value_wider   = {{($bits(o_nop_timer_value_wider)-$bits(i_t_mr)-1){1'b0}}, i_t_mr} + {{($bits(o_nop_timer_value_wider)-2){1'b0}},2'b10};
    end else begin
        o_nop_timer_value_wider   = {$bits(o_nop_timer_value_wider){1'b0}};
    end
end
assign o_nop_timer_value = o_nop_timer_value_wider[$bits(o_nop_timer_value)-1:0];

// MRW for MR13 VRCG0 state flag
assign o_st_mr_vrcg = (r_curr_state == ST_MR13_VRCG0);

`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
//------------------------------------------
//  Assertions
//------------------------------------------
// Check that HWFFC MR update is requested when the load MR sequence is idle and i_mr_update_start is onehot. Exception: i_mr_update_start[3] can be flaged with [2] or [1]
a_hwffc_mr_update_starts_in_idle_state : assert property (
    @ (posedge clk) disable iff (!rstn)
    (|i_mr_update_start) |-> (r_curr_state == ST_IDLE) && ($countones(i_mr_update_start)==1 || (i_mr_update_start[3] && $countones(i_mr_update_start & 4'b1110)==2))

) else $error ("[%t][%m] ERROR: HWFFC MR update has been requested when the load MR sequence is busy or encoding is invalid", $time);

// Check that an acknowledge of HWFFC load MR is asserted when a load MR is requested and 1-cycle pulse
a_hwffc_load_mr_handshaking : assert property (
    @ (posedge clk) disable iff (!rstn)
    // the acknowledge must be asserted when load MR is requested, and 1-cycle pulse
    $rose(i_load_mr_ack) |-> (r_curr_state != ST_IDLE) ##1 !i_load_mr_ack
) else $error ("[%t][%m] ERROR: HWFFC load MR handshaking has been performed uncorrectly", $time);

localparam CATEGORY = 5; // Allows groups of assertions to be enabled/disabled at the same time

// o_nop_timer_value overflow
assert_never #(0, 0, "o_nop_timer_value overflow", CATEGORY) a_o_nop_timer_value_overflow
  (clk, rstn, (o_nop_timer_value_wider[$bits(o_nop_timer_value)]==1'b1));

    
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
endmodule

