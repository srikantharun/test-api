// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// reset_gen asserions. Bind to module soc_mgmt_reset_gen.
//
module soc_mgmt_reset_gen_assertions #(
  parameter int unsigned NUM_RESETS_RSTGEN = 3,
  parameter int unsigned STAGE_NUM         = 3
)(
  input  wire                           i_clk                 ,
  input  wire                           i_por_rst_n           ,
  input  wire [                  11:0]  ao_stretch_delay      ,
  input  wire [                  11:0]  dmi_stretch_delay     ,
  input  wire [                  11:0]  global_stretch_delay  ,
  input  wire                           o_ao_rst_ip_n         ,
  input  wire                           o_dmi_rst_ip_n        ,
  input  wire                           o_global_rst_ip_n     ,
  input  wire [STAGE_NUM         -1:0]  rst_stage             ,
  input  logic                          i_test_mode           ,
  input  logic                          i_dft_clk_rst_ctrl    ,
  input  wire  [NUM_RESETS_RSTGEN-1:0]  i_test_rst_n          ,
  input  wire                           i_dmi_rst_n           ,
  input  wire                           i_rot_rst_n           ,
  input  wire                           i_wdt_rst_n           ,
  input  wire                           i_mbist_rst_n         ,
  input  wire                           i_debug_rst_n         ,
  input  wire                           i_ao_rst_req_n        ,
  input  logic                          i_ao_rst_ip_ack       ,
  input  logic                          o_dmi_rst_ack_n       ,
  input  logic                          i_dmi_rst_ip_ack      ,
  input  wire                           i_global_rst_req_n    ,
  input  logic                          i_global_rst_ip_ack   ,
  input  logic [3                   :0] ppmu_fsm_state_q      ,
  input  logic                          i_dmi_sw_rst_n        ,
  input  logic                          i_global_sw_rst_n
);

import uvm_pkg::*;
`include "uvm_macros.svh"

localparam int unsigned STRETCH_DELAY = 10;
localparam int unsigned DBNC_DELAY    =  2;

localparam int unsigned STAGE_RESET_DELAY   =                     STRETCH_DELAY + STAGE_NUM + 1;
localparam int unsigned S1_RESET_DELAY      = STAGE_RESET_DELAY + STRETCH_DELAY + STAGE_NUM + 1;
localparam int unsigned S2_RESET_DELAY      =    S1_RESET_DELAY + STRETCH_DELAY + STAGE_NUM + 1;

localparam int unsigned S0_DBNC_RESET_DELAY = STAGE_RESET_DELAY + DBNC_DELAY  + STAGE_NUM;
localparam int unsigned S1_DBNC_RESET_DELAY = S1_RESET_DELAY + DBNC_DELAY + STAGE_NUM;
localparam int unsigned S2_DBNC_RESET_DELAY = S2_RESET_DELAY + DBNC_DELAY + STAGE_NUM;


// Message reported when assertion fails
`define ASRT_FAIL_MSG `uvm_error("ASSERTION_ERROR", "ASSERTION FAILED.")

// Package to suport varaible delay sequences
import sva_delay_repeat_pkg::*;

default clocking @(posedge i_clk); endclocking

//==============================================================================
// Properties
// Signal ia not unknown
property p_sig_not_unknown(sig);
  (!$isunknown(sig));
endproperty

// Falling edge of reset. All reset outputs should be set asynchronously.
property p_rst_n_fall ( i_rst_n, o_rst_n );
  $fell(i_rst_n) |-> $fell(o_rst_n);
endproperty

// Rising edge of reset. All reset output should be high after stretch delay
// + resync. Add a tolerance window for synchronizer
property p_rst_n_win_rise_s0 ( i_rst_n, o_rst_n);
  $rose(i_rst_n) |-> ##[STAGE_RESET_DELAY-1:STAGE_RESET_DELAY+2] $rose(o_rst_n);
endproperty

property p_rst_n_win_rise_s1 ( i_rst_n, o_rst_n);
  $rose(i_rst_n) |-> ##[S1_RESET_DELAY-1:S1_RESET_DELAY+2] $rose(o_rst_n);
endproperty

property p_rst_n_win_rise_s2 ( i_rst_n, o_rst_n);
  $rose(i_rst_n) |-> ##[S2_RESET_DELAY-2:S2_RESET_DELAY+4] $rose(o_rst_n);
endproperty

property p_rst_n_sb_win_rise_s0 ( i_rst_n, o_rst_n);
  disable iff (!i_por_rst_n)
  $rose(i_rst_n) |-> ##[STAGE_RESET_DELAY-1:STAGE_RESET_DELAY+2] $rose(o_rst_n);
endproperty

property p_rst_n_sb_win_rise_s1 ( i_rst_n, o_rst_n);
  disable iff (!i_por_rst_n)
  $rose(i_rst_n) |-> ##[S1_RESET_DELAY-1:S1_RESET_DELAY+2] $rose(o_rst_n);
endproperty

property p_rst_n_sb_win_rise_s2 ( i_rst_n, o_rst_n);
  disable iff (!i_por_rst_n)
  $rose(i_rst_n) |-> ##[S2_RESET_DELAY-1:S2_RESET_DELAY+2] $rose(o_rst_n);
endproperty

// Falling edge of reset. Delayed with a debounce.
property p_dbnc_rst_n_fall (i_rst_n, o_rst_n);
  disable iff (!i_por_rst_n)
  $fell(i_rst_n) |-> ##[STAGE_NUM-1:STAGE_NUM+1] $fell(o_rst_n);
endproperty

// Rising edge of reset. Delayed with a debounce.
// use a window delay. in this case reset out delay will be different if reset after por are cleared at same time
property p_dbnc_rst_n_rise_s0 (i_rst_n, o_rst_n);
  // min delay is stretch delay default + stagen_num + 1
  // max delay is stretch delay default + stagen_num + dbnc delay
  $rose(i_rst_n) |-> ##[STAGE_RESET_DELAY:S0_DBNC_RESET_DELAY] $rose(o_rst_n);
endproperty

// increase delay for subsequent stages.
property p_dbnc_rst_n_rise_s1 (i_rst_n, o_rst_n);
  // min delay is stretch delay default + stagen_num + 1
  // max delay is stretch delay default + stagen_num + dbnc delay
  $rose(i_rst_n) |-> ##[S1_RESET_DELAY:S1_DBNC_RESET_DELAY+1] $rose(o_rst_n);
endproperty

property p_dbnc_rst_n_rise_s2 (i_rst_n, o_rst_n);
  // min delay is 2*stretch delay default + stagen_num + 1
  // max delay is 2*stretch delay default + stagen_num + dbnc delay
  $rose(i_rst_n) |-> ##[S2_RESET_DELAY-1:S2_DBNC_RESET_DELAY+2] $rose(o_rst_n);
endproperty

property p_sw_rst_n_rise ( i_rst_n, o_rst_n );
  disable iff (!i_por_rst_n)
  $rose(i_rst_n) |-> $rose(o_rst_n);
endproperty

property p_sw_rst_stage_stable(i_rst_n, o_rst_n);
  disable iff (!i_por_rst_n)
  $changed(i_rst_n) |-> $stable(o_rst_n);
endproperty

// reset fall and enable rise
property p_en_rise (i_rst_n, i_en);
  disable iff (!i_por_rst_n)
  $fell(i_rst_n) |-> $rose(i_en);
endproperty

property p_noc_rise(i_rst_n, o_rst_n, delay);
  disable iff (!i_por_rst_n)
  $rose(i_rst_n) |-> dynamic_delay(delay) ##0 $rose(o_rst_n);
endproperty

//==============================================================================
// Assertions
// Check That POR controls all resets
// STAGE0 - AO
a_ao_por_fall    : assert property ( p_rst_n_fall       (i_por_rst_n, rst_stage[0] )) else `ASRT_FAIL_MSG
a_ao_por_rise    : assert property ( p_rst_n_win_rise_s0(i_por_rst_n, rst_stage[0] )) else `ASRT_FAIL_MSG
a_ao_por_ip_fall : assert property ( p_rst_n_fall       (i_por_rst_n, o_ao_rst_ip_n)) else `ASRT_FAIL_MSG
a_ao_por_ip_rise : assert property ( p_rst_n_win_rise_s0(i_por_rst_n, o_ao_rst_ip_n)) else `ASRT_FAIL_MSG

// STAGE1 - DEBUG
a_debug_fall    : assert property ( p_rst_n_fall       (i_por_rst_n, rst_stage[1]  )) else `ASRT_FAIL_MSG
a_debug_rise    : assert property ( p_rst_n_win_rise_s1(i_por_rst_n, rst_stage[1]  )) else `ASRT_FAIL_MSG
a_debug_ip_fall : assert property ( p_rst_n_fall       (i_por_rst_n, o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG
a_debug_ip_rise : assert property ( p_rst_n_win_rise_s1(i_por_rst_n, o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG

// STAGE2 - GLOBAL
a_global_fall    : assert property ( p_rst_n_fall       (i_por_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_global_rise    : assert property ( p_rst_n_win_rise_s2(i_por_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_global_ip_fall : assert property ( p_rst_n_fall       (i_por_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_global_ip_rise : assert property ( p_rst_n_win_rise_s2(i_por_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG

// STAGE0 -> STAGE1
a_stage0_stage1_fall     : assert property  ( p_rst_n_fall          (rst_stage[0], rst_stage[1]  )) else `ASRT_FAIL_MSG
a_stage0_stage1_rise     : assert property  ( p_rst_n_sb_win_rise_s0(rst_stage[0], rst_stage[1]  )) else `ASRT_FAIL_MSG
a_ip_stage0_stage1_fall  : assert property  ( p_rst_n_fall          (rst_stage[0], o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG
a_ip_stage0_stage1_rise  : assert property  ( p_rst_n_sb_win_rise_s0(rst_stage[0], o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG

// STAGE0 -> STAGE2
a_stage0_stage2_fall     : assert property  ( p_rst_n_fall          (rst_stage[0], rst_stage[2]     )) else `ASRT_FAIL_MSG
a_stage0_stage2_rise     : assert property  ( p_rst_n_sb_win_rise_s1(rst_stage[0], rst_stage[2]     )) else `ASRT_FAIL_MSG
a_ip_stage0_stage2_fall  : assert property  ( p_rst_n_fall          (rst_stage[0], o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_ip_stage0_stage2_rise  : assert property  ( p_rst_n_sb_win_rise_s1(rst_stage[0], o_global_rst_ip_n)) else `ASRT_FAIL_MSG

//==============================================================================
// Stage 1
// i_dmi_rst_n
// Sets reset for stage 1 and 2 only.
a_dmi_fall       : assert property ( p_rst_n_fall          (i_dmi_rst_n, rst_stage[1]  )) else `ASRT_FAIL_MSG
a_dmi_rise       : assert property ( p_rst_n_sb_win_rise_s0(i_dmi_rst_n, rst_stage[1]  )) else `ASRT_FAIL_MSG
a_dmi_ip_fall    : assert property ( p_rst_n_fall          (i_dmi_rst_n, o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG
a_dmi_ip_rise    : assert property ( p_rst_n_sb_win_rise_s0(i_dmi_rst_n, o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG

// will also reset stage 2
a_dmi_s2_fall    : assert property ( p_rst_n_fall          (i_dmi_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_dmi_s2_rise    : assert property ( p_rst_n_sb_win_rise_s1(i_dmi_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_dmi_s2_ip_fall : assert property ( p_rst_n_fall          (i_dmi_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_dmi_s2_ip_rise : assert property ( p_rst_n_sb_win_rise_s1(i_dmi_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG

a_kse3_jtag_fall    : assert property ( p_rst_n_fall          (i_rot_rst_n, rst_stage[1]  )) else `ASRT_FAIL_MSG
a_kse3_jtag_rise    : assert property ( p_rst_n_sb_win_rise_s0(i_rot_rst_n, rst_stage[1]  )) else `ASRT_FAIL_MSG
a_kse3_jtag_ip_fall : assert property ( p_rst_n_fall          (i_rot_rst_n, o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG
a_kse3_jtag_ip_rise : assert property ( p_rst_n_sb_win_rise_s0(i_rot_rst_n, o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG

a_mbist_fall        : assert property ( p_rst_n_fall          (i_mbist_rst_n , rst_stage[1]  )) else `ASRT_FAIL_MSG
a_mbist_rise        : assert property ( p_rst_n_sb_win_rise_s0(i_mbist_rst_n , rst_stage[1]  )) else `ASRT_FAIL_MSG
a_mbist_ip_fall     : assert property ( p_rst_n_fall          (i_mbist_rst_n , o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG
a_mbist_ip_rise     : assert property ( p_rst_n_sb_win_rise_s0(i_mbist_rst_n , o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG

// software reset
// only sets ip rst_n with no delay
// the stage outpurt should not be affected by sw reset
a_dmi_sw_stage_stable: assert property ( p_sw_rst_stage_stable(i_dmi_sw_rst_n , rst_stage[1]  )) else `ASRT_FAIL_MSG
a_dmi_sw_ip_fall     : assert property ( p_rst_n_fall         (i_dmi_sw_rst_n , o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG
a_dmi_sw_ip_rise     : assert property ( p_sw_rst_n_rise      (i_dmi_sw_rst_n , o_dmi_rst_ip_n)) else `ASRT_FAIL_MSG

// will also reset stage 2
a_kse3_jtag_s2_fall    : assert property ( p_rst_n_fall          (i_rot_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_kse3_jtag_s2_rise    : assert property ( p_rst_n_sb_win_rise_s1(i_rot_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_kse3_jtag_s2_ip_fall : assert property ( p_rst_n_fall          (i_rot_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_kse3_jtag_s2_ip_rise : assert property ( p_rst_n_sb_win_rise_s1(i_rot_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG

a_mbist_s2_fall     : assert property ( p_rst_n_fall          (i_mbist_rst_n , rst_stage[2]     )) else `ASRT_FAIL_MSG
a_mbist_s2_rise     : assert property ( p_rst_n_sb_win_rise_s1(i_mbist_rst_n , rst_stage[2]     )) else `ASRT_FAIL_MSG
a_mbist_s2_ip_fall  : assert property ( p_rst_n_fall          (i_mbist_rst_n , o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_mbist_s2_ip_rise  : assert property ( p_rst_n_sb_win_rise_s1(i_mbist_rst_n , o_global_rst_ip_n)) else `ASRT_FAIL_MSG
// STAGE1 -> STAGE2
a_stage1_stage2_fall     : assert property  ( p_rst_n_fall          (rst_stage[1], rst_stage[2]     )) else `ASRT_FAIL_MSG
a_stage1_stage2_rise     : assert property  ( p_rst_n_sb_win_rise_s0(rst_stage[1], rst_stage[2]     )) else `ASRT_FAIL_MSG
a_ip_stage1_stage2_fall  : assert property  ( p_rst_n_fall          (rst_stage[1], o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_ip_stage1_stage2_rise  : assert property  ( p_rst_n_sb_win_rise_s0(rst_stage[1], o_global_rst_ip_n)) else `ASRT_FAIL_MSG

//==============================================================================
// Stage 2
// debug reset
a_debug_s2_fall    : assert property ( p_rst_n_fall          (i_debug_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_debug_s2_rise    : assert property ( p_rst_n_sb_win_rise_s0(i_debug_rst_n, rst_stage[2]     )) else `ASRT_FAIL_MSG
a_debug_s2_ip_fall : assert property ( p_rst_n_fall          (i_debug_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_debug_s2_ip_rise : assert property ( p_rst_n_sb_win_rise_s0(i_debug_rst_n, o_global_rst_ip_n)) else `ASRT_FAIL_MSG

a_wdt_s2_fall      : assert property ( p_rst_n_fall          (i_wdt_rst_n  , rst_stage[2]     )) else `ASRT_FAIL_MSG
a_wdt_s2_rise      : assert property ( p_rst_n_sb_win_rise_s0(i_wdt_rst_n  , rst_stage[2]     )) else `ASRT_FAIL_MSG
a_wdt_s2_ip_fall   : assert property ( p_rst_n_fall          (i_wdt_rst_n  , o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_wdt_s2_ip_rise   : assert property ( p_rst_n_sb_win_rise_s0(i_wdt_rst_n  , o_global_rst_ip_n)) else `ASRT_FAIL_MSG

// software reset
// only sets ip rst_n with no delay
// the stage outpurt should not be affected by sw reset
a_global_sw_stage_stable: assert property ( p_sw_rst_stage_stable(i_global_sw_rst_n , rst_stage[2]     )) else `ASRT_FAIL_MSG
a_global_sw_ip_fall     : assert property ( p_rst_n_fall         (i_global_sw_rst_n , o_global_rst_ip_n)) else `ASRT_FAIL_MSG
a_global_sw_ip_rise     : assert property ( p_sw_rst_n_rise      (i_global_sw_rst_n , o_global_rst_ip_n)) else `ASRT_FAIL_MSG

//==============================================================================
// Coverage for assertions

//==============================================================================
// signal not unknown. Check all inputs
a_i_por_rst_n          : assert property(p_sig_not_unknown(i_por_rst_n         )) else `ASRT_FAIL_MSG
a_i_test_mode          : assert property(p_sig_not_unknown(i_test_mode         )) else `ASRT_FAIL_MSG
a_i_dft_clk_rst_ctrl   : assert property(p_sig_not_unknown(i_dft_clk_rst_ctrl  )) else `ASRT_FAIL_MSG
a_i_test_rst_n         : assert property(p_sig_not_unknown(i_test_rst_n        )) else `ASRT_FAIL_MSG
a_i_dmi_rst_n          : assert property(p_sig_not_unknown(i_dmi_rst_n         )) else `ASRT_FAIL_MSG
a_i_rot_rst_n          : assert property(p_sig_not_unknown(i_rot_rst_n   )) else `ASRT_FAIL_MSG
a_i_wdt_rst_n          : assert property(p_sig_not_unknown(i_wdt_rst_n         )) else `ASRT_FAIL_MSG
a_i_mbist_rst_n        : assert property(p_sig_not_unknown(i_mbist_rst_n       )) else `ASRT_FAIL_MSG
a_i_debug_rst_n        : assert property(p_sig_not_unknown(i_debug_rst_n       )) else `ASRT_FAIL_MSG
a_i_ao_rst_req_n       : assert property(p_sig_not_unknown(i_ao_rst_req_n      )) else `ASRT_FAIL_MSG
a_i_ao_rst_ip_ack      : assert property(p_sig_not_unknown(i_ao_rst_ip_ack     )) else `ASRT_FAIL_MSG
a_i_dmi_rst_ip_ack     : assert property(p_sig_not_unknown(i_dmi_rst_ip_ack    )) else `ASRT_FAIL_MSG
a_i_global_rst_req_n   : assert property(p_sig_not_unknown(i_global_rst_req_n  )) else `ASRT_FAIL_MSG
a_i_global_rst_ip_ack  : assert property(p_sig_not_unknown(i_global_rst_ip_ack )) else `ASRT_FAIL_MSG

endmodule
