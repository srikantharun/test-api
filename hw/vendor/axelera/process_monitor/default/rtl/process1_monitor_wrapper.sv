// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: process monitor 1 behavioral model.
//
// Authors: Manuel Oliveira

module process1_monitor_wrapper
import process1_monitor_pkg::*;
(
  // JTAG
  input   wire                                         tcki,
  input   wire                                         trsti,

  input	  wire                                         i_clk,
  input   wire                                         i_enable,

  input   wire                                         i_ref_clk,

  input   logic                     [PR1_TARGET_W-1:0] i_target,

  input   logic                   [PR1_NB_MONITOR-1:0] i_use_ro,

  output  logic                                        o_valid,
  output  logic [PR1_NB_MONITOR-1:0] [PR1_COUNT_W-1:0] o_count
);
  wire                       monitor_clk;
  logic                      jtag_mode;
  logic                      jtag_enable;
  logic   [PR1_TARGET_W-1:0] jtag_target;
  logic [PR1_NB_MONITOR-1:0] jtag_use_ro;
  logic                      mux_enable;
  logic   [PR1_TARGET_W-1:0] mux_target;
  logic [PR1_NB_MONITOR-1:0] mux_use_ro;

  always_comb mux_enable = jtag_mode ? jtag_enable : i_enable;
  always_comb mux_target = jtag_mode ? jtag_target : i_target;
  always_comb mux_use_ro = jtag_mode ? jtag_use_ro : i_use_ro;

  axe_tcl_clk_mux2 u_clk_mux2 (
    .i_clk0(i_clk),
    .i_clk1(tcki),
    .i_sel (jtag_mode),
    .o_clk (monitor_clk)
  );

  process1_monitor u_process1_monitor (
    .clock    (monitor_clk),
    .enable   (mux_enable),
    .ref_clock(i_ref_clk),
    .target   (mux_target),
    .use_ro   (mux_use_ro),
    .valid    (o_valid),
    .count_0  (o_count[0]),
    .count_1  (o_count[1]),
    .count_2  (o_count[2]),
    .count_3  (o_count[3]),
    .count_4  (o_count[4]),
    .count_5  (o_count[5]),
    .count_6  (o_count[6]),
    .count_7  (o_count[7]),
    .count_8  (o_count[8]),
    .count_9  (o_count[9]),
    .count_10 (o_count[10]),
    .count_11 (o_count[11]),
    .count_12 (o_count[12]),
    .count_13 (o_count[13])
  );

  process1_monitor_jtag_tdr_core u_process1_monitor_jtag_tdr_core (
    // JTAG
    .tcki,
    .trsti,
    // JTAG TAP
    .seli ('0),
    .sei  ('0),
    .cei  ('0),
    .uei  ('0),
    .tdi  ('0),
    .tdo  (),

    .o_jtag_mode(jtag_mode),
    .o_enable   (jtag_enable),
    .o_target   (jtag_target),
    .o_use_ro   (jtag_use_ro),
    .i_valid    (o_valid),
    .i_count    (o_count)
  );

endmodule
