// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: process monitor 2 behavioral model.
//
// Authors: Manuel Oliveira

module process2_monitor_wrapper
import process2_monitor_pkg::*;
(
  // JTAG
  input   wire                                         tcki,
  input   wire                                         trsti,

  input	  wire                                         i_clk,
  input   wire                                         i_enable,

  input   wire                                         i_ref_clk,

  input   logic                     [PR2_TARGET_W-1:0] i_target,

  input   logic                   [PR2_NB_MONITOR-1:0] i_use_ro,

  output  logic                                        o_valid,
  output  logic [PR2_NB_MONITOR-1:0] [PR2_COUNT_W-1:0] o_count
);
  wire                       monitor_clk;
  logic                      jtag_mode;
  logic                      jtag_enable;
  logic   [PR2_TARGET_W-1:0] jtag_target;
  logic [PR2_NB_MONITOR-1:0] jtag_use_ro;
  logic                      mux_enable;
  logic   [PR2_TARGET_W-1:0] mux_target;
  logic [PR2_NB_MONITOR-1:0] mux_use_ro;

  always_comb mux_enable = jtag_mode ? jtag_enable : i_enable;
  always_comb mux_target = jtag_mode ? jtag_target : i_target;
  always_comb mux_use_ro = jtag_mode ? jtag_use_ro : i_use_ro;

  axe_tcl_clk_mux2 u_clk_mux2 (
    .i_clk0(i_clk),
    .i_clk1(tcki),
    .i_sel (jtag_mode),
    .o_clk (monitor_clk)
  );

  process2_monitor u_process2_monitor(
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
    .count_13 (o_count[13]),
    .count_14 (o_count[14]),
    .count_15 (o_count[15]),
    .count_16 (o_count[16]),
    .count_17 (o_count[17]),
    .count_18 (o_count[18]),
    .count_19 (o_count[19]),
    .count_20 (o_count[20]),
    .count_21 (o_count[21]),
    .count_22 (o_count[22]),
    .count_23 (o_count[23]),
    .count_24 (o_count[24]),
    .count_25 (o_count[25]),
    .count_26 (o_count[26]),
    .count_27 (o_count[27]),
    .count_28 (o_count[28]),
    .count_29 (o_count[29]),
    .count_30 (o_count[30]),
    .count_31 (o_count[31]),
    .count_32 (o_count[32]),
    .count_33 (o_count[33]),
    .count_34 (o_count[34]),
    .count_35 (o_count[35]),
    .count_36 (o_count[36]),
    .count_37 (o_count[37]),
    .count_38 (o_count[38]),
    .count_39 (o_count[39]),
    .count_40 (o_count[40]),
    .count_41 (o_count[41]),
    .count_42 (o_count[42])
  );

  process2_monitor_jtag_tdr_core u_process2_monitor_jtag_tdr_core (
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
