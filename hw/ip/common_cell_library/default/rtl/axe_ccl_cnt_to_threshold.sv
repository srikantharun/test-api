// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

/// Basic counting block that pulses the output pulse_o when the threshold_i is reached.
///
module axe_ccl_cnt_to_threshold #(
  /// Counter width (excluding overflow bit)
  parameter int unsigned Width = 8,
  /// Does the overflow needs to be sticky. (Stay asserted even if value goes down)
  parameter bit StickyOverflow = 1'b0
)(
  /// Clock, positive edge triggered
  input  wire              i_clk,
  /// Asynchronous reset, active low
  // doc async
  input  wire              i_rst_n,
  // doc sync clk_i
  /// Synchronous clear to set the internal count to 0
  input  logic             i_clear,
  /// Enable counting
  input  logic             i_enable,
  /// Counting increment
  input  logic [Width-1:0] i_increment,
  /// Counting threshold
  input  logic [Width-1:0] i_threshold,
  /// Threshold reached output pulse
  output logic             o_pulse,
  /// Overflow pulse
  output logic             o_overflow
);
  logic             counter_flush;
  logic [Width-1:0] counter_q;

  always_comb o_pulse       = counter_q >= i_threshold;
  always_comb counter_flush = i_clear | (o_pulse & ~i_enable);

  logic overflow;
  logic underflow;

  axe_ccl_cnt_delta #(
    .Width         (Width),
    .StickyOverflow(StickyOverflow)
  ) u_cnt_delta (
    .i_clk,
    .i_rst_n,
    .i_flush    (counter_flush),
    .i_enable,
    .i_decrement(1'b0),
    .i_delta    (i_increment),
    .o_count    (counter_q),
    .i_value    (i_increment),
    .i_overwrite(o_pulse),
    .o_overflow (overflow),
    .o_underflow(underflow)
  );

  always_comb o_overflow = overflow | underflow;
endmodule
