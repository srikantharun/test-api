// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Yasen Kazandzhiev <yasen.kazandzhiev@axelera.ai>

/// The module detects rising and falling edges of a single bit signal.
///
/// !!! warning
///
///     Do not use this module for asynchronous signals!
///

module axe_ccl_mon_edge_detector (
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /// Input signal
  input  logic i_signal,
  /// Rising edge detected
  output logic o_raise,
  /// Falling edge detected
  output logic o_fall
);

  logic signal_q;

  // Flop the input signal to detect an edge
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n)
      signal_q <= 1'b0;
    else
      signal_q <= i_signal;
  end

  // Detect rising edge
  always_comb o_raise = (i_signal & ~signal_q);

  // Detect falling edge
  always_comb o_fall = (~i_signal & signal_q);

endmodule
