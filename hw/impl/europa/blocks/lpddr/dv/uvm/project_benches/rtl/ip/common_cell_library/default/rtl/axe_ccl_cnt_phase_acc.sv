// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Phase accumulator for generating pulses every X cycles (X can be fractional).
///
module axe_ccl_cnt_phase_acc #(
  /// Configure the with of the increment value, the actual counter is 1-bit wider.
  parameter int unsigned Width = 0
)(
  /// Clock, positive edge triggered.
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low.
  input  wire  i_rst_n,
  // doc sync i_clk
  /// Synchronous clear. This resets the internal state to `0`.
  input  logic i_cnt_clr,
  /// Increment value to be added to the current phase of the accumulator.
  input  logic [Width-1:0] i_cnt_incr,
  /// Enable the ticking up of the accumulator.
  input  logic i_cnt_en,
  /// This is the overflow bit of the accumulator.
  output logic o_pulse,
  /// The current phase value of the accumulator.
  output logic [Width-1:0] o_phase
);
  // Parameter checks
  if (Width == 0) $fatal(1, "Parameter: 'Width' must be greater than 0;");


  // Signal for combinational assign
  logic [Width:0] phase_d;
  // Addition results in bit width increase in LHS signal by 1.
  assign phase_d = o_phase + i_cnt_incr;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)       {o_pulse, o_phase} <= '0;
    else if (i_cnt_clr) {o_pulse, o_phase} <= '0;
    else if (i_cnt_en)  {o_pulse, o_phase} <= phase_d;
  end
endmodule
