// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Up/Down-Counter with configurable delta
///
module axe_ccl_cnt_delta #(
  /// The width of the counter data
  parameter int unsigned Width          = 4,
  /// Makes the overflow bit sticky if set to `1'b1`.
  ///
  /// Once overflow is asserted it will be kept high until either `i_flush` or `i_overwrite`
  /// have been asserted.
  parameter bit          StickyOverflow = 1'b0
)(
  /// Clock, positive edge triggered
  input  wire              i_clk,
  /// Asynchronous reset, active low
  input  wire              i_rst_n,
  /// Synchronous clear, set the count to `Width'(0)`
  ///
  /// This has priority over `i_enable` and `i_overwrite`
  input  logic             i_flush,
  /// Enable / advance the counter
  input  logic             i_enable,
  /// Count down instead of counting up
  /// - `1'b0`: Increment the count by `i_delta`
  /// - `1'b1`: Decrement the count by `i_delta`
  input  logic             i_decrement,
  /// The delta to be added / substracted from `o_count`
  input  logic [Width-1:0] i_delta,
  /// The current counter state
  output logic [Width-1:0] o_count,
  /// The value to be loaded for overwrite into the counter
  input  logic [Width-1:0] i_value,
  /// Overwrite the next `o_count` with `i_value`.
  ///
  /// This has priority over `i_enable`
  input  logic             i_overwrite,
  /// The counter overflowed
  output logic             o_overflow,
  /// The counter underflowed
  output logic             o_underflow
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  if (Width == 0) $fatal(1, "Parameter: 'Width' must not be 0;");

  // Have one bit more for the carry
  localparam int unsigned CounterWidth = Width + 1;
  typedef logic [CounterWidth-1:0] counter_t;

  ///////////////////
  // Counter State //
  ///////////////////
  counter_t counter_q, counter_d;

  /////////////////////
  // Sticky Overflow //
  /////////////////////
  logic set_overflow;
  logic set_underflow;

  always_comb set_overflow  = ~i_decrement & i_enable & counter_d[Width];
  always_comb set_underflow =  i_decrement & i_enable & counter_d[Width];

  logic       clear_error;
  always_comb clear_error =
      i_flush
    | i_overwrite
    | (i_enable & (~counter_d[Width]) & (~StickyOverflow) & (o_overflow | o_underflow)); // When going back to proper range

  // RSFFR: R/S-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      o_overflow  <= 1'b0;
      o_underflow <= 1'b0;
    end else if (clear_error) begin
      o_overflow  <= 1'b0;
      o_underflow <= 1'b0;
    end else begin
      if (set_overflow)  o_overflow  <= 1'b1;
      if (set_underflow) o_underflow <= 1'b1;
    end
  end

  ///////////////////
  // Counter Logic //
  ///////////////////
  always_comb counter_d = counter_q + (counter_t'(i_delta) ^ {CounterWidth{i_decrement}}) + i_decrement;

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)         counter_q <= counter_t'(0);
    else if (i_flush)     counter_q <= counter_t'(0);
    else if (i_overwrite) counter_q <= counter_t'(i_value);
    else if (i_enable)    counter_q <= counter_d;
  end

  always_comb o_count = counter_q[Width-1:0];
endmodule
