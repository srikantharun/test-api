// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// SVA of cc_cnt_lfsr
///

module cc_cnt_lfsr_sva #(
  /// The width of the state
  parameter int unsigned Width = 16,
  /// The initial seed (state)
  parameter logic [Width-1:0] Seed = Width'(1),
  /// The granularity of the state fliping operation
  parameter int unsigned FlipGranularity = Width/2
)(
  /// Clock, positive edge triggered
  input  logic i_clk,
  /// Asynchronous reset, active low
  input  logic i_rst_n,
  /// Synchronous clear, this resets the state to `Seed`
  input  logic clear_i,
  /// Enable ticking up the LFSR
  input  logic enable_i,
  /// The feedback taps for the xor. The tap on index `0` is always connected.
  input  logic [Width-1:0] taps_i,
  /// Internal un-modified state of the module
  input logic [Width-1:0] state_o,
  /// Flip the output by `FlipGranularity`. If not used set to `1'b0`.
  input  logic flip_enable_i,
  /// Select one of the masks `and`/`or` to mask the output with.
  /// If not used set to `2'b00`.
  ///
  /// - `00`/`11`: No maksing
  /// - `01`: Masked with `mask_and_i`
  /// - `10`: Masked with `make_or_i`
  input  logic [1:0] mask_select_i,
  /// `And` mask, output is masked with this over an bit-wise `and` operation.
  input  logic [Width-1:0] mask_and_i,
  /// `Or` mask, output is masked with this over an bit-wise `or` operation.
  input  logic [Width-1:0] mask_or_i,
  /// The output data after fliping and masking
  input  logic [Width-1:0] data_o
);
  default clocking @(posedge i_clk); endclocking
  default disable iff (!i_rst_n);

  logic is_first_clk_cycle;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : is_first_clk_cycle_PROC
    if (~i_rst_n) is_first_clk_cycle <= 1'b1;
    else is_first_clk_cycle <= 1'b0;
  end : is_first_clk_cycle_PROC

  ap_reset_state : assert property(
    is_first_clk_cycle |-> state_o == Seed
  );

  logic [Width-1:0] expected_state;
  always_comb expected_state = ((^(taps_i & state_o)) << (Width - 1)) |  (state_o >> 1);

  logic [Width-1:0] flip_expectation;
  always_comb flip_expectation = flip_enable_i ? (state_o >> FlipGranularity) | (state_o << FlipGranularity) : state_o;

  ap_sequence_correct : assert property(check_seq_correct);

  property check_seq_correct;
    (enable_i && !clear_i) |=> (state_o == $past(expected_state));
  endproperty

  ap_mask_disabled : assert property(
    mask_select_i inside {2'b00, 2'b11} |-> (data_o == flip_expectation)
  );

  ap_mask_and : assert property(
    (mask_select_i == 2'b01) |-> (data_o == (flip_expectation & mask_and_i))
  );

  ap_mask_or : assert property(
    (mask_select_i == 2'b10) |-> (data_o == (flip_expectation | mask_or_i))
  );

  ap_clear_func : assert property(
    clear_i |=> (state_o == Seed)
  );

  ap_no_enable_func : assert property(
    (!enable_i && !clear_i) |=> $stable(state_o)
  );

  ap_enable_func : assert property(
    (enable_i && !clear_i && (state_o != '0) && (state_o != '1)) |=> $changed(state_o)
  );

endmodule
