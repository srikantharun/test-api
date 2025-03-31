// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//        Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Liniar Feedback Shift Register implementation with parametizable width and`xor`-taps on a dynamic layout. A shift pops the LSB and adds to the MSB.
///
module cc_cnt_lfsr #(
  /// The width of the state
  parameter int unsigned Width = 16,
  /// The initial seed (state)
  parameter logic [Width-1:0] Seed = Width'(1),
  /// The granularity of the state fliping operation
  parameter int unsigned FlipGranularity = Width/2
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire i_rst_n,
  // doc sync i_clk
  /// Synchronous clear, this resets the state to `Seed`
  input  logic clear_i,
  /// Enable ticking up the LFSR
  input  logic enable_i,
  /// The feedback taps for the xor. The tap on index `0` is always connected.
  input  logic [Width-1:0] taps_i,
  /// Internal un-modified state of the module
  output logic [Width-1:0] state_o,
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
  output logic [Width-1:0] data_o
);

  // The internal state of the LFSR
  logic [Width-1:0] state_q;
  logic feedback;

  // Tapping logic
  always_comb begin : proc_tap_feedback
    // Hard tap on 0
    feedback = ^(state_q & taps_i);
    //feedback = state_q[0];
    //// Iterate over the taps
    //for (int unsigned i = 1; i < Width; i++) begin
    //  if (taps_i[i]) feedback ^= state_q[i];
    //end
  end

  // Register with asynchronous and syncchronous clear, with load enable
  // `FFLARNC(state_q, {feedback, state_q[Width-1:1]}, enable_i, clear_i, Seed, i_clk, i_rst_n)
  always_ff @(posedge (i_clk) or negedge (i_rst_n)) begin
    if (!i_rst_n) begin
      state_q <= Seed;
    end else begin
      if (clear_i) begin
        state_q <= Seed;
      end else if (enable_i) begin
        state_q <= {feedback, state_q[Width-1:1]};
      end
    end
  end

  assign state_o = state_q;

  // Flipping logic
  logic [Width-1:0] data_flipped;
  assign data_flipped = flip_enable_i ? {<<FlipGranularity{state_q}} : state_q;

  // Masking logic
  always_comb begin : proc_masking
    case (mask_select_i)
      2'b01:   data_o = data_flipped & mask_and_i;
      2'b10:   data_o = data_flipped | mask_or_i;
      default: data_o = data_flipped;
    endcase
  end
endmodule
