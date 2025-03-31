// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Pulse clock crossing with feedback path
///
module axe_ccl_cdc_pulse #(
  /// Number of synchronization stages per direction
  parameter int unsigned SyncStages = 3
)(
  /// Source domain clock, positive edge triggered
  input  wire  i_src_clk,
  /// Source domain asynchronous reset, active low
  input  wire  i_src_rst_n,
  /// Source domain input pulse
  input  logic i_src_pulse,
  /// Source domain busy flag, input pulses are ignored!
  output logic o_src_busy,
  /// Source domain error flag, Pulse was not propagated.
  output logic o_src_error,

  /// Destination domain clock, positive edge triggered
  input  wire  i_dst_clk,
  /// Destination domain asynchronous reset, active low
  input  wire  i_dst_rst_n,
  /// Destination domain pulse
  output logic o_dst_pulse
);
  ///////////////////
  // Source domain //
  ///////////////////
  logic src_toggle;
  logic src_toggle_q;
  logic src_feedback;

  // We are busy synchronizing as long as toggle state and feedback are not the same (xor)
  always_comb o_src_busy  = src_toggle_q ^ src_feedback;

  // We can toggle if we are not busy
  always_comb src_toggle  = i_src_pulse & ~o_src_busy;

  // We have a dropped pulse (error) when pulse arrives during busy
  always_comb o_src_error = i_src_pulse &  o_src_busy;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_src_clk or negedge i_src_rst_n) begin
    if (!i_src_rst_n)    src_toggle_q <= 1'b0;
    else if (src_toggle) src_toggle_q <= ~src_toggle_q;
  end

  ////////////////////////
  // Destination domain //
  ////////////////////////
  logic dst_toggle, dst_toggle_q;

  // Output is just the xor when the toggle is updated
  always_comb o_dst_pulse = dst_toggle ^ dst_toggle_q;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_dst_clk or negedge i_dst_rst_n) begin
    if (!i_dst_rst_n) dst_toggle_q <= 1'b0;
    else              dst_toggle_q <= dst_toggle;
  end

  ///////////////////
  // Synchronizers //
  ///////////////////
  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(1'b0)
  ) u_src_to_dst_sync (
    .i_clk  (i_dst_clk),
    .i_rst_n(i_dst_rst_n),
    .i_d    (src_toggle_q),
    .o_q    (dst_toggle)
  );

  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(1'b0)
  ) u_dst_to_src_sync (
    .i_clk  (i_src_clk),
    .i_rst_n(i_src_rst_n),
    .i_d    (dst_toggle_q),
    .o_q    (src_feedback)
  );
endmodule
