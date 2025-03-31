// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Based on the design: https://github.com/pulp-platform/common_cells/blob/master/src/cdc_4phase.sv

/// A 4-phase clock domain crossing. (Source Domain)
///
/// While this is less efficient than a 2-phase CDC, it doesn't suffer from the same issues
/// during one sided resets since the IDLE state doesn't alternate with every transaction.
///
/// !!! example "Constraints"
///
///     Requires the `max_delay` of `min_period(i_src_clk, i_dst_clk)` through the paths:
///
///     - `async_data`
///     - `async_req`
///     - `async_ack`
///
module axe_ccl_cdc_4_phase #(
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of synchronizer stages
  parameter int unsigned SyncStages = 3,
  /// Wait with the input handshake until the `dst` side has completed the handshake.
  ///
  /// This increases the latency of the first transaction but has no effect on throughput.
  parameter int unsigned WaitHandshake = 1'b0,
  /// Start sending the `ResetMsg` within the asynchronous reset state.
  ///
  /// This is useful if we need to transmit m message to the other side of the CDC immediately
  /// during the asynchronous reset even if there is no clock available.
  ///
  /// Required for proper functionality of `axe_ccl_cdc_reset`.
  parameter bit SendResetMsg = 1'b0,
  /// The reset message to be transmitted if `SendResetMsg(1'b1)`.
  parameter data_t ResetMsg = data_t'(0)
)(
  ///////////////////
  // Source Domain //
  ///////////////////
  /// Clock, positive edge triggered (Source Domain)
  input  wire   i_src_clk,
  /// Asynchronous reset, active low (Source Domain)
  input  wire   i_src_rst_n,
  /// The input stream payload data
  input  data_t i_src_data,
  /// The input stream is valid
  input  logic  i_src_valid,
  /// The input stream is ready
  output logic  o_src_ready,

  ////////////////////////
  // Destination Domain //
  ////////////////////////
  /// Clock, positive edge triggered (Destination Domain)
  input  wire   i_dst_clk,
  /// Asynchronous reset, active low (Destination Domain)
  input  wire   i_dst_rst_n,
  /// The output stream payload data
  output data_t o_dst_data,
  /// The output stream is valid
  output logic  o_dst_valid,
  /// The output stream is ready
  input  logic  i_dst_ready
);

  data_t async_data;
  logic  async_req;
  logic  async_ack;

  axe_ccl_cdc_4_phase_src #(
    .DataWidth    (DataWidth),
    .data_t       (data_t),
    .SyncStages   (SyncStages),
    .WaitHandshake(WaitHandshake),
    .SendResetMsg (SendResetMsg),
    .ResetMsg     (ResetMsg)
  ) u_axe_ccl_cdc_4_phase_src (
    .i_clk       (i_src_clk),
    .i_rst_n     (i_src_rst_n),
    .i_data      (i_src_data),
    .i_valid     (i_src_valid),
    .o_ready     (o_src_ready),
    .o_async_data(async_data),
    .o_async_req (async_req),
    .i_async_ack (async_ack)
  );

  axe_ccl_cdc_4_phase_dst #(
    .DataWidth (DataWidth),
    .data_t    (data_t),
    .SyncStages(SyncStages)
  ) u_axe_ccl_cdc_4_phase_dst (
    .i_clk       (i_dst_clk),
    .i_rst_n     (i_dst_rst_n),
    .o_data      (o_dst_data),
    .o_valid     (o_dst_valid),
    .i_ready     (i_dst_ready),
    .i_async_data(async_data),
    .i_async_req (async_req),
    .o_async_ack (async_ack)
  );

endmodule
