// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Source domain logic of `axe_cdc_fifo`.
///
module axe_ccl_cdc_fifo_dst #(
  /// Number of storage spaces, needs at least 6 for full thoughput on the slower side.
  parameter int unsigned Depth = 6,
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of synchronizer stages
  parameter int unsigned SyncStages = 3,
  /// The address width to access the data.
  ///
  localparam int unsigned AddrWidth = cc_math_pkg::index_width(Depth)
)(
  ////////////////////////
  // Destination Domain //
  ////////////////////////
  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  /// Synchronously flush pointer (should be controlled by `axe_ccl_cdc_reset_control`)
  input  logic  i_flush,

  /// The output stream payload data
  output data_t o_data,
  /// The output stream is valid
  output logic  o_valid,
  /// The output stream is ready
  input  logic  i_ready,

  ///////////////////
  // Async Signals //
  ///////////////////
  /// The asynchronous output data
  input  data_t               i_async_data[Depth],
  /// The asynchronous write pointer from the src domain
  input  logic [AddrWidth:0]  i_async_w_gray_pointer,
  /// The asynchronous read pointer to the src domain
  output logic [AddrWidth:0]  o_async_r_gray_pointer
);
  //////////////////////
  // Type Definitions //
  //////////////////////
  typedef logic [AddrWidth-1:0] address_t;
  typedef logic [AddrWidth  :0] pointer_t;

  localparam pointer_t ResetIdxBin  = pointer_t'(axe_ccl_cdc_pkg::get_rst_bin_index(Depth));
  localparam pointer_t ResetIdxGray = pointer_t'(axe_ccl_cdc_pkg::bin_to_gray(32'(ResetIdxBin)));

  /////////////////////////////////
  // Pointer and Address Forming //
  /////////////////////////////////

  pointer_t w_gray_pointer;

  cc_cdc_sync_array #(
    .SyncStages (SyncStages),
    .Width      (AddrWidth+1),
    .ResetValues(ResetIdxGray)
  ) u_axe_ccl_cdc_sync_array (
    .i_clk,
    .i_rst_n,
    .i_data (i_async_w_gray_pointer),
    .o_data (w_gray_pointer)
  );

  logic     capture_data;
  logic     fifo_is_empty;
  address_t read_address;

  axe_ccl_cdc_fifo_pointer #(
    .Mode (1'b1),
    .Depth(Depth)
  ) u_read_pointer (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_update      (capture_data),
    .i_gray_pointer(w_gray_pointer),
    .o_flag        (fifo_is_empty),
    .o_address     (read_address),
    .o_gray_pointer(o_async_r_gray_pointer)
  );

  //////////////////////////////////
  // Handshaking and Data Capture //
  //////////////////////////////////
  data_t      data_d;
  always_comb data_d = i_async_data[read_address];

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          o_data <= data_t'(0);
    else if (capture_data) o_data <= data_d;
  end

  cc_stream_pipe_load #(
    .NumStages(1)
  ) u_capture_pipeline (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_valid(~fifo_is_empty),
    .o_ready(/* not used */), // ASO-UNUSED_OUTPUT : Another output `o_load(capture_data)` is used for flow control.
    .o_load (capture_data),
    .o_state(/* not used */), // ASO-UNUSED_OUTPUT : No observability needed.
    .o_valid,
    .i_ready
  );
endmodule
