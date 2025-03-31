// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// A full thoughput CDC FIFO with gray pointer synchronization.
///
module axe_ccl_cdc_fifo #(
  /// Number of storage spaces, needs at least 6 for full thoughput on the slower side.
  parameter int unsigned Depth = 6,
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of synchronizer stages
  ///
  /// !!! note
  ///
  ///     Theresetandflush logic needs strict less sync stages to avoid metastability during
  ///     async reset, asthe minimum sync stages is 3 at high clock speeds we needat least 4.
  parameter int unsigned SyncStages = 4,
  /// Initiate a flush on Async Reset on either side.
  parameter bit          FlushOnAsyncReset = 1'b1
)(
  ///////////////////
  // Source Domain //
  ///////////////////
  /// Clock, positive edge triggered (Source Domain)
  input  wire   i_src_clk,
  /// Asynchronous reset, active low (Source Domain)
  input  wire   i_src_rst_n,
  /// Flush the data in the fifo (will also flush the src side)
  input  logic  i_src_flush,
  /// The flush is ongoing.
  output logic  o_src_purging,

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
  /// Flush the data in the fifo (will also flush the src side)
  input  logic  i_dst_flush,
  /// The flush is ongoing.
  output logic  o_dst_purging,

  /// The output stream payload data
  output data_t o_dst_data,
  /// The output stream is valid
  output logic  o_dst_valid,
  /// The output stream is ready
  input  logic  i_dst_ready
);

  localparam int unsigned PointerWidth = cc_math_pkg::index_width(Depth) + 1;
  typedef logic [PointerWidth-1:0] pointer_t;

  data_t    async_data[Depth];
  pointer_t async_w_gray_pointer;
  pointer_t async_r_gray_pointer;

  axe_ccl_cdc_pkg::flush_phase_e async_src_to_dst_flush_phase;
  logic                          async_src_to_dst_flush_req;
  logic                          async_src_to_dst_flush_ack;
  axe_ccl_cdc_pkg::flush_phase_e async_dst_to_src_flush_phase;
  logic                          async_dst_to_src_flush_req;
  logic                          async_dst_to_src_flush_ack;

  logic  src_isolate;
  logic  src_flush;

  axe_ccl_cdc_reset_control #(
    .SyncStages       (SyncStages-1), // This is correct!
    .FlushOnAsyncReset(FlushOnAsyncReset)
  ) u_axe_ccl_cdc_reset_control_src (
    .i_clk              (i_src_clk),
    .i_rst_n            (i_src_rst_n),
    .i_flush            (i_src_flush),
    .o_isolate_req      (src_isolate),
    .i_isolate_ack      (src_isolate),
    .o_flush_req        (src_flush),
    .i_flush_ack        (src_flush),
    .o_async_next_phase (async_src_to_dst_flush_phase),
    .o_async_request    (async_src_to_dst_flush_req),
    .i_async_acknowledge(async_src_to_dst_flush_ack),
    .i_async_next_phase (async_dst_to_src_flush_phase),
    .i_async_request    (async_dst_to_src_flush_req),
    .o_async_acknowledge(async_dst_to_src_flush_ack)
  );

  data_t src_data;
  logic  src_valid;
  logic  src_ready;

  cc_stream_disconnect #(
    .DataWidth(DataWidth),
    .data_t   (data_t)
  ) u_axe_ccl_stream_disconnect_src (
    .i_disconnect (src_isolate),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */), // ASO-UNUSED_OUTPUT : No observabilty needed
    .o_transaction(/* not used */), // ASO-UNUSED_OUTPUT : No observabilty needed
    .i_data       (i_src_data),
    .i_valid      (i_src_valid),
    .o_ready      (o_src_ready),
    .o_data       (src_data),
    .o_valid      (src_valid),
    .i_ready      (src_ready)
  );

  axe_ccl_cdc_fifo_src #(
    .Depth     (Depth),
    .DataWidth (DataWidth),
    .data_t    (data_t),
    .SyncStages(SyncStages)
  ) u_axe_ccl_cdc_fifo_src (
    .i_clk                 (i_src_clk),
    .i_rst_n               (i_src_rst_n),
    .i_flush               (src_flush),
    .i_data                (src_data),
    .i_valid               (src_valid),
    .o_ready               (src_ready),
    .o_async_data          (async_data),
    .o_async_w_gray_pointer(async_w_gray_pointer),
    .i_async_r_gray_pointer(async_r_gray_pointer)
  );

  logic  dst_isolate;
  logic  dst_flush;

  axe_ccl_cdc_reset_control #(
    .SyncStages       (SyncStages-1), // This is correct!
    .FlushOnAsyncReset(FlushOnAsyncReset)
  ) u_axe_ccl_cdc_reset_control_dst (
    .i_clk              (i_dst_clk),
    .i_rst_n            (i_dst_rst_n),
    .i_flush            (i_dst_flush),
    .o_isolate_req      (dst_isolate),
    .i_isolate_ack      (dst_isolate),
    .o_flush_req        (dst_flush),
    .i_flush_ack        (dst_flush),
    .o_async_next_phase (async_dst_to_src_flush_phase),
    .o_async_request    (async_dst_to_src_flush_req),
    .i_async_acknowledge(async_dst_to_src_flush_ack),
    .i_async_next_phase (async_src_to_dst_flush_phase),
    .i_async_request    (async_src_to_dst_flush_req),
    .o_async_acknowledge(async_src_to_dst_flush_ack)
  );

  data_t dst_data;
  logic  dst_valid;
  logic  dst_ready;

  axe_ccl_cdc_fifo_dst #(
    .Depth     (Depth),
    .DataWidth (DataWidth),
    .data_t    (data_t),
    .SyncStages(SyncStages)
  ) u_axe_ccl_cdc_fifo_dst (
    .i_clk                 (i_dst_clk),
    .i_rst_n               (i_dst_rst_n),
    .i_flush               (dst_flush),
    .o_data                (dst_data),
    .o_valid               (dst_valid),
    .i_ready               (dst_ready),
    .i_async_data          (async_data),
    .i_async_w_gray_pointer(async_w_gray_pointer),
    .o_async_r_gray_pointer(async_r_gray_pointer)
  );

  cc_stream_disconnect #(
    .DataWidth(DataWidth),
    .data_t   (data_t)
  ) u_axe_ccl_stream_disconnect_dst (
    .i_disconnect (dst_isolate),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */), // ASO-UNUSED_OUTPUT : No observability needed
    .o_transaction(/* not used */), // ASO-UNUSED_OUTPUT : No Observability needed
    .i_data       (dst_data),
    .i_valid      (dst_valid),
    .o_ready      (dst_ready),
    .o_data       (o_dst_data),
    .o_valid      (o_dst_valid),
    .i_ready      (i_dst_ready)
  );

  // The isolate signals are on during the whole sequence
  always_comb o_src_purging = src_isolate;
  always_comb o_dst_purging = dst_isolate;
endmodule
