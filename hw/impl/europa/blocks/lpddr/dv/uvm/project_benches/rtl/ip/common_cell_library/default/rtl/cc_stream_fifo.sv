// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// First-In-First-Out buffer with valid/ready handshaking
///
module cc_stream_fifo #(
  /// Number of storage spaces
  parameter int unsigned Depth = 4,
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// Have no latency for the data showing up, TODO(@wolfgang.roenninger): Define Latency?
  parameter bit FallThrough = 1'b0,
  /// Derived: The width of the address pointers
  localparam int unsigned AddrWidth = cc_math_pkg::index_width(Depth)
)(
  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  // doc async
  input  wire   i_rst_n,
  // doc sync i_clk
  /// Flush the contents of the Fifo
  input  logic  i_flush,


  /// The input stream payload data
  input  data_t i_data,
  /// The input stream is valid
  input  logic  i_valid,
  /// The input stream is ready
  output logic  o_ready,

  /// The output stream payload data
  output data_t o_data,
  /// The output stream is valid
  output logic  o_valid,
  /// The output stream is ready
  input  logic  i_ready,

  /// Observation: Indicate the overall ussage of the fifo
  output logic [AddrWidth:0] o_usage,
  /// Observation: The Fifo is full, no further space for data
  output logic               o_full,
  /// Observation: The Fifo is empty, does not contain any data
  output logic               o_empty
);
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////
  if ($bits(data_t) == 0) $fatal(1, "Parameter: '$bits(data_t)' does not produce valid data; Width is: %d", $bits(data_t));

  // TODO(@wolfgang.roenninger): Refactor this module to be ground truth to replace:
  //                               - cc_stream_buffer
  //                               - sync_fifo
  //                               - fifo_v3

  localparam int unsigned UsageWidth = AddrWidth + 1;

  logic [AddrWidth-1:0] usage;
  assign o_usage = o_full ? UsageWidth'(Depth) : UsageWidth'(usage);

  logic  push, pop;
  assign push = i_valid & o_ready;
  assign pop  = o_valid & i_ready;

  assign o_ready = ~o_full;
  assign o_valid = ~o_empty;

  fifo_v3 #(
    .FALL_THROUGH(FallThrough),
    .DEPTH       (Depth),
    .dtype_t     (data_t)
  ) u_fifo_v3 (
    .i_clk,
    .i_rst_n,
    .flush_i   (i_flush),
    .testmode_i('0),
    .full_o    (o_full),
    .empty_o   (o_empty),
    .usage_o   (usage),
    .data_i    (i_data),
    .push_i    (push),
    .data_o    (o_data),
    .pop_i     (pop)
  );
endmodule
