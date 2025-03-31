// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Convert fully handshaked stream to memory protocol
///
/// Converts a non back-pressurable memory to fully AXI-Like stream handshaking. Has the capability
/// to send sideband data for requests that generate a response.
///
module axe_ccl_stream_to_mem #(
  /// Number of buffered responses (fall-through, thus no additional latency).
  ///
  /// This defines the maximum number of outstanding requests on the memory interface. If the
  /// attached memory responds in the same cycle a request is applied, this MUST be 0. If the
  /// attached memory responds at least one cycle after a request, this MUST be >= 1 and should be
  /// equal to the response latency of the memory to saturate bandwidth.
  parameter int unsigned BufferDepth = 1,
  /// Memory request payload, usually write enable, write data, etc.
  ///
  /// Only forwarded in here to keep stream and handshake signals aligned.
  parameter type req_data_t = logic[1:0],
  /// Memory response payload, usually read data.
  parameter type rsp_data_t = logic[1:0],
  /// Memory read sideband payload, can be IDs, last flags etc.
  ///
  /// Only forwarded in here to keep stream and handshake signals aligned.
  parameter type sideband_t = logic[0:0]
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /// Synchronous flush to clear any in flight request
  input  logic i_flush,

  ////////////////////
  // Request Stream //
  ////////////////////
  /// Request stream payload
  input  req_data_t i_req_data,
  /// Request read sideband payload, will show up together with read data
  input  sideband_t i_req_sideband,
  /// Request stream payload causes memory response
  input  logic      i_req_gen_rsp,
  /// Request stream will bypass the memory lookup, generate a response, mem data will be 0
  input logic       i_req_bypass,
  /// Request sream is valid
  input  logic      i_req_valid,
  /// Request stream is ready
  output logic      o_req_ready,

  ///////////////////////
  // Request To Memory //
  ///////////////////////
  /// Memory request stream payload
  output req_data_t o_mem_req_data,
  /// Memory request sream is valid
  output logic      o_mem_req_valid,
  /// Memory request stream is ready
  input  logic      i_mem_req_ready,

  //////////////////////////
  // Response from Memory //
  //////////////////////////
  /// Memory request stream payload
  input  rsp_data_t i_mem_rsp_data,
  /// Memory request sream is valid
  input  logic      i_mem_rsp_valid,

  /////////////////////
  // Response Stream //
  /////////////////////
  /// Memory response data payload stream
  output rsp_data_t o_rsp_data,
  /// Read sidemand payload
  output sideband_t o_rsp_sideband,
  /// Response stream is valid
  output logic      o_rsp_valid,
  /// Response stream is ready
  input  logic      i_rsp_ready
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  if ($bits(i_req_data) <= 1) $fatal(1, "Parameter: 'req_data_t' must be overwritten;");
  if ($bits(o_rsp_data) <= 1) $fatal(1, "Parameter: 'rsp_data_t' must be overwritten;");

  // Request payload is just forwarded to keep the signal names aligned in calling module
  always_comb o_mem_req_data = i_req_data;

  if (BufferDepth == 0) begin : gen_bypass
    $fatal(1, "Parameter: 'BufferDepth' == 0 is currently not supported;");

    always_comb o_mem_req_valid = i_req_valid;
    always_comb o_rsp_valid     = o_mem_req_valid & i_mem_req_ready & i_mem_rsp_valid & i_req_gen_rsp;
    always_comb o_req_ready     = i_req_gen_rsp ? (o_rsp_valid & i_rsp_ready) : i_mem_req_ready;

    always_comb o_rsp_data     = i_mem_rsp_data;
    always_comb o_rsp_sideband = i_req_sideband;
  end
  else begin : gen_buffer
    // Tracked in sideband FIFO
    logic sideband_select;
    logic sideband_valid, sideband_ready;

    always_comb sideband_select = i_req_gen_rsp | i_req_bypass;

    cc_stream_fork #(
      .NumStreams(2)
    ) u_cc_stream_fork (
      .i_clk,
      .i_rst_n,
      .i_flush,
      .i_select({sideband_select, ~i_req_bypass}),
      .i_valid (i_req_valid),
      .o_ready (o_req_ready),
      .o_valid ({sideband_valid, o_mem_req_valid}),
      .i_ready ({sideband_ready, i_mem_req_ready})
    );

    // Buffers
    rsp_data_t  rsp_data;
    logic [1:0] rsp_valid, rsp_ready;

    cc_stream_fifo #(
      .Depth      (BufferDepth + 1),  // The stream fork can handshake an additional request when the sideband is full
      .data_t     (rsp_data_t),
      .FallThrough(1'b1)
    ) u_response_data_fifo (
      .i_clk,
      .i_rst_n,
      .i_flush,
      .i_data (i_mem_rsp_data),
      .i_valid(i_mem_rsp_valid),
      .o_ready(/* not used */),  // ASO-UNUSED_OUTPUT : The read data has no back-pressure, sideband of module makes sure this is not overfilled.
      .o_data (rsp_data),
      .o_valid(rsp_valid[0]),
      .i_ready(rsp_ready[0]),
      .o_usage(/* not used */),  // ASO-UNUSED_OUTPUT : No Observability needed.
      .o_full (/* not used */),  // ASO-UNUSED_OUTPUT : No Observability needed.
      .o_empty(/* not used */)   // ASO-UNUSED_OUTPUT : No Observability needed.
    );

    localparam int unsigned SidebandDataWidth   = $bits(i_req_sideband) + 1;
    localparam bit          SidebandFallThrough = BufferDepth == 0;

    logic rsp_bypass;

    cc_stream_fifo #(
      .Depth      (BufferDepth),
      .DataWidth  (SidebandDataWidth),
      .FallThrough(SidebandFallThrough)
    ) u_response_sideband_fifo (
      .i_clk,
      .i_rst_n,
      .i_flush,
      .i_data ({i_req_bypass, i_req_sideband}),
      .i_valid(sideband_valid),
      .o_ready(sideband_ready),
      .o_data ({rsp_bypass, o_rsp_sideband}),
      .o_valid(rsp_valid[1]),
      .i_ready(rsp_ready[1]),
      .o_usage(/* not used */), // ASO-UNUSED_OUTPUT : No Observability needed.
      .o_full (/* not used */), // ASO-UNUSED_OUTPUT : No Observability needed.
      .o_empty(/* not used */)  // ASO-UNUSED_OUTPUT : No Observability needed.
    );

    always_comb o_rsp_data = rsp_bypass ? '0 : rsp_data;

    cc_stream_join #(
      .NumStreams(2)
    ) u_cc_stream_join (
      .i_select({1'b1, ~rsp_bypass}),
      .i_valid(rsp_valid),
      .o_ready(rsp_ready),
      .o_valid(o_rsp_valid),
      .i_ready(i_rsp_ready)
    );
  end
endmodule
