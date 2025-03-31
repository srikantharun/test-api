// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// First-In-First-Out buffer with valid/ready handshaking
///
module axe_ccl_stream_fifo_mem #(
  /// Number of storage spaces
  parameter int unsigned Depth = 16,
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// Derived: The width of the address pointers
  localparam int unsigned AddrWidth = cc_math_pkg::index_width(Depth),
  /// Memory Implementation Key
  parameter MemImplKey = "default",
  /// Sideband input signal type to tc_sram
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
)(
  ////////////////////////////
  // Clock, Reset and Flush //
  ////////////////////////////

  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  // doc async
  input  wire   i_rst_n,
  // doc sync i_clk
  /// Flush the contents of the Fifo
  input  logic  i_flush,

  //////////////////
  // Input Stream //
  //////////////////
  /// The input stream payload data
  input  data_t i_data,
  /// The input stream is valid
  input  logic  i_valid,
  /// The input stream is ready
  output logic  o_ready,

  ///////////////////
  // Output Stream //
  ///////////////////
  /// The output stream payload data
  output data_t o_data,
  /// The output stream is valid
  output logic  o_valid,
  /// The output stream is ready
  input  logic  i_ready,

  /////////////////
  // Observation //
  /////////////////
  /// Observation: Indicate the overall ussage of the fifo
  output logic [AddrWidth:0] o_usage,
  /// Observation: The Fifo is full, no further space for data
  output logic               o_full,
  /// Observation: The Fifo is empty, does not contain any data
  output logic               o_empty,

  /////////////////////////////
  // Memory Sideband Signals //
  /////////////////////////////
  /// Memory sideband input signals
  input  ram_impl_inp_t i_ram_impl,
  /// Memory sideband output signals
  output ram_impl_oup_t o_ram_impl
);
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////
  if ($bits(i_data) == 0) $fatal(1, "Parameter: '$bits(data_t)' does not produce valid data; Width is: %d", $bits(i_data));
  if (Depth <= 4) $fatal(1, "Parameter: 'Depth' Must be larger than 4;");

  typedef logic [AddrWidth:0] usage_t;

  ///////////
  // Flags //
  ///////////
  logic transaction_input;
  logic transaction_stage;
  logic transaction_output;
  always_comb transaction_input  = i_valid & o_ready;
  always_comb transaction_output = o_valid & i_ready;

  axe_ccl_cnt_delta #(
    .Width         (AddrWidth+1),
    .StickyOverflow(1'b0)
  ) u_cnt_usage (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_enable   (transaction_input ^ transaction_output),
    .i_decrement(transaction_output),
    .i_delta    (usage_t'(1)),
    .o_count    (o_usage),
    .i_value    (usage_t'(0)),
    .i_overwrite(1'b0),
    .o_overflow (/* not used */),
    .o_underflow(/* not used */)
  );

  always_comb o_full  = o_usage == usage_t'(Depth);
  always_comb o_empty = o_usage == usage_t'(0);

  /////////////////////////
  // Input Stream Muxing //
  /////////////////////////
  typedef enum logic {
    BYPASS,
    MEMORY
  } select_e;

  select_e select_q;

  data_t   demux_data[2];
  logic    demux_valid[2];
  logic    demux_ready[2];

  // This here provides the flow control!
  always_comb demux_ready[MEMORY] = ~o_full;

  cc_stream_demux_unpack #(
    .DataWidth  (DataWidth),
    .data_t     (data_t),
    .NumStreams (2),
    .DropOnError(1'b0)
  ) u_demux_input (
    .i_data,
    .i_select(select_q),
    .i_valid,
    .o_ready,
    .o_error (/*not used*/),
    .o_data  (demux_data),
    .o_valid (demux_valid),
    .i_ready (demux_ready)
  );

  data_t   mux_data[2];
  logic    mux_valid[2];
  logic    mux_ready[2];

  always_comb mux_data[BYPASS]    = demux_data[BYPASS];
  always_comb mux_valid[BYPASS]   = demux_valid[BYPASS];
  always_comb demux_ready[BYPASS] = mux_ready[BYPASS];

  data_t   stage_data;
  logic    stage_valid;
  logic    stage_ready;

  cc_stream_mux_unpack #(
    .DataWidth (DataWidth),
    .data_t    (data_t),
    .NumStreams(2)
  ) u_mux_input (
    .i_select(select_q),
    .o_error (/*not used*/),
    .i_data  (mux_data),
    .i_valid (mux_valid),
    .o_ready (mux_ready),
    .o_data  (stage_data),
    .o_valid (stage_valid),
    .i_ready (stage_ready)
  );

  /////////////////////////////
  // 3 Deep Fifo for Staging //
  /////////////////////////////
  localparam int unsigned STAGE_DEPTH = 3;
  typedef logic[cc_math_pkg::index_width(STAGE_DEPTH):0] stage_usage_t;

  always_comb   transaction_stage = stage_valid & stage_ready;

  stage_usage_t stage_usage;
  logic         stage_full;
  logic         stage_next_cycle_full;
  always_comb   stage_next_cycle_full =
      ( stage_full & ~transaction_output)
    | ((stage_usage >= stage_usage_t'(STAGE_DEPTH-1)) & ~transaction_output & transaction_stage);

  cc_stream_fifo #(
    .Depth      (3),   // Depth 3 is needed to absorb all lateny of accessing the memory and still have full throughput
    .DataWidth  (DataWidth),
    .data_t     (data_t),
    .FallThrough(1'b0) // We are large, no fall thourgh needed
  ) u_staging_fifo (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_data (stage_data),
    .i_valid(stage_valid),
    .o_ready(stage_ready),
    .o_data,
    .o_valid,
    .i_ready,
    .o_usage(stage_usage),
    .o_full (stage_full),
    .o_empty(/*not used*/)
  );

  ////////////////
  // The Memory //
  ////////////////
  localparam int unsigned MemoryDepth = Depth; // This could be optimized
  localparam int unsigned MemoryWidth = $bits(i_data);
  typedef logic [AddrWidth-1:0] addr_t;

  logic  request_write;
  logic  request_read;

  addr_t pointer_write_q;
  addr_t pointer_read_q;

  // And yes this only works because our memory space has too much space and is not optimally used....
  logic       pointers_are_equal;
  always_comb pointers_are_equal = pointer_write_q == pointer_read_q;

  axe_tcl_ram_1rp_1wp #(
    .NumWords   (MemoryDepth),
    .DataWidth  (MemoryWidth),
    .ByteWidth  (MemoryWidth),
    .ReadLatency(1), // We used fixed latency to make control easier
    .ImplKey    (MemImplKey),
    .impl_inp_t (ram_impl_inp_t),
    .impl_oup_t (ram_impl_oup_t)
  ) u_memory (
    .i_wr_clk  (i_clk),
    .i_wr_rst_n(i_rst_n),
    .i_wr_req  (request_write),
    .i_wr_addr (pointer_write_q),
    .i_wr_data (demux_data[MEMORY]),
    .i_wr_mask (1'b1),
    .i_rd_clk  (i_clk),
    .i_rd_rst_n(i_rst_n),
    .i_rd_req  (request_read),
    .i_rd_addr (pointer_read_q),
    .o_rd_data (mux_data[MEMORY]),
    .i_impl    (i_ram_impl),
    .o_impl    (o_ram_impl)
  );

  cc_cnt_shift_reg #(
    .Width (1),
    .Stages(1)
  ) u_request_read_shift_reg (
    .i_clk,
    .i_rst_n,
    .i_clear  (i_flush),
    .i_stall  (1'b0),
    .i_data   (1'b0), // To be optimized away, we are interested in the load
    .i_data_en(request_read),
    .o_data   (/* open */),
    .o_updated(mux_valid[MEMORY])
  );

  /////////////
  // Control //
  /////////////
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)           pointer_write_q <= addr_t'(0);
    else if (i_flush)       pointer_write_q <= addr_t'(0);
    else if (request_write) pointer_write_q <= (pointer_write_q == addr_t'(Depth-1)) ? addr_t'(0) : pointer_write_q + addr_t'(1);
  end
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          pointer_read_q <= addr_t'(0);
    else if (i_flush)      pointer_read_q <= addr_t'(0);
    else if (request_read) pointer_read_q <= (pointer_read_q == addr_t'(Depth-1)) ? addr_t'(0) : pointer_read_q + addr_t'(1);
  end

  logic toggle;
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)     select_q <= BYPASS;
    else if (i_flush) select_q <= BYPASS;
    else if (toggle)  select_q <= (select_q == BYPASS) ? MEMORY : BYPASS;
  end

  // Write is easy, if the stream is connected push to memory
  always_comb request_write = demux_valid[MEMORY] & demux_ready[MEMORY];

  // Read a new value if there is space in the stage and the pointers are different
  always_comb request_read  = ~pointers_are_equal & ((mux_ready[MEMORY] & ~stage_next_cycle_full) | (~mux_ready[MEMORY] & transaction_output));

  // When to toggle?
  always_comb toggle = (select_q == BYPASS) ?
       stage_next_cycle_full : (pointers_are_equal & ~demux_valid[MEMORY] & mux_ready[MEMORY] & ~stage_next_cycle_full);

endmodule
