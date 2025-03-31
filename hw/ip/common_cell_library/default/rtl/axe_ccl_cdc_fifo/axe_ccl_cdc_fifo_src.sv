// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Source domain logic of `axe_cdc_fifo`.
///
module axe_ccl_cdc_fifo_src #(
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
  ///////////////////
  // Source Domain //
  ///////////////////
  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  /// Synchronously flush pointer (should be controlled by `axe_ccl_cdc_reset_control`)
  input  logic  i_flush,

  /// The input stream payload data
  input  data_t i_data,
  /// The input stream is valid
  input  logic  i_valid,
  /// The input stream is ready
  output logic  o_ready,

  ///////////////////
  // Async Signals //
  ///////////////////
  /// The asynchronous output data
  output data_t               o_async_data[Depth],
  /// The asynchronous write pointer to the dst domain
  output logic [AddrWidth:0]  o_async_w_gray_pointer,
  /// The asynchronous read pointer from the dst domain
  input  logic [AddrWidth:0]  i_async_r_gray_pointer
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

  pointer_t r_gray_pointer;

  cc_cdc_sync_array #(
    .SyncStages (SyncStages),
    .Width      (AddrWidth+1),
    .ResetValues(ResetIdxGray)
  ) u_axe_ccl_cdc_sync_array (
    .i_clk,
    .i_rst_n,
    .i_data (i_async_r_gray_pointer),
    .o_data (r_gray_pointer)
  );

  logic     store_data;
  logic     fifo_is_full;
  address_t write_address;

  axe_ccl_cdc_fifo_pointer #(
    .Mode (1'b0),
    .Depth(Depth)
  ) u_write_pointer (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_update      (store_data),
    .i_gray_pointer(r_gray_pointer),
    .o_flag        (fifo_is_full),
    .o_address     (write_address),
    .o_gray_pointer(o_async_w_gray_pointer)
  );

  /////////////////
  // Handshaking //
  /////////////////
  always_comb o_ready    = ~fifo_is_full;
  always_comb store_data = i_valid & o_ready;

  //////////////////
  // Data Storage //
  //////////////////
  // DFFL: D-Flip-Flop, load enable
  always_ff @(posedge i_clk) begin
    if (store_data) o_async_data[write_address] <= i_data;
  end
endmodule
