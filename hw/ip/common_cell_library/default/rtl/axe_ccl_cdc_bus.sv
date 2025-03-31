// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>


/// Bus clock crossing with feedback path.
///
/// !!! danger "Not Full Throughput"
///
///     If busy is high, no data resync is started.
///
/// Uses for the synchronization a [Pulse Synchronizer (axe_ccl_cdc_pulse)](./pulse.md).
/// The data runs alongside it and is captured when the pulse reached the other domain.
///
module axe_ccl_cdc_bus #(
  /// Number of synchronization stages per direction
  parameter int unsigned SyncStages = 3,
  /// The data width if the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth  = 1,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type         data_t     = logic[DataWidth-1:0],
  /// The reset value of the data Flops
  parameter data_t       ResetValue = data_t'(0)
)(
  /// Source domain clock, positive edge triggered
  input  wire   i_src_clk,
  /// Source domain asynchronous reset, active low
  input  wire   i_src_rst_n,
  /// Source domain input enable (sync this data)
  input  logic  i_src_en,
  /// Source data input
  input  data_t i_src_data,
  /// Source domain busy flag, new data sync requests are ignored while high
  output logic  o_src_busy,

  /// Destination domain clock, positive edge triggered
  input  wire   i_dst_clk,
  /// Destination domain asynchronous reset, active low
  input  wire   i_dst_rst_n,
  /// Destination domain data
  output data_t o_dst_data,
  /// Destination domain update pulse (new data this cycle)
  output logic  o_dst_update
);

  logic  src_capture;
  logic  dst_capture;
  data_t src_data_q;
  data_t dst_data_q;
  logic  dst_update_q;

  always_comb src_capture = i_src_en && !o_src_busy;

  axe_ccl_cdc_pulse #(
    .SyncStages (SyncStages)
  ) u_sync_p (
    .i_src_clk,
    .i_src_rst_n,
    .i_src_pulse (src_capture),
    .o_src_busy,
    .o_src_error (), // ASO-UNUSED_OUTPUT : No propagation of error if a request was dropped.

    .i_dst_clk,
    .i_dst_rst_n,
    .o_dst_pulse (dst_capture)
  );

  always_ff @ (posedge i_src_clk or negedge i_src_rst_n)
  if (!i_src_rst_n)     src_data_q <= ResetValue;
  else if (src_capture) src_data_q <= i_src_data;

  always_ff @ (posedge i_dst_clk or negedge i_dst_rst_n)
  if (!i_dst_rst_n) begin
    dst_data_q <= ResetValue;
    dst_update_q <= 1'b0;
  end
  else begin
    dst_update_q <= dst_capture;
    if (dst_capture)
      dst_data_q <= src_data_q;
  end

  always_comb o_dst_data   = dst_data_q;
  always_comb o_dst_update = dst_update_q;

endmodule
