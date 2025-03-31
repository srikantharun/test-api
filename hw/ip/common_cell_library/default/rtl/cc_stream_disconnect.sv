// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Disconnect a stream, optionally drop input stream items via the handshaking when disconnected.
///
module cc_stream_disconnect #(
  /// The data width if the default of parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type data_t = logic[DataWidth-1:0]
)(
  /// Enable the disconnect of the downstream, should be stable in regards to `valid_i`
  input  logic  i_disconnect,
  /// Drop (filter) the item out of the input stream.
  /// This will drop regardless of `i_disconnect`!
  input  logic  i_drop,
  /// Indicats that an intput stream item was dropped
  output logic  o_dropped,
  /// Indicates that there was a transaction across the module.
  /// Does not trigger if `i_drop`
  output logic  o_transaction,
  /// Input stream data
  input  data_t i_data,
  /// Input stream valid
  input  logic  i_valid,
  /// Input stream ready
  output logic  o_ready,
  /// Output stream data
  output data_t o_data,
  /// Output stream valid
  output logic  o_valid,
  /// Output stream ready
  input  logic  i_ready
);
  // Add dropping functionality

  logic valid, ready;

  cc_stream_filter i_stream_filter (
    .i_drop,
    .o_dropped,
    .i_valid,
    .o_ready,
    .o_valid(valid),
    .i_ready(ready)
  );

  // Disconnect if asserted
  always_comb o_data  = i_disconnect ? '0   : i_data;
  always_comb o_valid = i_disconnect ? 1'b0 :   valid;
  always_comb   ready = i_disconnect ? 1'b0 : i_ready;

  // Observability
  always_comb o_transaction = ready & o_valid;
endmodule
