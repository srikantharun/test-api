// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Select one of several output streams.
///
module cc_stream_demux #(
  /// The number of input streams to select from
  parameter int unsigned NumStreams = 0,
  /// Drop input if the sect does fall out of the range
  parameter bit DropOnError = 0,
  /// The selection data type. Represents the select index.
  localparam type select_t = logic[cc_math_pkg::index_width(NumStreams)-1:0]
)(
  /// Valid of the input stream
  input  logic i_valid,
  /// Ready from the input stream
  output logic o_ready,
  /// Select the desired output. Ideally should be stable in regards to `valid_i`.
  input  select_t i_select,
  /// Indicate that select is not properly set. If `DropOnError == 1` the input stream item is **dropped**!
  output logic o_error,
  /// Valids from the output streams
  output logic [NumStreams-1:0] o_valid,
  /// Readies from the output streams
  input  logic [NumStreams-1:0] i_ready
);
  // Parameter sanitization
  if (NumStreams == 0)
      $fatal(1, "Parameter `NumStreams` has to be larger than 0.");

  // Guarding if statement ala styleguide to prevent accidental X
  logic  select_is_sane;
  assign select_is_sane = (i_select <= select_t'(NumStreams-1));
  assign o_error = ~select_is_sane & i_valid;

  assign o_valid = NumStreams'(i_valid & select_is_sane) << i_select;
  assign o_ready = select_is_sane ? i_ready[i_select] : DropOnError;

endmodule


/// Select one of several unpacked output streams.
///
module cc_stream_demux_unpack #(
  /// The data width if the default of parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of input streams to select from
  parameter int unsigned NumStreams = 0,
  /// Drop input if the sect does fall out of the range
  parameter bit DropOnError = 0,
  /// The selection data type. Represents the select index.
  localparam type select_t = logic[cc_math_pkg::index_width(NumStreams)-1:0]
)(
  /// Input stream payload
  input  data_t   i_data,
  /// Select the desired output. Ideally should be stable in regards to `valid_i`.
  input  select_t i_select,
  /// Valid of the input stream
  input  logic    i_valid,
  /// Ready from the input stream
  output logic    o_ready,
  /// Indicate that select is not properly set. If `DropOnError == 1` the input stream item is **dropped**!
  output logic    o_error,
  /// Output stream data
  output data_t   o_data[NumStreams],
  /// Valids from the output streams
  output logic    o_valid[NumStreams],
  /// Readies from the output streams
  input  logic    i_ready[NumStreams]
);
  // Parameter sanitization
  if (NumStreams == 0)
      $fatal(1, "Parameter `NumStreams` has to be larger than 0.");

  logic [NumStreams-1:0] select_onehot;
  logic [NumStreams-1:0] valid;
  logic [NumStreams-1:0] ready;

  // Use of stream operator to unpack and pack the handshake
  always_comb o_valid       = {<< {valid}};
  always_comb ready         = {<< {i_ready}};
  always_comb select_onehot = NumStreams'(i_valid && !o_error) << i_select;

  always_comb begin
    for (int unsigned oup_idx = 0; oup_idx < NumStreams; oup_idx++) begin
      o_data[oup_idx] = select_onehot[oup_idx] ? i_data : '0;
    end
  end

  cc_stream_demux #(
    .NumStreams (NumStreams),
    .DropOnError(DropOnError)
  ) u_cc_stream_mux (
    .i_valid,
    .o_ready,
    .i_select,
    .o_error,
    .o_valid (valid),
    .i_ready (ready)
  );
endmodule
