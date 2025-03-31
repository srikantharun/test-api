// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Select one of several input streams.
///
module cc_stream_mux #(
  /// The data width if the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of input streams to select from
  parameter int unsigned NumStreams = 0,
  /// The selection data type. Represents the select index.
  localparam type select_t = logic[cc_math_pkg::index_width(NumStreams)-1:0]
)(
  /// Select the desired input. Ideally should be stable in regards to `o_valid`.
  input  select_t i_select,
  /// Indicate that select is not properly set. The module is stalling.
  output logic o_error,
  /// The input data array
  input  data_t [NumStreams-1:0] i_data,
  /// Valids from the input streams
  input  logic [NumStreams-1:0] i_valid,
  /// Readies from the input streams
  output logic [NumStreams-1:0] o_ready,
  /// Selected output data
  output data_t o_data,
  /// Valid of the output stream
  output logic o_valid,
  /// Ready from the output stream
  input  logic i_ready
);
  ////////////////////////////
  // Parameter sanitization //
  ////////////////////////////
  if (NumStreams == 0)
      $fatal(1, "Parameter `NumStreams` has to be larger than 0.");
  if ($bits(data_t) == 0)
      $fatal(1, "Parameter `DataWidth` has to be larger than 0.");

  // Select the needed input data, guarding if statement ala styleguide to prevent accidental X
  logic  select_is_sane;
  assign select_is_sane = (i_select <= select_t'(NumStreams-1));
  assign o_error = ~select_is_sane & |i_valid;

  assign o_data  = select_is_sane ? i_data[i_select]  : '0;
  assign o_valid = select_is_sane ? i_valid[i_select] : 1'b0;
  assign o_ready = NumStreams'(i_ready & select_is_sane) << i_select;

endmodule


/// Select one of several unpacked input streams.
///
module cc_stream_mux_unpack #(
  /// The data width if the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of input streams to select from
  parameter int unsigned NumStreams = 0,
  /// The selection data type. Represents the select index.
  localparam type select_t = logic[cc_math_pkg::index_width(NumStreams)-1:0]
)(
  /// Select the desired input. Ideally should be stable in regards to `o_valid`.
  input  select_t i_select,
  /// Indicate that select is not properly set. The module is stalling.
  output logic o_error,
  /// The input data array
  input  data_t i_data[NumStreams],
  /// Valids from the input streams
  input  logic i_valid[NumStreams],
  /// Readies from the input streams
  output logic o_ready[NumStreams],
  /// Selected output data
  output data_t o_data,
  /// Valid of the output stream
  output logic o_valid,
  /// Ready from the output stream
  input  logic i_ready
);

  // pack and unpack the respective signals
  data_t [NumStreams-1:0] data;
  logic  [NumStreams-1:0] valid, ready;

  // Use of stream operator to unpack and pack the handshake
  always_comb  valid   = {<< {i_valid}};
  always_comb  o_ready = {<< {ready}};

  always_comb begin
    for (int unsigned stream_idx = 0; stream_idx < NumStreams; stream_idx++) begin
      data[stream_idx]  = i_data[stream_idx];
    end
  end

  cc_stream_mux #(
    .data_t    (data_t),
    .NumStreams(NumStreams)
  ) u_cc_stream_mux (
    .i_select,
    .o_error,
    .i_data  (data),
    .i_valid (valid),
    .o_ready (ready),
    .o_data,
    .o_valid,
    .i_ready
  );
endmodule
