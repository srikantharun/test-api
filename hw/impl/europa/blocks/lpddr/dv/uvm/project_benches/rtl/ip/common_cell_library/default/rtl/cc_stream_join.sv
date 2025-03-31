// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Join together multiple stream handshakes into one. The input handshakes can be masked.
///
module cc_stream_join #(
  /// The number of input streams to join
  parameter int unsigned NumStreams = 0
)(
  /// Enable bit mask on which streams should be joined.
  /// If not selected an input handshake does not happen.
  ///
  /// This should be also handshaked from one of the input streams or set statically.
  input  logic [NumStreams-1:0] i_select,
  /// Valids from the input streams
  input  logic [NumStreams-1:0] i_valid,
  /// Readies from the input streams
  output logic [NumStreams-1:0] o_ready,
  /// Valid of the output stream
  output logic o_valid,
  /// Ready from the output stream
  input  logic i_ready
);
  // Parameter sanitization
  if (NumStreams == 0) $fatal(1, "Parameter: 'NumStreams' has to be larger than 0.");

  // Internal valid after masking
  logic [NumStreams-1:0] valid;
  // There is any valid select present
  logic  select_is_sane;
  assign select_is_sane = |i_select;
  // A transaction happens at the output
  logic  transaction;
  assign transaction = o_valid & i_ready;

  // Generate the input masking of the respective streams
  for (genvar i = 0; unsigned'(i) < NumStreams; i++) begin : gen_input_masking
    assign valid[i]   = i_select[i] ? i_valid[i]  : select_is_sane;
    assign o_ready[i] = i_select[i] ? transaction : 1'b0;
  end

  // Output valid assignment
  assign o_valid = &valid;

endmodule
