// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Selectively filter out (drop) stream items via the handshaking.
///
module cc_stream_filter (
  /// Drop (filter) the item out of the input stream
  input  logic i_drop,
  /// Indicats that an intput stream item was dropped
  output logic o_dropped,
  /// Input stream valid
  input  logic i_valid,
  /// Input stream ready
  output logic o_ready,
  /// Output stream valid
  output logic o_valid,
  /// Output stream ready
  input  logic i_ready
);
  assign o_dropped = i_drop & i_valid;
  assign o_valid   = i_drop ? 1'b0 : i_valid;
  assign o_ready   = i_drop ? 1'b1 : i_ready;

endmodule
