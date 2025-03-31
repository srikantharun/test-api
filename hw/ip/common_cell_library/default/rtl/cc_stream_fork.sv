// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Fork a stream to multiple stream handshakes. The output handshakes can be masked.
///
module cc_stream_fork #(
  /// The number of input streams to fork
  parameter int unsigned NumStreams = 0
)(
  /// Clock, positive edge triggered.
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk
  /// Flush the state of the internal registers.
  input  logic i_flush,
  /// Enable bit mask on which streams should be forked.
  /// If not selected an input handshake does not happen.
  ///
  /// This should be also handshaked with the input stream or set statically.
  input  logic [NumStreams-1:0] i_select,
  /// Valid from the input stream
  input  logic i_valid,
  /// Ready from the input stream
  output logic o_ready,
  /// Valids of the output streams
  output logic [NumStreams-1:0] o_valid,
  /// Readies from the output streams
  input  logic [NumStreams-1:0] i_ready
);
  /////////////////////////////////
  // Parameters and Sanitization //
  /////////////////////////////////
  if (NumStreams == 0) $fatal(1, "Parameter `NumStreams` has to be larger than 0.");

  // State to keep track of each stream handshake status
  logic                  wait_q[NumStreams];
  logic                  wait_d[NumStreams];
  logic [NumStreams-1:0] update;

  ///////////////////////////////////////
  // There is any valid select present //
  ///////////////////////////////////////
  logic       select_is_sane;
  always_comb select_is_sane = |i_select;

  ///////////////////////////////////////////////
  // Flags if there are transactions happening //
  ///////////////////////////////////////////////
  logic                  inp_transaction;
  logic [NumStreams-1:0] oup_transaction;
  logic [NumStreams-1:0] oup_transferred;

  always_comb inp_transaction = i_valid & o_ready;

  //////////////////////////////
  // Control the input stream //
  //////////////////////////////
  always_comb o_ready = select_is_sane & (&oup_transferred);

  /////////////////////////////////
  // State of each output stream //
  /////////////////////////////////
  for (genvar stream_idx = 0; unsigned'(stream_idx) < NumStreams; stream_idx++) begin : gen_oup_state
    always_comb oup_transaction[stream_idx] = o_valid[stream_idx] & i_ready[stream_idx];

    always_comb o_valid[stream_idx]         = ~wait_q[stream_idx]
                                            &  i_select[stream_idx]
                                            &  i_valid;

    always_comb oup_transferred[stream_idx] =  wait_q[stream_idx]
                                            | ~i_select[stream_idx]
                                            | oup_transaction[stream_idx];

    always_comb wait_d[stream_idx]          = wait_q[stream_idx]
                                            ? (~inp_transaction)                                // Go back to ready on input transaction
                                            : (~inp_transaction & oup_transaction[stream_idx]); // Wait if we transfer output, but not input

    always_comb update[stream_idx]          = wait_d[stream_idx] ^ wait_q[stream_idx];
  end

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)     foreach (wait_q[stream_idx]) wait_q[stream_idx] <= 1'b0;
    else if (i_flush) foreach (wait_q[stream_idx]) wait_q[stream_idx] <= 1'b0;
    else if (|update)                              wait_q             <= wait_d;
  end
endmodule
