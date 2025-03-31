// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Stream module which handels the handshaking of multiple pieline stages.
///
module cc_stream_pipe_load #(
  /// The amount of pipeline stages ( > 0)
  parameter int unsigned NumStages = 0
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk
  /// Flush the pipeline, set all states to 0. This will deassert `o_valid`.
  /// If no flushing capabilities are needed, set to `1'b0`
  input  logic i_flush,
  /// Input handshake stream valid
  input  logic i_valid,
  /// Input handshake stream ready
  output logic o_ready,
  /// Load signal for the data pipeline registers
  /// Data starts in stage 0 and moves upwards in index!
  output logic [NumStages-1:0] o_load,
  /// State of a pipeline stage, contains valid data if `1'b1`
  /// Data starts in stage 0 and moves upwards in index!
  output logic [NumStages-1:0] o_state,
  /// Output handshake stream valid
  output logic o_valid,
  /// Output handshake stream ready
  input  logic i_ready
);
  ////////////////////////////
  // Parameter sanitization //
  ////////////////////////////
  if (NumStages == 0) $fatal(1, "Parameter: 'NumStages' has to be larger than 0.");

  //////////////////////////////////////
  // Internal signals for handshaking //
  //////////////////////////////////////
  logic [NumStages  :0] valid_q; // Valid shift register
  logic [NumStages  :0] ready;   // Back-pressure ready
  logic [NumStages-1:0] toggle;  // Toggle valid FF state

  /////////////////////////////
  // Connect port handshakes //
  /////////////////////////////
  assign valid_q[0]       = i_valid;
  assign o_ready          = ready[0];
  assign o_valid          = valid_q[NumStages];
  assign ready[NumStages] = i_ready;

  ////////////////////////////////////
  // Indicate the internal FF state //
  ////////////////////////////////////
  assign o_state = valid_q[NumStages:1];

  for (genvar i = 0; unsigned'(i) < NumStages; i++) begin : gen_stages
    // Find out if this stage is ready.
    // If there is nothing in the stage we can take a value.
    // If stage is occupied, then next stage needs to be ready.
    // Determine if the stage is loaded, a transaction happens
    // Toggle the state holding FF when needed
    assign o_load[i] = valid_q[i] &  ready[i];
    assign toggle[i] = valid_q[i+1] ? (ready[i+1] & ~o_load[i]) : o_load[i];
    assign ready[i]  = valid_q[i+1] ?  ready[i+1]               : 1'b1;

    // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)       valid_q[i+1] <= 1'b0;
      else if (i_flush)   valid_q[i+1] <= 1'b0;
      else if (toggle[i]) valid_q[i+1] <= ~valid_q[i+1];
    end
  end

endmodule
