// (C) Copyright 2023 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>


/// # Token spill reg wrapper
///
/// Generator wrapper around `spill_reg` that instantiates a spill_reg for each token pair in a token bus.
///
///
/// Breaks all combinational paths between its input and output stream. Acts as a two deep FIFO.
///
module token_cut #(
  /// The width of the data stream
  parameter int unsigned NumTokens = 1,
  /// Bypass the internal spill register.
  parameter bit Bypass = 1'b0
)(
  input  logic                 i_clk,
  input  logic                 i_rst_n,
  input  logic [NumTokens-1:0] i_s_valid,
  output logic [NumTokens-1:0] o_s_ready,
  output logic [NumTokens-1:0] o_m_valid,
  input  logic [NumTokens-1:0] i_m_ready
);
  if (NumTokens == 0) $fatal(1, "Parameter: 'NumTokens' Must bot be 0;");

  for (genvar g = 0; unsigned'(g) < NumTokens; g++) begin : gen_spill
    cc_stream_spill_reg #(
      .DataWidth(1),
      .Bypass   (Bypass)
    ) u_spill_register (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data ('0),
      .i_valid(i_s_valid[g]),
      .o_ready(o_s_ready[g]),
      .o_data (), // ASO-UNUSED_OUTPUT: not used
      .o_valid(o_m_valid[g]),
      .i_ready(i_m_ready[g])
    );
  end

endmodule
