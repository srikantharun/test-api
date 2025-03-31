// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_DIST_MUX_SINGLE_OUT
`define MVM_DIST_MUX_SINGLE_OUT

module mvm_dist_mux_single_out
  import imc_bank_pkg::*;
  import mvm_pkg::*;
#(
  parameter int unsigned OR_DATA = 0,
  parameter int unsigned DATA_WIDTH = 8
) (
  input logic [DATA_WIDTH-1:0] in_0,
  input logic in_0_valid,

  input logic [DATA_WIDTH-1:0] in_1,
  input logic in_1_valid,

  output logic [DATA_WIDTH-1:0] out_data

);

  // Unconnected OK: valids are not used if OR_DATA == 1
  logic unconnected_ok_valids;

  // The OR-ed data mux expects that either of the two data inputs is already gated using the valid signal higher up the stream.
  if (OR_DATA == 1) begin : g_or_ed_data_mux
    assign out_data = in_0 | in_1;
    assign unconnected_ok_valids = &{in_0_valid, in_1_valid};
    // The gating data mux explicitly gates the data when no input is valid.
  end else begin : g_gating_data_mux
    always_comb begin
      out_data = '0;
      if (in_0_valid) begin
        out_data = in_0;
      end
      if (in_1_valid) begin
        out_data = in_1;
      end
    end
  end

endmodule

`endif  // MVM_DIST_MUX_SINGLE_OUT
