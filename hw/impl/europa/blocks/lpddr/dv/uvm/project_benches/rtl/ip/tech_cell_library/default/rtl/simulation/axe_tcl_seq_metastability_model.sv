// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Description: Simulation models which are shared for all implementations of `axe_tcl_seq`

/// Module to simulate simulation metastability
///
/// This will randomly add a cycle delay to the input signal.
module axe_tcl_seq_metastability_model #(
  /// Reset Value
  parameter bit ResetValue = 0,
  /// The probability of metastability
  ///
  /// This follows the formula one metastability event every `1 / (Ratio+1)` cycles.
  parameter int unsigned Ratio = 99
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk
  /// State input
  input  logic i_q,
  /// State output
  output logic o_q
);

  `ifndef SYNTHESIS
    logic reg_q2;

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) reg_q2 <= ResetValue;
      else          reg_q2 <= i_q;
    end

    always_comb begin : proc_metastability_probability
      randcase
        Ratio : o_q = i_q;
        1     : o_q = reg_q2;
      endcase
    end

  `else
    assign o_q = i_q;
  `endif
endmodule
