// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Integrated Synchronization Cell
///
module axe_tcl_seq_sync #(
  /// Number of synchronization stages
  parameter int unsigned SyncStages = 3,
  /// Reset value
  parameter bit ResetValue = 0,
  /// The probability of metastability, see axe_tcl_seq_metastability_model
  parameter int unsigned Ratio = 99
)(
  /// Clock to synchronize to, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc async
  /// Data input
  input  logic i_d,
  // doc sync i_clk
  /// Synchronized data output
  output logic o_q
);

  /////////////////////////////
  // Print the configuration //
  /////////////////////////////
`ifdef AXE_TCL_PRINT_CONFIG
  $info(
    "\n",
    "#################################################################################\n",
    "# 'axe_tcl_seq_sync' instantiated with the configuration:\n",
    "#   SyncStages: %d\n", SyncStages,
    "#   ResetValue: %d\n", ResetValue,
    "#################################################################################"
  );
`endif

  logic [SyncStages-1:0] reg_q;

  if (SyncStages > 1) begin : gen_sync
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) reg_q <= {SyncStages{ResetValue}};
      else          reg_q <= {reg_q[SyncStages-2:0], i_d};
    end
  end : gen_sync
  else begin : gen_no_sync
    assign reg_q[0] = i_d;
  end : gen_no_sync

  `ifndef SYNTHESIS
    axe_tcl_seq_metastability_model #(
      .ResetValue(ResetValue),
      .Ratio     (Ratio)
    ) i_metastability_model (
      .i_clk,
      .i_rst_n,
      .i_q    (reg_q[SyncStages-1]),
      .o_q
    );
  `else
    assign o_q = reg_q[SyncStages-1];
  `endif
endmodule
