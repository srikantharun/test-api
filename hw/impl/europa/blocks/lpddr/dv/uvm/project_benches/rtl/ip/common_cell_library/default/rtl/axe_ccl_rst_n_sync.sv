// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Reset syncrionizer, for asynchronous, active low, with test bypass
///
module axe_ccl_rst_n_sync #(
  /// The number of synchronier stages
  parameter int unsigned SyncStages = 3
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low, functional
  input  wire  i_rst_n,
  /// Test / Scan bypass enable of the reset
  input  logic i_test_mode,
  /// Synchronized active low reset
  output wire  o_rst_n
);

  wire rst_synced_n;

  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(1'b0)
  ) u_rst_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (1'b1),
    .o_q    (rst_synced_n)
  );

  wire rst_n;

  axe_tcl_clk_mux2 u_rst_mux_bypass (
    .i_clk0(rst_synced_n),
    .i_clk1(i_rst_n),
    .i_sel (i_test_mode),
    .o_clk (rst_n)
  );

  // Additional buffer to increase the drive strength
  axe_tcl_clk_buffer u_rst_buf (
    .i_clk(rst_n),
    .o_clk(o_rst_n)
  );
endmodule
