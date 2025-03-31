// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary

module nds_rst_sync (
  test_mode,
  test_resetn_in,
  resetn_in,
  clk,
  resetn_out
);

  parameter  RESET_SYNC_STAGE = 2;

  input   test_mode;
  input   test_resetn_in;
  input   resetn_in;
  input   clk;

  output  resetn_out;

  wire i_rst_n;
  axe_tcl_clk_mux2 u_clk_mux (
    .i_clk0(resetn_in),
    .i_clk1(test_resetn_in),
    .i_sel(test_mode),
    .o_clk(i_rst_n)
  );

  axe_ccl_rst_n_sync #(
    .SyncStages(RESET_SYNC_STAGE)
  ) u_rst_n_sync (
    .i_clk(clk),
    .i_rst_n(i_rst_n),
    .i_test_mode(test_mode),
    .o_rst_n(resetn_out)
  );

endmodule
