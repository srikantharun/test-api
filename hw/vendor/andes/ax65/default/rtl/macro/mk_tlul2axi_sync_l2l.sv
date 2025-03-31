// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary

module mk_tlul2axi_sync_l2l (
  resetn,
  clk,
  d,
  q
);
  parameter SYNC_STAGE = 2;
  parameter RESET_VALUE = 1'b0;

  input resetn;
  input clk;
  input d;
  output q;

  axe_tcl_seq_sync #(
    .SyncStages(SYNC_STAGE),
    .ResetValue(RESET_VALUE)
  ) u_seq_sync (
    .i_clk(clk),
    .i_rst_n(resetn),
    .i_d(d),
    .o_q(q)
  );

endmodule
