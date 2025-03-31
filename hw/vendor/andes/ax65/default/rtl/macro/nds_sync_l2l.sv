// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary


module nds_sync_l2l (
  b_reset_n,
  b_clk,
  a_signal,
  b_signal,
  b_signal_rising_edge_pulse,
  b_signal_falling_edge_pulse,
  b_signal_edge_pulse
);

  parameter SYNC_STAGE = 2;
  parameter RESET_VALUE = 1'b0;

  input  b_reset_n;
  input  b_clk;
  input  a_signal;
  output b_signal;
  output b_signal_rising_edge_pulse;
  output b_signal_falling_edge_pulse;
  output b_signal_edge_pulse;

  axe_tcl_seq_sync #(
    .SyncStages(SYNC_STAGE),
    .ResetValue(RESET_VALUE)
  ) u_seq_sync (
    .i_clk(b_clk),
    .i_rst_n(b_reset_n),
    .i_d(a_signal),
    .o_q(b_signal)
  );

  logic b_signal_rising_edge_pulse;
  logic b_signal_falling_edge_pulse;
  logic b_signal_edge_pulse;
  logic b_signal_d1;

  always_ff @(negedge b_reset_n or posedge b_clk) begin
    if (!b_reset_n) begin
      b_signal_d1 <= RESET_VALUE;
    end
    else begin
      b_signal_d1 <= b_signal;
    end
  end

  always_comb b_signal_rising_edge_pulse = b_signal && !b_signal_d1;
  always_comb b_signal_falling_edge_pulse = !(b_signal || !b_signal_d1);
  always_comb b_signal_edge_pulse = b_signal ^ b_signal_d1;

endmodule
