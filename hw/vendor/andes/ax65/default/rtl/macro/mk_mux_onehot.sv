// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary

module mk_mux_onehot (
  out,
  sel,
  in
);
  parameter N = 2;
  parameter W = 8;

  output [W - 1:0] out;
  input [N - 1:0] sel;
  input [(N * W) - 1:0] in;

  axe_ccl_mux_onehot #(
    .DataWidth(W),
    .NumInputs(N)
  ) u_mux_onehot (
    .i_data(in),
    .i_select(sel),
    .o_data(out)
  );

endmodule
