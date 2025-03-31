// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary

module nds_onehot2bin (
  out,
  in
);
  parameter N = 8;
  localparam W = $clog2(N);

  output   [W-1:0] out;
  input    [N-1:0] in;

  logic unused_empty;
  logic unused_error;

  cc_decode_onehot #(
    .OhtWidth(N)
  ) u_decode_onehot (
    .i_onehot(in),
    .o_binary(out),
    .o_empty(unused_empty),
    .o_error(unused_error)
  );

endmodule

