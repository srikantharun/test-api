// Copyright (C) 2024, Andes Technology Corp. Confidential Proprietary

module atcaxi2tluh500_onehot2bin (
  out,
  in
);
  parameter N = 8;
  localparam W = $clog2(N);

  output   [W-1:0] out;
  input    [N-1:0] in;

  nds_onehot2bin #(
    .N(N)
  ) u_decode_onehot (
    .out(out),
    .in(in)
  );

endmodule
