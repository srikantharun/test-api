// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: mimic multiplier using loop var by increasing result everytime loop is increased
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_MUL_INCR_SV_
`define _IFD_ODR_MUL_INCR_SV_

module ifd_odr_mul_incr #(
  parameter int unsigned A_W = 8,
  parameter int unsigned B_W = 8
) (
  input  wire                           i_clk,
  input  wire                           i_rst_n,
  // kernel loop:
  input  logic                          a_incr,
  input  logic                          a_set0,
  input  logic signed [    B_W - 1 : 0] b,
  output logic signed [A_W+B_W - 1 : 0] res
);

  logic signed [A_W+B_W - 1 : 0] a_mul_b;
  reg signed   [A_W+B_W - 1 : 0] a_mul_b_q;

  // doing the 'multiplication'
  assign a_mul_b = a_mul_b_q + b;

  // flop storing the multiplication result:
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) a_mul_b_q <= 0;
    else begin
      if (a_set0) a_mul_b_q <= 0;
      else if (a_incr) a_mul_b_q <= a_mul_b;
    end
  end

  assign res = a_mul_b_q;

endmodule

`endif  // _IFD_ODR_MUL_INCR_SV_
