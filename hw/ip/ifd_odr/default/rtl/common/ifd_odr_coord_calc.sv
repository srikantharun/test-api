// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Coordination calculation, based on stride, dilation and offset
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_COOR_CALC_SV_
`define _IFD_ODR_COOR_CALC_SV_

`ifndef IFD_ODR_MAX
`define IFD_ODR_MAX(a, b) ((a)>(b)?(a):(b))
`endif
module ifd_odr_coord_calc #(
  parameter int unsigned INNER_STR_W = 8,
  parameter int unsigned INNER_LEN_W = 8,
  parameter int unsigned OUTER_STR_W = 8,
  parameter int unsigned OUTER_LEN_W = 8,
  parameter int unsigned DIM_OFF_W = 8,
  parameter int unsigned COORD_W = 16
) (
  input  wire                              i_clk,
  input  wire                              i_rst_n,
  // inner loop:
  input  logic                              inner_incr,
  input  logic                              inner_set0,
  input  logic signed [INNER_STR_W - 1 : 0] inner_strd,
  // outer loop:
  input  logic                              outer_incr,
  input  logic                              outer_set0,
  input  logic signed [OUTER_STR_W - 1 : 0] outer_strd,
  // offset:
  input  logic signed [  DIM_OFF_W - 1 : 0] offset,
  output logic signed [    COORD_W - 1 : 0] coord
);

  localparam int unsigned MulInnerW = INNER_STR_W + INNER_LEN_W;
  localparam int unsigned MulOuterW = OUTER_STR_W + OUTER_LEN_W;
  localparam int unsigned MulAddW = 1 + `IFD_ODR_MAX(MulInnerW, MulOuterW);
  localparam int unsigned ResW = 2 +
  `IFD_ODR_MAX(MulAddW, DIM_OFF_W);  // result with is independent of port, this is the ideal size

  logic signed [MulInnerW - 1 : 0] mul_inner_res;
  logic signed [MulOuterW - 1 : 0] mul_outer_res;
  logic signed [  MulAddW - 1 : 0] mul_add;
  logic signed [      ResW - 1 : 0] coord_res;

  // do the k * d with mul_incr
  ifd_odr_mul_incr #(
    .A_W(INNER_LEN_W),
    .B_W(INNER_STR_W)
  ) u_mul_krnl_d (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .a_incr(inner_incr),
    .a_set0(inner_set0),
    .b(inner_strd),
    .res(mul_inner_res)
  );

  // do the out * strd with mul_incr
  ifd_odr_mul_incr #(
    .A_W(OUTER_LEN_W),
    .B_W(OUTER_STR_W)
  ) u_mul_out_strd (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .a_incr(outer_incr),
    .a_set0(outer_set0),
    .b(outer_strd),
    .res(mul_outer_res)
  );

  // add the two multiplied numbers together with the offset to get the total result:
  // wider LHS is needed for a proper add
  // spyglass disable_block W164b
  assign mul_add = mul_inner_res + mul_outer_res;
  assign coord_res = mul_add + offset;
  // spyglass enable_block W164b

  // assign to output, this will either crop or extend the result:
  //spyglass disable_block W164a_a
  assign coord = coord_res;
  //spyglass enable_block W164a_a

endmodule

`endif  // _IFD_ODR_COOR_CALC_SV_
