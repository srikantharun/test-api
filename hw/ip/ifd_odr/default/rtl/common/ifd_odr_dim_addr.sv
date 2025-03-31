// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Address calculation for dimension
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_DIM_ADDR_SV_
`define _IFD_ODR_DIM_ADDR_SV_

module ifd_odr_dim_addr #(
  parameter int unsigned INNER_STR_W = 8,
  parameter int unsigned INNER_LEN_W = 8,
  parameter int unsigned OUTER_STR_W = 8,
  parameter int unsigned OUTER_LEN_W = 8,
  parameter int unsigned DIM_OFF_W = 8,
  parameter int unsigned DIM_W_W = 8,
  parameter int unsigned COORD_W = 16,
  parameter int unsigned MEM_STRD_W = 16,
  parameter int unsigned ADDR_W = 16
) (
  input wire                               i_clk,
  input wire                               i_rst_n,
  // inner loop:
  input logic                              inner_incr,
  input logic                              inner_set0,
  input logic signed [INNER_STR_W - 1 : 0] inner_strd,
  // outer loop:
  input logic                              outer_incr,
  input logic                              outer_set0,
  input logic signed [OUTER_STR_W - 1 : 0] outer_strd,
  // offset:
  input logic signed [  DIM_OFF_W - 1 : 0] offset,
  // control:
  input logic        [    DIM_W_W - 1 : 0] dim_w,
  input logic                              vect_en,
  input logic                              pad_mode,
  input logic                              pipe_en,

  // memory:
  input logic [MEM_STRD_W - 1 : 0] mem_strd,

  // result:
  output logic [COORD_W - 1 : 0] coord_out,
  output logic [ADDR_W - 1 : 0] addr_out,
  output logic pad
);

  localparam int unsigned CoorMulStrdW = MEM_STRD_W + COORD_W;

  logic signed [COORD_W-1:0] coord;
  logic signed [COORD_W-1:0] coord_pad;
  reg [COORD_W-1:0] coord_q;

  logic [CoorMulStrdW-1:0] mul_res;

  logic pad_chk;
  reg pad_q;

  ifd_odr_coord_calc #(
    .INNER_STR_W(INNER_STR_W),
    .INNER_LEN_W(INNER_LEN_W),
    .OUTER_STR_W(OUTER_STR_W),
    .OUTER_LEN_W(OUTER_LEN_W),
    .DIM_OFF_W(DIM_OFF_W),
    .COORD_W(COORD_W)
  ) u_coord_calc (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    // kernel loop:
    .inner_incr(inner_incr),
    .inner_set0(inner_set0),
    .inner_strd(inner_strd),
    // outer loop:
    .outer_incr(outer_incr),
    .outer_set0(outer_set0),
    .outer_strd(outer_strd),
    // offset:
    .offset(offset),
    .coord(coord)
  );

  ifd_odr_pad_check #(
    .COORD_W(COORD_W),
    .DIM_W_W(DIM_W_W)
  ) u_pad_chk (
    .coord(coord),
    .dim(dim_w),
    .vect_en(vect_en),
    .pad_mode(pad_mode),
    .pad(pad_chk),
    .coord_out(coord_pad)
  );

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      coord_q <= '0;
      pad_q   <= '0;
    end else if (pipe_en) begin
      coord_q <= unsigned'(coord_pad);
      pad_q   <= pad_chk;
    end
  end

  assign pad = pad_q;

  // wider LHS is needed for a proper mul
  // spyglass disable_block W164b
  assign mul_res = coord_q * mem_strd;
  // spyglass enable_block W164b

  assign coord_out = coord_q;
  assign addr_out = mul_res[ADDR_W-1:0];  // truncate to addr_w

endmodule

`endif  // _IFD_ODR_DIM_ADDR_SV_
