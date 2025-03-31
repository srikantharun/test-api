// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Check if coordinate is under-/overflowing or not
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_PAD_CHECK_SV_
`define _IFD_ODR_PAD_CHECK_SV_

module ifd_odr_pad_check #(
  parameter int unsigned COORD_W = 8,
  parameter int unsigned DIM_W_W = 8
) (
  // padding / cropping based on in_w/h and dim_w/h
  input  logic signed [COORD_W - 1 : 0] coord,
  input  logic        [DIM_W_W - 1 : 0] dim,
  input  logic                          vect_en,
  input  logic                          pad_mode,
  output logic                          pad,
  output logic signed [COORD_W - 1 : 0] coord_out
);

  logic signed [DIM_W_W:0] dim_signed;
  logic under, over;

  assign dim_signed = signed'({1'b0, dim});  // zero extend with 1 bit for signed conversion

  ////////////////////////////////////////////
  // under/over check:
  assign under = coord[COORD_W-1];  // check if negative by sign bit (underflow)
  assign over = (coord >= dim_signed);  // check if above dimension (overflow)

  ////////////////////////////////////////////
  // act on under / over:
  always_comb begin
    // default no padding:
    coord_out = coord;
    pad = 0;

    // check padding requirements:
    if ((!vect_en) && pad_mode == ifd_odr_pkg::IFD_ODR_PAD_MODE_EDGE) begin
      if (under) coord_out = 0;
      else if (over) coord_out = signed'(dim - 1);
    end else begin
      pad = under | over;
    end
  end
endmodule

`endif  // _IFD_ODR_PAD_CHECK_SV_
