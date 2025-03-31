// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Check inner padding
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_INNER_PAD_SV_
`define _IFD_ODR_INNER_PAD_SV_

module ifd_odr_inner_pad
  import ifd_odr_pkg::*;
#(
  parameter int unsigned COORD_W = 8,
  parameter int unsigned DIM_W_W = 8
) (
  input logic signed [COORD_W - 1 : 0] coord,
  input logic [DIM_W_W - 1 : 0] dim_w,
  input logic vect_pad,
  input logic [IFD_ODR_AG_MSK_START_DW - 1 : 0] msk_start,
  input logic [IFD_ODR_AG_MSK_END_DW - 1 : 0] msk_end,

  output logic [IFD_ODR_PWORD64_LEN - 1 : 0] inner_pad
);

  logic [IFD_ODR_AG_MSK_START_DW-1:0] c_msk_st;
  logic [IFD_ODR_AG_MSK_END_DW-1:0] c_msk_end;

  logic [2*IFD_ODR_PWORD64_LEN-1:0] lsb_mask_long;
  logic [IFD_ODR_PWORD64_LEN-1:0] lsb_mask;
  logic [2*IFD_ODR_PWORD64_LEN-1:0] msb_mask_long;  // upper half counts
  logic [IFD_ODR_PWORD64_LEN-1:0] msb_mask;

  // if vect_coord == 0: curr_mask_start = mask_start, 0 when pad is active
  assign c_msk_st = (vect_pad) ? 0 : ((coord == 0) ? msk_start : 0);
  // if vect_coord == vect_dim_width - 1: curr_mask_end = mask_end, 0 when pad is active
  assign c_msk_end = (vect_pad) ? 0 : ((unsigned'(coord) == (dim_w - 1)) ? msk_end : IFD_ODR_PWORD64_LEN);

  // shift in zero's for lower part (lsb size) of vec based on inner pad st coordinate
  assign lsb_mask_long = {{IFD_ODR_PWORD64_LEN{1'b1}}, {IFD_ODR_PWORD64_LEN{1'b0}}} << c_msk_st;
  assign lsb_mask = lsb_mask_long[2*IFD_ODR_PWORD64_LEN-1:IFD_ODR_PWORD64_LEN];
  // shift in ones for upper part (msb size) of vec based on inner pad st coordinate
  assign msb_mask_long = {{IFD_ODR_PWORD64_LEN{1'b0}}, {IFD_ODR_PWORD64_LEN{1'b1}}} << c_msk_end;
  assign msb_mask = msb_mask_long[2*IFD_ODR_PWORD64_LEN-1:IFD_ODR_PWORD64_LEN];

  // total inner padding is an and of both masks:
  assign inner_pad = lsb_mask & msb_mask;

endmodule

`endif  // _IFD_ODR_INNER_PAD_SV_
