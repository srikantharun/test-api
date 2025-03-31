// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: loop counter
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_LOOP_CNT_SV_
`define _IFD_ODR_LOOP_CNT_SV_

module ifd_odr_loop_cnt #(
  parameter int unsigned VAL_W = 8
) (
  input  wire              i_clk,
  input  wire              i_rst_n,
  // count:
  input  logic             start,
  input  logic             decr,
  input  logic [VAL_W-1:0] cfg_val,
  output logic             zero,
  output logic             mul_incr,
  output logic             mul_set0
);

  logic [VAL_W - 1 : 0] cnt_nxt;
  reg   [VAL_W - 1 : 0] cnt_q;
  logic                 cnt_zero;

  assign mul_incr = decr & ~cnt_zero;
  assign mul_set0 = decr & cnt_zero | start;

  // flop storing the multiplication result:
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      cnt_q <= 0;
    end else begin
      if (start | decr) cnt_q <= cnt_nxt;
    end
  end

  // zero check: simple inverted reduce orr
  assign cnt_zero = ~|cnt_q;

  always_comb begin : cnt_nxt_det
    if (start | cnt_zero) cnt_nxt = cfg_val - 1;
    else cnt_nxt = cnt_q - 1;
  end

  assign zero = cnt_zero;
endmodule

`endif  // _IFD_ODR_LOOP_CNT_SV_
