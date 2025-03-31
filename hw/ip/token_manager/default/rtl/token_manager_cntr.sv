// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Counter for the token manager
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TOKEN_MGR_CNTR_SV
`define TOKEN_MGR_CNTR_SV

module token_manager_cntr #(
  parameter bit          ResetValueAtConsume = 0,
  parameter int unsigned CounterWidth        = 8
)(
  input wire                      i_clk,
  input wire                      i_rst_n,

  // token interface:
  input  logic                    i_prod_valid,
  output logic                    o_prod_ready,
  input  logic [CounterWidth-1:0] i_incr_value,

  output logic                    o_cons_valid,
  input  logic                    i_cons_ready,

  output logic [CounterWidth-1:0] o_current_cnt,
  output logic                    o_saturated
);

  logic [CounterWidth-1:0] cnt_q;
  logic [CounterWidth-1:0] cnt_q_decr;
  logic [CounterWidth  :0] cnt_q_incr;
  logic [CounterWidth-1:0] cnt_d;
  logic cnt_en;

  logic cnt_sat;
  logic cnt_zero_n;

  assign cnt_sat    = (cnt_q == {CounterWidth{1'b1}});
  assign cnt_zero_n = (|cnt_q);

  assign o_cons_valid = cnt_zero_n;
  assign o_prod_ready = ~cnt_sat;
  assign o_saturated  = cnt_sat;

  assign cnt_en = (i_cons_ready & cnt_zero_n) | (i_prod_valid & (~cnt_sat));

  assign o_current_cnt = cnt_q;

  always_comb begin : proc_cnt_decr_check
    if (i_cons_ready & cnt_zero_n) begin  // can decrease
      if (ResetValueAtConsume) begin  // destructive read resets count to 0
        cnt_q_decr = 0;
      end else begin
        cnt_q_decr = cnt_q - 1;
      end
    end else begin
      cnt_q_decr = cnt_q;
    end
  end

  always_comb begin : proc_cnt_incr_check
    if (i_prod_valid & (~cnt_sat)) begin  // can increase
      cnt_q_incr = {'0, cnt_q_decr} + {'0, i_incr_value};
    end else begin
      cnt_q_incr = {'0, cnt_q_decr};
    end
  end

  // overflow check
  assign cnt_d = (cnt_q_incr[CounterWidth]) ? '1 : cnt_q_incr[CounterWidth-1:0];

  // flop result:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : proc_cnt_reg
    if (!i_rst_n) begin
      cnt_q <= '0;
    end else begin
      if (cnt_en == 1'b1) cnt_q <= cnt_d;
    end
  end

endmodule

`endif  // TOKEN_MGR_CNTR_SV
