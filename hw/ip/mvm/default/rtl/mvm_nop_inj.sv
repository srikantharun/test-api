// (C) Copyright Axelera AI 2025
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: NOP Injection, a quick response if nothing goes wrong
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_NOP_INJ_SV
`define MVM_NOP_INJ_SV

module mvm_nop_inj # (
    parameter type nop_inj_rate_t = logic [6:0]
  )
  (
    input wire           i_clk,
    input wire           i_rst_n,

    input nop_inj_rate_t i_nop_inj_rate,
    input logic          i_nop_inj_enable,

    output logic         o_inj_nop
  );

  logic cnt_clear;
  logic cnt_en;
  nop_inj_rate_t cnt_q;
  nop_inj_rate_t cnt_d;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : seq_nop_inj_cnt_proc
    if (!i_rst_n)       cnt_q <= '0;
    else if (cnt_clear) cnt_q <= '0;
    else if (cnt_en)    cnt_q <= cnt_d;
  end

  always_comb cnt_clear = !i_nop_inj_enable && |cnt_q;

  always_comb cnt_en = i_nop_inj_enable;

  always_comb cnt_d = cnt_q + nop_inj_rate_t'(1);

  always_comb begin : comb_nop_inj_proc
    o_inj_nop = 1'b0;
    if (i_nop_inj_enable) begin
      if (i_nop_inj_rate > cnt_q) begin
        o_inj_nop = 1'b1;
      end
    end
  end

endmodule

`endif  // MVM_NOP_INJ_SV
