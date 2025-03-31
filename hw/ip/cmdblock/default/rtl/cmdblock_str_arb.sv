// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Simple 2-1 arbiter for streams, if PRIO scheme is 0 slave 0 always has priority, else round robin
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_STR_ARB_SV_
`define _CMDBLOCK_STR_ARB_SV_

module cmdblock_str_arb #(
  parameter int unsigned PRIO = 0
) (
  input wire i_clk,
  input logic i_rst_n,

  output logic sel,

  input  logic vld_s0,
  output logic rdy_s0,
  input  logic vld_s1,
  output logic rdy_s1,

  output logic vld_m,
  input  logic rdy_m
);

  logic sel_vld;

  logic str_sel;
  logic str_sel_en;
  reg   str_sel_q;

  always_comb begin : arb
    str_sel    = 'b0;
    str_sel_en = 'b0;
    if (PRIO == 0) begin  // fixed highest prio on slave 0
      if (vld_s0 == 1'b1) str_sel = 1'b0;
      else  //if (vld_s1 == 1'b1)
        str_sel = 1'b1;
    end else begin  // round robin
      // save selected slave once accepted
      if ((sel_vld == 1'b1) && (rdy_m == 1'b1)) str_sel_en = 1'b1;

      if ((vld_s0 == 1'b1) && (vld_s1 == 1'b1))  // both valid, take other then last access
        str_sel = ~str_sel_q;
      else if (vld_s0 == 1'b1) str_sel = 1'b0;
      else  //if (vld_s1 == 1'b1)
        str_sel = 1'b1;
    end
  end

  if (PRIO == 0) begin : g_prio_0
    wire i_clk_nc, i_rst_n_nc, not_connected;
    // spyglass disable_block W528
    assign not_connected = str_sel | str_sel_en;
    assign i_clk_nc = i_clk;
    assign i_rst_n_nc = i_rst_n;
    // spyglass enable_block W528
  end else begin: g_prio
    always_ff @(posedge i_clk, negedge i_rst_n) begin : i_rr_sel_reg
      if (i_rst_n == 1'b0) begin
        str_sel_q <= '0;
      end else begin
        if (str_sel_en == 1'b1) begin
          str_sel_q <= str_sel;
        end
      end
    end
  end

  assign sel_vld = (str_sel == 1'b0) ? vld_s0 : vld_s1;
  assign rdy_s0 = (str_sel == 1'b0) ? rdy_m : '0;
  assign rdy_s1 = (str_sel == 1'b1) ? rdy_m : '0;

  assign vld_m = sel_vld;

  assign sel = str_sel;
endmodule

`endif  // _CMDBLOCK_STR_ARB_SV_
