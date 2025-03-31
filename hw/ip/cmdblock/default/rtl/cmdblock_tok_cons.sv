// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token consumer block, will block stream until all token conditions have been met
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_TOK_CONS_SV_
`define _CMDBLOCK_TOK_CONS_SV_

module cmdblock_tok_cons #(
  parameter int unsigned NR_TOK = 4
) (
  input wire i_clk,
  input logic i_rst_n,

  input  logic                cmd_tok_vld,
  input  logic [NR_TOK-1 : 0] cmd_tok,
  output logic                cmd_tok_rdy,

  input  logic [NR_TOK-1 : 0] tok_vld,
  output logic [NR_TOK-1 : 0] tok_rdy,

  output logic block_cmd,
  input  logic cmd_snd,

  output logic wait_token,
  output logic [NR_TOK-1 : 0] pending_tokens
);

  logic                cmd_fifo_rvld;
  logic                cmd_fifo_rrdy;
  logic [NR_TOK-1 : 0] cmd_fifo_rdata;

  logic [NR_TOK-1 : 0] tok_rvld;
  logic [NR_TOK-1 : 0] tok_rrdy;

  logic                tokens_rcvd;
  logic                condition_met;

  // command FIFO, for all outstanding commands:
  cc_stream_buffer #(
    .DEPTH(2),
    .DW(NR_TOK),
    .USE_MACRO(0)
  ) i_cmd_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (cmd_tok_vld),
    .wr_data(cmd_tok),
    .wr_rdy (cmd_tok_rdy),

    .rd_rdy (cmd_fifo_rrdy),
    .rd_data(cmd_fifo_rdata),
    .rd_vld (cmd_fifo_rvld)
  );


  // block command when not all tokens have been received that are required:
  always_comb tokens_rcvd = &(~cmd_fifo_rdata | tok_rvld);
  always_comb wait_token = (~tokens_rcvd) & cmd_fifo_rvld;
  always_comb pending_tokens = cmd_fifo_rvld ? (cmd_fifo_rdata & ~tok_rvld) : '0;
  always_comb condition_met = tokens_rcvd & cmd_fifo_rvld;
  always_comb block_cmd = ~condition_met;
  always_comb tok_rrdy = cmd_fifo_rdata & {NR_TOK{condition_met & cmd_snd}};
  always_comb cmd_fifo_rrdy = cmd_fifo_rvld & condition_met & cmd_snd;

  // token FIFO's (for shielding purposes)
  for (genvar i = 0; unsigned'(i) < NR_TOK; i++) begin : g_fifos
    cc_stream_buffer #(
      .DEPTH(2),
      .DW(1),
      .USE_MACRO(0)
    ) i_tok_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (tok_vld[i]),
      .wr_data(1'b0),
      .wr_rdy (tok_rdy[i]),

      .rd_rdy (tok_rrdy[i]),
      .rd_data(), // ASO-UNUSED_OUTPUT: data not used
      .rd_vld (tok_rvld[i])
    );
  end

endmodule

`endif  // _CMDBLOCK_TOK_CONS_SV_
