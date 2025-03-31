// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token produced block, will generate the tokens for a command after a DONE gets in
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_TOK_PROD_SV_
`define _CMDBLOCK_TOK_PROD_SV_

module cmdblock_tok_prod #(
  parameter int unsigned NR_TOK = 4,
  parameter int unsigned MAX_OUTST_CMDS = 4
) (
  input wire i_clk,
  input logic i_rst_n,

  input  logic                cmd_tok_vld,
  input  logic [NR_TOK-1 : 0] cmd_tok,
  output logic                cmd_tok_rdy,

  output logic [NR_TOK-1 : 0] tok_vld,
  input  logic [NR_TOK-1 : 0] tok_rdy,

  input logic cmd_done
);

  logic                cmd_fifo_rvld;
  logic                cmd_fifo_rrdy;
  logic [NR_TOK-1 : 0] cmd_fifo_rdata;

  logic                done_fifo_rvld;
  logic                done_fifo_rrdy;

  logic                unblock_cmd_vld;
  logic                unblock_cmd_rdy;

  logic [NR_TOK-1 : 0] str_cast_vld;
  logic [NR_TOK-1 : 0] str_cast_rdy;

  logic [NR_TOK-1 : 0] tok_wvld;
  logic [NR_TOK-1 : 0] tok_wrdy;

  // command FIFO, for all outstanding commands:
  cc_stream_buffer #(
    .DEPTH(MAX_OUTST_CMDS),
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

  // done FIFO:
  cc_stream_buffer #(
    .DEPTH(MAX_OUTST_CMDS),
    .DW(1),
    .USE_MACRO(0)
  ) i_data_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld(cmd_done),
    .wr_data(1'b0),
    .wr_rdy(),   // ASO-UNUSED_OUTPUT: ready not used

    .rd_rdy (done_fifo_rrdy),
    .rd_data(), // ASO-UNUSED_OUTPUT: data not used
    .rd_vld (done_fifo_rvld)
  );

  // block stream as long done fifo is empty:
  cmdblock_str_block i_str_block (
    .block(~done_fifo_rvld),

    .sl_vld(cmd_fifo_rvld),
    .sl_rdy(cmd_fifo_rrdy),

    .mt_vld(unblock_cmd_vld),
    .mt_rdy(unblock_cmd_rdy)
  );

  // pop item from done when command is consumed:
  always_comb done_fifo_rrdy = unblock_cmd_vld & unblock_cmd_rdy;

  // stream multicast:
  cmdblock_str_multicast #(
    .NR_OUTPUTS(NR_TOK)
  ) i_str_multicast (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .s_vld(unblock_cmd_vld),
    .s_rdy(unblock_cmd_rdy),

    .m_vld(str_cast_vld),
    .m_rdy(str_cast_rdy)
  );

  // drop item if data is 0, else pass to tok fifo:
  always_comb tok_wvld = str_cast_vld & cmd_fifo_rdata;
  always_comb str_cast_rdy = tok_wrdy | ~cmd_fifo_rdata;

  // token FIFO's (for shielding purposes)
  for (genvar i = 0; unsigned'(i) < NR_TOK; i++) begin : g_fifos
    cc_stream_buffer #(
      .DEPTH(2),
      .DW(1),
      .USE_MACRO(0)
    ) i_tok_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (tok_wvld[i]),
      .wr_data(1'b0),
      .wr_rdy (tok_wrdy[i]),

      .rd_rdy (tok_rdy[i]),
      .rd_data(), // ASO-UNUSED_OUTPUT: data not used
      .rd_vld (tok_vld[i])
    );
  end

endmodule

`endif  // _CMDBLOCK_TOK_PROD_SV_
