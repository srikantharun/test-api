// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple stream block
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_STR_BLOCK_SV_
`define _CMDBLOCK_STR_BLOCK_SV_

module cmdblock_str_block (
  input logic block,

  input  logic sl_vld,
  output logic sl_rdy,

  output logic mt_vld,
  input  logic mt_rdy
);

  assign sl_rdy = mt_rdy & ~block;
  assign mt_vld = sl_vld & ~block;

endmodule

`endif  // _CMDBLOCK_STR_BLOCK_SV_
