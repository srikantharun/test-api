// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple register of variable size
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_REG_SV_
`define _CMDBLOCK_REG_SV_

module cmdblock_reg #(
  parameter int unsigned REG_W = 2
) (
  input wire i_clk,

  input logic en,
  input logic [((REG_W+7)/8)-1:0] byte_en,
  input logic [REG_W-1:0] d,
  output logic [REG_W-1:0] q
);

  localparam int NrBytes = (REG_W + 7) / 8;
  localparam int LastBw = (REG_W % 8) > 0 ? REG_W % 8 : 8;

  reg   [REG_W-1:0] d_q;
  logic [REG_W-1:0] d_masked;

  for (genvar b = 0; b < NrBytes; b++) begin : g_NrBytes
    if (b == unsigned'(NrBytes - 1))
      assign d_masked[LastBw+b*8-1:b*8] = (byte_en[b] == 1'b1) ? d[LastBw+b*8-1:b*8] : d_q[LastBw+b*8-1:b*8];
    else
      assign d_masked[(b+1)*8-1:b*8] = (byte_en[b] == 1'b1) ? d[(b+1)*8-1:b*8] : d_q[(b+1)*8-1:b*8];
  end

  // Used as memory (either descmem or FIFO), so no reset required for the data
  // spyglass disable_block STARC05-3.3.1.4b
  // spyglass disable_block STARC-2.3.4.3
  always_ff @(posedge i_clk) begin
    if (en == 1'b1) begin
      d_q <= d_masked;
    end
  end
  // spyglass enable_block STARC-2.3.4.3
  // spyglass enable_block STARC05-3.3.1.4b
  assign q = d_q;

endmodule
`endif  // _CMDBLOCK_REG_SV_
