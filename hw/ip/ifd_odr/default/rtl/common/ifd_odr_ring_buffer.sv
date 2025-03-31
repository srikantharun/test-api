// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: ring buffer block, modulo + retimable flops at end
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_ODR_RING_BUFFER_SV_
`define _IFD_ODR_RING_BUFFER_SV_

module ifd_odr_ring_buffer #(
  parameter int unsigned ADDR_W = 36,
  parameter int unsigned RB_AW = 32,
  parameter int unsigned ADDR_GR_BYTES = 64,
  parameter int unsigned RB_GR_BYTES = 64,
  parameter int unsigned RB_FLOPS = 2
) (
  input wire i_clk,

  input logic pipe_en,

  input logic [ADDR_W-1:0] addr_in,
  input logic [ RB_AW-1:0] ring_buff_size,

  output logic [ADDR_W-1:0] addr_out
);

  localparam int unsigned AddrGrW = $clog2(ADDR_GR_BYTES);
  localparam int unsigned RbGrW = $clog2(RB_GR_BYTES);

  logic [ADDR_W-1:0] addr_in_gran;  // granularity corrected
  logic [RB_AW-1:0] ring_buff_size_gran;  // granularity corrected

  logic [ADDR_W - 1 : 0] mod_result;
  reg [ADDR_W - 1 : 0] outp_q[RB_FLOPS];

  // replace lsb's with 0'for granularity
  assign addr_in_gran = {addr_in[ADDR_W-1:AddrGrW], {AddrGrW{1'b0}}};
  assign ring_buff_size_gran = {ring_buff_size[RB_AW-1:RbGrW], {RbGrW{1'b0}}};

  // actual mod:
  always_comb begin
    // no mod when size is 0:
    if (ring_buff_size_gran == 0) mod_result = addr_in_gran;
    else mod_result = addr_in_gran % ring_buff_size_gran;
  end

  // flop storing the multiplication result (not rst needed as is data no control):
  // spyglass disable_block STARC05-3.3.1.4b
  // spyglass disable_block STARC-2.3.4.3
  always_ff @(posedge i_clk) begin
    if (pipe_en) begin
      for (int i = 0; unsigned'(i) < RB_FLOPS; i++) begin
        if (i == 0) outp_q[i] <= mod_result;
        else outp_q[i] <= outp_q[i-1];
      end
    end
  end
  // spyglass enable_block STARC-2.3.4.3
  // spyglass enable_block STARC05-3.3.1.4b

  assign addr_out = {outp_q[RB_FLOPS-1][ADDR_W-1:AddrGrW], {AddrGrW{1'b0}}};

endmodule

`endif  // _IFD_ODR_RING_BUFFER_SV_
