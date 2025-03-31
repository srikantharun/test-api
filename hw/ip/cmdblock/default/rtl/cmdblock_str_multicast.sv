// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple stream multicaster, only accept slave when all master have accepted
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _CMDBLOCK_STR_MULTICAST_SV_
`define _CMDBLOCK_STR_MULTICAST_SV_

module cmdblock_str_multicast #(
  parameter int unsigned NR_OUTPUTS = 2
) (
  input wire i_clk,
  input logic i_rst_n,

  input  logic s_vld,
  output logic s_rdy,

  output logic [NR_OUTPUTS-1:0] m_vld,
  input  logic [NR_OUTPUTS-1:0] m_rdy
);

  reg [NR_OUTPUTS-1:0] rdy_rcvd;
  logic [NR_OUTPUTS-1:0] rdy_rcvd_en;
  logic all_rcvd;

  assign m_vld = {NR_OUTPUTS{s_vld}} & ~rdy_rcvd;
  assign s_rdy = all_rcvd;

  assign all_rcvd = &(rdy_rcvd | m_rdy);  // get flopped version, or current state

  // enable rdy_rcvd flop when all receveid or when slave is valid and output is ready
  assign rdy_rcvd_en = {NR_OUTPUTS{all_rcvd & s_vld}} | ({NR_OUTPUTS{s_vld}} & m_rdy);

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      rdy_rcvd <= '0;
    end else begin
      foreach (rdy_rcvd_en[i]) begin
        if (rdy_rcvd_en[i]) begin
          rdy_rcvd[i] <= (~all_rcvd) & m_rdy[i];
        end
      end
    end
  end


  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
  property p_vld_deassrtion_on_rdy(i_clk, i_rst_n, vld, rdy);
    @(posedge i_clk) disable iff (!i_rst_n) (vld & ~rdy) |=> vld;
  endproperty

  assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, s_vld, s_rdy))
  else $error("Protocol Violation: Valid was de-asserted without ready assertion");

  for (genvar i = 0; i < NR_OUTPUTS; i++) begin : gen_output_assertions
    assert property (p_vld_deassrtion_on_rdy(i_clk, i_rst_n, m_vld[i], m_rdy[i]))
    else $error("Protocol Violation: Valid was de-asserted without ready assertion");
  end

`endif  // ASSERTIONS_ON
  //synopsys translate_on


endmodule

`endif  // _CMDBLOCK_STR_MULTICAST_SV_
