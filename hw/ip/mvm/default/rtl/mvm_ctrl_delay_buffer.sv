// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Reusable delay buffer for MVM-DP ctrl signals. Type of ctrl bundle is set through parameter data_type_t
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_CTRL_DELAY_BUFFER_SV
`define MVM_CTRL_DELAY_BUFFER_SV

module mvm_ctrl_delay_buffer #(
  parameter int unsigned NB_DELAY_CYCLES = 1,
  // data type struct of tdata
  parameter type data_type_t = logic,
  // Halt the pipeline when m_tvalid is low
  //(WARNING: this prohibits the end of a transaction continue flowing through the buffer)
  parameter int unsigned BLOCKING = 0
) (

  input wire i_clk,
  input logic i_rst_n,

  // Slave AXIS interface
  input logic s_tvalid_i,
  input data_type_t s_tdata_i,
  output logic s_tready_o,
  // Master AXIS interface
  output logic m_tvalid_o,
  output data_type_t m_tdata_o,
  input logic m_tready_i

);

  // Delay registers
  logic [NB_DELAY_CYCLES-1:0] tvalid_reg;
  logic [NB_DELAY_CYCLES-1:0] tlast_reg;
  data_type_t [NB_DELAY_CYCLES-1:0] tdata_reg;

  // Output assignments
  // For now backpressure is not pipelined (this requires skidbuffer)
  assign s_tready_o = m_tready_i;
  assign m_tvalid_o = tvalid_reg[NB_DELAY_CYCLES-1];
  assign m_tdata_o = tdata_reg[NB_DELAY_CYCLES-1];

  logic write_enable;
  if (BLOCKING == 1) assign write_enable = m_tready_i & s_tvalid_i;
  else assign write_enable = m_tready_i;


  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      tvalid_reg <= '{NB_DELAY_CYCLES{1'b0}};
      tdata_reg  <= '{default: '0};
    end else if (write_enable) begin
      for (int i = 0; i < NB_DELAY_CYCLES; i++) begin
        if (i == 0) begin
          tvalid_reg[0] <= s_tvalid_i;
          tdata_reg[0]  <= s_tdata_i;
        end else begin
          tvalid_reg[i] <= tvalid_reg[i-1];
          tdata_reg[i]  <= tdata_reg[i-1];
        end
      end
    end
  end
endmodule



`endif  // MVM_CTRL_DELAY_BUFFER_SV
