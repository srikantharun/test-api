// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Single input buffer for the par2bser conversion
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_INP_BUF_REG_SV
`define MVM_INP_BUF_REG_SV

module mvm_inp_buf_reg #(
  parameter int unsigned DATA_W = 8,
  parameter int unsigned PW_LEN = 64,
  parameter int unsigned GATE_GRANULARITY = 32
) (
  input wire i_clk,
  input wire i_rst_n,
  // input data, 1 p-word of 8bit words
  input logic [PW_LEN - 1:0] [DATA_W - 1 : 0] inp_buf_pw_i,
  // write enable to buffer
  input logic inp_buf_we_i,
  // n-hot encoded
  input logic [PW_LEN/GATE_GRANULARITY-1:0] inp_buf_group_enable_i,
  output logic [PW_LEN - 1:0] [DATA_W - 1 : 0] inp_buf_oup_o
);
  localparam int unsigned NumGates = PW_LEN / GATE_GRANULARITY;  // =2

  logic [NumGates-1:0][PW_LEN/NumGates-1:0][DATA_W-1:0] inp_buf_reg;
  //logic [DATA_W-1:0] inp_buf_next [0:NumGates-1][0:PW_LEN/NumGates-1];
  //[DATA_W-1:0] inp_buf_reg [0:NumGates-1][0:PW_LEN/NumGates-1]

  // Input buffer does not need reset, content is only valid after explicit write
  for (genvar i = 0; i < NumGates; i++) begin : gen_gating_registers
    always_ff @(posedge i_clk) begin
      // if (!i_rst_n) begin
      // not resetting inp_buf_reg.
      // Valid signalling + input gating should make sure that only
      // input buffer words that have been written prior are
      // used in the processing.
      if (inp_buf_we_i) begin
        for (int k = 0; k < PW_LEN / NumGates; k++)
          inp_buf_reg[i][k] <= inp_buf_pw_i[k+(i*GATE_GRANULARITY)];  //inp_buf_next[i][k];
      end
    end
  end

  always_comb begin
    for (int j = 0; j < NumGates; j++) begin
      //inp_buf_next[j] = inp_buf_pw_i[(j+1)*GATE_GRANULARITY-1:j*GATE_GRANULARITY];
      for (int k = 0; k < PW_LEN / NumGates; k++)
        inp_buf_oup_o[k+(j*GATE_GRANULARITY)] = inp_buf_reg[j][k];
    end
  end



endmodule

`endif  // MVM_INP_BUF_REG_SV
