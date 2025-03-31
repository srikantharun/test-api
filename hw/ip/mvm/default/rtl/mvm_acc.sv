// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Serial accumulator to produce full mvm output result using partial sum from imc banks.
// Owner: roel uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_ACC_SV
`define MVM_ACC_SV

module mvm_acc #(
  parameter int unsigned INP_WIDTH = 19,
  parameter int unsigned ACC_WIDTH = 34
) (
  input wire i_clk,
  input wire i_rst_n,
  input logic [INP_WIDTH - 1 : 0] imc_to_accum_i,  // 17b input coming from IMC
  input logic [3:0] ctrl_acc_shift_pos_i,  // 0-15, inp shift / mult
  input logic ctrl_acc_group_enable_i,  // enables or disables full accumulator, active High
  input logic ctrl_acc_output_enable_i,  // enables passing accumulator output to output buffer
  input logic ctrl_acc_clear_i,  // enables passing accumulator output to output buffer
  input logic ctrl_acc_signed_weights,
  input logic ctrl_acc_signed_inputs,
  input logic ctrl_acc_input_precision,
  output logic accum_valid_o,
  output logic [ACC_WIDTH - 1 : 0] accum_to_buf_o  // 26b output value
);

  logic [ACC_WIDTH - 1 : 0] acc_reg, acc_next, acc_next_gated;
  logic [ACC_WIDTH - 1 : 0] imc_input_padded, imc_input_shifted, imc_input_to_acc;
  logic ctrl_acc_output_enable_q;

  // Output enable delay register to align with accumulator output
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      ctrl_acc_output_enable_q <= '0;
    end else begin
      if (ctrl_acc_group_enable_i) begin
        ctrl_acc_output_enable_q <= ctrl_acc_output_enable_i;
      end
    end
  end

  // Accumulator register, does not need reset as output is gated when not valid.
  always_ff @(posedge i_clk) begin
    if (ctrl_acc_group_enable_i) begin
      acc_reg <= acc_next[ACC_WIDTH-1 : 0];
    end
  end

  logic highest_pos;
  assign highest_pos = ctrl_acc_input_precision ?
                       (ctrl_acc_shift_pos_i == 'd15) :
                       (ctrl_acc_shift_pos_i ==  'd7) ;

  // Sign extension and addition
  always_comb begin
    // Sign extension padding if weights are signed. This means that 17b output values are signed as well
    imc_input_padded = ctrl_acc_signed_weights
          ? {{ACC_WIDTH-INP_WIDTH{imc_to_accum_i[INP_WIDTH-1]}},imc_to_accum_i}
          : {{ACC_WIDTH-INP_WIDTH{1'b0}},imc_to_accum_i};
    // Shift to the correct bit serial position
    imc_input_shifted = imc_input_padded << ctrl_acc_shift_pos_i;
    // Check and account for signed inputs.
    imc_input_to_acc = (highest_pos & ctrl_acc_signed_inputs)
                     ? ~imc_input_shifted+1 : imc_input_shifted;
    acc_next_gated = acc_reg & ({ACC_WIDTH{~ctrl_acc_clear_i}});
    acc_next = acc_next_gated + imc_input_to_acc;
    accum_to_buf_o = ctrl_acc_output_enable_q ? acc_reg : '0;
    accum_valid_o = ctrl_acc_output_enable_q;
  end

endmodule

`endif  // MVM_ACC_SV
