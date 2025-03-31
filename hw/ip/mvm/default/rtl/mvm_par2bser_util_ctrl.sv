// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Controls the par2bser utilization
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_PAR2BSER_UTIL_CTRL_SV
`define MVM_PAR2BSER_UTIL_CTRL_SV

module mvm_par2bser_util_ctrl
  import imc_bank_pkg::*;
  import mvm_pkg::*;
  (
    input wire                                            i_clk,
    input wire                                            i_rst_n,

    // Current Utilization
    input logic                      [MVM_UTIL_WIDTH-1:0] i_current_util,
    input logic                                           i_current_util_valid,

    // Util limiting
    input logic            [MVM_UTIL_INTERFACE_WIDTH-1:0] i_util_limit_value,
    input logic                                           i_util_limit_enable,

    // Exponential average
    input  logic [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0] i_util_average_nominator,
    output logic           [MVM_UTIL_INTERFACE_WIDTH-1:0] o_util_average,

    output logic                                          o_util_limit_trigger_nop
  );

  logic [MVM_UTIL_WIDTH-1:0] util_average, util_limit_value;


  // Drop the lower bits for the signal that goes to the outside.
  always_comb o_util_average = util_average[MVM_UTIL_WIDTH-MVM_UTIL_INTERFACE_WIDTH +: MVM_UTIL_INTERFACE_WIDTH];
  // Shift the incoming util_limit value to match the internal resolution
  // Spyglass does not figure out that shifting increases the number of bits
  always_comb util_limit_value = i_util_limit_value << (MVM_UTIL_WIDTH - MVM_UTIL_INTERFACE_WIDTH);

  // Exponential filter on utilisation
  mvm_exp_avg_util inst_exp_avg_util (
    .i_clk,
    .i_rst_n,
    .enable_filter_i         (1'b1),
    // Util input
    .util_valid_i            (i_current_util_valid),
    .util_value_i            (i_current_util),
    // Exponential average
    .util_average_nominator_i(i_util_average_nominator),
    .util_average_o          (util_average)
  );

  // Comparator that decides to add extra stalls when the average util is above the set limit
  always_comb begin
    o_util_limit_trigger_nop = 1'b0;
    if (i_util_limit_enable) begin
      if (util_average > util_limit_value) begin
        o_util_limit_trigger_nop = 1'b1;
      end
    end
  end

endmodule

`endif  // MVM_PAR2BSER_UTIL_CTRL_SV
