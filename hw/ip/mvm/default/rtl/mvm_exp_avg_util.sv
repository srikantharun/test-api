// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple exponential averaging filter
// util_average_o[k] = util_average_o[k-1]*(util_average_nominator_i/MVM_UTIL_EXP_AVG_DENOMINATOR) + util_value_i[k]*((util_average_nominator_i-MVM_UTIL_EXP_AVG_DENOMINATOR)/MVM_UTIL_EXP_AVG_DENOMINATOR)
// Owner: Roel Uytterhoeven <roel.uytterhoeven@axelera.ai>

`ifndef MVM_EXP_AVG_UTIL
`define MVM_EXP_AVG_UTIL

module mvm_exp_avg_util
  import imc_bank_pkg::*;
  import mvm_pkg::*;
(
  input wire i_clk,
  input wire i_rst_n,

  input logic enable_filter_i,

  // Util input
  input logic util_valid_i,
  input logic [MVM_UTIL_WIDTH-1:0] util_value_i,

  // Exponential average
  input logic [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0] util_average_nominator_i,
  output logic [MVM_UTIL_WIDTH-1:0] util_average_o

);
  // verilog_lint: waive-start line-length
  logic [MVM_UTIL_WIDTH-1:0] util_value_new, util_average_q, util_average_next;
  logic [MVM_UTIL_WIDTH+MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0]
      util_average_high_res, util_average_high_res_scaled;
  logic [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH:0]
      rounding_error, rounding_error_next, rounding_error_q;
  logic rounding;

  // If util is not valid, the new util value for this cycle is 0 (basically, not valid means nop)
  assign util_value_new = util_valid_i ? util_value_i : '0;
  // Make the high resolution product of y[k-1]*a + (a-1)*x[k]
  assign util_average_high_res = util_average_q*util_average_nominator_i + (MVM_UTIL_EXP_AVG_DENOMINATOR-util_average_nominator_i)*util_value_new;
  // Keep track of the rounding errors introduced by bringing the high resultion product back to normal resolution
  assign rounding_error = rounding_error_q + util_average_high_res[$clog2(
      MVM_UTIL_EXP_AVG_DENOMINATOR
  )-1:0];
  // Compute next util_average by reducing the high res value back to normal resolution and adding the potential rounding bit
  assign util_average_high_res_scaled = (util_average_high_res >> $clog2(
      MVM_UTIL_EXP_AVG_DENOMINATOR
  )) + rounding;
  assign util_average_next = util_average_high_res_scaled[MVM_UTIL_WIDTH-1:0];
  // Decide whether we have to set the rounding bit to 1
  always_comb begin
    rounding = 1'b0;
    rounding_error_next = rounding_error;
    if (rounding_error >= MVM_UTIL_EXP_AVG_DENOMINATOR) begin
      rounding_error_next = rounding_error - MVM_UTIL_EXP_AVG_DENOMINATOR;
      rounding = 1'b1;
    end
  end

  // If the filter is not enabled, tie the output
  assign util_average_o = enable_filter_i ? util_average_q : '0;

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      util_average_q   <= '0;
      rounding_error_q <= '0;
    end else begin
      if (enable_filter_i) begin
        util_average_q   <= util_average_next;
        rounding_error_q <= rounding_error_next;
        // Disabling the filter, resets its internal state
      end else begin
        util_average_q   <= '0;
        rounding_error_q <= '0;
      end
    end
  end
  // verilog_lint: waive-stop line-length
endmodule

`endif  // MVM_EXP_AVG_UTIL
