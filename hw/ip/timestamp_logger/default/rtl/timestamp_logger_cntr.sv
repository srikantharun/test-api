// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Timestamp Logger counter, counter with scale that provides a scaled timestamp
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TIMESTAMP_LOGGER_CNTR_SV
`define TIMESTAMP_LOGGER_CNTR_SV

module timestamp_logger_cntr (
  input  wire  i_clk,
  input  wire  i_rst_n,

  input  logic                                                    i_cntr_en,
  input  logic                                                    i_cntr_rst,
  input  logic [timestamp_logger_pkg::TimeLogScaleW-1:0]          i_scale_val,
  output logic [timestamp_logger_pkg::TimeLogEntryTimestampW-1:0] o_timestamp
);

  logic [timestamp_logger_pkg::TimeLogCntrW-1:0]  cnt_d, cnt_q;

  // output assignment, shift bases on scale_val:
  always_comb o_timestamp = cnt_q >> i_scale_val; //cnt_q[i_scale_val+:timestamp_logger_pkg::TimeLogEntryTimestampW];

  always_comb cnt_d = cnt_q + 1;

  // counter flop:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : cntr_reg
    if (!i_rst_n) begin
      cnt_q       <= timestamp_logger_pkg::TimeLogCntrW'(0);
    end else begin
      if (i_cntr_rst)
        cnt_q     <= timestamp_logger_pkg::TimeLogCntrW'(0);
      else if (i_cntr_en)
        cnt_q     <= cnt_d;
    end
  end

endmodule

`endif  // TIMESTAMP_LOGGER_CNTR_SV
