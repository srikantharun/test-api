// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Fall-through register with a simple stream-like ready/valid handshake. This register does not cut
// combinatorial paths on any signals: in case the module at its output is ready to accept data
// within the same clock cycle, they are forwarded. Use this module to get a 'default ready'
// behavior towards the input.
//
// NOTE: In terms of latency-insensitive elastic channels, this module behaves like an elastic
// buffer with forward latency Lf = 0, backward latency Lb = 0, and capacity C = 1.
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>
module cc_stream_reg_el #(
  /// The data width of the default parameter `data_t logic[DataWidth-1:0]` is used.
  /// Not needed if `data_t` is specified.
  parameter int unsigned DataWidth      = 0,
  /// The actual data type used, only use of parameter `DataWidth`
  parameter type         data_t         = logic [DataWidth-1:0],
  /// Data FFs can be made non-resettable to save on reset network routing for wide data regs
  parameter bit          DataRegNoReset = 1'b0
) (
  /// Clock, positive edge triggered
  input  wire   i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  // doc sync i_clk
  /// Flush any active saved data
  input  logic  i_flush,
  /// The input data
  input  data_t i_data,
  /// Valid from the input stream
  input  logic  i_valid,
  /// Ready from the input stream
  output logic  o_ready,
  /// the output data
  output data_t o_data,
  /// Valid of the output stream
  output logic  o_valid,
  /// Ready from the output stream
  input  logic  i_ready
);

  data_t data_q;
  logic valid_enable, data_enable, valid_q;
  assign o_ready      = i_ready | ~valid_q;
  assign valid_enable = (i_valid ^ i_ready) & (i_valid ^ valid_q);
  assign data_enable  = i_valid & ~(valid_q ^ i_ready);

  // FFLARNC: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
`ifndef NO_SYNOPSYS_FF
  /* synopsys sync_set_reset "i_flush" */
`endif
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) valid_q <= '0;
    else if (i_flush) valid_q <= '0;
    else if (valid_enable) valid_q <= i_valid;
  end

  if (DataRegNoReset) begin : gen_non_rst_regs
    // FFLNR: D-Flip-Flop, load enable, no reset
    always_ff @(posedge i_clk) begin
      if (data_enable) data_q <= i_data;
    end
  end else begin : gen_rst_regs
    // FFL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) data_q <= data_t'(0);
      else if (data_enable) data_q <= i_data;
    end
  end

  // Return value from reg if present
  assign o_valid = i_valid | valid_q;
  assign o_data  = valid_q ? data_q : i_data;

endmodule
