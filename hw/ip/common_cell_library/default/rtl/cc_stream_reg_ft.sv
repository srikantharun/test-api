// (C) Copyright 2022 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Stream module with a data register. Use to get `default ready` behaviour towards the input. Behaves as a 1-deep fall-through first in first out biffer.
///
module cc_stream_reg_ft #(
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
  // Registers to save data and if the data is valid.
  data_t data_q;
  logic  data_load;
  logic  valid_q;
  logic  valid_toggle;

  if (DataRegNoReset) begin : gen_non_rst_regs
    // DFFL: D-Flip-Flop, load enable
    always_ff @(posedge i_clk) begin
      if (data_load) data_q <= i_data;
    end
  end else begin : gen_rst_regs
    // DFFRL: D-Flip-Flop, asynchronous reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) data_q <= data_t'(0);
      else if (data_load) data_q <= i_data;
    end
  end

`ifndef NO_SYNOPSYS_FF
  /* synopsys sync_set_reset "i_flush" */
`endif
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) valid_q <= 1'b0;
    else if (i_flush) valid_q <= 1'b0;
    else if (valid_toggle) valid_q <= ~valid_q;
  end

  // Input output assignments depending on the state of the module
  assign o_ready = ~valid_q;
  assign o_data = valid_q ? data_q : i_data;
  assign o_valid = valid_q ? 1'b1 : i_valid;

  // Determine when to toggle the state
  assign valid_toggle = valid_q ? i_ready : (i_valid & ~i_ready);

  // Only load data if we go to valid state.
  assign data_load = ~valid_q & valid_toggle;
endmodule
