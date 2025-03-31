// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// A shift register with arbitrary depth and enable for the flops
///
module cc_cnt_shift_reg #(
  /// The width of the data (optional)
  parameter int unsigned Width = 0,
  /// The actual data type that is used on the port
  parameter type data_t = logic[Width-1:0],
  /// The number of pipeline stages
  parameter int unsigned Stages = 0
)(
  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  /// Synchronous clear, resets the enable
  input  logic  i_clear,
  /// Stall the whole register, control and data stay put
  input  logic  i_stall,
  /// Data input
  input  data_t i_data,
  /// Input data is valid, enable the register chain
  input  logic  i_data_en,
  /// Output data
  output data_t o_data,
  /// Output data updated, shifted version of 'i_data_en'
  output logic  o_updated
);
  // parameter checks
  if ($bits(data_t) == 0) $fatal(1, "Parameter: '$bits(data_t)' has to be larger than 0;");

  // Internal data
  data_t [Stages:0] data_q;
  logic  [Stages:0] data_enable_q;

  logic  load_enable;
  assign load_enable = ~i_stall;

  // Input and output assignments
  assign data_q[0]        = i_data;
  assign data_enable_q[0] = i_data_en;

  assign o_data    = data_q[Stages];
  assign o_updated = data_enable_q[Stages] & load_enable;

  if (Stages > 0) begin : gen_reg
    for (genvar i = 0; unsigned'(i) < Stages; i++) begin : gen_stage
      // Control
      logic  load_control;
      assign load_control = load_enable & (data_enable_q[i+1]|data_enable_q[i]);

      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n)          data_enable_q[i+1] <= 1'b0;
        else if (i_clear)      data_enable_q[i+1] <= 1'b0;
        else if (load_control) data_enable_q[i+1] <= data_enable_q[i];
      end

      // Datapath
      logic  load_data;
      assign load_data = data_enable_q[i] & load_enable;

      always_ff @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n)       data_q[i+1] <= data_t'('0);
        else if (load_data) data_q[i+1] <= data_q[i];
      end
    end
  end : gen_reg
endmodule
