// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//        Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Monitors the minimum and maximum values of unsigned data.
///
module axe_ccl_mon_minimum_maximum #(
  /// Data Width to be monitored
  parameter int unsigned DataWidth = 8
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk
  /// Synchronous clear for data_min
  input  logic i_clear_min,
  /// Synchronous clear for data_max
  input  logic i_clear_max,
  /// Enable monitoring
  input  logic i_enable,
  /// Input data to monitor
  input  logic unsigned [DataWidth-1:0] i_data,
  /// Minimum captured data out
  output logic unsigned [DataWidth-1:0] o_data_min,
  /// Maxmimum captured data out
  output logic unsigned [DataWidth-1:0] o_data_max
);
  //////////////////////////
  // Parameter SAnitation //
  //////////////////////////
  if (DataWidth == 0) $fatal(1, "Parameter: 'DataWidth' must be larger than 0;");

  ///////////////////
  // Functionality //
  ///////////////////
  logic below_old_min;
  logic above_old_max;

  logic [DataWidth-1:0] data_min_q;
  logic [DataWidth-1:0] data_max_q;

  logic [DataWidth-1:0] clear_value_min;
  logic [DataWidth-1:0] clear_value_max;

  always_comb below_old_min = unsigned'(i_data) < unsigned'(data_min_q);
  always_comb above_old_max = unsigned'(i_data) > unsigned'(data_max_q);

  // TODO(@tiago.campos): Do we want different synchronous reset behaviour depending on the enabled state?
  always_comb clear_value_min = i_enable ? i_data : '1;
  always_comb clear_value_max = i_enable ? i_data : '0;

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                      data_min_q <= '1;
    else if (i_clear_min)              data_min_q <= clear_value_min;
    else if (i_enable & below_old_min) data_min_q <= i_data;
  end

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                       data_max_q <= '0;
    else if (i_clear_max)               data_max_q <= clear_value_max;
    else if (i_enable & above_old_max)  data_max_q <= i_data;
  end

  ////////////////////////
  // Output Assignments //
  ////////////////////////
  always_comb o_data_min = data_min_q;
  always_comb o_data_max = data_max_q;
endmodule
