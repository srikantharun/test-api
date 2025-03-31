// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>
//        Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Compare data against a hysteresis, toggle the active when exceeding one of the boundaries.
///
module axe_ccl_mon_hysteresis_comparator #(
  /// Data Width
  parameter int unsigned DataWidth = 8,
  /// Reset Value of `o_active`
  parameter bit          ResetValue = 1'b0
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk
  /// Enable updating of the hysteresis
  input  logic i_enable,
  /// Clear the `o_active` output to `ResetValue`
  input  logic i_clear,
  /// Upper hysteresis limit
  input  logic unsigned [DataWidth-1:0] i_upper,
  /// Lower hysteresis limit
  input  logic unsigned [DataWidth-1:0] i_lower,
  /// Input data to monitor
  input  logic unsigned [DataWidth-1:0] i_data,
  /// Hysteresis compare output
  output logic o_active,
  /// Limits are not sanely configured
  output logic o_error
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (DataWidth == 0) $fatal(1, "Parameter: 'DataWidth' must be not 0;");

  ///////////////////
  // Functionality //
  ///////////////////
  logic active_q, active_toggle;
  logic above_upper_limit, below_lower_limit;

  always_comb above_upper_limit = unsigned'(i_data) > unsigned'(i_upper);
  always_comb below_lower_limit = unsigned'(i_data) < unsigned'(i_lower);

  // Both flags can only be active if the relationship is inverted.
  always_comb o_error = above_upper_limit & below_lower_limit;

  always_comb active_toggle =
         i_enable
      &  ~o_error
      & (active_q ? below_lower_limit : above_upper_limit);

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)           active_q <= '0;
    else if (i_clear)       active_q <= ResetValue;
    else if (active_toggle) active_q <= ~active_q;
  end

  ///////////////////////
  // Output Assignment //
  ///////////////////////
  always_comb o_active = active_q;
endmodule
