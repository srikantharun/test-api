// (C) Copyright Axelera AI 2025
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>
//        Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Compare data against a hysteresis, toggle the active when exceeding one of the boundaries.
///
module axe_ccl_mon_hysteresis_comparator #(
  /// Data Width
  parameter int unsigned DataWidth = 8,
  /// Value of `o_active` when `i_clear` is active
  parameter bit          ClearValue = 1'b0
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
  /// Select Polarity:
  ///
  /// - `0` : positive polarity
  /// - `1` : negative polarity
  input  logic i_polarity,
  /// On hysteresis threshold
  input  logic unsigned [DataWidth-1:0] i_on,
  /// Off hysteresis threshold
  input  logic unsigned [DataWidth-1:0] i_off,
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
  logic crossing_on_threshold, crossing_off_threshold;

  always_comb crossing_on_threshold  = i_polarity ? unsigned'(i_data) < unsigned'(i_on)  : unsigned'(i_data) > unsigned'(i_on);
  always_comb crossing_off_threshold = i_polarity ? unsigned'(i_data) > unsigned'(i_off) : unsigned'(i_data) < unsigned'(i_off);

  // Both flags can only be active if the relationship is inverted.
  always_comb o_error = i_polarity ? unsigned'(i_on) >= unsigned'(i_off) : unsigned'(i_on) <= unsigned'(i_off);

  always_comb active_toggle =
         i_enable
      &  ~o_error
      & (active_q ? crossing_off_threshold : crossing_on_threshold);

  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)           active_q <= '0;
    else if (i_clear)       active_q <= ClearValue;
    else if (active_toggle) active_q <= ~active_q;
  end

  ///////////////////////
  // Output Assignment //
  ///////////////////////
  always_comb o_active = active_q;
endmodule
