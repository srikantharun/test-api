// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// The design uses a phase accumulator to periodically open a clock gate.
///
module axe_ccl_clk_div_by_pt #(
  /// The width of the phase accumulator
  parameter int unsigned PhaseAccWidth = 0,
  /// Reset value of the flip-flop which drives the clock gate.
  parameter bit ResetValClkEn = 1,
  /// Delay the clock enable internally so the o_active appears 1 cycle ahead.
  parameter bit DelayClkPulse = 0
)(
  /// Input clock, positive edge triggered.
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low.
  input  wire  i_rst_n,
  // doc sync i_clk
  /// Test mode activate, enables the clock gate by default.
  input  logic i_test_en,
  /// Enable the downstream clock `o_clk`.
  ///
  /// - `0` : Downstream `o_clk` is **gated**!
  /// - `1` : Some clock pulses can be selectively taken out to form the division.
  input  logic i_div_en,
  /// Clear the phase of the accumulator.
  ///
  /// This implies that the next pulse only happens when the accumlator overflows again.
  input  logic i_acc_clr,
  /// The increment for the phase accumulator. This defines the division ratio.
  input  logic [PhaseAccWidth-1:0] i_acc_incr,
  /// Flag indicating that the clock gate is open and lets the clock through.
  /// Active high, same speed as the fast clock.
  /// This signal directly drives the enable of the clock gate.
  output logic o_active,
  /// The divided clock output. `i_clk` passed through a clock gate.
  // doc async
  output wire  o_clk
);
  if (PhaseAccWidth == 0) $fatal(1,
      "Parameter: 'PhaseAccWidth' must be greater than 0;"
  );

  // Internal signals
  logic accumulator_enable; // Enable counting of the accumulator when needed
  logic enable_clock_d;     // Enable the clock gate for this pulse
  logic enable_clock_q;     // Registered to prevent hazards at the gate enable
  logic increment_is_zero;  // Disable the phase accumulator as clock is not divided
  logic accumulator_pulse;  // Pulse of the phase accumulator, this enables the gate when dividing
  logic enable_clock;       // Enable signal for final clock gate


  // Comparator, so that we know that the desired division value is 1
  assign increment_is_zero  = i_acc_incr == PhaseAccWidth'(0);
  // Enable the counting of the pahse accumulator when the divier is enabled and there is a ratio.
  assign accumulator_enable = i_div_en && !increment_is_zero;

  axe_ccl_cnt_phase_acc #(
    .Width(PhaseAccWidth)
  ) u_axe_ccl_cnt_phase_acc (
    .i_clk,
    .i_rst_n,
    .i_cnt_clr (i_acc_clr),
    .i_cnt_incr(i_acc_incr),
    .i_cnt_en  (accumulator_enable),
    .o_pulse   (accumulator_pulse),
    .o_phase   (/*open*/)
  );

  // When the divider is enabled selectively filter out clock pulses.
  // Let the clock through when divider is disabeld.
  assign enable_clock_d = i_div_en && (increment_is_zero || accumulator_pulse);

  // Have an additional flop stage in front of the clock gate enable to prevent hazards.
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) enable_clock_q <= ResetValClkEn;
    else          enable_clock_q <= enable_clock_d;
  end

  // Add visibility to when the downstream clock gate is enabeld
  assign o_active = enable_clock_q | i_test_en;

  // Configurable delay to clock gate enable
  if (DelayClkPulse) begin: g_delayclkpulse
    logic active_q;
    always_ff @ (posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) active_q <= ResetValClkEn;
      else          active_q <= o_active;
    end
    always_comb enable_clock = active_q;
  end: g_delayclkpulse
  else begin: g_nodelayclkpulse
    always_comb enable_clock = o_active;
  end: g_nodelayclkpulse

  // The clock gate that lets selectively clock pulses through
  axe_tcl_clk_gating u_clk_gate (
    .i_clk,
    .i_en     (enable_clock),
    .i_test_en,
    .o_clk
  );
endmodule
