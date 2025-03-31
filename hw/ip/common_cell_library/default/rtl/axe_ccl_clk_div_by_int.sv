// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Divide a clock by an integer ratio.
///
module axe_ccl_clk_div_by_int #(
  /// Maximum Division Ratio
  parameter  int unsigned MaxDivision  = 25,
  /// The width of the division ration signal
  localparam int unsigned DivisorWidth = cc_math_pkg::index_width(MaxDivision),
  /// The generated clock is turned on in reset
  parameter bit ClkOnInReset = 1'b1
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asnchronous reset, active low
  input  wire  i_rst_n,
  /// Testmode bypass
  input  logic i_test_mode,
  /// Configuration from CSR
  ///
  /// Allowed values:
  ///
  /// - `0`: Clock off
  /// - `1`: Divide by `1`, feedthrough
  /// - `N`: Divide by `N`
  ///
  /// !!! note
  ///
  ///     Values larger than `MaxDivision` will be sanitized to `MaxDivision`.
  ///
  input  logic [DivisorWidth:0] i_divisor,
  /// Output divided clock
  output wire  o_clk
);

  ///////////////////////
  // Config sanitation //
  ///////////////////////
  typedef logic [DivisorWidth  :0] divisor_t;
  typedef logic [DivisorWidth-1:0] cycle_index_t;

  divisor_t   divisor_d;
  always_comb divisor_d = (i_divisor > divisor_t'(MaxDivision)) ? divisor_t'(MaxDivision) : i_divisor;
  divisor_t   divisor_q;

  logic       load_divisor;
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          divisor_q <= divisor_t'(ClkOnInReset);
    else if (load_divisor) divisor_q <= divisor_d;
  end

  ///////////////////
  // Cycle Counter //
  ///////////////////
  logic         increment_cycle;
  logic         start_a_cycle;
  cycle_index_t cycle_index;

  always_comb increment_cycle = divisor_q > divisor_t'(1);

  axe_ccl_cnt_delta #(
    .Width         (DivisorWidth),
    .StickyOverflow(1'b0)
  ) u_axe_ccl_cnt_delta (
    .i_clk,
    .i_rst_n,
    .i_flush    (start_a_cycle),
    .i_enable   (increment_cycle),
    .i_decrement(1'b0),
    .i_delta    (cycle_index_t'(1)),
    .o_count    (cycle_index),
    .i_value    (cycle_index_t'(0)),
    .i_overwrite(1'b0),
    .o_overflow (/* open */), // ASO-UNUSED_OUTPUT : Observability not needed.
    .o_underflow(/* open */)  // ASO-UNUSED_OUTPUT : Observability not needed.
  );

  /////////////
  // Control //
  /////////////
  logic       at_end_of_cycle;
  always_comb at_end_of_cycle = (divisor_q == divisor_t'(0)) | (divisor_t'(cycle_index + 1) >= divisor_q);
  always_comb load_divisor    = at_end_of_cycle & (divisor_d != divisor_q);
  always_comb start_a_cycle   = at_end_of_cycle & (cycle_index != cycle_index_t'(0));

  ///////////////////////
  // Phase Calculation //
  ///////////////////////
  divisor_t   half_cycle_index;
  always_comb half_cycle_index    = divisor_q >> 1;

  logic       cycle_at_midpoint;
  always_comb cycle_at_midpoint   = cycle_index == half_cycle_index;

  logic       cycle_in_upper_half;
  always_comb cycle_in_upper_half = cycle_index >  half_cycle_index;

  logic [1:0] phase_d;
  logic [1:0] phase_q;

  always_comb begin
    phase_d = phase_q;

    unique case (divisor_q)
      divisor_t'(0): phase_d = 2'b00;
      divisor_t'(1): phase_d = 2'b10;
      default: begin
        phase_d[0] = ~(cycle_at_midpoint | cycle_in_upper_half);
        phase_d[1] = divisor_q[0] ? ~cycle_in_upper_half : ~(cycle_at_midpoint | cycle_in_upper_half);
      end
    endcase
  end

  logic       update_phase;
  always_comb update_phase = (phase_q != phase_d);

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          phase_q <= {ClkOnInReset, 1'b0};
    else if (update_phase) phase_q <= phase_d;
  end

  ///////////////////////////////////////////////////
  // The actual phase resolution and clock forming //
  // Should be implemented with `tech_cells` only! //
  ///////////////////////////////////////////////////
  clk_div_by_int_modulator u_clk_div_by_int_modulator (
    .i_clk,
    .i_rst_n,
    .i_test_mode,
    .i_phase_0  (phase_q[0]),
    .i_phase_1  (phase_q[1]),
    .o_clk
  );
endmodule
