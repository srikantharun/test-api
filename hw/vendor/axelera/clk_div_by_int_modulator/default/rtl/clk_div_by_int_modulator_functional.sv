// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Form the actual clock phase for the integer clock divider.
///
/// !!! example "Constraining"
///
///     This module needs to be carefully constrained to perform the correct glitchless operation!
///
///     If you want to have downstream logic only work from a specific division ratio use something on the line off
///     (adapt values in <...>):
///
///     ```tcl
///     create_generated_clock \
///       -combinational \
///       -name <div3_clk_mux> \
///       -divide_by <3>
///       -master_clock <i_clk> \
///       -source {u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div/u_tc_lib_clk_mux/S0}
///     ```
///
///     Clock gating **must** be explicitly defined:
///
///     ```tcl
///     set_clock_gating_check
///       -low \
///       -setup 0.050 \
///       -hold  0.050 \
///       [get_pins u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div/u_tc_lib_clk_mux/A]
///
///     set_clock_gating_check
///       -high \
///       -setup 0.050 \
///       -hold  0.050 \
///       [get_pins u_clk_div_by_int_modulator/u_axe_tcl_clk_mux2_div/u_tc_lib_clk_mux/B]
///     ```
///
module clk_div_by_int_modulator #(
  /// The generated clock is turned on in reset
  parameter bit ClkOnInReset = 1'b1
)(
  /// Clock, positive edgetriggered
  input  wire  i_clk,
  /// Asynchronous reset, active low (must be synchronized to i_clk)
  input  wire  i_rst_n,
  /// Testmode bypass
  input  logic i_test_mode,
  /// FSM Phase 0 wire
  input  logic i_phase_0,
  /// FSM Phase 1 wire
  input  logic i_phase_1,
  /// Output formed clock
  output wire  o_clk
);

  // These Flip-Flops intentionally use blocking assignments! If we were to use
  // non-blocking assignment like we normally do for flip-flops, we would create
  // a race condition when sampling data from the fast clock domain into
  // flip-flops clocked by t_ff0_q and t_ff1_q. To avoid this, we use blocking assignments
  // which is the recomended method acording to:
  // S. Sutherland and D. Mills,
  // Verilog and System Verilog gotchas: 101 common coding errors and how to
  // avoid them. New York: Springer, 2007. page 64.

  logic phase_0_q;
  logic phase_1_q;

  // verilog_lint: waive-start always-ff-non-blocking // ASO-BLOCKING_ASSIGN: Intentional blocking assignment
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin : flop_pos_phase_0
    if (!i_rst_n) phase_0_q = 1'b0; // ASO-BLOCKING_ASSIGN : Intentional blocking assignment
    else          phase_0_q = i_phase_0; // ASO-BLOCKING_ASSIGN : Intentional blocking assignment
  end

  always_latch begin : latch_neg_phase_1
    if (!i_rst_n)    phase_1_q = ClkOnInReset;
    else if (!i_clk) phase_1_q = i_phase_1;
  end
  // verilog_lint: waive-stop always-ff-non-blocking // ASO-BLOCKING_ASSIGN: Intentional blocking assignment

  wire divided_clk;

  axe_tcl_clk_mux2 u_axe_tcl_clk_mux2_div (
    .i_clk0(phase_0_q),
    .i_clk1(phase_1_q),
    .i_sel (i_clk),
    .o_clk (divided_clk)
  );

  wire output_clk;

  axe_tcl_clk_mux2 u_axe_tcl_clk_mux2_test (
    .i_clk0(divided_clk),
    .i_clk1(i_clk),
    .i_sel (i_test_mode),
    .o_clk
  );
endmodule
