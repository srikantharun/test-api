// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Throttle unit controller
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef DWM_THROTTLE_CTRL_UNIT_SV
`define DWM_THROTTLE_CTRL_UNIT_SV

module dwm_throttle_ctrl_unit
  import dwm_throttle_ctrl_unit_pkg::*;
#(
  /// Width of the throttle values
  parameter int unsigned TU_UTIL_WIDTH = 7
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  /// Max limit used
  input  logic [TU_UTIL_WIDTH-1:0]               i_max_limit,
  /// Limit used if throttle is enabled
  input  logic [TU_UTIL_WIDTH-1:0]               i_throttle_limit,
  /// Define throttle modes
  input  throttle_mode_e                         i_throttle_mode,

  /// Select the input max throttle
  ///   0: Max limit
  ///   1: Throttle limit
  input  logic                                   i_combined_throttle,
  /// Baseline cycle time between increments of one for the utilization limit
  input  logic [TU_CNT_INCR_DECR_TIME_WIDTH-1:0] i_soft_throttle_incr_time,
  /// Baseline cycle time between decrements of one for the utilization limit
  input  logic [TU_CNT_INCR_DECR_TIME_WIDTH-1:0] i_soft_throttle_decr_time,
  /// Pre-scale factor for the baseline cycle times above (multiplier)
  input  logic [TU_CNT_PRESCALE_WIDTH-1:0]       i_soft_throttle_prescale,
  /// Validate the util limit
  output logic                                   o_util_limit_en,
  /// Util limit imposed by throttle unit
  output logic [TU_UTIL_WIDTH-1:0]               o_util_limit
);

  logic [TU_N_THROTTLE_MODES-1:0][TU_UTIL_WIDTH-1:0] util_limit_per_mode;
  logic [TU_N_THROTTLE_MODES-1:0]                    util_limit_en_per_mode;

  /// E_DISABLED
  always_comb util_limit_per_mode[E_DISABLED]    = '0;
  always_comb util_limit_en_per_mode[E_DISABLED] = '0;

  /// E_MAX_LIMIT
  always_comb util_limit_per_mode[E_MAX_LIMIT]    = i_max_limit;
  always_comb util_limit_en_per_mode[E_MAX_LIMIT] = 1'b1;

  /// E_HARD_THROTTLE
  always_comb util_limit_per_mode[E_HARD_THROTTLE]    = i_combined_throttle ? i_throttle_limit : i_max_limit;
  always_comb util_limit_en_per_mode[E_HARD_THROTTLE] = 1'b1;

  /// E_SOFT_THROTTLE
  // Track whether softnening is enabled
  logic soft_en;
  // Decide whether we want to increment or decrement
  logic [TU_UTIL_WIDTH-1:0] softening_target;
  logic softening_below_target;
  logic softening_above_target;
  // Prescaler and incr/decr pulses
  logic softening_prescaler_pulse;
  // Final softnening limit levels
  logic [TU_UTIL_WIDTH-1:0] s_soft_limit, r_soft_limit_q;

  always_comb soft_en = (i_throttle_mode == E_SOFT_THROTTLE);

  axe_ccl_cnt_to_threshold #(
    .Width(TU_CNT_PRESCALE_WIDTH)
  ) u_cnt_soft_prescale (
    .i_clk,
    .i_rst_n,
    .i_clear    (1'b0),
    .i_enable   (soft_en),
    .i_increment((TU_CNT_PRESCALE_WIDTH)'(1)),
    .i_threshold(i_soft_throttle_prescale),
    .o_pulse    (softening_prescaler_pulse),
    .o_overflow (/* open */)
  );

  always_comb softening_target = i_combined_throttle ? i_throttle_limit : i_max_limit;
  always_comb softening_below_target = soft_en & (unsigned'(r_soft_limit_q) < unsigned'(softening_target));
  always_comb softening_above_target = soft_en & (unsigned'(r_soft_limit_q) > unsigned'(softening_target));

  logic softening_below_target_pulse;

  axe_ccl_cnt_to_threshold #(
    .Width(TU_CNT_INCR_DECR_TIME_WIDTH)
  ) u_cnt_soft_incr (
    .i_clk,
    .i_rst_n,
    .i_clear    (~softening_below_target),
    .i_enable   (softening_prescaler_pulse),
    .i_increment((TU_CNT_INCR_DECR_TIME_WIDTH)'(1)),
    .i_threshold(i_soft_throttle_incr_time),
    .o_pulse    (softening_below_target_pulse),
    .o_overflow (/* open */)
  );

  logic softening_above_target_pulse;

  axe_ccl_cnt_to_threshold #(
    .Width(TU_CNT_INCR_DECR_TIME_WIDTH)
  ) u_cnt_soft_decr (
    .i_clk,
    .i_rst_n,
    .i_clear    (~softening_above_target),
    .i_enable   (softening_prescaler_pulse),
    .i_increment((TU_CNT_INCR_DECR_TIME_WIDTH)'(1)),
    .i_threshold(i_soft_throttle_decr_time),
    .o_pulse    (softening_above_target_pulse),
    .o_overflow (/* open */)
  );

  always_comb begin : s_soft_limit_cproc
    s_soft_limit = r_soft_limit_q;

    if (softening_above_target_pulse && softening_above_target && (s_soft_limit != '0))
      s_soft_limit = s_soft_limit - 1'b1;
    if (softening_below_target_pulse && softening_below_target && (s_soft_limit != '1))
      s_soft_limit = s_soft_limit + 1'b1;
  end

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)      r_soft_limit_q <= '0;
    else if (!soft_en) r_soft_limit_q <= util_limit_per_mode[i_throttle_mode];
    else if (soft_en)  r_soft_limit_q <= s_soft_limit;

  always_comb util_limit_per_mode[E_SOFT_THROTTLE]    = r_soft_limit_q;
  always_comb util_limit_en_per_mode[E_SOFT_THROTTLE] = 1'b1;

  // Output
  always_comb o_util_limit    = util_limit_per_mode[i_throttle_mode];
  always_comb o_util_limit_en = util_limit_en_per_mode[i_throttle_mode];

endmodule
`endif  // DWM_THROTTLE_CTRL_UNIT_SV
