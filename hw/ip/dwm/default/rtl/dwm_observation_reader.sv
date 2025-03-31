// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// An observation reader (ORD) observes an AXI-Stream (data, valid), collects statistics and reacts
///   to it by either triggering IRQ or asserting/deasserting throttle signals.
/// The observation reader is controlled/observed over a CSR interface.
///
module dwm_observation_reader #(
  /// Select the number of observators/comparators to generate independent throttle signals
  parameter int unsigned N_OBS = 2,
  /// Data structure used to collect the sensor data
  parameter type data_t = logic [7:0]
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,
  /// Validate the input stream
  input  logic i_axis_valid,
  /// Input sensor data stream
  input  data_t i_axis_data,
  /// On threshold value per observation
  input  data_t [N_OBS-1:0] i_cfg_on_th,
  /// Off threshold value per observation
  input  data_t [N_OBS-1:0] i_cfg_off_th,
  /// Select polarity per observation
  /// 0: positive polarity; 1: negative polarity
  input  logic [N_OBS-1:0] i_cfg_polarity,
  /// Enable comparators per observation
  input  logic [N_OBS-1:0] i_cfg_enable,
  /// Force enabling output throttle
  input  logic [N_OBS-1:0] i_cfg_sw_overwrite,
  /// Clean the minimum input data recorded
  input  logic i_cfg_clean_min,
  /// Clean the maximum input data recorded
  input  logic i_cfg_clean_max,
  /// Throttle signal
  output logic [N_OBS-1:0] o_throttle,
  /// Error in the polarity observation configuration
  output logic [N_OBS-1:0] o_error,
  /// Minimum value record from the input sensor data stream
  output data_t o_cfg_min_value,
  /// Maximum value record from the input sensor data stream
  output data_t o_cfg_max_value
);

  if (N_OBS == 0) $fatal(1, "Parameter: 'N_OBS' must be higher than 0;");

  localparam int unsigned LP_DATA_WD = $bits(data_t);
  logic [N_OBS-1:0] int_throttle;

  for (genvar obs_index = 0; obs_index < N_OBS; obs_index++) begin : g_observers

    axe_ccl_mon_hysteresis_comparator #(
      .DataWidth(LP_DATA_WD),
      .ClearValue(1'b0)
    ) u_hysteresis_comparator (
      .i_clk,
      .i_rst_n,
      .i_enable  (i_axis_valid),
      .i_clear   (!i_cfg_enable[obs_index]),
      .i_polarity(i_cfg_polarity[obs_index]),
      .i_on      (i_cfg_on_th[obs_index]),
      .i_off     (i_cfg_off_th[obs_index]),
      .i_data    (i_axis_data),
      .o_active  (int_throttle[obs_index]),
      .o_error   (o_error[obs_index])
    );

    always_comb o_throttle[obs_index] = int_throttle[obs_index] || i_cfg_sw_overwrite[obs_index];

  end

  axe_ccl_mon_minimum_maximum #(
    .DataWidth(LP_DATA_WD)
  ) u_min_max_recorder (
    .i_clk,
    .i_rst_n,
    .i_clear_min(i_cfg_clean_min),
    .i_clear_max(i_cfg_clean_max),
    .i_enable   (i_axis_valid),
    .i_data     (i_axis_data),
    .o_data_min (o_cfg_min_value),
    .o_data_max (o_cfg_max_value)
  );

endmodule
