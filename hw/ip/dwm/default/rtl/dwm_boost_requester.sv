// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// The Boost Requester unit is responsible for asserting the boost request signal
/// if the utilisation average crosses a threshold value.
///
module dwm_boost_requester #(
  /// Number of synchronization stages
  parameter int unsigned SyncStages = 3,
  /// Data structure used to collect the sensor data
  parameter type data_t = logic [7:0]
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,
  /// Enables the boost request unit
  input  logic i_enable,
  /// Reports the current average utilization of the MVM
  input  data_t i_avg_util,
  /// Defines the threshold value where a boost request should be sent
  input  data_t i_on_th,
  /// Defines the threshold value where the boost request should be cancelled
  input  data_t i_off_th,
  /// External throttle flag
  input  logic i_throttle,
  /// Defines the utilization limit in boost mode
  input  data_t i_boost_limit,
  /// Defines the utilization limit with boost mode disabled
  input  data_t i_standard_limit,
  /// Authorization to use enable boost mode
  input  logic i_boost_ack,
  /// Request boost mode
  output logic o_boost_req,
  /// Utilization limit for MVM
  output data_t o_util_limit,
  /// Error in the polarity configuration
  output logic o_polarity_err
);

  localparam int unsigned LP_DATA_WD = $bits(data_t);
  logic comparator_enable;
  logic boost_ack_sync;
  logic boost_mode_activated;
  logic clear_comparator;

  always_comb comparator_enable = i_enable && !i_throttle;

  always_comb clear_comparator = !i_enable || i_throttle;

  axe_ccl_mon_hysteresis_comparator #(
    .DataWidth(LP_DATA_WD),
    .ClearValue(1'b0)
  ) u_hysteresis_comparator (
    .i_clk,
    .i_rst_n,
    .i_enable  (comparator_enable),
    .i_clear   (clear_comparator),
    .i_polarity(1'b0),
    .i_on      (i_on_th),
    .i_off     (i_off_th),
    .i_data    (i_avg_util),
    .o_active  (o_boost_req),
    .o_error   (o_polarity_err)
  );

  axe_tcl_seq_sync #(
    .SyncStages(SyncStages)
  ) u_sync_bist_busy (
    .i_clk,
    .i_rst_n,
    .i_d(i_boost_ack),
    .o_q(boost_ack_sync)
  );

  always_comb boost_mode_activated = !i_throttle && boost_ack_sync;

  always_comb o_util_limit = boost_mode_activated ? i_boost_limit : i_standard_limit;

endmodule
