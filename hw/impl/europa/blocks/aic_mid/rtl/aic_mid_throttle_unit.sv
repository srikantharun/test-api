// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// MID Throttle Unit
///
module aic_mid_throttle_unit
  import aic_mid_pkg::*;
  #(
    /// Clock-to-Clock data structure
    parameter type c2c_data_t = logic [7:0]
  ) (
    /// Clock port
    input  wire i_clk,
    /// Reset port
    input  wire i_rst_n,

    /// Validate data coming from the IMC VDD C2C monitor
    input  logic            i_axis_c2c_imc_valid,
    /// IMC VDD monitor data
    input  c2c_data_t       i_axis_c2c_imc_data,

    /// `ON` threshold for IMC C2C Observer
    input  c2c_data_t [1:0] i_imc_cfg_obs_on_th,
    /// `OFF` threshold for IMC C2C Observer
    input  c2c_data_t [1:0] i_imc_cfg_obs_off_th,
    /// Defines the polarity of IMC C2C Observer
    input  logic      [1:0] i_imc_cfg_obs_polarity,
    /// Enable the Observer
    input  logic      [1:0] i_imc_cfg_obs_enable,
    /// Force the throttle via SW
    input  logic      [1:0] i_imc_cfg_obs_sw_force,
    /// Clean the minimum value recorded
    input  logic            i_imc_cfg_obs_clean_min,
    /// Clean the maximum value recorded
    input  logic            i_imc_cfg_obs_clean_max,
    /// Maximum value record from the IMC C2C monitor
    output c2c_data_t       o_imc_cfg_obs_max_value,
    /// Minimum value record from the IMC C2C monitor
    output c2c_data_t       o_imc_cfg_obs_min_value,

    /// Validate data coming from the Core VDD C2C monitor
    input  logic            i_axis_c2c_core_valid,
    /// IMC Core monitor data
    input  c2c_data_t       i_axis_c2c_core_data,

    /// `ON` threshold for Core VDD C2C Observer
    input  c2c_data_t [1:0] i_core_cfg_obs_on_th,
    /// `OFF` threshold for Core VDD C2C Observer
    input  c2c_data_t [1:0] i_core_cfg_obs_off_th,
    /// Defines the polarity of Core VDD C2C Observer
    input  logic      [1:0] i_core_cfg_obs_polarity,
    /// Enable the Observer for Core VDD
    input  logic      [1:0] i_core_cfg_obs_enable,
    /// Force the throttle via SW
    input  logic      [1:0] i_core_cfg_obs_sw_force,
    /// Clean the minimum value recorded
    input  logic            i_core_cfg_obs_clean_min,
    /// Clean the maximum value recorded
    input  logic            i_core_cfg_obs_clean_max,
    /// Maximum value record from the Core VDD C2C monitor
    output c2c_data_t       o_core_cfg_obs_max_value,
    /// Minimum value record from the Core VDD C2C monitor
    output c2c_data_t       o_core_cfg_obs_min_value,

    /// Reports wrong settings of the observation polarity
    output logic [1:0][1:0] o_error,
    /// Configure which Observation throttle is used to define the Utilisation limit or NOP injection
    input  logic [1:0][1:0] i_obs_throttle_cfg,

    /// Thermal throttle triggered by TMS
    input  logic            i_thermal_throttle,
    /// AI Core throttle triggered by DLM
    input  logic            i_aic_throttle,
    /// MVM throttle being generated based on the C2C data to control the clock throttle of AI Core
    output logic            o_mvm_throttle,

    /// Configure the NOP injection throttle control unit
    input  inj_nop_rate_cfg_t i_nop_inj_tu_cfg,
    /// NOP injection rate based on the active throttles
    output nop_inj_rate_t     o_nop_inj_rate,
    /// Validate the NOP injection rate
    output logic              o_nop_inj_valid,

    ///  Maximum utilisation defined by the active throttles
    output util_data_t        o_util_limit,
    /// Validate the max utilisation
    output logic              o_util_limit_en,
    /// Configure the Utilisation throttle control unit
    input  util_cfg_t         i_util_tu_cfg,

    /// Record the minimum average utilisation reported by MVM
    output util_data_t      o_util_min,
    /// Record the maximum average utilisation reported by MVM
    output util_data_t      o_util_max,
    /// Clean the value recorded as the minimum average utilisation reported by MVM
    input  logic            i_clean_util_min,
    /// Clean the value recorded as the maximum average utilisation reported by MVM
    input  logic            i_clean_util_max,

    /// Enable the boost logic
    input  logic            i_enable_boost_req,
    /// Average MVM Utilisation
    input  util_data_t      i_avg_util,
    /// `ON` threshold to trigger the boost request
    input  util_data_t      i_req_boost_on_th,
    /// `OFF` threshold to revoke the boost request
    input  util_data_t      i_req_boost_off_th,
    /// Permission from SoC Manager to enable the boost mode
    input  logic            i_boost_ack,
    /// Utilisation limit when boost mode is disabled
    input  util_data_t      i_normal_util_limit,
    /// Utilisation limit when boost mode is enabled
    input  util_data_t      i_boost_util_limit,

    /// Invalid polarity configured for the boost request
    output logic            o_polarity_err_cfg,
    /// Trigger a boost request to the SoC Manager
    output logic            o_boost_req,

    /// Select which throttle disengage the boost request
    input  logic [3:0]      i_cfg_disengage_boost,

    /// Configure which throttle indication should be used to trigger an warning irq
    input  logic [1:0][1:0] i_irq_warning_cfg,
    /// Configure which throttle indication should be used to trigger an critical irq
    input  logic [1:0][1:0] i_irq_critical_cfg,
    /// Warning IRQ
    output logic            o_warning_irq,
    /// Critical IRQ
    output logic            o_critical_irq
  );
  logic [1:0] imc_obs_throttle;
  logic [1:0] core_obs_throttle;
  logic ultra_fast_throttle;
  logic fast_throttle;
  logic [2:0] nop_inj_throttle;
  logic [2:0] util_throttle;
  util_data_t max_util_limit;
  logic disengage_boost_req;

  dwm_observation_reader #(
    .N_OBS (2),
    .data_t(c2c_data_t)
  ) u_imc_c2c_observation (
    .i_clk,
    .i_rst_n,
    .i_axis_valid      (i_axis_c2c_imc_valid),
    .i_axis_data       (i_axis_c2c_imc_data),
    .i_cfg_on_th       (i_imc_cfg_obs_on_th),
    .i_cfg_off_th      (i_imc_cfg_obs_off_th),
    .i_cfg_polarity    (i_imc_cfg_obs_polarity),
    .i_cfg_enable      (i_imc_cfg_obs_enable),
    .i_cfg_sw_overwrite(i_imc_cfg_obs_sw_force),
    .i_cfg_clean_min   (i_imc_cfg_obs_clean_min),
    .i_cfg_clean_max   (i_imc_cfg_obs_clean_max),
    .o_throttle        (imc_obs_throttle),
    .o_error           (o_error[0]),
    .o_cfg_min_value   (o_imc_cfg_obs_min_value),
    .o_cfg_max_value   (o_imc_cfg_obs_max_value)
  );

  dwm_observation_reader #(
    .N_OBS (2),
    .data_t(c2c_data_t)
  ) u_core_c2c_observation (
    .i_clk,
    .i_rst_n,
    .i_axis_valid      (i_axis_c2c_core_valid),
    .i_axis_data       (i_axis_c2c_core_data),
    .i_cfg_on_th       (i_core_cfg_obs_on_th),
    .i_cfg_off_th      (i_core_cfg_obs_off_th),
    .i_cfg_polarity    (i_core_cfg_obs_polarity),
    .i_cfg_enable      (i_core_cfg_obs_enable),
    .i_cfg_sw_overwrite(i_core_cfg_obs_sw_force),
    .i_cfg_clean_min   (i_core_cfg_obs_clean_min),
    .i_cfg_clean_max   (i_core_cfg_obs_clean_max),
    .o_throttle        (core_obs_throttle),
    .o_error           (o_error[1]),
    .o_cfg_min_value   (o_core_cfg_obs_min_value),
    .o_cfg_max_value   (o_core_cfg_obs_max_value)
  );

  always_comb ultra_fast_throttle = (imc_obs_throttle[ULTRA_FAST_IDX]  && i_obs_throttle_cfg[ULTRA_FAST_IDX][IMC_IDX] )
                                 || (core_obs_throttle[ULTRA_FAST_IDX] && i_obs_throttle_cfg[ULTRA_FAST_IDX][CORE_IDX]);

  always_comb fast_throttle = (imc_obs_throttle[FAST_IDX]  && i_obs_throttle_cfg[FAST_IDX][IMC_IDX] )
                           || (core_obs_throttle[FAST_IDX] && i_obs_throttle_cfg[FAST_IDX][CORE_IDX]);

  always_comb nop_inj_throttle = {ultra_fast_throttle, fast_throttle, i_aic_throttle};

  always_comb util_throttle = {i_thermal_throttle, fast_throttle, i_aic_throttle};

  dwm_dynamic_throttle_ctrl_unit #(
    .N_THROTTLE_PINS (3),
    .PICK_MAX_NOT_MIN(1),
    .TU_UTIL_WIDTH   ($bits(nop_inj_rate_t)),
    .IDLE(dwm_throttle_ctrl_unit_pkg::E_DISABLED)
  ) u_nop_inj_rate_ctrl (
    .i_clk,
    .i_rst_n,
    .i_static_settings   (i_nop_inj_tu_cfg.static_settings),
    .i_throttle_value    (i_nop_inj_tu_cfg.throttle_value),
    .i_throttle_mode     (i_nop_inj_tu_cfg.throttle_mode),
    .i_throttle_en       (i_nop_inj_tu_cfg.throttle_en),
    .i_throttle          (nop_inj_throttle),
    .i_sw_overwrite      (i_nop_inj_tu_cfg.sw_overwrite),
    .i_throttle_incr_time(i_nop_inj_tu_cfg.throttle_incr_time),
    .i_throttle_decr_time(i_nop_inj_tu_cfg.throttle_decr_time),
    .i_throttle_prescale (i_nop_inj_tu_cfg.throttle_prescale),
    .o_data              (o_nop_inj_rate),
    .o_enable            (o_nop_inj_valid)
  );

  dwm_dynamic_throttle_ctrl_unit #(
    .N_THROTTLE_PINS (3),
    .PICK_MAX_NOT_MIN(0),
    .TU_UTIL_WIDTH   ($bits(util_data_t)),
    .IDLE(dwm_throttle_ctrl_unit_pkg::E_DISABLED)
  ) u_util_limit_ctrl (
    .i_clk,
    .i_rst_n,
    .i_static_settings   (max_util_limit),
    .i_throttle_value    (i_util_tu_cfg.throttle_value),
    .i_throttle_mode     (i_util_tu_cfg.throttle_mode),
    .i_throttle_en       (i_util_tu_cfg.throttle_en),
    .i_throttle          (util_throttle),
    .i_sw_overwrite      (i_util_tu_cfg.sw_overwrite),
    .i_throttle_incr_time(i_util_tu_cfg.throttle_incr_time),
    .i_throttle_decr_time(i_util_tu_cfg.throttle_decr_time),
    .i_throttle_prescale (i_util_tu_cfg.throttle_prescale),
    .o_data              (o_util_limit),
    .o_enable            (o_util_limit_en)
  );

  always_comb disengage_boost_req = |(i_cfg_disengage_boost & (
                                                              fast_throttle << THROTTLE_DISENGAGE_FAST_IDX |
                                                              ultra_fast_throttle << THROTTLE_DISENGAGE_ULTRA_FAST_IDX |
                                                              i_thermal_throttle << THROTTLE_DISENGAGE_THERMAL_IDX |
                                                              i_aic_throttle << THROTTLE_DISENGAGE_AIC_IDX
                                                            ));

  dwm_boost_requester #(
    .SyncStages(3),
    .data_t    (util_data_t)
  ) u_boost_requester (
    .i_clk,
    .i_rst_n,
    .i_enable        (i_enable_boost_req),
    .i_avg_util      (i_avg_util),
    .i_on_th         (i_req_boost_on_th),
    .i_off_th        (i_req_boost_off_th),
    .i_throttle      (disengage_boost_req),
    .i_boost_limit   (i_boost_util_limit),
    .i_standard_limit(i_normal_util_limit),
    .i_boost_ack     (i_boost_ack),
    .o_boost_req     (o_boost_req),
    .o_util_limit    (max_util_limit),
    .o_polarity_err  (o_polarity_err_cfg)
  );

  axe_ccl_mon_minimum_maximum #(
    .DataWidth($bits(util_data_t))
  ) u_util_record_min_max (
    .i_clk,
    .i_rst_n,
    .i_clear_min(i_clean_util_min),
    .i_clear_max(i_clean_util_max),
    .i_enable   (i_enable_boost_req),
    .i_data     (i_avg_util),
    .o_data_min (o_util_min),
    .o_data_max (o_util_max)
  );

  always_comb o_warning_irq = (
                                (imc_obs_throttle[ULTRA_FAST_IDX]  && i_irq_warning_cfg[ULTRA_FAST_IDX][IMC_IDX] ) ||
                                (core_obs_throttle[ULTRA_FAST_IDX] && i_irq_warning_cfg[ULTRA_FAST_IDX][CORE_IDX])
                              ) ||
                              (
                                (imc_obs_throttle[FAST_IDX]  && i_irq_warning_cfg[FAST_IDX][IMC_IDX] ) ||
                                (core_obs_throttle[FAST_IDX] && i_irq_warning_cfg[FAST_IDX][CORE_IDX])
                              );

  always_comb o_critical_irq = (
                                (imc_obs_throttle[ULTRA_FAST_IDX]  && i_irq_critical_cfg[ULTRA_FAST_IDX][IMC_IDX] ) ||
                                (core_obs_throttle[ULTRA_FAST_IDX] && i_irq_critical_cfg[ULTRA_FAST_IDX][CORE_IDX])
                              ) ||
                              (
                                (imc_obs_throttle[FAST_IDX]  && i_irq_critical_cfg[FAST_IDX][IMC_IDX] ) ||
                                (core_obs_throttle[FAST_IDX] && i_irq_critical_cfg[FAST_IDX][CORE_IDX])
                              );

endmodule
