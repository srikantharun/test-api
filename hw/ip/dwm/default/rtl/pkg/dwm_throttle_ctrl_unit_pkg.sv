// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Throttle unit package
// Parameters and typedefs
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef DWM_THROTTLE_CTRL_UNIT_PKG_SV
`define DWM_THROTTLE_CTRL_UNIT_PKG_SV

package dwm_throttle_ctrl_unit_pkg;
  // Data widths
  parameter int unsigned TU_VOLTAGE_DATA_WIDTH     = 6;
  parameter int unsigned TU_TEMPERATURE_DATA_WIDTH = 10;

  // Sampling
  parameter int unsigned TU_UTIL_SAMPLE_INTERVAL    = 31;
  parameter int unsigned TU_UTIL_SAMPLE_INTERVAL_WD = cc_math_pkg::index_width(TU_UTIL_SAMPLE_INTERVAL + 1);

  // Soft throttling
  parameter int unsigned TU_CNT_PRESCALE_WIDTH       = 8;
  parameter int unsigned TU_CNT_INCR_DECR_TIME_WIDTH = 16;

  // Throttle modes
  parameter int unsigned TU_N_THROTTLE_MODES = 4;
  parameter int unsigned TuThrottleModeWidth = cc_math_pkg::index_width(TU_N_THROTTLE_MODES);

  typedef enum logic [TuThrottleModeWidth-1:0] {
    E_DISABLED      = 2'b00,
    E_MAX_LIMIT     = 2'b01,
    E_HARD_THROTTLE = 2'b10,
    E_SOFT_THROTTLE = 2'b11
  } throttle_mode_e;

endpackage

`endif  // DWM_THROTTLE_CTRL_UNIT_PKG_SV
