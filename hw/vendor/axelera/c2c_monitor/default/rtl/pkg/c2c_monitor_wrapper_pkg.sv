// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: C2C Wrapper package
//
// Authors: Manuel Oliveira
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef C2C_MONITOR_WRAPPER_PKG_SV
`define C2C_MONITOR_WRAPPER_PKG_SV

package c2c_monitor_wrapper_pkg;

  parameter int unsigned CA_WD = 32'd4;
  parameter int unsigned CB_WD = 32'd10;
  parameter int unsigned CC_WD = 32'd10;
  parameter int unsigned CD_WD = 32'd20;

  parameter int unsigned SCALE_WD = 32'd4;

  parameter int unsigned CA_RESULT_WD = 2*c2c_monitor_pkg::C2C_COUNT_W + CA_WD;
  parameter int unsigned CB_RESULT_WD =   c2c_monitor_pkg::C2C_COUNT_W + CB_WD;
  parameter int unsigned CC_RESULT_WD =   c2c_monitor_pkg::C2C_COUNT_W + CC_WD;
  parameter int unsigned MARGIN_WD    = 32'd21;

  parameter int unsigned CD_RESULT_WD =   c2c_monitor_pkg::C2C_COUNT_W + CD_WD;

  typedef logic [c2c_monitor_pkg::C2C_COUNT_W-1:0] c2c_data_width_t;
  typedef                   c2c_data_width_t [1:0] c2c_count_t;

  typedef enum logic [1:0] {
    c2c_0 = 2'd0,
    c2c_1 = 2'd1,
    c2c_2 = 2'd2,
    medium_vote = 2'd3
  } c2c_vote_opt_e;

  typedef struct packed {
    logic [CA_WD-1:0] A;
    logic [CB_WD-1:0] B;
    logic [CC_WD-1:0] C;
    logic [CD_WD-1:0] D;
  } c2c_const_t;

  typedef struct packed {
    c2c_vote_opt_e          vote;
    logic    [SCALE_WD-1:0] scale;
    c2c_const_t       [1:0] constants;
  } c2c_cfg_t;

  typedef enum logic {
    SVT = 1'b0,
    LVT = 1'b1
  } volt_threshold_e;

endpackage

`endif  // C2C_MONITOR_WRAPPER_PKG_SV
