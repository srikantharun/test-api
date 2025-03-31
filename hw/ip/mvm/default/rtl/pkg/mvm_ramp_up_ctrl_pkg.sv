// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MVM Ramp Up Control package
// Parameters and typedefs
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_RAMP_UP_CTRL_PKG_SV
`define MVM_RAMP_UP_CTRL_PKG_SV

package mvm_ramp_up_ctrl_pkg;
  // Data widths
  parameter int unsigned RAMP_BUDGET_COST_BASE    = 8;
  parameter int unsigned RAMP_BUDGET_COST_PER_COL = 4;
  parameter int unsigned RAMP_BUDGET_COST_PER_ROW = 4;
  parameter int unsigned RAMP_BUDGET_COST_PER_RC  = 1;
  parameter int unsigned RAMP_BUDGET_INCREMENT    = 8;
  parameter int unsigned RAMP_BUDGET_CLIP         = 8;
  parameter int unsigned RAMP_BUDGET_CALC_WD      = 10;
  parameter int unsigned RAMP_BUDGET_WD           = 8;

  parameter int unsigned MVM_ROWS_WD              = $clog2(mvm_pkg::MVM_INP_GATING_DW) + 1;
  parameter int unsigned MVM_COLS_WD              = $clog2(mvm_pkg::MVM_OUP_GATING_DW) + 1;

  parameter int unsigned         MAX_RAMP_BUDGET  = 2**RAMP_BUDGET_WD - 1;

  typedef logic    [RAMP_BUDGET_COST_BASE-1:0] budget_cost_base_t;
  typedef logic [RAMP_BUDGET_COST_PER_COL-1:0] budget_cost_per_col_t;
  typedef logic [RAMP_BUDGET_COST_PER_ROW-1:0] budget_cost_per_row_t;
  typedef logic [ RAMP_BUDGET_COST_PER_RC-1:0] budget_cost_per_rc_t;
  typedef logic   [ RAMP_BUDGET_INCREMENT-1:0] budget_increment_t;
  typedef logic [RAMP_BUDGET_COST_PER_COL-1:0] budget_clip_t;
  typedef logic      [RAMP_BUDGET_CALC_WD-1:0] budget_calc_t;
  typedef logic           [RAMP_BUDGET_WD-1:0] budget_t;


  typedef logic[MVM_ROWS_WD-1:0] mvm_rows_t;
  typedef logic[MVM_COLS_WD-1:0] mvm_cols_t;

  typedef struct packed {
    budget_cost_base_t    budget_cost_base;
    budget_cost_per_col_t budget_cost_per_col;
    budget_cost_per_row_t budget_cost_per_row;
    budget_cost_per_rc_t  budget_cost_per_rc;
    budget_increment_t    budget_increment;
    budget_clip_t         budget_clip;
  } ramp_up_ctrl_t;

endpackage

`endif  // MVM_RAMP_UP_CTRL_PKG_SV
