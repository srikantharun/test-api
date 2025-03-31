// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MVM ramp up control unit
// Control the budgeting and throttle MVM in case of full budgeting utilization minimizing the power peeks
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef MVM_RAMP_UP_CTRL_SV
`define MVM_RAMP_UP_CTRL_SV

module mvm_ramp_up_ctrl
  import mvm_ramp_up_ctrl_pkg::*;
  (
    input  wire           i_clk,
    input  wire           i_rst_n,
    input  mvm_rows_t     i_nb_active_rows,
    input  mvm_cols_t     i_nb_active_cols,
    input  ramp_up_ctrl_t i_ramp_budget_ctrl,
    input  logic          i_ext_trigger_nop,
    output logic          o_trigger_nop,
    output logic          o_err_not_enough_budget
  );
  ////////////////////////
  // Signals declaration
  logic         input_available;
  budget_t      launch_cost;
  logic         lauch_input;
  budget_t      current_budget_d;
  budget_t      current_budget_q;
  budget_t      activity_drop;
  logic         activity_drop_valid;
  budget_calc_t combine_budget;
  budget_calc_t updated_budget;
  ///////////////////////
  // RTL
  cc_cnt_shift_reg #(
    .data_t(budget_t),
    .Stages(16)
  ) u_mvm_activity (
    .i_clk,
    .i_rst_n,
    .i_clear  (1'b0),
    .i_stall  (1'b0),
    .i_data   (launch_cost),
    .i_data_en(lauch_input),
    .o_data   (activity_drop),
    .o_updated(activity_drop_valid)
  );

  always_comb input_available = |i_nb_active_rows && |i_nb_active_cols;

  always_comb begin : launch_cost_cal_comb_proc
    budget_calc_t tmp_launch_cost;
    tmp_launch_cost = i_ramp_budget_ctrl.budget_cost_base
                   + i_ramp_budget_ctrl.budget_cost_per_col*i_nb_active_cols
                   + i_ramp_budget_ctrl.budget_cost_per_row*i_nb_active_rows
                   + i_ramp_budget_ctrl.budget_cost_per_rc*i_nb_active_cols*i_nb_active_rows;
    launch_cost = (tmp_launch_cost > budget_calc_t'(MAX_RAMP_BUDGET)) ? budget_t'(MAX_RAMP_BUDGET) : budget_t'(tmp_launch_cost);
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin : update_budget_seq_proc
    if (!i_rst_n)                                                      current_budget_q <= budget_t'(0);
    else if ((current_budget_q ^ current_budget_d) && input_available) current_budget_q <= current_budget_d;
  end

  always_comb combine_budget = current_budget_q + i_ramp_budget_ctrl.budget_increment
                             + (activity_drop_valid ? activity_drop : budget_calc_t'(0));

  always_comb begin : nop_injection_decision_comb_proc
    if (input_available && (combine_budget > budget_calc_t'(launch_cost)) && !i_ext_trigger_nop) begin
      lauch_input = 1'b1;
      updated_budget = combine_budget - launch_cost;
    end else begin
      lauch_input = 1'b0;
      updated_budget = combine_budget;
    end
  end

  always_comb current_budget_d = (updated_budget < i_ramp_budget_ctrl.budget_clip) ? updated_budget : i_ramp_budget_ctrl.budget_clip;

  always_comb o_trigger_nop = !lauch_input && input_available;

  always_comb o_err_not_enough_budget = (launch_cost >= (i_ramp_budget_ctrl.budget_clip + i_ramp_budget_ctrl.budget_increment))
                                      || (i_ramp_budget_ctrl.budget_increment == budget_increment_t'(0));

endmodule
`endif  // MVM_RAMP_UP_CTRL_SV
