// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: IMC BIST Controller
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

`ifndef IMC_BIST_CTL_SV
`define IMC_BIST_CTL_SV

module imc_bist_ctl
  import imc_bist_pkg::bist_type_e  ;
  import imc_bist_pkg::expect_type_e;
  import imc_bist_pkg::IMC_BIST_CYCLE_PW;
  import imc_bist_pkg::E_IMC_MBIST;
  import imc_bist_pkg::E_IMC_CBIST;
  import imc_bank_pkg::*;
#(
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t,
  parameter type aic_csr_reg2hw_imc_status_t = imc_bist_pkg::hw2reg_imc_bist_status_reg_t
) (
  input wire i_clk,
  input wire i_rst_n,
  // Input declared but not read.
  // tiago: This is intentional for Bronze
  input logic jtag_tck_i,
  input logic jtag_ti_rst_n,

  // <-> CSR/JTAG
  input  aic_csr_reg2hw_t regcsr_i,
  output aic_csr_hw2reg_t regcsr_o,
  input  aic_csr_reg2hw_t regjtag_i,
  output aic_csr_hw2reg_t regjtag_o,

  // <-> GEN
  output logic start_po,
  output logic resume_po,
  output logic stop_po,
  output bist_type_e bist_type_o,
  input logic busy_i,

  // <-> IMUX/IMUXC
  output logic bist_mode_o,

  // <-> COLL
  input logic fault_det_i,
  input logic fault_valid_i,
  input logic [mvm_pkg::MVM_IMC_BANK_PW-1:0] fault_bank_i,
  input logic [imc_bank_pkg::IMC_BANK_COL_PW-1:0] fault_col_i,
  input logic [IMC_BIST_CYCLE_PW-1:0] fault_cycle_i,
  output logic fault_pop_o
);
  // verilog_lint: waive-start line-length
  /// -----------------------
  /// ----- TYPES -----------
  /// -----------------------
  // FSM states
  typedef enum logic [7:0] {
    E_IDLE = 8'd0,
    E_RUN_NORM = 8'd1,
    E_STOPPING = 8'd2,
    E_RUN_BIM = 8'd4,
    E_RUN_FAM = 8'd8,
    E_PAUSING = 8'd16,
    E_PAUSED = 8'd32,
    E_UNPAUSING = 8'd64
  } bist_ctl_state_e;

  // Onehot FSM transition vector
  typedef struct packed {
    logic idle_from_invalid_state;
    /// ---> Start BIST
    logic run_norm_from_idle;
    logic run_bim_from_idle;
    logic run_fam_from_idle;
    /// ---> Restart BIST
    logic run_bim_from_run_bim;
    /// ---> Stop BIST
    logic stopping_from_run_norm;
    logic stopping_from_run_bim;
    logic stopping_from_run_fam;
    logic stopping_from_pausing;
    logic stopping_from_unpausing;
    logic idle_from_stopping;
    /// ---> Pause/Unpause BIST
    logic pausing_from_run_fam;
    logic paused_from_pausing;
    logic idle_from_pausing;
    logic unpausing_from_paused;
    logic paused_from_unpausing;
    logic run_fam_from_unpausing;
  } fsm_hint_t;

  // Latency absorption == amount of cycle to wait in STOPPING state for bank flush
  // 7 cycles internal latency + 16 cycles mvm ramping delay + 1 acc delay + 1 coll delay
  localparam int unsigned LBrakingDistance = 25;

  /// -----------------------
  /// ----- FLOPS/WIRES -----
  /// -----------------------
  // JTAG/CSR mux/demux
  aic_csr_reg2hw_t s_muxed_reg2hw;
  aic_csr_hw2reg_t s_muxed_hw2reg;

  // Rising edge detectors
  logic r_mbist_start_q, r_stop_q;
  logic r_cbist_start_q;
  logic r_resume_q;
  logic s_mbist_start_rising_edge_p, s_stop_rising_edge_p;
  logic r_mbist_start_rising_edge_p, r_stop_rising_edge_p;
  logic s_cbist_start_rising_edge_p;
  logic r_cbist_start_rising_edge_p;
  logic s_resume_rising_edge_p;
  logic r_resume_rising_edge_p;
  logic s_any_start_rising_edge_p;

  // State
  logic [$clog2(LBrakingDistance+1)-1:0]
      r_current_braking_distance, s_current_braking_distance;
  fsm_hint_t s_fsm_hint;
  bist_ctl_state_e s_state, r_state;

  logic s_eval_cfg_norm;
  logic s_eval_cfg_bim;
  logic s_eval_cfg_fam;

  bist_type_e   s_bist_type_by_leaving_idle;
  bist_type_e   s_bist_type_by_restarting_burnin;

  // State observation
  logic s_entering_idle_p, s_leaving_idle_p, s_entering_stopping_p;
  logic r_entering_idle_p, r_leaving_idle_p, r_entering_stopping_p;
  logic s_entering_paused_p, r_entering_paused_p;
  logic s_entering_unpausing_p, r_entering_unpausing_p;
  logic s_leaving_paused_p, r_leaving_paused_p;
  logic s_restarting_burnin_p;
  // Current run observation
  logic r_current_run_fail_det_latch, r_current_run_stop_det_latch;
  bist_type_e   r_current_run_bist_type_latch;
  logic r_current_run_single_pass_latch;
  logic r_current_run_bim_latch;
  logic s_eval_pass;

  // Output layer
  logic s_update_status_p;
  logic s_set_status_p;
  logic r_update_status_p;
  logic r_set_status_p;
  logic start_p_int;
  logic resume_p_int;
  logic stop_p_int;
  logic fault_pop_int;
  bist_type_e   bist_type_int;

  // Unconnected OK: The controller doesn't care about register status bits, it uses custom interface with other subblocks
  logic unconnected_ok_s_muxed_reg2hw_status;
  // Unconnected OK: We don't use the muxed csr_sel, we use directly from regcsr_i so JTAG can't override it
  logic unconnected_ok_s_muxed_reg2hw_cfg_csr_sel;

  /// -----------------------
  /// ----- DESIGN ----------
  /// -----------------------

  /// --------------------------------------
  /// ----- 1. CSR/JTAG MUX/DEMUX ----------
  /// --------------------------------------
  // Select between CSR and JTAG reg interfaces
  // Basic input mux, csr_sel quasi-static
  assign s_muxed_reg2hw = regcsr_i.imc_bist_cfg.csr_sel.q ? regcsr_i : regjtag_i;
  assign unconnected_ok_s_muxed_reg2hw_status = |s_muxed_reg2hw.imc_bist_status;
  assign unconnected_ok_s_muxed_reg2hw_cfg_csr_sel = s_muxed_reg2hw.imc_bist_cfg.csr_sel.q;
  // AND-gated output demux
  assign regcsr_o = regcsr_i.imc_bist_cfg.csr_sel.q ? s_muxed_hw2reg : '0;
  assign regjtag_o = (~regcsr_i.imc_bist_cfg.csr_sel.q) ? s_muxed_hw2reg : '0;

  /// --------------------------------------
  /// ----- 2. RISING EDGE DETECTORS -------
  /// --------------------------------------
  // Rising edge detectors, will be included in the synchronizers...
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_mbist_start_q <= 1'b0;
    else r_mbist_start_q <= s_muxed_reg2hw.imc_bist_cmd.mbist_start.q;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cbist_start_q <= 1'b0;
    else r_cbist_start_q <= s_muxed_reg2hw.imc_bist_cmd.cbist_start.q;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_resume_q <= 1'b0;
    else r_resume_q <= s_muxed_reg2hw.imc_bist_cmd.resume.q;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_stop_q <= 1'b0;
    else r_stop_q <= s_muxed_reg2hw.imc_bist_cmd.stop.q;

  assign s_mbist_start_rising_edge_p = s_muxed_reg2hw.imc_bist_cmd.mbist_start.q & ~r_mbist_start_q;
  assign s_cbist_start_rising_edge_p = s_muxed_reg2hw.imc_bist_cmd.cbist_start.q & ~r_cbist_start_q;
  assign s_resume_rising_edge_p      = s_muxed_reg2hw.imc_bist_cmd.resume.q & ~r_resume_q;
  assign s_stop_rising_edge_p        = s_muxed_reg2hw.imc_bist_cmd.stop.q & ~r_stop_q;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_mbist_start_rising_edge_p <= 1'b0;
    else r_mbist_start_rising_edge_p <= s_mbist_start_rising_edge_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cbist_start_rising_edge_p <= 1'b0;
    else r_cbist_start_rising_edge_p <= s_cbist_start_rising_edge_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_resume_rising_edge_p <= 1'b0;
    else r_resume_rising_edge_p <= s_resume_rising_edge_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_stop_rising_edge_p <= 1'b0;
    else r_stop_rising_edge_p <= s_stop_rising_edge_p;

  // Derivative pulses
  assign s_any_start_rising_edge_p = s_mbist_start_rising_edge_p | s_cbist_start_rising_edge_p;

  /// --------------------------------------
  /// ----- 3. STATE FSM -------------------
  /// --------------------------------------
  // Evaluate configuration
  // Normal mode
  assign s_eval_cfg_norm = ~s_muxed_reg2hw.imc_bist_cfg.fail_analysis & ~s_muxed_reg2hw.imc_bist_cfg.burn_in.q;
  // Burnin mode
  assign s_eval_cfg_bim = s_muxed_reg2hw.imc_bist_cfg.burn_in.q;
  // Failure analysis mode
  assign s_eval_cfg_fam = s_muxed_reg2hw.imc_bist_cfg.fail_analysis & ~s_muxed_reg2hw.imc_bist_cfg.burn_in.q;

  // Evaluate transitions
  /// ---> Start BIST
  assign s_fsm_hint.run_norm_from_idle = (r_state == E_IDLE) & s_any_start_rising_edge_p & s_eval_cfg_norm;
  assign s_fsm_hint.run_bim_from_idle = (r_state == E_IDLE) & s_any_start_rising_edge_p & s_eval_cfg_bim;
  assign s_fsm_hint.run_fam_from_idle = (r_state == E_IDLE) & s_any_start_rising_edge_p & s_eval_cfg_fam;

  /// ---> Stop BIST
  // Hit the brakes if 1. gen is DONE, 2. fault has been detected, 3. SW STOP
  // All non-stopping non-idle states have imediate stop access
  assign s_fsm_hint.stopping_from_run_norm = (r_state == E_RUN_NORM) & (~busy_i | fault_det_i | s_stop_rising_edge_p);
  assign s_fsm_hint.stopping_from_run_bim = (r_state == E_RUN_BIM) & (fault_det_i | s_stop_rising_edge_p);
  assign s_fsm_hint.stopping_from_run_fam = (r_state == E_RUN_FAM) & s_stop_rising_edge_p;
  assign s_fsm_hint.stopping_from_pausing = (r_state == E_PAUSING) & s_stop_rising_edge_p;
  assign s_fsm_hint.stopping_from_unpausing = (r_state == E_UNPAUSING) & s_stop_rising_edge_p;
  // Stopping state runs a fixed LBrakingDistance cycles
  assign s_fsm_hint.idle_from_stopping = (r_state == E_STOPPING) & (r_current_braking_distance == LBrakingDistance);

  /// ---> Restart BIST (Burnin mode)
  // Restart burn-in cycle if we reach end of current bist type
  assign s_fsm_hint.run_bim_from_run_bim = (r_state == E_RUN_BIM) & (~busy_i & ~fault_det_i & ~s_stop_rising_edge_p);

  /// ---> Pause/Unpause BIST (Failure analysis mode)
  // Start pausing if failure is detected or generator is done
  // Pause on generator done because we can have failures arriving during flush
  assign s_fsm_hint.pausing_from_run_fam = (r_state == E_RUN_FAM) & (fault_det_i | ~busy_i);
  // Pause with failure found means enter analysis mode
  assign s_fsm_hint.paused_from_pausing = (r_state == E_PAUSING) & (r_current_braking_distance == LBrakingDistance) & fault_valid_i;
  // Pause without failure found means test has passed, return to idle
  assign s_fsm_hint.idle_from_pausing = (r_state == E_PAUSING) & (r_current_braking_distance == LBrakingDistance) & ~fault_valid_i;
  // Unpause when SW/JTAG acknowledges failure
  assign s_fsm_hint.unpausing_from_paused = (r_state == E_PAUSED) & s_resume_rising_edge_p;
  // Re-pause if back-to-back failures exist during unpause
  assign s_fsm_hint.paused_from_unpausing = (r_state == E_UNPAUSING) & fault_valid_i;
  assign s_fsm_hint.run_fam_from_unpausing = (r_state == E_UNPAUSING) & ~fault_valid_i;

  assign s_fsm_hint.idle_from_invalid_state = ~(r_state inside {E_IDLE, E_RUN_NORM, E_STOPPING, E_RUN_BIM, E_RUN_FAM, E_PAUSING, E_PAUSED, E_UNPAUSING});

  // Apply transitions
  always_comb begin : s_state_cproc
    s_state = r_state;
    if (s_fsm_hint.run_norm_from_idle) s_state = E_RUN_NORM;
    else if (s_fsm_hint.run_bim_from_idle) s_state = E_RUN_BIM;
    else if (s_fsm_hint.run_fam_from_idle) s_state = E_RUN_FAM;
    else if (s_fsm_hint.run_bim_from_run_bim) s_state = E_RUN_BIM;
    else if (s_fsm_hint.stopping_from_run_norm) s_state = E_STOPPING;
    else if (s_fsm_hint.stopping_from_run_bim) s_state = E_STOPPING;
    else if (s_fsm_hint.stopping_from_run_fam) s_state = E_STOPPING;
    else if (s_fsm_hint.stopping_from_pausing) s_state = E_STOPPING;
    else if (s_fsm_hint.stopping_from_unpausing) s_state = E_STOPPING;
    else if (s_fsm_hint.idle_from_stopping) s_state = E_IDLE;
    else if (s_fsm_hint.pausing_from_run_fam) s_state = E_PAUSING;
    else if (s_fsm_hint.paused_from_pausing) s_state = E_PAUSED;
    else if (s_fsm_hint.unpausing_from_paused) s_state = E_UNPAUSING;
    else if (s_fsm_hint.idle_from_pausing) s_state = E_IDLE;
    else if (s_fsm_hint.paused_from_unpausing) s_state = E_PAUSED;
    else if (s_fsm_hint.run_fam_from_unpausing) s_state = E_RUN_FAM;
    else if (s_fsm_hint.idle_from_invalid_state) s_state = E_IDLE;
  end : s_state_cproc

  // Store state
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_state <= E_IDLE;
    else r_state <= s_state;

  // FSM additional logic
  // Braking distance counter
  always_comb begin : s_current_braking_distance_cproc
    if (r_state == E_STOPPING) s_current_braking_distance = (r_current_braking_distance + 1'b1);
    else if (r_state == E_PAUSING) s_current_braking_distance = (r_current_braking_distance + 1'b1);
    else if (s_fsm_hint.stopping_from_run_norm) s_current_braking_distance = '0;
    else if (s_fsm_hint.stopping_from_run_bim) s_current_braking_distance = '0;
    else if (s_fsm_hint.stopping_from_run_fam) s_current_braking_distance = '0;
    else if (s_fsm_hint.stopping_from_pausing) s_current_braking_distance = '0;
    else if (s_fsm_hint.stopping_from_unpausing) s_current_braking_distance = '0;
    else if (s_fsm_hint.pausing_from_run_fam) s_current_braking_distance = '0;
    else s_current_braking_distance = r_current_braking_distance;
  end : s_current_braking_distance_cproc

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_braking_distance <= '0;
    else r_current_braking_distance <= s_current_braking_distance;

  // bist type triggered by SW/JTAG
  assign s_bist_type_by_leaving_idle = s_cbist_start_rising_edge_p ? E_IMC_CBIST : E_IMC_MBIST;
  // bist type triggered by burnin mode (just toggle the mode)
  assign s_bist_type_by_restarting_burnin = (r_current_run_bist_type_latch == E_IMC_CBIST) ? E_IMC_MBIST : E_IMC_CBIST;

  /// --------------------------------------
  /// ----- 4. STATE OBSERVATION -----------
  /// --------------------------------------
  // State observation - For output drivers
  assign s_entering_idle_p = (r_state != E_IDLE) & (s_state == E_IDLE);
  assign s_leaving_idle_p = (r_state == E_IDLE) & (s_state != E_IDLE);
  assign s_entering_paused_p = (r_state != E_PAUSED) & (s_state == E_PAUSED);
  assign s_leaving_paused_p = (r_state == E_PAUSED) & (s_state != E_PAUSED);
  assign s_entering_unpausing_p = (r_state != E_UNPAUSING) & (s_state == E_UNPAUSING);
  assign s_entering_stopping_p = (r_state != E_STOPPING) & (s_state == E_STOPPING);
  assign s_restarting_burnin_p = (r_state == E_RUN_BIM) & s_fsm_hint.run_bim_from_run_bim;

  // Delayed versions of observation helpers - For ACKs and DONE
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_entering_idle_p <= 1'b0;
    else r_entering_idle_p <= s_entering_idle_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_leaving_idle_p <= 1'b0;
    else r_leaving_idle_p <= s_leaving_idle_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_entering_stopping_p <= 1'b0;
    else r_entering_stopping_p <= s_entering_stopping_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_entering_paused_p <= 1'b0;
    else r_entering_paused_p <= s_entering_paused_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_leaving_paused_p <= 1'b0;
    else r_leaving_paused_p <= s_leaving_paused_p;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_entering_unpausing_p <= 1'b0;
    else r_entering_unpausing_p <= s_entering_unpausing_p;

  // Current run observation
  // Latch failing state - drives PASS low
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_run_fail_det_latch <= 1'b0;
    else if (s_leaving_idle_p) r_current_run_fail_det_latch <= 1'b0;
    else if (fault_det_i) r_current_run_fail_det_latch <= 1'b1;

  // Latch SW STOP state - drives PASS low (if not burn-in)
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_run_stop_det_latch <= 1'b0;
    else if (s_leaving_idle_p) r_current_run_stop_det_latch <= 1'b0;
    else if (s_stop_rising_edge_p) r_current_run_stop_det_latch <= 1'b1;

  // Latch BIST mode
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_run_bist_type_latch <= E_IMC_MBIST;
    else if (s_leaving_idle_p) r_current_run_bist_type_latch <= s_bist_type_by_leaving_idle;
    else if (s_restarting_burnin_p)
      r_current_run_bist_type_latch <= s_bist_type_by_restarting_burnin;

  // Latch single pass (only used for burnin mode)
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_run_single_pass_latch <= 1'b0;
    else if (s_leaving_idle_p) r_current_run_single_pass_latch <= 1'b0;
    else if (~r_current_run_fail_det_latch & ~r_current_run_stop_det_latch & ~busy_i)
      r_current_run_single_pass_latch <= 1'b1;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_current_run_bim_latch <= 1'b0;
    else if (s_leaving_idle_p) r_current_run_bim_latch <= s_fsm_hint.run_bim_from_idle;

  /// --------------------------------------
  /// ----- 5. DRIVE OUTPUTS ---------------
  /// --------------------------------------
  // Normal run passes if the test was not stopped and there were no failures
  // Burn-in run passes if at least 1 BIST type ran to completion and there were no failures
  assign s_eval_pass = (r_current_run_bim_latch ? r_current_run_single_pass_latch : ~r_current_run_stop_det_latch) &
                        ~r_current_run_fail_det_latch;

  // Outputs HW2REG
  // CTL
  // Acknowledge START/RESUME/STOP CMDs by clearing the register
  //   on the cycle after the pulses are sent to subblocks
  assign s_update_status_p = s_entering_idle_p | s_leaving_idle_p | s_entering_paused_p | s_leaving_paused_p;
  assign s_set_status_p = s_entering_idle_p | s_entering_paused_p;
  assign r_update_status_p = r_entering_idle_p | r_leaving_idle_p | r_entering_paused_p | r_leaving_paused_p;
  assign r_set_status_p = r_entering_idle_p | r_entering_paused_p;

  assign s_muxed_hw2reg.imc_bist_cmd.mbist_start = '{
          // We can leave idle through MBIST or CBIST start, filter it
          de:
          r_leaving_idle_p
          &
          r_mbist_start_rising_edge_p,
          d: 1'b0
      };
  assign s_muxed_hw2reg.imc_bist_cmd.cbist_start = '{
          de: r_leaving_idle_p & r_cbist_start_rising_edge_p,
          d: 1'b0
      };
  assign s_muxed_hw2reg.imc_bist_cmd.resume = '{de: r_entering_unpausing_p, d: 1'b0};
  assign s_muxed_hw2reg.imc_bist_cmd.stop = '{
          // We can enter stopping through FE of GEN busy or through SW STOP, filter it
          de:
          r_entering_stopping_p
          &
          r_stop_rising_edge_p,
          d: 1'b0
      };
  // STATUS
  assign s_muxed_hw2reg.imc_bist_status.busy = '{
          de: s_entering_idle_p | s_leaving_idle_p,
          d: s_leaving_idle_p
      };
  assign s_muxed_hw2reg.imc_bist_status.done = '{de: r_update_status_p, d: r_set_status_p};
  assign s_muxed_hw2reg.imc_bist_status.pass = '{
          de: s_update_status_p,
          d: s_entering_idle_p & s_eval_pass
      };
  assign s_muxed_hw2reg.imc_bist_status.repair_needed = '0; // To be provided by BIRA controller
  assign s_muxed_hw2reg.imc_bist_status.error_bank = '{
          de: s_update_status_p,
          d: (s_set_status_p ? fault_bank_i : '0)
      };
  assign s_muxed_hw2reg.imc_bist_status.error_col = '{
          de: s_update_status_p,
          d: (s_set_status_p ? fault_col_i : '0)
      };
  assign s_muxed_hw2reg.imc_bist_status.error_cycle = '{
          de: s_update_status_p,
          d: (s_set_status_p ? fault_cycle_i : '0)
      };

  // Outputs GEN
  always_comb begin : start_cproc
    // Detect when to (re)start

    // If we are idle and we get a CBIST or MBIST pulse
    // else if we are in burnin and the current mode finishes
    if (r_state == E_IDLE & s_any_start_rising_edge_p) start_p_int = 1'b1;
    else if (r_state == E_RUN_BIM & s_fsm_hint.run_bim_from_run_bim) start_p_int = 1'b1;
    else start_p_int = 1'b0;
  end : start_cproc

  always_comb begin : resume_cproc
    // Detect when to resume

    if (r_state == E_UNPAUSING & s_fsm_hint.run_fam_from_unpausing) resume_p_int = 1'b1;
    else resume_p_int = 1'b0;
  end : resume_cproc

  always_comb begin : stop_cproc
    // Detect when to stop

    if (r_state == E_RUN_NORM & (s_stop_rising_edge_p | fault_det_i)) stop_p_int = 1'b1;
    else if (r_state == E_RUN_BIM & (s_stop_rising_edge_p | fault_det_i)) stop_p_int = 1'b1;
    else if (r_state == E_RUN_FAM & (s_stop_rising_edge_p | fault_det_i)) stop_p_int = 1'b1;
    else stop_p_int = 1'b0;
  end : stop_cproc

  always_comb begin : bist_type_cproc
    // Detect bist type

    // If we are starting through SW/JTAG
    // else if we are restarting from burnin mode
    // else use latched bist type
    if (r_state == E_IDLE & s_any_start_rising_edge_p) bist_type_int = s_bist_type_by_leaving_idle;
    else if (r_state == E_RUN_BIM & s_fsm_hint.run_bim_from_run_bim)
      bist_type_int = s_bist_type_by_restarting_burnin;
    else bist_type_int = r_current_run_bist_type_latch;
  end : bist_type_cproc

  always_comb begin : fault_pop_cproc
    // Detect fault pop

    if (r_state == E_PAUSED & s_fsm_hint.unpausing_from_paused) fault_pop_int = 1'b1;
    else fault_pop_int = 1'b0;
  end : fault_pop_cproc

  // Assign outputs
  assign start_po = start_p_int;
  assign resume_po = resume_p_int;
  assign stop_po = stop_p_int;
  assign bist_type_o = bist_type_int;

  // Outputs IMUX/IMUXC
  assign bist_mode_o = ~(r_state == E_IDLE) || s_any_start_rising_edge_p;

  // Outputs COLL
  assign fault_pop_o = fault_pop_int;

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
`endif  // ASSERTIONS_ON
  //synopsys translate_on
  // verilog_lint: waive-stop line-length
endmodule
`endif  // IMC_BIST_CTL_SV
