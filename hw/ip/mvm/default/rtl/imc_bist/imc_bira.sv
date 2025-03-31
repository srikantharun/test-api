// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   IMC repair analysis controller
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module imc_bira
  import imc_bank_pkg::IMC_BANK_COL_PW;
  import mvm_pkg::MVM_IMC_BANK_PW;
  import imc_bist_pkg::IMC_BIST_CYCLE_PW;
#(
  parameter type aic_csr_hw2reg_t = imc_bist_pkg::aic_csr_hw2reg_t,
  parameter type aic_csr_reg2hw_t = imc_bist_pkg::aic_csr_reg2hw_t
) (
  input  wire                              i_clk,
  input  wire                              i_rst_n,

  input  aic_csr_reg2hw_t                  i_mux_reg,
  output aic_csr_hw2reg_t                  o_mux_reg,
  output aic_csr_reg2hw_t                  o_ctl_reg,
  input  aic_csr_hw2reg_t                  i_ctl_reg,

  output logic                             o_clear,

  output logic                             o_imc_bisr_mux_mode,
  output logic [1:0]                       o_imc_repair_req,
  output logic [1:0] [MVM_IMC_BANK_PW-1:0] o_imc_repair_bank,
  output logic [1:0] [IMC_BANK_COL_PW-1:0] o_imc_repair_col,
  input  logic [1:0]                       i_imc_repair_ack,
  input  logic [1:0]                       i_imc_repair_nack
);

  /// -----------------------
  /// ----- TYPES -----------
  /// -----------------------
  // FSM states
  typedef enum logic [5:0] {
    E_BYPASS        = 'd0,
    E_IDLE          = 'd1,
    E_RUNNING_MBIST = 'd2,
    E_REPAIR_MBIST  = 'd4,
    E_RUNNING_CBIST = 'd8,
    E_REPAIR_CBIST  = 'd16,
    E_DONE          = 'd32
  } bira_ctl_state_e_t;

  // Onehot FSM transition vector
  typedef struct packed {
    logic bypass_from_invalid_state;
    logic bypass_from_any_state;
    logic idle_from_bypass;
    logic running_mbist_from_idle;
    logic running_cbist_from_idle;
    logic repair_mbist_from_running_mbist;
    logic running_cbist_from_running_mbist;
    logic done_from_running_mbist;
    logic running_mbist_from_repair_mbist;
    logic done_from_repair_mbist;
    logic repair_cbist_from_running_cbist;
    logic done_from_running_cbist;
    logic running_cbist_from_repair_cbist;
    logic done_from_repair_cbist;
  } fsm_transition_t;

  typedef struct packed {
    logic bypass_en;
    logic sync_clear_en;
    logic start_mbist;
    logic start_cbist;
    logic assert_repair_req;
    logic deassert_repair_req;
    logic assert_status_busy;
    logic assert_status_pass;
    logic assert_status_fail;
  } fsm_action_t;

  /// -----------------------
  /// ----- SIGNALS ---------
  /// -----------------------
  bira_ctl_state_e_t r_state, s_state;
  fsm_transition_t   s_state_transition;
  fsm_action_t       s_state_action;

  logic                         r_pass;
  logic   [MVM_IMC_BANK_PW-1:0] r_error_bank;
  logic   [IMC_BANK_COL_PW-1:0] r_error_col;
  logic [IMC_BIST_CYCLE_PW-1:0] r_error_cycle;
  logic                         r_repair_needed;

  logic r_mbist_start_q;
  logic r_cbist_start_q;
  logic s_mbist_start_rising_edge_p;
  logic s_cbist_start_rising_edge_p;

  logic s_clear;

  aic_csr_reg2hw_t r_int_cmd;
  aic_csr_hw2reg_t r_int_status;

  logic                             r_mux_mode, s_mux_mode;
  logic [1:0]                       r_imc_repair_req;
  logic [1:0] [MVM_IMC_BANK_PW-1:0] r_imc_repair_bank;
  logic [1:0] [IMC_BANK_COL_PW-1:0] r_imc_repair_col;

  /// -----------------------
  /// ----- DESIGN ----------
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)                              r_pass  <= 1'b0;
    else if(i_ctl_reg.imc_bist_status.pass.de) r_pass <= i_ctl_reg.imc_bist_status.pass.d;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)                                    r_error_bank <= '0;
    else if(i_ctl_reg.imc_bist_status.error_bank.de) r_error_bank <= i_ctl_reg.imc_bist_status.error_bank.d;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)                                   r_error_col <= '0;
    else if(i_ctl_reg.imc_bist_status.error_col.de) r_error_col <= i_ctl_reg.imc_bist_status.error_col.d;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)                                     r_error_cycle <= '0;
    else if(i_ctl_reg.imc_bist_status.error_cycle.de) r_error_cycle <= i_ctl_reg.imc_bist_status.error_cycle.d;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_mbist_start_q <= 1'b0;
    else          r_mbist_start_q <= i_mux_reg.imc_bist_cmd.mbist_start.q;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_cbist_start_q <= 1'b0;
    else          r_cbist_start_q <= i_mux_reg.imc_bist_cmd.cbist_start.q;

  assign s_mbist_start_rising_edge_p = i_mux_reg.imc_bist_cmd.mbist_start.q & ~r_mbist_start_q;
  assign s_cbist_start_rising_edge_p = i_mux_reg.imc_bist_cmd.cbist_start.q & ~r_cbist_start_q;
  assign s_any_start_rising_edge_p   = s_mbist_start_rising_edge_p | s_cbist_start_rising_edge_p;

  /// -----------------------
  /// ----- FSM -------------
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n) r_state <= E_BYPASS;
    else          r_state <= s_state;

  always_ff @(posedge i_clk, negedge i_rst_n)
    if (!i_rst_n)                r_mux_mode <= 1'b0;
    else if(|s_state_transition) r_mux_mode <= s_mux_mode;

  always_comb begin : s_state_cproc
    s_state = r_state;
         if(s_state_transition.bypass_from_invalid_state)        s_state = E_BYPASS;
    else if(s_state_transition.bypass_from_any_state)            s_state = E_BYPASS;
    else if(s_state_transition.idle_from_bypass)                 s_state = E_IDLE;
    else if(s_state_transition.running_mbist_from_idle)          s_state = E_RUNNING_MBIST;
    else if(s_state_transition.running_cbist_from_idle)          s_state = E_RUNNING_CBIST;
    else if(s_state_transition.repair_mbist_from_running_mbist)  s_state = E_REPAIR_MBIST;
    else if(s_state_transition.running_cbist_from_running_mbist) s_state = E_RUNNING_CBIST;
    else if(s_state_transition.done_from_running_mbist)          s_state = E_DONE;
    else if(s_state_transition.running_mbist_from_repair_mbist)  s_state = E_RUNNING_MBIST;
    else if(s_state_transition.done_from_repair_mbist)           s_state = E_DONE;
    else if(s_state_transition.repair_cbist_from_running_cbist)  s_state = E_REPAIR_CBIST;
    else if(s_state_transition.done_from_running_cbist)          s_state = E_DONE;
    else if(s_state_transition.running_cbist_from_repair_cbist)  s_state = E_RUNNING_CBIST;
    else if(s_state_transition.done_from_repair_cbist)           s_state = E_DONE;
  end

  always_comb begin : s_mux_mode_cproc
    s_mux_mode = r_mux_mode;
         if( s_state_transition.bypass_from_invalid_state) s_mux_mode = 1'b0;
    else if( s_state_transition.bypass_from_any_state)     s_mux_mode = 1'b0;
    else if(|s_state_transition)                           s_mux_mode = 1'b1;
  end

  assign s_state_transition.bypass_from_invalid_state =
    ~(r_state inside {E_BYPASS, E_IDLE, E_RUNNING_MBIST, E_REPAIR_MBIST, E_RUNNING_CBIST, E_REPAIR_CBIST, E_DONE});
  assign s_state_transition.bypass_from_any_state =
    ~|i_mux_reg.imc_bist_cfg.bira_mode.q;

  assign s_state_transition.idle_from_bypass =
    (r_state == E_BYPASS)
    & |i_mux_reg.imc_bist_cfg.bira_mode.q;

  assign s_state_transition.running_mbist_from_idle =
    (r_state == E_IDLE)
    & s_any_start_rising_edge_p
    & i_mux_reg.imc_bist_cfg.bira_mode[0];

  assign s_state_transition.running_cbist_from_idle =
    (r_state == E_IDLE)
    & s_any_start_rising_edge_p
    & ~i_mux_reg.imc_bist_cfg.bira_mode[0];

  assign s_state_transition.repair_mbist_from_running_mbist =
    (r_state == E_RUNNING_MBIST)
    & i_ctl_reg.imc_bist_status.done.de
    & i_ctl_reg.imc_bist_status.done.d
    & ~r_pass;

  assign s_state_transition.running_cbist_from_running_mbist =
    (r_state == E_RUNNING_MBIST)
    & i_ctl_reg.imc_bist_status.done.de
    & i_ctl_reg.imc_bist_status.done.d
    & r_pass
    & i_mux_reg.imc_bist_cfg.bira_mode[1];

  assign s_state_transition.done_from_running_mbist =
    (r_state == E_RUNNING_MBIST)
    & i_ctl_reg.imc_bist_status.done.de
    & i_ctl_reg.imc_bist_status.done.d
    & r_pass
    & ~i_mux_reg.imc_bist_cfg.bira_mode[1];

  assign s_state_transition.running_mbist_from_repair_mbist =
    (r_state == E_REPAIR_MBIST)
    & |(i_imc_repair_ack & ~i_imc_repair_nack);

  assign s_state_transition.done_from_repair_mbist =
    (r_state == E_REPAIR_MBIST)
    & (|i_imc_repair_nack);

  assign s_state_transition.repair_cbist_from_running_cbist =
    (r_state == E_RUNNING_CBIST)
    & i_ctl_reg.imc_bist_status.done.de
    & i_ctl_reg.imc_bist_status.done.d
    & ~r_pass;

  assign s_state_transition.done_from_running_cbist =
    (r_state == E_RUNNING_CBIST)
    & i_ctl_reg.imc_bist_status.done.de
    & i_ctl_reg.imc_bist_status.done.d
    & r_pass;

  assign s_state_transition.running_cbist_from_repair_cbist =
    (r_state == E_REPAIR_CBIST)
    & |(i_imc_repair_ack & ~i_imc_repair_nack);

  assign s_state_transition.done_from_repair_cbist =
    (r_state == E_REPAIR_CBIST)
    & (|i_imc_repair_nack);

  assign s_state_action.bypass_en =
    (r_state == E_BYPASS);

  assign s_state_action.sync_clear_en =
    s_state_transition.bypass_from_invalid_state
    | s_state_transition.bypass_from_any_state
    | s_state_transition.idle_from_bypass;

  assign s_state_action.start_mbist =
    s_state_transition.running_mbist_from_idle
    | s_state_transition.running_mbist_from_repair_mbist;

  assign s_state_action.start_cbist =
    s_state_transition.running_cbist_from_idle
    | s_state_transition.running_cbist_from_repair_cbist
    | s_state_transition.running_cbist_from_running_mbist;

  assign s_state_action.assert_repair_req =
    s_state_transition.repair_mbist_from_running_mbist
    | s_state_transition.repair_cbist_from_running_cbist;

  assign s_state_action.deassert_repair_req =
    s_state_transition.running_mbist_from_repair_mbist
    | s_state_transition.running_cbist_from_repair_cbist;

  assign s_state_action.assert_status_busy =
    s_state_transition.running_mbist_from_idle
    | s_state_transition.running_cbist_from_idle;

  assign s_state_action.assert_status_pass =
    s_state_transition.done_from_running_mbist
    | s_state_transition.done_from_running_cbist;

  assign s_state_action.assert_status_fail =
    s_state_transition.done_from_repair_mbist
    | s_state_transition.done_from_repair_cbist;

  /// -----------------------
  /// ----- Internal --------
  /// -----------------------
  assign s_clear = s_state_action.sync_clear_en;

  /// -----------------------
  /// ----- Commands --------
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n)
    if(!i_rst_n) r_int_cmd <= '{default: '0};
    else begin
      r_int_cmd <= '{default: '0};
      if(s_state_action.start_mbist)
        r_int_cmd.imc_bist_cmd.mbist_start.q <= 1'b1;
      else if(s_state_action.start_cbist)
        r_int_cmd.imc_bist_cmd.cbist_start.q <= 1'b1;
    end

  /// -----------------------
  /// ----- Repair request --
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n) begin
      r_imc_repair_req  <= '0;
      r_imc_repair_bank <= '0;
      r_imc_repair_col  <= '0;
      r_repair_needed   <= '0;
    end else begin
      if(s_clear) begin
        r_imc_repair_req  <= '0;
        r_imc_repair_bank <= '0;
        r_imc_repair_col  <= '0;
        r_repair_needed   <= '0;
      end if(s_state_action.assert_repair_req) begin
        // Two repair requests are generated in CBIST mode.
        // Because CBIST is a neighbor-compare technique,
        //   it's not possible to determine which bank is correct
        r_imc_repair_req  <= {(r_state == E_RUNNING_CBIST), 1'b1};
        r_imc_repair_bank <= {(r_error_bank-2), r_error_bank};
        r_imc_repair_col  <= {2{r_error_col}};
        r_repair_needed   <= '1;
      end else if(s_state_action.deassert_repair_req) begin
        r_imc_repair_req <= '0;
      end
    end
  end

  /// -----------------------
  /// ----- Status ----------
  /// -----------------------
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if(!i_rst_n) r_int_status <= '{default: '0};
    else begin
      r_int_status <= '{default: '0};
      if(s_state_action.assert_status_busy
          | s_state_action.assert_status_pass
          | s_state_action.assert_status_fail)
      begin
        r_int_status.imc_bist_status <= '{
          busy: '{
            de: 1'b1,
            d : s_state_action.assert_status_busy
          },
          done: '{
            de: 1'b1,
            d : s_state_action.assert_status_pass | s_state_action.assert_status_fail
          },
          pass: '{
            de: 1'b1,
            d : s_state_action.assert_status_pass & ~s_state_action.assert_status_fail
          },
          error_bank: '{
            de: 1'b1,
            d : s_state_action.assert_status_fail ? r_error_bank : '0
          },
          error_col: '{
            de: 1'b1,
            d : s_state_action.assert_status_fail ? r_error_col : '0
          },
          error_cycle: '{
            de: 1'b1,
            d : s_state_action.assert_status_fail ? r_error_cycle : '0
          },
          repair_needed: '{
            de: 1'b1,
            d : s_state_action.assert_status_busy ? 1'b0 : r_repair_needed
          }
        };
      end
    end
  end

  /// -----------------------
  /// ----- Outputs ---------
  /// -----------------------
  assign o_mux_reg           = s_state_action.bypass_en ? i_ctl_reg : r_int_status;
  assign o_ctl_reg           = s_state_action.bypass_en ? i_mux_reg : r_int_cmd;
  assign o_clear             = s_state_action.sync_clear_en;
  assign o_imc_bisr_mux_mode = r_mux_mode;
  assign o_imc_repair_req    = r_imc_repair_req;
  assign o_imc_repair_bank   = r_imc_repair_bank;
  assign o_imc_repair_col    = r_imc_repair_col;

endmodule : imc_bira
