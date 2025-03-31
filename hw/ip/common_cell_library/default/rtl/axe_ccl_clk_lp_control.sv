// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// Low Power clock controller using AMBA LowPower interface for the handshake.
///
/// Turn of the clock after low power request is accepted and no activity is observed.
/// Uses a variable timeout to governs how fast this should happen after activity is signaled to be idle.
///

module axe_ccl_clk_lp_control #(
  /// Port width setting for the idle delay
  parameter int unsigned IdleDelayW = 4
)(
  ///////////////////
  // Configuration //
  ///////////////////
  /// Clock, positive edge triggered
  input  wire     i_clk,
  /// Asynchronous reset
  input  wire     i_rst_n,
  /// Clock_gate bypass enable
  input  logic    i_scan_en,

  /// Low Power enable
  input  logic                  i_low_power_en,
  /// Low Power active, clock is gated when set
  output logic                  o_low_power_active,
  /// Low Power idle delay, wait this amount of cycles before going into low power state
  input  logic [IdleDelayW-1:0] i_low_power_idle_delay,

  /////////////////////////
  // Low Power Interface //
  /////////////////////////
  /// QREQn
  output logic    o_qreq_n,
  /// QDENY
  input  logic    i_qdeny,
  /// QACCEPTn
  input  logic    i_qaccept_n,
  /// QACTIVE
  input  logic    i_qactive,

  /// Output gated clock
  output wire     o_clk
);

  // Protocol states
  typedef enum logic[3:0] {
    q_run,
    q_request,
    q_stopped,
    q_exit,
    q_denied,
    q_continue
  } qstate_e;

  /////////////
  // Signals //
  /////////////
  qstate_e  qstate_d, qstate_q;
  logic qstate_stopped_d, qstate_stopped_q;
  logic clk_enable;
  logic [IdleDelayW-1:0] idle_cnt_d, idle_cnt_q;
  logic idle_cnt_zero_nd, idle_cnt_zero_nq;
  logic idle_n;
  logic qreq_n_d;

  //////////////////
  // Idle Check   //
  //////////////////
    // count for idle when qreq_n and active are both zero; don't underflow
  always_comb idle_cnt_d = (i_qactive) ? i_low_power_idle_delay :
                              (|idle_cnt_q) ? idle_cnt_q - 1 : idle_cnt_q;
    // 'predict' the zero notification, such that it can be flopped together with the data
  always_comb idle_cnt_zero_nd = |idle_cnt_d;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)     idle_cnt_q <= '1;
    else if (idle_cnt_d != idle_cnt_q) {idle_cnt_zero_nq, idle_cnt_q} <= {idle_cnt_zero_nd, idle_cnt_d};
  end

  ///////////////////
  // State Control //
  ///////////////////
  always_comb begin
    qstate_d = qstate_q;

    unique case (qstate_q)
      q_run: begin
        if ((~idle_cnt_zero_nq) & (~i_qactive) & i_low_power_en)
          qstate_d = q_request;
      end

      q_request: begin
        if (i_qactive | i_qdeny)
          qstate_d = q_denied;
        else if (~i_qaccept_n) // use same latency as qactive and qdeny to make sure those are alligend
          qstate_d = q_stopped;
      end

      q_stopped: begin
        if (i_qactive | (~i_low_power_en)) // use direct inputs to exit as soon as possible
          qstate_d = q_exit;
      end

      q_exit, q_continue: begin
        if (i_qaccept_n & (~i_qdeny))
          qstate_d = q_run;
      end

      q_denied: begin
        qstate_d = q_continue;
      end

      default: qstate_d = q_run;
    endcase
  end

  always_comb qreq_n_d = (qstate_d inside {q_run, q_exit, q_continue}) ? 1'b1 : 1'b0;
  always_comb qstate_stopped_d = (qstate_d == q_stopped);

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      qstate_q <= q_run;
      qstate_stopped_q <= 1'b0;
      o_qreq_n <= 1'b0;
    end else if (qstate_q != qstate_d) begin
      qstate_q <= qstate_d;
      qstate_stopped_q <= qstate_stopped_d;
      o_qreq_n <= qreq_n_d;
    end
  end
  always_comb o_low_power_active = qstate_stopped_q;

  //////////////////////
  // The clock gating //
  //////////////////////
    // clk enable is driven low in case qstate == stopped
  always_comb clk_enable = qstate_stopped_q ? 1'b0 : 1'b1;
  axe_tcl_clk_gating u_clk_gate (
    .i_clk,
    .i_en     (clk_enable),
    .i_test_en(i_scan_en),
    .o_clk
  );

endmodule
