// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Yasen Kazandzhiev <yasen.kazandzhiev@axelera.ai>


module dwm_boost_manager #(
  /// Number of throttle requests - min value is 2
  parameter int unsigned N_REQ = 2,
  /// Data structure used to define the power budget structure
  parameter type data_t = logic [7:0],
  /// Number of synchronization stages
  parameter int unsigned SyncStages = 3
)(
  /// Clock, positive edge triggered
  input  wire               i_clk,
  /// Asynchronous reset, active low
  input  wire               i_rst_n,
  /// External Throttle trigger which revokes the boost acknowledge
  input  logic              i_throttle,
  /// Defines the additional budget that can be requested per AI Core
  input  data_t [N_REQ-1:0] i_req_boost_value,
  /// Defines the standard budget available
  input  data_t             i_budget_value,
  /// Overwrite the budget available stored internally
  input  logic              i_budget_overwrite,
  /// Boost request from each AI Core
  input  logic [N_REQ-1:0]  i_boost_req,
  /// Give permission to boost utilization per AI Core
  output logic [N_REQ-1:0]  o_boost_ack
);

  if (N_REQ < 2) $fatal(1, "Parameter: 'N_REQ' must be at least 2;");

  localparam int unsigned N_REQ_LOG = cc_math_pkg::index_width(N_REQ);
  localparam type idx_t = logic [N_REQ_LOG-1:0];

  typedef struct packed {
    data_t    value;
    logic     en;
  } add_val_t;

  logic              internal_pipe_flush;
  logic  [N_REQ-1:0] boost_req_to_arb_q;
  logic  [N_REQ-1:0] boost_req_fall_edge;
  logic  [N_REQ-1:0] arb_gnt;
  data_t             req_boost_value_selected;
  logic              arb_valid;
  logic              ready_to_arb;
  idx_t              req_boost_selected_idx;
  data_t             avail_power_budget_q;
  data_t             decr_avail_power_budget;
  add_val_t          total_power_budget_to_return_d;
  add_val_t          total_power_budget_to_return_q;
  logic  [N_REQ-1:0] power_budget_to_return_en;

  // Flush the internal pipeline and revokes the boost acknowledge
  always_comb internal_pipe_flush = (i_throttle | i_budget_overwrite);

  for (genvar I = 0; I < N_REQ; I++) begin : g_process_boost_req

    logic boost_req_sync;
    logic boost_req_sync_gated;
    logic boost_req_raise_edge;

    // Synchronization for i_boost_req signal coming from AI Core
    axe_tcl_seq_sync #(
      .SyncStages(SyncStages),
      .ResetValue(1'b0)
    ) u_i_boost_req_sync (
      .i_clk   (i_clk),
      .i_rst_n (i_rst_n),
      .i_d     (i_boost_req[I]),
      .o_q     (boost_req_sync)
    );

    always_comb boost_req_sync_gated = (boost_req_sync & ~internal_pipe_flush);

    // Instantiation of pulse detector
    axe_ccl_mon_edge_detector u_boost_req_edge_detector (
      .i_clk    (i_clk),
      .i_rst_n  (i_rst_n),
      .i_signal (boost_req_sync_gated),
      .o_raise  (boost_req_raise_edge),
      .o_fall   (boost_req_fall_edge[I])
    );

    // Flop to hold the request to the arbiter until it's granted
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n)
        boost_req_to_arb_q[I] <= 1'b0;
      else if ((boost_req_to_arb_q[I] & arb_gnt[I]) | boost_req_fall_edge[I])
        boost_req_to_arb_q[I] <= 1'b0;
      else if (boost_req_raise_edge)
        boost_req_to_arb_q[I] <= 1'b1;
    end
  end : g_process_boost_req

  // Instantiation of first-come-first-serve arbiter
  rr_arb_tree #(
    .NumIn      (N_REQ),
    .datatype_t (data_t),
    .ExtPrio    (1'b0),
    .AxiVldRdy  (1'b1),
    .LockIn     (1'b1),
    .FairArb    (1'b1)
  ) u_rr_arb_tree (
    .i_clk      (i_clk),
    .i_rst_n    (i_rst_n),
    .flush_i    (internal_pipe_flush),
    .rr_i       ('0),
    .req_i      (boost_req_to_arb_q),
    .gnt_o      (arb_gnt),
    .data_i     (i_req_boost_value),
    .req_o      (arb_valid),
    .gnt_i      (ready_to_arb),
    .data_o     (req_boost_value_selected),
    .idx_o      (req_boost_selected_idx)
  );

  // Generate ready to the arbiter only if the available power budget exceeds the additional power budget requested by the selected device
  always_comb ready_to_arb = (arb_valid & (avail_power_budget_q >= req_boost_value_selected));

  // Decrement the value of the available power budget only if acknowledge the request from the arbiter
  assign decr_avail_power_budget = (ready_to_arb) ? (avail_power_budget_q - req_boost_value_selected) : avail_power_budget_q;

  logic avail_power_budget_en;
  always_comb avail_power_budget_en = (internal_pipe_flush | total_power_budget_to_return_q.en | ready_to_arb);

  // Register to store the available power budget
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n)
      avail_power_budget_q <= '0;
    else if (avail_power_budget_en) begin
      if (internal_pipe_flush)
        avail_power_budget_q <= i_budget_value;
      else if (total_power_budget_to_return_q.en) // equivalent to delayed |power_budget_to_return_en
        avail_power_budget_q <= (decr_avail_power_budget + total_power_budget_to_return_q.value);
      else if (ready_to_arb)
        avail_power_budget_q <= decr_avail_power_budget;
    end
  end

  for (genvar I = 0; I < N_REQ; I++) begin : g_process_req_fall_edge_and_boost_ack

    // Need to return the power budget by a requester during the falling edge of i_boost_req only if
    // the budget has previously been consumed (indicated by the corresponding o_boost_ack)
    always_comb power_budget_to_return_en[I] = (boost_req_fall_edge[I] & o_boost_ack[I]);

    // Registers for boost_ack
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (~i_rst_n)
        o_boost_ack[I] <= 1'b0;
      else if (internal_pipe_flush | power_budget_to_return_en[I])
        o_boost_ack[I] <= 1'b0;
      else if (ready_to_arb & (req_boost_selected_idx == I))
        o_boost_ack[I] <= 1'b1;
    end
  end : g_process_req_fall_edge_and_boost_ack

  // Logic to add N_REQ number of values (since at the same cycle, potentially, we can have up to N_REQ falling edges for all boost request signals)
  always_comb begin
    total_power_budget_to_return_d.en = |power_budget_to_return_en;
    total_power_budget_to_return_d.value = '0;
    for (int unsigned i=0; i < N_REQ; i++) begin
      if(power_budget_to_return_en[i]) total_power_budget_to_return_d.value += i_req_boost_value[i];
    end
  end

  // Flop the final added value and associated enable, then go to the accumulator (avail_power_budget_q)
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (~i_rst_n)
      total_power_budget_to_return_q <= add_val_t'(0);
    else
      total_power_budget_to_return_q <= total_power_budget_to_return_d;
  end

endmodule
