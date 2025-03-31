// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: C2C monitor behavioral model.
//
// Authors: Manuel Oliveira

module c2c_monitor_wrapper
  import c2c_monitor_wrapper_pkg::*;
  (
    input  wire             i_pll_clk,
    input  wire             i_test_mode,
    input  wire             i_clk,
    input  wire             i_rst_n,
    input  logic            i_enable,
    input  c2c_cfg_t        i_cfg,
    output logic            o_axis_valid,
    output c2c_data_width_t o_axis_data
  );

  // =====================================================
  // Signal declarations
  // =====================================================

  wire                          pll_clk_gated;
  c2c_count_t             [2:0] c2c_counters;
  c2c_count_t                   medium_vote;
  c2c_count_t                   voting_result_d;
  c2c_count_t                   voting_result_q;
  logic                         voting_cdc_busy;
  logic                         enable_q;
  logic                         enable_sync;
  logic                   [1:0] valid_result_count;
  logic                         valid_result;
  c2c_cfg_t                     cfg;
  c2c_vote_opt_e                vote_cfg_sync;
  logic                         vote_cfg_update_d;
  logic                         vote_cfg_update_q;
  logic                         vote_cfg_cdc_busy;
  c2c_count_t                   data;
  logic                         data_valid;
  c2c_data_width_t              axis_data;
  logic                         axis_valid;
  logic [1:0][CA_RESULT_WD-1:0] mult_const_a_d;
  logic [1:0][CA_RESULT_WD-1:0] mult_const_a_q;
  logic [1:0][CB_RESULT_WD-1:0] mult_const_b_d;
  logic [1:0][CB_RESULT_WD-1:0] mult_const_b_q;
  logic [1:0][CC_RESULT_WD-1:0] mult_const_c_d;
  logic [1:0][CC_RESULT_WD-1:0] mult_const_c_q;
  logic [1:0][MARGIN_WD   -1:0] margins;
  logic      [MARGIN_WD   -1:0] min_margin;

  // =====================================================
  // RTL
  // =====================================================

  always_ff @(posedge i_clk, negedge i_rst_n) begin : enable_monitor_seq_proc
    if (!i_rst_n)                 enable_q <= 1'b0;
    else if (i_enable ^ enable_q) enable_q <= i_enable;
  end

  axe_tcl_seq_sync #(
    .SyncStages( 2 ),
    .ResetValue(1'b0)
  ) u_enable_sync (
    .i_clk  (i_pll_clk),
    .i_rst_n(i_rst_n),
    .i_d    (enable_q),
    .o_q    (enable_sync)
  );

  axe_tcl_clk_gating u_clk_gate (
    .i_clk    (i_pll_clk),
    .i_en     (enable_sync),
    .i_test_en(i_test_mode),
    .o_clk    (pll_clk_gated)
  );

  always_ff @(posedge i_clk, negedge i_rst_n) begin : vote_cfg_seq_proc
    if (!i_rst_n)                                     cfg <= c2c_cfg_t'(0);
    else if (vote_cfg_update_d && !vote_cfg_cdc_busy) cfg <= i_cfg;
  end

  always_comb vote_cfg_update_d = i_cfg ^ cfg;

  always_ff @(posedge i_clk, negedge i_rst_n) begin : vote_cfg_update_seq_proc
    if (!i_rst_n)                                   vote_cfg_update_q <= 1'b0;
    else if (vote_cfg_update_d ^ vote_cfg_update_q) vote_cfg_update_q <= vote_cfg_update_d;
  end

  axe_ccl_cdc_bus #(
    .SyncStages ( 2 ),
    .data_t     ( c2c_vote_opt_e )
  ) u_vote_cfg_resync (
    .i_src_clk    (i_clk),
    .i_src_rst_n  (i_rst_n),
    .i_src_en     (vote_cfg_update_q),
    .i_src_data   (cfg.vote),
    .o_src_busy   (vote_cfg_cdc_busy),

    .i_dst_clk    (pll_clk_gated),
    .i_dst_rst_n  (i_rst_n),
    .o_dst_data   (vote_cfg_sync),
    .o_dst_update (/* NA */)// ASO-UNUSED_OUTPUT: The values are just considered once the enable is sync with the pll_clk_gated.
  );

  for(genvar c2c = 0; c2c < 3; c2c++) begin : g_c2c
  c2c_monitor u_c2c_monitor (
    .clock   (pll_clk_gated),
    .count_0 (c2c_counters[c2c][SVT]),
    .count_1 (c2c_counters[c2c][LVT])
  );
  end

  always_comb begin : medium_vote_comb_proc
    foreach(medium_vote[count]) begin
      c2c_count_t a;
      c2c_count_t b;
      c2c_count_t c;
      a = c2c_counters[0][count];
      b = c2c_counters[1][count];
      c = c2c_counters[2][count];
      if ((a <= b) && (b <= c)) medium_vote[count] = b;  // a b c
      if ((a <= c) && (c <= b)) medium_vote[count] = c;  // a c b
      if ((b <= a) && (a <= c)) medium_vote[count] = a;  // b a c
      if ((b <= c) && (c <= a)) medium_vote[count] = c;  // b c a
      if ((c <= a) && (a <= b)) medium_vote[count] = a;  // c a b
      medium_vote[count] = b;                            // c b a
    end
  end

  always_comb begin : voting_result_comb_proc
    unique case(vote_cfg_sync)
    c2c_0:   voting_result_d = c2c_counters[c2c_0];
    c2c_1:   voting_result_d = c2c_counters[c2c_1];
    c2c_2:   voting_result_d = c2c_counters[c2c_2];
    default: voting_result_d = medium_vote;
    endcase
  end

  always_ff @(posedge pll_clk_gated, negedge i_rst_n) begin : voting_result_seq_proc
    if (!i_rst_n)                                                     voting_result_q <= c2c_count_t'(0);
    else if ((voting_result_d ^ voting_result_q) && !voting_cdc_busy) voting_result_q <= voting_result_d;
  end

  always_ff @(posedge pll_clk_gated, negedge i_rst_n) begin : valid_result_count_seq_proc
    if (!i_rst_n)                                   valid_result_count <= 2'd0;
    else if (!(|valid_result_count) & !enable_sync) valid_result_count <= 2'd0;
    else if (!valid_result & enable_sync)           valid_result_count <= valid_result_count + 2'd1;
  end

  always_comb valid_result = &valid_result_count;

  axe_ccl_cdc_bus #(
    .SyncStages ( 2 ),
    .data_t     ( c2c_count_t )
  ) u_result_resync (
    .i_src_clk    (pll_clk_gated),
    .i_src_rst_n  (i_rst_n),
    .i_src_en     (valid_result),
    .i_src_data   (voting_result_q),
    .o_src_busy   (voting_cdc_busy),

    .i_dst_clk    (i_clk),
    .i_dst_rst_n  (i_rst_n),
    .o_dst_data   (data),
    .o_dst_update (data_valid)
  );

  always_comb foreach(mult_const_a_d[index]) mult_const_a_d[index] = cfg.constants[index].A * data[LVT] * data[SVT];
  always_comb foreach(mult_const_b_d[index]) mult_const_b_d[index] = cfg.constants[index].B * data[SVT];
  always_comb foreach(mult_const_c_d[index]) mult_const_c_d[index] = cfg.constants[index].C * data[LVT];

  always_ff @( posedge i_clk, negedge i_rst_n ) begin : mult_const_A_seq_proc
    if (!i_rst_n)                             mult_const_a_q <= '0;
    else if (mult_const_a_q ^ mult_const_a_d) mult_const_a_q <= mult_const_a_d;
  end

  always_ff @( posedge i_clk, negedge i_rst_n ) begin : mult_const_B_seq_proc
    if (!i_rst_n)                             mult_const_b_q <= '0;
    else if (mult_const_b_q ^ mult_const_b_d) mult_const_b_q <= mult_const_b_d;
  end

  always_ff @( posedge i_clk, negedge i_rst_n ) begin : mult_const_C_seq_proc
    if (!i_rst_n)                             mult_const_c_q <= '0;
    else if (mult_const_c_q ^ mult_const_c_d) mult_const_c_q <= mult_const_c_d;
  end

  always_ff @( posedge i_clk, negedge i_rst_n ) begin : axis_valid_seq_proc
    if (!i_rst_n)                     axis_valid <= 1'b0;
    else if (axis_valid ^ data_valid) axis_valid <= data_valid;
  end

  always_comb foreach(margins[index]) margins[index] = mult_const_a_q + mult_const_b_q + mult_const_c_q + cfg.constants[index].D;

  always_comb min_margin = (margins[0] < margins[1]) ? margins[0] : margins[1];

  always_comb axis_data = c2c_data_width_t'(min_margin >> cfg.scale);

  always_ff @( posedge i_clk, negedge i_rst_n ) begin : out_axis_data_seq_proc
    if (!i_rst_n)                     o_axis_data <= c2c_data_width_t'(0);
    else if (o_axis_data ^ axis_data) o_axis_data <= axis_data;
  end

  always_ff @( posedge i_clk, negedge i_rst_n ) begin : out_axis_valid_seq_proc
    if (!i_rst_n)                       o_axis_valid <= '0;
    else if (o_axis_valid ^ data_valid) o_axis_valid <= data_valid;
  end

endmodule
