// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// SVA of boost requester
///

`ifndef DWM_BOOST_REQUESTER_SVA_SV
`define DWM_BOOST_REQUESTER_SVA_SV

module dwm_boost_requester_sva #(
  parameter bit ENABLE_ASSERT  = 1'b1,
  parameter bit ENABLE_ASSUME  = 1'b1,
  parameter bit ENABLE_COVER   = 1'b1,
  parameter bit OVERCONSTRAINT = 1'b0,
  parameter int unsigned SyncStages = 3,
  parameter type data_t = logic [7:0]
)(
  input  wire   i_clk,
  input  wire   i_rst_n,
  input  logic  i_enable,
  input  data_t i_avg_util,
  input  data_t i_on_th,
  input  data_t i_off_th,
  input  logic  i_throttle,
  input  data_t i_boost_limit,
  input  data_t i_standard_limit,
  input  logic  i_boost_ack,
  input  logic  o_boost_req,
  input  data_t o_util_limit,
  input  logic  o_polarity_err
);
  default clocking @(posedge i_clk); endclocking
  default disable iff (!i_rst_n);
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Sequences
  // =====================================================
  sequence seq_valid_comparator;
    i_enable && !i_throttle;
  endsequence
  sequence seq_on_th_crossed;
    (i_avg_util > i_on_th);
  endsequence
  sequence seq_off_th_crossed;
    (i_avg_util < i_off_th);
  endsequence
  sequence seq_valid_cfg_polarity;
    (i_on_th > i_off_th);
  endsequence
  sequence seq_invalid_cfg_polarity;
    (i_on_th <= i_off_th);
  endsequence
  // =====================================================
  // Properties
  // =====================================================
  property prop_valid_cfg;
    seq_valid_cfg_polarity;
  endproperty
  property prop_valid_data;
    (seq_valid_cfg_polarity and seq_valid_comparator and seq_on_th_crossed) |=> o_boost_req;
  endproperty
  property prop_on_th;
    seq_valid_comparator and seq_on_th_crossed and !o_boost_req |=> o_boost_req;
  endproperty
  property prop_off_th;
    seq_valid_comparator and seq_off_th_crossed and o_boost_req |=> !o_boost_req;
  endproperty
  property prop_boost_limit;
    i_boost_ack ##SyncStages !i_throttle |-> (o_util_limit == i_boost_limit);
  endproperty

  // =====================================================
  // Assumes
  // =====================================================
  if(ENABLE_ASSUME) begin : g_assume
    if(OVERCONSTRAINT) begin : g_over_constraint
      fv_overconstraint_valid_cfg: assume property(prop_valid_cfg);
    end
  end
  // =====================================================
  // Assertions
  // =====================================================
  if(ENABLE_ASSERT) begin : g_assert
      fv_throttle       : assert property (prop_valid_data);
      fv_error          : assert property (seq_invalid_cfg_polarity |-> o_polarity_err);
      fv_boost_limit    : assert property (prop_boost_limit);
      fv_throttle_limit : assert property (i_throttle |-> (o_util_limit == i_standard_limit));
      fv_throttle_req   : assert property (i_throttle |=> !o_boost_req);
      fv_not_boost_ack  : assert property (!i_boost_ack |-> ##SyncStages (o_util_limit == i_standard_limit));
  end
  // =====================================================
  // Covers
  // =====================================================
  if(ENABLE_COVER) begin : g_cover
    fv_cover_error          : cover property (o_polarity_err);
    fv_cover_boost_req      : cover property (o_boost_req);
    fv_cover_on             : cover property (prop_on_th);
    fv_cover_off            : cover property (prop_off_th);
    fv_cover_boost_limit    : cover property (o_util_limit == i_boost_limit);
    fv_cover_standard_limit : cover property (o_util_limit == i_standard_limit);
    fv_cover_throttle       : cover property (i_throttle);
  end

endmodule

`endif // DWM_BOOST_REQUESTER_SVA_SV
