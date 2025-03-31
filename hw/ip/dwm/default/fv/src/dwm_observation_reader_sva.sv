// (C) Copyright 2025 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// SVA of observation reader
///

`ifndef DWM_OBSERVATION_READER_SVA_SV
`define DWM_OBSERVATION_READER_SVA_SV

module dwm_observation_reader_sva #(
  parameter bit ENABLE_ASSERT  = 1'b1,
  parameter bit ENABLE_ASSUME  = 1'b1,
  parameter bit ENABLE_COVER   = 1'b1,
  parameter bit OVERCONSTRAINT = 1'b0,
  parameter int unsigned N_OBS = 2,
  parameter type data_t        = logic [7:0]
)(
  input  wire               i_clk,
  input  wire               i_rst_n,
  input  logic              i_axis_valid,
  input  data_t             i_axis_data,
  input  data_t [N_OBS-1:0] i_cfg_on_th,
  input  data_t [N_OBS-1:0] i_cfg_off_th,
  input  logic  [N_OBS-1:0] i_cfg_polarity,
  input  logic  [N_OBS-1:0] i_cfg_enable,
  input  logic  [N_OBS-1:0] i_cfg_sw_overwrite,
  input  logic              i_cfg_clean_min,
  input  logic              i_cfg_clean_max,
  input  logic  [N_OBS-1:0] o_throttle,
  input  logic  [N_OBS-1:0] o_error,
  input  data_t             o_cfg_min_value,
  input  data_t             o_cfg_max_value
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
  sequence seq_valid_observer(int unsigned index);
    i_axis_valid && i_cfg_enable[index];
  endsequence
  sequence seq_on_th_crossed(int unsigned index);
    (i_cfg_polarity[index] && (i_axis_data < i_cfg_on_th[index])) || (!i_cfg_polarity[index] && (i_axis_data > i_cfg_on_th[index]));
  endsequence
  sequence seq_off_th_crossed(int unsigned index);
    (i_cfg_polarity[index] && (i_axis_data > i_cfg_off_th[index])) || (!i_cfg_polarity[index] && (i_axis_data < i_cfg_off_th[index]));
  endsequence
  sequence seq_valid_cfg_polarity(int unsigned index);
    (i_cfg_polarity[index] && (i_cfg_on_th[index] < i_cfg_off_th[index])) || (!i_cfg_polarity[index] && (i_cfg_on_th[index] > i_cfg_off_th[index]));
  endsequence
  sequence seq_negative_polarity(int unsigned index);
    (i_cfg_polarity[index] && (i_cfg_on_th[index] < i_cfg_off_th[index]));
  endsequence
  sequence seq_positive_polarity(int unsigned index);
    (!i_cfg_polarity[index] && (i_cfg_on_th[index] > i_cfg_off_th[index]));
  endsequence
  sequence seq_invalid_cfg_polarity(int unsigned index);
    (i_cfg_polarity[index] && (i_cfg_on_th[index] >= i_cfg_off_th[index])) || (!i_cfg_polarity[index] && (i_cfg_on_th[index] <= i_cfg_off_th[index]));
  endsequence
  // =====================================================
  // Properties
  // =====================================================
  property prop_valid_cfg(int unsigned index);
    seq_valid_cfg_polarity(index);
  endproperty
  property prop_valid_data(int unsigned index);
    (seq_valid_cfg_polarity(index) and seq_valid_observer(index) and seq_on_th_crossed(index)) |=> o_throttle[index];
  endproperty
  property prop_force_sw_throttle(int unsigned index);
    i_cfg_sw_overwrite[index] |-> o_throttle[index];
  endproperty
  property prop_on_th_negative_polarity(int unsigned index);
    seq_valid_observer(index) and seq_negative_polarity(index) and seq_on_th_crossed(index) and !o_throttle[index] |=> o_throttle[index];
  endproperty
  property prop_off_th_negative_polarity(int unsigned index);
    seq_valid_observer(index) and seq_negative_polarity(index) and seq_off_th_crossed(index) and o_throttle[index] |=> !o_throttle[index];
  endproperty
  property prop_on_th_positive_polarity(int unsigned index);
    seq_valid_observer(index) and seq_positive_polarity(index) and seq_on_th_crossed(index) and !o_throttle[index] |=> o_throttle[index];
  endproperty
  property prop_off_th_positive_polarity(int unsigned index);
    seq_valid_observer(index) and seq_positive_polarity(index) and seq_off_th_crossed(index) and o_throttle[index] |=> !o_throttle[index];
  endproperty

  // =====================================================
  // Assumes
  // =====================================================
  if(ENABLE_ASSUME) begin : g_assume
    for(genvar index = 0; index < N_OBS; index++) begin : g_assume_observer
    if(OVERCONSTRAINT) begin : g_over_constraint
      fv_overconstraint_valid_cfg: assume property(prop_valid_cfg(index));
    end
  end
  end
  // =====================================================
  // Assertions
  // =====================================================
  if(ENABLE_ASSERT) begin : g_assert
    for(genvar index = 0; index < N_OBS; index++) begin : g_assert_observer
      fv_sensor_throttle: assert property (prop_valid_data(index));
      fv_sw_throttle    : assert property (prop_force_sw_throttle(index));
      fv_error          : assert property (seq_invalid_cfg_polarity(index) |-> o_error[index]);
      fv_min_recorded   : assert property ((i_axis_valid && (i_axis_data < o_cfg_min_value) && !i_cfg_clean_max) |=> (o_cfg_min_value == $past(i_axis_data)));
      fv_max_recorded   : assert property ((i_axis_valid && (i_axis_data > o_cfg_max_value) && !i_cfg_clean_min) |=> (o_cfg_max_value == $past(i_axis_data)));
      fv_clean_min      : assert property (i_cfg_clean_min |=> ((o_cfg_min_value == '1) or (o_cfg_min_value == $past(i_axis_data))));
      fv_clean_max      : assert property (i_cfg_clean_max |=> ((o_cfg_max_value == '0) or (o_cfg_max_value == $past(i_axis_data))));
      fv_disable        : assert property (!i_cfg_enable[index] ##1 !i_cfg_sw_overwrite[index] |-> !o_throttle[index]);
    end
  end
  // =====================================================
  // Covers
  // =====================================================
  if(ENABLE_COVER) begin : g_cover
    for(genvar index = 0; index < N_OBS; index++) begin : g_cover_observer
      fv_cover_error       : cover property (o_error[index]);
      fv_cover_throttle    : cover property (o_throttle[index]);
      fv_cover_neg_pol_on  : cover property (prop_on_th_negative_polarity(index));
      fv_cover_neg_pol_off : cover property (prop_off_th_negative_polarity(index));
    end
  end

endmodule

`endif // DWM_OBSERVATION_READER_SVA_SV
