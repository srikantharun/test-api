// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Merge the different AXI streams onto the manager port.
///
/// The sole purpose of this unit is to merge the two *AXI Manager* functions form the
/// [Instruction Fetch](instruction_fetch/index.md) and the [Copy Unit](copy_unit/index.md).
/// As both will use different `AXI IDs` (configurable via the parameters of the `aic_cd`) we can use a more
/// light-weight implementation than a full `axe_axi_mux`.  Only the channels responsible for read operations need merging.
/// The `AR`'s are meged via a *round-robin* scheme, whereas the `R` response is simply muxed based on the `AXI.R.ID`.
/// The unit also contains an `axe_axi_cut` at the manager port.  Which channels are cut can be configured via the
/// parameters of the `aic_cd` top-level.
///
/// ![AIC_CD_AXI_MERGE: Block Diagram](./figures/aic_cd_axi_merge.drawio.svg)
///
module aic_cd_axi_merge #(
  /// The Axi ID width of the AXI AR channel
  parameter int unsigned AxiIdWidth = aic_cd_defaults_pkg::AXI_M_ID_WIDTH,
  /// The Concrete AXI ID to use
  parameter logic [AxiIdWidth-1:0] AxiIdForCopy = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(1),
  /// Add a spill register on AW
  parameter bit CutAw = 1'b1,
  /// Add a spill register on W
  parameter bit CutW  = 1'b1,
  /// Add a spill register on B
  parameter bit CutB  = 1'b1,
  /// Add a spill register on AR
  parameter bit CutAr = 1'b1,
  /// Add a spill register on R
  parameter bit CutR  = 1'b1,
  /// The AXI AW channel type
  parameter type axi_aw_t = aic_cd_defaults_pkg::axi_m_aw_t,
  /// The AXI W channel type
  parameter type axi_w_t = aic_cd_defaults_pkg::axi_m_w_t,
  /// The AXI B channel type
  parameter type axi_b_t = aic_cd_defaults_pkg::axi_m_b_t,
  /// The AXI AR channel type
  parameter type axi_ar_t = aic_cd_defaults_pkg::axi_m_ar_t,
  /// The AXI R channel type
  parameter type axi_r_t = aic_cd_defaults_pkg::axi_m_r_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ///////////////////////
  // Instruction Fetch //
  ///////////////////////
  input  axi_ar_t i_axi_instruction_ar,
  input  logic    i_axi_instruction_ar_valid,
  output logic    o_axi_instruction_ar_ready,
  output axi_r_t  o_axi_instruction_r,
  output logic    o_axi_instruction_r_valid,
  input  logic    i_axi_instruction_r_ready,

  //////////////////
  // Execute Copy //
  //////////////////
  input  axi_aw_t i_axi_copy_aw,
  input  logic    i_axi_copy_aw_valid,
  output logic    o_axi_copy_aw_ready,
  input  axi_w_t  i_axi_copy_w,
  input  logic    i_axi_copy_w_valid,
  output logic    o_axi_copy_w_ready,
  output axi_b_t  o_axi_copy_b,
  output logic    o_axi_copy_b_valid,
  input  logic    i_axi_copy_b_ready,
  input  axi_ar_t i_axi_copy_ar,
  input  logic    i_axi_copy_ar_valid,
  output logic    o_axi_copy_ar_ready,
  output axi_r_t  o_axi_copy_r,
  output logic    o_axi_copy_r_valid,
  input  logic    i_axi_copy_r_ready,

  //////////////////
  // Manager port //
  //////////////////
  output axi_aw_t o_axi_m_aw,
  output logic    o_axi_m_aw_valid,
  input  logic    i_axi_m_aw_ready,
  output axi_w_t  o_axi_m_w,
  output logic    o_axi_m_w_valid,
  input  logic    i_axi_m_w_ready,
  input  axi_b_t  i_axi_m_b,
  input  logic    i_axi_m_b_valid,
  output logic    o_axi_m_b_ready,
  output axi_ar_t o_axi_m_ar,
  output logic    o_axi_m_ar_valid,
  input  logic    i_axi_m_ar_ready,
  input  axi_r_t  i_axi_m_r,
  input  logic    i_axi_m_r_valid,
  output logic    o_axi_m_r_ready
);

  /////////////////////
  // Multiplex Reads //
  /////////////////////
  axi_ar_t axi_s_ar;
  logic    axi_s_ar_valid;
  logic    axi_s_ar_ready;
  axi_r_t  axi_s_r;
  logic    axi_s_r_valid;
  logic    axi_s_r_ready;

  cc_stream_round_robin_arbiter #(
    .data_t (axi_ar_t),
    .N_INP  (2),
    .ARBITER("rr")
  ) u_axe_ccl_stream_arbiter (
    .i_clk,
    .i_rst_n,
    .inp_data_i ({i_axi_copy_ar,       i_axi_instruction_ar}),
    .inp_valid_i({i_axi_copy_ar_valid, i_axi_instruction_ar_valid}),
    .inp_ready_o({o_axi_copy_ar_ready, o_axi_instruction_ar_ready}),
    .oup_data_o (axi_s_ar),
    .oup_valid_o(axi_s_ar_valid),
    .oup_ready_i(axi_s_ar_ready)
  );

  logic       read_select_copy;
  always_comb read_select_copy = i_axi_m_r.id == AxiIdForCopy;

  always_comb o_axi_instruction_r = axi_s_r;
  always_comb o_axi_copy_r        = axi_s_r;

  cc_stream_demux #(
    .NumStreams (2),
    .DropOnError(1'b0)
  ) u_axe_ccl_stream_demux (
    .i_valid (axi_s_r_valid),
    .o_ready (axi_s_r_ready),
    .i_select(read_select_copy),
    .o_error (/* not used */),
    .o_valid ({o_axi_copy_r_valid, o_axi_instruction_r_valid}),
    .i_ready ({i_axi_copy_r_ready, i_axi_instruction_r_ready})
  );

  ///////////////////////////////////////////////
  // Connect via a Cut, Writes are fed through //
  ///////////////////////////////////////////////
  axe_axi_cut #(
    .CutAw(CutAw),
    .CutW (CutW),
    .CutB (CutB),
    .CutAr(CutAr),
    .CutR (CutR),
    .axi_aw_t(axi_aw_t),
    .axi_w_t (axi_w_t),
    .axi_b_t (axi_b_t),
    .axi_ar_t(axi_ar_t),
    .axi_r_t (axi_r_t)
  ) u_axi_cut (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (i_axi_copy_aw),
    .i_axi_s_aw_valid(i_axi_copy_aw_valid),
    .o_axi_s_aw_ready(o_axi_copy_aw_ready),
    .i_axi_s_w       (i_axi_copy_w),
    .i_axi_s_w_valid (i_axi_copy_w_valid),
    .o_axi_s_w_ready (o_axi_copy_w_ready),
    .o_axi_s_b       (o_axi_copy_b),
    .o_axi_s_b_valid (o_axi_copy_b_valid),
    .i_axi_s_b_ready (i_axi_copy_b_ready),
    .i_axi_s_ar      (axi_s_ar),
    .i_axi_s_ar_valid(axi_s_ar_valid),
    .o_axi_s_ar_ready(axi_s_ar_ready),
    .o_axi_s_r       (axi_s_r),
    .o_axi_s_r_valid (axi_s_r_valid),
    .i_axi_s_r_ready (axi_s_r_ready),
    .o_axi_m_aw,
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    .o_axi_m_w,
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    .i_axi_m_b,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,
    .o_axi_m_ar,
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    .i_axi_m_r,
    .i_axi_m_r_valid,
    .o_axi_m_r_ready
  );
endmodule
