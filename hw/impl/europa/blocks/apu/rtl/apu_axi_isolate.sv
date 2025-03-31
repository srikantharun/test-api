/// Module wrapper around `axe_axi_isolate`
/// - mostly existing to reduce the number of parameters
/// - providing Q-channel low power device interface
module apu_axi_isolate #(
  /// ID width of all AXI4+ATOP ports
  parameter int signed AxiIdWidth = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Data width of all AXI4+ATOP ports
  parameter int signed AxiDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// Maximum number of pending transactions per channel
  parameter int unsigned MaxTxn = 32'd16,
  /// Support atomic operations (ATOPs)
  parameter bit SupportAtops = 1'b1,
  // Channel structs
  parameter type axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t
) (
  /// Rising-edge clock of all ports
  input  wire     i_clk,
  /// Asynchronous reset, active low
  input  wire     i_rst_n,

  /////////////////////////
  // Low Power Interface //
  /////////////////////////
  /// QREQn
  input  logic    i_qreq_n,
  /// QDENY
  output logic    o_qdeny,
  /// QACCEPTn
  output logic    o_qaccept_n,
  /// QACTIVE
  output logic    o_qactive,

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_aw_t i_axi_s_aw,
  input  logic    i_axi_s_aw_valid,
  output logic    o_axi_s_aw_ready,
  input  axi_w_t  i_axi_s_w,
  input  logic    i_axi_s_w_valid,
  output logic    o_axi_s_w_ready,
  output axi_b_t  o_axi_s_b,
  output logic    o_axi_s_b_valid,
  input  logic    i_axi_s_b_ready,
  input  axi_ar_t i_axi_s_ar,
  input  logic    i_axi_s_ar_valid,
  output logic    o_axi_s_ar_ready,
  output axi_r_t  o_axi_s_r,
  output logic    o_axi_s_r_valid,
  input  logic    i_axi_s_r_ready,

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

  // Isolate will never deny a req
  always_comb o_qdeny = '0;

  logic isolated;
  always_comb o_qaccept_n = !isolated;

  axe_axi_isolate #(
    .AxiIdWidth(AxiIdWidth),
    .AxiDataWidth(AxiDataWidth),
    .MaxTxn(MaxTxn),
    .TerminateTxn(1'b0),
    .DemuxCutAw(1'b0),
    .DemuxCutW(1'b0),
    .DemuxCutB(1'b0),
    .DemuxCutAr(1'b0),
    .DemuxCutR(1'b0),
    .DemuxUniqueIds(1'b0),
    .SupportAtops(SupportAtops),
    .axi_aw_t(axi_aw_t),
    .axi_w_t(axi_w_t),
    .axi_b_t(axi_b_t),
    .axi_ar_t(axi_ar_t),
    .axi_r_t(axi_r_t)
  ) u_axi_isolate (
    .i_isolate(!i_qreq_n),
    .o_isolated(isolated),
    .o_outstanding(o_qactive),
    .*
  );

endmodule
