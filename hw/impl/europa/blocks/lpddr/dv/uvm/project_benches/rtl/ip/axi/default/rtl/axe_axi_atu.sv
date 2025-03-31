// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Original Authors: Andreas Kurth  <akurth@iis.ee.ethz.ch>
//                   Noah Huetter   <noah.huetter@axelera.ai>

/// AXI4+ATOP Address Translation Unit (ATU)
module axe_axi_atu #(
  /// The ID width of the Transaction
  parameter int unsigned  AxiIdWidth         = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Address width of main AXI4+ATOP subordinate port
  parameter int unsigned AxiSubPortAddrWidth = axe_axi_default_types_pkg::WIDTH_ADDR_64,
  /// Address width of main AXI4+ATOP manager port
  parameter int unsigned AxiManPortAddrWidth = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Maximum number of in-flight transactions on main AXI4+ATOP subordinate port
  parameter int unsigned AxiSubPortMaxTxns = 8,
  /// Support ATOP transactions as per AXI5 spec.
  parameter int unsigned SupportAtops = 1'b1,
  /// Number of bits in the page offset field of an address. These bist are not considered in the match
  /// and are added to the translated address. May not be smaller than 12 (AMBA)
  parameter int unsigned L1PageOffsetSize = axe_axi_default_types_pkg::AtuPageOffsetSize,
  /// Number of entries in L1 ATU
  parameter int unsigned L1NumEntries = axe_axi_default_types_pkg::AtuNumEntries,
  /// Pipeline AW and AR channel after L1 ATU
  parameter bit L1CutAx = 1'b1,

  parameter type axi_s_aw_t   = axe_axi_default_types_pkg::axi_aw_4_64_4_t,
  parameter type axi_m_aw_t   = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type axi_w_t      = axe_axi_default_types_pkg::axi_w_512_64_4_t,
  parameter type axi_b_t      = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type axi_s_ar_t   = axe_axi_default_types_pkg::axi_ar_4_64_4_t,
  parameter type axi_m_ar_t   = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type axi_r_t      = axe_axi_default_types_pkg::axi_r_4_64_4_t,
  /// Type of page table entry
  parameter type entry_t = axe_axi_default_types_pkg::atu_entry_t
)(
  /// Rising-edge clock of all ports
  input  wire       i_clk,
  /// Asynchronous reset, active low
  input  wire       i_rst_n,

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_s_aw_t i_axi_s_aw,
  input  logic      i_axi_s_aw_valid,
  output logic      o_axi_s_aw_ready,
  input  axi_w_t    i_axi_s_w,
  input  logic      i_axi_s_w_valid,
  output logic      o_axi_s_w_ready,
  output axi_b_t    o_axi_s_b,
  output logic      o_axi_s_b_valid,
  input  logic      i_axi_s_b_ready,
  input  axi_s_ar_t i_axi_s_ar,
  input  logic      i_axi_s_ar_valid,
  output logic      o_axi_s_ar_ready,
  output axi_r_t    o_axi_s_r,
  output logic      o_axi_s_r_valid,
  input  logic      i_axi_s_r_ready,

  //////////////////
  // Manager port //
  //////////////////
  output axi_m_aw_t o_axi_m_aw,
  output logic      o_axi_m_aw_valid,
  input  logic      i_axi_m_aw_ready,
  output axi_w_t    o_axi_m_w,
  output logic      o_axi_m_w_valid,
  input  logic      i_axi_m_w_ready,
  input  axi_b_t    i_axi_m_b,
  input  logic      i_axi_m_b_valid,
  output logic      o_axi_m_b_ready,
  output axi_m_ar_t o_axi_m_ar,
  output logic      o_axi_m_ar_valid,
  input  logic      i_axi_m_ar_ready,
  input  axi_r_t    i_axi_m_r,
  input  logic      i_axi_m_r_valid,
  output logic      o_axi_m_r_ready,

  /// Configured translation entries
  input  entry_t    i_entries[L1NumEntries],
  /// Whether ATU is bypassed (no translation)
  input  logic      i_bypass
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////

  typedef logic [AxiManPortAddrWidth-1:0] man_addr_t;

  /// Index where to route on hit or miss.
  typedef enum logic {
    ErrorSubordinate = 1'b0,
    ManagerPort      = 1'b1
  } atu_unit_index_e;

  /// Translation lookup result.
  typedef struct packed {
    logic      hit;
    man_addr_t addr;
  } atu_result_t;

  // Fork input requests into L1 ATU.
  logic
      aw_valid,
      ar_valid,
      aw_ready,
      ar_ready,
      l1_atu_wr_req_valid,
      l1_atu_rd_req_valid,
      l1_atu_wr_req_ready,
      l1_atu_rd_req_ready;
  cc_stream_fork #(
    .NumStreams(2)
  ) u_aw_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(2'b11),
    .i_valid (i_axi_s_aw_valid),
    .o_ready (o_axi_s_aw_ready),
    .o_valid ({l1_atu_wr_req_valid, aw_valid}),
    .i_ready ({l1_atu_wr_req_ready, aw_ready})
  );
  cc_stream_fork #(
    .NumStreams(2)
  ) u_ar_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(2'b11),
    .i_valid(i_axi_s_ar_valid),
    .o_ready(o_axi_s_ar_ready),
    .o_valid({l1_atu_rd_req_valid, ar_valid}),
    .i_ready({l1_atu_rd_req_ready, ar_ready})
  );

  // L1 ATU
  atu_result_t l1_atu_wr_res, l1_atu_rd_res;
  logic l1_atu_wr_res_valid, l1_atu_rd_res_valid, l1_atu_wr_res_ready, l1_atu_rd_res_ready;
  axe_axi_atu_l1 #(
    .InpAddrWidth  (AxiSubPortAddrWidth),
    .OupAddrWidth  (AxiManPortAddrWidth),
    .NumEntries    (L1NumEntries),
    .PageOffsetSize(L1PageOffsetSize),
    .result_t      (atu_result_t),
    .entry_t       (entry_t)
  ) u_l1_atu (
    .i_clk,
    .i_rst_n,
    .i_wr_req_addr (i_axi_s_aw.addr),
    .i_wr_req_valid(l1_atu_wr_req_valid),
    .o_wr_req_ready(l1_atu_wr_req_ready),
    .o_wr_res      (l1_atu_wr_res),
    .o_wr_res_valid(l1_atu_wr_res_valid),
    .i_wr_res_ready(l1_atu_wr_res_ready),
    .i_rd_req_addr (i_axi_s_ar.addr),
    .i_rd_req_valid(l1_atu_rd_req_valid),
    .o_rd_req_ready(l1_atu_rd_req_ready),
    .o_rd_res      (l1_atu_rd_res),
    .o_rd_res_valid(l1_atu_rd_res_valid),
    .i_rd_res_ready(l1_atu_rd_res_ready),
    .i_entries,
    .i_bypass
  );

  // Join L1 ATU responses with Ax requests into demultiplexer.
  axi_s_aw_t axi_demux_inp_aw;
  logic      axi_demux_inp_aw_valid;
  logic      axi_demux_inp_aw_ready;
  axi_w_t    axi_demux_inp_w;
  logic      axi_demux_inp_w_valid;
  logic      axi_demux_inp_w_ready;
  axi_b_t    axi_demux_inp_b;
  logic      axi_demux_inp_b_valid;
  logic      axi_demux_inp_b_ready;
  axi_s_ar_t axi_demux_inp_ar;
  logic      axi_demux_inp_ar_valid;
  logic      axi_demux_inp_ar_ready;
  axi_r_t    axi_demux_inp_r;
  logic      axi_demux_inp_r_valid;
  logic      axi_demux_inp_r_ready;

  always_comb axi_demux_inp_aw = i_axi_s_aw;
  cc_stream_join #(
    .NumStreams(2)
  ) u_aw_join (
    .i_select(2'b11),
    .i_valid ({l1_atu_wr_res_valid, aw_valid}),
    .o_ready ({l1_atu_wr_res_ready, aw_ready}),
    .o_valid (axi_demux_inp_aw_valid),
    .i_ready (axi_demux_inp_aw_ready)
  );

  always_comb axi_demux_inp_ar = i_axi_s_ar;
  cc_stream_join #(
    .NumStreams(2)
  ) u_ar_join (
    .i_select(2'b11),
    .i_valid ({l1_atu_rd_res_valid, ar_valid}),
    .o_ready ({l1_atu_rd_res_ready, ar_ready}),
    .o_valid (axi_demux_inp_ar_valid),
    .i_ready (axi_demux_inp_ar_ready)
  );

  // Connect W, B, and R channels directly between demultiplexer and subordinate port.
  assign axi_demux_inp_w       = i_axi_s_w;
  assign axi_demux_inp_w_valid = i_axi_s_w_valid;
  assign o_axi_s_w_ready       = axi_demux_inp_w_ready;

  assign o_axi_s_b             = axi_demux_inp_b;
  assign o_axi_s_b_valid       = axi_demux_inp_b_valid;
  assign axi_demux_inp_b_ready = i_axi_s_b_ready;

  assign o_axi_s_r             = axi_demux_inp_r;
  assign o_axi_s_r_valid       = axi_demux_inp_r_valid;
  assign axi_demux_inp_r_ready = i_axi_s_r_ready;

  // Demultiplex between address modifier for ATU hits and error subordinate for ATU misses.
  axi_s_aw_t axi_demux_oup_aw[2];
  logic      axi_demux_oup_aw_valid[2];
  logic      axi_demux_oup_aw_ready[2];
  axi_w_t    axi_demux_oup_w[2];
  logic      axi_demux_oup_w_valid[2];
  logic      axi_demux_oup_w_ready[2];
  axi_b_t    axi_demux_oup_b[2];
  logic      axi_demux_oup_b_valid[2];
  logic      axi_demux_oup_b_ready[2];
  axi_s_ar_t axi_demux_oup_ar[2];
  logic      axi_demux_oup_ar_valid[2];
  logic      axi_demux_oup_ar_ready[2];
  axi_r_t    axi_demux_oup_r[2];
  logic      axi_demux_oup_r_valid[2];
  logic      axi_demux_oup_r_ready[2];

  axe_axi_demux #(
    .NumPorts    (2),
    .AxiIdWidth  (AxiIdWidth),
    .MaxTxn      (AxiSubPortMaxTxns),
    .AxiLookBits (AxiIdWidth),
    .SupportAtops(SupportAtops),
    .UniqueIds   (1'b0),
    .CutAw       (L1CutAx),
    .CutW        (1'b0),
    .CutB        (1'b0),
    .CutAr       (L1CutAx),
    .CutR        (1'b0),
    .axi_aw_t    (axi_s_aw_t),
    .axi_w_t     (axi_w_t),
    .axi_b_t     (axi_b_t),
    .axi_ar_t    (axi_s_ar_t),
    .axi_r_t     (axi_r_t)
  ) u_sub_demux (
    .i_clk,
    .i_rst_n,

    .i_axi_s_aw       (axi_demux_inp_aw),
    .i_axi_s_aw_select(l1_atu_wr_res.hit),
    .i_axi_s_aw_valid (axi_demux_inp_aw_valid),
    .o_axi_s_aw_ready (axi_demux_inp_aw_ready),
    .i_axi_s_w        (axi_demux_inp_w),
    .i_axi_s_w_valid  (axi_demux_inp_w_valid),
    .o_axi_s_w_ready  (axi_demux_inp_w_ready),
    .o_axi_s_b        (axi_demux_inp_b),
    .o_axi_s_b_valid  (axi_demux_inp_b_valid),
    .i_axi_s_b_ready  (axi_demux_inp_b_ready),
    .i_axi_s_ar       (axi_demux_inp_ar),
    .i_axi_s_ar_select(l1_atu_rd_res.hit),
    .i_axi_s_ar_valid (axi_demux_inp_ar_valid),
    .o_axi_s_ar_ready (axi_demux_inp_ar_ready),
    .o_axi_s_r        (axi_demux_inp_r),
    .o_axi_s_r_valid  (axi_demux_inp_r_valid),
    .i_axi_s_r_ready  (axi_demux_inp_r_ready),

    .o_axi_m_aw       (axi_demux_oup_aw),
    .o_axi_m_aw_valid (axi_demux_oup_aw_valid),
    .i_axi_m_aw_ready (axi_demux_oup_aw_ready),
    .o_axi_m_w        (axi_demux_oup_w),
    .o_axi_m_w_valid  (axi_demux_oup_w_valid),
    .i_axi_m_w_ready  (axi_demux_oup_w_ready),
    .i_axi_m_b        (axi_demux_oup_b),
    .i_axi_m_b_valid  (axi_demux_oup_b_valid),
    .o_axi_m_b_ready  (axi_demux_oup_b_ready),
    .o_axi_m_ar       (axi_demux_oup_ar),
    .o_axi_m_ar_valid (axi_demux_oup_ar_valid),
    .i_axi_m_ar_ready (axi_demux_oup_ar_ready),
    .i_axi_m_r        (axi_demux_oup_r),
    .i_axi_m_r_valid  (axi_demux_oup_r_valid),
    .o_axi_m_r_ready  (axi_demux_oup_r_ready)
  );

  // Pipeline translated address together with AW and AR.
  man_addr_t l1_atu_wr_res_addr_buf, l1_atu_rd_res_addr_buf;
  cc_stream_spill_reg #(
    .data_t(man_addr_t),
    .Bypass(~L1CutAx)
  ) u_spill_reg_wr_addr (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (l1_atu_wr_res.addr),
    .i_valid(axi_demux_inp_aw_valid && l1_atu_wr_res.hit && axi_demux_inp_aw_ready),
    .o_ready(/* unused */),
    .o_data (l1_atu_wr_res_addr_buf),
    .o_valid(/* unused */),
    .i_ready(axi_demux_oup_aw_valid[ManagerPort] && axi_demux_oup_aw_ready[ManagerPort])
  );
  cc_stream_spill_reg #(
    .data_t(man_addr_t),
    .Bypass(~L1CutAx)
  ) u_spill_reg_rd_addr (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (l1_atu_rd_res.addr),
    .i_valid(axi_demux_inp_ar_valid && l1_atu_rd_res.hit && axi_demux_inp_ar_ready),
    .o_ready(/* unused */),
    .o_data (l1_atu_rd_res_addr_buf),
    .o_valid(/* unused */),
    .i_ready(axi_demux_oup_ar_valid[ManagerPort] && axi_demux_oup_ar_ready[ManagerPort])
  );

  // Handle ATU hits: Replace address and forward to manager port.
  axe_axi_modify_address #(
    .axi_m_addr_t(man_addr_t),
    .axi_s_aw_t  (axi_s_aw_t),
    .axi_m_aw_t  (axi_m_aw_t),
    .axi_w_t     (axi_w_t),
    .axi_b_t     (axi_b_t),
    .axi_s_ar_t  (axi_s_ar_t),
    .axi_m_ar_t  (axi_m_ar_t),
    .axi_r_t     (axi_r_t)
  ) u_mod_addr (
    .i_axi_s_aw      (axi_demux_oup_aw[ManagerPort]),
    .i_axi_s_aw_addr (l1_atu_wr_res_addr_buf),
    .i_axi_s_aw_valid(axi_demux_oup_aw_valid[ManagerPort]),
    .o_axi_s_aw_ready(axi_demux_oup_aw_ready[ManagerPort]),
    .i_axi_s_w       (axi_demux_oup_w[ManagerPort]),
    .i_axi_s_w_valid (axi_demux_oup_w_valid[ManagerPort]),
    .o_axi_s_w_ready (axi_demux_oup_w_ready[ManagerPort]),
    .o_axi_s_b       (axi_demux_oup_b[ManagerPort]),
    .o_axi_s_b_valid (axi_demux_oup_b_valid[ManagerPort]),
    .i_axi_s_b_ready (axi_demux_oup_b_ready[ManagerPort]),
    .i_axi_s_ar      (axi_demux_oup_ar[ManagerPort]),
    .i_axi_s_ar_addr (l1_atu_rd_res_addr_buf),
    .i_axi_s_ar_valid(axi_demux_oup_ar_valid[ManagerPort]),
    .o_axi_s_ar_ready(axi_demux_oup_ar_ready[ManagerPort]),
    .o_axi_s_r       (axi_demux_oup_r[ManagerPort]),
    .o_axi_s_r_valid (axi_demux_oup_r_valid[ManagerPort]),
    .i_axi_s_r_ready (axi_demux_oup_r_ready[ManagerPort]),
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

  // Handle ATU misses: Absorb burst and respond with subordinate error.
  axe_axi_err_sub #(
    .AxiIdWidth  (AxiIdWidth),
    .Resp        (axi_pkg::RespSlvErr),
    .DataWidth   (32'd32),
    .ReadData    (32'hDEC0FFEE),
    .MaxTxn      (1),
    .SupportAtops(SupportAtops),
    .axi_aw_t    (axi_s_aw_t),
    .axi_w_t     (axi_w_t),
    .axi_b_t     (axi_b_t),
    .axi_ar_t    (axi_s_ar_t),
    .axi_r_t     (axi_r_t)
  ) u_err_sub (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_demux_oup_aw[ErrorSubordinate]),
    .i_axi_s_aw_valid(axi_demux_oup_aw_valid[ErrorSubordinate]),
    .o_axi_s_aw_ready(axi_demux_oup_aw_ready[ErrorSubordinate]),
    .i_axi_s_w       (axi_demux_oup_w[ErrorSubordinate]),
    .i_axi_s_w_valid (axi_demux_oup_w_valid[ErrorSubordinate]),
    .o_axi_s_w_ready (axi_demux_oup_w_ready[ErrorSubordinate]),
    .o_axi_s_b       (axi_demux_oup_b[ErrorSubordinate]),
    .o_axi_s_b_valid (axi_demux_oup_b_valid[ErrorSubordinate]),
    .i_axi_s_b_ready (axi_demux_oup_b_ready[ErrorSubordinate]),
    .i_axi_s_ar      (axi_demux_oup_ar[ErrorSubordinate]),
    .i_axi_s_ar_valid(axi_demux_oup_ar_valid[ErrorSubordinate]),
    .o_axi_s_ar_ready(axi_demux_oup_ar_ready[ErrorSubordinate]),
    .o_axi_s_r       (axi_demux_oup_r[ErrorSubordinate]),
    .o_axi_s_r_valid (axi_demux_oup_r_valid[ErrorSubordinate]),
    .i_axi_s_r_ready (axi_demux_oup_r_ready[ErrorSubordinate])
  );
endmodule
