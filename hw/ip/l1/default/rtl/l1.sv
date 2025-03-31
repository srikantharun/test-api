// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

/// Description: L1 subsystem top level
// Contains L1 memory and the tighly and loosely coupled interconnect fabrics
// The TC interconnnect fabric provides connections between the L1 memory
// and the following masters:  MVM core, DWPU core and AXI core interconnect.
// The LC interconnect fabric provides connections between the
// MVM and DWPU core to the AXI core interconnect.

`ifndef _L1_SV_
`define _L1_SV_

module l1
  import axe_tcl_sram_pkg::*, l1_pkg::*, mmio_pkg::*;
#(
   // Allow Reuse with different Key Parameters
   parameter uint_t L1_NUM_BANKS           = DEFAULT_L1_NUM_BANKS,
   parameter uint_t L1_NUM_DMC_WO_REQUESTS = DEFAULT_L1_NUM_DMC_WO_REQUESTS,
   parameter uint_t L1_NUM_DMC_RO_REQUESTS = DEFAULT_L1_NUM_DMC_RO_REQUESTS,
   parameter uint_t L1_NUM_RVV_REQUESTS    = DEFAULT_L1_NUM_RVV_REQUESTS,
   parameter mem_map_cfg_t L1_DAISY_CHAIN_MAPPING[L1_NR_SUB_BANKS * L1_NUM_BANKS * 1] = DEFAULT_L1_DAISY_CHAIN_MAPPING,
   parameter bit L1_REQ_PIPE               = 1'b1,
   parameter uint_t L1_MAX_OSR             = L1_RESP_LATENCY + (L1_REQ_PIPE ? 1 : 0)
)
(
  // Clock and reset signals
  input wire i_clk,
  input wire i_rst_n,
  input logic i_scan_en,

  // =====================================================
  // DMC MMIO
  // =====================================================
  input  mmio_dmc_wo_req_t [L1_NUM_DMC_WO_REQUESTS-1:0] i_dmc_wo_req,
  output mmio_dmc_wo_rsp_t [L1_NUM_DMC_WO_REQUESTS-1:0] o_dmc_wo_rsp,
  input  mmio_dmc_ro_req_t [L1_NUM_DMC_RO_REQUESTS-1:0] i_dmc_ro_req,
  output mmio_dmc_ro_rsp_t [L1_NUM_DMC_RO_REQUESTS-1:0] o_dmc_ro_rsp,

  // =====================================================
  // RVV MMIO
  // =====================================================
  input  mmio_rvv_req_t [L1_NUM_RVV_REQUESTS-1:0] i_rvv_req,
  output mmio_rvv_rsp_t [L1_NUM_RVV_REQUESTS-1:0] o_rvv_rsp,

  input impl_inp_t i_mem_impl,
  output impl_oup_t o_mem_impl
);

  // Dependent params on primary params in instance
  localparam uint_t L1_NUM_DMC_REQUESTS = L1_NUM_DMC_WO_REQUESTS + L1_NUM_DMC_RO_REQUESTS;

  localparam uint_t L1_MACROS_PER_MINI_BANK = L1_BANK_DATA_DEPTH / L1_MACRO_DATA_DEPTH;

  localparam uint_t TOT_NUM_SOURCES = L1_NUM_DMC_REQUESTS + L1_NUM_RVV_REQUESTS;
  localparam uint_t SRC_SEL_W = $clog2(TOT_NUM_SOURCES);

  // =====================================================
  // Signal declarations
  // =====================================================
  mmio_dmc_ro_req_t [L1_NUM_DMC_RO_REQUESTS-1:0] mmio_dmc_ro_post_osr_req;
  mmio_dmc_ro_rsp_t [L1_NUM_DMC_RO_REQUESTS-1:0] mmio_dmc_ro_post_osr_rsp;
  mmio_dmc_wo_req_t [L1_NUM_DMC_WO_REQUESTS-1:0] mmio_dmc_wo_post_osr_req;
  mmio_dmc_wo_rsp_t [L1_NUM_DMC_WO_REQUESTS-1:0] mmio_dmc_wo_post_osr_rsp;
  mmio_rvv_req_t    [L1_NUM_RVV_REQUESTS-1:0]    mmio_rvv_post_osr_req;
  mmio_rvv_rsp_t    [L1_NUM_RVV_REQUESTS-1:0]    mmio_rvv_post_osr_rsp;

  mmio_dmc_full_req_t [L1_NUM_DMC_REQUESTS-1:0] mmio_dmc_req;
  mmio_dmc_full_rsp_t [L1_NUM_DMC_REQUESTS-1:0] mmio_dmc_rsp;
  mmio_rvv_req_t      [L1_NUM_RVV_REQUESTS-1:0] mmio_rvv_req;
  mmio_rvv_rsp_t      [L1_NUM_RVV_REQUESTS-1:0] mmio_rvv_rsp;

  logic [L1_NUM_DMC_RO_REQUESTS-1:0]                       dmc_ro_src_vld;
  logic [L1_NUM_DMC_WO_REQUESTS-1:0]                       dmc_wo_src_vld;
  logic [L1_NUM_DMC_REQUESTS-1:0]                          dmc_src_vld;
  logic [L1_NUM_DMC_REQUESTS-1:0]                          dmc_src_rdy;
  logic [L1_NUM_DMC_REQUESTS-1:0][MMIO_DMC_ADDR_WIDTH-1:0] dmc_src_addr;
  logic [L1_NUM_RVV_REQUESTS-1:0]                          rvv_src_vld;
  logic [L1_NUM_RVV_REQUESTS-1:0]                          rvv_src_rdy;
  logic [L1_NUM_RVV_REQUESTS-1:0][MMIO_RVV_ADDR_WIDTH-1:0] rvv_src_addr;

  mmio_dmc_slim_rsp_t [L1_NUM_DMC_REQUESTS-1:0] mem_dmc_src_rsp;
  mmio_rvv_slim_rsp_t [L1_NUM_RVV_REQUESTS-1:0] mem_rvv_src_rsp;

  logic [L1_NUM_DMC_WO_REQUESTS-1:0] dmc_wo_idle_n;
  logic [L1_NUM_DMC_RO_REQUESTS-1:0] dmc_ro_idle_n;
  logic [L1_NUM_RVV_REQUESTS-1:0]    rvv_idle_n;
  logic                              l1_mem_idle_n;
  logic                              l1_mem_idle_n_q;
  logic                              l1_mem_clk_en;
  wire                               l1_mem_clk;
  // =====================================================
  // RTL
  // =====================================================

  // Clock-gating section. Get the idle's and drive a clock-gate for L1 mem:
  always_comb l1_mem_idle_n = |{dmc_wo_idle_n, dmc_ro_idle_n, rvv_idle_n};
  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n)
      l1_mem_idle_n_q <= 1'b0;
    else if (l1_mem_idle_n_q ^ l1_mem_idle_n)
      l1_mem_idle_n_q <= l1_mem_idle_n;
  end
  if (L1_REQ_PIPE) begin : g_clk_en_pipe
    always_comb l1_mem_clk_en = l1_mem_idle_n_q;
  end else begin : g_clk_en_no_pipe
    // TODO Clock needs to be ungated one cycle earlier if there is no request pipe, but clock
    // gate should have a flop before it. Not gating for now, to be revisited.
    always_comb l1_mem_clk_en = 1'b1;
  end
  axe_tcl_clk_gating u_l1_gate (
    .i_clk,
    .i_en(l1_mem_clk_en),
    .i_test_en(i_scan_en),
    .o_clk(l1_mem_clk)
  );

  // Assign input to internal request signal, this is a full spec'ed MMIO request
  // DMC:
  always_comb begin
    // read only:
    for (uint_t dmc_ro_idx=0; dmc_ro_idx<L1_NUM_DMC_RO_REQUESTS; dmc_ro_idx++) begin
      // req, needs to be filled up with tight values
      mmio_dmc_req[dmc_ro_idx].payload.addr = mmio_dmc_ro_post_osr_req[dmc_ro_idx].payload.addr;
      mmio_dmc_req[dmc_ro_idx].payload.we   = 1'b0;
      mmio_dmc_req[dmc_ro_idx].payload.wbe  = '0;
      mmio_dmc_req[dmc_ro_idx].payload.data = '0;
      mmio_dmc_req[dmc_ro_idx].valid        = mmio_dmc_ro_post_osr_req[dmc_ro_idx].valid;
      mmio_dmc_req[dmc_ro_idx].rsp_ready    = 1'b1; // Fix to 1, as OSR tracker can absorb all outstanding requests

      dmc_ro_src_vld[dmc_ro_idx] = mmio_dmc_ro_post_osr_req[dmc_ro_idx].valid;
      dmc_src_addr[dmc_ro_idx] = mmio_dmc_ro_post_osr_req[dmc_ro_idx].payload.addr;
      // rsp, take ack and payload from memory, ready comes from arbiter:
      mmio_dmc_ro_post_osr_rsp[dmc_ro_idx].ready         = dmc_src_rdy[dmc_ro_idx];
      mmio_dmc_ro_post_osr_rsp[dmc_ro_idx].ack           = mem_dmc_src_rsp[dmc_ro_idx].ack;
      mmio_dmc_ro_post_osr_rsp[dmc_ro_idx].payload.data  = mem_dmc_src_rsp[dmc_ro_idx].payload.data;
      mmio_dmc_ro_post_osr_rsp[dmc_ro_idx].payload.error = 1'b0;
    end
    // write only:
    for (uint_t dmc_wo_idx=0; dmc_wo_idx<L1_NUM_DMC_WO_REQUESTS; dmc_wo_idx++) begin
      // req
      mmio_dmc_req[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].payload.addr = mmio_dmc_wo_post_osr_req[dmc_wo_idx].payload.addr;
      mmio_dmc_req[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].payload.we   = 1'b1;
      mmio_dmc_req[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].payload.wbe  = mmio_dmc_wo_post_osr_req[dmc_wo_idx].payload.wbe;
      mmio_dmc_req[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].payload.data = mmio_dmc_wo_post_osr_req[dmc_wo_idx].payload.data;
      mmio_dmc_req[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].valid        = mmio_dmc_wo_post_osr_req[dmc_wo_idx].valid;
      mmio_dmc_req[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].rsp_ready    = 1'b1; // Fix to 1, as OSR tracker can absorb all outstanding requests

      dmc_wo_src_vld[dmc_wo_idx] = mmio_dmc_wo_post_osr_req[dmc_wo_idx].valid;
      dmc_src_addr[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx] = mmio_dmc_wo_post_osr_req[dmc_wo_idx].payload.addr;
      // rsp, take ack and payload from memory, ready comes from arbiter:
      mmio_dmc_wo_post_osr_rsp[dmc_wo_idx].ready         = dmc_src_rdy[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx];
      mmio_dmc_wo_post_osr_rsp[dmc_wo_idx].ack           = mem_dmc_src_rsp[L1_NUM_DMC_RO_REQUESTS + dmc_wo_idx].ack;
      mmio_dmc_wo_post_osr_rsp[dmc_wo_idx].payload.error = 1'b0;
    end
  end
  always_comb dmc_src_vld = {dmc_wo_src_vld, dmc_ro_src_vld};

  // RVV:
  always_comb begin
    for (uint_t rvv_idx=0; rvv_idx<L1_NUM_RVV_REQUESTS; rvv_idx++) begin
      //req can be directly assigned as both are the same
      mmio_rvv_req[rvv_idx] = mmio_rvv_post_osr_req[rvv_idx];

      rvv_src_vld [rvv_idx] = mmio_rvv_post_osr_req[rvv_idx].valid;
      rvv_src_addr[rvv_idx] = mmio_rvv_post_osr_req[rvv_idx].payload.addr;
      // rsp, take ack and payload from memory, ready comes from arbiter:
      mmio_rvv_post_osr_rsp[rvv_idx].ready         = rvv_src_rdy[rvv_idx];
      mmio_rvv_post_osr_rsp[rvv_idx].ack           = mem_rvv_src_rsp[rvv_idx].ack;
      mmio_rvv_post_osr_rsp[rvv_idx].payload.data  = mem_rvv_src_rsp[rvv_idx].payload.data;
      mmio_rvv_post_osr_rsp[rvv_idx].payload.error = 1'b0;
    end
  end

  // Outstanding read check, only pass through MMIO request when it can be absorbed
  // only required for DMC path, as RVV won't backpressure
  for (genvar idx=0; unsigned'(idx)<L1_NUM_DMC_RO_REQUESTS; idx++) begin: g_ro_osr_track
    l1_osr_track #(
      .mmio_req_t(mmio_dmc_ro_req_t),
      .mmio_rsp_t(mmio_dmc_ro_rsp_t),
      .MAX_OSR(L1_MAX_OSR)
    ) u_dmc_ro_osr_track (
      // Clock and reset signal
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      .o_idle_n(dmc_ro_idle_n[idx]),

      .i_mmio_req(i_dmc_ro_req[idx]),
      .o_mmio_rsp(o_dmc_ro_rsp[idx]),

      .o_mmio_req(mmio_dmc_ro_post_osr_req[idx]),
      .i_mmio_rsp(mmio_dmc_ro_post_osr_rsp[idx])
    );
    logic rsp_rdy_nc;
    always_comb rsp_rdy_nc = mmio_dmc_ro_post_osr_req[idx].rsp_ready; // ASO-UNUSED_VARIABLE: response ready not used as the memory can't backpressure
  end
  for (genvar idx=0; unsigned'(idx)<L1_NUM_DMC_WO_REQUESTS; idx++) begin: g_wo_osr_track
    l1_osr_track #(
      .mmio_req_t(mmio_dmc_wo_req_t),
      .mmio_rsp_t(mmio_dmc_wo_rsp_t),
      .MAX_OSR(L1_MAX_OSR)
    ) u_dmc_wo_osr_track (
      // Clock and reset signal
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      .o_idle_n(dmc_wo_idle_n[idx]),

      .i_mmio_req(i_dmc_wo_req[idx]),
      .o_mmio_rsp(o_dmc_wo_rsp[idx]),

      .o_mmio_req(mmio_dmc_wo_post_osr_req[idx]),
      .i_mmio_rsp(mmio_dmc_wo_post_osr_rsp[idx])
    );
    logic rsp_rdy_nc;
    always_comb rsp_rdy_nc = mmio_dmc_wo_post_osr_req[idx].rsp_ready; // ASO-UNUSED_VARIABLE: response ready not used as the memory can't backpressure
  end
  for (genvar idx=0; unsigned'(idx)<L1_NUM_RVV_REQUESTS; idx++) begin: g_rvv_osr_track
    l1_osr_track #(
      .mmio_req_t(mmio_rvv_req_t),
      .mmio_rsp_t(mmio_rvv_rsp_t),
      .MAX_OSR(L1_MAX_OSR),
      .MNGR_RSP_ALWAYS_READY(1)
    ) u_rvv_osr_track (
      // Clock and reset signal
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      .o_idle_n(rvv_idle_n[idx]),

      .i_mmio_req(i_rvv_req[idx]),
      .o_mmio_rsp(o_rvv_rsp[idx]),

      .o_mmio_req(mmio_rvv_post_osr_req[idx]),
      .i_mmio_rsp(mmio_rvv_post_osr_rsp[idx])
    );
  end

  logic [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0][SRC_SEL_W-1:0]  mem_src_sel;
  logic [L1_NR_SUB_BANKS-1:0][L1_NUM_BANKS-1:0]                 mem_src_vld;
  // L1 fabric
  l1_tc_fabric #(
    .NUM_DMC_SOURCES      (L1_NUM_DMC_REQUESTS),
    .NUM_RVV_SOURCES      (L1_NUM_RVV_REQUESTS),
    .NUM_BANKS            (L1_NUM_BANKS),
    .NUM_SUB_BANKS        (L1_NR_SUB_BANKS),
    .MEM_ADDR_WIDTH       (MMIO_DMC_ADDR_WIDTH),
    .BANK_DATA_WIDTH      (L1_BANK_DATA_WIDTH)
  ) u_dmc_fabric (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_dmc_vld (dmc_src_vld),
    .o_dmc_rdy (dmc_src_rdy),
    .i_dmc_addr(dmc_src_addr),
    .i_rvv_vld (rvv_src_vld),
    .o_rvv_rdy (rvv_src_rdy),
    .i_rvv_addr(rvv_src_addr),

    .o_src_sel(mem_src_sel),
    .o_src_vld(mem_src_vld)
  );

  l1_mem #(
    .L1_NUM_BANKS(L1_NUM_BANKS),
    .L1_MACROS_PER_MINI_BANK(L1_MACROS_PER_MINI_BANK),
    .L1_REQ_PIPE(L1_REQ_PIPE),

    .NUM_DMC_SOURCES(L1_NUM_DMC_REQUESTS),
    .NUM_RVV_SOURCES(L1_NUM_RVV_REQUESTS),
    .L1_DAISY_CHAIN_MAPPING(L1_DAISY_CHAIN_MAPPING)
  ) u_l1_mem (
    .i_clk      (i_clk),
    .i_gated_clk(l1_mem_clk),
    .i_rst_n    (i_rst_n),

    .i_src_sel  (mem_src_sel),
    .i_src_vld  (mem_src_vld),

    .i_dmc_src_req(mmio_dmc_req),
    .i_rvv_src_req(mmio_rvv_req),

    .o_dmc_src_rsp(mem_dmc_src_rsp),
    .o_rvv_src_rsp(mem_rvv_src_rsp),

    .i_mem_impl(i_mem_impl),
    .o_mem_impl(o_mem_impl)
  );

endmodule


`endif  // L1_SV
