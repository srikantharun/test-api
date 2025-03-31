// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// MMIO bridge wrapper of L1
///
module pve_l1
  import axi_pkg::*;
  import chip_pkg::*;
  import mmio_pkg::*;
  import axe_tcl_sram_pkg::*;
  import pve_pkg::*;
  import pve_cva6v_pkg::*;
  import pve_l1_pkg::*;
  import cva6v_pve_pkg::*;
(
  /// Clock, positive edge triggered
  input  wire                  i_clk,
  /// Asynchronous reset, active low
  input  wire                  i_rst_n,

  input logic                  i_scan_en,

  // MMIO ports
  input  pve_cva6v_mem_logic_t i_rvv_l1_mem_req_valid[PVE_CLUSTER_N_CPU],
  input  pve_cva6v_mem_addr_t  i_rvv_l1_mem_req_addr [PVE_CLUSTER_N_CPU],
  input  pve_cva6v_mem_logic_t i_rvv_l1_mem_req_we   [PVE_CLUSTER_N_CPU],
  input  pve_cva6v_mem_be_t    i_rvv_l1_mem_req_be   [PVE_CLUSTER_N_CPU],
  input  pve_cva6v_mem_data_t  i_rvv_l1_mem_req_wdata[PVE_CLUSTER_N_CPU],
  output pve_cva6v_mem_logic_t o_rvv_l1_mem_req_ready[PVE_CLUSTER_N_CPU],
  output pve_cva6v_mem_logic_t o_rvv_l1_mem_rsp_valid[PVE_CLUSTER_N_CPU],
  output pve_cva6v_mem_data_t  o_rvv_l1_mem_rsp_rdata[PVE_CLUSTER_N_CPU],
  output pve_cva6v_mem_logic_t o_rvv_l1_mem_rsp_err  [PVE_CLUSTER_N_CPU],

  // AXI write address channel
  input  logic                 i_l1_axi_s_awvalid,
  input  pve_ht_axi_m_id_t     i_l1_axi_s_awid,
  input  chip_axi_addr_t       i_l1_axi_s_awaddr,
  input  axi_len_t             i_l1_axi_s_awlen,
  input  axi_size_e            i_l1_axi_s_awsize,
  input  axi_burst_e           i_l1_axi_s_awburst,
  output logic                 o_l1_axi_s_awready,
  // AXI write data channel
  input  logic                 i_l1_axi_s_wvalid,
  input  chip_axi_ht_data_t    i_l1_axi_s_wdata,
  input  chip_axi_ht_wstrb_t   i_l1_axi_s_wstrb,
  input  logic                 i_l1_axi_s_wlast,
  output logic                 o_l1_axi_s_wready,
  // AXI write response channel
  output logic                 o_l1_axi_s_bvalid,
  output pve_ht_axi_m_id_t     o_l1_axi_s_bid,
  output axi_resp_e            o_l1_axi_s_bresp,
  input  logic                 i_l1_axi_s_bready,
  // AXI read address channel
  input  logic                 i_l1_axi_s_arvalid,
  input  pve_ht_axi_m_id_t     i_l1_axi_s_arid,
  input  chip_axi_addr_t       i_l1_axi_s_araddr,
  input  axi_len_t             i_l1_axi_s_arlen,
  input  axi_size_e            i_l1_axi_s_arsize,
  input  axi_burst_e           i_l1_axi_s_arburst,
  output logic                 o_l1_axi_s_arready,
  // AXI read data/response channel
  output logic                 o_l1_axi_s_rvalid,
  output pve_ht_axi_m_id_t     o_l1_axi_s_rid,
  output chip_axi_ht_data_t    o_l1_axi_s_rdata,
  output axi_resp_e            o_l1_axi_s_rresp,
  output logic                 o_l1_axi_s_rlast,
  input  logic                 i_l1_axi_s_rready,

  // Configuration control
  input  pve_l1_base_addr_t    i_l1_base_address,

  // SRAM configuration
  input  impl_inp_t            i_mem_impl,
  output impl_oup_t            o_mem_impl
);

  mmio_dmc_wo_req_t ext_l1_mmio_wr_req;
  mmio_dmc_wo_rsp_t ext_l1_mmio_wr_rsp;
  mmio_dmc_ro_req_t ext_l1_mmio_rd_req;
  mmio_dmc_ro_rsp_t ext_l1_mmio_rd_rsp;

  axi_resp_t l1_axi_s_bresp;
  axi_resp_t l1_axi_s_rresp;

  axi2mmio_bridge #(
    .AXI_S_ID_WIDTH(PVE_HT_M_ID_W),
    .AXI_ADDR_WIDTH(CHIP_AXI_ADDR_W),
    .AXI_WSTRB_WIDTH(CHIP_AXI_HT_WSTRB_W),
    .AXI_DATA_WIDTH(CHIP_AXI_HT_DATA_W),
    .MEM_BASE_ADDRESS_WIDTH(PVE_L1_BASE_ADDR_W)
  ) u_axi2mmio (
    // Clock and reset signals
    .i_clk,
    .i_rst_n,
    // AXI write address channel
    .i_axi_s_awvalid          (i_l1_axi_s_awvalid),
    .i_axi_s_awaddr           (i_l1_axi_s_awaddr),
    .i_axi_s_awid             (i_l1_axi_s_awid),
    .i_axi_s_awlen            (i_l1_axi_s_awlen),
    .i_axi_s_awsize           (axi_size_t'(i_l1_axi_s_awsize)),
    .i_axi_s_awburst          (axi_burst_t'(i_l1_axi_s_awburst)),
    .o_axi_s_awready          (o_l1_axi_s_awready),
    // AXI write data channel
    .i_axi_s_wvalid           (i_l1_axi_s_wvalid),
    .i_axi_s_wlast            (i_l1_axi_s_wlast),
    .i_axi_s_wstrb            (i_l1_axi_s_wstrb),
    .i_axi_s_wdata            (i_l1_axi_s_wdata),
    .o_axi_s_wready           (o_l1_axi_s_wready),
    // AXI write response channel
    .o_axi_s_bvalid           (o_l1_axi_s_bvalid),
    .o_axi_s_bid              (o_l1_axi_s_bid),
    .o_axi_s_bresp            (l1_axi_s_bresp),
    .i_axi_s_bready           (i_l1_axi_s_bready),
    // AXI read address channel
    .i_axi_s_arvalid          (i_l1_axi_s_arvalid),
    .i_axi_s_araddr           (i_l1_axi_s_araddr),
    .i_axi_s_arid             (i_l1_axi_s_arid),
    .i_axi_s_arlen            (i_l1_axi_s_arlen),
    .i_axi_s_arsize           (axi_size_t'(i_l1_axi_s_arsize)),
    .i_axi_s_arburst          (axi_burst_t'(i_l1_axi_s_arburst)),
    .o_axi_s_arready          (o_l1_axi_s_arready),
    // AXI read data/response channel
    .o_axi_s_rvalid           (o_l1_axi_s_rvalid),
    .o_axi_s_rlast            (o_l1_axi_s_rlast),
    .o_axi_s_rid              (o_l1_axi_s_rid),
    .o_axi_s_rdata            (o_l1_axi_s_rdata),
    .o_axi_s_rresp            (l1_axi_s_rresp),
    .i_axi_s_rready           (i_l1_axi_s_rready),
    // MMIO write channel
    .o_mmio_s_wr_req          (ext_l1_mmio_wr_req),
    .i_mmio_s_wr_rsp          (ext_l1_mmio_wr_rsp),
    // MMIO read channel
    .o_mmio_s_rd_req          (ext_l1_mmio_rd_req),
    .i_mmio_s_rd_rsp          (ext_l1_mmio_rd_rsp),

    // Configuration control
    .i_mem_base_address        (i_l1_base_address)
  );

  assign o_l1_axi_s_bresp = axi_resp_e'(l1_axi_s_bresp);
  assign o_l1_axi_s_rresp = axi_resp_e'(l1_axi_s_rresp);

  mmio_rvv_req_t [PVE_CLUSTER_N_CPU*MemPortCount-1:0] rvv_l1_mem_req;
  mmio_rvv_rsp_t [PVE_CLUSTER_N_CPU*MemPortCount-1:0] rvv_l1_mem_rsp;

  for (genvar i = 0; i < PVE_CLUSTER_N_CPU; i++) begin : g_outer
    for (genvar j = 0; j < MemPortCount; j++) begin : g_iner
      mmio_rvv_req_payload_t rvv_l1_mem_req_payload;
      assign rvv_l1_mem_req_payload.addr = i_rvv_l1_mem_req_addr [i][j];
      assign rvv_l1_mem_req_payload.we   = i_rvv_l1_mem_req_we   [i][j];
      assign rvv_l1_mem_req_payload.wbe  = i_rvv_l1_mem_req_be   [i][j];
      assign rvv_l1_mem_req_payload.data = i_rvv_l1_mem_req_wdata[i][j];

      cc_stream_spill_reg #(
        .data_t(mmio_rvv_req_payload_t),
        .Bypass(1'b0)
      ) u_req_spill_reg (
        .i_clk,
        .i_rst_n,
        .i_flush(1'b0),
        .i_data (rvv_l1_mem_req_payload),
        .i_valid(i_rvv_l1_mem_req_valid[i][j]),
        .o_ready(o_rvv_l1_mem_req_ready[i][j]),
        .o_data (rvv_l1_mem_req[i*MemPortCount+j].payload),
        .o_valid(rvv_l1_mem_req[i*MemPortCount+j].valid),
        .i_ready(rvv_l1_mem_rsp[i*MemPortCount+j].ready)
      );

      assign o_rvv_l1_mem_rsp_valid[i][j] = rvv_l1_mem_rsp[i*MemPortCount+j].ack;
      assign o_rvv_l1_mem_rsp_rdata[i][j] = rvv_l1_mem_rsp[i*MemPortCount+j].payload.data;
      assign o_rvv_l1_mem_rsp_err  [i][j] = rvv_l1_mem_rsp[i*MemPortCount+j].payload.error;
    end
  end

  l1 #(
    // Allow Reuse with different Key Parameters
    .L1_NUM_BANKS           (PVE_CLUSTER_N_CPU * MemPortCount),
    .L1_NUM_DMC_WO_REQUESTS (1),
    .L1_NUM_DMC_RO_REQUESTS (1),
    .L1_NUM_RVV_REQUESTS    (PVE_CLUSTER_N_CPU * MemPortCount),
    .L1_DAISY_CHAIN_MAPPING (PVE_L1_DAISY_CHAIN_MAPPING),
    .L1_REQ_PIPE            (1'b0)
  ) u_l1 (
    // Clock and reset signals
    .i_clk,
    .i_rst_n,
    .i_scan_en,

    // =====================================================
    // DMC MMIO
    // =====================================================
    .i_dmc_wo_req  (ext_l1_mmio_wr_req),
    .o_dmc_wo_rsp  (ext_l1_mmio_wr_rsp),
    .i_dmc_ro_req  (ext_l1_mmio_rd_req),
    .o_dmc_ro_rsp  (ext_l1_mmio_rd_rsp),

    // =====================================================
    // RVV MMIO
    // =====================================================
    .i_rvv_req      (rvv_l1_mem_req),
    .o_rvv_rsp      (rvv_l1_mem_rsp),

    .i_mem_impl,
    .o_mem_impl
  );

endmodule
