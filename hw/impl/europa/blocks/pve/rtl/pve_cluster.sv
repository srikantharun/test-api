// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Video Pre / Post Processor CPU Cluster
///

module pve_cluster
  import axi_pkg::*;
  import chip_pkg::*;
  import axe_tcl_sram_pkg::*;
  import mmio_pkg::*;
  import pve_pkg::*;
  import pve_cva6v_pkg::*;
  import cva6v_pve_pkg::*;
  import pve_l1_pkg::*;
#(
  parameter int CVA6V_NUM_CUTS = 3,
  parameter int L1_NUM_CUTS    = 3
) (
  input  wire                     i_clk,
  input  wire                     i_rst_n,
  input  logic                    i_clk_en            [PVE_CLUSTER_N_CPU],

  // Config
  input  chip_axi_addr_t          i_boot_addr         [PVE_CLUSTER_N_CPU],
  input  pve_hart_base_t          i_hart_id           [PVE_CLUSTER_N_CPU],
  // Memory regions
  input  pve_cva6v_memreg_addr_t  i_memreg_addr       [PVE_CLUSTER_N_CPU],
  input  pve_cva6v_memreg_size_t  i_memreg_size       [PVE_CLUSTER_N_CPU],
  input  pve_cva6v_memreg_tcdm_t  i_memreg_tcdm       [PVE_CLUSTER_N_CPU],
  // Interrupt inputs
  input  logic                    i_int_shutdown_req,
  input  logic                    i_ipi               [PVE_CLUSTER_N_CPU],
  input  logic                    i_time_irq          [PVE_CLUSTER_N_CPU],
  input  pve_cva6v_platf_irq_t    i_platform_irq      [PVE_CLUSTER_N_CPU],
  // Debug
  input  logic                    i_debug_req         [PVE_CLUSTER_N_CPU],
  input  logic                    i_debug_rst_halt_req[PVE_CLUSTER_N_CPU],
  output logic                    o_debug_stop_time   [PVE_CLUSTER_N_CPU],
  // Hart status
  output logic                    o_hart_is_wfi       [PVE_CLUSTER_N_CPU],
  output logic                    o_hart_unavail      [PVE_CLUSTER_N_CPU],
  output logic                    o_hart_under_reset  [PVE_CLUSTER_N_CPU],

  // Memory side, AXI Manager
  // AW
  output logic                    o_cpu_axi_m_awvalid[PVE_CLUSTER_N_CPU],
  output pve_lt_axi_s_id_t        o_cpu_axi_m_awid   [PVE_CLUSTER_N_CPU],
  output chip_axi_addr_t          o_cpu_axi_m_awaddr [PVE_CLUSTER_N_CPU],
  output axi_len_t                o_cpu_axi_m_awlen  [PVE_CLUSTER_N_CPU],
  output axi_size_e               o_cpu_axi_m_awsize [PVE_CLUSTER_N_CPU],
  output axi_burst_e              o_cpu_axi_m_awburst[PVE_CLUSTER_N_CPU],
  output logic                    o_cpu_axi_m_awlock [PVE_CLUSTER_N_CPU],
  output axi_cache_e              o_cpu_axi_m_awcache[PVE_CLUSTER_N_CPU],
  output axi_prot_t               o_cpu_axi_m_awprot [PVE_CLUSTER_N_CPU],
  output axi_atop_t               o_cpu_axi_m_awatop [PVE_CLUSTER_N_CPU],
  input  logic                    i_cpu_axi_m_awready[PVE_CLUSTER_N_CPU],
  // W
  output logic                    o_cpu_axi_m_wvalid [PVE_CLUSTER_N_CPU],
  output chip_axi_lt_data_t       o_cpu_axi_m_wdata  [PVE_CLUSTER_N_CPU],
  output chip_axi_lt_wstrb_t      o_cpu_axi_m_wstrb  [PVE_CLUSTER_N_CPU],
  output logic                    o_cpu_axi_m_wlast  [PVE_CLUSTER_N_CPU],
  input  logic                    i_cpu_axi_m_wready [PVE_CLUSTER_N_CPU],
  // B
  input  logic                    i_cpu_axi_m_bvalid [PVE_CLUSTER_N_CPU],
  input  pve_lt_axi_s_id_t        i_cpu_axi_m_bid    [PVE_CLUSTER_N_CPU],
  input  axi_resp_e               i_cpu_axi_m_bresp  [PVE_CLUSTER_N_CPU],
  output logic                    o_cpu_axi_m_bready [PVE_CLUSTER_N_CPU],
  // AR
  output logic                    o_cpu_axi_m_arvalid[PVE_CLUSTER_N_CPU],
  output pve_lt_axi_s_id_t        o_cpu_axi_m_arid   [PVE_CLUSTER_N_CPU],
  output chip_axi_addr_t          o_cpu_axi_m_araddr [PVE_CLUSTER_N_CPU],
  output axi_len_t                o_cpu_axi_m_arlen  [PVE_CLUSTER_N_CPU],
  output axi_size_e               o_cpu_axi_m_arsize [PVE_CLUSTER_N_CPU],
  output axi_burst_e              o_cpu_axi_m_arburst[PVE_CLUSTER_N_CPU],
  output logic                    o_cpu_axi_m_arlock [PVE_CLUSTER_N_CPU],
  output axi_cache_e              o_cpu_axi_m_arcache[PVE_CLUSTER_N_CPU],
  output axi_prot_t               o_cpu_axi_m_arprot [PVE_CLUSTER_N_CPU],
  input  logic                    i_cpu_axi_m_arready[PVE_CLUSTER_N_CPU],
  // R
  input  logic                    i_cpu_axi_m_rvalid [PVE_CLUSTER_N_CPU],
  input  pve_lt_axi_s_id_t        i_cpu_axi_m_rid    [PVE_CLUSTER_N_CPU],
  input  chip_axi_lt_data_t       i_cpu_axi_m_rdata  [PVE_CLUSTER_N_CPU],
  input  axi_resp_e               i_cpu_axi_m_rresp  [PVE_CLUSTER_N_CPU],
  input  logic                    i_cpu_axi_m_rlast  [PVE_CLUSTER_N_CPU],
  output logic                    o_cpu_axi_m_rready [PVE_CLUSTER_N_CPU],

  // Raptor performance counter signals
  output perf_cntr_fu_status_t    [PVE_CLUSTER_N_CPU-1:0] o_perf_cntr_fu_status,
  output logic                    [PVE_CLUSTER_N_CPU-1:0] o_perf_cntr_dispatch_queue_full,
  output logic                    [PVE_CLUSTER_N_CPU-1:0] o_perf_cntr_dispatch_queue_empty,
  output logic                    [PVE_CLUSTER_N_CPU-1:0] o_perf_cntr_commit_queue_full,
  output logic                    [PVE_CLUSTER_N_CPU-1:0] o_perf_cntr_commit_queue_empty,
  // CVA6V performance event signals
  output pve_cva6v_event_addr_t   [PVE_CLUSTER_N_CPU-1:0] o_perf_event_addr,
  output pve_cva6v_event_deltas_t [PVE_CLUSTER_N_CPU-1:0] o_perf_event_deltas,

  // AXI write address channel
  input  logic                    i_l1_axi_s_awvalid,
  input  pve_ht_axi_m_id_t        i_l1_axi_s_awid,
  input  chip_axi_addr_t          i_l1_axi_s_awaddr,
  input  axi_len_t                i_l1_axi_s_awlen,
  input  axi_size_e               i_l1_axi_s_awsize,
  input  axi_burst_e              i_l1_axi_s_awburst,
  output logic                    o_l1_axi_s_awready,
  // AXI write data channel
  input  logic                    i_l1_axi_s_wvalid,
  input  chip_axi_ht_data_t       i_l1_axi_s_wdata,
  input  chip_axi_ht_wstrb_t      i_l1_axi_s_wstrb,
  input  logic                    i_l1_axi_s_wlast,
  output logic                    o_l1_axi_s_wready,
  // AXI write response channel
  output logic                    o_l1_axi_s_bvalid,
  output pve_ht_axi_m_id_t        o_l1_axi_s_bid,
  output axi_resp_e               o_l1_axi_s_bresp,
  input  logic                    i_l1_axi_s_bready,
  // AXI read address channel
  input  logic                    i_l1_axi_s_arvalid,
  input  pve_ht_axi_m_id_t        i_l1_axi_s_arid,
  input  chip_axi_addr_t          i_l1_axi_s_araddr,
  input  axi_len_t                i_l1_axi_s_arlen,
  input  axi_size_e               i_l1_axi_s_arsize,
  input  axi_burst_e              i_l1_axi_s_arburst,
  output logic                    o_l1_axi_s_arready,
  // AXI read data/response channel
  output logic                    o_l1_axi_s_rvalid,
  output pve_ht_axi_m_id_t        o_l1_axi_s_rid,
  output chip_axi_ht_data_t       o_l1_axi_s_rdata,
  output axi_resp_e               o_l1_axi_s_rresp,
  output logic                    o_l1_axi_s_rlast,
  input  logic                    i_l1_axi_s_rready,

  // Configuration control
  input  pve_l1_base_addr_t       i_l1_base_address
);
  // AW
  logic               spreg_cpu_o_axi_m_awvalid[PVE_CLUSTER_N_CPU];
  pve_lt_axi_s_id_t   spreg_cpu_o_axi_m_awid   [PVE_CLUSTER_N_CPU];
  chip_axi_addr_t     spreg_cpu_o_axi_m_awaddr [PVE_CLUSTER_N_CPU];
  axi_len_t           spreg_cpu_o_axi_m_awlen  [PVE_CLUSTER_N_CPU];
  axi_size_e          spreg_cpu_o_axi_m_awsize [PVE_CLUSTER_N_CPU];
  axi_burst_e         spreg_cpu_o_axi_m_awburst[PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_o_axi_m_awlock [PVE_CLUSTER_N_CPU];
  axi_cache_e         spreg_cpu_o_axi_m_awcache[PVE_CLUSTER_N_CPU];
  axi_prot_t          spreg_cpu_o_axi_m_awprot [PVE_CLUSTER_N_CPU];
  axi_atop_t          spreg_cpu_o_axi_m_awatop [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_i_axi_m_awready[PVE_CLUSTER_N_CPU];
   // W
  logic               spreg_cpu_o_axi_m_wvalid [PVE_CLUSTER_N_CPU];
  chip_axi_lt_data_t  spreg_cpu_o_axi_m_wdata  [PVE_CLUSTER_N_CPU];
  chip_axi_lt_wstrb_t spreg_cpu_o_axi_m_wstrb  [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_o_axi_m_wlast  [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_i_axi_m_wready [PVE_CLUSTER_N_CPU];
   // B
  logic               spreg_cpu_i_axi_m_bvalid [PVE_CLUSTER_N_CPU];
  pve_lt_axi_s_id_t   spreg_cpu_i_axi_m_bid    [PVE_CLUSTER_N_CPU];
  axi_resp_e          spreg_cpu_i_axi_m_bresp  [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_o_axi_m_bready [PVE_CLUSTER_N_CPU];
  // AR
  logic               spreg_cpu_o_axi_m_arvalid[PVE_CLUSTER_N_CPU];
  pve_lt_axi_s_id_t   spreg_cpu_o_axi_m_arid   [PVE_CLUSTER_N_CPU];
  chip_axi_addr_t     spreg_cpu_o_axi_m_araddr [PVE_CLUSTER_N_CPU];
  axi_len_t           spreg_cpu_o_axi_m_arlen  [PVE_CLUSTER_N_CPU];
  axi_size_e          spreg_cpu_o_axi_m_arsize [PVE_CLUSTER_N_CPU];
  axi_burst_e         spreg_cpu_o_axi_m_arburst[PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_o_axi_m_arlock [PVE_CLUSTER_N_CPU];
  axi_cache_e         spreg_cpu_o_axi_m_arcache[PVE_CLUSTER_N_CPU];
  axi_prot_t          spreg_cpu_o_axi_m_arprot [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_i_axi_m_arready[PVE_CLUSTER_N_CPU];
   // R
  logic               spreg_cpu_i_axi_m_rvalid [PVE_CLUSTER_N_CPU];
  pve_lt_axi_s_id_t   spreg_cpu_i_axi_m_rid    [PVE_CLUSTER_N_CPU];
  chip_axi_lt_data_t  spreg_cpu_i_axi_m_rdata  [PVE_CLUSTER_N_CPU];
  axi_resp_e          spreg_cpu_i_axi_m_rresp  [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_i_axi_m_rlast  [PVE_CLUSTER_N_CPU];
  logic               spreg_cpu_o_axi_m_rready [PVE_CLUSTER_N_CPU];

  pve_cva6v_memreg_addr_1d_t memreg_addr_inp[PVE_CLUSTER_N_CPU];
  pve_cva6v_memreg_size_1d_t memreg_size_inp[PVE_CLUSTER_N_CPU];

  pve_cva6v_mem_logic_t   rvv_cva6v_mem_req_valid[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_addr_1d_t rvv_cva6v_mem_req_addr [PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t   rvv_cva6v_mem_req_we   [PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_be_1d_t   rvv_cva6v_mem_req_be   [PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_data_1d_t rvv_cva6v_mem_req_wdata[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t   rvv_cva6v_mem_req_ready[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t   rvv_cva6v_mem_rsp_valid[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_data_1d_t rvv_cva6v_mem_rsp_rdata[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t   rvv_cva6v_mem_rsp_err  [PVE_CLUSTER_N_CPU];

  pve_l1_mem_logic_t rvv_l1_mem_req_valid;
  pve_l1_mem_addr_t  rvv_l1_mem_req_addr;
  pve_l1_mem_logic_t rvv_l1_mem_req_we;
  pve_l1_mem_be_t    rvv_l1_mem_req_be;
  pve_l1_mem_data_t  rvv_l1_mem_req_wdata;
  pve_l1_mem_logic_t rvv_l1_mem_req_ready;
  pve_l1_mem_logic_t rvv_l1_mem_rsp_valid;
  pve_l1_mem_data_t  rvv_l1_mem_rsp_rdata;
  pve_l1_mem_logic_t rvv_l1_mem_rsp_err;

  perf_cntr_fu_status_1d_t    perf_cntr_fu_status_oup[PVE_CLUSTER_N_CPU];
  pve_cva6v_event_addr_1d_t   perf_event_addr_oup    [PVE_CLUSTER_N_CPU];
  pve_cva6v_event_deltas_1d_t perf_event_deltas_oup  [PVE_CLUSTER_N_CPU];

  // AW
  logic               spreg_l1_i_axi_s_awvalid;
  chip_axi_addr_t     spreg_l1_i_axi_s_awaddr;
  pve_ht_axi_m_id_t   spreg_l1_i_axi_s_awid;
  axi_len_t           spreg_l1_i_axi_s_awlen;
  axi_size_e          spreg_l1_i_axi_s_awsize;
  axi_burst_e         spreg_l1_i_axi_s_awburst;
  logic               spreg_l1_o_axi_s_awready;
  // W
  logic               spreg_l1_i_axi_s_wvalid;
  logic               spreg_l1_i_axi_s_wlast;
  chip_axi_ht_wstrb_t spreg_l1_i_axi_s_wstrb;
  chip_axi_ht_data_t  spreg_l1_i_axi_s_wdata;
  logic               spreg_l1_o_axi_s_wready;
  // B
  logic               spreg_l1_o_axi_s_bvalid;
  pve_ht_axi_m_id_t   spreg_l1_o_axi_s_bid;
  axi_resp_e          spreg_l1_o_axi_s_bresp;
  logic               spreg_l1_i_axi_s_bready;
  // AR
  logic               spreg_l1_i_axi_s_arvalid;
  chip_axi_addr_t     spreg_l1_i_axi_s_araddr;
  pve_ht_axi_m_id_t   spreg_l1_i_axi_s_arid;
  axi_len_t           spreg_l1_i_axi_s_arlen;
  axi_size_e          spreg_l1_i_axi_s_arsize;
  axi_burst_e         spreg_l1_i_axi_s_arburst;
  logic               spreg_l1_o_axi_s_arready;
  // R
  logic               spreg_l1_o_axi_s_rvalid;
  logic               spreg_l1_o_axi_s_rlast;
  pve_ht_axi_m_id_t   spreg_l1_o_axi_s_rid;
  chip_axi_ht_data_t  spreg_l1_o_axi_s_rdata;
  axi_resp_e          spreg_l1_o_axi_s_rresp;
  logic               spreg_l1_i_axi_s_rready;

  for (genvar C = 0; C < PVE_CLUSTER_N_CPU; C++) begin : g_cpu
    for (genvar I = 0; I < MemRegionCount; I++) begin: g_memreg
      always_comb memreg_addr_inp[C][I*PLength+:PLength]               = i_memreg_addr[C][I];
      always_comb memreg_size_inp[C][I*PAddrSizeWidth+:PAddrSizeWidth] = i_memreg_size[C][I];
    end
    for (genvar I = 0; I < raptor_pkg::FunctUnitCount; I++) begin: g_perf_status
      always_comb o_perf_cntr_fu_status[C][I] = perf_cntr_fu_status_oup[C][I*4+:4];
    end
    for (genvar I = 0; I < EventPortCount; I++) begin: g_event_addr
      always_comb o_perf_event_addr[C][I] = perf_event_addr_oup[C][I*PerfEventAddrWidth+:PerfEventAddrWidth];
      for (genvar J = 0; J < PerfEventCount; J++) begin: g_event_delta
        always_comb o_perf_event_deltas[C][I][J] = perf_event_deltas_oup[C][(I*PerfEventCount+J)*EventDelta+:EventDelta];
      end
    end
    pve_cva6v_p u_cva6v (
      .i_clk,
      .i_rst_n,
      .i_clk_en                        (i_clk_en[C]),

      // Config
      .i_boot_addr                     (pve_cva6v_xwidth_t'(i_boot_addr[C])),
      .i_hart_id                       (pve_cva6v_xwidth_t'(i_hart_id  [C])),
      // Memory regions
      .i_memreg_addr                   (memreg_addr_inp[C]),
      .i_memreg_size                   (memreg_size_inp[C]),
      .i_memreg_tcdm                   (i_memreg_tcdm  [C]),
      // Interrupt inputs
      .i_irq                           ({1'b0, i_int_shutdown_req}),
      .i_ipi                           (i_ipi                  [C]),
      .i_time_irq                      (i_time_irq             [C]),
      .i_platform_irq                  (i_platform_irq         [C]),
      // Debug
      .i_debug_req                     (i_debug_req         [C]),
      .i_debug_rst_halt_req            (i_debug_rst_halt_req[C]),
      .o_debug_stop_time               (o_debug_stop_time   [C]),
      // Hart status
      .o_hart_is_wfi                   (o_hart_is_wfi     [C]),
      .o_hart_unavail                  (o_hart_unavail    [C]),
      .o_hart_under_reset              (o_hart_under_reset[C]),
      // Memory side, AXI Manager
      // AW
      .o_axi_m_awvalid                 (spreg_cpu_o_axi_m_awvalid[C]),
      .o_axi_m_awid                    (spreg_cpu_o_axi_m_awid   [C]),
      .o_axi_m_awaddr                  (spreg_cpu_o_axi_m_awaddr [C]),
      .o_axi_m_awlen                   (spreg_cpu_o_axi_m_awlen  [C]),
      .o_axi_m_awsize                  (spreg_cpu_o_axi_m_awsize [C]),
      .o_axi_m_awburst                 (spreg_cpu_o_axi_m_awburst[C]),
      .o_axi_m_awlock                  (spreg_cpu_o_axi_m_awlock [C]),
      .o_axi_m_awcache                 (spreg_cpu_o_axi_m_awcache[C]),
      .o_axi_m_awprot                  (spreg_cpu_o_axi_m_awprot [C]),
      .o_axi_m_awatop                  (spreg_cpu_o_axi_m_awatop [C]),
      .i_axi_m_awready                 (spreg_cpu_i_axi_m_awready[C]),
      // W
      .o_axi_m_wvalid                  (spreg_cpu_o_axi_m_wvalid [C]),
      .o_axi_m_wdata                   (spreg_cpu_o_axi_m_wdata  [C]),
      .o_axi_m_wstrb                   (spreg_cpu_o_axi_m_wstrb  [C]),
      .o_axi_m_wlast                   (spreg_cpu_o_axi_m_wlast  [C]),
      .i_axi_m_wready                  (spreg_cpu_i_axi_m_wready [C]),
      // B
      .i_axi_m_bvalid                  (spreg_cpu_i_axi_m_bvalid [C]),
      .i_axi_m_bid                     (spreg_cpu_i_axi_m_bid    [C]),
      .i_axi_m_bresp                   (spreg_cpu_i_axi_m_bresp  [C]),
      .o_axi_m_bready                  (spreg_cpu_o_axi_m_bready [C]),
      // AR
      .o_axi_m_arvalid                 (spreg_cpu_o_axi_m_arvalid[C]),
      .o_axi_m_arid                    (spreg_cpu_o_axi_m_arid   [C]),
      .o_axi_m_araddr                  (spreg_cpu_o_axi_m_araddr [C]),
      .o_axi_m_arlen                   (spreg_cpu_o_axi_m_arlen  [C]),
      .o_axi_m_arsize                  (spreg_cpu_o_axi_m_arsize [C]),
      .o_axi_m_arburst                 (spreg_cpu_o_axi_m_arburst[C]),
      .o_axi_m_arlock                  (spreg_cpu_o_axi_m_arlock [C]),
      .o_axi_m_arcache                 (spreg_cpu_o_axi_m_arcache[C]),
      .o_axi_m_arprot                  (spreg_cpu_o_axi_m_arprot [C]),
      .i_axi_m_arready                 (spreg_cpu_i_axi_m_arready[C]),
      // R
      .i_axi_m_rvalid                  (spreg_cpu_i_axi_m_rvalid [C]),
      .i_axi_m_rid                     (spreg_cpu_i_axi_m_rid    [C]),
      .i_axi_m_rdata                   (spreg_cpu_i_axi_m_rdata  [C]),
      .i_axi_m_rresp                   (spreg_cpu_i_axi_m_rresp  [C]),
      .i_axi_m_rlast                   (spreg_cpu_i_axi_m_rlast  [C]),
      .o_axi_m_rready                  (spreg_cpu_o_axi_m_rready [C]),
      // Raptor memory ports
      .o_mem_req_valid                 (rvv_cva6v_mem_req_valid[C]),
      .o_mem_req_addr                  (rvv_cva6v_mem_req_addr [C]),
      .o_mem_req_we                    (rvv_cva6v_mem_req_we   [C]),
      .o_mem_req_be                    (rvv_cva6v_mem_req_be   [C]),
      .o_mem_req_wdata                 (rvv_cva6v_mem_req_wdata[C]),
      .i_mem_req_ready                 (rvv_cva6v_mem_req_ready[C]),
      .i_mem_res_valid                 (rvv_cva6v_mem_rsp_valid[C]),
      .i_mem_res_rdata                 (rvv_cva6v_mem_rsp_rdata[C]),
      .i_mem_res_err                   (rvv_cva6v_mem_rsp_err  [C]),
      // Raptor performance counter signals
      .o_perf_cntr_fu_status           (perf_cntr_fu_status_oup         [C]),
      .o_perf_cntr_dispatch_queue_full (o_perf_cntr_dispatch_queue_full [C]),
      .o_perf_cntr_dispatch_queue_empty(o_perf_cntr_dispatch_queue_empty[C]),
      .o_perf_cntr_commit_queue_full   (o_perf_cntr_commit_queue_full   [C]),
      .o_perf_cntr_commit_queue_empty  (o_perf_cntr_commit_queue_empty  [C]),
      // CVA6V performance event signals
      .o_perf_event_addr               (perf_event_addr_oup  [C]),
      .o_perf_event_deltas             (perf_event_deltas_oup[C]),
      // JTAG
      .ijtag_tck                       ('0),
      .ijtag_reset                     ('0),
      .ijtag_sel                       ('0),
      .ijtag_ue                        ('0),
      .ijtag_se                        ('0),
      .ijtag_ce                        ('0),
      .ijtag_si                        ('0),
      .ijtag_so                        (  ),
      // DFT
      .test_clk                        ('0),
      .test_mode                       ('0),
      .edt_update                      ('0),
      .scan_en                         ('0),
      .scan_in                         ('0),
      .scan_out                        (  ),
      // BIST
      .bisr_clk                        ('0),
      .bisr_reset                      ('0),
      .bisr_shift_en                   ('0),
      .bisr_si                         ('0),
      .bisr_so                         (  )
    );

    always_comb rvv_l1_mem_req_valid[C*MemPortCount+:MemPortCount] = rvv_cva6v_mem_req_valid[C];
    always_comb rvv_l1_mem_req_addr[C*MemPortCount*MemPortAddrWidth+:MemPortCount*MemPortAddrWidth] = rvv_cva6v_mem_req_addr[C];
    always_comb rvv_l1_mem_req_we[C*MemPortCount+:MemPortCount] = rvv_cva6v_mem_req_we[C];
    always_comb rvv_l1_mem_req_be[C*MemPortCount*MemPortBeWidth+:MemPortCount*MemPortBeWidth] = rvv_cva6v_mem_req_be[C];
    always_comb rvv_l1_mem_req_wdata[C*MemPortCount*MemPortWidth+:MemPortCount*MemPortWidth] = rvv_cva6v_mem_req_wdata[C];
    always_comb rvv_cva6v_mem_req_ready[C] = rvv_l1_mem_req_ready[C*MemPortCount+:MemPortCount];
    always_comb rvv_cva6v_mem_rsp_valid[C] = rvv_l1_mem_rsp_valid[C*MemPortCount+:MemPortCount];
    always_comb rvv_cva6v_mem_rsp_rdata[C] = rvv_l1_mem_rsp_rdata[C*MemPortCount*MemPortWidth+:MemPortCount*MemPortWidth];
    always_comb rvv_cva6v_mem_rsp_err  [C] = rvv_l1_mem_rsp_err  [C*MemPortCount+:MemPortCount];

    pve_axi_multistage_spill_reg #(
      .NUM_STAGES_AW(CVA6V_NUM_CUTS  ),
      .NUM_STAGES_W (CVA6V_NUM_CUTS  ),
      .NUM_STAGES_B (CVA6V_NUM_CUTS+1),
      .NUM_STAGES_AR(CVA6V_NUM_CUTS  ),
      .NUM_STAGES_R (CVA6V_NUM_CUTS  ),
      .axi_addr_t   (chip_axi_addr_t    ),
      .axi_id_t     (pve_lt_axi_s_id_t  ),
      .axi_data_t   (chip_axi_lt_data_t ),
      .axi_strb_t   (chip_axi_lt_wstrb_t)
    ) u_cva6v_spill_reg (
      .i_clk,
      .i_rst_n,
      // Subordinate side
      // AXI write address channel
      .i_axi_s_awvalid(spreg_cpu_o_axi_m_awvalid[C]),
      .i_axi_s_awid   (spreg_cpu_o_axi_m_awid   [C]),
      .i_axi_s_awaddr (spreg_cpu_o_axi_m_awaddr [C]),
      .i_axi_s_awlen  (spreg_cpu_o_axi_m_awlen  [C]),
      .i_axi_s_awsize (spreg_cpu_o_axi_m_awsize [C]),
      .i_axi_s_awburst(spreg_cpu_o_axi_m_awburst[C]),
      .i_axi_s_awlock (spreg_cpu_o_axi_m_awlock [C]),
      .i_axi_s_awcache(spreg_cpu_o_axi_m_awcache[C]),
      .i_axi_s_awprot (spreg_cpu_o_axi_m_awprot [C]),
      .i_axi_s_awatop (spreg_cpu_o_axi_m_awatop [C]),
      .o_axi_s_awready(spreg_cpu_i_axi_m_awready[C]),
      // AXI write data channel
      .i_axi_s_wvalid (spreg_cpu_o_axi_m_wvalid [C]),
      .i_axi_s_wdata  (spreg_cpu_o_axi_m_wdata  [C]),
      .i_axi_s_wstrb  (spreg_cpu_o_axi_m_wstrb  [C]),
      .i_axi_s_wlast  (spreg_cpu_o_axi_m_wlast  [C]),
      .o_axi_s_wready (spreg_cpu_i_axi_m_wready [C]),
      // AXI write response channel
      .o_axi_s_bvalid (spreg_cpu_i_axi_m_bvalid [C]),
      .o_axi_s_bid    (spreg_cpu_i_axi_m_bid    [C]),
      .o_axi_s_bresp  (spreg_cpu_i_axi_m_bresp  [C]),
      .i_axi_s_bready (spreg_cpu_o_axi_m_bready [C]),
      // AXI read address channel
      .i_axi_s_arvalid(spreg_cpu_o_axi_m_arvalid[C]),
      .i_axi_s_arid   (spreg_cpu_o_axi_m_arid   [C]),
      .i_axi_s_araddr (spreg_cpu_o_axi_m_araddr [C]),
      .i_axi_s_arlen  (spreg_cpu_o_axi_m_arlen  [C]),
      .i_axi_s_arsize (spreg_cpu_o_axi_m_arsize [C]),
      .i_axi_s_arburst(spreg_cpu_o_axi_m_arburst[C]),
      .i_axi_s_arlock (spreg_cpu_o_axi_m_arlock [C]),
      .i_axi_s_arcache(spreg_cpu_o_axi_m_arcache[C]),
      .i_axi_s_arprot (spreg_cpu_o_axi_m_arprot [C]),
      .o_axi_s_arready(spreg_cpu_i_axi_m_arready[C]),
      // AXI read data/response channel
      .o_axi_s_rvalid (spreg_cpu_i_axi_m_rvalid [C]),
      .o_axi_s_rid    (spreg_cpu_i_axi_m_rid    [C]),
      .o_axi_s_rdata  (spreg_cpu_i_axi_m_rdata  [C]),
      .o_axi_s_rresp  (spreg_cpu_i_axi_m_rresp  [C]),
      .o_axi_s_rlast  (spreg_cpu_i_axi_m_rlast  [C]),
      .i_axi_s_rready (spreg_cpu_o_axi_m_rready [C]),
      // Manager Ports
      // AXI write address channel
      .o_axi_m_awvalid(o_cpu_axi_m_awvalid[C]),
      .o_axi_m_awid   (o_cpu_axi_m_awid   [C]),
      .o_axi_m_awaddr (o_cpu_axi_m_awaddr [C]),
      .o_axi_m_awlen  (o_cpu_axi_m_awlen  [C]),
      .o_axi_m_awsize (o_cpu_axi_m_awsize [C]),
      .o_axi_m_awburst(o_cpu_axi_m_awburst[C]),
      .o_axi_m_awlock (o_cpu_axi_m_awlock [C]),
      .o_axi_m_awcache(o_cpu_axi_m_awcache[C]),
      .o_axi_m_awprot (o_cpu_axi_m_awprot [C]),
      .o_axi_m_awatop (o_cpu_axi_m_awatop [C]),
      .i_axi_m_awready(i_cpu_axi_m_awready[C]),
      // AXI write data channel
      .o_axi_m_wvalid (o_cpu_axi_m_wvalid [C]),
      .o_axi_m_wdata  (o_cpu_axi_m_wdata  [C]),
      .o_axi_m_wstrb  (o_cpu_axi_m_wstrb  [C]),
      .o_axi_m_wlast  (o_cpu_axi_m_wlast  [C]),
      .i_axi_m_wready (i_cpu_axi_m_wready [C]),
      // AXI write response channel
      .i_axi_m_bvalid (i_cpu_axi_m_bvalid [C]),
      .i_axi_m_bid    (i_cpu_axi_m_bid    [C]),
      .i_axi_m_bresp  (i_cpu_axi_m_bresp  [C]),
      .o_axi_m_bready (o_cpu_axi_m_bready [C]),
      // AXI read address channel
      .o_axi_m_arvalid(o_cpu_axi_m_arvalid[C]),
      .o_axi_m_arid   (o_cpu_axi_m_arid   [C]),
      .o_axi_m_araddr (o_cpu_axi_m_araddr [C]),
      .o_axi_m_arlen  (o_cpu_axi_m_arlen  [C]),
      .o_axi_m_arsize (o_cpu_axi_m_arsize [C]),
      .o_axi_m_arburst(o_cpu_axi_m_arburst[C]),
      .o_axi_m_arlock (o_cpu_axi_m_arlock [C]),
      .o_axi_m_arcache(o_cpu_axi_m_arcache[C]),
      .o_axi_m_arprot (o_cpu_axi_m_arprot [C]),
      .i_axi_m_arready(i_cpu_axi_m_arready[C]),
      // AXI read data/response channel
      .i_axi_m_rvalid (i_cpu_axi_m_rvalid [C]),
      .i_axi_m_rid    (i_cpu_axi_m_rid    [C]),
      .i_axi_m_rdata  (i_cpu_axi_m_rdata  [C]),
      .i_axi_m_rresp  (i_cpu_axi_m_rresp  [C]),
      .i_axi_m_rlast  (i_cpu_axi_m_rlast  [C]),
      .o_axi_m_rready (o_cpu_axi_m_rready [C])
    );
  end: g_cpu

  pve_axi_multistage_spill_reg #(
    .NUM_STAGES_AW(L1_NUM_CUTS        ),
    .NUM_STAGES_W (L1_NUM_CUTS        ),
    .NUM_STAGES_B (L1_NUM_CUTS        ),
    .NUM_STAGES_AR(L1_NUM_CUTS        ),
    .NUM_STAGES_R (L1_NUM_CUTS        ),
    .axi_addr_t   (chip_axi_addr_t    ),
    .axi_id_t     (pve_ht_axi_m_id_t  ),
    .axi_data_t   (chip_axi_ht_data_t ),
    .axi_strb_t   (chip_axi_ht_wstrb_t)
  ) u_l1_spill_reg (
    .i_clk,
    .i_rst_n,
    // Subordinate side
    // AXI write address channel
    .i_axi_s_awvalid(i_l1_axi_s_awvalid),
    .i_axi_s_awid   (i_l1_axi_s_awid   ),
    .i_axi_s_awaddr (i_l1_axi_s_awaddr ),
    .i_axi_s_awlen  (i_l1_axi_s_awlen  ),
    .i_axi_s_awsize (i_l1_axi_s_awsize ),
    .i_axi_s_awburst(i_l1_axi_s_awburst),
    .i_axi_s_awlock ('0                ),
    .i_axi_s_awcache(axi_cache_e'('0)  ),
    .i_axi_s_awprot ('0                ),
    .i_axi_s_awatop ('0                ),
    .o_axi_s_awready(o_l1_axi_s_awready),
    // AXI write data channel
    .i_axi_s_wvalid (i_l1_axi_s_wvalid ),
    .i_axi_s_wdata  (i_l1_axi_s_wdata  ),
    .i_axi_s_wstrb  (i_l1_axi_s_wstrb  ),
    .i_axi_s_wlast  (i_l1_axi_s_wlast  ),
    .o_axi_s_wready (o_l1_axi_s_wready ),
    // AXI write response channel
    .o_axi_s_bvalid (o_l1_axi_s_bvalid ),
    .o_axi_s_bid    (o_l1_axi_s_bid    ),
    .o_axi_s_bresp  (o_l1_axi_s_bresp  ),
    .i_axi_s_bready (i_l1_axi_s_bready ),
    // AXI read address channel
    .i_axi_s_arvalid(i_l1_axi_s_arvalid),
    .i_axi_s_arid   (i_l1_axi_s_arid   ),
    .i_axi_s_araddr (i_l1_axi_s_araddr ),
    .i_axi_s_arlen  (i_l1_axi_s_arlen  ),
    .i_axi_s_arsize (i_l1_axi_s_arsize ),
    .i_axi_s_arburst(i_l1_axi_s_arburst),
    .i_axi_s_arlock ('0                ),
    .i_axi_s_arcache(axi_cache_e'('0)  ),
    .i_axi_s_arprot ('0                ),
    .o_axi_s_arready(o_l1_axi_s_arready),
    // AXI read data/response channel
    .o_axi_s_rvalid (o_l1_axi_s_rvalid ),
    .o_axi_s_rid    (o_l1_axi_s_rid    ),
    .o_axi_s_rdata  (o_l1_axi_s_rdata  ),
    .o_axi_s_rresp  (o_l1_axi_s_rresp  ),
    .o_axi_s_rlast  (o_l1_axi_s_rlast  ),
    .i_axi_s_rready (i_l1_axi_s_rready ),
    // Manager Ports
    // AXI write address channel
    .o_axi_m_awvalid(spreg_l1_i_axi_s_awvalid),
    .o_axi_m_awid   (spreg_l1_i_axi_s_awid   ),
    .o_axi_m_awaddr (spreg_l1_i_axi_s_awaddr ),
    .o_axi_m_awlen  (spreg_l1_i_axi_s_awlen  ),
    .o_axi_m_awsize (spreg_l1_i_axi_s_awsize ),
    .o_axi_m_awburst(spreg_l1_i_axi_s_awburst),
    .o_axi_m_awlock (                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use AWLOCK
    .o_axi_m_awcache(                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use AWCACHE
    .o_axi_m_awprot (                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use AWPROT
    .o_axi_m_awatop (                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use AWTOP
    .i_axi_m_awready(spreg_l1_o_axi_s_awready),
    // AXI write data channel
    .o_axi_m_wvalid (spreg_l1_i_axi_s_wvalid ),
    .o_axi_m_wdata  (spreg_l1_i_axi_s_wdata  ),
    .o_axi_m_wstrb  (spreg_l1_i_axi_s_wstrb  ),
    .o_axi_m_wlast  (spreg_l1_i_axi_s_wlast  ),
    .i_axi_m_wready (spreg_l1_o_axi_s_wready ),
    // AXI write response channel
    .i_axi_m_bvalid (spreg_l1_o_axi_s_bvalid ),
    .i_axi_m_bid    (spreg_l1_o_axi_s_bid    ),
    .i_axi_m_bresp  (spreg_l1_o_axi_s_bresp  ),
    .o_axi_m_bready (spreg_l1_i_axi_s_bready ),
    // AXI read address channel
    .o_axi_m_arvalid(spreg_l1_i_axi_s_arvalid),
    .o_axi_m_arid   (spreg_l1_i_axi_s_arid   ),
    .o_axi_m_araddr (spreg_l1_i_axi_s_araddr ),
    .o_axi_m_arlen  (spreg_l1_i_axi_s_arlen  ),
    .o_axi_m_arsize (spreg_l1_i_axi_s_arsize ),
    .o_axi_m_arburst(spreg_l1_i_axi_s_arburst),
    .o_axi_m_arlock (                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use ARLOCK
    .o_axi_m_arcache(                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use ARCACHE
    .o_axi_m_arprot (                        ), // ASO-UNUSED_OUTPUT: pve_l1 doesn't use ARPROT
    .i_axi_m_arready(spreg_l1_o_axi_s_arready),
    // AXI read data/response channel
    .i_axi_m_rvalid (spreg_l1_o_axi_s_rvalid ),
    .i_axi_m_rid    (spreg_l1_o_axi_s_rid    ),
    .i_axi_m_rdata  (spreg_l1_o_axi_s_rdata  ),
    .i_axi_m_rresp  (spreg_l1_o_axi_s_rresp  ),
    .i_axi_m_rlast  (spreg_l1_o_axi_s_rlast  ),
    .o_axi_m_rready (spreg_l1_i_axi_s_rready )
  );

  pve_l1_p u_pve_l1 (
    .i_clk,
    .i_rst_n,

    // MMIO ports
    .i_rvv_l1_mem_req_valid(rvv_l1_mem_req_valid    ),
    .i_rvv_l1_mem_req_addr (rvv_l1_mem_req_addr     ),
    .i_rvv_l1_mem_req_we   (rvv_l1_mem_req_we       ),
    .i_rvv_l1_mem_req_be   (rvv_l1_mem_req_be       ),
    .i_rvv_l1_mem_req_wdata(rvv_l1_mem_req_wdata    ),
    .o_rvv_l1_mem_req_ready(rvv_l1_mem_req_ready    ),
    .o_rvv_l1_mem_rsp_valid(rvv_l1_mem_rsp_valid    ),
    .o_rvv_l1_mem_rsp_rdata(rvv_l1_mem_rsp_rdata    ),
    .o_rvv_l1_mem_rsp_err  (rvv_l1_mem_rsp_err      ),

    // AXI write address channel
    .i_l1_axi_s_awvalid    (spreg_l1_i_axi_s_awvalid),
    .i_l1_axi_s_awid       (spreg_l1_i_axi_s_awid   ),
    .i_l1_axi_s_awaddr     (spreg_l1_i_axi_s_awaddr ),
    .i_l1_axi_s_awlen      (spreg_l1_i_axi_s_awlen  ),
    .i_l1_axi_s_awsize     (spreg_l1_i_axi_s_awsize ),
    .i_l1_axi_s_awburst    (spreg_l1_i_axi_s_awburst),
    .o_l1_axi_s_awready    (spreg_l1_o_axi_s_awready),
    // AXI write data channel
    .i_l1_axi_s_wvalid     (spreg_l1_i_axi_s_wvalid ),
    .i_l1_axi_s_wdata      (spreg_l1_i_axi_s_wdata  ),
    .i_l1_axi_s_wstrb      (spreg_l1_i_axi_s_wstrb  ),
    .i_l1_axi_s_wlast      (spreg_l1_i_axi_s_wlast  ),
    .o_l1_axi_s_wready     (spreg_l1_o_axi_s_wready ),
    // AXI write response channel
    .o_l1_axi_s_bvalid     (spreg_l1_o_axi_s_bvalid ),
    .o_l1_axi_s_bid        (spreg_l1_o_axi_s_bid    ),
    .o_l1_axi_s_bresp      (spreg_l1_o_axi_s_bresp  ),
    .i_l1_axi_s_bready     (spreg_l1_i_axi_s_bready ),
    // AXI read address channel
    .i_l1_axi_s_arvalid    (spreg_l1_i_axi_s_arvalid),
    .i_l1_axi_s_arid       (spreg_l1_i_axi_s_arid   ),
    .i_l1_axi_s_araddr     (spreg_l1_i_axi_s_araddr ),
    .i_l1_axi_s_arlen      (spreg_l1_i_axi_s_arlen  ),
    .i_l1_axi_s_arsize     (spreg_l1_i_axi_s_arsize ),
    .i_l1_axi_s_arburst    (spreg_l1_i_axi_s_arburst),
    .o_l1_axi_s_arready    (spreg_l1_o_axi_s_arready),
    // AXI read data/response channel
    .o_l1_axi_s_rvalid     (spreg_l1_o_axi_s_rvalid ),
    .o_l1_axi_s_rid        (spreg_l1_o_axi_s_rid    ),
    .o_l1_axi_s_rdata      (spreg_l1_o_axi_s_rdata  ),
    .o_l1_axi_s_rresp      (spreg_l1_o_axi_s_rresp  ),
    .o_l1_axi_s_rlast      (spreg_l1_o_axi_s_rlast  ),
    .i_l1_axi_s_rready     (spreg_l1_i_axi_s_rready ),

    // Configuration control
    .i_l1_base_address,

    // JTAG
    .ijtag_tck                       ('0),
    .ijtag_reset                     ('0),
    .ijtag_sel                       ('0),
    .ijtag_ue                        ('0),
    .ijtag_se                        ('0),
    .ijtag_ce                        ('0),
    .ijtag_si                        ('0),
    .ijtag_so                        (),
    // DFT
    .test_clk                        ('0),
    .test_mode                       ('0),
    .edt_update                      ('0),
    .scan_en                         ('0),
    .scan_in                         ('0),
    .scan_out                        (),
    // BIST
    .bisr_clk                        ('0),
    .bisr_reset                      ('0),
    .bisr_shift_en                   ('0),
    .bisr_si                         ('0),
    .bisr_so                         ()
  );

endmodule
