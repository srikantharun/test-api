// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA
// Owner: Matt Morris <matt.morris@axelera.ai>

`ifndef DMA_SV
`define DMA_SV

module dma
  import dma_pkg::*;
  import axi_pkg::*;
  import dma_reg_pkg::*;
  import axe_tcl_sram_pkg::*;
  #(
    parameter  int  NUM_PORTS            = 2,
    parameter  int  NUM_CHNLS            = 4,
    parameter  int  DMA_N_BUF_IDXS       = 256,
    parameter  int  DMA_N_IMPL_BUF_IDXS  = 256,
    parameter  int  NR_TOK_PROD          = 3,
    parameter  int  NR_TOK_CONS          = 3,
    parameter  int  NR_TOP_TOK_PROD      = 3,
    parameter  int  NR_TOP_TOK_CONS      = 3,
    parameter  type dma_axi_s_data_t     = logic [64-1:0],
    parameter  type dma_axi_s_addr_t     = logic [ 40-1:0],
    parameter  type dma_axi_s_id_t       = logic [  4-1:0],
    localparam type dma_axi_s_strb_t     = logic [ $bits(dma_axi_s_data_t)/8-1:0],

    parameter  type dma_axi_m_data_t     = logic [512-1:0],
    parameter  type dma_axi_m_addr_t     = logic [ 40-1:0],
    parameter  type dma_axi_m_id_t       = logic [  9-1:0],
    localparam type dma_axi_m_strb_t     = logic [ $bits(dma_axi_m_data_t)/8-1:0],
    parameter  type dma_token_prod_t     = logic [NR_TOK_PROD+NR_TOP_TOK_PROD-1:0],
    parameter  type dma_token_cons_t     = logic [NR_TOK_CONS+NR_TOP_TOK_CONS-1:0],

    localparam int unsigned NumRegions   = 1 + 3*NUM_CHNLS,
    parameter longint  RegionStAddr[NumRegions] = DmaDefaultRegionStAddr[0+:NumRegions],
    parameter longint RegionEndAddr[NumRegions] = DmaDefaultRegionEndAddr[0+:NumRegions]
  ) (
    // Clock and reset signals
    input  wire             i_clk,
    input  wire             i_rst_n,

    // SRAM Sidebands
    input  impl_inp_t       i_impl,
    output impl_oup_t       o_impl,

    // Control
    output logic [NUM_CHNLS-1:0] o_int,

    output logic [$bits(dma_token_prod_t)-1:0]  o_tok_prod_vld[NUM_CHNLS],
    input  logic [$bits(dma_token_prod_t)-1:0]  i_tok_prod_rdy[NUM_CHNLS],
    input  logic [$bits(dma_token_cons_t)-1:0]  i_tok_cons_vld[NUM_CHNLS],
    output logic [$bits(dma_token_cons_t)-1:0]  o_tok_cons_rdy[NUM_CHNLS],

    output logic [NUM_CHNLS-1:0] o_ts_start,
    output logic [NUM_CHNLS-1:0] o_ts_end,
    output logic [NUM_CHNLS-1:0] o_acd_sync,
    output dma_dev_obs_t [NUM_CHNLS-1:0] o_obs,

    // AXI 4 Configuration Interface
    // AXI write address channel
    input  logic            i_axi_s_awvalid,
    input  dma_axi_s_addr_t i_axi_s_awaddr,
    input  dma_axi_s_id_t   i_axi_s_awid,
    input  axi_len_t        i_axi_s_awlen,
    input  axi_size_e       i_axi_s_awsize,
    input  axi_burst_e      i_axi_s_awburst,
    input  logic            i_axi_s_awlock,
    input  axi_cache_e      i_axi_s_awcache,
    input  axi_prot_t       i_axi_s_awprot,
    output logic            o_axi_s_awready,
    // AXI write data channel
    input  logic            i_axi_s_wvalid,
    input  logic            i_axi_s_wlast,
    input  dma_axi_s_data_t i_axi_s_wdata,
    input  dma_axi_s_strb_t i_axi_s_wstrb,
    output logic            o_axi_s_wready,
    // AXI write response channel
    output logic            o_axi_s_bvalid,
    output dma_axi_s_id_t   o_axi_s_bid,
    output axi_resp_e       o_axi_s_bresp,
    input  logic            i_axi_s_bready,
    // AXI read address channel
    input  logic            i_axi_s_arvalid,
    input  dma_axi_s_addr_t i_axi_s_araddr,
    input  dma_axi_s_id_t   i_axi_s_arid,
    input  axi_len_t        i_axi_s_arlen,
    input  axi_size_e       i_axi_s_arsize,
    input  axi_burst_e      i_axi_s_arburst,
    input  logic            i_axi_s_arlock,
    input  axi_cache_e      i_axi_s_arcache,
    input  axi_prot_t       i_axi_s_arprot,
    output logic            o_axi_s_arready,
    // AXI read data/response channel
    output logic            o_axi_s_rvalid,
    output logic            o_axi_s_rlast,
    output dma_axi_s_id_t   o_axi_s_rid,
    output dma_axi_s_data_t o_axi_s_rdata,
    output axi_resp_e       o_axi_s_rresp,
    input  logic            i_axi_s_rready,

    // AXI 4 Data Ports
    // AXI write address channel
    output logic            o_axi_m_awvalid [NUM_PORTS],
    output dma_axi_m_addr_t o_axi_m_awaddr  [NUM_PORTS],
    output dma_axi_m_id_t   o_axi_m_awid    [NUM_PORTS],
    output axi_len_t        o_axi_m_awlen   [NUM_PORTS],
    output axi_size_e       o_axi_m_awsize  [NUM_PORTS],
    output axi_burst_e      o_axi_m_awburst [NUM_PORTS],
    output logic            o_axi_m_awlock  [NUM_PORTS],
    output axi_cache_e      o_axi_m_awcache [NUM_PORTS],
    output axi_prot_t       o_axi_m_awprot  [NUM_PORTS],
    input  logic            i_axi_m_awready [NUM_PORTS],
    // AXI write data channel
    output logic            o_axi_m_wvalid  [NUM_PORTS],
    output logic            o_axi_m_wlast   [NUM_PORTS],
    output dma_axi_m_data_t o_axi_m_wdata   [NUM_PORTS],
    output dma_axi_m_strb_t o_axi_m_wstrb   [NUM_PORTS],
    input  logic            i_axi_m_wready  [NUM_PORTS],
    // AXI write response channel
    input  logic            i_axi_m_bvalid  [NUM_PORTS],
    input  dma_axi_m_id_t   i_axi_m_bid     [NUM_PORTS],
    input  axi_resp_e       i_axi_m_bresp   [NUM_PORTS],
    output logic            o_axi_m_bready  [NUM_PORTS],
    // AXI read address channel
    output logic            o_axi_m_arvalid [NUM_PORTS],
    output dma_axi_m_addr_t o_axi_m_araddr  [NUM_PORTS],
    output dma_axi_m_id_t   o_axi_m_arid    [NUM_PORTS],
    output axi_len_t        o_axi_m_arlen   [NUM_PORTS],
    output axi_size_e       o_axi_m_arsize  [NUM_PORTS],
    output axi_burst_e      o_axi_m_arburst [NUM_PORTS],
    output logic            o_axi_m_arlock  [NUM_PORTS],
    output axi_cache_e      o_axi_m_arcache [NUM_PORTS],
    output axi_prot_t       o_axi_m_arprot  [NUM_PORTS],
    input  logic            i_axi_m_arready [NUM_PORTS],
    // AXI read data/response channel
    input  logic            i_axi_m_rvalid  [NUM_PORTS],
    input  logic            i_axi_m_rlast   [NUM_PORTS],
    input  dma_axi_m_id_t   i_axi_m_rid     [NUM_PORTS],
    input  dma_axi_m_data_t i_axi_m_rdata   [NUM_PORTS],
    input  axi_resp_e       i_axi_m_rresp   [NUM_PORTS],
    output logic            o_axi_m_rready  [NUM_PORTS]

  );

  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] rd_port_xfer_req;
  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] rd_port_xfer_gnt;
  dma_rd_xfer_t rd_port_xfer [NUM_CHNLS];

  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] rd_port_resp_req;
  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] rd_port_resp_gnt;
  dma_rd_resp_t rd_port_resp [NUM_PORTS];

  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] wr_port_xfer_req;
  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] wr_port_xfer_gnt;
  dma_wr_xfer_t wr_port_xfer [NUM_CHNLS];

  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] wr_port_resp_req;
  logic [NUM_PORTS-1:0][NUM_CHNLS-1:0] wr_port_resp_gnt;
  dma_wr_resp_t wr_port_resp [NUM_PORTS];

  dma_global_cfg_t global_cfg [NUM_CHNLS];
  dma_global_sts_t global_sts [NUM_CHNLS];

  impl_inp_t [4 * NUM_CHNLS-1:0] top_impl_in;
  impl_oup_t [4 * NUM_CHNLS-1:0] top_impl_out;
  impl_oup_t [3:0] mems2impl[NUM_CHNLS];

  //logic [NUM_PORTS-1:0] ll_xfer_req;
  //logic [NUM_PORTS-1:0] ll_xfer_gnt;
  //logic [NUM_PORTS-1:0] ll_resp_req;
  //logic [NUM_PORTS-1:0] ll_resp_gnt;

  apb_h2d_t chnl_csr_req [NUM_CHNLS];
  apb_d2h_t chnl_csr_rsp [NUM_CHNLS];
  apb_h2d_t chnl_cmd_req [NUM_CHNLS];
  apb_d2h_t chnl_cmd_rsp [NUM_CHNLS];

  axi_a_ch_h2d_t chnl_mmu_axi_aw     [NUM_CHNLS];
  logic          chnl_mmu_axi_awready[NUM_CHNLS];
  axi_a_ch_h2d_t chnl_mmu_axi_ar     [NUM_CHNLS];
  logic          chnl_mmu_axi_arready[NUM_CHNLS];
  axi_w_ch_h2d_t chnl_mmu_axi_w      [NUM_CHNLS];
  logic          chnl_mmu_axi_wready [NUM_CHNLS];
  axi_r_ch_d2h_t chnl_mmu_axi_r      [NUM_CHNLS];
  logic          chnl_mmu_axi_rready [NUM_CHNLS];
  axi_b_ch_d2h_t chnl_mmu_axi_b      [NUM_CHNLS];
  logic          chnl_mmu_axi_bready [NUM_CHNLS];
  axi_a_ch_h2d_t chnl_csr_axi_aw     [NUM_CHNLS];
  logic          chnl_csr_axi_awready[NUM_CHNLS];
  axi_a_ch_h2d_t chnl_csr_axi_ar     [NUM_CHNLS];
  logic          chnl_csr_axi_arready[NUM_CHNLS];
  axi_w_ch_h2d_t chnl_csr_axi_w      [NUM_CHNLS];
  logic          chnl_csr_axi_wready [NUM_CHNLS];
  axi_r_ch_d2h_t chnl_csr_axi_r      [NUM_CHNLS];
  logic          chnl_csr_axi_rready [NUM_CHNLS];
  axi_b_ch_d2h_t chnl_csr_axi_b      [NUM_CHNLS];
  logic          chnl_csr_axi_bready [NUM_CHNLS];
  axi_a_ch_h2d_t chnl_cmd_axi_aw     [NUM_CHNLS];
  logic          chnl_cmd_axi_awready[NUM_CHNLS];
  axi_a_ch_h2d_t chnl_cmd_axi_ar     [NUM_CHNLS];
  logic          chnl_cmd_axi_arready[NUM_CHNLS];
  axi_w_ch_h2d_t chnl_cmd_axi_w      [NUM_CHNLS];
  logic          chnl_cmd_axi_wready [NUM_CHNLS];
  axi_r_ch_d2h_t chnl_cmd_axi_r      [NUM_CHNLS];
  logic          chnl_cmd_axi_rready [NUM_CHNLS];
  axi_b_ch_d2h_t chnl_cmd_axi_b      [NUM_CHNLS];
  logic          chnl_cmd_axi_bready [NUM_CHNLS];

  dma_token_prod_t tok_prod_vld[NUM_CHNLS];
  dma_token_prod_t tok_prod_rdy[NUM_CHNLS];
  dma_token_cons_t tok_cons_vld[NUM_CHNLS];
  dma_token_cons_t tok_cons_rdy[NUM_CHNLS];


  dma_progif
  #(
    .NUM_PORTS        (NUM_PORTS),
    .NUM_CHNLS        (NUM_CHNLS),
    .dma_axi_s_data_t (dma_axi_s_data_t),
    .dma_axi_s_strb_t (dma_axi_s_strb_t),
    .dma_axi_s_addr_t (dma_axi_s_addr_t),
    .dma_axi_s_id_t   (dma_axi_s_id_t),
    .RegionStAddr     (RegionStAddr),
    .RegionEndAddr    (RegionEndAddr)
  ) u_progif
  (
    .i_clk,
    .i_rst_n,

    .i_axi_s_awvalid,
    .i_axi_s_awaddr,
    .i_axi_s_awid,
    .i_axi_s_awlen,
    .i_axi_s_awsize,
    .i_axi_s_awburst,
    .i_axi_s_awlock,
    .i_axi_s_awcache,
    .i_axi_s_awprot,
    .o_axi_s_awready,

    .i_axi_s_wvalid,
    .i_axi_s_wlast,
    .i_axi_s_wdata,
    .i_axi_s_wstrb,
    .o_axi_s_wready,

    .o_axi_s_bvalid,
    .o_axi_s_bid,
    .o_axi_s_bresp,
    .i_axi_s_bready,

    .i_axi_s_arvalid,
    .i_axi_s_araddr,
    .i_axi_s_arid,
    .i_axi_s_arlen,
    .i_axi_s_arsize,
    .i_axi_s_arburst,
    .i_axi_s_arlock,
    .i_axi_s_arcache,
    .i_axi_s_arprot,
    .o_axi_s_arready,

    .o_axi_s_rvalid,
    .o_axi_s_rlast,
    .o_axi_s_rid,
    .o_axi_s_rdata,
    .o_axi_s_rresp,
    .i_axi_s_rready,

    //.o_ll_xfer_req     (ll_xfer_req),
    //.i_ll_xfer_gnt     (ll_xfer_gnt),
    //.o_ll_xfer         (rd_port_xfer[NUM_CHNLS]),

    //.i_ll_resp_req     (ll_resp_req),
    //.o_ll_resp_gnt     (ll_resp_gnt),
    //.i_ll_resp         (rd_port_resp),

    .o_global_cfg      (global_cfg),
    .i_global_sts      (global_sts),

    .o_chnl_mmu_axi_aw      (chnl_mmu_axi_aw),
    .i_chnl_mmu_axi_awready (chnl_mmu_axi_awready),
    .o_chnl_mmu_axi_ar      (chnl_mmu_axi_ar),
    .i_chnl_mmu_axi_arready (chnl_mmu_axi_arready),
    .o_chnl_mmu_axi_w       (chnl_mmu_axi_w),
    .i_chnl_mmu_axi_wready  (chnl_mmu_axi_wready),
    .i_chnl_mmu_axi_r       (chnl_mmu_axi_r),
    .o_chnl_mmu_axi_rready  (chnl_mmu_axi_rready),
    .i_chnl_mmu_axi_b       (chnl_mmu_axi_b),
    .o_chnl_mmu_axi_bready  (chnl_mmu_axi_bready),
    .o_chnl_csr_axi_aw      (chnl_csr_axi_aw),
    .i_chnl_csr_axi_awready (chnl_csr_axi_awready),
    .o_chnl_csr_axi_ar      (chnl_csr_axi_ar),
    .i_chnl_csr_axi_arready (chnl_csr_axi_arready),
    .o_chnl_csr_axi_w       (chnl_csr_axi_w),
    .i_chnl_csr_axi_wready  (chnl_csr_axi_wready),
    .i_chnl_csr_axi_r       (chnl_csr_axi_r),
    .o_chnl_csr_axi_rready  (chnl_csr_axi_rready),
    .i_chnl_csr_axi_b       (chnl_csr_axi_b),
    .o_chnl_csr_axi_bready  (chnl_csr_axi_bready),
    .o_chnl_cmd_axi_aw      (chnl_cmd_axi_aw),
    .i_chnl_cmd_axi_awready (chnl_cmd_axi_awready),
    .o_chnl_cmd_axi_ar      (chnl_cmd_axi_ar),
    .i_chnl_cmd_axi_arready (chnl_cmd_axi_arready),
    .o_chnl_cmd_axi_w       (chnl_cmd_axi_w),
    .i_chnl_cmd_axi_wready  (chnl_cmd_axi_wready),
    .i_chnl_cmd_axi_r       (chnl_cmd_axi_r),
    .o_chnl_cmd_axi_rready  (chnl_cmd_axi_rready),
    .i_chnl_cmd_axi_b       (chnl_cmd_axi_b),
    .o_chnl_cmd_axi_bready  (chnl_cmd_axi_bready)

  );

  //for (genvar P = 0; P < NUM_PORTS; P++) begin: g_llwire
    //always_comb rd_port_xfer_req[P][NUM_CHNLS] = ll_xfer_req[P];
    //always_comb ll_xfer_gnt[P] = rd_port_xfer_gnt[P][NUM_CHNLS];
    //always_comb ll_resp_req[P] = rd_port_resp_req[P][NUM_CHNLS];
    //always_comb rd_port_resp_gnt[P][NUM_CHNLS] = ll_resp_gnt[P];
  //end: g_llwire


  for (genvar I = 0; I < NUM_PORTS; I++) begin: g_portmux

    dma_axi_rd_port_mux
    #(
      .NUM_CHNLS       (NUM_CHNLS),
      .dma_axi_data_t  (dma_axi_m_data_t),
      .dma_axi_strb_t  (dma_axi_m_strb_t),
      .dma_axi_addr_t  (dma_axi_m_addr_t),
      .dma_axi_id_t    (dma_axi_m_id_t)
    ) u_axi_rd_mux
    (
      .i_clk,
      .i_rst_n,

      .i_xfer_req      (rd_port_xfer_req[I]),
      .o_xfer_gnt      (rd_port_xfer_gnt[I]),
      .i_xfer          (rd_port_xfer),

      .o_resp_req      (rd_port_resp_req[I]),
      .i_resp_gnt      (rd_port_resp_gnt[I]),
      .o_resp          (rd_port_resp[I]),

      .o_axi_m_arvalid (o_axi_m_arvalid[I]),
      .o_axi_m_araddr  (o_axi_m_araddr[I]),
      .o_axi_m_arid    (o_axi_m_arid[I]),
      .o_axi_m_arlen   (o_axi_m_arlen[I]),
      .o_axi_m_arsize  (o_axi_m_arsize[I]),
      .o_axi_m_arburst (o_axi_m_arburst[I]),
      .o_axi_m_arlock  (o_axi_m_arlock[I]),
      .o_axi_m_arcache (o_axi_m_arcache[I]),
      .o_axi_m_arprot  (o_axi_m_arprot[I]),
      .i_axi_m_arready (i_axi_m_arready[I]),

      .i_axi_m_rvalid  (i_axi_m_rvalid[I]),
      .i_axi_m_rlast   (i_axi_m_rlast[I]),
      .i_axi_m_rid     (i_axi_m_rid[I]),
      .i_axi_m_rdata   (i_axi_m_rdata[I]),
      .i_axi_m_rresp   (i_axi_m_rresp[I]),
      .o_axi_m_rready  (o_axi_m_rready[I])

    );

    dma_axi_wr_port_mux
    #(
       .NUM_CHNLS      (NUM_CHNLS),
      .dma_axi_data_t  (dma_axi_m_data_t),
      .dma_axi_strb_t  (dma_axi_m_strb_t),
      .dma_axi_addr_t  (dma_axi_m_addr_t),
      .dma_axi_id_t    (dma_axi_m_id_t)
    ) u_axi_wr_mux
    (
      .i_clk,
      .i_rst_n,

      .i_xfer_req      (wr_port_xfer_req[I]),
      .o_xfer_gnt      (wr_port_xfer_gnt[I]),
      .i_xfer          (wr_port_xfer),

      .o_resp_req      (wr_port_resp_req[I]),
      .i_resp_gnt      (wr_port_resp_gnt[I]),
      .o_resp          (wr_port_resp[I]),

      .o_axi_m_awvalid (o_axi_m_awvalid[I]),
      .o_axi_m_awaddr  (o_axi_m_awaddr[I]),
      .o_axi_m_awid    (o_axi_m_awid[I]),
      .o_axi_m_awlen   (o_axi_m_awlen[I]),
      .o_axi_m_awsize  (o_axi_m_awsize[I]),
      .o_axi_m_awburst (o_axi_m_awburst[I]),
      .o_axi_m_awlock  (o_axi_m_awlock[I]),
      .o_axi_m_awcache (o_axi_m_awcache[I]),
      .o_axi_m_awprot  (o_axi_m_awprot[I]),
      .i_axi_m_awready (i_axi_m_awready[I]),

      .o_axi_m_wvalid  (o_axi_m_wvalid[I]),
      .o_axi_m_wlast   (o_axi_m_wlast[I]),
      .o_axi_m_wdata   (o_axi_m_wdata[I]),
      .o_axi_m_wstrb   (o_axi_m_wstrb[I]),
      .i_axi_m_wready  (i_axi_m_wready[I]),

      .i_axi_m_bvalid  (i_axi_m_bvalid[I]),
      .i_axi_m_bid     (i_axi_m_bid[I]),
      .i_axi_m_bresp   (i_axi_m_bresp[I]),
      .o_axi_m_bready  (o_axi_m_bready[I])

    );
  end: g_portmux

  for (genvar C = 0; C < NUM_CHNLS; C++) begin: g_chnl

    logic [NUM_PORTS-1:0] src_xfer_req;
    logic [NUM_PORTS-1:0] src_xfer_gnt;
    logic [NUM_PORTS-1:0] src_resp_req;
    logic [NUM_PORTS-1:0] src_resp_gnt;
    logic [NUM_PORTS-1:0] dst_xfer_req;
    logic [NUM_PORTS-1:0] dst_xfer_gnt;
    logic [NUM_PORTS-1:0] dst_resp_req;
    logic [NUM_PORTS-1:0] dst_resp_gnt;


    for (genvar P = 0; P < NUM_PORTS; P++) begin: g_portwire

      always_comb rd_port_xfer_req[P][C] = src_xfer_req[P];
      always_comb src_xfer_gnt[P]        = rd_port_xfer_gnt[P][C];
      always_comb src_resp_req[P]        = rd_port_resp_req[P][C];
      always_comb rd_port_resp_gnt[P][C] = src_resp_gnt[P];
      always_comb wr_port_xfer_req[P][C] = dst_xfer_req[P];
      always_comb dst_xfer_gnt[P]        = wr_port_xfer_gnt[P][C];
      always_comb dst_resp_req[P]        = wr_port_resp_req[P][C];
      always_comb wr_port_resp_gnt[P][C] = dst_resp_gnt[P];

    end: g_portwire

    dma_channel #(
      .DMA_N_BUF_IDXS(DMA_N_BUF_IDXS),
      .DMA_N_IMPL_BUF_IDXS(DMA_N_IMPL_BUF_IDXS),
      .NR_TOK_PROD(NR_TOK_PROD),
      .NR_TOK_CONS(NR_TOK_CONS),
      .NR_TOP_TOK_PROD(NR_TOP_TOK_PROD),
      .NR_TOP_TOK_CONS(NR_TOP_TOK_CONS)
    ) u_chnl (
      .i_clk,
      .i_rst_n,

       .i_impl           (top_impl_in[4*C +: 4]),
       .o_impl           (mems2impl[C]),

      .i_global_cfg      (global_cfg[C]),
      .o_global_sts      (global_sts[C]),

      .i_chnl_mmu_axi_aw      (chnl_mmu_axi_aw[C]),
      .o_chnl_mmu_axi_awready (chnl_mmu_axi_awready[C]),
      .i_chnl_mmu_axi_ar      (chnl_mmu_axi_ar[C]),
      .o_chnl_mmu_axi_arready (chnl_mmu_axi_arready[C]),
      .i_chnl_mmu_axi_w       (chnl_mmu_axi_w[C]),
      .o_chnl_mmu_axi_wready  (chnl_mmu_axi_wready[C]),
      .o_chnl_mmu_axi_r       (chnl_mmu_axi_r[C]),
      .i_chnl_mmu_axi_rready  (chnl_mmu_axi_rready[C]),
      .o_chnl_mmu_axi_b       (chnl_mmu_axi_b[C]),
      .i_chnl_mmu_axi_bready  (chnl_mmu_axi_bready[C]),
      .i_chnl_csr_axi_aw      (chnl_csr_axi_aw[C]),
      .o_chnl_csr_axi_awready (chnl_csr_axi_awready[C]),
      .i_chnl_csr_axi_ar      (chnl_csr_axi_ar[C]),
      .o_chnl_csr_axi_arready (chnl_csr_axi_arready[C]),
      .i_chnl_csr_axi_w       (chnl_csr_axi_w[C]),
      .o_chnl_csr_axi_wready  (chnl_csr_axi_wready[C]),
      .o_chnl_csr_axi_r       (chnl_csr_axi_r[C]),
      .i_chnl_csr_axi_rready  (chnl_csr_axi_rready[C]),
      .o_chnl_csr_axi_b       (chnl_csr_axi_b[C]),
      .i_chnl_csr_axi_bready  (chnl_csr_axi_bready[C]),
      .i_chnl_cmd_axi_aw      (chnl_cmd_axi_aw[C]),
      .o_chnl_cmd_axi_awready (chnl_cmd_axi_awready[C]),
      .i_chnl_cmd_axi_ar      (chnl_cmd_axi_ar[C]),
      .o_chnl_cmd_axi_arready (chnl_cmd_axi_arready[C]),
      .i_chnl_cmd_axi_w       (chnl_cmd_axi_w[C]),
      .o_chnl_cmd_axi_wready  (chnl_cmd_axi_wready[C]),
      .o_chnl_cmd_axi_r       (chnl_cmd_axi_r[C]),
      .i_chnl_cmd_axi_rready  (chnl_cmd_axi_rready[C]),
      .o_chnl_cmd_axi_b       (chnl_cmd_axi_b[C]),
      .i_chnl_cmd_axi_bready  (chnl_cmd_axi_bready[C]),

      .o_src_xfer_req     (src_xfer_req),
      .i_src_xfer_gnt     (src_xfer_gnt),
      .o_src_xfer         (rd_port_xfer[C]),

      .i_src_resp_req     (src_resp_req),
      .o_src_resp_gnt     (src_resp_gnt),
      .i_src_resp         (rd_port_resp),

      .o_dst_xfer_req     (dst_xfer_req),
      .i_dst_xfer_gnt     (dst_xfer_gnt),
      .o_dst_xfer         (wr_port_xfer[C]),

      .i_dst_resp_req     (dst_resp_req),
      .o_dst_resp_gnt     (dst_resp_gnt),
      .i_dst_resp         (wr_port_resp),

      .o_tok_prod_vld     (o_tok_prod_vld[C]),
      .i_tok_prod_rdy     (i_tok_prod_rdy[C]),
      .i_tok_cons_vld     (i_tok_cons_vld[C]),
      .o_tok_cons_rdy     (o_tok_cons_rdy[C]),

      .o_ts_start         (o_ts_start[C]),
      .o_ts_end           (o_ts_end[C]),
      .o_acd_sync         (o_acd_sync[C]),
      .o_obs              (o_obs[C]),

      .o_sts              (),
      .o_int              (o_int[C])
);


  end: g_chnl

  always_comb
    for (int unsigned C = 0; C < NUM_CHNLS; C++)
      for (int unsigned I = 0; I < 4; I++)
        top_impl_out[4*C+I] = mems2impl[C][I];

axe_tcl_sram_cfg #(
  .NUM_SRAMS  ( 4 * NUM_CHNLS )
) u_sram_cfg (
  /// implementation specific inputs
  .i_s     (i_impl),
  /// implementation specific outputs
  .o_s     (o_impl),
  /// implementation specific outputs
  .o_m     (top_impl_in),
  /// implementation specific inputs
  .i_m     (top_impl_out)
);


endmodule
`endif


