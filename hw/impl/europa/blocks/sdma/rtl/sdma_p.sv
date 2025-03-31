// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>

/// Stream DMA
///
module sdma_p
  import axi_pkg::*;
  import chip_pkg::*;
  import sdma_pkg::*;
  import axe_tcl_sram_pkg::*;
(
  /// Fast Clock, positive edge triggered
  input   wire i_clk,
  /// Ref Clock, positive edge triggered
  input   wire i_ref_clk,
  /// Asynchronous POR / always On reset, active low
  input   wire i_ao_rst_n,
  /// Asynchronous global reset, active low
  input   wire i_global_rst_n,
  /// Interrupts
  output  logic [NUM_CHNLS-1:0]   o_int,
  /// SDMA number, to be used by top token manager to determine which UID to attach
  input  logic i_sdma_nr,

  input  logic i_inter_core_sync,

  /// Tokens
  output chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_maddr,
  output logic                            o_tok_prod_ocpl_m_mcmd,
  input  logic                            i_tok_prod_ocpl_m_scmdaccept,
  output chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_mdata,
  input  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_maddr,
  input  logic                            i_tok_cons_ocpl_s_mcmd,
  output logic                            o_tok_cons_ocpl_s_scmdaccept,
  input  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_mdata,

  //////////////////////////////////////////////
  /// SYS_CFG Bus
  //////////////////////////////////////////////

  input  chip_syscfg_addr_t       i_cfg_apb4_s_paddr,
  input  chip_apb_syscfg_data_t   i_cfg_apb4_s_pwdata,
  input  logic                    i_cfg_apb4_s_pwrite,
  input  logic                    i_cfg_apb4_s_psel,
  input  logic                    i_cfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t   i_cfg_apb4_s_pstrb,
  input  logic [3-1:0]            i_cfg_apb4_s_pprot,
  output logic                    o_cfg_apb4_s_pready,
  output chip_apb_syscfg_data_t   o_cfg_apb4_s_prdata,
  output logic                    o_cfg_apb4_s_pslverr,

  output logic                    o_noc_async_idle_req,
  input  logic                    i_noc_async_idle_ack,
  input  logic                    i_noc_async_idle_val,
  output logic                    o_noc_tok_async_idle_req,
  input  logic                    i_noc_tok_async_idle_ack,
  input  logic                    i_noc_tok_async_idle_val,
  output logic                    o_noc_clken,
  output logic                    o_noc_rst_n,

  input  logic                    i_clock_throttle,

    // AXI 4 Configuration Interface
    // AXI write address channel
    input  logic                  i_axi_s_awvalid,
    input  chip_axi_addr_t        i_axi_s_awaddr,
    input  sdma_axi_lt_id_t       i_axi_s_awid,
    input  axi_len_t              i_axi_s_awlen,
    input  axi_size_e             i_axi_s_awsize,
    input  axi_burst_e            i_axi_s_awburst,
    input  logic                  i_axi_s_awlock,
    input  axi_cache_e            i_axi_s_awcache,
    input  axi_prot_t             i_axi_s_awprot,
    output logic                  o_axi_s_awready,
    // AXI write data channel
    input  logic                  i_axi_s_wvalid,
    input  logic                  i_axi_s_wlast,
    input  chip_axi_lt_data_t     i_axi_s_wdata,
    input  chip_axi_lt_wstrb_t    i_axi_s_wstrb,
    output logic                  o_axi_s_wready,
    // AXI write response channel
    output logic                  o_axi_s_bvalid,
    output sdma_axi_lt_id_t       o_axi_s_bid,
    output axi_resp_e             o_axi_s_bresp,
    input  logic                  i_axi_s_bready,
    // AXI read address channel
    input  logic                  i_axi_s_arvalid,
    input  chip_axi_addr_t        i_axi_s_araddr,
    input  sdma_axi_lt_id_t       i_axi_s_arid,
    input  axi_len_t              i_axi_s_arlen,
    input  axi_size_e             i_axi_s_arsize,
    input  axi_burst_e            i_axi_s_arburst,
    input  logic                  i_axi_s_arlock,
    input  axi_cache_e            i_axi_s_arcache,
    input  axi_prot_t             i_axi_s_arprot,
    output logic                  o_axi_s_arready,
    // AXI read data/response channel
    output logic                  o_axi_s_rvalid,
    output logic                  o_axi_s_rlast,
    output sdma_axi_lt_id_t       o_axi_s_rid,
    output chip_axi_lt_data_t     o_axi_s_rdata,
    output axi_resp_e             o_axi_s_rresp,
    input  logic                  i_axi_s_rready,

    // AXI 4 Data Ports
    // PORT 0
    // AXI write address channel
    output logic                  o_axi_m0_awvalid,
    output chip_axi_addr_t        o_axi_m0_awaddr,
    output sdma_axi_ht_id_t       o_axi_m0_awid,
    output axi_len_t              o_axi_m0_awlen,
    output axi_size_e             o_axi_m0_awsize,
    output axi_burst_e            o_axi_m0_awburst,
    output logic                  o_axi_m0_awlock,
    output axi_cache_e            o_axi_m0_awcache,
    output axi_prot_t             o_axi_m0_awprot,
    input  logic                  i_axi_m0_awready,
    // AXI write data channel
    output logic                  o_axi_m0_wvalid,
    output logic                  o_axi_m0_wlast,
    output chip_axi_ht_data_t     o_axi_m0_wdata,
    output chip_axi_ht_wstrb_t    o_axi_m0_wstrb,
    input  logic                  i_axi_m0_wready,
    // AXI write response channel
    input  logic                  i_axi_m0_bvalid,
    input  sdma_axi_ht_id_t       i_axi_m0_bid,
    input  axi_resp_e             i_axi_m0_bresp,
    output logic                  o_axi_m0_bready,
    // AXI read address channel
    output logic                  o_axi_m0_arvalid,
    output chip_axi_addr_t        o_axi_m0_araddr,
    output sdma_axi_ht_id_t       o_axi_m0_arid,
    output axi_len_t              o_axi_m0_arlen,
    output axi_size_e             o_axi_m0_arsize,
    output axi_burst_e            o_axi_m0_arburst,
    output logic                  o_axi_m0_arlock,
    output axi_cache_e            o_axi_m0_arcache,
    output axi_prot_t             o_axi_m0_arprot,
    input  logic                  i_axi_m0_arready,
    // AXI read data/response channel
    input  logic                  i_axi_m0_rvalid,
    input  logic                  i_axi_m0_rlast,
    input  sdma_axi_ht_id_t       i_axi_m0_rid,
    input  chip_axi_ht_data_t     i_axi_m0_rdata,
    input  axi_resp_e             i_axi_m0_rresp,
    output logic                  o_axi_m0_rready,
    // PORT 1
    // AXI write address channel
    output logic                  o_axi_m1_awvalid,
    output chip_axi_addr_t        o_axi_m1_awaddr,
    output sdma_axi_ht_id_t       o_axi_m1_awid,
    output axi_len_t              o_axi_m1_awlen,
    output axi_size_e             o_axi_m1_awsize,
    output axi_burst_e            o_axi_m1_awburst,
    output logic                  o_axi_m1_awlock,
    output axi_cache_e            o_axi_m1_awcache,
    output axi_prot_t             o_axi_m1_awprot,
    input  logic                  i_axi_m1_awready,
    // AXI write data channel
    output logic                  o_axi_m1_wvalid,
    output logic                  o_axi_m1_wlast,
    output chip_axi_ht_data_t     o_axi_m1_wdata,
    output chip_axi_ht_wstrb_t    o_axi_m1_wstrb,
    input  logic                  i_axi_m1_wready,
    // AXI write response channel
    input  logic                  i_axi_m1_bvalid,
    input  sdma_axi_ht_id_t       i_axi_m1_bid,
    input  axi_resp_e             i_axi_m1_bresp,
    output logic                  o_axi_m1_bready,
    // AXI read address channel
    output logic                  o_axi_m1_arvalid,
    output chip_axi_addr_t        o_axi_m1_araddr,
    output sdma_axi_ht_id_t       o_axi_m1_arid,
    output axi_len_t              o_axi_m1_arlen,
    output axi_size_e             o_axi_m1_arsize,
    output axi_burst_e            o_axi_m1_arburst,
    output logic                  o_axi_m1_arlock,
    output axi_cache_e            o_axi_m1_arcache,
    output axi_prot_t             o_axi_m1_arprot,
    input  logic                  i_axi_m1_arready,
    // AXI read data/response channel
    input  logic                  i_axi_m1_rvalid,
    input  logic                  i_axi_m1_rlast,
    input  sdma_axi_ht_id_t       i_axi_m1_rid,
    input  chip_axi_ht_data_t     i_axi_m1_rdata,
    input  axi_resp_e             i_axi_m1_rresp,
    output logic                  o_axi_m1_rready,

  ///// AXI manager:
  // Write Address Channel
  output sdma_axi_lt_id_t     o_axi_trc_m_awid,
  output chip_axi_addr_t      o_axi_trc_m_awaddr,
  output axi_pkg::axi_len_t   o_axi_trc_m_awlen,
  output axi_pkg::axi_size_t  o_axi_trc_m_awsize,
  output axi_pkg::axi_burst_t o_axi_trc_m_awburst,
  output logic                o_axi_trc_m_awlock,
  output axi_pkg::axi_cache_e o_axi_trc_m_awcache,
  output axi_pkg::axi_qos_t   o_axi_trc_m_awqos,
  output axi_pkg::axi_prot_t  o_axi_trc_m_awprot,
  output logic                o_axi_trc_m_awvalid,
  input  logic                i_axi_trc_m_awready,
  // Write  Data Channel
  output chip_axi_lt_data_t   o_axi_trc_m_wdata,
  output chip_axi_lt_wstrb_t  o_axi_trc_m_wstrb,
  output logic                o_axi_trc_m_wlast,
  output logic                o_axi_trc_m_wvalid,
  input  logic                i_axi_trc_m_wready,
  // Write Response Channel
  input  sdma_axi_lt_id_t     i_axi_trc_m_bid,
  input  axi_pkg::axi_resp_t  i_axi_trc_m_bresp,
  input  logic                i_axi_trc_m_bvalid,
  output logic                o_axi_trc_m_bready,
  // Read Address Channel
  output sdma_axi_lt_id_t     o_axi_trc_m_arid,
  output chip_axi_addr_t      o_axi_trc_m_araddr,
  output axi_pkg::axi_len_t   o_axi_trc_m_arlen,
  output axi_pkg::axi_size_t  o_axi_trc_m_arsize,
  output axi_pkg::axi_burst_t o_axi_trc_m_arburst,
  output logic                o_axi_trc_m_arlock,
  output axi_pkg::axi_cache_e o_axi_trc_m_arcache,
  output axi_pkg::axi_qos_t   o_axi_trc_m_arqos,
  output axi_pkg::axi_prot_t  o_axi_trc_m_arprot,
  output logic                o_axi_trc_m_arvalid,
  input  logic                i_axi_trc_m_arready,
  // Read Data Channel
  input  sdma_axi_lt_id_t     i_axi_trc_m_rid,
  input  chip_axi_lt_data_t   i_axi_trc_m_rdata,
  input  axi_pkg::axi_resp_t  i_axi_trc_m_rresp,
  input  logic                i_axi_trc_m_rlast,
  input  logic                i_axi_trc_m_rvalid,
  output logic                o_axi_trc_m_rready,

  //////////////////////////////////////////////
  /// DFT
  //////////////////////////////////////////////

  // JTAG
  input  wire                   tck,
  input  wire                   trst,
  input  logic                  tms,
  input  logic                  tdi,
  output logic                  tdo_en,
  output logic                  tdo,
  // DFT
  input  wire                   test_clk,
  input  logic                  test_mode,
  input  logic                  edt_update,
  input  logic                  scan_en,
  input  logic [           7:0] scan_in,
  output logic [           7:0] scan_out,
  // BIST
  input  wire                   bisr_clk,
  input  wire                   bisr_reset,
  input  logic                  bisr_shift_en,
  input  logic                  bisr_si,
  output logic                  bisr_so

);
  // AXI 4 Configuration Interface
  // AXI write address channel
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_awvalid;
  chip_axi_addr_t        [SDMA_AXI_ENDPOINTS-1:0] axi_s_awaddr;
  sdma_axi_lt_id_t       [SDMA_AXI_ENDPOINTS-1:0] axi_s_awid;
  axi_len_t              [SDMA_AXI_ENDPOINTS-1:0] axi_s_awlen;
  axi_size_e             [SDMA_AXI_ENDPOINTS-1:0] axi_s_awsize;
  axi_burst_e            [SDMA_AXI_ENDPOINTS-1:0] axi_s_awburst;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_awlock;
  axi_cache_e            [SDMA_AXI_ENDPOINTS-1:0] axi_s_awcache;
  axi_prot_t             [SDMA_AXI_ENDPOINTS-1:0] axi_s_awprot;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_awready;
  // AXI write data channel
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_wvalid;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_wlast;
  chip_axi_lt_data_t     [SDMA_AXI_ENDPOINTS-1:0] axi_s_wdata;
  chip_axi_lt_wstrb_t    [SDMA_AXI_ENDPOINTS-1:0] axi_s_wstrb;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_wready;
  // AXI write response channel
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_bvalid;
  sdma_axi_lt_id_t       [SDMA_AXI_ENDPOINTS-1:0] axi_s_bid;
  axi_resp_e             [SDMA_AXI_ENDPOINTS-1:0] axi_s_bresp;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_bready;
  // AXI read address channel
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_arvalid;
  chip_axi_addr_t        [SDMA_AXI_ENDPOINTS-1:0] axi_s_araddr;
  sdma_axi_lt_id_t       [SDMA_AXI_ENDPOINTS-1:0] axi_s_arid;
  axi_len_t              [SDMA_AXI_ENDPOINTS-1:0] axi_s_arlen;
  axi_size_e             [SDMA_AXI_ENDPOINTS-1:0] axi_s_arsize;
  axi_burst_e            [SDMA_AXI_ENDPOINTS-1:0] axi_s_arburst;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_arlock;
  axi_cache_e            [SDMA_AXI_ENDPOINTS-1:0] axi_s_arcache;
  axi_prot_t             [SDMA_AXI_ENDPOINTS-1:0] axi_s_arprot;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_arready;
  // AXI read data/response channel
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_rvalid;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_rlast;
  sdma_axi_lt_id_t       [SDMA_AXI_ENDPOINTS-1:0] axi_s_rid;
  chip_axi_lt_data_t     [SDMA_AXI_ENDPOINTS-1:0] axi_s_rdata;
  axi_resp_e             [SDMA_AXI_ENDPOINTS-1:0] axi_s_rresp;
  logic                  [SDMA_AXI_ENDPOINTS-1:0] axi_s_rready;

  logic                  axi_m_awvalid [NUM_PORTS];
  chip_axi_addr_t        axi_m_awaddr  [NUM_PORTS];
  sdma_axi_ht_id_t       axi_m_awid    [NUM_PORTS];
  axi_len_t              axi_m_awlen   [NUM_PORTS];
  axi_size_e             axi_m_awsize  [NUM_PORTS];
  axi_burst_e            axi_m_awburst [NUM_PORTS];
  logic                  axi_m_awlock  [NUM_PORTS];
  axi_cache_e            axi_m_awcache [NUM_PORTS];
  axi_prot_t             axi_m_awprot  [NUM_PORTS];
  logic                  axi_m_awready [NUM_PORTS];
  logic                  axi_m_wvalid  [NUM_PORTS];
  logic                  axi_m_wlast   [NUM_PORTS];
  chip_axi_ht_data_t     axi_m_wdata   [NUM_PORTS];
  chip_axi_ht_wstrb_t    axi_m_wstrb   [NUM_PORTS];
  logic                  axi_m_wready  [NUM_PORTS];
  logic                  axi_m_bvalid  [NUM_PORTS];
  sdma_axi_ht_id_t       axi_m_bid     [NUM_PORTS];
  axi_resp_e             axi_m_bresp   [NUM_PORTS];
  logic                  axi_m_bready  [NUM_PORTS];
  logic                  axi_m_arvalid [NUM_PORTS];
  chip_axi_addr_t        axi_m_araddr  [NUM_PORTS];
  sdma_axi_ht_id_t       axi_m_arid    [NUM_PORTS];
  axi_len_t              axi_m_arlen   [NUM_PORTS];
  axi_size_e             axi_m_arsize  [NUM_PORTS];
  axi_burst_e            axi_m_arburst [NUM_PORTS];
  logic                  axi_m_arlock  [NUM_PORTS];
  axi_cache_e            axi_m_arcache [NUM_PORTS];
  axi_prot_t             axi_m_arprot  [NUM_PORTS];
  logic                  axi_m_arready [NUM_PORTS];
  logic                  axi_m_rvalid  [NUM_PORTS];
  logic                  axi_m_rlast   [NUM_PORTS];
  sdma_axi_ht_id_t       axi_m_rid     [NUM_PORTS];
  chip_axi_ht_data_t     axi_m_rdata   [NUM_PORTS];
  axi_resp_e             axi_m_rresp   [NUM_PORTS];
  logic                  axi_m_rready  [NUM_PORTS];

  logic [NUM_CHNLS-1:0] ts_start;
  logic [NUM_CHNLS-1:0] ts_end;

pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;

logic dma_clk;
logic dma_rst_n;

logic prn;
logic pde;
logic ret;

logic noc_clken;
logic noc_rst_n;
logic [3:0] noc_async_idle_req;
logic [3:0] noc_async_idle_ack;
logic [3:0] noc_async_idle_val;

logic [token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.max_num_prod-1:0] tok_prod_vld[token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];
logic [token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.max_num_prod-1:0] tok_prod_rdy[token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];
logic [token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.max_num_cons-1:0] tok_cons_vld[token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];
logic [token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.max_num_cons-1:0] tok_cons_rdy[token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.nr_loc_devs];

sdma_csr_reg_pkg::sdma_csr_reg2hw_t reg2hw;
sdma_csr_reg_pkg::sdma_csr_hw2reg_t hw2reg;

always_comb hw2reg.id = i_sdma_nr;

logic global_sync;

pctl
  #(
     .N_FAST_CLKS               (1),
     .N_RESETS                  (1),
     .N_MEM_PG                  (1),
     .N_FENCES                  (2),
     .N_THROTTLE_PINS           (1),
     .CLKRST_MATRIX             (1'b1),
     .PLL_CLK_IS_I_CLK          (1'b0),
     .NOC_RST_IDX               (0),
     .SYNC_CLK_IDX              (0),
     .AUTO_RESET_REMOVE         (1'b0),
     .paddr_t                   (chip_syscfg_addr_t),
     .pdata_t                   (chip_apb_syscfg_data_t),
     .pstrb_t                   (chip_apb_syscfg_strb_t)
  ) u_pctl
  (
    .i_clk                       (i_ref_clk),
    .i_ao_rst_n,
    .i_global_rst_n,
    .i_test_mode                 (test_mode),

    .i_pll_clk                   (i_clk),
    .o_partition_clk             (dma_clk),

    .o_partition_rst_n           (dma_rst_n),
    .o_ao_rst_sync_n             (),

    .o_noc_async_idle_req({o_noc_tok_async_idle_req, o_noc_async_idle_req}),
    .i_noc_async_idle_ack({i_noc_tok_async_idle_ack, i_noc_async_idle_ack}),
    .i_noc_async_idle_val({i_noc_tok_async_idle_val, i_noc_async_idle_val}),
    .o_noc_clken,
    .o_noc_rst_n,

    .o_int_shutdown_req(),
    .i_int_shutdown_ack(1'b1),

    .o_ret             (ret),
    .o_pde             (pde),
    .i_prn             (prn),

    .i_global_sync_async (i_inter_core_sync),
    .o_global_sync     (global_sync),

    .i_throttle        (i_clock_throttle),

    //////////////////////////////////////////////
    /// SYS_CFG Bus
    //////////////////////////////////////////////

    .i_cfg_apb4_s_paddr,
    .i_cfg_apb4_s_pwdata,
    .i_cfg_apb4_s_pwrite,
    .i_cfg_apb4_s_psel,
    .i_cfg_apb4_s_penable,
    .i_cfg_apb4_s_pstrb,
    .i_cfg_apb4_s_pprot,
    .o_cfg_apb4_s_pready,
    .o_cfg_apb4_s_prdata,
    .o_cfg_apb4_s_pslverr,

    .o_ao_csr_apb_req          (ao_csr_apb_req),
    .i_ao_csr_apb_rsp          (ao_csr_apb_rsp)
  );

  always_comb ao_csr_apb_rsp = '{ pslverr : 1'b1,
                                  prdata  : 32'h0,
                                  pready  : 1'b1 };

  //////////////////////////////////////////////////
  // Simple demux for config bus:
  logic [$clog2(SDMA_AXI_ENDPOINTS+1)-1:0] bus_sel_rd;
  logic [$clog2(SDMA_AXI_ENDPOINTS+1)-1:0] bus_sel_wr;

  aic_fabric_addr_decoder #(
    .AW(SDMA_CAPPED_AW+1),
    .CORE_ID_LSB(SDMA_CAPPED_AW),
    .NR_CORE_IDS(1),
    .CORE_IDS({1}), // prot[0] (privileged) set
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(SDMA_AXI_ENDPOINTS),
    .NR_REGIONS(SDMA_AXI_ENDPOINTS),
    .REGION_IS_CORE(SDMA_REGION_PRIV),
    .SKIP_CORE_CHECK_IF_NOT_CORE(1'b1), // don't check prot bit in address for non 'core'/prot regions
    .REGION_ST_ADDR(SDMA_REGION_ST_ADDR),
    .REGION_END_ADDR(SDMA_REGION_END_ADDR),
    .REGION_SLAVE_ID(SDMA_REGION_IDX)
  ) u_ext_decode_wr (
    .addr_in({i_axi_s_awprot[0], i_axi_s_awaddr[SDMA_CAPPED_AW-1:0]}),
    .core_id(1'b1), // check for privileged bit set in case of protected region ('core')

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(SDMA_CAPPED_AW+1),
    .CORE_ID_LSB(SDMA_CAPPED_AW),
    .NR_CORE_IDS(1),
    .CORE_IDS({1}), // prot[0] (privileged) set
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(SDMA_AXI_ENDPOINTS),
    .NR_REGIONS(SDMA_AXI_ENDPOINTS),
    .REGION_IS_CORE(SDMA_REGION_PRIV),
    .SKIP_CORE_CHECK_IF_NOT_CORE(1'b1), // don't check prot bit in address for non 'core'/prot regions
    .REGION_ST_ADDR(SDMA_REGION_ST_ADDR),
    .REGION_END_ADDR(SDMA_REGION_END_ADDR),
    .REGION_SLAVE_ID(SDMA_REGION_IDX)
  ) u_ext_decode_rd (
    .addr_in({i_axi_s_arprot[0], i_axi_s_araddr[SDMA_CAPPED_AW-1:0]}),
    .core_id(1'b1), // check for privileged bit set in case of protected region ('core')

    .sl_select(bus_sel_rd)
  );
  // AXI bus:
  logic [$bits(axi_resp_e)-1:0] axi_s_bresp_o, axi_s_rresp_o;
  always_comb o_axi_s_bresp = axi_resp_e'(axi_s_bresp_o);
  always_comb o_axi_s_rresp = axi_resp_e'(axi_s_rresp_o);
  simple_axi_demux #(
    .NR_MASTERS(SDMA_AXI_ENDPOINTS),
    .IDW($bits(sdma_axi_lt_id_t)),
    .AW($bits(chip_axi_addr_t)),
    .DW($bits(chip_axi_lt_data_t)),
    .BW($bits(axi_len_t)),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(8),
    .EXT_SEL(1)
  ) u_bus (
    .i_clk  (dma_clk),
    .i_rst_n(dma_rst_n),

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    // Master:
    // write address channel:
    .s_awvalid(i_axi_s_awvalid),
    .s_awaddr(i_axi_s_awaddr),
    .s_awid(i_axi_s_awid),
    .s_awlen(i_axi_s_awlen),
    .s_awsize(i_axi_s_awsize),
    .s_awburst(i_axi_s_awburst),
    .s_awlock(i_axi_s_awlock),
    .s_awcache(i_axi_s_awcache),
    .s_awprot(i_axi_s_awprot),
    .s_awready(o_axi_s_awready),

    // write data channel:
    .s_wvalid(i_axi_s_wvalid),
    .s_wdata (i_axi_s_wdata),
    .s_wstrb (i_axi_s_wstrb),
    .s_wlast (i_axi_s_wlast),
    .s_wready(o_axi_s_wready),

    // write response channel:
    .s_bvalid(o_axi_s_bvalid),
    .s_bid(o_axi_s_bid),
    .s_bresp(axi_s_bresp_o),
    .s_bready(i_axi_s_bready),

    // read address channel:
    .s_arvalid(i_axi_s_arvalid),
    .s_araddr(i_axi_s_araddr),
    .s_arid(i_axi_s_arid),
    .s_arlen(i_axi_s_arlen),
    .s_arsize(i_axi_s_arsize),
    .s_arburst(i_axi_s_arburst),
    .s_arlock(i_axi_s_arlock),
    .s_arcache(i_axi_s_arcache),
    .s_arprot(i_axi_s_arprot),
    .s_arready(o_axi_s_arready),

    // read response channel:
    .s_rvalid(o_axi_s_rvalid),
    .s_rid(o_axi_s_rid),
    .s_rdata(o_axi_s_rdata),
    .s_rresp(axi_s_rresp_o),
    .s_rlast(o_axi_s_rlast),
    .s_rready(i_axi_s_rready),

    // Slaves:
    // write address channel:
    .m_awvalid(axi_s_awvalid),
    .m_awaddr(axi_s_awaddr),
    .m_awid(axi_s_awid),
    .m_awlen(axi_s_awlen),
    .m_awsize(axi_s_awsize),
    .m_awburst(axi_s_awburst),
    .m_awlock(axi_s_awlock),
    .m_awcache(axi_s_awcache),
    .m_awprot(axi_s_awprot),
    .m_awready(axi_s_awready),

    // write data channel:
    .m_wvalid(axi_s_wvalid),
    .m_wdata(axi_s_wdata),
    .m_wstrb(axi_s_wstrb),
    .m_wlast(axi_s_wlast),
    .m_wready(axi_s_wready),

    // write response channel:
    .m_bvalid(axi_s_bvalid),
    .m_bid(axi_s_bid),
    .m_bresp(axi_s_bresp),
    .m_bready(axi_s_bready),

    // read address channel:
    .m_arvalid(axi_s_arvalid),
    .m_araddr(axi_s_araddr),
    .m_arid(axi_s_arid),
    .m_arlen(axi_s_arlen),
    .m_arsize(axi_s_arsize),
    .m_arburst(axi_s_arburst),
    .m_arlock(axi_s_arlock),
    .m_arcache(axi_s_arcache),
    .m_arprot(axi_s_arprot),
    .m_arready(axi_s_arready),

    // read response channel:
    .m_rvalid(axi_s_rvalid),
    .m_rid(axi_s_rid),
    .m_rdata(axi_s_rdata),
    .m_rresp(axi_s_rresp),
    .m_rlast(axi_s_rlast),
    .m_rready(axi_s_rready)
  );
  ///////////////////////////////////////////

  dma
  #(
     .NUM_PORTS         ( NUM_PORTS ),
     .NUM_CHNLS         ( NUM_CHNLS ),
     .DMA_N_BUF_IDXS    ( 256 ),
     .DMA_N_IMPL_BUF_IDXS( 256 ),
     .NR_TOK_PROD       ( NR_TOK_PROD ),
     .NR_TOK_CONS       ( NR_TOK_CONS ),
     .NR_TOP_TOK_PROD   ( NR_TOP_TOK_PROD ),
     .NR_TOP_TOK_CONS   ( NR_TOP_TOK_CONS ),
     .dma_axi_s_data_t  (chip_axi_lt_data_t),
     .dma_axi_s_addr_t  (chip_axi_addr_t),
     .dma_axi_s_id_t    (sdma_axi_lt_id_t),
     .dma_axi_m_data_t  (chip_axi_ht_data_t),
     .dma_axi_m_addr_t  (chip_axi_addr_t),
     .dma_axi_m_id_t    (sdma_axi_ht_id_t)
  ) u_dma (
    // Clock and reset signals
     .i_clk            (dma_clk),
     .i_rst_n          (dma_rst_n),

    .i_impl            (axe_tcl_sram_pkg::impl_inp_t'{
                         //TODO: @(matt.morris) Remove this once we update the structure to remove the margin signals
                         default: '0,
                         ret    : ret,
                         pde    : pde,
                         se     : scan_en
                    }),
    .o_impl            (prn),

     .o_int,

    .o_tok_prod_vld(tok_prod_vld),
    .i_tok_prod_rdy(tok_prod_rdy),
    .i_tok_cons_vld(tok_cons_vld),
    .o_tok_cons_rdy(tok_cons_rdy),

    .o_ts_start      (ts_start),
    .o_ts_end        (ts_end),
    .o_acd_sync(),  // ASO-UNUSED_OUTPUT: Not used in SDMA
    .o_obs(), // ASO-UNUSED_OUTPUT: Not used in SDMA

    // AXI 4 Configuration Interface
    // AXI write address channel
    .i_axi_s_awvalid(axi_s_awvalid[dma_idx]),
    .i_axi_s_awaddr(axi_s_awaddr[dma_idx]),
    .i_axi_s_awid(axi_s_awid[dma_idx]),
    .i_axi_s_awlen(axi_s_awlen[dma_idx]),
    .i_axi_s_awsize(axi_s_awsize[dma_idx]),
    .i_axi_s_awburst(axi_s_awburst[dma_idx]),
    .i_axi_s_awlock(axi_s_awlock[dma_idx]),
    .i_axi_s_awcache(axi_s_awcache[dma_idx]),
    .i_axi_s_awprot(axi_s_awprot[dma_idx]),
    .o_axi_s_awready(axi_s_awready[dma_idx]),
    // AXI write data channel
    .i_axi_s_wvalid(axi_s_wvalid[dma_idx]),
    .i_axi_s_wlast(axi_s_wlast[dma_idx]),
    .i_axi_s_wdata(axi_s_wdata[dma_idx]),
    .i_axi_s_wstrb(axi_s_wstrb[dma_idx]),
    .o_axi_s_wready(axi_s_wready[dma_idx]),
    // AXI write response channel
    .o_axi_s_bvalid(axi_s_bvalid[dma_idx]),
    .o_axi_s_bid(axi_s_bid[dma_idx]),
    .o_axi_s_bresp(axi_s_bresp[dma_idx]),
    .i_axi_s_bready(axi_s_bready[dma_idx]),
    // AXI read address channel
    .i_axi_s_arvalid(axi_s_arvalid[dma_idx]),
    .i_axi_s_araddr(axi_s_araddr[dma_idx]),
    .i_axi_s_arid(axi_s_arid[dma_idx]),
    .i_axi_s_arlen(axi_s_arlen[dma_idx]),
    .i_axi_s_arsize(axi_s_arsize[dma_idx]),
    .i_axi_s_arburst(axi_s_arburst[dma_idx]),
    .i_axi_s_arlock(axi_s_arlock[dma_idx]),
    .i_axi_s_arcache(axi_s_arcache[dma_idx]),
    .i_axi_s_arprot(axi_s_arprot[dma_idx]),
    .o_axi_s_arready(axi_s_arready[dma_idx]),
    // AXI read data/response channel
    .o_axi_s_rvalid(axi_s_rvalid[dma_idx]),
    .o_axi_s_rlast(axi_s_rlast[dma_idx]),
    .o_axi_s_rid(axi_s_rid[dma_idx]),
    .o_axi_s_rdata(axi_s_rdata[dma_idx]),
    .o_axi_s_rresp(axi_s_rresp[dma_idx]),
    .i_axi_s_rready(axi_s_rready[dma_idx]),

    // AXI 4 Data Ports
    // AXI write address channel
    .o_axi_m_awvalid (axi_m_awvalid),
    .o_axi_m_awaddr  (axi_m_awaddr),
    .o_axi_m_awid    (axi_m_awid),
    .o_axi_m_awlen   (axi_m_awlen),
    .o_axi_m_awsize  (axi_m_awsize),
    .o_axi_m_awburst (axi_m_awburst),
    .o_axi_m_awlock  (axi_m_awlock),
    .o_axi_m_awcache (axi_m_awcache),
    .o_axi_m_awprot  (axi_m_awprot),
    .i_axi_m_awready (axi_m_awready),
    // AXI write data channel
    .o_axi_m_wvalid  (axi_m_wvalid),
    .o_axi_m_wlast   (axi_m_wlast),
    .o_axi_m_wdata   (axi_m_wdata),
    .o_axi_m_wstrb   (axi_m_wstrb),
    .i_axi_m_wready  (axi_m_wready),
    // AXI write response channel
    .i_axi_m_bvalid  (axi_m_bvalid),
    .i_axi_m_bid     (axi_m_bid),
    .i_axi_m_bresp   (axi_m_bresp),
    .o_axi_m_bready  (axi_m_bready),
    // AXI read address channel
    .o_axi_m_arvalid (axi_m_arvalid),
    .o_axi_m_araddr  (axi_m_araddr),
    .o_axi_m_arid    (axi_m_arid),
    .o_axi_m_arlen   (axi_m_arlen),
    .o_axi_m_arsize  (axi_m_arsize),
    .o_axi_m_arburst (axi_m_arburst),
    .o_axi_m_arlock  (axi_m_arlock),
    .o_axi_m_arcache (axi_m_arcache),
    .o_axi_m_arprot  (axi_m_arprot),
    .i_axi_m_arready (axi_m_arready),
    // AXI read data/response channel
    .i_axi_m_rvalid  (axi_m_rvalid),
    .i_axi_m_rlast   (axi_m_rlast),
    .i_axi_m_rid     (axi_m_rid),
    .i_axi_m_rdata   (axi_m_rdata),
    .i_axi_m_rresp   (axi_m_rresp),
    .o_axi_m_rready  (axi_m_rready)

  );


  // PORT 0
  // AXI write address channel
  always_comb o_axi_m0_awvalid = axi_m_awvalid[0];
  always_comb o_axi_m0_awaddr  = axi_m_awaddr[0];
  always_comb o_axi_m0_awid    = axi_m_awid[0];
  always_comb o_axi_m0_awlen   = axi_m_awlen[0];
  always_comb o_axi_m0_awsize  = axi_m_awsize[0];
  always_comb o_axi_m0_awburst = axi_m_awburst[0];
  always_comb o_axi_m0_awlock  = axi_m_awlock[0];
  always_comb o_axi_m0_awcache = axi_m_awcache[0];
  always_comb o_axi_m0_awprot  = axi_m_awprot[0];
  always_comb axi_m_awready[0] = i_axi_m0_awready;
  // AXI write data channel
  always_comb o_axi_m0_wvalid  = axi_m_wvalid[0];
  always_comb o_axi_m0_wlast   = axi_m_wlast[0];
  always_comb o_axi_m0_wdata   = axi_m_wdata[0];
  always_comb o_axi_m0_wstrb   = axi_m_wstrb[0];
  always_comb axi_m_wready[0]  = i_axi_m0_wready;
  // AXI write response channel
  always_comb axi_m_bvalid[0]  = i_axi_m0_bvalid;
  always_comb axi_m_bid[0]     = i_axi_m0_bid;
  always_comb axi_m_bresp[0]   = i_axi_m0_bresp;
  always_comb o_axi_m0_bready  = axi_m_bready[0];
  // AXI read address channel
  always_comb o_axi_m0_arvalid = axi_m_arvalid[0];
  always_comb o_axi_m0_araddr  = axi_m_araddr[0];
  always_comb o_axi_m0_arid    = axi_m_arid[0];
  always_comb o_axi_m0_arlen   = axi_m_arlen[0];
  always_comb o_axi_m0_arsize  = axi_m_arsize[0];
  always_comb o_axi_m0_arburst = axi_m_arburst[0];
  always_comb o_axi_m0_arlock  = axi_m_arlock[0];
  always_comb o_axi_m0_arcache = axi_m_arcache[0];
  always_comb o_axi_m0_arprot  = axi_m_arprot[0];
  always_comb axi_m_arready[0] = i_axi_m0_arready;
  // AXI read data/response channel
  always_comb axi_m_rvalid[0]  = i_axi_m0_rvalid;
  always_comb axi_m_rlast[0]   = i_axi_m0_rlast;
  always_comb axi_m_rid[0]     = i_axi_m0_rid;
  always_comb axi_m_rdata[0]   = i_axi_m0_rdata;
  always_comb axi_m_rresp[0]   = i_axi_m0_rresp;
  always_comb o_axi_m0_rready  = axi_m_rready[0];
  // PORT 1
  // AXI write address channel
  always_comb o_axi_m1_awvalid = axi_m_awvalid[1];
  always_comb o_axi_m1_awaddr  = axi_m_awaddr[1];
  always_comb o_axi_m1_awid    = axi_m_awid[1];
  always_comb o_axi_m1_awlen   = axi_m_awlen[1];
  always_comb o_axi_m1_awsize  = axi_m_awsize[1];
  always_comb o_axi_m1_awburst = axi_m_awburst[1];
  always_comb o_axi_m1_awlock  = axi_m_awlock[1];
  always_comb o_axi_m1_awcache = axi_m_awcache[1];
  always_comb o_axi_m1_awprot  = axi_m_awprot[1];
  always_comb axi_m_awready[1] = i_axi_m1_awready;
  // AXI write data channel
  always_comb o_axi_m1_wvalid  = axi_m_wvalid[1];
  always_comb o_axi_m1_wlast   = axi_m_wlast[1];
  always_comb o_axi_m1_wdata   = axi_m_wdata[1];
  always_comb o_axi_m1_wstrb   = axi_m_wstrb[1];
  always_comb axi_m_wready[1]  = i_axi_m1_wready;
  // AXI write response channel
  always_comb axi_m_bvalid[1]  = i_axi_m1_bvalid;
  always_comb axi_m_bid[1]     = i_axi_m1_bid;
  always_comb axi_m_bresp[1]   = i_axi_m1_bresp;
  always_comb o_axi_m1_bready  = axi_m_bready[1];
  // AXI read address channel
  always_comb o_axi_m1_arvalid = axi_m_arvalid[1];
  always_comb o_axi_m1_araddr  = axi_m_araddr[1];
  always_comb o_axi_m1_arid    = axi_m_arid[1];
  always_comb o_axi_m1_arlen   = axi_m_arlen[1];
  always_comb o_axi_m1_arsize  = axi_m_arsize[1];
  always_comb o_axi_m1_arburst = axi_m_arburst[1];
  always_comb o_axi_m1_arlock  = axi_m_arlock[1];
  always_comb o_axi_m1_arcache = axi_m_arcache[1];
  always_comb o_axi_m1_arprot  = axi_m_arprot[1];
  always_comb axi_m_arready[1] = i_axi_m1_arready;
  // AXI read data/response channel
  always_comb axi_m_rvalid[1]  = i_axi_m1_rvalid;
  always_comb axi_m_rlast[1]   = i_axi_m1_rlast;
  always_comb axi_m_rid[1]     = i_axi_m1_rid;
  always_comb axi_m_rdata[1]   = i_axi_m1_rdata;
  always_comb axi_m_rresp[1]   = i_axi_m1_rresp;
  always_comb o_axi_m1_rready  = axi_m_rready[1];

  ///////////////////////////////////////
  // CSR:

  sdma_csr_reg_pkg::axi_b_ch_d2h_t csr_axi_b;
  sdma_csr_reg_pkg::axi_r_ch_d2h_t csr_axi_r;

  always_comb axi_s_bid[csr_idx] = csr_axi_b.id;
  always_comb axi_s_bresp[csr_idx] = axi_resp_e'(csr_axi_b.resp);
  always_comb axi_s_bvalid[csr_idx] = csr_axi_b.valid;

  always_comb axi_s_rid[csr_idx] = csr_axi_r.id;
  always_comb axi_s_rdata[csr_idx] = csr_axi_r.data;
  always_comb axi_s_rresp[csr_idx] = axi_resp_e'(csr_axi_r.resp);
  always_comb axi_s_rlast[csr_idx] = csr_axi_r.last;
  always_comb axi_s_rvalid[csr_idx] = csr_axi_r.valid;
  sdma_csr_reg_top u_csr (
    .clk_i(dma_clk),
    .rst_ni(dma_rst_n),

    .axi_aw_i(sdma_csr_reg_pkg::axi_a_ch_h2d_t'{
      id: axi_s_awid[csr_idx],
      addr: axi_s_awaddr[csr_idx],
      len: axi_s_awlen[csr_idx],
      size: axi_s_awsize[csr_idx],
      burst: axi_s_awburst[csr_idx],
      valid: axi_s_awvalid[csr_idx]
    }),
    .axi_awready(axi_s_awready[csr_idx]),
    // Write  Data Channel
    .axi_w_i(sdma_csr_reg_pkg::axi_w_ch_h2d_t'{
      data: axi_s_wdata[csr_idx],
      strb: axi_s_wstrb[csr_idx],
      last: axi_s_wlast[csr_idx],
      valid: axi_s_wvalid[csr_idx]
    }),
    .axi_wready(axi_s_wready[csr_idx]),
    // Write Response Channel
    .axi_b_o(csr_axi_b),
    .axi_bready(axi_s_bready[csr_idx]),
    // Read Address Channel
    .axi_ar_i(sdma_csr_reg_pkg::axi_a_ch_h2d_t'{
      id: axi_s_arid[csr_idx],
      addr: axi_s_araddr[csr_idx],
      len: axi_s_arlen[csr_idx],
      size: axi_s_arsize[csr_idx],
      burst: axi_s_arburst[csr_idx],
      valid: axi_s_arvalid[csr_idx]
    }),
    .axi_arready(axi_s_arready[csr_idx]),
    // Read Data Channel
    .axi_r_o(csr_axi_r),
    .axi_rready(axi_s_rready[csr_idx]),

    .reg2hw(reg2hw),
    .hw2reg(hw2reg),

    .devmode_i(1'b1)
  );
  ///////////////////////////////////////
  // TimestampLogger:
  logic global_sync_q, global_sync_pulse;
  logic global_sync_timestamplogger;

  always_comb global_sync_pulse = global_sync ^ global_sync_q;
  always_comb global_sync_timestamplogger = global_sync_pulse; // TODO Sander/Matt: attach CSR enable to it: pulse & reg2hw.global_sync_control.en.q
  always_ff @( posedge dma_clk or negedge dma_rst_n ) begin
    if (!dma_rst_n)
      global_sync_q <= 1'b0;
    else if (global_sync_pulse)
      global_sync_q <= global_sync;
  end

  logic [$bits(axi_resp_e)-1:0] axi_s_bresp_tl, axi_s_rresp_tl;
  always_comb axi_s_bresp[ts_idx] = axi_resp_e'(axi_s_bresp_tl);
  always_comb axi_s_rresp[ts_idx] = axi_resp_e'(axi_s_rresp_tl);
  timestamp_logger_sdma #(
    .AxiSIdWidth($bits(sdma_axi_lt_id_t)),
    .AxiMIdWidth($bits(sdma_axi_lt_id_t)),
    .AxiAddrWidth($bits(chip_axi_addr_t)),
    .AxiDataWidth($bits(chip_axi_lt_data_t)),

    // default address regions for CSR, and MEM:
    .REGION_ST_ADDR({SDMA_TIMESTAMP_CSR_ST_ADDR, SDMA_TIMESTAMP_MEM_ST_ADDR}),
    .REGION_END_ADDR({SDMA_TIMESTAMP_CSR_END_ADDR, SDMA_TIMESTAMP_MEM_END_ADDR})
  ) u_timestamp_logger (
    .i_clk(dma_clk),
    .i_rst_n(dma_rst_n),

    .i_scan_en(scan_en),

    .i_sync_start(global_sync_timestamplogger & reg2hw.global_sync_control.q),

    .i_ts_start(ts_start),
    .i_ts_end(ts_end),

    ///// AXI subordinate:
    // Write Address Channel
    .i_axi_s_aw_id(axi_s_awid[ts_idx]),
    .i_axi_s_aw_addr(axi_s_awaddr[ts_idx]),
    .i_axi_s_aw_len(axi_s_awlen[ts_idx]),
    .i_axi_s_aw_size(axi_s_awsize[ts_idx]),
    .i_axi_s_aw_burst(axi_s_awburst[ts_idx]),
    .i_axi_s_aw_valid(axi_s_awvalid[ts_idx]),
    .o_axi_s_aw_ready(axi_s_awready[ts_idx]),
    // Write  Data Channel
    .i_axi_s_w_data(axi_s_wdata[ts_idx]),
    .i_axi_s_w_strb(axi_s_wstrb[ts_idx]),
    .i_axi_s_w_last(axi_s_wlast[ts_idx]),
    .i_axi_s_w_valid(axi_s_wvalid[ts_idx]),
    .o_axi_s_w_ready(axi_s_wready[ts_idx]),
    // Write Response Channel
    .o_axi_s_b_id(axi_s_bid[ts_idx]),
    .o_axi_s_b_resp(axi_s_bresp_tl),
    .o_axi_s_b_valid(axi_s_bvalid[ts_idx]),
    .i_axi_s_b_ready(axi_s_bready[ts_idx]),
    // Read Address Channel
    .i_axi_s_ar_id(axi_s_arid[ts_idx]),
    .i_axi_s_ar_addr(axi_s_araddr[ts_idx]),
    .i_axi_s_ar_len(axi_s_arlen[ts_idx]),
    .i_axi_s_ar_size(axi_s_arsize[ts_idx]),
    .i_axi_s_ar_burst(axi_s_arburst[ts_idx]),
    .i_axi_s_ar_valid(axi_s_arvalid[ts_idx]),
    .o_axi_s_ar_ready(axi_s_arready[ts_idx]),
    // Read Data Channel
    .o_axi_s_r_id(axi_s_rid[ts_idx]),
    .o_axi_s_r_data(axi_s_rdata[ts_idx]),
    .o_axi_s_r_resp(axi_s_rresp_tl),
    .o_axi_s_r_last(axi_s_rlast[ts_idx]),
    .o_axi_s_r_valid(axi_s_rvalid[ts_idx]),
    .i_axi_s_r_ready(axi_s_rready[ts_idx]),

    ///// AXI manager:
    // Write Address Channel
    .o_axi_m_aw_id(o_axi_trc_m_awid),
    .o_axi_m_aw_addr(o_axi_trc_m_awaddr),
    .o_axi_m_aw_len(o_axi_trc_m_awlen),
    .o_axi_m_aw_size(o_axi_trc_m_awsize),
    .o_axi_m_aw_burst(o_axi_trc_m_awburst),
    .o_axi_m_aw_valid(o_axi_trc_m_awvalid),
    .i_axi_m_aw_ready(i_axi_trc_m_awready),
    // Write  Data Channel
    .o_axi_m_w_data(o_axi_trc_m_wdata),
    .o_axi_m_w_strb(o_axi_trc_m_wstrb),
    .o_axi_m_w_last(o_axi_trc_m_wlast),
    .o_axi_m_w_valid(o_axi_trc_m_wvalid),
    .i_axi_m_w_ready(i_axi_trc_m_wready),
    // Write Response Channel
    .i_axi_m_b_id(i_axi_trc_m_bid),
    .i_axi_m_b_resp(i_axi_trc_m_bresp),
    .i_axi_m_b_valid(i_axi_trc_m_bvalid),
    .o_axi_m_b_ready(o_axi_trc_m_bready),
    // Read Address Channel
    .o_axi_m_ar_id(o_axi_trc_m_arid),
    .o_axi_m_ar_addr(o_axi_trc_m_araddr),
    .o_axi_m_ar_len(o_axi_trc_m_arlen),
    .o_axi_m_ar_size(o_axi_trc_m_arsize),
    .o_axi_m_ar_burst(o_axi_trc_m_arburst),
    .o_axi_m_ar_valid(o_axi_trc_m_arvalid),
    .i_axi_m_ar_ready(i_axi_trc_m_arready),
    // Read Data Channel
    .i_axi_m_r_id(i_axi_trc_m_rid),
    .i_axi_m_r_data(i_axi_trc_m_rdata),
    .i_axi_m_r_resp(i_axi_trc_m_rresp),
    .i_axi_m_r_last(i_axi_trc_m_rlast),
    .i_axi_m_r_valid(i_axi_trc_m_rvalid),
    .o_axi_m_r_ready(o_axi_trc_m_rready)
  );
  // TimestampLogger doesn't support / use lock, cache, qos or prot:
  always_comb o_axi_trc_m_awlock = '0;
  always_comb o_axi_trc_m_awcache = axi_cache_e'('0);
  always_comb o_axi_trc_m_awqos = '0;
  always_comb o_axi_trc_m_awprot = '0;
  always_comb o_axi_trc_m_arlock = '0;
  always_comb o_axi_trc_m_arcache = axi_cache_e'('0);
  always_comb o_axi_trc_m_arqos = '0;
  always_comb o_axi_trc_m_arprot = '0;

  //////////////////////////
  // TokenMgr:
  token_manager_pkg::tokmgr_uid_all_t tok_uid_to_vuid, tok_vuid_to_uid;
  always_comb begin
    tok_uid_to_vuid = '0; // rsvd fields to zero
    tok_vuid_to_uid = '0; // rsvd fields to zero

    tok_uid_to_vuid.aic0  = reg2hw.uid_to_vuid_aic0;
    tok_uid_to_vuid.aic1  = reg2hw.uid_to_vuid_aic1;
    tok_uid_to_vuid.aic2  = reg2hw.uid_to_vuid_aic2;
    tok_uid_to_vuid.aic3  = reg2hw.uid_to_vuid_aic3;
    tok_uid_to_vuid.aic4  = reg2hw.uid_to_vuid_aic4;
    tok_uid_to_vuid.aic5  = reg2hw.uid_to_vuid_aic5;
    tok_uid_to_vuid.aic6  = reg2hw.uid_to_vuid_aic6;
    tok_uid_to_vuid.aic7  = reg2hw.uid_to_vuid_aic7;
    tok_uid_to_vuid.sdma0 = reg2hw.uid_to_vuid_sdma0;
    tok_uid_to_vuid.sdma1 = reg2hw.uid_to_vuid_sdma1;
    tok_uid_to_vuid.apu   = reg2hw.uid_to_vuid_apu;

    tok_vuid_to_uid.aic0  = reg2hw.vuid_to_uid_aic0;
    tok_vuid_to_uid.aic1  = reg2hw.vuid_to_uid_aic1;
    tok_vuid_to_uid.aic2  = reg2hw.vuid_to_uid_aic2;
    tok_vuid_to_uid.aic3  = reg2hw.vuid_to_uid_aic3;
    tok_vuid_to_uid.aic4  = reg2hw.vuid_to_uid_aic4;
    tok_vuid_to_uid.aic5  = reg2hw.vuid_to_uid_aic5;
    tok_vuid_to_uid.aic6  = reg2hw.vuid_to_uid_aic6;
    tok_vuid_to_uid.aic7  = reg2hw.vuid_to_uid_aic7;
    tok_vuid_to_uid.sdma0 = reg2hw.vuid_to_uid_sdma0;
    tok_vuid_to_uid.sdma1 = reg2hw.vuid_to_uid_sdma1;
    tok_vuid_to_uid.apu   = reg2hw.vuid_to_uid_apu;
  end

  token_manager_sdma_csr_reg_pkg::axi_b_ch_d2h_t tok_mgr_axi_b;
  token_manager_sdma_csr_reg_pkg::axi_r_ch_d2h_t tok_mgr_axi_r;

  always_comb axi_s_bid[tok_idx] = tok_mgr_axi_b.id;
  always_comb axi_s_bresp[tok_idx] = axi_resp_e'(tok_mgr_axi_b.resp);
  always_comb axi_s_bvalid[tok_idx] = tok_mgr_axi_b.valid;

  always_comb axi_s_rid[tok_idx] = tok_mgr_axi_r.id;
  always_comb axi_s_rdata[tok_idx] = tok_mgr_axi_r.data;
  always_comb axi_s_rresp[tok_idx] = axi_resp_e'(tok_mgr_axi_r.resp);
  always_comb axi_s_rlast[tok_idx] = tok_mgr_axi_r.last;
  always_comb axi_s_rvalid[tok_idx] = tok_mgr_axi_r.valid;

  chip_pkg::chip_ocpl_token_addr_t tok_prod_ocpl_m_maddr;
  logic                            tok_prod_ocpl_m_mcmd;
  logic                            tok_prod_ocpl_m_scmdaccept;
  chip_pkg::chip_ocpl_token_data_t tok_prod_ocpl_m_mdata;

  chip_pkg::chip_ocpl_token_addr_t tok_cons_ocpl_s_maddr;
  logic                            tok_cons_ocpl_s_mcmd;
  logic                            tok_cons_ocpl_s_scmdaccept;
  chip_pkg::chip_ocpl_token_data_t tok_cons_ocpl_s_mdata;

  ocp_lite_cut #(
    .addr_t(logic [chip_pkg::CHIP_OCPL_TOKEN_ADDR_W-1:0]),
    .data_t(logic [chip_pkg::CHIP_OCPL_TOKEN_DATA_W-1:0])
  ) i_tok_prod_ocpl_m_spill_1 (
    .i_clk          (dma_clk),
    .i_rst_n        (dma_rst_n),
    .i_s_mcmd       (tok_prod_ocpl_m_mcmd),
    .i_s_maddr      (tok_prod_ocpl_m_maddr),
    .i_s_mdata      (tok_prod_ocpl_m_mdata),
    .o_s_scmd_accept(tok_prod_ocpl_m_scmdaccept),
    .o_m_mcmd       (o_tok_prod_ocpl_m_mcmd),
    .o_m_maddr      (o_tok_prod_ocpl_m_maddr),
    .o_m_mdata      (o_tok_prod_ocpl_m_mdata),
    .i_m_scmd_accept(i_tok_prod_ocpl_m_scmdaccept)
  );

  ocp_lite_cut #(
    .addr_t(logic [chip_pkg::CHIP_OCPL_TOKEN_ADDR_W-1:0]),
    .data_t(logic [chip_pkg::CHIP_OCPL_TOKEN_DATA_W-1:0])
  ) i_tok_cons_ocpl_s_spill_1 (
    .i_clk          (dma_clk),
    .i_rst_n        (dma_rst_n),
    .i_s_mcmd       (i_tok_cons_ocpl_s_mcmd),
    .i_s_maddr      (i_tok_cons_ocpl_s_maddr),
    .i_s_mdata      (i_tok_cons_ocpl_s_mdata),
    .o_s_scmd_accept(o_tok_cons_ocpl_s_scmdaccept),
    .o_m_mcmd       (tok_cons_ocpl_s_mcmd),
    .o_m_maddr      (tok_cons_ocpl_s_maddr),
    .o_m_mdata      (tok_cons_ocpl_s_mdata),
    .i_m_scmd_accept(tok_cons_ocpl_s_scmdaccept)
  );

  token_manager_sdma u_token_manager (
    .i_clk(dma_clk),
    .i_rst_n(dma_rst_n),

    // top info:
    .i_sdma_nr(i_sdma_nr),
    // UID - VUID:
    .i_uid_to_vuid(tok_uid_to_vuid),
    // VUID - UID:
    .i_vuid_to_uid(tok_vuid_to_uid),

    // Top connection via OCPL:
    .o_tok_prod_ocpl_m_maddr(tok_prod_ocpl_m_maddr),
    .o_tok_prod_ocpl_m_mcmd (tok_prod_ocpl_m_mcmd),
    .i_tok_prod_ocpl_m_scmdaccept (tok_prod_ocpl_m_scmdaccept),
    .o_tok_prod_ocpl_m_mdata(tok_prod_ocpl_m_mdata),

    .i_tok_cons_ocpl_s_maddr(tok_cons_ocpl_s_maddr),
    .i_tok_cons_ocpl_s_mcmd(tok_cons_ocpl_s_mcmd),
    .o_tok_cons_ocpl_s_scmdaccept(tok_cons_ocpl_s_scmdaccept),
    .i_tok_cons_ocpl_s_mdata(tok_cons_ocpl_s_mdata),

      // local connections for top:
    .i_top_prod_valid(tok_prod_vld),
    .o_top_prod_ready(tok_prod_rdy),

    .o_top_cons_valid(tok_cons_vld),
    .i_top_cons_ready(tok_cons_rdy),

    ///// AXI slave:
    // Write Address Channel
    .i_axi_s_aw(token_manager_sdma_csr_reg_pkg::axi_a_ch_h2d_t'{
      id: axi_s_awid[tok_idx],
      addr: axi_s_awaddr[tok_idx],
      len: axi_s_awlen[tok_idx],
      size: axi_s_awsize[tok_idx],
      burst: axi_s_awburst[tok_idx],
      valid: axi_s_awvalid[tok_idx]
    }),
    .o_axi_s_aw_ready(axi_s_awready[tok_idx]),
    // Write  Data Channel
    .i_axi_s_w(token_manager_sdma_csr_reg_pkg::axi_w_ch_h2d_t'{
      data: axi_s_wdata[tok_idx],
      strb: axi_s_wstrb[tok_idx],
      last: axi_s_wlast[tok_idx],
      valid: axi_s_wvalid[tok_idx]
    }),
    .o_axi_s_w_ready(axi_s_wready[tok_idx]),
    // Write Response Channel
    .o_axi_s_b(tok_mgr_axi_b),
    .i_axi_s_b_ready(axi_s_bready[tok_idx]),
    // Read Address Channel
    .i_axi_s_ar(token_manager_sdma_csr_reg_pkg::axi_a_ch_h2d_t'{
      id: axi_s_arid[tok_idx],
      addr: axi_s_araddr[tok_idx],
      len: axi_s_arlen[tok_idx],
      size: axi_s_arsize[tok_idx],
      burst: axi_s_arburst[tok_idx],
      valid: axi_s_arvalid[tok_idx]
    }),
    .o_axi_s_ar_ready(axi_s_arready[tok_idx]),
    // Read Data Channel
    .o_axi_s_r(tok_mgr_axi_r),
    .i_axi_s_r_ready(axi_s_rready[tok_idx]),

    // interrupt:
    .o_irq() // TODO Sander/Matt: attach somewhere, CSR?
  );
endmodule
