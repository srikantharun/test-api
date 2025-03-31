// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Implementation of L2 Europa
///
module l2_p
    import chip_pkg::*;
    import axi_pkg::*;
    import l2_p_pkg::*;
  (
    /// Fast Clock, positive edge triggered
    input   wire                  i_clk,
    /// APB Clock, positive edge triggered
    input   wire                  i_ref_clk,
    /// Asynchronous POR / always On reset, active low
    input   wire                  i_ao_rst_n,
    /// Asynchronous global reset, active low
    input   wire                  i_global_rst_n,
    /// Synchronous NoC reset, active low
    output  wire                  o_noc_rst_n,

    /// Isolation interface
    output logic                  o_noc_async_idle_req,
    input  logic                  i_noc_async_idle_ack,
    input  logic                  i_noc_async_idle_val,
    output logic                  o_noc_clken,

    // AXI Interface
    // AW channel
    input  chip_axi_addr_t        i_ht_axi_s_awaddr,
    input  l2_targ_ht_axi_id_t    i_ht_axi_s_awid,
    input  axi_len_t              i_ht_axi_s_awlen,
    input  axi_size_t             i_ht_axi_s_awsize,
    input  axi_burst_t            i_ht_axi_s_awburst,
    input  axi_cache_t            i_ht_axi_s_awcache,
    input  axi_prot_t             i_ht_axi_s_awprot,
    input  logic                  i_ht_axi_s_awlock,
    input  axi_qos_t              i_ht_axi_s_awqos,
    input  axi_region_t           i_ht_axi_s_awregion,
    input  chip_axi_ht_awuser_t   i_ht_axi_s_awuser,
    input  logic                  i_ht_axi_s_awvalid,
    output logic                  o_ht_axi_s_awready,
    // W channel
    input  chip_axi_ht_data_t     i_ht_axi_s_wdata,
    input  chip_axi_ht_wstrb_t    i_ht_axi_s_wstrb,
    input  logic                  i_ht_axi_s_wlast,
    input  chip_axi_ht_wuser_t    i_ht_axi_s_wuser,
    input  logic                  i_ht_axi_s_wvalid,
    output logic                  o_ht_axi_s_wready,
    // B channel
    output logic                  o_ht_axi_s_bvalid,
    output l2_targ_ht_axi_id_t    o_ht_axi_s_bid,
    output chip_axi_ht_buser_t    o_ht_axi_s_buser,
    output axi_resp_t             o_ht_axi_s_bresp,
    input  logic                  i_ht_axi_s_bready,
    // AR channel
    input  chip_axi_addr_t        i_ht_axi_s_araddr,
    input  l2_targ_ht_axi_id_t    i_ht_axi_s_arid,
    input  axi_len_t              i_ht_axi_s_arlen,
    input  axi_size_t             i_ht_axi_s_arsize,
    input  axi_burst_t            i_ht_axi_s_arburst,
    input  axi_cache_t            i_ht_axi_s_arcache,
    input  axi_prot_t             i_ht_axi_s_arprot,
    input  axi_qos_t              i_ht_axi_s_arqos,
    input  axi_region_t           i_ht_axi_s_arregion,
    input  chip_axi_ht_aruser_t   i_ht_axi_s_aruser,
    input  logic                  i_ht_axi_s_arlock,
    input  logic                  i_ht_axi_s_arvalid,
    output logic                  o_ht_axi_s_arready,
    // R channel
    output logic                  o_ht_axi_s_rvalid,
    output logic                  o_ht_axi_s_rlast,
    output l2_targ_ht_axi_id_t    o_ht_axi_s_rid,
    output chip_axi_ht_data_t     o_ht_axi_s_rdata,
    output chip_axi_ht_ruser_t    o_ht_axi_s_ruser,
    output axi_resp_t             o_ht_axi_s_rresp,
    input  logic                  i_ht_axi_s_rready,
    // APB
    input  chip_syscfg_addr_t     i_cfg_apb4_s_paddr,
    input  chip_apb_syscfg_data_t i_cfg_apb4_s_pwdata,
    input  logic                  i_cfg_apb4_s_pwrite,
    input  logic                  i_cfg_apb4_s_psel,
    input  logic                  i_cfg_apb4_s_penable,
    input  chip_apb_syscfg_strb_t i_cfg_apb4_s_pstrb,
    input  logic          [3-1:0] i_cfg_apb4_s_pprot,
    output logic                  o_cfg_apb4_s_pready,
    output chip_apb_syscfg_data_t o_cfg_apb4_s_prdata,
    output logic                  o_cfg_apb4_s_pslverr,
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
  // --------------------------------------------------------------
  // Signals
  // --------------------------------------------------------------
  // AXI Interface
  // AW channel
  chip_axi_addr_t        l2_axi_awaddr;
  l2_targ_ht_axi_id_t    l2_axi_awid;
  axi_len_t              l2_axi_awlen;
  axi_size_t             l2_axi_awsize;
  axi_burst_t            l2_axi_awburst;
  axi_cache_t            l2_axi_awcache;
  axi_prot_t             l2_axi_awprot;
  logic                  l2_axi_awlock;
  logic                  l2_axi_awvalid;
  logic                  l2_axi_awready;
  // W channel
  chip_axi_ht_data_t     l2_axi_wdata;
  chip_axi_ht_wstrb_t    l2_axi_wstrb;
  logic                  l2_axi_wlast;
  logic                  l2_axi_wvalid;
  logic                  l2_axi_wready;
  // B channel
  logic                  l2_axi_bvalid;
  l2_targ_ht_axi_id_t    l2_axi_bid;
  axi_resp_t             l2_axi_bresp;
  logic                  l2_axi_bready;
  // AR channel
  chip_axi_addr_t        l2_axi_araddr;
  l2_targ_ht_axi_id_t    l2_axi_arid;
  axi_len_t              l2_axi_arlen;
  axi_size_t             l2_axi_arsize;
  axi_burst_t            l2_axi_arburst;
  axi_cache_t            l2_axi_arcache;
  axi_prot_t             l2_axi_arprot;
  logic                  l2_axi_arlock;
  logic                  l2_axi_arvalid;
  logic                  l2_axi_arready;
  // R channel
  logic                  l2_axi_rvalid;
  logic                  l2_axi_rlast;
  l2_targ_ht_axi_id_t    l2_axi_rid;
  chip_axi_ht_data_t     l2_axi_rdata;
  axi_resp_t             l2_axi_rresp;
  logic                  l2_axi_rready;
  // Internal Clocks and Resets
  wire                   l2_clk;
  wire                   l2_rst_n;
  // SRAM control signals
  logic                  ret;
  logic                  pde;
  logic                  prn;

  // --------------------------------------------------------------
  // RTL
  // --------------------------------------------------------------
  pctl #(
    .N_FAST_CLKS      (1),
    .N_RESETS         (1),
    .N_MEM_PG         (1),
    .N_FENCES         (1),
    .CLKRST_MATRIX    (1'b1),
    .PLL_CLK_IS_I_CLK (1'b0),
    .NOC_RST_IDX      (1'b0),
    .SYNC_CLK_IDX     (1'b0),
    .AUTO_RESET_REMOVE(1'b0),
    .paddr_t          (chip_syscfg_addr_t),
    .pdata_t          (chip_apb_syscfg_data_t),
    .pstrb_t          (chip_apb_syscfg_strb_t)
  ) u_pctl (
    // Input clocks and resets
    .i_clk               (i_ref_clk),
    .i_ao_rst_n,
    .i_global_rst_n,
    .i_test_mode         (test_mode),
    // Output clocks and resets
    .i_pll_clk           (i_clk),
    .o_partition_clk     (l2_clk),
    .o_partition_rst_n   (l2_rst_n),
    .o_ao_rst_sync_n     (), // ASO-UNUSED_OUTPUT: No specifc AO CSR for l2
    // Isolation interface
    .o_noc_async_idle_req,
    .i_noc_async_idle_ack,
    .i_noc_async_idle_val,
    .o_noc_clken,
    .o_noc_rst_n,
    .o_int_shutdown_req  (),// ASO-UNUSED_OUTPUT: L2 doesn't request shutdown
    .i_int_shutdown_ack  (1'b1),
    // SRAM control signals
    .o_ret               (ret),
    .o_pde               (pde),
    .i_prn               (prn),
    // SYS_CFG Bus
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
    // Sync interface
    .i_global_sync_async(1'b0),
    .o_global_sync      (),// ASO-UNUSED_OUTPUT: L2 doesn't use sync interface,
    // External APB interface
    .o_ao_csr_apb_req    (), // ASO-UNUSED_OUTPUT: No specifc AO CSR for l2
    .i_ao_csr_apb_rsp    (pctl_ao_csr_reg_pkg::apb_d2h_t'('0))
  );

  axe_axi_multicut_flat #(
    .NumCuts       (1),                    // Number of cuts.
    .AxiIdWidth    (L2_TARG_HT_AXI_ID_W),  // AXI ID Width
    .AxiAddrWidth  (CHIP_AXI_ADDR_W),      // AXI Address Width
    .AxiDataWidth  (CHIP_AXI_HT_DATA_W),   // AXI Data Width
    .AxiAwUserWidth(CHIP_AXI_HT_AWUSER_W), // AXI AW User Width
    .AxiWUserWidth  (CHIP_AXI_HT_WUSER_W), // AXI  W User Width
    .AxiBUserWidth  (CHIP_AXI_HT_BUSER_W), // AXI  B User Width
    .AxiArUserWidth (CHIP_AXI_HT_ARUSER_W),// AXI AR User Width
    .AxiRUserWidth  (CHIP_AXI_HT_RUSER_W)  // AXI  R User Width
  ) u_axi_cut (
    .i_clk             (l2_clk  ),
    .i_rst_n           (l2_rst_n),
    //////////////////////
    // Subordinate Port //
    //////////////////////
    .i_axi_s_aw_id     (i_ht_axi_s_awid    ),
    .i_axi_s_aw_addr   (i_ht_axi_s_awaddr  ),
    .i_axi_s_aw_len    (i_ht_axi_s_awlen   ),
    .i_axi_s_aw_size   (i_ht_axi_s_awsize  ),
    .i_axi_s_aw_burst  (i_ht_axi_s_awburst ),
    .i_axi_s_aw_lock   (i_ht_axi_s_awlock  ),
    .i_axi_s_aw_cache  (i_ht_axi_s_awcache ),
    .i_axi_s_aw_prot   (i_ht_axi_s_awprot  ),
    .i_axi_s_aw_qos    (i_ht_axi_s_awqos   ),
    .i_axi_s_aw_region (i_ht_axi_s_awregion),
    .i_axi_s_aw_user   (i_ht_axi_s_awuser  ),
    .i_axi_s_aw_valid  (i_ht_axi_s_awvalid ),
    .o_axi_s_aw_ready  (o_ht_axi_s_awready ),
    .i_axi_s_w_data    (i_ht_axi_s_wdata   ),
    .i_axi_s_w_strb    (i_ht_axi_s_wstrb   ),
    .i_axi_s_w_last    (i_ht_axi_s_wlast   ),
    .i_axi_s_w_user    (i_ht_axi_s_wuser   ),
    .i_axi_s_w_valid   (i_ht_axi_s_wvalid  ),
    .o_axi_s_w_ready   (o_ht_axi_s_wready  ),
    .o_axi_s_b_id      (o_ht_axi_s_bid     ),
    .o_axi_s_b_resp    (o_ht_axi_s_bresp   ),
    .o_axi_s_b_user    (o_ht_axi_s_buser   ),
    .o_axi_s_b_valid   (o_ht_axi_s_bvalid  ),
    .i_axi_s_b_ready   (i_ht_axi_s_bready  ),
    .i_axi_s_ar_id     (i_ht_axi_s_arid    ),
    .i_axi_s_ar_addr   (i_ht_axi_s_araddr  ),
    .i_axi_s_ar_len    (i_ht_axi_s_arlen   ),
    .i_axi_s_ar_size   (i_ht_axi_s_arsize  ),
    .i_axi_s_ar_burst  (i_ht_axi_s_arburst ),
    .i_axi_s_ar_lock   (i_ht_axi_s_arlock  ),
    .i_axi_s_ar_cache  (i_ht_axi_s_arcache ),
    .i_axi_s_ar_prot   (i_ht_axi_s_arprot  ),
    .i_axi_s_ar_qos    (i_ht_axi_s_arqos   ),
    .i_axi_s_ar_region (i_ht_axi_s_arregion),
    .i_axi_s_ar_user   (i_ht_axi_s_aruser  ),
    .i_axi_s_ar_valid  (i_ht_axi_s_arvalid ),
    .o_axi_s_ar_ready  (o_ht_axi_s_arready ),
    .o_axi_s_r_id      (o_ht_axi_s_rid     ),
    .o_axi_s_r_data    (o_ht_axi_s_rdata   ),
    .o_axi_s_r_resp    (o_ht_axi_s_rresp   ),
    .o_axi_s_r_last    (o_ht_axi_s_rlast   ),
    .o_axi_s_r_user    (o_ht_axi_s_ruser   ),
    .o_axi_s_r_valid   (o_ht_axi_s_rvalid  ),
    .i_axi_s_r_ready   (i_ht_axi_s_rready  ),
    /////////////////////
    // Management Port //
    /////////////////////
    .o_axi_m_aw_id      (l2_axi_awid             ),
    .o_axi_m_aw_addr    (l2_axi_awaddr           ),
    .o_axi_m_aw_len     (l2_axi_awlen            ),
    .o_axi_m_aw_size    (l2_axi_awsize           ),
    .o_axi_m_aw_burst   (l2_axi_awburst          ),
    .o_axi_m_aw_lock    (l2_axi_awlock           ),
    .o_axi_m_aw_cache   (l2_axi_awcache          ),
    .o_axi_m_aw_prot    (l2_axi_awprot           ),
    .o_axi_m_aw_qos     (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .o_axi_m_aw_region  (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .o_axi_m_aw_valid   (l2_axi_awvalid          ),
    .o_axi_m_aw_user    (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .i_axi_m_aw_ready   (l2_axi_awready          ),
    .o_axi_m_w_data     (l2_axi_wdata            ),
    .o_axi_m_w_strb     (l2_axi_wstrb            ),
    .o_axi_m_w_last     (l2_axi_wlast            ),
    .o_axi_m_w_user     (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .o_axi_m_w_valid    (l2_axi_wvalid           ),
    .i_axi_m_w_ready    (l2_axi_wready           ),
    .i_axi_m_b_id       (l2_axi_bid              ),
    .i_axi_m_b_resp     (l2_axi_bresp            ),
    .i_axi_m_b_user     (chip_axi_ht_buser_t'('0)),
    .i_axi_m_b_valid    (l2_axi_bvalid           ),
    .o_axi_m_b_ready    (l2_axi_bready           ),
    .o_axi_m_ar_id      (l2_axi_arid             ),
    .o_axi_m_ar_addr    (l2_axi_araddr           ),
    .o_axi_m_ar_len     (l2_axi_arlen            ),
    .o_axi_m_ar_size    (l2_axi_arsize           ),
    .o_axi_m_ar_burst   (l2_axi_arburst          ),
    .o_axi_m_ar_lock    (l2_axi_arlock           ),
    .o_axi_m_ar_cache   (l2_axi_arcache          ),
    .o_axi_m_ar_prot    (l2_axi_arprot           ),
    .o_axi_m_ar_qos     (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .o_axi_m_ar_region  (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .o_axi_m_ar_user    (                        ), // ASO-UNUSED_OUTPUT: AXI4 feature not supported by l2
    .o_axi_m_ar_valid   (l2_axi_arvalid          ),
    .i_axi_m_ar_ready   (l2_axi_arready          ),
    .i_axi_m_r_id       (l2_axi_rid              ),
    .i_axi_m_r_data     (l2_axi_rdata            ),
    .i_axi_m_r_resp     (l2_axi_rresp            ),
    .i_axi_m_r_last     (l2_axi_rlast            ),
    .i_axi_m_r_user     (chip_axi_ht_ruser_t'('0)),
    .i_axi_m_r_valid    (l2_axi_rvalid           ),
    .o_axi_m_r_ready    (l2_axi_rready           )

  );

  l2_impl u_l2_impl (
    // Clock and reset signals
    .i_clk          (l2_clk  ),
    .i_rst_n        (l2_rst_n),
    // AXI write address channel
    .i_axi_s_awvalid(l2_axi_awvalid),
    .i_axi_s_awaddr (l2_axi_awaddr ),
    .i_axi_s_awid   (l2_axi_awid   ),
    .i_axi_s_awlen  (l2_axi_awlen  ),
    .i_axi_s_awsize (l2_axi_awsize ),
    .i_axi_s_awburst(l2_axi_awburst),
    .i_axi_s_awlock (l2_axi_awlock ),
    .i_axi_s_awcache(l2_axi_awcache),
    .i_axi_s_awprot (l2_axi_awprot ),
    .o_axi_s_awready(l2_axi_awready),
    // AXI write data channel
    .i_axi_s_wvalid (l2_axi_wvalid ),
    .i_axi_s_wlast  (l2_axi_wlast  ),
    .i_axi_s_wdata  (l2_axi_wdata  ),
    .i_axi_s_wstrb  (l2_axi_wstrb  ),
    .o_axi_s_wready (l2_axi_wready ),
    // AXI write response channel
    .o_axi_s_bvalid (l2_axi_bvalid ),
    .o_axi_s_bid    (l2_axi_bid    ),
    .o_axi_s_bresp  (l2_axi_bresp  ),
    .i_axi_s_bready (l2_axi_bready ),
    // AXI read address channel
    .i_axi_s_arvalid(l2_axi_arvalid),
    .i_axi_s_araddr (l2_axi_araddr ),
    .i_axi_s_arid   (l2_axi_arid   ),
    .i_axi_s_arlen  (l2_axi_arlen  ),
    .i_axi_s_arsize (l2_axi_arsize ),
    .i_axi_s_arburst(l2_axi_arburst),
    .i_axi_s_arlock (l2_axi_arlock ),
    .i_axi_s_arcache(l2_axi_arcache),
    .i_axi_s_arprot (l2_axi_arprot ),
    .o_axi_s_arready(l2_axi_arready),
    // AXI read data/response channel
    .o_axi_s_rvalid (l2_axi_rvalid ),
    .o_axi_s_rlast  (l2_axi_rlast  ),
    .o_axi_s_rid    (l2_axi_rid    ),
    .o_axi_s_rdata  (l2_axi_rdata  ),
    .o_axi_s_rresp  (l2_axi_rresp  ),
    .i_axi_s_rready (l2_axi_rready ),
    // SRAM configuration
    .i_ret          (ret           ),
    .i_pde          (pde           ),
    .o_prn          (prn           ),
    .i_scan_en      (scan_en       )
  );

endmodule
