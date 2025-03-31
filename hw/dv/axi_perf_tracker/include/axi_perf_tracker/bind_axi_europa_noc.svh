// ===========================================================================================================//
//  (C) Copyright Axelera AI 2021                                                                       //
//  All Rights Reserved                                                                                 //
//  Axelera AI Confidential                                                                             //
//  Owner : srinivas.prakash@axelera.ai                                                                 //
//  Description : This module binds DUT's AXI Interface to the tracker signals                          //
// ===========================================================================================================//
// =============================================================================================================
// Macro to declare and bind AXI tracker instance for a given interface and configuration
// =============================================================================================================

`ifndef __BIND_ENOC_AXI_PERF_TRACKER__
`define __BIND_ENOC_AXI_PERF_TRACKER__

`define DECLARE_AND_BIND_AXI_TRACKER(clk_rst, inst_name, log1, log2, clk_period_in_ns, addr_w, data_w, id_w, is_init, is_sdma, is_pcie) \
  bind `DUT axi_tracker # ( \
                        .WR_TRACE         (log1), \
                        .RD_TRACE         (log2), \
                        .CLK_PERIOD_IN_NS (clk_period_in_ns), \
                        .AXI_ADDR_WIDTH   (addr_w), \
                        .AXI_DATA_WIDTH   (data_w), \
                        .AXI_ID_WIDTH     (id_w) \
                      ) \
                      ``inst_name``_AXI_TRACKER_INST ( \
                        .aclk     ( i_``clk_rst``_clk                                                       ), \
                        .arstn    ( is_sdma ? i_``clk_rst``_global_rst_n    : is_pcie ? i_``clk_rst``_data_rst_n : i_``clk_rst``_rst_n ), \
                        .arqos    ( is_init ? i_``inst_name``_axi_s_arqos   : o_``inst_name``_axi_m_arqos   ), \
                        .araddr   ( is_init ? i_``inst_name``_axi_s_araddr  : o_``inst_name``_axi_m_araddr  ), \
                        .arburst  ( is_init ? i_``inst_name``_axi_s_arburst : o_``inst_name``_axi_m_arburst ), \
                        .arcache  ( is_init ? i_``inst_name``_axi_s_arcache : o_``inst_name``_axi_m_arcache ), \
                        .arid     ( is_init ? i_``inst_name``_axi_s_arid    : o_``inst_name``_axi_m_arid    ), \
                        .arlen    ( is_init ? i_``inst_name``_axi_s_arlen   : o_``inst_name``_axi_m_arlen   ), \
                        .arlock   ( is_init ? i_``inst_name``_axi_s_arlock  : o_``inst_name``_axi_m_arlock  ), \
                        .arprot   ( is_init ? i_``inst_name``_axi_s_arprot  : o_``inst_name``_axi_m_arprot  ), \
                        .arsize   ( is_init ? i_``inst_name``_axi_s_arsize  : o_``inst_name``_axi_m_arsize  ), \
                        .arvalid  ( is_init ? i_``inst_name``_axi_s_arvalid : o_``inst_name``_axi_m_arvalid ), \
                        .arready  ( is_init ? o_``inst_name``_axi_s_arready : i_``inst_name``_axi_m_arready ), \
                        .rdata    ( is_init ? o_``inst_name``_axi_s_rdata   : i_``inst_name``_axi_m_rdata   ), \
                        .rid      ( is_init ? o_``inst_name``_axi_s_rid     : i_``inst_name``_axi_m_rid     ), \
                        .rlast    ( is_init ? o_``inst_name``_axi_s_rlast   : i_``inst_name``_axi_m_rlast   ), \
                        .rresp    ( is_init ? o_``inst_name``_axi_s_rresp   : i_``inst_name``_axi_m_rresp   ), \
                        .rvalid   ( is_init ? o_``inst_name``_axi_s_rvalid  : i_``inst_name``_axi_m_rvalid  ), \
                        .rready   ( is_init ? i_``inst_name``_axi_s_rready  : o_``inst_name``_axi_m_rready  ), \
                        .awqos    ( is_init ? i_``inst_name``_axi_s_awqos   : o_``inst_name``_axi_m_awqos   ), \
                        .awaddr   ( is_init ? i_``inst_name``_axi_s_awaddr  : o_``inst_name``_axi_m_awaddr  ), \
                        .awburst  ( is_init ? i_``inst_name``_axi_s_awburst : o_``inst_name``_axi_m_awburst ), \
                        .awcache  ( is_init ? i_``inst_name``_axi_s_awcache : o_``inst_name``_axi_m_awcache ), \
                        .awid     ( is_init ? i_``inst_name``_axi_s_awid    : o_``inst_name``_axi_m_awid    ), \
                        .awlen    ( is_init ? i_``inst_name``_axi_s_awlen   : o_``inst_name``_axi_m_awlen   ), \
                        .awlock   ( is_init ? i_``inst_name``_axi_s_awlock  : o_``inst_name``_axi_m_awlock  ), \
                        .awprot   ( is_init ? i_``inst_name``_axi_s_awprot  : o_``inst_name``_axi_m_awprot  ), \
                        .awsize   ( is_init ? i_``inst_name``_axi_s_awsize  : o_``inst_name``_axi_m_awsize  ), \
                        .awvalid  ( is_init ? i_``inst_name``_axi_s_awvalid : o_``inst_name``_axi_m_awvalid ), \
                        .awready  ( is_init ? o_``inst_name``_axi_s_awready : i_``inst_name``_axi_m_awready ), \
                        .wdata    ( is_init ? i_``inst_name``_axi_s_wdata   : o_``inst_name``_axi_m_wdata   ), \
                        .wstrb    ( is_init ? i_``inst_name``_axi_s_wstrb   : o_``inst_name``_axi_m_wstrb   ), \
                        .wlast    ( is_init ? i_``inst_name``_axi_s_wlast   : o_``inst_name``_axi_m_wlast   ), \
                        .wvalid   ( is_init ? i_``inst_name``_axi_s_wvalid  : o_``inst_name``_axi_m_wvalid  ), \
                        .wready   ( is_init ? o_``inst_name``_axi_s_wready  : i_``inst_name``_axi_m_wready  ), \
                        .bresp    ( is_init ? o_``inst_name``_axi_s_bresp   : i_``inst_name``_axi_m_bresp   ), \
                        .bid      ( is_init ? o_``inst_name``_axi_s_bid     : i_``inst_name``_axi_m_bid     ), \
                        .bvalid   ( is_init ? o_``inst_name``_axi_s_bvalid  : i_``inst_name``_axi_m_bvalid  ), \
                        .bready   ( is_init ? i_``inst_name``_axi_s_bready  : o_``inst_name``_axi_m_bready  ) \
                      );

`endif

