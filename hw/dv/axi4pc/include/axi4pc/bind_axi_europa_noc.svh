// ===========================================================================================================//
//  (C) Copyright Axelera AI 2021                                                                       //
//  All Rights Reserved                                                                                 //
//  Axelera AI Confidential                                                                             //
//  Owner : srinivas.prakash@axelera.ai                                                                 //
//  Description : This module binds DUT's AXI Interface to the Checker signals                          //
// ===========================================================================================================//
// =============================================================================================================
// Macro to declare and bind AXI Protocol Checker instance for a given interface and configuration
// =============================================================================================================

`ifndef __BIND_ENOC_AXI_CHECKER__
`define __BIND_ENOC_AXI_CHECKER__

`define DECLARE_AND_BIND_AXI_CHECKER(clk_rst, inst_name, log1, log2, clk_period_in_ns, addr_w, data_w, id_w, is_init, is_sdma, is_pcie) \
  bind `DUT Axi4PC # ( \
                        .ADDR_WIDTH   (addr_w), \
                        .DATA_WIDTH   (data_w), \
                        .WID_WIDTH     (id_w), \
                        .RID_WIDTH     (id_w), \
                        .MAXWBURSTS(20), \
                        .MAXRBURSTS(20), \
                        .RecommendOn(0), \
                        .RecMaxWaitOn(0), \
                        .AWREADY_MAXWAITS (256), \
                        .ARREADY_MAXWAITS (256), \
                        .WREADY_MAXWAITS (256), \
                        .BREADY_MAXWAITS (16), \
                        .RREADY_MAXWAITS (16) \
                      ) \
                      ``inst_name``_AXI_CHECKER_INST ( \
                        .ACLK     ( i_``clk_rst``_clk                                                       ), \
                        .ARESETn    ( is_sdma ? i_``clk_rst``_global_rst_n    : is_pcie ? i_``clk_rst``_data_rst_n : i_``clk_rst``_rst_n ), \
                        .ARQOS    ( is_init ? i_``inst_name``_axi_s_arqos   : o_``inst_name``_axi_m_arqos   ), \
                        .ARADDR   ( is_init ? i_``inst_name``_axi_s_araddr  : o_``inst_name``_axi_m_araddr  ), \
                        .ARBURST  ( is_init ? i_``inst_name``_axi_s_arburst : o_``inst_name``_axi_m_arburst ), \
                        .ARCACHE  ( is_init ? i_``inst_name``_axi_s_arcache : o_``inst_name``_axi_m_arcache ), \
                        .ARID     ( is_init ? i_``inst_name``_axi_s_arid    : o_``inst_name``_axi_m_arid    ), \
                        .ARLEN    ( is_init ? i_``inst_name``_axi_s_arlen   : o_``inst_name``_axi_m_arlen   ), \
                        .ARLOCK   ( is_init ? i_``inst_name``_axi_s_arlock  : o_``inst_name``_axi_m_arlock  ), \
                        .ARPROT   ( is_init ? i_``inst_name``_axi_s_arprot  : o_``inst_name``_axi_m_arprot  ), \
                        .ARSIZE   ( is_init ? i_``inst_name``_axi_s_arsize  : o_``inst_name``_axi_m_arsize  ), \
                        .ARVALID  ( is_init ? i_``inst_name``_axi_s_arvalid : o_``inst_name``_axi_m_arvalid ), \
                        .ARREADY  ( is_init ? o_``inst_name``_axi_s_arready : i_``inst_name``_axi_m_arready ), \
                        .RDATA    ( is_init ? o_``inst_name``_axi_s_rdata   : i_``inst_name``_axi_m_rdata   ), \
                        .RID      ( is_init ? o_``inst_name``_axi_s_rid     : i_``inst_name``_axi_m_rid     ), \
                        .RLAST    ( is_init ? o_``inst_name``_axi_s_rlast   : i_``inst_name``_axi_m_rlast   ), \
                        .RRESP    ( is_init ? o_``inst_name``_axi_s_rresp   : i_``inst_name``_axi_m_rresp   ), \
                        .RVALID   ( is_init ? o_``inst_name``_axi_s_rvalid  : i_``inst_name``_axi_m_rvalid  ), \
                        .RREADY   ( is_init ? i_``inst_name``_axi_s_rready  : o_``inst_name``_axi_m_rready  ), \
                        .AWQOS    ( is_init ? i_``inst_name``_axi_s_awqos   : o_``inst_name``_axi_m_awqos   ), \
                        .AWADDR   ( is_init ? i_``inst_name``_axi_s_awaddr  : o_``inst_name``_axi_m_awaddr  ), \
                        .AWBURST  ( is_init ? i_``inst_name``_axi_s_awburst : o_``inst_name``_axi_m_awburst ), \
                        .AWCACHE  ( is_init ? i_``inst_name``_axi_s_awcache : o_``inst_name``_axi_m_awcache ), \
                        .AWID     ( is_init ? i_``inst_name``_axi_s_awid    : o_``inst_name``_axi_m_awid    ), \
                        .AWLEN    ( is_init ? i_``inst_name``_axi_s_awlen   : o_``inst_name``_axi_m_awlen   ), \
                        .AWLOCK   ( is_init ? i_``inst_name``_axi_s_awlock  : o_``inst_name``_axi_m_awlock  ), \
                        .AWPROT   ( is_init ? i_``inst_name``_axi_s_awprot  : o_``inst_name``_axi_m_awprot  ), \
                        .AWSIZE   ( is_init ? i_``inst_name``_axi_s_awsize  : o_``inst_name``_axi_m_awsize  ), \
                        .AWVALID  ( is_init ? i_``inst_name``_axi_s_awvalid : o_``inst_name``_axi_m_awvalid ), \
                        .AWREADY  ( is_init ? o_``inst_name``_axi_s_awready : i_``inst_name``_axi_m_awready ), \
                        .WDATA    ( is_init ? i_``inst_name``_axi_s_wdata   : o_``inst_name``_axi_m_wdata   ), \
                        .WSTRB    ( is_init ? i_``inst_name``_axi_s_wstrb   : o_``inst_name``_axi_m_wstrb   ), \
                        .WLAST    ( is_init ? i_``inst_name``_axi_s_wlast   : o_``inst_name``_axi_m_wlast   ), \
                        .WVALID   ( is_init ? i_``inst_name``_axi_s_wvalid  : o_``inst_name``_axi_m_wvalid  ), \
                        .WREADY   ( is_init ? o_``inst_name``_axi_s_wready  : i_``inst_name``_axi_m_wready  ), \
                        .BRESP    ( is_init ? o_``inst_name``_axi_s_bresp   : i_``inst_name``_axi_m_bresp   ), \
                        .BID      ( is_init ? o_``inst_name``_axi_s_bid     : i_``inst_name``_axi_m_bid     ), \
                        .BVALID   ( is_init ? o_``inst_name``_axi_s_bvalid  : i_``inst_name``_axi_m_bvalid  ), \
                        .BREADY   ( is_init ? i_``inst_name``_axi_s_bready  : o_``inst_name``_axi_m_bready  ), \
                        .AWUSER   (32'h0), \
                        .WUSER    (32'h0), \
                        .ARUSER   (32'h0), \
                        .RUSER    (32'h0), \
                        .BUSER    (32'h0), \
                        .AWREGION (4'b0), \
                        .ARREGION (4'b0), \
                        .CACTIVE  (1'b0), \
                        .CSYSREQ  (1'b0), \
                        .CSYSACK  (1'b0) \
                      );

`endif
