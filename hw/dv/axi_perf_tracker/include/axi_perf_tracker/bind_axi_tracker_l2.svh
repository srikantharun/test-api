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

`ifndef __BIND_L2_AXI_PERF_TRACKER__
`define __BIND_L2_AXI_PERF_TRACKER__

`define TRACKER_DUT l2_p 
 

`define DECLARE_AND_BIND_AXI_TRACKER_L2(inst_name, log1, log2, addr_w, data_w, id_w) \
  bind `TRACKER_DUT axi_tracker # ( \
                        .WR_TRACE             (log1), \
                        .RD_TRACE             (log2), \
                        .CLK_PERIOD_IN_NS (0.83), \
                        .AXI_ADDR_WIDTH   (addr_w), \
                        .AXI_DATA_WIDTH   (data_w), \
                        .AXI_ID_WIDTH     (id_w) \
                      ) \
                      ``inst_name``_AXI_TRACKER_INST ( \
                        .aclk     ( i_clk                            ), \
                        .arstn    ( i_global_rst_n                   ), \
                        .arvalid  ( i_``inst_name``_arvalid          ), \
                        .araddr   ( i_``inst_name``_araddr           ), \
                        .arlen    ( i_``inst_name``_arlen            ), \
                        .arsize   ( i_``inst_name``_arsize           ), \
                        .arburst  ( i_``inst_name``_arburst          ), \
                        .arlock   ( i_``inst_name``_arlock           ), \
                        .arcache  ( i_``inst_name``_arcache          ), \
                        .arprot   ( i_``inst_name``_arprot           ), \
                        .arid     ( i_``inst_name``_arid             ), \
                        .arready  ( o_``inst_name``_arready          ), \
                        .rready   ( i_``inst_name``_rready           ), \
                        .rvalid   ( o_``inst_name``_rvalid           ), \
                        .rlast    ( o_``inst_name``_rlast            ), \
                        .rdata    ( o_``inst_name``_rdata            ), \
                        .rresp    ( o_``inst_name``_rresp            ), \
                        .rid      ( o_``inst_name``_rid              ), \
                        .awvalid  ( i_``inst_name``_awvalid          ), \
                        .awaddr   ( i_``inst_name``_awaddr           ), \
                        .awlen    ( i_``inst_name``_awlen            ), \
                        .awsize   ( i_``inst_name``_awsize           ), \
                        .awburst  ( i_``inst_name``_awburst          ), \
                        .awlock   ( i_``inst_name``_awlock           ), \
                        .awcache  ( i_``inst_name``_awcache          ), \
                        .awprot   ( i_``inst_name``_awprot           ), \
                        .awid     ( i_``inst_name``_awid             ), \
                        .awready  ( o_``inst_name``_awready          ), \
                        .wvalid   ( i_``inst_name``_wvalid           ), \
                        .wlast    ( i_``inst_name``_wlast            ), \
                        .wdata    ( i_``inst_name``_wdata            ), \
                        .wstrb    ( i_``inst_name``_wstrb            ), \
                        .wready   ( o_``inst_name``_wready           ), \
                        .bready   ( i_``inst_name``_bready           ), \
                        .bvalid   ( o_``inst_name``_bvalid           ), \
                        .bresp    ( o_``inst_name``_bresp            ), \
                        .bid      ( o_``inst_name``_bid              ) \
                      );

  `DECLARE_AND_BIND_AXI_TRACKER_L2(ht_axi_s, "l2_wr_txns.txt", "l2_rd_txns.txt", 40, 512, 4)

`endif

