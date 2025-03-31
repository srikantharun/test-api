// ===========================================================================================//
//  (C) Copyright Axelera AI 2024                                                             //
//  All Rights Reserved                                                                       //
//  Axelera AI Confidential                                                                   //
//  Owner : sultan.khan@axelera.ai                                                            //
//  Description : This module binds DUT's AXI Interface to the tracker signals                //
// ===========================================================================================//

// =============================================================================================================
// Macro to declare and bind AXI tracker instance for a given interface and configuration
// =============================================================================================================

`ifndef __BIND_DMA_AXI_PERF_TRACKER__
`define __BIND_DMA_AXI_PERF_TRACKER__

`define TRACKER_DUT dma 
 

`define DECLARE_AND_BIND_AXI_TRACKER_DMA_AXI_IF(inst_name, axi_sig_ref, log1, log2, addr_w, data_w, id_w) \
  bind `TRACKER_DUT axi_tracker # ( \
                        .WR_TRACE         (log1),   \
                        .RD_TRACE         (log2),   \
                        .CLK_PERIOD_IN_NS (1.25),   \
                        .AXI_ADDR_WIDTH   (addr_w), \
                        .AXI_DATA_WIDTH   (data_w), \
                        .AXI_ID_WIDTH     (id_w)    \
                      ) \
                      ``inst_name``_AXI_TRACKER_INST ( \
                        .aclk     ( i_clk                            ), \
                        .arstn    ( i_rst_n                          ), \
                        .arvalid  ( i_``axi_sig_ref``_arvalid          ), \
                        .araddr   ( i_``axi_sig_ref``_araddr           ), \
                        .arlen    ( i_``axi_sig_ref``_arlen            ), \
                        .arsize   ( i_``axi_sig_ref``_arsize           ), \
                        .arburst  ( i_``axi_sig_ref``_arburst          ), \
                        .arlock   ( i_``axi_sig_ref``_arlock           ), \
                        .arcache  ( i_``axi_sig_ref``_arcache          ), \
                        .arprot   ( i_``axi_sig_ref``_arprot           ), \
                        .arid     ( i_``axi_sig_ref``_arid             ), \
                        .arready  ( o_``axi_sig_ref``_arready          ), \
                        .rready   ( i_``axi_sig_ref``_rready           ), \
                        .rvalid   ( o_``axi_sig_ref``_rvalid           ), \
                        .rlast    ( o_``axi_sig_ref``_rlast            ), \
                        .rdata    ( o_``axi_sig_ref``_rdata            ), \
                        .rresp    ( o_``axi_sig_ref``_rresp            ), \
                        .rid      ( o_``axi_sig_ref``_rid              ), \
                        .awvalid  ( i_``axi_sig_ref``_awvalid          ), \
                        .awaddr   ( i_``axi_sig_ref``_awaddr           ), \
                        .awlen    ( i_``axi_sig_ref``_awlen            ), \
                        .awsize   ( i_``axi_sig_ref``_awsize           ), \
                        .awburst  ( i_``axi_sig_ref``_awburst          ), \
                        .awlock   ( i_``axi_sig_ref``_awlock           ), \
                        .awcache  ( i_``axi_sig_ref``_awcache          ), \
                        .awprot   ( i_``axi_sig_ref``_awprot           ), \
                        .awid     ( i_``axi_sig_ref``_awid             ), \
                        .awready  ( o_``axi_sig_ref``_awready          ), \
                        .wvalid   ( i_``axi_sig_ref``_wvalid           ), \
                        .wlast    ( i_``axi_sig_ref``_wlast            ), \
                        .wdata    ( i_``axi_sig_ref``_wdata            ), \
                        .wstrb    ( i_``axi_sig_ref``_wstrb            ), \
                        .wready   ( o_``axi_sig_ref``_wready           ), \
                        .bready   ( i_``axi_sig_ref``_bready           ), \
                        .bvalid   ( o_``axi_sig_ref``_bvalid           ), \
                        .bresp    ( o_``axi_sig_ref``_bresp            ), \
                        .bid      ( o_``axi_sig_ref``_bid              ) \
                      );


`define DECLARE_AND_BIND_AXI_TRACKER_DMA_TRANSFER_PORT(inst_name, axi_sig_ref, port_inst, log1, log2, addr_w, data_w, id_w) \
  bind `TRACKER_DUT axi_tracker # ( \
                        .WR_TRACE         (log1),   \
                        .RD_TRACE         (log2),   \
                        .CLK_PERIOD_IN_NS (1.25),   \
                        .AXI_ADDR_WIDTH   (addr_w), \
                        .AXI_DATA_WIDTH   (data_w), \
                        .AXI_ID_WIDTH     (id_w)    \
                      ) \
                      ``inst_name``_AXI_TRACKER_INST ( \
                        .aclk     ( i_clk                                   ), \
                        .arstn    ( i_rst_n                                 ), \
                        .arvalid  ( o_``axi_sig_ref``_arvalid``port_inst``  ), \
                        .araddr   ( o_``axi_sig_ref``_araddr``port_inst``   ), \
                        .arlen    ( o_``axi_sig_ref``_arlen``port_inst``    ), \
                        .arsize   ( o_``axi_sig_ref``_arsize``port_inst``   ), \
                        .arburst  ( o_``axi_sig_ref``_arburst``port_inst``  ), \
                        .arlock   ( o_``axi_sig_ref``_arlock``port_inst``   ), \
                        .arcache  ( o_``axi_sig_ref``_arcache``port_inst``  ), \
                        .arprot   ( o_``axi_sig_ref``_arprot``port_inst``   ), \
                        .arid     ( o_``axi_sig_ref``_arid``port_inst``     ), \
                        .arready  ( i_``axi_sig_ref``_arready``port_inst``  ), \
                        .rready   ( o_``axi_sig_ref``_rready``port_inst``   ), \
                        .rvalid   ( i_``axi_sig_ref``_rvalid``port_inst``   ), \
                        .rlast    ( i_``axi_sig_ref``_rlast``port_inst``    ), \
                        .rdata    ( i_``axi_sig_ref``_rdata``port_inst``    ), \
                        .rresp    ( i_``axi_sig_ref``_rresp``port_inst``    ), \
                        .rid      ( i_``axi_sig_ref``_rid``port_inst``      ), \
                        .awvalid  ( o_``axi_sig_ref``_awvalid``port_inst``  ), \
                        .awaddr   ( o_``axi_sig_ref``_awaddr``port_inst``   ), \
                        .awlen    ( o_``axi_sig_ref``_awlen``port_inst``    ), \
                        .awsize   ( o_``axi_sig_ref``_awsize``port_inst``   ), \
                        .awburst  ( o_``axi_sig_ref``_awburst``port_inst``  ), \
                        .awlock   ( o_``axi_sig_ref``_awlock``port_inst``   ), \
                        .awcache  ( o_``axi_sig_ref``_awcache``port_inst``  ), \
                        .awprot   ( o_``axi_sig_ref``_awprot``port_inst``   ), \
                        .awid     ( o_``axi_sig_ref``_awid``port_inst``     ), \
                        .awready  ( i_``axi_sig_ref``_awready``port_inst``  ), \
                        .wvalid   ( o_``axi_sig_ref``_wvalid``port_inst``   ), \
                        .wlast    ( o_``axi_sig_ref``_wlast``port_inst``    ), \
                        .wdata    ( o_``axi_sig_ref``_wdata``port_inst``    ), \
                        .wstrb    ( o_``axi_sig_ref``_wstrb``port_inst``    ), \
                        .wready   ( i_``axi_sig_ref``_wready``port_inst``   ), \
                        .bready   ( o_``axi_sig_ref``_bready``port_inst``   ), \
                        .bvalid   ( i_``axi_sig_ref``_bvalid``port_inst``   ), \
                        .bresp    ( i_``axi_sig_ref``_bresp``port_inst``    ), \
                        .bid      ( i_``axi_sig_ref``_bid``port_inst``      ) \
                      );


  // Tracker on each of the 3 AXI-Interfaces of the DMA DUT
  `DECLARE_AND_BIND_AXI_TRACKER_DMA_AXI_IF(i_bind_dut_reg_if, axi_s, "dma_regif_wr_txns.txt", "dma_regif_rd_txns.txt", 40, 64, 4)
  `DECLARE_AND_BIND_AXI_TRACKER_DMA_TRANSFER_PORT(i_bind_dut_dma_port0, axi_m, [0], "dma_port0_wr_txns.txt", "dma_port0_rd_txns.txt", 40, 512, 9)
  `DECLARE_AND_BIND_AXI_TRACKER_DMA_TRANSFER_PORT(i_bind_dut_dma_port1, axi_m, [1], "dma_port1_wr_txns.txt", "dma_port1_rd_txns.txt", 40, 512, 9)

`endif
 
