
// Binding protocol checker to the dut, this module will provide performance benchmarking, data comparison and other
// reference from: hw/dv/axi_perf_tracker/axi_tracker.sv
`ifndef __BIND_SPM_AXI_PERF_TRACKER__
`define __BIND_SPM_AXI_PERF_TRACKER__
bind i_spm_dut axi_tracker #(
    .WR_TRACE             ("spm_wr_txns.txt"),
    .RD_TRACE             ("spm_rd_txns.txt"),
    .CLK_PERIOD_IN_NS (0.833),
    .AXI_ADDR_WIDTH   (`DEF_SPM_AXI_ADDR_WIDTH),
    .AXI_DATA_WIDTH   (`DEF_SPM_AXI_DATA_WIDTH),
    .AXI_ID_WIDTH     (`DEF_SPM_AXI_ID_WIDTH)
) spm_ip_axi_performance_tracker(
    .aclk(i_clk),
    .arstn(i_rst_n),
    // AW channel
    .awvalid(i_axi_s_awvalid),
    .awaddr(i_axi_s_awaddr),
    .awid(i_axi_s_awid),
    .awlen(i_axi_s_awlen),
    .awsize(i_axi_s_awsize),
    .awburst(i_axi_s_awburst),
    .awlock(i_axi_s_awlock),
    .awcache(i_axi_s_awcache),
    .awprot(i_axi_s_awprot),
    .awready(o_axi_s_awready),
    //.AWATOP(spm_axi_awatop), //not part of axipc
    // W channel
    .wvalid(i_axi_s_wvalid),
    .wlast(i_axi_s_wlast),
    .wdata(i_axi_s_wdata),
    .wstrb(i_axi_s_wstrb),
    .wready(o_axi_s_wready),
    // B channel
    .bvalid(o_axi_s_bvalid),
    .bid(o_axi_s_bid),
    .bresp(o_axi_s_bresp),
    .bready(i_axi_s_bready),
    //AR channel
    .arvalid(i_axi_s_arvalid),
    .araddr(i_axi_s_araddr),
    .arid(i_axi_s_arid),
    .arlen(i_axi_s_arlen),
    .arsize(i_axi_s_arsize),
    .arburst(i_axi_s_arburst),
    .arlock(i_axi_s_arlock),
    .arcache(i_axi_s_arcache),
    .arprot(i_axi_s_arprot),
    .arready(o_axi_s_arready),
    // R channel
    .rvalid(o_axi_s_rvalid),
    .rlast(o_axi_s_rlast),
    .rid(o_axi_s_rid),
    .rdata(o_axi_s_rdata),
    .rresp(o_axi_s_rresp),
    .rready(i_axi_s_rready)
);
`endif // __BIND_SPM_AXI_PERF_TRACKER__

