// Binding protocol checker to the dut, this module will provide protocol assertions and support auxialiary code
// reference from: hw/dv/axi4pc/AxiPC.sv
`ifndef __BIND_SPM_AXI4PC__
`define __BIND_SPM_AXI4PC__
bind i_spm_dut Axi4PC #(
    .ADDR_WIDTH(`DEF_SPM_AXI_ADDR_WIDTH),
    .DATA_WIDTH(`DEF_SPM_AXI_DATA_WIDTH),
    .RID_WIDTH(`DEF_SPM_AXI_ID_WIDTH),
    .WID_WIDTH(`DEF_SPM_AXI_ID_WIDTH),
    .AWREADY_MAXWAITS(10000), //not really wanted, this depends also on master (if it issues too many axi transactions)
    .ARREADY_MAXWAITS(10000), //not really wanted, this depends also on master (if it issues too many axi transactions)
    .WREADY_MAXWAITS(10000), //not really wanted, this depends also on master (if it issues too many axi transactions)
    .BREADY_MAXWAITS(10000), //not really wanted, this depends also on master (if it issues too many axi transactions)
    .RREADY_MAXWAITS(10000), //not really wanted, this depends also on master (if it issues too many axi transactions)
    .MAXWBURSTS(99), // TBD as in hw/ip/spm/default/docs/index.md
    .MAXRBURSTS(99) // TBD as in hw/ip/spm/default/docs/index.md
) spm_ip_axi_protocol_checker(
    .ACLK(i_clk),
    .ARESETn(i_rst_n),
    // AW channel
    .AWVALID(i_axi_s_awvalid),
    .AWADDR(i_axi_s_awaddr),
    .AWID(i_axi_s_awid),
    .AWLEN(i_axi_s_awlen),
    .AWSIZE(i_axi_s_awsize),
    .AWBURST(i_axi_s_awburst),
    .AWLOCK(i_axi_s_awlock),
    .AWCACHE(i_axi_s_awcache),
    .AWPROT(i_axi_s_awprot),
    .AWREADY(o_axi_s_awready),
    //.AWATOP(spm_axi_awatop), //not part of axipc
    // W channel
    .WVALID(i_axi_s_wvalid),
    .WLAST(i_axi_s_wlast),
    .WDATA(i_axi_s_wdata),
    .WSTRB(i_axi_s_wstrb),
    .WREADY(o_axi_s_wready),
    // B channel
    .BVALID(o_axi_s_bvalid),
    .BID(o_axi_s_bid),
    .BRESP(o_axi_s_bresp),
    .BREADY(i_axi_s_bready),
    //AR channel
    .ARVALID(i_axi_s_arvalid),
    .ARADDR(i_axi_s_araddr),
    .ARID(i_axi_s_arid),
    .ARLEN(i_axi_s_arlen),
    .ARSIZE(i_axi_s_arsize),
    .ARBURST(i_axi_s_arburst),
    .ARLOCK(i_axi_s_arlock),
    .ARCACHE(i_axi_s_arcache),
    .ARPROT(i_axi_s_arprot),
    .ARREADY(o_axi_s_arready),
    // R channel
    .RVALID(o_axi_s_rvalid),
    .RLAST(o_axi_s_rlast),
    .RID(o_axi_s_rid),
    .RDATA(o_axi_s_rdata),
    .RRESP(o_axi_s_rresp),
    .RREADY(i_axi_s_rready),
    // unused
    .AWUSER(32'h0),
    .WUSER(32'h0),
    .ARUSER(32'h0),
    .RUSER(32'h0),
    .BUSER(32'h0),
    .AWREGION(4'b0),
    .AWQOS(4'b0),
    .ARQOS(4'b0),
    .ARREGION(4'b0),
    .CACTIVE(1'b0),
    .CSYSREQ(1'b0),
    .CSYSACK(1'b0)
);
`endif // __BIND_SPM_AXI4PC__
