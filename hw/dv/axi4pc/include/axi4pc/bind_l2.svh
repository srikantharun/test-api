`ifndef __BIND_L2_AXI4PC_DEFINES_H
`define __BIND_L2_AXI4PC_DEFINES_H

`ifndef TARGET_GLS
`ifdef TARGET_DFT
  `define __BIND_L2_AXI4PC_MODULE_NAME l2_p_l2
`else
  `define __BIND_L2_AXI4PC_MODULE_NAME l2
`endif

bind `__BIND_L2_AXI4PC_MODULE_NAME Axi4PC # (
				.DATA_WIDTH(512),
                .ADDR_WIDTH(36),
				//.ID_WIDTH  (`DW_VIP_AXI_AID_PORT_WIDTH),
				.RID_WIDTH  (4),
				.WID_WIDTH  (4),
                .MAXWBURSTS(20),
                .MAXRBURSTS(20),
                .RecommendOn(0),
				.RecMaxWaitOn( 0 ),
        .AWREADY_MAXWAITS ( 256 ),
        .ARREADY_MAXWAITS ( 256 ),
        .WREADY_MAXWAITS ( 256 ),
        .BREADY_MAXWAITS ( 16 ),
        .RREADY_MAXWAITS ( 16 )
				)
	AXI_AIP_L2
				(
				.ACLK(clk),
				.ARESETn(rst_n),
				.ARVALID(axi_hp_s_arvalid),
				.ARADDR(axi_hp_s_araddr ),
				.ARLEN(axi_hp_s_arlen),
				.ARSIZE( axi_hp_s_arsize),
				.ARBURST( axi_hp_s_arburst ),
				.ARLOCK( axi_hp_s_arlock),
				.ARCACHE( axi_hp_s_arcache ),
				.ARPROT( axi_hp_s_arprot ),
				.ARID( axi_hp_s_arid ),
				.ARREADY( axi_hp_s_arready ),
				.RREADY( axi_hp_s_rready ),
				.RVALID( axi_hp_s_rvalid ),
				.RLAST( axi_hp_s_rlast ),
				.RDATA(  axi_hp_s_rdata ),
				.RRESP( axi_hp_s_rresp ),
				.RID( axi_hp_s_rid ),
				.AWVALID( axi_hp_s_awvalid ),
				.AWADDR( axi_hp_s_awaddr ),
				.AWLEN( axi_hp_s_awlen),
				.AWSIZE( axi_hp_s_awsize ),
				.AWBURST( axi_hp_s_awburst ),
				.AWLOCK( axi_hp_s_awlock ),
				.AWCACHE( axi_hp_s_awcache ),
				.AWPROT( axi_hp_s_awprot ),
				.AWID( axi_hp_s_awid ),
				.AWREADY( axi_hp_s_awready ),
				.WVALID( axi_hp_s_wvalid ),
				.WLAST( axi_hp_s_wlast ),
				.WDATA(  axi_hp_s_wdata ),
				.WSTRB( axi_hp_s_wstrb ),
				.WREADY( axi_hp_s_wready),
				.BREADY( axi_hp_s_bready ),
				.BVALID( axi_hp_s_bvalid ),
				.BRESP( axi_hp_s_bresp ),
				.BID( axi_hp_s_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)
				);

`endif

`endif
