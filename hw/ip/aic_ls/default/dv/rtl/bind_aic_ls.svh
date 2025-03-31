 import dmc_pkg::*;
//  bind dmc_l1 Axi4PC #(
//     .ADDR_WIDTH(aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH),
//     .DATA_WIDTH(aic_common_pkg::AIC_HT_AXI_DATA_WIDTH),
//     .WID_WIDTH(aic_common_pkg::AIC_HT_AXI_M_ID_WIDTH),
//     .RID_WIDTH(aic_common_pkg::AIC_HT_AXI_M_ID_WIDTH),
//     .AWREADY_MAXWAITS ( 1024 ),
//     .ARREADY_MAXWAITS ( 1024 ),
//     .WREADY_MAXWAITS ( 1024 ),
//     .BREADY_MAXWAITS ( 16 ),
//     .RREADY_MAXWAITS ( 16 )
//   ) dmc_l1_ht_axi_m_protocol_checker(
// `ifdef LS_DUT_PATH
//     .ACLK(`LS_DUT_PATH.u_dmc.i_clk),  // reconnect manually if not default, should use gated clock to avoid assertion errros in clock gate tests
//     .ARESETn(`LS_DUT_PATH.u_dmc.i_rst_n),// reconnect manually if not default, just use same level as clk
// `else
//     .ACLK(i_clk),  // reconnect manually if not default,
//     .ARESETn(i_rst_n),// reconnect manually if not default
// `endif
//     .ARVALID(hp_axi_m_arvalid),
// 		.ARADDR(hp_axi_m_araddr ),
// 		.ARLEN(hp_axi_m_arlen),
// 		.ARSIZE( hp_axi_m_arsize),
// 		.ARBURST( hp_axi_m_arburst ),
// 		.ARLOCK( hp_axi_m_arlock),
// 		.ARCACHE( hp_axi_m_arcache ),
// 		.ARPROT( hp_axi_m_arprot ),
// 		.ARID( hp_axi_m_arid ),
// 		.ARREADY( hp_axi_m_arready ),
// 		.RREADY( hp_axi_m_rready ),
// 		.RVALID( hp_axi_m_rvalid ),
// 		.RLAST( hp_axi_m_rlast ),
// 		.RDATA(  hp_axi_m_rdata ),
// 		.RRESP( hp_axi_m_rresp ),
// 		.RID( hp_axi_m_rid ),
// 		.AWVALID( hp_axi_m_awvalid ),
// 		.AWADDR( hp_axi_m_awaddr ),
// 		.AWLEN( hp_axi_m_awlen),
// 		.AWSIZE( hp_axi_m_awsize ),
// 		.AWBURST( hp_axi_m_awburst ),
// 		.AWLOCK( hp_axi_m_awlock ),
// 		.AWCACHE( hp_axi_m_awcache ),
// 		.AWPROT( hp_axi_m_awprot ),
// 		.AWID( hp_axi_m_awid ),
// 		.AWREADY( hp_axi_m_awready ),
// 				.WVALID( hp_axi_m_wvalid ),
// 				.WLAST( hp_axi_m_wlast ),
// 				.WDATA(  hp_axi_m_wdata ),
// 				.WSTRB( hp_axi_m_wstrb ),
// 				.WREADY( hp_axi_m_wready),
// 				.BREADY( hp_axi_m_bready ),
// 				.BVALID( hp_axi_m_bvalid ),
// 				.BRESP( hp_axi_m_bresp ),
// 				.BID( hp_axi_m_bid  ),
// 				.AWUSER( 32'h0 ),
// 				.WUSER( 32'h0 ),
// 				.ARUSER( 32'h0 ),
// 				.RUSER( 32'h0 ),
// 				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

//      );


bind aic_ls_p Axi4PC #(
    .ADDR_WIDTH(aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH),
    .DATA_WIDTH(aic_common_pkg::AIC_HT_AXI_DATA_WIDTH),
    .RID_WIDTH(aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH),
    .WID_WIDTH(aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH),
    .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024 ),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) dmc_l1_ht_axi_protocol_checker(
`ifdef LS_DUT_PATH
    .ACLK(`LS_DUT_PATH.u_dmc.i_clk),  // reconnect manually if not default, should use gated clock to avoid assertion errros in clock gate tests
    .ARESETn(`LS_DUT_PATH.u_dmc.i_rst_n),// reconnect manually if not default, just use same level as clk
`else
    .ACLK(i_clk),  // reconnect manually if not default,
    .ARESETn(i_rst_n),// reconnect manually if not default
`endif
    .ARVALID(i_hp_axi_s_arvalid),
		.ARADDR(i_hp_axi_s_araddr ),
		.ARLEN(i_hp_axi_s_arlen),
		.ARSIZE( i_hp_axi_s_arsize),
		.ARBURST( i_hp_axi_s_arburst ),
		.ARLOCK( i_hp_axi_s_arlock),
		.ARCACHE( i_hp_axi_s_arcache ),
		.ARPROT( i_hp_axi_s_arprot ),
		.ARID( i_hp_axi_s_arid ),
		.ARREADY( o_hp_axi_s_arready ),
		.RREADY( i_hp_axi_s_rready ),
		.RVALID( o_hp_axi_s_rvalid ),
		.RLAST( o_hp_axi_s_rlast ),
		.RDATA(   o_hp_axi_s_rdata ),
		.RRESP( o_hp_axi_s_rresp ),
		.RID( o_hp_axi_s_rid ),
		.AWVALID( i_hp_axi_s_awvalid ),
		.AWADDR( i_hp_axi_s_awaddr ),
		.AWLEN( i_hp_axi_s_awlen),
		.AWSIZE( i_hp_axi_s_awsize ),
		.AWBURST( i_hp_axi_s_awburst ),
		.AWLOCK( i_hp_axi_s_awlock ),
		.AWCACHE( i_hp_axi_s_awcache ),
		.AWPROT( i_hp_axi_s_awprot ),
		.AWID( i_hp_axi_s_awid ),
		.AWREADY( o_hp_axi_s_awready ),
				.WVALID( i_hp_axi_s_wvalid ),
				.WLAST( i_hp_axi_s_wlast ),
				.WDATA(   i_hp_axi_s_wdata ),
				.WSTRB( i_hp_axi_s_wstrb ),
				.WREADY( o_hp_axi_s_wready),
				.BREADY( i_hp_axi_s_bready ),
				.BVALID( o_hp_axi_s_bvalid ),
				.BRESP( o_hp_axi_s_bresp ),
				.BID( o_hp_axi_s_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );


bind aic_ls_p Axi4PC #(
    .ADDR_WIDTH(aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .DATA_WIDTH(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .RID_WIDTH(aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
    .WID_WIDTH(aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
    .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024 ),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) AIC_LT_axi_cfg_protocol_checker(
`ifdef LS_DUT_PATH
    .ACLK(`LS_DUT_PATH.u_dmc.i_clk),  // reconnect manually if not default, should use gated clock to avoid assertion errros in clock gate tests
    .ARESETn(`LS_DUT_PATH.u_dmc.i_rst_n),// reconnect manually if not default, just use same level as clk
`else
    .ACLK(i_clk),  // reconnect manually if not default,
    .ARESETn(i_rst_n),// reconnect manually if not default
`endif
    .ARVALID(i_cfg_axi_s_arvalid),
		.ARADDR(i_cfg_axi_s_araddr ),
		.ARLEN(i_cfg_axi_s_arlen),
		.ARSIZE( i_cfg_axi_s_arsize),
		.ARBURST( i_cfg_axi_s_arburst ),
		.ARLOCK( '0 ),
		.ARCACHE( '0 ),
		.ARPROT( '0 ),
		.ARID( i_cfg_axi_s_arid ),
		.ARREADY( o_cfg_axi_s_arready ),
		.RREADY( i_cfg_axi_s_rready ),
		.RVALID( o_cfg_axi_s_rvalid ),
		.RLAST( o_cfg_axi_s_rlast ),
		.RDATA(    o_cfg_axi_s_rdata ),
		.RRESP( o_cfg_axi_s_rresp ),
		.RID( o_cfg_axi_s_rid ),
		.AWVALID( i_cfg_axi_s_awvalid ),
		.AWADDR( i_cfg_axi_s_awaddr ),
		.AWLEN( i_cfg_axi_s_awlen),
		.AWSIZE( i_cfg_axi_s_awsize ),
		.AWBURST( i_cfg_axi_s_awburst ),
		.AWLOCK( '0 ),
		.AWCACHE( '0 ),
		.AWPROT( '0 ),
		.AWID( i_cfg_axi_s_awid ),
		.AWREADY( o_cfg_axi_s_awready ),
				.WVALID( i_cfg_axi_s_wvalid ),
				.WLAST( i_cfg_axi_s_wlast ),
				.WDATA(  i_cfg_axi_s_wdata ),
				.WSTRB( i_cfg_axi_s_wstrb ),
				.WREADY( o_cfg_axi_s_wready),
				.BREADY( i_cfg_axi_s_bready ),
				.BVALID( o_cfg_axi_s_bvalid ),
				.BRESP( o_cfg_axi_s_bresp ),
				.BID( o_cfg_axi_s_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );

