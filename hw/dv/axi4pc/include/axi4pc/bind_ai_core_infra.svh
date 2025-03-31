bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_HP_AXI_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_HP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_HP_AXI_NM_ID_WIDTH),
    .RID_WIDTH(AI_CORE_HP_AXI_NM_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_infra_hp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(noc_hp_axi_s_arvalid),
		.ARADDR(noc_hp_axi_s_araddr ),
		.ARLEN(noc_hp_axi_s_arlen),
		.ARSIZE( noc_hp_axi_s_arsize),
		.ARBURST( noc_hp_axi_s_arburst ),
		.ARLOCK( noc_hp_axi_s_arlock),
		.ARCACHE( noc_hp_axi_s_arcache ),
		.ARPROT( noc_hp_axi_s_arprot ),
		.ARID( noc_hp_axi_s_arid ),
		.ARREADY( noc_hp_axi_s_arready ),
		.RREADY( noc_hp_axi_s_rready ),
		.RVALID( noc_hp_axi_s_rvalid ),
		.RLAST( noc_hp_axi_s_rlast ),
		.RDATA(  noc_hp_axi_s_rdata ),
		.RRESP( noc_hp_axi_s_rresp ),
		.RID( noc_hp_axi_s_rid ),
		.AWVALID( noc_hp_axi_s_awvalid ),
		.AWADDR( noc_hp_axi_s_awaddr ),
		.AWLEN( noc_hp_axi_s_awlen),
		.AWSIZE( noc_hp_axi_s_awsize ),
		.AWBURST( noc_hp_axi_s_awburst ),
		.AWLOCK( noc_hp_axi_s_awlock ),
		.AWCACHE( noc_hp_axi_s_awcache ),
		.AWPROT( noc_hp_axi_s_awprot ),
		.AWID( noc_hp_axi_s_awid ),
		.AWREADY( noc_hp_axi_s_awready ),
				.WVALID( noc_hp_axi_s_wvalid ),
				.WLAST( noc_hp_axi_s_wlast ),
				.WDATA(  noc_hp_axi_s_wdata ),
				.WSTRB( noc_hp_axi_s_wstrb ),
				.WREADY( noc_hp_axi_s_wready),
				.BREADY( noc_hp_axi_s_bready ),
				.BVALID( noc_hp_axi_s_bvalid ),
				.BRESP( noc_hp_axi_s_bresp ),
				.BID( noc_hp_axi_s_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );


bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_HP_AXI_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_HP_AXI_DATA_WIDTH),
    .RID_WIDTH(AI_CORE_HP_AXI_S_ID_WIDTH),
    .WID_WIDTH(AI_CORE_HP_AXI_S_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 2048),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_ls_hp_axi_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_ls_hp_axi_s_arvalid),
		.ARADDR(ai_core_ls_hp_axi_s_araddr ),
		.ARLEN(ai_core_ls_hp_axi_s_arlen),
		.ARSIZE( ai_core_ls_hp_axi_s_arsize),
		.ARBURST( ai_core_ls_hp_axi_s_arburst ),
		.ARLOCK( ai_core_ls_hp_axi_s_arlock),
		.ARCACHE( ai_core_ls_hp_axi_s_arcache ),
		.ARPROT( ai_core_ls_hp_axi_s_arprot ),
		.ARID( ai_core_ls_hp_axi_s_arid ),
		.ARREADY( ai_core_ls_hp_axi_s_arready ),
		.RREADY( ai_core_ls_hp_axi_s_rready ),
		.RVALID( ai_core_ls_hp_axi_s_rvalid ),
		.RLAST( ai_core_ls_hp_axi_s_rlast ),
		.RDATA(  ai_core_ls_hp_axi_s_rdata ),
		.RRESP( ai_core_ls_hp_axi_s_rresp ),
		.RID( ai_core_ls_hp_axi_s_rid ),
		.AWVALID( ai_core_ls_hp_axi_s_awvalid ),
		.AWADDR( ai_core_ls_hp_axi_s_awaddr ),
		.AWLEN( ai_core_ls_hp_axi_s_awlen),
		.AWSIZE( ai_core_ls_hp_axi_s_awsize ),
		.AWBURST( ai_core_ls_hp_axi_s_awburst ),
		.AWLOCK( ai_core_ls_hp_axi_s_awlock ),
		.AWCACHE( ai_core_ls_hp_axi_s_awcache ),
		.AWPROT( ai_core_ls_hp_axi_s_awprot ),
		.AWID( ai_core_ls_hp_axi_s_awid ),
		.AWREADY( ai_core_ls_hp_axi_s_awready ),
				.WVALID( ai_core_ls_hp_axi_s_wvalid ),
				.WLAST( ai_core_ls_hp_axi_s_wlast ),
				.WDATA(  ai_core_ls_hp_axi_s_wdata ),
				.WSTRB( ai_core_ls_hp_axi_s_wstrb ),
				.WREADY( ai_core_ls_hp_axi_s_wready),
				.BREADY( ai_core_ls_hp_axi_s_bready ),
				.BVALID( ai_core_ls_hp_axi_s_bvalid ),
				.BRESP( ai_core_ls_hp_axi_s_bresp ),
				.BID( ai_core_ls_hp_axi_s_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );


bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_HP_AXI_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_HP_AXI_DATA_WIDTH),
    .RID_WIDTH(AI_CORE_HP_AXI_M_ID_WIDTH),
    .WID_WIDTH(AI_CORE_HP_AXI_M_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_ls_hp_axi_m_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_ls_hp_axi_m_arvalid),
		.ARADDR(ai_core_ls_hp_axi_m_araddr ),
		.ARLEN(ai_core_ls_hp_axi_m_arlen),
		.ARSIZE( ai_core_ls_hp_axi_m_arsize),
		.ARBURST( ai_core_ls_hp_axi_m_arburst ),
		.ARLOCK( ai_core_ls_hp_axi_m_arlock),
		.ARCACHE( ai_core_ls_hp_axi_m_arcache ),
		.ARPROT( ai_core_ls_hp_axi_m_arprot ),
		.ARID( ai_core_ls_hp_axi_m_arid ),
		.ARREADY( ai_core_ls_hp_axi_m_arready ),
		.RREADY( ai_core_ls_hp_axi_m_rready ),
		.RVALID( ai_core_ls_hp_axi_m_rvalid ),
		.RLAST( ai_core_ls_hp_axi_m_rlast ),
		.RDATA( ai_core_ls_hp_axi_m_rdata ),
		.RRESP( ai_core_ls_hp_axi_m_rresp ),
		.RID( ai_core_ls_hp_axi_m_rid ),
		.AWVALID( ai_core_ls_hp_axi_m_awvalid ),
		.AWADDR( ai_core_ls_hp_axi_m_awaddr ),
		.AWLEN( ai_core_ls_hp_axi_m_awlen),
		.AWSIZE( ai_core_ls_hp_axi_m_awsize ),
		.AWBURST( ai_core_ls_hp_axi_m_awburst ),
		.AWLOCK( ai_core_ls_hp_axi_m_awlock ),
		.AWCACHE( ai_core_ls_hp_axi_m_awcache ),
		.AWPROT( ai_core_ls_hp_axi_m_awprot ),
		.AWID( ai_core_ls_hp_axi_m_awid ),
		.AWREADY( ai_core_ls_hp_axi_m_awready ),
				.WVALID( ai_core_ls_hp_axi_m_wvalid ),
				.WLAST( ai_core_ls_hp_axi_m_wlast ),
				.WDATA(  ai_core_ls_hp_axi_m_wdata ),
				.WSTRB( ai_core_ls_hp_axi_m_wstrb ),
				.WREADY( ai_core_ls_hp_axi_m_wready),
				.BREADY( ai_core_ls_hp_axi_m_bready ),
				.BVALID( ai_core_ls_hp_axi_m_bvalid ),
				.BRESP( ai_core_ls_hp_axi_m_bresp ),
				.BID( ai_core_ls_hp_axi_m_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );



bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_M_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_M_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_infra_lp_axi_m_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(noc_lp_axi_m_arvalid),
		.ARADDR(noc_lp_axi_m_araddr ),
		.ARLEN(noc_lp_axi_m_arlen),
		.ARSIZE( noc_lp_axi_m_arsize),
		.ARBURST( noc_lp_axi_m_arburst ),
		.ARLOCK( noc_lp_axi_m_arlock),
		.ARCACHE( noc_lp_axi_m_arcache ),
		.ARPROT( noc_lp_axi_m_arprot ),
		.ARID( noc_lp_axi_m_arid ),
		.ARREADY( noc_lp_axi_m_arready ),
		.RREADY( noc_lp_axi_m_rready ),
		.RVALID( noc_lp_axi_m_rvalid ),
		.RLAST( noc_lp_axi_m_rlast ),
		.RDATA(  noc_lp_axi_m_rdata ),
		.RRESP( noc_lp_axi_m_rresp ),
		.RID( noc_lp_axi_m_rid ),
		.AWVALID( noc_lp_axi_m_awvalid ),
		 .AWADDR( noc_lp_axi_m_awaddr ),
		 .AWLEN( noc_lp_axi_m_awlen),
		 .AWSIZE( noc_lp_axi_m_awsize ),
		 .AWBURST( noc_lp_axi_m_awburst ),
		 .AWLOCK( noc_lp_axi_m_awlock ),
		 .AWCACHE( noc_lp_axi_m_awcache ),
		 .AWPROT( noc_lp_axi_m_awprot ),
		 .AWID( noc_lp_axi_m_awid ),
		 .AWREADY( noc_lp_axi_m_awready ),
		 .WVALID( noc_lp_axi_m_wvalid ),
		 .WLAST( noc_lp_axi_m_wlast ),
	   .WDATA(  noc_lp_axi_m_wdata ),
		 .WSTRB( noc_lp_axi_m_wstrb ),
		 .WREADY( noc_lp_axi_m_wready),
		 .BREADY( noc_lp_axi_m_bready ),
		 .BVALID( noc_lp_axi_m_bvalid ),
		 .BRESP( noc_lp_axi_m_bresp ),
		 .BID( noc_lp_axi_m_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );


bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_infra_lp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(noc_lp_axi_s_arvalid),
		.ARADDR(noc_lp_axi_s_araddr ),
		.ARLEN(noc_lp_axi_s_arlen),
		.ARSIZE( noc_lp_axi_s_arsize),
		.ARBURST( noc_lp_axi_s_arburst ),
		.ARLOCK( noc_lp_axi_s_arlock),
		.ARCACHE( noc_lp_axi_s_arcache ),
		.ARPROT( noc_lp_axi_s_arprot ),
		.ARID( noc_lp_axi_s_arid ),
		.ARREADY( noc_lp_axi_s_arready ),
		.RREADY( noc_lp_axi_s_rready ),
		.RVALID( noc_lp_axi_s_rvalid ),
		.RLAST( noc_lp_axi_s_rlast ),
		.RDATA(  noc_lp_axi_s_rdata ),
		.RRESP( noc_lp_axi_s_rresp ),
		.RID( noc_lp_axi_s_rid ),
		.AWVALID( noc_lp_axi_s_awvalid ),
		 .AWADDR( noc_lp_axi_s_awaddr ),
		 .AWLEN( noc_lp_axi_s_awlen),
		 .AWSIZE( noc_lp_axi_s_awsize ),
		 .AWBURST( noc_lp_axi_s_awburst ),
		 .AWLOCK( noc_lp_axi_s_awlock ),
		 .AWCACHE( noc_lp_axi_s_awcache ),
		 .AWPROT( noc_lp_axi_s_awprot ),
		 .AWID( noc_lp_axi_s_awid ),
		 .AWREADY( noc_lp_axi_s_awready ),
		 .WVALID( noc_lp_axi_s_wvalid ),
		 .WLAST( noc_lp_axi_s_wlast ),
	   .WDATA(  noc_lp_axi_s_wdata ),
		 .WSTRB( noc_lp_axi_s_wstrb ),
		 .WREADY( noc_lp_axi_s_wready),
		 .BREADY( noc_lp_axi_s_bready ),
		 .BVALID( noc_lp_axi_s_bvalid ),
		 .BRESP( noc_lp_axi_s_bresp ),
		 .BID( noc_lp_axi_s_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );


bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_LOCAL_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_mvm_lp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_mvm_lp_axi_s_arvalid),
		.ARADDR(ai_core_mvm_lp_axi_s_araddr ),
		.ARLEN(ai_core_mvm_lp_axi_s_arlen),
		.ARSIZE( ai_core_mvm_lp_axi_s_arsize),
		.ARBURST( ai_core_mvm_lp_axi_s_arburst ),
		.ARLOCK( ai_core_mvm_lp_axi_s_arlock),
		.ARCACHE( ai_core_mvm_lp_axi_s_arcache ),
		.ARPROT( ai_core_mvm_lp_axi_s_arprot ),
		.ARID( ai_core_mvm_lp_axi_s_arid ),
		.ARREADY( ai_core_mvm_lp_axi_s_arready ),
		.RREADY( ai_core_mvm_lp_axi_s_rready ),
		.RVALID( ai_core_mvm_lp_axi_s_rvalid ),
		.RLAST( ai_core_mvm_lp_axi_s_rlast ),
		.RDATA(  ai_core_mvm_lp_axi_s_rdata ),
		.RRESP( ai_core_mvm_lp_axi_s_rresp ),
		.RID( ai_core_mvm_lp_axi_s_rid ),
		.AWVALID( ai_core_mvm_lp_axi_s_awvalid ),
		 .AWADDR( ai_core_mvm_lp_axi_s_awaddr ),
		 .AWLEN( ai_core_mvm_lp_axi_s_awlen),
		 .AWSIZE( ai_core_mvm_lp_axi_s_awsize ),
		 .AWBURST( ai_core_mvm_lp_axi_s_awburst ),
		 .AWLOCK( ai_core_mvm_lp_axi_s_awlock ),
		 .AWCACHE( ai_core_mvm_lp_axi_s_awcache ),
		 .AWPROT( ai_core_mvm_lp_axi_s_awprot ),
		 .AWID( ai_core_mvm_lp_axi_s_awid ),
		 .AWREADY( ai_core_mvm_lp_axi_s_awready ),
		 .WVALID( ai_core_mvm_lp_axi_s_wvalid ),
		 .WLAST( ai_core_mvm_lp_axi_s_wlast ),
	   .WDATA(  ai_core_mvm_lp_axi_s_wdata ),
		 .WSTRB( ai_core_mvm_lp_axi_s_wstrb ),
		 .WREADY( ai_core_mvm_lp_axi_s_wready),
		 .BREADY( ai_core_mvm_lp_axi_s_bready ),
		 .BVALID( ai_core_mvm_lp_axi_s_bvalid ),
		 .BRESP( ai_core_mvm_lp_axi_s_bresp ),
		 .BID( ai_core_mvm_lp_axi_s_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );


  bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_LOCAL_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
  	.AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_dwpu_lp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_dwpu_lp_axi_s_arvalid),
		.ARADDR(ai_core_dwpu_lp_axi_s_araddr ),
		.ARLEN(ai_core_dwpu_lp_axi_s_arlen),
		.ARSIZE( ai_core_dwpu_lp_axi_s_arsize),
		.ARBURST( ai_core_dwpu_lp_axi_s_arburst ),
		.ARLOCK( ai_core_dwpu_lp_axi_s_arlock),
		.ARCACHE( ai_core_dwpu_lp_axi_s_arcache ),
		.ARPROT( ai_core_dwpu_lp_axi_s_arprot ),
		.ARID( ai_core_dwpu_lp_axi_s_arid ),
		.ARREADY( ai_core_dwpu_lp_axi_s_arready ),
		.RREADY( ai_core_dwpu_lp_axi_s_rready ),
		.RVALID( ai_core_dwpu_lp_axi_s_rvalid ),
		.RLAST( ai_core_dwpu_lp_axi_s_rlast ),
		.RDATA(  ai_core_dwpu_lp_axi_s_rdata ),
		.RRESP( ai_core_dwpu_lp_axi_s_rresp ),
		.RID( ai_core_dwpu_lp_axi_s_rid ),
		.AWVALID( ai_core_dwpu_lp_axi_s_awvalid ),
		 .AWADDR( ai_core_dwpu_lp_axi_s_awaddr ),
		 .AWLEN( ai_core_dwpu_lp_axi_s_awlen),
		 .AWSIZE( ai_core_dwpu_lp_axi_s_awsize ),
		 .AWBURST( ai_core_dwpu_lp_axi_s_awburst ),
		 .AWLOCK( ai_core_dwpu_lp_axi_s_awlock ),
		 .AWCACHE( ai_core_dwpu_lp_axi_s_awcache ),
		 .AWPROT( ai_core_dwpu_lp_axi_s_awprot ),
		 .AWID( ai_core_dwpu_lp_axi_s_awid ),
		 .AWREADY( ai_core_dwpu_lp_axi_s_awready ),
		 .WVALID( ai_core_dwpu_lp_axi_s_wvalid ),
		 .WLAST( ai_core_dwpu_lp_axi_s_wlast ),
	   .WDATA(  ai_core_dwpu_lp_axi_s_wdata ),
		 .WSTRB( ai_core_dwpu_lp_axi_s_wstrb ),
		 .WREADY( ai_core_dwpu_lp_axi_s_wready),
		 .BREADY( ai_core_dwpu_lp_axi_s_bready ),
		 .BVALID( ai_core_dwpu_lp_axi_s_bvalid ),
		 .BRESP( ai_core_dwpu_lp_axi_s_bresp ),
		 .BID( ai_core_dwpu_lp_axi_s_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );



  bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_LOCAL_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_iau_dpu_lp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_iau_dpu_0_lp_axi_s_arvalid),
		.ARADDR(ai_core_iau_dpu_0_lp_axi_s_araddr ),
		.ARLEN(ai_core_iau_dpu_0_lp_axi_s_arlen),
		.ARSIZE( ai_core_iau_dpu_0_lp_axi_s_arsize),
		.ARBURST( ai_core_iau_dpu_0_lp_axi_s_arburst ),
		.ARLOCK( ai_core_iau_dpu_0_lp_axi_s_arlock),
		.ARCACHE( ai_core_iau_dpu_0_lp_axi_s_arcache ),
		.ARPROT( ai_core_iau_dpu_0_lp_axi_s_arprot ),
		.ARID( ai_core_iau_dpu_0_lp_axi_s_arid ),
		.ARREADY( ai_core_iau_dpu_0_lp_axi_s_arready ),
		.RREADY( ai_core_iau_dpu_0_lp_axi_s_rready ),
		.RVALID( ai_core_iau_dpu_0_lp_axi_s_rvalid ),
		.RLAST( ai_core_iau_dpu_0_lp_axi_s_rlast ),
		.RDATA(  ai_core_iau_dpu_0_lp_axi_s_rdata ),
		.RRESP( ai_core_iau_dpu_0_lp_axi_s_rresp ),
		.RID( ai_core_iau_dpu_0_lp_axi_s_rid ),
		.AWVALID( ai_core_iau_dpu_0_lp_axi_s_awvalid ),
		 .AWADDR( ai_core_iau_dpu_0_lp_axi_s_awaddr ),
		 .AWLEN( ai_core_iau_dpu_0_lp_axi_s_awlen),
		 .AWSIZE( ai_core_iau_dpu_0_lp_axi_s_awsize ),
		 .AWBURST( ai_core_iau_dpu_0_lp_axi_s_awburst ),
		 .AWLOCK( ai_core_iau_dpu_0_lp_axi_s_awlock ),
		 .AWCACHE( ai_core_iau_dpu_0_lp_axi_s_awcache ),
		 .AWPROT( ai_core_iau_dpu_0_lp_axi_s_awprot ),
		 .AWID( ai_core_iau_dpu_0_lp_axi_s_awid ),
		 .AWREADY( ai_core_iau_dpu_0_lp_axi_s_awready ),
		 .WVALID( ai_core_iau_dpu_0_lp_axi_s_wvalid ),
		 .WLAST( ai_core_iau_dpu_0_lp_axi_s_wlast ),
	   .WDATA(  ai_core_iau_dpu_0_lp_axi_s_wdata ),
		 .WSTRB( ai_core_iau_dpu_0_lp_axi_s_wstrb ),
		 .WREADY( ai_core_iau_dpu_0_lp_axi_s_wready),
		 .BREADY( ai_core_iau_dpu_0_lp_axi_s_bready ),
		 .BVALID( ai_core_iau_dpu_0_lp_axi_s_bvalid ),
		 .BRESP( ai_core_iau_dpu_0_lp_axi_s_bresp ),
		 .BID( ai_core_iau_dpu_0_lp_axi_s_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );



  bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_LOCAL_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_iau_dpu_1_lp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_iau_dpu_1_lp_axi_s_arvalid),
		.ARADDR(ai_core_iau_dpu_1_lp_axi_s_araddr ),
		.ARLEN(ai_core_iau_dpu_1_lp_axi_s_arlen),
		.ARSIZE( ai_core_iau_dpu_1_lp_axi_s_arsize),
		.ARBURST( ai_core_iau_dpu_1_lp_axi_s_arburst ),
		.ARLOCK( ai_core_iau_dpu_1_lp_axi_s_arlock),
		.ARCACHE( ai_core_iau_dpu_1_lp_axi_s_arcache ),
		.ARPROT( ai_core_iau_dpu_1_lp_axi_s_arprot ),
		.ARID( ai_core_iau_dpu_1_lp_axi_s_arid ),
		.ARREADY( ai_core_iau_dpu_1_lp_axi_s_arready ),
		.RREADY( ai_core_iau_dpu_1_lp_axi_s_rready ),
		.RVALID( ai_core_iau_dpu_1_lp_axi_s_rvalid ),
		.RLAST( ai_core_iau_dpu_1_lp_axi_s_rlast ),
		.RDATA(  ai_core_iau_dpu_1_lp_axi_s_rdata ),
		.RRESP( ai_core_iau_dpu_1_lp_axi_s_rresp ),
		.RID( ai_core_iau_dpu_1_lp_axi_s_rid ),
		.AWVALID( ai_core_iau_dpu_1_lp_axi_s_awvalid ),
		 .AWADDR( ai_core_iau_dpu_1_lp_axi_s_awaddr ),
		 .AWLEN( ai_core_iau_dpu_1_lp_axi_s_awlen),
		 .AWSIZE( ai_core_iau_dpu_1_lp_axi_s_awsize ),
		 .AWBURST( ai_core_iau_dpu_1_lp_axi_s_awburst ),
		 .AWLOCK( ai_core_iau_dpu_1_lp_axi_s_awlock ),
		 .AWCACHE( ai_core_iau_dpu_1_lp_axi_s_awcache ),
		 .AWPROT( ai_core_iau_dpu_1_lp_axi_s_awprot ),
		 .AWID( ai_core_iau_dpu_1_lp_axi_s_awid ),
		 .AWREADY( ai_core_iau_dpu_1_lp_axi_s_awready ),
		 .WVALID( ai_core_iau_dpu_1_lp_axi_s_wvalid ),
		 .WLAST( ai_core_iau_dpu_1_lp_axi_s_wlast ),
	   .WDATA(  ai_core_iau_dpu_1_lp_axi_s_wdata ),
		 .WSTRB( ai_core_iau_dpu_1_lp_axi_s_wstrb ),
		 .WREADY( ai_core_iau_dpu_1_lp_axi_s_wready),
		 .BREADY( ai_core_iau_dpu_1_lp_axi_s_bready ),
		 .BVALID( ai_core_iau_dpu_1_lp_axi_s_bvalid ),
		 .BRESP( ai_core_iau_dpu_1_lp_axi_s_bresp ),
		 .BID( ai_core_iau_dpu_1_lp_axi_s_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );



  bind ai_core_infra_p Axi4PC #(
    .ADDR_WIDTH(AI_CORE_LP_AXI_LOCAL_ADDR_WIDTH),
    .DATA_WIDTH(AI_CORE_LP_AXI_DATA_WIDTH),
    .WID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
    .RID_WIDTH(AI_CORE_LP_AXI_S_ID_WIDTH),
	  .AWREADY_MAXWAITS ( 1024 ),
    .ARREADY_MAXWAITS ( 1024 ),
    .WREADY_MAXWAITS ( 1024),
    .BREADY_MAXWAITS ( 16 ),
    .RREADY_MAXWAITS ( 16 )
  ) ai_core_ls_lp_axi_s_protocol_checker(
    .ACLK(clk),  // reconnect manually if not default
    .ARESETn(rst_n),// reconnect manually if not default
    .ARVALID(ai_core_ls_lp_axi_s_arvalid),
		.ARADDR(ai_core_ls_lp_axi_s_araddr ),
		.ARLEN(ai_core_ls_lp_axi_s_arlen),
		.ARSIZE( ai_core_ls_lp_axi_s_arsize),
		.ARBURST( ai_core_ls_lp_axi_s_arburst ),
		.ARLOCK( ai_core_ls_lp_axi_s_arlock),
		.ARCACHE( ai_core_ls_lp_axi_s_arcache ),
		.ARPROT( ai_core_ls_lp_axi_s_arprot ),
		.ARID( ai_core_ls_lp_axi_s_arid ),
		.ARREADY( ai_core_ls_lp_axi_s_arready ),
		.RREADY( ai_core_ls_lp_axi_s_rready ),
		.RVALID( ai_core_ls_lp_axi_s_rvalid ),
		.RLAST( ai_core_ls_lp_axi_s_rlast ),
		.RDATA(  ai_core_ls_lp_axi_s_rdata ),
		.RRESP( ai_core_ls_lp_axi_s_rresp ),
		.RID( ai_core_ls_lp_axi_s_rid ),
		.AWVALID( ai_core_ls_lp_axi_s_awvalid ),
		 .AWADDR( ai_core_ls_lp_axi_s_awaddr ),
		 .AWLEN( ai_core_ls_lp_axi_s_awlen),
		 .AWSIZE( ai_core_ls_lp_axi_s_awsize ),
		 .AWBURST( ai_core_ls_lp_axi_s_awburst ),
		 .AWLOCK( ai_core_ls_lp_axi_s_awlock ),
		 .AWCACHE( ai_core_ls_lp_axi_s_awcache ),
		 .AWPROT( ai_core_ls_lp_axi_s_awprot ),
		 .AWID( ai_core_ls_lp_axi_s_awid ),
		 .AWREADY( ai_core_ls_lp_axi_s_awready ),
		 .WVALID( ai_core_ls_lp_axi_s_wvalid ),
		 .WLAST( ai_core_ls_lp_axi_s_wlast ),
	   .WDATA(  ai_core_ls_lp_axi_s_wdata ),
		 .WSTRB( ai_core_ls_lp_axi_s_wstrb ),
		 .WREADY( ai_core_ls_lp_axi_s_wready),
		 .BREADY( ai_core_ls_lp_axi_s_bready ),
		 .BVALID( ai_core_ls_lp_axi_s_bvalid ),
		 .BRESP( ai_core_ls_lp_axi_s_bresp ),
		 .BID( ai_core_ls_lp_axi_s_bid  ),
		 .AWUSER( 32'h0 ),
		 .WUSER( 32'h0 ),
		 .ARUSER( 32'h0 ),
		 .RUSER( 32'h0 ),
		 .BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)

     );









