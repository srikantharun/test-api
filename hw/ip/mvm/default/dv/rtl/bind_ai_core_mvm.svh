bind mvm Axi4PC # (
				.DATA_WIDTH(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
                .ADDR_WIDTH(aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH),
				.RID_WIDTH  (aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
				.WID_WIDTH  (aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
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
	AXI_AIP_AI_CORE_MVM_PROTOCOL_CHECKER
				(
				.ACLK(i_clk),
				.ARESETn(i_rst_n),
				.ARVALID(i_ai_core_mvm_axi_s_arvalid),
				.ARADDR(i_ai_core_mvm_axi_s_araddr ),
				.ARLEN(i_ai_core_mvm_axi_s_arlen),
				.ARSIZE(i_ai_core_mvm_axi_s_arsize),
				.ARBURST( i_ai_core_mvm_axi_s_arburst ),
                //TODO: currently cache/prot/lock signals are not supported by Design
                // currently, tied to 0
                //Kindly update in future
				.ARLOCK(0),
				.ARCACHE(0),
				.ARPROT(0),
				.ARID( i_ai_core_mvm_axi_s_arid ),
				.ARREADY( o_ai_core_mvm_axi_s_arready ),
				.RREADY( i_ai_core_mvm_axi_s_rready ),
				.RVALID( o_ai_core_mvm_axi_s_rvalid ),
				.RLAST( o_ai_core_mvm_axi_s_rlast ),
				.RDATA(  o_ai_core_mvm_axi_s_rdata ),
				.RRESP( o_ai_core_mvm_axi_s_rresp ),
				.RID( o_ai_core_mvm_axi_s_rid ),
				.AWVALID( i_ai_core_mvm_axi_s_awvalid ),
				.AWADDR( i_ai_core_mvm_axi_s_awaddr ),
				.AWLEN( i_ai_core_mvm_axi_s_awlen),
				.AWSIZE( i_ai_core_mvm_axi_s_awsize ),
				.AWBURST( i_ai_core_mvm_axi_s_awburst ),
				.AWLOCK(0),
				.AWCACHE(0),
				.AWPROT(0),
				.AWID( i_ai_core_mvm_axi_s_awid ),
				.AWREADY( o_ai_core_mvm_axi_s_awready ),
				.WVALID( i_ai_core_mvm_axi_s_wvalid ),
				.WLAST( i_ai_core_mvm_axi_s_wlast ),
				.WDATA(  i_ai_core_mvm_axi_s_wdata ),
				.WSTRB( i_ai_core_mvm_axi_s_wstrb ),
				.WREADY( o_ai_core_mvm_axi_s_wready),
				.BREADY( i_ai_core_mvm_axi_s_bready ),
				.BVALID( o_ai_core_mvm_axi_s_bvalid ),
				.BRESP( o_ai_core_mvm_axi_s_bresp ),
				.BID( o_ai_core_mvm_axi_s_bid  ),
				.AWUSER( 32'h0 ),
				.WUSER( 32'h0 ),
				.ARUSER( 32'h0 ),
				.RUSER( 32'h0 ),
				.BUSER(32'h0),  .AWREGION(4'b0) , .AWQOS(4'b0) , .ARQOS(4'b0), .ARREGION(4'b0),.CACTIVE(1'b0),.CSYSREQ(1'b0),.CSYSACK(1'b0)
				);



