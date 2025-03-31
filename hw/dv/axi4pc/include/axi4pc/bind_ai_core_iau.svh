bind iau Axi4PC 
	AXI_AIP_ai_core_iau_lp_PROTOCOL_CHECKER
				(
				.ACLK     ( i_clk           ) ,
				.ARESETn  ( i_rst_n         ) ,
				.ARVALID  ( i_axi_s_arvalid ) ,
				.ARADDR   ( i_axi_s_araddr  ) ,
				.ARLEN    ( i_axi_s_arlen   ) ,
				.ARSIZE   ( i_axi_s_arsize  ) ,
				.ARBURST  ( i_axi_s_arburst ) ,
				.ARLOCK   ( 0               ) ,
				.ARCACHE  ( 0               ) ,
				.ARPROT   ( 0               ) ,
				.ARID     ( i_axi_s_arid    ) ,
				.ARREADY  ( o_axi_s_arready ) ,
				.RREADY   ( i_axi_s_rready  ) ,
				.RVALID   ( o_axi_s_rvalid  ) ,
				.RLAST    ( o_axi_s_rlast   ) ,
				.RDATA    ( o_axi_s_rdata   ) ,
				.RRESP    ( o_axi_s_rresp   ) ,
				.RID      ( o_axi_s_rid     ) ,
				.AWVALID  ( i_axi_s_awvalid ) ,
				.AWADDR   ( i_axi_s_awaddr  ) ,
				.AWLEN    ( i_axi_s_awlen   ) ,
				.AWSIZE   ( i_axi_s_awsize  ) ,
				.AWBURST  ( i_axi_s_awburst ) ,
				.AWLOCK   ( 0               ) ,
				.AWCACHE  ( 0               ) ,
				.AWPROT   ( 0               ) ,
				.AWID     ( i_axi_s_awid    ) ,
				.AWREADY  ( o_axi_s_awready ) ,
				.WVALID   ( i_axi_s_wvalid  ) ,
				.WLAST    ( i_axi_s_wlast   ) ,
				.WDATA    ( i_axi_s_wdata   ) ,
				.WSTRB    ( i_axi_s_wstrb   ) ,
				.WREADY   ( o_axi_s_wready  ) ,
				.BREADY   ( i_axi_s_bready  ) ,
				.BVALID   ( o_axi_s_bvalid  ) ,
				.BRESP    ( o_axi_s_bresp   ) ,
				.BID      ( o_axi_s_bid     ) ,
				.AWUSER   ( 32'h0           ) ,
				.WUSER    ( 32'h0           ) ,
				.ARUSER   ( 32'h0           ) ,
				.RUSER    ( 32'h0           ) ,
				.BUSER    ( 32'h0           ) ,
        .AWREGION ( 4'b0            ) ,
        .AWQOS    ( 4'b0            ) ,
        .ARQOS    ( 4'b0            ) ,
        .ARREGION ( 4'b0            ) ,
        .CACTIVE  ( 1'b0            ) ,
        .CSYSREQ  ( 1'b0            ) ,
        .CSYSACK  ( 1'b0            )
				);
