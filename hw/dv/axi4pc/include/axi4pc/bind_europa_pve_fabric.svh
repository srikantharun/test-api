`define axi4pc_bind_mst_macro(checker_name, prfx, mst_num, addr_w, data_w, id_w) \
  bind pve_fabric Axi4PC # ( \
          .DATA_WIDTH(data_w), \
          .ADDR_WIDTH(addr_w), \
          .RID_WIDTH(id_w), \
          .WID_WIDTH(id_w), \
          .MAXWBURSTS(512), \
          .MAXRBURSTS(512), \
          .RecommendOn(0), \
          .RecMaxWaitOn(0), \
          .AWREADY_MAXWAITS(256), \
          .ARREADY_MAXWAITS(256), \
          .WREADY_MAXWAITS(256), \
          .BREADY_MAXWAITS(16), \
          .RREADY_MAXWAITS(16) \
          ) \
  AXI_Protocol_checker_``checker_name``( \
          .ACLK(i_clk), \
          .ARESETn(i_rst_n), \
          .ARVALID(o_``prfx``_arvalid[mst_num]), \
          .ARADDR(o_``prfx``_araddr[mst_num]), \
          .ARLEN(o_``prfx``_arlen[mst_num]), \
          .ARSIZE(o_``prfx``_arsize[mst_num]), \
          .ARBURST(o_``prfx``_arburst[mst_num]), \
          .ARLOCK(o_``prfx``_arlock[mst_num]), \
          .ARCACHE(o_``prfx``_arcache[mst_num]), \
          .ARPROT(o_``prfx``_arprot[mst_num]), \
          .ARID(o_``prfx``_arid[mst_num]), \
          .ARREADY(i_``prfx``_arready[mst_num]), \
          .RREADY(o_``prfx``_rready[mst_num]), \
          .RVALID(i_``prfx``_rvalid[mst_num]), \
          .RLAST(i_``prfx``_rlast[mst_num]), \
          .RDATA({i_``prfx``_rdata[mst_num]}), \
          .RRESP(i_``prfx``_rresp[mst_num]), \
          .RID(i_``prfx``_rid[mst_num]), \
          .AWVALID(o_``prfx``_awvalid[mst_num]), \
          .AWADDR(o_``prfx``_awaddr[mst_num]), \
          .AWLEN(o_``prfx``_awlen[mst_num]), \
          .AWSIZE(o_``prfx``_awsize[mst_num]), \
          .AWBURST(o_``prfx``_awburst[mst_num]), \
          .AWLOCK(o_``prfx``_awlock[mst_num]), \
          .AWCACHE(o_``prfx``_awcache[mst_num]), \
          .AWPROT(o_``prfx``_awprot[mst_num]), \
          .AWID(o_``prfx``_awid[mst_num]), \
          .AWREADY(i_``prfx``_awready[mst_num]), \
          .WVALID(o_``prfx``_wvalid[mst_num]), \
          .WLAST(o_``prfx``_wlast[mst_num]), \
          .WDATA(o_``prfx``_wdata[mst_num]), \
          .WSTRB(o_``prfx``_wstrb[mst_num]), \
          .WREADY(i_``prfx``_wready[mst_num]), \
          .BREADY(o_``prfx``_bready[mst_num]), \
          .BVALID(i_``prfx``_bvalid[mst_num]), \
          .BRESP(i_``prfx``_bresp[mst_num]), \
          .BID(i_``prfx``_bid[mst_num]), \
          .AWUSER(32'h0), .WUSER(32'h0), .ARUSER(32'h0), .RUSER(32'h0), .BUSER(32'h0), .AWREGION(4'b0), .AWQOS(4'b0), .ARQOS(4'b0), .ARREGION(4'b0), .CACTIVE(1'b0), .CSYSREQ(1'b0), .CSYSACK(1'b0) \
  );


`define axi4pc_bind_slv_macro(checker_name, prfx, slv_num, addr_w, data_w, id_w) \
  bind pve_fabric Axi4PC # ( \
          .DATA_WIDTH(data_w), \
          .ADDR_WIDTH(addr_w), \
          .RID_WIDTH(id_w), \
          .WID_WIDTH(id_w), \
          .MAXWBURSTS(512), \
          .MAXRBURSTS(512), \
          .RecommendOn(0), \
          .RecMaxWaitOn(0), \
          .AWREADY_MAXWAITS(256), \
          .ARREADY_MAXWAITS(256), \
          .WREADY_MAXWAITS(256), \
          .BREADY_MAXWAITS(16), \
          .RREADY_MAXWAITS(16) \
          ) \
  AXI_Protocol_checker_``checker_name``( \
          .ACLK(i_clk), \
          .ARESETn(i_rst_n), \
          .ARVALID(i_``prfx``_arvalid[slv_num]), \
          .ARADDR(i_``prfx``_araddr[slv_num]), \
          .ARLEN(i_``prfx``_arlen[slv_num]), \
          .ARSIZE(i_``prfx``_arsize[slv_num]), \
          .ARBURST(i_``prfx``_arburst[slv_num]), \
          .ARLOCK(i_``prfx``_arlock[slv_num]), \
          .ARCACHE(i_``prfx``_arcache[slv_num]), \
          .ARPROT(i_``prfx``_arprot[slv_num]), \
          .ARID(i_``prfx``_arid[slv_num]), \
          .ARREADY(o_``prfx``_arready[slv_num]), \
          .RREADY(i_``prfx``_rready[slv_num]), \
          .RVALID(o_``prfx``_rvalid[slv_num]), \
          .RLAST(o_``prfx``_rlast[slv_num]), \
          .RDATA({o_``prfx``_rdata[slv_num]}), \
          .RRESP(o_``prfx``_rresp[slv_num]), \
          .RID(o_``prfx``_rid[slv_num]), \
          .AWVALID(i_``prfx``_awvalid[slv_num]), \
          .AWADDR(i_``prfx``_awaddr[slv_num]), \
          .AWLEN(i_``prfx``_awlen[slv_num]), \
          .AWSIZE(i_``prfx``_awsize[slv_num]), \
          .AWBURST(i_``prfx``_awburst[slv_num]), \
          .AWLOCK(i_``prfx``_awlock[slv_num]), \
          .AWCACHE(i_``prfx``_awcache[slv_num]), \
          .AWPROT(i_``prfx``_awprot[slv_num]), \
          .AWID(i_``prfx``_awid[slv_num]), \
          .AWREADY(o_``prfx``_awready[slv_num]), \
          .WVALID(i_``prfx``_wvalid[slv_num]), \
          .WLAST(i_``prfx``_wlast[slv_num]), \
          .WDATA(i_``prfx``_wdata[slv_num]), \
          .WSTRB(i_``prfx``_wstrb[slv_num]), \
          .WREADY(o_``prfx``_wready[slv_num]), \
          .BREADY(i_``prfx``_bready[slv_num]), \
          .BVALID(o_``prfx``_bvalid[slv_num]), \
          .BRESP(o_``prfx``_bresp[slv_num]), \
          .BID(o_``prfx``_bid[slv_num]), \
          .AWUSER(32'h0), .WUSER(32'h0), .ARUSER(32'h0), .RUSER(32'h0), .BUSER(32'h0), .AWREGION(4'b0), .AWQOS(4'b0), .ARQOS(4'b0), .ARREGION(4'b0), .CACTIVE(1'b0), .CSYSREQ(1'b0), .CSYSACK(1'b0) \
  );

`ifndef SKIP_AXI_PC4_ATOMIC
  `axi4pc_bind_mst_macro(targ_dma0,   lt_axi_m, 0, 40, 64, 8)
  `axi4pc_bind_mst_macro(targ_dma1,   lt_axi_m, 1, 40, 64, 8)
  `axi4pc_bind_mst_macro(targ_clint,  lt_axi_m, 2, 40, 64, 8)
  `axi4pc_bind_mst_macro(targ_perfc,  lt_axi_m, 3, 40, 64, 8)
  `axi4pc_bind_mst_macro(targ_trace,  lt_axi_m, 4, 40, 64, 8)
  `axi4pc_bind_mst_macro(targ_spm,    lt_axi_m, 5, 40, 64, 8)
  `axi4pc_bind_mst_macro(targ_lt_ext, lt_axi_m, 6, 40, 64, 8)
`endif

  `axi4pc_bind_mst_macro(targ_cl0l1,  ht_axi_m, 0, 40, 512, 11)
  `axi4pc_bind_mst_macro(targ_cl1l1,  ht_axi_m, 1, 40, 512, 11)
  `axi4pc_bind_mst_macro(targ_cl2l1,  ht_axi_m, 2, 40, 512, 11)
  `axi4pc_bind_mst_macro(targ_cl3l1,  ht_axi_m, 3, 40, 512, 11)
  `axi4pc_bind_mst_macro(targ_ht_ext, ht_axi_m, 4, 40, 512, 11)

`ifndef SKIP_AXI_PC4_ATOMIC
  `axi4pc_bind_slv_macro(init_cl0cpu0 ,lt_axi_s, 0, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl0cpu1 ,lt_axi_s, 1, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl1cpu0 ,lt_axi_s, 2, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl1cpu1 ,lt_axi_s, 3, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl2cpu0 ,lt_axi_s, 4, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl2cpu1 ,lt_axi_s, 5, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl3cpu0 ,lt_axi_s, 6, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_cl3cpu1 ,lt_axi_s, 7, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_trace   ,lt_axi_s, 8, 40, 64, 4)
  `axi4pc_bind_slv_macro(init_ext     ,lt_axi_s, 9, 40, 64, 4)
`endif

  `axi4pc_bind_slv_macro(init_dma0_0 ,ht_axi_s, 0, 40, 512, 8)
  `axi4pc_bind_slv_macro(init_dma0_1 ,ht_axi_s, 1, 40, 512, 8)
  `axi4pc_bind_slv_macro(init_dma1_0 ,ht_axi_s, 2, 40, 512, 8)
  `axi4pc_bind_slv_macro(init_dma1_1 ,ht_axi_s, 3, 40, 512, 8)

