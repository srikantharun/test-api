`ifdef AXI_VIP
  // VIP Interface instance representing the AXI system
  assign dwpu_axi_if.common_aclk = clk;

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
  assign dwpu_axi_if.master_if[0].aresetn = axi_reset_if.reset;
  assign dwpu_axi_if.master_if[1].aresetn = axi_reset_if.reset;
  assign dwpu_axi_if.slave_if[0].aresetn  = axi_reset_if.reset;

  // AXIS:
  //------------------------------------------------------
  // DWPU IFD0
  assign dwpu_axi_if.master_if[1].tvalid   = `DWPU_SLV.dwpu_ifd0_axis_s_tvalid ;  //  TB output port
  assign dwpu_axi_if.master_if[1].tready   = `DWPU_SLV.dwpu_ifd0_axis_s_tready ;  //  TB input port
  assign dwpu_axi_if.master_if[1].tdata    = `DWPU_SLV.dwpu_ifd0_axis_s_tdata  ;  //  TB output port
  assign dwpu_axi_if.master_if[1].tlast    = `DWPU_SLV.dwpu_ifd0_axis_s_tlast  ;  //  TB Output port


  // DWPU IAU
  assign dwpu_axi_if.slave_if[0].tvalid    = `DWPU_SLV.dwpu_iau_axis_m_tvalid ; // TB input port
  assign dwpu_axi_if.slave_if[0].tready    = `DWPU_SLV.dwpu_iau_axis_m_tready ; // TB output port
  assign dwpu_axi_if.slave_if[0].tdata     = `DWPU_SLV.dwpu_iau_axis_m_tdata  ; // TB input port
  assign dwpu_axi_if.slave_if[0].tlast     = `DWPU_SLV.dwpu_iau_axis_m_tlast  ; // TB input port

 // AXI LP interface
`ifdef AXI_VIP_CONN_M
  assign dwpu_axi_if.master_if[0].awvalid  = `DWPU_SLV.ai_core_dwpu_axi_s_awvalid;
  assign dwpu_axi_if.master_if[0].awaddr   = `DWPU_SLV.ai_core_dwpu_axi_s_awaddr ;
  assign dwpu_axi_if.master_if[0].awid     = `DWPU_SLV.ai_core_dwpu_axi_s_awid   ;
  assign dwpu_axi_if.master_if[0].awlen    = `DWPU_SLV.ai_core_dwpu_axi_s_awlen  ;
  assign dwpu_axi_if.master_if[0].awsize   = `DWPU_SLV.ai_core_dwpu_axi_s_awsize ;
  assign dwpu_axi_if.master_if[0].awburst  = `DWPU_SLV.ai_core_dwpu_axi_s_awburst;
  assign dwpu_axi_if.master_if[0].awlock   = `DWPU_SLV.ai_core_dwpu_axi_s_awlock ;
  assign dwpu_axi_if.master_if[0].awcache  = `DWPU_SLV.ai_core_dwpu_axi_s_awcache;
  assign dwpu_axi_if.master_if[0].awprot   = `DWPU_SLV.ai_core_dwpu_axi_s_awprot ;

  assign dwpu_axi_if.master_if[0].awready  = `DWPU_SLV.ai_core_dwpu_axi_s_awready;

  assign dwpu_axi_if.master_if[0].wvalid   = `DWPU_SLV.ai_core_dwpu_axi_s_wvalid;
  assign dwpu_axi_if.master_if[0].wlast    = `DWPU_SLV.ai_core_dwpu_axi_s_wlast ;
  assign dwpu_axi_if.master_if[0].wdata    = `DWPU_SLV.ai_core_dwpu_axi_s_wdata ;
  assign dwpu_axi_if.master_if[0].wstrb    = `DWPU_SLV.ai_core_dwpu_axi_s_wstrb ;

  assign dwpu_axi_if.master_if[0].wready   = `DWPU_SLV.ai_core_dwpu_axi_s_wready;

  assign dwpu_axi_if.master_if[0].bvalid   = `DWPU_SLV.ai_core_dwpu_axi_s_bvalid;
  assign dwpu_axi_if.master_if[0].bid      = `DWPU_SLV.ai_core_dwpu_axi_s_bid;
  assign dwpu_axi_if.master_if[0].bresp    = `DWPU_SLV.ai_core_dwpu_axi_s_bresp;

  assign dwpu_axi_if.master_if[0].bready   = `DWPU_SLV.ai_core_dwpu_axi_s_bready;

  assign dwpu_axi_if.master_if[0].arvalid  = `DWPU_SLV.ai_core_dwpu_axi_s_arvalid;
  assign dwpu_axi_if.master_if[0].araddr   = `DWPU_SLV.ai_core_dwpu_axi_s_araddr ;
  assign dwpu_axi_if.master_if[0].arid     = `DWPU_SLV.ai_core_dwpu_axi_s_arid   ;
  assign dwpu_axi_if.master_if[0].arlen    = `DWPU_SLV.ai_core_dwpu_axi_s_arlen  ;
  assign dwpu_axi_if.master_if[0].arsize   = `DWPU_SLV.ai_core_dwpu_axi_s_arsize ;
  assign dwpu_axi_if.master_if[0].arburst  = `DWPU_SLV.ai_core_dwpu_axi_s_arburst;
  assign dwpu_axi_if.master_if[0].arlock   = `DWPU_SLV.ai_core_dwpu_axi_s_arlock ;
  assign dwpu_axi_if.master_if[0].arcache  = `DWPU_SLV.ai_core_dwpu_axi_s_arcache;
  assign dwpu_axi_if.master_if[0].arprot   = `DWPU_SLV.ai_core_dwpu_axi_s_arprot ;

  assign dwpu_axi_if.master_if[0].arready  = `DWPU_SLV.ai_core_dwpu_axi_s_arready;

  assign dwpu_axi_if.master_if[0].rvalid   = `DWPU_SLV.ai_core_dwpu_axi_s_rvalid  ;
  assign dwpu_axi_if.master_if[0].rlast    = `DWPU_SLV.ai_core_dwpu_axi_s_rlast   ;
  assign dwpu_axi_if.master_if[0].rid      = `DWPU_SLV.ai_core_dwpu_axi_s_rid     ;
  assign dwpu_axi_if.master_if[0].rdata    = `DWPU_SLV.ai_core_dwpu_axi_s_rdata   ;
  assign dwpu_axi_if.master_if[0].rresp    = `DWPU_SLV.ai_core_dwpu_axi_s_rresp   ;

  assign dwpu_axi_if.master_if[0].rready   = `DWPU_SLV.ai_core_dwpu_axi_s_rready;

`endif //AXI_VIP_CONN_M
`endif //AXI_VIP
  
assign dwpu_agt_if.reset_an_i = axi_reset_if.reset;
assign dwpu_agt_if.irq_o      = `DWPU_SLV.irq_out;
assign dwpu_agt_if.obs_o      = `DWPU_SLV.ai_core_dwpu_obs;
assign dwpu_agt_if.trace_vld_o      = `DWPU_SLV.ai_core_dwpu_trace_vld;

assign dwpu_tok_agt_if.reset_n      = axi_reset_if.reset;
assign dwpu_tok_agt_if.tok_cons_rdy = `DWPU_SLV.ai_core_dwpu_tok_cons_rdy;
assign dwpu_tok_agt_if.tok_prod_vld = `DWPU_SLV.ai_core_dwpu_tok_prod_vld;
assign dwpu_tok_agt_if.tok_cons_vld = `DWPU_SLV.ai_core_dwpu_tok_cons_vld;
assign dwpu_tok_agt_if.tok_prod_rdy = `DWPU_SLV.ai_core_dwpu_tok_prod_rdy;
