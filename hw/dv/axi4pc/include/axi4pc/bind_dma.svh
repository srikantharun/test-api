  // =============================================================================================================
  // AXI Protocol Checkers (on the DUT's AXI Interfaces) 
  // =============================================================================================================

  // Checker on the AXI SLAVE Interface into the DUT (Register Interface)
  // --------------------------------------------------------------------

bind dma Axi4PC
         #(
          .ADDR_WIDTH      (40),
          .DATA_WIDTH      (64),
          .WID_WIDTH       (4),
          .RID_WIDTH       (4),
          .MAXWBURSTS      (16),
          .MAXRBURSTS      (16)

         )  i_bind_axi_chkr_dut_reg_if
         (
          // Global Signals
          .ACLK            (i_clk),
          .ARESETn         (i_rst_n),

          // Write Address Channel
          .AWID            (i_axi_s_awid),
          .AWADDR          (i_axi_s_awaddr),
          .AWLEN           (i_axi_s_awlen),
          .AWSIZE          (i_axi_s_awsize),
          .AWBURST         (i_axi_s_awburst),
          .AWLOCK          (i_axi_s_awlock),
          .AWCACHE         (i_axi_s_awcache),
          .AWPROT          (i_axi_s_awprot),
          .AWQOS           (4'h0),
          .AWREGION        (4'h0),
          .AWUSER          (32'h0000_0000),
          .AWVALID         (i_axi_s_awvalid),
          .AWREADY         (o_axi_s_awready),

          // Write Channel
          .WLAST           (i_axi_s_wlast),
          .WDATA           (i_axi_s_wdata),
          .WSTRB           (i_axi_s_wstrb),
          .WUSER           (32'h0000_0000),
          .WVALID          (i_axi_s_wvalid),
          .WREADY          (o_axi_s_wready),

          // Write Response Channel
          .BID             (o_axi_s_bid),
          .BRESP           (o_axi_s_bresp),
          .BUSER           (32'h0000_0000),
          .BVALID          (o_axi_s_bvalid),
          .BREADY          (i_axi_s_bready),

          // Read Address Channel
          .ARID            (i_axi_s_arid),
          .ARADDR          (i_axi_s_araddr),
          .ARLEN           (i_axi_s_arlen),
          .ARSIZE          (i_axi_s_arsize),
          .ARBURST         (i_axi_s_arburst),
          .ARLOCK          (i_axi_s_arlock),
          .ARCACHE         (i_axi_s_arcache),
          .ARPROT          (i_axi_s_arprot),
          .ARQOS           (4'h0),  
          .ARREGION        (4'h0),  
          .ARUSER          (32'h0000_0000),
          .ARVALID         (i_axi_s_arvalid),
          .ARREADY         (o_axi_s_arready),

          // Read Channel
          .RID             (o_axi_s_rid),
          .RLAST           (o_axi_s_rlast),
          .RDATA           (o_axi_s_rdata),
          .RRESP           (o_axi_s_rresp),
          .RUSER           (32'h0000_0000),
          .RVALID          (o_axi_s_rvalid),
          .RREADY          (i_axi_s_rready),

          // Low power interface
          .CACTIVE         (1'b0),    // AXI-Fabric INACTIVE
          .CSYSREQ         (1'b0),    // But no request to axi-fabric   to enter low-power
          .CSYSACK         (1'b0)     // And no ack     from axi-fabric to enter low-power 
          );

         // Checker on each of the AXI Master Interfaces from the DUT (DMA Transfer Ports)
         // ------------------------------------------------------------------------------
         
bind dma Axi4PC
         #(
          .ADDR_WIDTH      (40),
          .DATA_WIDTH      (512),
          .WID_WIDTH       (9),
          .RID_WIDTH       (9),
          .MAXWBURSTS      (16),
          .MAXRBURSTS      (16)

         )  i_bind_axi_chkr_dut_dma_port0
         (
          // Global Signals
          .ACLK            (i_clk),
          .ARESETn         (i_rst_n),

          // Write Address Channel
          .AWID            (o_axi_m_awid[0]),
          .AWADDR          (o_axi_m_awaddr[0]),
          .AWLEN           (o_axi_m_awlen[0]),
          .AWSIZE          (o_axi_m_awsize[0]),
          .AWBURST         (o_axi_m_awburst[0]),
          .AWLOCK          (o_axi_m_awlock[0]),
          .AWCACHE         (o_axi_m_awcache[0]),
          .AWPROT          (o_axi_m_awprot[0]),
          .AWQOS           (4'h0),    
          .AWREGION        (4'h0),    
          .AWUSER          (32'h0000_0000),
          .AWVALID         (o_axi_m_awvalid[0]),
          .AWREADY         (i_axi_m_awready[0]),

          // Write Channel
          .WLAST           (o_axi_m_wlast[0]),
          .WDATA           (o_axi_m_wdata[0]),
          .WSTRB           (o_axi_m_wstrb[0]),
          .WUSER           (32'h0000_0000),
          .WVALID          (o_axi_m_wvalid[0]),
          .WREADY          (i_axi_m_wready[0]),

          // Write Response Channel
          .BID             (i_axi_m_bid[0]),
          .BRESP           (i_axi_m_bresp[0]),
          .BUSER           (32'h0000_0000),
          .BVALID          (i_axi_m_bvalid[0]),
          .BREADY          (o_axi_m_bready[0]),

          // Read Address Channel
          .ARID            (o_axi_m_arid[0]),
          .ARADDR          (o_axi_m_araddr[0]),
          .ARLEN           (o_axi_m_arlen[0]),
          .ARSIZE          (o_axi_m_arsize[0]),
          .ARBURST         (o_axi_m_arburst[0]),
          .ARLOCK          (o_axi_m_arlock[0]),
          .ARCACHE         (o_axi_m_arcache[0]),
          .ARPROT          (o_axi_m_arprot[0]),
          .ARQOS           (4'h0),    
          .ARREGION        (4'h0),    
          .ARUSER          (32'h0000_0000),
          .ARVALID         (o_axi_m_arvalid[0]),
          .ARREADY         (i_axi_m_arready[0]),

          // Read Channel
          .RID             (i_axi_m_rid[0]),
          .RLAST           (i_axi_m_rlast[0]),
          .RDATA           (i_axi_m_rdata[0]),
          .RRESP           (i_axi_m_rresp[0]),
          .RUSER           (32'h0000_0000),
          .RVALID          (i_axi_m_rvalid[0]),
          .RREADY          (o_axi_m_rready[0]),

          // Low power interface
          .CACTIVE         (1'b0),    // AXI-Fabric INACTIVE
          .CSYSREQ         (1'b0),    // But no request to axi-fabric   to enter low-power
          .CSYSACK         (1'b0)     // And no ack     from axi-fabric to enter low-power 
          );


bind dma Axi4PC
         #(
          .ADDR_WIDTH      (40),
          .DATA_WIDTH      (512),
          .WID_WIDTH       (9),
          .RID_WIDTH       (9),
          .MAXWBURSTS      (16),
          .MAXRBURSTS      (16)

         )  i_bind_axi_chkr_dut_dma_port1
         (
          // Global Signals
          .ACLK            (i_clk),
          .ARESETn         (i_rst_n),

          // Write Address Channel
          .AWID            (o_axi_m_awid[1]),
          .AWADDR          (o_axi_m_awaddr[1]),
          .AWLEN           (o_axi_m_awlen[1]),
          .AWSIZE          (o_axi_m_awsize[1]),
          .AWBURST         (o_axi_m_awburst[1]),
          .AWLOCK          (o_axi_m_awlock[1]),
          .AWCACHE         (o_axi_m_awcache[1]),
          .AWPROT          (o_axi_m_awprot[1]),
          .AWQOS           (4'h0),    
          .AWREGION        (4'h0),    
          .AWUSER          (32'h0000_0000),
          .AWVALID         (o_axi_m_awvalid[1]),
          .AWREADY         (i_axi_m_awready[1]),

          // Write Channel
          .WLAST           (o_axi_m_wlast[1]),
          .WDATA           (o_axi_m_wdata[1]),
          .WSTRB           (o_axi_m_wstrb[1]),
          .WUSER           (32'h0000_0000),
          .WVALID          (o_axi_m_wvalid[1]),
          .WREADY          (i_axi_m_wready[1]),

          // Write Response Channel
          .BID             (i_axi_m_bid[1]),
          .BRESP           (i_axi_m_bresp[1]),
          .BUSER           (32'h0000_0000),
          .BVALID          (i_axi_m_bvalid[1]),
          .BREADY          (o_axi_m_bready[1]),

          // Read Address Channel
          .ARID            (o_axi_m_arid[1]),
          .ARADDR          (o_axi_m_araddr[1]),
          .ARLEN           (o_axi_m_arlen[1]),
          .ARSIZE          (o_axi_m_arsize[1]),
          .ARBURST         (o_axi_m_arburst[1]),
          .ARLOCK          (o_axi_m_arlock[1]),
          .ARCACHE         (o_axi_m_arcache[1]),
          .ARPROT          (o_axi_m_arprot[1]),
          .ARQOS           (4'h0),    
          .ARREGION        (4'h0),    
          .ARUSER          (32'h0000_0000),
          .ARVALID         (o_axi_m_arvalid[1]),
          .ARREADY         (i_axi_m_arready[1]),

          // Read Channel
          .RID             (i_axi_m_rid[1]),
          .RLAST           (i_axi_m_rlast[1]),
          .RDATA           (i_axi_m_rdata[1]),
          .RRESP           (i_axi_m_rresp[1]),
          .RUSER           (32'h0000_0000),
          .RVALID          (i_axi_m_rvalid[1]),
          .RREADY          (o_axi_m_rready[1]),

          // Low power interface
          .CACTIVE         (1'b0),    // AXI-Fabric INACTIVE
          .CSYSREQ         (1'b0),    // But no request to axi-fabric   to enter low-power
          .CSYSACK         (1'b0)     // And no ack     from axi-fabric to enter low-power 
          );

