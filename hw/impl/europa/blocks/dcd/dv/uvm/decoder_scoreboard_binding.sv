
`define DECODER_PATH dut.I_TOP
import allegro_codec_pkg::*;

`ifdef USE_ALLEGRO_IP_TOP

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)
) axi_mcu_if (
  .awaddr         (awaddr_mcu    ),
  .awvalid        (awvalid_mcu   ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (awlen_mcu     ),
  .awburst        (awburst_mcu   ),
  .awsize         (awsize_mcu    ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (awid_mcu      ),
  .awready        (awready_mcu   ),
  .araddr         (araddr_mcu    ),
  .arvalid        (arvalid_mcu   ),
  .awakeup        ('h0),
  .arlen          (arlen_mcu     ),
  .arburst        (arburst_mcu   ),
  .arsize         (arsize_mcu    ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (arid_mcu      ),
  .arready        (arready_mcu   ),
  .wdata          (wdata_mcu     ),
  .wvalid         (wvalid_mcu    ),
  .wstrb          (wstrb_mcu     ),
  .wlast          (wlast_mcu     ),
  .wid            ('h0),
  .wready         (wready_mcu    ),
  .rdata          (rdata_mcu     ),
  .rvalid         (rvalid_mcu    ),
  .rlast          (rlast_mcu     ),
  .rresp          (rresp_mcu     ),
  .rid            (rid_mcu       ),
  .rready         (rready_mcu    ),
  .bresp          (bresp_mcu     ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (bvalid_mcu   ),
  .bid            (bid_mcu      ),
  .bready         (bready_mcu   )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_mcu (decoder_if.axi_if.master_if[0].svt_axi_master_async_modport, `DECODER_PATH.axi_mcu_if);

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)

) axi_core0_if (
  .awaddr         (awaddr0     ),
  .awvalid        (awvalid0    ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (awlen0      ),
  .awburst        (awburst0    ),
  .awsize         (awsize0     ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (awid0       ),
  .awready        (awready0    ),
  .araddr         (araddr0     ),
  .arvalid        (arvalid0    ),
  .awakeup        ('h0),
  .arlen          (arlen0      ),
  .arburst        (arburst0    ),
  .arsize         (arsize0     ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (arid0       ),
  .arready        (arready0    ),
  .wdata          (wdata0      ),
  .wvalid         (wvalid0     ),
  .wstrb          (wstrb0      ),
  .wlast          (wlast0      ),
  .wid            ('h0),
  .wready         (wready0     ),
  .rdata          (rdata0      ),
  .rvalid         (rvalid0     ),
  .rlast          (rlast0      ),
  .rresp          (rresp0      ),
  .rid            (rid0        ),
  .rready         (rready0     ),
  .bresp          (bresp0      ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (bvalid0    ),
  .bid            (bid0       ),
  .bready         (bready0    )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_core0 (decoder_if.axi_if.master_if[1].svt_axi_master_async_modport, `DECODER_PATH.axi_core0_if);

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)

) axi_core1_if (
  .awaddr         (awaddr1     ),
  .awvalid        (awvalid1    ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (awlen1      ),
  .awburst        (awburst1    ),
  .awsize         (awsize1     ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (awid1       ),
  .awready        (awready1    ),
  .araddr         (araddr1     ),
  .arvalid        (arvalid1    ),
  .awakeup        ('h0),
  .arlen          (arlen1      ),
  .arburst        (arburst1    ),
  .arsize         (arsize1     ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (arid1       ),
  .arready        (arready1    ),
  .wdata          (wdata1      ),
  .wvalid         (wvalid1     ),
  .wstrb          (wstrb1      ),
  .wlast          (wlast1      ),
  .wid            ('h0),
  .wready         (wready1     ),
  .rdata          (rdata1      ),
  .rvalid         (rvalid1     ),
  .rlast          (rlast1      ),
  .rresp          (rresp1      ),
  .rid            (rid1        ),
  .rready         (rready1     ),
  .bresp          (bresp1      ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (bvalid1    ),
  .bid            (bid1       ),
  .bready         (bready1    )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_core1 (decoder_if.axi_if.master_if[2].svt_axi_master_async_modport, `DECODER_PATH.axi_core1_if);

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)

) axi_postproc_if (
  .awaddr         (awaddr2     ),
  .awvalid        (awvalid2    ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (awlen2      ),
  .awburst        (awburst2    ),
  .awsize         (awsize2     ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (awid2       ),
  .awready        (awready2    ),
  .araddr         (araddr2     ),
  .arvalid        (arvalid2    ),
  .awakeup        ('h0),
  .arlen          (arlen2      ),
  .arburst        (arburst2    ),
  .arsize         (arsize2     ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (arid2       ),
  .arready        (arready2    ),
  .wdata          (wdata2      ),
  .wvalid         (wvalid2     ),
  .wstrb          (wstrb2      ),
  .wlast          (wlast2      ),
  .wid            ('h0),
  .wready         (wready2     ),
  .rdata          (rdata2      ),
  .rvalid         (rvalid2     ),
  .rlast          (rlast2      ),
  .rresp          (rresp2      ),
  .rid            (rid2        ),
  .rready         (rready2     ),
  .bresp          (bresp2      ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (bvalid2    ),
  .bid            (bid2       ),
  .bready         (bready2    )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_postproc (decoder_if.axi_if.master_if[3].svt_axi_master_async_modport, `DECODER_PATH.axi_postproc_if);

decoder_if decoder_if ();
assign decoder_if.axi_if.master_if[0].aresetn = `DECODER_PATH.mrstn;
assign decoder_if.axi_if.master_if[0].aclk    = `DECODER_PATH.mclk;
assign decoder_if.axi_if.master_if[1].aresetn = `DECODER_PATH.rstn;
assign decoder_if.axi_if.master_if[1].aclk    = `DECODER_PATH.clk;
assign decoder_if.axi_if.master_if[2].aresetn = `DECODER_PATH.rstn;
assign decoder_if.axi_if.master_if[2].aclk    = `DECODER_PATH.clk;
assign decoder_if.axi_if.master_if[3].aresetn = `DECODER_PATH.rstn;
assign decoder_if.axi_if.master_if[3].aclk    = `DECODER_PATH.clk;

//-----------------------------------------------------------------------
// APB
//-----------------------------------------------------------------------
//Connect APB Passive Slave IF Signals to `DECODER_PATH Slave IF Pins
assign decoder_if.apb_if.slave_if[0].pclk    = `DECODER_PATH.clk;
assign decoder_if.apb_if.slave_if[0].presetn = `DECODER_PATH.rstn;
assign decoder_if.apb_if.slave_if[0].psel    = `DECODER_PATH.psel;
assign decoder_if.apb_if.slave_if[0].penable = `DECODER_PATH.penable;
assign decoder_if.apb_if.slave_if[0].pwrite  = `DECODER_PATH.pwrite;
assign decoder_if.apb_if.slave_if[0].paddr   = `DECODER_PATH.paddr;
assign decoder_if.apb_if.slave_if[0].pwdata  = `DECODER_PATH.pwdata;
assign decoder_if.apb_if.slave_if[0].pstrb   = 'hF;
assign decoder_if.apb_if.slave_if[0].pprot   = 'h0;
assign decoder_if.apb_if.slave_if[0].prdata  = `DECODER_PATH.prdata;
assign decoder_if.apb_if.slave_if[0].pready  = `DECODER_PATH.pready;
assign decoder_if.apb_if.slave_if[0].pslverr = 'h0;

`else

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)
) axi_mcu_if (
  .awaddr         (o_mcu_axi_m_awaddr    ),
  .awvalid        (o_mcu_axi_m_awvalid   ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (o_mcu_axi_m_awlen     ),
  .awburst        (o_mcu_axi_m_awburst   ),
  .awsize         (o_mcu_axi_m_awsize    ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (o_mcu_axi_m_awid      ),
  .awready        (i_mcu_axi_m_awready   ),
  .araddr         (o_mcu_axi_m_araddr    ),
  .arvalid        (o_mcu_axi_m_arvalid   ),
  .awakeup        ('h0),
  .arlen          (o_mcu_axi_m_arlen     ),
  .arburst        (o_mcu_axi_m_arburst   ),
  .arsize         (o_mcu_axi_m_arsize    ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (o_mcu_axi_m_arid      ),
  .arready        (i_mcu_axi_m_arready   ),
  .wdata          (o_mcu_axi_m_wdata     ),
  .wvalid         (o_mcu_axi_m_wvalid    ),
  .wstrb          (o_mcu_axi_m_wstrb     ),
  .wlast          (o_mcu_axi_m_wlast     ),
  .wid            ('h0),
  .wready         (i_mcu_axi_m_wready    ),
  .rdata          (i_mcu_axi_m_rdata     ),
  .rvalid         (i_mcu_axi_m_rvalid    ),
  .rlast          (i_mcu_axi_m_rlast     ),
  .rresp          (i_mcu_axi_m_rresp     ),
  .rid            (i_mcu_axi_m_rid       ),
  .rready         (o_mcu_axi_m_rready    ),
  .bresp          (i_mcu_axi_m_bresp     ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (i_mcu_axi_m_bvalid   ),
  .bid            (i_mcu_axi_m_bid      ),
  .bready         (o_mcu_axi_m_bready   )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_mcu (decoder_if.axi_if.master_if[0].svt_axi_master_async_modport, `DECODER_PATH.axi_mcu_if);

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)

) axi_core0_if (
  .awaddr         (o_dec_0_axi_m_awaddr    ),
  .awvalid        (o_dec_0_axi_m_awvalid   ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (o_dec_0_axi_m_awlen     ),
  .awburst        (o_dec_0_axi_m_awburst   ),
  .awsize         (o_dec_0_axi_m_awsize    ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (o_dec_0_axi_m_awid      ),
  .awready        (i_dec_0_axi_m_awready   ),
  .araddr         (o_dec_0_axi_m_araddr    ),
  .arvalid        (o_dec_0_axi_m_arvalid   ),
  .awakeup        ('h0),
  .arlen          (o_dec_0_axi_m_arlen     ),
  .arburst        (o_dec_0_axi_m_arburst   ),
  .arsize         (o_dec_0_axi_m_arsize    ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (o_dec_0_axi_m_arid      ),
  .arready        (i_dec_0_axi_m_arready   ),
  .wdata          (o_dec_0_axi_m_wdata     ),
  .wvalid         (o_dec_0_axi_m_wvalid    ),
  .wstrb          (o_dec_0_axi_m_wstrb     ),
  .wlast          (o_dec_0_axi_m_wlast     ),
  .wid            ('h0),
  .wready         (i_dec_0_axi_m_wready    ),
  .rdata          (i_dec_0_axi_m_rdata     ),
  .rvalid         (i_dec_0_axi_m_rvalid    ),
  .rlast          (i_dec_0_axi_m_rlast     ),
  .rresp          (i_dec_0_axi_m_rresp     ),
  .rid            (i_dec_0_axi_m_rid       ),
  .rready         (o_dec_0_axi_m_rready    ),
  .bresp          (i_dec_0_axi_m_bresp     ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (i_dec_0_axi_m_bvalid   ),
  .bid            (i_dec_0_axi_m_bid      ),
  .bready         (o_dec_0_axi_m_bready   )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_core0 (decoder_if.axi_if.master_if[1].svt_axi_master_async_modport, `DECODER_PATH.axi_core0_if);

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)

) axi_core1_if (
  .awaddr         (o_dec_1_axi_m_awaddr    ),
  .awvalid        (o_dec_1_axi_m_awvalid   ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (o_dec_1_axi_m_awlen     ),
  .awburst        (o_dec_1_axi_m_awburst   ),
  .awsize         (o_dec_1_axi_m_awsize    ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (o_dec_1_axi_m_awid      ),
  .awready        (i_dec_1_axi_m_awready   ),
  .araddr         (o_dec_1_axi_m_araddr    ),
  .arvalid        (o_dec_1_axi_m_arvalid   ),
  .awakeup        ('h0),
  .arlen          (o_dec_1_axi_m_arlen     ),
  .arburst        (o_dec_1_axi_m_arburst   ),
  .arsize         (o_dec_1_axi_m_arsize    ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (o_dec_1_axi_m_arid      ),
  .arready        (i_dec_1_axi_m_arready   ),
  .wdata          (o_dec_1_axi_m_wdata     ),
  .wvalid         (o_dec_1_axi_m_wvalid    ),
  .wstrb          (o_dec_1_axi_m_wstrb     ),
  .wlast          (o_dec_1_axi_m_wlast     ),
  .wid            ('h0),
  .wready         (i_dec_1_axi_m_wready    ),
  .rdata          (i_dec_1_axi_m_rdata     ),
  .rvalid         (i_dec_1_axi_m_rvalid    ),
  .rlast          (i_dec_1_axi_m_rlast     ),
  .rresp          (i_dec_1_axi_m_rresp     ),
  .rid            (i_dec_1_axi_m_rid       ),
  .rready         (o_dec_1_axi_m_rready    ),
  .bresp          (i_dec_1_axi_m_bresp     ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (i_dec_1_axi_m_bvalid   ),
  .bid            (i_dec_1_axi_m_bid      ),
  .bready         (o_dec_1_axi_m_bready   )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_core1 (decoder_if.axi_if.master_if[2].svt_axi_master_async_modport, `DECODER_PATH.axi_core1_if);

bind `DECODER_PATH svt_axi_master_bind_if #(
  .AWADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .ARADDR_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_ADDR_WIDTH),
  .AWLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARLEN_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_LEN_WIDTH),
  .ARSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWSIZE_WIDTH_PARAM  (allegro_codec_pkg::CODEC_AXI_SIZE_WIDTH),
  .AWBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARBURST_WIDTH_PARAM (allegro_codec_pkg::CODEC_AXI_BURST_TYPE_WIDTH),
  .ARID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .BID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WID_WIDTH_PARAM     (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .RDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .WSTRB_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_WSTRB_WIDTH),
  .RRESP_WIDTH_PARAM   (1),
  .AWID_WIDTH_PARAM    (allegro_codec_pkg::CODEC_AXI_ID_WIDTH),
  .WDATA_WIDTH_PARAM   (allegro_codec_pkg::CODEC_AXI_DATA_WIDTH),
  .BRESP_WIDTH_PARAM   (1)

) axi_postproc_if (
  .awaddr         (o_dec_2_axi_m_awaddr    ),
  .awvalid        (o_dec_2_axi_m_awvalid   ),
  .acwakeup       ('h0),
  .acvalid        ('h0),
  .awlen          (o_dec_2_axi_m_awlen     ),
  .awburst        (o_dec_2_axi_m_awburst   ),
  .awsize         (o_dec_2_axi_m_awsize    ),
  .awlock         ('h0),
  .awprot         ('h0),
  .awcache        ('h0),
  .awid           (o_dec_2_axi_m_awid      ),
  .awready        (i_dec_2_axi_m_awready   ),
  .araddr         (o_dec_2_axi_m_araddr    ),
  .arvalid        (o_dec_2_axi_m_arvalid   ),
  .awakeup        ('h0),
  .arlen          (o_dec_2_axi_m_arlen     ),
  .arburst        (o_dec_2_axi_m_arburst   ),
  .arsize         (o_dec_2_axi_m_arsize    ),
  .arlock         ('h0),
  .arprot         ('h0),
  .arcache        ('h0),
  .arid           (o_dec_2_axi_m_arid      ),
  .arready        (i_dec_2_axi_m_arready   ),
  .wdata          (o_dec_2_axi_m_wdata     ),
  .wvalid         (o_dec_2_axi_m_wvalid    ),
  .wstrb          (o_dec_2_axi_m_wstrb     ),
  .wlast          (o_dec_2_axi_m_wlast     ),
  .wid            ('h0),
  .wready         (i_dec_2_axi_m_wready    ),
  .rdata          (i_dec_2_axi_m_rdata     ),
  .rvalid         (i_dec_2_axi_m_rvalid    ),
  .rlast          (i_dec_2_axi_m_rlast     ),
  .rresp          (i_dec_2_axi_m_rresp     ),
  .rid            (i_dec_2_axi_m_rid       ),
  .rready         (o_dec_2_axi_m_rready    ),
  .bresp          (i_dec_2_axi_m_bresp     ),
  .rdatachk       (),
  .ruser          ('h0),
  .buser          ('h0),
  .crready        ('h0),
  .cdready        ('h0),
  .cddatachk      ('h0),
  .tready         ('h0),
  .bvalid         (i_dec_2_axi_m_bvalid   ),
  .bid            (i_dec_2_axi_m_bid      ),
  .bready         (o_dec_2_axi_m_bready   )
);
bind alg_ip_top_tb svt_axi_master_connector #(0) master_bind_connector_postproc (decoder_if.axi_if.master_if[3].svt_axi_master_async_modport, `DECODER_PATH.axi_postproc_if);

decoder_if decoder_if ();
assign decoder_if.axi_if.master_if[0].aresetn = `DECODER_PATH.dcd_mcu_rst_n;
assign decoder_if.axi_if.master_if[0].aclk    = `DECODER_PATH.i_mcu_clk;
assign decoder_if.axi_if.master_if[1].aresetn = `DECODER_PATH.dcd_rst_n;
assign decoder_if.axi_if.master_if[1].aclk    = `DECODER_PATH.i_clk;
assign decoder_if.axi_if.master_if[2].aresetn = `DECODER_PATH.dcd_rst_n;
assign decoder_if.axi_if.master_if[2].aclk    = `DECODER_PATH.i_clk;
assign decoder_if.axi_if.master_if[3].aresetn = `DECODER_PATH.dcd_rst_n;
assign decoder_if.axi_if.master_if[3].aclk    = `DECODER_PATH.i_clk;

//-----------------------------------------------------------------------
// APB
//-----------------------------------------------------------------------
//Connect APB Passive Slave IF Signals to `DECODER_PATH Slave IF Pins
assign decoder_if.apb_if.slave_if[0].pclk    = `DECODER_PATH.i_clk;
assign decoder_if.apb_if.slave_if[0].presetn = `DECODER_PATH.dcd_rst_n;
assign decoder_if.apb_if.slave_if[0].psel    = `DECODER_PATH.i_cfg_apb4_s_psel;
assign decoder_if.apb_if.slave_if[0].penable = `DECODER_PATH.i_cfg_apb4_s_penable;
assign decoder_if.apb_if.slave_if[0].pwrite  = `DECODER_PATH.i_cfg_apb4_s_pwrite;
assign decoder_if.apb_if.slave_if[0].paddr   = `DECODER_PATH.i_cfg_apb4_s_paddr;
assign decoder_if.apb_if.slave_if[0].pwdata  = `DECODER_PATH.i_cfg_apb4_s_pwdata;
assign decoder_if.apb_if.slave_if[0].pstrb   = 'hF;
assign decoder_if.apb_if.slave_if[0].pprot   = 'h0;
assign decoder_if.apb_if.slave_if[0].prdata  = `DECODER_PATH.o_cfg_apb4_s_prdata;
assign decoder_if.apb_if.slave_if[0].pready  = `DECODER_PATH.o_cfg_apb4_s_pready;
assign decoder_if.apb_if.slave_if[0].pslverr = `DECODER_PATH.o_cfg_apb4_s_pslverr;


`endif // USE_ALLEGRO_IP_TOP


initial begin
  uvm_config_db#(virtual interface decoder_if)::set(null, "uvm_test_top.m_decoder_env", "vif", decoder_if);
  run_test();
end

