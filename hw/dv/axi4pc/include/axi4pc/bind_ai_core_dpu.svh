bind dpu Axi4PC # (
  .DATA_WIDTH ( aic_common_pkg::AIC_LT_AXI_DATA_WIDTH       ) ,
  .ADDR_WIDTH ( aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH ) ,
  .RID_WIDTH  ( aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH       ) ,
  .WID_WIDTH  ( aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH       )
)
AXI_AIP_ai_core_dpu_lp_PROTOCOL_CHECKER (
  .ACLK    ( i_clk                   ) ,
  .ARESETn ( i_rst_n                 ) ,
  .ARVALID ( i_dpu_cfg_axi_s_arvalid ) ,
  .ARADDR  ( i_dpu_cfg_axi_s_araddr  ) ,
  .ARLEN   ( i_dpu_cfg_axi_s_arlen   ) ,
  .ARSIZE  ( i_dpu_cfg_axi_s_arsize  ) ,
  .ARBURST ( i_dpu_cfg_axi_s_arburst ) ,
  .ARLOCK  ( 0                       ) ,
  .ARCACHE ( 0                       ) ,
  .ARPROT  ( 0                       ) ,
  .ARID    ( i_dpu_cfg_axi_s_arid    ) ,
  .ARREADY ( o_dpu_cfg_axi_s_arready ) ,
  .RREADY  ( i_dpu_cfg_axi_s_rready  ) ,
  .RVALID  ( o_dpu_cfg_axi_s_rvalid  ) ,
  .RLAST   ( o_dpu_cfg_axi_s_rlast   ) ,
  .RDATA   ( o_dpu_cfg_axi_s_rdata   ) ,
  .RRESP   ( o_dpu_cfg_axi_s_rresp   ) ,
  .RID     ( o_dpu_cfg_axi_s_rid     ) ,
  .AWVALID ( i_dpu_cfg_axi_s_awvalid ) ,
  .AWADDR  ( i_dpu_cfg_axi_s_awaddr  ) ,
  .AWLEN   ( i_dpu_cfg_axi_s_awlen   ) ,
  .AWSIZE  ( i_dpu_cfg_axi_s_awsize  ) ,
  .AWBURST ( i_dpu_cfg_axi_s_awburst ) ,
  .AWLOCK  ( 0                       ) ,
  .AWCACHE ( 0                       ) ,
  .AWPROT  ( 0                       ) ,
  .AWID    ( i_dpu_cfg_axi_s_awid    ) ,
  .AWREADY ( o_dpu_cfg_axi_s_awready ) ,
  .WVALID  ( i_dpu_cfg_axi_s_wvalid  ) ,
  .WLAST   ( i_dpu_cfg_axi_s_wlast   ) ,
  .WDATA   ( i_dpu_cfg_axi_s_wdata   ) ,
  .WSTRB   ( i_dpu_cfg_axi_s_wstrb   ) ,
  .WREADY  ( o_dpu_cfg_axi_s_wready  ) ,
  .BREADY  ( i_dpu_cfg_axi_s_bready  ) ,
  .BVALID  ( o_dpu_cfg_axi_s_bvalid  ) ,
  .BRESP    ( o_dpu_cfg_axi_s_bresp  ) ,
  .BID      ( o_dpu_cfg_axi_s_bid    ) ,
  .AWUSER   ( 32'h0                  ) ,
  .WUSER    ( 32'h0                  ) ,
  .ARUSER   ( 32'h0                  ) ,
  .RUSER    ( 32'h0                  ) ,
  .BUSER    ( 32'h0                  ) ,
  .AWREGION ( 4'b0                   ) ,
  .AWQOS    ( 4'b0                   ) ,
  .ARQOS    ( 4'b0                   ) ,
  .ARREGION ( 4'b0                   ) ,
  .CACTIVE  ( 1'b0                   ) ,
  .CSYSREQ  ( 1'b0                   ) ,
  .CSYSACK  ( 1'b0                   )
);






