iau #(
  `ifdef D_IAU
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_D_IAU_REGION_END_ADDR)
  `else
    .REGION_ST_ADDR(aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_ST_ADDR),
    .REGION_END_ADDR(aic_addr_map_pkg::AIC_LOC_M_IAU_REGION_END_ADDR)
  `endif

)  dut (
  // Clock and reset
  .i_clk                   ( clk                         ) ,
  .i_rst_n                 ( rst_n                       ) ,
  .i_scan_en               (1'b0                         ) ,
  //// AXI subordinate
  // Write Address Channel
  .i_axi_s_awid            ( axi_if.master_if[0].awid    ) ,
  .i_axi_s_awaddr          ( axi_if.master_if[0].awaddr  ) ,
  .i_axi_s_awlen           ( axi_if.master_if[0].awlen   ) ,
  .i_axi_s_awsize          ( axi_if.master_if[0].awsize  ) ,
  .i_axi_s_awburst         ( axi_if.master_if[0].awburst ) ,
  .i_axi_s_awvalid         ( axi_if.master_if[0].awvalid ) ,
  .o_axi_s_awready         ( axi_if.master_if[0].awready ) ,
  // Read Address Channel
  .i_axi_s_arid            ( axi_if.master_if[0].arid    ) ,
  .i_axi_s_araddr          ( axi_if.master_if[0].araddr  ) ,
  .i_axi_s_arlen           ( axi_if.master_if[0].arlen   ) ,
  .i_axi_s_arsize          ( axi_if.master_if[0].arsize  ) ,
  .i_axi_s_arburst         ( axi_if.master_if[0].arburst ) ,
  .i_axi_s_arvalid         ( axi_if.master_if[0].arvalid ) ,
  .o_axi_s_arready         ( axi_if.master_if[0].arready ) ,
  // Write Data Channel
  .i_axi_s_wdata           ( axi_if.master_if[0].wdata   ) ,
  .i_axi_s_wstrb           ( axi_if.master_if[0].wstrb   ) ,
  .i_axi_s_wlast           ( axi_if.master_if[0].wlast   ) ,
  .i_axi_s_wvalid          ( axi_if.master_if[0].wvalid  ) ,
  .o_axi_s_wready          ( axi_if.master_if[0].wready  ) ,
  // Read Data Channel
  .o_axi_s_rid             ( axi_if.master_if[0].rid     ) ,
  .o_axi_s_rdata           ( axi_if.master_if[0].rdata   ) ,
  .o_axi_s_rresp           ( axi_if.master_if[0].rresp   ) ,
  .o_axi_s_rlast           ( axi_if.master_if[0].rlast   ) ,
  .o_axi_s_rvalid          ( axi_if.master_if[0].rvalid  ) ,
  .i_axi_s_rready          ( axi_if.master_if[0].rready  ) ,
  // Write Response Channel
  .o_axi_s_bid             ( axi_if.master_if[0].bid     ) ,
  .o_axi_s_bresp           ( axi_if.master_if[0].bresp   ) ,
  .o_axi_s_bvalid          ( axi_if.master_if[0].bvalid  ) ,
  .i_axi_s_bready          ( axi_if.master_if[0].bready  ) ,
   // Token System
  .o_iau_tok_prod_vld      ( iau_tok_prod_vld            ) ,
  .i_iau_tok_prod_rdy      ( iau_tok_prod_rdy            ) ,
  .i_iau_tok_cons_vld      ( iau_tok_cons_vld            ) ,
  .o_iau_tok_cons_rdy      ( iau_tok_cons_rdy            ) ,
   // AXIS subordinate
  .i_axis_s_tvalid         ( axi_if.master_if[1].tvalid  ) ,
  .i_axis_s_tdata          ( axi_if.master_if[1].tdata   ) ,
  .i_axis_s_tlast          ( axi_if.master_if[1].tlast   ) ,
  .o_axis_s_tready         ( axi_if.master_if[1].tready  ) ,
   // AXIS manager
  .o_axis_m_tvalid         ( axi_if.slave_if[0].tvalid   ) ,
  .o_axis_m_tdata          ( axi_if.slave_if[0].tdata    ) ,
  .o_axis_m_tlast          ( axi_if.slave_if[0].tlast    ) ,
  .i_axis_m_tready         ( axi_if.slave_if[0].tready   ) ,
   // IRQ
  .o_irq                   ( if_iau.irq_o                ) ,
   // Observation
  .o_obs                   ( if_iau.obs_o                ) ,
   // Block Identification
  .i_cid                   ( if_iau.cid_i                ) ,
  .i_block_id              ( if_iau.block_id_i           )
  );
