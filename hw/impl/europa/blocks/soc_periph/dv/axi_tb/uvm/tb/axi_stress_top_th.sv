
`include "svt_axi_master_param_if.svi"
`include "svt_apb_slave_if.svi"


module axi_stress_top_th;

  timeunit 1ns; timeprecision 1ps;


  wire  ref_clk;
  wire  emmc_clk;
  wire  periph_clk;
  wire  rst;
  wire  test_mode;
  logic clk_en;

  axe_clk_generator u_axe_clk_generator_ref_clk (
      .i_enable(clk_en),
      .o_clk(ref_clk)
  );

  axe_clk_generator u_axe_clk_generator_emmc_clk (
      .i_enable(clk_en),
      .o_clk(emmc_clk)
  );

  axe_clk_generator u_axe_clk_generator_periph_clk (
      .i_enable(clk_en),
      .o_clk(periph_clk)
  );

  axe_rst_generator u_axe_rst_generator (
      .i_clk(periph_clk),
      .o_rst(rst)
  );

  initial begin
    u_axe_rst_generator.async_rst(.duration_ns(2000));
    u_axe_clk_generator_emmc_clk.set_clock(.freq_mhz(200), .duty(50));
    u_axe_clk_generator_ref_clk.set_clock(.freq_mhz(50), .duty(50));
    u_axe_clk_generator_periph_clk.set_clock(.freq_mhz(100), .duty(50));
    clk_en <= 1'b1;
  end

  svt_axi_if axi_if ();
  svt_axi_master_param_if #(
      .SVT_AXI_ADDR_WIDTH_PARAM(40),
      .SVT_AXI_BURST_LENGTH_WIDTH_PARAM(8),
      .SVT_AXI_DATA_WIDTH_PARAM(64),
      .SVT_AXI_ID_WIDTH_PARAM(4),
      .SVT_AXI_ADDR_USER_WIDTH_PARAM(1),
      .SVT_AXI_DATA_USER_WIDTH_PARAM(1),
      .SVT_AXI_BRESP_USER_WIDTH_PARAM(1)
  ) master_if_0 (
      axi_if.master_if[0]
  );

  assign axi_if.common_aclk = periph_clk;
  assign master_if_0.aresetn = ~rst;
  assign test_mode = 1'b0;

  soc_periph_p u_soc_periph_p (
      .i_ref_clk(ref_clk),
      .i_emmc_clk(emmc_clk),
      .i_periph_clk(periph_clk),
      .i_ao_rst_n(~rst),
      .i_global_rst_n(~rst),
      .test_mode,
      .i_lt_axi_s_awaddr(master_if_0.awaddr),
      .i_lt_axi_s_awid(master_if_0.awid),
      .i_lt_axi_s_awlen(master_if_0.awlen),
      .i_lt_axi_s_awsize(master_if_0.awsize),
      .i_lt_axi_s_awburst(master_if_0.awburst),
      .i_lt_axi_s_awcache(master_if_0.awcache),
      .i_lt_axi_s_awprot(master_if_0.awprot),
      .i_lt_axi_s_awlock(master_if_0.awlock),
      .i_lt_axi_s_awqos(master_if_0.awqos),
      .i_lt_axi_s_awregion(master_if_0.awregion),
      .i_lt_axi_s_awuser(master_if_0.awuser),
      .i_lt_axi_s_awvalid(master_if_0.awvalid),
      .o_lt_axi_s_awready(master_if_0.awready),
      .i_lt_axi_s_wdata(master_if_0.wdata),
      .i_lt_axi_s_wstrb(master_if_0.wstrb),
      .i_lt_axi_s_wlast(master_if_0.wlast),
      .i_lt_axi_s_wuser(master_if_0.wuser),
      .i_lt_axi_s_wvalid(master_if_0.wvalid),
      .o_lt_axi_s_wready(master_if_0.wready),
      .o_lt_axi_s_bvalid(master_if_0.bvalid),
      .o_lt_axi_s_bid(master_if_0.bid),
      .o_lt_axi_s_buser(master_if_0.buser),
      .o_lt_axi_s_bresp(master_if_0.bresp),
      .i_lt_axi_s_bready(master_if_0.bready),
      .i_lt_axi_s_araddr(master_if_0.araddr),
      .i_lt_axi_s_arid(master_if_0.arid),
      .i_lt_axi_s_arlen(master_if_0.arlen),
      .i_lt_axi_s_arsize(master_if_0.arsize),
      .i_lt_axi_s_arburst(master_if_0.arburst),
      .i_lt_axi_s_arcache(master_if_0.arcache),
      .i_lt_axi_s_arprot(master_if_0.arprot),
      .i_lt_axi_s_arqos(master_if_0.arqos),
      .i_lt_axi_s_arregion(master_if_0.arregion),
      .i_lt_axi_s_aruser(master_if_0.aruser),
      .i_lt_axi_s_arlock(master_if_0.arlock),
      .i_lt_axi_s_arvalid(master_if_0.arvalid),
      .o_lt_axi_s_arready(master_if_0.arready),
      .o_lt_axi_s_rvalid(master_if_0.rvalid),
      .o_lt_axi_s_rlast(master_if_0.rlast),
      .o_lt_axi_s_rid(master_if_0.rid),
      .o_lt_axi_s_rdata(master_if_0.rdata),
      .o_lt_axi_s_ruser(master_if_0.ruser),
      .o_lt_axi_s_rresp(master_if_0.rresp),
      .i_lt_axi_s_rready(master_if_0.rready)
  );

endmodule
