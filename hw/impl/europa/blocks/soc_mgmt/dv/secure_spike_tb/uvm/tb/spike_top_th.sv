`include "svt_axi_master_param_if.svi"

module spike_top_th;

  timeunit 1ns; timeprecision 1ps;

  logic clk;
  logic rst;
  logic clk_en;
  logic o_ao_rst_n;
  logic o_global_rst_n;
  logic o_fast_clk;
  logic o_apu_clk;
  logic o_ddr_ref_east_clk;
  logic o_codec_clk;
  logic o_emmc_clk;
  logic o_periph_clk;
  logic o_noc_clk;
  logic o_noc_rst_n;
  logic o_security_irq;

  axe_clk_generator u_axe_clk_generator_rot_clk (
      .i_enable(clk_en),
      .o_clk(clk)
  );

  axe_rst_generator u_axe_rst_generator (
      .i_clk(clk),
      .o_rst(rst)
  );

  initial begin
    u_axe_rst_generator.async_rst(.duration_ns(3000));
    u_axe_clk_generator_rot_clk.set_clock(.freq_mhz(1200), .duty(50));
    clk_en <= 1'b1;
  end

  svt_axi_if axi_if ();

  assign axi_if.common_aclk = o_periph_clk;

  // First interface for ROT
  svt_axi_master_param_if #(
      .SVT_AXI_ADDR_WIDTH_PARAM(40),
      .SVT_AXI_BURST_LENGTH_WIDTH_PARAM(8), //TODO needs confirmation
      .SVT_AXI_DATA_WIDTH_PARAM(64),
      .SVT_AXI_ID_WIDTH_PARAM(4),
      .SVT_AXI_ADDR_USER_WIDTH_PARAM(1), //TODO needs confirmation
      .SVT_AXI_DATA_USER_WIDTH_PARAM(1), //TODO needs confirmation
      .SVT_AXI_BRESP_USER_WIDTH_PARAM(1) //TODO needs confirmation
  ) master_if_0 (
      axi_if.master_if[0]
  );
  assign master_if_0.aresetn = ~rst;

  // Second interface for AXI RAM used by uvm_sw_ipc
  svt_axi_master_param_if #(
      .SVT_AXI_ADDR_WIDTH_PARAM(40),
      .SVT_AXI_BURST_LENGTH_WIDTH_PARAM(8),
      .SVT_AXI_DATA_WIDTH_PARAM(64),
      .SVT_AXI_ID_WIDTH_PARAM(4)
  ) master_if_1 (
      axi_if.master_if[1]
  );
  assign master_if_1.aresetn = ~rst;


  soc_mgmt_p u_soc_mgmt_p (
    .i_ref_clk (clk),
    .i_por_rst_n (~rst),
    .o_ao_rst_n (o_ao_rst_n),
    .o_global_rst_n (o_global_rst_n),
    .o_fast_clk (o_fast_clk),
    .o_apu_clk (o_apu_clk),
    .o_ddr_ref_east_clk (o_ddr_ref_east_clk),
    .o_codec_clk (o_codec_clk),
    .o_emmc_clk (o_emmc_clk),
    .o_periph_clk (o_periph_clk),
    .o_noc_clk (o_noc_clk),
    .o_noc_rst_n (o_noc_rst_n),
    .o_lt_axi_m_awaddr (),
    .o_lt_axi_m_awid (),
    .o_lt_axi_m_awlen (),
    .o_lt_axi_m_awsize (),
    .o_lt_axi_m_awburst (),
    .o_lt_axi_m_awcache (),
    .o_lt_axi_m_awprot (),
    .o_lt_axi_m_awlock (),
    .o_lt_axi_m_awqos (),
    .o_lt_axi_m_awregion (),
    .o_lt_axi_m_awuser (),
    .o_lt_axi_m_awvalid (),
    .i_lt_axi_m_awready (),
    .o_lt_axi_m_wvalid (),
    .o_lt_axi_m_wlast (),
    .o_lt_axi_m_wstrb (),
    .o_lt_axi_m_wdata (),
    .o_lt_axi_m_wuser (),
    .i_lt_axi_m_wready ('1),
    .i_lt_axi_m_bvalid ('0),
    .i_lt_axi_m_bid ('0),
    .i_lt_axi_m_bresp ('0),
    .i_lt_axi_m_buser ('0),
    .o_lt_axi_m_bready (),
    .o_lt_axi_m_arvalid (),
    .o_lt_axi_m_araddr (),
    .o_lt_axi_m_arid (),
    .o_lt_axi_m_arlen (),
    .o_lt_axi_m_arsize (),
    .o_lt_axi_m_arburst (),
    .o_lt_axi_m_arcache (),
    .o_lt_axi_m_arprot (),
    .o_lt_axi_m_arqos (),
    .o_lt_axi_m_arregion (),
    .o_lt_axi_m_aruser (),
    .o_lt_axi_m_arlock (),
    .i_lt_axi_m_arready ('1),
    .i_lt_axi_m_rvalid ('0),
    .i_lt_axi_m_rlast ('0),
    .i_lt_axi_m_rid ('0),
    .i_lt_axi_m_rdata ('0),
    .i_lt_axi_m_rresp ('0),
    .i_lt_axi_m_ruser ('0),
    .o_lt_axi_m_rready (),
    .i_lt_axi_s_awvalid (master_if_0.awvalid),
    .i_lt_axi_s_awaddr (master_if_0.awaddr),
    .i_lt_axi_s_awid (master_if_0.awid),
    .i_lt_axi_s_awlen (master_if_0.awlen),
    .i_lt_axi_s_awsize (master_if_0.awsize),
    .i_lt_axi_s_awburst (master_if_0.awburst),
    .i_lt_axi_s_awcache (master_if_0.awcache),
    .i_lt_axi_s_awprot (master_if_0.awprot),
    .i_lt_axi_s_awlock (master_if_0.awlock),
    .i_lt_axi_s_awqos (master_if_0.awqos),
    .i_lt_axi_s_awregion (master_if_0.awregion),
    .i_lt_axi_s_awuser (master_if_0.awuser),
    .o_lt_axi_s_awready (master_if_0.awready),
    .i_lt_axi_s_wvalid (master_if_0.wvalid),
    .i_lt_axi_s_wlast (master_if_0.wlast),
    .i_lt_axi_s_wstrb (master_if_0.wstrb),
    .i_lt_axi_s_wdata (master_if_0.wdata),
    .i_lt_axi_s_wuser (master_if_0.wuser),
    .o_lt_axi_s_wready (master_if_0.wready),
    .o_lt_axi_s_bvalid (master_if_0.bvalid),
    .o_lt_axi_s_bid (master_if_0.bid),
    .o_lt_axi_s_bresp (master_if_0.bresp),
    .o_lt_axi_s_buser (master_if_0.buser),
    .i_lt_axi_s_bready (master_if_0.bready),
    .i_lt_axi_s_arvalid (master_if_0.arvalid),
    .i_lt_axi_s_araddr (master_if_0.araddr),
    .i_lt_axi_s_arid (master_if_0.arid),
    .i_lt_axi_s_arlen (master_if_0.arlen),
    .i_lt_axi_s_arsize (master_if_0.arsize),
    .i_lt_axi_s_arburst (master_if_0.arburst),
    .i_lt_axi_s_arcache (master_if_0.arcache),
    .i_lt_axi_s_arprot (master_if_0.arprot),
    .i_lt_axi_s_arqos (master_if_0.arqos),
    .i_lt_axi_s_arregion (master_if_0.arregion),
    .i_lt_axi_s_aruser (master_if_0.aruser),
    .i_lt_axi_s_arlock (master_if_0.arlock),
    .o_lt_axi_s_arready (master_if_0.arready),
    .o_lt_axi_s_rvalid (master_if_0.rvalid),
    .o_lt_axi_s_rlast (master_if_0.rlast),
    .o_lt_axi_s_rid (master_if_0.rid),
    .o_lt_axi_s_rdata (master_if_0.rdata),
    .o_lt_axi_s_rresp (master_if_0.rresp),
    .o_lt_axi_s_ruser (master_if_0.ruser),
    .i_lt_axi_s_rready (master_if_0.rready),
    .i_syscfg_apb4_s_paddr ('0),
    .i_syscfg_apb4_s_pwdata ('0),
    .i_syscfg_apb4_s_pwrite ('0),
    .i_syscfg_apb4_s_psel ('0),
    .i_syscfg_apb4_s_penable ('0),
    .i_syscfg_apb4_s_pstrb ('0),
    .i_syscfg_apb4_s_pprot ('0),
    .o_syscfg_apb4_s_pready (),
    .o_syscfg_apb4_s_prdata (),
    .o_syscfg_apb4_s_pslverr (),
    .i_thermal_throttle ('0),
    .o_thermal_throttle (),
    .o_thermal_throttle_warning_n (),
    .o_thermal_warning (),
    .o_thermal_shutdown_n (),
    .o_rtc_irq (),
    .o_wdt_irq (),
    .o_security_irq (o_security_irq),
    .tck (clk),
    .trst (rst),
    .tms ('0),
    .tdi ('0),
    .tdo_en (),
    .tdo (),
    .test_mode ('0),
    .i_dft_spare ('0),
    .o_dft_spare (),
    .ssn_bus_clk ('0),
    .ssn_bus_data_in ('0),
    .ssn_bus_data_out (),
    .bisr_clk ('0),
    .bisr_reset ('0),
    .bisr_shift_en ('0),
    .bisr_si ('0),
    .bisr_so (),
    .i_auto_repair_done ('0),
    .o_debugint (),
    .o_resethaltreq (),
    .i_hart_unavail ('0),
    .i_hart_under_reset ('0),
    .i_dft_otp_test_mode ('0),
    .i_dft_otp_tst_a ('0),
    .i_dft_otp_tst_din ('0),
    .i_dft_otp_tst_readen ('0),
    .i_dft_otp_tst_ceb ('0),
    .i_dft_otp_tst_cle ('0),
    .i_dft_otp_tst_dle ('0),
    .i_dft_otp_tst_web ('0),
    .i_dft_otp_tst_rstb ('0),
    .i_dft_otp_tst_cpumpen ('0),
    .i_dft_otp_tst_pgmen ('0),
    .i_dft_otp_tst_seltm ('0),
    .o_dft_otp_tst_d (),
    .o_dft_otp_tst_lock (),
    .i_obs_bus ('0),
    .o_obs_bus (),
    .o_global_sync (),
    .io_otp_vtdo (),
    .io_otp_vrefm (),
    .io_otp_vpp (),
    .io_pvt_ibias_ts (),
    .io_pvt_vsense_ts (),
    .io_pvt_test_out_ts (),
    .io_efuse_vqps (),
    .io_efuse_vddwl ()
  );


  //--------------------------------------------------------
  // UVM SW IPC CONFIG
  //--------------------------------------------------------
  `include "uvm_sw_ipc_connections.sv"

  // Add RAM for uvm_sw_ipc
  dv_axi_ram #(
      .ADDR_WIDTH(40),
      .DATA_WIDTH(64),
      .ID_WIDTH  (4)
  ) u_dv_axi_ram (
      .clk          (o_periph_clk),
      .rst          (rst),
      .s_axi_awid   (master_if_1.awid),
      .s_axi_awaddr (master_if_1.awaddr),
      .s_axi_awlen  (master_if_1.awlen),
      .s_axi_awsize (master_if_1.awsize),
      .s_axi_awburst(master_if_1.awburst),
      .s_axi_awlock (master_if_1.awlock),
      .s_axi_awcache(master_if_1.awcache),
      .s_axi_awprot (master_if_1.awprot),
      .s_axi_awvalid(master_if_1.awvalid),
      .s_axi_awready(master_if_1.awready),
      .s_axi_wdata  (master_if_1.wdata),
      .s_axi_wstrb  (master_if_1.wstrb),
      .s_axi_wlast  (master_if_1.wlast),
      .s_axi_wvalid (master_if_1.wvalid),
      .s_axi_wready (master_if_1.wready),
      .s_axi_bid    (master_if_1.bid),
      .s_axi_bresp  (master_if_1.bresp),
      .s_axi_bvalid (master_if_1.bvalid),
      .s_axi_bready (master_if_1.bready),
      .s_axi_arid   (master_if_1.arid),
      .s_axi_araddr (master_if_1.araddr),
      .s_axi_arlen  (master_if_1.arlen),
      .s_axi_arsize (master_if_1.arsize),
      .s_axi_arburst(master_if_1.arburst),
      .s_axi_arlock (master_if_1.arlock),
      .s_axi_arcache(master_if_1.arcache),
      .s_axi_arprot (master_if_1.arprot),
      .s_axi_arvalid(master_if_1.arvalid),
      .s_axi_arready(master_if_1.arready),
      .s_axi_rid    (master_if_1.rid),
      .s_axi_rdata  (master_if_1.rdata),
      .s_axi_rresp  (master_if_1.rresp),
      .s_axi_rlast  (master_if_1.rlast),
      .s_axi_rvalid (master_if_1.rvalid),
      .s_axi_rready (master_if_1.rready)
  );

endmodule
