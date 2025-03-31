
`include "svt_axi_master_param_if.svi"
`include "svt_axi_slave_param_if.svi"

interface timer_if;
  wire pclk;
  wire timer_int;

  clocking mon_cb @(posedge pclk);
    input timer_int;
  endclocking
endinterface

module spike_top_th;

  timeunit 1ns; timeprecision 1ps;

  wire         ref_clk;
  wire         emmc_clk;
  wire         periph_clk;
  wire         uart_x16_bclk;
  wire         i2c_48Mhz_clk;
  wire         rst;
  wire         rst_i2c_slave;
  logic        clk_en;
  logic        uart_tx;
  wire         uart_rx;
  wire         uart_cts_n;
  wire         uart_rts_n;
  wire         uart_int;
  logic [15:0] i_gpio;
  wire  [15:0] o_gpio;
  wire  [15:0] o_gpio_oe;
  wire         o_gpio_int;
  wire         o_timer_int;
  wire         o_mem_ale_oepad;
  wire         o_mem_ale_iepad;
  wire         o_mem_ale_opad;
  wire         i_mem_cmd_ipad;
  wire         o_mem_cmd_oepad;
  wire         o_mem_cmd_iepad;
  wire         o_mem_cmd_opad;
  wire         o_mem_ctrl_0_oepad;
  wire         o_mem_ctrl_0_iepad;
  wire         i_mem_ctrl_0_ipad;
  wire         o_mem_ctrl_1_oepad;
  wire         o_mem_ctrl_1_iepad;
  wire         o_mem_ctrl_1_opad;
  wire         o_mem_rstbar_oepad;
  wire         o_mem_rstbar_iepad;
  wire         o_mem_rstbar_opad;
  wire         i_mem_lpbk_dqs_ipad;
  wire         o_mem_lpbk_dqs_oepad;
  wire         o_mem_lpbk_dqs_iepad;
  wire         i_mem_dqs_ipad;
  wire         o_mem_dqs_oepad;
  wire         o_mem_dqs_iepad;
  wire         o_mem_rebar_oepad;
  wire         o_mem_rebar_iepad;
  wire         o_mem_rebar_opad;
  wire         i_mem_rebar_ipad;
  wire  [ 7:0] i_mem_data_ipad;
  wire  [ 7:0] o_mem_data_oepad;
  wire  [ 7:0] o_mem_data_iepad;
  wire  [ 7:0] o_mem_data_opad;
  wire         o_mem_webar_oepad;
  wire         o_mem_webar_iepad;
  wire         o_mem_webar_opad;
  wire         o_mem_wpbar_oepad;
  wire         o_mem_wpbar_iepad;
  wire         i_mem_wpbar_ipad;
  wire         test_mode;
  wire         i_i2c_0_clk;
  wire         i_i2c_0_data;
  wire         o_i2c_0_int;
  wire         i_i2c_1_clk;
  wire         i_i2c_1_data;
  wire         o_i2c_1_int;
  wire         o_i2c_0_clk_oe;
  wire         o_i2c_0_data_oe;
  wire         o_i2c_1_clk_oe;
  wire         o_i2c_1_data_oe;

  axe_clk_generator u_axe_clk_generator_emmc_clk (
      .i_enable(clk_en),
      .o_clk(emmc_clk)
  );

  axe_clk_generator u_axe_clk_generator_periph_clk (
      .i_enable(clk_en),
      .o_clk(periph_clk)
  );

  axe_clk_generator u_axe_clk_generator_ref_clk (
      .i_enable(clk_en),
      .o_clk(ref_clk)
  );

  axe_clk_generator u_axe_clk_generator_x16_bclk (
      .i_enable(clk_en),
      .o_clk(uart_x16_bclk)
  );

  axe_clk_generator u_axe_clk_generator_48Mhz_clk (
      .i_enable(clk_en),
      .o_clk(i2c_48Mhz_clk)
  );

  axe_rst_generator u_axe_rst_generator (
      .i_clk(periph_clk),
      .o_rst(rst)
  );

  axe_rst_generator u_axe_rst_generator_i2c_slave (
      .i_clk(periph_clk),
      .o_rst(rst_i2c_slave)
  );

  timer_if tim_if ();

  assign tim_if.pclk = periph_clk;
  assign tim_if.timer_int = o_timer_int;

  initial begin
    u_axe_rst_generator.async_rst(.duration_ns(2000));
    u_axe_clk_generator_emmc_clk.set_clock(.freq_mhz(200), .duty(50));
    u_axe_clk_generator_periph_clk.set_clock(.freq_mhz(100), .duty(50));
    u_axe_clk_generator_ref_clk.set_clock(.freq_mhz(50), .duty(50));
    u_axe_clk_generator_x16_bclk.set_clock(.freq_mhz(1.8432), .duty(50));
    u_axe_clk_generator_48Mhz_clk.set_clock(.freq_mhz(48), .duty(50));
    clk_en <= 1'b1;
    u_axe_rst_generator_i2c_slave.async_rst(.duration_ns(100));
  end

  svt_axi_if axi_if ();
  assign axi_if.common_aclk = periph_clk;

  // First interface for SOC_PERIPH AXI PORT
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

  svt_axi_slave_param_if #(
      .SVT_AXI_ADDR_WIDTH_PARAM(40),
      .SVT_AXI_BURST_LENGTH_WIDTH_PARAM(8),
      .SVT_AXI_DATA_WIDTH_PARAM(64),
      .SVT_AXI_ID_WIDTH_PARAM(4)
  ) slave_if_0 (
      axi_if.slave_if[0]
  );
  assign slave_if_0.aresetn = ~rst;

  // Create a SPI slave
  svt_spi_if spi_slave_if (
      .bus_clk(pclk),
      .reset  (rst)
  );

  initial begin
    // FIXME: Waiting for pads to be properly connected
    // Indicate to the EMMC controller that the clock is stable
    force u_soc_periph_p.emmc_outreg_cfg.ics = 1'b1;
  end

  soc_periph_p u_soc_periph_p (
      .i_ref_clk(ref_clk),
      .i_emmc_clk(emmc_clk),
      .i_periph_clk(periph_clk),
      .i_ao_rst_n(~rst),
      .i_global_rst_n(~rst),
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
      .i_lt_axi_s_rready(master_if_0.rready),

      .i_uart_cst_n(uart_cts_n),
      .i_uart_rx(uart_rx),
      .o_uart_rts_n(uart_rts_n),
      .o_uart_tx(uart_tx),
      .o_uart_int(uart_int),

      .o_spi_clk(spi_slave_if.sclk),
      .o_spi_ss_n(spi_slave_if.ss_n),
      .o_spi_sd_oe_n(spi_slave_if.oe_n),
      .o_spi_sd(spi_slave_if.mosi),
      .i_spi_sd(spi_slave_if.miso),

      .i_gpio(i_gpio),
      .o_gpio(o_gpio),
      .o_gpio_int(o_gpio_int),
      .o_gpio_oe(o_gpio_oe),

      .o_timer_int(o_timer_int),


      .o_mem_ale_oepad,
      .o_mem_ale_iepad,
      .o_mem_ale_opad,
      .i_mem_cmd_ipad,
      .o_mem_cmd_oepad,
      .o_mem_cmd_iepad,
      .o_mem_cmd_opad,
      .o_mem_ctrl_0_oepad,
      .o_mem_ctrl_0_iepad,
      .i_mem_ctrl_0_ipad,
      .o_mem_ctrl_1_oepad,
      .o_mem_ctrl_1_iepad,
      .o_mem_ctrl_1_opad,
      .o_mem_rstbar_oepad,
      .o_mem_rstbar_iepad,
      .o_mem_rstbar_opad,
      .i_mem_lpbk_dqs_ipad,
      .o_mem_lpbk_dqs_oepad,
      .o_mem_lpbk_dqs_iepad,
      .i_mem_dqs_ipad,
      .o_mem_dqs_oepad,
      .o_mem_dqs_iepad,
      .o_mem_rebar_oepad,
      .o_mem_rebar_iepad,
      .o_mem_rebar_opad,
      .i_mem_rebar_ipad,
      .i_mem_data_ipad,
      .o_mem_data_oepad,
      .o_mem_data_iepad,
      .o_mem_data_opad,
      .o_mem_webar_oepad,
      .o_mem_webar_iepad,
      .o_mem_webar_opad,
      .o_mem_wpbar_oepad,
      .o_mem_wpbar_iepad,
      .i_mem_wpbar_ipad,

      .o_lt_axi_m_awaddr(slave_if_0.awaddr[21:0]),
      .o_lt_axi_m_awlen(slave_if_0.awlen),
      .o_lt_axi_m_awsize(slave_if_0.awsize),
      .o_lt_axi_m_awburst(slave_if_0.awburst),
      .o_lt_axi_m_awcache(slave_if_0.awcache),
      .o_lt_axi_m_awprot(slave_if_0.awprot),
      .o_lt_axi_m_awlock(slave_if_0.awlock),
      .o_lt_axi_m_awqos(slave_if_0.awqos),
      .o_lt_axi_m_awregion(slave_if_0.awregion),
      .o_lt_axi_m_awuser(slave_if_0.awuser),
      .o_lt_axi_m_awvalid(slave_if_0.awvalid),
      .i_lt_axi_m_awready(slave_if_0.awready),
      .o_lt_axi_m_wdata(slave_if_0.wdata),
      .o_lt_axi_m_wstrb(slave_if_0.wstrb),
      .o_lt_axi_m_wlast(slave_if_0.wlast),
      .o_lt_axi_m_wuser(slave_if_0.wuser),
      .o_lt_axi_m_wvalid(slave_if_0.wvalid),
      .i_lt_axi_m_wready(slave_if_0.wready),
      .i_lt_axi_m_bvalid(slave_if_0.bvalid),
      .i_lt_axi_m_buser(slave_if_0.buser),
      .i_lt_axi_m_bresp(slave_if_0.bresp),
      .o_lt_axi_m_bready(slave_if_0.bready),
      .o_lt_axi_m_araddr(slave_if_0.araddr[21:0]),
      .o_lt_axi_m_arlen(slave_if_0.arlen),
      .o_lt_axi_m_arsize(slave_if_0.arsize),
      .o_lt_axi_m_arburst(slave_if_0.arburst),
      .o_lt_axi_m_arcache(slave_if_0.arcache),
      .o_lt_axi_m_arprot(slave_if_0.arprot),
      .o_lt_axi_m_arqos(slave_if_0.arqos),
      .o_lt_axi_m_arregion(slave_if_0.arregion),
      .o_lt_axi_m_aruser(slave_if_0.aruser),
      .o_lt_axi_m_arlock(slave_if_0.arlock),
      .o_lt_axi_m_arvalid(slave_if_0.arvalid),
      .i_lt_axi_m_arready(slave_if_0.arready),
      .i_lt_axi_m_rvalid(slave_if_0.rvalid),
      .i_lt_axi_m_rlast(slave_if_0.rlast),
      .i_lt_axi_m_rdata(slave_if_0.rdata),
      .i_lt_axi_m_ruser(slave_if_0.ruser),
      .i_lt_axi_m_rresp(slave_if_0.rresp),
      .o_lt_axi_m_rready(slave_if_0.rready),
      .i_i2c_0_clk,
      .i_i2c_0_data,
      .o_i2c_0_int,

      .i_i2c_1_clk,
      .i_i2c_1_data,
      .o_i2c_1_int,

      .o_i2c_0_clk_oe,
      .o_i2c_0_data_oe,
      .o_i2c_1_clk_oe,
      .o_i2c_1_data_oe,
      .test_mode ('0),
      .scan_en ('0)
      // .test_clk ('0),
      // .edt_update ('0),
      // .scan_in ('0),
      // .scan_out (),
      // .bisr_clk ('0),
      // .bisr_reset ('0),
      // .bisr_shift_en ('0),
      // .bisr_si ('0),
      // .bisr_so ()

      // FIXME: Determine how to handle these connections.
      // See: https://git.axelera.ai/prod/europa/-/issues/1424
      // .o_lt_axi_m_arid(slave_if_0.arid),
      // .i_lt_axi_m_bid(slave_if_0.bid),
      // .i_lt_axi_m_rid(slave_if_0.rid),
      // .o_lt_axi_m_awid(slave_if_0.awid),

      // TODO: Connect these wires
      //
      // .o_spi_int,
      //
      // .ijtag_tck,
      // .ijtag_reset,
      // .ijtag_sel,
      // .ijtag_ue,
      // .ijtag_se,
      // .ijtag_ce,
      // .ijtag_si,
      // .ijtag_so,
      //
      // .i_uart_tx_ret,
      // .i_uart_tx_pde,
      // .i_uart_tx_mcsw,
      // .i_uart_tx_se,
      // .i_uart_tx_mcs,
      // .i_uart_tx_adme,
      // .o_uart_tx_prn,
      // .i_uart_rx_ret,
      // .i_uart_rx_pde,
      // .i_uart_rx_mcsw,
      // .i_uart_rx_se,
      // .i_uart_rx_mcs,
      // .i_uart_rx_adme,
      // .o_uart_rx_prn
  );

  // FIXME: Temporary fix
  // See: https://git.axelera.ai/prod/europa/-/issues/1424
  assign slave_if_0.arid = 0;
  assign slave_if_0.awid = 0;
  assign slave_if_0.wid = 0;
  assign slave_if_0.awaddr[39:22] = 'h0;
  assign slave_if_0.araddr[39:22] = 'h0;

  //--------------------------------------------------------
  // UART TRANSACTOR CONFIG
  //--------------------------------------------------------
  uart_xactor #(
      .CLK_SAMPLES(16)
  ) u_uart_xactor (
      .clk(uart_x16_bclk),
      .rx (uart_tx),
      .tx (uart_rx)
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
      .clk          (periph_clk),
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

  //--------------------------------------------------------
  // I2C SLAVE CONFIG
  //--------------------------------------------------------
  wire sda_0;
  wire scl_0;
  wire sda_1;
  wire scl_1;

  i2cSlave u_i2c0_slave (
      .clk(i2c_48Mhz_clk),
      .rst(rst_i2c_slave),
      .sda(sda_0),
      .scl(scl_0)
  );

  i2cSlave u_i2c1_slave (
      .clk(i2c_48Mhz_clk),
      .rst(rst_i2c_slave),
      .sda(sda_1),
      .scl(scl_1)
  );


  //--------------------------------------------------------
  // I2C MASTER CONFIG
  //--------------------------------------------------------
  i2c_master_if i2c0_master_if ();
  i2c_master_if i2c1_master_if ();
  assign i2c0_master_if.arst_i   = ~rst;
  assign i2c1_master_if.arst_i   = ~rst;
  assign i2c0_master_if.wb_clk_i = i2c_48Mhz_clk;
  assign i2c1_master_if.wb_clk_i = i2c_48Mhz_clk;

  initial begin
    i2c0_master_if.wb_cyc_i <= 1'b0;
    i2c0_master_if.wb_stb_i <= 1'b0;
    i2c0_master_if.wb_we_i  <= 1'b0;
    i2c0_master_if.wb_adr_i <= 'h0;
    i2c1_master_if.wb_cyc_i <= 1'b0;
    i2c1_master_if.wb_stb_i <= 1'b0;
    i2c1_master_if.wb_we_i  <= 1'b0;
    i2c1_master_if.wb_adr_i <= 'h0;
  end

  i2c_master_top u_i2c0_master (
      // wishbone interface
      .wb_clk_i(i2c0_master_if.wb_clk_i),
      .wb_rst_i(1'b0),  // Unused
      .arst_i(i2c0_master_if.arst_i),
      .wb_adr_i(i2c0_master_if.wb_adr_i),
      .wb_dat_i(i2c0_master_if.wb_dat_i),
      .wb_dat_o(i2c0_master_if.wb_dat_o),
      .wb_we_i(i2c0_master_if.wb_we_i),
      .wb_stb_i(i2c0_master_if.wb_stb_i),
      .wb_cyc_i(i2c0_master_if.wb_cyc_i),
      .wb_ack_o(i2c0_master_if.wb_ack_o),
      .wb_inta_o(i2c0_master_if.wb_inta_o),
      // i2c signals
      .scl_pad_i(i2c0_master_if.scl_pad_i),
      .scl_pad_o(i2c0_master_if.scl_pad_o),
      .scl_padoen_o(i2c0_master_if.scl_padoen_o),
      .sda_pad_i(i2c0_master_if.sda_pad_i),
      .sda_pad_o(i2c0_master_if.sda_pad_o),
      .sda_padoen_o(i2c0_master_if.sda_padoen_o)
  );

  i2c_master_top u_i2c1_master (
      // wishbone interface
      .wb_clk_i(i2c1_master_if.wb_clk_i),
      .wb_rst_i(1'b0),  // Unused
      .arst_i(i2c1_master_if.arst_i),
      .wb_adr_i(i2c1_master_if.wb_adr_i),
      .wb_dat_i(i2c1_master_if.wb_dat_i),
      .wb_dat_o(i2c1_master_if.wb_dat_o),
      .wb_we_i(i2c1_master_if.wb_we_i),
      .wb_stb_i(i2c1_master_if.wb_stb_i),
      .wb_cyc_i(i2c1_master_if.wb_cyc_i),
      .wb_ack_o(i2c1_master_if.wb_ack_o),
      .wb_inta_o(i2c1_master_if.wb_inta_o),
      // i2c signals
      .scl_pad_i(i2c1_master_if.scl_pad_i),
      .scl_pad_o(i2c1_master_if.scl_pad_o),
      .scl_padoen_o(i2c1_master_if.scl_padoen_o),
      .sda_pad_i(i2c1_master_if.sda_pad_i),
      .sda_pad_o(i2c1_master_if.sda_pad_o),
      .sda_padoen_o(i2c1_master_if.sda_padoen_o)
  );

  //--------------------------------------------------------
  // I2C WIRES CONNECTION
  //--------------------------------------------------------

  assign i_i2c_0_data = sda_0;
  assign i_i2c_1_data = sda_1;
  assign i_i2c_0_clk  = scl_0;
  assign i_i2c_1_clk  = scl_1;

  assign i2c0_master_if.sda_pad_i = sda_0;
  assign i2c0_master_if.scl_pad_i = scl_0;
  assign i2c1_master_if.sda_pad_i = sda_1;
  assign i2c1_master_if.scl_pad_i = scl_1;

  assign sda_0 = ((o_i2c_0_data_oe === 1'b1) || (i2c0_master_if.sda_padoen_o === 1'b0)) ? 1'b0 : 1'bZ;
  assign scl_0 = ((o_i2c_0_clk_oe === 1'b1) || (i2c0_master_if.scl_padoen_o === 1'b0)) ? 1'b0: 1'bZ;
  pullup (sda_0);
  pullup (scl_0);

  assign sda_1 = ((o_i2c_1_data_oe === 1'b1) || (i2c1_master_if.sda_padoen_o === 1'b0)) ? 1'b0 : 1'bZ;
  assign scl_1 = ((o_i2c_1_clk_oe === 1'b1) || (i2c1_master_if.scl_padoen_o === 1'b0)) ? 1'b0: 1'bZ;
  pullup (sda_1);
  pullup (scl_1);


  //--------------------------------------------------------
  // EMMC VIP CONFIG
  //--------------------------------------------------------
  sd_4v00_if sd_if ();
  uhsii_link_phy16_if uhsii_if (
      sd_if.rst_n,
      1'b0
  );
  wire dat2_pu_pd_s;
  assign sd_if.cle = 1'b0;  // Disable current limit error (see ECL p. 113 of cdns spec)
  assign sd_if.bus_lvs = 1'b0;  // Only support high-voltage mode

  // Connections taken from /home/projects/SD_EMMC_EVAL/cdn_nv5401__ip6061_ip6185___r602v2p1_r007v1p1_20220705/cdns_sdhc/func_ver/sanity/c_env/sv/tb_harness.sv

  // ALL PAD ENABLE SIGNALS ARE ACTIVE LOW

  // mem_wpbar connection
  assign i_mem_wpbar_ipad = (o_mem_wpbar_iepad === 'b0) ? sd_if.sdwp_n : 1'b0;

  // mem_webar connection
  assign sd_if.clk = (o_mem_webar_oepad === 'b0) ? o_mem_webar_opad : 1'bZ;

  // mem_data connection
  assign i_mem_data_ipad = (o_mem_data_iepad === 'b0) ? sd_if.dat : 1'b1;
  generate
    for (genvar i = 0; i < 8; i++) begin
      pullup (sd_if.dat[i]);
      assign sd_if.dat[i] = (o_mem_data_oepad[i] === 1'b0) ? o_mem_data_opad[i] : 1'bz;
    end
  endgenerate

  // mem_dqs connection
  pullup (sd_if.ds_i);
  assign i_mem_dqs_ipad = (o_mem_dqs_iepad === 'b0) ? sd_if.ds_i : 1'b1;

  // mem_cmd connection
  pullup (sd_if.cmd);
  assign i_mem_cmd_ipad = (o_mem_cmd_iepad === 'b0) ? sd_if.cmd : 1'b1; // Set it to 1 by default to avoid X propagation
  assign sd_if.cmd = (o_mem_cmd_oepad === 'b0) ? o_mem_cmd_opad : 1'bZ;

  // mem_ctrl_0 connection
  assign i_mem_ctrl_0_ipad = (o_mem_ctrl_0_iepad === 'b0) ? sd_if.sdcd_n : 1'b0;

  // mem_ctrl_1 connection
  assign sd_if.bus_pow = (o_mem_ctrl_1_oepad === 'b0) ? o_mem_ctrl_1_opad : 1'bZ;

  // mem_ale connection
  assign dat2_pu_pd_s = (o_mem_ale_oepad === 'b0) ? o_mem_ale_opad : 1'bZ;

  // Map mem_rebar onto mem_lpbk_dqs
  assign i_mem_lpbk_dqs_ipad = (o_mem_rebar_oepad == 'b0) ? o_mem_rebar_opad : 1'bZ;

endmodule
