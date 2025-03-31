// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Stefan Linz <stefan.linz@axelera.ai>

///
module soc_periph
  import chip_pkg::*;
  import axi_pkg::*;
  import soc_periph_pkg::*;
  import axe_tcl_sram_pkg::*;
  import emmc_pkg::emmc_outreg_cfg_t;
  import emmc_pkg::emmc_inreg_cfg_t;
(
  input  wire                         i_emmc_clk,
  input  wire                         i_emmc_rst_n,

  input  wire                         i_periph_clk,
  input  wire                         i_periph_rst_n,


  input  logic                        test_mode,
  input  logic                        scan_en,

  input  emmc_outreg_cfg_t            emmc_outreg_cfg,
  output emmc_inreg_cfg_t             emmc_inreg_cfg,

  input  chip_axi_addr_t              i_lt_axi_s_awaddr,
  input  soc_periph_targ_lt_axi_id_t  i_lt_axi_s_awid,
  input  axi_len_t                    i_lt_axi_s_awlen,
  input  axi_size_t                   i_lt_axi_s_awsize,
  input  axi_burst_t                  i_lt_axi_s_awburst,
  input  axi_cache_t                  i_lt_axi_s_awcache,
  input  axi_prot_t                   i_lt_axi_s_awprot,
  input  logic                        i_lt_axi_s_awlock,
  input  axi_qos_t                    i_lt_axi_s_awqos,
  input  axi_region_t                 i_lt_axi_s_awregion,
  input  chip_axi_lt_awuser_t         i_lt_axi_s_awuser,
  input  logic                        i_lt_axi_s_awvalid,
  output logic                        o_lt_axi_s_awready,
  input  chip_axi_lt_data_t           i_lt_axi_s_wdata,
  input  chip_axi_lt_wstrb_t          i_lt_axi_s_wstrb,
  input  logic                        i_lt_axi_s_wlast,
  input  chip_axi_lt_wuser_t          i_lt_axi_s_wuser,
  input  logic                        i_lt_axi_s_wvalid,
  output logic                        o_lt_axi_s_wready,

  output logic                        o_lt_axi_s_bvalid,
  output soc_periph_targ_lt_axi_id_t  o_lt_axi_s_bid,
  output chip_axi_lt_buser_t          o_lt_axi_s_buser,
  output axi_resp_t                   o_lt_axi_s_bresp,
  input  logic                        i_lt_axi_s_bready,
  input  chip_axi_addr_t              i_lt_axi_s_araddr,
  input  soc_periph_targ_lt_axi_id_t  i_lt_axi_s_arid,
  input  axi_len_t                    i_lt_axi_s_arlen,
  input  axi_size_t                   i_lt_axi_s_arsize,
  input  axi_burst_t                  i_lt_axi_s_arburst,
  input  axi_cache_t                  i_lt_axi_s_arcache,
  input  axi_prot_t                   i_lt_axi_s_arprot,
  input  axi_qos_t                    i_lt_axi_s_arqos,
  input  axi_region_t                 i_lt_axi_s_arregion,
  input  chip_axi_lt_aruser_t         i_lt_axi_s_aruser,
  input  logic                        i_lt_axi_s_arlock,
  input  logic                        i_lt_axi_s_arvalid,
  output logic                        o_lt_axi_s_arready,
  output logic                        o_lt_axi_s_rvalid,
  output logic                        o_lt_axi_s_rlast,
  output soc_periph_targ_lt_axi_id_t  o_lt_axi_s_rid,
  output chip_axi_lt_data_t           o_lt_axi_s_rdata,
  output chip_axi_lt_ruser_t          o_lt_axi_s_ruser,
  output axi_resp_t                   o_lt_axi_s_rresp,
  input  logic                        i_lt_axi_s_rready,

  output  chip_axi_addr_t             o_lt_axi_m_awaddr,
  output  soc_periph_targ_lt_axi_id_t o_lt_axi_m_awid,
  output  axi_len_t                   o_lt_axi_m_awlen,
  output  axi_size_t                  o_lt_axi_m_awsize,
  output  axi_burst_t                 o_lt_axi_m_awburst,
  output  axi_cache_t                 o_lt_axi_m_awcache,
  output  axi_prot_t                  o_lt_axi_m_awprot,
  output  logic                       o_lt_axi_m_awlock,
  output  axi_qos_t                   o_lt_axi_m_awqos,
  output  axi_region_t                o_lt_axi_m_awregion,
  output  chip_axi_lt_awuser_t        o_lt_axi_m_awuser,
  output  logic                       o_lt_axi_m_awvalid,
  input   logic                       i_lt_axi_m_awready,
  output  chip_axi_lt_data_t          o_lt_axi_m_wdata,
  output  chip_axi_lt_wstrb_t         o_lt_axi_m_wstrb,
  output  logic                       o_lt_axi_m_wlast,
  output  chip_axi_lt_wuser_t         o_lt_axi_m_wuser,
  output  logic                       o_lt_axi_m_wvalid,
  input   logic                       i_lt_axi_m_wready,
  input   logic                       i_lt_axi_m_bvalid,
  input   soc_periph_targ_lt_axi_id_t i_lt_axi_m_bid,
  input   chip_axi_lt_buser_t         i_lt_axi_m_buser,
  input   axi_resp_t                  i_lt_axi_m_bresp,
  output  logic                       o_lt_axi_m_bready,
  output  chip_axi_addr_t             o_lt_axi_m_araddr,
  output  soc_periph_targ_lt_axi_id_t o_lt_axi_m_arid,
  output  axi_len_t                   o_lt_axi_m_arlen,
  output  axi_size_t                  o_lt_axi_m_arsize,
  output  axi_burst_t                 o_lt_axi_m_arburst,
  output  axi_cache_t                 o_lt_axi_m_arcache,
  output  axi_prot_t                  o_lt_axi_m_arprot,
  output  axi_qos_t                   o_lt_axi_m_arqos,
  output  axi_region_t                o_lt_axi_m_arregion,
  output  chip_axi_lt_aruser_t        o_lt_axi_m_aruser,
  output  logic                       o_lt_axi_m_arlock,
  output  logic                       o_lt_axi_m_arvalid,
  input  logic                        i_lt_axi_m_arready,
  input  logic                        i_lt_axi_m_rvalid,
  input  logic                        i_lt_axi_m_rlast,
  input  soc_periph_targ_lt_axi_id_t  i_lt_axi_m_rid,
  input  chip_axi_lt_data_t           i_lt_axi_m_rdata,
  input  chip_axi_lt_ruser_t          i_lt_axi_m_ruser,
  input  axi_resp_t                   i_lt_axi_m_rresp,
  output logic                        o_lt_axi_m_rready,

  input  logic                        i_uart_cst_n,
  input  logic                        i_uart_rx,
  output logic                        o_uart_rts_n,
  output logic                        o_uart_tx,
  output logic                        o_uart_int,

  input  logic [15:0]                 i_gpio,
  output logic [15:0]                 o_gpio_oe,
  output logic [15:0]                 o_gpio,
  output logic                        o_gpio_int,

  output logic                        o_i2c_0_clk_oe,
  output logic                        o_i2c_0_data_oe,
  input  logic                        i_i2c_0_clk,
  input  logic                        i_i2c_0_data,
  output logic                        o_i2c_0_int,

  output logic                        o_i2c_1_clk_oe,
  output logic                        o_i2c_1_data_oe,
  input  logic                        i_i2c_1_clk,
  input  logic                        i_i2c_1_data,
  output logic                        o_i2c_1_int,

  output logic                        o_spi_clk,
  output logic [3:0]                  o_spi_ss_n,
  output logic [3:0]                  o_spi_sd_oe_n,
  output logic [3:0]                  o_spi_sd,
  input  logic [3:0]                  i_spi_sd,
  output logic                        o_spi_int,

  output logic                        o_timer_int,

  output                              o_mem_ale_oepad,
  output                              o_mem_ale_iepad,
  output                              o_mem_ale_opad,
  input                               i_mem_cmd_ipad,
  output                              o_mem_cmd_oepad,
  output                              o_mem_cmd_iepad,
  output                              o_mem_cmd_opad,
  output                              o_mem_ctrl_0_oepad,
  output                              o_mem_ctrl_0_iepad,
  input                               i_mem_ctrl_0_ipad,
  output                              o_mem_ctrl_1_oepad,
  output                              o_mem_ctrl_1_iepad,
  output                              o_mem_ctrl_1_opad,
  output                              o_mem_rstbar_oepad,
  output                              o_mem_rstbar_iepad,
  output                              o_mem_rstbar_opad,
  input                               i_mem_lpbk_dqs_ipad,
  output                              o_mem_lpbk_dqs_oepad,
  output                              o_mem_lpbk_dqs_iepad,
  input                               i_mem_dqs_ipad,
  output                              o_mem_dqs_oepad,
  output                              o_mem_dqs_iepad,
  output                              o_mem_rebar_oepad,
  output                              o_mem_rebar_iepad,
  output                              o_mem_rebar_opad,
  input                               i_mem_rebar_ipad,
  input  [7:0]                        i_mem_data_ipad,
  output [7:0]                        o_mem_data_oepad,
  output [7:0]                        o_mem_data_iepad,
  output [7:0]                        o_mem_data_opad,
  output                              o_mem_webar_oepad,
  output                              o_mem_webar_iepad,
  output                              o_mem_webar_opad,
  output                              o_mem_wpbar_oepad,
  output                              o_mem_wpbar_iepad,
  input                               i_mem_wpbar_ipad,
  output logic                        o_emmc_int,

  // Observation bus
  output logic [15:0]                 o_obs,

  // SRAM configuration
  input  logic                        i_ret,
  input  logic                        i_pde,
  output logic                        o_prn

);

//==============================================================================
  // type declaration
  typedef logic  [7:0] tsel_data_t;
  typedef logic [31:0] phy_t;

  typedef struct packed {
    logic activity;
    logic gen_call;
    logic rd_req;
    logic rx_done;
    logic rx_full;
    logic rx_over;
    logic rx_under;
    logic scl_stuck_at_low;
    logic smbus_clk_mext;
    logic smbus_clk_sext;
    logic smbus_host_notify;
    logic smbus_quick_cmd_det;
    logic start_det;
    logic stop_det;
    logic tx_abrt;
    logic tx_empty;
    logic tx_over;
  } i2c_int_t;

  typedef struct packed {
    logic mst;
    logic rxf;
    logic rxo;
    logic rxu;
    logic txe;
    logic txo;
  } spi_int_t;

//==============================================================================
// signal dclaration
  logic        gpio_int;
  logic        uart_int;
  i2c_int_t    i2c_0_int;
  i2c_int_t    i2c_1_int;
  spi_int_t    spi_int;
  logic [1:0]  timer_int;
  logic        emmc_int;

  logic        gpio_int_q;
  logic        uart_int_q;
  logic        i2c_0_int_q;
  logic        i2c_1_int_q;
  logic        spi_int_q;
  logic        timer_int_q;
  logic        emmc_int_q;

  logic [1:0] spi_mode;
  logic [3:0] spi_sd_in;
  logic [3:0] spi_sd_oe_n;

  logic [9:0]       uart_rx_ram_in;
  logic [3:0]       uart_rx_ram_rd_addr;
  logic             uart_rx_ram_rd_ce_n;
  logic             uart_rx_ram_we_n;
  logic [3:0]       uart_rx_ram_wr_addr;
  logic [7:0]       uart_tx_ram_in;
  logic [3:0]       uart_tx_ram_rd_addr;
  logic             uart_tx_ram_rd_ce_n;
  logic             uart_tx_ram_we_n;
  logic [3:0]       uart_tx_ram_wr_addr;
  logic [11:0]      uart_rx_ram_out_wide;
  logic [7:0]       uart_tx_ram_out_wide;

  logic   [31:0]  apb_cfg_emmc_prdata;
  logic   [31:0]  apb_cfg_emmc_paddr;
  logic           apb_cfg_emmc_penable;
  logic           apb_cfg_emmc_psel;
  logic   [31:0]  apb_cfg_emmc_pwdata;
  logic           apb_cfg_emmc_pwrite;
  logic           apb_cfg_emmc_pslverr;
  logic           apb_cfg_emmc_pready;

  logic           tsel_dqs_0_opad      ;
  logic           tsel_dqs_1_opad      ;
  logic           tsel_dqs_2_opad      ;
  logic           tsel_dqs_3_opad      ;
  tsel_data_t     tsel_data_0_opad     ;
  tsel_data_t     tsel_data_1_opad     ;
  tsel_data_t     tsel_data_2_opad     ;
  tsel_data_t     tsel_data_3_opad     ;
  logic           v18                  ;
  phy_t           phy_gpio_reg_ctrl_0  ;
  phy_t           phy_gpio_reg_status_0;
  phy_t           phy_gpio_reg_ctrl_1  ;
  phy_t           phy_gpio_reg_status_1;

  always_ff @ (posedge i_periph_clk or negedge i_periph_rst_n)
  if (!i_periph_rst_n) begin
    gpio_int_q  <= 1'b0;
    uart_int_q  <= 1'b0;
    i2c_0_int_q <= 1'b0;
    i2c_1_int_q <= 1'b0;
    spi_int_q   <= 1'b0;
    timer_int_q <= 1'b0;
    emmc_int_q  <= 1'b0;
  end
  else begin
    gpio_int_q  <= gpio_int;
    uart_int_q  <= uart_int;
    i2c_0_int_q <= |i2c_0_int;
    i2c_1_int_q <= |i2c_1_int;
    spi_int_q   <= |spi_int;
    timer_int_q <= |timer_int;
    emmc_int_q  <= emmc_int;
  end

  always_comb o_gpio_int  = gpio_int_q;
  always_comb o_uart_int  = uart_int_q;
  always_comb o_i2c_0_int = i2c_0_int_q;
  always_comb o_i2c_1_int = i2c_1_int_q;
  always_comb o_spi_int   = spi_int_q;
  always_comb o_timer_int = timer_int_q;
  always_comb o_emmc_int  = emmc_int_q;

  always_comb begin
    if (spi_mode == 2'b00) begin
      spi_sd_in[0] = i_spi_sd[1];
      spi_sd_in[3:1] = 3'b000;
      o_spi_sd_oe_n = 4'b0010;
    end
    else begin
      spi_sd_in = i_spi_sd;
      o_spi_sd_oe_n = spi_sd_oe_n;
    end
  end

  soc_periph_dw_peripherals u_peripherals (
   // Ports for Interface PCLK
   .PCLK_pclk                                       (i_periph_clk),
   // Ports for Interface PRESETn
   .PRESETn_presetn                                 (i_periph_rst_n),
   // Ports for Interface SIO
   .SIO_cts_n                                       (i_uart_cst_n),
   .SIO_sin                                         (i_uart_rx),
   .SIO_rts_n                                       (o_uart_rts_n),
   .SIO_sout                                        (o_uart_tx),
   // Ports for Interface apb_cfg_emmc
   .apb_cfg_emmc_prdata,
   .apb_cfg_emmc_paddr,
   .apb_cfg_emmc_penable,
   .apb_cfg_emmc_psel,
   .apb_cfg_emmc_pwdata,
   .apb_cfg_emmc_pwrite,
   .apb_cfg_emmc_pslverr,
   .apb_cfg_emmc_pready,
   // Ports for Interface apb_gpio_api
   .apb_gpio_api_gpio_ext_porta                     (i_gpio),
   .apb_gpio_api_gpio_porta_ddr                     (o_gpio_oe),
   .apb_gpio_api_gpio_porta_dr                      (o_gpio),
   // Ports for Interface slave0_soc_periph_dw_axi_ACLK
   .slave0_soc_periph_dw_axi_ACLK_aclk              (i_periph_clk),
   // Ports for Interface slave0_soc_periph_dw_axi_ARESETn
   .slave0_soc_periph_dw_axi_ARESETn_aresetn        (i_periph_rst_n),
   // Ports for Interface slave0_soc_periph_dw_axi_AXI_Slave
   .lt_axi_s_araddr       (i_lt_axi_s_araddr[31:0]),
   .lt_axi_s_arburst      (i_lt_axi_s_arburst),
   .lt_axi_s_arcache      (i_lt_axi_s_arcache),
   .lt_axi_s_arid         (i_lt_axi_s_arid),
   .lt_axi_s_arlen        (i_lt_axi_s_arlen),
   .lt_axi_s_arlock       (i_lt_axi_s_arlock),
   .lt_axi_s_arprot       (i_lt_axi_s_arprot),
   .lt_axi_s_arsize       (i_lt_axi_s_arsize),
   .lt_axi_s_arvalid      (i_lt_axi_s_arvalid),
   .lt_axi_s_awaddr       (i_lt_axi_s_awaddr[31:0]),
   .lt_axi_s_awburst      (i_lt_axi_s_awburst),
   .lt_axi_s_awcache      (i_lt_axi_s_awcache),
   .lt_axi_s_awid         (i_lt_axi_s_awid),
   .lt_axi_s_awlen        (i_lt_axi_s_awlen),
   .lt_axi_s_awlock       (i_lt_axi_s_awlock),
   .lt_axi_s_awprot       (i_lt_axi_s_awprot),
   .lt_axi_s_awsize       (i_lt_axi_s_awsize),
   .lt_axi_s_awvalid      (i_lt_axi_s_awvalid),
   .lt_axi_s_bready       (i_lt_axi_s_bready),
   .lt_axi_s_rready       (i_lt_axi_s_rready),
   .lt_axi_s_wdata        (i_lt_axi_s_wdata),
   .lt_axi_s_wlast        (i_lt_axi_s_wlast),
   .lt_axi_s_wstrb        (i_lt_axi_s_wstrb),
   .lt_axi_s_wvalid       (i_lt_axi_s_wvalid),
   .lt_axi_s_arready      (o_lt_axi_s_arready),
   .lt_axi_s_awready      (o_lt_axi_s_awready),
   .lt_axi_s_bid          (o_lt_axi_s_bid),
   .lt_axi_s_bresp        (o_lt_axi_s_bresp),
   .lt_axi_s_bvalid       (o_lt_axi_s_bvalid),
   .lt_axi_s_rdata        (o_lt_axi_s_rdata),
   .lt_axi_s_rid          (o_lt_axi_s_rid),
   .lt_axi_s_rlast        (o_lt_axi_s_rlast),
   .lt_axi_s_rresp        (o_lt_axi_s_rresp),
   .lt_axi_s_rvalid       (o_lt_axi_s_rvalid),
   .lt_axi_s_wready       (o_lt_axi_s_wready),
   // Ports for Manually exported pin s
   .soc_periph_dw_gpio_pclk_intr                    (i_periph_clk),
   .soc_periph_dw_i2c_0_ic_clk                      (i_periph_clk),
   .soc_periph_dw_i2c_0_ic_clk_in_a                 (i_i2c_0_clk),
   .soc_periph_dw_i2c_0_ic_data_in_a                (i_i2c_0_data),
   .soc_periph_dw_i2c_0_ic_rst_n                    (i_periph_rst_n),
   .soc_periph_dw_i2c_1_ic_clk                      (i_periph_clk),
   .soc_periph_dw_i2c_1_ic_clk_in_a                 (i_i2c_1_clk),
   .soc_periph_dw_i2c_1_ic_data_in_a                (i_i2c_1_data),
   .soc_periph_dw_i2c_1_ic_rst_n                    (i_periph_rst_n),
   .soc_periph_dw_ssi_rxd                           (spi_sd_in),
   .soc_periph_dw_ssi_ss_in_n                       (1'b1),
   .soc_periph_dw_ssi_ssi_clk                       (i_periph_clk),
   .soc_periph_dw_ssi_ssi_rst_n                     (i_periph_rst_n),
   .soc_periph_dw_timers_scan_mode                  (test_mode),
   .soc_periph_dw_timers_timer_1_clk                (i_periph_clk),
   .soc_periph_dw_timers_timer_1_resetn             (i_periph_rst_n),
   .soc_periph_dw_timers_timer_2_clk                (i_periph_clk),
   .soc_periph_dw_timers_timer_2_resetn             (i_periph_rst_n),
   .soc_periph_dw_uart_dcd_n                        (1'h1),
   .soc_periph_dw_uart_dsr_n                        (1'h1),
   .soc_periph_dw_uart_ri_n                         (1'h1),
   .soc_periph_dw_uart_rx_ram_out                   (uart_rx_ram_out_wide[9:0]),
   .soc_periph_dw_uart_scan_mode                    (test_mode),
   .soc_periph_dw_uart_tx_ram_out                   (uart_tx_ram_out_wide),
   .soc_periph_dw_gpio_gpio_intr_flag               (gpio_int),
   .soc_periph_dw_gpio_gpio_intrclk_en              (),
   .soc_periph_dw_i2c_0_ic_activity_intr            (i2c_0_int.activity),
   .soc_periph_dw_i2c_0_ic_clk_oe                   (o_i2c_0_clk_oe),
   .soc_periph_dw_i2c_0_ic_data_oe                  (o_i2c_0_data_oe),
   .soc_periph_dw_i2c_0_ic_gen_call_intr            (i2c_0_int.gen_call),
   .soc_periph_dw_i2c_0_ic_rd_req_intr              (i2c_0_int.rd_req),
   .soc_periph_dw_i2c_0_ic_rx_done_intr             (i2c_0_int.rx_done),
   .soc_periph_dw_i2c_0_ic_rx_full_intr             (i2c_0_int.rx_full),
   .soc_periph_dw_i2c_0_ic_rx_over_intr             (i2c_0_int.rx_over),
   .soc_periph_dw_i2c_0_ic_rx_under_intr            (i2c_0_int.rx_under),
   .soc_periph_dw_i2c_0_ic_scl_stuck_at_low_intr    (i2c_0_int.scl_stuck_at_low),
   .soc_periph_dw_i2c_0_ic_smbus_clk_mext_intr      (i2c_0_int.smbus_clk_mext),
   .soc_periph_dw_i2c_0_ic_smbus_clk_sext_intr      (i2c_0_int.smbus_clk_sext),
   .soc_periph_dw_i2c_0_ic_smbus_host_notify_intr   (i2c_0_int.smbus_host_notify),
   .soc_periph_dw_i2c_0_ic_smbus_quick_cmd_det_intr (i2c_0_int.smbus_quick_cmd_det),
   .soc_periph_dw_i2c_0_ic_start_det_intr           (i2c_0_int.start_det),
   .soc_periph_dw_i2c_0_ic_stop_det_intr            (i2c_0_int.stop_det),
   .soc_periph_dw_i2c_0_ic_tx_abrt_intr             (i2c_0_int.tx_abrt),
   .soc_periph_dw_i2c_0_ic_tx_empty_intr            (i2c_0_int.tx_empty),
   .soc_periph_dw_i2c_0_ic_tx_over_intr             (i2c_0_int.tx_over),
   .soc_periph_dw_i2c_1_ic_activity_intr            (i2c_1_int.activity),
   .soc_periph_dw_i2c_1_ic_clk_oe                   (o_i2c_1_clk_oe),
   .soc_periph_dw_i2c_1_ic_data_oe                  (o_i2c_1_data_oe),
   .soc_periph_dw_i2c_1_ic_gen_call_intr            (i2c_1_int.gen_call),
   .soc_periph_dw_i2c_1_ic_rd_req_intr              (i2c_1_int.rd_req),
   .soc_periph_dw_i2c_1_ic_rx_done_intr             (i2c_1_int.rx_done),
   .soc_periph_dw_i2c_1_ic_rx_full_intr             (i2c_1_int.rx_full),
   .soc_periph_dw_i2c_1_ic_rx_over_intr             (i2c_1_int.rx_over),
   .soc_periph_dw_i2c_1_ic_rx_under_intr            (i2c_1_int.rx_under),
   .soc_periph_dw_i2c_1_ic_scl_stuck_at_low_intr    (i2c_1_int.scl_stuck_at_low),
   .soc_periph_dw_i2c_1_ic_smbus_clk_mext_intr      (i2c_1_int.smbus_clk_mext),
   .soc_periph_dw_i2c_1_ic_smbus_clk_sext_intr      (i2c_1_int.smbus_clk_sext),
   .soc_periph_dw_i2c_1_ic_smbus_host_notify_intr   (i2c_1_int.smbus_host_notify),
   .soc_periph_dw_i2c_1_ic_smbus_quick_cmd_det_intr (i2c_1_int.smbus_quick_cmd_det),
   .soc_periph_dw_i2c_1_ic_start_det_intr           (i2c_1_int.start_det),
   .soc_periph_dw_i2c_1_ic_stop_det_intr            (i2c_1_int.stop_det),
   .soc_periph_dw_i2c_1_ic_tx_abrt_intr             (i2c_1_int.tx_abrt),
   .soc_periph_dw_i2c_1_ic_tx_empty_intr            (i2c_1_int.tx_empty),
   .soc_periph_dw_i2c_1_ic_tx_over_intr             (i2c_1_int.tx_over),
   .soc_periph_dw_ssi_sclk_out                      (o_spi_clk),
   .soc_periph_dw_ssi_spi_mode                      (spi_mode),
   .soc_periph_dw_ssi_ss_0_n                        (o_spi_ss_n[0]),
   .soc_periph_dw_ssi_ss_1_n                        (o_spi_ss_n[1]),
   .soc_periph_dw_ssi_ss_2_n                        (o_spi_ss_n[2]),
   .soc_periph_dw_ssi_ss_3_n                        (o_spi_ss_n[3]),
   .soc_periph_dw_ssi_ssi_mst_intr                  (spi_int.mst),
   .soc_periph_dw_ssi_ssi_oe_n                      (spi_sd_oe_n),
   .soc_periph_dw_ssi_ssi_rxf_intr                  (spi_int.rxf),
   .soc_periph_dw_ssi_ssi_rxo_intr                  (spi_int.rxo),
   .soc_periph_dw_ssi_ssi_rxu_intr                  (spi_int.rxu),
   .soc_periph_dw_ssi_ssi_txe_intr                  (spi_int.txe),
   .soc_periph_dw_ssi_ssi_txo_intr                  (spi_int.txo),
   .soc_periph_dw_ssi_txd                           (o_spi_sd),
   .soc_periph_dw_timers_timer_en                   (),
   .soc_periph_dw_timers_timer_intr                 (timer_int),
   .soc_periph_dw_uart_intr                         (uart_int),
   .soc_periph_dw_uart_rx_ram_in                    (uart_rx_ram_in),
   .soc_periph_dw_uart_rx_ram_rd_addr               (uart_rx_ram_rd_addr),
   .soc_periph_dw_uart_rx_ram_rd_ce_n               (uart_rx_ram_rd_ce_n),
   .soc_periph_dw_uart_rx_ram_re_n                  (),
   .soc_periph_dw_uart_rx_ram_we_n                  (uart_rx_ram_we_n),
   .soc_periph_dw_uart_rx_ram_wr_addr               (uart_rx_ram_wr_addr),
   .soc_periph_dw_uart_tx_ram_in                    (uart_tx_ram_in),
   .soc_periph_dw_uart_tx_ram_rd_addr               (uart_tx_ram_rd_addr),
   .soc_periph_dw_uart_tx_ram_rd_ce_n               (uart_tx_ram_rd_ce_n),
   .soc_periph_dw_uart_tx_ram_re_n                  (),
   .soc_periph_dw_uart_tx_ram_we_n                  (uart_tx_ram_we_n),
   .soc_periph_dw_uart_tx_ram_wr_addr               (uart_tx_ram_wr_addr)
  );

  axe_tcl_sram_pkg::impl_inp_t i_sram_cfg;
  axe_tcl_sram_pkg::impl_oup_t o_sram_cfg;
  always_comb begin
    // Inputs
    i_sram_cfg = '{default: '0};
    i_sram_cfg.ret = i_ret;
    i_sram_cfg.pde = i_pde;
    i_sram_cfg.se  = scan_en;

    // Outputs
    o_prn = o_sram_cfg.prn;
  end

  axe_tcl_sram_pkg::impl_inp_t    [5:0] cfg_sram_inp;
  axe_tcl_sram_pkg::impl_oup_t    [5:0] cfg_sram_oup;
  axe_tcl_sram_cfg #(
    .NUM_SRAMS(6)
  ) u_sram_cfg (
    .i_s(i_sram_cfg),
    .o_s(o_sram_cfg),
    .o_m(cfg_sram_inp),
    .i_m(cfg_sram_oup)
  );

  axe_tcl_ram_1rp_1wp #(
    .NumWords (16),
    .DataWidth(12),
    .ByteWidth(12),
    .ReadLatency(1),
    .ImplKey  ("HS_RVT"),
    .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
  ) u_uart_rx_ram (
    .i_wr_clk  (i_periph_clk),
    .i_wr_rst_n(i_periph_rst_n),
    .i_wr_req  (~uart_rx_ram_we_n),
    .i_wr_addr (uart_rx_ram_wr_addr),
    .i_wr_data ({2'b00, uart_rx_ram_in}),
    .i_wr_mask (~uart_rx_ram_we_n),
    .i_rd_clk  (i_periph_clk),
    .i_rd_rst_n(i_periph_rst_n),
    .i_rd_req  (uart_rx_ram_rd_ce_n),
    .i_rd_addr (uart_rx_ram_rd_addr),
    .o_rd_data (uart_rx_ram_out_wide),
    .i_impl    (cfg_sram_inp[0]),
    .o_impl    (cfg_sram_oup[0])
  );

  axe_tcl_ram_1rp_1wp #(
    .NumWords (16),
    .DataWidth(8),
    .ByteWidth(8),
    .ReadLatency(1),
    .ImplKey  ("HS_RVT"),
    .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
  ) u_uart_tx_ram (
    .i_wr_clk  (i_periph_clk),
    .i_wr_rst_n(i_periph_rst_n),
    .i_wr_req  (~uart_tx_ram_we_n),
    .i_wr_addr (uart_tx_ram_wr_addr),
    .i_wr_data (uart_tx_ram_in),
    .i_wr_mask (~uart_tx_ram_we_n),
    .i_rd_clk  (i_periph_clk),
    .i_rd_rst_n(i_periph_rst_n),
    .i_rd_req  (~uart_tx_ram_rd_ce_n),
    .i_rd_addr (uart_tx_ram_rd_addr),
    .o_rd_data (uart_tx_ram_out_wide),
    .i_impl    (cfg_sram_inp[1]),
    .o_impl    (cfg_sram_oup[1])
  );

  emmc #(
    .emmc_axi_addr_t    (chip_axi_addr_t),
    .emmc_axi_data_t    (chip_axi_lt_data_t),
    .emmc_axi_wstrb_t   (chip_axi_lt_wstrb_t),
    .emmc_axi_id_t      (soc_periph_targ_lt_axi_id_t),
    .emmc_axi_user_t    (chip_axi_lt_aruser_t)
  ) u_emmc(
    // Clocks and resets
    .i_pclk      (i_periph_clk),
    .i_preset_n  (i_periph_rst_n),
    .i_emmc_clk  (i_emmc_clk),
    .i_emmc_rst_n(i_emmc_rst_n),

    .o_interrupt(emmc_int),

    // INPUT REGISTERS Driving into EMMC IP: Clock stable enable register, Capability Registers, and Clock Multiplier Configuration registers
    .emmc_outreg_cfg(emmc_outreg_cfg),
    // OUTPUT REgisters Driving out of the EMMC IP: Clock Enable Register
    .emmc_inreg_cfg(emmc_inreg_cfg),

    // APB subordinate interface
    .i_s_paddr(apb_cfg_emmc_paddr),
    .i_s_psel(apb_cfg_emmc_psel),
    .i_s_penable(apb_cfg_emmc_penable),
    .i_s_pwrite(apb_cfg_emmc_pwrite),
    .i_s_pwdata(apb_cfg_emmc_pwdata),
    .o_s_pready(apb_cfg_emmc_pready),
    .o_s_prdata(apb_cfg_emmc_prdata),
    .o_s_pslverr(apb_cfg_emmc_pslverr),

    // AXI manager interface
    .i_m_awready(i_lt_axi_m_awready),
    .o_m_awaddr(o_lt_axi_m_awaddr),
    .o_m_awid(o_lt_axi_m_awid),
    .o_m_awlen(o_lt_axi_m_awlen),
    .o_m_awsize(o_lt_axi_m_awsize),
    .o_m_awburst(o_lt_axi_m_awburst),
    .o_m_awlock(o_lt_axi_m_awlock),
    .o_m_awcache(o_lt_axi_m_awcache),
    .o_m_awprot(o_lt_axi_m_awprot),
    .o_m_awqos(o_lt_axi_m_awqos),
    .o_m_awregion(o_lt_axi_m_awregion),
    .o_m_awuser(o_lt_axi_m_awuser),
    .o_m_awvalid(o_lt_axi_m_awvalid),

    .i_m_wready(i_lt_axi_m_wready),
    .o_m_wdata(o_lt_axi_m_wdata),
    .o_m_wstrb(o_lt_axi_m_wstrb),
    .o_m_wlast(o_lt_axi_m_wlast),
    .o_m_wuser(o_lt_axi_m_wuser),
    .o_m_wvalid(o_lt_axi_m_wvalid),
    .i_m_bresp(i_lt_axi_m_bresp),
    .i_m_bvalid(i_lt_axi_m_bvalid),
    .i_m_bid('0),
    .i_m_buser('0),
    .o_m_bready(o_lt_axi_m_bready),

    .i_m_arready(i_lt_axi_m_arready),
    .o_m_araddr(o_lt_axi_m_araddr),
    .o_m_arid(o_lt_axi_m_arid),
    .o_m_arlen(o_lt_axi_m_arlen),
    .o_m_arsize(o_lt_axi_m_arsize),
    .o_m_arburst(o_lt_axi_m_arburst),
    .o_m_arlock(o_lt_axi_m_arlock),
    .o_m_arcache(o_lt_axi_m_arcache),
    .o_m_arprot(o_lt_axi_m_arprot),
    .o_m_arqos(o_lt_axi_m_arqos),
    .o_m_arregion(o_lt_axi_m_arregion),
    .o_m_aruser(o_lt_axi_m_aruser),
    .o_m_arvalid(o_lt_axi_m_arvalid),
    .i_m_rdata(i_lt_axi_m_rdata),
    .i_m_rresp(i_lt_axi_m_rresp),
    .i_m_rlast(i_lt_axi_m_rlast),
    .i_m_rvalid(i_lt_axi_m_rvalid),
    .o_m_rready(o_lt_axi_m_rready),

    // Config registers - TODO needs external register
    .i_impl_inp(cfg_sram_inp[5:2]),
    .o_impl_oup(cfg_sram_oup[5:2]),

    // Pads
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
    .o_tsel_dqs_0_opad       ( tsel_dqs_0_opad       ), // NOT USED
    .o_tsel_dqs_1_opad       ( tsel_dqs_1_opad       ), // NOT USED
    .o_tsel_dqs_2_opad       ( tsel_dqs_2_opad       ), // NOT USED
    .o_tsel_dqs_3_opad       ( tsel_dqs_3_opad       ), // NOT USED
    .o_tsel_data_0_opad      ( tsel_data_0_opad      ), // NOT USED
    .o_tsel_data_1_opad      ( tsel_data_1_opad      ), // NOT USED
    .o_tsel_data_2_opad      ( tsel_data_2_opad      ), // NOT USED
    .o_tsel_data_3_opad      ( tsel_data_3_opad      ), // NOT USED
    .o_v18                   ( v18                   ), // NOT USED
    .o_phy_gpio_reg_ctrl_0   ( phy_gpio_reg_ctrl_0   ), // NOT USED
    .i_phy_gpio_reg_status_0 ( phy_gpio_reg_status_0 ), // NOT USED
    .o_phy_gpio_reg_ctrl_1   ( phy_gpio_reg_ctrl_1   ), // NOT USED
    .i_phy_gpio_reg_status_1 ( phy_gpio_reg_status_1 ), // NOT USED
    .test_mode               ( test_mode             ),
    .scan_en                 ( scan_en               )
  );

  // tie inputs
  always_comb begin
    phy_gpio_reg_status_0 = '0;
    phy_gpio_reg_status_1 = '0;
  end


// TODO: matt.morris : Place holder - what can we use here???
always_comb o_obs = '0;

endmodule
