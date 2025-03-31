// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>

//
module soc_periph_p
  import chip_pkg::*;
  import axi_pkg::*;
  import soc_periph_pkg::*;
  import emmc_pkg::*;
(
  // - Clocks and Resets
  // APB Clock, positive edge triggered
  input  wire   i_ref_clk,
  input  wire   i_emmc_clk,
  input  wire   i_periph_clk,
  input  wire   i_global_rst_n,
  input  wire   i_ao_rst_n,

  // AXI-S LT
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

  // AXI-M LT
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

  // SysCfg APB
  input  chip_syscfg_addr_t           i_cfg_apb4_s_paddr,
  input  chip_apb_syscfg_data_t       i_cfg_apb4_s_pwdata,
  input  logic                        i_cfg_apb4_s_pwrite,
  input  logic                        i_cfg_apb4_s_psel,
  input  logic                        i_cfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t       i_cfg_apb4_s_pstrb,
  input  logic [3-1:0]                i_cfg_apb4_s_pprot,
  output logic                        o_cfg_apb4_s_pready,
  output chip_apb_syscfg_data_t       o_cfg_apb4_s_prdata,
  output logic                        o_cfg_apb4_s_pslverr,

  // NoC Fence / Clken
  output logic                        o_noc_async_idle_req,
  input  logic                        i_noc_async_idle_ack,
  input  logic                        i_noc_async_idle_val,
  output logic                        o_noc_clken,
  output logic                        o_noc_rst_n,

  // Observation
  output logic [15:0]                 o_obs,

  // UART
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

  output logic                        o_timer_int,

  output wire                         o_spi_clk,
  output logic [3:0]                  o_spi_ss_n,
  output logic [3:0]                  o_spi_sd_oe_n,
  output logic [3:0]                  o_spi_sd,
  input  logic [3:0]                  i_spi_sd,
  output logic                        o_spi_int,

  /// DFT signals
  input  wire  tck,
  input  wire  trst,
  input  logic tms,
  input  logic tdi,
  output logic tdo_en,
  output logic tdo,

  input  wire                         test_clk,
  input  logic                        test_mode,
  input  logic                        edt_update,
  input  logic                        scan_en,
  input  logic [                 7:0] scan_in,
  output logic [                 7:0] scan_out,

  input  wire                         bisr_clk,
  input  wire                         bisr_reset,
  input  logic                        bisr_shift_en,
  input  logic                        bisr_si,
  output logic                        bisr_so,

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
  output                              o_emmc_int,

  // PADCTRL: Ref Clk Sel Freq
  output logic [1:0]                  o_ref_clk_sel_freq,

  // PADCTRL: Drive Strengths
  output logic [1:0]                  o_jtag_drive,
  output logic [1:0]                  o_uart_drive,
  output logic [1:0]                  o_spi_drive,
  output logic [1:0]                  o_i2c_drive,
  output logic [1:0]                  o_gpio_drive,
  output logic [1:0]                  o_obs_drive,
  output logic [1:0]                  o_dft_drive,
  output logic [2:0]                  o_emmc_drive,

  // PADCTRL: Schmitt Triggers
  output logic                        o_clk_schmitt,
  output logic                        o_rst_schmitt,
  output logic                        o_spi_schmitt,
  output logic                        o_uart_schmitt,
  output logic                        o_i2c_schmitt,
  output logic                        o_gpio_schmitt,
  output logic                        o_emmc_schmitt,
  output logic                        o_dft_schmitt,

  output logic [2:0]                  o_bootmode_pull_en,
  output logic [3:0]                  o_spi_sd_pd_en,
  output logic                        o_uart_cts_n_pd_en,
  output logic                        o_uart_rx_pd_en,
  output logic [15:0]                 o_gpio_pd_en
);

  // --------------------------------------------------------------
  // Signals
  // --------------------------------------------------------------
  wire emmc_clk   , periph_clk;
  wire emmc_rst_n , periph_rst_n;
  wire ao_rst_sync_n;

  soc_periph_ao_csr_reg_pkg::apb_h2d_t ao_padctrl_csr_apb_h2d;
  soc_periph_ao_csr_reg_pkg::apb_d2h_t ao_padctrl_csr_apb_d2h;
  soc_periph_ao_csr_reg_pkg::soc_periph_ao_csr_reg2hw_t padctrl_reg2hw;
  soc_periph_ao_csr_reg_pkg::soc_periph_ao_csr_hw2reg_t padctrl_hw2reg;
  emmc_outreg_cfg_t emmc_outreg_cfg;
  emmc_inreg_cfg_t  emmc_inreg_cfg;

  // --------------------------------------------------------------
  // RTL
  // --------------------------------------------------------------

  typedef struct packed {
    logic periph_clken;
    logic emmc_clken;
  } soc_periph_clken_t;

  soc_periph_clken_t noc_clken;
  always_comb o_noc_clken = noc_clken.periph_clken;

  pctl #(
      .N_FAST_CLKS(2),
      .N_RESETS   (2),
      .N_MEM_PG          ( 1 ),
      .N_FENCES          ( 1 ),
      .N_THROTTLE_PINS   ( N_THROTTLE_PINS ),
      .CLKRST_MATRIX     ( {2'b10 ,
                            2'b01} ),
      .PLL_CLK_IS_I_CLK  ( 1'b0 ),
      .AUTO_RESET_REMOVE ( 1'b1 ),
      .AUTO_FENCE_REMOVE ( 1'b1 ),
      .paddr_t(chip_syscfg_addr_t),
      .pdata_t(chip_apb_syscfg_data_t),
      .pstrb_t(chip_apb_syscfg_strb_t)
  ) u_pctl (
    .i_clk         (i_ref_clk),
    .i_ao_rst_n    (i_ao_rst_n),
    .i_global_rst_n(i_global_rst_n),
    .i_test_mode   (test_mode),

    .i_pll_clk      ({i_periph_clk , i_emmc_clk}),
    .o_partition_clk({  periph_clk ,   emmc_clk}),

    .o_partition_rst_n({periph_rst_n, emmc_rst_n}),
    .o_ao_rst_sync_n  (ao_rst_sync_n),

    .o_noc_async_idle_req,
    .i_noc_async_idle_ack,
    .i_noc_async_idle_val,
    .o_noc_clken (noc_clken),
    .o_noc_rst_n,

    .o_int_shutdown_req (),
    .i_int_shutdown_ack (1'b0),

    .i_global_sync_async(1'b0),
    .o_global_sync      (),

    // SRAM configuration
    .o_ret(ret),
    .o_pde(pde),
    .i_prn(prn),

    .i_throttle(1'h0),

    //////////////////////////////////////////////
    /// SYS_CFG Bus
    //////////////////////////////////////////////
    .i_cfg_apb4_s_paddr,
    .i_cfg_apb4_s_pwdata,
    .i_cfg_apb4_s_pwrite,
    .i_cfg_apb4_s_psel,
    .i_cfg_apb4_s_penable,
    .i_cfg_apb4_s_pstrb,
    .i_cfg_apb4_s_pprot,
    .o_cfg_apb4_s_pready,
    .o_cfg_apb4_s_prdata,
    .o_cfg_apb4_s_pslverr,

    .o_ao_csr_apb_req(ao_padctrl_csr_apb_h2d),
    .i_ao_csr_apb_rsp(ao_padctrl_csr_apb_d2h)
  );

  // PadCtrl
  soc_periph_ao_csr_reg_top u_ao_csr_padctrl
  (
    .clk_i  (i_ref_clk),
    .rst_ni (ao_rst_sync_n),
    .apb_i  (ao_padctrl_csr_apb_h2d),
    .apb_o  (ao_padctrl_csr_apb_d2h),
    // To HW
    .reg2hw (padctrl_reg2hw), // Write
    .hw2reg (padctrl_hw2reg),
    // Config
    .devmode_i (1'b1)
  );

  always_comb o_ref_clk_sel_freq = padctrl_reg2hw.padctrl_ref_clk;
  always_comb o_jtag_drive       = padctrl_reg2hw.io_ds_jtag;
  always_comb o_uart_drive       = padctrl_reg2hw.io_ds_uart;
  always_comb o_spi_drive        = padctrl_reg2hw.io_ds_spi;
  always_comb o_i2c_drive        = padctrl_reg2hw.io_ds_i2c;
  always_comb o_gpio_drive       = padctrl_reg2hw.io_ds_gpio;
  always_comb o_obs_drive        = padctrl_reg2hw.io_ds_obs;
  always_comb o_dft_drive        = padctrl_reg2hw.io_ds_dft;
  always_comb o_emmc_drive       = padctrl_reg2hw.io_ds_emmc;
  always_comb o_clk_schmitt      = padctrl_reg2hw.io_st_clk;
  always_comb o_rst_schmitt      = padctrl_reg2hw.io_st_rst;
  always_comb o_spi_schmitt      = padctrl_reg2hw.io_st_spi;
  always_comb o_uart_schmitt     = padctrl_reg2hw.io_st_uart;
  always_comb o_i2c_schmitt      = padctrl_reg2hw.io_st_i2c;
  always_comb o_gpio_schmitt     = padctrl_reg2hw.io_st_gpio;
  always_comb o_emmc_schmitt     = padctrl_reg2hw.io_st_emmc;
  always_comb o_dft_schmitt      = padctrl_reg2hw.io_st_dft;

  // - EMMC Signals
  // demux emmc SRS registers and IFMUL registers
  always_comb emmc_outreg_cfg.s0_hwinit_srs16 = padctrl_reg2hw.s0_hwinit_srs16;
  always_comb emmc_outreg_cfg.s0_hwinit_srs17 = padctrl_reg2hw.s0_hwinit_srs17;
  always_comb emmc_outreg_cfg.s0_hwinit_srs18 = padctrl_reg2hw.s0_hwinit_srs18;
  always_comb emmc_outreg_cfg.s0_hwinit_srs19 = padctrl_reg2hw.s0_hwinit_srs19;
  always_comb emmc_outreg_cfg.s0_hwinit_srs24 = padctrl_reg2hw.s0_hwinit_srs24;
  always_comb emmc_outreg_cfg.s0_hwinit_srs25 = padctrl_reg2hw.s0_hwinit_srs25;
  always_comb emmc_outreg_cfg.s0_hwinit_srs26 = padctrl_reg2hw.s0_hwinit_srs26;
  always_comb emmc_outreg_cfg.s0_hwinit_srs27 = padctrl_reg2hw.s0_hwinit_srs27;
  always_comb emmc_outreg_cfg.ics             = padctrl_reg2hw.ics;

  // demux emmx output registers
  always_comb padctrl_hw2reg.ice.d = emmc_inreg_cfg.ice;

  // Pull Down Controls
  always_comb o_spi_sd_pd_en      = { padctrl_reg2hw.io_spi_data_pd_en.spi_sd3_pd_en,
                                      padctrl_reg2hw.io_spi_data_pd_en.spi_sd2_pd_en,
                                      padctrl_reg2hw.io_spi_data_pd_en.spi_sd1_pd_en,
                                      padctrl_reg2hw.io_spi_data_pd_en.spi_sd0_pd_en };
  always_comb o_uart_cts_n_pd_en  =   padctrl_reg2hw.io_uart_pd_en.uart_cts_n_pd_en;
  always_comb o_uart_rx_pd_en     =   padctrl_reg2hw.io_uart_pd_en.uart_rx_pd_en;
  always_comb o_bootmode_pull_en  = { padctrl_reg2hw.io_bootmode_pull_en.bootmode_2_pd_en,
                                      padctrl_reg2hw.io_bootmode_pull_en.bootmode_1_pd_en,
                                      padctrl_reg2hw.io_bootmode_pull_en.bootmode_0_pu_en };
  always_comb o_gpio_pd_en        = { padctrl_reg2hw.io_gpio_pd_en.gpio_15_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_14_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_13_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_12_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_11_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_10_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_9_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_8_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_7_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_6_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_5_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_4_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_3_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_2_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_1_pd_en,
                                      padctrl_reg2hw.io_gpio_pd_en.gpio_0_pd_en };

// - SocPeriph instance
soc_periph u_soc_periph (
  .i_emmc_clk         (emmc_clk),
  .i_emmc_rst_n       (emmc_rst_n),
  .i_periph_clk       (periph_clk),
  .i_periph_rst_n     (periph_rst_n),

  .test_mode,
  .scan_en,

  .o_obs,

  .i_ret              (ret),
  .i_pde              (pde),
  .o_prn              (prn),

  .emmc_outreg_cfg    (emmc_outreg_cfg),
  .emmc_inreg_cfg     (emmc_inreg_cfg),

  .i_lt_axi_s_awaddr,
  .i_lt_axi_s_awid,
  .i_lt_axi_s_awlen,
  .i_lt_axi_s_awsize,
  .i_lt_axi_s_awburst,
  .i_lt_axi_s_awcache,
  .i_lt_axi_s_awprot,
  .i_lt_axi_s_awlock,
  .i_lt_axi_s_awqos,
  .i_lt_axi_s_awregion,
  .i_lt_axi_s_awuser,
  .i_lt_axi_s_awvalid,
  .o_lt_axi_s_awready,
  .i_lt_axi_s_wdata,
  .i_lt_axi_s_wstrb,
  .i_lt_axi_s_wlast,
  .i_lt_axi_s_wuser,
  .i_lt_axi_s_wvalid,
  .o_lt_axi_s_wready,
  .o_lt_axi_s_bvalid,
  .o_lt_axi_s_bid,
  .o_lt_axi_s_buser,
  .o_lt_axi_s_bresp,
  .i_lt_axi_s_bready,
  .i_lt_axi_s_araddr,
  .i_lt_axi_s_arid,
  .i_lt_axi_s_arlen,
  .i_lt_axi_s_arsize,
  .i_lt_axi_s_arburst,
  .i_lt_axi_s_arcache,
  .i_lt_axi_s_arprot,
  .i_lt_axi_s_arqos,
  .i_lt_axi_s_arregion,
  .i_lt_axi_s_aruser,
  .i_lt_axi_s_arlock,
  .i_lt_axi_s_arvalid,
  .o_lt_axi_s_arready,
  .o_lt_axi_s_rvalid,
  .o_lt_axi_s_rlast,
  .o_lt_axi_s_rid,
  .o_lt_axi_s_rdata,
  .o_lt_axi_s_ruser,
  .o_lt_axi_s_rresp,
  .i_lt_axi_s_rready,

  .o_lt_axi_m_awaddr,
  .o_lt_axi_m_awid,
  .o_lt_axi_m_awlen,
  .o_lt_axi_m_awsize,
  .o_lt_axi_m_awburst,
  .o_lt_axi_m_awcache,
  .o_lt_axi_m_awprot,
  .o_lt_axi_m_awlock,
  .o_lt_axi_m_awqos,
  .o_lt_axi_m_awregion,
  .o_lt_axi_m_awuser,
  .o_lt_axi_m_awvalid,
  .i_lt_axi_m_awready,
  .o_lt_axi_m_wdata,
  .o_lt_axi_m_wstrb,
  .o_lt_axi_m_wlast,
  .o_lt_axi_m_wuser,
  .o_lt_axi_m_wvalid,
  .i_lt_axi_m_wready,
  .i_lt_axi_m_bvalid,
  .i_lt_axi_m_bid,
  .i_lt_axi_m_buser,
  .i_lt_axi_m_bresp,
  .o_lt_axi_m_bready,
  .o_lt_axi_m_araddr,
  .o_lt_axi_m_arid,
  .o_lt_axi_m_arlen,
  .o_lt_axi_m_arsize,
  .o_lt_axi_m_arburst,
  .o_lt_axi_m_arcache,
  .o_lt_axi_m_arprot,
  .o_lt_axi_m_arqos,
  .o_lt_axi_m_arregion,
  .o_lt_axi_m_aruser,
  .o_lt_axi_m_arlock,
  .o_lt_axi_m_arvalid,
  .i_lt_axi_m_arready,
  .i_lt_axi_m_rvalid,
  .i_lt_axi_m_rlast,
  .i_lt_axi_m_rid,
  .i_lt_axi_m_rdata,
  .i_lt_axi_m_ruser,
  .i_lt_axi_m_rresp,
  .o_lt_axi_m_rready,

  .i_uart_cst_n,
  .i_uart_rx,
  .o_uart_rts_n,
  .o_uart_tx,
  .o_uart_int,

  .i_gpio,
  .o_gpio_oe,
  .o_gpio,
  .o_gpio_int,

  .o_i2c_0_clk_oe,
  .o_i2c_0_data_oe,
  .i_i2c_0_clk,
  .i_i2c_0_data,
  .o_i2c_0_int,

  .o_i2c_1_clk_oe,
  .o_i2c_1_data_oe,
  .i_i2c_1_clk,
  .i_i2c_1_data,
  .o_i2c_1_int,

  .o_spi_clk(o_spi_clk),
  .o_spi_ss_n,
  .o_spi_sd_oe_n,
  .o_spi_sd,
  .i_spi_sd,
  .o_spi_int,

  .o_timer_int,

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
  .o_emmc_int
);


endmodule
