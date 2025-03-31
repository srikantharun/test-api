
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: Axelera (Axelera@axelera.ai)

`ifndef AIPU_SV
`define AIPU_SV

module aipu

  import aic_common_pkg::*;
  import aic_ls_pkg::*;
  import apu_interrupt_map_pkg::*;
  import apu_pkg::*;
  import axe_tcl_sram_pkg::*;
  import axi_pkg::*;
  import chip_pkg::*;
  import dcd_pkg::*;
  import ddr_west_clock_gen_pkg::*;
  import dmc_pkg::*;
  import emmc_pkg::*;
  import l2_p_pkg::*;
  import lpddr_pkg::*;
  import pcie_pkg::*;
  import pve_pkg::*;
  import rot_pkg::*;
  import soc_mgmt_pkg::*;
  import soc_periph_pkg::*;
  import svs_monitor_pkg::*;
  import sys_spm_pkg::*;


(
  input wire    i_ref_clk,
  input wire    i_tck,
  output wire    o_spi_clk_out,
  input wire    i_ssn_bus_0_clk,
  input wire    i_ssn_bus_1_clk,
  input wire    i_por_rst_n,
  input wire    i_trst_n,
  input logic   i_uart_rx,
  output logic   o_uart_tx,
  input logic   i_uart_cts_n,
  output logic   o_uart_rts_n,
  output logic  [3:0] o_spi_ss_n,
  input logic  [3:0] i_spi_sd,
  output logic  [3:0] o_spi_sd,
  output logic  [3:0] o_spi_sd_oe_n,
  input wire    i_i2c_0_clk,
  output logic   o_i2c_0_clk_oe,
  input wire    i_i2c_1_clk,
  output logic   o_i2c_1_clk_oe,
  input logic   i_i2c_0_data,
  output logic   o_i2c_0_data_oe,
  input logic   i_i2c_1_data,
  output logic   o_i2c_1_data_oe,
  input logic  [15:0] i_gpio,
  output logic  [15:0] o_gpio,
  output logic  [15:0] o_gpio_oe,
  output logic   o_mem_ale_oepad,
  output logic   o_mem_ale_opad,
  input logic   i_mem_cmd_ipad,
  output logic   o_mem_cmd_oepad,
  output logic   o_mem_cmd_iepad,
  output logic   o_mem_cmd_opad,
  output logic   o_mem_ctrl_0_iepad,
  input logic   i_mem_ctrl_0_ipad,
  output logic   o_mem_ctrl_1_oepad,
  output logic   o_mem_ctrl_1_opad,
  output logic   o_mem_rstbar_oepad,
  output logic   o_mem_rstbar_opad,
  input logic   i_mem_lpbk_dqs_ipad,
  output logic   o_mem_lpbk_dqs_iepad,
  input logic   i_mem_dqs_ipad,
  output logic   o_mem_dqs_iepad,
  output logic   o_mem_rebar_oepad,
  output logic   o_mem_rebar_iepad,
  output logic   o_mem_rebar_opad,
  input logic   i_mem_rebar_ipad,
  input logic  [7:0] i_mem_data_ipad,
  output logic  [7:0] o_mem_data_oepad,
  output logic  [7:0] o_mem_data_iepad,
  output logic  [7:0] o_mem_data_opad,
  output logic   o_mem_webar_oepad,
  output logic   o_mem_webar_opad,
  output logic   o_mem_wpbar_iepad,
  input logic   i_mem_wpbar_ipad,
  output logic  [1:0] o_ref_clk_sel_freq,
  output logic  [1:0] o_jtag_drive,
  output logic  [1:0] o_uart_drive,
  output logic  [1:0] o_spi_drive,
  output logic  [1:0] o_i2c_drive,
  output logic  [1:0] o_gpio_drive,
  output logic  [1:0] o_obs_drive,
  output logic  [1:0] o_dft_drive,
  output logic  [2:0] o_emmc_drive,
  output logic   o_clk_schmitt,
  output logic   o_rst_schmitt,
  output logic   o_spi_schmitt,
  output logic   o_uart_schmitt,
  output logic   o_i2c_schmitt,
  output logic   o_gpio_schmitt,
  output logic   o_emmc_schmitt,
  output logic   o_dft_schmitt,
  output logic  [2:0] o_bootmode_pull_en,
  output logic  [3:0] o_spi_sd_pd_en,
  output logic   o_uart_cts_n_pd_en,
  output logic   o_uart_rx_pd_en,
  output logic  [15:0] o_gpio_pd_en,
  output logic  [15:0] o_observability,
  output logic   o_thermal_warning_n,
  output logic   o_thermal_shutdown_n,
  input logic   i_thermal_throttle,
  input logic   i_throttle,
  input logic  [2:0] i_boot_mode,
  input logic   i_tms,
  input logic   i_td,
  output logic   o_td,
  input logic  [45-1:0] i_dft_test,
  output logic  [45-1:0] o_dft_test,
  output logic  [45-1:0] o_dft_test_oe,
  inout wire    io_efuse_vqps,
  inout wire    io_efuse_vddwl,
  inout wire    io_pvt_test_out_ts,
  inout wire    io_otp_vtdo,
  inout wire    io_otp_vrefm,
  inout wire    io_otp_vpp,
  output wire    o_lpddr_ppp_0_bp_memreset_l,
  output wire    o_lpddr_ppp_1_bp_memreset_l,
  output wire    o_lpddr_ppp_2_bp_memreset_l,
  output wire    o_lpddr_ppp_3_bp_memreset_l,
  inout wire   [19:0] io_lpddr_ppp_0_bp_a,
  inout wire   [19:0] io_lpddr_ppp_1_bp_a,
  inout wire   [19:0] io_lpddr_ppp_2_bp_a,
  inout wire   [19:0] io_lpddr_ppp_3_bp_a,
  inout wire    io_lpddr_ppp_0_bp_ato,
  inout wire    io_lpddr_ppp_1_bp_ato,
  inout wire    io_lpddr_ppp_2_bp_ato,
  inout wire    io_lpddr_ppp_3_bp_ato,
  inout wire    io_lpddr_ppp_0_bp_ato_pll,
  inout wire    io_lpddr_ppp_1_bp_ato_pll,
  inout wire    io_lpddr_ppp_2_bp_ato_pll,
  inout wire    io_lpddr_ppp_3_bp_ato_pll,
  inout wire   [12:0] io_lpddr_ppp_0_bp_b0_d,
  inout wire   [12:0] io_lpddr_ppp_1_bp_b0_d,
  inout wire   [12:0] io_lpddr_ppp_2_bp_b0_d,
  inout wire   [12:0] io_lpddr_ppp_3_bp_b0_d,
  inout wire   [12:0] io_lpddr_ppp_0_bp_b1_d,
  inout wire   [12:0] io_lpddr_ppp_1_bp_b1_d,
  inout wire   [12:0] io_lpddr_ppp_2_bp_b1_d,
  inout wire   [12:0] io_lpddr_ppp_3_bp_b1_d,
  inout wire   [12:0] io_lpddr_ppp_0_bp_b2_d,
  inout wire   [12:0] io_lpddr_ppp_1_bp_b2_d,
  inout wire   [12:0] io_lpddr_ppp_2_bp_b2_d,
  inout wire   [12:0] io_lpddr_ppp_3_bp_b2_d,
  inout wire   [12:0] io_lpddr_ppp_0_bp_b3_d,
  inout wire   [12:0] io_lpddr_ppp_1_bp_b3_d,
  inout wire   [12:0] io_lpddr_ppp_2_bp_b3_d,
  inout wire   [12:0] io_lpddr_ppp_3_bp_b3_d,
  inout wire    io_lpddr_ppp_0_bp_ck0_c,
  inout wire    io_lpddr_ppp_1_bp_ck0_c,
  inout wire    io_lpddr_ppp_2_bp_ck0_c,
  inout wire    io_lpddr_ppp_3_bp_ck0_c,
  inout wire    io_lpddr_ppp_0_bp_ck0_t,
  inout wire    io_lpddr_ppp_1_bp_ck0_t,
  inout wire    io_lpddr_ppp_2_bp_ck0_t,
  inout wire    io_lpddr_ppp_3_bp_ck0_t,
  inout wire    io_lpddr_ppp_0_bp_ck1_c,
  inout wire    io_lpddr_ppp_1_bp_ck1_c,
  inout wire    io_lpddr_ppp_2_bp_ck1_c,
  inout wire    io_lpddr_ppp_3_bp_ck1_c,
  inout wire    io_lpddr_ppp_0_bp_ck1_t,
  inout wire    io_lpddr_ppp_1_bp_ck1_t,
  inout wire    io_lpddr_ppp_2_bp_ck1_t,
  inout wire    io_lpddr_ppp_3_bp_ck1_t,
  inout wire    io_lpddr_ppp_0_bp_zn,
  inout wire    io_lpddr_ppp_1_bp_zn,
  inout wire    io_lpddr_ppp_2_bp_zn,
  inout wire    io_lpddr_ppp_3_bp_zn,
  output wire    o_lpddr_graph_0_bp_memreset_l,
  output wire    o_lpddr_graph_1_bp_memreset_l,
  output wire    o_lpddr_graph_2_bp_memreset_l,
  output wire    o_lpddr_graph_3_bp_memreset_l,
  inout wire   [19:0] io_lpddr_graph_0_bp_a,
  inout wire   [19:0] io_lpddr_graph_1_bp_a,
  inout wire   [19:0] io_lpddr_graph_2_bp_a,
  inout wire   [19:0] io_lpddr_graph_3_bp_a,
  inout wire    io_lpddr_graph_0_bp_ato,
  inout wire    io_lpddr_graph_1_bp_ato,
  inout wire    io_lpddr_graph_2_bp_ato,
  inout wire    io_lpddr_graph_3_bp_ato,
  inout wire    io_lpddr_graph_0_bp_ato_pll,
  inout wire    io_lpddr_graph_1_bp_ato_pll,
  inout wire    io_lpddr_graph_2_bp_ato_pll,
  inout wire    io_lpddr_graph_3_bp_ato_pll,
  inout wire   [12:0] io_lpddr_graph_0_bp_b0_d,
  inout wire   [12:0] io_lpddr_graph_1_bp_b0_d,
  inout wire   [12:0] io_lpddr_graph_2_bp_b0_d,
  inout wire   [12:0] io_lpddr_graph_3_bp_b0_d,
  inout wire   [12:0] io_lpddr_graph_0_bp_b1_d,
  inout wire   [12:0] io_lpddr_graph_1_bp_b1_d,
  inout wire   [12:0] io_lpddr_graph_2_bp_b1_d,
  inout wire   [12:0] io_lpddr_graph_3_bp_b1_d,
  inout wire   [12:0] io_lpddr_graph_0_bp_b2_d,
  inout wire   [12:0] io_lpddr_graph_1_bp_b2_d,
  inout wire   [12:0] io_lpddr_graph_2_bp_b2_d,
  inout wire   [12:0] io_lpddr_graph_3_bp_b2_d,
  inout wire   [12:0] io_lpddr_graph_0_bp_b3_d,
  inout wire   [12:0] io_lpddr_graph_1_bp_b3_d,
  inout wire   [12:0] io_lpddr_graph_2_bp_b3_d,
  inout wire   [12:0] io_lpddr_graph_3_bp_b3_d,
  inout wire    io_lpddr_graph_0_bp_ck0_c,
  inout wire    io_lpddr_graph_1_bp_ck0_c,
  inout wire    io_lpddr_graph_2_bp_ck0_c,
  inout wire    io_lpddr_graph_3_bp_ck0_c,
  inout wire    io_lpddr_graph_0_bp_ck0_t,
  inout wire    io_lpddr_graph_1_bp_ck0_t,
  inout wire    io_lpddr_graph_2_bp_ck0_t,
  inout wire    io_lpddr_graph_3_bp_ck0_t,
  inout wire    io_lpddr_graph_0_bp_ck1_c,
  inout wire    io_lpddr_graph_1_bp_ck1_c,
  inout wire    io_lpddr_graph_2_bp_ck1_c,
  inout wire    io_lpddr_graph_3_bp_ck1_c,
  inout wire    io_lpddr_graph_0_bp_ck1_t,
  inout wire    io_lpddr_graph_1_bp_ck1_t,
  inout wire    io_lpddr_graph_2_bp_ck1_t,
  inout wire    io_lpddr_graph_3_bp_ck1_t,
  inout wire    io_lpddr_graph_0_bp_zn,
  inout wire    io_lpddr_graph_1_bp_zn,
  inout wire    io_lpddr_graph_2_bp_zn,
  inout wire    io_lpddr_graph_3_bp_zn,
  input wire    i_pcie_perst_n,
  inout wire    io_pcie_resref,
  input wire    i_ref_pad_clk_p,
  input wire    i_ref_pad_clk_m,
  input logic   i_pcie_rxm_00,
  input logic   i_pcie_rxm_01,
  input logic   i_pcie_rxm_02,
  input logic   i_pcie_rxm_03,
  input logic   i_pcie_rxp_00,
  input logic   i_pcie_rxp_01,
  input logic   i_pcie_rxp_02,
  input logic   i_pcie_rxp_03,
  output logic   o_pcie_txm_00,
  output logic   o_pcie_txm_01,
  output logic   o_pcie_txm_02,
  output logic   o_pcie_txm_03,
  output logic   o_pcie_txp_00,
  output logic   o_pcie_txp_01,
  output logic   o_pcie_txp_02,
  output logic   o_pcie_txp_03
);


  logic  [39:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_0_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_0_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_0_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_0_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_0_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_0_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_0_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_0_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_0_to_u_apu_p__o_stoptime_async;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_tok_idle_val;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bvalid;
  logic  [8:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rresp;
  logic  [39:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awaddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awlock;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_araddr;
  logic  [5:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arprot;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_maddr;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_mcmd;
  logic  [7:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_mdata;
  logic  [15:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_idle_val;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_tok_idle_val;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rresp;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rlast;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awid;
  logic  [39:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awaddr;
  logic  [7:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awburst;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awqos;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wvalid;
  logic  [63:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_bready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arid;
  logic  [39:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_araddr;
  logic  [7:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arburst;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arlock;
  logic  [3:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arqos;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bvalid;
  logic  [10:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rvalid;
  logic  [10:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rlast;
  logic  [15:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_pwr_idle_ack;
  logic   u_noc_top_to_u_pve_p_0__o_pve_0_pwr_idle_val;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rresp;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rlast;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awid;
  logic  [39:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awaddr;
  logic  [7:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awburst;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awqos;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wvalid;
  logic  [63:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_bready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arid;
  logic  [39:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_araddr;
  logic  [7:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arburst;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arlock;
  logic  [3:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arqos;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_awready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_wready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bvalid;
  logic  [10:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bresp;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_arready;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rvalid;
  logic  [10:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rid;
  logic  [511:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rresp;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rlast;
  logic  [15:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_pwr_idle_ack;
  logic   u_noc_top_to_u_pve_p_1__o_pve_1_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_0__o_l2_0_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_1__o_l2_1_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_2__o_l2_2_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_3__o_l2_3_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_4__o_l2_4_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_5__o_l2_5_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_6__o_l2_6_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awprot;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awlock;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awvalid;
  logic  [511:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wdata;
  logic  [63:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wlast;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arprot;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arlock;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_pwr_idle_ack;
  logic   u_noc_top_to_u_l2_p_7__o_l2_7_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_pwr_idle_vec_val;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_araddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_rready;
  logic  [39:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awaddr;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awcache;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awlen;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awlock;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awqos;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awsize;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awvalid;
  logic  [255:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wlast;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wstrb;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wvalid;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_bready;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_paddr;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_penable;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_psel;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pstrb;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pwrite;
  logic  [15:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pprot;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_pwr_idle_vec_ack;
  logic  [1:0] u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_pwr_idle_vec_val;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_awready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_wready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bvalid;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_arready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rvalid;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rlast;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rid;
  logic  [127:0] u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_awready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_wready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bvalid;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_arready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rvalid;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rlast;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rid;
  logic  [127:0] u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_awready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_wready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bvalid;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_arready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rvalid;
  logic   u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rlast;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rid;
  logic  [127:0] u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bvalid;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rlast;
  logic  [4:0] u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rid;
  logic  [127:0] u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rresp;
  logic  [19:0] u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pwrite;
  logic   u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_psel;
  logic   u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pprot;
  logic  [15:0] u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_dcd_p__o_dcd_pwr_idle_ack;
  logic   u_noc_top_to_u_dcd_p__o_dcd_pwr_idle_val;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_pwr_idle_ack;
  logic   u_noc_top_to_u_dcd_p__o_dcd_mcu_pwr_idle_val;
  logic   u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_awready;
  logic   u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_wready;
  logic  [8:0] u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bresp;
  logic   u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bvalid;
  logic   u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_arready;
  logic   u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rlast;
  logic  [8:0] u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rid;
  logic  [255:0] u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rresp;
  logic   u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rvalid;
  logic   u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_wready;
  logic  [9:0] u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bvalid;
  logic   u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rlast;
  logic  [9:0] u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rresp;
  logic   u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rvalid;
  logic  [39:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awaddr;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awqos;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awvalid;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wlast;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wstrb;
  logic  [63:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wdata;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_araddr;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arqos;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_apu_p__o_apu_pwr_idle_ack;
  logic   u_noc_top_to_u_apu_p__o_apu_pwr_idle_val;
  logic   u_noc_top_to_u_apu_p__o_apu_pwr_tok_idle_ack;
  logic   u_noc_top_to_u_apu_p__o_apu_pwr_tok_idle_val;
  logic   u_noc_top_to_u_apu_p__o_apu_init_tok_ocpl_s_scmdaccept;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_maddr;
  logic  [7:0] u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_mdata;
  logic   u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_mcmd;
  logic   u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_0;
  logic   u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_1;
  logic   u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_2;
  logic   u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_3;
  logic   u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_0;
  logic   u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_1;
  logic   u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_2;
  logic   u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_3;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_awready;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_wready;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bvalid;
  logic  [6:0] u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bresp;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_arready;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rvalid;
  logic  [6:0] u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rid;
  logic  [127:0] u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rresp;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rlast;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awvalid;
  logic  [5:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awid;
  logic  [39:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awaddr;
  logic  [7:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awburst;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awqos;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wvalid;
  logic  [127:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wdata;
  logic  [15:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wstrb;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wlast;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_bready;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arvalid;
  logic  [5:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arid;
  logic  [39:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_araddr;
  logic  [7:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arburst;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arlock;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arqos;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_rready;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awvalid;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awid;
  logic  [39:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awaddr;
  logic  [7:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awburst;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awprot;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awqos;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wvalid;
  logic  [31:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wdata;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wstrb;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wlast;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_bready;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arvalid;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arid;
  logic  [39:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_araddr;
  logic  [7:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arburst;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arlock;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arqos;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pprot;
  logic  [19:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pwdata;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pwrite;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_psel;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pprot;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_pwr_idle_ack;
  logic   u_noc_top_to_u_pcie_p__o_pcie_init_mt_pwr_idle_val;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_pwr_idle_ack;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_mt_pwr_idle_val;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_pwr_idle_ack;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_pwr_idle_val;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_pwr_idle_ack;
  logic   u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_pwr_idle_val;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bvalid;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rlast;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rresp;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awvalid;
  logic  [39:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awqos;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wlast;
  logic  [7:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wstrb;
  logic  [63:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wdata;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_bready;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arvalid;
  logic  [39:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arqos;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_rready;
  logic  [18:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_pwr_idle_ack;
  logic   u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awqos;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arqos;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_rready;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_awready;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_wready;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bvalid;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bid;
  logic  [1:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bresp;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_arready;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rvalid;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rlast;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rid;
  logic  [63:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rdata;
  logic  [1:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rresp;
  logic  [15:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_pwr_idle_ack;
  logic   u_noc_top_to_u_soc_periph_p__o_soc_periph_pwr_idle_val;
  logic  [39:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awaddr;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awid;
  logic  [7:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awlen;
  logic  [2:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awsize;
  logic  [1:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awburst;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awcache;
  logic  [2:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awprot;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awlock;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awqos;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awvalid;
  logic  [63:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wdata;
  logic  [7:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wstrb;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wlast;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wvalid;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_bready;
  logic  [39:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_araddr;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arid;
  logic  [7:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arlen;
  logic  [2:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arsize;
  logic  [1:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arburst;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arcache;
  logic  [2:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arprot;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arqos;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arlock;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arvalid;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_rready;
  logic  [15:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_pwr_idle_ack;
  logic   u_noc_top_to_u_sys_spm_p__o_sys_spm_pwr_idle_val;
  logic  [15:0] u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_paddr;
  logic  [31:0] u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pwdata;
  logic   u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pwrite;
  logic   u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_psel;
  logic   u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_penable;
  logic  [3:0] u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pstrb;
  logic  [2:0] u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pprot;
  logic   u_noc_top_to_u_apu_p__o_irq;
  logic  [15:0] u_noc_top_to_u_soc_mgmt_p__o_obs;
  wire   u_soc_mgmt_p_to_multi__o_fast_clk;
  wire   u_soc_mgmt_p_to_multi__o_ao_rst_n;
  wire   u_soc_mgmt_p_to_multi__o_global_rst_n;
  logic   u_soc_mgmt_p_to_multi__o_global_sync;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_debugint_1;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_debugint_2;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_debugint_3;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_debugint_4;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_debugint_5;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_debugint_6;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_debugint_7;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_debugint_8;
  logic  [7:0] u_soc_mgmt_p_to_u_pve_p_0__o_debugint_9;
  logic  [7:0] u_soc_mgmt_p_to_u_pve_p_1__o_debugint_10;
  logic  [5:0] u_soc_mgmt_p_to_u_apu_p__o_debugint_0;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_resethaltreq_1;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_resethaltreq_2;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_resethaltreq_3;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_resethaltreq_4;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_resethaltreq_5;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_resethaltreq_6;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_resethaltreq_7;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_resethaltreq_8;
  logic  [7:0] u_soc_mgmt_p_to_u_pve_p_0__o_resethaltreq_9;
  logic  [7:0] u_soc_mgmt_p_to_u_pve_p_1__o_resethaltreq_10;
  logic  [5:0] u_soc_mgmt_p_to_u_apu_p__o_resethaltreq_0;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_thermal_throttle_0;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_thermal_throttle_1;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_thermal_throttle_2;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_thermal_throttle_3;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_thermal_throttle_4;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_thermal_throttle_5;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_thermal_throttle_6;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_thermal_throttle_7;
  logic   u_soc_mgmt_p_to_u_pve_p_0__o_thermal_throttle_8;
  logic   u_soc_mgmt_p_to_u_pve_p_1__o_thermal_throttle_9;
  logic   u_soc_mgmt_p_to_u_apu_p__o_thermal_throttle_10;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_thermal_warning;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_clock_throttle_0;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_clock_throttle_1;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_clock_throttle_2;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_clock_throttle_3;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_clock_throttle_4;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_clock_throttle_5;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_clock_throttle_6;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_clock_throttle_7;
  logic   u_soc_mgmt_p_to_u_pve_p_0__o_clock_throttle_8;
  logic   u_soc_mgmt_p_to_u_pve_p_1__o_clock_throttle_9;
  logic   u_soc_mgmt_p_to_u_apu_p__o_clock_throttle_10;
  logic   u_soc_mgmt_p_to_u_noc_top__o_clock_throttle_11;
  logic   u_soc_mgmt_p_to_u_noc_top__o_clock_throttle_12;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_aic_throttle;
  logic   u_soc_mgmt_p_to_u_ai_core_p_0__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_1__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_2__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_3__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_4__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_5__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_6__o_aic_boost_ack;
  logic   u_soc_mgmt_p_to_u_ai_core_p_7__o_aic_boost_ack;
  wire   u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk;
  wire   u_soc_mgmt_p_to_multi__o_codec_clk;
  wire   u_soc_mgmt_p_to_multi__o_apu_clk;
  wire   u_soc_mgmt_p_to_multi__o_periph_clk;
  logic  [39:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awaddr;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awid;
  logic  [7:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awlen;
  logic  [2:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awsize;
  logic  [1:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awburst;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awcache;
  logic  [2:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awprot;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awlock;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awqos;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awvalid;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wvalid;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wlast;
  logic  [7:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wstrb;
  logic  [63:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wdata;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_bready;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arvalid;
  logic  [39:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_araddr;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arid;
  logic  [7:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arlen;
  logic  [2:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arsize;
  logic  [1:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arburst;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arcache;
  logic  [2:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arprot;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arqos;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arlock;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_rready;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_awready;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_wready;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bvalid;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bid;
  logic  [1:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bresp;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_arready;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rvalid;
  logic   u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rlast;
  logic  [3:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rid;
  logic  [63:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rdata;
  logic  [1:0] u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rresp;
  logic   u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_pready;
  logic  [31:0] u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_prdata;
  logic   u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_pslverr;
  wire   u_soc_mgmt_p_to_u_noc_top__o_noc_rst_n;
  logic   u_soc_mgmt_p_to_u_noc_top__o_noc_async_idle_req;
  logic   u_soc_mgmt_p_to_u_apu_p__o_rtc_irq;
  logic   u_soc_mgmt_p_to_u_apu_p__o_wdt_irq;
  logic   u_soc_mgmt_p_to_u_apu_p__o_security_irq;
  logic   u_soc_mgmt_p_to_u_apu_p__o_irq_tms_throttle;
  logic   u_soc_mgmt_p_to_u_apu_p__o_irq_tms_warning;
  logic   u_soc_mgmt_p_to_u_apu_p__o_irq_tms_shutdown;
  logic   u_soc_mgmt_p_to_u_apu_p__o_dlm_irq_warning;
  logic   u_soc_mgmt_p_to_u_apu_p__o_dlm_irq_critical;
  wire   u_soc_mgmt_p_to_u_soc_periph_p__o_emmc_clk;
  wire   u_soc_mgmt_p_to_u_noc_top__o_noc_clk;
  logic   u_apu_p_to_u_ai_core_p_0__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_1__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_2__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_3__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_4__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_5__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_6__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_7__o_aic_msip;
  logic   u_apu_p_to_u_ai_core_p_0__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_1__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_2__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_3__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_4__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_5__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_6__o_aic_mtip;
  logic   u_apu_p_to_u_ai_core_p_7__o_aic_mtip;
  logic  [39:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awaddr;
  logic  [8:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awid;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awlen;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awsize;
  logic  [1:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awburst;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awcache;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awprot;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awlock;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awqos;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wlast;
  logic  [31:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wstrb;
  logic  [255:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wdata;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_bready;
  logic  [39:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_araddr;
  logic  [8:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arid;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arlen;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arsize;
  logic  [1:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arburst;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arcache;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arprot;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arqos;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arlock;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_rready;
  logic  [39:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awaddr;
  logic  [APU_AXI_LT_S_ID_W-1:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awid;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awlen;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awsize;
  logic  [1:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awburst;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awcache;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awprot;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awlock;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awqos;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wlast;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wstrb;
  logic  [63:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wdata;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_bready;
  logic  [39:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_araddr;
  logic  [APU_AXI_LT_S_ID_W-1:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arid;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arlen;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arsize;
  logic  [1:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arburst;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arcache;
  logic  [2:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arprot;
  logic  [3:0] u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arqos;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arlock;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_rready;
  logic   u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_awready;
  logic   u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_wready;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bid;
  logic  [1:0] u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bresp;
  logic   u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bvalid;
  logic   u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_arready;
  logic   u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rlast;
  logic  [7:0] u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rid;
  logic  [63:0] u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rdata;
  logic  [1:0] u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rresp;
  logic   u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rvalid;
  logic   u_apu_p_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_apu_p_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_apu_p_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_apu_p_to_u_noc_top__o_noc_async_idle_req;
  logic   u_apu_p_to_u_noc_top__o_noc_tok_async_idle_req;
  logic   u_apu_p_to_u_noc_top__o_noc_rst_n;
  logic   u_apu_p_to_u_noc_top__o_noc_clken;
  logic  [7:0] u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic  [7:0] u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic   u_apu_p_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic  [5:0] u_apu_p_to_u_soc_mgmt_p__o_cores_hart_unavail;
  logic  [5:0] u_apu_p_to_u_soc_mgmt_p__o_cores_hart_under_reset;
  wire   u_apu_p_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_apu_p_to_u_soc_mgmt_p__io_vsense_ts;
  logic  [39:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_1_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_1_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_1_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_1_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_1_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_1_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_1_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_1_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_1_to_u_apu_p__o_stoptime_async;
  logic  [39:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_2_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_2_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_2_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_2_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_2_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_2_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_2_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_2_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_2_to_u_apu_p__o_stoptime_async;
  logic  [39:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_3_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_3_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_3_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_3_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_3_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_3_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_3_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_3_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_3_to_u_apu_p__o_stoptime_async;
  logic  [39:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_4_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_4_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_4_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_4_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_4_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_4_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_4_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_4_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_4_to_u_apu_p__o_stoptime_async;
  logic  [39:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_5_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_5_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_5_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_5_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_5_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_5_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_5_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_5_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_5_to_u_apu_p__o_stoptime_async;
  logic  [39:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_6_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_6_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_6_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_6_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_6_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_6_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_6_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_6_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_6_to_u_apu_p__o_stoptime_async;
  logic  [39:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awid;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awprot;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awlock;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awvalid;
  logic  [511:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wdata;
  logic  [63:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wstrb;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wlast;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wvalid;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_bready;
  logic  [39:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_araddr;
  logic  [8:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arid;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arlen;
  logic  [AIC_HT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arsize;
  logic  [AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arburst;
  logic  [AIC_HT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arcache;
  logic  [AIC_HT_AXI_PROT_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arprot;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arlock;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arvalid;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_rready;
  logic  [39:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awaddr;
  logic  [8:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awid;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awprot;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awlock;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awvalid;
  logic  [63:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wdata;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wstrb;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wlast;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wvalid;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_bready;
  logic  [39:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_araddr;
  logic  [8:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arid;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arburst;
  logic  [AIC_LT_AXI_CACHE_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arcache;
  logic  [AIC_LT_AXI_PROT_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arprot;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arlock;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arvalid;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_rready;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_awready;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_wready;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bvalid;
  logic  [5:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bresp;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_arready;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rvalid;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rlast;
  logic  [5:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rid;
  logic  [63:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rresp;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_maddr;
  logic   u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_mcmd;
  logic  [7:0] u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_mdata;
  logic   u_ai_core_p_7_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept;
  logic   u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_async_idle_req;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_ocpl_tok_async_idle_req;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_rst_n;
  logic   u_ai_core_p_7_to_u_noc_top__o_noc_clken;
  wire   u_ai_core_p_7_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_ai_core_p_7_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_ai_core_p_7_to_u_soc_mgmt_p__o_hart_unavail_async;
  logic   u_ai_core_p_7_to_u_soc_mgmt_p__o_hart_under_reset_async;
  logic   u_ai_core_p_7_to_u_soc_mgmt_p__o_aic_boost_req_async;
  logic  [15:0] u_ai_core_p_7_to_u_soc_mgmt_p__o_aic_obs;
  logic   u_ai_core_p_7_to_u_apu_p__o_stoptime_async;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awid;
  logic  [39:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awaddr;
  logic  [7:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awlen;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awsize;
  logic  [1:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awburst;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awlock;
  logic  [3:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awcache;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awprot;
  logic  [3:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awqos;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wvalid;
  logic  [63:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wdata;
  logic  [7:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wstrb;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wlast;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_bready;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arid;
  logic  [39:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_araddr;
  logic  [7:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arlen;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arsize;
  logic  [1:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arburst;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arlock;
  logic  [3:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arcache;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arprot;
  logic  [3:0] u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arqos;
  logic   u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_rready;
  logic   u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_awready;
  logic   u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_wready;
  logic   u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bid;
  logic  [1:0] u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bresp;
  logic   u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_arready;
  logic   u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rid;
  logic  [63:0] u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rdata;
  logic  [1:0] u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rresp;
  logic   u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rlast;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_awvalid;
  logic  [10:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awid;
  logic  [39:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awaddr;
  logic  [7:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awlen;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awsize;
  logic  [1:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awburst;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_awlock;
  logic  [3:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awcache;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_awprot;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_wvalid;
  logic  [511:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_wdata;
  logic  [63:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_wstrb;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_wlast;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_bready;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_arvalid;
  logic  [10:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_arid;
  logic  [39:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_araddr;
  logic  [7:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_arlen;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_arsize;
  logic  [1:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_arburst;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_arlock;
  logic  [3:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_arcache;
  logic  [2:0] u_pve_p_0_to_u_noc_top__o_dma_axi_m_arprot;
  logic   u_pve_p_0_to_u_noc_top__o_dma_axi_m_rready;
  logic   u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_pve_p_0_to_u_noc_top__o_noc_async_idle_req;
  logic   u_pve_p_0_to_u_noc_top__o_noc_rst_n;
  logic   u_pve_p_0_to_u_noc_top__o_noc_clken;
  logic  [7:0] u_pve_p_0_to_u_soc_mgmt_p__o_hart_unavail;
  logic  [7:0] u_pve_p_0_to_u_soc_mgmt_p__o_hart_under_reset;
  wire   u_pve_p_0_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_pve_p_0_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awid;
  logic  [39:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awaddr;
  logic  [7:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awlen;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awsize;
  logic  [1:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awburst;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awlock;
  logic  [3:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awcache;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awprot;
  logic  [3:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awqos;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wvalid;
  logic  [63:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wdata;
  logic  [7:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wstrb;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wlast;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_bready;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arvalid;
  logic  [PVE_LT_M_ID_W-1:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arid;
  logic  [39:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_araddr;
  logic  [7:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arlen;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arsize;
  logic  [1:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arburst;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arlock;
  logic  [3:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arcache;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arprot;
  logic  [3:0] u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arqos;
  logic   u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_rready;
  logic   u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_awready;
  logic   u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_wready;
  logic   u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bid;
  logic  [1:0] u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bresp;
  logic   u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_arready;
  logic   u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rvalid;
  logic  [PVE_LT_S_ID_W-1:0] u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rid;
  logic  [63:0] u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rdata;
  logic  [1:0] u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rresp;
  logic   u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rlast;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_awvalid;
  logic  [10:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awid;
  logic  [39:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awaddr;
  logic  [7:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awlen;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awsize;
  logic  [1:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awburst;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_awlock;
  logic  [3:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awcache;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_awprot;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_wvalid;
  logic  [511:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_wdata;
  logic  [63:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_wstrb;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_wlast;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_bready;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_arvalid;
  logic  [10:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_arid;
  logic  [39:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_araddr;
  logic  [7:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_arlen;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_arsize;
  logic  [1:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_arburst;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_arlock;
  logic  [3:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_arcache;
  logic  [2:0] u_pve_p_1_to_u_noc_top__o_dma_axi_m_arprot;
  logic   u_pve_p_1_to_u_noc_top__o_dma_axi_m_rready;
  logic   u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_pve_p_1_to_u_noc_top__o_noc_async_idle_req;
  logic   u_pve_p_1_to_u_noc_top__o_noc_rst_n;
  logic   u_pve_p_1_to_u_noc_top__o_noc_clken;
  logic  [7:0] u_pve_p_1_to_u_soc_mgmt_p__o_hart_unavail;
  logic  [7:0] u_pve_p_1_to_u_soc_mgmt_p__o_hart_under_reset;
  wire   u_pve_p_1_to_u_soc_mgmt_p__io_ibias_ts;
  wire   u_pve_p_1_to_u_soc_mgmt_p__io_vsense_ts;
  logic   u_l2_p_0_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_0_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_0_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_0_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_0_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_0_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_0_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_0_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_0_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_0_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_0_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_0_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_0_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_0_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_1_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_1_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_1_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_1_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_1_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_1_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_1_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_1_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_1_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_1_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_1_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_1_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_1_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_1_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_2_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_2_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_2_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_2_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_2_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_2_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_2_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_2_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_2_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_2_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_2_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_2_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_2_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_2_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_3_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_3_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_3_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_3_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_3_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_3_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_3_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_3_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_3_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_3_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_3_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_3_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_3_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_3_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_4_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_4_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_4_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_4_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_4_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_4_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_4_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_4_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_4_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_4_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_4_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_4_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_4_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_4_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_5_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_5_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_5_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_5_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_5_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_5_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_5_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_5_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_5_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_5_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_5_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_5_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_5_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_5_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_6_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_6_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_6_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_6_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_6_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_6_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_6_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_6_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_6_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_6_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_6_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_6_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_6_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_6_to_u_noc_top__o_noc_clken;
  logic   u_l2_p_7_to_u_noc_top__o_ht_axi_s_awready;
  logic   u_l2_p_7_to_u_noc_top__o_ht_axi_s_wready;
  logic   u_l2_p_7_to_u_noc_top__o_ht_axi_s_bvalid;
  logic  [3:0] u_l2_p_7_to_u_noc_top__o_ht_axi_s_bid;
  logic  [1:0] u_l2_p_7_to_u_noc_top__o_ht_axi_s_bresp;
  logic   u_l2_p_7_to_u_noc_top__o_ht_axi_s_arready;
  logic   u_l2_p_7_to_u_noc_top__o_ht_axi_s_rvalid;
  logic   u_l2_p_7_to_u_noc_top__o_ht_axi_s_rlast;
  logic  [3:0] u_l2_p_7_to_u_noc_top__o_ht_axi_s_rid;
  logic  [511:0] u_l2_p_7_to_u_noc_top__o_ht_axi_s_rdata;
  logic  [1:0] u_l2_p_7_to_u_noc_top__o_ht_axi_s_rresp;
  logic   u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_l2_p_7_to_u_noc_top__o_noc_async_idle_req;
  wire   u_l2_p_7_to_u_noc_top__o_noc_rst_n;
  logic   u_l2_p_7_to_u_noc_top__o_noc_clken;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_graph_0_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_graph_0_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_graph_0_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_graph_0_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_graph_0_to_u_soc_mgmt_p__o_lpddr_obs;
  wire   u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk;
  logic   u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic  [15:0] u_ddr_west_clock_gen_p_to_u_soc_mgmt_p__o_ddr_west_clkgen_obs;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_graph_1_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_graph_1_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_graph_1_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_graph_1_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_graph_1_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_graph_2_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_graph_2_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_graph_2_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_graph_2_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_graph_2_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_graph_3_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_graph_3_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_graph_3_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_graph_3_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_graph_3_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_ppp_0_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_ppp_0_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_ppp_0_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_ppp_0_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_ppp_0_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_ppp_1_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_ppp_1_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_ppp_1_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_ppp_1_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_ppp_1_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_ppp_2_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_ppp_2_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_ppp_2_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_ppp_2_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_ppp_2_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_sbr_done_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_derate_temp_limit_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_ap_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_corrected_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_pie_prog_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_ecc_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_rdfptrchk_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_pie_parity_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_acsm_parity_err_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_trng_fail_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_init_cmplt_intr;
  logic   u_lpddr_p_ppp_3_to_u_apu_p__o_phy_trng_cmplt_intr;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_arready;
  logic  [255:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rdata;
  logic  [7:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rid;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rlast;
  logic  [1:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rresp;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rvalid;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_awready;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_wready;
  logic  [7:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bid;
  logic  [1:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bresp;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bvalid;
  logic  [31:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pready;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready;
  logic  [31:0] u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr;
  logic  [1:0] u_lpddr_p_ppp_3_to_u_noc_top__o_noc_async_idle_req;
  wire   u_lpddr_p_ppp_3_to_u_noc_top__o_noc_rst_n;
  logic   u_lpddr_p_ppp_3_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_lpddr_p_ppp_3_to_u_soc_mgmt_p__o_lpddr_obs;
  logic   u_dcd_p_to_u_apu_p__o_pintreq;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awaddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awprot;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awlock;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awqos;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awvalid;
  logic  [127:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wdata;
  logic  [15:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wstrb;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wlast;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wvalid;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_bready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_araddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arprot;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arqos;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arlock;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arvalid;
  logic   u_dcd_p_to_u_noc_top__o_dec_0_axi_m_rready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awaddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awprot;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awlock;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awqos;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awvalid;
  logic  [127:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wdata;
  logic  [15:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wstrb;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wlast;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wvalid;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_bready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_araddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arprot;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arqos;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arlock;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arvalid;
  logic   u_dcd_p_to_u_noc_top__o_dec_1_axi_m_rready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awaddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awprot;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awlock;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awqos;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awvalid;
  logic  [127:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wdata;
  logic  [15:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wstrb;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wlast;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wvalid;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_bready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_araddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arprot;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arqos;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arlock;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arvalid;
  logic   u_dcd_p_to_u_noc_top__o_dec_2_axi_m_rready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awaddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awprot;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_awlock;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_awqos;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_awvalid;
  logic  [127:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_wdata;
  logic  [15:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_wstrb;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_wlast;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_wvalid;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_bready;
  logic  [39:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_araddr;
  logic  [4:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arid;
  logic  [7:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arlen;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arsize;
  logic  [1:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arburst;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arcache;
  logic  [2:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arprot;
  logic  [3:0] u_dcd_p_to_u_noc_top__o_mcu_axi_m_arqos;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_arlock;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_arvalid;
  logic   u_dcd_p_to_u_noc_top__o_mcu_axi_m_rready;
  logic   u_dcd_p_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_dcd_p_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_dcd_p_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_pready;
  logic  [31:0] u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_prdata;
  logic   u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_pslverr;
  logic   u_dcd_p_to_u_noc_top__o_noc_async_idle_req;
  logic   u_dcd_p_to_u_noc_top__o_noc_mcu_async_idle_req;
  logic   u_dcd_p_to_u_noc_top__o_noc_clk_en;
  logic   u_dcd_p_to_u_noc_top__o_noc_mcu_clk_en;
  wire   u_dcd_p_to_u_noc_top__o_noc_rst_n;
  wire   u_dcd_p_to_u_noc_top__o_noc_mcu_rst_n;
  logic  [15:0] u_dcd_p_to_u_soc_mgmt_p__o_dcd_obs;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awvalid;
  logic  [6:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awid;
  logic  [39:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awaddr;
  logic  [7:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awlen;
  logic  [2:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awsize;
  logic  [1:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awburst;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awlock;
  logic  [3:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awcache;
  logic  [2:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awprot;
  logic  [3:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awqos;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wvalid;
  logic  [127:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wdata;
  logic  [15:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wstrb;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wlast;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_bready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arvalid;
  logic  [6:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arid;
  logic  [39:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_araddr;
  logic  [7:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arlen;
  logic  [2:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arsize;
  logic  [1:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arburst;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arlock;
  logic  [3:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arcache;
  logic  [2:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arprot;
  logic  [3:0] u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arqos;
  logic   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_rready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_awready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_wready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bvalid;
  logic  [5:0] u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bid;
  logic  [1:0] u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bresp;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_arready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rvalid;
  logic  [5:0] u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rid;
  logic  [127:0] u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rdata;
  logic  [1:0] u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rresp;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rlast;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_awready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_wready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bvalid;
  logic  [3:0] u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bid;
  logic  [1:0] u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bresp;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_arready;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rvalid;
  logic  [3:0] u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rid;
  logic  [31:0] u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rdata;
  logic  [1:0] u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rresp;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rlast;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_pready;
  logic  [31:0] u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_prdata;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_pslverr;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_pready;
  logic  [31:0] u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_prdata;
  logic   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_pslverr;
  logic   u_pcie_p_to_u_noc_top__o_noc_init_mt_axi_clken;
  logic   u_pcie_p_to_u_noc_top__o_noc_targ_mt_axi_clken;
  logic   u_pcie_p_to_u_noc_top__o_noc_targ_cfg_dbi_axi_clken;
  logic   u_pcie_p_to_u_noc_top__o_noc_targ_cfg_apb_clken;
  wire   u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_rst_n;
  wire   u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rst_n;
  wire   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rst_n;
  wire   u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_rst_n;
  logic   u_pcie_p_to_u_noc_top__o_noc_async_idle_init_mt_axi_req;
  logic   u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_mt_axi_req;
  logic   u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_cfg_apb_req;
  logic   u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_cfg_dbi_axi_req;
  logic  [15:0] u_pcie_p_to_u_soc_mgmt_p__o_pcie_obs;
  logic   u_pcie_p_to_u_apu_p__o_pcie_int;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_s_awready;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_s_wready;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bvalid;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bid;
  logic  [1:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bresp;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_s_arready;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rvalid;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rlast;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rid;
  logic  [63:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rdata;
  logic  [1:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rresp;
  logic  [39:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awaddr;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awid;
  logic  [7:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awlen;
  logic  [2:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awsize;
  logic  [1:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awburst;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awcache;
  logic  [2:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awprot;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awlock;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awqos;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awvalid;
  logic  [63:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wdata;
  logic  [7:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wstrb;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wlast;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wvalid;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_bready;
  logic  [39:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_araddr;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arid;
  logic  [7:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arlen;
  logic  [2:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arsize;
  logic  [1:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arburst;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arcache;
  logic  [2:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arprot;
  logic  [3:0] u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arqos;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arlock;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arvalid;
  logic   u_soc_periph_p_to_u_noc_top__o_lt_axi_m_rready;
  logic   u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_soc_periph_p_to_u_noc_top__o_noc_async_idle_req;
  logic   u_soc_periph_p_to_u_noc_top__o_noc_rst_n;
  logic   u_soc_periph_p_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_soc_periph_p_to_u_soc_mgmt_p__o_obs;
  logic   u_soc_periph_p_to_u_apu_p__o_uart_int;
  logic   u_soc_periph_p_to_u_apu_p__o_gpio_int;
  logic   u_soc_periph_p_to_u_apu_p__o_i2c_0_int;
  logic   u_soc_periph_p_to_u_apu_p__o_i2c_1_int;
  logic   u_soc_periph_p_to_u_apu_p__o_timer_int;
  logic   u_soc_periph_p_to_u_apu_p__o_spi_int;
  logic   u_soc_periph_p_to_u_apu_p__o_emmc_int;
  logic   u_sys_spm_p_to_u_noc_top__o_lt_axi_s_awready;
  logic   u_sys_spm_p_to_u_noc_top__o_lt_axi_s_wready;
  logic   u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bvalid;
  logic  [3:0] u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bid;
  logic  [1:0] u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bresp;
  logic   u_sys_spm_p_to_u_noc_top__o_lt_axi_s_arready;
  logic   u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rvalid;
  logic   u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rlast;
  logic  [3:0] u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rid;
  logic  [63:0] u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rdata;
  logic  [1:0] u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rresp;
  logic   u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_pready;
  logic  [31:0] u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_prdata;
  logic   u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_pslverr;
  logic   u_sys_spm_p_to_u_noc_top__o_noc_async_idle_req;
  wire   u_sys_spm_p_to_u_noc_top__o_noc_rst_n;
  logic   u_sys_spm_p_to_u_noc_top__o_noc_clken;
  logic  [15:0] u_sys_spm_p_to_u_soc_mgmt_p__o_sysspm_obs;
  logic   u_sys_spm_p_to_u_apu_p__o_irq;
  wire  [52-1:0] u_soc_mgmt_p_io_pvt_ibias_ts_unconn;
  wire  [52-1:0] u_soc_mgmt_p_io_pvt_vsense_ts_unconn;
  logic   u_soc_mgmt_p_o_thermal_throttle_unconn;
  logic  [4-1:0] u_soc_mgmt_p_o_thermal_warning_unconn;
  logic  [2-1:0] u_soc_mgmt_p_o_clock_throttle_unconn;



`ifdef AI_CORE_P_0_STUB
ai_core_p_stub u_ai_core_p_0 (
`else
ai_core_p u_ai_core_p_0 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_thermal_throttle_0),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_clock_throttle_0),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_0_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd1),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_0_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_0__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_0__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_debugint_1),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_0__o_resethaltreq_1),
  .o_stoptime_async (u_ai_core_p_0_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_0_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_0_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_0_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_0_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_0_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_0_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_0_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_0_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_0_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_1_STUB
ai_core_p_stub u_ai_core_p_1 (
`else
ai_core_p u_ai_core_p_1 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_thermal_throttle_1),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_clock_throttle_1),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_1_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd2),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_1_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_1__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_1__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_debugint_2),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_1__o_resethaltreq_2),
  .o_stoptime_async (u_ai_core_p_1_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_1_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_1_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_1_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_1_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_1_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_1_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_1_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_1_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_1_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_2_STUB
ai_core_p_stub u_ai_core_p_2 (
`else
ai_core_p u_ai_core_p_2 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_thermal_throttle_2),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_clock_throttle_2),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_2_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd3),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_2_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_2__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_2__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_debugint_3),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_2__o_resethaltreq_3),
  .o_stoptime_async (u_ai_core_p_2_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_2_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_2_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_2_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_2_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_2_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_2_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_2_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_2_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_2_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_3_STUB
ai_core_p_stub u_ai_core_p_3 (
`else
ai_core_p u_ai_core_p_3 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_thermal_throttle_3),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_clock_throttle_3),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_3_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd4),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_3_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_3__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_3__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_debugint_4),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_3__o_resethaltreq_4),
  .o_stoptime_async (u_ai_core_p_3_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_3_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_3_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_3_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_3_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_3_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_3_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_3_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_3_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_3_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_4_STUB
ai_core_p_stub u_ai_core_p_4 (
`else
ai_core_p u_ai_core_p_4 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_thermal_throttle_4),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_clock_throttle_4),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_4_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd5),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_4_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_4__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_4__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_debugint_5),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_4__o_resethaltreq_5),
  .o_stoptime_async (u_ai_core_p_4_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_4_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_4_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_4_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_4_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_4_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_4_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_4_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_4_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_4_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_5_STUB
ai_core_p_stub u_ai_core_p_5 (
`else
ai_core_p u_ai_core_p_5 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_thermal_throttle_5),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_clock_throttle_5),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_5_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd6),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_5_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_5__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_5__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_debugint_6),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_5__o_resethaltreq_6),
  .o_stoptime_async (u_ai_core_p_5_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_5_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_5_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_5_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_5_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_5_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_5_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_5_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_5_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_5_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_6_STUB
ai_core_p_stub u_ai_core_p_6 (
`else
ai_core_p u_ai_core_p_6 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_thermal_throttle_6),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_clock_throttle_6),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_6_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd7),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_6_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_6__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_6__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_debugint_7),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_6__o_resethaltreq_7),
  .o_stoptime_async (u_ai_core_p_6_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_6_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_6_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_6_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_6_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_6_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_6_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_6_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_6_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_6_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef AI_CORE_P_7_STUB
ai_core_p_stub u_ai_core_p_7 (
`else
ai_core_p u_ai_core_p_7 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .i_thermal_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_thermal_throttle_7),
  .i_clock_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_clock_throttle_7),
  .i_aic_throttle_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_aic_throttle),
  .i_thermal_warning_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_thermal_warning),
  .i_aic_boost_ack_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_aic_boost_ack),
  .o_aic_boost_req_async (u_ai_core_p_7_to_u_soc_mgmt_p__o_aic_boost_req_async),
  .i_cid (12'd8),
  .o_tok_prod_ocpl_m_maddr (u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_tok_ocpl_s_scmdaccept),
  .o_tok_prod_ocpl_m_mdata (u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_ai_core_p_7_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_mdata),
  .o_irq (),
  .i_msip_async (u_apu_p_to_u_ai_core_p_7__o_aic_msip),
  .i_mtip_async (u_apu_p_to_u_ai_core_p_7__o_aic_mtip),
  .i_debug_int_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_debugint_8),
  .i_resethaltreq_async (u_soc_mgmt_p_to_u_ai_core_p_7__o_resethaltreq_8),
  .o_stoptime_async (u_ai_core_p_7_to_u_apu_p__o_stoptime_async),
  .o_hart_unavail_async (u_ai_core_p_7_to_u_soc_mgmt_p__o_hart_unavail_async),
  .o_hart_under_reset_async (u_ai_core_p_7_to_u_soc_mgmt_p__o_hart_under_reset_async),
  .io_ibias_ts (u_ai_core_p_7_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_ai_core_p_7_to_u_soc_mgmt_p__io_vsense_ts),
  .o_aic_obs (u_ai_core_p_7_to_u_soc_mgmt_p__o_aic_obs),
  .i_reserved ('0),
  .o_reserved (),
  .o_noc_ht_axi_m_awaddr (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_awvalid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .i_noc_ht_axi_m_awready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_awready),
  .o_noc_ht_axi_m_wdata (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_wstrb (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wlast (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wvalid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_noc_ht_axi_m_wready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_wready),
  .i_noc_ht_axi_m_bvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bvalid),
  .i_noc_ht_axi_m_bid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bid),
  .i_noc_ht_axi_m_bresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bresp),
  .o_noc_ht_axi_m_bready (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_araddr (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_arvalid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .i_noc_ht_axi_m_arready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_arready),
  .i_noc_ht_axi_m_rvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rvalid),
  .i_noc_ht_axi_m_rlast (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rlast),
  .i_noc_ht_axi_m_rid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rid),
  .i_noc_ht_axi_m_rdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rdata),
  .i_noc_ht_axi_m_rresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rresp),
  .o_noc_ht_axi_m_rready (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_noc_lt_axi_m_awaddr (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_awvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .i_noc_lt_axi_m_awready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_awready),
  .o_noc_lt_axi_m_wdata (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_wstrb (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wlast (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .i_noc_lt_axi_m_wready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_wready),
  .i_noc_lt_axi_m_bvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bvalid),
  .i_noc_lt_axi_m_bid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bid),
  .i_noc_lt_axi_m_bresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bresp),
  .o_noc_lt_axi_m_bready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_araddr (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_arvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_noc_lt_axi_m_arready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_arready),
  .i_noc_lt_axi_m_rvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rvalid),
  .i_noc_lt_axi_m_rlast (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rlast),
  .i_noc_lt_axi_m_rid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rid),
  .i_noc_lt_axi_m_rdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rdata),
  .i_noc_lt_axi_m_rresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rresp),
  .o_noc_lt_axi_m_rready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_s_awaddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awaddr),
  .i_noc_lt_axi_s_awid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awid),
  .i_noc_lt_axi_s_awlen (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awlen),
  .i_noc_lt_axi_s_awsize (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awsize),
  .i_noc_lt_axi_s_awburst (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awburst),
  .i_noc_lt_axi_s_awcache (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awcache),
  .i_noc_lt_axi_s_awprot (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awprot),
  .i_noc_lt_axi_s_awlock (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awlock),
  .i_noc_lt_axi_s_awvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awvalid),
  .o_noc_lt_axi_s_awready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_awready),
  .i_noc_lt_axi_s_wdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wdata),
  .i_noc_lt_axi_s_wstrb (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wstrb),
  .i_noc_lt_axi_s_wlast (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wlast),
  .i_noc_lt_axi_s_wvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wvalid),
  .o_noc_lt_axi_s_wready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_noc_lt_axi_s_bready (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_bready),
  .i_noc_lt_axi_s_araddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_araddr),
  .i_noc_lt_axi_s_arid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arid),
  .i_noc_lt_axi_s_arlen (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arlen),
  .i_noc_lt_axi_s_arsize (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arsize),
  .i_noc_lt_axi_s_arburst (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arburst),
  .i_noc_lt_axi_s_arcache (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arcache),
  .i_noc_lt_axi_s_arprot (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arprot),
  .i_noc_lt_axi_s_arlock (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arlock),
  .i_noc_lt_axi_s_arvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arvalid),
  .o_noc_lt_axi_s_arready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_noc_lt_axi_s_rready (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_ai_core_p_7_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_idle_val),
  .o_noc_clken (u_ai_core_p_7_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_ai_core_p_7_to_u_noc_top__o_noc_rst_n),
  .o_noc_ocpl_tok_async_idle_req (u_ai_core_p_7_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_noc_ocpl_tok_async_idle_ack (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_tok_idle_ack),
  .i_noc_ocpl_tok_async_idle_val (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_tok_idle_val),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so ()
);
`ifdef APU_P_STUB
apu_p_stub u_apu_p (
`else
apu_p u_apu_p (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_apu_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_clock_throttle (u_soc_mgmt_p_to_u_apu_p__o_clock_throttle_10),
  .i_thermal_throttle (u_soc_mgmt_p_to_u_apu_p__o_thermal_throttle_10),
  .i_cores_nmi ('0),
  .o_aic_msip ({
  u_apu_p_to_u_ai_core_p_7__o_aic_msip,
  u_apu_p_to_u_ai_core_p_6__o_aic_msip,
  u_apu_p_to_u_ai_core_p_5__o_aic_msip,
  u_apu_p_to_u_ai_core_p_4__o_aic_msip,
  u_apu_p_to_u_ai_core_p_3__o_aic_msip,
  u_apu_p_to_u_ai_core_p_2__o_aic_msip,
  u_apu_p_to_u_ai_core_p_1__o_aic_msip,
  u_apu_p_to_u_ai_core_p_0__o_aic_msip}),
  .o_aic_mtip ({
  u_apu_p_to_u_ai_core_p_7__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_6__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_5__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_4__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_3__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_2__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_1__o_aic_mtip,
  u_apu_p_to_u_ai_core_p_0__o_aic_mtip}),
  .i_aic_stoptime ({
  u_ai_core_p_7_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_6_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_5_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_4_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_3_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_2_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_1_to_u_apu_p__o_stoptime_async,
  u_ai_core_p_0_to_u_apu_p__o_stoptime_async}),
  .i_irq__soc_mgmt__thermal_throttle (u_soc_mgmt_p_to_u_apu_p__o_irq_tms_throttle),
  .i_irq__soc_mgmt__thermal_warning (u_soc_mgmt_p_to_u_apu_p__o_irq_tms_warning),
  .i_irq__soc_mgmt__thermal_shutdown (u_soc_mgmt_p_to_u_apu_p__o_irq_tms_shutdown),
  .i_irq__lpddr_graph_0__ctrl_derate_temp_limit (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_graph_1__ctrl_derate_temp_limit (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_graph_2__ctrl_derate_temp_limit (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_graph_3__ctrl_derate_temp_limit (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_ppp_0__ctrl_derate_temp_limit (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_ppp_1__ctrl_derate_temp_limit (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_ppp_2__ctrl_derate_temp_limit (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__lpddr_ppp_3__ctrl_derate_temp_limit (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .i_irq__soc_mgmt__dlm_warning (u_soc_mgmt_p_to_u_apu_p__o_dlm_irq_warning),
  .i_irq__soc_mgmt__dlm_critical (u_soc_mgmt_p_to_u_apu_p__o_dlm_irq_critical),
  .i_irq__lpddr_graph_0__ctrl_ecc_uncorrected_err (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_graph_0__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_graph_0__phy_pie_prog_err (u_lpddr_p_graph_0_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_graph_0__phy_ecc_err (u_lpddr_p_graph_0_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_graph_0__phy_rdfptrchk_err (u_lpddr_p_graph_0_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_graph_0__phy_pie_parity_err (u_lpddr_p_graph_0_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_graph_0__phy_acsm_parity_err (u_lpddr_p_graph_0_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_graph_1__ctrl_ecc_uncorrected_err (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_graph_1__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_graph_1__phy_pie_prog_err (u_lpddr_p_graph_1_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_graph_1__phy_ecc_err (u_lpddr_p_graph_1_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_graph_1__phy_rdfptrchk_err (u_lpddr_p_graph_1_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_graph_1__phy_pie_parity_err (u_lpddr_p_graph_1_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_graph_1__phy_acsm_parity_err (u_lpddr_p_graph_1_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_graph_2__ctrl_ecc_uncorrected_err (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_graph_2__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_graph_2__phy_pie_prog_err (u_lpddr_p_graph_2_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_graph_2__phy_ecc_err (u_lpddr_p_graph_2_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_graph_2__phy_rdfptrchk_err (u_lpddr_p_graph_2_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_graph_2__phy_pie_parity_err (u_lpddr_p_graph_2_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_graph_2__phy_acsm_parity_err (u_lpddr_p_graph_2_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_graph_3__ctrl_ecc_uncorrected_err (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_graph_3__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_graph_3__phy_pie_prog_err (u_lpddr_p_graph_3_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_graph_3__phy_ecc_err (u_lpddr_p_graph_3_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_graph_3__phy_rdfptrchk_err (u_lpddr_p_graph_3_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_graph_3__phy_pie_parity_err (u_lpddr_p_graph_3_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_graph_3__phy_acsm_parity_err (u_lpddr_p_graph_3_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_ppp_0__ctrl_ecc_uncorrected_err (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_ppp_0__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_ppp_0__phy_pie_prog_err (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_ppp_0__phy_ecc_err (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_ppp_0__phy_rdfptrchk_err (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_ppp_0__phy_pie_parity_err (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_ppp_0__phy_acsm_parity_err (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_ppp_1__ctrl_ecc_uncorrected_err (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_ppp_1__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_ppp_1__phy_pie_prog_err (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_ppp_1__phy_ecc_err (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_ppp_1__phy_rdfptrchk_err (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_ppp_1__phy_pie_parity_err (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_ppp_1__phy_acsm_parity_err (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_ppp_2__ctrl_ecc_uncorrected_err (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_ppp_2__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_ppp_2__phy_pie_prog_err (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_ppp_2__phy_ecc_err (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_ppp_2__phy_rdfptrchk_err (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_ppp_2__phy_pie_parity_err (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_ppp_2__phy_acsm_parity_err (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__lpddr_ppp_3__ctrl_ecc_uncorrected_err (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .i_irq__lpddr_ppp_3__ctrl_rd_linkecc_uncorr_err (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .i_irq__lpddr_ppp_3__phy_pie_prog_err (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_pie_prog_err_intr),
  .i_irq__lpddr_ppp_3__phy_ecc_err (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_ecc_err_intr),
  .i_irq__lpddr_ppp_3__phy_rdfptrchk_err (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .i_irq__lpddr_ppp_3__phy_pie_parity_err (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_pie_parity_err_intr),
  .i_irq__lpddr_ppp_3__phy_acsm_parity_err (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .i_irq__pcie__perst_n (i_pcie_perst_n),
  .i_irq__sys_spm__error (u_sys_spm_p_to_u_apu_p__o_irq),
  .i_irq__lpddr_graph_0__ctrl_ecc_ap_err (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_graph_0__phy_trng_fail (u_lpddr_p_graph_0_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_graph_1__ctrl_ecc_ap_err (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_graph_1__phy_trng_fail (u_lpddr_p_graph_1_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_graph_2__ctrl_ecc_ap_err (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_graph_2__phy_trng_fail (u_lpddr_p_graph_2_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_graph_3__ctrl_ecc_ap_err (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_graph_3__phy_trng_fail (u_lpddr_p_graph_3_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_ppp_0__ctrl_ecc_ap_err (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_ppp_0__phy_trng_fail (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_ppp_1__ctrl_ecc_ap_err (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_ppp_1__phy_trng_fail (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_ppp_2__ctrl_ecc_ap_err (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_ppp_2__phy_trng_fail (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__lpddr_ppp_3__ctrl_ecc_ap_err (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .i_irq__lpddr_ppp_3__phy_trng_fail (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_trng_fail_intr),
  .i_irq__soc_mgmt__rtc (u_soc_mgmt_p_to_u_apu_p__o_rtc_irq),
  .i_irq__soc_mgmt__wdt (u_soc_mgmt_p_to_u_apu_p__o_wdt_irq),
  .i_irq__soc_periph__timer (u_soc_periph_p_to_u_apu_p__o_timer_int),
  .i_irq__lpddr_graph_0__ctrl_sbr_done (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_graph_0__ctrl_ecc_corrected_err (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_graph_0__ctrl_rd_linkecc_corr_err (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_graph_0__phy_init_cmplt (u_lpddr_p_graph_0_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_graph_0__phy_trng_cmplt (u_lpddr_p_graph_0_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_graph_1__ctrl_sbr_done (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_graph_1__ctrl_ecc_corrected_err (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_graph_1__ctrl_rd_linkecc_corr_err (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_graph_1__phy_init_cmplt (u_lpddr_p_graph_1_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_graph_1__phy_trng_cmplt (u_lpddr_p_graph_1_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_graph_2__ctrl_sbr_done (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_graph_2__ctrl_ecc_corrected_err (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_graph_2__ctrl_rd_linkecc_corr_err (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_graph_2__phy_init_cmplt (u_lpddr_p_graph_2_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_graph_2__phy_trng_cmplt (u_lpddr_p_graph_2_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_graph_3__ctrl_sbr_done (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_graph_3__ctrl_ecc_corrected_err (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_graph_3__ctrl_rd_linkecc_corr_err (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_graph_3__phy_init_cmplt (u_lpddr_p_graph_3_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_graph_3__phy_trng_cmplt (u_lpddr_p_graph_3_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_ppp_0__ctrl_sbr_done (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_ppp_0__ctrl_ecc_corrected_err (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_ppp_0__ctrl_rd_linkecc_corr_err (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_ppp_0__phy_init_cmplt (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_ppp_0__phy_trng_cmplt (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_ppp_1__ctrl_sbr_done (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_ppp_1__ctrl_ecc_corrected_err (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_ppp_1__ctrl_rd_linkecc_corr_err (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_ppp_1__phy_init_cmplt (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_ppp_1__phy_trng_cmplt (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_ppp_2__ctrl_sbr_done (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_ppp_2__ctrl_ecc_corrected_err (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_ppp_2__ctrl_rd_linkecc_corr_err (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_ppp_2__phy_init_cmplt (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_ppp_2__phy_trng_cmplt (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__lpddr_ppp_3__ctrl_sbr_done (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_sbr_done_intr),
  .i_irq__lpddr_ppp_3__ctrl_ecc_corrected_err (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .i_irq__lpddr_ppp_3__ctrl_rd_linkecc_corr_err (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .i_irq__lpddr_ppp_3__phy_init_cmplt (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_init_cmplt_intr),
  .i_irq__lpddr_ppp_3__phy_trng_cmplt (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_trng_cmplt_intr),
  .i_irq__soc_mgmt__security (u_soc_mgmt_p_to_u_apu_p__o_security_irq),
  .i_irq__soc_periph__emmc (u_soc_periph_p_to_u_apu_p__o_emmc_int),
  .i_irq__dcd__int (u_dcd_p_to_u_apu_p__o_pintreq),
  .i_irq__noc__int (u_noc_top_to_u_apu_p__o_irq),
  .i_irq__noc__sdma_0_int_0 (u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_0),
  .i_irq__noc__sdma_0_int_1 (u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_1),
  .i_irq__noc__sdma_0_int_2 (u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_2),
  .i_irq__noc__sdma_0_int_3 (u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_3),
  .i_irq__noc__sdma_1_int_0 (u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_0),
  .i_irq__noc__sdma_1_int_1 (u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_1),
  .i_irq__noc__sdma_1_int_2 (u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_2),
  .i_irq__noc__sdma_1_int_3 (u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_3),
  .i_irq__soc_periph__uart (u_soc_periph_p_to_u_apu_p__o_uart_int),
  .i_irq__soc_periph__gpio (u_soc_periph_p_to_u_apu_p__o_gpio_int),
  .i_irq__soc_periph__i2c_0 (u_soc_periph_p_to_u_apu_p__o_i2c_0_int),
  .i_irq__soc_periph__i2c_1 (u_soc_periph_p_to_u_apu_p__o_i2c_1_int),
  .i_irq__soc_periph__spi (u_soc_periph_p_to_u_apu_p__o_spi_int),
  .i_irq__pcie__int (u_pcie_p_to_u_apu_p__o_pcie_int),
  .i_cores_debugint (u_soc_mgmt_p_to_u_apu_p__o_debugint_0),
  .i_cores_resethaltreq (u_soc_mgmt_p_to_u_apu_p__o_resethaltreq_0),
  .o_cores_hart_unavail (u_apu_p_to_u_soc_mgmt_p__o_cores_hart_unavail),
  .o_cores_hart_under_reset (u_apu_p_to_u_soc_mgmt_p__o_cores_hart_under_reset),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_apu_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_apu_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_apu_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_apu_p_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_apu_p__o_apu_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_apu_p__o_apu_pwr_idle_val),
  .o_noc_tok_async_idle_req (u_apu_p_to_u_noc_top__o_noc_tok_async_idle_req),
  .i_noc_tok_async_idle_ack (u_noc_top_to_u_apu_p__o_apu_pwr_tok_idle_ack),
  .i_noc_tok_async_idle_val (u_noc_top_to_u_apu_p__o_apu_pwr_tok_idle_val),
  .o_noc_clken (u_apu_p_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_apu_p_to_u_noc_top__o_noc_rst_n),
  .o_apu_init_lt_axi_m_awaddr (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awaddr),
  .o_apu_init_lt_axi_m_awid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awid),
  .o_apu_init_lt_axi_m_awlen (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awlen),
  .o_apu_init_lt_axi_m_awsize (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awsize),
  .o_apu_init_lt_axi_m_awburst (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awburst),
  .o_apu_init_lt_axi_m_awcache (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awcache),
  .o_apu_init_lt_axi_m_awprot (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awprot),
  .o_apu_init_lt_axi_m_awlock (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awlock),
  .o_apu_init_lt_axi_m_awqos (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awqos),
  .o_apu_init_lt_axi_m_awregion (),
  .o_apu_init_lt_axi_m_awuser (),
  .i_apu_init_lt_axi_m_awready (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_awready),
  .o_apu_init_lt_axi_m_awvalid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awvalid),
  .o_apu_init_lt_axi_m_wlast (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wlast),
  .o_apu_init_lt_axi_m_wstrb (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wstrb),
  .o_apu_init_lt_axi_m_wdata (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wdata),
  .o_apu_init_lt_axi_m_wuser (),
  .i_apu_init_lt_axi_m_wready (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_wready),
  .o_apu_init_lt_axi_m_wvalid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wvalid),
  .i_apu_init_lt_axi_m_bid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bid),
  .i_apu_init_lt_axi_m_bresp (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bresp),
  .i_apu_init_lt_axi_m_buser ('0),
  .o_apu_init_lt_axi_m_bready (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_bready),
  .i_apu_init_lt_axi_m_bvalid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bvalid),
  .o_apu_init_lt_axi_m_araddr (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_araddr),
  .o_apu_init_lt_axi_m_arid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arid),
  .o_apu_init_lt_axi_m_arlen (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arlen),
  .o_apu_init_lt_axi_m_arsize (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arsize),
  .o_apu_init_lt_axi_m_arburst (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arburst),
  .o_apu_init_lt_axi_m_arcache (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arcache),
  .o_apu_init_lt_axi_m_arprot (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arprot),
  .o_apu_init_lt_axi_m_arqos (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arqos),
  .o_apu_init_lt_axi_m_arregion (),
  .o_apu_init_lt_axi_m_aruser (),
  .o_apu_init_lt_axi_m_arlock (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arlock),
  .i_apu_init_lt_axi_m_arready (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_arready),
  .o_apu_init_lt_axi_m_arvalid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arvalid),
  .i_apu_init_lt_axi_m_rlast (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rlast),
  .i_apu_init_lt_axi_m_rid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rid),
  .i_apu_init_lt_axi_m_rdata (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rdata),
  .i_apu_init_lt_axi_m_rresp (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rresp),
  .i_apu_init_lt_axi_m_ruser ('0),
  .o_apu_init_lt_axi_m_rready (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_rready),
  .i_apu_init_lt_axi_m_rvalid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rvalid),
  .i_apu_targ_lt_axi_s_awaddr (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awaddr),
  .i_apu_targ_lt_axi_s_awid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awid),
  .i_apu_targ_lt_axi_s_awlen (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awlen),
  .i_apu_targ_lt_axi_s_awsize (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awsize),
  .i_apu_targ_lt_axi_s_awburst (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awburst),
  .i_apu_targ_lt_axi_s_awcache (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awcache),
  .i_apu_targ_lt_axi_s_awprot (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awprot),
  .i_apu_targ_lt_axi_s_awlock (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awlock),
  .i_apu_targ_lt_axi_s_awqos (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awqos),
  .i_apu_targ_lt_axi_s_awregion ('0),
  .i_apu_targ_lt_axi_s_awuser ('0),
  .o_apu_targ_lt_axi_s_awready (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_awready),
  .i_apu_targ_lt_axi_s_awvalid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awvalid),
  .i_apu_targ_lt_axi_s_wlast (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wlast),
  .i_apu_targ_lt_axi_s_wstrb (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wstrb),
  .i_apu_targ_lt_axi_s_wdata (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wdata),
  .i_apu_targ_lt_axi_s_wuser ('0),
  .o_apu_targ_lt_axi_s_wready (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_wready),
  .i_apu_targ_lt_axi_s_wvalid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wvalid),
  .o_apu_targ_lt_axi_s_bid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bid),
  .o_apu_targ_lt_axi_s_bresp (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bresp),
  .o_apu_targ_lt_axi_s_buser (),
  .i_apu_targ_lt_axi_s_bready (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_bready),
  .o_apu_targ_lt_axi_s_bvalid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bvalid),
  .i_apu_targ_lt_axi_s_araddr (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_araddr),
  .i_apu_targ_lt_axi_s_arid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arid),
  .i_apu_targ_lt_axi_s_arlen (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arlen),
  .i_apu_targ_lt_axi_s_arsize (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arsize),
  .i_apu_targ_lt_axi_s_arburst (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arburst),
  .i_apu_targ_lt_axi_s_arcache (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arcache),
  .i_apu_targ_lt_axi_s_arprot (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arprot),
  .i_apu_targ_lt_axi_s_arqos (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arqos),
  .i_apu_targ_lt_axi_s_arregion ('0),
  .i_apu_targ_lt_axi_s_aruser ('0),
  .i_apu_targ_lt_axi_s_arlock (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arlock),
  .o_apu_targ_lt_axi_s_arready (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_arready),
  .i_apu_targ_lt_axi_s_arvalid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arvalid),
  .o_apu_targ_lt_axi_s_rlast (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rlast),
  .o_apu_targ_lt_axi_s_rid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rid),
  .o_apu_targ_lt_axi_s_rdata (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rdata),
  .o_apu_targ_lt_axi_s_rresp (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rresp),
  .o_apu_targ_lt_axi_s_ruser (),
  .i_apu_targ_lt_axi_s_rready (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_rready),
  .o_apu_targ_lt_axi_s_rvalid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rvalid),
  .o_apu_init_mt_axi_m_awaddr (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awaddr),
  .o_apu_init_mt_axi_m_awid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awid),
  .o_apu_init_mt_axi_m_awlen (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awlen),
  .o_apu_init_mt_axi_m_awsize (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awsize),
  .o_apu_init_mt_axi_m_awburst (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awburst),
  .o_apu_init_mt_axi_m_awcache (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awcache),
  .o_apu_init_mt_axi_m_awprot (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awprot),
  .o_apu_init_mt_axi_m_awlock (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awlock),
  .o_apu_init_mt_axi_m_awqos (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awqos),
  .o_apu_init_mt_axi_m_awregion (),
  .o_apu_init_mt_axi_m_awuser (),
  .i_apu_init_mt_axi_m_awready (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_awready),
  .o_apu_init_mt_axi_m_awvalid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awvalid),
  .o_apu_init_mt_axi_m_wlast (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wlast),
  .o_apu_init_mt_axi_m_wstrb (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wstrb),
  .o_apu_init_mt_axi_m_wdata (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wdata),
  .o_apu_init_mt_axi_m_wuser (),
  .i_apu_init_mt_axi_m_wready (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_wready),
  .o_apu_init_mt_axi_m_wvalid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wvalid),
  .i_apu_init_mt_axi_m_bid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bid),
  .i_apu_init_mt_axi_m_bresp (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bresp),
  .i_apu_init_mt_axi_m_buser ('0),
  .o_apu_init_mt_axi_m_bready (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_bready),
  .i_apu_init_mt_axi_m_bvalid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bvalid),
  .o_apu_init_mt_axi_m_araddr (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_araddr),
  .o_apu_init_mt_axi_m_arid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arid),
  .o_apu_init_mt_axi_m_arlen (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arlen),
  .o_apu_init_mt_axi_m_arsize (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arsize),
  .o_apu_init_mt_axi_m_arburst (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arburst),
  .o_apu_init_mt_axi_m_arcache (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arcache),
  .o_apu_init_mt_axi_m_arprot (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arprot),
  .o_apu_init_mt_axi_m_arqos (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arqos),
  .o_apu_init_mt_axi_m_arregion (),
  .o_apu_init_mt_axi_m_aruser (),
  .o_apu_init_mt_axi_m_arlock (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arlock),
  .i_apu_init_mt_axi_m_arready (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_arready),
  .o_apu_init_mt_axi_m_arvalid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arvalid),
  .i_apu_init_mt_axi_m_rlast (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rlast),
  .i_apu_init_mt_axi_m_rid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rid),
  .i_apu_init_mt_axi_m_rdata (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rdata),
  .i_apu_init_mt_axi_m_rresp (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rresp),
  .i_apu_init_mt_axi_m_ruser ('0),
  .o_apu_init_mt_axi_m_rready (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_rready),
  .i_apu_init_mt_axi_m_rvalid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rvalid),
  .o_tok_prod_ocpl_m_maddr (u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mdata (u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_tok_prod_ocpl_m_mcmd (u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_tok_prod_ocpl_m_scmdaccept (u_noc_top_to_u_apu_p__o_apu_init_tok_ocpl_s_scmdaccept),
  .i_tok_cons_ocpl_s_maddr (u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_maddr),
  .i_tok_cons_ocpl_s_mdata (u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_mdata),
  .i_tok_cons_ocpl_s_mcmd (u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_mcmd),
  .o_tok_cons_ocpl_s_scmdaccept (u_apu_p_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .io_ibias_ts (u_apu_p_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_apu_p_to_u_soc_mgmt_p__io_vsense_ts),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef DCD_P_STUB
dcd_p_stub u_dcd_p (
`else
dcd_p u_dcd_p (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .i_mcu_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_jtag_clk (i_tck),
  .i_jtag_rst_n (i_trst_n),
  .i_jtag_ms ('0),
  .i_jtag_di ('0),
  .o_jtag_do (),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_dcd_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_dcd_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_dcd_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_pintreq (u_dcd_p_to_u_apu_p__o_pintreq),
  .o_dec_0_axi_m_awaddr (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awaddr),
  .o_dec_0_axi_m_awid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awid),
  .o_dec_0_axi_m_awlen (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awlen),
  .o_dec_0_axi_m_awsize (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awsize),
  .o_dec_0_axi_m_awburst (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awburst),
  .o_dec_0_axi_m_awcache (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awcache),
  .o_dec_0_axi_m_awprot (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awprot),
  .o_dec_0_axi_m_awlock (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awlock),
  .o_dec_0_axi_m_awqos (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awqos),
  .o_dec_0_axi_m_awregion (),
  .o_dec_0_axi_m_awuser (),
  .o_dec_0_axi_m_awvalid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awvalid),
  .o_dec_0_axi_m_wdata (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wdata),
  .o_dec_0_axi_m_wstrb (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wstrb),
  .o_dec_0_axi_m_wlast (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wlast),
  .o_dec_0_axi_m_wuser (),
  .o_dec_0_axi_m_wvalid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wvalid),
  .o_dec_0_axi_m_bready (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_bready),
  .o_dec_0_axi_m_araddr (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_araddr),
  .o_dec_0_axi_m_arid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arid),
  .o_dec_0_axi_m_arlen (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arlen),
  .o_dec_0_axi_m_arsize (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arsize),
  .o_dec_0_axi_m_arburst (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arburst),
  .o_dec_0_axi_m_arcache (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arcache),
  .o_dec_0_axi_m_arprot (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arprot),
  .o_dec_0_axi_m_arqos (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arqos),
  .o_dec_0_axi_m_arregion (),
  .o_dec_0_axi_m_aruser (),
  .o_dec_0_axi_m_arlock (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arlock),
  .o_dec_0_axi_m_arvalid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arvalid),
  .o_dec_0_axi_m_rready (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_rready),
  .i_dec_0_axi_m_awready (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_awready),
  .i_dec_0_axi_m_wready (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_wready),
  .i_dec_0_axi_m_bvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bvalid),
  .i_dec_0_axi_m_bid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bid),
  .i_dec_0_axi_m_buser ('0),
  .i_dec_0_axi_m_bresp (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bresp),
  .i_dec_0_axi_m_arready (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_arready),
  .i_dec_0_axi_m_rvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rvalid),
  .i_dec_0_axi_m_rlast (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rlast),
  .i_dec_0_axi_m_rid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rid),
  .i_dec_0_axi_m_rdata (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rdata),
  .i_dec_0_axi_m_ruser ('0),
  .i_dec_0_axi_m_rresp (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rresp),
  .o_dec_1_axi_m_awaddr (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awaddr),
  .o_dec_1_axi_m_awid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awid),
  .o_dec_1_axi_m_awlen (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awlen),
  .o_dec_1_axi_m_awsize (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awsize),
  .o_dec_1_axi_m_awburst (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awburst),
  .o_dec_1_axi_m_awcache (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awcache),
  .o_dec_1_axi_m_awprot (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awprot),
  .o_dec_1_axi_m_awlock (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awlock),
  .o_dec_1_axi_m_awqos (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awqos),
  .o_dec_1_axi_m_awregion (),
  .o_dec_1_axi_m_awuser (),
  .o_dec_1_axi_m_awvalid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awvalid),
  .o_dec_1_axi_m_wdata (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wdata),
  .o_dec_1_axi_m_wstrb (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wstrb),
  .o_dec_1_axi_m_wlast (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wlast),
  .o_dec_1_axi_m_wuser (),
  .o_dec_1_axi_m_wvalid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wvalid),
  .o_dec_1_axi_m_bready (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_bready),
  .o_dec_1_axi_m_araddr (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_araddr),
  .o_dec_1_axi_m_arid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arid),
  .o_dec_1_axi_m_arlen (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arlen),
  .o_dec_1_axi_m_arsize (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arsize),
  .o_dec_1_axi_m_arburst (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arburst),
  .o_dec_1_axi_m_arcache (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arcache),
  .o_dec_1_axi_m_arprot (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arprot),
  .o_dec_1_axi_m_arqos (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arqos),
  .o_dec_1_axi_m_arregion (),
  .o_dec_1_axi_m_aruser (),
  .o_dec_1_axi_m_arlock (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arlock),
  .o_dec_1_axi_m_arvalid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arvalid),
  .o_dec_1_axi_m_rready (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_rready),
  .i_dec_1_axi_m_awready (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_awready),
  .i_dec_1_axi_m_wready (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_wready),
  .i_dec_1_axi_m_bvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bvalid),
  .i_dec_1_axi_m_bid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bid),
  .i_dec_1_axi_m_buser ('0),
  .i_dec_1_axi_m_bresp (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bresp),
  .i_dec_1_axi_m_arready (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_arready),
  .i_dec_1_axi_m_rvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rvalid),
  .i_dec_1_axi_m_rlast (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rlast),
  .i_dec_1_axi_m_rid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rid),
  .i_dec_1_axi_m_rdata (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rdata),
  .i_dec_1_axi_m_ruser ('0),
  .i_dec_1_axi_m_rresp (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rresp),
  .o_dec_2_axi_m_awaddr (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awaddr),
  .o_dec_2_axi_m_awid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awid),
  .o_dec_2_axi_m_awlen (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awlen),
  .o_dec_2_axi_m_awsize (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awsize),
  .o_dec_2_axi_m_awburst (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awburst),
  .o_dec_2_axi_m_awcache (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awcache),
  .o_dec_2_axi_m_awprot (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awprot),
  .o_dec_2_axi_m_awlock (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awlock),
  .o_dec_2_axi_m_awqos (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awqos),
  .o_dec_2_axi_m_awregion (),
  .o_dec_2_axi_m_awuser (),
  .o_dec_2_axi_m_awvalid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awvalid),
  .o_dec_2_axi_m_wdata (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wdata),
  .o_dec_2_axi_m_wstrb (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wstrb),
  .o_dec_2_axi_m_wlast (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wlast),
  .o_dec_2_axi_m_wuser (),
  .o_dec_2_axi_m_wvalid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wvalid),
  .o_dec_2_axi_m_bready (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_bready),
  .o_dec_2_axi_m_araddr (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_araddr),
  .o_dec_2_axi_m_arid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arid),
  .o_dec_2_axi_m_arlen (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arlen),
  .o_dec_2_axi_m_arsize (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arsize),
  .o_dec_2_axi_m_arburst (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arburst),
  .o_dec_2_axi_m_arcache (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arcache),
  .o_dec_2_axi_m_arprot (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arprot),
  .o_dec_2_axi_m_arqos (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arqos),
  .o_dec_2_axi_m_arregion (),
  .o_dec_2_axi_m_aruser (),
  .o_dec_2_axi_m_arlock (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arlock),
  .o_dec_2_axi_m_arvalid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arvalid),
  .o_dec_2_axi_m_rready (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_rready),
  .i_dec_2_axi_m_awready (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_awready),
  .i_dec_2_axi_m_wready (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_wready),
  .i_dec_2_axi_m_bvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bvalid),
  .i_dec_2_axi_m_bid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bid),
  .i_dec_2_axi_m_buser ('0),
  .i_dec_2_axi_m_bresp (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bresp),
  .i_dec_2_axi_m_arready (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_arready),
  .i_dec_2_axi_m_rvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rvalid),
  .i_dec_2_axi_m_rlast (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rlast),
  .i_dec_2_axi_m_rid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rid),
  .i_dec_2_axi_m_rdata (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rdata),
  .i_dec_2_axi_m_ruser ('0),
  .i_dec_2_axi_m_rresp (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rresp),
  .o_mcu_axi_m_awaddr (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awaddr),
  .o_mcu_axi_m_awid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awid),
  .o_mcu_axi_m_awlen (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awlen),
  .o_mcu_axi_m_awsize (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awsize),
  .o_mcu_axi_m_awburst (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awburst),
  .o_mcu_axi_m_awcache (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awcache),
  .o_mcu_axi_m_awprot (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awprot),
  .o_mcu_axi_m_awlock (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awlock),
  .o_mcu_axi_m_awqos (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awqos),
  .o_mcu_axi_m_awregion (),
  .o_mcu_axi_m_awuser (),
  .o_mcu_axi_m_awvalid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awvalid),
  .o_mcu_axi_m_wdata (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wdata),
  .o_mcu_axi_m_wstrb (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wstrb),
  .o_mcu_axi_m_wlast (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wlast),
  .o_mcu_axi_m_wuser (),
  .o_mcu_axi_m_wvalid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wvalid),
  .o_mcu_axi_m_bready (u_dcd_p_to_u_noc_top__o_mcu_axi_m_bready),
  .o_mcu_axi_m_araddr (u_dcd_p_to_u_noc_top__o_mcu_axi_m_araddr),
  .o_mcu_axi_m_arid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arid),
  .o_mcu_axi_m_arlen (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arlen),
  .o_mcu_axi_m_arsize (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arsize),
  .o_mcu_axi_m_arburst (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arburst),
  .o_mcu_axi_m_arcache (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arcache),
  .o_mcu_axi_m_arprot (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arprot),
  .o_mcu_axi_m_arqos (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arqos),
  .o_mcu_axi_m_arregion (),
  .o_mcu_axi_m_aruser (),
  .o_mcu_axi_m_arlock (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arlock),
  .o_mcu_axi_m_arvalid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arvalid),
  .o_mcu_axi_m_rready (u_dcd_p_to_u_noc_top__o_mcu_axi_m_rready),
  .i_mcu_axi_m_awready (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_awready),
  .i_mcu_axi_m_wready (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_wready),
  .i_mcu_axi_m_bvalid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bvalid),
  .i_mcu_axi_m_bid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bid),
  .i_mcu_axi_m_buser ('0),
  .i_mcu_axi_m_bresp (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bresp),
  .i_mcu_axi_m_arready (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_arready),
  .i_mcu_axi_m_rvalid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rvalid),
  .i_mcu_axi_m_rlast (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rlast),
  .i_mcu_axi_m_rid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rid),
  .i_mcu_axi_m_rdata (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rdata),
  .i_mcu_axi_m_ruser ('0),
  .i_mcu_axi_m_rresp (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rresp),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_dcd_p_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_dcd_p__o_dcd_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_dcd_p__o_dcd_pwr_idle_val),
  .o_noc_mcu_async_idle_req (u_dcd_p_to_u_noc_top__o_noc_mcu_async_idle_req),
  .i_noc_mcu_async_idle_ack (u_noc_top_to_u_dcd_p__o_dcd_mcu_pwr_idle_ack),
  .i_noc_mcu_async_idle_val (u_noc_top_to_u_dcd_p__o_dcd_mcu_pwr_idle_val),
  .o_noc_clk_en (u_dcd_p_to_u_noc_top__o_noc_clk_en),
  .o_noc_mcu_clk_en (u_dcd_p_to_u_noc_top__o_noc_mcu_clk_en),
  .i_syscfg_apb4_s_paddr (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_paddr),
  .i_syscfg_apb4_s_pwdata (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pwdata),
  .i_syscfg_apb4_s_pwrite (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pwrite),
  .i_syscfg_apb4_s_psel (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_psel),
  .i_syscfg_apb4_s_penable (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_penable),
  .i_syscfg_apb4_s_pstrb (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pstrb),
  .i_syscfg_apb4_s_pprot (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pprot),
  .o_syscfg_apb4_s_pready (u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_pready),
  .o_syscfg_apb4_s_prdata (u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_prdata),
  .o_syscfg_apb4_s_pslverr (u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_pslverr),
  .o_noc_rst_n (u_dcd_p_to_u_noc_top__o_noc_rst_n),
  .o_noc_mcu_rst_n (u_dcd_p_to_u_noc_top__o_noc_mcu_rst_n),
  .o_dcd_obs (u_dcd_p_to_u_soc_mgmt_p__o_dcd_obs),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef DDR_WEST_CLOCK_GEN_P_STUB
ddr_west_clock_gen_p_stub u_ddr_west_clock_gen_p (
`else
ddr_west_clock_gen_p u_ddr_west_clock_gen_p (
`endif
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ddr_west_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_ddr_west_clkgen_obs (u_ddr_west_clock_gen_p_to_u_soc_mgmt_p__o_ddr_west_clkgen_obs),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_0_STUB
l2_p_stub u_l2_p_0 (
`else
l2_p u_l2_p_0 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_0_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_0_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_0__o_l2_0_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_0__o_l2_0_pwr_idle_val),
  .o_noc_clken (u_l2_p_0_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_0_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_0_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_0_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_0_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_1_STUB
l2_p_stub u_l2_p_1 (
`else
l2_p u_l2_p_1 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_1_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_1_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_1__o_l2_1_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_1__o_l2_1_pwr_idle_val),
  .o_noc_clken (u_l2_p_1_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_1_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_1_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_1_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_1_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_2_STUB
l2_p_stub u_l2_p_2 (
`else
l2_p u_l2_p_2 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_2_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_2_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_2__o_l2_2_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_2__o_l2_2_pwr_idle_val),
  .o_noc_clken (u_l2_p_2_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_2_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_2_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_2_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_2_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_3_STUB
l2_p_stub u_l2_p_3 (
`else
l2_p u_l2_p_3 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_3_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_3_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_3__o_l2_3_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_3__o_l2_3_pwr_idle_val),
  .o_noc_clken (u_l2_p_3_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_3_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_3_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_3_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_3_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_4_STUB
l2_p_stub u_l2_p_4 (
`else
l2_p u_l2_p_4 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_4_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_4_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_4__o_l2_4_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_4__o_l2_4_pwr_idle_val),
  .o_noc_clken (u_l2_p_4_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_4_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_4_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_4_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_4_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_5_STUB
l2_p_stub u_l2_p_5 (
`else
l2_p u_l2_p_5 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_5_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_5_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_5__o_l2_5_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_5__o_l2_5_pwr_idle_val),
  .o_noc_clken (u_l2_p_5_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_5_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_5_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_5_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_5_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_6_STUB
l2_p_stub u_l2_p_6 (
`else
l2_p u_l2_p_6 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_6_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_6_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_6__o_l2_6_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_6__o_l2_6_pwr_idle_val),
  .o_noc_clken (u_l2_p_6_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_6_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_6_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_6_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_6_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef L2_P_7_STUB
l2_p_stub u_l2_p_7 (
`else
l2_p u_l2_p_7 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_l2_p_7_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_l2_p_7_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_l2_p_7__o_l2_7_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_l2_p_7__o_l2_7_pwr_idle_val),
  .o_noc_clken (u_l2_p_7_to_u_noc_top__o_noc_clken),
  .i_ht_axi_s_awaddr (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awaddr),
  .i_ht_axi_s_awid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awid),
  .i_ht_axi_s_awlen (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awlen),
  .i_ht_axi_s_awsize (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awsize),
  .i_ht_axi_s_awburst (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awburst),
  .i_ht_axi_s_awcache (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awcache),
  .i_ht_axi_s_awprot (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awprot),
  .i_ht_axi_s_awlock (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awlock),
  .i_ht_axi_s_awqos ('0),
  .i_ht_axi_s_awregion ('0),
  .i_ht_axi_s_awuser ('0),
  .i_ht_axi_s_awvalid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awvalid),
  .o_ht_axi_s_awready (u_l2_p_7_to_u_noc_top__o_ht_axi_s_awready),
  .i_ht_axi_s_wdata (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wdata),
  .i_ht_axi_s_wstrb (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wstrb),
  .i_ht_axi_s_wlast (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wlast),
  .i_ht_axi_s_wuser ('0),
  .i_ht_axi_s_wvalid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wvalid),
  .o_ht_axi_s_wready (u_l2_p_7_to_u_noc_top__o_ht_axi_s_wready),
  .o_ht_axi_s_bvalid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_ht_axi_s_bid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_bid),
  .o_ht_axi_s_buser (),
  .o_ht_axi_s_bresp (u_l2_p_7_to_u_noc_top__o_ht_axi_s_bresp),
  .i_ht_axi_s_bready (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_bready),
  .i_ht_axi_s_araddr (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_araddr),
  .i_ht_axi_s_arid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arid),
  .i_ht_axi_s_arlen (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arlen),
  .i_ht_axi_s_arsize (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arsize),
  .i_ht_axi_s_arburst (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arburst),
  .i_ht_axi_s_arcache (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arcache),
  .i_ht_axi_s_arprot (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arprot),
  .i_ht_axi_s_arqos ('0),
  .i_ht_axi_s_arregion ('0),
  .i_ht_axi_s_aruser ('0),
  .i_ht_axi_s_arlock (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arlock),
  .i_ht_axi_s_arvalid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arvalid),
  .o_ht_axi_s_arready (u_l2_p_7_to_u_noc_top__o_ht_axi_s_arready),
  .o_ht_axi_s_rvalid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_ht_axi_s_rlast (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rlast),
  .o_ht_axi_s_rid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rid),
  .o_ht_axi_s_rdata (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rdata),
  .o_ht_axi_s_ruser (),
  .o_ht_axi_s_rresp (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rresp),
  .i_ht_axi_s_rready (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef LPDDR_P_GRAPH_0_STUB
lpddr_p_stub u_lpddr_p_graph_0 (
`else
lpddr_p u_lpddr_p_graph_0 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_graph_0_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_graph_0_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_graph_0_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_graph_0_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_graph_0_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_graph_0_bp_memreset_l),
  .BP_A (io_lpddr_graph_0_bp_a),
  .BP_ATO (io_lpddr_graph_0_bp_ato),
  .BP_ATO_PLL (io_lpddr_graph_0_bp_ato_pll),
  .BP_B0_D (io_lpddr_graph_0_bp_b0_d),
  .BP_B1_D (io_lpddr_graph_0_bp_b1_d),
  .BP_B2_D (io_lpddr_graph_0_bp_b2_d),
  .BP_B3_D (io_lpddr_graph_0_bp_b3_d),
  .BP_CK0_C (io_lpddr_graph_0_bp_ck0_c),
  .BP_CK0_T (io_lpddr_graph_0_bp_ck0_t),
  .BP_CK1_C (io_lpddr_graph_0_bp_ck1_c),
  .BP_CK1_T (io_lpddr_graph_0_bp_ck1_t),
  .BP_ZN (io_lpddr_graph_0_bp_zn)
);
`ifdef LPDDR_P_GRAPH_1_STUB
lpddr_p_stub u_lpddr_p_graph_1 (
`else
lpddr_p u_lpddr_p_graph_1 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_graph_1_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_graph_1_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_graph_1_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_graph_1_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_graph_1_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_graph_1_bp_memreset_l),
  .BP_A (io_lpddr_graph_1_bp_a),
  .BP_ATO (io_lpddr_graph_1_bp_ato),
  .BP_ATO_PLL (io_lpddr_graph_1_bp_ato_pll),
  .BP_B0_D (io_lpddr_graph_1_bp_b0_d),
  .BP_B1_D (io_lpddr_graph_1_bp_b1_d),
  .BP_B2_D (io_lpddr_graph_1_bp_b2_d),
  .BP_B3_D (io_lpddr_graph_1_bp_b3_d),
  .BP_CK0_C (io_lpddr_graph_1_bp_ck0_c),
  .BP_CK0_T (io_lpddr_graph_1_bp_ck0_t),
  .BP_CK1_C (io_lpddr_graph_1_bp_ck1_c),
  .BP_CK1_T (io_lpddr_graph_1_bp_ck1_t),
  .BP_ZN (io_lpddr_graph_1_bp_zn)
);
`ifdef LPDDR_P_GRAPH_2_STUB
lpddr_p_stub u_lpddr_p_graph_2 (
`else
lpddr_p u_lpddr_p_graph_2 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_graph_2_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_graph_2_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_graph_2_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_graph_2_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_graph_2_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_graph_2_bp_memreset_l),
  .BP_A (io_lpddr_graph_2_bp_a),
  .BP_ATO (io_lpddr_graph_2_bp_ato),
  .BP_ATO_PLL (io_lpddr_graph_2_bp_ato_pll),
  .BP_B0_D (io_lpddr_graph_2_bp_b0_d),
  .BP_B1_D (io_lpddr_graph_2_bp_b1_d),
  .BP_B2_D (io_lpddr_graph_2_bp_b2_d),
  .BP_B3_D (io_lpddr_graph_2_bp_b3_d),
  .BP_CK0_C (io_lpddr_graph_2_bp_ck0_c),
  .BP_CK0_T (io_lpddr_graph_2_bp_ck0_t),
  .BP_CK1_C (io_lpddr_graph_2_bp_ck1_c),
  .BP_CK1_T (io_lpddr_graph_2_bp_ck1_t),
  .BP_ZN (io_lpddr_graph_2_bp_zn)
);
`ifdef LPDDR_P_GRAPH_3_STUB
lpddr_p_stub u_lpddr_p_graph_3 (
`else
lpddr_p u_lpddr_p_graph_3 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_graph_3_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_graph_3_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_graph_3_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_graph_3_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_graph_3_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_graph_3_bp_memreset_l),
  .BP_A (io_lpddr_graph_3_bp_a),
  .BP_ATO (io_lpddr_graph_3_bp_ato),
  .BP_ATO_PLL (io_lpddr_graph_3_bp_ato_pll),
  .BP_B0_D (io_lpddr_graph_3_bp_b0_d),
  .BP_B1_D (io_lpddr_graph_3_bp_b1_d),
  .BP_B2_D (io_lpddr_graph_3_bp_b2_d),
  .BP_B3_D (io_lpddr_graph_3_bp_b3_d),
  .BP_CK0_C (io_lpddr_graph_3_bp_ck0_c),
  .BP_CK0_T (io_lpddr_graph_3_bp_ck0_t),
  .BP_CK1_C (io_lpddr_graph_3_bp_ck1_c),
  .BP_CK1_T (io_lpddr_graph_3_bp_ck1_t),
  .BP_ZN (io_lpddr_graph_3_bp_zn)
);
`ifdef LPDDR_P_PPP_0_STUB
lpddr_p_stub u_lpddr_p_ppp_0 (
`else
lpddr_p u_lpddr_p_ppp_0 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_ppp_0_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_ppp_0_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_ppp_0_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_ppp_0_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_ppp_0_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_ppp_0_bp_memreset_l),
  .BP_A (io_lpddr_ppp_0_bp_a),
  .BP_ATO (io_lpddr_ppp_0_bp_ato),
  .BP_ATO_PLL (io_lpddr_ppp_0_bp_ato_pll),
  .BP_B0_D (io_lpddr_ppp_0_bp_b0_d),
  .BP_B1_D (io_lpddr_ppp_0_bp_b1_d),
  .BP_B2_D (io_lpddr_ppp_0_bp_b2_d),
  .BP_B3_D (io_lpddr_ppp_0_bp_b3_d),
  .BP_CK0_C (io_lpddr_ppp_0_bp_ck0_c),
  .BP_CK0_T (io_lpddr_ppp_0_bp_ck0_t),
  .BP_CK1_C (io_lpddr_ppp_0_bp_ck1_c),
  .BP_CK1_T (io_lpddr_ppp_0_bp_ck1_t),
  .BP_ZN (io_lpddr_ppp_0_bp_zn)
);
`ifdef LPDDR_P_PPP_1_STUB
lpddr_p_stub u_lpddr_p_ppp_1 (
`else
lpddr_p u_lpddr_p_ppp_1 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_ppp_1_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_ppp_1_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_ppp_1_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_ppp_1_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_ppp_1_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_ppp_1_bp_memreset_l),
  .BP_A (io_lpddr_ppp_1_bp_a),
  .BP_ATO (io_lpddr_ppp_1_bp_ato),
  .BP_ATO_PLL (io_lpddr_ppp_1_bp_ato_pll),
  .BP_B0_D (io_lpddr_ppp_1_bp_b0_d),
  .BP_B1_D (io_lpddr_ppp_1_bp_b1_d),
  .BP_B2_D (io_lpddr_ppp_1_bp_b2_d),
  .BP_B3_D (io_lpddr_ppp_1_bp_b3_d),
  .BP_CK0_C (io_lpddr_ppp_1_bp_ck0_c),
  .BP_CK0_T (io_lpddr_ppp_1_bp_ck0_t),
  .BP_CK1_C (io_lpddr_ppp_1_bp_ck1_c),
  .BP_CK1_T (io_lpddr_ppp_1_bp_ck1_t),
  .BP_ZN (io_lpddr_ppp_1_bp_zn)
);
`ifdef LPDDR_P_PPP_2_STUB
lpddr_p_stub u_lpddr_p_ppp_2 (
`else
lpddr_p u_lpddr_p_ppp_2 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_ppp_2_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_ppp_2_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_ppp_2_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_ppp_2_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_ppp_2_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_ppp_2_bp_memreset_l),
  .BP_A (io_lpddr_ppp_2_bp_a),
  .BP_ATO (io_lpddr_ppp_2_bp_ato),
  .BP_ATO_PLL (io_lpddr_ppp_2_bp_ato_pll),
  .BP_B0_D (io_lpddr_ppp_2_bp_b0_d),
  .BP_B1_D (io_lpddr_ppp_2_bp_b1_d),
  .BP_B2_D (io_lpddr_ppp_2_bp_b2_d),
  .BP_B3_D (io_lpddr_ppp_2_bp_b3_d),
  .BP_CK0_C (io_lpddr_ppp_2_bp_ck0_c),
  .BP_CK0_T (io_lpddr_ppp_2_bp_ck0_t),
  .BP_CK1_C (io_lpddr_ppp_2_bp_ck1_c),
  .BP_CK1_T (io_lpddr_ppp_2_bp_ck1_t),
  .BP_ZN (io_lpddr_ppp_2_bp_zn)
);
`ifdef LPDDR_P_PPP_3_STUB
lpddr_p_stub u_lpddr_p_ppp_3 (
`else
lpddr_p u_lpddr_p_ppp_3 (
`endif
  .i_ao_clk (i_ref_clk),
  .i_lpddr_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_ao_rst_sync_n (),
  .o_noc_async_idle_req (u_lpddr_p_ppp_3_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_pwr_idle_vec_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_pwr_idle_vec_val),
  .o_noc_clken (u_lpddr_p_ppp_3_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_lpddr_p_ppp_3_to_u_noc_top__o_noc_rst_n),
  .i_lpddr_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_araddr),
  .i_lpddr_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arburst),
  .i_lpddr_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arcache),
  .i_lpddr_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arid),
  .i_lpddr_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arlen),
  .i_lpddr_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arlock),
  .i_lpddr_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arprot),
  .i_lpddr_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arqos),
  .i_lpddr_axi_m_arregion ('0),
  .i_lpddr_axi_m_aruser ('0),
  .i_lpddr_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arsize),
  .i_lpddr_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arvalid),
  .i_lpddr_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_rready),
  .i_lpddr_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awaddr),
  .i_lpddr_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awburst),
  .i_lpddr_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awcache),
  .i_lpddr_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awid),
  .i_lpddr_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awlen),
  .i_lpddr_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awlock),
  .i_lpddr_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awprot),
  .i_lpddr_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awqos),
  .i_lpddr_axi_m_awregion ('0),
  .i_lpddr_axi_m_awuser ('0),
  .i_lpddr_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awsize),
  .i_lpddr_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awvalid),
  .i_lpddr_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wdata),
  .i_lpddr_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wlast),
  .i_lpddr_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wstrb),
  .i_lpddr_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wvalid),
  .i_lpddr_axi_m_wuser ('0),
  .i_lpddr_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_bready),
  .o_lpddr_axi_m_arready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_axi_m_rdata (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rdata),
  .o_lpddr_axi_m_rid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rid),
  .o_lpddr_axi_m_rlast (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_axi_m_ruser (),
  .o_lpddr_axi_m_rresp (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rresp),
  .o_lpddr_axi_m_rvalid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_axi_m_awready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_axi_m_wready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_axi_m_bid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_axi_m_bresp (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bresp),
  .o_lpddr_axi_m_bvalid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .o_lpddr_axi_m_buser (),
  .i_lpddr_cfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_paddr),
  .i_lpddr_cfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_penable),
  .i_lpddr_cfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pprot),
  .i_lpddr_cfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_psel),
  .i_lpddr_cfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pstrb),
  .i_lpddr_cfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pwdata),
  .i_lpddr_cfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pwrite),
  .o_lpddr_cfg_apb4_s_prdata (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .o_lpddr_cfg_apb4_s_pready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_cfg_apb4_s_pslverr (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .i_lpddr_syscfg_apb4_s_paddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_paddr),
  .i_lpddr_syscfg_apb4_s_pwdata (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pwdata),
  .i_lpddr_syscfg_apb4_s_pwrite (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pwrite),
  .i_lpddr_syscfg_apb4_s_psel (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_psel),
  .i_lpddr_syscfg_apb4_s_penable (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_penable),
  .i_lpddr_syscfg_apb4_s_pstrb (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pstrb),
  .i_lpddr_syscfg_apb4_s_pprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pprot),
  .o_lpddr_syscfg_apb4_s_pready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_syscfg_apb4_s_prdata (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .o_lpddr_syscfg_apb4_s_pslverr (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_ctrl_sbr_done_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_sbr_done_intr),
  .o_ctrl_derate_temp_limit_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_derate_temp_limit_intr),
  .o_ctrl_ecc_ap_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_ap_err_intr),
  .o_ctrl_ecc_corrected_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_corrected_err_intr),
  .o_ctrl_ecc_uncorrected_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_ecc_uncorrected_err_intr),
  .o_ctrl_rd_linkecc_corr_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_rd_linkecc_corr_err_intr),
  .o_ctrl_rd_linkecc_uncorr_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_ctrl_rd_linkecc_uncorr_err_intr),
  .o_phy_pie_prog_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_pie_prog_err_intr),
  .o_phy_ecc_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_ecc_err_intr),
  .o_phy_rdfptrchk_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_rdfptrchk_err_intr),
  .o_phy_pie_parity_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_pie_parity_err_intr),
  .o_phy_acsm_parity_err_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_acsm_parity_err_intr),
  .o_phy_trng_fail_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_trng_fail_intr),
  .o_phy_init_cmplt_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_init_cmplt_intr),
  .o_phy_trng_cmplt_intr (u_lpddr_p_ppp_3_to_u_apu_p__o_phy_trng_cmplt_intr),
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_lpddr_obs (u_lpddr_p_ppp_3_to_u_soc_mgmt_p__o_lpddr_obs),
  .BP_MEMRESET_L (o_lpddr_ppp_3_bp_memreset_l),
  .BP_A (io_lpddr_ppp_3_bp_a),
  .BP_ATO (io_lpddr_ppp_3_bp_ato),
  .BP_ATO_PLL (io_lpddr_ppp_3_bp_ato_pll),
  .BP_B0_D (io_lpddr_ppp_3_bp_b0_d),
  .BP_B1_D (io_lpddr_ppp_3_bp_b1_d),
  .BP_B2_D (io_lpddr_ppp_3_bp_b2_d),
  .BP_B3_D (io_lpddr_ppp_3_bp_b3_d),
  .BP_CK0_C (io_lpddr_ppp_3_bp_ck0_c),
  .BP_CK0_T (io_lpddr_ppp_3_bp_ck0_t),
  .BP_CK1_C (io_lpddr_ppp_3_bp_ck1_c),
  .BP_CK1_T (io_lpddr_ppp_3_bp_ck1_t),
  .BP_ZN (io_lpddr_ppp_3_bp_zn)
);
`ifdef NOC_TOP_STUB
noc_top_stub u_noc_top (
`else
noc_top u_noc_top (
`endif
  .i_ref_clk (i_ref_clk),
  .test_mode ('0),
  .scan_en ('0),
  .i_sdma_0_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_sdma_0_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_sdma_0_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_sdma_0_int ({
  u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_3,
  u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_2,
  u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_1,
  u_noc_top_to_u_apu_p__o_sdma_0_int__i_irq__noc__sdma_0_int_0}),
  .i_sdma_0_clock_throttle (u_soc_mgmt_p_to_u_noc_top__o_clock_throttle_11),
  .i_sdma_1_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_sdma_1_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_sdma_1_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_sdma_1_int ({
  u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_3,
  u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_2,
  u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_1,
  u_noc_top_to_u_apu_p__o_sdma_1_int__i_irq__noc__sdma_1_int_0}),
  .i_sdma_1_clock_throttle (u_soc_mgmt_p_to_u_noc_top__o_clock_throttle_12),
  .i_sdma_inter_core_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .o_obs (u_noc_top_to_u_soc_mgmt_p__o_obs),
  .o_irq (u_noc_top_to_u_apu_p__o_irq),
  .i_aic_0_aon_clk (i_ref_clk),
  .i_aic_0_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_0_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_0_clken (u_ai_core_p_0_to_u_noc_top__o_noc_clken),
  .i_aic_0_init_ht_axi_s_araddr (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_0_init_ht_axi_s_arburst (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_0_init_ht_axi_s_arcache (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_0_init_ht_axi_s_arid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_0_init_ht_axi_s_arlen (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_0_init_ht_axi_s_arlock (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_0_init_ht_axi_s_arprot (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_0_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_arready),
  .i_aic_0_init_ht_axi_s_arsize (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_0_init_ht_axi_s_arvalid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_0_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rdata),
  .o_aic_0_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rid),
  .o_aic_0_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rlast),
  .i_aic_0_init_ht_axi_s_rready (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_0_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rresp),
  .o_aic_0_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_rvalid),
  .i_aic_0_init_ht_axi_s_awaddr (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_0_init_ht_axi_s_awburst (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_0_init_ht_axi_s_awcache (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_0_init_ht_axi_s_awid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_0_init_ht_axi_s_awlen (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_0_init_ht_axi_s_awlock (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_0_init_ht_axi_s_awprot (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_0_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_awready),
  .i_aic_0_init_ht_axi_s_awsize (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_0_init_ht_axi_s_awvalid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_0_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bid),
  .i_aic_0_init_ht_axi_s_bready (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_0_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bresp),
  .o_aic_0_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_bvalid),
  .i_aic_0_init_ht_axi_s_wdata (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_0_init_ht_axi_s_wlast (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_0_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_ht_axi_s_wready),
  .i_aic_0_init_ht_axi_s_wstrb (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_0_init_ht_axi_s_wvalid (u_ai_core_p_0_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_0_init_lt_axi_s_araddr (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_0_init_lt_axi_s_arburst (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_0_init_lt_axi_s_arcache (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_0_init_lt_axi_s_arid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_0_init_lt_axi_s_arlen (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_0_init_lt_axi_s_arlock (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_0_init_lt_axi_s_arprot (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_0_init_lt_axi_s_arqos ('0),
  .o_aic_0_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_arready),
  .i_aic_0_init_lt_axi_s_arsize (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_0_init_lt_axi_s_arvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_0_init_lt_axi_s_awaddr (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_0_init_lt_axi_s_awburst (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_0_init_lt_axi_s_awcache (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_0_init_lt_axi_s_awid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_0_init_lt_axi_s_awlen (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_0_init_lt_axi_s_awlock (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_0_init_lt_axi_s_awprot (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_0_init_lt_axi_s_awqos ('0),
  .o_aic_0_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_awready),
  .i_aic_0_init_lt_axi_s_awsize (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_0_init_lt_axi_s_awvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_0_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bid),
  .i_aic_0_init_lt_axi_s_bready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_0_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bresp),
  .o_aic_0_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_bvalid),
  .o_aic_0_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rdata),
  .o_aic_0_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rid),
  .o_aic_0_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rlast),
  .i_aic_0_init_lt_axi_s_rready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_0_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rresp),
  .o_aic_0_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_rvalid),
  .i_aic_0_init_lt_axi_s_wdata (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_0_init_lt_axi_s_wlast (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_0_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_lt_axi_s_wready),
  .i_aic_0_init_lt_axi_s_wstrb (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_0_init_lt_axi_s_wvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_0_pwr_idle_val (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_idle_val),
  .o_aic_0_pwr_idle_ack (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_idle_ack),
  .i_aic_0_pwr_idle_req (u_ai_core_p_0_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_0_rst_n (u_ai_core_p_0_to_u_noc_top__o_noc_rst_n),
  .o_aic_0_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_araddr),
  .o_aic_0_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arburst),
  .o_aic_0_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arcache),
  .o_aic_0_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arid),
  .o_aic_0_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arlen),
  .o_aic_0_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arlock),
  .o_aic_0_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arprot),
  .o_aic_0_targ_lt_axi_m_arqos (),
  .i_aic_0_targ_lt_axi_m_arready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_0_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arsize),
  .o_aic_0_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_arvalid),
  .o_aic_0_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awaddr),
  .o_aic_0_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awburst),
  .o_aic_0_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awcache),
  .o_aic_0_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awid),
  .o_aic_0_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awlen),
  .o_aic_0_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awlock),
  .o_aic_0_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awprot),
  .o_aic_0_targ_lt_axi_m_awqos (),
  .i_aic_0_targ_lt_axi_m_awready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_0_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awsize),
  .o_aic_0_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_awvalid),
  .i_aic_0_targ_lt_axi_m_bid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_0_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_bready),
  .i_aic_0_targ_lt_axi_m_bresp (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_0_targ_lt_axi_m_bvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_0_targ_lt_axi_m_rdata (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_0_targ_lt_axi_m_rid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_0_targ_lt_axi_m_rlast (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_0_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_rready),
  .i_aic_0_targ_lt_axi_m_rresp (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_0_targ_lt_axi_m_rvalid (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_0_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wdata),
  .o_aic_0_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wlast),
  .i_aic_0_targ_lt_axi_m_wready (u_ai_core_p_0_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_0_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wstrb),
  .o_aic_0_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_lt_axi_m_wvalid),
  .o_aic_0_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_paddr),
  .o_aic_0_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_penable),
  .o_aic_0_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pprot),
  .i_aic_0_targ_syscfg_apb_m_prdata (u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_0_targ_syscfg_apb_m_pready (u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_0_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_psel),
  .i_aic_0_targ_syscfg_apb_m_pslverr (u_ai_core_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_0_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pstrb),
  .o_aic_0_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pwdata),
  .o_aic_0_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_syscfg_apb_m_pwrite),
  .o_aic_0_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_tok_idle_val),
  .o_aic_0_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_0__o_aic_0_pwr_tok_idle_ack),
  .i_aic_0_pwr_tok_idle_req (u_ai_core_p_0_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_0_init_tok_ocpl_s_maddr (u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_0_init_tok_ocpl_s_mcmd (u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_0_init_tok_ocpl_s_mdata (u_ai_core_p_0_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_0_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_0__o_aic_0_init_tok_ocpl_s_scmdaccept),
  .o_aic_0_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_maddr),
  .o_aic_0_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_mcmd),
  .o_aic_0_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_0__o_aic_0_targ_tok_ocpl_m_mdata),
  .i_aic_0_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_0_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_1_aon_clk (i_ref_clk),
  .i_aic_1_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_1_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_1_clken (u_ai_core_p_1_to_u_noc_top__o_noc_clken),
  .i_aic_1_init_ht_axi_s_araddr (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_1_init_ht_axi_s_arburst (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_1_init_ht_axi_s_arcache (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_1_init_ht_axi_s_arid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_1_init_ht_axi_s_arlen (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_1_init_ht_axi_s_arlock (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_1_init_ht_axi_s_arprot (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_1_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_arready),
  .i_aic_1_init_ht_axi_s_arsize (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_1_init_ht_axi_s_arvalid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_1_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rdata),
  .o_aic_1_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rid),
  .o_aic_1_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rlast),
  .i_aic_1_init_ht_axi_s_rready (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_1_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rresp),
  .o_aic_1_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_rvalid),
  .i_aic_1_init_ht_axi_s_awaddr (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_1_init_ht_axi_s_awburst (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_1_init_ht_axi_s_awcache (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_1_init_ht_axi_s_awid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_1_init_ht_axi_s_awlen (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_1_init_ht_axi_s_awlock (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_1_init_ht_axi_s_awprot (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_1_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_awready),
  .i_aic_1_init_ht_axi_s_awsize (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_1_init_ht_axi_s_awvalid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_1_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bid),
  .i_aic_1_init_ht_axi_s_bready (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_1_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bresp),
  .o_aic_1_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_bvalid),
  .i_aic_1_init_ht_axi_s_wdata (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_1_init_ht_axi_s_wlast (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_1_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_ht_axi_s_wready),
  .i_aic_1_init_ht_axi_s_wstrb (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_1_init_ht_axi_s_wvalid (u_ai_core_p_1_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_1_init_lt_axi_s_araddr (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_1_init_lt_axi_s_arburst (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_1_init_lt_axi_s_arcache (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_1_init_lt_axi_s_arid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_1_init_lt_axi_s_arlen (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_1_init_lt_axi_s_arlock (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_1_init_lt_axi_s_arprot (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_1_init_lt_axi_s_arqos ('0),
  .o_aic_1_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_arready),
  .i_aic_1_init_lt_axi_s_arsize (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_1_init_lt_axi_s_arvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_1_init_lt_axi_s_awaddr (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_1_init_lt_axi_s_awburst (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_1_init_lt_axi_s_awcache (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_1_init_lt_axi_s_awid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_1_init_lt_axi_s_awlen (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_1_init_lt_axi_s_awlock (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_1_init_lt_axi_s_awprot (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_1_init_lt_axi_s_awqos ('0),
  .o_aic_1_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_awready),
  .i_aic_1_init_lt_axi_s_awsize (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_1_init_lt_axi_s_awvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_1_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bid),
  .i_aic_1_init_lt_axi_s_bready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_1_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bresp),
  .o_aic_1_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_bvalid),
  .o_aic_1_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rdata),
  .o_aic_1_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rid),
  .o_aic_1_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rlast),
  .i_aic_1_init_lt_axi_s_rready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_1_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rresp),
  .o_aic_1_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_rvalid),
  .i_aic_1_init_lt_axi_s_wdata (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_1_init_lt_axi_s_wlast (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_1_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_lt_axi_s_wready),
  .i_aic_1_init_lt_axi_s_wstrb (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_1_init_lt_axi_s_wvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_1_pwr_idle_val (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_idle_val),
  .o_aic_1_pwr_idle_ack (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_idle_ack),
  .i_aic_1_pwr_idle_req (u_ai_core_p_1_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_1_rst_n (u_ai_core_p_1_to_u_noc_top__o_noc_rst_n),
  .o_aic_1_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_araddr),
  .o_aic_1_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arburst),
  .o_aic_1_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arcache),
  .o_aic_1_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arid),
  .o_aic_1_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arlen),
  .o_aic_1_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arlock),
  .o_aic_1_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arprot),
  .o_aic_1_targ_lt_axi_m_arqos (),
  .i_aic_1_targ_lt_axi_m_arready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_1_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arsize),
  .o_aic_1_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_arvalid),
  .o_aic_1_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awaddr),
  .o_aic_1_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awburst),
  .o_aic_1_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awcache),
  .o_aic_1_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awid),
  .o_aic_1_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awlen),
  .o_aic_1_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awlock),
  .o_aic_1_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awprot),
  .o_aic_1_targ_lt_axi_m_awqos (),
  .i_aic_1_targ_lt_axi_m_awready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_1_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awsize),
  .o_aic_1_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_awvalid),
  .i_aic_1_targ_lt_axi_m_bid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_1_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_bready),
  .i_aic_1_targ_lt_axi_m_bresp (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_1_targ_lt_axi_m_bvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_1_targ_lt_axi_m_rdata (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_1_targ_lt_axi_m_rid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_1_targ_lt_axi_m_rlast (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_1_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_rready),
  .i_aic_1_targ_lt_axi_m_rresp (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_1_targ_lt_axi_m_rvalid (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_1_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wdata),
  .o_aic_1_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wlast),
  .i_aic_1_targ_lt_axi_m_wready (u_ai_core_p_1_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_1_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wstrb),
  .o_aic_1_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_lt_axi_m_wvalid),
  .o_aic_1_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_paddr),
  .o_aic_1_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_penable),
  .o_aic_1_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pprot),
  .i_aic_1_targ_syscfg_apb_m_prdata (u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_1_targ_syscfg_apb_m_pready (u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_1_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_psel),
  .i_aic_1_targ_syscfg_apb_m_pslverr (u_ai_core_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_1_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pstrb),
  .o_aic_1_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pwdata),
  .o_aic_1_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_syscfg_apb_m_pwrite),
  .o_aic_1_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_tok_idle_val),
  .o_aic_1_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_1__o_aic_1_pwr_tok_idle_ack),
  .i_aic_1_pwr_tok_idle_req (u_ai_core_p_1_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_1_init_tok_ocpl_s_maddr (u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_1_init_tok_ocpl_s_mcmd (u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_1_init_tok_ocpl_s_mdata (u_ai_core_p_1_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_1_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_1__o_aic_1_init_tok_ocpl_s_scmdaccept),
  .o_aic_1_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_maddr),
  .o_aic_1_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_mcmd),
  .o_aic_1_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_1__o_aic_1_targ_tok_ocpl_m_mdata),
  .i_aic_1_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_1_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_2_aon_clk (i_ref_clk),
  .i_aic_2_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_2_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_2_clken (u_ai_core_p_2_to_u_noc_top__o_noc_clken),
  .i_aic_2_init_ht_axi_s_araddr (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_2_init_ht_axi_s_arburst (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_2_init_ht_axi_s_arcache (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_2_init_ht_axi_s_arid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_2_init_ht_axi_s_arlen (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_2_init_ht_axi_s_arlock (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_2_init_ht_axi_s_arprot (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_2_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_arready),
  .i_aic_2_init_ht_axi_s_arsize (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_2_init_ht_axi_s_arvalid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_2_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rdata),
  .o_aic_2_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rid),
  .o_aic_2_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rlast),
  .i_aic_2_init_ht_axi_s_rready (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_2_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rresp),
  .o_aic_2_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_rvalid),
  .i_aic_2_init_ht_axi_s_awaddr (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_2_init_ht_axi_s_awburst (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_2_init_ht_axi_s_awcache (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_2_init_ht_axi_s_awid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_2_init_ht_axi_s_awlen (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_2_init_ht_axi_s_awlock (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_2_init_ht_axi_s_awprot (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_2_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_awready),
  .i_aic_2_init_ht_axi_s_awsize (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_2_init_ht_axi_s_awvalid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_2_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bid),
  .i_aic_2_init_ht_axi_s_bready (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_2_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bresp),
  .o_aic_2_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_bvalid),
  .i_aic_2_init_ht_axi_s_wdata (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_2_init_ht_axi_s_wlast (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_2_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_ht_axi_s_wready),
  .i_aic_2_init_ht_axi_s_wstrb (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_2_init_ht_axi_s_wvalid (u_ai_core_p_2_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_2_init_lt_axi_s_araddr (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_2_init_lt_axi_s_arburst (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_2_init_lt_axi_s_arcache (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_2_init_lt_axi_s_arid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_2_init_lt_axi_s_arlen (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_2_init_lt_axi_s_arlock (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_2_init_lt_axi_s_arprot (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_2_init_lt_axi_s_arqos ('0),
  .o_aic_2_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_arready),
  .i_aic_2_init_lt_axi_s_arsize (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_2_init_lt_axi_s_arvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_2_init_lt_axi_s_awaddr (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_2_init_lt_axi_s_awburst (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_2_init_lt_axi_s_awcache (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_2_init_lt_axi_s_awid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_2_init_lt_axi_s_awlen (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_2_init_lt_axi_s_awlock (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_2_init_lt_axi_s_awprot (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_2_init_lt_axi_s_awqos ('0),
  .o_aic_2_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_awready),
  .i_aic_2_init_lt_axi_s_awsize (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_2_init_lt_axi_s_awvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_2_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bid),
  .i_aic_2_init_lt_axi_s_bready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_2_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bresp),
  .o_aic_2_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_bvalid),
  .o_aic_2_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rdata),
  .o_aic_2_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rid),
  .o_aic_2_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rlast),
  .i_aic_2_init_lt_axi_s_rready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_2_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rresp),
  .o_aic_2_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_rvalid),
  .i_aic_2_init_lt_axi_s_wdata (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_2_init_lt_axi_s_wlast (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_2_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_lt_axi_s_wready),
  .i_aic_2_init_lt_axi_s_wstrb (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_2_init_lt_axi_s_wvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_2_pwr_idle_val (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_idle_val),
  .o_aic_2_pwr_idle_ack (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_idle_ack),
  .i_aic_2_pwr_idle_req (u_ai_core_p_2_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_2_rst_n (u_ai_core_p_2_to_u_noc_top__o_noc_rst_n),
  .o_aic_2_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_araddr),
  .o_aic_2_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arburst),
  .o_aic_2_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arcache),
  .o_aic_2_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arid),
  .o_aic_2_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arlen),
  .o_aic_2_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arlock),
  .o_aic_2_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arprot),
  .o_aic_2_targ_lt_axi_m_arqos (),
  .i_aic_2_targ_lt_axi_m_arready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_2_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arsize),
  .o_aic_2_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_arvalid),
  .o_aic_2_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awaddr),
  .o_aic_2_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awburst),
  .o_aic_2_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awcache),
  .o_aic_2_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awid),
  .o_aic_2_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awlen),
  .o_aic_2_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awlock),
  .o_aic_2_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awprot),
  .o_aic_2_targ_lt_axi_m_awqos (),
  .i_aic_2_targ_lt_axi_m_awready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_2_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awsize),
  .o_aic_2_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_awvalid),
  .i_aic_2_targ_lt_axi_m_bid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_2_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_bready),
  .i_aic_2_targ_lt_axi_m_bresp (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_2_targ_lt_axi_m_bvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_2_targ_lt_axi_m_rdata (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_2_targ_lt_axi_m_rid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_2_targ_lt_axi_m_rlast (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_2_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_rready),
  .i_aic_2_targ_lt_axi_m_rresp (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_2_targ_lt_axi_m_rvalid (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_2_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wdata),
  .o_aic_2_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wlast),
  .i_aic_2_targ_lt_axi_m_wready (u_ai_core_p_2_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_2_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wstrb),
  .o_aic_2_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_lt_axi_m_wvalid),
  .o_aic_2_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_paddr),
  .o_aic_2_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_penable),
  .o_aic_2_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pprot),
  .i_aic_2_targ_syscfg_apb_m_prdata (u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_2_targ_syscfg_apb_m_pready (u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_2_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_psel),
  .i_aic_2_targ_syscfg_apb_m_pslverr (u_ai_core_p_2_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_2_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pstrb),
  .o_aic_2_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pwdata),
  .o_aic_2_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_syscfg_apb_m_pwrite),
  .o_aic_2_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_tok_idle_val),
  .o_aic_2_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_2__o_aic_2_pwr_tok_idle_ack),
  .i_aic_2_pwr_tok_idle_req (u_ai_core_p_2_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_2_init_tok_ocpl_s_maddr (u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_2_init_tok_ocpl_s_mcmd (u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_2_init_tok_ocpl_s_mdata (u_ai_core_p_2_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_2_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_2__o_aic_2_init_tok_ocpl_s_scmdaccept),
  .o_aic_2_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_maddr),
  .o_aic_2_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_mcmd),
  .o_aic_2_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_2__o_aic_2_targ_tok_ocpl_m_mdata),
  .i_aic_2_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_2_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_3_aon_clk (i_ref_clk),
  .i_aic_3_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_3_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_3_clken (u_ai_core_p_3_to_u_noc_top__o_noc_clken),
  .i_aic_3_init_ht_axi_s_araddr (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_3_init_ht_axi_s_arburst (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_3_init_ht_axi_s_arcache (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_3_init_ht_axi_s_arid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_3_init_ht_axi_s_arlen (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_3_init_ht_axi_s_arlock (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_3_init_ht_axi_s_arprot (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_3_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_arready),
  .i_aic_3_init_ht_axi_s_arsize (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_3_init_ht_axi_s_arvalid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_3_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rdata),
  .o_aic_3_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rid),
  .o_aic_3_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rlast),
  .i_aic_3_init_ht_axi_s_rready (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_3_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rresp),
  .o_aic_3_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_rvalid),
  .i_aic_3_init_ht_axi_s_awaddr (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_3_init_ht_axi_s_awburst (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_3_init_ht_axi_s_awcache (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_3_init_ht_axi_s_awid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_3_init_ht_axi_s_awlen (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_3_init_ht_axi_s_awlock (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_3_init_ht_axi_s_awprot (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_3_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_awready),
  .i_aic_3_init_ht_axi_s_awsize (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_3_init_ht_axi_s_awvalid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_3_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bid),
  .i_aic_3_init_ht_axi_s_bready (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_3_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bresp),
  .o_aic_3_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_bvalid),
  .i_aic_3_init_ht_axi_s_wdata (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_3_init_ht_axi_s_wlast (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_3_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_ht_axi_s_wready),
  .i_aic_3_init_ht_axi_s_wstrb (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_3_init_ht_axi_s_wvalid (u_ai_core_p_3_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_3_init_lt_axi_s_araddr (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_3_init_lt_axi_s_arburst (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_3_init_lt_axi_s_arcache (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_3_init_lt_axi_s_arid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_3_init_lt_axi_s_arlen (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_3_init_lt_axi_s_arlock (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_3_init_lt_axi_s_arprot (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_3_init_lt_axi_s_arqos ('0),
  .o_aic_3_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_arready),
  .i_aic_3_init_lt_axi_s_arsize (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_3_init_lt_axi_s_arvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_3_init_lt_axi_s_awaddr (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_3_init_lt_axi_s_awburst (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_3_init_lt_axi_s_awcache (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_3_init_lt_axi_s_awid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_3_init_lt_axi_s_awlen (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_3_init_lt_axi_s_awlock (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_3_init_lt_axi_s_awprot (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_3_init_lt_axi_s_awqos ('0),
  .o_aic_3_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_awready),
  .i_aic_3_init_lt_axi_s_awsize (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_3_init_lt_axi_s_awvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_3_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bid),
  .i_aic_3_init_lt_axi_s_bready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_3_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bresp),
  .o_aic_3_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_bvalid),
  .o_aic_3_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rdata),
  .o_aic_3_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rid),
  .o_aic_3_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rlast),
  .i_aic_3_init_lt_axi_s_rready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_3_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rresp),
  .o_aic_3_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_rvalid),
  .i_aic_3_init_lt_axi_s_wdata (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_3_init_lt_axi_s_wlast (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_3_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_lt_axi_s_wready),
  .i_aic_3_init_lt_axi_s_wstrb (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_3_init_lt_axi_s_wvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_3_pwr_idle_val (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_idle_val),
  .o_aic_3_pwr_idle_ack (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_idle_ack),
  .i_aic_3_pwr_idle_req (u_ai_core_p_3_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_3_rst_n (u_ai_core_p_3_to_u_noc_top__o_noc_rst_n),
  .o_aic_3_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_araddr),
  .o_aic_3_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arburst),
  .o_aic_3_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arcache),
  .o_aic_3_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arid),
  .o_aic_3_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arlen),
  .o_aic_3_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arlock),
  .o_aic_3_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arprot),
  .o_aic_3_targ_lt_axi_m_arqos (),
  .i_aic_3_targ_lt_axi_m_arready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_3_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arsize),
  .o_aic_3_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_arvalid),
  .o_aic_3_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awaddr),
  .o_aic_3_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awburst),
  .o_aic_3_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awcache),
  .o_aic_3_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awid),
  .o_aic_3_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awlen),
  .o_aic_3_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awlock),
  .o_aic_3_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awprot),
  .o_aic_3_targ_lt_axi_m_awqos (),
  .i_aic_3_targ_lt_axi_m_awready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_3_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awsize),
  .o_aic_3_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_awvalid),
  .i_aic_3_targ_lt_axi_m_bid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_3_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_bready),
  .i_aic_3_targ_lt_axi_m_bresp (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_3_targ_lt_axi_m_bvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_3_targ_lt_axi_m_rdata (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_3_targ_lt_axi_m_rid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_3_targ_lt_axi_m_rlast (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_3_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_rready),
  .i_aic_3_targ_lt_axi_m_rresp (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_3_targ_lt_axi_m_rvalid (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_3_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wdata),
  .o_aic_3_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wlast),
  .i_aic_3_targ_lt_axi_m_wready (u_ai_core_p_3_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_3_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wstrb),
  .o_aic_3_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_lt_axi_m_wvalid),
  .o_aic_3_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_paddr),
  .o_aic_3_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_penable),
  .o_aic_3_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pprot),
  .i_aic_3_targ_syscfg_apb_m_prdata (u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_3_targ_syscfg_apb_m_pready (u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_3_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_psel),
  .i_aic_3_targ_syscfg_apb_m_pslverr (u_ai_core_p_3_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_3_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pstrb),
  .o_aic_3_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pwdata),
  .o_aic_3_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_syscfg_apb_m_pwrite),
  .o_aic_3_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_tok_idle_val),
  .o_aic_3_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_3__o_aic_3_pwr_tok_idle_ack),
  .i_aic_3_pwr_tok_idle_req (u_ai_core_p_3_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_3_init_tok_ocpl_s_maddr (u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_3_init_tok_ocpl_s_mcmd (u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_3_init_tok_ocpl_s_mdata (u_ai_core_p_3_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_3_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_3__o_aic_3_init_tok_ocpl_s_scmdaccept),
  .o_aic_3_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_maddr),
  .o_aic_3_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_mcmd),
  .o_aic_3_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_3__o_aic_3_targ_tok_ocpl_m_mdata),
  .i_aic_3_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_3_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_4_aon_clk (i_ref_clk),
  .i_aic_4_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_4_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_4_clken (u_ai_core_p_4_to_u_noc_top__o_noc_clken),
  .i_aic_4_init_ht_axi_s_araddr (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_4_init_ht_axi_s_arburst (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_4_init_ht_axi_s_arcache (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_4_init_ht_axi_s_arid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_4_init_ht_axi_s_arlen (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_4_init_ht_axi_s_arlock (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_4_init_ht_axi_s_arprot (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_4_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_arready),
  .i_aic_4_init_ht_axi_s_arsize (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_4_init_ht_axi_s_arvalid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_4_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rdata),
  .o_aic_4_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rid),
  .o_aic_4_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rlast),
  .i_aic_4_init_ht_axi_s_rready (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_4_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rresp),
  .o_aic_4_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_rvalid),
  .i_aic_4_init_ht_axi_s_awaddr (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_4_init_ht_axi_s_awburst (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_4_init_ht_axi_s_awcache (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_4_init_ht_axi_s_awid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_4_init_ht_axi_s_awlen (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_4_init_ht_axi_s_awlock (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_4_init_ht_axi_s_awprot (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_4_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_awready),
  .i_aic_4_init_ht_axi_s_awsize (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_4_init_ht_axi_s_awvalid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_4_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bid),
  .i_aic_4_init_ht_axi_s_bready (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_4_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bresp),
  .o_aic_4_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_bvalid),
  .i_aic_4_init_ht_axi_s_wdata (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_4_init_ht_axi_s_wlast (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_4_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_ht_axi_s_wready),
  .i_aic_4_init_ht_axi_s_wstrb (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_4_init_ht_axi_s_wvalid (u_ai_core_p_4_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_4_init_lt_axi_s_araddr (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_4_init_lt_axi_s_arburst (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_4_init_lt_axi_s_arcache (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_4_init_lt_axi_s_arid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_4_init_lt_axi_s_arlen (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_4_init_lt_axi_s_arlock (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_4_init_lt_axi_s_arprot (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_4_init_lt_axi_s_arqos ('0),
  .o_aic_4_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_arready),
  .i_aic_4_init_lt_axi_s_arsize (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_4_init_lt_axi_s_arvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_4_init_lt_axi_s_awaddr (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_4_init_lt_axi_s_awburst (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_4_init_lt_axi_s_awcache (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_4_init_lt_axi_s_awid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_4_init_lt_axi_s_awlen (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_4_init_lt_axi_s_awlock (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_4_init_lt_axi_s_awprot (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_4_init_lt_axi_s_awqos ('0),
  .o_aic_4_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_awready),
  .i_aic_4_init_lt_axi_s_awsize (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_4_init_lt_axi_s_awvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_4_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bid),
  .i_aic_4_init_lt_axi_s_bready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_4_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bresp),
  .o_aic_4_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_bvalid),
  .o_aic_4_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rdata),
  .o_aic_4_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rid),
  .o_aic_4_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rlast),
  .i_aic_4_init_lt_axi_s_rready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_4_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rresp),
  .o_aic_4_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_rvalid),
  .i_aic_4_init_lt_axi_s_wdata (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_4_init_lt_axi_s_wlast (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_4_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_lt_axi_s_wready),
  .i_aic_4_init_lt_axi_s_wstrb (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_4_init_lt_axi_s_wvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_4_pwr_idle_val (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_idle_val),
  .o_aic_4_pwr_idle_ack (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_idle_ack),
  .i_aic_4_pwr_idle_req (u_ai_core_p_4_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_4_rst_n (u_ai_core_p_4_to_u_noc_top__o_noc_rst_n),
  .o_aic_4_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_araddr),
  .o_aic_4_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arburst),
  .o_aic_4_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arcache),
  .o_aic_4_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arid),
  .o_aic_4_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arlen),
  .o_aic_4_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arlock),
  .o_aic_4_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arprot),
  .o_aic_4_targ_lt_axi_m_arqos (),
  .i_aic_4_targ_lt_axi_m_arready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_4_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arsize),
  .o_aic_4_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_arvalid),
  .o_aic_4_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awaddr),
  .o_aic_4_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awburst),
  .o_aic_4_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awcache),
  .o_aic_4_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awid),
  .o_aic_4_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awlen),
  .o_aic_4_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awlock),
  .o_aic_4_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awprot),
  .o_aic_4_targ_lt_axi_m_awqos (),
  .i_aic_4_targ_lt_axi_m_awready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_4_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awsize),
  .o_aic_4_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_awvalid),
  .i_aic_4_targ_lt_axi_m_bid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_4_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_bready),
  .i_aic_4_targ_lt_axi_m_bresp (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_4_targ_lt_axi_m_bvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_4_targ_lt_axi_m_rdata (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_4_targ_lt_axi_m_rid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_4_targ_lt_axi_m_rlast (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_4_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_rready),
  .i_aic_4_targ_lt_axi_m_rresp (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_4_targ_lt_axi_m_rvalid (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_4_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wdata),
  .o_aic_4_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wlast),
  .i_aic_4_targ_lt_axi_m_wready (u_ai_core_p_4_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_4_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wstrb),
  .o_aic_4_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_lt_axi_m_wvalid),
  .o_aic_4_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_paddr),
  .o_aic_4_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_penable),
  .o_aic_4_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pprot),
  .i_aic_4_targ_syscfg_apb_m_prdata (u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_4_targ_syscfg_apb_m_pready (u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_4_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_psel),
  .i_aic_4_targ_syscfg_apb_m_pslverr (u_ai_core_p_4_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_4_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pstrb),
  .o_aic_4_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pwdata),
  .o_aic_4_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_syscfg_apb_m_pwrite),
  .o_aic_4_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_tok_idle_val),
  .o_aic_4_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_4__o_aic_4_pwr_tok_idle_ack),
  .i_aic_4_pwr_tok_idle_req (u_ai_core_p_4_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_4_init_tok_ocpl_s_maddr (u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_4_init_tok_ocpl_s_mcmd (u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_4_init_tok_ocpl_s_mdata (u_ai_core_p_4_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_4_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_4__o_aic_4_init_tok_ocpl_s_scmdaccept),
  .o_aic_4_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_maddr),
  .o_aic_4_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_mcmd),
  .o_aic_4_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_4__o_aic_4_targ_tok_ocpl_m_mdata),
  .i_aic_4_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_4_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_5_aon_clk (i_ref_clk),
  .i_aic_5_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_5_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_5_clken (u_ai_core_p_5_to_u_noc_top__o_noc_clken),
  .i_aic_5_init_ht_axi_s_araddr (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_5_init_ht_axi_s_arburst (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_5_init_ht_axi_s_arcache (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_5_init_ht_axi_s_arid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_5_init_ht_axi_s_arlen (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_5_init_ht_axi_s_arlock (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_5_init_ht_axi_s_arprot (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_5_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_arready),
  .i_aic_5_init_ht_axi_s_arsize (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_5_init_ht_axi_s_arvalid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_5_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rdata),
  .o_aic_5_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rid),
  .o_aic_5_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rlast),
  .i_aic_5_init_ht_axi_s_rready (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_5_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rresp),
  .o_aic_5_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_rvalid),
  .i_aic_5_init_ht_axi_s_awaddr (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_5_init_ht_axi_s_awburst (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_5_init_ht_axi_s_awcache (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_5_init_ht_axi_s_awid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_5_init_ht_axi_s_awlen (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_5_init_ht_axi_s_awlock (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_5_init_ht_axi_s_awprot (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_5_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_awready),
  .i_aic_5_init_ht_axi_s_awsize (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_5_init_ht_axi_s_awvalid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_5_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bid),
  .i_aic_5_init_ht_axi_s_bready (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_5_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bresp),
  .o_aic_5_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_bvalid),
  .i_aic_5_init_ht_axi_s_wdata (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_5_init_ht_axi_s_wlast (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_5_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_ht_axi_s_wready),
  .i_aic_5_init_ht_axi_s_wstrb (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_5_init_ht_axi_s_wvalid (u_ai_core_p_5_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_5_init_lt_axi_s_araddr (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_5_init_lt_axi_s_arburst (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_5_init_lt_axi_s_arcache (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_5_init_lt_axi_s_arid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_5_init_lt_axi_s_arlen (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_5_init_lt_axi_s_arlock (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_5_init_lt_axi_s_arprot (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_5_init_lt_axi_s_arqos ('0),
  .o_aic_5_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_arready),
  .i_aic_5_init_lt_axi_s_arsize (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_5_init_lt_axi_s_arvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_5_init_lt_axi_s_awaddr (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_5_init_lt_axi_s_awburst (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_5_init_lt_axi_s_awcache (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_5_init_lt_axi_s_awid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_5_init_lt_axi_s_awlen (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_5_init_lt_axi_s_awlock (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_5_init_lt_axi_s_awprot (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_5_init_lt_axi_s_awqos ('0),
  .o_aic_5_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_awready),
  .i_aic_5_init_lt_axi_s_awsize (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_5_init_lt_axi_s_awvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_5_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bid),
  .i_aic_5_init_lt_axi_s_bready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_5_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bresp),
  .o_aic_5_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_bvalid),
  .o_aic_5_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rdata),
  .o_aic_5_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rid),
  .o_aic_5_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rlast),
  .i_aic_5_init_lt_axi_s_rready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_5_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rresp),
  .o_aic_5_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_rvalid),
  .i_aic_5_init_lt_axi_s_wdata (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_5_init_lt_axi_s_wlast (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_5_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_lt_axi_s_wready),
  .i_aic_5_init_lt_axi_s_wstrb (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_5_init_lt_axi_s_wvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_5_pwr_idle_val (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_idle_val),
  .o_aic_5_pwr_idle_ack (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_idle_ack),
  .i_aic_5_pwr_idle_req (u_ai_core_p_5_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_5_rst_n (u_ai_core_p_5_to_u_noc_top__o_noc_rst_n),
  .o_aic_5_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_araddr),
  .o_aic_5_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arburst),
  .o_aic_5_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arcache),
  .o_aic_5_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arid),
  .o_aic_5_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arlen),
  .o_aic_5_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arlock),
  .o_aic_5_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arprot),
  .o_aic_5_targ_lt_axi_m_arqos (),
  .i_aic_5_targ_lt_axi_m_arready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_5_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arsize),
  .o_aic_5_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_arvalid),
  .o_aic_5_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awaddr),
  .o_aic_5_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awburst),
  .o_aic_5_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awcache),
  .o_aic_5_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awid),
  .o_aic_5_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awlen),
  .o_aic_5_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awlock),
  .o_aic_5_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awprot),
  .o_aic_5_targ_lt_axi_m_awqos (),
  .i_aic_5_targ_lt_axi_m_awready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_5_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awsize),
  .o_aic_5_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_awvalid),
  .i_aic_5_targ_lt_axi_m_bid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_5_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_bready),
  .i_aic_5_targ_lt_axi_m_bresp (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_5_targ_lt_axi_m_bvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_5_targ_lt_axi_m_rdata (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_5_targ_lt_axi_m_rid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_5_targ_lt_axi_m_rlast (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_5_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_rready),
  .i_aic_5_targ_lt_axi_m_rresp (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_5_targ_lt_axi_m_rvalid (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_5_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wdata),
  .o_aic_5_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wlast),
  .i_aic_5_targ_lt_axi_m_wready (u_ai_core_p_5_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_5_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wstrb),
  .o_aic_5_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_lt_axi_m_wvalid),
  .o_aic_5_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_paddr),
  .o_aic_5_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_penable),
  .o_aic_5_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pprot),
  .i_aic_5_targ_syscfg_apb_m_prdata (u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_5_targ_syscfg_apb_m_pready (u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_5_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_psel),
  .i_aic_5_targ_syscfg_apb_m_pslverr (u_ai_core_p_5_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_5_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pstrb),
  .o_aic_5_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pwdata),
  .o_aic_5_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_syscfg_apb_m_pwrite),
  .o_aic_5_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_tok_idle_val),
  .o_aic_5_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_5__o_aic_5_pwr_tok_idle_ack),
  .i_aic_5_pwr_tok_idle_req (u_ai_core_p_5_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_5_init_tok_ocpl_s_maddr (u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_5_init_tok_ocpl_s_mcmd (u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_5_init_tok_ocpl_s_mdata (u_ai_core_p_5_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_5_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_5__o_aic_5_init_tok_ocpl_s_scmdaccept),
  .o_aic_5_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_maddr),
  .o_aic_5_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_mcmd),
  .o_aic_5_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_5__o_aic_5_targ_tok_ocpl_m_mdata),
  .i_aic_5_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_5_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_6_aon_clk (i_ref_clk),
  .i_aic_6_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_6_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_6_clken (u_ai_core_p_6_to_u_noc_top__o_noc_clken),
  .i_aic_6_init_ht_axi_s_araddr (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_6_init_ht_axi_s_arburst (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_6_init_ht_axi_s_arcache (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_6_init_ht_axi_s_arid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_6_init_ht_axi_s_arlen (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_6_init_ht_axi_s_arlock (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_6_init_ht_axi_s_arprot (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_6_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_arready),
  .i_aic_6_init_ht_axi_s_arsize (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_6_init_ht_axi_s_arvalid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_6_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rdata),
  .o_aic_6_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rid),
  .o_aic_6_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rlast),
  .i_aic_6_init_ht_axi_s_rready (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_6_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rresp),
  .o_aic_6_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_rvalid),
  .i_aic_6_init_ht_axi_s_awaddr (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_6_init_ht_axi_s_awburst (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_6_init_ht_axi_s_awcache (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_6_init_ht_axi_s_awid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_6_init_ht_axi_s_awlen (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_6_init_ht_axi_s_awlock (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_6_init_ht_axi_s_awprot (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_6_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_awready),
  .i_aic_6_init_ht_axi_s_awsize (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_6_init_ht_axi_s_awvalid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_6_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bid),
  .i_aic_6_init_ht_axi_s_bready (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_6_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bresp),
  .o_aic_6_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_bvalid),
  .i_aic_6_init_ht_axi_s_wdata (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_6_init_ht_axi_s_wlast (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_6_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_ht_axi_s_wready),
  .i_aic_6_init_ht_axi_s_wstrb (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_6_init_ht_axi_s_wvalid (u_ai_core_p_6_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_6_init_lt_axi_s_araddr (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_6_init_lt_axi_s_arburst (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_6_init_lt_axi_s_arcache (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_6_init_lt_axi_s_arid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_6_init_lt_axi_s_arlen (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_6_init_lt_axi_s_arlock (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_6_init_lt_axi_s_arprot (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_6_init_lt_axi_s_arqos ('0),
  .o_aic_6_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_arready),
  .i_aic_6_init_lt_axi_s_arsize (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_6_init_lt_axi_s_arvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_6_init_lt_axi_s_awaddr (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_6_init_lt_axi_s_awburst (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_6_init_lt_axi_s_awcache (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_6_init_lt_axi_s_awid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_6_init_lt_axi_s_awlen (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_6_init_lt_axi_s_awlock (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_6_init_lt_axi_s_awprot (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_6_init_lt_axi_s_awqos ('0),
  .o_aic_6_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_awready),
  .i_aic_6_init_lt_axi_s_awsize (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_6_init_lt_axi_s_awvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_6_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bid),
  .i_aic_6_init_lt_axi_s_bready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_6_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bresp),
  .o_aic_6_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_bvalid),
  .o_aic_6_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rdata),
  .o_aic_6_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rid),
  .o_aic_6_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rlast),
  .i_aic_6_init_lt_axi_s_rready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_6_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rresp),
  .o_aic_6_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_rvalid),
  .i_aic_6_init_lt_axi_s_wdata (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_6_init_lt_axi_s_wlast (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_6_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_lt_axi_s_wready),
  .i_aic_6_init_lt_axi_s_wstrb (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_6_init_lt_axi_s_wvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_6_pwr_idle_val (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_idle_val),
  .o_aic_6_pwr_idle_ack (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_idle_ack),
  .i_aic_6_pwr_idle_req (u_ai_core_p_6_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_6_rst_n (u_ai_core_p_6_to_u_noc_top__o_noc_rst_n),
  .o_aic_6_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_araddr),
  .o_aic_6_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arburst),
  .o_aic_6_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arcache),
  .o_aic_6_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arid),
  .o_aic_6_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arlen),
  .o_aic_6_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arlock),
  .o_aic_6_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arprot),
  .o_aic_6_targ_lt_axi_m_arqos (),
  .i_aic_6_targ_lt_axi_m_arready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_6_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arsize),
  .o_aic_6_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_arvalid),
  .o_aic_6_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awaddr),
  .o_aic_6_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awburst),
  .o_aic_6_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awcache),
  .o_aic_6_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awid),
  .o_aic_6_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awlen),
  .o_aic_6_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awlock),
  .o_aic_6_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awprot),
  .o_aic_6_targ_lt_axi_m_awqos (),
  .i_aic_6_targ_lt_axi_m_awready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_6_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awsize),
  .o_aic_6_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_awvalid),
  .i_aic_6_targ_lt_axi_m_bid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_6_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_bready),
  .i_aic_6_targ_lt_axi_m_bresp (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_6_targ_lt_axi_m_bvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_6_targ_lt_axi_m_rdata (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_6_targ_lt_axi_m_rid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_6_targ_lt_axi_m_rlast (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_6_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_rready),
  .i_aic_6_targ_lt_axi_m_rresp (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_6_targ_lt_axi_m_rvalid (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_6_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wdata),
  .o_aic_6_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wlast),
  .i_aic_6_targ_lt_axi_m_wready (u_ai_core_p_6_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_6_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wstrb),
  .o_aic_6_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_lt_axi_m_wvalid),
  .o_aic_6_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_paddr),
  .o_aic_6_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_penable),
  .o_aic_6_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pprot),
  .i_aic_6_targ_syscfg_apb_m_prdata (u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_6_targ_syscfg_apb_m_pready (u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_6_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_psel),
  .i_aic_6_targ_syscfg_apb_m_pslverr (u_ai_core_p_6_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_6_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pstrb),
  .o_aic_6_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pwdata),
  .o_aic_6_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_syscfg_apb_m_pwrite),
  .o_aic_6_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_tok_idle_val),
  .o_aic_6_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_6__o_aic_6_pwr_tok_idle_ack),
  .i_aic_6_pwr_tok_idle_req (u_ai_core_p_6_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_6_init_tok_ocpl_s_maddr (u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_6_init_tok_ocpl_s_mcmd (u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_6_init_tok_ocpl_s_mdata (u_ai_core_p_6_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_6_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_6__o_aic_6_init_tok_ocpl_s_scmdaccept),
  .o_aic_6_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_maddr),
  .o_aic_6_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_mcmd),
  .o_aic_6_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_6__o_aic_6_targ_tok_ocpl_m_mdata),
  .i_aic_6_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_6_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_aic_7_aon_clk (i_ref_clk),
  .i_aic_7_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_aic_7_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_aic_7_clken (u_ai_core_p_7_to_u_noc_top__o_noc_clken),
  .i_aic_7_init_ht_axi_s_araddr (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_araddr),
  .i_aic_7_init_ht_axi_s_arburst (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arburst),
  .i_aic_7_init_ht_axi_s_arcache (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arcache),
  .i_aic_7_init_ht_axi_s_arid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arid),
  .i_aic_7_init_ht_axi_s_arlen (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arlen),
  .i_aic_7_init_ht_axi_s_arlock (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arlock),
  .i_aic_7_init_ht_axi_s_arprot (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arprot),
  .o_aic_7_init_ht_axi_s_arready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_arready),
  .i_aic_7_init_ht_axi_s_arsize (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arsize),
  .i_aic_7_init_ht_axi_s_arvalid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_arvalid),
  .o_aic_7_init_ht_axi_s_rdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rdata),
  .o_aic_7_init_ht_axi_s_rid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rid),
  .o_aic_7_init_ht_axi_s_rlast (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rlast),
  .i_aic_7_init_ht_axi_s_rready (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_rready),
  .o_aic_7_init_ht_axi_s_rresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rresp),
  .o_aic_7_init_ht_axi_s_rvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_rvalid),
  .i_aic_7_init_ht_axi_s_awaddr (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awaddr),
  .i_aic_7_init_ht_axi_s_awburst (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awburst),
  .i_aic_7_init_ht_axi_s_awcache (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awcache),
  .i_aic_7_init_ht_axi_s_awid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awid),
  .i_aic_7_init_ht_axi_s_awlen (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awlen),
  .i_aic_7_init_ht_axi_s_awlock (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awlock),
  .i_aic_7_init_ht_axi_s_awprot (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awprot),
  .o_aic_7_init_ht_axi_s_awready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_awready),
  .i_aic_7_init_ht_axi_s_awsize (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awsize),
  .i_aic_7_init_ht_axi_s_awvalid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_awvalid),
  .o_aic_7_init_ht_axi_s_bid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bid),
  .i_aic_7_init_ht_axi_s_bready (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_bready),
  .o_aic_7_init_ht_axi_s_bresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bresp),
  .o_aic_7_init_ht_axi_s_bvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_bvalid),
  .i_aic_7_init_ht_axi_s_wdata (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wdata),
  .i_aic_7_init_ht_axi_s_wlast (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wlast),
  .o_aic_7_init_ht_axi_s_wready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_ht_axi_s_wready),
  .i_aic_7_init_ht_axi_s_wstrb (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wstrb),
  .i_aic_7_init_ht_axi_s_wvalid (u_ai_core_p_7_to_u_noc_top__o_noc_ht_axi_m_wvalid),
  .i_aic_7_init_lt_axi_s_araddr (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_araddr),
  .i_aic_7_init_lt_axi_s_arburst (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arburst),
  .i_aic_7_init_lt_axi_s_arcache (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arcache),
  .i_aic_7_init_lt_axi_s_arid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arid),
  .i_aic_7_init_lt_axi_s_arlen (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arlen),
  .i_aic_7_init_lt_axi_s_arlock (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arlock),
  .i_aic_7_init_lt_axi_s_arprot (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arprot),
  .i_aic_7_init_lt_axi_s_arqos ('0),
  .o_aic_7_init_lt_axi_s_arready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_arready),
  .i_aic_7_init_lt_axi_s_arsize (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arsize),
  .i_aic_7_init_lt_axi_s_arvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_arvalid),
  .i_aic_7_init_lt_axi_s_awaddr (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awaddr),
  .i_aic_7_init_lt_axi_s_awburst (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awburst),
  .i_aic_7_init_lt_axi_s_awcache (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awcache),
  .i_aic_7_init_lt_axi_s_awid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awid),
  .i_aic_7_init_lt_axi_s_awlen (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awlen),
  .i_aic_7_init_lt_axi_s_awlock (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awlock),
  .i_aic_7_init_lt_axi_s_awprot (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awprot),
  .i_aic_7_init_lt_axi_s_awqos ('0),
  .o_aic_7_init_lt_axi_s_awready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_awready),
  .i_aic_7_init_lt_axi_s_awsize (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awsize),
  .i_aic_7_init_lt_axi_s_awvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_awvalid),
  .o_aic_7_init_lt_axi_s_bid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bid),
  .i_aic_7_init_lt_axi_s_bready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_bready),
  .o_aic_7_init_lt_axi_s_bresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bresp),
  .o_aic_7_init_lt_axi_s_bvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_bvalid),
  .o_aic_7_init_lt_axi_s_rdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rdata),
  .o_aic_7_init_lt_axi_s_rid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rid),
  .o_aic_7_init_lt_axi_s_rlast (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rlast),
  .i_aic_7_init_lt_axi_s_rready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_rready),
  .o_aic_7_init_lt_axi_s_rresp (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rresp),
  .o_aic_7_init_lt_axi_s_rvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_rvalid),
  .i_aic_7_init_lt_axi_s_wdata (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wdata),
  .i_aic_7_init_lt_axi_s_wlast (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wlast),
  .o_aic_7_init_lt_axi_s_wready (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_lt_axi_s_wready),
  .i_aic_7_init_lt_axi_s_wstrb (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wstrb),
  .i_aic_7_init_lt_axi_s_wvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_m_wvalid),
  .o_aic_7_pwr_idle_val (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_idle_val),
  .o_aic_7_pwr_idle_ack (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_idle_ack),
  .i_aic_7_pwr_idle_req (u_ai_core_p_7_to_u_noc_top__o_noc_async_idle_req),
  .i_aic_7_rst_n (u_ai_core_p_7_to_u_noc_top__o_noc_rst_n),
  .o_aic_7_targ_lt_axi_m_araddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_araddr),
  .o_aic_7_targ_lt_axi_m_arburst (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arburst),
  .o_aic_7_targ_lt_axi_m_arcache (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arcache),
  .o_aic_7_targ_lt_axi_m_arid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arid),
  .o_aic_7_targ_lt_axi_m_arlen (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arlen),
  .o_aic_7_targ_lt_axi_m_arlock (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arlock),
  .o_aic_7_targ_lt_axi_m_arprot (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arprot),
  .o_aic_7_targ_lt_axi_m_arqos (),
  .i_aic_7_targ_lt_axi_m_arready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_arready),
  .o_aic_7_targ_lt_axi_m_arsize (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arsize),
  .o_aic_7_targ_lt_axi_m_arvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_arvalid),
  .o_aic_7_targ_lt_axi_m_awaddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awaddr),
  .o_aic_7_targ_lt_axi_m_awburst (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awburst),
  .o_aic_7_targ_lt_axi_m_awcache (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awcache),
  .o_aic_7_targ_lt_axi_m_awid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awid),
  .o_aic_7_targ_lt_axi_m_awlen (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awlen),
  .o_aic_7_targ_lt_axi_m_awlock (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awlock),
  .o_aic_7_targ_lt_axi_m_awprot (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awprot),
  .o_aic_7_targ_lt_axi_m_awqos (),
  .i_aic_7_targ_lt_axi_m_awready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_awready),
  .o_aic_7_targ_lt_axi_m_awsize (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awsize),
  .o_aic_7_targ_lt_axi_m_awvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_awvalid),
  .i_aic_7_targ_lt_axi_m_bid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bid),
  .o_aic_7_targ_lt_axi_m_bready (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_bready),
  .i_aic_7_targ_lt_axi_m_bresp (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bresp),
  .i_aic_7_targ_lt_axi_m_bvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_bvalid),
  .i_aic_7_targ_lt_axi_m_rdata (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rdata),
  .i_aic_7_targ_lt_axi_m_rid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rid),
  .i_aic_7_targ_lt_axi_m_rlast (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rlast),
  .o_aic_7_targ_lt_axi_m_rready (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_rready),
  .i_aic_7_targ_lt_axi_m_rresp (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rresp),
  .i_aic_7_targ_lt_axi_m_rvalid (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_rvalid),
  .o_aic_7_targ_lt_axi_m_wdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wdata),
  .o_aic_7_targ_lt_axi_m_wlast (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wlast),
  .i_aic_7_targ_lt_axi_m_wready (u_ai_core_p_7_to_u_noc_top__o_noc_lt_axi_s_wready),
  .o_aic_7_targ_lt_axi_m_wstrb (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wstrb),
  .o_aic_7_targ_lt_axi_m_wvalid (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_lt_axi_m_wvalid),
  .o_aic_7_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_paddr),
  .o_aic_7_targ_syscfg_apb_m_penable (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_penable),
  .o_aic_7_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pprot),
  .i_aic_7_targ_syscfg_apb_m_prdata (u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_aic_7_targ_syscfg_apb_m_pready (u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_aic_7_targ_syscfg_apb_m_psel (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_psel),
  .i_aic_7_targ_syscfg_apb_m_pslverr (u_ai_core_p_7_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_aic_7_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pstrb),
  .o_aic_7_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pwdata),
  .o_aic_7_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_syscfg_apb_m_pwrite),
  .o_aic_7_pwr_tok_idle_val (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_tok_idle_val),
  .o_aic_7_pwr_tok_idle_ack (u_noc_top_to_u_ai_core_p_7__o_aic_7_pwr_tok_idle_ack),
  .i_aic_7_pwr_tok_idle_req (u_ai_core_p_7_to_u_noc_top__o_noc_ocpl_tok_async_idle_req),
  .i_aic_7_init_tok_ocpl_s_maddr (u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_aic_7_init_tok_ocpl_s_mcmd (u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_aic_7_init_tok_ocpl_s_mdata (u_ai_core_p_7_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_aic_7_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_ai_core_p_7__o_aic_7_init_tok_ocpl_s_scmdaccept),
  .o_aic_7_targ_tok_ocpl_m_maddr (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_maddr),
  .o_aic_7_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_mcmd),
  .o_aic_7_targ_tok_ocpl_m_mdata (u_noc_top_to_u_ai_core_p_7__o_aic_7_targ_tok_ocpl_m_mdata),
  .i_aic_7_targ_tok_ocpl_m_scmdaccept (u_ai_core_p_7_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_apu_aon_clk (i_ref_clk),
  .i_apu_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_apu_init_lt_axi_s_araddr (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_araddr),
  .i_apu_init_lt_axi_s_arburst (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arburst),
  .i_apu_init_lt_axi_s_arcache (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arcache),
  .i_apu_init_lt_axi_s_arid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arid),
  .i_apu_init_lt_axi_s_arlen (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arlen),
  .i_apu_init_lt_axi_s_arlock (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arlock),
  .i_apu_init_lt_axi_s_arprot (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arprot),
  .i_apu_init_lt_axi_s_arqos (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arqos),
  .o_apu_init_lt_axi_s_arready (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_arready),
  .i_apu_init_lt_axi_s_arsize (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arsize),
  .i_apu_init_lt_axi_s_arvalid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_arvalid),
  .i_apu_init_lt_axi_s_awaddr (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awaddr),
  .i_apu_init_lt_axi_s_awburst (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awburst),
  .i_apu_init_lt_axi_s_awcache (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awcache),
  .i_apu_init_lt_axi_s_awid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awid),
  .i_apu_init_lt_axi_s_awlen (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awlen),
  .i_apu_init_lt_axi_s_awlock (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awlock),
  .i_apu_init_lt_axi_s_awprot (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awprot),
  .i_apu_init_lt_axi_s_awqos (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awqos),
  .o_apu_init_lt_axi_s_awready (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_awready),
  .i_apu_init_lt_axi_s_awsize (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awsize),
  .i_apu_init_lt_axi_s_awvalid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_awvalid),
  .o_apu_init_lt_axi_s_bid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bid),
  .i_apu_init_lt_axi_s_bready (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_bready),
  .o_apu_init_lt_axi_s_bresp (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bresp),
  .o_apu_init_lt_axi_s_bvalid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_bvalid),
  .o_apu_init_lt_axi_s_rdata (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rdata),
  .o_apu_init_lt_axi_s_rid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rid),
  .o_apu_init_lt_axi_s_rlast (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rlast),
  .i_apu_init_lt_axi_s_rready (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_rready),
  .o_apu_init_lt_axi_s_rresp (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rresp),
  .o_apu_init_lt_axi_s_rvalid (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_rvalid),
  .i_apu_init_lt_axi_s_wdata (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wdata),
  .i_apu_init_lt_axi_s_wlast (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wlast),
  .o_apu_init_lt_axi_s_wready (u_noc_top_to_u_apu_p__o_apu_init_lt_axi_s_wready),
  .i_apu_init_lt_axi_s_wstrb (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wstrb),
  .i_apu_init_lt_axi_s_wvalid (u_apu_p_to_u_noc_top__o_apu_init_lt_axi_m_wvalid),
  .i_apu_init_mt_axi_s_araddr (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_araddr),
  .i_apu_init_mt_axi_s_arburst (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arburst),
  .i_apu_init_mt_axi_s_arcache (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arcache),
  .i_apu_init_mt_axi_s_arid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arid),
  .i_apu_init_mt_axi_s_arlen (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arlen),
  .i_apu_init_mt_axi_s_arlock (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arlock),
  .i_apu_init_mt_axi_s_arprot (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arprot),
  .i_apu_init_mt_axi_s_arqos (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arqos),
  .o_apu_init_mt_axi_s_arready (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_arready),
  .i_apu_init_mt_axi_s_arsize (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arsize),
  .i_apu_init_mt_axi_s_arvalid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_arvalid),
  .o_apu_init_mt_axi_s_rdata (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rdata),
  .o_apu_init_mt_axi_s_rid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rid),
  .o_apu_init_mt_axi_s_rlast (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rlast),
  .i_apu_init_mt_axi_s_rready (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_rready),
  .o_apu_init_mt_axi_s_rresp (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rresp),
  .o_apu_init_mt_axi_s_rvalid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_rvalid),
  .i_apu_init_mt_axi_s_awaddr (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awaddr),
  .i_apu_init_mt_axi_s_awburst (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awburst),
  .i_apu_init_mt_axi_s_awcache (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awcache),
  .i_apu_init_mt_axi_s_awid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awid),
  .i_apu_init_mt_axi_s_awlen (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awlen),
  .i_apu_init_mt_axi_s_awlock (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awlock),
  .i_apu_init_mt_axi_s_awprot (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awprot),
  .i_apu_init_mt_axi_s_awqos (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awqos),
  .o_apu_init_mt_axi_s_awready (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_awready),
  .i_apu_init_mt_axi_s_awsize (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awsize),
  .i_apu_init_mt_axi_s_awvalid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_awvalid),
  .o_apu_init_mt_axi_s_bid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bid),
  .i_apu_init_mt_axi_s_bready (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_bready),
  .o_apu_init_mt_axi_s_bresp (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bresp),
  .o_apu_init_mt_axi_s_bvalid (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_bvalid),
  .i_apu_init_mt_axi_s_wdata (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wdata),
  .i_apu_init_mt_axi_s_wlast (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wlast),
  .o_apu_init_mt_axi_s_wready (u_noc_top_to_u_apu_p__o_apu_init_mt_axi_s_wready),
  .i_apu_init_mt_axi_s_wstrb (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wstrb),
  .i_apu_init_mt_axi_s_wvalid (u_apu_p_to_u_noc_top__o_apu_init_mt_axi_m_wvalid),
  .o_apu_pwr_idle_val (u_noc_top_to_u_apu_p__o_apu_pwr_idle_val),
  .o_apu_pwr_idle_ack (u_noc_top_to_u_apu_p__o_apu_pwr_idle_ack),
  .i_apu_pwr_idle_req (u_apu_p_to_u_noc_top__o_noc_async_idle_req),
  .o_apu_targ_lt_axi_m_araddr (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_araddr),
  .o_apu_targ_lt_axi_m_arburst (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arburst),
  .o_apu_targ_lt_axi_m_arcache (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arcache),
  .o_apu_targ_lt_axi_m_arid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arid),
  .o_apu_targ_lt_axi_m_arlen (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arlen),
  .o_apu_targ_lt_axi_m_arlock (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arlock),
  .o_apu_targ_lt_axi_m_arprot (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arprot),
  .o_apu_targ_lt_axi_m_arqos (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arqos),
  .i_apu_targ_lt_axi_m_arready (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_arready),
  .o_apu_targ_lt_axi_m_arsize (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arsize),
  .o_apu_targ_lt_axi_m_arvalid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_arvalid),
  .o_apu_targ_lt_axi_m_awaddr (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awaddr),
  .o_apu_targ_lt_axi_m_awburst (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awburst),
  .o_apu_targ_lt_axi_m_awcache (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awcache),
  .o_apu_targ_lt_axi_m_awid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awid),
  .o_apu_targ_lt_axi_m_awlen (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awlen),
  .o_apu_targ_lt_axi_m_awlock (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awlock),
  .o_apu_targ_lt_axi_m_awprot (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awprot),
  .o_apu_targ_lt_axi_m_awqos (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awqos),
  .i_apu_targ_lt_axi_m_awready (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_awready),
  .o_apu_targ_lt_axi_m_awsize (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awsize),
  .o_apu_targ_lt_axi_m_awvalid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_awvalid),
  .i_apu_targ_lt_axi_m_bid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bid),
  .o_apu_targ_lt_axi_m_bready (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_bready),
  .i_apu_targ_lt_axi_m_bresp (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bresp),
  .i_apu_targ_lt_axi_m_bvalid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_bvalid),
  .i_apu_targ_lt_axi_m_rdata (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rdata),
  .i_apu_targ_lt_axi_m_rid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rid),
  .i_apu_targ_lt_axi_m_rlast (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rlast),
  .o_apu_targ_lt_axi_m_rready (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_rready),
  .i_apu_targ_lt_axi_m_rresp (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rresp),
  .i_apu_targ_lt_axi_m_rvalid (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_rvalid),
  .o_apu_targ_lt_axi_m_wdata (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wdata),
  .o_apu_targ_lt_axi_m_wlast (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wlast),
  .i_apu_targ_lt_axi_m_wready (u_apu_p_to_u_noc_top__o_apu_targ_lt_axi_s_wready),
  .o_apu_targ_lt_axi_m_wstrb (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wstrb),
  .o_apu_targ_lt_axi_m_wvalid (u_noc_top_to_u_apu_p__o_apu_targ_lt_axi_m_wvalid),
  .o_apu_targ_syscfg_apb_m_paddr (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_paddr),
  .o_apu_targ_syscfg_apb_m_penable (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_penable),
  .o_apu_targ_syscfg_apb_m_pprot (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pprot),
  .i_apu_targ_syscfg_apb_m_prdata (u_apu_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_apu_targ_syscfg_apb_m_pready (u_apu_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_apu_targ_syscfg_apb_m_psel (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_psel),
  .i_apu_targ_syscfg_apb_m_pslverr (u_apu_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_apu_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pstrb),
  .o_apu_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pwdata),
  .o_apu_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_apu_p__o_apu_targ_syscfg_apb_m_pwrite),
  .o_apu_pwr_tok_idle_val (u_noc_top_to_u_apu_p__o_apu_pwr_tok_idle_val),
  .o_apu_pwr_tok_idle_ack (u_noc_top_to_u_apu_p__o_apu_pwr_tok_idle_ack),
  .i_apu_pwr_tok_idle_req (u_apu_p_to_u_noc_top__o_noc_tok_async_idle_req),
  .i_apu_init_tok_ocpl_s_maddr (u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_maddr),
  .i_apu_init_tok_ocpl_s_mcmd (u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_mcmd),
  .i_apu_init_tok_ocpl_s_mdata (u_apu_p_to_u_noc_top__o_tok_prod_ocpl_m_mdata),
  .o_apu_init_tok_ocpl_s_scmdaccept (u_noc_top_to_u_apu_p__o_apu_init_tok_ocpl_s_scmdaccept),
  .o_apu_targ_tok_ocpl_m_maddr (u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_maddr),
  .o_apu_targ_tok_ocpl_m_mcmd (u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_mcmd),
  .o_apu_targ_tok_ocpl_m_mdata (u_noc_top_to_u_apu_p__o_apu_targ_tok_ocpl_m_mdata),
  .i_apu_targ_tok_ocpl_m_scmdaccept (u_apu_p_to_u_noc_top__o_tok_cons_ocpl_s_scmdaccept),
  .i_apu_x_clk (u_soc_mgmt_p_to_multi__o_apu_clk),
  .i_apu_x_clken (u_apu_p_to_u_noc_top__o_noc_clken),
  .i_apu_x_rst_n (u_apu_p_to_u_noc_top__o_noc_rst_n),
  .i_dcd_aon_clk (i_ref_clk),
  .i_dcd_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_dcd_codec_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .i_dcd_codec_clken (u_dcd_p_to_u_noc_top__o_noc_clk_en),
  .i_dcd_codec_rst_n (u_dcd_p_to_u_noc_top__o_noc_rst_n),
  .i_dcd_dec_0_init_mt_axi_s_araddr (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_araddr),
  .i_dcd_dec_0_init_mt_axi_s_arburst (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arburst),
  .i_dcd_dec_0_init_mt_axi_s_arcache (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arcache),
  .i_dcd_dec_0_init_mt_axi_s_arid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arid),
  .i_dcd_dec_0_init_mt_axi_s_arlen (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arlen),
  .i_dcd_dec_0_init_mt_axi_s_arlock (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arlock),
  .i_dcd_dec_0_init_mt_axi_s_arprot (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arprot),
  .i_dcd_dec_0_init_mt_axi_s_arqos (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arqos),
  .o_dcd_dec_0_init_mt_axi_s_arready (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_arready),
  .i_dcd_dec_0_init_mt_axi_s_arsize (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arsize),
  .i_dcd_dec_0_init_mt_axi_s_arvalid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_arvalid),
  .o_dcd_dec_0_init_mt_axi_s_rdata (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rdata),
  .o_dcd_dec_0_init_mt_axi_s_rid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rid),
  .o_dcd_dec_0_init_mt_axi_s_rlast (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rlast),
  .i_dcd_dec_0_init_mt_axi_s_rready (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_rready),
  .o_dcd_dec_0_init_mt_axi_s_rresp (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rresp),
  .o_dcd_dec_0_init_mt_axi_s_rvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_rvalid),
  .i_dcd_dec_0_init_mt_axi_s_awaddr (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awaddr),
  .i_dcd_dec_0_init_mt_axi_s_awburst (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awburst),
  .i_dcd_dec_0_init_mt_axi_s_awcache (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awcache),
  .i_dcd_dec_0_init_mt_axi_s_awid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awid),
  .i_dcd_dec_0_init_mt_axi_s_awlen (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awlen),
  .i_dcd_dec_0_init_mt_axi_s_awlock (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awlock),
  .i_dcd_dec_0_init_mt_axi_s_awprot (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awprot),
  .i_dcd_dec_0_init_mt_axi_s_awqos (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awqos),
  .o_dcd_dec_0_init_mt_axi_s_awready (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_awready),
  .i_dcd_dec_0_init_mt_axi_s_awsize (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awsize),
  .i_dcd_dec_0_init_mt_axi_s_awvalid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_awvalid),
  .o_dcd_dec_0_init_mt_axi_s_bid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bid),
  .i_dcd_dec_0_init_mt_axi_s_bready (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_bready),
  .o_dcd_dec_0_init_mt_axi_s_bresp (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bresp),
  .o_dcd_dec_0_init_mt_axi_s_bvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_bvalid),
  .i_dcd_dec_0_init_mt_axi_s_wdata (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wdata),
  .i_dcd_dec_0_init_mt_axi_s_wlast (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wlast),
  .o_dcd_dec_0_init_mt_axi_s_wready (u_noc_top_to_u_dcd_p__o_dcd_dec_0_init_mt_axi_s_wready),
  .i_dcd_dec_0_init_mt_axi_s_wstrb (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wstrb),
  .i_dcd_dec_0_init_mt_axi_s_wvalid (u_dcd_p_to_u_noc_top__o_dec_0_axi_m_wvalid),
  .i_dcd_dec_1_init_mt_axi_s_araddr (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_araddr),
  .i_dcd_dec_1_init_mt_axi_s_arburst (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arburst),
  .i_dcd_dec_1_init_mt_axi_s_arcache (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arcache),
  .i_dcd_dec_1_init_mt_axi_s_arid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arid),
  .i_dcd_dec_1_init_mt_axi_s_arlen (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arlen),
  .i_dcd_dec_1_init_mt_axi_s_arlock (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arlock),
  .i_dcd_dec_1_init_mt_axi_s_arprot (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arprot),
  .i_dcd_dec_1_init_mt_axi_s_arqos (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arqos),
  .o_dcd_dec_1_init_mt_axi_s_arready (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_arready),
  .i_dcd_dec_1_init_mt_axi_s_arsize (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arsize),
  .i_dcd_dec_1_init_mt_axi_s_arvalid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_arvalid),
  .o_dcd_dec_1_init_mt_axi_s_rdata (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rdata),
  .o_dcd_dec_1_init_mt_axi_s_rid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rid),
  .o_dcd_dec_1_init_mt_axi_s_rlast (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rlast),
  .i_dcd_dec_1_init_mt_axi_s_rready (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_rready),
  .o_dcd_dec_1_init_mt_axi_s_rresp (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rresp),
  .o_dcd_dec_1_init_mt_axi_s_rvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_rvalid),
  .i_dcd_dec_1_init_mt_axi_s_awaddr (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awaddr),
  .i_dcd_dec_1_init_mt_axi_s_awburst (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awburst),
  .i_dcd_dec_1_init_mt_axi_s_awcache (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awcache),
  .i_dcd_dec_1_init_mt_axi_s_awid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awid),
  .i_dcd_dec_1_init_mt_axi_s_awlen (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awlen),
  .i_dcd_dec_1_init_mt_axi_s_awlock (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awlock),
  .i_dcd_dec_1_init_mt_axi_s_awprot (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awprot),
  .i_dcd_dec_1_init_mt_axi_s_awqos (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awqos),
  .o_dcd_dec_1_init_mt_axi_s_awready (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_awready),
  .i_dcd_dec_1_init_mt_axi_s_awsize (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awsize),
  .i_dcd_dec_1_init_mt_axi_s_awvalid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_awvalid),
  .o_dcd_dec_1_init_mt_axi_s_bid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bid),
  .i_dcd_dec_1_init_mt_axi_s_bready (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_bready),
  .o_dcd_dec_1_init_mt_axi_s_bresp (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bresp),
  .o_dcd_dec_1_init_mt_axi_s_bvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_bvalid),
  .i_dcd_dec_1_init_mt_axi_s_wdata (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wdata),
  .i_dcd_dec_1_init_mt_axi_s_wlast (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wlast),
  .o_dcd_dec_1_init_mt_axi_s_wready (u_noc_top_to_u_dcd_p__o_dcd_dec_1_init_mt_axi_s_wready),
  .i_dcd_dec_1_init_mt_axi_s_wstrb (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wstrb),
  .i_dcd_dec_1_init_mt_axi_s_wvalid (u_dcd_p_to_u_noc_top__o_dec_1_axi_m_wvalid),
  .i_dcd_dec_2_init_mt_axi_s_araddr (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_araddr),
  .i_dcd_dec_2_init_mt_axi_s_arburst (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arburst),
  .i_dcd_dec_2_init_mt_axi_s_arcache (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arcache),
  .i_dcd_dec_2_init_mt_axi_s_arid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arid),
  .i_dcd_dec_2_init_mt_axi_s_arlen (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arlen),
  .i_dcd_dec_2_init_mt_axi_s_arlock (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arlock),
  .i_dcd_dec_2_init_mt_axi_s_arprot (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arprot),
  .i_dcd_dec_2_init_mt_axi_s_arqos (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arqos),
  .o_dcd_dec_2_init_mt_axi_s_arready (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_arready),
  .i_dcd_dec_2_init_mt_axi_s_arsize (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arsize),
  .i_dcd_dec_2_init_mt_axi_s_arvalid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_arvalid),
  .o_dcd_dec_2_init_mt_axi_s_rdata (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rdata),
  .o_dcd_dec_2_init_mt_axi_s_rid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rid),
  .o_dcd_dec_2_init_mt_axi_s_rlast (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rlast),
  .i_dcd_dec_2_init_mt_axi_s_rready (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_rready),
  .o_dcd_dec_2_init_mt_axi_s_rresp (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rresp),
  .o_dcd_dec_2_init_mt_axi_s_rvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_rvalid),
  .i_dcd_dec_2_init_mt_axi_s_awaddr (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awaddr),
  .i_dcd_dec_2_init_mt_axi_s_awburst (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awburst),
  .i_dcd_dec_2_init_mt_axi_s_awcache (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awcache),
  .i_dcd_dec_2_init_mt_axi_s_awid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awid),
  .i_dcd_dec_2_init_mt_axi_s_awlen (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awlen),
  .i_dcd_dec_2_init_mt_axi_s_awlock (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awlock),
  .i_dcd_dec_2_init_mt_axi_s_awprot (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awprot),
  .i_dcd_dec_2_init_mt_axi_s_awqos (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awqos),
  .o_dcd_dec_2_init_mt_axi_s_awready (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_awready),
  .i_dcd_dec_2_init_mt_axi_s_awsize (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awsize),
  .i_dcd_dec_2_init_mt_axi_s_awvalid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_awvalid),
  .o_dcd_dec_2_init_mt_axi_s_bid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bid),
  .i_dcd_dec_2_init_mt_axi_s_bready (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_bready),
  .o_dcd_dec_2_init_mt_axi_s_bresp (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bresp),
  .o_dcd_dec_2_init_mt_axi_s_bvalid (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_bvalid),
  .i_dcd_dec_2_init_mt_axi_s_wdata (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wdata),
  .i_dcd_dec_2_init_mt_axi_s_wlast (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wlast),
  .o_dcd_dec_2_init_mt_axi_s_wready (u_noc_top_to_u_dcd_p__o_dcd_dec_2_init_mt_axi_s_wready),
  .i_dcd_dec_2_init_mt_axi_s_wstrb (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wstrb),
  .i_dcd_dec_2_init_mt_axi_s_wvalid (u_dcd_p_to_u_noc_top__o_dec_2_axi_m_wvalid),
  .i_dcd_mcu_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_dcd_mcu_clken (u_dcd_p_to_u_noc_top__o_noc_mcu_clk_en),
  .i_dcd_mcu_init_lt_axi_s_araddr (u_dcd_p_to_u_noc_top__o_mcu_axi_m_araddr),
  .i_dcd_mcu_init_lt_axi_s_arburst (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arburst),
  .i_dcd_mcu_init_lt_axi_s_arcache (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arcache),
  .i_dcd_mcu_init_lt_axi_s_arid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arid),
  .i_dcd_mcu_init_lt_axi_s_arlen (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arlen),
  .i_dcd_mcu_init_lt_axi_s_arlock (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arlock),
  .i_dcd_mcu_init_lt_axi_s_arprot (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arprot),
  .i_dcd_mcu_init_lt_axi_s_arqos (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arqos),
  .o_dcd_mcu_init_lt_axi_s_arready (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_arready),
  .i_dcd_mcu_init_lt_axi_s_arsize (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arsize),
  .i_dcd_mcu_init_lt_axi_s_arvalid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_arvalid),
  .o_dcd_mcu_init_lt_axi_s_rdata (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rdata),
  .o_dcd_mcu_init_lt_axi_s_rid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rid),
  .o_dcd_mcu_init_lt_axi_s_rlast (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rlast),
  .i_dcd_mcu_init_lt_axi_s_rready (u_dcd_p_to_u_noc_top__o_mcu_axi_m_rready),
  .o_dcd_mcu_init_lt_axi_s_rresp (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rresp),
  .o_dcd_mcu_init_lt_axi_s_rvalid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_rvalid),
  .i_dcd_mcu_init_lt_axi_s_awaddr (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awaddr),
  .i_dcd_mcu_init_lt_axi_s_awburst (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awburst),
  .i_dcd_mcu_init_lt_axi_s_awcache (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awcache),
  .i_dcd_mcu_init_lt_axi_s_awid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awid),
  .i_dcd_mcu_init_lt_axi_s_awlen (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awlen),
  .i_dcd_mcu_init_lt_axi_s_awlock (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awlock),
  .i_dcd_mcu_init_lt_axi_s_awprot (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awprot),
  .i_dcd_mcu_init_lt_axi_s_awqos (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awqos),
  .o_dcd_mcu_init_lt_axi_s_awready (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_awready),
  .i_dcd_mcu_init_lt_axi_s_awsize (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awsize),
  .i_dcd_mcu_init_lt_axi_s_awvalid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_awvalid),
  .o_dcd_mcu_init_lt_axi_s_bid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bid),
  .i_dcd_mcu_init_lt_axi_s_bready (u_dcd_p_to_u_noc_top__o_mcu_axi_m_bready),
  .o_dcd_mcu_init_lt_axi_s_bresp (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bresp),
  .o_dcd_mcu_init_lt_axi_s_bvalid (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_bvalid),
  .i_dcd_mcu_init_lt_axi_s_wdata (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wdata),
  .i_dcd_mcu_init_lt_axi_s_wlast (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wlast),
  .o_dcd_mcu_init_lt_axi_s_wready (u_noc_top_to_u_dcd_p__o_dcd_mcu_init_lt_axi_s_wready),
  .i_dcd_mcu_init_lt_axi_s_wstrb (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wstrb),
  .i_dcd_mcu_init_lt_axi_s_wvalid (u_dcd_p_to_u_noc_top__o_mcu_axi_m_wvalid),
  .o_dcd_mcu_pwr_idle_val (u_noc_top_to_u_dcd_p__o_dcd_mcu_pwr_idle_val),
  .o_dcd_mcu_pwr_idle_ack (u_noc_top_to_u_dcd_p__o_dcd_mcu_pwr_idle_ack),
  .i_dcd_mcu_pwr_idle_req (u_dcd_p_to_u_noc_top__o_noc_mcu_async_idle_req),
  .i_dcd_mcu_rst_n (u_dcd_p_to_u_noc_top__o_noc_mcu_rst_n),
  .o_dcd_pwr_idle_val (u_noc_top_to_u_dcd_p__o_dcd_pwr_idle_val),
  .o_dcd_pwr_idle_ack (u_noc_top_to_u_dcd_p__o_dcd_pwr_idle_ack),
  .i_dcd_pwr_idle_req (u_dcd_p_to_u_noc_top__o_noc_async_idle_req),
  .o_dcd_targ_cfg_apb_m_paddr (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_paddr),
  .o_dcd_targ_cfg_apb_m_penable (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_penable),
  .o_dcd_targ_cfg_apb_m_pprot (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pprot),
  .i_dcd_targ_cfg_apb_m_prdata (u_dcd_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_dcd_targ_cfg_apb_m_pready (u_dcd_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_dcd_targ_cfg_apb_m_psel (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_psel),
  .i_dcd_targ_cfg_apb_m_pslverr (u_dcd_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_dcd_targ_cfg_apb_m_pstrb (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pstrb),
  .o_dcd_targ_cfg_apb_m_pwdata (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pwdata),
  .o_dcd_targ_cfg_apb_m_pwrite (u_noc_top_to_u_dcd_p__o_dcd_targ_cfg_apb_m_pwrite),
  .o_dcd_targ_syscfg_apb_m_paddr (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_paddr),
  .o_dcd_targ_syscfg_apb_m_penable (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_penable),
  .o_dcd_targ_syscfg_apb_m_pprot (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pprot),
  .i_dcd_targ_syscfg_apb_m_prdata (u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_prdata),
  .i_dcd_targ_syscfg_apb_m_pready (u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_pready),
  .o_dcd_targ_syscfg_apb_m_psel (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_psel),
  .i_dcd_targ_syscfg_apb_m_pslverr (u_dcd_p_to_u_noc_top__o_syscfg_apb4_s_pslverr),
  .o_dcd_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pstrb),
  .o_dcd_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pwdata),
  .o_dcd_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_dcd_p__o_dcd_targ_syscfg_apb_m_pwrite),
  .i_ddr_wpll_aon_clk (i_ref_clk),
  .i_ddr_wpll_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .o_ddr_wpll_targ_syscfg_apb_m_paddr (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_paddr),
  .o_ddr_wpll_targ_syscfg_apb_m_penable (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_penable),
  .o_ddr_wpll_targ_syscfg_apb_m_pprot (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pprot),
  .i_ddr_wpll_targ_syscfg_apb_m_prdata (u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_ddr_wpll_targ_syscfg_apb_m_pready (u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_ddr_wpll_targ_syscfg_apb_m_psel (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_psel),
  .i_ddr_wpll_targ_syscfg_apb_m_pslverr (u_ddr_west_clock_gen_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_ddr_wpll_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pstrb),
  .o_ddr_wpll_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pwdata),
  .o_ddr_wpll_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_ddr_west_clock_gen_p__o_ddr_wpll_targ_syscfg_apb_m_pwrite),
  .i_l2_0_aon_clk (i_ref_clk),
  .i_l2_0_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_0_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_0_clken (u_l2_p_0_to_u_noc_top__o_noc_clken),
  .o_l2_0_pwr_idle_val (u_noc_top_to_u_l2_p_0__o_l2_0_pwr_idle_val),
  .o_l2_0_pwr_idle_ack (u_noc_top_to_u_l2_p_0__o_l2_0_pwr_idle_ack),
  .i_l2_0_pwr_idle_req (u_l2_p_0_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_0_rst_n (u_l2_p_0_to_u_noc_top__o_noc_rst_n),
  .o_l2_0_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_araddr),
  .o_l2_0_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arburst),
  .o_l2_0_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arcache),
  .o_l2_0_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arid),
  .o_l2_0_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arlen),
  .o_l2_0_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arlock),
  .o_l2_0_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arprot),
  .i_l2_0_targ_ht_axi_m_arready (u_l2_p_0_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_0_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arsize),
  .o_l2_0_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_arvalid),
  .i_l2_0_targ_ht_axi_m_rdata (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_0_targ_ht_axi_m_rid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_0_targ_ht_axi_m_rlast (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_0_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_rready),
  .i_l2_0_targ_ht_axi_m_rresp (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_0_targ_ht_axi_m_rvalid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_0_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awaddr),
  .o_l2_0_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awburst),
  .o_l2_0_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awcache),
  .o_l2_0_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awid),
  .o_l2_0_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awlen),
  .o_l2_0_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awlock),
  .o_l2_0_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awprot),
  .i_l2_0_targ_ht_axi_m_awready (u_l2_p_0_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_0_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awsize),
  .o_l2_0_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_awvalid),
  .i_l2_0_targ_ht_axi_m_bid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_0_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_bready),
  .i_l2_0_targ_ht_axi_m_bresp (u_l2_p_0_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_0_targ_ht_axi_m_bvalid (u_l2_p_0_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_0_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wdata),
  .o_l2_0_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wlast),
  .i_l2_0_targ_ht_axi_m_wready (u_l2_p_0_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_0_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wstrb),
  .o_l2_0_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_0__o_l2_0_targ_ht_axi_m_wvalid),
  .o_l2_0_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_paddr),
  .o_l2_0_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_penable),
  .o_l2_0_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pprot),
  .i_l2_0_targ_syscfg_apb_m_prdata (u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_0_targ_syscfg_apb_m_pready (u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_0_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_psel),
  .i_l2_0_targ_syscfg_apb_m_pslverr (u_l2_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_0_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pstrb),
  .o_l2_0_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pwdata),
  .o_l2_0_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_0__o_l2_0_targ_syscfg_apb_m_pwrite),
  .i_l2_1_aon_clk (i_ref_clk),
  .i_l2_1_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_1_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_1_clken (u_l2_p_1_to_u_noc_top__o_noc_clken),
  .o_l2_1_pwr_idle_val (u_noc_top_to_u_l2_p_1__o_l2_1_pwr_idle_val),
  .o_l2_1_pwr_idle_ack (u_noc_top_to_u_l2_p_1__o_l2_1_pwr_idle_ack),
  .i_l2_1_pwr_idle_req (u_l2_p_1_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_1_rst_n (u_l2_p_1_to_u_noc_top__o_noc_rst_n),
  .o_l2_1_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_araddr),
  .o_l2_1_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arburst),
  .o_l2_1_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arcache),
  .o_l2_1_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arid),
  .o_l2_1_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arlen),
  .o_l2_1_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arlock),
  .o_l2_1_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arprot),
  .i_l2_1_targ_ht_axi_m_arready (u_l2_p_1_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_1_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arsize),
  .o_l2_1_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_arvalid),
  .i_l2_1_targ_ht_axi_m_rdata (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_1_targ_ht_axi_m_rid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_1_targ_ht_axi_m_rlast (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_1_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_rready),
  .i_l2_1_targ_ht_axi_m_rresp (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_1_targ_ht_axi_m_rvalid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_1_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awaddr),
  .o_l2_1_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awburst),
  .o_l2_1_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awcache),
  .o_l2_1_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awid),
  .o_l2_1_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awlen),
  .o_l2_1_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awlock),
  .o_l2_1_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awprot),
  .i_l2_1_targ_ht_axi_m_awready (u_l2_p_1_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_1_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awsize),
  .o_l2_1_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_awvalid),
  .i_l2_1_targ_ht_axi_m_bid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_1_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_bready),
  .i_l2_1_targ_ht_axi_m_bresp (u_l2_p_1_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_1_targ_ht_axi_m_bvalid (u_l2_p_1_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_1_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wdata),
  .o_l2_1_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wlast),
  .i_l2_1_targ_ht_axi_m_wready (u_l2_p_1_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_1_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wstrb),
  .o_l2_1_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_1__o_l2_1_targ_ht_axi_m_wvalid),
  .o_l2_1_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_paddr),
  .o_l2_1_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_penable),
  .o_l2_1_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pprot),
  .i_l2_1_targ_syscfg_apb_m_prdata (u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_1_targ_syscfg_apb_m_pready (u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_1_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_psel),
  .i_l2_1_targ_syscfg_apb_m_pslverr (u_l2_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_1_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pstrb),
  .o_l2_1_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pwdata),
  .o_l2_1_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_1__o_l2_1_targ_syscfg_apb_m_pwrite),
  .i_l2_2_aon_clk (i_ref_clk),
  .i_l2_2_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_2_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_2_clken (u_l2_p_2_to_u_noc_top__o_noc_clken),
  .o_l2_2_pwr_idle_val (u_noc_top_to_u_l2_p_2__o_l2_2_pwr_idle_val),
  .o_l2_2_pwr_idle_ack (u_noc_top_to_u_l2_p_2__o_l2_2_pwr_idle_ack),
  .i_l2_2_pwr_idle_req (u_l2_p_2_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_2_rst_n (u_l2_p_2_to_u_noc_top__o_noc_rst_n),
  .o_l2_2_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_araddr),
  .o_l2_2_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arburst),
  .o_l2_2_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arcache),
  .o_l2_2_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arid),
  .o_l2_2_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arlen),
  .o_l2_2_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arlock),
  .o_l2_2_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arprot),
  .i_l2_2_targ_ht_axi_m_arready (u_l2_p_2_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_2_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arsize),
  .o_l2_2_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_arvalid),
  .i_l2_2_targ_ht_axi_m_rdata (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_2_targ_ht_axi_m_rid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_2_targ_ht_axi_m_rlast (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_2_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_rready),
  .i_l2_2_targ_ht_axi_m_rresp (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_2_targ_ht_axi_m_rvalid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_2_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awaddr),
  .o_l2_2_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awburst),
  .o_l2_2_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awcache),
  .o_l2_2_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awid),
  .o_l2_2_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awlen),
  .o_l2_2_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awlock),
  .o_l2_2_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awprot),
  .i_l2_2_targ_ht_axi_m_awready (u_l2_p_2_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_2_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awsize),
  .o_l2_2_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_awvalid),
  .i_l2_2_targ_ht_axi_m_bid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_2_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_bready),
  .i_l2_2_targ_ht_axi_m_bresp (u_l2_p_2_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_2_targ_ht_axi_m_bvalid (u_l2_p_2_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_2_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wdata),
  .o_l2_2_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wlast),
  .i_l2_2_targ_ht_axi_m_wready (u_l2_p_2_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_2_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wstrb),
  .o_l2_2_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_2__o_l2_2_targ_ht_axi_m_wvalid),
  .o_l2_2_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_paddr),
  .o_l2_2_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_penable),
  .o_l2_2_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pprot),
  .i_l2_2_targ_syscfg_apb_m_prdata (u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_2_targ_syscfg_apb_m_pready (u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_2_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_psel),
  .i_l2_2_targ_syscfg_apb_m_pslverr (u_l2_p_2_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_2_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pstrb),
  .o_l2_2_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pwdata),
  .o_l2_2_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_2__o_l2_2_targ_syscfg_apb_m_pwrite),
  .i_l2_3_aon_clk (i_ref_clk),
  .i_l2_3_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_3_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_3_clken (u_l2_p_3_to_u_noc_top__o_noc_clken),
  .o_l2_3_pwr_idle_val (u_noc_top_to_u_l2_p_3__o_l2_3_pwr_idle_val),
  .o_l2_3_pwr_idle_ack (u_noc_top_to_u_l2_p_3__o_l2_3_pwr_idle_ack),
  .i_l2_3_pwr_idle_req (u_l2_p_3_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_3_rst_n (u_l2_p_3_to_u_noc_top__o_noc_rst_n),
  .o_l2_3_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_araddr),
  .o_l2_3_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arburst),
  .o_l2_3_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arcache),
  .o_l2_3_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arid),
  .o_l2_3_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arlen),
  .o_l2_3_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arlock),
  .o_l2_3_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arprot),
  .i_l2_3_targ_ht_axi_m_arready (u_l2_p_3_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_3_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arsize),
  .o_l2_3_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_arvalid),
  .i_l2_3_targ_ht_axi_m_rdata (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_3_targ_ht_axi_m_rid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_3_targ_ht_axi_m_rlast (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_3_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_rready),
  .i_l2_3_targ_ht_axi_m_rresp (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_3_targ_ht_axi_m_rvalid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_3_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awaddr),
  .o_l2_3_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awburst),
  .o_l2_3_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awcache),
  .o_l2_3_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awid),
  .o_l2_3_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awlen),
  .o_l2_3_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awlock),
  .o_l2_3_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awprot),
  .i_l2_3_targ_ht_axi_m_awready (u_l2_p_3_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_3_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awsize),
  .o_l2_3_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_awvalid),
  .i_l2_3_targ_ht_axi_m_bid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_3_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_bready),
  .i_l2_3_targ_ht_axi_m_bresp (u_l2_p_3_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_3_targ_ht_axi_m_bvalid (u_l2_p_3_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_3_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wdata),
  .o_l2_3_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wlast),
  .i_l2_3_targ_ht_axi_m_wready (u_l2_p_3_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_3_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wstrb),
  .o_l2_3_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_3__o_l2_3_targ_ht_axi_m_wvalid),
  .o_l2_3_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_paddr),
  .o_l2_3_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_penable),
  .o_l2_3_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pprot),
  .i_l2_3_targ_syscfg_apb_m_prdata (u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_3_targ_syscfg_apb_m_pready (u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_3_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_psel),
  .i_l2_3_targ_syscfg_apb_m_pslverr (u_l2_p_3_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_3_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pstrb),
  .o_l2_3_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pwdata),
  .o_l2_3_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_3__o_l2_3_targ_syscfg_apb_m_pwrite),
  .i_l2_4_aon_clk (i_ref_clk),
  .i_l2_4_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_4_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_4_clken (u_l2_p_4_to_u_noc_top__o_noc_clken),
  .o_l2_4_pwr_idle_val (u_noc_top_to_u_l2_p_4__o_l2_4_pwr_idle_val),
  .o_l2_4_pwr_idle_ack (u_noc_top_to_u_l2_p_4__o_l2_4_pwr_idle_ack),
  .i_l2_4_pwr_idle_req (u_l2_p_4_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_4_rst_n (u_l2_p_4_to_u_noc_top__o_noc_rst_n),
  .o_l2_4_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_araddr),
  .o_l2_4_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arburst),
  .o_l2_4_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arcache),
  .o_l2_4_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arid),
  .o_l2_4_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arlen),
  .o_l2_4_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arlock),
  .o_l2_4_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arprot),
  .i_l2_4_targ_ht_axi_m_arready (u_l2_p_4_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_4_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arsize),
  .o_l2_4_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_arvalid),
  .i_l2_4_targ_ht_axi_m_rdata (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_4_targ_ht_axi_m_rid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_4_targ_ht_axi_m_rlast (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_4_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_rready),
  .i_l2_4_targ_ht_axi_m_rresp (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_4_targ_ht_axi_m_rvalid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_4_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awaddr),
  .o_l2_4_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awburst),
  .o_l2_4_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awcache),
  .o_l2_4_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awid),
  .o_l2_4_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awlen),
  .o_l2_4_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awlock),
  .o_l2_4_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awprot),
  .i_l2_4_targ_ht_axi_m_awready (u_l2_p_4_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_4_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awsize),
  .o_l2_4_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_awvalid),
  .i_l2_4_targ_ht_axi_m_bid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_4_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_bready),
  .i_l2_4_targ_ht_axi_m_bresp (u_l2_p_4_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_4_targ_ht_axi_m_bvalid (u_l2_p_4_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_4_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wdata),
  .o_l2_4_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wlast),
  .i_l2_4_targ_ht_axi_m_wready (u_l2_p_4_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_4_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wstrb),
  .o_l2_4_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_4__o_l2_4_targ_ht_axi_m_wvalid),
  .o_l2_4_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_paddr),
  .o_l2_4_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_penable),
  .o_l2_4_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pprot),
  .i_l2_4_targ_syscfg_apb_m_prdata (u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_4_targ_syscfg_apb_m_pready (u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_4_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_psel),
  .i_l2_4_targ_syscfg_apb_m_pslverr (u_l2_p_4_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_4_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pstrb),
  .o_l2_4_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pwdata),
  .o_l2_4_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_4__o_l2_4_targ_syscfg_apb_m_pwrite),
  .i_l2_5_aon_clk (i_ref_clk),
  .i_l2_5_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_5_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_5_clken (u_l2_p_5_to_u_noc_top__o_noc_clken),
  .o_l2_5_pwr_idle_val (u_noc_top_to_u_l2_p_5__o_l2_5_pwr_idle_val),
  .o_l2_5_pwr_idle_ack (u_noc_top_to_u_l2_p_5__o_l2_5_pwr_idle_ack),
  .i_l2_5_pwr_idle_req (u_l2_p_5_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_5_rst_n (u_l2_p_5_to_u_noc_top__o_noc_rst_n),
  .o_l2_5_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_araddr),
  .o_l2_5_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arburst),
  .o_l2_5_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arcache),
  .o_l2_5_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arid),
  .o_l2_5_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arlen),
  .o_l2_5_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arlock),
  .o_l2_5_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arprot),
  .i_l2_5_targ_ht_axi_m_arready (u_l2_p_5_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_5_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arsize),
  .o_l2_5_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_arvalid),
  .i_l2_5_targ_ht_axi_m_rdata (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_5_targ_ht_axi_m_rid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_5_targ_ht_axi_m_rlast (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_5_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_rready),
  .i_l2_5_targ_ht_axi_m_rresp (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_5_targ_ht_axi_m_rvalid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_5_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awaddr),
  .o_l2_5_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awburst),
  .o_l2_5_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awcache),
  .o_l2_5_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awid),
  .o_l2_5_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awlen),
  .o_l2_5_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awlock),
  .o_l2_5_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awprot),
  .i_l2_5_targ_ht_axi_m_awready (u_l2_p_5_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_5_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awsize),
  .o_l2_5_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_awvalid),
  .i_l2_5_targ_ht_axi_m_bid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_5_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_bready),
  .i_l2_5_targ_ht_axi_m_bresp (u_l2_p_5_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_5_targ_ht_axi_m_bvalid (u_l2_p_5_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_5_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wdata),
  .o_l2_5_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wlast),
  .i_l2_5_targ_ht_axi_m_wready (u_l2_p_5_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_5_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wstrb),
  .o_l2_5_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_5__o_l2_5_targ_ht_axi_m_wvalid),
  .o_l2_5_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_paddr),
  .o_l2_5_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_penable),
  .o_l2_5_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pprot),
  .i_l2_5_targ_syscfg_apb_m_prdata (u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_5_targ_syscfg_apb_m_pready (u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_5_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_psel),
  .i_l2_5_targ_syscfg_apb_m_pslverr (u_l2_p_5_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_5_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pstrb),
  .o_l2_5_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pwdata),
  .o_l2_5_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_5__o_l2_5_targ_syscfg_apb_m_pwrite),
  .i_l2_6_aon_clk (i_ref_clk),
  .i_l2_6_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_6_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_6_clken (u_l2_p_6_to_u_noc_top__o_noc_clken),
  .o_l2_6_pwr_idle_val (u_noc_top_to_u_l2_p_6__o_l2_6_pwr_idle_val),
  .o_l2_6_pwr_idle_ack (u_noc_top_to_u_l2_p_6__o_l2_6_pwr_idle_ack),
  .i_l2_6_pwr_idle_req (u_l2_p_6_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_6_rst_n (u_l2_p_6_to_u_noc_top__o_noc_rst_n),
  .o_l2_6_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_araddr),
  .o_l2_6_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arburst),
  .o_l2_6_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arcache),
  .o_l2_6_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arid),
  .o_l2_6_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arlen),
  .o_l2_6_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arlock),
  .o_l2_6_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arprot),
  .i_l2_6_targ_ht_axi_m_arready (u_l2_p_6_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_6_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arsize),
  .o_l2_6_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_arvalid),
  .i_l2_6_targ_ht_axi_m_rdata (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_6_targ_ht_axi_m_rid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_6_targ_ht_axi_m_rlast (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_6_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_rready),
  .i_l2_6_targ_ht_axi_m_rresp (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_6_targ_ht_axi_m_rvalid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_6_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awaddr),
  .o_l2_6_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awburst),
  .o_l2_6_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awcache),
  .o_l2_6_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awid),
  .o_l2_6_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awlen),
  .o_l2_6_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awlock),
  .o_l2_6_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awprot),
  .i_l2_6_targ_ht_axi_m_awready (u_l2_p_6_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_6_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awsize),
  .o_l2_6_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_awvalid),
  .i_l2_6_targ_ht_axi_m_bid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_6_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_bready),
  .i_l2_6_targ_ht_axi_m_bresp (u_l2_p_6_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_6_targ_ht_axi_m_bvalid (u_l2_p_6_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_6_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wdata),
  .o_l2_6_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wlast),
  .i_l2_6_targ_ht_axi_m_wready (u_l2_p_6_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_6_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wstrb),
  .o_l2_6_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_6__o_l2_6_targ_ht_axi_m_wvalid),
  .o_l2_6_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_paddr),
  .o_l2_6_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_penable),
  .o_l2_6_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pprot),
  .i_l2_6_targ_syscfg_apb_m_prdata (u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_6_targ_syscfg_apb_m_pready (u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_6_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_psel),
  .i_l2_6_targ_syscfg_apb_m_pslverr (u_l2_p_6_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_6_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pstrb),
  .o_l2_6_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pwdata),
  .o_l2_6_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_6__o_l2_6_targ_syscfg_apb_m_pwrite),
  .i_l2_7_aon_clk (i_ref_clk),
  .i_l2_7_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_l2_7_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_l2_7_clken (u_l2_p_7_to_u_noc_top__o_noc_clken),
  .o_l2_7_pwr_idle_val (u_noc_top_to_u_l2_p_7__o_l2_7_pwr_idle_val),
  .o_l2_7_pwr_idle_ack (u_noc_top_to_u_l2_p_7__o_l2_7_pwr_idle_ack),
  .i_l2_7_pwr_idle_req (u_l2_p_7_to_u_noc_top__o_noc_async_idle_req),
  .i_l2_7_rst_n (u_l2_p_7_to_u_noc_top__o_noc_rst_n),
  .o_l2_7_targ_ht_axi_m_araddr (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_araddr),
  .o_l2_7_targ_ht_axi_m_arburst (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arburst),
  .o_l2_7_targ_ht_axi_m_arcache (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arcache),
  .o_l2_7_targ_ht_axi_m_arid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arid),
  .o_l2_7_targ_ht_axi_m_arlen (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arlen),
  .o_l2_7_targ_ht_axi_m_arlock (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arlock),
  .o_l2_7_targ_ht_axi_m_arprot (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arprot),
  .i_l2_7_targ_ht_axi_m_arready (u_l2_p_7_to_u_noc_top__o_ht_axi_s_arready),
  .o_l2_7_targ_ht_axi_m_arsize (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arsize),
  .o_l2_7_targ_ht_axi_m_arvalid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_arvalid),
  .i_l2_7_targ_ht_axi_m_rdata (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rdata),
  .i_l2_7_targ_ht_axi_m_rid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rid),
  .i_l2_7_targ_ht_axi_m_rlast (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rlast),
  .o_l2_7_targ_ht_axi_m_rready (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_rready),
  .i_l2_7_targ_ht_axi_m_rresp (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rresp),
  .i_l2_7_targ_ht_axi_m_rvalid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_rvalid),
  .o_l2_7_targ_ht_axi_m_awaddr (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awaddr),
  .o_l2_7_targ_ht_axi_m_awburst (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awburst),
  .o_l2_7_targ_ht_axi_m_awcache (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awcache),
  .o_l2_7_targ_ht_axi_m_awid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awid),
  .o_l2_7_targ_ht_axi_m_awlen (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awlen),
  .o_l2_7_targ_ht_axi_m_awlock (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awlock),
  .o_l2_7_targ_ht_axi_m_awprot (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awprot),
  .i_l2_7_targ_ht_axi_m_awready (u_l2_p_7_to_u_noc_top__o_ht_axi_s_awready),
  .o_l2_7_targ_ht_axi_m_awsize (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awsize),
  .o_l2_7_targ_ht_axi_m_awvalid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_awvalid),
  .i_l2_7_targ_ht_axi_m_bid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_bid),
  .o_l2_7_targ_ht_axi_m_bready (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_bready),
  .i_l2_7_targ_ht_axi_m_bresp (u_l2_p_7_to_u_noc_top__o_ht_axi_s_bresp),
  .i_l2_7_targ_ht_axi_m_bvalid (u_l2_p_7_to_u_noc_top__o_ht_axi_s_bvalid),
  .o_l2_7_targ_ht_axi_m_wdata (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wdata),
  .o_l2_7_targ_ht_axi_m_wlast (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wlast),
  .i_l2_7_targ_ht_axi_m_wready (u_l2_p_7_to_u_noc_top__o_ht_axi_s_wready),
  .o_l2_7_targ_ht_axi_m_wstrb (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wstrb),
  .o_l2_7_targ_ht_axi_m_wvalid (u_noc_top_to_u_l2_p_7__o_l2_7_targ_ht_axi_m_wvalid),
  .o_l2_7_targ_syscfg_apb_m_paddr (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_paddr),
  .o_l2_7_targ_syscfg_apb_m_penable (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_penable),
  .o_l2_7_targ_syscfg_apb_m_pprot (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pprot),
  .i_l2_7_targ_syscfg_apb_m_prdata (u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_l2_7_targ_syscfg_apb_m_pready (u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_l2_7_targ_syscfg_apb_m_psel (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_psel),
  .i_l2_7_targ_syscfg_apb_m_pslverr (u_l2_p_7_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_l2_7_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pstrb),
  .o_l2_7_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pwdata),
  .o_l2_7_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_l2_p_7__o_l2_7_targ_syscfg_apb_m_pwrite),
  .i_l2_addr_mode_port_b0 ('1),
  .i_l2_addr_mode_port_b1 ('0),
  .i_l2_intr_mode_port_b0 ('1),
  .i_l2_intr_mode_port_b1 ('1),
  .i_lpddr_graph_0_aon_clk (i_ref_clk),
  .i_lpddr_graph_0_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_graph_0_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_lpddr_graph_0_clken (u_lpddr_p_graph_0_to_u_noc_top__o_noc_clken),
  .o_lpddr_graph_0_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_pwr_idle_vec_val),
  .o_lpddr_graph_0_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_pwr_idle_vec_ack),
  .i_lpddr_graph_0_pwr_idle_vec_req (u_lpddr_p_graph_0_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_graph_0_rst_n (u_lpddr_p_graph_0_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_graph_0_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_paddr),
  .o_lpddr_graph_0_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_penable),
  .o_lpddr_graph_0_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pprot),
  .i_lpddr_graph_0_targ_cfg_apb_m_prdata (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_graph_0_targ_cfg_apb_m_pready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_graph_0_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_psel),
  .i_lpddr_graph_0_targ_cfg_apb_m_pslverr (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_graph_0_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pstrb),
  .o_lpddr_graph_0_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pwdata),
  .o_lpddr_graph_0_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_cfg_apb_m_pwrite),
  .o_lpddr_graph_0_targ_ht_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_araddr),
  .o_lpddr_graph_0_targ_ht_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arburst),
  .o_lpddr_graph_0_targ_ht_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arcache),
  .o_lpddr_graph_0_targ_ht_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arid),
  .o_lpddr_graph_0_targ_ht_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arlen),
  .o_lpddr_graph_0_targ_ht_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arlock),
  .o_lpddr_graph_0_targ_ht_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arprot),
  .o_lpddr_graph_0_targ_ht_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arqos),
  .i_lpddr_graph_0_targ_ht_axi_m_arready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_graph_0_targ_ht_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arsize),
  .o_lpddr_graph_0_targ_ht_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_arvalid),
  .o_lpddr_graph_0_targ_ht_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awaddr),
  .o_lpddr_graph_0_targ_ht_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awburst),
  .o_lpddr_graph_0_targ_ht_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awcache),
  .o_lpddr_graph_0_targ_ht_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awid),
  .o_lpddr_graph_0_targ_ht_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awlen),
  .o_lpddr_graph_0_targ_ht_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awlock),
  .o_lpddr_graph_0_targ_ht_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awprot),
  .o_lpddr_graph_0_targ_ht_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awqos),
  .i_lpddr_graph_0_targ_ht_axi_m_awready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_graph_0_targ_ht_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awsize),
  .o_lpddr_graph_0_targ_ht_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_awvalid),
  .i_lpddr_graph_0_targ_ht_axi_m_bid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_graph_0_targ_ht_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_bready),
  .i_lpddr_graph_0_targ_ht_axi_m_bresp (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_graph_0_targ_ht_axi_m_bvalid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_graph_0_targ_ht_axi_m_rdata (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_graph_0_targ_ht_axi_m_rid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_graph_0_targ_ht_axi_m_rlast (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_graph_0_targ_ht_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_rready),
  .i_lpddr_graph_0_targ_ht_axi_m_rresp (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_graph_0_targ_ht_axi_m_rvalid (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_graph_0_targ_ht_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wdata),
  .o_lpddr_graph_0_targ_ht_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wlast),
  .i_lpddr_graph_0_targ_ht_axi_m_wready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_graph_0_targ_ht_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wstrb),
  .o_lpddr_graph_0_targ_ht_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_ht_axi_m_wvalid),
  .o_lpddr_graph_0_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_paddr),
  .o_lpddr_graph_0_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_penable),
  .o_lpddr_graph_0_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pprot),
  .i_lpddr_graph_0_targ_syscfg_apb_m_prdata (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_graph_0_targ_syscfg_apb_m_pready (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_graph_0_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_psel),
  .i_lpddr_graph_0_targ_syscfg_apb_m_pslverr (u_lpddr_p_graph_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_graph_0_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pstrb),
  .o_lpddr_graph_0_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pwdata),
  .o_lpddr_graph_0_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_0__o_lpddr_graph_0_targ_syscfg_apb_m_pwrite),
  .i_lpddr_graph_1_aon_clk (i_ref_clk),
  .i_lpddr_graph_1_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_graph_1_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_lpddr_graph_1_clken (u_lpddr_p_graph_1_to_u_noc_top__o_noc_clken),
  .o_lpddr_graph_1_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_pwr_idle_vec_val),
  .o_lpddr_graph_1_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_pwr_idle_vec_ack),
  .i_lpddr_graph_1_pwr_idle_vec_req (u_lpddr_p_graph_1_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_graph_1_rst_n (u_lpddr_p_graph_1_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_graph_1_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_paddr),
  .o_lpddr_graph_1_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_penable),
  .o_lpddr_graph_1_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pprot),
  .i_lpddr_graph_1_targ_cfg_apb_m_prdata (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_graph_1_targ_cfg_apb_m_pready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_graph_1_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_psel),
  .i_lpddr_graph_1_targ_cfg_apb_m_pslverr (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_graph_1_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pstrb),
  .o_lpddr_graph_1_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pwdata),
  .o_lpddr_graph_1_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_cfg_apb_m_pwrite),
  .o_lpddr_graph_1_targ_ht_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_araddr),
  .o_lpddr_graph_1_targ_ht_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arburst),
  .o_lpddr_graph_1_targ_ht_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arcache),
  .o_lpddr_graph_1_targ_ht_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arid),
  .o_lpddr_graph_1_targ_ht_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arlen),
  .o_lpddr_graph_1_targ_ht_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arlock),
  .o_lpddr_graph_1_targ_ht_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arprot),
  .o_lpddr_graph_1_targ_ht_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arqos),
  .i_lpddr_graph_1_targ_ht_axi_m_arready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_graph_1_targ_ht_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arsize),
  .o_lpddr_graph_1_targ_ht_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_arvalid),
  .o_lpddr_graph_1_targ_ht_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awaddr),
  .o_lpddr_graph_1_targ_ht_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awburst),
  .o_lpddr_graph_1_targ_ht_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awcache),
  .o_lpddr_graph_1_targ_ht_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awid),
  .o_lpddr_graph_1_targ_ht_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awlen),
  .o_lpddr_graph_1_targ_ht_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awlock),
  .o_lpddr_graph_1_targ_ht_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awprot),
  .o_lpddr_graph_1_targ_ht_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awqos),
  .i_lpddr_graph_1_targ_ht_axi_m_awready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_graph_1_targ_ht_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awsize),
  .o_lpddr_graph_1_targ_ht_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_awvalid),
  .i_lpddr_graph_1_targ_ht_axi_m_bid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_graph_1_targ_ht_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_bready),
  .i_lpddr_graph_1_targ_ht_axi_m_bresp (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_graph_1_targ_ht_axi_m_bvalid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_graph_1_targ_ht_axi_m_rdata (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_graph_1_targ_ht_axi_m_rid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_graph_1_targ_ht_axi_m_rlast (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_graph_1_targ_ht_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_rready),
  .i_lpddr_graph_1_targ_ht_axi_m_rresp (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_graph_1_targ_ht_axi_m_rvalid (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_graph_1_targ_ht_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wdata),
  .o_lpddr_graph_1_targ_ht_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wlast),
  .i_lpddr_graph_1_targ_ht_axi_m_wready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_graph_1_targ_ht_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wstrb),
  .o_lpddr_graph_1_targ_ht_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_ht_axi_m_wvalid),
  .o_lpddr_graph_1_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_paddr),
  .o_lpddr_graph_1_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_penable),
  .o_lpddr_graph_1_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pprot),
  .i_lpddr_graph_1_targ_syscfg_apb_m_prdata (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_graph_1_targ_syscfg_apb_m_pready (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_graph_1_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_psel),
  .i_lpddr_graph_1_targ_syscfg_apb_m_pslverr (u_lpddr_p_graph_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_graph_1_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pstrb),
  .o_lpddr_graph_1_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pwdata),
  .o_lpddr_graph_1_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_1__o_lpddr_graph_1_targ_syscfg_apb_m_pwrite),
  .i_lpddr_graph_2_aon_clk (i_ref_clk),
  .i_lpddr_graph_2_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_graph_2_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_lpddr_graph_2_clken (u_lpddr_p_graph_2_to_u_noc_top__o_noc_clken),
  .o_lpddr_graph_2_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_pwr_idle_vec_val),
  .o_lpddr_graph_2_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_pwr_idle_vec_ack),
  .i_lpddr_graph_2_pwr_idle_vec_req (u_lpddr_p_graph_2_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_graph_2_rst_n (u_lpddr_p_graph_2_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_graph_2_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_paddr),
  .o_lpddr_graph_2_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_penable),
  .o_lpddr_graph_2_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pprot),
  .i_lpddr_graph_2_targ_cfg_apb_m_prdata (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_graph_2_targ_cfg_apb_m_pready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_graph_2_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_psel),
  .i_lpddr_graph_2_targ_cfg_apb_m_pslverr (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_graph_2_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pstrb),
  .o_lpddr_graph_2_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pwdata),
  .o_lpddr_graph_2_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_cfg_apb_m_pwrite),
  .o_lpddr_graph_2_targ_ht_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_araddr),
  .o_lpddr_graph_2_targ_ht_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arburst),
  .o_lpddr_graph_2_targ_ht_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arcache),
  .o_lpddr_graph_2_targ_ht_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arid),
  .o_lpddr_graph_2_targ_ht_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arlen),
  .o_lpddr_graph_2_targ_ht_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arlock),
  .o_lpddr_graph_2_targ_ht_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arprot),
  .o_lpddr_graph_2_targ_ht_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arqos),
  .i_lpddr_graph_2_targ_ht_axi_m_arready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_graph_2_targ_ht_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arsize),
  .o_lpddr_graph_2_targ_ht_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_arvalid),
  .o_lpddr_graph_2_targ_ht_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awaddr),
  .o_lpddr_graph_2_targ_ht_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awburst),
  .o_lpddr_graph_2_targ_ht_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awcache),
  .o_lpddr_graph_2_targ_ht_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awid),
  .o_lpddr_graph_2_targ_ht_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awlen),
  .o_lpddr_graph_2_targ_ht_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awlock),
  .o_lpddr_graph_2_targ_ht_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awprot),
  .o_lpddr_graph_2_targ_ht_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awqos),
  .i_lpddr_graph_2_targ_ht_axi_m_awready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_graph_2_targ_ht_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awsize),
  .o_lpddr_graph_2_targ_ht_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_awvalid),
  .i_lpddr_graph_2_targ_ht_axi_m_bid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_graph_2_targ_ht_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_bready),
  .i_lpddr_graph_2_targ_ht_axi_m_bresp (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_graph_2_targ_ht_axi_m_bvalid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_graph_2_targ_ht_axi_m_rdata (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_graph_2_targ_ht_axi_m_rid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_graph_2_targ_ht_axi_m_rlast (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_graph_2_targ_ht_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_rready),
  .i_lpddr_graph_2_targ_ht_axi_m_rresp (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_graph_2_targ_ht_axi_m_rvalid (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_graph_2_targ_ht_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wdata),
  .o_lpddr_graph_2_targ_ht_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wlast),
  .i_lpddr_graph_2_targ_ht_axi_m_wready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_graph_2_targ_ht_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wstrb),
  .o_lpddr_graph_2_targ_ht_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_ht_axi_m_wvalid),
  .o_lpddr_graph_2_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_paddr),
  .o_lpddr_graph_2_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_penable),
  .o_lpddr_graph_2_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pprot),
  .i_lpddr_graph_2_targ_syscfg_apb_m_prdata (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_graph_2_targ_syscfg_apb_m_pready (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_graph_2_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_psel),
  .i_lpddr_graph_2_targ_syscfg_apb_m_pslverr (u_lpddr_p_graph_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_graph_2_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pstrb),
  .o_lpddr_graph_2_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pwdata),
  .o_lpddr_graph_2_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_2__o_lpddr_graph_2_targ_syscfg_apb_m_pwrite),
  .i_lpddr_graph_3_aon_clk (i_ref_clk),
  .i_lpddr_graph_3_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_graph_3_clk (u_ddr_west_clock_gen_p_to_multi__o_ddr_west_clk),
  .i_lpddr_graph_3_clken (u_lpddr_p_graph_3_to_u_noc_top__o_noc_clken),
  .o_lpddr_graph_3_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_pwr_idle_vec_val),
  .o_lpddr_graph_3_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_pwr_idle_vec_ack),
  .i_lpddr_graph_3_pwr_idle_vec_req (u_lpddr_p_graph_3_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_graph_3_rst_n (u_lpddr_p_graph_3_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_graph_3_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_paddr),
  .o_lpddr_graph_3_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_penable),
  .o_lpddr_graph_3_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pprot),
  .i_lpddr_graph_3_targ_cfg_apb_m_prdata (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_graph_3_targ_cfg_apb_m_pready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_graph_3_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_psel),
  .i_lpddr_graph_3_targ_cfg_apb_m_pslverr (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_graph_3_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pstrb),
  .o_lpddr_graph_3_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pwdata),
  .o_lpddr_graph_3_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_cfg_apb_m_pwrite),
  .o_lpddr_graph_3_targ_ht_axi_m_araddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_araddr),
  .o_lpddr_graph_3_targ_ht_axi_m_arburst (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arburst),
  .o_lpddr_graph_3_targ_ht_axi_m_arcache (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arcache),
  .o_lpddr_graph_3_targ_ht_axi_m_arid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arid),
  .o_lpddr_graph_3_targ_ht_axi_m_arlen (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arlen),
  .o_lpddr_graph_3_targ_ht_axi_m_arlock (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arlock),
  .o_lpddr_graph_3_targ_ht_axi_m_arprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arprot),
  .o_lpddr_graph_3_targ_ht_axi_m_arqos (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arqos),
  .i_lpddr_graph_3_targ_ht_axi_m_arready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_graph_3_targ_ht_axi_m_arsize (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arsize),
  .o_lpddr_graph_3_targ_ht_axi_m_arvalid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_arvalid),
  .o_lpddr_graph_3_targ_ht_axi_m_awaddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awaddr),
  .o_lpddr_graph_3_targ_ht_axi_m_awburst (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awburst),
  .o_lpddr_graph_3_targ_ht_axi_m_awcache (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awcache),
  .o_lpddr_graph_3_targ_ht_axi_m_awid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awid),
  .o_lpddr_graph_3_targ_ht_axi_m_awlen (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awlen),
  .o_lpddr_graph_3_targ_ht_axi_m_awlock (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awlock),
  .o_lpddr_graph_3_targ_ht_axi_m_awprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awprot),
  .o_lpddr_graph_3_targ_ht_axi_m_awqos (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awqos),
  .i_lpddr_graph_3_targ_ht_axi_m_awready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_graph_3_targ_ht_axi_m_awsize (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awsize),
  .o_lpddr_graph_3_targ_ht_axi_m_awvalid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_awvalid),
  .i_lpddr_graph_3_targ_ht_axi_m_bid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_graph_3_targ_ht_axi_m_bready (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_bready),
  .i_lpddr_graph_3_targ_ht_axi_m_bresp (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_graph_3_targ_ht_axi_m_bvalid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_graph_3_targ_ht_axi_m_rdata (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_graph_3_targ_ht_axi_m_rid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_graph_3_targ_ht_axi_m_rlast (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_graph_3_targ_ht_axi_m_rready (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_rready),
  .i_lpddr_graph_3_targ_ht_axi_m_rresp (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_graph_3_targ_ht_axi_m_rvalid (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_graph_3_targ_ht_axi_m_wdata (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wdata),
  .o_lpddr_graph_3_targ_ht_axi_m_wlast (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wlast),
  .i_lpddr_graph_3_targ_ht_axi_m_wready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_graph_3_targ_ht_axi_m_wstrb (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wstrb),
  .o_lpddr_graph_3_targ_ht_axi_m_wvalid (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_ht_axi_m_wvalid),
  .o_lpddr_graph_3_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_paddr),
  .o_lpddr_graph_3_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_penable),
  .o_lpddr_graph_3_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pprot),
  .i_lpddr_graph_3_targ_syscfg_apb_m_prdata (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_graph_3_targ_syscfg_apb_m_pready (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_graph_3_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_psel),
  .i_lpddr_graph_3_targ_syscfg_apb_m_pslverr (u_lpddr_p_graph_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_graph_3_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pstrb),
  .o_lpddr_graph_3_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pwdata),
  .o_lpddr_graph_3_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_graph_3__o_lpddr_graph_3_targ_syscfg_apb_m_pwrite),
  .i_lpddr_graph_addr_mode_port_b0 ('1),
  .i_lpddr_graph_addr_mode_port_b1 ('0),
  .i_lpddr_graph_intr_mode_port_b0 ('1),
  .i_lpddr_graph_intr_mode_port_b1 ('1),
  .i_lpddr_ppp_0_aon_clk (i_ref_clk),
  .i_lpddr_ppp_0_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_ppp_0_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_lpddr_ppp_0_clken (u_lpddr_p_ppp_0_to_u_noc_top__o_noc_clken),
  .o_lpddr_ppp_0_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_pwr_idle_vec_val),
  .o_lpddr_ppp_0_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_pwr_idle_vec_ack),
  .i_lpddr_ppp_0_pwr_idle_vec_req (u_lpddr_p_ppp_0_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_ppp_0_rst_n (u_lpddr_p_ppp_0_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_ppp_0_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_paddr),
  .o_lpddr_ppp_0_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_penable),
  .o_lpddr_ppp_0_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pprot),
  .i_lpddr_ppp_0_targ_cfg_apb_m_prdata (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_ppp_0_targ_cfg_apb_m_pready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_ppp_0_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_psel),
  .i_lpddr_ppp_0_targ_cfg_apb_m_pslverr (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_ppp_0_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pstrb),
  .o_lpddr_ppp_0_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pwdata),
  .o_lpddr_ppp_0_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_cfg_apb_m_pwrite),
  .o_lpddr_ppp_0_targ_mt_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_araddr),
  .o_lpddr_ppp_0_targ_mt_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arburst),
  .o_lpddr_ppp_0_targ_mt_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arcache),
  .o_lpddr_ppp_0_targ_mt_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arid),
  .o_lpddr_ppp_0_targ_mt_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arlen),
  .o_lpddr_ppp_0_targ_mt_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arlock),
  .o_lpddr_ppp_0_targ_mt_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arprot),
  .o_lpddr_ppp_0_targ_mt_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arqos),
  .i_lpddr_ppp_0_targ_mt_axi_m_arready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_ppp_0_targ_mt_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arsize),
  .o_lpddr_ppp_0_targ_mt_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_arvalid),
  .o_lpddr_ppp_0_targ_mt_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awaddr),
  .o_lpddr_ppp_0_targ_mt_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awburst),
  .o_lpddr_ppp_0_targ_mt_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awcache),
  .o_lpddr_ppp_0_targ_mt_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awid),
  .o_lpddr_ppp_0_targ_mt_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awlen),
  .o_lpddr_ppp_0_targ_mt_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awlock),
  .o_lpddr_ppp_0_targ_mt_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awprot),
  .o_lpddr_ppp_0_targ_mt_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awqos),
  .i_lpddr_ppp_0_targ_mt_axi_m_awready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_ppp_0_targ_mt_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awsize),
  .o_lpddr_ppp_0_targ_mt_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_awvalid),
  .i_lpddr_ppp_0_targ_mt_axi_m_bid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_ppp_0_targ_mt_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_bready),
  .i_lpddr_ppp_0_targ_mt_axi_m_bresp (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_ppp_0_targ_mt_axi_m_bvalid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_ppp_0_targ_mt_axi_m_rdata (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_ppp_0_targ_mt_axi_m_rid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_ppp_0_targ_mt_axi_m_rlast (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_ppp_0_targ_mt_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_rready),
  .i_lpddr_ppp_0_targ_mt_axi_m_rresp (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_ppp_0_targ_mt_axi_m_rvalid (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_ppp_0_targ_mt_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wdata),
  .o_lpddr_ppp_0_targ_mt_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wlast),
  .i_lpddr_ppp_0_targ_mt_axi_m_wready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_ppp_0_targ_mt_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wstrb),
  .o_lpddr_ppp_0_targ_mt_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_mt_axi_m_wvalid),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_paddr),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_penable),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pprot),
  .i_lpddr_ppp_0_targ_syscfg_apb_m_prdata (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_ppp_0_targ_syscfg_apb_m_pready (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_psel),
  .i_lpddr_ppp_0_targ_syscfg_apb_m_pslverr (u_lpddr_p_ppp_0_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pstrb),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pwdata),
  .o_lpddr_ppp_0_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_0__o_lpddr_ppp_0_targ_syscfg_apb_m_pwrite),
  .i_lpddr_ppp_1_aon_clk (i_ref_clk),
  .i_lpddr_ppp_1_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_ppp_1_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_lpddr_ppp_1_clken (u_lpddr_p_ppp_1_to_u_noc_top__o_noc_clken),
  .o_lpddr_ppp_1_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_pwr_idle_vec_val),
  .o_lpddr_ppp_1_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_pwr_idle_vec_ack),
  .i_lpddr_ppp_1_pwr_idle_vec_req (u_lpddr_p_ppp_1_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_ppp_1_rst_n (u_lpddr_p_ppp_1_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_ppp_1_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_paddr),
  .o_lpddr_ppp_1_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_penable),
  .o_lpddr_ppp_1_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pprot),
  .i_lpddr_ppp_1_targ_cfg_apb_m_prdata (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_ppp_1_targ_cfg_apb_m_pready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_ppp_1_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_psel),
  .i_lpddr_ppp_1_targ_cfg_apb_m_pslverr (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_ppp_1_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pstrb),
  .o_lpddr_ppp_1_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pwdata),
  .o_lpddr_ppp_1_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_cfg_apb_m_pwrite),
  .o_lpddr_ppp_1_targ_mt_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_araddr),
  .o_lpddr_ppp_1_targ_mt_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arburst),
  .o_lpddr_ppp_1_targ_mt_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arcache),
  .o_lpddr_ppp_1_targ_mt_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arid),
  .o_lpddr_ppp_1_targ_mt_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arlen),
  .o_lpddr_ppp_1_targ_mt_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arlock),
  .o_lpddr_ppp_1_targ_mt_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arprot),
  .o_lpddr_ppp_1_targ_mt_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arqos),
  .i_lpddr_ppp_1_targ_mt_axi_m_arready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_ppp_1_targ_mt_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arsize),
  .o_lpddr_ppp_1_targ_mt_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_arvalid),
  .o_lpddr_ppp_1_targ_mt_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awaddr),
  .o_lpddr_ppp_1_targ_mt_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awburst),
  .o_lpddr_ppp_1_targ_mt_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awcache),
  .o_lpddr_ppp_1_targ_mt_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awid),
  .o_lpddr_ppp_1_targ_mt_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awlen),
  .o_lpddr_ppp_1_targ_mt_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awlock),
  .o_lpddr_ppp_1_targ_mt_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awprot),
  .o_lpddr_ppp_1_targ_mt_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awqos),
  .i_lpddr_ppp_1_targ_mt_axi_m_awready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_ppp_1_targ_mt_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awsize),
  .o_lpddr_ppp_1_targ_mt_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_awvalid),
  .i_lpddr_ppp_1_targ_mt_axi_m_bid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_ppp_1_targ_mt_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_bready),
  .i_lpddr_ppp_1_targ_mt_axi_m_bresp (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_ppp_1_targ_mt_axi_m_bvalid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_ppp_1_targ_mt_axi_m_rdata (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_ppp_1_targ_mt_axi_m_rid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_ppp_1_targ_mt_axi_m_rlast (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_ppp_1_targ_mt_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_rready),
  .i_lpddr_ppp_1_targ_mt_axi_m_rresp (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_ppp_1_targ_mt_axi_m_rvalid (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_ppp_1_targ_mt_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wdata),
  .o_lpddr_ppp_1_targ_mt_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wlast),
  .i_lpddr_ppp_1_targ_mt_axi_m_wready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_ppp_1_targ_mt_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wstrb),
  .o_lpddr_ppp_1_targ_mt_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_mt_axi_m_wvalid),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_paddr),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_penable),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pprot),
  .i_lpddr_ppp_1_targ_syscfg_apb_m_prdata (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_ppp_1_targ_syscfg_apb_m_pready (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_psel),
  .i_lpddr_ppp_1_targ_syscfg_apb_m_pslverr (u_lpddr_p_ppp_1_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pstrb),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pwdata),
  .o_lpddr_ppp_1_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_1__o_lpddr_ppp_1_targ_syscfg_apb_m_pwrite),
  .i_lpddr_ppp_2_aon_clk (i_ref_clk),
  .i_lpddr_ppp_2_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_ppp_2_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_lpddr_ppp_2_clken (u_lpddr_p_ppp_2_to_u_noc_top__o_noc_clken),
  .o_lpddr_ppp_2_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_pwr_idle_vec_val),
  .o_lpddr_ppp_2_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_pwr_idle_vec_ack),
  .i_lpddr_ppp_2_pwr_idle_vec_req (u_lpddr_p_ppp_2_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_ppp_2_rst_n (u_lpddr_p_ppp_2_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_ppp_2_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_paddr),
  .o_lpddr_ppp_2_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_penable),
  .o_lpddr_ppp_2_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pprot),
  .i_lpddr_ppp_2_targ_cfg_apb_m_prdata (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_ppp_2_targ_cfg_apb_m_pready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_ppp_2_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_psel),
  .i_lpddr_ppp_2_targ_cfg_apb_m_pslverr (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_ppp_2_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pstrb),
  .o_lpddr_ppp_2_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pwdata),
  .o_lpddr_ppp_2_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_cfg_apb_m_pwrite),
  .o_lpddr_ppp_2_targ_mt_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_araddr),
  .o_lpddr_ppp_2_targ_mt_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arburst),
  .o_lpddr_ppp_2_targ_mt_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arcache),
  .o_lpddr_ppp_2_targ_mt_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arid),
  .o_lpddr_ppp_2_targ_mt_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arlen),
  .o_lpddr_ppp_2_targ_mt_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arlock),
  .o_lpddr_ppp_2_targ_mt_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arprot),
  .o_lpddr_ppp_2_targ_mt_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arqos),
  .i_lpddr_ppp_2_targ_mt_axi_m_arready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_ppp_2_targ_mt_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arsize),
  .o_lpddr_ppp_2_targ_mt_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_arvalid),
  .o_lpddr_ppp_2_targ_mt_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awaddr),
  .o_lpddr_ppp_2_targ_mt_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awburst),
  .o_lpddr_ppp_2_targ_mt_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awcache),
  .o_lpddr_ppp_2_targ_mt_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awid),
  .o_lpddr_ppp_2_targ_mt_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awlen),
  .o_lpddr_ppp_2_targ_mt_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awlock),
  .o_lpddr_ppp_2_targ_mt_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awprot),
  .o_lpddr_ppp_2_targ_mt_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awqos),
  .i_lpddr_ppp_2_targ_mt_axi_m_awready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_ppp_2_targ_mt_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awsize),
  .o_lpddr_ppp_2_targ_mt_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_awvalid),
  .i_lpddr_ppp_2_targ_mt_axi_m_bid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_ppp_2_targ_mt_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_bready),
  .i_lpddr_ppp_2_targ_mt_axi_m_bresp (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_ppp_2_targ_mt_axi_m_bvalid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_ppp_2_targ_mt_axi_m_rdata (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_ppp_2_targ_mt_axi_m_rid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_ppp_2_targ_mt_axi_m_rlast (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_ppp_2_targ_mt_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_rready),
  .i_lpddr_ppp_2_targ_mt_axi_m_rresp (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_ppp_2_targ_mt_axi_m_rvalid (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_ppp_2_targ_mt_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wdata),
  .o_lpddr_ppp_2_targ_mt_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wlast),
  .i_lpddr_ppp_2_targ_mt_axi_m_wready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_ppp_2_targ_mt_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wstrb),
  .o_lpddr_ppp_2_targ_mt_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_mt_axi_m_wvalid),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_paddr),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_penable),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pprot),
  .i_lpddr_ppp_2_targ_syscfg_apb_m_prdata (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_ppp_2_targ_syscfg_apb_m_pready (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_psel),
  .i_lpddr_ppp_2_targ_syscfg_apb_m_pslverr (u_lpddr_p_ppp_2_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pstrb),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pwdata),
  .o_lpddr_ppp_2_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_2__o_lpddr_ppp_2_targ_syscfg_apb_m_pwrite),
  .i_lpddr_ppp_3_aon_clk (i_ref_clk),
  .i_lpddr_ppp_3_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lpddr_ppp_3_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .i_lpddr_ppp_3_clken (u_lpddr_p_ppp_3_to_u_noc_top__o_noc_clken),
  .o_lpddr_ppp_3_pwr_idle_vec_val (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_pwr_idle_vec_val),
  .o_lpddr_ppp_3_pwr_idle_vec_ack (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_pwr_idle_vec_ack),
  .i_lpddr_ppp_3_pwr_idle_vec_req (u_lpddr_p_ppp_3_to_u_noc_top__o_noc_async_idle_req),
  .i_lpddr_ppp_3_rst_n (u_lpddr_p_ppp_3_to_u_noc_top__o_noc_rst_n),
  .o_lpddr_ppp_3_targ_cfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_paddr),
  .o_lpddr_ppp_3_targ_cfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_penable),
  .o_lpddr_ppp_3_targ_cfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pprot),
  .i_lpddr_ppp_3_targ_cfg_apb_m_prdata (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_prdata),
  .i_lpddr_ppp_3_targ_cfg_apb_m_pready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pready),
  .o_lpddr_ppp_3_targ_cfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_psel),
  .i_lpddr_ppp_3_targ_cfg_apb_m_pslverr (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_cfg_apb4_s_pslverr),
  .o_lpddr_ppp_3_targ_cfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pstrb),
  .o_lpddr_ppp_3_targ_cfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pwdata),
  .o_lpddr_ppp_3_targ_cfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_cfg_apb_m_pwrite),
  .o_lpddr_ppp_3_targ_mt_axi_m_araddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_araddr),
  .o_lpddr_ppp_3_targ_mt_axi_m_arburst (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arburst),
  .o_lpddr_ppp_3_targ_mt_axi_m_arcache (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arcache),
  .o_lpddr_ppp_3_targ_mt_axi_m_arid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arid),
  .o_lpddr_ppp_3_targ_mt_axi_m_arlen (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arlen),
  .o_lpddr_ppp_3_targ_mt_axi_m_arlock (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arlock),
  .o_lpddr_ppp_3_targ_mt_axi_m_arprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arprot),
  .o_lpddr_ppp_3_targ_mt_axi_m_arqos (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arqos),
  .i_lpddr_ppp_3_targ_mt_axi_m_arready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_arready),
  .o_lpddr_ppp_3_targ_mt_axi_m_arsize (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arsize),
  .o_lpddr_ppp_3_targ_mt_axi_m_arvalid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_arvalid),
  .o_lpddr_ppp_3_targ_mt_axi_m_awaddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awaddr),
  .o_lpddr_ppp_3_targ_mt_axi_m_awburst (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awburst),
  .o_lpddr_ppp_3_targ_mt_axi_m_awcache (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awcache),
  .o_lpddr_ppp_3_targ_mt_axi_m_awid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awid),
  .o_lpddr_ppp_3_targ_mt_axi_m_awlen (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awlen),
  .o_lpddr_ppp_3_targ_mt_axi_m_awlock (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awlock),
  .o_lpddr_ppp_3_targ_mt_axi_m_awprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awprot),
  .o_lpddr_ppp_3_targ_mt_axi_m_awqos (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awqos),
  .i_lpddr_ppp_3_targ_mt_axi_m_awready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_awready),
  .o_lpddr_ppp_3_targ_mt_axi_m_awsize (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awsize),
  .o_lpddr_ppp_3_targ_mt_axi_m_awvalid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_awvalid),
  .i_lpddr_ppp_3_targ_mt_axi_m_bid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bid),
  .o_lpddr_ppp_3_targ_mt_axi_m_bready (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_bready),
  .i_lpddr_ppp_3_targ_mt_axi_m_bresp (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bresp),
  .i_lpddr_ppp_3_targ_mt_axi_m_bvalid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_bvalid),
  .i_lpddr_ppp_3_targ_mt_axi_m_rdata (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rdata),
  .i_lpddr_ppp_3_targ_mt_axi_m_rid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rid),
  .i_lpddr_ppp_3_targ_mt_axi_m_rlast (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rlast),
  .o_lpddr_ppp_3_targ_mt_axi_m_rready (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_rready),
  .i_lpddr_ppp_3_targ_mt_axi_m_rresp (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rresp),
  .i_lpddr_ppp_3_targ_mt_axi_m_rvalid (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_rvalid),
  .o_lpddr_ppp_3_targ_mt_axi_m_wdata (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wdata),
  .o_lpddr_ppp_3_targ_mt_axi_m_wlast (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wlast),
  .i_lpddr_ppp_3_targ_mt_axi_m_wready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_axi_m_wready),
  .o_lpddr_ppp_3_targ_mt_axi_m_wstrb (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wstrb),
  .o_lpddr_ppp_3_targ_mt_axi_m_wvalid (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_mt_axi_m_wvalid),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_paddr (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_paddr),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_penable (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_penable),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_pprot (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pprot),
  .i_lpddr_ppp_3_targ_syscfg_apb_m_prdata (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_prdata),
  .i_lpddr_ppp_3_targ_syscfg_apb_m_pready (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pready),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_psel (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_psel),
  .i_lpddr_ppp_3_targ_syscfg_apb_m_pslverr (u_lpddr_p_ppp_3_to_u_noc_top__o_lpddr_syscfg_apb4_s_pslverr),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pstrb),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pwdata),
  .o_lpddr_ppp_3_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_lpddr_p_ppp_3__o_lpddr_ppp_3_targ_syscfg_apb_m_pwrite),
  .i_lpddr_ppp_addr_mode_port_b0 ('1),
  .i_lpddr_ppp_addr_mode_port_b1 ('0),
  .i_lpddr_ppp_intr_mode_port_b0 ('1),
  .i_lpddr_ppp_intr_mode_port_b1 ('1),
  .i_noc_clk (u_soc_mgmt_p_to_u_noc_top__o_noc_clk),
  .i_noc_rst_n (u_soc_mgmt_p_to_u_noc_top__o_noc_rst_n),
  .i_pcie_aon_clk (i_ref_clk),
  .i_pcie_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_pcie_init_mt_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .i_pcie_init_mt_clken (u_pcie_p_to_u_noc_top__o_noc_init_mt_axi_clken),
  .o_pcie_init_mt_pwr_idle_val (u_noc_top_to_u_pcie_p__o_pcie_init_mt_pwr_idle_val),
  .o_pcie_init_mt_pwr_idle_ack (u_noc_top_to_u_pcie_p__o_pcie_init_mt_pwr_idle_ack),
  .i_pcie_init_mt_pwr_idle_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_init_mt_axi_req),
  .i_pcie_init_mt_axi_s_araddr (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_araddr),
  .i_pcie_init_mt_axi_s_arburst (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arburst),
  .i_pcie_init_mt_axi_s_arcache (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arcache),
  .i_pcie_init_mt_axi_s_arid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arid),
  .i_pcie_init_mt_axi_s_arlen (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arlen),
  .i_pcie_init_mt_axi_s_arlock (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arlock),
  .i_pcie_init_mt_axi_s_arprot (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arprot),
  .i_pcie_init_mt_axi_s_arqos (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arqos),
  .o_pcie_init_mt_axi_s_arready (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_arready),
  .i_pcie_init_mt_axi_s_arsize (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arsize),
  .i_pcie_init_mt_axi_s_arvalid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arvalid),
  .o_pcie_init_mt_axi_s_rdata (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rdata),
  .o_pcie_init_mt_axi_s_rid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rid),
  .o_pcie_init_mt_axi_s_rlast (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rlast),
  .i_pcie_init_mt_axi_s_rready (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_rready),
  .o_pcie_init_mt_axi_s_rresp (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rresp),
  .o_pcie_init_mt_axi_s_rvalid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rvalid),
  .i_pcie_init_mt_rst_n (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_rst_n),
  .i_pcie_init_mt_axi_s_awaddr (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awaddr),
  .i_pcie_init_mt_axi_s_awburst (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awburst),
  .i_pcie_init_mt_axi_s_awcache (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awcache),
  .i_pcie_init_mt_axi_s_awid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awid),
  .i_pcie_init_mt_axi_s_awlen (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awlen),
  .i_pcie_init_mt_axi_s_awlock (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awlock),
  .i_pcie_init_mt_axi_s_awprot (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awprot),
  .i_pcie_init_mt_axi_s_awqos (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awqos),
  .o_pcie_init_mt_axi_s_awready (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_awready),
  .i_pcie_init_mt_axi_s_awsize (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awsize),
  .i_pcie_init_mt_axi_s_awvalid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awvalid),
  .o_pcie_init_mt_axi_s_bid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bid),
  .i_pcie_init_mt_axi_s_bready (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_bready),
  .o_pcie_init_mt_axi_s_bresp (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bresp),
  .o_pcie_init_mt_axi_s_bvalid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bvalid),
  .i_pcie_init_mt_axi_s_wdata (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wdata),
  .i_pcie_init_mt_axi_s_wlast (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wlast),
  .o_pcie_init_mt_axi_s_wready (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_wready),
  .i_pcie_init_mt_axi_s_wstrb (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wstrb),
  .i_pcie_init_mt_axi_s_wvalid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wvalid),
  .o_pcie_targ_cfg_apb_m_paddr (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_paddr),
  .o_pcie_targ_cfg_apb_m_penable (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_penable),
  .o_pcie_targ_cfg_apb_m_pprot (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pprot),
  .i_pcie_targ_cfg_apb_m_prdata (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_prdata),
  .i_pcie_targ_cfg_apb_m_pready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_pready),
  .o_pcie_targ_cfg_apb_m_psel (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_psel),
  .i_pcie_targ_cfg_apb_m_pslverr (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_pslverr),
  .o_pcie_targ_cfg_apb_m_pstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pstrb),
  .o_pcie_targ_cfg_apb_m_pwdata (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pwdata),
  .o_pcie_targ_cfg_apb_m_pwrite (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pwrite),
  .i_pcie_targ_cfg_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .i_pcie_targ_cfg_clken (u_pcie_p_to_u_noc_top__o_noc_targ_cfg_apb_clken),
  .o_pcie_targ_cfg_dbi_axi_m_araddr (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_araddr),
  .o_pcie_targ_cfg_dbi_axi_m_arburst (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arburst),
  .o_pcie_targ_cfg_dbi_axi_m_arcache (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arcache),
  .o_pcie_targ_cfg_dbi_axi_m_arid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arid),
  .o_pcie_targ_cfg_dbi_axi_m_arlen (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arlen),
  .o_pcie_targ_cfg_dbi_axi_m_arlock (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arlock),
  .o_pcie_targ_cfg_dbi_axi_m_arprot (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arprot),
  .o_pcie_targ_cfg_dbi_axi_m_arqos (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arqos),
  .i_pcie_targ_cfg_dbi_axi_m_arready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_arready),
  .o_pcie_targ_cfg_dbi_axi_m_arsize (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arsize),
  .o_pcie_targ_cfg_dbi_axi_m_arvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arvalid),
  .o_pcie_targ_cfg_dbi_axi_m_awaddr (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awaddr),
  .o_pcie_targ_cfg_dbi_axi_m_awburst (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awburst),
  .o_pcie_targ_cfg_dbi_axi_m_awcache (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awcache),
  .o_pcie_targ_cfg_dbi_axi_m_awid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awid),
  .o_pcie_targ_cfg_dbi_axi_m_awlen (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awlen),
  .o_pcie_targ_cfg_dbi_axi_m_awlock (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awlock),
  .o_pcie_targ_cfg_dbi_axi_m_awprot (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awprot),
  .o_pcie_targ_cfg_dbi_axi_m_awqos (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awqos),
  .i_pcie_targ_cfg_dbi_axi_m_awready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_awready),
  .o_pcie_targ_cfg_dbi_axi_m_awsize (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awsize),
  .o_pcie_targ_cfg_dbi_axi_m_awvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awvalid),
  .i_pcie_targ_cfg_dbi_axi_m_bid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bid),
  .o_pcie_targ_cfg_dbi_axi_m_bready (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_bready),
  .i_pcie_targ_cfg_dbi_axi_m_bresp (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bresp),
  .i_pcie_targ_cfg_dbi_axi_m_bvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bvalid),
  .i_pcie_targ_cfg_dbi_axi_m_rdata (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rdata),
  .i_pcie_targ_cfg_dbi_axi_m_rid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rid),
  .i_pcie_targ_cfg_dbi_axi_m_rlast (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rlast),
  .o_pcie_targ_cfg_dbi_axi_m_rready (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_rready),
  .i_pcie_targ_cfg_dbi_axi_m_rresp (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rresp),
  .i_pcie_targ_cfg_dbi_axi_m_rvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rvalid),
  .o_pcie_targ_cfg_dbi_axi_m_wdata (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wdata),
  .o_pcie_targ_cfg_dbi_axi_m_wlast (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wlast),
  .i_pcie_targ_cfg_dbi_axi_m_wready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_wready),
  .o_pcie_targ_cfg_dbi_axi_m_wstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wstrb),
  .o_pcie_targ_cfg_dbi_axi_m_wvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wvalid),
  .i_pcie_targ_cfg_dbi_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .i_pcie_targ_cfg_dbi_clken (u_pcie_p_to_u_noc_top__o_noc_targ_cfg_dbi_axi_clken),
  .o_pcie_targ_cfg_dbi_pwr_idle_val (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_pwr_idle_val),
  .o_pcie_targ_cfg_dbi_pwr_idle_ack (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_pwr_idle_ack),
  .i_pcie_targ_cfg_dbi_pwr_idle_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_cfg_dbi_axi_req),
  .i_pcie_targ_cfg_dbi_rst_n (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rst_n),
  .o_pcie_targ_cfg_pwr_idle_val (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_pwr_idle_val),
  .o_pcie_targ_cfg_pwr_idle_ack (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_pwr_idle_ack),
  .i_pcie_targ_cfg_pwr_idle_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_cfg_apb_req),
  .i_pcie_targ_cfg_rst_n (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_rst_n),
  .i_pcie_targ_mt_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .i_pcie_targ_mt_clken (u_pcie_p_to_u_noc_top__o_noc_targ_mt_axi_clken),
  .o_pcie_targ_mt_pwr_idle_val (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_pwr_idle_val),
  .o_pcie_targ_mt_pwr_idle_ack (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_pwr_idle_ack),
  .i_pcie_targ_mt_pwr_idle_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_mt_axi_req),
  .o_pcie_targ_mt_axi_m_araddr (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_araddr),
  .o_pcie_targ_mt_axi_m_arburst (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arburst),
  .o_pcie_targ_mt_axi_m_arcache (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arcache),
  .o_pcie_targ_mt_axi_m_arid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arid),
  .o_pcie_targ_mt_axi_m_arlen (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arlen),
  .o_pcie_targ_mt_axi_m_arlock (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arlock),
  .o_pcie_targ_mt_axi_m_arprot (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arprot),
  .o_pcie_targ_mt_axi_m_arqos (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arqos),
  .i_pcie_targ_mt_axi_m_arready (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_arready),
  .o_pcie_targ_mt_axi_m_arsize (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arsize),
  .o_pcie_targ_mt_axi_m_arvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arvalid),
  .i_pcie_targ_mt_axi_m_rdata (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rdata),
  .i_pcie_targ_mt_axi_m_rid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rid),
  .i_pcie_targ_mt_axi_m_rlast (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rlast),
  .o_pcie_targ_mt_axi_m_rready (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_rready),
  .i_pcie_targ_mt_axi_m_rresp (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rresp),
  .i_pcie_targ_mt_axi_m_rvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rvalid),
  .i_pcie_targ_mt_rst_n (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rst_n),
  .o_pcie_targ_mt_axi_m_awaddr (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awaddr),
  .o_pcie_targ_mt_axi_m_awburst (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awburst),
  .o_pcie_targ_mt_axi_m_awcache (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awcache),
  .o_pcie_targ_mt_axi_m_awid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awid),
  .o_pcie_targ_mt_axi_m_awlen (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awlen),
  .o_pcie_targ_mt_axi_m_awlock (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awlock),
  .o_pcie_targ_mt_axi_m_awprot (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awprot),
  .o_pcie_targ_mt_axi_m_awqos (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awqos),
  .i_pcie_targ_mt_axi_m_awready (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_awready),
  .o_pcie_targ_mt_axi_m_awsize (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awsize),
  .o_pcie_targ_mt_axi_m_awvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awvalid),
  .i_pcie_targ_mt_axi_m_bid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bid),
  .o_pcie_targ_mt_axi_m_bready (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_bready),
  .i_pcie_targ_mt_axi_m_bresp (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bresp),
  .i_pcie_targ_mt_axi_m_bvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bvalid),
  .o_pcie_targ_mt_axi_m_wdata (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wdata),
  .o_pcie_targ_mt_axi_m_wlast (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wlast),
  .i_pcie_targ_mt_axi_m_wready (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_wready),
  .o_pcie_targ_mt_axi_m_wstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wstrb),
  .o_pcie_targ_mt_axi_m_wvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wvalid),
  .o_pcie_targ_syscfg_apb_m_paddr (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_paddr),
  .o_pcie_targ_syscfg_apb_m_penable (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_penable),
  .o_pcie_targ_syscfg_apb_m_pprot (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pprot),
  .i_pcie_targ_syscfg_apb_m_prdata (u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_prdata),
  .i_pcie_targ_syscfg_apb_m_pready (u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_pready),
  .o_pcie_targ_syscfg_apb_m_psel (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_psel),
  .i_pcie_targ_syscfg_apb_m_pslverr (u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_pslverr),
  .o_pcie_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pstrb),
  .o_pcie_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pwdata),
  .o_pcie_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pwrite),
  .i_pve_0_aon_clk (i_ref_clk),
  .i_pve_0_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_pve_0_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_pve_0_clken (u_pve_p_0_to_u_noc_top__o_noc_clken),
  .i_pve_0_init_ht_axi_s_araddr (u_pve_p_0_to_u_noc_top__o_dma_axi_m_araddr),
  .i_pve_0_init_ht_axi_s_arburst (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arburst),
  .i_pve_0_init_ht_axi_s_arcache (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arcache),
  .i_pve_0_init_ht_axi_s_arid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arid),
  .i_pve_0_init_ht_axi_s_arlen (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arlen),
  .i_pve_0_init_ht_axi_s_arlock (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arlock),
  .i_pve_0_init_ht_axi_s_arprot (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arprot),
  .o_pve_0_init_ht_axi_s_arready (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_arready),
  .i_pve_0_init_ht_axi_s_arsize (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arsize),
  .i_pve_0_init_ht_axi_s_arvalid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arvalid),
  .o_pve_0_init_ht_axi_s_rdata (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rdata),
  .o_pve_0_init_ht_axi_s_rid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rid),
  .o_pve_0_init_ht_axi_s_rlast (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rlast),
  .i_pve_0_init_ht_axi_s_rready (u_pve_p_0_to_u_noc_top__o_dma_axi_m_rready),
  .o_pve_0_init_ht_axi_s_rresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rresp),
  .o_pve_0_init_ht_axi_s_rvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rvalid),
  .i_pve_0_init_ht_axi_s_awaddr (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awaddr),
  .i_pve_0_init_ht_axi_s_awburst (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awburst),
  .i_pve_0_init_ht_axi_s_awcache (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awcache),
  .i_pve_0_init_ht_axi_s_awid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awid),
  .i_pve_0_init_ht_axi_s_awlen (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awlen),
  .i_pve_0_init_ht_axi_s_awlock (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awlock),
  .i_pve_0_init_ht_axi_s_awprot (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awprot),
  .o_pve_0_init_ht_axi_s_awready (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_awready),
  .i_pve_0_init_ht_axi_s_awsize (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awsize),
  .i_pve_0_init_ht_axi_s_awvalid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awvalid),
  .o_pve_0_init_ht_axi_s_bid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bid),
  .i_pve_0_init_ht_axi_s_bready (u_pve_p_0_to_u_noc_top__o_dma_axi_m_bready),
  .o_pve_0_init_ht_axi_s_bresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bresp),
  .o_pve_0_init_ht_axi_s_bvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bvalid),
  .i_pve_0_init_ht_axi_s_wdata (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wdata),
  .i_pve_0_init_ht_axi_s_wlast (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wlast),
  .o_pve_0_init_ht_axi_s_wready (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_wready),
  .i_pve_0_init_ht_axi_s_wstrb (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wstrb),
  .i_pve_0_init_ht_axi_s_wvalid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wvalid),
  .i_pve_0_init_lt_axi_s_araddr (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_araddr),
  .i_pve_0_init_lt_axi_s_arburst (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arburst),
  .i_pve_0_init_lt_axi_s_arcache (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arcache),
  .i_pve_0_init_lt_axi_s_arid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arid),
  .i_pve_0_init_lt_axi_s_arlen (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arlen),
  .i_pve_0_init_lt_axi_s_arlock (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arlock),
  .i_pve_0_init_lt_axi_s_arprot (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arprot),
  .i_pve_0_init_lt_axi_s_arqos (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arqos),
  .o_pve_0_init_lt_axi_s_arready (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_arready),
  .i_pve_0_init_lt_axi_s_arsize (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arsize),
  .i_pve_0_init_lt_axi_s_arvalid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arvalid),
  .o_pve_0_init_lt_axi_s_rdata (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rdata),
  .o_pve_0_init_lt_axi_s_rid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rid),
  .o_pve_0_init_lt_axi_s_rlast (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rlast),
  .i_pve_0_init_lt_axi_s_rready (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_rready),
  .o_pve_0_init_lt_axi_s_rresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rresp),
  .o_pve_0_init_lt_axi_s_rvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rvalid),
  .i_pve_0_init_lt_axi_s_awaddr (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awaddr),
  .i_pve_0_init_lt_axi_s_awburst (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awburst),
  .i_pve_0_init_lt_axi_s_awcache (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awcache),
  .i_pve_0_init_lt_axi_s_awid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awid),
  .i_pve_0_init_lt_axi_s_awlen (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awlen),
  .i_pve_0_init_lt_axi_s_awlock (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awlock),
  .i_pve_0_init_lt_axi_s_awprot (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awprot),
  .i_pve_0_init_lt_axi_s_awqos (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awqos),
  .o_pve_0_init_lt_axi_s_awready (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_awready),
  .i_pve_0_init_lt_axi_s_awsize (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awsize),
  .i_pve_0_init_lt_axi_s_awvalid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awvalid),
  .o_pve_0_init_lt_axi_s_bid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bid),
  .i_pve_0_init_lt_axi_s_bready (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_bready),
  .o_pve_0_init_lt_axi_s_bresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bresp),
  .o_pve_0_init_lt_axi_s_bvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bvalid),
  .i_pve_0_init_lt_axi_s_wdata (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wdata),
  .i_pve_0_init_lt_axi_s_wlast (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wlast),
  .o_pve_0_init_lt_axi_s_wready (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_wready),
  .i_pve_0_init_lt_axi_s_wstrb (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wstrb),
  .i_pve_0_init_lt_axi_s_wvalid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wvalid),
  .o_pve_0_pwr_idle_val (u_noc_top_to_u_pve_p_0__o_pve_0_pwr_idle_val),
  .o_pve_0_pwr_idle_ack (u_noc_top_to_u_pve_p_0__o_pve_0_pwr_idle_ack),
  .i_pve_0_pwr_idle_req (u_pve_p_0_to_u_noc_top__o_noc_async_idle_req),
  .i_pve_0_rst_n (u_pve_p_0_to_u_noc_top__o_noc_rst_n),
  .o_pve_0_targ_lt_axi_m_araddr (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_araddr),
  .o_pve_0_targ_lt_axi_m_arburst (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arburst),
  .o_pve_0_targ_lt_axi_m_arcache (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arcache),
  .o_pve_0_targ_lt_axi_m_arid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arid),
  .o_pve_0_targ_lt_axi_m_arlen (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arlen),
  .o_pve_0_targ_lt_axi_m_arlock (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arlock),
  .o_pve_0_targ_lt_axi_m_arprot (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arprot),
  .o_pve_0_targ_lt_axi_m_arqos (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arqos),
  .i_pve_0_targ_lt_axi_m_arready (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_arready),
  .o_pve_0_targ_lt_axi_m_arsize (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arsize),
  .o_pve_0_targ_lt_axi_m_arvalid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arvalid),
  .o_pve_0_targ_lt_axi_m_awaddr (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awaddr),
  .o_pve_0_targ_lt_axi_m_awburst (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awburst),
  .o_pve_0_targ_lt_axi_m_awcache (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awcache),
  .o_pve_0_targ_lt_axi_m_awid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awid),
  .o_pve_0_targ_lt_axi_m_awlen (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awlen),
  .o_pve_0_targ_lt_axi_m_awlock (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awlock),
  .o_pve_0_targ_lt_axi_m_awprot (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awprot),
  .o_pve_0_targ_lt_axi_m_awqos (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awqos),
  .i_pve_0_targ_lt_axi_m_awready (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_awready),
  .o_pve_0_targ_lt_axi_m_awsize (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awsize),
  .o_pve_0_targ_lt_axi_m_awvalid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awvalid),
  .i_pve_0_targ_lt_axi_m_bid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bid),
  .o_pve_0_targ_lt_axi_m_bready (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_bready),
  .i_pve_0_targ_lt_axi_m_bresp (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bresp),
  .i_pve_0_targ_lt_axi_m_bvalid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bvalid),
  .i_pve_0_targ_lt_axi_m_rdata (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rdata),
  .i_pve_0_targ_lt_axi_m_rid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rid),
  .i_pve_0_targ_lt_axi_m_rlast (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rlast),
  .o_pve_0_targ_lt_axi_m_rready (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_rready),
  .i_pve_0_targ_lt_axi_m_rresp (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rresp),
  .i_pve_0_targ_lt_axi_m_rvalid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rvalid),
  .o_pve_0_targ_lt_axi_m_wdata (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wdata),
  .o_pve_0_targ_lt_axi_m_wlast (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wlast),
  .i_pve_0_targ_lt_axi_m_wready (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_wready),
  .o_pve_0_targ_lt_axi_m_wstrb (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wstrb),
  .o_pve_0_targ_lt_axi_m_wvalid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wvalid),
  .o_pve_0_targ_syscfg_apb_m_paddr (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_paddr),
  .o_pve_0_targ_syscfg_apb_m_penable (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_penable),
  .o_pve_0_targ_syscfg_apb_m_pprot (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pprot),
  .i_pve_0_targ_syscfg_apb_m_prdata (u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_pve_0_targ_syscfg_apb_m_pready (u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_pve_0_targ_syscfg_apb_m_psel (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_psel),
  .i_pve_0_targ_syscfg_apb_m_pslverr (u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_pve_0_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pstrb),
  .o_pve_0_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pwdata),
  .o_pve_0_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pwrite),
  .i_pve_1_aon_clk (i_ref_clk),
  .i_pve_1_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_pve_1_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_pve_1_clken (u_pve_p_1_to_u_noc_top__o_noc_clken),
  .i_pve_1_init_ht_axi_s_araddr (u_pve_p_1_to_u_noc_top__o_dma_axi_m_araddr),
  .i_pve_1_init_ht_axi_s_arburst (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arburst),
  .i_pve_1_init_ht_axi_s_arcache (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arcache),
  .i_pve_1_init_ht_axi_s_arid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arid),
  .i_pve_1_init_ht_axi_s_arlen (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arlen),
  .i_pve_1_init_ht_axi_s_arlock (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arlock),
  .i_pve_1_init_ht_axi_s_arprot (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arprot),
  .o_pve_1_init_ht_axi_s_arready (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_arready),
  .i_pve_1_init_ht_axi_s_arsize (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arsize),
  .i_pve_1_init_ht_axi_s_arvalid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arvalid),
  .o_pve_1_init_ht_axi_s_rdata (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rdata),
  .o_pve_1_init_ht_axi_s_rid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rid),
  .o_pve_1_init_ht_axi_s_rlast (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rlast),
  .i_pve_1_init_ht_axi_s_rready (u_pve_p_1_to_u_noc_top__o_dma_axi_m_rready),
  .o_pve_1_init_ht_axi_s_rresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rresp),
  .o_pve_1_init_ht_axi_s_rvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rvalid),
  .i_pve_1_init_ht_axi_s_awaddr (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awaddr),
  .i_pve_1_init_ht_axi_s_awburst (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awburst),
  .i_pve_1_init_ht_axi_s_awcache (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awcache),
  .i_pve_1_init_ht_axi_s_awid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awid),
  .i_pve_1_init_ht_axi_s_awlen (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awlen),
  .i_pve_1_init_ht_axi_s_awlock (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awlock),
  .i_pve_1_init_ht_axi_s_awprot (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awprot),
  .o_pve_1_init_ht_axi_s_awready (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_awready),
  .i_pve_1_init_ht_axi_s_awsize (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awsize),
  .i_pve_1_init_ht_axi_s_awvalid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awvalid),
  .o_pve_1_init_ht_axi_s_bid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bid),
  .i_pve_1_init_ht_axi_s_bready (u_pve_p_1_to_u_noc_top__o_dma_axi_m_bready),
  .o_pve_1_init_ht_axi_s_bresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bresp),
  .o_pve_1_init_ht_axi_s_bvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bvalid),
  .i_pve_1_init_ht_axi_s_wdata (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wdata),
  .i_pve_1_init_ht_axi_s_wlast (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wlast),
  .o_pve_1_init_ht_axi_s_wready (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_wready),
  .i_pve_1_init_ht_axi_s_wstrb (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wstrb),
  .i_pve_1_init_ht_axi_s_wvalid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wvalid),
  .i_pve_1_init_lt_axi_s_araddr (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_araddr),
  .i_pve_1_init_lt_axi_s_arburst (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arburst),
  .i_pve_1_init_lt_axi_s_arcache (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arcache),
  .i_pve_1_init_lt_axi_s_arid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arid),
  .i_pve_1_init_lt_axi_s_arlen (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arlen),
  .i_pve_1_init_lt_axi_s_arlock (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arlock),
  .i_pve_1_init_lt_axi_s_arprot (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arprot),
  .i_pve_1_init_lt_axi_s_arqos (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arqos),
  .o_pve_1_init_lt_axi_s_arready (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_arready),
  .i_pve_1_init_lt_axi_s_arsize (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arsize),
  .i_pve_1_init_lt_axi_s_arvalid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arvalid),
  .o_pve_1_init_lt_axi_s_rdata (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rdata),
  .o_pve_1_init_lt_axi_s_rid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rid),
  .o_pve_1_init_lt_axi_s_rlast (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rlast),
  .i_pve_1_init_lt_axi_s_rready (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_rready),
  .o_pve_1_init_lt_axi_s_rresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rresp),
  .o_pve_1_init_lt_axi_s_rvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rvalid),
  .i_pve_1_init_lt_axi_s_awaddr (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awaddr),
  .i_pve_1_init_lt_axi_s_awburst (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awburst),
  .i_pve_1_init_lt_axi_s_awcache (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awcache),
  .i_pve_1_init_lt_axi_s_awid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awid),
  .i_pve_1_init_lt_axi_s_awlen (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awlen),
  .i_pve_1_init_lt_axi_s_awlock (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awlock),
  .i_pve_1_init_lt_axi_s_awprot (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awprot),
  .i_pve_1_init_lt_axi_s_awqos (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awqos),
  .o_pve_1_init_lt_axi_s_awready (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_awready),
  .i_pve_1_init_lt_axi_s_awsize (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awsize),
  .i_pve_1_init_lt_axi_s_awvalid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awvalid),
  .o_pve_1_init_lt_axi_s_bid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bid),
  .i_pve_1_init_lt_axi_s_bready (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_bready),
  .o_pve_1_init_lt_axi_s_bresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bresp),
  .o_pve_1_init_lt_axi_s_bvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bvalid),
  .i_pve_1_init_lt_axi_s_wdata (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wdata),
  .i_pve_1_init_lt_axi_s_wlast (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wlast),
  .o_pve_1_init_lt_axi_s_wready (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_wready),
  .i_pve_1_init_lt_axi_s_wstrb (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wstrb),
  .i_pve_1_init_lt_axi_s_wvalid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wvalid),
  .o_pve_1_pwr_idle_val (u_noc_top_to_u_pve_p_1__o_pve_1_pwr_idle_val),
  .o_pve_1_pwr_idle_ack (u_noc_top_to_u_pve_p_1__o_pve_1_pwr_idle_ack),
  .i_pve_1_pwr_idle_req (u_pve_p_1_to_u_noc_top__o_noc_async_idle_req),
  .i_pve_1_rst_n (u_pve_p_1_to_u_noc_top__o_noc_rst_n),
  .o_pve_1_targ_lt_axi_m_araddr (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_araddr),
  .o_pve_1_targ_lt_axi_m_arburst (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arburst),
  .o_pve_1_targ_lt_axi_m_arcache (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arcache),
  .o_pve_1_targ_lt_axi_m_arid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arid),
  .o_pve_1_targ_lt_axi_m_arlen (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arlen),
  .o_pve_1_targ_lt_axi_m_arlock (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arlock),
  .o_pve_1_targ_lt_axi_m_arprot (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arprot),
  .o_pve_1_targ_lt_axi_m_arqos (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arqos),
  .i_pve_1_targ_lt_axi_m_arready (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_arready),
  .o_pve_1_targ_lt_axi_m_arsize (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arsize),
  .o_pve_1_targ_lt_axi_m_arvalid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arvalid),
  .o_pve_1_targ_lt_axi_m_awaddr (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awaddr),
  .o_pve_1_targ_lt_axi_m_awburst (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awburst),
  .o_pve_1_targ_lt_axi_m_awcache (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awcache),
  .o_pve_1_targ_lt_axi_m_awid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awid),
  .o_pve_1_targ_lt_axi_m_awlen (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awlen),
  .o_pve_1_targ_lt_axi_m_awlock (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awlock),
  .o_pve_1_targ_lt_axi_m_awprot (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awprot),
  .o_pve_1_targ_lt_axi_m_awqos (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awqos),
  .i_pve_1_targ_lt_axi_m_awready (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_awready),
  .o_pve_1_targ_lt_axi_m_awsize (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awsize),
  .o_pve_1_targ_lt_axi_m_awvalid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awvalid),
  .i_pve_1_targ_lt_axi_m_bid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bid),
  .o_pve_1_targ_lt_axi_m_bready (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_bready),
  .i_pve_1_targ_lt_axi_m_bresp (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bresp),
  .i_pve_1_targ_lt_axi_m_bvalid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bvalid),
  .i_pve_1_targ_lt_axi_m_rdata (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rdata),
  .i_pve_1_targ_lt_axi_m_rid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rid),
  .i_pve_1_targ_lt_axi_m_rlast (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rlast),
  .o_pve_1_targ_lt_axi_m_rready (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_rready),
  .i_pve_1_targ_lt_axi_m_rresp (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rresp),
  .i_pve_1_targ_lt_axi_m_rvalid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rvalid),
  .o_pve_1_targ_lt_axi_m_wdata (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wdata),
  .o_pve_1_targ_lt_axi_m_wlast (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wlast),
  .i_pve_1_targ_lt_axi_m_wready (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_wready),
  .o_pve_1_targ_lt_axi_m_wstrb (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wstrb),
  .o_pve_1_targ_lt_axi_m_wvalid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wvalid),
  .o_pve_1_targ_syscfg_apb_m_paddr (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_paddr),
  .o_pve_1_targ_syscfg_apb_m_penable (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_penable),
  .o_pve_1_targ_syscfg_apb_m_pprot (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pprot),
  .i_pve_1_targ_syscfg_apb_m_prdata (u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_pve_1_targ_syscfg_apb_m_pready (u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_pve_1_targ_syscfg_apb_m_psel (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_psel),
  .i_pve_1_targ_syscfg_apb_m_pslverr (u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_pve_1_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pstrb),
  .o_pve_1_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pwdata),
  .o_pve_1_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pwrite),
  .i_soc_mgmt_aon_clk (i_ref_clk),
  .i_soc_mgmt_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_soc_mgmt_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .i_soc_mgmt_clken (1'b1),
  .i_soc_mgmt_init_lt_axi_s_araddr (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_araddr),
  .i_soc_mgmt_init_lt_axi_s_arburst (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arburst),
  .i_soc_mgmt_init_lt_axi_s_arcache (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arcache),
  .i_soc_mgmt_init_lt_axi_s_arid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arid),
  .i_soc_mgmt_init_lt_axi_s_arlen (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arlen),
  .i_soc_mgmt_init_lt_axi_s_arlock (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arlock),
  .i_soc_mgmt_init_lt_axi_s_arprot (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arprot),
  .i_soc_mgmt_init_lt_axi_s_arqos (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arqos),
  .o_soc_mgmt_init_lt_axi_s_arready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_arready),
  .i_soc_mgmt_init_lt_axi_s_arsize (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arsize),
  .i_soc_mgmt_init_lt_axi_s_arvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arvalid),
  .i_soc_mgmt_init_lt_axi_s_awaddr (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awaddr),
  .i_soc_mgmt_init_lt_axi_s_awburst (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awburst),
  .i_soc_mgmt_init_lt_axi_s_awcache (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awcache),
  .i_soc_mgmt_init_lt_axi_s_awid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awid),
  .i_soc_mgmt_init_lt_axi_s_awlen (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awlen),
  .i_soc_mgmt_init_lt_axi_s_awlock (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awlock),
  .i_soc_mgmt_init_lt_axi_s_awprot (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awprot),
  .i_soc_mgmt_init_lt_axi_s_awqos (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awqos),
  .o_soc_mgmt_init_lt_axi_s_awready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_awready),
  .i_soc_mgmt_init_lt_axi_s_awsize (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awsize),
  .i_soc_mgmt_init_lt_axi_s_awvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awvalid),
  .o_soc_mgmt_init_lt_axi_s_bid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bid),
  .i_soc_mgmt_init_lt_axi_s_bready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_bready),
  .o_soc_mgmt_init_lt_axi_s_bresp (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bresp),
  .o_soc_mgmt_init_lt_axi_s_bvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bvalid),
  .o_soc_mgmt_init_lt_axi_s_rdata (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rdata),
  .o_soc_mgmt_init_lt_axi_s_rid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rid),
  .o_soc_mgmt_init_lt_axi_s_rlast (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rlast),
  .i_soc_mgmt_init_lt_axi_s_rready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_rready),
  .o_soc_mgmt_init_lt_axi_s_rresp (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rresp),
  .o_soc_mgmt_init_lt_axi_s_rvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rvalid),
  .i_soc_mgmt_init_lt_axi_s_wdata (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wdata),
  .i_soc_mgmt_init_lt_axi_s_wlast (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wlast),
  .o_soc_mgmt_init_lt_axi_s_wready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_wready),
  .i_soc_mgmt_init_lt_axi_s_wstrb (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wstrb),
  .i_soc_mgmt_init_lt_axi_s_wvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wvalid),
  .o_soc_mgmt_pwr_idle_val (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_pwr_idle_val),
  .o_soc_mgmt_pwr_idle_ack (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_pwr_idle_ack),
  .i_soc_mgmt_pwr_idle_req (u_soc_mgmt_p_to_u_noc_top__o_noc_async_idle_req),
  .i_soc_mgmt_rst_n (u_soc_mgmt_p_to_u_noc_top__o_noc_rst_n),
  .o_soc_mgmt_targ_lt_axi_m_araddr (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_araddr),
  .o_soc_mgmt_targ_lt_axi_m_arburst (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arburst),
  .o_soc_mgmt_targ_lt_axi_m_arcache (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arcache),
  .o_soc_mgmt_targ_lt_axi_m_arid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arid),
  .o_soc_mgmt_targ_lt_axi_m_arlen (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arlen),
  .o_soc_mgmt_targ_lt_axi_m_arlock (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arlock),
  .o_soc_mgmt_targ_lt_axi_m_arprot (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arprot),
  .o_soc_mgmt_targ_lt_axi_m_arqos (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arqos),
  .i_soc_mgmt_targ_lt_axi_m_arready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_arready),
  .o_soc_mgmt_targ_lt_axi_m_arsize (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arsize),
  .o_soc_mgmt_targ_lt_axi_m_arvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arvalid),
  .o_soc_mgmt_targ_lt_axi_m_awaddr (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awaddr),
  .o_soc_mgmt_targ_lt_axi_m_awburst (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awburst),
  .o_soc_mgmt_targ_lt_axi_m_awcache (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awcache),
  .o_soc_mgmt_targ_lt_axi_m_awid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awid),
  .o_soc_mgmt_targ_lt_axi_m_awlen (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awlen),
  .o_soc_mgmt_targ_lt_axi_m_awlock (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awlock),
  .o_soc_mgmt_targ_lt_axi_m_awprot (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awprot),
  .o_soc_mgmt_targ_lt_axi_m_awqos (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awqos),
  .i_soc_mgmt_targ_lt_axi_m_awready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_awready),
  .o_soc_mgmt_targ_lt_axi_m_awsize (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awsize),
  .o_soc_mgmt_targ_lt_axi_m_awvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awvalid),
  .i_soc_mgmt_targ_lt_axi_m_bid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bid),
  .o_soc_mgmt_targ_lt_axi_m_bready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_bready),
  .i_soc_mgmt_targ_lt_axi_m_bresp (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bresp),
  .i_soc_mgmt_targ_lt_axi_m_bvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bvalid),
  .i_soc_mgmt_targ_lt_axi_m_rdata (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rdata),
  .i_soc_mgmt_targ_lt_axi_m_rid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rid),
  .i_soc_mgmt_targ_lt_axi_m_rlast (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rlast),
  .o_soc_mgmt_targ_lt_axi_m_rready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_rready),
  .i_soc_mgmt_targ_lt_axi_m_rresp (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rresp),
  .i_soc_mgmt_targ_lt_axi_m_rvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rvalid),
  .o_soc_mgmt_targ_lt_axi_m_wdata (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wdata),
  .o_soc_mgmt_targ_lt_axi_m_wlast (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wlast),
  .i_soc_mgmt_targ_lt_axi_m_wready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_wready),
  .o_soc_mgmt_targ_lt_axi_m_wstrb (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wstrb),
  .o_soc_mgmt_targ_lt_axi_m_wvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wvalid),
  .o_soc_mgmt_targ_syscfg_apb_m_paddr (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_paddr),
  .o_soc_mgmt_targ_syscfg_apb_m_penable (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_penable),
  .o_soc_mgmt_targ_syscfg_apb_m_pprot (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pprot),
  .i_soc_mgmt_targ_syscfg_apb_m_prdata (u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_prdata),
  .i_soc_mgmt_targ_syscfg_apb_m_pready (u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_pready),
  .o_soc_mgmt_targ_syscfg_apb_m_psel (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_psel),
  .i_soc_mgmt_targ_syscfg_apb_m_pslverr (u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_pslverr),
  .o_soc_mgmt_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pstrb),
  .o_soc_mgmt_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pwdata),
  .o_soc_mgmt_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pwrite),
  .i_soc_periph_aon_clk (i_ref_clk),
  .i_soc_periph_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_soc_periph_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .i_soc_periph_clken (u_soc_periph_p_to_u_noc_top__o_noc_clken),
  .i_soc_periph_init_lt_axi_s_araddr (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_araddr),
  .i_soc_periph_init_lt_axi_s_arburst (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arburst),
  .i_soc_periph_init_lt_axi_s_arcache (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arcache),
  .i_soc_periph_init_lt_axi_s_arid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arid),
  .i_soc_periph_init_lt_axi_s_arlen (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arlen),
  .i_soc_periph_init_lt_axi_s_arlock (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arlock),
  .i_soc_periph_init_lt_axi_s_arprot (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arprot),
  .i_soc_periph_init_lt_axi_s_arqos (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arqos),
  .o_soc_periph_init_lt_axi_s_arready (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_arready),
  .i_soc_periph_init_lt_axi_s_arsize (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arsize),
  .i_soc_periph_init_lt_axi_s_arvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arvalid),
  .i_soc_periph_init_lt_axi_s_awaddr (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awaddr),
  .i_soc_periph_init_lt_axi_s_awburst (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awburst),
  .i_soc_periph_init_lt_axi_s_awcache (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awcache),
  .i_soc_periph_init_lt_axi_s_awid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awid),
  .i_soc_periph_init_lt_axi_s_awlen (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awlen),
  .i_soc_periph_init_lt_axi_s_awlock (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awlock),
  .i_soc_periph_init_lt_axi_s_awprot (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awprot),
  .i_soc_periph_init_lt_axi_s_awqos (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awqos),
  .o_soc_periph_init_lt_axi_s_awready (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_awready),
  .i_soc_periph_init_lt_axi_s_awsize (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awsize),
  .i_soc_periph_init_lt_axi_s_awvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awvalid),
  .o_soc_periph_init_lt_axi_s_bid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bid),
  .i_soc_periph_init_lt_axi_s_bready (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_bready),
  .o_soc_periph_init_lt_axi_s_bresp (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bresp),
  .o_soc_periph_init_lt_axi_s_bvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bvalid),
  .o_soc_periph_init_lt_axi_s_rdata (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rdata),
  .o_soc_periph_init_lt_axi_s_rid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rid),
  .o_soc_periph_init_lt_axi_s_rlast (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rlast),
  .i_soc_periph_init_lt_axi_s_rready (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_rready),
  .o_soc_periph_init_lt_axi_s_rresp (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rresp),
  .o_soc_periph_init_lt_axi_s_rvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rvalid),
  .i_soc_periph_init_lt_axi_s_wdata (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wdata),
  .i_soc_periph_init_lt_axi_s_wlast (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wlast),
  .o_soc_periph_init_lt_axi_s_wready (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_wready),
  .i_soc_periph_init_lt_axi_s_wstrb (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wstrb),
  .i_soc_periph_init_lt_axi_s_wvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wvalid),
  .o_soc_periph_pwr_idle_val (u_noc_top_to_u_soc_periph_p__o_soc_periph_pwr_idle_val),
  .o_soc_periph_pwr_idle_ack (u_noc_top_to_u_soc_periph_p__o_soc_periph_pwr_idle_ack),
  .i_soc_periph_pwr_idle_req (u_soc_periph_p_to_u_noc_top__o_noc_async_idle_req),
  .i_soc_periph_rst_n (u_soc_periph_p_to_u_noc_top__o_noc_rst_n),
  .o_soc_periph_targ_lt_axi_m_araddr (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_araddr),
  .o_soc_periph_targ_lt_axi_m_arburst (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arburst),
  .o_soc_periph_targ_lt_axi_m_arcache (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arcache),
  .o_soc_periph_targ_lt_axi_m_arid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arid),
  .o_soc_periph_targ_lt_axi_m_arlen (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arlen),
  .o_soc_periph_targ_lt_axi_m_arlock (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arlock),
  .o_soc_periph_targ_lt_axi_m_arprot (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arprot),
  .o_soc_periph_targ_lt_axi_m_arqos (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arqos),
  .i_soc_periph_targ_lt_axi_m_arready (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_arready),
  .o_soc_periph_targ_lt_axi_m_arsize (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arsize),
  .o_soc_periph_targ_lt_axi_m_arvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arvalid),
  .o_soc_periph_targ_lt_axi_m_awaddr (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awaddr),
  .o_soc_periph_targ_lt_axi_m_awburst (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awburst),
  .o_soc_periph_targ_lt_axi_m_awcache (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awcache),
  .o_soc_periph_targ_lt_axi_m_awid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awid),
  .o_soc_periph_targ_lt_axi_m_awlen (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awlen),
  .o_soc_periph_targ_lt_axi_m_awlock (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awlock),
  .o_soc_periph_targ_lt_axi_m_awprot (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awprot),
  .o_soc_periph_targ_lt_axi_m_awqos (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awqos),
  .i_soc_periph_targ_lt_axi_m_awready (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_awready),
  .o_soc_periph_targ_lt_axi_m_awsize (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awsize),
  .o_soc_periph_targ_lt_axi_m_awvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awvalid),
  .i_soc_periph_targ_lt_axi_m_bid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bid),
  .o_soc_periph_targ_lt_axi_m_bready (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_bready),
  .i_soc_periph_targ_lt_axi_m_bresp (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bresp),
  .i_soc_periph_targ_lt_axi_m_bvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bvalid),
  .i_soc_periph_targ_lt_axi_m_rdata (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rdata),
  .i_soc_periph_targ_lt_axi_m_rid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rid),
  .i_soc_periph_targ_lt_axi_m_rlast (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rlast),
  .o_soc_periph_targ_lt_axi_m_rready (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_rready),
  .i_soc_periph_targ_lt_axi_m_rresp (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rresp),
  .i_soc_periph_targ_lt_axi_m_rvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rvalid),
  .o_soc_periph_targ_lt_axi_m_wdata (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wdata),
  .o_soc_periph_targ_lt_axi_m_wlast (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wlast),
  .i_soc_periph_targ_lt_axi_m_wready (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_wready),
  .o_soc_periph_targ_lt_axi_m_wstrb (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wstrb),
  .o_soc_periph_targ_lt_axi_m_wvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wvalid),
  .o_soc_periph_targ_syscfg_apb_m_paddr (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_paddr),
  .o_soc_periph_targ_syscfg_apb_m_penable (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_penable),
  .o_soc_periph_targ_syscfg_apb_m_pprot (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pprot),
  .i_soc_periph_targ_syscfg_apb_m_prdata (u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_soc_periph_targ_syscfg_apb_m_pready (u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_soc_periph_targ_syscfg_apb_m_psel (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_psel),
  .i_soc_periph_targ_syscfg_apb_m_pslverr (u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_soc_periph_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pstrb),
  .o_soc_periph_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pwdata),
  .o_soc_periph_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pwrite),
  .i_sys_spm_aon_clk (i_ref_clk),
  .i_sys_spm_aon_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_sys_spm_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_sys_spm_clken (u_sys_spm_p_to_u_noc_top__o_noc_clken),
  .o_sys_spm_pwr_idle_val (u_noc_top_to_u_sys_spm_p__o_sys_spm_pwr_idle_val),
  .o_sys_spm_pwr_idle_ack (u_noc_top_to_u_sys_spm_p__o_sys_spm_pwr_idle_ack),
  .i_sys_spm_pwr_idle_req (u_sys_spm_p_to_u_noc_top__o_noc_async_idle_req),
  .i_sys_spm_rst_n (u_sys_spm_p_to_u_noc_top__o_noc_rst_n),
  .o_sys_spm_targ_lt_axi_m_araddr (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_araddr),
  .o_sys_spm_targ_lt_axi_m_arburst (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arburst),
  .o_sys_spm_targ_lt_axi_m_arcache (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arcache),
  .o_sys_spm_targ_lt_axi_m_arid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arid),
  .o_sys_spm_targ_lt_axi_m_arlen (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arlen),
  .o_sys_spm_targ_lt_axi_m_arlock (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arlock),
  .o_sys_spm_targ_lt_axi_m_arprot (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arprot),
  .o_sys_spm_targ_lt_axi_m_arqos (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arqos),
  .i_sys_spm_targ_lt_axi_m_arready (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_arready),
  .o_sys_spm_targ_lt_axi_m_arsize (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arsize),
  .o_sys_spm_targ_lt_axi_m_arvalid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arvalid),
  .o_sys_spm_targ_lt_axi_m_awaddr (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awaddr),
  .o_sys_spm_targ_lt_axi_m_awburst (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awburst),
  .o_sys_spm_targ_lt_axi_m_awcache (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awcache),
  .o_sys_spm_targ_lt_axi_m_awid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awid),
  .o_sys_spm_targ_lt_axi_m_awlen (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awlen),
  .o_sys_spm_targ_lt_axi_m_awlock (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awlock),
  .o_sys_spm_targ_lt_axi_m_awprot (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awprot),
  .o_sys_spm_targ_lt_axi_m_awqos (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awqos),
  .i_sys_spm_targ_lt_axi_m_awready (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_awready),
  .o_sys_spm_targ_lt_axi_m_awsize (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awsize),
  .o_sys_spm_targ_lt_axi_m_awvalid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awvalid),
  .i_sys_spm_targ_lt_axi_m_bid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bid),
  .o_sys_spm_targ_lt_axi_m_bready (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_bready),
  .i_sys_spm_targ_lt_axi_m_bresp (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bresp),
  .i_sys_spm_targ_lt_axi_m_bvalid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bvalid),
  .i_sys_spm_targ_lt_axi_m_rdata (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rdata),
  .i_sys_spm_targ_lt_axi_m_rid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rid),
  .i_sys_spm_targ_lt_axi_m_rlast (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rlast),
  .o_sys_spm_targ_lt_axi_m_rready (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_rready),
  .i_sys_spm_targ_lt_axi_m_rresp (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rresp),
  .i_sys_spm_targ_lt_axi_m_rvalid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rvalid),
  .o_sys_spm_targ_lt_axi_m_wdata (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wdata),
  .o_sys_spm_targ_lt_axi_m_wlast (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wlast),
  .i_sys_spm_targ_lt_axi_m_wready (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_wready),
  .o_sys_spm_targ_lt_axi_m_wstrb (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wstrb),
  .o_sys_spm_targ_lt_axi_m_wvalid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wvalid),
  .o_sys_spm_targ_syscfg_apb_m_paddr (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_paddr),
  .o_sys_spm_targ_syscfg_apb_m_penable (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_penable),
  .o_sys_spm_targ_syscfg_apb_m_pprot (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pprot),
  .i_sys_spm_targ_syscfg_apb_m_prdata (u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .i_sys_spm_targ_syscfg_apb_m_pready (u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_sys_spm_targ_syscfg_apb_m_psel (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_psel),
  .i_sys_spm_targ_syscfg_apb_m_pslverr (u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_sys_spm_targ_syscfg_apb_m_pstrb (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pstrb),
  .o_sys_spm_targ_syscfg_apb_m_pwdata (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pwdata),
  .o_sys_spm_targ_syscfg_apb_m_pwrite (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pwrite)
);
`ifdef PCIE_P_STUB
pcie_p_stub u_pcie_p (
`else
pcie_p u_pcie_p (
`endif
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_async_idle_init_mt_axi_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_init_mt_axi_req),
  .o_noc_async_idle_targ_mt_axi_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_mt_axi_req),
  .o_noc_async_idle_targ_cfg_dbi_axi_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_cfg_dbi_axi_req),
  .o_noc_async_idle_targ_cfg_apb_req (u_pcie_p_to_u_noc_top__o_noc_async_idle_targ_cfg_apb_req),
  .i_noc_async_idle_init_mt_axi_ack (u_noc_top_to_u_pcie_p__o_pcie_init_mt_pwr_idle_ack),
  .i_noc_async_idle_targ_mt_axi_ack (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_pwr_idle_ack),
  .i_noc_async_idle_targ_cfg_dbi_axi_ack (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_pwr_idle_ack),
  .i_noc_async_idle_targ_cfg_apb_ack (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_pwr_idle_ack),
  .i_noc_async_idle_init_mt_axi_val (u_noc_top_to_u_pcie_p__o_pcie_init_mt_pwr_idle_val),
  .i_noc_async_idle_targ_mt_axi_val (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_pwr_idle_val),
  .i_noc_async_idle_targ_cfg_dbi_axi_val (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_pwr_idle_val),
  .i_noc_async_idle_targ_cfg_apb_val (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_pwr_idle_val),
  .o_noc_init_mt_axi_clken (u_pcie_p_to_u_noc_top__o_noc_init_mt_axi_clken),
  .o_noc_targ_mt_axi_clken (u_pcie_p_to_u_noc_top__o_noc_targ_mt_axi_clken),
  .o_noc_targ_cfg_dbi_axi_clken (u_pcie_p_to_u_noc_top__o_noc_targ_cfg_dbi_axi_clken),
  .o_noc_targ_cfg_apb_clken (u_pcie_p_to_u_noc_top__o_noc_targ_cfg_apb_clken),
  .i_pcie_aux_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .i_pcie_init_mt_axi_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .i_pcie_targ_mt_axi_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .i_pcie_targ_cfg_dbi_axi_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .o_pcie_init_mt_axi_rst_n (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_rst_n),
  .o_pcie_targ_mt_axi_rst_n (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rst_n),
  .o_pcie_targ_cfg_dbi_axi_rst_n (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rst_n),
  .i_pcie_targ_cfg_apb_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .o_pcie_targ_cfg_apb_rst_n (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_rst_n),
  .i_ref_alt_clk_p (u_soc_mgmt_p_to_multi__o_periph_clk),
  .io_pcie_resref (io_pcie_resref),
  .i_ref_pad_clk_p (i_ref_pad_clk_p),
  .i_ref_pad_clk_m (i_ref_pad_clk_m),
  .i_pcie_rxm_00 (i_pcie_rxm_00),
  .i_pcie_rxm_01 (i_pcie_rxm_01),
  .i_pcie_rxm_02 (i_pcie_rxm_02),
  .i_pcie_rxm_03 (i_pcie_rxm_03),
  .i_pcie_rxp_00 (i_pcie_rxp_00),
  .i_pcie_rxp_01 (i_pcie_rxp_01),
  .i_pcie_rxp_02 (i_pcie_rxp_02),
  .i_pcie_rxp_03 (i_pcie_rxp_03),
  .o_pcie_txm_00 (o_pcie_txm_00),
  .o_pcie_txm_01 (o_pcie_txm_01),
  .o_pcie_txm_02 (o_pcie_txm_02),
  .o_pcie_txm_03 (o_pcie_txm_03),
  .o_pcie_txp_00 (o_pcie_txp_00),
  .o_pcie_txp_01 (o_pcie_txp_01),
  .o_pcie_txp_02 (o_pcie_txp_02),
  .o_pcie_txp_03 (o_pcie_txp_03),
  .o_pcie_init_mt_axi_awvalid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awvalid),
  .o_pcie_init_mt_axi_awid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awid),
  .o_pcie_init_mt_axi_awaddr (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awaddr),
  .o_pcie_init_mt_axi_awlen (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awlen),
  .o_pcie_init_mt_axi_awsize (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awsize),
  .o_pcie_init_mt_axi_awburst (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awburst),
  .o_pcie_init_mt_axi_awlock (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awlock),
  .o_pcie_init_mt_axi_awcache (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awcache),
  .o_pcie_init_mt_axi_awprot (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awprot),
  .o_pcie_init_mt_axi_awqos (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_awqos),
  .o_pcie_init_mt_axi_awregion (),
  .o_pcie_init_mt_axi_awuser (),
  .i_pcie_init_mt_axi_awready (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_awready),
  .o_pcie_init_mt_axi_wvalid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wvalid),
  .o_pcie_init_mt_axi_wdata (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wdata),
  .o_pcie_init_mt_axi_wstrb (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wstrb),
  .o_pcie_init_mt_axi_wlast (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_wlast),
  .o_pcie_init_mt_axi_wuser (),
  .i_pcie_init_mt_axi_wready (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_wready),
  .i_pcie_init_mt_axi_bvalid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bvalid),
  .i_pcie_init_mt_axi_bid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bid),
  .i_pcie_init_mt_axi_bresp (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_bresp),
  .i_pcie_init_mt_axi_buser ('0),
  .o_pcie_init_mt_axi_bready (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_bready),
  .o_pcie_init_mt_axi_arvalid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arvalid),
  .o_pcie_init_mt_axi_arid (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arid),
  .o_pcie_init_mt_axi_araddr (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_araddr),
  .o_pcie_init_mt_axi_arlen (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arlen),
  .o_pcie_init_mt_axi_arsize (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arsize),
  .o_pcie_init_mt_axi_arburst (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arburst),
  .o_pcie_init_mt_axi_arlock (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arlock),
  .o_pcie_init_mt_axi_arcache (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arcache),
  .o_pcie_init_mt_axi_arprot (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arprot),
  .o_pcie_init_mt_axi_arqos (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_arqos),
  .o_pcie_init_mt_axi_arregion (),
  .o_pcie_init_mt_axi_aruser (),
  .i_pcie_init_mt_axi_arready (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_arready),
  .i_pcie_init_mt_axi_rvalid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rvalid),
  .i_pcie_init_mt_axi_rid (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rid),
  .i_pcie_init_mt_axi_rdata (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rdata),
  .i_pcie_init_mt_axi_rresp (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rresp),
  .i_pcie_init_mt_axi_rlast (u_noc_top_to_u_pcie_p__o_pcie_init_mt_axi_s_rlast),
  .i_pcie_init_mt_axi_ruser ('0),
  .o_pcie_init_mt_axi_rready (u_pcie_p_to_u_noc_top__o_pcie_init_mt_axi_rready),
  .i_pcie_targ_mt_axi_awvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awvalid),
  .i_pcie_targ_mt_axi_awid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awid),
  .i_pcie_targ_mt_axi_awaddr (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awaddr),
  .i_pcie_targ_mt_axi_awlen (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awlen),
  .i_pcie_targ_mt_axi_awsize (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awsize),
  .i_pcie_targ_mt_axi_awburst (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awburst),
  .i_pcie_targ_mt_axi_awlock (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awlock),
  .i_pcie_targ_mt_axi_awcache (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awcache),
  .i_pcie_targ_mt_axi_awprot (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awprot),
  .i_pcie_targ_mt_axi_awqos (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_awqos),
  .i_pcie_targ_mt_axi_awregion ('0),
  .i_pcie_targ_mt_axi_awuser ('0),
  .o_pcie_targ_mt_axi_awready (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_awready),
  .i_pcie_targ_mt_axi_wvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wvalid),
  .i_pcie_targ_mt_axi_wdata (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wdata),
  .i_pcie_targ_mt_axi_wstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wstrb),
  .i_pcie_targ_mt_axi_wlast (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_wlast),
  .i_pcie_targ_mt_axi_wuser ('0),
  .o_pcie_targ_mt_axi_wready (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_wready),
  .o_pcie_targ_mt_axi_bvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bvalid),
  .o_pcie_targ_mt_axi_bid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bid),
  .o_pcie_targ_mt_axi_bresp (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_bresp),
  .o_pcie_targ_mt_axi_buser (),
  .i_pcie_targ_mt_axi_bready (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_bready),
  .i_pcie_targ_mt_axi_arvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arvalid),
  .i_pcie_targ_mt_axi_arid (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arid),
  .i_pcie_targ_mt_axi_araddr (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_araddr),
  .i_pcie_targ_mt_axi_arlen (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arlen),
  .i_pcie_targ_mt_axi_arsize (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arsize),
  .i_pcie_targ_mt_axi_arburst (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arburst),
  .i_pcie_targ_mt_axi_arlock (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arlock),
  .i_pcie_targ_mt_axi_arcache (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arcache),
  .i_pcie_targ_mt_axi_arprot (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arprot),
  .i_pcie_targ_mt_axi_arqos (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_arqos),
  .i_pcie_targ_mt_axi_arregion ('0),
  .i_pcie_targ_mt_axi_aruser ('0),
  .o_pcie_targ_mt_axi_arready (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_arready),
  .o_pcie_targ_mt_axi_rvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rvalid),
  .o_pcie_targ_mt_axi_rid (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rid),
  .o_pcie_targ_mt_axi_rdata (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rdata),
  .o_pcie_targ_mt_axi_rresp (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rresp),
  .o_pcie_targ_mt_axi_rlast (u_pcie_p_to_u_noc_top__o_pcie_targ_mt_axi_rlast),
  .o_pcie_targ_mt_axi_ruser (),
  .i_pcie_targ_mt_axi_rready (u_noc_top_to_u_pcie_p__o_pcie_targ_mt_axi_m_rready),
  .i_pcie_targ_cfg_dbi_axi_awvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awvalid),
  .i_pcie_targ_cfg_dbi_axi_awid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awid),
  .i_pcie_targ_cfg_dbi_axi_awaddr (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awaddr),
  .i_pcie_targ_cfg_dbi_axi_awlen (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awlen),
  .i_pcie_targ_cfg_dbi_axi_awsize (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awsize),
  .i_pcie_targ_cfg_dbi_axi_awburst (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awburst),
  .i_pcie_targ_cfg_dbi_axi_awlock (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awlock),
  .i_pcie_targ_cfg_dbi_axi_awcache (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awcache),
  .i_pcie_targ_cfg_dbi_axi_awprot (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awprot),
  .i_pcie_targ_cfg_dbi_axi_awqos (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_awqos),
  .i_pcie_targ_cfg_dbi_axi_awregion ('0),
  .i_pcie_targ_cfg_dbi_axi_awuser ('0),
  .o_pcie_targ_cfg_dbi_axi_awready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_awready),
  .i_pcie_targ_cfg_dbi_axi_wvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wvalid),
  .i_pcie_targ_cfg_dbi_axi_wdata (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wdata),
  .i_pcie_targ_cfg_dbi_axi_wstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wstrb),
  .i_pcie_targ_cfg_dbi_axi_wlast (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_wlast),
  .i_pcie_targ_cfg_dbi_axi_wuser ('0),
  .o_pcie_targ_cfg_dbi_axi_wready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_wready),
  .o_pcie_targ_cfg_dbi_axi_bvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bvalid),
  .o_pcie_targ_cfg_dbi_axi_bid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bid),
  .o_pcie_targ_cfg_dbi_axi_bresp (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_bresp),
  .o_pcie_targ_cfg_dbi_axi_buser (),
  .i_pcie_targ_cfg_dbi_axi_bready (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_bready),
  .i_pcie_targ_cfg_dbi_axi_arvalid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arvalid),
  .i_pcie_targ_cfg_dbi_axi_arid (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arid),
  .i_pcie_targ_cfg_dbi_axi_araddr (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_araddr),
  .i_pcie_targ_cfg_dbi_axi_arlen (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arlen),
  .i_pcie_targ_cfg_dbi_axi_arsize (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arsize),
  .i_pcie_targ_cfg_dbi_axi_arburst (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arburst),
  .i_pcie_targ_cfg_dbi_axi_arlock (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arlock),
  .i_pcie_targ_cfg_dbi_axi_arcache (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arcache),
  .i_pcie_targ_cfg_dbi_axi_arprot (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arprot),
  .i_pcie_targ_cfg_dbi_axi_arqos (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_arqos),
  .i_pcie_targ_cfg_dbi_axi_arregion ('0),
  .i_pcie_targ_cfg_dbi_axi_aruser ('0),
  .o_pcie_targ_cfg_dbi_axi_arready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_arready),
  .o_pcie_targ_cfg_dbi_axi_rvalid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rvalid),
  .o_pcie_targ_cfg_dbi_axi_rid (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rid),
  .o_pcie_targ_cfg_dbi_axi_rdata (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rdata),
  .o_pcie_targ_cfg_dbi_axi_rresp (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rresp),
  .o_pcie_targ_cfg_dbi_axi_rlast (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_dbi_axi_rlast),
  .o_pcie_targ_cfg_dbi_axi_ruser (),
  .i_pcie_targ_cfg_dbi_axi_rready (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_dbi_axi_m_rready),
  .i_pcie_targ_cfg_apb_paddr (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_paddr),
  .i_pcie_targ_cfg_apb_pwdata (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pwdata),
  .i_pcie_targ_cfg_apb_pwrite (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pwrite),
  .i_pcie_targ_cfg_apb_psel (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_psel),
  .i_pcie_targ_cfg_apb_penable (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_penable),
  .i_pcie_targ_cfg_apb_pstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pstrb),
  .i_pcie_targ_cfg_apb_pprot (u_noc_top_to_u_pcie_p__o_pcie_targ_cfg_apb_m_pprot),
  .o_pcie_targ_cfg_apb_pready (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_pready),
  .o_pcie_targ_cfg_apb_prdata (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_prdata),
  .o_pcie_targ_cfg_apb_pslverr (u_pcie_p_to_u_noc_top__o_pcie_targ_cfg_apb_pslverr),
  .i_pcie_targ_syscfg_apb_paddr (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_paddr),
  .i_pcie_targ_syscfg_apb_pwdata (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pwdata),
  .i_pcie_targ_syscfg_apb_pwrite (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pwrite),
  .i_pcie_targ_syscfg_apb_psel (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_psel),
  .i_pcie_targ_syscfg_apb_penable (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_penable),
  .i_pcie_targ_syscfg_apb_pstrb (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pstrb),
  .i_pcie_targ_syscfg_apb_pprot (u_noc_top_to_u_pcie_p__o_pcie_targ_syscfg_apb_m_pprot),
  .o_pcie_targ_syscfg_apb_pready (u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_pready),
  .o_pcie_targ_syscfg_apb_prdata (u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_prdata),
  .o_pcie_targ_syscfg_apb_pslverr (u_pcie_p_to_u_noc_top__o_pcie_targ_syscfg_apb_pslverr),
  .o_pcie_int (u_pcie_p_to_u_apu_p__o_pcie_int),
  .o_pcie_obs (u_pcie_p_to_u_soc_mgmt_p__o_pcie_obs),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
`ifdef PVE_P_0_STUB
pve_p_stub u_pve_p_0 (
`else
pve_p u_pve_p_0 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_clock_throttle (u_soc_mgmt_p_to_u_pve_p_0__o_clock_throttle_8),
  .i_thermal_throttle (u_soc_mgmt_p_to_u_pve_p_0__o_thermal_throttle_8),
  .o_noc_async_idle_req (u_pve_p_0_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_pve_p_0__o_pve_0_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_pve_p_0__o_pve_0_pwr_idle_val),
  .o_noc_clken (u_pve_p_0_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_pve_p_0_to_u_noc_top__o_noc_rst_n),
  .i_hart_base (PVE0_HART_BASE),
  .i_debug_req (u_soc_mgmt_p_to_u_pve_p_0__o_debugint_9),
  .i_debug_rst_halt_req (u_soc_mgmt_p_to_u_pve_p_0__o_resethaltreq_9),
  .o_hart_unavail (u_pve_p_0_to_u_soc_mgmt_p__o_hart_unavail),
  .o_hart_under_reset (u_pve_p_0_to_u_soc_mgmt_p__o_hart_under_reset),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_pve_p_0__o_pve_0_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_pve_p_0_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_ctrlo_axi_m_awvalid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awvalid),
  .o_ctrlo_axi_m_awid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awid),
  .o_ctrlo_axi_m_awaddr (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awaddr),
  .o_ctrlo_axi_m_awlen (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awlen),
  .o_ctrlo_axi_m_awsize (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awsize),
  .o_ctrlo_axi_m_awburst (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awburst),
  .o_ctrlo_axi_m_awlock (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awlock),
  .o_ctrlo_axi_m_awcache (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awcache),
  .o_ctrlo_axi_m_awprot (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awprot),
  .o_ctrlo_axi_m_awqos (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_awqos),
  .o_ctrlo_axi_m_awregion (),
  .o_ctrlo_axi_m_awuser (),
  .i_ctrlo_axi_m_awready (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_awready),
  .o_ctrlo_axi_m_wvalid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wvalid),
  .o_ctrlo_axi_m_wdata (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wdata),
  .o_ctrlo_axi_m_wstrb (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wstrb),
  .o_ctrlo_axi_m_wlast (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_wlast),
  .o_ctrlo_axi_m_wuser (),
  .i_ctrlo_axi_m_wready (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_wready),
  .i_ctrlo_axi_m_bvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bvalid),
  .i_ctrlo_axi_m_bid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bid),
  .i_ctrlo_axi_m_bresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_bresp),
  .i_ctrlo_axi_m_buser ('0),
  .o_ctrlo_axi_m_bready (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_bready),
  .o_ctrlo_axi_m_arvalid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arvalid),
  .o_ctrlo_axi_m_arid (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arid),
  .o_ctrlo_axi_m_araddr (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_araddr),
  .o_ctrlo_axi_m_arlen (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arlen),
  .o_ctrlo_axi_m_arsize (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arsize),
  .o_ctrlo_axi_m_arburst (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arburst),
  .o_ctrlo_axi_m_arlock (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arlock),
  .o_ctrlo_axi_m_arcache (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arcache),
  .o_ctrlo_axi_m_arprot (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arprot),
  .o_ctrlo_axi_m_arqos (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_arqos),
  .o_ctrlo_axi_m_arregion (),
  .o_ctrlo_axi_m_aruser (),
  .i_ctrlo_axi_m_arready (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_arready),
  .i_ctrlo_axi_m_rvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rvalid),
  .i_ctrlo_axi_m_rid (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rid),
  .i_ctrlo_axi_m_rdata (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rdata),
  .i_ctrlo_axi_m_rresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rresp),
  .i_ctrlo_axi_m_rlast (u_noc_top_to_u_pve_p_0__o_pve_0_init_lt_axi_s_rlast),
  .i_ctrlo_axi_m_ruser ('0),
  .o_ctrlo_axi_m_rready (u_pve_p_0_to_u_noc_top__o_ctrlo_axi_m_rready),
  .i_ctrli_axi_s_awvalid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awvalid),
  .i_ctrli_axi_s_awid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awid),
  .i_ctrli_axi_s_awaddr (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awaddr),
  .i_ctrli_axi_s_awlen (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awlen),
  .i_ctrli_axi_s_awsize (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awsize),
  .i_ctrli_axi_s_awburst (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awburst),
  .i_ctrli_axi_s_awlock (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awlock),
  .i_ctrli_axi_s_awcache (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awcache),
  .i_ctrli_axi_s_awprot (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awprot),
  .i_ctrli_axi_s_awqos (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_awqos),
  .i_ctrli_axi_s_awregion ('0),
  .i_ctrli_axi_s_awuser ('0),
  .o_ctrli_axi_s_awready (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_awready),
  .i_ctrli_axi_s_wvalid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wvalid),
  .i_ctrli_axi_s_wdata (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wdata),
  .i_ctrli_axi_s_wstrb (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wstrb),
  .i_ctrli_axi_s_wlast (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_wlast),
  .i_ctrli_axi_s_wuser ('0),
  .o_ctrli_axi_s_wready (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_wready),
  .o_ctrli_axi_s_bvalid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bvalid),
  .o_ctrli_axi_s_bid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bid),
  .o_ctrli_axi_s_bresp (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_bresp),
  .o_ctrli_axi_s_buser (),
  .i_ctrli_axi_s_bready (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_bready),
  .i_ctrli_axi_s_arvalid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arvalid),
  .i_ctrli_axi_s_arid (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arid),
  .i_ctrli_axi_s_araddr (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_araddr),
  .i_ctrli_axi_s_arlen (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arlen),
  .i_ctrli_axi_s_arsize (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arsize),
  .i_ctrli_axi_s_arburst (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arburst),
  .i_ctrli_axi_s_arlock (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arlock),
  .i_ctrli_axi_s_arcache (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arcache),
  .i_ctrli_axi_s_arprot (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arprot),
  .i_ctrli_axi_s_arqos (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_arqos),
  .i_ctrli_axi_s_arregion ('0),
  .i_ctrli_axi_s_aruser ('0),
  .o_ctrli_axi_s_arready (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_arready),
  .o_ctrli_axi_s_rvalid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rvalid),
  .o_ctrli_axi_s_rid (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rid),
  .o_ctrli_axi_s_rdata (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rdata),
  .o_ctrli_axi_s_rresp (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rresp),
  .o_ctrli_axi_s_rlast (u_pve_p_0_to_u_noc_top__o_ctrli_axi_s_rlast),
  .o_ctrli_axi_s_ruser (),
  .i_ctrli_axi_s_rready (u_noc_top_to_u_pve_p_0__o_pve_0_targ_lt_axi_m_rready),
  .o_dma_axi_m_awvalid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awvalid),
  .o_dma_axi_m_awid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awid),
  .o_dma_axi_m_awaddr (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awaddr),
  .o_dma_axi_m_awlen (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awlen),
  .o_dma_axi_m_awsize (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awsize),
  .o_dma_axi_m_awburst (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awburst),
  .o_dma_axi_m_awlock (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awlock),
  .o_dma_axi_m_awcache (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awcache),
  .o_dma_axi_m_awprot (u_pve_p_0_to_u_noc_top__o_dma_axi_m_awprot),
  .o_dma_axi_m_awqos (),
  .o_dma_axi_m_awregion (),
  .o_dma_axi_m_awuser (),
  .i_dma_axi_m_awready (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_awready),
  .o_dma_axi_m_wvalid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wvalid),
  .o_dma_axi_m_wdata (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wdata),
  .o_dma_axi_m_wstrb (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wstrb),
  .o_dma_axi_m_wlast (u_pve_p_0_to_u_noc_top__o_dma_axi_m_wlast),
  .o_dma_axi_m_wuser (),
  .i_dma_axi_m_wready (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_wready),
  .i_dma_axi_m_bvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bvalid),
  .i_dma_axi_m_bid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bid),
  .i_dma_axi_m_bresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_bresp),
  .i_dma_axi_m_buser ('0),
  .o_dma_axi_m_bready (u_pve_p_0_to_u_noc_top__o_dma_axi_m_bready),
  .o_dma_axi_m_arvalid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arvalid),
  .o_dma_axi_m_arid (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arid),
  .o_dma_axi_m_araddr (u_pve_p_0_to_u_noc_top__o_dma_axi_m_araddr),
  .o_dma_axi_m_arlen (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arlen),
  .o_dma_axi_m_arsize (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arsize),
  .o_dma_axi_m_arburst (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arburst),
  .o_dma_axi_m_arlock (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arlock),
  .o_dma_axi_m_arcache (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arcache),
  .o_dma_axi_m_arprot (u_pve_p_0_to_u_noc_top__o_dma_axi_m_arprot),
  .o_dma_axi_m_arqos (),
  .o_dma_axi_m_arregion (),
  .o_dma_axi_m_aruser (),
  .i_dma_axi_m_arready (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_arready),
  .i_dma_axi_m_rvalid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rvalid),
  .i_dma_axi_m_rid (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rid),
  .i_dma_axi_m_rdata (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rdata),
  .i_dma_axi_m_rresp (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rresp),
  .i_dma_axi_m_rlast (u_noc_top_to_u_pve_p_0__o_pve_0_init_ht_axi_s_rlast),
  .i_dma_axi_m_ruser ('0),
  .o_dma_axi_m_rready (u_pve_p_0_to_u_noc_top__o_dma_axi_m_rready),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .io_ibias_ts (u_pve_p_0_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_pve_p_0_to_u_soc_mgmt_p__io_vsense_ts)
);
`ifdef PVE_P_1_STUB
pve_p_stub u_pve_p_1 (
`else
pve_p u_pve_p_1 (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_clock_throttle (u_soc_mgmt_p_to_u_pve_p_1__o_clock_throttle_9),
  .i_thermal_throttle (u_soc_mgmt_p_to_u_pve_p_1__o_thermal_throttle_9),
  .o_noc_async_idle_req (u_pve_p_1_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_pve_p_1__o_pve_1_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_pve_p_1__o_pve_1_pwr_idle_val),
  .o_noc_clken (u_pve_p_1_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_pve_p_1_to_u_noc_top__o_noc_rst_n),
  .i_hart_base (PVE1_HART_BASE),
  .i_debug_req (u_soc_mgmt_p_to_u_pve_p_1__o_debugint_10),
  .i_debug_rst_halt_req (u_soc_mgmt_p_to_u_pve_p_1__o_resethaltreq_10),
  .o_hart_unavail (u_pve_p_1_to_u_soc_mgmt_p__o_hart_unavail),
  .o_hart_under_reset (u_pve_p_1_to_u_soc_mgmt_p__o_hart_under_reset),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_pve_p_1__o_pve_1_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_pve_p_1_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_ctrlo_axi_m_awvalid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awvalid),
  .o_ctrlo_axi_m_awid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awid),
  .o_ctrlo_axi_m_awaddr (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awaddr),
  .o_ctrlo_axi_m_awlen (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awlen),
  .o_ctrlo_axi_m_awsize (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awsize),
  .o_ctrlo_axi_m_awburst (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awburst),
  .o_ctrlo_axi_m_awlock (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awlock),
  .o_ctrlo_axi_m_awcache (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awcache),
  .o_ctrlo_axi_m_awprot (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awprot),
  .o_ctrlo_axi_m_awqos (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_awqos),
  .o_ctrlo_axi_m_awregion (),
  .o_ctrlo_axi_m_awuser (),
  .i_ctrlo_axi_m_awready (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_awready),
  .o_ctrlo_axi_m_wvalid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wvalid),
  .o_ctrlo_axi_m_wdata (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wdata),
  .o_ctrlo_axi_m_wstrb (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wstrb),
  .o_ctrlo_axi_m_wlast (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_wlast),
  .o_ctrlo_axi_m_wuser (),
  .i_ctrlo_axi_m_wready (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_wready),
  .i_ctrlo_axi_m_bvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bvalid),
  .i_ctrlo_axi_m_bid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bid),
  .i_ctrlo_axi_m_bresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_bresp),
  .i_ctrlo_axi_m_buser ('0),
  .o_ctrlo_axi_m_bready (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_bready),
  .o_ctrlo_axi_m_arvalid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arvalid),
  .o_ctrlo_axi_m_arid (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arid),
  .o_ctrlo_axi_m_araddr (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_araddr),
  .o_ctrlo_axi_m_arlen (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arlen),
  .o_ctrlo_axi_m_arsize (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arsize),
  .o_ctrlo_axi_m_arburst (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arburst),
  .o_ctrlo_axi_m_arlock (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arlock),
  .o_ctrlo_axi_m_arcache (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arcache),
  .o_ctrlo_axi_m_arprot (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arprot),
  .o_ctrlo_axi_m_arqos (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_arqos),
  .o_ctrlo_axi_m_arregion (),
  .o_ctrlo_axi_m_aruser (),
  .i_ctrlo_axi_m_arready (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_arready),
  .i_ctrlo_axi_m_rvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rvalid),
  .i_ctrlo_axi_m_rid (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rid),
  .i_ctrlo_axi_m_rdata (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rdata),
  .i_ctrlo_axi_m_rresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rresp),
  .i_ctrlo_axi_m_rlast (u_noc_top_to_u_pve_p_1__o_pve_1_init_lt_axi_s_rlast),
  .i_ctrlo_axi_m_ruser ('0),
  .o_ctrlo_axi_m_rready (u_pve_p_1_to_u_noc_top__o_ctrlo_axi_m_rready),
  .i_ctrli_axi_s_awvalid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awvalid),
  .i_ctrli_axi_s_awid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awid),
  .i_ctrli_axi_s_awaddr (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awaddr),
  .i_ctrli_axi_s_awlen (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awlen),
  .i_ctrli_axi_s_awsize (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awsize),
  .i_ctrli_axi_s_awburst (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awburst),
  .i_ctrli_axi_s_awlock (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awlock),
  .i_ctrli_axi_s_awcache (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awcache),
  .i_ctrli_axi_s_awprot (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awprot),
  .i_ctrli_axi_s_awqos (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_awqos),
  .i_ctrli_axi_s_awregion ('0),
  .i_ctrli_axi_s_awuser ('0),
  .o_ctrli_axi_s_awready (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_awready),
  .i_ctrli_axi_s_wvalid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wvalid),
  .i_ctrli_axi_s_wdata (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wdata),
  .i_ctrli_axi_s_wstrb (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wstrb),
  .i_ctrli_axi_s_wlast (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_wlast),
  .i_ctrli_axi_s_wuser ('0),
  .o_ctrli_axi_s_wready (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_wready),
  .o_ctrli_axi_s_bvalid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bvalid),
  .o_ctrli_axi_s_bid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bid),
  .o_ctrli_axi_s_bresp (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_bresp),
  .o_ctrli_axi_s_buser (),
  .i_ctrli_axi_s_bready (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_bready),
  .i_ctrli_axi_s_arvalid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arvalid),
  .i_ctrli_axi_s_arid (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arid),
  .i_ctrli_axi_s_araddr (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_araddr),
  .i_ctrli_axi_s_arlen (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arlen),
  .i_ctrli_axi_s_arsize (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arsize),
  .i_ctrli_axi_s_arburst (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arburst),
  .i_ctrli_axi_s_arlock (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arlock),
  .i_ctrli_axi_s_arcache (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arcache),
  .i_ctrli_axi_s_arprot (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arprot),
  .i_ctrli_axi_s_arqos (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_arqos),
  .i_ctrli_axi_s_arregion ('0),
  .i_ctrli_axi_s_aruser ('0),
  .o_ctrli_axi_s_arready (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_arready),
  .o_ctrli_axi_s_rvalid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rvalid),
  .o_ctrli_axi_s_rid (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rid),
  .o_ctrli_axi_s_rdata (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rdata),
  .o_ctrli_axi_s_rresp (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rresp),
  .o_ctrli_axi_s_rlast (u_pve_p_1_to_u_noc_top__o_ctrli_axi_s_rlast),
  .o_ctrli_axi_s_ruser (),
  .i_ctrli_axi_s_rready (u_noc_top_to_u_pve_p_1__o_pve_1_targ_lt_axi_m_rready),
  .o_dma_axi_m_awvalid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awvalid),
  .o_dma_axi_m_awid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awid),
  .o_dma_axi_m_awaddr (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awaddr),
  .o_dma_axi_m_awlen (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awlen),
  .o_dma_axi_m_awsize (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awsize),
  .o_dma_axi_m_awburst (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awburst),
  .o_dma_axi_m_awlock (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awlock),
  .o_dma_axi_m_awcache (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awcache),
  .o_dma_axi_m_awprot (u_pve_p_1_to_u_noc_top__o_dma_axi_m_awprot),
  .o_dma_axi_m_awqos (),
  .o_dma_axi_m_awregion (),
  .o_dma_axi_m_awuser (),
  .i_dma_axi_m_awready (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_awready),
  .o_dma_axi_m_wvalid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wvalid),
  .o_dma_axi_m_wdata (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wdata),
  .o_dma_axi_m_wstrb (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wstrb),
  .o_dma_axi_m_wlast (u_pve_p_1_to_u_noc_top__o_dma_axi_m_wlast),
  .o_dma_axi_m_wuser (),
  .i_dma_axi_m_wready (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_wready),
  .i_dma_axi_m_bvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bvalid),
  .i_dma_axi_m_bid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bid),
  .i_dma_axi_m_bresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_bresp),
  .i_dma_axi_m_buser ('0),
  .o_dma_axi_m_bready (u_pve_p_1_to_u_noc_top__o_dma_axi_m_bready),
  .o_dma_axi_m_arvalid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arvalid),
  .o_dma_axi_m_arid (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arid),
  .o_dma_axi_m_araddr (u_pve_p_1_to_u_noc_top__o_dma_axi_m_araddr),
  .o_dma_axi_m_arlen (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arlen),
  .o_dma_axi_m_arsize (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arsize),
  .o_dma_axi_m_arburst (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arburst),
  .o_dma_axi_m_arlock (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arlock),
  .o_dma_axi_m_arcache (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arcache),
  .o_dma_axi_m_arprot (u_pve_p_1_to_u_noc_top__o_dma_axi_m_arprot),
  .o_dma_axi_m_arqos (),
  .o_dma_axi_m_arregion (),
  .o_dma_axi_m_aruser (),
  .i_dma_axi_m_arready (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_arready),
  .i_dma_axi_m_rvalid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rvalid),
  .i_dma_axi_m_rid (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rid),
  .i_dma_axi_m_rdata (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rdata),
  .i_dma_axi_m_rresp (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rresp),
  .i_dma_axi_m_rlast (u_noc_top_to_u_pve_p_1__o_pve_1_init_ht_axi_s_rlast),
  .i_dma_axi_m_ruser ('0),
  .o_dma_axi_m_rready (u_pve_p_1_to_u_noc_top__o_dma_axi_m_rready),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_mode ('0),
  .ssn_bus_clk ('0),
  .ssn_bus_data_in ('0),
  .ssn_bus_data_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .io_ibias_ts (u_pve_p_1_to_u_soc_mgmt_p__io_ibias_ts),
  .io_vsense_ts (u_pve_p_1_to_u_soc_mgmt_p__io_vsense_ts)
);
`ifdef SOC_MGMT_P_STUB
soc_mgmt_p_stub u_soc_mgmt_p (
`else
soc_mgmt_p u_soc_mgmt_p (
`endif
  .i_ref_clk (i_ref_clk),
  .i_por_rst_n (i_por_rst_n),
  .o_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .o_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_fast_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .o_apu_clk (u_soc_mgmt_p_to_multi__o_apu_clk),
  .o_ddr_ref_east_clk (u_soc_mgmt_p_to_multi__o_ddr_ref_east_clk),
  .o_codec_clk (u_soc_mgmt_p_to_multi__o_codec_clk),
  .o_emmc_clk (u_soc_mgmt_p_to_u_soc_periph_p__o_emmc_clk),
  .o_periph_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .o_noc_clk (u_soc_mgmt_p_to_u_noc_top__o_noc_clk),
  .o_noc_rst_n (u_soc_mgmt_p_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_soc_mgmt_p_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_pwr_idle_val),
  .o_aic_throttle ({
  u_soc_mgmt_p_to_u_ai_core_p_7__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_aic_throttle,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_aic_throttle}),
  .o_clock_throttle ({
  u_soc_mgmt_p_o_clock_throttle_unconn,
  u_soc_mgmt_p_to_u_noc_top__o_clock_throttle_12,
  u_soc_mgmt_p_to_u_noc_top__o_clock_throttle_11,
  u_soc_mgmt_p_to_u_apu_p__o_clock_throttle_10,
  u_soc_mgmt_p_to_u_pve_p_1__o_clock_throttle_9,
  u_soc_mgmt_p_to_u_pve_p_0__o_clock_throttle_8,
  u_soc_mgmt_p_to_u_ai_core_p_7__o_clock_throttle_7,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_clock_throttle_6,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_clock_throttle_5,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_clock_throttle_4,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_clock_throttle_3,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_clock_throttle_2,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_clock_throttle_1,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_clock_throttle_0}),
  .i_aic_boost_req ({
  u_ai_core_p_7_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_6_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_5_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_4_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_3_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_2_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_1_to_u_soc_mgmt_p__o_aic_boost_req_async,
  u_ai_core_p_0_to_u_soc_mgmt_p__o_aic_boost_req_async}),
  .o_aic_boost_ack ({
  u_soc_mgmt_p_to_u_ai_core_p_7__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_aic_boost_ack,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_aic_boost_ack}),
  .i_throttle (i_throttle),
  .o_dlm_irq_warning (u_soc_mgmt_p_to_u_apu_p__o_dlm_irq_warning),
  .o_dlm_irq_critical (u_soc_mgmt_p_to_u_apu_p__o_dlm_irq_critical),
  .o_lt_axi_m_awaddr (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awaddr),
  .o_lt_axi_m_awid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awid),
  .o_lt_axi_m_awlen (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awlen),
  .o_lt_axi_m_awsize (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awsize),
  .o_lt_axi_m_awburst (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awburst),
  .o_lt_axi_m_awcache (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awcache),
  .o_lt_axi_m_awprot (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awprot),
  .o_lt_axi_m_awlock (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awlock),
  .o_lt_axi_m_awqos (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awqos),
  .o_lt_axi_m_awregion (),
  .o_lt_axi_m_awuser (),
  .o_lt_axi_m_awvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_awvalid),
  .i_lt_axi_m_awready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_awready),
  .o_lt_axi_m_wvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wvalid),
  .o_lt_axi_m_wlast (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wlast),
  .o_lt_axi_m_wstrb (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wstrb),
  .o_lt_axi_m_wdata (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_wdata),
  .o_lt_axi_m_wuser (),
  .i_lt_axi_m_wready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_wready),
  .i_lt_axi_m_bvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bvalid),
  .i_lt_axi_m_bid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bid),
  .i_lt_axi_m_bresp (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_bresp),
  .i_lt_axi_m_buser ('0),
  .o_lt_axi_m_bready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_bready),
  .o_lt_axi_m_arvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arvalid),
  .o_lt_axi_m_araddr (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_araddr),
  .o_lt_axi_m_arid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arid),
  .o_lt_axi_m_arlen (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arlen),
  .o_lt_axi_m_arsize (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arsize),
  .o_lt_axi_m_arburst (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arburst),
  .o_lt_axi_m_arcache (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arcache),
  .o_lt_axi_m_arprot (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arprot),
  .o_lt_axi_m_arqos (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arqos),
  .o_lt_axi_m_arregion (),
  .o_lt_axi_m_aruser (),
  .o_lt_axi_m_arlock (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_arlock),
  .i_lt_axi_m_arready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_arready),
  .i_lt_axi_m_rvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rvalid),
  .i_lt_axi_m_rlast (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rlast),
  .i_lt_axi_m_rid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rid),
  .i_lt_axi_m_rdata (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rdata),
  .i_lt_axi_m_rresp (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_init_lt_axi_s_rresp),
  .i_lt_axi_m_ruser ('0),
  .o_lt_axi_m_rready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_m_rready),
  .i_lt_axi_s_awvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awvalid),
  .i_lt_axi_s_awaddr (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awaddr),
  .i_lt_axi_s_awid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awid),
  .i_lt_axi_s_awlen (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awlen),
  .i_lt_axi_s_awsize (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awsize),
  .i_lt_axi_s_awburst (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awburst),
  .i_lt_axi_s_awcache (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awcache),
  .i_lt_axi_s_awprot (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awprot),
  .i_lt_axi_s_awlock (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awlock),
  .i_lt_axi_s_awqos (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_awqos),
  .i_lt_axi_s_awregion ('0),
  .i_lt_axi_s_awuser ('0),
  .o_lt_axi_s_awready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_awready),
  .i_lt_axi_s_wvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wvalid),
  .i_lt_axi_s_wlast (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wlast),
  .i_lt_axi_s_wstrb (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wstrb),
  .i_lt_axi_s_wdata (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_wdata),
  .i_lt_axi_s_wuser ('0),
  .o_lt_axi_s_wready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_wready),
  .o_lt_axi_s_bvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bvalid),
  .o_lt_axi_s_bid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bid),
  .o_lt_axi_s_bresp (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_bresp),
  .o_lt_axi_s_buser (),
  .i_lt_axi_s_bready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_bready),
  .i_lt_axi_s_arvalid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arvalid),
  .i_lt_axi_s_araddr (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_araddr),
  .i_lt_axi_s_arid (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arid),
  .i_lt_axi_s_arlen (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arlen),
  .i_lt_axi_s_arsize (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arsize),
  .i_lt_axi_s_arburst (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arburst),
  .i_lt_axi_s_arcache (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arcache),
  .i_lt_axi_s_arprot (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arprot),
  .i_lt_axi_s_arqos (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arqos),
  .i_lt_axi_s_arregion ('0),
  .i_lt_axi_s_aruser ('0),
  .i_lt_axi_s_arlock (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_arlock),
  .o_lt_axi_s_arready (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_arready),
  .o_lt_axi_s_rvalid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rvalid),
  .o_lt_axi_s_rlast (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rlast),
  .o_lt_axi_s_rid (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rid),
  .o_lt_axi_s_rdata (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rdata),
  .o_lt_axi_s_rresp (u_soc_mgmt_p_to_u_noc_top__o_lt_axi_s_rresp),
  .o_lt_axi_s_ruser (),
  .i_lt_axi_s_rready (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_lt_axi_m_rready),
  .i_syscfg_apb4_s_paddr (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_paddr),
  .i_syscfg_apb4_s_pwdata (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pwdata),
  .i_syscfg_apb4_s_pwrite (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pwrite),
  .i_syscfg_apb4_s_psel (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_psel),
  .i_syscfg_apb4_s_penable (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_penable),
  .i_syscfg_apb4_s_pstrb (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pstrb),
  .i_syscfg_apb4_s_pprot (u_noc_top_to_u_soc_mgmt_p__o_soc_mgmt_targ_syscfg_apb_m_pprot),
  .o_syscfg_apb4_s_pready (u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_pready),
  .o_syscfg_apb4_s_prdata (u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_prdata),
  .o_syscfg_apb4_s_pslverr (u_soc_mgmt_p_to_u_noc_top__o_syscfg_apb4_s_pslverr),
  .o_mbist_apb_m_paddr (),
  .o_mbist_apb_m_pwdata (),
  .o_mbist_apb_m_pwrite (),
  .o_mbist_apb_m_psel (),
  .o_mbist_apb_m_penable (),
  .i_mbist_apb_m_pready ('0),
  .i_mbist_apb_m_prdata ('0),
  .i_mbist_apb_m_pslverr ('0),
  .i_thermal_throttle (i_thermal_throttle),
  .o_thermal_throttle ({
  u_soc_mgmt_p_o_thermal_throttle_unconn,
  u_soc_mgmt_p_to_u_apu_p__o_thermal_throttle_10,
  u_soc_mgmt_p_to_u_pve_p_1__o_thermal_throttle_9,
  u_soc_mgmt_p_to_u_pve_p_0__o_thermal_throttle_8,
  u_soc_mgmt_p_to_u_ai_core_p_7__o_thermal_throttle_7,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_thermal_throttle_6,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_thermal_throttle_5,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_thermal_throttle_4,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_thermal_throttle_3,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_thermal_throttle_2,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_thermal_throttle_1,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_thermal_throttle_0}),
  .o_thermal_throttle_warning_n (o_thermal_warning_n),
  .o_thermal_warning ({
  u_soc_mgmt_p_o_thermal_warning_unconn,
  u_soc_mgmt_p_to_u_ai_core_p_7__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_thermal_warning,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_thermal_warning}),
  .o_thermal_shutdown_n (o_thermal_shutdown_n),
  .o_irq_tms_throttle (u_soc_mgmt_p_to_u_apu_p__o_irq_tms_throttle),
  .o_irq_tms_warning (u_soc_mgmt_p_to_u_apu_p__o_irq_tms_warning),
  .o_irq_tms_shutdown (u_soc_mgmt_p_to_u_apu_p__o_irq_tms_shutdown),
  .o_rtc_irq (u_soc_mgmt_p_to_u_apu_p__o_rtc_irq),
  .o_wdt_irq (u_soc_mgmt_p_to_u_apu_p__o_wdt_irq),
  .o_security_irq (u_soc_mgmt_p_to_u_apu_p__o_security_irq),
  .i_boot_mode (i_boot_mode),
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
  .tck ('0),
  .trst ('0),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .i_auto_repair_done ('0),
  .o_debugint ({
  u_soc_mgmt_p_to_u_pve_p_1__o_debugint_10,
  u_soc_mgmt_p_to_u_pve_p_0__o_debugint_9,
  u_soc_mgmt_p_to_u_ai_core_p_7__o_debugint_8,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_debugint_7,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_debugint_6,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_debugint_5,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_debugint_4,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_debugint_3,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_debugint_2,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_debugint_1,
  u_soc_mgmt_p_to_u_apu_p__o_debugint_0}),
  .o_resethaltreq ({
  u_soc_mgmt_p_to_u_pve_p_1__o_resethaltreq_10,
  u_soc_mgmt_p_to_u_pve_p_0__o_resethaltreq_9,
  u_soc_mgmt_p_to_u_ai_core_p_7__o_resethaltreq_8,
  u_soc_mgmt_p_to_u_ai_core_p_6__o_resethaltreq_7,
  u_soc_mgmt_p_to_u_ai_core_p_5__o_resethaltreq_6,
  u_soc_mgmt_p_to_u_ai_core_p_4__o_resethaltreq_5,
  u_soc_mgmt_p_to_u_ai_core_p_3__o_resethaltreq_4,
  u_soc_mgmt_p_to_u_ai_core_p_2__o_resethaltreq_3,
  u_soc_mgmt_p_to_u_ai_core_p_1__o_resethaltreq_2,
  u_soc_mgmt_p_to_u_ai_core_p_0__o_resethaltreq_1,
  u_soc_mgmt_p_to_u_apu_p__o_resethaltreq_0}),
  .i_hart_unavail ({
  u_pve_p_1_to_u_soc_mgmt_p__o_hart_unavail,
  u_pve_p_0_to_u_soc_mgmt_p__o_hart_unavail,
  u_ai_core_p_7_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_6_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_5_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_4_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_3_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_2_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_1_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_ai_core_p_0_to_u_soc_mgmt_p__o_hart_unavail_async,
  u_apu_p_to_u_soc_mgmt_p__o_cores_hart_unavail}),
  .i_hart_under_reset ({
  u_pve_p_1_to_u_soc_mgmt_p__o_hart_under_reset,
  u_pve_p_0_to_u_soc_mgmt_p__o_hart_under_reset,
  u_ai_core_p_7_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_6_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_5_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_4_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_3_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_2_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_1_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_ai_core_p_0_to_u_soc_mgmt_p__o_hart_under_reset_async,
  u_apu_p_to_u_soc_mgmt_p__o_cores_hart_under_reset}),
  .o_dbg_taps_en (),
  .o_otp_tap_en (),
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
  .i_dft_otp_tst_vddrdy ('0),
  .i_dft_otp_tst_clken ('0),
  .o_dft_otp_tst_d (),
  .o_dft_otp_tst_lock (),
  .i_obs_bus ({
  u_sys_spm_p_to_u_soc_mgmt_p__o_sysspm_obs,
  u_soc_periph_p_to_u_soc_mgmt_p__o_obs,
  u_pcie_p_to_u_soc_mgmt_p__o_pcie_obs,
  u_noc_top_to_u_soc_mgmt_p__o_obs,
  u_lpddr_p_ppp_3_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_ppp_2_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_ppp_1_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_ppp_0_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_graph_3_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_graph_2_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_graph_1_to_u_soc_mgmt_p__o_lpddr_obs,
  u_lpddr_p_graph_0_to_u_soc_mgmt_p__o_lpddr_obs,
  u_ddr_west_clock_gen_p_to_u_soc_mgmt_p__o_ddr_west_clkgen_obs,
  u_dcd_p_to_u_soc_mgmt_p__o_dcd_obs,
  u_ai_core_p_7_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_6_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_5_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_4_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_3_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_2_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_1_to_u_soc_mgmt_p__o_aic_obs,
  u_ai_core_p_0_to_u_soc_mgmt_p__o_aic_obs}),
  .o_obs_bus (o_observability),
  .o_global_sync (u_soc_mgmt_p_to_multi__o_global_sync),
  .io_otp_vtdo (io_otp_vtdo),
  .io_otp_vrefm (io_otp_vrefm),
  .io_otp_vpp (io_otp_vpp),
  .io_pvt_ibias_ts ({
  u_soc_mgmt_p_io_pvt_ibias_ts_unconn,
  u_pve_p_1_to_u_soc_mgmt_p__io_ibias_ts,
  u_pve_p_0_to_u_soc_mgmt_p__io_ibias_ts,
  u_apu_p_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_7_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_6_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_5_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_4_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_3_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_2_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_1_to_u_soc_mgmt_p__io_ibias_ts,
  u_ai_core_p_0_to_u_soc_mgmt_p__io_ibias_ts}),
  .io_pvt_vsense_ts ({
  u_soc_mgmt_p_io_pvt_vsense_ts_unconn,
  u_pve_p_1_to_u_soc_mgmt_p__io_vsense_ts,
  u_pve_p_0_to_u_soc_mgmt_p__io_vsense_ts,
  u_apu_p_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_7_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_6_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_5_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_4_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_3_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_2_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_1_to_u_soc_mgmt_p__io_vsense_ts,
  u_ai_core_p_0_to_u_soc_mgmt_p__io_vsense_ts}),
  .io_pvt_test_out_ts (io_pvt_test_out_ts),
  .io_efuse_vqps (io_efuse_vqps),
  .io_efuse_vddwl (io_efuse_vddwl)
);
`ifdef SOC_PERIPH_P_STUB
soc_periph_p_stub u_soc_periph_p (
`else
soc_periph_p u_soc_periph_p (
`endif
  .i_ref_clk (i_ref_clk),
  .i_emmc_clk (u_soc_mgmt_p_to_u_soc_periph_p__o_emmc_clk),
  .i_periph_clk (u_soc_mgmt_p_to_multi__o_periph_clk),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_lt_axi_s_awaddr (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awaddr),
  .i_lt_axi_s_awid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awid),
  .i_lt_axi_s_awlen (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awlen),
  .i_lt_axi_s_awsize (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awsize),
  .i_lt_axi_s_awburst (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awburst),
  .i_lt_axi_s_awcache (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awcache),
  .i_lt_axi_s_awprot (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awprot),
  .i_lt_axi_s_awlock (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awlock),
  .i_lt_axi_s_awqos (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awqos),
  .i_lt_axi_s_awregion ('0),
  .i_lt_axi_s_awuser ('0),
  .i_lt_axi_s_awvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_awvalid),
  .o_lt_axi_s_awready (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_awready),
  .i_lt_axi_s_wdata (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wdata),
  .i_lt_axi_s_wstrb (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wstrb),
  .i_lt_axi_s_wlast (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wlast),
  .i_lt_axi_s_wuser ('0),
  .i_lt_axi_s_wvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_wvalid),
  .o_lt_axi_s_wready (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_wready),
  .o_lt_axi_s_bvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bvalid),
  .o_lt_axi_s_bid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bid),
  .o_lt_axi_s_buser (),
  .o_lt_axi_s_bresp (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_bresp),
  .i_lt_axi_s_bready (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_bready),
  .i_lt_axi_s_araddr (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_araddr),
  .i_lt_axi_s_arid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arid),
  .i_lt_axi_s_arlen (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arlen),
  .i_lt_axi_s_arsize (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arsize),
  .i_lt_axi_s_arburst (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arburst),
  .i_lt_axi_s_arcache (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arcache),
  .i_lt_axi_s_arprot (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arprot),
  .i_lt_axi_s_arqos (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arqos),
  .i_lt_axi_s_arregion ('0),
  .i_lt_axi_s_aruser ('0),
  .i_lt_axi_s_arlock (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arlock),
  .i_lt_axi_s_arvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_arvalid),
  .o_lt_axi_s_arready (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_arready),
  .o_lt_axi_s_rvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rvalid),
  .o_lt_axi_s_rlast (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rlast),
  .o_lt_axi_s_rid (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rid),
  .o_lt_axi_s_rdata (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rdata),
  .o_lt_axi_s_ruser (),
  .o_lt_axi_s_rresp (u_soc_periph_p_to_u_noc_top__o_lt_axi_s_rresp),
  .i_lt_axi_s_rready (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_lt_axi_m_rready),
  .o_lt_axi_m_awaddr (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awaddr),
  .o_lt_axi_m_awid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awid),
  .o_lt_axi_m_awlen (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awlen),
  .o_lt_axi_m_awsize (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awsize),
  .o_lt_axi_m_awburst (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awburst),
  .o_lt_axi_m_awcache (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awcache),
  .o_lt_axi_m_awprot (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awprot),
  .o_lt_axi_m_awlock (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awlock),
  .o_lt_axi_m_awqos (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awqos),
  .o_lt_axi_m_awregion (),
  .o_lt_axi_m_awuser (),
  .o_lt_axi_m_awvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_awvalid),
  .i_lt_axi_m_awready (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_awready),
  .o_lt_axi_m_wdata (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wdata),
  .o_lt_axi_m_wstrb (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wstrb),
  .o_lt_axi_m_wlast (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wlast),
  .o_lt_axi_m_wuser (),
  .o_lt_axi_m_wvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_wvalid),
  .i_lt_axi_m_wready (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_wready),
  .i_lt_axi_m_bvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bvalid),
  .i_lt_axi_m_bid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bid),
  .i_lt_axi_m_buser ('0),
  .i_lt_axi_m_bresp (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_bresp),
  .o_lt_axi_m_bready (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_bready),
  .o_lt_axi_m_araddr (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_araddr),
  .o_lt_axi_m_arid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arid),
  .o_lt_axi_m_arlen (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arlen),
  .o_lt_axi_m_arsize (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arsize),
  .o_lt_axi_m_arburst (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arburst),
  .o_lt_axi_m_arcache (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arcache),
  .o_lt_axi_m_arprot (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arprot),
  .o_lt_axi_m_arqos (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arqos),
  .o_lt_axi_m_arregion (),
  .o_lt_axi_m_aruser (),
  .o_lt_axi_m_arlock (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arlock),
  .o_lt_axi_m_arvalid (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_arvalid),
  .i_lt_axi_m_arready (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_arready),
  .i_lt_axi_m_rvalid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rvalid),
  .i_lt_axi_m_rlast (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rlast),
  .i_lt_axi_m_rid (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rid),
  .i_lt_axi_m_rdata (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rdata),
  .i_lt_axi_m_ruser ('0),
  .i_lt_axi_m_rresp (u_noc_top_to_u_soc_periph_p__o_soc_periph_init_lt_axi_s_rresp),
  .o_lt_axi_m_rready (u_soc_periph_p_to_u_noc_top__o_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_soc_periph_p__o_soc_periph_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_soc_periph_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_noc_async_idle_req (u_soc_periph_p_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_soc_periph_p__o_soc_periph_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_soc_periph_p__o_soc_periph_pwr_idle_val),
  .o_noc_clken (u_soc_periph_p_to_u_noc_top__o_noc_clken),
  .o_noc_rst_n (u_soc_periph_p_to_u_noc_top__o_noc_rst_n),
  .o_obs (u_soc_periph_p_to_u_soc_mgmt_p__o_obs),
  .i_uart_cst_n (i_uart_cts_n),
  .i_uart_rx (i_uart_rx),
  .o_uart_rts_n (o_uart_rts_n),
  .o_uart_tx (o_uart_tx),
  .o_uart_int (u_soc_periph_p_to_u_apu_p__o_uart_int),
  .i_gpio (i_gpio),
  .o_gpio_oe (o_gpio_oe),
  .o_gpio (o_gpio),
  .o_gpio_int (u_soc_periph_p_to_u_apu_p__o_gpio_int),
  .o_i2c_0_clk_oe (o_i2c_0_clk_oe),
  .o_i2c_0_data_oe (o_i2c_0_data_oe),
  .i_i2c_0_clk (i_i2c_0_clk),
  .i_i2c_0_data (i_i2c_0_data),
  .o_i2c_0_int (u_soc_periph_p_to_u_apu_p__o_i2c_0_int),
  .o_i2c_1_clk_oe (o_i2c_1_clk_oe),
  .o_i2c_1_data_oe (o_i2c_1_data_oe),
  .i_i2c_1_clk (i_i2c_1_clk),
  .i_i2c_1_data (i_i2c_1_data),
  .o_i2c_1_int (u_soc_periph_p_to_u_apu_p__o_i2c_1_int),
  .o_timer_int (u_soc_periph_p_to_u_apu_p__o_timer_int),
  .o_spi_clk (o_spi_clk_out),
  .o_spi_ss_n (o_spi_ss_n),
  .o_spi_sd_oe_n (o_spi_sd_oe_n),
  .o_spi_sd (o_spi_sd),
  .i_spi_sd (i_spi_sd),
  .o_spi_int (u_soc_periph_p_to_u_apu_p__o_spi_int),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .o_mem_ale_oepad (o_mem_ale_oepad),
  .o_mem_ale_iepad (),
  .o_mem_ale_opad (o_mem_ale_opad),
  .i_mem_cmd_ipad (i_mem_cmd_ipad),
  .o_mem_cmd_oepad (o_mem_cmd_oepad),
  .o_mem_cmd_iepad (o_mem_cmd_iepad),
  .o_mem_cmd_opad (o_mem_cmd_opad),
  .o_mem_ctrl_0_oepad (),
  .o_mem_ctrl_0_iepad (o_mem_ctrl_0_iepad),
  .i_mem_ctrl_0_ipad (i_mem_ctrl_0_ipad),
  .o_mem_ctrl_1_oepad (o_mem_ctrl_1_oepad),
  .o_mem_ctrl_1_iepad (),
  .o_mem_ctrl_1_opad (o_mem_ctrl_1_opad),
  .o_mem_rstbar_oepad (o_mem_rstbar_oepad),
  .o_mem_rstbar_iepad (),
  .o_mem_rstbar_opad (o_mem_rstbar_opad),
  .i_mem_lpbk_dqs_ipad (i_mem_lpbk_dqs_ipad),
  .o_mem_lpbk_dqs_oepad (),
  .o_mem_lpbk_dqs_iepad (o_mem_lpbk_dqs_iepad),
  .i_mem_dqs_ipad (i_mem_dqs_ipad),
  .o_mem_dqs_oepad (),
  .o_mem_dqs_iepad (o_mem_dqs_iepad),
  .o_mem_rebar_oepad (o_mem_rebar_oepad),
  .o_mem_rebar_iepad (o_mem_rebar_iepad),
  .o_mem_rebar_opad (o_mem_rebar_opad),
  .i_mem_rebar_ipad (i_mem_rebar_ipad),
  .i_mem_data_ipad (i_mem_data_ipad),
  .o_mem_data_oepad (o_mem_data_oepad),
  .o_mem_data_iepad (o_mem_data_iepad),
  .o_mem_data_opad (o_mem_data_opad),
  .o_mem_webar_oepad (o_mem_webar_oepad),
  .o_mem_webar_iepad (),
  .o_mem_webar_opad (o_mem_webar_opad),
  .o_mem_wpbar_oepad (),
  .o_mem_wpbar_iepad (o_mem_wpbar_iepad),
  .i_mem_wpbar_ipad (i_mem_wpbar_ipad),
  .o_emmc_int (u_soc_periph_p_to_u_apu_p__o_emmc_int),
  .o_ref_clk_sel_freq (o_ref_clk_sel_freq),
  .o_jtag_drive (o_jtag_drive),
  .o_uart_drive (o_uart_drive),
  .o_spi_drive (o_spi_drive),
  .o_i2c_drive (o_i2c_drive),
  .o_gpio_drive (o_gpio_drive),
  .o_obs_drive (o_obs_drive),
  .o_dft_drive (o_dft_drive),
  .o_emmc_drive (o_emmc_drive),
  .o_clk_schmitt (o_clk_schmitt),
  .o_rst_schmitt (o_rst_schmitt),
  .o_spi_schmitt (o_spi_schmitt),
  .o_uart_schmitt (o_uart_schmitt),
  .o_i2c_schmitt (o_i2c_schmitt),
  .o_gpio_schmitt (o_gpio_schmitt),
  .o_emmc_schmitt (o_emmc_schmitt),
  .o_dft_schmitt (o_dft_schmitt),
  .o_bootmode_pull_en (o_bootmode_pull_en),
  .o_spi_sd_pd_en (o_spi_sd_pd_en),
  .o_uart_cts_n_pd_en (o_uart_cts_n_pd_en),
  .o_uart_rx_pd_en (o_uart_rx_pd_en),
  .o_gpio_pd_en (o_gpio_pd_en)
);
`ifdef SYS_SPM_P_STUB
sys_spm_p_stub u_sys_spm_p (
`else
sys_spm_p u_sys_spm_p (
`endif
  .i_clk (u_soc_mgmt_p_to_multi__o_fast_clk),
  .i_ref_clk (i_ref_clk),
  .i_ao_rst_n (u_soc_mgmt_p_to_multi__o_ao_rst_n),
  .i_global_rst_n (u_soc_mgmt_p_to_multi__o_global_rst_n),
  .o_noc_rst_n (u_sys_spm_p_to_u_noc_top__o_noc_rst_n),
  .o_noc_async_idle_req (u_sys_spm_p_to_u_noc_top__o_noc_async_idle_req),
  .i_noc_async_idle_ack (u_noc_top_to_u_sys_spm_p__o_sys_spm_pwr_idle_ack),
  .i_noc_async_idle_val (u_noc_top_to_u_sys_spm_p__o_sys_spm_pwr_idle_val),
  .o_noc_clken (u_sys_spm_p_to_u_noc_top__o_noc_clken),
  .i_lt_axi_s_awaddr (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awaddr),
  .i_lt_axi_s_awid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awid),
  .i_lt_axi_s_awlen (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awlen),
  .i_lt_axi_s_awsize (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awsize),
  .i_lt_axi_s_awburst (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awburst),
  .i_lt_axi_s_awcache (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awcache),
  .i_lt_axi_s_awprot (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awprot),
  .i_lt_axi_s_awlock (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awlock),
  .i_lt_axi_s_awqos (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awqos),
  .i_lt_axi_s_awregion ('0),
  .i_lt_axi_s_awuser ('0),
  .i_lt_axi_s_awvalid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_awvalid),
  .o_lt_axi_s_awready (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_awready),
  .i_lt_axi_s_wdata (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wdata),
  .i_lt_axi_s_wstrb (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wstrb),
  .i_lt_axi_s_wlast (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wlast),
  .i_lt_axi_s_wuser ('0),
  .i_lt_axi_s_wvalid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_wvalid),
  .o_lt_axi_s_wready (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_wready),
  .o_lt_axi_s_bvalid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bvalid),
  .o_lt_axi_s_bid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bid),
  .o_lt_axi_s_buser (),
  .o_lt_axi_s_bresp (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_bresp),
  .i_lt_axi_s_bready (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_bready),
  .i_lt_axi_s_araddr (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_araddr),
  .i_lt_axi_s_arid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arid),
  .i_lt_axi_s_arlen (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arlen),
  .i_lt_axi_s_arsize (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arsize),
  .i_lt_axi_s_arburst (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arburst),
  .i_lt_axi_s_arcache (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arcache),
  .i_lt_axi_s_arprot (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arprot),
  .i_lt_axi_s_arqos (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arqos),
  .i_lt_axi_s_arregion ('0),
  .i_lt_axi_s_aruser ('0),
  .i_lt_axi_s_arlock (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arlock),
  .i_lt_axi_s_arvalid (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_arvalid),
  .o_lt_axi_s_arready (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_arready),
  .o_lt_axi_s_rvalid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rvalid),
  .o_lt_axi_s_rlast (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rlast),
  .o_lt_axi_s_rid (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rid),
  .o_lt_axi_s_rdata (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rdata),
  .o_lt_axi_s_ruser (),
  .o_lt_axi_s_rresp (u_sys_spm_p_to_u_noc_top__o_lt_axi_s_rresp),
  .i_lt_axi_s_rready (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_lt_axi_m_rready),
  .i_cfg_apb4_s_paddr (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_paddr),
  .i_cfg_apb4_s_pwdata (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pwdata),
  .i_cfg_apb4_s_pwrite (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pwrite),
  .i_cfg_apb4_s_psel (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_psel),
  .i_cfg_apb4_s_penable (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_penable),
  .i_cfg_apb4_s_pstrb (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pstrb),
  .i_cfg_apb4_s_pprot (u_noc_top_to_u_sys_spm_p__o_sys_spm_targ_syscfg_apb_m_pprot),
  .o_cfg_apb4_s_pready (u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata (u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr (u_sys_spm_p_to_u_noc_top__o_cfg_apb4_s_pslverr),
  .o_irq (u_sys_spm_p_to_u_apu_p__o_irq),
  .o_sysspm_obs (u_sys_spm_p_to_u_soc_mgmt_p__o_sysspm_obs),
  .tck (i_tck),
  .trst (i_trst_n),
  .tms ('0),
  .tdi ('0),
  .tdo_en (),
  .tdo (),
  .test_clk ('0),
  .test_mode ('0),
  .edt_update ('0),
  .scan_en ('0),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);


endmodule
`endif  // AIPU_SV
