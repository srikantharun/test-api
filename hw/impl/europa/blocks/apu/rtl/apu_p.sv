/// Description: Application Processor Unit containing AX65 Cluster
///
module apu_p
  import apu_pkg::*;
  import apu_interrupt_map_pkg::*;
  import chip_pkg::*;
(
  /// Fast Clock, positive edge triggered
  input   wire i_clk,
  /// Ref Clock, positive edge triggered
  input   wire i_ref_clk,
  /// Asynchronous POR / always On reset, active low
  input   wire i_ao_rst_n,
  /// Asynchronous global reset, active low
  input   wire i_global_rst_n,

  /// Throttle sigs
  input  logic i_clock_throttle,
  input  logic i_thermal_throttle,

  /// Core NMI IRQs
  input  logic [CORE_WIDTH - 1:0] i_cores_nmi,
  /// External IRQs from AIC to APU
  output logic [APU_AIC_WIDTH - 1:0] o_aic_msip,
  output logic [APU_AIC_WIDTH - 1:0] o_aic_mtip,
  input  logic [APU_AIC_WIDTH - 1:0] i_aic_stoptime,
  /// External IRQs to APU
  input  logic i_irq__soc_mgmt__thermal_throttle,
  input  logic i_irq__soc_mgmt__thermal_warning,
  input  logic i_irq__soc_mgmt__thermal_shutdown,
  input  logic i_irq__lpddr_graph_0__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_graph_1__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_graph_2__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_graph_3__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_ppp_0__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_ppp_1__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_ppp_2__ctrl_derate_temp_limit,
  input  logic i_irq__lpddr_ppp_3__ctrl_derate_temp_limit,
  input  logic i_irq__soc_mgmt__dlm_warning,
  input  logic i_irq__soc_mgmt__dlm_critical,
  input  logic i_irq__lpddr_graph_0__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_graph_0__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_graph_0__phy_pie_prog_err,
  input  logic i_irq__lpddr_graph_0__phy_ecc_err,
  input  logic i_irq__lpddr_graph_0__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_graph_0__phy_pie_parity_err,
  input  logic i_irq__lpddr_graph_0__phy_acsm_parity_err,
  input  logic i_irq__lpddr_graph_1__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_graph_1__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_graph_1__phy_pie_prog_err,
  input  logic i_irq__lpddr_graph_1__phy_ecc_err,
  input  logic i_irq__lpddr_graph_1__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_graph_1__phy_pie_parity_err,
  input  logic i_irq__lpddr_graph_1__phy_acsm_parity_err,
  input  logic i_irq__lpddr_graph_2__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_graph_2__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_graph_2__phy_pie_prog_err,
  input  logic i_irq__lpddr_graph_2__phy_ecc_err,
  input  logic i_irq__lpddr_graph_2__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_graph_2__phy_pie_parity_err,
  input  logic i_irq__lpddr_graph_2__phy_acsm_parity_err,
  input  logic i_irq__lpddr_graph_3__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_graph_3__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_graph_3__phy_pie_prog_err,
  input  logic i_irq__lpddr_graph_3__phy_ecc_err,
  input  logic i_irq__lpddr_graph_3__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_graph_3__phy_pie_parity_err,
  input  logic i_irq__lpddr_graph_3__phy_acsm_parity_err,
  input  logic i_irq__lpddr_ppp_0__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_ppp_0__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_ppp_0__phy_pie_prog_err,
  input  logic i_irq__lpddr_ppp_0__phy_ecc_err,
  input  logic i_irq__lpddr_ppp_0__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_ppp_0__phy_pie_parity_err,
  input  logic i_irq__lpddr_ppp_0__phy_acsm_parity_err,
  input  logic i_irq__lpddr_ppp_1__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_ppp_1__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_ppp_1__phy_pie_prog_err,
  input  logic i_irq__lpddr_ppp_1__phy_ecc_err,
  input  logic i_irq__lpddr_ppp_1__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_ppp_1__phy_pie_parity_err,
  input  logic i_irq__lpddr_ppp_1__phy_acsm_parity_err,
  input  logic i_irq__lpddr_ppp_2__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_ppp_2__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_ppp_2__phy_pie_prog_err,
  input  logic i_irq__lpddr_ppp_2__phy_ecc_err,
  input  logic i_irq__lpddr_ppp_2__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_ppp_2__phy_pie_parity_err,
  input  logic i_irq__lpddr_ppp_2__phy_acsm_parity_err,
  input  logic i_irq__lpddr_ppp_3__ctrl_ecc_uncorrected_err,
  input  logic i_irq__lpddr_ppp_3__ctrl_rd_linkecc_uncorr_err,
  input  logic i_irq__lpddr_ppp_3__phy_pie_prog_err,
  input  logic i_irq__lpddr_ppp_3__phy_ecc_err,
  input  logic i_irq__lpddr_ppp_3__phy_rdfptrchk_err,
  input  logic i_irq__lpddr_ppp_3__phy_pie_parity_err,
  input  logic i_irq__lpddr_ppp_3__phy_acsm_parity_err,
  input  logic i_irq__pcie__perst_n,
  input  logic i_irq__sys_spm__error,
  input  logic i_irq__lpddr_graph_0__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_graph_0__phy_trng_fail,
  input  logic i_irq__lpddr_graph_1__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_graph_1__phy_trng_fail,
  input  logic i_irq__lpddr_graph_2__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_graph_2__phy_trng_fail,
  input  logic i_irq__lpddr_graph_3__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_graph_3__phy_trng_fail,
  input  logic i_irq__lpddr_ppp_0__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_ppp_0__phy_trng_fail,
  input  logic i_irq__lpddr_ppp_1__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_ppp_1__phy_trng_fail,
  input  logic i_irq__lpddr_ppp_2__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_ppp_2__phy_trng_fail,
  input  logic i_irq__lpddr_ppp_3__ctrl_ecc_ap_err,
  input  logic i_irq__lpddr_ppp_3__phy_trng_fail,
  input  logic i_irq__soc_mgmt__rtc,
  input  logic i_irq__soc_mgmt__wdt,
  input  logic i_irq__soc_periph__timer,
  input  logic i_irq__lpddr_graph_0__ctrl_sbr_done,
  input  logic i_irq__lpddr_graph_0__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_graph_0__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_graph_0__phy_init_cmplt,
  input  logic i_irq__lpddr_graph_0__phy_trng_cmplt,
  input  logic i_irq__lpddr_graph_1__ctrl_sbr_done,
  input  logic i_irq__lpddr_graph_1__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_graph_1__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_graph_1__phy_init_cmplt,
  input  logic i_irq__lpddr_graph_1__phy_trng_cmplt,
  input  logic i_irq__lpddr_graph_2__ctrl_sbr_done,
  input  logic i_irq__lpddr_graph_2__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_graph_2__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_graph_2__phy_init_cmplt,
  input  logic i_irq__lpddr_graph_2__phy_trng_cmplt,
  input  logic i_irq__lpddr_graph_3__ctrl_sbr_done,
  input  logic i_irq__lpddr_graph_3__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_graph_3__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_graph_3__phy_init_cmplt,
  input  logic i_irq__lpddr_graph_3__phy_trng_cmplt,
  input  logic i_irq__lpddr_ppp_0__ctrl_sbr_done,
  input  logic i_irq__lpddr_ppp_0__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_ppp_0__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_ppp_0__phy_init_cmplt,
  input  logic i_irq__lpddr_ppp_0__phy_trng_cmplt,
  input  logic i_irq__lpddr_ppp_1__ctrl_sbr_done,
  input  logic i_irq__lpddr_ppp_1__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_ppp_1__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_ppp_1__phy_init_cmplt,
  input  logic i_irq__lpddr_ppp_1__phy_trng_cmplt,
  input  logic i_irq__lpddr_ppp_2__ctrl_sbr_done,
  input  logic i_irq__lpddr_ppp_2__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_ppp_2__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_ppp_2__phy_init_cmplt,
  input  logic i_irq__lpddr_ppp_2__phy_trng_cmplt,
  input  logic i_irq__lpddr_ppp_3__ctrl_sbr_done,
  input  logic i_irq__lpddr_ppp_3__ctrl_ecc_corrected_err,
  input  logic i_irq__lpddr_ppp_3__ctrl_rd_linkecc_corr_err,
  input  logic i_irq__lpddr_ppp_3__phy_init_cmplt,
  input  logic i_irq__lpddr_ppp_3__phy_trng_cmplt,
  input  logic i_irq__soc_mgmt__security,
  input  logic i_irq__soc_periph__emmc,
  input  logic i_irq__dcd__int,
  input  logic i_irq__noc__int,
  input  logic i_irq__noc__sdma_0_int_0,
  input  logic i_irq__noc__sdma_0_int_1,
  input  logic i_irq__noc__sdma_0_int_2,
  input  logic i_irq__noc__sdma_0_int_3,
  input  logic i_irq__noc__sdma_1_int_0,
  input  logic i_irq__noc__sdma_1_int_1,
  input  logic i_irq__noc__sdma_1_int_2,
  input  logic i_irq__noc__sdma_1_int_3,
  input  logic i_irq__soc_periph__uart,
  input  logic i_irq__soc_periph__gpio,
  input  logic i_irq__soc_periph__i2c_0,
  input  logic i_irq__soc_periph__i2c_1,
  input  logic i_irq__soc_periph__spi,
  input  logic i_irq__pcie__int,

  /// Debug sigs
  input logic [CORE_WIDTH - 1:0] i_cores_debugint,
  input logic [CORE_WIDTH - 1:0] i_cores_resethaltreq,
  output logic [CORE_WIDTH - 1:0] o_cores_hart_unavail,
  output logic [CORE_WIDTH - 1:0] o_cores_hart_under_reset,

  //////////////////////////////////////////////
  /// SYS_CFG Bus
  //////////////////////////////////////////////
  input  chip_syscfg_addr_t       i_cfg_apb4_s_paddr,
  input  chip_apb_syscfg_data_t   i_cfg_apb4_s_pwdata,
  input  logic                    i_cfg_apb4_s_pwrite,
  input  logic                    i_cfg_apb4_s_psel,
  input  logic                    i_cfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t   i_cfg_apb4_s_pstrb,
  input  logic [3-1:0]            i_cfg_apb4_s_pprot,
  output logic                    o_cfg_apb4_s_pready,
  output chip_apb_syscfg_data_t   o_cfg_apb4_s_prdata,
  output logic                    o_cfg_apb4_s_pslverr,

  output logic o_noc_async_idle_req,
  input  logic i_noc_async_idle_ack,
  input  logic i_noc_async_idle_val,

  output logic o_noc_tok_async_idle_req,
  input  logic i_noc_tok_async_idle_ack,
  input  logic i_noc_tok_async_idle_val,

  output logic o_noc_clken,
  output logic o_noc_rst_n,

  /// NoC AXI Connections LP Init Port
  // AXI write address channel
  output chip_pkg::chip_axi_addr_t      o_apu_init_lt_axi_m_awaddr,
  output apu_axi_lt_s_id_t              o_apu_init_lt_axi_m_awid,
  output axi_pkg::axi_len_t             o_apu_init_lt_axi_m_awlen,
  output axi_pkg::axi_size_t            o_apu_init_lt_axi_m_awsize,
  output axi_pkg::axi_burst_t           o_apu_init_lt_axi_m_awburst,
  output axi_pkg::axi_cache_t           o_apu_init_lt_axi_m_awcache,
  output axi_pkg::axi_prot_t            o_apu_init_lt_axi_m_awprot,
  output logic                          o_apu_init_lt_axi_m_awlock,
  output axi_pkg::axi_qos_t             o_apu_init_lt_axi_m_awqos,
  output axi_pkg::axi_region_t          o_apu_init_lt_axi_m_awregion,
  output chip_pkg::chip_axi_lt_awuser_t o_apu_init_lt_axi_m_awuser,
  input  logic                          i_apu_init_lt_axi_m_awready,
  output logic                          o_apu_init_lt_axi_m_awvalid,
  // AXI write data channel
  output logic                          o_apu_init_lt_axi_m_wlast,
  output chip_pkg::chip_axi_lt_wstrb_t  o_apu_init_lt_axi_m_wstrb,
  output chip_pkg::chip_axi_lt_data_t   o_apu_init_lt_axi_m_wdata,
  output chip_pkg::chip_axi_lt_wuser_t  o_apu_init_lt_axi_m_wuser,
  input  logic                          i_apu_init_lt_axi_m_wready,
  output logic                          o_apu_init_lt_axi_m_wvalid,
  // AXI write response channel
  input  apu_axi_lt_s_id_t              i_apu_init_lt_axi_m_bid,
  input  axi_pkg::axi_resp_t            i_apu_init_lt_axi_m_bresp,
  input  chip_pkg::chip_axi_lt_buser_t  i_apu_init_lt_axi_m_buser,
  output logic                          o_apu_init_lt_axi_m_bready,
  input  logic                          i_apu_init_lt_axi_m_bvalid,
  // AXI read address channel
  output chip_pkg::chip_axi_addr_t      o_apu_init_lt_axi_m_araddr,
  output apu_axi_lt_s_id_t              o_apu_init_lt_axi_m_arid,
  output axi_pkg::axi_len_t             o_apu_init_lt_axi_m_arlen,
  output axi_pkg::axi_size_t            o_apu_init_lt_axi_m_arsize,
  output axi_pkg::axi_burst_t           o_apu_init_lt_axi_m_arburst,
  output axi_pkg::axi_cache_t           o_apu_init_lt_axi_m_arcache,
  output axi_pkg::axi_prot_t            o_apu_init_lt_axi_m_arprot,
  output axi_pkg::axi_qos_t             o_apu_init_lt_axi_m_arqos,
  output axi_pkg::axi_region_t          o_apu_init_lt_axi_m_arregion,
  output chip_pkg::chip_axi_lt_aruser_t o_apu_init_lt_axi_m_aruser,
  output logic                          o_apu_init_lt_axi_m_arlock,
  input  logic                          i_apu_init_lt_axi_m_arready,
  output logic                          o_apu_init_lt_axi_m_arvalid,
  // AXI read data/response channel
  input  logic                          i_apu_init_lt_axi_m_rlast,
  input  apu_axi_lt_s_id_t              i_apu_init_lt_axi_m_rid,
  input  chip_pkg::chip_axi_lt_data_t   i_apu_init_lt_axi_m_rdata,
  input  axi_pkg::axi_resp_t            i_apu_init_lt_axi_m_rresp,
  input  chip_pkg::chip_axi_lt_ruser_t  i_apu_init_lt_axi_m_ruser,
  output logic                          o_apu_init_lt_axi_m_rready,
  input  logic                          i_apu_init_lt_axi_m_rvalid,

  /// NoC AXI Connections LP Target Port
  // AXI write address channel
  input  chip_pkg::chip_axi_addr_t      i_apu_targ_lt_axi_s_awaddr,
  input  apu_axi_lt_m_id_t              i_apu_targ_lt_axi_s_awid,
  input  axi_pkg::axi_len_t             i_apu_targ_lt_axi_s_awlen,
  input  axi_pkg::axi_size_t            i_apu_targ_lt_axi_s_awsize,
  input  axi_pkg::axi_burst_t           i_apu_targ_lt_axi_s_awburst,
  input  axi_pkg::axi_cache_t           i_apu_targ_lt_axi_s_awcache,
  input  axi_pkg::axi_prot_t            i_apu_targ_lt_axi_s_awprot,
  input  logic                          i_apu_targ_lt_axi_s_awlock,
  input  axi_pkg::axi_qos_t             i_apu_targ_lt_axi_s_awqos,
  input  axi_pkg::axi_region_t          i_apu_targ_lt_axi_s_awregion,
  input  chip_pkg::chip_axi_lt_awuser_t i_apu_targ_lt_axi_s_awuser,
  output logic                          o_apu_targ_lt_axi_s_awready,
  input  logic                          i_apu_targ_lt_axi_s_awvalid,
  // AXI write data channel
  input  logic                          i_apu_targ_lt_axi_s_wlast,
  input  chip_pkg::chip_axi_lt_wstrb_t  i_apu_targ_lt_axi_s_wstrb,
  input  chip_pkg::chip_axi_lt_data_t   i_apu_targ_lt_axi_s_wdata,
  input  chip_pkg::chip_axi_lt_wuser_t  i_apu_targ_lt_axi_s_wuser,
  output logic                          o_apu_targ_lt_axi_s_wready,
  input  logic                          i_apu_targ_lt_axi_s_wvalid,
  // AXI write response channel
  output apu_axi_lt_m_id_t              o_apu_targ_lt_axi_s_bid,
  output axi_pkg::axi_resp_t            o_apu_targ_lt_axi_s_bresp,
  output chip_pkg::chip_axi_lt_buser_t  o_apu_targ_lt_axi_s_buser,
  input  logic                          i_apu_targ_lt_axi_s_bready,
  output logic                          o_apu_targ_lt_axi_s_bvalid,
  // AXI read address channel
  input  chip_pkg::chip_axi_addr_t      i_apu_targ_lt_axi_s_araddr,
  input  apu_axi_lt_m_id_t              i_apu_targ_lt_axi_s_arid,
  input  axi_pkg::axi_len_t             i_apu_targ_lt_axi_s_arlen,
  input  axi_pkg::axi_size_t            i_apu_targ_lt_axi_s_arsize,
  input  axi_pkg::axi_burst_t           i_apu_targ_lt_axi_s_arburst,
  input  axi_pkg::axi_cache_t           i_apu_targ_lt_axi_s_arcache,
  input  axi_pkg::axi_prot_t            i_apu_targ_lt_axi_s_arprot,
  input  axi_pkg::axi_qos_t             i_apu_targ_lt_axi_s_arqos,
  input  axi_pkg::axi_region_t          i_apu_targ_lt_axi_s_arregion,
  input  chip_pkg::chip_axi_lt_aruser_t i_apu_targ_lt_axi_s_aruser,
  input  logic                          i_apu_targ_lt_axi_s_arlock,
  output logic                          o_apu_targ_lt_axi_s_arready,
  input  logic                          i_apu_targ_lt_axi_s_arvalid,
  // AXI read data/response channel
  output logic                          o_apu_targ_lt_axi_s_rlast,
  output apu_axi_lt_m_id_t              o_apu_targ_lt_axi_s_rid,
  output chip_pkg::chip_axi_lt_data_t   o_apu_targ_lt_axi_s_rdata,
  output axi_pkg::axi_resp_t            o_apu_targ_lt_axi_s_rresp,
  output chip_pkg::chip_axi_lt_ruser_t  o_apu_targ_lt_axi_s_ruser,
  input  logic                          i_apu_targ_lt_axi_s_rready,
  output logic                          o_apu_targ_lt_axi_s_rvalid,

  /// NoC Connections HP AXI Init Interface
  // AXI write address channel
  output chip_pkg::chip_axi_addr_t      o_apu_init_mt_axi_m_awaddr,
  output apu_axi_mt_m_id_t              o_apu_init_mt_axi_m_awid,
  output axi_pkg::axi_len_t             o_apu_init_mt_axi_m_awlen,
  output axi_pkg::axi_size_t            o_apu_init_mt_axi_m_awsize,
  output axi_pkg::axi_burst_t           o_apu_init_mt_axi_m_awburst,
  output axi_pkg::axi_cache_t           o_apu_init_mt_axi_m_awcache,
  output axi_pkg::axi_prot_t            o_apu_init_mt_axi_m_awprot,
  output logic                          o_apu_init_mt_axi_m_awlock,
  output axi_pkg::axi_qos_t             o_apu_init_mt_axi_m_awqos,
  output axi_pkg::axi_region_t          o_apu_init_mt_axi_m_awregion,
  output chip_pkg::chip_axi_mt_awuser_t o_apu_init_mt_axi_m_awuser,
  input  logic                          i_apu_init_mt_axi_m_awready,
  output logic                          o_apu_init_mt_axi_m_awvalid,
  // AXI write data channel
  output logic                          o_apu_init_mt_axi_m_wlast,
  output apu_axi_mt_wstrb_t             o_apu_init_mt_axi_m_wstrb,
  output apu_axi_mt_data_t              o_apu_init_mt_axi_m_wdata,
  output chip_pkg::chip_axi_mt_wuser_t  o_apu_init_mt_axi_m_wuser,
  input  logic                          i_apu_init_mt_axi_m_wready,
  output logic                          o_apu_init_mt_axi_m_wvalid,
  // AXI write response channel
  input  apu_axi_mt_m_id_t              i_apu_init_mt_axi_m_bid,
  input  axi_pkg::axi_resp_t            i_apu_init_mt_axi_m_bresp,
  input  chip_pkg::chip_axi_mt_buser_t  i_apu_init_mt_axi_m_buser,
  output logic                          o_apu_init_mt_axi_m_bready,
  input  logic                          i_apu_init_mt_axi_m_bvalid,
  // AXI read address channel
  output chip_pkg::chip_axi_addr_t      o_apu_init_mt_axi_m_araddr,
  output apu_axi_mt_m_id_t              o_apu_init_mt_axi_m_arid,
  output axi_pkg::axi_len_t             o_apu_init_mt_axi_m_arlen,
  output axi_pkg::axi_size_t            o_apu_init_mt_axi_m_arsize,
  output axi_pkg::axi_burst_t           o_apu_init_mt_axi_m_arburst,
  output axi_pkg::axi_cache_t           o_apu_init_mt_axi_m_arcache,
  output axi_pkg::axi_prot_t            o_apu_init_mt_axi_m_arprot,
  output axi_pkg::axi_qos_t             o_apu_init_mt_axi_m_arqos,
  output axi_pkg::axi_region_t          o_apu_init_mt_axi_m_arregion,
  output chip_pkg::chip_axi_mt_aruser_t o_apu_init_mt_axi_m_aruser,
  output logic                          o_apu_init_mt_axi_m_arlock,
  input  logic                          i_apu_init_mt_axi_m_arready,
  output logic                          o_apu_init_mt_axi_m_arvalid,
  // AXI read data/response channel
  input  logic                          i_apu_init_mt_axi_m_rlast,
  input  apu_axi_mt_m_id_t              i_apu_init_mt_axi_m_rid,
  input  apu_axi_mt_data_t              i_apu_init_mt_axi_m_rdata,
  input  axi_pkg::axi_resp_t            i_apu_init_mt_axi_m_rresp,
  input  chip_pkg::chip_axi_mt_ruser_t  i_apu_init_mt_axi_m_ruser,
  output logic                          o_apu_init_mt_axi_m_rready,
  input  logic                          i_apu_init_mt_axi_m_rvalid,

  // TODO - Placeholder signals for skeleton. To be reviewed and finalized in Bronze.

  // Token network
  output chip_pkg::chip_ocpl_token_addr_t o_tok_prod_ocpl_m_maddr,
  output chip_pkg::chip_ocpl_token_data_t o_tok_prod_ocpl_m_mdata,
  output logic                            o_tok_prod_ocpl_m_mcmd,
  input  logic                            i_tok_prod_ocpl_m_scmdaccept,
  input  chip_pkg::chip_ocpl_token_addr_t i_tok_cons_ocpl_s_maddr,
  input  chip_pkg::chip_ocpl_token_data_t i_tok_cons_ocpl_s_mdata,
  input  logic                            i_tok_cons_ocpl_s_mcmd,
  output logic                            o_tok_cons_ocpl_s_scmdaccept,

  // PVT remote sensor
  inout wire io_ibias_ts,
  inout wire io_vsense_ts,

  /// DFT signals
  input  wire  tck,
  input  wire  trst,
  input  logic tms,
  input  logic tdi,
  output logic tdo_en,
  output logic tdo,

  input  logic test_mode,

  input  wire  ssn_bus_clk,
  input  logic [23:0] ssn_bus_data_in,
  output logic [23:0] ssn_bus_data_out,
  input  wire  bisr_clk,
  input  wire  bisr_reset,
  input  logic bisr_shift_en,
  input  logic bisr_si,
  output logic bisr_so

  // TODO - Add Placeholder signals for the Trace Bus

);

  // binding for DFT, driven after DFT insertion
  logic scan_en = 0;

  pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;
  apu_ao_csr_reg_pkg::apu_ao_csr_reg2hw_t reg2hw;
  apu_ao_csr_reg_pkg::apu_ao_csr_hw2reg_t hw2reg;

  wire [CORE_WIDTH - 1:0] cores_clk;
  wire [CORE_WIDTH - 1:0] cores_rst_n;
  wire aclk;
  wire aclk_free;
  wire arst_n;
  wire l2c_clk;
  wire l2c_rst_n;
  wire ao_rst_sync_n;

  logic [APU_FAST_CLK_WIDTH-1:0] noc_clken;
  // Notify NoC if AXI bus clk is active
  always_comb o_noc_clken = noc_clken[0];

  // DFT request
  wire ref_clk_buf;
  axe_tcl_clk_buffer u_ref_clk_occ_buf (
    .i_clk(i_ref_clk),
    .o_clk(ref_clk_buf)
  );

  pctl #(
    .N_FAST_CLKS(APU_FAST_CLK_WIDTH),
    .N_RESETS   (APU_FAST_CLK_WIDTH),
    .N_MEM_PG   (1),
    .N_FENCES   (2),
    .N_THROTTLE_PINS(2),
    .CLKRST_MATRIX({
      8'b1000_0000,
      8'b0100_0000,
      8'b0010_0000,
      8'b0001_0000,
      8'b0000_1000,
      8'b0000_0100,
      8'b0000_0010,
      8'b0000_0001
    }),
    .PLL_CLK_IS_I_CLK('0),
    .NOC_RST_IDX(0),
    .SYNC_CLK_IDX(0),
    .AUTO_RESET_REMOVE(1'b1),
    .AUTO_FENCE_REMOVE(1'b1),
    .paddr_t    (chip_syscfg_addr_t),
    .pdata_t    (chip_apb_syscfg_data_t),
    .pstrb_t    (chip_apb_syscfg_strb_t)
  ) u_pctl (
    .i_clk(ref_clk_buf),
    .i_ao_rst_n,
    .i_global_rst_n,
    .i_test_mode(test_mode),

    .i_pll_clk({APU_FAST_CLK_WIDTH{i_clk}}),
    .o_partition_clk({cores_clk, l2c_clk, aclk_free}),

    .o_partition_rst_n({cores_rst_n, l2c_rst_n, arst_n}),
    .o_ao_rst_sync_n(ao_rst_sync_n),

    .o_noc_async_idle_req({o_noc_tok_async_idle_req, o_noc_async_idle_req}),
    .i_noc_async_idle_ack({i_noc_tok_async_idle_ack, i_noc_async_idle_ack}),
    .i_noc_async_idle_val({i_noc_tok_async_idle_val, i_noc_async_idle_val}),
    .o_noc_clken(noc_clken),
    .o_noc_rst_n,

    .o_int_shutdown_req(),
    .i_int_shutdown_ack(1'b1),

    .o_ret(),
    .o_pde(),
    .i_prn(1'b0),

    .i_global_sync_async(1'b0),
    .o_global_sync(),

    .i_throttle({i_thermal_throttle, i_clock_throttle}),

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

    .o_ao_csr_apb_req(ao_csr_apb_req),
    .i_ao_csr_apb_rsp(ao_csr_apb_rsp)
  );

  axe_tcl_clk_buffer u_aclk_occ_hookup_buf (
    .i_clk(aclk_free),
    .o_clk(aclk)
  );

  apu_ao_csr_reg_top u_apu_ao_csr (
    .clk_i(ref_clk_buf),
    .rst_ni(ao_rst_sync_n),
    .apb_i(ao_csr_apb_req),
    .apb_o(ao_csr_apb_rsp),
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  // Disable init
  logic [CORE_WIDTH - 1:0] i_cores_disable_init;
  logic i_l2c_disable_init;

  // Cores cfg
  logic [CORE_WIDTH - 1:0][47:0] i_cores_reset_vector;

  // SRAM impl signals
  axe_tcl_sram_pkg::impl_inp_t [CORE_WIDTH - 1:0] i_cores_ctrl;
  axe_tcl_sram_pkg::impl_oup_t [CORE_WIDTH - 1:0] o_cores_ctrl;
  axe_tcl_sram_pkg::impl_inp_t i_l2c_ctrl;
  axe_tcl_sram_pkg::impl_oup_t o_l2c_ctrl;
  axe_tcl_sram_pkg::impl_inp_t i_dma_ctrl;
  axe_tcl_sram_pkg::impl_oup_t o_dma_ctrl;
  axe_tcl_sram_pkg::impl_inp_rom_t i_rom_ctrl;
  axe_tcl_sram_pkg::impl_oup_rom_t o_rom_ctrl;

  for (genvar i = 0; unsigned'(i) < CORE_WIDTH; i++) begin: g_ao_csr_cores_connectivity
    always_comb i_cores_disable_init[i] = reg2hw.apu_core_disable_init[i];

    always_comb i_cores_reset_vector[i] = { reg2hw.apu_core_reset_vector_high[i], reg2hw.apu_core_reset_vector_low[i] };

    always_comb i_cores_ctrl[i].mcsw = axe_tcl_pkg::MCSW; // TODO(vincent.morillon): statically assigned but overriden in the macro
    always_comb i_cores_ctrl[i].mcs = axe_tcl_pkg::MCS;   // TODO(vincent.morillon): statically assigned but overriden in the macro
    always_comb i_cores_ctrl[i].adme = axe_tcl_pkg::ADME; // TODO(vincent.morillon): statically assigned but overriden in the macro
    always_comb i_cores_ctrl[i].ret = reg2hw.apu_core_mem_power_mode[i].ret;
    always_comb i_cores_ctrl[i].pde = reg2hw.apu_core_mem_power_mode[i].pde;
    always_comb hw2reg.apu_core_mem_power_up_ready[i] = o_cores_ctrl[i].prn;
  end

  always_comb i_l2c_disable_init = reg2hw.apu_l2c_disable_init;

  always_comb i_l2c_ctrl.mcsw = axe_tcl_pkg::MCSW; // TODO(vincent.morillon): statically assigned but overriden in the macro
  always_comb i_l2c_ctrl.mcs = axe_tcl_pkg::MCS;   // TODO(vincent.morillon): statically assigned but overriden in the macro
  always_comb i_l2c_ctrl.adme = axe_tcl_pkg::ADME; // TODO(vincent.morillon): statically assigned but overriden in the macro
  always_comb i_l2c_ctrl.ret = reg2hw.apu_l2c_mem_power_mode.ret;
  always_comb i_l2c_ctrl.pde = reg2hw.apu_l2c_mem_power_mode.pde;
  always_comb hw2reg.apu_l2c_mem_power_up_ready = o_l2c_ctrl.prn;

  always_comb i_dma_ctrl.se = scan_en;
  always_comb i_dma_ctrl.mcsw = axe_tcl_pkg::MCSW; // TODO(vincent.morillon): statically assigned but overriden in the macro
  always_comb i_dma_ctrl.mcs = axe_tcl_pkg::MCS;   // TODO(vincent.morillon): statically assigned but overriden in the macro
  always_comb i_dma_ctrl.adme = axe_tcl_pkg::ADME; // TODO(vincent.morillon): statically assigned but overriden in the macro
  always_comb i_dma_ctrl.ret = reg2hw.apu_dma_mem_power_mode.ret;
  always_comb i_dma_ctrl.pde = reg2hw.apu_dma_mem_power_mode.pde;
  always_comb hw2reg.apu_dma_mem_power_up_ready = o_dma_ctrl.prn;

  always_comb i_rom_ctrl.se = scan_en;
  always_comb i_rom_ctrl.pde = reg2hw.apu_rom_mem_power_mode;
  always_comb hw2reg.apu_rom_mem_power_up_ready = o_rom_ctrl.prn;

  // Connect external IRQs to struct
  apu_external_irqs_t external_irqs;
  apu_interrupt_connectivity_external u_apu_irqs_connect_ext (
    .o_external_irqs(external_irqs),
    .*
  );

  // AXI cut
  /// NoC AXI Connections LP Init Port
  apu_axi_lt_s_aw_t if_apu_init_lt_axi_m_aw;
  apu_axi_lt_w_t if_apu_init_lt_axi_m_w;
  apu_axi_lt_s_b_t if_apu_init_lt_axi_m_b;
  apu_axi_lt_s_ar_t if_apu_init_lt_axi_m_ar;
  apu_axi_lt_s_r_t if_apu_init_lt_axi_m_r;

  // AXI write address channel
  always_comb o_apu_init_lt_axi_m_awaddr = if_apu_init_lt_axi_m_aw.addr;
  always_comb o_apu_init_lt_axi_m_awid = if_apu_init_lt_axi_m_aw.id;
  always_comb o_apu_init_lt_axi_m_awlen = if_apu_init_lt_axi_m_aw.len;
  always_comb o_apu_init_lt_axi_m_awsize = if_apu_init_lt_axi_m_aw.size;
  always_comb o_apu_init_lt_axi_m_awburst = if_apu_init_lt_axi_m_aw.burst;
  always_comb o_apu_init_lt_axi_m_awcache = if_apu_init_lt_axi_m_aw.cache;
  always_comb o_apu_init_lt_axi_m_awprot = if_apu_init_lt_axi_m_aw.prot;
  always_comb o_apu_init_lt_axi_m_awlock = if_apu_init_lt_axi_m_aw.lock;
  always_comb o_apu_init_lt_axi_m_awqos = if_apu_init_lt_axi_m_aw.qos;
  always_comb o_apu_init_lt_axi_m_awregion = if_apu_init_lt_axi_m_aw.region;
  always_comb o_apu_init_lt_axi_m_awuser = if_apu_init_lt_axi_m_aw.user;
  // AXI write data channel
  always_comb o_apu_init_lt_axi_m_wlast = if_apu_init_lt_axi_m_w.last;
  always_comb o_apu_init_lt_axi_m_wstrb = if_apu_init_lt_axi_m_w.strb;
  always_comb o_apu_init_lt_axi_m_wdata = if_apu_init_lt_axi_m_w.data;
  always_comb o_apu_init_lt_axi_m_wuser = if_apu_init_lt_axi_m_w.user;
  // AXI write response channel
  always_comb if_apu_init_lt_axi_m_b.id = i_apu_init_lt_axi_m_bid;
  always_comb if_apu_init_lt_axi_m_b.resp = axi_pkg::axi_resp_e'(i_apu_init_lt_axi_m_bresp);
  always_comb if_apu_init_lt_axi_m_b.user = i_apu_init_lt_axi_m_buser;
  // AXI read address channel
  always_comb o_apu_init_lt_axi_m_araddr = if_apu_init_lt_axi_m_ar.addr;
  always_comb o_apu_init_lt_axi_m_arid = if_apu_init_lt_axi_m_ar.id;
  always_comb o_apu_init_lt_axi_m_arlen = if_apu_init_lt_axi_m_ar.len;
  always_comb o_apu_init_lt_axi_m_arsize = if_apu_init_lt_axi_m_ar.size;
  always_comb o_apu_init_lt_axi_m_arburst = if_apu_init_lt_axi_m_ar.burst;
  always_comb o_apu_init_lt_axi_m_arcache = if_apu_init_lt_axi_m_ar.cache;
  always_comb o_apu_init_lt_axi_m_arprot = if_apu_init_lt_axi_m_ar.prot;
  always_comb o_apu_init_lt_axi_m_arqos = if_apu_init_lt_axi_m_ar.qos;
  always_comb o_apu_init_lt_axi_m_arregion = if_apu_init_lt_axi_m_ar.region;
  always_comb o_apu_init_lt_axi_m_aruser = if_apu_init_lt_axi_m_ar.user;
  always_comb o_apu_init_lt_axi_m_arlock = if_apu_init_lt_axi_m_ar.lock;
  // AXI read data/response channel
  always_comb if_apu_init_lt_axi_m_r.last = i_apu_init_lt_axi_m_rlast;
  always_comb if_apu_init_lt_axi_m_r.id = i_apu_init_lt_axi_m_rid;
  always_comb if_apu_init_lt_axi_m_r.data = i_apu_init_lt_axi_m_rdata;
  always_comb if_apu_init_lt_axi_m_r.resp = axi_pkg::axi_resp_e'(i_apu_init_lt_axi_m_rresp);
  always_comb if_apu_init_lt_axi_m_r.user = i_apu_init_lt_axi_m_ruser;

  apu_axi_lt_s_aw_t apu_init_lt_axi_m_aw;
  logic apu_init_lt_axi_m_awready;
  logic apu_init_lt_axi_m_awvalid;
  apu_axi_lt_w_t apu_init_lt_axi_m_w;
  logic apu_init_lt_axi_m_wready;
  logic apu_init_lt_axi_m_wvalid;
  apu_axi_lt_s_b_t apu_init_lt_axi_m_b;
  logic apu_init_lt_axi_m_bready;
  logic apu_init_lt_axi_m_bvalid;
  apu_axi_lt_s_ar_t apu_init_lt_axi_m_ar;
  logic apu_init_lt_axi_m_arready;
  logic apu_init_lt_axi_m_arvalid;
  apu_axi_lt_s_r_t apu_init_lt_axi_m_r;
  logic apu_init_lt_axi_m_rready;
  logic apu_init_lt_axi_m_rvalid;

  axe_axi_multicut #(
    .NumCuts(2), // Number of cuts.
    // AXI structs
    .axi_aw_t(apu_axi_lt_s_aw_t),
    .axi_w_t (apu_axi_lt_w_t),
    .axi_b_t (apu_axi_lt_s_b_t),
    .axi_ar_t(apu_axi_lt_s_ar_t),
    .axi_r_t (apu_axi_lt_s_r_t)
  ) u_axi_cut_lt_init (
    .i_clk(aclk),
    .i_rst_n(arst_n),

    .i_axi_s_aw      (apu_init_lt_axi_m_aw),
    .o_axi_s_aw_ready(apu_init_lt_axi_m_awready),
    .i_axi_s_aw_valid(apu_init_lt_axi_m_awvalid),
    .i_axi_s_w       (apu_init_lt_axi_m_w),
    .o_axi_s_w_ready (apu_init_lt_axi_m_wready),
    .i_axi_s_w_valid (apu_init_lt_axi_m_wvalid),
    .o_axi_s_b       (apu_init_lt_axi_m_b),
    .i_axi_s_b_ready (apu_init_lt_axi_m_bready),
    .o_axi_s_b_valid (apu_init_lt_axi_m_bvalid),
    .i_axi_s_ar      (apu_init_lt_axi_m_ar),
    .o_axi_s_ar_ready(apu_init_lt_axi_m_arready),
    .i_axi_s_ar_valid(apu_init_lt_axi_m_arvalid),
    .o_axi_s_r       (apu_init_lt_axi_m_r),
    .i_axi_s_r_ready (apu_init_lt_axi_m_rready),
    .o_axi_s_r_valid (apu_init_lt_axi_m_rvalid),

    .o_axi_m_aw      (if_apu_init_lt_axi_m_aw),
    .i_axi_m_aw_ready(i_apu_init_lt_axi_m_awready),
    .o_axi_m_aw_valid(o_apu_init_lt_axi_m_awvalid),
    .o_axi_m_w       (if_apu_init_lt_axi_m_w),
    .i_axi_m_w_ready (i_apu_init_lt_axi_m_wready),
    .o_axi_m_w_valid (o_apu_init_lt_axi_m_wvalid),
    .i_axi_m_b       (if_apu_init_lt_axi_m_b),
    .o_axi_m_b_ready (o_apu_init_lt_axi_m_bready),
    .i_axi_m_b_valid (i_apu_init_lt_axi_m_bvalid),
    .o_axi_m_ar      (if_apu_init_lt_axi_m_ar),
    .i_axi_m_ar_ready(i_apu_init_lt_axi_m_arready),
    .o_axi_m_ar_valid(o_apu_init_lt_axi_m_arvalid),
    .i_axi_m_r       (if_apu_init_lt_axi_m_r),
    .o_axi_m_r_ready (o_apu_init_lt_axi_m_rready),
    .i_axi_m_r_valid (i_apu_init_lt_axi_m_rvalid)
  );

  /// NoC AXI Connections LP Target Port
  apu_axi_lt_m_aw_t if_apu_targ_lt_axi_s_aw;
  apu_axi_lt_w_t if_apu_targ_lt_axi_s_w;
  apu_axi_lt_m_b_t if_apu_targ_lt_axi_s_b;
  apu_axi_lt_m_ar_t if_apu_targ_lt_axi_s_ar;
  apu_axi_lt_m_r_t if_apu_targ_lt_axi_s_r;

  // AXI write address channel
  always_comb if_apu_targ_lt_axi_s_aw.addr = i_apu_targ_lt_axi_s_awaddr;
  always_comb if_apu_targ_lt_axi_s_aw.id = i_apu_targ_lt_axi_s_awid;
  always_comb if_apu_targ_lt_axi_s_aw.len = i_apu_targ_lt_axi_s_awlen;
  always_comb if_apu_targ_lt_axi_s_aw.size = axi_pkg::axi_size_e'(i_apu_targ_lt_axi_s_awsize);
  always_comb if_apu_targ_lt_axi_s_aw.burst = axi_pkg::axi_burst_e'(i_apu_targ_lt_axi_s_awburst);
  always_comb if_apu_targ_lt_axi_s_aw.cache = i_apu_targ_lt_axi_s_awcache;
  always_comb if_apu_targ_lt_axi_s_aw.prot = i_apu_targ_lt_axi_s_awprot;
  always_comb if_apu_targ_lt_axi_s_aw.lock = i_apu_targ_lt_axi_s_awlock;
  always_comb if_apu_targ_lt_axi_s_aw.qos = i_apu_targ_lt_axi_s_awqos;
  always_comb if_apu_targ_lt_axi_s_aw.region = i_apu_targ_lt_axi_s_awregion;
  always_comb if_apu_targ_lt_axi_s_aw.user = i_apu_targ_lt_axi_s_awuser;
  // AXI write data channel
  always_comb if_apu_targ_lt_axi_s_w.last = i_apu_targ_lt_axi_s_wlast;
  always_comb if_apu_targ_lt_axi_s_w.strb = i_apu_targ_lt_axi_s_wstrb;
  always_comb if_apu_targ_lt_axi_s_w.data = i_apu_targ_lt_axi_s_wdata;
  always_comb if_apu_targ_lt_axi_s_w.user = i_apu_targ_lt_axi_s_wuser;
  // AXI write response channel
  always_comb o_apu_targ_lt_axi_s_bid = if_apu_targ_lt_axi_s_b.id;
  always_comb o_apu_targ_lt_axi_s_bresp = if_apu_targ_lt_axi_s_b.resp;
  always_comb o_apu_targ_lt_axi_s_buser = if_apu_targ_lt_axi_s_b.user;
  // AXI read address channel
  always_comb if_apu_targ_lt_axi_s_ar.addr = i_apu_targ_lt_axi_s_araddr;
  always_comb if_apu_targ_lt_axi_s_ar.id = i_apu_targ_lt_axi_s_arid;
  always_comb if_apu_targ_lt_axi_s_ar.len = i_apu_targ_lt_axi_s_arlen;
  always_comb if_apu_targ_lt_axi_s_ar.size = axi_pkg::axi_size_e'(i_apu_targ_lt_axi_s_arsize);
  always_comb if_apu_targ_lt_axi_s_ar.burst = axi_pkg::axi_burst_e'(i_apu_targ_lt_axi_s_arburst);
  always_comb if_apu_targ_lt_axi_s_ar.cache = i_apu_targ_lt_axi_s_arcache;
  always_comb if_apu_targ_lt_axi_s_ar.prot = i_apu_targ_lt_axi_s_arprot;
  always_comb if_apu_targ_lt_axi_s_ar.qos = i_apu_targ_lt_axi_s_arqos;
  always_comb if_apu_targ_lt_axi_s_ar.region = i_apu_targ_lt_axi_s_arregion;
  always_comb if_apu_targ_lt_axi_s_ar.user = i_apu_targ_lt_axi_s_aruser;
  always_comb if_apu_targ_lt_axi_s_ar.lock = i_apu_targ_lt_axi_s_arlock;
  // AXI read data/response channel
  always_comb o_apu_targ_lt_axi_s_rlast = if_apu_targ_lt_axi_s_r.last;
  always_comb o_apu_targ_lt_axi_s_rid = if_apu_targ_lt_axi_s_r.id;
  always_comb o_apu_targ_lt_axi_s_rdata = if_apu_targ_lt_axi_s_r.data;
  always_comb o_apu_targ_lt_axi_s_rresp = if_apu_targ_lt_axi_s_r.resp;
  always_comb o_apu_targ_lt_axi_s_ruser = if_apu_targ_lt_axi_s_r.user;

  apu_axi_lt_m_aw_t apu_targ_lt_axi_s_aw;
  logic apu_targ_lt_axi_s_awready;
  logic apu_targ_lt_axi_s_awvalid;
  apu_axi_lt_w_t apu_targ_lt_axi_s_w;
  logic apu_targ_lt_axi_s_wready;
  logic apu_targ_lt_axi_s_wvalid;
  apu_axi_lt_m_b_t apu_targ_lt_axi_s_b;
  logic apu_targ_lt_axi_s_bready;
  logic apu_targ_lt_axi_s_bvalid;
  apu_axi_lt_m_ar_t apu_targ_lt_axi_s_ar;
  logic apu_targ_lt_axi_s_arready;
  logic apu_targ_lt_axi_s_arvalid;
  apu_axi_lt_m_r_t apu_targ_lt_axi_s_r;
  logic apu_targ_lt_axi_s_rready;
  logic apu_targ_lt_axi_s_rvalid;

  axe_axi_multicut #(
    .NumCuts(2), // Number of cuts.
    // AXI structs
    .axi_aw_t(apu_axi_lt_m_aw_t),
    .axi_w_t (apu_axi_lt_w_t),
    .axi_b_t (apu_axi_lt_m_b_t),
    .axi_ar_t(apu_axi_lt_m_ar_t),
    .axi_r_t (apu_axi_lt_m_r_t)
  ) u_axi_cut_lt_targ (
    .i_clk(aclk),
    .i_rst_n(arst_n),

    .i_axi_s_aw      (if_apu_targ_lt_axi_s_aw),
    .o_axi_s_aw_ready(o_apu_targ_lt_axi_s_awready),
    .i_axi_s_aw_valid(i_apu_targ_lt_axi_s_awvalid),
    .i_axi_s_w       (if_apu_targ_lt_axi_s_w),
    .o_axi_s_w_ready (o_apu_targ_lt_axi_s_wready),
    .i_axi_s_w_valid (i_apu_targ_lt_axi_s_wvalid),
    .o_axi_s_b       (if_apu_targ_lt_axi_s_b),
    .i_axi_s_b_ready (i_apu_targ_lt_axi_s_bready),
    .o_axi_s_b_valid (o_apu_targ_lt_axi_s_bvalid),
    .i_axi_s_ar      (if_apu_targ_lt_axi_s_ar),
    .o_axi_s_ar_ready(o_apu_targ_lt_axi_s_arready),
    .i_axi_s_ar_valid(i_apu_targ_lt_axi_s_arvalid),
    .o_axi_s_r       (if_apu_targ_lt_axi_s_r),
    .i_axi_s_r_ready (i_apu_targ_lt_axi_s_rready),
    .o_axi_s_r_valid (o_apu_targ_lt_axi_s_rvalid),

    .o_axi_m_aw      (apu_targ_lt_axi_s_aw),
    .i_axi_m_aw_ready(apu_targ_lt_axi_s_awready),
    .o_axi_m_aw_valid(apu_targ_lt_axi_s_awvalid),
    .o_axi_m_w       (apu_targ_lt_axi_s_w),
    .i_axi_m_w_ready (apu_targ_lt_axi_s_wready),
    .o_axi_m_w_valid (apu_targ_lt_axi_s_wvalid),
    .i_axi_m_b       (apu_targ_lt_axi_s_b),
    .o_axi_m_b_ready (apu_targ_lt_axi_s_bready),
    .i_axi_m_b_valid (apu_targ_lt_axi_s_bvalid),
    .o_axi_m_ar      (apu_targ_lt_axi_s_ar),
    .i_axi_m_ar_ready(apu_targ_lt_axi_s_arready),
    .o_axi_m_ar_valid(apu_targ_lt_axi_s_arvalid),
    .i_axi_m_r       (apu_targ_lt_axi_s_r),
    .o_axi_m_r_ready (apu_targ_lt_axi_s_rready),
    .i_axi_m_r_valid (apu_targ_lt_axi_s_rvalid)
  );

  /// NoC Connections HP AXI Init Interface
  apu_axi_mt_m_aw_t if_apu_init_mt_axi_m_aw;
  apu_axi_mt_w_t if_apu_init_mt_axi_m_w;
  apu_axi_mt_m_b_t if_apu_init_mt_axi_m_b;
  apu_axi_mt_m_ar_t if_apu_init_mt_axi_m_ar;
  apu_axi_mt_m_r_t if_apu_init_mt_axi_m_r;

  // AXI write address channel
  always_comb o_apu_init_mt_axi_m_awaddr = if_apu_init_mt_axi_m_aw.addr;
  always_comb o_apu_init_mt_axi_m_awid = if_apu_init_mt_axi_m_aw.id;
  always_comb o_apu_init_mt_axi_m_awlen = if_apu_init_mt_axi_m_aw.len;
  always_comb o_apu_init_mt_axi_m_awsize = if_apu_init_mt_axi_m_aw.size;
  always_comb o_apu_init_mt_axi_m_awburst = if_apu_init_mt_axi_m_aw.burst;
  always_comb o_apu_init_mt_axi_m_awcache = if_apu_init_mt_axi_m_aw.cache;
  always_comb o_apu_init_mt_axi_m_awprot = if_apu_init_mt_axi_m_aw.prot;
  always_comb o_apu_init_mt_axi_m_awlock = if_apu_init_mt_axi_m_aw.lock;
  always_comb o_apu_init_mt_axi_m_awqos = if_apu_init_mt_axi_m_aw.qos;
  always_comb o_apu_init_mt_axi_m_awregion = if_apu_init_mt_axi_m_aw.region;
  always_comb o_apu_init_mt_axi_m_awuser = if_apu_init_mt_axi_m_aw.user;
  // AXI write data channel
  always_comb o_apu_init_mt_axi_m_wlast = if_apu_init_mt_axi_m_w.last;
  always_comb o_apu_init_mt_axi_m_wstrb = if_apu_init_mt_axi_m_w.strb;
  always_comb o_apu_init_mt_axi_m_wdata = if_apu_init_mt_axi_m_w.data;
  always_comb o_apu_init_mt_axi_m_wuser = if_apu_init_mt_axi_m_w.user;
  // AXI write response channel
  always_comb if_apu_init_mt_axi_m_b.id = i_apu_init_mt_axi_m_bid;
  always_comb if_apu_init_mt_axi_m_b.resp = axi_pkg::axi_resp_e'(i_apu_init_mt_axi_m_bresp);
  always_comb if_apu_init_mt_axi_m_b.user = i_apu_init_mt_axi_m_buser;
  // AXI read address channel
  always_comb o_apu_init_mt_axi_m_araddr = if_apu_init_mt_axi_m_ar.addr;
  always_comb o_apu_init_mt_axi_m_arid = if_apu_init_mt_axi_m_ar.id;
  always_comb o_apu_init_mt_axi_m_arlen = if_apu_init_mt_axi_m_ar.len;
  always_comb o_apu_init_mt_axi_m_arsize = if_apu_init_mt_axi_m_ar.size;
  always_comb o_apu_init_mt_axi_m_arburst = if_apu_init_mt_axi_m_ar.burst;
  always_comb o_apu_init_mt_axi_m_arcache = if_apu_init_mt_axi_m_ar.cache;
  always_comb o_apu_init_mt_axi_m_arprot = if_apu_init_mt_axi_m_ar.prot;
  always_comb o_apu_init_mt_axi_m_arqos = if_apu_init_mt_axi_m_ar.qos;
  always_comb o_apu_init_mt_axi_m_arregion = if_apu_init_mt_axi_m_ar.region;
  always_comb o_apu_init_mt_axi_m_aruser = if_apu_init_mt_axi_m_ar.user;
  always_comb o_apu_init_mt_axi_m_arlock = if_apu_init_mt_axi_m_ar.lock;
  // AXI read data/response channel
  always_comb if_apu_init_mt_axi_m_r.last = i_apu_init_mt_axi_m_rlast;
  always_comb if_apu_init_mt_axi_m_r.id = i_apu_init_mt_axi_m_rid;
  always_comb if_apu_init_mt_axi_m_r.data = i_apu_init_mt_axi_m_rdata;
  always_comb if_apu_init_mt_axi_m_r.resp = axi_pkg::axi_resp_e'(i_apu_init_mt_axi_m_rresp);
  always_comb if_apu_init_mt_axi_m_r.user = i_apu_init_mt_axi_m_ruser;

  apu_axi_mt_m_aw_t apu_init_mt_axi_m_aw;
  logic apu_init_mt_axi_m_awready;
  logic apu_init_mt_axi_m_awvalid;
  apu_axi_mt_w_t apu_init_mt_axi_m_w;
  logic apu_init_mt_axi_m_wready;
  logic apu_init_mt_axi_m_wvalid;
  apu_axi_mt_m_b_t apu_init_mt_axi_m_b;
  logic apu_init_mt_axi_m_bready;
  logic apu_init_mt_axi_m_bvalid;
  apu_axi_mt_m_ar_t apu_init_mt_axi_m_ar;
  logic apu_init_mt_axi_m_arready;
  logic apu_init_mt_axi_m_arvalid;
  apu_axi_mt_m_r_t apu_init_mt_axi_m_r;
  logic apu_init_mt_axi_m_rready;
  logic apu_init_mt_axi_m_rvalid;

  axe_axi_multicut #(
    .NumCuts(2), // Number of cuts.
    // AXI structs
    .axi_aw_t(apu_axi_mt_m_aw_t),
    .axi_w_t (apu_axi_mt_w_t),
    .axi_b_t (apu_axi_mt_m_b_t),
    .axi_ar_t(apu_axi_mt_m_ar_t),
    .axi_r_t (apu_axi_mt_m_r_t)
  ) u_axi_cut_mt_init (
    .i_clk(aclk),
    .i_rst_n(arst_n),

    .i_axi_s_aw      (apu_init_mt_axi_m_aw),
    .o_axi_s_aw_ready(apu_init_mt_axi_m_awready),
    .i_axi_s_aw_valid(apu_init_mt_axi_m_awvalid),
    .i_axi_s_w       (apu_init_mt_axi_m_w),
    .o_axi_s_w_ready (apu_init_mt_axi_m_wready),
    .i_axi_s_w_valid (apu_init_mt_axi_m_wvalid),
    .o_axi_s_b       (apu_init_mt_axi_m_b),
    .i_axi_s_b_ready (apu_init_mt_axi_m_bready),
    .o_axi_s_b_valid (apu_init_mt_axi_m_bvalid),
    .i_axi_s_ar      (apu_init_mt_axi_m_ar),
    .o_axi_s_ar_ready(apu_init_mt_axi_m_arready),
    .i_axi_s_ar_valid(apu_init_mt_axi_m_arvalid),
    .o_axi_s_r       (apu_init_mt_axi_m_r),
    .i_axi_s_r_ready (apu_init_mt_axi_m_rready),
    .o_axi_s_r_valid (apu_init_mt_axi_m_rvalid),

    .o_axi_m_aw      (if_apu_init_mt_axi_m_aw),
    .i_axi_m_aw_ready(i_apu_init_mt_axi_m_awready),
    .o_axi_m_aw_valid(o_apu_init_mt_axi_m_awvalid),
    .o_axi_m_w       (if_apu_init_mt_axi_m_w),
    .i_axi_m_w_ready (i_apu_init_mt_axi_m_wready),
    .o_axi_m_w_valid (o_apu_init_mt_axi_m_wvalid),
    .i_axi_m_b       (if_apu_init_mt_axi_m_b),
    .o_axi_m_b_ready (o_apu_init_mt_axi_m_bready),
    .i_axi_m_b_valid (i_apu_init_mt_axi_m_bvalid),
    .o_axi_m_ar      (if_apu_init_mt_axi_m_ar),
    .i_axi_m_ar_ready(i_apu_init_mt_axi_m_arready),
    .o_axi_m_ar_valid(o_apu_init_mt_axi_m_arvalid),
    .i_axi_m_r       (if_apu_init_mt_axi_m_r),
    .o_axi_m_r_ready (o_apu_init_mt_axi_m_rready),
    .i_axi_m_r_valid (i_apu_init_mt_axi_m_rvalid)
  );

  // OCPL SPILL for tok_prod_ocpl_m
  chip_pkg::chip_ocpl_token_addr_t tok_prod_ocpl_subip_maddr;
  chip_pkg::chip_ocpl_token_data_t tok_prod_ocpl_subip_mdata;
  logic tok_prod_ocpl_subip_mcmd;
  logic tok_prod_ocpl_subip_scmdaccept;

  ocp_lite_multicut #(
    .NumCuts(2),
    .addr_t(chip_pkg::chip_ocpl_token_addr_t),
    .data_t(chip_pkg::chip_ocpl_token_data_t)
  ) u_tok_prod_ocpl_m_cut (
    .i_clk(aclk),
    .i_rst_n(arst_n),
    .i_s_mcmd(tok_prod_ocpl_subip_mcmd),
    .i_s_maddr(tok_prod_ocpl_subip_maddr),
    .i_s_mdata(tok_prod_ocpl_subip_mdata),
    .o_s_scmd_accept(tok_prod_ocpl_subip_scmdaccept),
    .o_m_mcmd(o_tok_prod_ocpl_m_mcmd),
    .o_m_maddr(o_tok_prod_ocpl_m_maddr),
    .o_m_mdata(o_tok_prod_ocpl_m_mdata),
    .i_m_scmd_accept(i_tok_prod_ocpl_m_scmdaccept)
  );

  // OCPL SPILL for tok_cons_ocpl_s
  chip_pkg::chip_ocpl_token_addr_t tok_cons_ocpl_subip_maddr;
  chip_pkg::chip_ocpl_token_data_t tok_cons_ocpl_subip_mdata;
  logic tok_cons_ocpl_subip_mcmd;
  logic tok_cons_ocpl_subip_scmdaccept;

  ocp_lite_multicut #(
    .NumCuts(2),
    .addr_t(chip_pkg::chip_ocpl_token_addr_t),
    .data_t(chip_pkg::chip_ocpl_token_data_t)
  ) u_tok_cons_ocpl_s_cut (
    .i_clk(aclk),
    .i_rst_n(arst_n),
    .i_s_mcmd(i_tok_cons_ocpl_s_mcmd),
    .i_s_maddr(i_tok_cons_ocpl_s_maddr),
    .i_s_mdata(i_tok_cons_ocpl_s_mdata),
    .o_s_scmd_accept(o_tok_cons_ocpl_s_scmdaccept),
    .o_m_mcmd(tok_cons_ocpl_subip_mcmd),
    .o_m_maddr(tok_cons_ocpl_subip_maddr),
    .o_m_mdata(tok_cons_ocpl_subip_mdata),
    .i_m_scmd_accept(tok_cons_ocpl_subip_scmdaccept)
  );

  // Derive mtime_clk from div2 chain of ref_clk
  localparam int unsigned MTIME_CLK_NUM_DIV2 = 2;
  wire mtime_clk_div [MTIME_CLK_NUM_DIV2+1];

  assign mtime_clk_div[0] = i_ref_clk;

  for (genvar i = 0; unsigned'(i) < MTIME_CLK_NUM_DIV2; i++) begin: g_mtime_clk_div2
    axe_ccl_clk_div_by_2 u_mtime_clk_div2 (
      .i_clk(mtime_clk_div[i]),
      .i_rst_n(arst_n), // Timer reset with bus_clk
      .i_test_mode('0),
      .i_enable('1),
      .o_clk(mtime_clk_div[i+1])
    );
  end

  apu u_apu (
    .i_mtime_clk(mtime_clk_div[MTIME_CLK_NUM_DIV2]),
    .i_por_rst_n(ao_rst_sync_n),
    .i_cores_clk(cores_clk),
    .i_cores_rst_n(cores_rst_n),
    .i_aclk(aclk),
    .i_free_run_aclk(aclk_free),
    .i_arst_n(arst_n),
    .i_l2c_clk(l2c_clk),
    .i_l2c_rst_n(l2c_rst_n),
    .i_test_mode(test_mode),

    /// External IRQs to APU
    .i_external_irqs(external_irqs),

    /// NoC AXI Connections LP Manager Port (MMIO)
    // AXI write address channel
    .o_apu_init_lt_axi_m_aw(apu_init_lt_axi_m_aw),
    .i_apu_init_lt_axi_m_awready(apu_init_lt_axi_m_awready),
    .o_apu_init_lt_axi_m_awvalid(apu_init_lt_axi_m_awvalid),
    // AXI write data channel
    .o_apu_init_lt_axi_m_w(apu_init_lt_axi_m_w),
    .i_apu_init_lt_axi_m_wready(apu_init_lt_axi_m_wready),
    .o_apu_init_lt_axi_m_wvalid(apu_init_lt_axi_m_wvalid),
    // AXI write response channel
    .i_apu_init_lt_axi_m_b(apu_init_lt_axi_m_b),
    .o_apu_init_lt_axi_m_bready(apu_init_lt_axi_m_bready),
    .i_apu_init_lt_axi_m_bvalid(apu_init_lt_axi_m_bvalid),
    // AXI read address channel
    .o_apu_init_lt_axi_m_ar(apu_init_lt_axi_m_ar),
    .i_apu_init_lt_axi_m_arready(apu_init_lt_axi_m_arready),
    .o_apu_init_lt_axi_m_arvalid(apu_init_lt_axi_m_arvalid),
    // AXI read data/response channel
    .i_apu_init_lt_axi_m_r(apu_init_lt_axi_m_r),
    .o_apu_init_lt_axi_m_rready(apu_init_lt_axi_m_rready),
    .i_apu_init_lt_axi_m_rvalid(apu_init_lt_axi_m_rvalid),

    /// NoC AXI Connections LP Subordinate Port (IOCP)
    // AXI write address channel
    .i_apu_targ_lt_axi_s_aw(apu_targ_lt_axi_s_aw),
    .o_apu_targ_lt_axi_s_awready(apu_targ_lt_axi_s_awready),
    .i_apu_targ_lt_axi_s_awvalid(apu_targ_lt_axi_s_awvalid),
    // AXI write data channel
    .i_apu_targ_lt_axi_s_w(apu_targ_lt_axi_s_w),
    .o_apu_targ_lt_axi_s_wready(apu_targ_lt_axi_s_wready),
    .i_apu_targ_lt_axi_s_wvalid(apu_targ_lt_axi_s_wvalid),
    // AXI write response channel
    .o_apu_targ_lt_axi_s_b(apu_targ_lt_axi_s_b),
    .i_apu_targ_lt_axi_s_bready(apu_targ_lt_axi_s_bready),
    .o_apu_targ_lt_axi_s_bvalid(apu_targ_lt_axi_s_bvalid),
    // AXI read address channel
    .i_apu_targ_lt_axi_s_ar(apu_targ_lt_axi_s_ar),
    .o_apu_targ_lt_axi_s_arready(apu_targ_lt_axi_s_arready),
    .i_apu_targ_lt_axi_s_arvalid(apu_targ_lt_axi_s_arvalid),
    // AXI read data/response channel
    .o_apu_targ_lt_axi_s_r(apu_targ_lt_axi_s_r),
    .i_apu_targ_lt_axi_s_rready(apu_targ_lt_axi_s_rready),
    .o_apu_targ_lt_axi_s_rvalid(apu_targ_lt_axi_s_rvalid),

    /// NoC Connections HP AXI Manager Interface (DMA/MEM)
    // AXI write address channel
    .o_apu_init_mt_axi_m_aw(apu_init_mt_axi_m_aw),
    .i_apu_init_mt_axi_m_awready(apu_init_mt_axi_m_awready),
    .o_apu_init_mt_axi_m_awvalid(apu_init_mt_axi_m_awvalid),
    // AXI write data channel
    .o_apu_init_mt_axi_m_w(apu_init_mt_axi_m_w),
    .i_apu_init_mt_axi_m_wready(apu_init_mt_axi_m_wready),
    .o_apu_init_mt_axi_m_wvalid(apu_init_mt_axi_m_wvalid),
    // AXI write response channel
    .i_apu_init_mt_axi_m_b(apu_init_mt_axi_m_b),
    .o_apu_init_mt_axi_m_bready(apu_init_mt_axi_m_bready),
    .i_apu_init_mt_axi_m_bvalid(apu_init_mt_axi_m_bvalid),
    // AXI read address channel
    .o_apu_init_mt_axi_m_ar(apu_init_mt_axi_m_ar),
    .i_apu_init_mt_axi_m_arready(apu_init_mt_axi_m_arready),
    .o_apu_init_mt_axi_m_arvalid(apu_init_mt_axi_m_arvalid),
    // AXI read data/response channel
    .i_apu_init_mt_axi_m_r(apu_init_mt_axi_m_r),
    .o_apu_init_mt_axi_m_rready(apu_init_mt_axi_m_rready),
    .i_apu_init_mt_axi_m_rvalid(apu_init_mt_axi_m_rvalid),

    // Token network
    .o_tok_prod_ocpl_m_maddr(tok_prod_ocpl_subip_maddr),
    .o_tok_prod_ocpl_m_mdata(tok_prod_ocpl_subip_mdata),
    .o_tok_prod_ocpl_m_mcmd(tok_prod_ocpl_subip_mcmd),
    .i_tok_prod_ocpl_m_scmdaccept(tok_prod_ocpl_subip_scmdaccept),
    .i_tok_cons_ocpl_s_maddr(tok_cons_ocpl_subip_maddr),
    .i_tok_cons_ocpl_s_mdata(tok_cons_ocpl_subip_mdata),
    .i_tok_cons_ocpl_s_mcmd(tok_cons_ocpl_subip_mcmd),
    .o_tok_cons_ocpl_s_scmdaccept(tok_cons_ocpl_subip_scmdaccept),

    .i_fabric_low_power_en(reg2hw.fabric_low_power_control.enable),
    .i_fabric_low_power_idle_delay(reg2hw.fabric_low_power_control.idle_delay),

    .*
  );

  pvt_probe_wrapper  u_pvt_probe (
    .io_ibias_ts,
    .io_vsense_ts
  );

  // SVS Monitor
  svs_monitor_pkg::svs_count_t svs_count;
  logic                        svs_valid;
  // Process1 monitor
  process1_monitor_pkg::pr1_count_t p1_count;
  logic                             p1_valid;
  // Process2 monitor
  process2_monitor_pkg::pr2_count_t p2_count;
  logic                             p2_valid;

  // Process1 monitor
  always_comb foreach(hw2reg.p1_counters[counter])
    hw2reg.p1_counters[counter] = '{
      de: p1_valid,
      d:  p1_count[counter]
  };

  process1_monitor_wrapper u_p1_monitor (
    .tcki     (tck),
    .trsti    (trst),
    .i_clk    (ref_clk_buf),
    .i_enable (reg2hw.p1_control.enable),
    .i_ref_clk(ref_clk_buf),
    .i_target (reg2hw.p1_control.target),
    .i_use_ro (reg2hw.p1_ro_select),
    .o_valid  (p1_valid),
    .o_count  (p1_count)
  );

  // Process2 monitor
  always_comb foreach(hw2reg.p2_counters[counter])
    hw2reg.p2_counters[counter] = '{
      de: p2_valid,
      d:  p2_count[counter]
  };

  process2_monitor_wrapper u_p2_monitor (
    .tcki     (tck),
    .trsti    (trst),
    .i_clk    (ref_clk_buf),
    .i_enable (reg2hw.p2_control.enable),
    .i_ref_clk(ref_clk_buf),
    .i_target (reg2hw.p2_control.target),
    .i_use_ro (reg2hw.p2_ro_select),
    .o_valid  (p2_valid),
    .o_count  (p2_count)
  );

  // SVS Monitor
  always_comb foreach(hw2reg.svs_counters[counter])
    hw2reg.svs_counters[counter] = '{
      de: svs_valid,
      d:  svs_count[counter]
  };

  svs_monitor_wrapper u_svs_monitor (
    .tcki     (tck),
    .trsti    (trst),
    .i_clk    (ref_clk_buf),
    .i_enable (reg2hw.svs_control.enable),
    .i_ref_clk(ref_clk_buf),
    .i_target (reg2hw.svs_control.target),
    .i_use_ro (reg2hw.svs_ro_select),
    .o_valid  (svs_valid),
    .o_count  (svs_count)
  );

endmodule
