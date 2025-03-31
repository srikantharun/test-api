
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//


module dcd_p_stub
  import chip_pkg::*;
  import axi_pkg::*;
  import dcd_pkg::*;

#(
)(
  //-------------------------------
  // interface signals
  //-------------------------------

  //-------------------------------
  // wrapper io
  //-------------------------------
  input  wire   i_clk,
  input  wire   i_mcu_clk,
  input  wire   i_jtag_clk,
  input  wire   i_jtag_rst_n,
  input  logic  i_jtag_ms,
  input  logic  i_jtag_di,
  output logic  o_jtag_do,
  input  dcd_targ_cfg_apb_addr_t  i_cfg_apb4_s_paddr,
  input  dcd_targ_cfg_apb_data_t  i_cfg_apb4_s_pwdata,
  input  logic  i_cfg_apb4_s_pwrite,
  input  logic  i_cfg_apb4_s_psel,
  input  logic  i_cfg_apb4_s_penable,
  input  dcd_targ_cfg_apb_strb_t  i_cfg_apb4_s_pstrb,
  input  axi_prot_t  i_cfg_apb4_s_pprot,
  output logic  o_cfg_apb4_s_pready,
  output dcd_targ_cfg_apb_data_t  o_cfg_apb4_s_prdata,
  output logic  o_cfg_apb4_s_pslverr,
  output logic  o_pintreq,

  //-------------------------------
  // protocol ports
  //-------------------------------

  //-------------------------------
  // AXI4 o_dec_0_axi_m
  //-------------------------------
  output       chip_axi_addr_t o_dec_0_axi_m_awaddr  ,
  output       dcd_dec_0_init_mt_axi_id_t o_dec_0_axi_m_awid    ,
  output       axi_len_t o_dec_0_axi_m_awlen   ,
  output       axi_size_t o_dec_0_axi_m_awsize  ,
  output       axi_burst_t o_dec_0_axi_m_awburst ,
  output       axi_cache_t o_dec_0_axi_m_awcache ,
  output       axi_prot_t o_dec_0_axi_m_awprot  ,
  output logic o_dec_0_axi_m_awlock  ,
  output       axi_qos_t o_dec_0_axi_m_awqos   ,
  output       axi_region_t o_dec_0_axi_m_awregion,
  output       chip_axi_mt_awuser_t o_dec_0_axi_m_awuser  ,
  output logic o_dec_0_axi_m_awvalid ,
  output       dcd_dec_0_init_mt_axi_data_t o_dec_0_axi_m_wdata   ,
  output       dcd_dec_0_init_mt_axi_strb_t o_dec_0_axi_m_wstrb   ,
  output logic o_dec_0_axi_m_wlast   ,
  output       chip_axi_mt_wuser_t o_dec_0_axi_m_wuser   ,
  output logic o_dec_0_axi_m_wvalid  ,
  output logic o_dec_0_axi_m_bready  ,
  output       chip_axi_addr_t o_dec_0_axi_m_araddr  ,
  output       dcd_dec_0_init_mt_axi_id_t o_dec_0_axi_m_arid    ,
  output       axi_len_t o_dec_0_axi_m_arlen   ,
  output       axi_size_t o_dec_0_axi_m_arsize  ,
  output       axi_burst_t o_dec_0_axi_m_arburst ,
  output       axi_cache_t o_dec_0_axi_m_arcache ,
  output       axi_prot_t o_dec_0_axi_m_arprot  ,
  output       axi_qos_t o_dec_0_axi_m_arqos   ,
  output       axi_region_t o_dec_0_axi_m_arregion,
  output       chip_axi_mt_aruser_t o_dec_0_axi_m_aruser  ,
  output logic o_dec_0_axi_m_arlock  ,
  output logic o_dec_0_axi_m_arvalid ,
  output logic o_dec_0_axi_m_rready  ,

  //-------------------------------
  // AXI4 i_dec_0_axi_m
  //-------------------------------
  input  logic i_dec_0_axi_m_awready,
  input  logic i_dec_0_axi_m_wready ,
  input  logic i_dec_0_axi_m_bvalid ,
  input        dcd_dec_0_init_mt_axi_id_t i_dec_0_axi_m_bid    ,
  input        chip_axi_mt_buser_t i_dec_0_axi_m_buser  ,
  input        axi_resp_t i_dec_0_axi_m_bresp  ,
  input  logic i_dec_0_axi_m_arready,
  input  logic i_dec_0_axi_m_rvalid ,
  input  logic i_dec_0_axi_m_rlast  ,
  input        dcd_dec_0_init_mt_axi_id_t i_dec_0_axi_m_rid    ,
  input        dcd_dec_0_init_mt_axi_data_t i_dec_0_axi_m_rdata  ,
  input        chip_axi_mt_ruser_t i_dec_0_axi_m_ruser  ,
  input        axi_resp_t i_dec_0_axi_m_rresp  ,

  //-------------------------------
  // AXI4 o_dec_1_axi_m
  //-------------------------------
  output       chip_axi_addr_t o_dec_1_axi_m_awaddr  ,
  output       dcd_dec_1_init_mt_axi_id_t o_dec_1_axi_m_awid    ,
  output       axi_len_t o_dec_1_axi_m_awlen   ,
  output       axi_size_t o_dec_1_axi_m_awsize  ,
  output       axi_burst_t o_dec_1_axi_m_awburst ,
  output       axi_cache_t o_dec_1_axi_m_awcache ,
  output       axi_prot_t o_dec_1_axi_m_awprot  ,
  output logic o_dec_1_axi_m_awlock  ,
  output       axi_qos_t o_dec_1_axi_m_awqos   ,
  output       axi_region_t o_dec_1_axi_m_awregion,
  output       chip_axi_mt_awuser_t o_dec_1_axi_m_awuser  ,
  output logic o_dec_1_axi_m_awvalid ,
  output       dcd_dec_1_init_mt_axi_data_t o_dec_1_axi_m_wdata   ,
  output       dcd_dec_1_init_mt_axi_strb_t o_dec_1_axi_m_wstrb   ,
  output logic o_dec_1_axi_m_wlast   ,
  output       chip_axi_mt_wuser_t o_dec_1_axi_m_wuser   ,
  output logic o_dec_1_axi_m_wvalid  ,
  output logic o_dec_1_axi_m_bready  ,
  output       chip_axi_addr_t o_dec_1_axi_m_araddr  ,
  output       dcd_dec_1_init_mt_axi_id_t o_dec_1_axi_m_arid    ,
  output       axi_len_t o_dec_1_axi_m_arlen   ,
  output       axi_size_t o_dec_1_axi_m_arsize  ,
  output       axi_burst_t o_dec_1_axi_m_arburst ,
  output       axi_cache_t o_dec_1_axi_m_arcache ,
  output       axi_prot_t o_dec_1_axi_m_arprot  ,
  output       axi_qos_t o_dec_1_axi_m_arqos   ,
  output       axi_region_t o_dec_1_axi_m_arregion,
  output       chip_axi_mt_aruser_t o_dec_1_axi_m_aruser  ,
  output logic o_dec_1_axi_m_arlock  ,
  output logic o_dec_1_axi_m_arvalid ,
  output logic o_dec_1_axi_m_rready  ,

  //-------------------------------
  // AXI4 i_dec_1_axi_m
  //-------------------------------
  input  logic i_dec_1_axi_m_awready,
  input  logic i_dec_1_axi_m_wready ,
  input  logic i_dec_1_axi_m_bvalid ,
  input        dcd_dec_1_init_mt_axi_id_t i_dec_1_axi_m_bid    ,
  input        chip_axi_mt_buser_t i_dec_1_axi_m_buser  ,
  input        axi_resp_t i_dec_1_axi_m_bresp  ,
  input  logic i_dec_1_axi_m_arready,
  input  logic i_dec_1_axi_m_rvalid ,
  input  logic i_dec_1_axi_m_rlast  ,
  input        dcd_dec_1_init_mt_axi_id_t i_dec_1_axi_m_rid    ,
  input        dcd_dec_1_init_mt_axi_data_t i_dec_1_axi_m_rdata  ,
  input        chip_axi_mt_ruser_t i_dec_1_axi_m_ruser  ,
  input        axi_resp_t i_dec_1_axi_m_rresp  ,

  //-------------------------------
  // AXI4 o_dec_2_axi_m
  //-------------------------------
  output       chip_axi_addr_t o_dec_2_axi_m_awaddr  ,
  output       dcd_dec_2_init_mt_axi_id_t o_dec_2_axi_m_awid    ,
  output       axi_len_t o_dec_2_axi_m_awlen   ,
  output       axi_size_t o_dec_2_axi_m_awsize  ,
  output       axi_burst_t o_dec_2_axi_m_awburst ,
  output       axi_cache_t o_dec_2_axi_m_awcache ,
  output       axi_prot_t o_dec_2_axi_m_awprot  ,
  output logic o_dec_2_axi_m_awlock  ,
  output       axi_qos_t o_dec_2_axi_m_awqos   ,
  output       axi_region_t o_dec_2_axi_m_awregion,
  output       chip_axi_mt_awuser_t o_dec_2_axi_m_awuser  ,
  output logic o_dec_2_axi_m_awvalid ,
  output       dcd_dec_2_init_mt_axi_data_t o_dec_2_axi_m_wdata   ,
  output       dcd_dec_2_init_mt_axi_strb_t o_dec_2_axi_m_wstrb   ,
  output logic o_dec_2_axi_m_wlast   ,
  output       chip_axi_mt_wuser_t o_dec_2_axi_m_wuser   ,
  output logic o_dec_2_axi_m_wvalid  ,
  output logic o_dec_2_axi_m_bready  ,
  output       chip_axi_addr_t o_dec_2_axi_m_araddr  ,
  output       dcd_dec_2_init_mt_axi_id_t o_dec_2_axi_m_arid    ,
  output       axi_len_t o_dec_2_axi_m_arlen   ,
  output       axi_size_t o_dec_2_axi_m_arsize  ,
  output       axi_burst_t o_dec_2_axi_m_arburst ,
  output       axi_cache_t o_dec_2_axi_m_arcache ,
  output       axi_prot_t o_dec_2_axi_m_arprot  ,
  output       axi_qos_t o_dec_2_axi_m_arqos   ,
  output       axi_region_t o_dec_2_axi_m_arregion,
  output       chip_axi_mt_aruser_t o_dec_2_axi_m_aruser  ,
  output logic o_dec_2_axi_m_arlock  ,
  output logic o_dec_2_axi_m_arvalid ,
  output logic o_dec_2_axi_m_rready  ,

  //-------------------------------
  // AXI4 i_dec_2_axi_m
  //-------------------------------
  input  logic i_dec_2_axi_m_awready,
  input  logic i_dec_2_axi_m_wready ,
  input  logic i_dec_2_axi_m_bvalid ,
  input        dcd_dec_2_init_mt_axi_id_t i_dec_2_axi_m_bid    ,
  input        chip_axi_mt_buser_t i_dec_2_axi_m_buser  ,
  input        axi_resp_t i_dec_2_axi_m_bresp  ,
  input  logic i_dec_2_axi_m_arready,
  input  logic i_dec_2_axi_m_rvalid ,
  input  logic i_dec_2_axi_m_rlast  ,
  input        dcd_dec_2_init_mt_axi_id_t i_dec_2_axi_m_rid    ,
  input        dcd_dec_2_init_mt_axi_data_t i_dec_2_axi_m_rdata  ,
  input        chip_axi_mt_ruser_t i_dec_2_axi_m_ruser  ,
  input        axi_resp_t i_dec_2_axi_m_rresp  ,

  //-------------------------------
  // AXI4 o_mcu_axi_m
  //-------------------------------
  output       chip_axi_addr_t o_mcu_axi_m_awaddr  ,
  output       dcd_mcu_init_lt_axi_id_t o_mcu_axi_m_awid    ,
  output       axi_len_t o_mcu_axi_m_awlen   ,
  output       axi_size_t o_mcu_axi_m_awsize  ,
  output       axi_burst_t o_mcu_axi_m_awburst ,
  output       axi_cache_t o_mcu_axi_m_awcache ,
  output       axi_prot_t o_mcu_axi_m_awprot  ,
  output logic o_mcu_axi_m_awlock  ,
  output       axi_qos_t o_mcu_axi_m_awqos   ,
  output       axi_region_t o_mcu_axi_m_awregion,
  output       chip_axi_mt_awuser_t o_mcu_axi_m_awuser  ,
  output logic o_mcu_axi_m_awvalid ,
  output       dcd_mcu_init_lt_axi_data_t o_mcu_axi_m_wdata   ,
  output       dcd_mcu_init_lt_axi_strb_t o_mcu_axi_m_wstrb   ,
  output logic o_mcu_axi_m_wlast   ,
  output       chip_axi_mt_wuser_t o_mcu_axi_m_wuser   ,
  output logic o_mcu_axi_m_wvalid  ,
  output logic o_mcu_axi_m_bready  ,
  output       chip_axi_addr_t o_mcu_axi_m_araddr  ,
  output       dcd_mcu_init_lt_axi_id_t o_mcu_axi_m_arid    ,
  output       axi_len_t o_mcu_axi_m_arlen   ,
  output       axi_size_t o_mcu_axi_m_arsize  ,
  output       axi_burst_t o_mcu_axi_m_arburst ,
  output       axi_cache_t o_mcu_axi_m_arcache ,
  output       axi_prot_t o_mcu_axi_m_arprot  ,
  output       axi_qos_t o_mcu_axi_m_arqos   ,
  output       axi_region_t o_mcu_axi_m_arregion,
  output       chip_axi_mt_aruser_t o_mcu_axi_m_aruser  ,
  output logic o_mcu_axi_m_arlock  ,
  output logic o_mcu_axi_m_arvalid ,
  output logic o_mcu_axi_m_rready  ,

  //-------------------------------
  // AXI4 i_mcu_axi_m
  //-------------------------------
  input  logic i_mcu_axi_m_awready,
  input  logic i_mcu_axi_m_wready ,
  input  logic i_mcu_axi_m_bvalid ,
  input        dcd_mcu_init_lt_axi_id_t i_mcu_axi_m_bid    ,
  input        chip_axi_mt_buser_t i_mcu_axi_m_buser  ,
  input        axi_resp_t i_mcu_axi_m_bresp  ,
  input  logic i_mcu_axi_m_arready,
  input  logic i_mcu_axi_m_rvalid ,
  input  logic i_mcu_axi_m_rlast  ,
  input        dcd_mcu_init_lt_axi_id_t i_mcu_axi_m_rid    ,
  input        dcd_mcu_init_lt_axi_data_t i_mcu_axi_m_rdata  ,
  input        chip_axi_mt_ruser_t i_mcu_axi_m_ruser  ,
  input        axi_resp_t i_mcu_axi_m_rresp  ,

  //-------------------------------
  // Partition Controller Interface
  //-------------------------------
  input  wire                         i_ref_clk           ,
  input  wire                         i_ao_rst_n          ,
  input  wire                         i_global_rst_n      ,
  output wire                         o_ao_rst_sync_n     ,
  output logic                        o_noc_async_idle_req,
  input  logic                        i_noc_async_idle_ack,
  input  logic                        i_noc_async_idle_val,
  output logic                        o_noc_mcu_async_idle_req,
  input  logic                        i_noc_mcu_async_idle_ack,
  input  logic                        i_noc_mcu_async_idle_val,
  output logic                        o_noc_clk_en        ,
  output logic                        o_noc_mcu_clk_en    ,
  input  chip_syscfg_addr_t           i_syscfg_apb4_s_paddr  ,
  input  chip_apb_syscfg_data_t       i_syscfg_apb4_s_pwdata ,
  input  logic                        i_syscfg_apb4_s_pwrite ,
  input  logic                        i_syscfg_apb4_s_psel   ,
  input  logic                        i_syscfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t       i_syscfg_apb4_s_pstrb  ,
  input  logic                  [3-1:0] i_syscfg_apb4_s_pprot  ,
  output logic                        o_syscfg_apb4_s_pready ,
  output chip_apb_syscfg_data_t       o_syscfg_apb4_s_prdata ,
  output logic                        o_syscfg_apb4_s_pslverr,
  output wire                         o_noc_rst_n         ,
  output wire                         o_noc_mcu_rst_n     ,

  // Observability signals for DCD
  output logic [15:0] o_dcd_obs,
  //-------------------------------
  // DFT Interface
  //-------------------------------
  input  wire   tck,
  input  wire   trst,
  input  logic  tms,
  input  logic  tdi,
  output logic  tdo_en,
  output logic  tdo,

  input  logic  test_mode,

  input  wire   ssn_bus_clk,
  input  logic [25-1: 0] ssn_bus_data_in,
  output logic [25-1: 0] ssn_bus_data_out,
  input  wire   bisr_clk,
  input  wire   bisr_reset,
  input  logic  bisr_shift_en,
  input  logic  bisr_si,
  output logic  bisr_so
);

  assign o_jtag_do = 1'b0;
  assign o_cfg_apb4_s_pready = 1'b1;
  assign o_cfg_apb4_s_prdata = '0;
  assign o_cfg_apb4_s_pslverr = 1'b0;
  assign o_pintreq = 1'b0;
  assign o_dec_0_axi_m_awaddr = '0;
  assign o_dec_0_axi_m_awid = '0;
  assign o_dec_0_axi_m_awlen = '0;
  assign o_dec_0_axi_m_awsize = '0;
  assign o_dec_0_axi_m_awburst = '0;
  assign o_dec_0_axi_m_awcache = '0;
  assign o_dec_0_axi_m_awprot = '0;
  assign o_dec_0_axi_m_awlock = 1'b0;
  assign o_dec_0_axi_m_awqos = '0;
  assign o_dec_0_axi_m_awregion = '0;
  assign o_dec_0_axi_m_awuser = '0;
  assign o_dec_0_axi_m_awvalid = 1'b0;
  assign o_dec_0_axi_m_wdata = '0;
  assign o_dec_0_axi_m_wstrb = '0;
  assign o_dec_0_axi_m_wlast = 1'b0;
  assign o_dec_0_axi_m_wuser = '0;
  assign o_dec_0_axi_m_wvalid = 1'b0;
  assign o_dec_0_axi_m_bready = 1'b1;
  assign o_dec_0_axi_m_araddr = '0;
  assign o_dec_0_axi_m_arid = '0;
  assign o_dec_0_axi_m_arlen = '0;
  assign o_dec_0_axi_m_arsize = '0;
  assign o_dec_0_axi_m_arburst = '0;
  assign o_dec_0_axi_m_arcache = '0;
  assign o_dec_0_axi_m_arprot = '0;
  assign o_dec_0_axi_m_arqos = '0;
  assign o_dec_0_axi_m_arregion = '0;
  assign o_dec_0_axi_m_aruser = '0;
  assign o_dec_0_axi_m_arlock = 1'b0;
  assign o_dec_0_axi_m_arvalid = 1'b0;
  assign o_dec_0_axi_m_rready = 1'b1;
  assign o_dec_1_axi_m_awaddr = '0;
  assign o_dec_1_axi_m_awid = '0;
  assign o_dec_1_axi_m_awlen = '0;
  assign o_dec_1_axi_m_awsize = '0;
  assign o_dec_1_axi_m_awburst = '0;
  assign o_dec_1_axi_m_awcache = '0;
  assign o_dec_1_axi_m_awprot = '0;
  assign o_dec_1_axi_m_awlock = 1'b0;
  assign o_dec_1_axi_m_awqos = '0;
  assign o_dec_1_axi_m_awregion = '0;
  assign o_dec_1_axi_m_awuser = '0;
  assign o_dec_1_axi_m_awvalid = 1'b0;
  assign o_dec_1_axi_m_wdata = '0;
  assign o_dec_1_axi_m_wstrb = '0;
  assign o_dec_1_axi_m_wlast = 1'b0;
  assign o_dec_1_axi_m_wuser = '0;
  assign o_dec_1_axi_m_wvalid = 1'b0;
  assign o_dec_1_axi_m_bready = 1'b1;
  assign o_dec_1_axi_m_araddr = '0;
  assign o_dec_1_axi_m_arid = '0;
  assign o_dec_1_axi_m_arlen = '0;
  assign o_dec_1_axi_m_arsize = '0;
  assign o_dec_1_axi_m_arburst = '0;
  assign o_dec_1_axi_m_arcache = '0;
  assign o_dec_1_axi_m_arprot = '0;
  assign o_dec_1_axi_m_arqos = '0;
  assign o_dec_1_axi_m_arregion = '0;
  assign o_dec_1_axi_m_aruser = '0;
  assign o_dec_1_axi_m_arlock = 1'b0;
  assign o_dec_1_axi_m_arvalid = 1'b0;
  assign o_dec_1_axi_m_rready = 1'b1;
  assign o_dec_2_axi_m_awaddr = '0;
  assign o_dec_2_axi_m_awid = '0;
  assign o_dec_2_axi_m_awlen = '0;
  assign o_dec_2_axi_m_awsize = '0;
  assign o_dec_2_axi_m_awburst = '0;
  assign o_dec_2_axi_m_awcache = '0;
  assign o_dec_2_axi_m_awprot = '0;
  assign o_dec_2_axi_m_awlock = 1'b0;
  assign o_dec_2_axi_m_awqos = '0;
  assign o_dec_2_axi_m_awregion = '0;
  assign o_dec_2_axi_m_awuser = '0;
  assign o_dec_2_axi_m_awvalid = 1'b0;
  assign o_dec_2_axi_m_wdata = '0;
  assign o_dec_2_axi_m_wstrb = '0;
  assign o_dec_2_axi_m_wlast = 1'b0;
  assign o_dec_2_axi_m_wuser = '0;
  assign o_dec_2_axi_m_wvalid = 1'b0;
  assign o_dec_2_axi_m_bready = 1'b1;
  assign o_dec_2_axi_m_araddr = '0;
  assign o_dec_2_axi_m_arid = '0;
  assign o_dec_2_axi_m_arlen = '0;
  assign o_dec_2_axi_m_arsize = '0;
  assign o_dec_2_axi_m_arburst = '0;
  assign o_dec_2_axi_m_arcache = '0;
  assign o_dec_2_axi_m_arprot = '0;
  assign o_dec_2_axi_m_arqos = '0;
  assign o_dec_2_axi_m_arregion = '0;
  assign o_dec_2_axi_m_aruser = '0;
  assign o_dec_2_axi_m_arlock = 1'b0;
  assign o_dec_2_axi_m_arvalid = 1'b0;
  assign o_dec_2_axi_m_rready = 1'b1;
  assign o_mcu_axi_m_awaddr = '0;
  assign o_mcu_axi_m_awid = '0;
  assign o_mcu_axi_m_awlen = '0;
  assign o_mcu_axi_m_awsize = '0;
  assign o_mcu_axi_m_awburst = '0;
  assign o_mcu_axi_m_awcache = '0;
  assign o_mcu_axi_m_awprot = '0;
  assign o_mcu_axi_m_awlock = 1'b0;
  assign o_mcu_axi_m_awqos = '0;
  assign o_mcu_axi_m_awregion = '0;
  assign o_mcu_axi_m_awuser = '0;
  assign o_mcu_axi_m_awvalid = 1'b0;
  assign o_mcu_axi_m_wdata = '0;
  assign o_mcu_axi_m_wstrb = '0;
  assign o_mcu_axi_m_wlast = 1'b0;
  assign o_mcu_axi_m_wuser = '0;
  assign o_mcu_axi_m_wvalid = 1'b0;
  assign o_mcu_axi_m_bready = 1'b1;
  assign o_mcu_axi_m_araddr = '0;
  assign o_mcu_axi_m_arid = '0;
  assign o_mcu_axi_m_arlen = '0;
  assign o_mcu_axi_m_arsize = '0;
  assign o_mcu_axi_m_arburst = '0;
  assign o_mcu_axi_m_arcache = '0;
  assign o_mcu_axi_m_arprot = '0;
  assign o_mcu_axi_m_arqos = '0;
  assign o_mcu_axi_m_arregion = '0;
  assign o_mcu_axi_m_aruser = '0;
  assign o_mcu_axi_m_arlock = 1'b0;
  assign o_mcu_axi_m_arvalid = 1'b0;
  assign o_mcu_axi_m_rready = 1'b1;
  assign o_ao_rst_sync_n = 1'b0;
  assign o_noc_async_idle_req = 1'b0;
  assign o_noc_mcu_async_idle_req = 1'b0;
  assign o_noc_clk_en = 1'b0;
  assign o_noc_mcu_clk_en = 1'b0;
  assign o_syscfg_apb4_s_pready = 1'b1;
  assign o_syscfg_apb4_s_prdata = '0;
  assign o_syscfg_apb4_s_pslverr = 1'b0;
  assign o_noc_rst_n = 1'b0;
  assign o_noc_mcu_rst_n = 1'b0;
  assign o_dcd_obs = {15+1{1'b0}};
  assign tdo_en = 1'b0;
  assign tdo = 1'b0;

endmodule
