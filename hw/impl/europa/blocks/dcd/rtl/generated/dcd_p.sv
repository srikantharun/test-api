
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//

module dcd_p
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

wire dcd_clk, dcd_mcu_clk;
wire dcd_rst_n, dcd_mcu_rst_n;

wire [31:0] unconnected_pintbus;

wire scan_en = 0;

logic [3:0] ret, pde, prn;


//-------------------------------
// Protocols
//-------------------------------







//-------------------------------
// AXI SPILL for o_dec_0_axi_m
//-------------------------------
  dcd_dec_0_init_mt_axi_id_t o_dec_0_axi_m_subip_awid   ;
  chip_axi_addr_t o_dec_0_axi_m_subip_awaddr ;
  axi_len_t o_dec_0_axi_m_subip_awlen  ;
  axi_size_t o_dec_0_axi_m_subip_awsize ;
  axi_burst_t o_dec_0_axi_m_subip_awburst;
  logic o_dec_0_axi_m_subip_awlock ;
  axi_cache_t o_dec_0_axi_m_subip_awcache;
  axi_prot_t o_dec_0_axi_m_subip_awprot ;
  axi_qos_t o_dec_0_axi_m_subip_awqos  ;
  axi_region_t o_dec_0_axi_m_subip_awregion;
  chip_axi_mt_awuser_t o_dec_0_axi_m_subip_awuser ;
  logic o_dec_0_axi_m_subip_awvalid;
  dcd_dec_0_init_mt_axi_data_t o_dec_0_axi_m_subip_wdata  ;
  dcd_dec_0_init_mt_axi_strb_t o_dec_0_axi_m_subip_wstrb  ;
  logic o_dec_0_axi_m_subip_wlast  ;
  chip_axi_mt_wuser_t o_dec_0_axi_m_subip_wuser  ;
  logic o_dec_0_axi_m_subip_wvalid ;
  logic o_dec_0_axi_m_subip_bready ;
  dcd_dec_0_init_mt_axi_id_t o_dec_0_axi_m_subip_arid   ;
  chip_axi_addr_t o_dec_0_axi_m_subip_araddr ;
  axi_len_t o_dec_0_axi_m_subip_arlen  ;
  axi_size_t o_dec_0_axi_m_subip_arsize ;
  axi_burst_t o_dec_0_axi_m_subip_arburst;
  logic o_dec_0_axi_m_subip_arlock ;
  axi_cache_t o_dec_0_axi_m_subip_arcache;
  axi_prot_t o_dec_0_axi_m_subip_arprot ;
  axi_qos_t o_dec_0_axi_m_subip_arqos  ;
  axi_region_t o_dec_0_axi_m_subip_arregion;
  chip_axi_mt_aruser_t o_dec_0_axi_m_subip_aruser ;
  logic o_dec_0_axi_m_subip_arvalid;
  logic o_dec_0_axi_m_subip_rready ;


//-------------------------------
// AXI SPILL for i_dec_0_axi_m
//-------------------------------
  logic i_dec_0_axi_m_subip_awready;
  logic i_dec_0_axi_m_subip_wready ;
  dcd_dec_0_init_mt_axi_id_t i_dec_0_axi_m_subip_bid    ;
  axi_resp_t i_dec_0_axi_m_subip_bresp  ;
  chip_axi_mt_buser_t i_dec_0_axi_m_subip_buser  ;
  logic i_dec_0_axi_m_subip_bvalid ;
  logic i_dec_0_axi_m_subip_arready;
  dcd_dec_0_init_mt_axi_id_t i_dec_0_axi_m_subip_rid    ;
  dcd_dec_0_init_mt_axi_data_t i_dec_0_axi_m_subip_rdata  ;
  axi_resp_t i_dec_0_axi_m_subip_rresp  ;
  logic i_dec_0_axi_m_subip_rlast  ;
  chip_axi_mt_ruser_t i_dec_0_axi_m_subip_ruser  ;
  logic i_dec_0_axi_m_subip_rvalid ;

axe_axi_multicut_flat #(
  .AxiAddrWidth (CHIP_AXI_ADDR_W),
  .AxiIdWidth (DCD_DEC_0_INIT_MT_AXI_ID_W),
  .AxiDataWidth (DCD_DEC_0_INIT_MT_AXI_DATA_W),
  .NumCuts(1)
  ) i_dec_0_axi_m_spill_flat (
    .i_clk(dcd_clk),
    .i_rst_n(dcd_rst_n),
    .i_axi_s_aw_id(o_dec_0_axi_m_subip_awid),
    .i_axi_s_aw_addr(o_dec_0_axi_m_subip_awaddr),
    .i_axi_s_aw_len(o_dec_0_axi_m_subip_awlen),
    .i_axi_s_aw_size(o_dec_0_axi_m_subip_awsize),
    .i_axi_s_aw_burst(o_dec_0_axi_m_subip_awburst),
    .i_axi_s_aw_lock(o_dec_0_axi_m_subip_awlock),
    .i_axi_s_aw_cache(o_dec_0_axi_m_subip_awcache),
    .i_axi_s_aw_prot(o_dec_0_axi_m_subip_awprot),
    .i_axi_s_aw_qos(o_dec_0_axi_m_subip_awqos),
    .i_axi_s_aw_region(o_dec_0_axi_m_subip_awregion),
    .i_axi_s_aw_user(o_dec_0_axi_m_subip_awuser),
    .i_axi_s_aw_valid(o_dec_0_axi_m_subip_awvalid),
    .o_axi_s_aw_ready(i_dec_0_axi_m_subip_awready),
    .i_axi_s_w_data(o_dec_0_axi_m_subip_wdata),
    .i_axi_s_w_strb(o_dec_0_axi_m_subip_wstrb),
    .i_axi_s_w_last(o_dec_0_axi_m_subip_wlast),
    .i_axi_s_w_user(o_dec_0_axi_m_subip_wuser),
    .i_axi_s_w_valid(o_dec_0_axi_m_subip_wvalid),
    .o_axi_s_w_ready(i_dec_0_axi_m_subip_wready),
    .o_axi_s_b_id(i_dec_0_axi_m_subip_bid),
    .o_axi_s_b_resp(i_dec_0_axi_m_subip_bresp),
    .o_axi_s_b_user(i_dec_0_axi_m_subip_buser),
    .o_axi_s_b_valid(i_dec_0_axi_m_subip_bvalid),
    .i_axi_s_b_ready(o_dec_0_axi_m_subip_bready),
    .i_axi_s_ar_id(o_dec_0_axi_m_subip_arid),
    .i_axi_s_ar_addr(o_dec_0_axi_m_subip_araddr),
    .i_axi_s_ar_len(o_dec_0_axi_m_subip_arlen),
    .i_axi_s_ar_size(o_dec_0_axi_m_subip_arsize),
    .i_axi_s_ar_burst(o_dec_0_axi_m_subip_arburst),
    .i_axi_s_ar_lock(o_dec_0_axi_m_subip_arlock),
    .i_axi_s_ar_cache(o_dec_0_axi_m_subip_arcache),
    .i_axi_s_ar_prot(o_dec_0_axi_m_subip_arprot),
    .i_axi_s_ar_qos(o_dec_0_axi_m_subip_arqos),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user(o_dec_0_axi_m_subip_aruser),
    .i_axi_s_ar_valid(o_dec_0_axi_m_subip_arvalid),
    .o_axi_s_ar_ready(i_dec_0_axi_m_subip_arready),
    .o_axi_s_r_id(i_dec_0_axi_m_subip_rid),
    .o_axi_s_r_data(i_dec_0_axi_m_subip_rdata),
    .o_axi_s_r_resp(i_dec_0_axi_m_subip_rresp),
    .o_axi_s_r_last(i_dec_0_axi_m_subip_rlast),
    .o_axi_s_r_user(i_dec_0_axi_m_subip_ruser),
    .o_axi_s_r_valid(i_dec_0_axi_m_subip_rvalid),
    .i_axi_s_r_ready(o_dec_0_axi_m_subip_rready),
    .o_axi_m_aw_id(o_dec_0_axi_m_awid),
    .o_axi_m_aw_addr(o_dec_0_axi_m_awaddr),
    .o_axi_m_aw_len(o_dec_0_axi_m_awlen),
    .o_axi_m_aw_size(o_dec_0_axi_m_awsize),
    .o_axi_m_aw_burst(o_dec_0_axi_m_awburst),
    .o_axi_m_aw_lock(o_dec_0_axi_m_awlock),
    .o_axi_m_aw_cache(o_dec_0_axi_m_awcache),
    .o_axi_m_aw_prot(o_dec_0_axi_m_awprot),
    .o_axi_m_aw_qos(o_dec_0_axi_m_awqos),
    .o_axi_m_aw_region(o_dec_0_axi_m_awregion),
    .o_axi_m_aw_valid(o_dec_0_axi_m_awvalid),
    .o_axi_m_aw_user(o_dec_0_axi_m_awuser),
    .i_axi_m_aw_ready(i_dec_0_axi_m_awready),
    .o_axi_m_w_data(o_dec_0_axi_m_wdata),
    .o_axi_m_w_strb(o_dec_0_axi_m_wstrb),
    .o_axi_m_w_last(o_dec_0_axi_m_wlast),
    .o_axi_m_w_user(o_dec_0_axi_m_wuser),
    .o_axi_m_w_valid(o_dec_0_axi_m_wvalid),
    .i_axi_m_w_ready(i_dec_0_axi_m_wready),
    .i_axi_m_b_id(i_dec_0_axi_m_bid),
    .i_axi_m_b_resp(i_dec_0_axi_m_bresp),
    .i_axi_m_b_user(i_dec_0_axi_m_buser),
    .i_axi_m_b_valid(i_dec_0_axi_m_bvalid),
    .o_axi_m_b_ready(o_dec_0_axi_m_bready),
    .o_axi_m_ar_id(o_dec_0_axi_m_arid),
    .o_axi_m_ar_addr(o_dec_0_axi_m_araddr),
    .o_axi_m_ar_len(o_dec_0_axi_m_arlen),
    .o_axi_m_ar_size(o_dec_0_axi_m_arsize),
    .o_axi_m_ar_burst(o_dec_0_axi_m_arburst),
    .o_axi_m_ar_lock(o_dec_0_axi_m_arlock),
    .o_axi_m_ar_cache(o_dec_0_axi_m_arcache),
    .o_axi_m_ar_prot(o_dec_0_axi_m_arprot),
    .o_axi_m_ar_qos(o_dec_0_axi_m_arqos),
    .o_axi_m_ar_region(o_dec_0_axi_m_arregion),
    .o_axi_m_ar_user(o_dec_0_axi_m_aruser),
    .o_axi_m_ar_valid(o_dec_0_axi_m_arvalid),
    .i_axi_m_ar_ready(i_dec_0_axi_m_arready),
    .i_axi_m_r_id(i_dec_0_axi_m_rid),
    .i_axi_m_r_data(i_dec_0_axi_m_rdata),
    .i_axi_m_r_resp(i_dec_0_axi_m_rresp),
    .i_axi_m_r_last(i_dec_0_axi_m_rlast),
    .i_axi_m_r_user(i_dec_0_axi_m_ruser),
    .i_axi_m_r_valid(i_dec_0_axi_m_rvalid),
    .o_axi_m_r_ready(o_dec_0_axi_m_rready)
);
//-------------------------------
// AXI SPILL for o_dec_1_axi_m
//-------------------------------
  dcd_dec_1_init_mt_axi_id_t o_dec_1_axi_m_subip_awid   ;
  chip_axi_addr_t o_dec_1_axi_m_subip_awaddr ;
  axi_len_t o_dec_1_axi_m_subip_awlen  ;
  axi_size_t o_dec_1_axi_m_subip_awsize ;
  axi_burst_t o_dec_1_axi_m_subip_awburst;
  logic o_dec_1_axi_m_subip_awlock ;
  axi_cache_t o_dec_1_axi_m_subip_awcache;
  axi_prot_t o_dec_1_axi_m_subip_awprot ;
  axi_qos_t o_dec_1_axi_m_subip_awqos  ;
  axi_region_t o_dec_1_axi_m_subip_awregion;
  chip_axi_mt_awuser_t o_dec_1_axi_m_subip_awuser ;
  logic o_dec_1_axi_m_subip_awvalid;
  dcd_dec_1_init_mt_axi_data_t o_dec_1_axi_m_subip_wdata  ;
  dcd_dec_1_init_mt_axi_strb_t o_dec_1_axi_m_subip_wstrb  ;
  logic o_dec_1_axi_m_subip_wlast  ;
  chip_axi_mt_wuser_t o_dec_1_axi_m_subip_wuser  ;
  logic o_dec_1_axi_m_subip_wvalid ;
  logic o_dec_1_axi_m_subip_bready ;
  dcd_dec_1_init_mt_axi_id_t o_dec_1_axi_m_subip_arid   ;
  chip_axi_addr_t o_dec_1_axi_m_subip_araddr ;
  axi_len_t o_dec_1_axi_m_subip_arlen  ;
  axi_size_t o_dec_1_axi_m_subip_arsize ;
  axi_burst_t o_dec_1_axi_m_subip_arburst;
  logic o_dec_1_axi_m_subip_arlock ;
  axi_cache_t o_dec_1_axi_m_subip_arcache;
  axi_prot_t o_dec_1_axi_m_subip_arprot ;
  axi_qos_t o_dec_1_axi_m_subip_arqos  ;
  axi_region_t o_dec_1_axi_m_subip_arregion;
  chip_axi_mt_aruser_t o_dec_1_axi_m_subip_aruser ;
  logic o_dec_1_axi_m_subip_arvalid;
  logic o_dec_1_axi_m_subip_rready ;


//-------------------------------
// AXI SPILL for i_dec_1_axi_m
//-------------------------------
  logic i_dec_1_axi_m_subip_awready;
  logic i_dec_1_axi_m_subip_wready ;
  dcd_dec_1_init_mt_axi_id_t i_dec_1_axi_m_subip_bid    ;
  axi_resp_t i_dec_1_axi_m_subip_bresp  ;
  chip_axi_mt_buser_t i_dec_1_axi_m_subip_buser  ;
  logic i_dec_1_axi_m_subip_bvalid ;
  logic i_dec_1_axi_m_subip_arready;
  dcd_dec_1_init_mt_axi_id_t i_dec_1_axi_m_subip_rid    ;
  dcd_dec_1_init_mt_axi_data_t i_dec_1_axi_m_subip_rdata  ;
  axi_resp_t i_dec_1_axi_m_subip_rresp  ;
  logic i_dec_1_axi_m_subip_rlast  ;
  chip_axi_mt_ruser_t i_dec_1_axi_m_subip_ruser  ;
  logic i_dec_1_axi_m_subip_rvalid ;

axe_axi_multicut_flat #(
  .AxiAddrWidth (CHIP_AXI_ADDR_W),
  .AxiIdWidth (DCD_DEC_1_INIT_MT_AXI_ID_W),
  .AxiDataWidth (DCD_DEC_1_INIT_MT_AXI_DATA_W),
  .NumCuts(1)
  ) i_dec_1_axi_m_spill_flat (
    .i_clk(dcd_clk),
    .i_rst_n(dcd_rst_n),
    .i_axi_s_aw_id(o_dec_1_axi_m_subip_awid),
    .i_axi_s_aw_addr(o_dec_1_axi_m_subip_awaddr),
    .i_axi_s_aw_len(o_dec_1_axi_m_subip_awlen),
    .i_axi_s_aw_size(o_dec_1_axi_m_subip_awsize),
    .i_axi_s_aw_burst(o_dec_1_axi_m_subip_awburst),
    .i_axi_s_aw_lock(o_dec_1_axi_m_subip_awlock),
    .i_axi_s_aw_cache(o_dec_1_axi_m_subip_awcache),
    .i_axi_s_aw_prot(o_dec_1_axi_m_subip_awprot),
    .i_axi_s_aw_qos(o_dec_1_axi_m_subip_awqos),
    .i_axi_s_aw_region(o_dec_1_axi_m_subip_awregion),
    .i_axi_s_aw_user(o_dec_1_axi_m_subip_awuser),
    .i_axi_s_aw_valid(o_dec_1_axi_m_subip_awvalid),
    .o_axi_s_aw_ready(i_dec_1_axi_m_subip_awready),
    .i_axi_s_w_data(o_dec_1_axi_m_subip_wdata),
    .i_axi_s_w_strb(o_dec_1_axi_m_subip_wstrb),
    .i_axi_s_w_last(o_dec_1_axi_m_subip_wlast),
    .i_axi_s_w_user(o_dec_1_axi_m_subip_wuser),
    .i_axi_s_w_valid(o_dec_1_axi_m_subip_wvalid),
    .o_axi_s_w_ready(i_dec_1_axi_m_subip_wready),
    .o_axi_s_b_id(i_dec_1_axi_m_subip_bid),
    .o_axi_s_b_resp(i_dec_1_axi_m_subip_bresp),
    .o_axi_s_b_user(i_dec_1_axi_m_subip_buser),
    .o_axi_s_b_valid(i_dec_1_axi_m_subip_bvalid),
    .i_axi_s_b_ready(o_dec_1_axi_m_subip_bready),
    .i_axi_s_ar_id(o_dec_1_axi_m_subip_arid),
    .i_axi_s_ar_addr(o_dec_1_axi_m_subip_araddr),
    .i_axi_s_ar_len(o_dec_1_axi_m_subip_arlen),
    .i_axi_s_ar_size(o_dec_1_axi_m_subip_arsize),
    .i_axi_s_ar_burst(o_dec_1_axi_m_subip_arburst),
    .i_axi_s_ar_lock(o_dec_1_axi_m_subip_arlock),
    .i_axi_s_ar_cache(o_dec_1_axi_m_subip_arcache),
    .i_axi_s_ar_prot(o_dec_1_axi_m_subip_arprot),
    .i_axi_s_ar_qos(o_dec_1_axi_m_subip_arqos),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user(o_dec_1_axi_m_subip_aruser),
    .i_axi_s_ar_valid(o_dec_1_axi_m_subip_arvalid),
    .o_axi_s_ar_ready(i_dec_1_axi_m_subip_arready),
    .o_axi_s_r_id(i_dec_1_axi_m_subip_rid),
    .o_axi_s_r_data(i_dec_1_axi_m_subip_rdata),
    .o_axi_s_r_resp(i_dec_1_axi_m_subip_rresp),
    .o_axi_s_r_last(i_dec_1_axi_m_subip_rlast),
    .o_axi_s_r_user(i_dec_1_axi_m_subip_ruser),
    .o_axi_s_r_valid(i_dec_1_axi_m_subip_rvalid),
    .i_axi_s_r_ready(o_dec_1_axi_m_subip_rready),
    .o_axi_m_aw_id(o_dec_1_axi_m_awid),
    .o_axi_m_aw_addr(o_dec_1_axi_m_awaddr),
    .o_axi_m_aw_len(o_dec_1_axi_m_awlen),
    .o_axi_m_aw_size(o_dec_1_axi_m_awsize),
    .o_axi_m_aw_burst(o_dec_1_axi_m_awburst),
    .o_axi_m_aw_lock(o_dec_1_axi_m_awlock),
    .o_axi_m_aw_cache(o_dec_1_axi_m_awcache),
    .o_axi_m_aw_prot(o_dec_1_axi_m_awprot),
    .o_axi_m_aw_qos(o_dec_1_axi_m_awqos),
    .o_axi_m_aw_region(o_dec_1_axi_m_awregion),
    .o_axi_m_aw_valid(o_dec_1_axi_m_awvalid),
    .o_axi_m_aw_user(o_dec_1_axi_m_awuser),
    .i_axi_m_aw_ready(i_dec_1_axi_m_awready),
    .o_axi_m_w_data(o_dec_1_axi_m_wdata),
    .o_axi_m_w_strb(o_dec_1_axi_m_wstrb),
    .o_axi_m_w_last(o_dec_1_axi_m_wlast),
    .o_axi_m_w_user(o_dec_1_axi_m_wuser),
    .o_axi_m_w_valid(o_dec_1_axi_m_wvalid),
    .i_axi_m_w_ready(i_dec_1_axi_m_wready),
    .i_axi_m_b_id(i_dec_1_axi_m_bid),
    .i_axi_m_b_resp(i_dec_1_axi_m_bresp),
    .i_axi_m_b_user(i_dec_1_axi_m_buser),
    .i_axi_m_b_valid(i_dec_1_axi_m_bvalid),
    .o_axi_m_b_ready(o_dec_1_axi_m_bready),
    .o_axi_m_ar_id(o_dec_1_axi_m_arid),
    .o_axi_m_ar_addr(o_dec_1_axi_m_araddr),
    .o_axi_m_ar_len(o_dec_1_axi_m_arlen),
    .o_axi_m_ar_size(o_dec_1_axi_m_arsize),
    .o_axi_m_ar_burst(o_dec_1_axi_m_arburst),
    .o_axi_m_ar_lock(o_dec_1_axi_m_arlock),
    .o_axi_m_ar_cache(o_dec_1_axi_m_arcache),
    .o_axi_m_ar_prot(o_dec_1_axi_m_arprot),
    .o_axi_m_ar_qos(o_dec_1_axi_m_arqos),
    .o_axi_m_ar_region(o_dec_1_axi_m_arregion),
    .o_axi_m_ar_user(o_dec_1_axi_m_aruser),
    .o_axi_m_ar_valid(o_dec_1_axi_m_arvalid),
    .i_axi_m_ar_ready(i_dec_1_axi_m_arready),
    .i_axi_m_r_id(i_dec_1_axi_m_rid),
    .i_axi_m_r_data(i_dec_1_axi_m_rdata),
    .i_axi_m_r_resp(i_dec_1_axi_m_rresp),
    .i_axi_m_r_last(i_dec_1_axi_m_rlast),
    .i_axi_m_r_user(i_dec_1_axi_m_ruser),
    .i_axi_m_r_valid(i_dec_1_axi_m_rvalid),
    .o_axi_m_r_ready(o_dec_1_axi_m_rready)
);
//-------------------------------
// AXI SPILL for o_dec_2_axi_m
//-------------------------------
  dcd_dec_2_init_mt_axi_id_t o_dec_2_axi_m_subip_awid   ;
  chip_axi_addr_t o_dec_2_axi_m_subip_awaddr ;
  axi_len_t o_dec_2_axi_m_subip_awlen  ;
  axi_size_t o_dec_2_axi_m_subip_awsize ;
  axi_burst_t o_dec_2_axi_m_subip_awburst;
  logic o_dec_2_axi_m_subip_awlock ;
  axi_cache_t o_dec_2_axi_m_subip_awcache;
  axi_prot_t o_dec_2_axi_m_subip_awprot ;
  axi_qos_t o_dec_2_axi_m_subip_awqos  ;
  axi_region_t o_dec_2_axi_m_subip_awregion;
  chip_axi_mt_awuser_t o_dec_2_axi_m_subip_awuser ;
  logic o_dec_2_axi_m_subip_awvalid;
  dcd_dec_2_init_mt_axi_data_t o_dec_2_axi_m_subip_wdata  ;
  dcd_dec_2_init_mt_axi_strb_t o_dec_2_axi_m_subip_wstrb  ;
  logic o_dec_2_axi_m_subip_wlast  ;
  chip_axi_mt_wuser_t o_dec_2_axi_m_subip_wuser  ;
  logic o_dec_2_axi_m_subip_wvalid ;
  logic o_dec_2_axi_m_subip_bready ;
  dcd_dec_2_init_mt_axi_id_t o_dec_2_axi_m_subip_arid   ;
  chip_axi_addr_t o_dec_2_axi_m_subip_araddr ;
  axi_len_t o_dec_2_axi_m_subip_arlen  ;
  axi_size_t o_dec_2_axi_m_subip_arsize ;
  axi_burst_t o_dec_2_axi_m_subip_arburst;
  logic o_dec_2_axi_m_subip_arlock ;
  axi_cache_t o_dec_2_axi_m_subip_arcache;
  axi_prot_t o_dec_2_axi_m_subip_arprot ;
  axi_qos_t o_dec_2_axi_m_subip_arqos  ;
  axi_region_t o_dec_2_axi_m_subip_arregion;
  chip_axi_mt_aruser_t o_dec_2_axi_m_subip_aruser ;
  logic o_dec_2_axi_m_subip_arvalid;
  logic o_dec_2_axi_m_subip_rready ;


//-------------------------------
// AXI SPILL for i_dec_2_axi_m
//-------------------------------
  logic i_dec_2_axi_m_subip_awready;
  logic i_dec_2_axi_m_subip_wready ;
  dcd_dec_2_init_mt_axi_id_t i_dec_2_axi_m_subip_bid    ;
  axi_resp_t i_dec_2_axi_m_subip_bresp  ;
  chip_axi_mt_buser_t i_dec_2_axi_m_subip_buser  ;
  logic i_dec_2_axi_m_subip_bvalid ;
  logic i_dec_2_axi_m_subip_arready;
  dcd_dec_2_init_mt_axi_id_t i_dec_2_axi_m_subip_rid    ;
  dcd_dec_2_init_mt_axi_data_t i_dec_2_axi_m_subip_rdata  ;
  axi_resp_t i_dec_2_axi_m_subip_rresp  ;
  logic i_dec_2_axi_m_subip_rlast  ;
  chip_axi_mt_ruser_t i_dec_2_axi_m_subip_ruser  ;
  logic i_dec_2_axi_m_subip_rvalid ;

axe_axi_multicut_flat #(
  .AxiAddrWidth (CHIP_AXI_ADDR_W),
  .AxiIdWidth (DCD_DEC_2_INIT_MT_AXI_ID_W),
  .AxiDataWidth (DCD_DEC_2_INIT_MT_AXI_DATA_W),
  .NumCuts(1)
  ) i_dec_2_axi_m_spill_flat (
    .i_clk(dcd_clk),
    .i_rst_n(dcd_rst_n),
    .i_axi_s_aw_id(o_dec_2_axi_m_subip_awid),
    .i_axi_s_aw_addr(o_dec_2_axi_m_subip_awaddr),
    .i_axi_s_aw_len(o_dec_2_axi_m_subip_awlen),
    .i_axi_s_aw_size(o_dec_2_axi_m_subip_awsize),
    .i_axi_s_aw_burst(o_dec_2_axi_m_subip_awburst),
    .i_axi_s_aw_lock(o_dec_2_axi_m_subip_awlock),
    .i_axi_s_aw_cache(o_dec_2_axi_m_subip_awcache),
    .i_axi_s_aw_prot(o_dec_2_axi_m_subip_awprot),
    .i_axi_s_aw_qos(o_dec_2_axi_m_subip_awqos),
    .i_axi_s_aw_region(o_dec_2_axi_m_subip_awregion),
    .i_axi_s_aw_user(o_dec_2_axi_m_subip_awuser),
    .i_axi_s_aw_valid(o_dec_2_axi_m_subip_awvalid),
    .o_axi_s_aw_ready(i_dec_2_axi_m_subip_awready),
    .i_axi_s_w_data(o_dec_2_axi_m_subip_wdata),
    .i_axi_s_w_strb(o_dec_2_axi_m_subip_wstrb),
    .i_axi_s_w_last(o_dec_2_axi_m_subip_wlast),
    .i_axi_s_w_user(o_dec_2_axi_m_subip_wuser),
    .i_axi_s_w_valid(o_dec_2_axi_m_subip_wvalid),
    .o_axi_s_w_ready(i_dec_2_axi_m_subip_wready),
    .o_axi_s_b_id(i_dec_2_axi_m_subip_bid),
    .o_axi_s_b_resp(i_dec_2_axi_m_subip_bresp),
    .o_axi_s_b_user(i_dec_2_axi_m_subip_buser),
    .o_axi_s_b_valid(i_dec_2_axi_m_subip_bvalid),
    .i_axi_s_b_ready(o_dec_2_axi_m_subip_bready),
    .i_axi_s_ar_id(o_dec_2_axi_m_subip_arid),
    .i_axi_s_ar_addr(o_dec_2_axi_m_subip_araddr),
    .i_axi_s_ar_len(o_dec_2_axi_m_subip_arlen),
    .i_axi_s_ar_size(o_dec_2_axi_m_subip_arsize),
    .i_axi_s_ar_burst(o_dec_2_axi_m_subip_arburst),
    .i_axi_s_ar_lock(o_dec_2_axi_m_subip_arlock),
    .i_axi_s_ar_cache(o_dec_2_axi_m_subip_arcache),
    .i_axi_s_ar_prot(o_dec_2_axi_m_subip_arprot),
    .i_axi_s_ar_qos(o_dec_2_axi_m_subip_arqos),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user(o_dec_2_axi_m_subip_aruser),
    .i_axi_s_ar_valid(o_dec_2_axi_m_subip_arvalid),
    .o_axi_s_ar_ready(i_dec_2_axi_m_subip_arready),
    .o_axi_s_r_id(i_dec_2_axi_m_subip_rid),
    .o_axi_s_r_data(i_dec_2_axi_m_subip_rdata),
    .o_axi_s_r_resp(i_dec_2_axi_m_subip_rresp),
    .o_axi_s_r_last(i_dec_2_axi_m_subip_rlast),
    .o_axi_s_r_user(i_dec_2_axi_m_subip_ruser),
    .o_axi_s_r_valid(i_dec_2_axi_m_subip_rvalid),
    .i_axi_s_r_ready(o_dec_2_axi_m_subip_rready),
    .o_axi_m_aw_id(o_dec_2_axi_m_awid),
    .o_axi_m_aw_addr(o_dec_2_axi_m_awaddr),
    .o_axi_m_aw_len(o_dec_2_axi_m_awlen),
    .o_axi_m_aw_size(o_dec_2_axi_m_awsize),
    .o_axi_m_aw_burst(o_dec_2_axi_m_awburst),
    .o_axi_m_aw_lock(o_dec_2_axi_m_awlock),
    .o_axi_m_aw_cache(o_dec_2_axi_m_awcache),
    .o_axi_m_aw_prot(o_dec_2_axi_m_awprot),
    .o_axi_m_aw_qos(o_dec_2_axi_m_awqos),
    .o_axi_m_aw_region(o_dec_2_axi_m_awregion),
    .o_axi_m_aw_valid(o_dec_2_axi_m_awvalid),
    .o_axi_m_aw_user(o_dec_2_axi_m_awuser),
    .i_axi_m_aw_ready(i_dec_2_axi_m_awready),
    .o_axi_m_w_data(o_dec_2_axi_m_wdata),
    .o_axi_m_w_strb(o_dec_2_axi_m_wstrb),
    .o_axi_m_w_last(o_dec_2_axi_m_wlast),
    .o_axi_m_w_user(o_dec_2_axi_m_wuser),
    .o_axi_m_w_valid(o_dec_2_axi_m_wvalid),
    .i_axi_m_w_ready(i_dec_2_axi_m_wready),
    .i_axi_m_b_id(i_dec_2_axi_m_bid),
    .i_axi_m_b_resp(i_dec_2_axi_m_bresp),
    .i_axi_m_b_user(i_dec_2_axi_m_buser),
    .i_axi_m_b_valid(i_dec_2_axi_m_bvalid),
    .o_axi_m_b_ready(o_dec_2_axi_m_bready),
    .o_axi_m_ar_id(o_dec_2_axi_m_arid),
    .o_axi_m_ar_addr(o_dec_2_axi_m_araddr),
    .o_axi_m_ar_len(o_dec_2_axi_m_arlen),
    .o_axi_m_ar_size(o_dec_2_axi_m_arsize),
    .o_axi_m_ar_burst(o_dec_2_axi_m_arburst),
    .o_axi_m_ar_lock(o_dec_2_axi_m_arlock),
    .o_axi_m_ar_cache(o_dec_2_axi_m_arcache),
    .o_axi_m_ar_prot(o_dec_2_axi_m_arprot),
    .o_axi_m_ar_qos(o_dec_2_axi_m_arqos),
    .o_axi_m_ar_region(o_dec_2_axi_m_arregion),
    .o_axi_m_ar_user(o_dec_2_axi_m_aruser),
    .o_axi_m_ar_valid(o_dec_2_axi_m_arvalid),
    .i_axi_m_ar_ready(i_dec_2_axi_m_arready),
    .i_axi_m_r_id(i_dec_2_axi_m_rid),
    .i_axi_m_r_data(i_dec_2_axi_m_rdata),
    .i_axi_m_r_resp(i_dec_2_axi_m_rresp),
    .i_axi_m_r_last(i_dec_2_axi_m_rlast),
    .i_axi_m_r_user(i_dec_2_axi_m_ruser),
    .i_axi_m_r_valid(i_dec_2_axi_m_rvalid),
    .o_axi_m_r_ready(o_dec_2_axi_m_rready)
);
//-------------------------------
// AXI SPILL for o_mcu_axi_m
//-------------------------------
  dcd_mcu_init_lt_axi_id_t o_mcu_axi_m_subip_awid   ;
  chip_axi_addr_t o_mcu_axi_m_subip_awaddr ;
  axi_len_t o_mcu_axi_m_subip_awlen  ;
  axi_size_t o_mcu_axi_m_subip_awsize ;
  axi_burst_t o_mcu_axi_m_subip_awburst;
  logic o_mcu_axi_m_subip_awlock ;
  axi_cache_t o_mcu_axi_m_subip_awcache;
  axi_prot_t o_mcu_axi_m_subip_awprot ;
  axi_qos_t o_mcu_axi_m_subip_awqos  ;
  axi_region_t o_mcu_axi_m_subip_awregion;
  chip_axi_mt_awuser_t o_mcu_axi_m_subip_awuser ;
  logic o_mcu_axi_m_subip_awvalid;
  dcd_mcu_init_lt_axi_data_t o_mcu_axi_m_subip_wdata  ;
  dcd_mcu_init_lt_axi_strb_t o_mcu_axi_m_subip_wstrb  ;
  logic o_mcu_axi_m_subip_wlast  ;
  chip_axi_mt_wuser_t o_mcu_axi_m_subip_wuser  ;
  logic o_mcu_axi_m_subip_wvalid ;
  logic o_mcu_axi_m_subip_bready ;
  dcd_mcu_init_lt_axi_id_t o_mcu_axi_m_subip_arid   ;
  chip_axi_addr_t o_mcu_axi_m_subip_araddr ;
  axi_len_t o_mcu_axi_m_subip_arlen  ;
  axi_size_t o_mcu_axi_m_subip_arsize ;
  axi_burst_t o_mcu_axi_m_subip_arburst;
  logic o_mcu_axi_m_subip_arlock ;
  axi_cache_t o_mcu_axi_m_subip_arcache;
  axi_prot_t o_mcu_axi_m_subip_arprot ;
  axi_qos_t o_mcu_axi_m_subip_arqos  ;
  axi_region_t o_mcu_axi_m_subip_arregion;
  chip_axi_mt_aruser_t o_mcu_axi_m_subip_aruser ;
  logic o_mcu_axi_m_subip_arvalid;
  logic o_mcu_axi_m_subip_rready ;


//-------------------------------
// AXI SPILL for i_mcu_axi_m
//-------------------------------
  logic i_mcu_axi_m_subip_awready;
  logic i_mcu_axi_m_subip_wready ;
  dcd_mcu_init_lt_axi_id_t i_mcu_axi_m_subip_bid    ;
  axi_resp_t i_mcu_axi_m_subip_bresp  ;
  chip_axi_mt_buser_t i_mcu_axi_m_subip_buser  ;
  logic i_mcu_axi_m_subip_bvalid ;
  logic i_mcu_axi_m_subip_arready;
  dcd_mcu_init_lt_axi_id_t i_mcu_axi_m_subip_rid    ;
  dcd_mcu_init_lt_axi_data_t i_mcu_axi_m_subip_rdata  ;
  axi_resp_t i_mcu_axi_m_subip_rresp  ;
  logic i_mcu_axi_m_subip_rlast  ;
  chip_axi_mt_ruser_t i_mcu_axi_m_subip_ruser  ;
  logic i_mcu_axi_m_subip_rvalid ;

axe_axi_multicut_flat #(
  .AxiAddrWidth (CHIP_AXI_ADDR_W),
  .AxiIdWidth (DCD_MCU_INIT_LT_AXI_ID_W),
  .AxiDataWidth (DCD_MCU_INIT_LT_AXI_DATA_W),
  .NumCuts(1)
  ) i_mcu_axi_m_spill_flat (
    .i_clk(dcd_mcu_clk),
    .i_rst_n(dcd_mcu_rst_n),
    .i_axi_s_aw_id(o_mcu_axi_m_subip_awid),
    .i_axi_s_aw_addr(o_mcu_axi_m_subip_awaddr),
    .i_axi_s_aw_len(o_mcu_axi_m_subip_awlen),
    .i_axi_s_aw_size(o_mcu_axi_m_subip_awsize),
    .i_axi_s_aw_burst(o_mcu_axi_m_subip_awburst),
    .i_axi_s_aw_lock(o_mcu_axi_m_subip_awlock),
    .i_axi_s_aw_cache(o_mcu_axi_m_subip_awcache),
    .i_axi_s_aw_prot(o_mcu_axi_m_subip_awprot),
    .i_axi_s_aw_qos(o_mcu_axi_m_subip_awqos),
    .i_axi_s_aw_region(o_mcu_axi_m_subip_awregion),
    .i_axi_s_aw_user(o_mcu_axi_m_subip_awuser),
    .i_axi_s_aw_valid(o_mcu_axi_m_subip_awvalid),
    .o_axi_s_aw_ready(i_mcu_axi_m_subip_awready),
    .i_axi_s_w_data(o_mcu_axi_m_subip_wdata),
    .i_axi_s_w_strb(o_mcu_axi_m_subip_wstrb),
    .i_axi_s_w_last(o_mcu_axi_m_subip_wlast),
    .i_axi_s_w_user(o_mcu_axi_m_subip_wuser),
    .i_axi_s_w_valid(o_mcu_axi_m_subip_wvalid),
    .o_axi_s_w_ready(i_mcu_axi_m_subip_wready),
    .o_axi_s_b_id(i_mcu_axi_m_subip_bid),
    .o_axi_s_b_resp(i_mcu_axi_m_subip_bresp),
    .o_axi_s_b_user(i_mcu_axi_m_subip_buser),
    .o_axi_s_b_valid(i_mcu_axi_m_subip_bvalid),
    .i_axi_s_b_ready(o_mcu_axi_m_subip_bready),
    .i_axi_s_ar_id(o_mcu_axi_m_subip_arid),
    .i_axi_s_ar_addr(o_mcu_axi_m_subip_araddr),
    .i_axi_s_ar_len(o_mcu_axi_m_subip_arlen),
    .i_axi_s_ar_size(o_mcu_axi_m_subip_arsize),
    .i_axi_s_ar_burst(o_mcu_axi_m_subip_arburst),
    .i_axi_s_ar_lock(o_mcu_axi_m_subip_arlock),
    .i_axi_s_ar_cache(o_mcu_axi_m_subip_arcache),
    .i_axi_s_ar_prot(o_mcu_axi_m_subip_arprot),
    .i_axi_s_ar_qos(o_mcu_axi_m_subip_arqos),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user(o_mcu_axi_m_subip_aruser),
    .i_axi_s_ar_valid(o_mcu_axi_m_subip_arvalid),
    .o_axi_s_ar_ready(i_mcu_axi_m_subip_arready),
    .o_axi_s_r_id(i_mcu_axi_m_subip_rid),
    .o_axi_s_r_data(i_mcu_axi_m_subip_rdata),
    .o_axi_s_r_resp(i_mcu_axi_m_subip_rresp),
    .o_axi_s_r_last(i_mcu_axi_m_subip_rlast),
    .o_axi_s_r_user(i_mcu_axi_m_subip_ruser),
    .o_axi_s_r_valid(i_mcu_axi_m_subip_rvalid),
    .i_axi_s_r_ready(o_mcu_axi_m_subip_rready),
    .o_axi_m_aw_id(o_mcu_axi_m_awid),
    .o_axi_m_aw_addr(o_mcu_axi_m_awaddr),
    .o_axi_m_aw_len(o_mcu_axi_m_awlen),
    .o_axi_m_aw_size(o_mcu_axi_m_awsize),
    .o_axi_m_aw_burst(o_mcu_axi_m_awburst),
    .o_axi_m_aw_lock(o_mcu_axi_m_awlock),
    .o_axi_m_aw_cache(o_mcu_axi_m_awcache),
    .o_axi_m_aw_prot(o_mcu_axi_m_awprot),
    .o_axi_m_aw_qos(o_mcu_axi_m_awqos),
    .o_axi_m_aw_region(o_mcu_axi_m_awregion),
    .o_axi_m_aw_valid(o_mcu_axi_m_awvalid),
    .o_axi_m_aw_user(o_mcu_axi_m_awuser),
    .i_axi_m_aw_ready(i_mcu_axi_m_awready),
    .o_axi_m_w_data(o_mcu_axi_m_wdata),
    .o_axi_m_w_strb(o_mcu_axi_m_wstrb),
    .o_axi_m_w_last(o_mcu_axi_m_wlast),
    .o_axi_m_w_user(o_mcu_axi_m_wuser),
    .o_axi_m_w_valid(o_mcu_axi_m_wvalid),
    .i_axi_m_w_ready(i_mcu_axi_m_wready),
    .i_axi_m_b_id(i_mcu_axi_m_bid),
    .i_axi_m_b_resp(i_mcu_axi_m_bresp),
    .i_axi_m_b_user(i_mcu_axi_m_buser),
    .i_axi_m_b_valid(i_mcu_axi_m_bvalid),
    .o_axi_m_b_ready(o_mcu_axi_m_bready),
    .o_axi_m_ar_id(o_mcu_axi_m_arid),
    .o_axi_m_ar_addr(o_mcu_axi_m_araddr),
    .o_axi_m_ar_len(o_mcu_axi_m_arlen),
    .o_axi_m_ar_size(o_mcu_axi_m_arsize),
    .o_axi_m_ar_burst(o_mcu_axi_m_arburst),
    .o_axi_m_ar_lock(o_mcu_axi_m_arlock),
    .o_axi_m_ar_cache(o_mcu_axi_m_arcache),
    .o_axi_m_ar_prot(o_mcu_axi_m_arprot),
    .o_axi_m_ar_qos(o_mcu_axi_m_arqos),
    .o_axi_m_ar_region(o_mcu_axi_m_arregion),
    .o_axi_m_ar_user(o_mcu_axi_m_aruser),
    .o_axi_m_ar_valid(o_mcu_axi_m_arvalid),
    .i_axi_m_ar_ready(i_mcu_axi_m_arready),
    .i_axi_m_r_id(i_mcu_axi_m_rid),
    .i_axi_m_r_data(i_mcu_axi_m_rdata),
    .i_axi_m_r_resp(i_mcu_axi_m_rresp),
    .i_axi_m_r_last(i_mcu_axi_m_rlast),
    .i_axi_m_r_user(i_mcu_axi_m_ruser),
    .i_axi_m_r_valid(i_mcu_axi_m_rvalid),
    .o_axi_m_r_ready(o_mcu_axi_m_rready)
);
//-------------------------------
// Wrapped module instantiation
//-------------------------------
dcd u_dcd (
  .i_clk(dcd_clk),
  .i_mcu_clk(dcd_mcu_clk),
  .i_jtag_clk(i_jtag_clk),
  .i_rst_n(dcd_rst_n),
  .i_mcu_rst_n(dcd_mcu_rst_n),
  .i_jtag_rst_n(i_jtag_rst_n),
  .o_mcu_int_next(unconnected_mcu_int_next),
  .i_mcu_ack_next(1'b0),
  .i_mcu_int_prev(1'b0),
  .o_mcu_ack_prev(unconnected_mcu_ack_prev),
  .i_jtag_ms(i_jtag_ms),
  .i_jtag_di(i_jtag_di),
  .o_jtag_do(o_jtag_do),
  .i_cfg_apb4_s_paddr(i_cfg_apb4_s_paddr),
  .i_cfg_apb4_s_pwdata(i_cfg_apb4_s_pwdata),
  .i_cfg_apb4_s_pwrite(i_cfg_apb4_s_pwrite),
  .i_cfg_apb4_s_psel(i_cfg_apb4_s_psel),
  .i_cfg_apb4_s_penable(i_cfg_apb4_s_penable),
  .i_cfg_apb4_s_pstrb(i_cfg_apb4_s_pstrb),
  .i_cfg_apb4_s_pprot(i_cfg_apb4_s_pprot),
  .o_cfg_apb4_s_pready(o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata(o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr(o_cfg_apb4_s_pslverr),
  .o_pintreq(o_pintreq),
  .o_pintbus(unconnected_pintbus),
  .test_mode(test_mode),
  .i_scan_en(scan_en),
  .i_ret_0(ret[0]),
  .i_pde_0(pde[0]),
  .i_se_0(scan_en),
  .o_prn_0(prn[0]),
  .i_ret_1(ret[1]),
  .i_pde_1(pde[1]),
  .i_se_1(scan_en),
  .o_prn_1(prn[1]),
  .i_ret_2(ret[2]),
  .i_pde_2(pde[2]),
  .i_se_2(scan_en),
  .o_prn_2(prn[2]),
  .i_ret_3(ret[3]),
  .i_pde_3(pde[3]),
  .i_se_3(scan_en),
  .o_prn_3(prn[3]),
  .o_dec_0_axi_m_awaddr(o_dec_0_axi_m_subip_awaddr),
  .o_dec_0_axi_m_awid(o_dec_0_axi_m_subip_awid),
  .o_dec_0_axi_m_awlen(o_dec_0_axi_m_subip_awlen),
  .o_dec_0_axi_m_awsize(o_dec_0_axi_m_subip_awsize),
  .o_dec_0_axi_m_awburst(o_dec_0_axi_m_subip_awburst),
  .o_dec_0_axi_m_awcache(o_dec_0_axi_m_subip_awcache),
  .o_dec_0_axi_m_awprot(o_dec_0_axi_m_subip_awprot),
  .o_dec_0_axi_m_awlock(o_dec_0_axi_m_subip_awlock),
  .o_dec_0_axi_m_awqos(o_dec_0_axi_m_subip_awqos),
  .o_dec_0_axi_m_awregion(o_dec_0_axi_m_subip_awregion),
  .o_dec_0_axi_m_awuser(o_dec_0_axi_m_subip_awuser),
  .o_dec_0_axi_m_awvalid(o_dec_0_axi_m_subip_awvalid),
  .o_dec_0_axi_m_wdata(o_dec_0_axi_m_subip_wdata),
  .o_dec_0_axi_m_wstrb(o_dec_0_axi_m_subip_wstrb),
  .o_dec_0_axi_m_wlast(o_dec_0_axi_m_subip_wlast),
  .o_dec_0_axi_m_wuser(o_dec_0_axi_m_subip_wuser),
  .o_dec_0_axi_m_wvalid(o_dec_0_axi_m_subip_wvalid),
  .o_dec_0_axi_m_bready(o_dec_0_axi_m_subip_bready),
  .o_dec_0_axi_m_araddr(o_dec_0_axi_m_subip_araddr),
  .o_dec_0_axi_m_arid(o_dec_0_axi_m_subip_arid),
  .o_dec_0_axi_m_arlen(o_dec_0_axi_m_subip_arlen),
  .o_dec_0_axi_m_arsize(o_dec_0_axi_m_subip_arsize),
  .o_dec_0_axi_m_arburst(o_dec_0_axi_m_subip_arburst),
  .o_dec_0_axi_m_arcache(o_dec_0_axi_m_subip_arcache),
  .o_dec_0_axi_m_arprot(o_dec_0_axi_m_subip_arprot),
  .o_dec_0_axi_m_arqos(o_dec_0_axi_m_subip_arqos),
  .o_dec_0_axi_m_arregion(o_dec_0_axi_m_subip_arregion),
  .o_dec_0_axi_m_aruser(o_dec_0_axi_m_subip_aruser),
  .o_dec_0_axi_m_arlock(o_dec_0_axi_m_subip_arlock),
  .o_dec_0_axi_m_arvalid(o_dec_0_axi_m_subip_arvalid),
  .o_dec_0_axi_m_rready(o_dec_0_axi_m_subip_rready),
  .i_dec_0_axi_m_awready(i_dec_0_axi_m_subip_awready),
  .i_dec_0_axi_m_wready(i_dec_0_axi_m_subip_wready),
  .i_dec_0_axi_m_bvalid(i_dec_0_axi_m_subip_bvalid),
  .i_dec_0_axi_m_bid(i_dec_0_axi_m_subip_bid),
  .i_dec_0_axi_m_buser(i_dec_0_axi_m_subip_buser),
  .i_dec_0_axi_m_bresp(i_dec_0_axi_m_subip_bresp),
  .i_dec_0_axi_m_arready(i_dec_0_axi_m_subip_arready),
  .i_dec_0_axi_m_rvalid(i_dec_0_axi_m_subip_rvalid),
  .i_dec_0_axi_m_rlast(i_dec_0_axi_m_subip_rlast),
  .i_dec_0_axi_m_rid(i_dec_0_axi_m_subip_rid),
  .i_dec_0_axi_m_rdata(i_dec_0_axi_m_subip_rdata),
  .i_dec_0_axi_m_ruser(i_dec_0_axi_m_subip_ruser),
  .i_dec_0_axi_m_rresp(i_dec_0_axi_m_subip_rresp),
  .o_dec_1_axi_m_awaddr(o_dec_1_axi_m_subip_awaddr),
  .o_dec_1_axi_m_awid(o_dec_1_axi_m_subip_awid),
  .o_dec_1_axi_m_awlen(o_dec_1_axi_m_subip_awlen),
  .o_dec_1_axi_m_awsize(o_dec_1_axi_m_subip_awsize),
  .o_dec_1_axi_m_awburst(o_dec_1_axi_m_subip_awburst),
  .o_dec_1_axi_m_awcache(o_dec_1_axi_m_subip_awcache),
  .o_dec_1_axi_m_awprot(o_dec_1_axi_m_subip_awprot),
  .o_dec_1_axi_m_awlock(o_dec_1_axi_m_subip_awlock),
  .o_dec_1_axi_m_awqos(o_dec_1_axi_m_subip_awqos),
  .o_dec_1_axi_m_awregion(o_dec_1_axi_m_subip_awregion),
  .o_dec_1_axi_m_awuser(o_dec_1_axi_m_subip_awuser),
  .o_dec_1_axi_m_awvalid(o_dec_1_axi_m_subip_awvalid),
  .o_dec_1_axi_m_wdata(o_dec_1_axi_m_subip_wdata),
  .o_dec_1_axi_m_wstrb(o_dec_1_axi_m_subip_wstrb),
  .o_dec_1_axi_m_wlast(o_dec_1_axi_m_subip_wlast),
  .o_dec_1_axi_m_wuser(o_dec_1_axi_m_subip_wuser),
  .o_dec_1_axi_m_wvalid(o_dec_1_axi_m_subip_wvalid),
  .o_dec_1_axi_m_bready(o_dec_1_axi_m_subip_bready),
  .o_dec_1_axi_m_araddr(o_dec_1_axi_m_subip_araddr),
  .o_dec_1_axi_m_arid(o_dec_1_axi_m_subip_arid),
  .o_dec_1_axi_m_arlen(o_dec_1_axi_m_subip_arlen),
  .o_dec_1_axi_m_arsize(o_dec_1_axi_m_subip_arsize),
  .o_dec_1_axi_m_arburst(o_dec_1_axi_m_subip_arburst),
  .o_dec_1_axi_m_arcache(o_dec_1_axi_m_subip_arcache),
  .o_dec_1_axi_m_arprot(o_dec_1_axi_m_subip_arprot),
  .o_dec_1_axi_m_arqos(o_dec_1_axi_m_subip_arqos),
  .o_dec_1_axi_m_arregion(o_dec_1_axi_m_subip_arregion),
  .o_dec_1_axi_m_aruser(o_dec_1_axi_m_subip_aruser),
  .o_dec_1_axi_m_arlock(o_dec_1_axi_m_subip_arlock),
  .o_dec_1_axi_m_arvalid(o_dec_1_axi_m_subip_arvalid),
  .o_dec_1_axi_m_rready(o_dec_1_axi_m_subip_rready),
  .i_dec_1_axi_m_awready(i_dec_1_axi_m_subip_awready),
  .i_dec_1_axi_m_wready(i_dec_1_axi_m_subip_wready),
  .i_dec_1_axi_m_bvalid(i_dec_1_axi_m_subip_bvalid),
  .i_dec_1_axi_m_bid(i_dec_1_axi_m_subip_bid),
  .i_dec_1_axi_m_buser(i_dec_1_axi_m_subip_buser),
  .i_dec_1_axi_m_bresp(i_dec_1_axi_m_subip_bresp),
  .i_dec_1_axi_m_arready(i_dec_1_axi_m_subip_arready),
  .i_dec_1_axi_m_rvalid(i_dec_1_axi_m_subip_rvalid),
  .i_dec_1_axi_m_rlast(i_dec_1_axi_m_subip_rlast),
  .i_dec_1_axi_m_rid(i_dec_1_axi_m_subip_rid),
  .i_dec_1_axi_m_rdata(i_dec_1_axi_m_subip_rdata),
  .i_dec_1_axi_m_ruser(i_dec_1_axi_m_subip_ruser),
  .i_dec_1_axi_m_rresp(i_dec_1_axi_m_subip_rresp),
  .o_dec_2_axi_m_awaddr(o_dec_2_axi_m_subip_awaddr),
  .o_dec_2_axi_m_awid(o_dec_2_axi_m_subip_awid),
  .o_dec_2_axi_m_awlen(o_dec_2_axi_m_subip_awlen),
  .o_dec_2_axi_m_awsize(o_dec_2_axi_m_subip_awsize),
  .o_dec_2_axi_m_awburst(o_dec_2_axi_m_subip_awburst),
  .o_dec_2_axi_m_awcache(o_dec_2_axi_m_subip_awcache),
  .o_dec_2_axi_m_awprot(o_dec_2_axi_m_subip_awprot),
  .o_dec_2_axi_m_awlock(o_dec_2_axi_m_subip_awlock),
  .o_dec_2_axi_m_awqos(o_dec_2_axi_m_subip_awqos),
  .o_dec_2_axi_m_awregion(o_dec_2_axi_m_subip_awregion),
  .o_dec_2_axi_m_awuser(o_dec_2_axi_m_subip_awuser),
  .o_dec_2_axi_m_awvalid(o_dec_2_axi_m_subip_awvalid),
  .o_dec_2_axi_m_wdata(o_dec_2_axi_m_subip_wdata),
  .o_dec_2_axi_m_wstrb(o_dec_2_axi_m_subip_wstrb),
  .o_dec_2_axi_m_wlast(o_dec_2_axi_m_subip_wlast),
  .o_dec_2_axi_m_wuser(o_dec_2_axi_m_subip_wuser),
  .o_dec_2_axi_m_wvalid(o_dec_2_axi_m_subip_wvalid),
  .o_dec_2_axi_m_bready(o_dec_2_axi_m_subip_bready),
  .o_dec_2_axi_m_araddr(o_dec_2_axi_m_subip_araddr),
  .o_dec_2_axi_m_arid(o_dec_2_axi_m_subip_arid),
  .o_dec_2_axi_m_arlen(o_dec_2_axi_m_subip_arlen),
  .o_dec_2_axi_m_arsize(o_dec_2_axi_m_subip_arsize),
  .o_dec_2_axi_m_arburst(o_dec_2_axi_m_subip_arburst),
  .o_dec_2_axi_m_arcache(o_dec_2_axi_m_subip_arcache),
  .o_dec_2_axi_m_arprot(o_dec_2_axi_m_subip_arprot),
  .o_dec_2_axi_m_arqos(o_dec_2_axi_m_subip_arqos),
  .o_dec_2_axi_m_arregion(o_dec_2_axi_m_subip_arregion),
  .o_dec_2_axi_m_aruser(o_dec_2_axi_m_subip_aruser),
  .o_dec_2_axi_m_arlock(o_dec_2_axi_m_subip_arlock),
  .o_dec_2_axi_m_arvalid(o_dec_2_axi_m_subip_arvalid),
  .o_dec_2_axi_m_rready(o_dec_2_axi_m_subip_rready),
  .i_dec_2_axi_m_awready(i_dec_2_axi_m_subip_awready),
  .i_dec_2_axi_m_wready(i_dec_2_axi_m_subip_wready),
  .i_dec_2_axi_m_bvalid(i_dec_2_axi_m_subip_bvalid),
  .i_dec_2_axi_m_bid(i_dec_2_axi_m_subip_bid),
  .i_dec_2_axi_m_buser(i_dec_2_axi_m_subip_buser),
  .i_dec_2_axi_m_bresp(i_dec_2_axi_m_subip_bresp),
  .i_dec_2_axi_m_arready(i_dec_2_axi_m_subip_arready),
  .i_dec_2_axi_m_rvalid(i_dec_2_axi_m_subip_rvalid),
  .i_dec_2_axi_m_rlast(i_dec_2_axi_m_subip_rlast),
  .i_dec_2_axi_m_rid(i_dec_2_axi_m_subip_rid),
  .i_dec_2_axi_m_rdata(i_dec_2_axi_m_subip_rdata),
  .i_dec_2_axi_m_ruser(i_dec_2_axi_m_subip_ruser),
  .i_dec_2_axi_m_rresp(i_dec_2_axi_m_subip_rresp),
  .o_mcu_axi_m_awaddr(o_mcu_axi_m_subip_awaddr),
  .o_mcu_axi_m_awid(o_mcu_axi_m_subip_awid),
  .o_mcu_axi_m_awlen(o_mcu_axi_m_subip_awlen),
  .o_mcu_axi_m_awsize(o_mcu_axi_m_subip_awsize),
  .o_mcu_axi_m_awburst(o_mcu_axi_m_subip_awburst),
  .o_mcu_axi_m_awcache(o_mcu_axi_m_subip_awcache),
  .o_mcu_axi_m_awprot(o_mcu_axi_m_subip_awprot),
  .o_mcu_axi_m_awlock(o_mcu_axi_m_subip_awlock),
  .o_mcu_axi_m_awqos(o_mcu_axi_m_subip_awqos),
  .o_mcu_axi_m_awregion(o_mcu_axi_m_subip_awregion),
  .o_mcu_axi_m_awuser(o_mcu_axi_m_subip_awuser),
  .o_mcu_axi_m_awvalid(o_mcu_axi_m_subip_awvalid),
  .o_mcu_axi_m_wdata(o_mcu_axi_m_subip_wdata),
  .o_mcu_axi_m_wstrb(o_mcu_axi_m_subip_wstrb),
  .o_mcu_axi_m_wlast(o_mcu_axi_m_subip_wlast),
  .o_mcu_axi_m_wuser(o_mcu_axi_m_subip_wuser),
  .o_mcu_axi_m_wvalid(o_mcu_axi_m_subip_wvalid),
  .o_mcu_axi_m_bready(o_mcu_axi_m_subip_bready),
  .o_mcu_axi_m_araddr(o_mcu_axi_m_subip_araddr),
  .o_mcu_axi_m_arid(o_mcu_axi_m_subip_arid),
  .o_mcu_axi_m_arlen(o_mcu_axi_m_subip_arlen),
  .o_mcu_axi_m_arsize(o_mcu_axi_m_subip_arsize),
  .o_mcu_axi_m_arburst(o_mcu_axi_m_subip_arburst),
  .o_mcu_axi_m_arcache(o_mcu_axi_m_subip_arcache),
  .o_mcu_axi_m_arprot(o_mcu_axi_m_subip_arprot),
  .o_mcu_axi_m_arqos(o_mcu_axi_m_subip_arqos),
  .o_mcu_axi_m_arregion(o_mcu_axi_m_subip_arregion),
  .o_mcu_axi_m_aruser(o_mcu_axi_m_subip_aruser),
  .o_mcu_axi_m_arlock(o_mcu_axi_m_subip_arlock),
  .o_mcu_axi_m_arvalid(o_mcu_axi_m_subip_arvalid),
  .o_mcu_axi_m_rready(o_mcu_axi_m_subip_rready),
  .i_mcu_axi_m_awready(i_mcu_axi_m_subip_awready),
  .i_mcu_axi_m_wready(i_mcu_axi_m_subip_wready),
  .i_mcu_axi_m_bvalid(i_mcu_axi_m_subip_bvalid),
  .i_mcu_axi_m_bid(i_mcu_axi_m_subip_bid),
  .i_mcu_axi_m_buser(i_mcu_axi_m_subip_buser),
  .i_mcu_axi_m_bresp(i_mcu_axi_m_subip_bresp),
  .i_mcu_axi_m_arready(i_mcu_axi_m_subip_arready),
  .i_mcu_axi_m_rvalid(i_mcu_axi_m_subip_rvalid),
  .i_mcu_axi_m_rlast(i_mcu_axi_m_subip_rlast),
  .i_mcu_axi_m_rid(i_mcu_axi_m_subip_rid),
  .i_mcu_axi_m_rdata(i_mcu_axi_m_subip_rdata),
  .i_mcu_axi_m_ruser(i_mcu_axi_m_subip_ruser),
  .i_mcu_axi_m_rresp(i_mcu_axi_m_subip_rresp)
);

assign o_noc_rst_n = dcd_rst_n;
assign o_noc_mcu_rst_n = dcd_mcu_rst_n;
assign o_dcd_obs = 16'b0;

//-------------------------------
// Partition controller Instance
//-------------------------------
logic                          int_shutdown_ack ;
  pctl #(
    .N_FAST_CLKS (2),
    .N_RESETS (2),
    .N_MEM_PG (4),
    .N_FENCES (2),
    .N_THROTTLE_PINS (0),
    .CLKRST_MATRIX (4'b1001),
    .PLL_CLK_IS_I_CLK (1'b0),
    .NOC_RST_IDX (1'b0),
    .SYNC_CLK_IDX (1'b0),
    .AUTO_RESET_REMOVE (1'b0),
    .paddr_t (chip_syscfg_addr_t),
    .pdata_t (chip_apb_syscfg_data_t),
    .pstrb_t (chip_apb_syscfg_strb_t)
  ) u_pctl (
    .i_clk(i_ref_clk),
    .i_ao_rst_n(i_ao_rst_n),
    .i_global_rst_n(i_global_rst_n),
    .i_test_mode(test_mode),
    .i_pll_clk({i_clk, i_mcu_clk}),
    .o_partition_clk({dcd_clk, dcd_mcu_clk}),
    .o_partition_rst_n({dcd_rst_n, dcd_mcu_rst_n}),
    .o_ao_rst_sync_n(o_ao_rst_sync_n),
    .o_noc_async_idle_req({o_noc_async_idle_req, o_noc_mcu_async_idle_req}),
    .i_noc_async_idle_ack({i_noc_async_idle_ack, i_noc_mcu_async_idle_ack}),
    .i_noc_async_idle_val({i_noc_async_idle_val, i_noc_mcu_async_idle_val}),
    .o_noc_clken({o_noc_clk_en, o_noc_mcu_clk_en}),
    .o_noc_rst_n(), // ASO-UNUSED_OUTPUT: NoC resets are driven by the o_partition_rst_n
    .o_int_shutdown_req(int_shutdown_req),
    .i_int_shutdown_ack(1'b1),
    .o_ret(ret),
    .o_pde(pde),
    .i_prn(prn),
    .i_global_sync_async(1'b0),
    .o_global_sync(global_sync),
    .i_throttle(1'b0),
    .i_cfg_apb4_s_paddr(i_syscfg_apb4_s_paddr),
    .i_cfg_apb4_s_pwdata(i_syscfg_apb4_s_pwdata),
    .i_cfg_apb4_s_pwrite(i_syscfg_apb4_s_pwrite),
    .i_cfg_apb4_s_psel(i_syscfg_apb4_s_psel),
    .i_cfg_apb4_s_penable(i_syscfg_apb4_s_penable),
    .i_cfg_apb4_s_pstrb(i_syscfg_apb4_s_pstrb),
    .i_cfg_apb4_s_pprot(i_syscfg_apb4_s_pprot),
    .o_cfg_apb4_s_pready(o_syscfg_apb4_s_pready),
    .o_cfg_apb4_s_prdata(o_syscfg_apb4_s_prdata),
    .o_cfg_apb4_s_pslverr(o_syscfg_apb4_s_pslverr),
    .o_ao_csr_apb_req(), // ASO-UNUSED_OUTPUT: No specifc AO CSR for dcd
    .i_ao_csr_apb_rsp(pctl_ao_csr_reg_pkg::apb_d2h_t'('0))
  );

endmodule
