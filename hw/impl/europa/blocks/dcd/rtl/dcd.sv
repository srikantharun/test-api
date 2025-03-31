//  (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Leonidas Katselas <leonidas.katselas@axelera.ai>

/// Dual core AVC HEVC JPEG DECODER with RISC-V IP
///
module dcd
  import chip_pkg::*;
  import axi_pkg::*;
  import dcd_pkg::*;
 (
  /// Clock, positive edge triggered
  input  wire                             i_clk,
  input  wire                             i_mcu_clk,
  input  wire                             i_jtag_clk,
  /// Asynchronous reset, active low
  input  wire                             i_rst_n,
  input  wire                             i_mcu_rst_n,
  input  wire                             i_jtag_rst_n,
  /// AXI master 0 write address signals
  output chip_axi_addr_t                  o_dec_0_axi_m_awaddr,
  output dcd_dec_0_init_mt_axi_id_t       o_dec_0_axi_m_awid,
  output axi_len_t                        o_dec_0_axi_m_awlen,
  output axi_size_t                       o_dec_0_axi_m_awsize,
  output axi_burst_t                      o_dec_0_axi_m_awburst,
  output axi_cache_t                      o_dec_0_axi_m_awcache,
  output axi_prot_t                       o_dec_0_axi_m_awprot,
  output logic                            o_dec_0_axi_m_awlock,
  output axi_qos_t                        o_dec_0_axi_m_awqos,
  output axi_region_t                     o_dec_0_axi_m_awregion,
  output chip_axi_mt_awuser_t             o_dec_0_axi_m_awuser,
  output logic                            o_dec_0_axi_m_awvalid,
  input  logic                            i_dec_0_axi_m_awready,
  /// AXI master 0 write data signals
  output dcd_dec_0_init_mt_axi_data_t     o_dec_0_axi_m_wdata,
  output dcd_dec_0_init_mt_axi_strb_t     o_dec_0_axi_m_wstrb,
  output logic                            o_dec_0_axi_m_wlast,
  output chip_axi_mt_wuser_t              o_dec_0_axi_m_wuser,
  output logic                            o_dec_0_axi_m_wvalid,
  input  logic                            i_dec_0_axi_m_wready,
  /// AXI master 0 write response signals
  input  logic                            i_dec_0_axi_m_bvalid,
  input  dcd_dec_0_init_mt_axi_id_t       i_dec_0_axi_m_bid,
  input  chip_axi_mt_buser_t              i_dec_0_axi_m_buser,
  input  axi_resp_t                       i_dec_0_axi_m_bresp,
  output logic                            o_dec_0_axi_m_bready,
  /// AXI master 0 read address signals
  output chip_axi_addr_t                  o_dec_0_axi_m_araddr,
  output dcd_dec_0_init_mt_axi_id_t       o_dec_0_axi_m_arid,
  output axi_len_t                        o_dec_0_axi_m_arlen,
  output axi_size_t                       o_dec_0_axi_m_arsize,
  output axi_burst_t                      o_dec_0_axi_m_arburst,
  output axi_cache_t                      o_dec_0_axi_m_arcache,
  output axi_prot_t                       o_dec_0_axi_m_arprot,
  output axi_qos_t                        o_dec_0_axi_m_arqos,
  output axi_region_t                     o_dec_0_axi_m_arregion,
  output chip_axi_mt_aruser_t             o_dec_0_axi_m_aruser,
  output logic                            o_dec_0_axi_m_arlock,
  output logic                            o_dec_0_axi_m_arvalid,
  input  logic                            i_dec_0_axi_m_arready,
  /// AXI master 0 read data signals
  input  logic                            i_dec_0_axi_m_rvalid,
  input  logic                            i_dec_0_axi_m_rlast,
  input  dcd_dec_0_init_mt_axi_id_t       i_dec_0_axi_m_rid,
  input  dcd_dec_0_init_mt_axi_data_t     i_dec_0_axi_m_rdata,
  input  chip_axi_mt_ruser_t              i_dec_0_axi_m_ruser,
  input  axi_resp_t                       i_dec_0_axi_m_rresp,
  output logic                            o_dec_0_axi_m_rready,
  /// AXI master 1 write address signals
  output chip_axi_addr_t                  o_dec_1_axi_m_awaddr,
  output dcd_dec_1_init_mt_axi_id_t       o_dec_1_axi_m_awid,
  output axi_len_t                        o_dec_1_axi_m_awlen,
  output axi_size_t                       o_dec_1_axi_m_awsize,
  output axi_burst_t                      o_dec_1_axi_m_awburst,
  output axi_cache_t                      o_dec_1_axi_m_awcache,
  output axi_prot_t                       o_dec_1_axi_m_awprot,
  output logic                            o_dec_1_axi_m_awlock,
  output axi_qos_t                        o_dec_1_axi_m_awqos,
  output axi_region_t                     o_dec_1_axi_m_awregion,
  output chip_axi_mt_awuser_t             o_dec_1_axi_m_awuser,
  output logic                            o_dec_1_axi_m_awvalid,
  input  logic                            i_dec_1_axi_m_awready,
  /// AXI master 1 write data signals
  output dcd_dec_1_init_mt_axi_data_t     o_dec_1_axi_m_wdata,
  output dcd_dec_1_init_mt_axi_strb_t     o_dec_1_axi_m_wstrb,
  output logic                            o_dec_1_axi_m_wlast,
  output chip_axi_mt_wuser_t              o_dec_1_axi_m_wuser,
  output logic                            o_dec_1_axi_m_wvalid,
  input  logic                            i_dec_1_axi_m_wready,
  /// AXI master 1 write response signals
  input  logic                            i_dec_1_axi_m_bvalid,
  input  dcd_dec_1_init_mt_axi_id_t       i_dec_1_axi_m_bid,
  input  chip_axi_mt_buser_t              i_dec_1_axi_m_buser,
  input  axi_resp_t                       i_dec_1_axi_m_bresp,
  output logic                            o_dec_1_axi_m_bready,
  /// AXI master 1 read address signals
  output chip_axi_addr_t                  o_dec_1_axi_m_araddr,
  output dcd_dec_1_init_mt_axi_id_t       o_dec_1_axi_m_arid,
  output axi_len_t                        o_dec_1_axi_m_arlen,
  output axi_size_t                       o_dec_1_axi_m_arsize,
  output axi_burst_t                      o_dec_1_axi_m_arburst,
  output axi_cache_t                      o_dec_1_axi_m_arcache,
  output axi_prot_t                       o_dec_1_axi_m_arprot,
  output axi_qos_t                        o_dec_1_axi_m_arqos,
  output axi_region_t                     o_dec_1_axi_m_arregion,
  output chip_axi_mt_aruser_t             o_dec_1_axi_m_aruser,
  output logic                            o_dec_1_axi_m_arlock,
  output logic                            o_dec_1_axi_m_arvalid,
  input  logic                            i_dec_1_axi_m_arready,
  /// AXI master 1 read data signals
  input  logic                            i_dec_1_axi_m_rvalid,
  input  logic                            i_dec_1_axi_m_rlast,
  input  dcd_dec_1_init_mt_axi_id_t       i_dec_1_axi_m_rid,
  input  dcd_dec_1_init_mt_axi_data_t     i_dec_1_axi_m_rdata,
  input  chip_axi_mt_ruser_t              i_dec_1_axi_m_ruser,
  input  axi_resp_t                       i_dec_1_axi_m_rresp,
  output logic                            o_dec_1_axi_m_rready,
  /// AXI master 2 write address signals
  output chip_axi_addr_t                  o_dec_2_axi_m_awaddr,
  output dcd_dec_2_init_mt_axi_id_t       o_dec_2_axi_m_awid,
  output axi_len_t                        o_dec_2_axi_m_awlen,
  output axi_size_t                       o_dec_2_axi_m_awsize,
  output axi_burst_t                      o_dec_2_axi_m_awburst,
  output axi_cache_t                      o_dec_2_axi_m_awcache,
  output axi_prot_t                       o_dec_2_axi_m_awprot,
  output logic                            o_dec_2_axi_m_awlock,
  output axi_qos_t                        o_dec_2_axi_m_awqos,
  output axi_region_t                     o_dec_2_axi_m_awregion,
  output chip_axi_mt_awuser_t             o_dec_2_axi_m_awuser,
  output logic                            o_dec_2_axi_m_awvalid,
  input  logic                            i_dec_2_axi_m_awready,
  /// AXI master 2 write data signals
  output dcd_dec_2_init_mt_axi_data_t     o_dec_2_axi_m_wdata,
  output dcd_dec_2_init_mt_axi_strb_t     o_dec_2_axi_m_wstrb,
  output logic                            o_dec_2_axi_m_wlast,
  output chip_axi_mt_wuser_t              o_dec_2_axi_m_wuser,
  output logic                            o_dec_2_axi_m_wvalid,
  input  logic                            i_dec_2_axi_m_wready,
  /// AXI master 2 write response signals
  input  logic                            i_dec_2_axi_m_bvalid,
  input  dcd_dec_2_init_mt_axi_id_t       i_dec_2_axi_m_bid,
  input  chip_axi_mt_buser_t              i_dec_2_axi_m_buser,
  input  axi_resp_t                       i_dec_2_axi_m_bresp,
  output logic                            o_dec_2_axi_m_bready,
  /// AXI master 2 read address signals
  output chip_axi_addr_t                  o_dec_2_axi_m_araddr,
  output dcd_dec_2_init_mt_axi_id_t       o_dec_2_axi_m_arid,
  output axi_len_t                        o_dec_2_axi_m_arlen,
  output axi_size_t                       o_dec_2_axi_m_arsize,
  output axi_burst_t                      o_dec_2_axi_m_arburst,
  output axi_cache_t                      o_dec_2_axi_m_arcache,
  output axi_prot_t                       o_dec_2_axi_m_arprot,
  output axi_qos_t                        o_dec_2_axi_m_arqos,
  output axi_region_t                     o_dec_2_axi_m_arregion,
  output chip_axi_mt_aruser_t             o_dec_2_axi_m_aruser,
  output logic                            o_dec_2_axi_m_arlock,
  output logic                            o_dec_2_axi_m_arvalid,
  input  logic                            i_dec_2_axi_m_arready,
  /// AXI master 2 read data signals
  input  logic                            i_dec_2_axi_m_rvalid,
  input  logic                            i_dec_2_axi_m_rlast,
  input  dcd_dec_2_init_mt_axi_id_t       i_dec_2_axi_m_rid,
  input  dcd_dec_2_init_mt_axi_data_t     i_dec_2_axi_m_rdata,
  input  chip_axi_mt_ruser_t              i_dec_2_axi_m_ruser,
  input  axi_resp_t                       i_dec_2_axi_m_rresp,
  output logic                            o_dec_2_axi_m_rready,
  /// RISC-V interrupt signals
  output logic                            o_mcu_int_next,
  input  logic                            i_mcu_ack_next,
  input  logic                            i_mcu_int_prev,
  output logic                            o_mcu_ack_prev,
  /// RISC-V JTAG signals
  input  logic                            i_jtag_ms,
  input  logic                            i_jtag_di,
  output logic                            o_jtag_do,
  /// RISC-V AXI master write address signals
  output chip_axi_addr_t                  o_mcu_axi_m_awaddr,
  output dcd_mcu_init_lt_axi_id_t         o_mcu_axi_m_awid,
  output axi_len_t                        o_mcu_axi_m_awlen,
  output axi_size_t                       o_mcu_axi_m_awsize,
  output axi_burst_t                      o_mcu_axi_m_awburst,
  output axi_cache_t                      o_mcu_axi_m_awcache,
  output axi_prot_t                       o_mcu_axi_m_awprot,
  output logic                            o_mcu_axi_m_awlock,
  output axi_qos_t                        o_mcu_axi_m_awqos,
  output axi_region_t                     o_mcu_axi_m_awregion,
  output chip_axi_mt_awuser_t             o_mcu_axi_m_awuser,
  output logic                            o_mcu_axi_m_awvalid,
  input  logic                            i_mcu_axi_m_awready,
  /// RISC-V AXI master write data signals
  output dcd_mcu_init_lt_axi_data_t       o_mcu_axi_m_wdata,
  output dcd_mcu_init_lt_axi_strb_t       o_mcu_axi_m_wstrb,
  output logic                            o_mcu_axi_m_wlast,
  output chip_axi_mt_wuser_t              o_mcu_axi_m_wuser,
  output logic                            o_mcu_axi_m_wvalid,
  input  logic                            i_mcu_axi_m_wready,
  /// RISC-V AXI master write response signals
  input  logic                            i_mcu_axi_m_bvalid,
  input  dcd_mcu_init_lt_axi_id_t         i_mcu_axi_m_bid,
  input  chip_axi_mt_buser_t              i_mcu_axi_m_buser,
  input  axi_resp_t                       i_mcu_axi_m_bresp,
  output logic                            o_mcu_axi_m_bready,
  /// RISC-V AXI master read address signals
  output chip_axi_addr_t                  o_mcu_axi_m_araddr,
  output dcd_mcu_init_lt_axi_id_t         o_mcu_axi_m_arid,
  output axi_len_t                        o_mcu_axi_m_arlen,
  output axi_size_t                       o_mcu_axi_m_arsize,
  output axi_burst_t                      o_mcu_axi_m_arburst,
  output axi_cache_t                      o_mcu_axi_m_arcache,
  output axi_prot_t                       o_mcu_axi_m_arprot,
  output axi_qos_t                        o_mcu_axi_m_arqos,
  output axi_region_t                     o_mcu_axi_m_arregion,
  output chip_axi_mt_aruser_t             o_mcu_axi_m_aruser,
  output logic                            o_mcu_axi_m_arlock,
  output logic                            o_mcu_axi_m_arvalid,
  input  logic                            i_mcu_axi_m_arready,
  /// RISC-V AXI master read data signals
  input  logic                            i_mcu_axi_m_rvalid,
  input  logic                            i_mcu_axi_m_rlast,
  input  dcd_mcu_init_lt_axi_id_t         i_mcu_axi_m_rid,
  input  dcd_mcu_init_lt_axi_data_t       i_mcu_axi_m_rdata,
  input  chip_axi_mt_ruser_t              i_mcu_axi_m_ruser,
  input  axi_resp_t                       i_mcu_axi_m_rresp,
  output logic                            o_mcu_axi_m_rready,
  /// APB slave signals,
  input  dcd_targ_cfg_apb_addr_t          i_cfg_apb4_s_paddr,
  input  dcd_targ_cfg_apb_data_t          i_cfg_apb4_s_pwdata,
  input  logic                            i_cfg_apb4_s_pwrite,
  input  logic                            i_cfg_apb4_s_psel,
  input  logic                            i_cfg_apb4_s_penable,
  input  dcd_targ_cfg_apb_strb_t          i_cfg_apb4_s_pstrb,
  input  axi_prot_t                       i_cfg_apb4_s_pprot,
  output logic                            o_cfg_apb4_s_pready,
  output dcd_targ_cfg_apb_data_t          o_cfg_apb4_s_prdata,
  output logic                            o_cfg_apb4_s_pslverr,
  /// decoder global signals
  output logic                            o_pintreq,
  output logic [                    31:0] o_pintbus,
  input  logic                            test_mode,
  input  logic                            i_scan_en,

  // RAM Configuration pins
  input logic       i_ret_0,
  input logic       i_pde_0,
  input logic       i_se_0,
  output logic      o_prn_0,

  input logic       i_ret_1,
  input logic       i_pde_1,
  input logic       i_se_1,
  output logic      o_prn_1,

  input logic       i_ret_2,
  input logic       i_pde_2,
  input logic       i_se_2,
  output logic      o_prn_2,

  input logic       i_ret_3,
  input logic       i_pde_3,
  input logic       i_se_3,
  output logic      o_prn_3
);

axe_tcl_sram_pkg::impl_inp_t [3:0] i_impl;
axe_tcl_sram_pkg::impl_oup_t [3:0] o_impl;

  // Structs mappigs
  always_comb begin
    // Inputs
    i_impl[0].ret  = i_ret_0;
    i_impl[0].pde  = i_pde_0;
    i_impl[0].se   = i_se_0;
    i_impl[1].ret  = i_ret_1;
    i_impl[1].pde  = i_pde_1;
    i_impl[1].se   = i_se_1;
    i_impl[2].ret  = i_ret_2;
    i_impl[2].pde  = i_pde_2;
    i_impl[2].se   = i_se_2;
    i_impl[3].ret  = i_ret_3;
    i_impl[3].pde  = i_pde_3;
    i_impl[3].se   = i_se_3;

    // Outputs
    o_prn_0 = o_impl[0].prn;
    o_prn_1 = o_impl[1].prn;
    o_prn_2 = o_impl[2].prn;
    o_prn_3 = o_impl[3].prn;

    // TODO: (@emre.kirkaya) remove this assignment once imp_inp_t struct updated.
    for(int idx = 0; idx < 4; idx++) begin
      i_impl[idx].mcs   = '0;
      i_impl[idx].mcsw  = '0;
      i_impl[idx].adme  = '0;
    end
  end

logic unconnected_dec_0_axi_m_buser;
logic unconnected_dec_0_axi_m_ruser;
logic unconnected_dec_1_axi_m_buser;
logic unconnected_dec_1_axi_m_ruser;
logic unconnected_dec_2_axi_m_buser;
logic unconnected_dec_2_axi_m_ruser;
logic unconnected_mcu_axi_m_buser;
logic unconnected_mcu_axi_m_ruser;

//Unused inputs
assign unconnected_dec_0_axi_m_buser = i_dec_0_axi_m_buser;
assign unconnected_dec_0_axi_m_ruser = i_dec_0_axi_m_ruser;
assign unconnected_dec_1_axi_m_buser = i_dec_1_axi_m_buser;
assign unconnected_dec_1_axi_m_ruser = i_dec_1_axi_m_ruser;
assign unconnected_dec_2_axi_m_buser = i_dec_2_axi_m_buser;
assign unconnected_dec_2_axi_m_ruser = i_dec_2_axi_m_ruser;
assign unconnected_mcu_axi_m_buser = i_mcu_axi_m_buser;
assign unconnected_mcu_axi_m_ruser = i_mcu_axi_m_ruser;

//Unused outputs
assign o_dec_0_axi_m_awcache = 1'b0;
assign o_dec_0_axi_m_awlock = 1'b0;
assign o_dec_0_axi_m_awqos = 1'b0;
assign o_dec_0_axi_m_awregion = 1'b0;
assign o_dec_0_axi_m_awuser = 1'b0;
assign o_dec_0_axi_m_wuser = 1'b0;
assign o_dec_0_axi_m_arcache = 1'b0;
assign o_dec_0_axi_m_arqos = 1'b0;
assign o_dec_0_axi_m_arregio = 1'b0;
assign o_dec_0_axi_m_aruser = 1'b0;
assign o_dec_0_axi_m_arlock = 1'b0;
assign o_dec_1_axi_m_awcache = 1'b0;
assign o_dec_1_axi_m_awlock = 1'b0;
assign o_dec_1_axi_m_awqos = 1'b0;
assign o_dec_1_axi_m_awregion = 1'b0;
assign o_dec_1_axi_m_awuser = 1'b0;
assign o_dec_1_axi_m_wuser = 1'b0;
assign o_dec_1_axi_m_arcache = 1'b0;
assign o_dec_1_axi_m_arqos = 1'b0;
assign o_dec_1_axi_m_arregion = 1'b0;
assign o_dec_1_axi_m_aruser = 1'b0;
assign o_dec_1_axi_m_arlock = 1'b0;
assign o_dec_2_axi_m_awcache = 1'b0;
assign o_dec_2_axi_m_awlock = 1'b0;
assign o_dec_2_axi_m_awqos = 1'b0;
assign o_dec_2_axi_m_awregion = 1'b0;
assign o_dec_2_axi_m_awuser = 1'b0;
assign o_dec_2_axi_m_wuser = 1'b0;
assign o_dec_2_axi_m_arcache = 1'b0;
assign o_dec_2_axi_m_arqos = 1'b0;
assign o_dec_2_axi_m_arregion = 1'b0;
assign o_dec_2_axi_m_aruser = 1'b0;
assign o_dec_2_axi_m_arlock = 1'b0;
assign o_mcu_axi_m_awcache = 1'b0;
assign o_mcu_axi_m_awlock = 1'b0;
assign o_mcu_axi_m_awqos = 1'b0;
assign o_mcu_axi_m_awregion = 1'b0;
assign o_mcu_axi_m_awuser = 1'b0;
assign o_mcu_axi_m_wuser = 1'b0;
assign o_mcu_axi_m_arcache = 1'b0;
assign o_mcu_axi_m_arqos = 1'b0;
assign o_mcu_axi_m_arregion = 1'b0;
assign o_mcu_axi_m_aruser = 1'b0;
assign o_mcu_axi_m_arlock = 1'b0;

codec u_codec (
  .i_clk                  (i_clk),
  .i_rst_n                (i_rst_n),
  .o_dec_0_axi_m_awaddr   (o_dec_0_axi_m_awaddr),
  .o_dec_0_axi_m_awid     (o_dec_0_axi_m_awid),
  .o_dec_0_axi_m_awlen    (o_dec_0_axi_m_awlen),
  .o_dec_0_axi_m_awsize   (o_dec_0_axi_m_awsize),
  .o_dec_0_axi_m_awburst  (o_dec_0_axi_m_awburst),
  .o_dec_0_axi_m_awprot   (o_dec_0_axi_m_awprot),
  .o_dec_0_axi_m_awvalid  (o_dec_0_axi_m_awvalid),
  .i_dec_0_axi_m_awready  (i_dec_0_axi_m_awready),
  .o_dec_0_axi_m_wdata    (o_dec_0_axi_m_wdata),
  .o_dec_0_axi_m_wstrb    (o_dec_0_axi_m_wstrb),
  .o_dec_0_axi_m_wlast    (o_dec_0_axi_m_wlast),
  .o_dec_0_axi_m_wvalid   (o_dec_0_axi_m_wvalid),
  .i_dec_0_axi_m_wready   (i_dec_0_axi_m_wready),
  .i_dec_0_axi_m_bvalid   (i_dec_0_axi_m_bvalid),
  .i_dec_0_axi_m_bid      (i_dec_0_axi_m_bid),
  .i_dec_0_axi_m_bresp    (i_dec_0_axi_m_bresp),
  .o_dec_0_axi_m_bready   (o_dec_0_axi_m_bready),
  .o_dec_0_axi_m_araddr   (o_dec_0_axi_m_araddr),
  .o_dec_0_axi_m_arid     (o_dec_0_axi_m_arid),
  .o_dec_0_axi_m_arlen    (o_dec_0_axi_m_arlen),
  .o_dec_0_axi_m_arsize   (o_dec_0_axi_m_arsize),
  .o_dec_0_axi_m_arburst  (o_dec_0_axi_m_arburst),
  .o_dec_0_axi_m_arprot   (o_dec_0_axi_m_arprot),
  .o_dec_0_axi_m_arvalid  (o_dec_0_axi_m_arvalid),
  .i_dec_0_axi_m_arready  (i_dec_0_axi_m_arready),
  .i_dec_0_axi_m_rvalid   (i_dec_0_axi_m_rvalid),
  .i_dec_0_axi_m_rlast    (i_dec_0_axi_m_rlast),
  .i_dec_0_axi_m_rid      (i_dec_0_axi_m_rid),
  .i_dec_0_axi_m_rdata    (i_dec_0_axi_m_rdata),
  .i_dec_0_axi_m_rresp    (i_dec_0_axi_m_rresp),
  .o_dec_0_axi_m_rready   (o_dec_0_axi_m_rready),
  .o_dec_1_axi_m_awaddr   (o_dec_1_axi_m_awaddr),
  .o_dec_1_axi_m_awid     (o_dec_1_axi_m_awid),
  .o_dec_1_axi_m_awlen    (o_dec_1_axi_m_awlen),
  .o_dec_1_axi_m_awsize   (o_dec_1_axi_m_awsize),
  .o_dec_1_axi_m_awburst  (o_dec_1_axi_m_awburst),
  .o_dec_1_axi_m_awprot   (o_dec_1_axi_m_awprot),
  .o_dec_1_axi_m_awvalid  (o_dec_1_axi_m_awvalid),
  .i_dec_1_axi_m_awready  (i_dec_1_axi_m_awready),
  .o_dec_1_axi_m_wdata    (o_dec_1_axi_m_wdata),
  .o_dec_1_axi_m_wstrb    (o_dec_1_axi_m_wstrb),
  .o_dec_1_axi_m_wlast    (o_dec_1_axi_m_wlast),
  .o_dec_1_axi_m_wvalid   (o_dec_1_axi_m_wvalid),
  .i_dec_1_axi_m_wready   (i_dec_1_axi_m_wready),
  .i_dec_1_axi_m_bvalid   (i_dec_1_axi_m_bvalid),
  .i_dec_1_axi_m_bid      (i_dec_1_axi_m_bid),
  .i_dec_1_axi_m_bresp    (i_dec_1_axi_m_bresp),
  .o_dec_1_axi_m_bready   (o_dec_1_axi_m_bready),
  .o_dec_1_axi_m_araddr   (o_dec_1_axi_m_araddr),
  .o_dec_1_axi_m_arid     (o_dec_1_axi_m_arid),
  .o_dec_1_axi_m_arlen    (o_dec_1_axi_m_arlen),
  .o_dec_1_axi_m_arsize   (o_dec_1_axi_m_arsize),
  .o_dec_1_axi_m_arburst  (o_dec_1_axi_m_arburst),
  .o_dec_1_axi_m_arprot   (o_dec_1_axi_m_arprot),
  .o_dec_1_axi_m_arvalid  (o_dec_1_axi_m_arvalid),
  .i_dec_1_axi_m_arready  (i_dec_1_axi_m_arready),
  .i_dec_1_axi_m_rvalid   (i_dec_1_axi_m_rvalid),
  .i_dec_1_axi_m_rlast    (i_dec_1_axi_m_rlast),
  .i_dec_1_axi_m_rid      (i_dec_1_axi_m_rid),
  .i_dec_1_axi_m_rdata    (i_dec_1_axi_m_rdata),
  .i_dec_1_axi_m_rresp    (i_dec_1_axi_m_rresp),
  .o_dec_1_axi_m_rready   (o_dec_1_axi_m_rready),
  .o_dec_2_axi_m_awaddr   (o_dec_2_axi_m_awaddr),
  .o_dec_2_axi_m_awid     (o_dec_2_axi_m_awid),
  .o_dec_2_axi_m_awlen    (o_dec_2_axi_m_awlen),
  .o_dec_2_axi_m_awsize   (o_dec_2_axi_m_awsize),
  .o_dec_2_axi_m_awburst  (o_dec_2_axi_m_awburst),
  .o_dec_2_axi_m_awprot   (o_dec_2_axi_m_awprot),
  .o_dec_2_axi_m_awvalid  (o_dec_2_axi_m_awvalid),
  .i_dec_2_axi_m_awready  (i_dec_2_axi_m_awready),
  .o_dec_2_axi_m_wdata    (o_dec_2_axi_m_wdata),
  .o_dec_2_axi_m_wstrb    (o_dec_2_axi_m_wstrb),
  .o_dec_2_axi_m_wlast    (o_dec_2_axi_m_wlast),
  .o_dec_2_axi_m_wvalid   (o_dec_2_axi_m_wvalid),
  .i_dec_2_axi_m_wready   (i_dec_2_axi_m_wready),
  .i_dec_2_axi_m_bvalid   (i_dec_2_axi_m_bvalid),
  .i_dec_2_axi_m_bid      (i_dec_2_axi_m_bid),
  .i_dec_2_axi_m_bresp    (i_dec_2_axi_m_bresp),
  .o_dec_2_axi_m_bready   (o_dec_2_axi_m_bready),
  .o_dec_2_axi_m_araddr   (o_dec_2_axi_m_araddr),
  .o_dec_2_axi_m_arid     (o_dec_2_axi_m_arid),
  .o_dec_2_axi_m_arlen    (o_dec_2_axi_m_arlen),
  .o_dec_2_axi_m_arsize   (o_dec_2_axi_m_arsize),
  .o_dec_2_axi_m_arburst  (o_dec_2_axi_m_arburst),
  .o_dec_2_axi_m_arprot   (o_dec_2_axi_m_arprot),
  .o_dec_2_axi_m_arvalid  (o_dec_2_axi_m_arvalid),
  .i_dec_2_axi_m_arready  (i_dec_2_axi_m_arready),
  .i_dec_2_axi_m_rvalid   (i_dec_2_axi_m_rvalid),
  .i_dec_2_axi_m_rlast    (i_dec_2_axi_m_rlast),
  .i_dec_2_axi_m_rid      (i_dec_2_axi_m_rid),
  .i_dec_2_axi_m_rdata    (i_dec_2_axi_m_rdata),
  .i_dec_2_axi_m_rresp    (i_dec_2_axi_m_rresp),
  .o_dec_2_axi_m_rready   (o_dec_2_axi_m_rready),
  .i_mclk                 (i_mcu_clk),
  .i_mrst_n               (i_mcu_rst_n),
  .o_mcu_int_next         (o_mcu_int_next),
  .i_mcu_ack_next         (i_mcu_ack_next),
  .i_mcu_int_prev         (i_mcu_int_prev),
  .o_mcu_ack_prev         (o_mcu_ack_prev),
  .i_jtag_clk             (i_jtag_clk),
  .i_jtag_ms              (i_jtag_ms),
  .i_jtag_di              (i_jtag_di),
  .o_jtag_do              (o_jtag_do),
  .o_mcu_axi_m_awaddr     (o_mcu_axi_m_awaddr),
  .o_mcu_axi_m_awid       (o_mcu_axi_m_awid),
  .o_mcu_axi_m_awlen      (o_mcu_axi_m_awlen),
  .o_mcu_axi_m_awsize     (o_mcu_axi_m_awsize),
  .o_mcu_axi_m_awburst    (o_mcu_axi_m_awburst),
  .o_mcu_axi_m_awprot     (o_mcu_axi_m_awprot),
  .o_mcu_axi_m_awvalid    (o_mcu_axi_m_awvalid),
  .i_mcu_axi_m_awready    (i_mcu_axi_m_awready),
  .o_mcu_axi_m_wdata      (o_mcu_axi_m_wdata),
  .o_mcu_axi_m_wstrb      (o_mcu_axi_m_wstrb),
  .o_mcu_axi_m_wlast      (o_mcu_axi_m_wlast),
  .o_mcu_axi_m_wvalid     (o_mcu_axi_m_wvalid),
  .i_mcu_axi_m_wready     (i_mcu_axi_m_wready),
  .i_mcu_axi_m_bvalid     (i_mcu_axi_m_bvalid),
  .i_mcu_axi_m_bid        (i_mcu_axi_m_bid),
  .i_mcu_axi_m_bresp      (i_mcu_axi_m_bresp),
  .o_mcu_axi_m_bready     (o_mcu_axi_m_bready),
  .o_mcu_axi_m_araddr     (o_mcu_axi_m_araddr),
  .o_mcu_axi_m_arid       (o_mcu_axi_m_arid),
  .o_mcu_axi_m_arlen      (o_mcu_axi_m_arlen),
  .o_mcu_axi_m_arsize     (o_mcu_axi_m_arsize),
  .o_mcu_axi_m_arburst    (o_mcu_axi_m_arburst),
  .o_mcu_axi_m_arprot     (o_mcu_axi_m_arprot),
  .o_mcu_axi_m_arvalid    (o_mcu_axi_m_arvalid),
  .i_mcu_axi_m_arready    (i_mcu_axi_m_arready),
  .i_mcu_axi_m_rvalid     (i_mcu_axi_m_rvalid),
  .i_mcu_axi_m_rlast      (i_mcu_axi_m_rlast),
  .i_mcu_axi_m_rid        (i_mcu_axi_m_rid),
  .i_mcu_axi_m_rdata      (i_mcu_axi_m_rdata),
  .i_mcu_axi_m_rresp      (i_mcu_axi_m_rresp),
  .o_mcu_axi_m_rready     (o_mcu_axi_m_rready),
  .i_cfg_apb4_s_paddr     (i_cfg_apb4_s_paddr),
  .i_cfg_apb4_s_pwdata    (i_cfg_apb4_s_pwdata),
  .i_cfg_apb4_s_pwrite    (i_cfg_apb4_s_pwrite),
  .i_cfg_apb4_s_psel      (i_cfg_apb4_s_psel),
  .i_cfg_apb4_s_penable   (i_cfg_apb4_s_penable),
  .i_cfg_apb4_s_pstrb     (i_cfg_apb4_s_pstrb),
  .i_cfg_apb4_s_pprot     (i_cfg_apb4_s_pprot),
  .o_cfg_apb4_s_pready    (o_cfg_apb4_s_pready),
  .o_cfg_apb4_s_prdata    (o_cfg_apb4_s_prdata),
  .o_cfg_apb4_s_pslverr   (o_cfg_apb4_s_pslverr),
  .o_pintreq              (o_pintreq),
  .o_pintbus              (o_pintbus),
  .i_test_mode            (test_mode),
  .i_scan_en              (i_scan_en),
  // Memory configutation pins
  .i_impl                 (i_impl),
  .o_impl                 (o_impl)
);


endmodule
