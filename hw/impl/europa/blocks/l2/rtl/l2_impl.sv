// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Europa L2 implementation.
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_IMPL_SV
`define L2_IMPL_SV

module l2_impl
  import chip_pkg::*;
  import axi_pkg::*;
  import l2_p_pkg::*;
  (
  // Clock and reset signals
  input  wire                i_clk,
  input  wire                i_rst_n,
  // AXI write address channel
  input  logic               i_axi_s_awvalid,
  input  chip_axi_addr_t     i_axi_s_awaddr,
  input  l2_targ_ht_axi_id_t i_axi_s_awid,
  input  axi_len_t           i_axi_s_awlen,
  input  axi_size_t          i_axi_s_awsize,
  input  axi_burst_t         i_axi_s_awburst,
  input  logic               i_axi_s_awlock,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  axi_cache_t         i_axi_s_awcache, // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  axi_prot_t          i_axi_s_awprot,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  output logic               o_axi_s_awready,
  // AXI write data channel
  input  logic               i_axi_s_wvalid,
  input  logic               i_axi_s_wlast,
  input  chip_axi_ht_data_t  i_axi_s_wdata,
  input  chip_axi_ht_wstrb_t i_axi_s_wstrb,
  output logic               o_axi_s_wready,
  // AXI write response channel
  output logic               o_axi_s_bvalid,
  output l2_targ_ht_axi_id_t o_axi_s_bid,
  output axi_resp_e          o_axi_s_bresp,
  input  logic               i_axi_s_bready,
  // AXI read address channel
  input  logic               i_axi_s_arvalid,
  input  chip_axi_addr_t     i_axi_s_araddr,
  input  l2_targ_ht_axi_id_t i_axi_s_arid,
  input  axi_len_t           i_axi_s_arlen,
  input  axi_size_t          i_axi_s_arsize,
  input  axi_burst_t         i_axi_s_arburst,
  input  logic               i_axi_s_arlock,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  axi_cache_t         i_axi_s_arcache, // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  axi_prot_t          i_axi_s_arprot,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  output logic               o_axi_s_arready,
  // AXI read data/response channel
  output logic               o_axi_s_rvalid,
  output logic               o_axi_s_rlast,
  output l2_targ_ht_axi_id_t o_axi_s_rid,
  output chip_axi_ht_data_t  o_axi_s_rdata,
  output axi_resp_e          o_axi_s_rresp,
  input  logic               i_axi_s_rready,

  // SRAM configuration
  input  logic               i_ret,
  input  logic               i_pde,
  output logic               o_prn,
  input  logic               i_scan_en

  );

  l2 #(
    .l2_axi_data_t (chip_axi_ht_data_t),
    .l2_axi_strb_t (chip_axi_ht_wstrb_t),
    .l2_axi_len_t  (axi_len_t),
    .l2_axi_addr_t (l2_addr_t),
    .l2_axi_id_t   (l2_targ_ht_axi_id_t),
    .l2_axi_size_t (axi_size_t),
    .l2_axi_burst_t(axi_burst_t),
    .l2_axi_resp_t (axi_resp_e),
    .l2_axi_cache_t(axi_cache_t),
    .l2_axi_prot_t (axi_prot_t)
  ) u_l2_gdr (
    // Clock and reset signals
    .i_clk ,
    .i_rst_n,
    // AXI write address channel
    .i_axi_s_awvalid,
    .i_axi_s_awaddr (l2_addr_t'(i_axi_s_awaddr)),
    .i_axi_s_awid,
    .i_axi_s_awlen,
    .i_axi_s_awsize,
    .i_axi_s_awburst,
    .i_axi_s_awlock,
    .i_axi_s_awcache,
    .i_axi_s_awprot,
    .o_axi_s_awready,
    // AXI write data channel
    .i_axi_s_wvalid,
    .i_axi_s_wlast,
    .i_axi_s_wdata,
    .i_axi_s_wstrb,
    .o_axi_s_wready,
    // AXI write response channel
    .o_axi_s_bvalid,
    .o_axi_s_bid,
    .o_axi_s_bresp,
    .i_axi_s_bready,
    // AXI read address channel
    .i_axi_s_arvalid,
    .i_axi_s_araddr (l2_addr_t'(i_axi_s_araddr)),
    .i_axi_s_arid,
    .i_axi_s_arlen,
    .i_axi_s_arsize,
    .i_axi_s_arburst,
    .i_axi_s_arlock,
    .i_axi_s_arcache,
    .i_axi_s_arprot,
    .o_axi_s_arready,
    // AXI read data/response channel
    .o_axi_s_rvalid,
    .o_axi_s_rlast,
    .o_axi_s_rid,
    .o_axi_s_rdata,
    .o_axi_s_rresp,
    .i_axi_s_rready,
    // SRAM configuration
    .i_impl         (axe_tcl_sram_pkg::impl_inp_t'{
                      //TODO: @(manuel.oliveira) Remove this once we update the structure to remove the margin signals
                      default: '0,
                      ret    : i_ret,
                      pde    : i_pde,
                      se     : i_scan_en
                    }),
    .o_impl         (o_prn)
  );

endmodule

`endif  // L2_IMPL_SV
