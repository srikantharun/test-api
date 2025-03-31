// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L2 module.
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_SV
`define L2_SV

module l2
  import l2_pkg::*;
  import l2_cfg_pkg::*;
  #(
    parameter type l2_axi_data_t = l2_pkg::l2_axi_data_t,
    parameter type l2_axi_strb_t = l2_pkg::l2_axi_strb_t,
    parameter type l2_axi_len_t = axi_pkg::axi_len_t,
    parameter type l2_axi_addr_t = l2_pkg::l2_axi_addr_t,
    parameter type l2_axi_id_t = l2_pkg::l2_axi_id_t,
    parameter type l2_axi_size_t = axi_pkg::axi_size_t,
    parameter type l2_axi_burst_t = axi_pkg::axi_burst_t,
    parameter type l2_axi_resp_t = axi_pkg::axi_resp_e,
    parameter type l2_axi_cache_t = axi_pkg::axi_cache_t,
    parameter type l2_axi_prot_t = axi_pkg::axi_prot_t
  ) (
  // Clock and reset signals
  input  wire                    i_clk,
  input  wire                    i_rst_n,
  // AXI write address channel
  input  logic                   i_axi_s_awvalid,
  input  l2_axi_addr_t           i_axi_s_awaddr,
  input  l2_axi_id_t             i_axi_s_awid,
  input  l2_axi_len_t            i_axi_s_awlen,
  input  l2_axi_size_t           i_axi_s_awsize,
  input  l2_axi_burst_t          i_axi_s_awburst,
  input  logic                   i_axi_s_awlock,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  l2_axi_cache_t          i_axi_s_awcache, // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  l2_axi_prot_t           i_axi_s_awprot,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  output logic                   o_axi_s_awready,
  // AXI write data channel
  input  logic                   i_axi_s_wvalid,
  input  logic                   i_axi_s_wlast,
  input  l2_axi_data_t           i_axi_s_wdata,
  input  l2_axi_strb_t           i_axi_s_wstrb,
  output logic                   o_axi_s_wready,
  // AXI write response channel
  output logic                   o_axi_s_bvalid,
  output l2_axi_id_t             o_axi_s_bid,
  output l2_axi_resp_t           o_axi_s_bresp,
  input  logic                   i_axi_s_bready,
  // AXI read address channel
  input  logic                   i_axi_s_arvalid,
  input  l2_axi_addr_t           i_axi_s_araddr,
  input  l2_axi_id_t             i_axi_s_arid,
  input  l2_axi_len_t            i_axi_s_arlen,
  input  l2_axi_size_t           i_axi_s_arsize,
  input  l2_axi_burst_t          i_axi_s_arburst,
  input  logic                   i_axi_s_arlock,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  l2_axi_cache_t          i_axi_s_arcache, // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  input  l2_axi_prot_t           i_axi_s_arprot,  // ASO-UNUSED_INPUT: AXI4 feature not supported by l2
  output logic                   o_axi_s_arready,
  // AXI read data/response channel
  output logic                   o_axi_s_rvalid,
  output logic                   o_axi_s_rlast,
  output l2_axi_id_t             o_axi_s_rid,
  output l2_axi_data_t           o_axi_s_rdata,
  output l2_axi_resp_t           o_axi_s_rresp,
  input  logic                   i_axi_s_rready,

  // SRAM configuration
  input  axe_tcl_sram_pkg::impl_inp_t i_impl,
  output axe_tcl_sram_pkg::impl_oup_t o_impl

);
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================

  //Wires
  l2_mem_req_t        mem_req;
  l2_mem_rsp_t        mem_rsp;
  logic               mem_rd_ready;
  logic               mem_wr_ready;

  axi_pkg::axi_resp_t axi_s_rresp;
  axi_pkg::axi_resp_t axi_s_bresp;
  // Regs
  logic               mwrite_delayed;
  logic               mread_delayed;

  // =====================================================
  // RTL
  // =====================================================

  always_comb begin : proc_adjust_type_comb
    o_axi_s_rresp = l2_axi_resp_t'(axi_s_rresp);
    o_axi_s_bresp = l2_axi_resp_t'(axi_s_bresp);
  end

  axi2reg #(
    .IDW          ($bits(l2_axi_id_t)),
    .AW           ($bits(l2_axi_addr_t)),
    .DW           ($bits(l2_axi_data_t)),
    .BW           ($bits(l2_axi_len_t)),
    .NR_WR_REQS   (2),
    .NR_RD_REQS   (2),
    .WBUF         (2),
    .RD_RESP_DEPTH(L2_MEMORY_RESP_LATENCY),
    .WR_RESP_DEPTH(L2_MEMORY_RESP_LATENCY),
    .OSR          (L2_MEMORY_RESP_LATENCY)
  ) u_l2_axi2mmio (
    .i_clk             (i_clk),
    .i_rst_n           (i_rst_n),
    ///// AXI slave:
    // Write Address Channel
    .awid            (i_axi_s_awid),
    .awaddr          (i_axi_s_awaddr),
    .awlen           (i_axi_s_awlen),
    .awsize          (i_axi_s_awsize),
    .awburst         (i_axi_s_awburst),
    .awvalid         (i_axi_s_awvalid),
    .awready         (o_axi_s_awready),
    // Read Address Channel
    .arid            (i_axi_s_arid),
    .araddr          (i_axi_s_araddr),
    .arlen           (i_axi_s_arlen),
    .arsize          (i_axi_s_arsize),
    .arburst         (i_axi_s_arburst),
    .arvalid         (i_axi_s_arvalid),
    .arready         (o_axi_s_arready),
    // Write  Data Channel
    .wdata           (i_axi_s_wdata),
    .wstrb           (i_axi_s_wstrb),
    .wlast           (i_axi_s_wlast),
    .wvalid          (i_axi_s_wvalid),
    .wready          (o_axi_s_wready),
    // Read Data Channel
    .rid             (o_axi_s_rid),
    .rdata           (o_axi_s_rdata),
    .rresp           (axi_s_rresp),
    .rlast           (o_axi_s_rlast),
    .rvalid          (o_axi_s_rvalid),
    .rready          (i_axi_s_rready),
    // Write Response Channel
    .bid             (o_axi_s_bid),
    .bresp           (axi_s_bresp),
    .bvalid          (o_axi_s_bvalid),
    .bready          (i_axi_s_bready),
    ////// reg master:
    // Write path:
    .reg_wvld        (mem_req.wr.en),
    .reg_wrdy        (mem_wr_ready),
    .reg_waddr       (mem_req.wr.addr),
    .reg_wdata       (mem_req.wr.data),
    .reg_wstrb       (mem_req.wr.wbe),
    .reg_wresp_vld   (mem_rsp.wr_rsp),
    .reg_wresp_rdy   (),                 // ASO-UNUSED_OUTPUT: The bridge should always accept response
    .reg_wresp_error ('0),
    // Read path:
    .reg_rvld        (mem_req.rd.en),
    .reg_rrdy        (mem_rd_ready),
    .reg_raddr       (mem_req.rd.addr),
    .reg_rresp_vld   (mem_rsp.rd_rsp),
    .reg_rresp_rdy   (),                 // ASO-UNUSED_OUTPUT: The bridge should always accept response
    .reg_rresp_error ('0),
    .reg_rresp_data  (mem_rsp.data)
  );

  l2_mem u_l2_mem (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_mem_req        (mem_req),
    .o_mem_rd_ready   (mem_rd_ready),
    .o_mem_wr_ready   (mem_wr_ready),
    .o_mem_rsp        (mem_rsp),
    // Memory configutation pins
    .i_impl           (i_impl),
    .o_impl           (o_impl)
  );

endmodule

`endif  // L2_SV
