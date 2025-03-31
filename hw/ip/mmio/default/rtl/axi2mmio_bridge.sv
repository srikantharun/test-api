// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AXI4 to MMIO bridge
// This module is a bridge between an AXI manager and two MMIO subordinates.
// The AXI read transaction is converted to a MMIO read transaction
// The AXI write transation is converted to a MMIO write transaction
// Two DW_axi_gs instances are used to increase the bandwidth.
// In addition, request backpressure is introduced when the AXI master
// is not ready to accept the memory response.

// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef AXI2MMIO_BRIDGE_SV
`define AXI2MMIO_BRIDGE_SV

module axi2mmio_bridge
  import mmio_pkg::*, axi_pkg::*;
#( parameter int unsigned AXI_S_ID_WIDTH = 32'd4,
   parameter int unsigned AXI_ADDR_WIDTH = 32'd40,
   parameter int unsigned AXI_WSTRB_WIDTH = 32'd8,
   parameter int unsigned AXI_DATA_WIDTH = 32'd64,
   parameter int unsigned MEM_BASE_ADDRESS_WIDTH = 32'd18,
   parameter int unsigned MAX_MEM_LATENCY = 10
) (
  // Clock and reset signals
  input  wire                                   i_clk,
  input  wire                                   i_rst_n,
  // AXI write address channel
  input  logic                                  i_axi_s_awvalid,
  input  logic      [      AXI_ADDR_WIDTH-1:0]  i_axi_s_awaddr,
  input  logic      [      AXI_S_ID_WIDTH-1:0]  i_axi_s_awid,
  input  axi_len_t                              i_axi_s_awlen,
  input  axi_size_t                             i_axi_s_awsize,
  input  axi_burst_t                            i_axi_s_awburst,
  output logic                                  o_axi_s_awready,
  // AXI write data channel
  input  logic                                  i_axi_s_wvalid,
  input  logic                                  i_axi_s_wlast,
  input  logic      [     AXI_WSTRB_WIDTH-1:0]  i_axi_s_wstrb,
  input  logic      [      AXI_DATA_WIDTH-1:0]  i_axi_s_wdata,
  output logic                                  o_axi_s_wready,
  // AXI write response channel
  output logic                                  o_axi_s_bvalid,
  output logic      [      AXI_S_ID_WIDTH-1:0]  o_axi_s_bid,
  output axi_resp_t                             o_axi_s_bresp,
  input  logic                                  i_axi_s_bready,
  // AXI read address channel
  input  logic                                  i_axi_s_arvalid,
  input  logic      [      AXI_ADDR_WIDTH-1:0]  i_axi_s_araddr,
  input  logic      [      AXI_S_ID_WIDTH-1:0]  i_axi_s_arid,
  input  axi_len_t                              i_axi_s_arlen,
  input  axi_size_t                             i_axi_s_arsize,
  input  axi_burst_t                            i_axi_s_arburst,
  output logic                                  o_axi_s_arready,
  // AXI read data/response channel
  output logic                                  o_axi_s_rvalid,
  output logic                                  o_axi_s_rlast,
  output logic      [      AXI_S_ID_WIDTH-1:0]  o_axi_s_rid,
  output logic      [      AXI_DATA_WIDTH-1:0]  o_axi_s_rdata,
  output axi_resp_t                             o_axi_s_rresp,
  input  logic                                  i_axi_s_rready,
  // MMIO write channel
  output mmio_dmc_wo_req_t                      o_mmio_s_wr_req,
  input  mmio_dmc_wo_rsp_t                      i_mmio_s_wr_rsp,
  // MMIO read channel
  output mmio_dmc_ro_req_t                      o_mmio_s_rd_req,
  input  mmio_dmc_ro_rsp_t                      i_mmio_s_rd_rsp,

  // Configuration control
  input logic [MEM_BASE_ADDRESS_WIDTH-1:0]      i_mem_base_address
);

  // =====================================================
  // Localparams
  // =====================================================
  localparam int unsigned VA_BASE_LSB = AXI_ADDR_WIDTH - MEM_BASE_ADDRESS_WIDTH;

  // =====================================================
  // Type declarations
  // =====================================================

  typedef enum logic [1:0] {
    OK_R     = 2'b00,
    OK_W     = 2'b01,
    SLVERR_R = 2'b10,
    SLVERR_W = 2'b11
  } gs_resp_type_e;

  // =====================================================
  // Signal declarations
  // =====================================================
  logic mread;
  logic mwrite;
  logic mread_err_msk;
  logic mwrite_err_msk;
  logic mlast;
  logic mlast_delayed;
  logic addr_err_rd;
  logic addr_err_rd_del;
  logic addr_err_rd_del_vld;
  logic addr_err_wr;
  logic addr_err_wr_req;
  logic addr_err_wr_del;
  logic addr_err_wr_del_vld;

  logic [AXI_ADDR_WIDTH-1:0] rd_addr;
  logic [AXI_ADDR_WIDTH-1:0] wr_addr;

  // =====================================================
  // RTL
  // =====================================================

  always_comb o_mmio_s_rd_req.payload.addr = rd_addr[mmio_pkg::MMIO_DMC_ADDR_WIDTH-1:0];
  always_comb o_mmio_s_wr_req.payload.addr = wr_addr[mmio_pkg::MMIO_DMC_ADDR_WIDTH-1:0];

  assign mread_err_msk = mread & (~addr_err_rd);
  assign mwrite_err_msk = mwrite & (~addr_err_wr);

  assign addr_err_rd = (rd_addr[VA_BASE_LSB+:MEM_BASE_ADDRESS_WIDTH] ==
                    i_mem_base_address[MEM_BASE_ADDRESS_WIDTH-1:0]) ? 1'b0 : 1'b1;
  assign o_mmio_s_rd_req.valid = mread_err_msk & (~addr_err_rd);

  assign addr_err_wr = (wr_addr[VA_BASE_LSB+:MEM_BASE_ADDRESS_WIDTH] ==
                    i_mem_base_address[MEM_BASE_ADDRESS_WIDTH-1:0]) ? 1'b0 : 1'b1;
  assign addr_err_wr_req = addr_err_wr;
  assign o_mmio_s_wr_req.valid = mwrite_err_msk & (~addr_err_wr);

  axi2reg #(
    .IDW(AXI_S_ID_WIDTH),
    .AW(AXI_ADDR_WIDTH),
    .DW(AXI_DATA_WIDTH),
    .BW(AXI_LEN_WIDTH),
    .NR_WR_REQS(3),  // max amount of reqs in axi2reg
    .NR_RD_REQS(3),  // max amount of reqs in axi2reg
    .WBUF(2),  // FIFO depth of write data
    .RD_RESP_DEPTH(2),  // FIFO depth of read data, same as OSR if backpressure is not supported
    .WR_RESP_DEPTH(2),  // FIFO depth of bresp, same as OSR if backpressure is not supported
    .OSR(MAX_MEM_LATENCY+2)  // max amount of outstanding requests
  ) u_axi2mmio (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    ///// AXI slave:
    // Write Address Channel
    .awid(i_axi_s_awid),
    .awaddr(i_axi_s_awaddr),
    .awlen(i_axi_s_awlen),
    .awsize(i_axi_s_awsize),
    .awburst(i_axi_s_awburst),
    .awvalid(i_axi_s_awvalid),
    .awready(o_axi_s_awready),
    // Read Address Channel
    .arid(i_axi_s_arid),
    .araddr(i_axi_s_araddr),
    .arlen(i_axi_s_arlen),
    .arsize(i_axi_s_arsize),
    .arburst(i_axi_s_arburst),
    .arvalid(i_axi_s_arvalid),
    .arready(o_axi_s_arready),
    // Write  Data Channel
    .wdata(i_axi_s_wdata),
    .wstrb(i_axi_s_wstrb),
    .wlast(i_axi_s_wlast),
    .wvalid(i_axi_s_wvalid),
    .wready(o_axi_s_wready),
    // Read Data Channel
    .rid(o_axi_s_rid),
    .rdata(o_axi_s_rdata),
    .rresp(o_axi_s_rresp),
    .rlast(o_axi_s_rlast),
    .rvalid(o_axi_s_rvalid),
    .rready(i_axi_s_rready),
    // Write Response Chainel
    .bid(o_axi_s_bid),
    .bresp(o_axi_s_bresp),
    .bvalid(o_axi_s_bvalid),
    .bready(i_axi_s_bready),

    ////// reg master:
    // Write path:
    .reg_wvld(mwrite),
    .reg_wrdy(i_mmio_s_wr_rsp.ready | addr_err_wr),
    .reg_waddr(wr_addr),
    .reg_wdata(o_mmio_s_wr_req.payload.data),
    .reg_wstrb(o_mmio_s_wr_req.payload.wbe),
    .reg_wresp_vld(i_mmio_s_wr_rsp.ack | (addr_err_wr_del & addr_err_wr_del_vld)),
    .reg_wresp_rdy(o_mmio_s_wr_req.rsp_ready),
    .reg_wresp_error(addr_err_wr_del | i_mmio_s_wr_rsp.payload.error),

    // Read path:
    .reg_rvld(mread),
    .reg_rrdy(i_mmio_s_rd_rsp.ready | addr_err_rd),
    .reg_raddr(rd_addr),
    .reg_rresp_vld(i_mmio_s_rd_rsp.ack | (addr_err_rd_del & addr_err_rd_del_vld)),
    .reg_rresp_rdy(o_mmio_s_rd_req.rsp_ready),
    .reg_rresp_error(addr_err_rd_del | i_mmio_s_rd_rsp.payload.error),
    .reg_rresp_data(i_mmio_s_rd_rsp.payload.data)
  );

  cc_stream_buffer #(
    .DW(1),
    .DEPTH(MAX_MEM_LATENCY)
  ) u_rd_shift_reg (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld(mread),
    .wr_data(addr_err_rd),
    .wr_rdy(), // ASO-UNUSED_OUTPUT: not used

      // pop entry either if there was an error or data is returned. Obviously mask with response ready
    .rd_rdy(o_mmio_s_rd_req.rsp_ready & (addr_err_rd_del | i_mmio_s_rd_rsp.ack)),
    .rd_data(addr_err_rd_del),
    .rd_vld(addr_err_rd_del_vld)
  );
  cc_stream_buffer #(
    .DW(1),
    .DEPTH(MAX_MEM_LATENCY)
  ) u_wr_error_response (
    .i_clk,
    .i_rst_n,

    .wr_vld(mwrite),
    .wr_data(addr_err_wr_req),
    .wr_rdy(), // ASO-UNUSED_OUTPUT: not used

      // pop entry either if there was an error or data is returned. Obviously mask with response ready
    .rd_rdy(o_mmio_s_wr_req.rsp_ready & (addr_err_wr_del | i_mmio_s_wr_rsp.ack)),
    .rd_data(addr_err_wr_del),
    .rd_vld(addr_err_wr_del_vld)
  );

endmodule

`endif  // MEM_AXI2MMIO_BRIDGE_SV
