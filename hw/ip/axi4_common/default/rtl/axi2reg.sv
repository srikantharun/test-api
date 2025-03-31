// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of axi2reg block for cmdblock
// This module handles the AXI to reg transaction requests for RD and WR.
// RD and WR are handled seperatly.
// In case of burst the address is increment based on size.
// Burst types INCR and FIXED are supported, WRAP is treated as INCR
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _AXI2REG_SV_
`define _AXI2REG_SV_

module axi2reg #(
  parameter int unsigned IDW = 4,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = 64,
  parameter int unsigned BW = 6,
  parameter int unsigned NR_WR_REQS = 2,
  parameter int unsigned NR_RD_REQS = 2,
  parameter int unsigned WBUF = NR_WR_REQS,
  parameter int unsigned RD_RESP_DEPTH = 2,
  parameter int unsigned WR_RESP_DEPTH = 2,
  parameter int unsigned OSR = 2
) (
  input wire i_clk,
  input wire i_rst_n,

  ///// AXI slave:
  // Write Address Channel
  input  wire [ IDW-1:0] awid,
  input  wire [  AW-1:0] awaddr,
  input  wire [  BW-1:0] awlen,
  input  wire [     2:0] awsize,
  input  wire [     1:0] awburst,
  // input  wire [     1:0] awlock,
  // input  wire [     2:0] awprot,
  input  wire            awvalid,
  output wire            awready,
  // Read Address Channel
  input  wire [ IDW-1:0] arid,
  input  wire [  AW-1:0] araddr,
  input  wire [  BW-1:0] arlen,
  input  wire [     2:0] arsize,
  input  wire [     1:0] arburst,
  // input  wire [     1:0] arlock,
  // input  wire [     2:0] arprot,
  input  wire            arvalid,
  output wire            arready,
  // Write  Data Channel
  input  wire [  DW-1:0] wdata,
  input  wire [DW/8-1:0] wstrb,
  input  wire            wlast,
  input  wire            wvalid,
  output wire            wready,
  // Read Data Channel
  output wire [ IDW-1:0] rid,
  output wire [  DW-1:0] rdata,
  output wire [     1:0] rresp,
  output wire            rlast,
  output wire            rvalid,
  input  wire            rready,
  // Write Response Channel
  output wire [ IDW-1:0] bid,
  output wire [     1:0] bresp,
  output wire            bvalid,
  input  wire            bready,

  ////// reg master:
  // Write path:
  output wire              reg_wvld,
  input  wire              reg_wrdy,
  output wire [    AW-1:0] reg_waddr,
  output wire [    DW-1:0] reg_wdata,
  output wire [(DW/8)-1:0] reg_wstrb,
  input  wire              reg_wresp_vld,
  output wire              reg_wresp_rdy,
  input  wire              reg_wresp_error,

  // Read path:
  output wire          reg_rvld,
  input  wire          reg_rrdy,
  output wire [AW-1:0] reg_raddr,
  input  wire          reg_rresp_vld,
  output wire          reg_rresp_rdy,
  input  wire          reg_rresp_error,
  input  wire [DW-1:0] reg_rresp_data
);

  typedef struct packed {
    logic [1:0]         resp;
  } wr_resp_t;

  typedef struct packed {
    logic [DW-1:0] data;
    logic [1:0]    resp;
  } rd_resp_t;

  // only send through last response in case of write path:
  logic blast_int;
  logic bvalid_int;
  logic bready_int;

  assign bvalid = bvalid_int & blast_int;
  assign bready_int = bready | ~blast_int;

  axi2reg_path #(
    .IDW(IDW),
    .AW(AW),
    .DW(DW),
    .BW(BW),
    .OSR(OSR),
    .WRITE(1),
    .datatype_t(wr_resp_t),
    .NR_REQS(NR_WR_REQS),
    .WBUF(WBUF),
    .RESP_DEPTH(WR_RESP_DEPTH)
  ) i_wr_path (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    ///// AXI slave:
    // Address Channel
    .id(awid),
    .len(awlen),
    .addr(awaddr),
    .size(awsize),
    .burst(awburst),
    // .lock(awlock),
    // .prot(awprot),
    .valid(awvalid),
    .ready(awready),

    // Write  Data Channel
    .wdata (wdata),
    .wstrb (wstrb),
    .wlast (wlast),
    .wvalid(wvalid),
    .wready(wready),

    // Resp Data Channel
    .rid(bid),
    .rdata(), // ASO-UNUSED_OUTPUT: rdata not used for wr path
    .rresp(bresp),
    .rlast(blast_int),
    .rvalid(bvalid_int),
    .rready(bready_int),

    .reg_vld(reg_wvld),
    .reg_rdy(reg_wrdy),
    .reg_addr(reg_waddr),
    .reg_wdata(reg_wdata),
    .reg_wstrb(reg_wstrb),
    .reg_resp_vld(reg_wresp_vld),
    .reg_resp_rdy(reg_wresp_rdy),
    .reg_resp_error(reg_wresp_error),
    .reg_resp_data('0)
  );

  axi2reg_path #(
    .IDW(IDW),
    .AW(AW),
    .DW(DW),
    .BW(BW),
    .OSR(OSR),
    .WRITE(0),
    .datatype_t(rd_resp_t),
    .NR_REQS(NR_RD_REQS),
    .WBUF(0),
    .RESP_DEPTH(RD_RESP_DEPTH)
  ) i_rd_path (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    ///// AXI slave:
    // Address Channel
    .id(arid),
    .len(arlen),
    .addr(araddr),
    .size(arsize),
    .burst(arburst),
    // .lock(arlock),
    // .prot(arprot),
    .valid(arvalid),
    .ready(arready),

    // Write  Data Channel
    .wdata ('0),
    .wstrb ('0),
    .wlast ('0),
    .wvalid('0),
    .wready(), // ASO-UNUSED_OUTPUT: write data not used for read path

    // Resp Data Channel
    .rid(rid),
    .rdata(rdata),
    .rresp(rresp),
    .rlast(rlast),
    .rvalid(rvalid),
    .rready(rready),

    .reg_vld(reg_rvld),
    .reg_rdy(reg_rrdy),
    .reg_addr(reg_raddr),
    .reg_wdata(), // ASO-UNUSED_OUTPUT: write data not used for read path
    .reg_wstrb(), // ASO-UNUSED_OUTPUT: write data not used for read path
    .reg_resp_vld(reg_rresp_vld),
    .reg_resp_rdy(reg_rresp_rdy),
    .reg_resp_error(reg_rresp_error),
    .reg_resp_data(reg_rresp_data)
  );

endmodule

`endif  // _AXI2REG_SV_
