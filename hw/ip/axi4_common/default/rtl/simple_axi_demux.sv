// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of simple_axi_demux it doesn't have fancy axi bus features
// like out of order completion, locking, etc; but not required for end points.
// At least it's configurable in sizes, addresses etc
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _SIMPLE_AXI_DEMUX_SV_
`define _SIMPLE_AXI_DEMUX_SV_

module simple_axi_demux #(
  parameter int unsigned NR_MASTERS = 2,
  parameter int unsigned SL_CAP = 'h4000,
  parameter int MT_ST_ADDR[NR_MASTERS] = '{default:0},
  parameter int MT_CAP[NR_MASTERS] = '{default:0},
  parameter int unsigned IDW = 4,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = 64,
  parameter int unsigned BW = 6,
  parameter int unsigned SL_WREQ_SHIELD = 0,
  parameter int unsigned SL_RREQ_SHIELD = 0,
  parameter int unsigned SL_WDATA_SHIELD = 0,
  parameter int unsigned SL_WRESP_SHIELD = 0,
  parameter int unsigned SL_RRESP_SHIELD = 0,
  parameter int unsigned OSR = 2,
  parameter int unsigned EXT_SEL = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic [$clog2(NR_MASTERS+1)-1:0] i_ext_mt_sel_rd,
  input logic [$clog2(NR_MASTERS+1)-1:0] i_ext_mt_sel_wr,

  ///// AXI slave:
  // Write Address Channel
  input  logic [ IDW-1:0] s_awid,
  input  logic [  AW-1:0] s_awaddr,
  input  logic [  BW-1:0] s_awlen,
  input  logic [     2:0] s_awsize,
  input  logic [     1:0] s_awburst,
  input  logic            s_awlock,
  input  logic [     2:0] s_awprot,
  input  logic [     3:0] s_awcache,
  input  logic            s_awvalid,
  output logic            s_awready,
  // Read Address Channel
  input  logic [ IDW-1:0] s_arid,
  input  logic [  AW-1:0] s_araddr,
  input  logic [  BW-1:0] s_arlen,
  input  logic [     2:0] s_arsize,
  input  logic [     1:0] s_arburst,
  input  logic            s_arlock,
  input  logic [     2:0] s_arprot,
  input  logic [     3:0] s_arcache,
  input  logic            s_arvalid,
  output logic            s_arready,
  // Write  Data Channel
  input  logic [  DW-1:0] s_wdata,
  input  logic [DW/8-1:0] s_wstrb,
  input  logic            s_wlast,
  input  logic            s_wvalid,
  output logic            s_wready,
  // Read Data Channel
  output logic [ IDW-1:0] s_rid,
  output logic [  DW-1:0] s_rdata,
  output logic [     1:0] s_rresp,
  output logic            s_rlast,
  output logic            s_rvalid,
  input  logic            s_rready,
  // Write Response Channel
  output logic [ IDW-1:0] s_bid,
  output logic [     1:0] s_bresp,
  output logic            s_bvalid,
  input  logic            s_bready,

  ///// AXI Master:
  // Write Address Channel
  output logic [NR_MASTERS-1:0][IDW-1:0] m_awid   ,
  output logic [NR_MASTERS-1:0][ BW-1:0] m_awlen  ,
  output logic [NR_MASTERS-1:0][ AW-1:0] m_awaddr ,
  output logic [NR_MASTERS-1:0][    2:0] m_awsize ,
  output logic [NR_MASTERS-1:0][    1:0] m_awburst,
  output logic [NR_MASTERS-1:0]          m_awlock ,
  output logic [NR_MASTERS-1:0][    2:0] m_awprot ,
  output logic [NR_MASTERS-1:0][    3:0] m_awcache,
  output logic [NR_MASTERS-1:0]          m_awvalid,
  input  logic [NR_MASTERS-1:0]          m_awready,

  // Read Address Channel
  output logic [NR_MASTERS-1:0][IDW-1:0] m_arid   ,
  output logic [NR_MASTERS-1:0][ BW-1:0] m_arlen  ,
  output logic [NR_MASTERS-1:0][ AW-1:0] m_araddr ,
  output logic [NR_MASTERS-1:0][    2:0] m_arsize ,
  output logic [NR_MASTERS-1:0][    1:0] m_arburst,
  output logic [NR_MASTERS-1:0]          m_arlock ,
  output logic [NR_MASTERS-1:0][    2:0] m_arprot ,
  output logic [NR_MASTERS-1:0][    3:0] m_arcache,
  output logic [NR_MASTERS-1:0]          m_arvalid,
  input  logic [NR_MASTERS-1:0]          m_arready,

  // Read Resp Channel
  input  logic [NR_MASTERS-1:0][IDW-1:0] m_rid   ,
  input  logic [NR_MASTERS-1:0][ DW-1:0] m_rdata ,
  input  logic [NR_MASTERS-1:0][    1:0] m_rresp ,
  input  logic [NR_MASTERS-1:0]          m_rlast ,
  input  logic [NR_MASTERS-1:0]          m_rvalid,
  output logic [NR_MASTERS-1:0]          m_rready,

  // Write  Data Channel
  output logic [NR_MASTERS-1:0][  DW-1:0] m_wdata ,
  output logic [NR_MASTERS-1:0][DW/8-1:0] m_wstrb ,
  output logic [NR_MASTERS-1:0]           m_wlast ,
  output logic [NR_MASTERS-1:0]           m_wvalid,
  input  logic [NR_MASTERS-1:0]           m_wready,

  // Write Resp Channel
  input  logic [NR_MASTERS-1:0][IDW-1:0] m_bid   ,
  input  logic [NR_MASTERS-1:0][    1:0] m_bresp ,
  input  logic [NR_MASTERS-1:0]          m_bvalid,
  output logic [NR_MASTERS-1:0]          m_bready
);

  logic [NR_MASTERS-1:0]zero_array;

  always_comb zero_array = '0;

  simple_axi_demux_path #(
    .NR_MASTERS(NR_MASTERS),
    .SL_CAP(SL_CAP),
    .MT_ST_ADDR(MT_ST_ADDR),
    .MT_CAP(MT_CAP),
    .IDW(IDW),
    .AW(AW),
    .DW(DW),
    .BW(BW),
    .OSR(OSR),
    .WRITE(1),
    .SL_REQ_SHIELD(SL_WREQ_SHIELD),
    .SL_WDATA_SHIELD(SL_WDATA_SHIELD),
    .SL_RESP_SHIELD(SL_WRESP_SHIELD),
    .EXT_SEL(EXT_SEL)
  ) i_wr_path (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .i_ext_mt_sel(i_ext_mt_sel_wr),

    ///// AXI slave:
    // Address Channel
    .s_id(s_awid),
    .s_len(s_awlen),
    .s_addr(s_awaddr),
    .s_size(s_awsize),
    .s_burst(s_awburst),
    .s_lock(s_awlock),
    .s_prot(s_awprot),
    .s_cache(s_awcache),
    .s_valid(s_awvalid),
    .s_ready(s_awready),

    // Write  Data Channel
    .s_wdata (s_wdata),
    .s_wstrb (s_wstrb),
    .s_wlast (s_wlast),
    .s_wvalid(s_wvalid),
    .s_wready(s_wready),

    // Resp Data Channel
    .s_rid(s_bid),
    .s_rdata(), // ASO-UNUSED_OUTPUT: port not used
    .s_rresp(s_bresp),
    .s_rlast(), // ASO-UNUSED_OUTPUT: port not used
    .s_rvalid(s_bvalid),
    .s_rready(s_bready),

    ///// AXI masters:
    // Address Channel
    .m_id(m_awid),
    .m_len(m_awlen),
    .m_addr(m_awaddr),
    .m_size(m_awsize),
    .m_burst(m_awburst),
    .m_lock(m_awlock),
    .m_prot(m_awprot),
    .m_cache(m_awcache),
    .m_valid(m_awvalid),
    .m_ready(m_awready),

    // Write  Data Channel
    .m_wdata (m_wdata),
    .m_wstrb (m_wstrb),
    .m_wlast (m_wlast),
    .m_wvalid(m_wvalid),
    .m_wready(m_wready),

    // Resp Data Channel
    .m_rid(m_bid),
    .m_rdata('0),         // Not used input in write
    .m_rresp(m_bresp),
    .m_rlast(zero_array),
    .m_rvalid(m_bvalid),
    .m_rready(m_bready)
  );

  // read path
  simple_axi_demux_path #(
    .NR_MASTERS(NR_MASTERS),
    .SL_CAP(SL_CAP),
    .MT_ST_ADDR(MT_ST_ADDR),
    .MT_CAP(MT_CAP),
    .IDW(IDW),
    .AW(AW),
    .DW(DW),
    .BW(BW),
    .OSR(OSR),
    .WRITE(0),
    .SL_REQ_SHIELD(SL_RREQ_SHIELD),
    .SL_RESP_SHIELD(SL_RRESP_SHIELD),
    .EXT_SEL(EXT_SEL)
  ) i_rd_path (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .i_ext_mt_sel(i_ext_mt_sel_rd),

    ///// AXI slave:
    // Address Channel
    .s_id(s_arid),
    .s_len(s_arlen),
    .s_addr(s_araddr),
    .s_size(s_arsize),
    .s_burst(s_arburst),
    .s_lock(s_arlock),
    .s_prot(s_arprot),
    .s_cache(s_arcache),
    .s_valid(s_arvalid),
    .s_ready(s_arready),

    // Write  Data Channel
    .s_wdata ('0),
    .s_wstrb ('0),
    .s_wlast ('0),
    .s_wvalid('0),
    .s_wready(), // ASO-UNUSED_OUTPUT: port not used

    // Resp Data Channel
    .s_rid(s_rid),
    .s_rdata(s_rdata),
    .s_rresp(s_rresp),
    .s_rlast(s_rlast),
    .s_rvalid(s_rvalid),
    .s_rready(s_rready),

    ///// AXI masters:
    // Address Channel
    .m_id(m_arid),
    .m_len(m_arlen),
    .m_addr(m_araddr),
    .m_size(m_arsize),
    .m_burst(m_arburst),
    .m_lock(m_arlock),
    .m_prot(m_arprot),
    .m_cache(m_arcache),
    .m_valid(m_arvalid),
    .m_ready(m_arready),

    // Write  Data Channel
    .m_wdata (), // ASO-UNUSED_OUTPUT: port not used
    .m_wstrb (), // ASO-UNUSED_OUTPUT: port not used
    .m_wlast (), // ASO-UNUSED_OUTPUT: port not used
    .m_wvalid(), // ASO-UNUSED_OUTPUT: port not used
    .m_wready(zero_array),

    // Resp Data Channel
    .m_rid(m_rid),
    .m_rdata(m_rdata),
    .m_rresp(m_rresp),
    .m_rlast(m_rlast),
    .m_rvalid(m_rvalid),
    .m_rready(m_rready)
  );


endmodule

`endif  // _SIMPLE_AXI_DEMUX_SV_
