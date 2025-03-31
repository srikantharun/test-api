// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: simple AXI interface
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _AXI_INTF_SV_
`define _AXI_INTF_SV_

interface axi_intf #(
    parameter int unsigned DW = 512,
    parameter int unsigned AW = 36,
    parameter int unsigned IDW = 9,
    parameter int unsigned BLW = 8
  );
  logic            clk;
  logic            rst_n;
  // Write Address Channel
  logic [ IDW-1:0] awid;
  logic [  AW-1:0] awaddr;
  logic [ BLW-1:0] awlen;
  logic [     2:0] awsize;
  logic [     1:0] awburst;
  logic            awlock;
  logic [     3:0] awcache;
  logic [     2:0] awprot;
  logic            awvalid;
  logic            awready;
  // Read Address Channel
  logic [ IDW-1:0] arid;
  logic [  AW-1:0] araddr;
  logic [ BLW-1:0] arlen;
  logic [     2:0] arsize;
  logic [     1:0] arburst;
  logic            arlock;
  logic [     3:0] arcache;
  logic [     2:0] arprot;
  logic            arvalid;
  logic            arready;
  // Write  Data Channel
  logic [  DW-1:0] wdata;
  logic [DW/8-1:0] wstrb;
  logic            wlast;
  logic            wvalid;
  logic            wready;
  // Read Data Channel
  logic [ IDW-1:0] rid;
  logic [  DW-1:0] rdata;
  logic [     1:0] rresp;
  logic            rlast;
  logic            rvalid;
  logic            rready;
  // Write Response Channel
  logic [ IDW-1:0] bid;
  logic [     1:0] bresp;
  logic            bvalid;
  logic            bready;

  semaphore wr_sema = new(1);
  semaphore rd_sema = new(1);

  clocking mt_cb @(posedge clk);
`ifdef GLS
    default input #200ps;
    default output #400ps;
`endif

    // Write Address Channel
    inout awid;
    inout awaddr;
    inout awlen;
    inout awsize;
    inout awburst;
    inout awlock;
    inout awcache;
    inout awprot;
    inout awvalid;
    input awready;
    // Read Address Channel
    inout arid;
    inout araddr;
    inout arlen;
    inout arsize;
    inout arburst;
    inout arlock;
    inout arcache;
    inout arprot;
    inout arvalid;
    input arready;
    // Write  Data Channel
    inout wdata;
    inout wstrb;
    inout wlast;
    inout wvalid;
    input wready;
    // Read Data Channel
    input rid;
    input rdata;
    input rresp;
    input rlast;
    input rvalid;
    inout rready;
    // Write Response Channel
    input bid;
    input bresp;
    input bvalid;
    inout bready;
  endclocking

  clocking sl_cb @(posedge clk);
`ifdef GLS
    default input #200ps;
    default output #400ps;
`endif

    // Write Address Channel
    input awid;
    input awaddr;
    input awlen;
    input awsize;
    input awburst;
    input awlock;
    input awcache;
    input awprot;
    input awvalid;
    inout awready;
    // Read Address Channel
    input arid;
    input araddr;
    input arlen;
    input arsize;
    input arburst;
    input arlock;
    input arcache;
    input arprot;
    input arvalid;
    inout arready;
    // Write  Data Channel
    input wdata;
    input wstrb;
    input wlast;
    input wvalid;
    inout wready;
    // Read Data Channel
    inout rid;
    inout rdata;
    inout rresp;
    inout rlast;
    inout rvalid;
    input rready;
    // Write Response Channel
    inout bid;
    inout bresp;
    inout bvalid;
    input bready;
  endclocking
endinterface

`endif  //_AXI_INTF_SV_
