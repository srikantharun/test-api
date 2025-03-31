
package alg_amba_vip_interfaces;
endpackage

interface al_vip_apb_if #(parameter ADDR = 20) (
  input  logic rstn,
  input  logic clk
);

  logic [ADDR - 1:0]  addr;
  logic         enable;
  logic [31:0]  rdata;
  logic         ready;
  logic         sel;
  logic         slverr;
  logic [31:0]  wdata;
  logic         write;

  modport slavemod (
    input  rstn,
    input  clk,
    input  addr,
    input  enable,
    output rdata,
    output ready,
    input  sel,
    output slverr,
    input  wdata,
    input  write
  );

  modport mastermod (
    input  rstn,
    input  clk,
    output addr,
    output enable,
    input  rdata,
    input  ready,
    output sel,
    input  slverr,
    output wdata,
    output write
  );
endinterface

interface al_vip_axi_if #(parameter WIDTH = 128) (
  input logic clk,
  input logic rstn
);

  logic [63:0]  araddr;
  logic [1:0]   arburst;
  logic [4:0]   arid;
  logic [7:0]   arlen;
  logic         arready;
  logic [2:0]   arsize;
  logic         arvalid;
  logic [63:0]  awaddr;
  logic [1:0]   awburst;
  logic [4:0]   awid;
  logic [7:0]   awlen;
  logic         awready;
  logic [2:0]   awsize;
  logic         awvalid;
  logic         bready;
  logic         bvalid;
  logic [1:0]   bresp;
  logic [4:0]   bid;
  logic [WIDTH-1:0]     rdata;
  logic [4:0]   rid;
  logic         rlast;
  logic         rready;
  logic         rvalid;
  logic [1:0]   rresp;
  logic [WIDTH-1:0]     wdata;
  logic [(WIDTH/8)-1:0] wstrb;
  logic         wlast;
  logic         wready;
  logic         wvalid;

  modport mastermod (
    input  clk,
    input  rstn,
    output araddr,
    output arburst,
    output arid,
    output arlen,
    input  arready,
    output arsize,
    output arvalid,
    output awaddr,
    output awburst,
    output awid,
    output awlen,
    input  awready,
    output awsize,
    output awvalid,
    output bready,
    input  bvalid,
    input  bresp,
    input  bid,
    input  rdata,
    input  rid,
    input  rlast,
    output rready,
    input  rvalid,
    input  rresp,
    output wdata,
    output wstrb,
    output wlast,
    input  wready,
    output wvalid
  );

  modport slavemod (
    input  clk,
    input  rstn,
    input  araddr,
    input  arburst,
    input  arid,
    input  arlen,
    output arready,
    input  arsize,
    input  arvalid,
    input  awaddr,
    input  awburst,
    input  awid,
    input  awlen,
    output awready,
    input  awsize,
    input  awvalid,
    input  bready,
    output bvalid,
    output bresp,
    output bid,
    output rdata,
    output rid,
    output rlast,
    input  rready,
    output rvalid,
    output rresp,
    input  wdata,
    input  wstrb,
    input  wlast,
    output wready,
    input  wvalid
  );
endinterface

