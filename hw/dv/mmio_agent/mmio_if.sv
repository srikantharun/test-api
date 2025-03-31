`ifndef MMIO_IF_SV
`define MMIO_IF_SV

// ADDR_WIDTH/DATA_WIDTH changes according to dmc/rvv type connection
interface mmio_if#(int DATA_WIDTH = 512, int ADDR_WIDTH = 22) (input clk, input rst);

  typedef struct packed {
    logic[ADDR_WIDTH-1:0]  addr;
    logic        we;  // write enable - if this is 1, it means we're requesting a write
    logic[(DATA_WIDTH+7)/8:0]        wbe;  // write strobe - which part of the data we want to write
    logic[DATA_WIDTH-1:0] data;
    logic        valid;
    logic        rsp_ready;
  } mmio_req_t;

  typedef struct packed {
    logic[DATA_WIDTH-1:0] data;
    logic        error;
    logic        ack;
    logic        ready;
    logic        rsp_ready;
  } mmio_resp_t;

  mmio_req_t  req;
  mmio_resp_t rsp;

  clocking mon @(posedge clk);
    input  req;
    input  rsp;
  endclocking

  clocking drv @(posedge clk);
    output req;
    input  rsp;
  endclocking

endinterface : mmio_if

`endif // MMIO_IF_SV

