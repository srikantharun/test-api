// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AXIS interface
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef AXIS_INTF_SV
`define AXIS_INTF_SV

interface axis_intf #(
  parameter DW = 512
);
  wire            clk;
  wire            rst_n;
  wire            vld;
  wire            rdy;
  wire [  DW-1:0] data;
  wire [DW/8-1:0] strb;
  wire            last;

  // AXI Stream Master Clocking Block 
  clocking mt_cb @(posedge clk);
    default input #0.2ns output #0.6ns;

    output vld;
    output data;
    output strb;
    output last;
    input rdy;

  endclocking : mt_cb

  // AXI Stream Slave Clocking Block 
  clocking sl_cb @(posedge clk);
    default input #0.2ns output #0.6ns;

    input vld;
    input data;
    input strb;
    input last;
    output rdy;

  endclocking : sl_cb

  // AXI Stream Monitor Clocking Block 
  clocking mon_cb @(posedge clk);
    default input #0.2ns output #0.2ns;

    input vld;
    input data;
    input strb;
    input last;
    input rdy;

  endclocking : mon_cb

endinterface : axis_intf

`endif  // AXIS_INTF_SV
