// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

// -------------------------------------------------------------------------
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_amem_array.sv#2 $
// -------------------------------------------------------------------------
// Description:
//             Memory Array with valid vector

  module DWC_ddr_umctl2_amem_array (
  clk,
  rst_n,
  init_n,
  wr_n,
  data_in,
  wr_addr,
  rd_addr,
  wcount,
  valid,
  data_out
  );

   parameter integer DATA_WIDTH = 4;  // RANGE 1 to 256
   parameter COUNT_WIDTH = 4;
   parameter DEPTH = 8;       // RANGE 2 to 256
   parameter MEM_MODE = 0;    // RANGE 0 to 3
   parameter ADDR_WIDTH = 3;  // RANGE 1 to 8

   input       clk;     // clock input
   input       rst_n;   // active low async. reset
   input       init_n;  // active low sync. reset
   input       wr_n;    // active low RAM write enable
   input [DATA_WIDTH-1:0]  data_in;  // RAM write data input bus
   input [ADDR_WIDTH-1:0]  wr_addr;  // RAM write address bus
   input [ADDR_WIDTH-1:0]  rd_addr;  // RAM read address bus
   input [COUNT_WIDTH-1:0] wcount;

   output [DEPTH-1:0]      valid; // data in memory matches specific value

   output [DATA_WIDTH-1:0]  data_out;  // RAM read data output bus


   wire [DATA_WIDTH*DEPTH-1:0]  mem;
  
  DWC_ddrctl_bcm56
   #(
    .WIDTH(DATA_WIDTH), .DEPTH(DEPTH), .ADDR_WIDTH(ADDR_WIDTH), .MEM_MODE(MEM_MODE)) U1 (
    .clk           (clk),            // Read clock input
    .rst_n         (rst_n),          // read domain active low asynch. reset
    .init_n        (init_n),         // read domain active low synch. reset
    .wr_n          (wr_n),           // active low write enable
    .wr_addr       (wr_addr),        // Write address input
    .wr_data       (data_in),        // Write data input
    .mem_out       (mem)        // Memory array output
    );
    
  wire             data_avail_unused;
  wire             rd_n;
  assign           rd_n = 1'b0;

  DWC_ddrctl_bcm50
   #(
    .WIDTH(DATA_WIDTH), .DEPTH(DEPTH), .ADDR_WIDTH(ADDR_WIDTH), .MEM_MODE(MEM_MODE)) U2 (
    .clk           (clk),            // Read clock input
    .rst_n         (rst_n),          // read domain active low asynch. reset
    .init_n        (init_n),         // read domain active low synch. reset
    .rd_n          (rd_n),           // active low read enable
    .rd_addr       (rd_addr),        // Read address input
    .mem_in        (mem),            // Memory array input
    .data_avail    (data_avail_unused), // Read data arrival status output
    .rd_data       (data_out)        // Read data output
    );
    
  DWC_ddr_umctl2_amem_data_match
   #(
    .ADDR_WIDTH(ADDR_WIDTH), .COUNT_WIDTH(COUNT_WIDTH), .DEPTH(DEPTH), .DATA_WIDTH(DATA_WIDTH)) U3 (
    .wr_addr       (wr_addr),        // input write address
    .wcount        (wcount),         // input write count
    .data_in       (data_in),        // input data
    .mem_in        (mem),            // input memory array
    .valid         (valid)           // output valid vector
    );
    
endmodule
