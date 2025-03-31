
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

//
// Description : DWC_ddrctl_bcm65.v Verilog module for DWC_ddrctl
//
// DesignWare IP ID: aaefdd18
//
////////////////////////////////////////////////////////////////////////////////


module DWC_ddrctl_bcm65(
    clk,
    rst_n,
    init_n,
    push_req_n,
    pop_req_n,
    data_in,
    empty,
    almost_empty,
    half_full,
    almost_full,
    full,
    error,
    data_out
);

// spyglass disable_block W146
// SMD: Explicit named association is recommended in instance references
// SJ: Current release uses ordered list for parameters, the design is checked and verified without errors

  parameter integer WIDTH           = 8;    // RANGE 1 TO 2048
  parameter integer DEPTH           = 4;    // RANGE 2 TO 1024
  parameter integer AE_LEVEL        = 1;    // RANGE 0 TO DEPTH-1
  parameter integer AF_LEVEL        = 1;    // RANGE 0 TO DEPTH-1
  parameter integer ERR_MODE        = 0;    // RANGE 0 TO 2
  parameter integer RST_MODE        = 0;    // RANGE 0 TO 1
  parameter integer ADDR_WIDTH      = 2;    // RANGE 1 TO 10

  input                     clk;            // clock input
  input                     rst_n;          // active low async. reset
  input                     init_n;         // active low sync. reset (FIFO flush)
  input                     push_req_n;     // active low push request
  input                     pop_req_n;      // active low pop request
  input  [WIDTH-1 : 0]      data_in;        // FIFO input data bus
  output                    empty;          // empty status flag
  output                    almost_empty;   // almost empty status flag
  output                    half_full;      // half full status flag
  output                    almost_full;    // almost full status flag
  output                    full;           // full status flag
  output                    error;          // error status flag
  output [WIDTH-1 : 0]      data_out;       // FIFO outptu data bus

  wire                      ram_async_rst_n;
  wire   [ADDR_WIDTH-1 : 0] ram_rd_addr, ram_wr_addr;
  wire                      ram_we_n;

 wire [ADDR_WIDTH-1 : 0] ae_level_i;
 wire [ADDR_WIDTH-1 : 0] af_thresh_i;

  assign ae_level_i = $unsigned(AE_LEVEL);
  assign af_thresh_i = $unsigned(DEPTH - AF_LEVEL);

generate
  if (RST_MODE == 0) begin : GEN_RM_EQ_0
    assign ram_async_rst_n = rst_n;
  end else begin : GEN_RM_NE_0
    assign ram_async_rst_n = 1'b1;
  end
endgenerate


  DWC_ddrctl_bcm06
   #(DEPTH, ERR_MODE, ADDR_WIDTH) U_FIFO_CTL(
    .clk(clk),
    .rst_n(rst_n),
    .init_n(init_n),
    .push_req_n(push_req_n),
    .pop_req_n(pop_req_n),
    .ae_level(ae_level_i[ADDR_WIDTH-1:0]),
    .af_thresh(af_thresh_i[ADDR_WIDTH-1:0]),
    .we_n(ram_we_n),
    .empty(empty),
    .almost_empty(almost_empty),
    .half_full(half_full),
    .almost_full(almost_full),
    .full(full),
    .error(error),
    .wr_addr(ram_wr_addr),
    .rd_addr(ram_rd_addr),
// spyglass disable_block W287b
// SMD: An output port of module or gate instance is not connected
// SJ: The following port(s) of this instance are intentionally unconnected.
// spyglass disable_block UnloadedOutTerm-ML
// SMD: Detected unloaded(unconnected) output terminal
// SJ: The following signal(s) are emanating from instance output port(s) that are intentionally not used. So, disable SpyGlass from reporting this warning. This instance design in which the signal(s) are connected is shared by other module(s) that may use these port(s) and signal(s) emanating from them.
    .wrd_count(),
    .nxt_empty_n(),
    .nxt_full(),
    .nxt_error()
// spyglass enable_block W287b
// spyglass enable_block UnloadedOutTerm-ML
  );

  DWC_ddrctl_bcm57
   #(WIDTH, DEPTH, 0, ADDR_WIDTH) U_FIFO_MEM(
    .clk(clk),
    .rst_n(ram_async_rst_n),
    .wr_n(ram_we_n),
    .rd_addr(ram_rd_addr),
    .wr_addr(ram_wr_addr),
    .data_in(data_in),
    .data_out(data_out)
  );

// spyglass enable_block W146
endmodule
