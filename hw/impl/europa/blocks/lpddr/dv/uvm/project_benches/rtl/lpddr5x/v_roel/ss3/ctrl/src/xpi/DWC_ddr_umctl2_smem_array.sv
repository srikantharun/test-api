//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_smem_array.sv#3 $
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

/******************************************************************************
 *                                                                            *
 * DESCRIPTION: memory Array with valid vector                                *
 *                                                                            *
 *****************************************************************************/

`include "DWC_ddrctl_all_defs.svh"
module DWC_ddr_umctl2_smem_array( 
    clk,
    rst_n,
    init_n,
    push_req_n,
    pop_req_n,
    data_in,
    wcount,
    empty, 
    almost_empty,
    half_full,
    almost_full,
    full,
    error,
    valid,
    data_out
    );
parameter WIDTH  = 8;                   // RANGE 1 TO 256
parameter COUNT_WIDTH = 4;
parameter DEPTH  = 4;                   // RANGE 2 TO 256
parameter AE_LEVEL = 1;                 // RANGE 0 TO 255
parameter AF_LEVEL = 1;                 // RANGE 0 TO 255
parameter ERR_MODE  =  0 ;              // RANGE 0 TO 2
parameter RST_MODE  =  0 ;              // RANGE 0 TO 1
parameter ADDR_WIDTH = 2 ;              // RANGE 1 TO 8

 input                  clk;            // clock input
 input                  rst_n;          // active low async. reset
 input                  init_n;         // active low sync. reset (FIFO flush)
 input                  push_req_n;     // active low push request
 input                  pop_req_n;      // active low pop request
 input [WIDTH-1 : 0]    data_in;        // FIFO input data bus
 input [COUNT_WIDTH-1:0]wcount;
 output                 empty;          // empty status flag
 output                 almost_empty;   // almost empty status flag
 output                 half_full;      // half full status flag
 output                 almost_full;    // almost full status flag
 output                 full;           // full status flag
 output                 error;          // error status flag

 output [DEPTH-1:0]     valid;
 output [WIDTH-1 : 0 ]  data_out;       // FIFO outptu data bus

 wire                ram_async_rst_n, ram_sync_rst_n;
 wire [ADDR_WIDTH-1 : 0] ram_rd_addr, ram_wr_addr;
 wire [31:00] ae_level_i;
 wire [31:00] af_thresh_i; 
 wire ram_we_n;
 
 wire [ADDR_WIDTH-1 : 0] wrd_count_unconnected;
 wire nxt_empty_n_unconnected;
 wire nxt_full_unconnected;
 wire nxt_error_unconnected;
       
  assign ae_level_i = AE_LEVEL;
  assign af_thresh_i = DEPTH - AF_LEVEL; 

generate
  if (RST_MODE == 0) begin : GEN_RM_EQ_0
    assign ram_async_rst_n = rst_n;
    assign ram_sync_rst_n  = init_n;
  end else begin : GEN_RM_NE_0
    assign ram_async_rst_n = 1'b1;
    assign ram_sync_rst_n  = 1'b1;
  end
endgenerate
  

  DWC_ddrctl_bcm06
   #(.DEPTH(DEPTH), .ERR_MODE(ERR_MODE), .ADDR_WIDTH(ADDR_WIDTH)) U_FIFO_CTL(
                        .clk(clk),
                        .rst_n(rst_n),
                        .init_n(init_n),
                        .push_req_n(push_req_n),
                        .pop_req_n(pop_req_n),
                        .ae_level(ae_level_i[ADDR_WIDTH-1:0]),
                        .af_thresh(af_thresh_i[ADDR_WIDTH-1:0]),
                        .empty(empty),
                        .almost_empty(almost_empty),
                        .half_full(half_full),
                        .almost_full(almost_full),
                        .full(full),
                        .error(error),
                        .we_n(ram_we_n),
                        .wr_addr(ram_wr_addr),
                        .rd_addr(ram_rd_addr),
                        .wrd_count(wrd_count_unconnected),
                        .nxt_empty_n(nxt_empty_n_unconnected),
                        .nxt_full(nxt_full_unconnected),
                        .nxt_error(nxt_error_unconnected)
                        );
    
  DWC_ddr_umctl2_amem_array
   #(.DATA_WIDTH(WIDTH), .COUNT_WIDTH(COUNT_WIDTH), .DEPTH(DEPTH), .MEM_MODE(0), .ADDR_WIDTH(ADDR_WIDTH)) U_FIFO_MEM( 
                        .clk        (clk),
                        .rst_n      (ram_async_rst_n),
                        .init_n     (ram_sync_rst_n),                                       
                        .wr_n       (ram_we_n),
                        .rd_addr    (ram_rd_addr),
                        .wr_addr    (ram_wr_addr),
                        .wcount     (wcount),
                        .valid      (valid),
                        .data_in    (data_in),
                        .data_out   (data_out)
                        );


endmodule
