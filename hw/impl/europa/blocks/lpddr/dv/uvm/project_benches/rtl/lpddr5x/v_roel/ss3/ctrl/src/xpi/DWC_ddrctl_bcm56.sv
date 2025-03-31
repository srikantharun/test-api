
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
// Description : DWC_ddrctl_bcm56.v Verilog module for DWC_ddrctl
//
// DesignWare IP ID: 7cf4c8c0
//
////////////////////////////////////////////////////////////////////////////////






module DWC_ddrctl_bcm56 (
  clk,         // Write clock input
  rst_n,       // write domain active low asynch. reset
  init_n,      // write domain active low synch. reset
  wr_n,        // acive low write enable
  wr_addr,     // Write address input
  wr_data,     // Write data input

  mem_out      // Memory array output
);

// spyglass disable_block W146
// SMD: Explicit named association is recommended in instance references
// SJ: Current release uses ordered list for parameters, the design is checked and verified without errors

parameter integer WIDTH = 8;      // RANGE 1 to 2048
parameter integer DEPTH = 4;      // RANGE 2 to 2048
parameter integer ADDR_WIDTH = 2; // RANGE 1 to 10
parameter integer MEM_MODE = 1;   // RANGE 0 to 7

input                       clk;
input                       rst_n;
input                       init_n;
input                       wr_n;
input  [ADDR_WIDTH-1 : 0]   wr_addr;
input  [WIDTH-1 : 0]        wr_data;

output [WIDTH*DEPTH-1 : 0]  mem_out;

reg [WIDTH*DEPTH-1 : 0]     mem_out;
reg [WIDTH*DEPTH-1 : 0]     mem_array_nxt;

wire [ADDR_WIDTH-1 : 0]     wr_addr_array;
wire                        wr_array;
wire [WIDTH-1 : 0]          wr_data_array;

// spyglass disable_block STARC-2.3.4.3
// SMD: A flip-flop should have an asynchronous set or an asynchronous reset
// SJ: This module can be specifically configured/implemented with only a synchronous reset or no resets at all.
// spyglass disable_block W415a
// SMD: Signal may be multiply assigned (beside initialization) in the same scope
// SJ: The design checked and verified that not any one of a single bit of the bus is assigned more than once beside initialization or the multiple assignments are intentional.

always @ (posedge clk or negedge rst_n) begin : clk_regs_PROC
  if (rst_n == 1'b0)
    mem_out <= {WIDTH*DEPTH{1'b0}};
  else if (init_n == 1'b0)
    mem_out <= {WIDTH*DEPTH{1'b0}};
  else if (wr_array == 1'b1)
    mem_out <= mem_array_nxt;
end

always @ (mem_out or wr_addr_array or wr_data_array) begin : mk_next_mem_PROC
  integer i, j, k;
  mem_array_nxt = mem_out;

  k = 0;
// synthesis loop_limit 8000
  for (i=0 ; i < DEPTH ; i=i+1) begin
    if ($unsigned(i) == {{(32-ADDR_WIDTH){1'b0}},wr_addr_array}) begin
// synthesis loop_limit 8000
      for (j=0 ; j < WIDTH ; j=j+1)
        mem_array_nxt[k+j] = wr_data_array[j];
    end

    k = k + WIDTH;
  end
end
// spyglass enable_block W415a


generate
  if ((MEM_MODE & 4) == 4) begin : GEN_MMBT2_1
    reg [ADDR_WIDTH-1 : 0] wr_addr_retimed;
    reg [WIDTH-1 : 0] wr_data_retimed;
    reg wr_retimed;

    always @ (posedge clk or negedge rst_n) begin : mmbt2_1_PROC
      if (rst_n == 1'b0) begin
        wr_addr_retimed <= {ADDR_WIDTH{1'b0}};
        wr_data_retimed <= {WIDTH{1'b0}};
        wr_retimed <= 1'b0;
      end else if (init_n == 1'b0) begin
        wr_addr_retimed <= {ADDR_WIDTH{1'b0}};
        wr_data_retimed <= {WIDTH{1'b0}};
        wr_retimed <= 1'b0;
      end else begin
        if (wr_n == 1'b0) begin
          wr_addr_retimed <= wr_addr;
          wr_data_retimed <= wr_data;
        end
        wr_retimed <= ~wr_n;
      end
    end

    assign wr_addr_array = wr_addr_retimed;
    assign wr_array = wr_retimed;
    assign wr_data_array = wr_data_retimed;
  end else begin : GEN_MMBT2_0
    assign wr_addr_array = wr_addr;
    assign wr_array = ~wr_n;
    assign wr_data_array = wr_data;
  end
endgenerate
// spyglass enable_block STARC-2.3.4.3

// spyglass enable_block W146
endmodule
