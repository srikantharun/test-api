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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_amem_data_match.sv#1 $
// -------------------------------------------------------------------------
// Description:
//             Memory data match generator

 module DWC_ddr_umctl2_amem_data_match
 #(
   parameter ADDR_WIDTH    = 3,
   parameter COUNT_WIDTH   = 4,
   parameter DEPTH         = 8,
   parameter DATA_WIDTH    = 4
 )
 (
   input [ADDR_WIDTH-1:0]        wr_addr, // input write address
   input [COUNT_WIDTH-1:0]       wcount, // input write count
   input [DATA_WIDTH-1:0]        data_in, // input data
   input [DATA_WIDTH*DEPTH-1:0]  mem_in, // input memory array
   output [DEPTH-1:0]            valid // output valid vector
 );

   //---------------------------------------------------------------------------
   // Local Parameters 
   //---------------------------------------------------------------------------

   localparam COMP_WIDTH   = (ADDR_WIDTH > COUNT_WIDTH)  ? ADDR_WIDTH : COUNT_WIDTH;

   //---------------------------------------------------------------------------
   // Internal Signals
   //---------------------------------------------------------------------------

   wire  [COMP_WIDTH-1:0]   addr, wcnt;
   wire  [COMP_WIDTH-1+1:0] addr_cnt;
   wire  [DEPTH-1:0]        data_valid;
   wire  [DATA_WIDTH-1:0]   data2comp;
   wire [DEPTH-1:0]         data_matched;
   wire                     cnt_gt_addr;
   wire  [COMP_WIDTH-1+1:0] cnt_addr;
   wire  [DEPTH-1:0]        valid_tmp_addr, valid_tmp_cnt, valid_tmp_indx1, valid_tmp_indx, valid_addr_cnt, valid_cnt_addr;
   wire  [DEPTH-1:0]        cmp_1;

   wire [ADDR_WIDTH-1:0]    addr_in;

   wire [DATA_WIDTH-1:0]    mem [0 : DEPTH-1];

   genvar n;

   //---------------------------------------------------------------------------
   // Main Module
   //---------------------------------------------------------------------------

   // input assign
   assign addr_in    = wr_addr;
   assign data2comp  = data_in;
   
   generate
      for (n=0 ; n<DEPTH ; n=n+1) begin: MEM_assign
         assign mem[n] = mem_in[n*DATA_WIDTH +: DATA_WIDTH];
      end
   endgenerate

   assign cmp_1      = {{(DEPTH-1){1'b0}},1'b1};

   // assign the final valid
   assign valid = data_matched & data_valid;

   generate
      if (ADDR_WIDTH > COUNT_WIDTH) begin: addr_gt_wcnt
         assign addr    = addr_in;
         assign wcnt    = {{(COMP_WIDTH-COUNT_WIDTH){1'b0}},wcount};
      end else if (ADDR_WIDTH < COUNT_WIDTH) begin: wcnt_gt_addr
         assign addr    = {{(COMP_WIDTH-ADDR_WIDTH){1'b0}},addr_in};
         assign wcnt    = wcount;
      end else begin: addr_eq_wcnt
         assign addr    = addr_in;
         assign wcnt    = wcount;
      end
   endgenerate

   // compare the memory content with the data to compare and generate match vector
   generate
      for (n=0 ; n<DEPTH ; n=n+1) begin: COMP_mem
         // compare input against memory array
         assign data_matched[n]     = ~|(mem[n] ^ data2comp);
         // mirror the valid
         assign valid_tmp_indx[n]   = valid_tmp_indx1[DEPTH-1-n];
      end
   endgenerate

   assign addr_cnt       = {1'b0,addr} - {1'b0,wcnt};
   assign cnt_addr       = {1'b0,wcnt} - {1'b0,addr};
   assign cnt_gt_addr    = addr_cnt[COMP_WIDTH];

   assign valid_tmp_addr  = (cmp_1 << addr) - 1;
   assign valid_tmp_cnt   = (cmp_1 << addr_cnt) - 1;
   assign valid_tmp_indx1 = (cmp_1 << cnt_addr) - 1;

   assign valid_addr_cnt = valid_tmp_addr & ~valid_tmp_cnt;
   assign valid_cnt_addr = valid_tmp_addr | valid_tmp_indx;

   // valid locations in the FIFO (PUSH side)
   assign data_valid  = (cnt_gt_addr) ? valid_cnt_addr : valid_addr_cnt;

 endmodule
