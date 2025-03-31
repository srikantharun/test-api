//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd_ie_rdata_merge.sv#1 $
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


`include "DWC_ddrctl_all_defs.svh"
module rd_ie_rdata_merge
#(
    parameter CORE_DATA_WIDTH       = `MEMC_DFI_DATA_WIDTH   // internal data width
   ,parameter DRAM_DATA_WIDTH       = `MEMC_DRAM_DATA_WIDTH  // SDRAM data width
)
(
   // Input
   input  [1:0]                        data_bus_width
  ,input  [CORE_DATA_WIDTH-1:0]        data     // write data read from write data RAM
   // Output
  ,output [CORE_DATA_WIDTH-1:0]        merged_rdata
);

   // Localparam
   localparam DATA_BEAT_NUM            = `MEMC_DFI_DATA_WIDTH/`MEMC_DRAM_DATA_WIDTH;
   localparam HALF_DRAM_DATA_WIDTH     = `MEMC_DRAM_DATA_WIDTH/2; // SDRAM BUS WIDTH in HBW mode
   localparam QUARTER_DRAM_DATA_WIDTH  = `MEMC_DRAM_DATA_WIDTH/4; // SDRAM BUS WIDTH in QBW mode

   // Wire
   wire [CORE_DATA_WIDTH-1:0]          full_bus_rdata;
   wire [(CORE_DATA_WIDTH/2)-1:0]      half_bus_rdata;
   
   assign full_bus_rdata = data;

   genvar i;
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * HALF_DRAM_DATA_WIDTH)' found in module 'rd_ie_rdata_merge'
//SJ: This coding style is acceptable and there is no plan to change it.
   // We will support MEMC_BURST_LENGTH_16 and MEMC_FREQ_RATIO_4 only.
   // Therefor, Number of SDRAM beat per 1 HIF beat will be always 8.
   generate
      for (i=0; i<DATA_BEAT_NUM; i=i+1) begin : MERGED_DATA_GEN
         assign half_bus_rdata[i*HALF_DRAM_DATA_WIDTH+:HALF_DRAM_DATA_WIDTH] = data[i*DRAM_DATA_WIDTH+:HALF_DRAM_DATA_WIDTH];
      end
   endgenerate
//spyglass enable_block SelfDeterminedExpr-ML

   assign merged_rdata = 
                            (data_bus_width == 2'b01) ? {{($bits(merged_rdata) - $bits(half_bus_rdata)){1'b0}},half_bus_rdata} : //HBW
                                                        full_bus_rdata; //FBW

endmodule
