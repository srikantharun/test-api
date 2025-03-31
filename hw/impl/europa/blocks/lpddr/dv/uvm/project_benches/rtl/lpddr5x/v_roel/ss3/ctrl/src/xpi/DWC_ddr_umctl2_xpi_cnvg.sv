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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_xpi_cnvg.sv#2 $
// -------------------------------------------------------------------------
// Description:
//   uMCTL XPI Converger
//   In HBW mode, this module packs the dispersed data into Lower Half
//   In QBW mode, this module packs the dispersed data into Lowerst Quarter
//   In FBW mode this is feed through
module DWC_ddr_umctl2_xpi_cnvg
 #(
        parameter ENIF_DATAW   = 512, // HIF interface data width
        parameter NAB          = 3,   // FREQ Ratio mode 
        parameter XBW_CHK      = 64, //Should be MEMC_DRAM_DATAW for all instances
        parameter M_DW         = 64   // DRAM Data width
        
 )
 ( 
   input [ENIF_DATAW-1:0]   in_data,
   input [1:0]              bus_width,
      
   output reg [ENIF_DATAW-1:0]  out_data   

  );

    localparam FBW           = 2'b00;
    localparam HBW           = 2'b01;
    localparam QBW           = 2'b10;
    localparam M_DW_HBW      = (XBW_CHK > 8)  ? M_DW/2 : M_DW;
    localparam M_DW_QBW      = (XBW_CHK > 16) ? M_DW/4 : M_DW_HBW;
    localparam M_SEG         = (1 << NAB);    
      
   
   int i;
   
   always@(*) begin : converger_block  
     if (bus_width==HBW) begin  
       out_data = {ENIF_DATAW{1'b0}};
       
       for (i=0; i<M_SEG;i++) begin
         out_data[(i*M_DW_HBW) +: M_DW_HBW] = in_data[(i*M_DW) +: M_DW_HBW] ;
       end   
     end else if (bus_width == QBW) begin //QBW
       out_data = {ENIF_DATAW{1'b0}};
              
       for (i=0; i<M_SEG; i++) begin
         out_data[(i*M_DW_QBW) +: M_DW_QBW] = in_data[(i*M_DW) +: M_DW_QBW] ;
       end    
     end else begin // (bus_width==FBW)
       out_data = in_data;  
     end  
   end //converger_block

        
endmodule
