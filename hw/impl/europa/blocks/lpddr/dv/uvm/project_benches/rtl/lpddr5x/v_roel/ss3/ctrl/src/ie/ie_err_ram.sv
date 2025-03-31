//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ie/ie_err_ram.sv#2 $
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

// ----------------------------------------------------------------------------
//                              DDR Controller
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
module ie_err_ram
#(
    parameter WIDTH      = 64
   ,parameter DEPTH      = 32
   ,parameter ADDR_BITS  = 5
   ,parameter RD_CLR     = 0      //1: the mask will be clear after read. 0: no clear after read.
   ,parameter REGOUT     = 1'b0   //1: rdata valid in the next cycle of raddr, like RAM;
                                  //0: rdata valid in the same cycle with raddr, like ROM;

)
(  
    input                    clk       
   ,input                    rstn      
   ,input                    wr        
   ,input  [WIDTH-1:0]       wdata     
   ,input  [ADDR_BITS-1:0]   waddr     
   ,input                    rd    //if RD_CLR is 1, rd will clear the rdata_mask_n[raddr], if RD_CLR is 0, rd is useless.
   ,input  [ADDR_BITS-1:0]   raddr     
   ,output [WIDTH-1:0]       rdata     

);

//------------------------------ LOCAL PARAMETERS ------------------------------------

reg [WIDTH-1:0]   err_ram        [0:DEPTH-1];

reg [WIDTH-1:0]   i_rdata;
//-----------------------------------------------------------
// Write Side
//-----------------------------------------------------------
integer i;

generate 
   if(RD_CLR==1) begin: RD_CLR_1
      reg [WIDTH-1:0] err_ram_nxt [0:DEPTH-1];
      always @ (*) begin
         for (i=0; i<DEPTH; i=i+1) begin
            err_ram_nxt[i] = err_ram[i];
            if(wr & waddr==i)
               err_ram_nxt[i] = wdata;
            if(rd & raddr==i)  //read and write access the same address, the new mask will put to rdata_mask_n and clear the mask by read.
               err_ram_nxt[i] = {WIDTH{1'b0}};
         end
      end

      always @ (posedge clk or negedge rstn) begin
         if(!rstn) begin
            for (i=0; i<DEPTH; i=i+1) begin
               err_ram[i] <= {WIDTH{1'b0}};
            end
         end else begin
            for (i=0; i<DEPTH; i=i+1) begin
               err_ram[i] <= err_ram_nxt[i];
            end
         end
      end
   end else begin: RD_CLR_0
      always @ (posedge clk or negedge rstn) begin
         if(!rstn) begin
            for (i=0; i<DEPTH; i=i+1) begin
               err_ram[i] <= {WIDTH{1'b0}};
            end
         end else if(wr) begin
            err_ram[waddr] <= wdata;
         end
      end
   end
endgenerate

//-----------------------------------------------------------
// Read Side
//-----------------------------------------------------------
always @ (*) begin
   i_rdata={WIDTH{1'b0}};
   if(wr && (waddr==raddr)) begin
      i_rdata = wdata;
   end else begin
           for (i=0;i<DEPTH;i++) begin
           if($unsigned(i)==raddr[ADDR_BITS-1:0]) 
              i_rdata = err_ram[i];
           end
   end
end

// select Register out or not
generate
   if(REGOUT==1) begin : REG_OUT_1
      reg [WIDTH-1:0]   r_rdata;

      always @ (posedge clk or negedge rstn) begin
         if(!rstn) begin
            r_rdata        <= {WIDTH{1'b0}};
         end else begin
            r_rdata        <= i_rdata;
         end
      end

      assign rdata        = r_rdata;
   end else begin : REG_OUT_0
      assign rdata        = i_rdata;
   end
endgenerate



endmodule
