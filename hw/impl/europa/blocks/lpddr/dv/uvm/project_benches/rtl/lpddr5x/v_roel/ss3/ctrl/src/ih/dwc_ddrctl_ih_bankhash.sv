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
// RCS information:
// ---    $Revision: #1 $
// -------------------------------------------------------------------------
// Description:
//   BankHash module
//
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module dwc_ddrctl_ih_bankhash
 #(
  parameter BANK_WIDTH = `MEMC_BANK_BITS,
  parameter BG_WIDTH   = `MEMC_BG_BITS,
  parameter ROW_WIDTH  = `MEMC_PAGE_BITS, 
  parameter MUX_SEL_WIDTH = 1
  )
  (     input  [ROW_WIDTH-1:0]                      am_row, 
        input  [`MEMC_BG_BANK_BITS-1:0]             am_bg_bank,
        input  [MUX_SEL_WIDTH-1:0]                  am_mux_sel,
        output logic [`MEMC_BG_BANK_BITS-1:0]       bh_bg_bank
  );
    
      //am_mux_sel is used to determine the row to bank bit mapping. 
      //In DDR54 configurations, there can be 3 combinations. 3 Bank bits, 4 bank bits and 5 bank bits. 
      // Respectively, number of row bits per bank bit would be 6, 5, 4. 
      // Respectively, value of am_mux_sel =  2'b10, 2'b01, 2'b00

      //In DDR54 configurations, there can be 2 combinations. 3 Bank bits and 4 bank bits 
      // Respectively, number of row bits per bank bit would be 6, 5
      // Respectively, value of am_mux_sel = 1'b0, 1'b1

      //maximum number of row bits per bank bit
      parameter ROW_BITS_PER_BANK_WIDTH    = 6; 

      logic [ROW_BITS_PER_BANK_WIDTH-1:0]   row_bits_per_bank[`MEMC_BG_BANK_BITS-1:0]; 


      
 
    always_comb begin 
        if (am_mux_sel) begin
          row_bits_per_bank[0] = {1'b0, am_row[16], am_row[12], am_row[8],   am_row[4], am_row[0]}; 
          row_bits_per_bank[1] = {1'b0, am_row[17], am_row[13], am_row[9],   am_row[5], am_row[1]}; 
          row_bits_per_bank[2] = {1'b0, 1'b0,       am_row[14], am_row[10],  am_row[6], am_row[2]}; 
          row_bits_per_bank[3] = {1'b0, 1'b0,       am_row[15], am_row[11],  am_row[7], am_row[3]}; 
        end
        else begin
          row_bits_per_bank[0] = {am_row[15], am_row[12], am_row[9], am_row[6], am_row[3],am_row[0]}; 
          row_bits_per_bank[1] = {am_row[16], am_row[13], am_row[10],am_row[7], am_row[4],am_row[1]}; 
          row_bits_per_bank[2] = {am_row[17], am_row[14], am_row[11],am_row[8], am_row[5],am_row[2]}; 
          row_bits_per_bank[3] = 6'b00_0000; 
        end

    end //always_comb

    always_comb begin
      for (int i = 0; i < `MEMC_BG_BANK_BITS; i++) begin
        bh_bg_bank[i] = (am_bg_bank[i] ^ (^row_bits_per_bank[i])); 
      end 
    end //always_comb

endmodule
