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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/apb/DWC_ddr_umctl2_bitsync.sv#4 $
// -------------------------------------------------------------------------
// Description:
//
`include "DWC_ddrctl_all_defs.svh"
module DWC_ddr_umctl2_bitsync
  #(parameter BCM_SYNC_TYPE = 2,
    parameter BCM_VERIF_EN  = 0)
   (input          clk_d,
    input          rst_d_n,
      //ccx_tgl : U_bitsync_dis_regs_ecc_syndrome ; data_s; ; P80001562-175292: legacy tb toggles this signal but only when power removal occurs. AXI config don't run legacy power removal.
      //ccx_tgl : U_bitsync_dis_regs_ecc_syndrome ; data_d; ; P80001562-175292: legacy tb toggles this signal but only when power removal occurs. AXI config don't run legacy power removal.
    input          data_s,
    output         data_d);

   localparam WIDTH=1'b1;


      
         DWC_ddrctl_bcm21
         
           #(.WIDTH       (WIDTH),
             .F_SYNC_TYPE (BCM_SYNC_TYPE),
             .VERIF_EN    (BCM_VERIF_EN))
         U_bcm21
           (.clk_d    (clk_d),
            .rst_d_n  (rst_d_n),
            .data_s   (data_s),
            .data_d   (data_d)
            );
            
   
endmodule
