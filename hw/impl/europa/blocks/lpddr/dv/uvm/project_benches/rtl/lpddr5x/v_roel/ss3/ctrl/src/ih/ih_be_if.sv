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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_be_if.sv#1 $
// -------------------------------------------------------------------------
// Description:
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module ih_be_if (
  ih_te_rd_valid,
  ih_te_hi_pri,
  te_gs_any_vpr_timed_out, 
  ih_gs_any_vpr_timed_out,
  ih_be_hi_pri_rd_xact
  );

// 2-bit read priority encoding
localparam         CMD_PRI_LPR    = `MEMC_CMD_PRI_LPR;
localparam         CMD_PRI_VPR    = `MEMC_CMD_PRI_VPR;
localparam         CMD_PRI_HPR    = `MEMC_CMD_PRI_HPR;
localparam         CMD_PRI_XVPR   = `MEMC_CMD_PRI_XVPR;

input  ih_te_rd_valid;
input  [1:0] ih_te_hi_pri;

input   te_gs_any_vpr_timed_out;
input   ih_gs_any_vpr_timed_out;

output  ih_be_hi_pri_rd_xact;
wire    ih_be_hi_pri_rd_xact;

// set the valid to bypass module high if the command is HPR
// block bypass access when there are any timed-out VPR commands - in IH or TE
assign  ih_be_hi_pri_rd_xact  = (ih_te_rd_valid) ? ((ih_te_hi_pri == CMD_PRI_HPR) 
                                                    & ~te_gs_any_vpr_timed_out & ~ih_gs_any_vpr_timed_out
                                                   ) : 1'b0;



endmodule
