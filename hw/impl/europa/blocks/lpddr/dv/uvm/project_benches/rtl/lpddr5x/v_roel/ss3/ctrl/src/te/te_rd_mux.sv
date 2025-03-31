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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_rd_mux.sv#2 $
// -------------------------------------------------------------------------
// Description:
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_rd_mux (
  in_port,
  sel,
  out_port
);

input   [`MEMC_NO_OF_RD_ENTRY -1:0]   in_port;
input   [`MEMC_RDCMD_ENTRY_BITS -1:0] sel;
output                                out_port;

wire out_port; 
assign out_port = in_port [sel [`MEMC_RDCMD_ENTRY_BITS -1:0]];

endmodule // te_rd_mux
