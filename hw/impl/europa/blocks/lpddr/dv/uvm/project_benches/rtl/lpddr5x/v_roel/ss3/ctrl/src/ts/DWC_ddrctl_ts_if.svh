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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/DWC_ddrctl_ts_if.svh#1 $
// -------------------------------------------------------------------------
// Description:
//
// This module defines interfaces from APB and ts Module
`ifndef __GUARD__DWC_DDRCTL_TS_IF__SVH__
`define __GUARD__DWC_DDRCTL_TS_IF__SVH__
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

typedef struct packed {
  logic [DWC_ddrctl_reg_pkg::HWFFC_MRWBUF_RDATA_WIDTH-1:0]            apb_rdata;
  logic                                                               mrwbuf_we;
  logic                                                               mrwbuf_re;
  logic [DWC_ddrctl_reg_pkg::HWFFC_MRWBUF_ADDR_WIDTH+DWC_ddrctl_reg_pkg::HWFFC_MRWBUF_SELECT_WIDTH-1:0]
                                                                      mrwbuf_addr;
  logic [DWC_ddrctl_reg_pkg::HWFFC_MRWBUF_WDATA_WIDTH-1:0]            mrwbuf_wdata;
} hwffcmrw_if_at_hwffcmrw_op_s;


`endif // __GUARD__DWC_DDRCTL_TS_IF__SVH__
