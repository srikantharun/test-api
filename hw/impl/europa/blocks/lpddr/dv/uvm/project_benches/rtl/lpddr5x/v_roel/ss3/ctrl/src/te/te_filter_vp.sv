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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_filter_vp.sv#1 $
// -------------------------------------------------------------------------
// Description:
//
// This filter classifies an entry to be one of the five classes.
// The five classes are listed in the order of favourable.
//   1. match prefer priority with expired page hit
//   2. match prefer priority without expired page hit
//   3. match prefer priority with page hit
//   4. match prefer priority without page hit

// After classification, the filter passes the entries that
// belong to the most favourable class to the selection network
// to participate a CAM search.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_filter_vp (
  te_vp_expired,
  te_bank_hit,
  te_page_hit,
  te_entry_participate
);

parameter CAM_ENTRIES = 32;

input  [CAM_ENTRIES -1:0]  te_vp_expired;         // Expired VPRW
input  [CAM_ENTRIES -1:0]  te_bank_hit;           // bank hit
input  [CAM_ENTRIES -1:0]  te_page_hit;           // page hit
output [CAM_ENTRIES -1:0]  te_entry_participate;  // qualified entry

wire   [CAM_ENTRIES -1:0]  choose_expired_page_hit; // expired page hit
wire   [CAM_ENTRIES -1:0]  choose_expired_bank_hit; // expired page miss 
wire   [CAM_ENTRIES -1:0]  choose_page_hit;         // page hit
wire   [CAM_ENTRIES -1:0]  choose_bank_hit;         // page miss

wire                       page_hit_exist;          // existence of the class mentioned above 
wire                       expired_page_hit_exist;  // existence of the class mentioned above 
wire                       expired_bank_hit_exist;  // existence of the class mentioned above 

// classify each entry
assign choose_page_hit = te_bank_hit &  te_page_hit;
assign choose_bank_hit = te_bank_hit ;
assign choose_expired_page_hit = choose_page_hit & te_vp_expired;
assign choose_expired_bank_hit = choose_bank_hit & te_vp_expired;
// check existence of each class
assign page_hit_exist = (| (choose_page_hit [CAM_ENTRIES -1:0]));
assign expired_page_hit_exist = (| (choose_expired_page_hit [CAM_ENTRIES -1:0]));
assign expired_bank_hit_exist = (| (choose_expired_bank_hit [CAM_ENTRIES -1:0]));

// Priority from high to low: expired page hits, expired page miss, page hit, page miss
assign te_entry_participate = expired_page_hit_exist ? choose_expired_page_hit :
                              expired_bank_hit_exist ? choose_expired_bank_hit :
                              page_hit_exist         ? choose_page_hit :
                                                       choose_bank_hit;
   
endmodule // te_filter_vp
