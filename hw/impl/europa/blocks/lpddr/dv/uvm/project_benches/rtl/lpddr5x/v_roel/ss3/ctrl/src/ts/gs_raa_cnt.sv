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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_raa_cnt.sv#3 $
// -------------------------------------------------------------------------
// Description:
//                This block is responsible for RAA counter
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module gs_raa_cnt
import DWC_ddrctl_reg_pkg::*;
#(
   //------------------------------- PARAMETERS -----------------------------------
    parameter  RAACNT_BITS          = INIT_RAA_CNT_WIDTH
)
(
   //------------------------- INPUTS AND OUTPUTS ---------------------------------
    input   logic                         co_yy_clk                           //
   ,input   logic                         core_ddrc_rstn                      //
   ,input   logic                         raa_cnt_en                          // enable
   ,input   logic [RAACNT_BITS-1:0]       dh_gs_init_raa_cnt                  // initial value of RAA counters
   ,input   logic [RAACNT_BITS-1:0]       raaimt_cnt                          // initial value of RAA counters
   ,input   logic [RAACNT_BITS-1:0]       raammt_cnt                          // initial value of RAA counters
   ,input   logic [RAACNT_BITS-1:0]       raadec_cnt                          // initial value of RAA counters
   ,input   logic [2:0]                   gs_dh_operating_mode                // operating mode (0:init, 1:normal, 2:powerdown, 3:selfref)
   ,input   logic                         act_this_bank                       // ACT issued to this bank
   ,input   logic                         ref_this_bank                       // REF issued to this bank
   ,input   logic                         rfm_this_bank                       // RFM issued to this bank
   ,output  logic                         raa_cnt_expired_early               // RAA count expired (1 clock cycle early)
   ,output  logic                         raa_cnt_expired                     // RAA count expired
   ,output  logic                         raa_cnt_eq0                         // RAA count is equal to 0
   ,output  logic [RAACNT_BITS-1:0]       raa_cnt                             // RAA count value
);

   logic    [RAACNT_BITS:0]               raa_cnt_p1_wider;
   logic    [RAACNT_BITS-1:0]             raa_cnt_p1_w;
   logic    [RAACNT_BITS-1:0]             raa_cnt_after_act_w;
   logic    [RAACNT_BITS:0]               raa_cnt_minus_raaimt_wider;
   logic    [RAACNT_BITS-1:0]             raa_cnt_minus_raaimt_w;
   logic    [RAACNT_BITS-1:0]             raa_cnt_after_ref_w;
   logic    [RAACNT_BITS:0]               raa_cnt_minus_raadec_wider;
   logic    [RAACNT_BITS-1:0]             raa_cnt_minus_raadec_w;
   logic    [RAACNT_BITS-1:0]             raa_cnt_after_rfm_w;
   logic    [RAACNT_BITS-1:0]             next_raa_cnt_w;
   logic    [RAACNT_BITS-1:0]             raa_cnt_r;

   //------------------------------------------------------------------------------
   // RAA counter
   //------------------------------------------------------------------------------
   assign raa_cnt_p1_wider             = {1'b0, raa_cnt_r} + {{RAACNT_BITS{1'b0}}, 1'b1};
   assign raa_cnt_p1_w                 = raa_cnt_p1_wider[RAACNT_BITS-1:0];
   assign raa_cnt_after_act_w          = (raa_cnt_p1_w < raammt_cnt) ? raa_cnt_p1_w : raammt_cnt;

   assign raa_cnt_minus_raaimt_wider   = {1'b0, raa_cnt_r} - {1'b0, raaimt_cnt};
   assign raa_cnt_minus_raaimt_w       = raa_cnt_minus_raaimt_wider[RAACNT_BITS-1:0];
   assign raa_cnt_after_ref_w          = raa_cnt_minus_raaimt_wider[RAACNT_BITS] ? {RAACNT_BITS{1'b0}} : raa_cnt_minus_raaimt_w;

   assign raa_cnt_minus_raadec_wider   = {1'b0, raa_cnt_r} - {1'b0, raadec_cnt};
   assign raa_cnt_minus_raadec_w       = raa_cnt_minus_raadec_wider[RAACNT_BITS-1:0];
   assign raa_cnt_after_rfm_w          = raa_cnt_minus_raadec_wider[RAACNT_BITS] ? {RAACNT_BITS{1'b0}} : raa_cnt_minus_raadec_w;

   always_comb begin : NEXT_RAA_CNT_PROC
      if (gs_dh_operating_mode == 2'b00) begin // init
         next_raa_cnt_w = dh_gs_init_raa_cnt;
      end else if (gs_dh_operating_mode == 2'b01) begin // normal
         if (act_this_bank) begin
            next_raa_cnt_w = raa_cnt_after_act_w;
         end else if (ref_this_bank) begin
            next_raa_cnt_w = raa_cnt_after_ref_w;
         end else if (rfm_this_bank) begin
            next_raa_cnt_w = raa_cnt_after_rfm_w;
         end else begin
            next_raa_cnt_w = raa_cnt_r;
         end
      end else begin
         next_raa_cnt_w = raa_cnt_r;
      end
   end

   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         raa_cnt_r <= {RAACNT_BITS{1'b0}};
      end else if (raa_cnt_en) begin
         raa_cnt_r <= next_raa_cnt_w;
      end
   end

   assign raa_cnt_expired_early  = (next_raa_cnt_w < raammt_cnt) ? 1'b0 : raa_cnt_en;
   assign raa_cnt_expired        = (raa_cnt_r < raammt_cnt) ? 1'b0 : raa_cnt_en;
   assign raa_cnt_eq0            = ~(|raa_cnt_r);
   assign raa_cnt                = raa_cnt_r;

endmodule // gs_raa_cnt
