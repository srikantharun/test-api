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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_reg_ff.sv#5 $
// -------------------------------------------------------------------------
// Description:
//           Register flip flop stage
//           This block adds a flip flop stage after registe rmultiplexer and divisor to improve timings
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module dwc_ddrctl_reg_ff 
import DWC_ddrctl_reg_pkg::*;
#(
) ( 

     input logic        core_ddrc_core_clk                // ddrc core clock
    ,input logic        core_ddrc_rstn                    // ddrc reset, low active

    ,input logic [T_REFI_X1_X32_WIDTH-1 : 0] regmux_ddrc_t_refi_x1_x32_div_comb
    ,input logic [REFRESH_TO_X1_X32_WIDTH-1 : 0] regmux_ddrc_refresh_to_x1_x32_div_comb
    ,input logic [REFRESH_MARGIN_WIDTH-1 : 0] regmux_ddrc_refresh_margin_div_comb
    ,input logic regmux_ddrc_refresh_to_x1_sel_comb
    ,input logic regmux_ddrc_t_refi_x1_sel_comb
    ,input logic [T_RFC_MIN_WIDTH-1 : 0] regmux_ddrc_t_rfc_min_div_comb
    ,input logic [REFRESH_TO_AB_X32_WIDTH-1 : 0] regmux_ddrc_refresh_to_ab_x32_div_comb
    ,input logic [T_RFC_MIN_AB_WIDTH-1 : 0] regmux_ddrc_t_rfc_min_ab_div_comb
    ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1 : 0] regmux_ddrc_refresh_timer0_start_value_x32_div_comb
    ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1 : 0] regmux_ddrc_refresh_timer1_start_value_x32_div_comb
    ,input logic [T_RFMPB_WIDTH-1 : 0] regmux_ddrc_t_rfmpb_div_comb
    ,input logic [T_PBR2PBR_WIDTH-1 : 0] regmux_ddrc_t_pbr2pbr_div_comb

    ,output logic [T_REFI_X1_X32_WIDTH-1 : 0] regmux_ddrc_t_refi_x1_x32_div_r
    ,output logic [REFRESH_TO_X1_X32_WIDTH-1 : 0] regmux_ddrc_refresh_to_x1_x32_div_r
    ,output logic [REFRESH_MARGIN_WIDTH-1 : 0] regmux_ddrc_refresh_margin_div_r
    ,output logic regmux_ddrc_refresh_to_x1_sel_r
    ,output logic regmux_ddrc_t_refi_x1_sel_r
    ,output logic [T_RFC_MIN_WIDTH-1 : 0] regmux_ddrc_t_rfc_min_div_r
    ,output logic [REFRESH_TO_AB_X32_WIDTH-1 : 0] regmux_ddrc_refresh_to_ab_x32_div_r
    ,output logic [T_RFC_MIN_AB_WIDTH-1 : 0] regmux_ddrc_t_rfc_min_ab_div_r   
    ,output logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1 : 0] regmux_ddrc_refresh_timer0_start_value_x32_div_r
    ,output logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1 : 0] regmux_ddrc_refresh_timer1_start_value_x32_div_r
    ,output logic [T_RFMPB_WIDTH-1 : 0] regmux_ddrc_t_rfmpb_div_r
    ,output logic [T_PBR2PBR_WIDTH-1 : 0] regmux_ddrc_t_pbr2pbr_div_r

);


always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_t_refi_x1_x32_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_t_refi_x1_x32_div_r <= {$bits(regmux_ddrc_t_refi_x1_x32_div_r){1'b0}};
  end else if (regmux_ddrc_t_refi_x1_x32_div_r != regmux_ddrc_t_refi_x1_x32_div_comb) begin
    regmux_ddrc_t_refi_x1_x32_div_r <= regmux_ddrc_t_refi_x1_x32_div_comb;
  end
end: regmux_ddrc_t_refi_x1_x32_div_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_refresh_to_x1_x32_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_refresh_to_x1_x32_div_r <= {$bits(regmux_ddrc_refresh_to_x1_x32_div_r){1'b0}};
  end else if (regmux_ddrc_refresh_to_x1_x32_div_r != regmux_ddrc_refresh_to_x1_x32_div_comb) begin
    regmux_ddrc_refresh_to_x1_x32_div_r <= regmux_ddrc_refresh_to_x1_x32_div_comb;
  end
end: regmux_ddrc_refresh_to_x1_x32_div_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_refresh_to_ab_x32_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_refresh_to_ab_x32_div_r <= {$bits(regmux_ddrc_refresh_to_ab_x32_div_r){1'b0}};
  end else if (regmux_ddrc_refresh_to_ab_x32_div_r != regmux_ddrc_refresh_to_ab_x32_div_comb) begin
    regmux_ddrc_refresh_to_ab_x32_div_r <= regmux_ddrc_refresh_to_ab_x32_div_comb;
  end
end: regmux_ddrc_refresh_to_ab_x32_div_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_refresh_margin_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_refresh_margin_div_r <= {$bits(regmux_ddrc_refresh_margin_div_r){1'b0}};
  end else if (regmux_ddrc_refresh_margin_div_r != regmux_ddrc_refresh_margin_div_comb) begin
    regmux_ddrc_refresh_margin_div_r <= regmux_ddrc_refresh_margin_div_comb;
  end
end: regmux_ddrc_refresh_margin_div_PROC


always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_t_refi_x1_sel_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_t_refi_x1_sel_r <= {$bits(regmux_ddrc_t_refi_x1_sel_r){1'b0}};
  end else begin
    regmux_ddrc_t_refi_x1_sel_r <= regmux_ddrc_t_refi_x1_sel_comb;
  end
end: regmux_ddrc_t_refi_x1_sel_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_refresh_to_x1_sel_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_refresh_to_x1_sel_r <= {$bits(regmux_ddrc_refresh_to_x1_sel_r){1'b0}};
  end else begin
    regmux_ddrc_refresh_to_x1_sel_r <= regmux_ddrc_refresh_to_x1_sel_comb;
  end
end: regmux_ddrc_refresh_to_x1_sel_PROC
always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_t_rfc_min_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_t_rfc_min_div_r <= {$bits(regmux_ddrc_t_rfc_min_div_r){1'b0}};
  end else if (regmux_ddrc_t_rfc_min_div_r != regmux_ddrc_t_rfc_min_div_comb) begin
    regmux_ddrc_t_rfc_min_div_r <= regmux_ddrc_t_rfc_min_div_comb;
  end
end: regmux_ddrc_t_rfc_min_div_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_t_rfc_min_ab_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_t_rfc_min_ab_div_r <= {$bits(regmux_ddrc_t_rfc_min_ab_div_r){1'b0}};
  end else if (regmux_ddrc_t_rfc_min_ab_div_r != regmux_ddrc_t_rfc_min_ab_div_comb) begin
    regmux_ddrc_t_rfc_min_ab_div_r <= regmux_ddrc_t_rfc_min_ab_div_comb;
  end
end: regmux_ddrc_t_rfc_min_ab_div_PROC


always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_refresh_timer0_start_value_x32_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_refresh_timer0_start_value_x32_div_r <= {$bits(regmux_ddrc_refresh_timer0_start_value_x32_div_r){1'b0}};
  end else if (regmux_ddrc_refresh_timer0_start_value_x32_div_r != regmux_ddrc_refresh_timer0_start_value_x32_div_comb) begin
    regmux_ddrc_refresh_timer0_start_value_x32_div_r <= regmux_ddrc_refresh_timer0_start_value_x32_div_comb;
  end
end: regmux_ddrc_refresh_timer0_start_value_x32_div_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_refresh_timer1_start_value_x32_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_refresh_timer1_start_value_x32_div_r <= {$bits(regmux_ddrc_refresh_timer1_start_value_x32_div_r){1'b0}};
  end else if (regmux_ddrc_refresh_timer1_start_value_x32_div_r != regmux_ddrc_refresh_timer1_start_value_x32_div_comb) begin
    regmux_ddrc_refresh_timer1_start_value_x32_div_r <= regmux_ddrc_refresh_timer1_start_value_x32_div_comb;
  end
end: regmux_ddrc_refresh_timer1_start_value_x32_div_PROC


always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_t_rfmpb_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_t_rfmpb_div_r <= {$bits(regmux_ddrc_t_rfmpb_div_r){1'b0}};
  end else if (regmux_ddrc_t_rfmpb_div_r != regmux_ddrc_t_rfmpb_div_comb) begin
    regmux_ddrc_t_rfmpb_div_r <= regmux_ddrc_t_rfmpb_div_comb;
  end
end: regmux_ddrc_t_rfmpb_div_PROC

always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin : regmux_ddrc_t_pbr2pbr_div_PROC
  if(!core_ddrc_rstn) begin
    regmux_ddrc_t_pbr2pbr_div_r <= {$bits(regmux_ddrc_t_pbr2pbr_div_r){1'b0}};
  end else if (regmux_ddrc_t_pbr2pbr_div_r != regmux_ddrc_t_pbr2pbr_div_comb) begin
    regmux_ddrc_t_pbr2pbr_div_r <= regmux_ddrc_t_pbr2pbr_div_comb;
  end
end: regmux_ddrc_t_pbr2pbr_div_PROC



endmodule : dwc_ddrctl_reg_ff
