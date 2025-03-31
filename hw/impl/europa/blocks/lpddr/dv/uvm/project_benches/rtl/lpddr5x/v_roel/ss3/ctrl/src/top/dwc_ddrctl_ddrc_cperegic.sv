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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cperegic.sv#1 $
// -------------------------------------------------------------------------
// Description:
//    CPE-REG interconnection
//
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module dwc_ddrctl_ddrc_cperegic 
import DWC_ddrctl_reg_pkg::*;
#(
       parameter NUM_RANKS                =  `MEMC_NUM_RANKS
      ,parameter NUM_LRANKS               =  `UMCTL2_NUM_LRANKS_TOTAL
      ,parameter NUM_LRANKS_DDRC          =  `DDRCTL_DDRC_NUM_LRANKS_TOTAL
)
(

       input                                     core_ddrc_core_clk
      ,input                                     core_ddrc_rstn
    ///////////////////////////////////////////////////////////////////////////////////////////////
    // mux output
    ///////////////////////////////////////////////////////////////////////////////////////////////
      ,output logic  [NUM_LRANKS-1:0]            ddrc_reg_rank_refresh_busy
      ,output logic  [NUM_LRANKS-1:0]            ext_rank_refresh_busy
      ,output logic                              gs_pi_wr_data_pipeline_empty
      ,output logic                              gs_pi_rd_data_pipeline_empty
      ,output logic                              gs_pi_data_pipeline_empty

      ,output logic  [2:0]                       ddrc_reg_operating_mode
      ,output logic  [SELFREF_TYPE_WIDTH-1:0]    ddrc_reg_selfref_type

      ,output logic                              cactive_ddrc
      ,output logic                              csysack_ddrc


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // input from ddrc_cpe
    ///////////////////////////////////////////////////////////////////////////////////////////////
      ,input  logic  [NUM_LRANKS_DDRC-1:0]       ddrc_rank_refresh_busy
      ,input  logic                              ddrc_wr_data_pipeline_empty
      ,input  logic                              ddrc_rd_data_pipeline_empty
      ,input  logic                              ddrc_data_pipeline_empty

      ,input  logic  [2:0]                       ddrc_operating_mode
      ,input  logic  [SELFREF_TYPE_WIDTH-1:0]    ddrc_selfref_type

      ,input  logic                              ddrc_cactive_ddrc
      ,input  logic                              ddrc_csysack_ddrc


    ///////////////////////////////////////////////////////////////////////////////////////////////
    // input from pas_cpe
    ///////////////////////////////////////////////////////////////////////////////////////////////
);

// Registered signal not to generate glitch for CDC
// pas_rank_refresh_busy is combinational logic to be registered.
always_ff @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
   if (!core_ddrc_rstn) begin
      ddrc_reg_rank_refresh_busy <= '0;
   end else begin
      ddrc_reg_rank_refresh_busy <=
                                                                {{(NUM_LRANKS-NUM_LRANKS_DDRC){1'b0}},ddrc_rank_refresh_busy};
   end
end

assign ext_rank_refresh_busy                 =
                                                                           {{(NUM_LRANKS-NUM_LRANKS_DDRC){1'b0}},ddrc_rank_refresh_busy};

assign gs_pi_wr_data_pipeline_empty          =
                                                                           ddrc_wr_data_pipeline_empty;
assign gs_pi_rd_data_pipeline_empty          =
                                                                           ddrc_rd_data_pipeline_empty;
assign gs_pi_data_pipeline_empty             =
                                                                           ddrc_data_pipeline_empty;

assign ddrc_reg_operating_mode               =
                                                                           ddrc_operating_mode;
assign ddrc_reg_selfref_type                 =
                                                                           ddrc_selfref_type;

assign cactive_ddrc                          =
                                                                           ddrc_cactive_ddrc;
assign csysack_ddrc                          =
                                                                           ddrc_csysack_ddrc;

endmodule : dwc_ddrctl_ddrc_cperegic
