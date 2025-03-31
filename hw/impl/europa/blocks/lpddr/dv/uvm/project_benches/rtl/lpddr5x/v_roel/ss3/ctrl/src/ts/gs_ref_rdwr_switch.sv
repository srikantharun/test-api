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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_ref_rdwr_switch.sv#1 $
// -------------------------------------------------------------------------
// Description:
// This module is responsible to switch RD/WR directionduring tRFC window if
// the current CAM (RD|WR) does not contain any valid commands for a rank 
// different from the one being refreshed.
// This enhancement is disabled in case of per-bank refresh.
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module gs_ref_rdwr_switch 
       #(
        parameter   RD_CAM_ENTRIES       = 1<<`MEMC_RDCMD_ENTRY_BITS,
        parameter   WR_CAM_ENTRIES       = 1<<`MEMC_WRCMD_ENTRY_BITS,
        parameter   LRANK_BITS           = `DDRCTL_DDRC_LRANK_BITS,
        parameter   NUM_LRANKS           = 1 << LRANK_BITS // max # of ranks supported
        )
        (
        input                                 co_yy_clk,                      // clock
        input                                 core_ddrc_rstn,                 // asynchronous falling-edge reset

        input [NUM_LRANKS-1:0]                te_gs_rank_wr_pending,          // Any valid entry in WR CAM per rank
        input [NUM_LRANKS-1:0]                te_gs_rank_rd_pending,          // Any valid entry in RD CAM per rank

        input                                 te_gs_any_wr_pending,
        input                                 te_gs_any_rd_pending,
        
        input [NUM_LRANKS-1:0]                t_rfc_min_timer_bitor,
        input                                 dh_gs_per_bank_refresh,         //per_bank refresh register
              
        output                                te_gs_wr_vld_ref_rdwr_switch,
        output                                te_gs_rd_vld_ref_rdwr_switch
        );

//------------------------------- PARAMETERS ----------------------------------

localparam  REGISTER_RDWR_SWITCH = `PIPELINE_REF_RDWR_SWITCH_EN;
                                

//--------------------------------- WIRES/REGS --------------------------------------

wire [NUM_LRANKS-1:0]                 i_te_wr_valid_num_lranks_ref;
wire [NUM_LRANKS-1:0]                 i_te_rd_valid_num_lranks_ref;

wire                                  te_gs_wr_vld_ref_rdwr_switch_int;
wire                                  te_gs_rd_vld_ref_rdwr_switch_int;

wire                                  per_bank_refresh_en;

//--------------------------------- LOGIC -----------------------------
     assign per_bank_refresh_en = dh_gs_per_bank_refresh;

// For WRs
assign i_te_wr_valid_num_lranks_ref = ~t_rfc_min_timer_bitor & te_gs_rank_wr_pending;
assign te_gs_wr_vld_ref_rdwr_switch_int = |i_te_wr_valid_num_lranks_ref;

// For RDs
assign i_te_rd_valid_num_lranks_ref = ~t_rfc_min_timer_bitor & te_gs_rank_rd_pending;
assign te_gs_rd_vld_ref_rdwr_switch_int = |i_te_rd_valid_num_lranks_ref;

generate
  if (REGISTER_RDWR_SWITCH == 1) begin: pipeline_switch_gen
    //Pipeline output signals
    reg                                  te_gs_wr_vld_ref_rdwr_switch_ff;
    reg                                  te_gs_rd_vld_ref_rdwr_switch_ff;
    
    always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if(~core_ddrc_rstn) begin
        te_gs_wr_vld_ref_rdwr_switch_ff <= 1'b0;
        te_gs_rd_vld_ref_rdwr_switch_ff <= 1'b0;
      end else begin
        te_gs_wr_vld_ref_rdwr_switch_ff <= te_gs_wr_vld_ref_rdwr_switch_int;
        te_gs_rd_vld_ref_rdwr_switch_ff <= te_gs_rd_vld_ref_rdwr_switch_int;
      end
    end
    
    assign te_gs_wr_vld_ref_rdwr_switch = (|t_rfc_min_timer_bitor & ~per_bank_refresh_en) ? te_gs_wr_vld_ref_rdwr_switch_ff : te_gs_any_wr_pending;
    assign te_gs_rd_vld_ref_rdwr_switch = (|t_rfc_min_timer_bitor & ~per_bank_refresh_en) ? te_gs_rd_vld_ref_rdwr_switch_ff : te_gs_any_rd_pending;
    
    end else begin
    
    assign te_gs_wr_vld_ref_rdwr_switch = (|t_rfc_min_timer_bitor & ~per_bank_refresh_en) ? te_gs_wr_vld_ref_rdwr_switch_int : te_gs_any_wr_pending;
    assign te_gs_rd_vld_ref_rdwr_switch = (|t_rfc_min_timer_bitor & ~per_bank_refresh_en) ? te_gs_rd_vld_ref_rdwr_switch_int : te_gs_any_rd_pending;
  
  end
endgenerate

endmodule  // gs_ref_rdwr_switch
