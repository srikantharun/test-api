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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cpperfic.sv#6 $
// -------------------------------------------------------------------------
// Description:
//    Perf signals generation
//
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module dwc_ddrctl_ddrc_cpperfic 
import DWC_ddrctl_reg_pkg::*;
#(
       parameter NUM_RANKS                = `MEMC_NUM_RANKS
      ,parameter RANK_BITS_DUP            = `MEMC_RANK_BITS
      ,parameter BG_BITS_DUP              = `MEMC_BG_BITS
      ,parameter CID_WIDTH_DUP            = `UMCTL2_CID_WIDTH
      ,parameter BSM_BITS                 = `UMCTL2_BSM_BITS
      ,parameter NUM_TOTAL_BSMS           = `UMCTL2_NUM_BSM
      ,parameter LRANK_BITS               = `UMCTL2_LRANK_BITS
      ,parameter BG_BANK_BITS             = `MEMC_BG_BANK_BITS
      ,parameter RANKBANK_BITS            = LRANK_BITS + BG_BANK_BITS
      ,parameter BG_BITS                  = `MEMC_BG_BITS
      ,parameter BANK_BITS                = `MEMC_BANK_BITS
      //,parameter BANK_ORG_WIDTH           = 1
      ,parameter CID_WIDTH                = `UMCTL2_CID_WIDTH
      ,parameter RANK_BITS                = `MEMC_RANK_BITS
      ,parameter CID_WIDTH_DDRC           = `DDRCTL_DDRC_CID_WIDTH
      ,parameter CMD_LEN_BITS             = `UMCTL2_CMD_LEN_BITS

)
(
   output    perf_hif_rd_or_wr,
   output    perf_hif_wr,
   output    perf_hif_rd,
   output    perf_hif_rmw,
   output    perf_hif_hi_pri_rd,
   output    perf_read_bypass,
   output    perf_act_bypass,
   output    perf_hpr_xact_when_critical, // hpr transaction when hpr q is critical
   output    perf_lpr_xact_when_critical, // lpr transaction when lpr q is critical
   output    perf_wr_xact_when_critical,  // wr transaction when wr q is critical
   output    perf_op_is_activate,
   output    perf_op_is_rd_or_wr,
   output    perf_op_is_rd_activate,
   output    perf_op_is_rd,
   output    perf_op_is_wr,
   output    perf_op_is_mwr,
   output    perf_op_is_wr16,
   output    perf_op_is_wr32,
   output    perf_op_is_rd16,
   output    perf_op_is_rd32,
   output    perf_op_is_cas,
   output    perf_op_is_cas_ws,
   output    perf_op_is_cas_ws_off,
   output    perf_op_is_cas_wck_sus,
   output    perf_op_is_enter_dsm,
   output    perf_op_is_precharge,
   output    perf_precharge_for_rdwr,
   output    perf_precharge_for_other,
   output    perf_rdwr_transitions,
   output    perf_write_combine,
   output    perf_write_combine_noecc,
   output    perf_write_combine_wrecc,
   output    perf_war_hazard,
   output    perf_raw_hazard,
   output    perf_waw_hazard,
   output    perf_ie_blk_hazard,
   output    [NUM_RANKS-1:0] perf_op_is_enter_selfref,
   output    [NUM_RANKS-1:0] perf_op_is_enter_powerdown,
   output    [NUM_RANKS-1:0] perf_op_is_enter_mpsm,
   output    [NUM_RANKS-1:0] perf_selfref_mode,
   output    perf_op_is_rfm,
   output    perf_op_is_refresh,
   output    perf_op_is_crit_ref,
   output    perf_op_is_spec_ref,
   output    perf_op_is_load_mode,
   output    perf_op_is_zqcl,
   output    perf_op_is_zqcs,
   output    [RANK_BITS_DUP-1:0]   perf_rank,
   output    [`MEMC_BANK_BITS-1:0] perf_bank,
   output    [BG_BITS_DUP-1:0]     perf_bg,
   output    [CID_WIDTH_DUP-1:0]   perf_cid,
   output    [RANK_BITS_DUP-1:0]   perf_bypass_rank,
   output    [`MEMC_BANK_BITS-1:0] perf_bypass_bank,
   output    [BG_BITS_DUP-1:0]     perf_bypass_bg,
   output    [CID_WIDTH_DUP-1:0]   perf_bypass_cid,
   output                          perf_bsm_alloc,
   output                          perf_bsm_starvation,
   output    [BSM_BITS:0]          perf_num_alloc_bsm,
   output                          perf_visible_window_limit_reached_rd,
   output                          perf_visible_window_limit_reached_wr,
   output                          perf_op_is_dqsosc_mpc,
   output                          perf_op_is_dqsosc_mrr,
   output                          perf_op_is_tcr_mrr,
   output                          perf_op_is_zqstart,
   output                          perf_op_is_zqlatch  

    ,input                        core_ddrc_core_clk
    ,input                        core_ddrc_rstn
    ,input                        hif_cmd_valid
    ,input [1:0]                  hif_cmd_type
    ,input                        hif_cmd_stall
    ,input [1:0]                  hif_cmd_pri
    ,input                        te_ih_retry
    ,input                        ddrc_co_perf_war_hazard_w
    ,input                        ddrc_co_perf_raw_hazard_w
    ,input                        ddrc_co_perf_waw_hazard_w  
    ,input                        ddrc_co_perf_ie_blk_hazard_w
    ,input                        te_yy_wr_combine  
    ,input                        ih_yy_wr_valid_no_addrerr 


    ,input                        ddrc_perf_hpr_xact_when_critical_w
    ,input                        ddrc_perf_lpr_xact_when_critical_w
    ,input                        ddrc_perf_wr_xact_when_critical_w
    ,input                        ddrc_perf_rdwr_transitions_w


    ,input                        ddrc_perf_op_is_dqsosc_mrr
    ,input                        ddrc_perf_op_is_dqsosc_mpc
    ,input                        ddrc_perf_op_is_zqstart
    ,input                        ddrc_perf_op_is_zqlatch
    ,input                        ddrc_perf_op_is_tcr_mrr
    ,input                        gs_pi_op_is_activate
    ,input                        gs_pi_op_is_rd
    ,input                        gs_pi_op_is_wr
    ,input                        gs_pi_wr_mode
    ,input                        gs_pi_op_is_precharge
    ,input                        gs_pi_op_is_load_mode
    ,input                        reg_ddrc_lpddr5
    ,input [BANK_ORG_WIDTH-1:0]   reg_ddrc_bank_org
    ,input                        ts_pi_mwr  
    ,input                        gs_pi_op_is_cas
    ,input                        gs_pi_op_is_cas_ws
    ,input                        gs_op_is_cas_ws_off
    ,input                        gs_op_is_cas_wck_sus
    ,input                        gs_pi_op_is_enter_dsm
    ,input                        gs_pi_op_is_rfm
    ,input                        ddrc_perf_precharge_for_rdwr
    ,input                        ddrc_perf_precharge_for_other
    ,input                        any_refresh_required
    ,input                        any_speculative_ref
    ,input [2:0]                  ddrc_reg_operating_mode
    ,input                        gs_pi_op_is_refresh
    ,input                        gs_pi_op_is_enter_selfref
    ,input                        gs_pi_op_is_enter_powerdown
    ,input                        te_yy_wr_combine_noecc
    ,input                        te_yy_wr_combine_wrecc

    ,input [NUM_TOTAL_BSMS-1:0]   ddrc_perf_sel_act_wr
    ,input [BSM_BITS-1:0]         ddrc_perf_bsm_num4act

    ,input [RANK_BITS-1:0]        ddrc_perf_rdwr_rank
    ,input [BG_BANK_BITS-1:0]     ddrc_perf_rdwr_bg_bank

  
    ,input                        ddrc_co_perf_vlimit_reached_rd_w
    ,input                        ddrc_co_perf_vlimit_reached_wr_w

);



//-----------------
// register declarations
//-----------------

   reg       i_perf_hif_rd_or_wr;
   reg       i_perf_hif_wr;
   reg       i_perf_hif_rd;
   reg       i_perf_hif_rmw;
   reg       i_perf_hif_hi_pri_rd;
   reg       i_perf_hpr_xact_when_critical; // hpr transaction when hpr q is critical
   reg       i_perf_lpr_xact_when_critical; // lpr transaction when lpr q is critical
   reg       i_perf_wr_xact_when_critical;  // wr transaction when wr q is critical
   reg       i_perf_op_is_activate;
   reg       i_perf_op_is_rd_or_wr;
   reg       i_perf_op_is_rd_activate;
   reg       i_perf_op_is_rd;
   reg       i_perf_op_is_wr;
   reg       i_perf_op_is_mwr;
   reg       i_perf_op_is_cas;
   reg       i_perf_op_is_cas_ws;
   reg       i_perf_op_is_cas_ws_off;
   reg       i_perf_op_is_cas_wck_sus;
   reg       i_perf_op_is_enter_dsm;
   reg       i_perf_op_is_precharge;
   reg       i_perf_precharge_for_rdwr;
   reg       i_perf_precharge_for_other;
   reg       i_perf_rdwr_transitions;
   reg       i_perf_write_combine;
   reg       i_perf_write_combine_wrecc;
   reg       i_perf_write_combine_noecc;
   reg       i_perf_war_hazard;
   reg       i_perf_raw_hazard;
   reg       i_perf_waw_hazard;
   reg       i_perf_ie_blk_hazard;
   reg       [NUM_RANKS-1:0] i_perf_op_is_enter_selfref;
   reg       [NUM_RANKS-1:0] i_perf_op_is_enter_powerdown;
   reg       [NUM_RANKS-1:0] i_perf_selfref_mode;
   
   reg       i_perf_op_is_rfm;
   reg       i_perf_op_is_refresh;
   reg       i_perf_op_is_crit_ref;
   reg       i_perf_op_is_spec_ref;
   reg       i_perf_op_is_load_mode;
   
   
   reg       [`MEMC_RANK_BITS-1:0] i_perf_rank;
   reg       [`MEMC_BANK_BITS-1:0] i_perf_bank;
   reg       [`MEMC_BG_BITS-1:0]   i_perf_bg;
   reg                             i_perf_visible_window_limit_reached_rd;
   reg                             i_perf_visible_window_limit_reached_wr;
   reg                             i_perf_op_is_dqsosc_mpc;
   reg                             i_perf_op_is_dqsosc_mrr;
   reg                             i_perf_op_is_tcr_mrr;
   reg                             i_perf_op_is_zqstart;
   reg                             i_perf_op_is_zqlatch;

 //-----------------------------
// Wire declarations
//-----------------------------
wire       ddrc_co_perf_hif_rd_or_wr_w;
wire       ddrc_co_perf_hif_wr_w;
wire       ddrc_co_perf_hif_rd_w;
wire       ddrc_co_perf_hif_rmw_w;
wire       ddrc_co_perf_hif_hi_pri_rd_w;


wire       ddrc_co_perf_hpr_xact_when_critical_w; // hpr transaction when hpr q is critical //BT_replace_P80001562-505275_
wire       ddrc_co_perf_lpr_xact_when_critical_w; // lpr transaction when lpr q is critical BT_replace_P80001562-505275_
wire       ddrc_co_perf_wr_xact_when_critical_w;  // wr transaction when wr q is critical BT_replace_P80001562-505275_
wire       ddrc_co_perf_rdwr_transitions_w;
wire       ddrc_co_perf_op_is_activate_w;
wire       ddrc_co_perf_op_is_rd_or_wr_w;
wire       ddrc_co_perf_op_is_rd_activate_w;
wire       ddrc_co_perf_op_is_rd_w;
wire       ddrc_co_perf_op_is_wr_w;
wire       ddrc_co_perf_op_is_mwr_w;
wire       ddrc_co_perf_op_is_cas_w;
wire       ddrc_co_perf_op_is_cas_ws_w;
wire       ddrc_co_perf_op_is_cas_ws_off_w;
wire       ddrc_co_perf_op_is_cas_wck_sus_w;
wire       ddrc_co_perf_op_is_enter_dsm_w;
wire       ddrc_co_perf_op_is_precharge_w;
wire       ddrc_co_perf_precharge_for_rdwr_w;
wire       ddrc_co_perf_precharge_for_other_w;
wire       ddrc_co_perf_write_combine_w;
wire       ddrc_co_perf_write_combine_wrecc_w;
wire       ddrc_co_perf_write_combine_noecc_w;
wire       [NUM_RANKS-1:0] ddrc_co_perf_op_is_enter_selfref_w;
wire       [NUM_RANKS-1:0] ddrc_co_perf_op_is_enter_powerdown_w;
wire       [NUM_RANKS-1:0] ddrc_co_perf_selfref_mode_w;
wire       ddrc_co_perf_op_is_rfm_w;
wire       ddrc_co_perf_op_is_refresh_w;
wire       ddrc_co_perf_op_is_crit_ref_w;
wire       ddrc_co_perf_op_is_spec_ref_w;
wire       ddrc_co_perf_op_is_load_mode_w;
wire       [`MEMC_RANK_BITS-1:0] ddrc_co_perf_rank_w;
wire       [`MEMC_BANK_BITS-1:0] ddrc_co_perf_bank_w;
wire       [`MEMC_BG_BITS-1:0]   ddrc_co_perf_bg_w;
wire                             bg_16b_addr_mode;
wire                        ddrc_co_perf_op_is_dqsosc_mrr_w;
wire                        ddrc_co_perf_op_is_dqsosc_mpc_w;
wire                        ddrc_co_perf_op_is_tcr_mrr_w;
wire                        ddrc_co_perf_op_is_zqstart_w;
wire                        ddrc_co_perf_op_is_zqlatch_w; 

//-----------------------------
// All wire assignments
//-----------------------------

wire i_rdwr_switch_policy_sel;
assign i_rdwr_switch_policy_sel = 1'b1;

assign ddrc_co_perf_lpr_xact_when_critical_w =
                                                                           ddrc_perf_lpr_xact_when_critical_w;
assign ddrc_co_perf_hpr_xact_when_critical_w =
                                                                           ddrc_perf_hpr_xact_when_critical_w;
assign ddrc_co_perf_wr_xact_when_critical_w  =
                                                                           ddrc_perf_wr_xact_when_critical_w;
assign ddrc_co_perf_rdwr_transitions_w       =
                                                                           ddrc_perf_rdwr_transitions_w;
assign  ddrc_co_perf_precharge_for_rdwr_w    =
                                                                         ddrc_perf_precharge_for_rdwr;
assign  ddrc_co_perf_precharge_for_other_w   =
                                                                          ddrc_perf_precharge_for_other; 

assign ddrc_co_perf_write_combine_w = 
                                        ih_yy_wr_valid_no_addrerr && 
                                        te_yy_wr_combine && ~te_ih_retry;

assign ddrc_co_perf_write_combine_noecc_w = 
                                       ih_yy_wr_valid_no_addrerr && 
                                       te_yy_wr_combine_noecc && ~te_ih_retry;

assign ddrc_co_perf_write_combine_wrecc_w = 
                                       ih_yy_wr_valid_no_addrerr && 
                                       te_yy_wr_combine_wrecc && ~te_ih_retry;





assign ddrc_co_perf_op_is_wr_w                  = (gs_pi_op_is_wr
                                                & ~ts_pi_mwr
                                                );
assign ddrc_co_perf_op_is_mwr_w                 = gs_pi_op_is_wr & ts_pi_mwr;


// ccx_cond:;;10; Redundant for now. 8B mode is not supported.
assign bg_16b_addr_mode                         = reg_ddrc_lpddr5 && (reg_ddrc_bank_org != {{($bits(reg_ddrc_bank_org)-1){1'b0}},1'b1});
assign ddrc_co_perf_op_is_cas_w                 = gs_pi_op_is_cas;
assign ddrc_co_perf_op_is_cas_ws_w              = gs_pi_op_is_cas_ws;
assign ddrc_co_perf_op_is_cas_ws_off_w          = gs_op_is_cas_ws_off;
assign ddrc_co_perf_op_is_cas_wck_sus_w         = gs_op_is_cas_wck_sus;
assign ddrc_co_perf_op_is_enter_dsm_w           = gs_pi_op_is_enter_dsm;
assign ddrc_co_perf_op_is_rfm_w                 = gs_pi_op_is_rfm;

assign ddrc_co_perf_op_is_refresh_w             = 
                                                  (gs_pi_op_is_refresh & (ddrc_reg_operating_mode[1:0] != 2'b00)) ; // count only non-init-mode refreshes

assign ddrc_co_perf_op_is_crit_ref_w            =
                                                  (ddrc_co_perf_op_is_refresh_w & any_refresh_required);

assign ddrc_co_perf_op_is_spec_ref_w            =
                                                  (ddrc_co_perf_op_is_refresh_w & ~any_refresh_required & any_speculative_ref);

assign ddrc_co_perf_op_is_enter_powerdown_w     = {NUM_RANKS{gs_pi_op_is_enter_powerdown}};
assign ddrc_co_perf_op_is_load_mode_w           = (gs_pi_op_is_load_mode & (ddrc_reg_operating_mode[1:0] != 2'b00)); // count only non-init-mode load_mode


assign ddrc_co_perf_hif_wr_w             = hif_cmd_valid & (hif_cmd_type == 2'b00) & ~hif_cmd_stall;
assign ddrc_co_perf_hif_rd_w             = hif_cmd_valid & (hif_cmd_type == 2'b01) & ~hif_cmd_stall;
assign ddrc_co_perf_hif_rd_or_wr_w       = ddrc_co_perf_hif_wr_w || ddrc_co_perf_hif_rd_w;
assign ddrc_co_perf_hif_rmw_w            = hif_cmd_valid & (hif_cmd_type == 2'b10) & ~hif_cmd_stall;
assign ddrc_co_perf_hif_hi_pri_rd_w      = hif_cmd_valid & (hif_cmd_type == 2'b01) & ~hif_cmd_stall & (hif_cmd_pri == 2'b10);
//assign ddrc_co_perf_hif_hi_pri_rd_w      = hif_cmd_valid & (hif_cmd_type == 2'b01) & ~hif_cmd_stall & hif_cmd_pri; // TEMP ONLY - use previous line when ARB is connected


assign ddrc_co_perf_op_is_activate_w     = gs_pi_op_is_activate;
assign ddrc_co_perf_op_is_rd_or_wr_w     = (gs_pi_op_is_rd | gs_pi_op_is_wr);

assign ddrc_co_perf_op_is_rd_activate_w  = (gs_pi_op_is_activate & (
                                            i_rdwr_switch_policy_sel ?  ~ddrc_perf_sel_act_wr[ddrc_perf_bsm_num4act] : 
                                          ~gs_pi_wr_mode));

assign ddrc_co_perf_op_is_rd_w           = gs_pi_op_is_rd;

assign ddrc_co_perf_op_is_precharge_w    = gs_pi_op_is_precharge;

assign ddrc_co_perf_op_is_enter_selfref_w= {NUM_RANKS{gs_pi_op_is_enter_selfref}};
assign ddrc_co_perf_selfref_mode_w       = 
                                           {NUM_RANKS{((ddrc_reg_operating_mode[1:0] == 2'b11)
                                           & !ddrc_reg_operating_mode[2]
                                           )}};

assign ddrc_co_perf_rank_w        = ddrc_perf_rdwr_rank;

assign ddrc_co_perf_bank_w        = (bg_16b_addr_mode) ? (({1'b0,ddrc_perf_rdwr_bg_bank[`MEMC_BANK_BITS + `MEMC_BG_BITS - 2:`MEMC_BG_BITS]})) :
                                                         ddrc_perf_rdwr_bg_bank[`MEMC_BANK_BITS-1:0];
assign ddrc_co_perf_bg_w          = (bg_16b_addr_mode) ? ddrc_perf_rdwr_bg_bank[`MEMC_BG_BITS-1:0] :
                                                         {`MEMC_BG_BITS{1'b0}};

assign ddrc_co_perf_op_is_tcr_mrr_w    = ddrc_perf_op_is_tcr_mrr ;
assign ddrc_co_perf_op_is_dqsosc_mrr_w = ddrc_perf_op_is_dqsosc_mrr;
assign ddrc_co_perf_op_is_dqsosc_mpc_w = ddrc_perf_op_is_dqsosc_mpc;
assign ddrc_co_perf_op_is_zqstart_w    = ddrc_perf_op_is_zqstart;
assign ddrc_co_perf_op_is_zqlatch_w    = ddrc_perf_op_is_zqlatch;

//--------------------------------------------------
// Flops for all the performance relates outputs
//--------------------------------------------------
   always @ (posedge core_ddrc_core_clk or negedge core_ddrc_rstn)
   begin
       if(~core_ddrc_rstn) begin
          i_perf_write_combine             <= 1'b0;
          i_perf_write_combine_noecc       <= 1'b0;
          i_perf_write_combine_wrecc       <= 1'b0;
          i_perf_op_is_wr                  <= 1'b0;
          i_perf_op_is_mwr                 <= 1'b0;
          i_perf_op_is_cas                 <= 1'b0;
          i_perf_op_is_cas_ws              <= 1'b0;
          i_perf_op_is_cas_ws_off          <= 1'b0;
          i_perf_op_is_cas_wck_sus         <= 1'b0;
          i_perf_op_is_enter_dsm           <= 1'b0;
          i_perf_op_is_rfm                 <= 1'b0;
          i_perf_op_is_refresh             <= 1'b0;
          i_perf_op_is_crit_ref            <= 1'b0;
          i_perf_op_is_spec_ref            <= 1'b0;
          i_perf_op_is_enter_powerdown     <= {NUM_RANKS{1'b0}};
          i_perf_op_is_load_mode           <= 1'b0;
          i_perf_hif_wr                    <= 1'b0;  
          i_perf_hif_rd                    <= 1'b0;  
          i_perf_hif_rd_or_wr              <= 1'b0;  
          i_perf_hif_rmw                   <= 1'b0;  
          i_perf_hif_hi_pri_rd             <= 1'b0;  
          i_perf_rdwr_transitions          <= 1'b0;
          i_perf_wr_xact_when_critical     <= 1'b0;
          i_perf_lpr_xact_when_critical    <= 1'b0;
          i_perf_hpr_xact_when_critical    <= 1'b0;
          i_perf_op_is_activate            <= 1'b0;
          i_perf_op_is_rd_or_wr            <= 1'b0;
          i_perf_op_is_rd_activate         <= 1'b0;
          i_perf_op_is_rd                  <= 1'b0;
          i_perf_op_is_precharge           <= 1'b0;
          i_perf_op_is_enter_selfref       <= {NUM_RANKS{1'b0}};
          i_perf_selfref_mode              <= {NUM_RANKS{1'b0}};
          i_perf_precharge_for_rdwr        <= 1'b0;
          i_perf_precharge_for_other       <= 1'b0;
          i_perf_war_hazard                <= 1'b0;
          i_perf_raw_hazard                <= 1'b0;
          i_perf_waw_hazard                <= 1'b0;
          i_perf_ie_blk_hazard             <= 1'b0;
   
          i_perf_rank                      <= {`MEMC_RANK_BITS{1'b0}};
          i_perf_bank                      <= {`MEMC_BANK_BITS{1'b0}};
          i_perf_bg                        <= {`MEMC_BG_BITS{1'b0}};
          i_perf_visible_window_limit_reached_rd <= 1'b0;
          i_perf_visible_window_limit_reached_wr <= 1'b0;
          i_perf_op_is_dqsosc_mpc       <= 1'b0;
          i_perf_op_is_dqsosc_mrr       <= 1'b0;
          i_perf_op_is_tcr_mrr          <= 1'b0;
          i_perf_op_is_zqstart          <= 1'b0;
          i_perf_op_is_zqlatch          <= 1'b0;
       end
       else begin
          i_perf_write_combine             <= ddrc_co_perf_write_combine_w;
          i_perf_write_combine_noecc       <= ddrc_co_perf_write_combine_noecc_w;
          i_perf_write_combine_wrecc       <= ddrc_co_perf_write_combine_wrecc_w;
          i_perf_op_is_wr                  <= ddrc_co_perf_op_is_wr_w;
          i_perf_op_is_mwr                 <= ddrc_co_perf_op_is_mwr_w;
          i_perf_op_is_cas                 <= ddrc_co_perf_op_is_cas_w;
          i_perf_op_is_cas_ws              <= ddrc_co_perf_op_is_cas_ws_w;
          i_perf_op_is_cas_ws_off          <= ddrc_co_perf_op_is_cas_ws_off_w;
          i_perf_op_is_cas_wck_sus         <= ddrc_co_perf_op_is_cas_wck_sus_w;
          i_perf_op_is_enter_dsm           <= ddrc_co_perf_op_is_enter_dsm_w;
          i_perf_op_is_rfm                 <= ddrc_co_perf_op_is_rfm_w;
          i_perf_op_is_refresh             <= ddrc_co_perf_op_is_refresh_w;
          i_perf_op_is_crit_ref            <= ddrc_co_perf_op_is_crit_ref_w;
          i_perf_op_is_spec_ref            <= ddrc_co_perf_op_is_spec_ref_w;
          i_perf_op_is_enter_powerdown     <= ddrc_co_perf_op_is_enter_powerdown_w;
          i_perf_op_is_load_mode           <= ddrc_co_perf_op_is_load_mode_w;
          i_perf_hif_wr                    <= ddrc_co_perf_hif_wr_w;
          i_perf_hif_rd                    <= ddrc_co_perf_hif_rd_w;
          i_perf_hif_rd_or_wr              <= ddrc_co_perf_hif_rd_or_wr_w;
          i_perf_hif_rmw                   <= ddrc_co_perf_hif_rmw_w;
          i_perf_hif_hi_pri_rd             <= ddrc_co_perf_hif_hi_pri_rd_w;
          i_perf_rdwr_transitions          <= ddrc_co_perf_rdwr_transitions_w;
          i_perf_wr_xact_when_critical     <= ddrc_co_perf_wr_xact_when_critical_w;
          i_perf_lpr_xact_when_critical    <= ddrc_co_perf_lpr_xact_when_critical_w;
          i_perf_hpr_xact_when_critical    <= ddrc_co_perf_hpr_xact_when_critical_w;
          i_perf_op_is_activate            <= ddrc_co_perf_op_is_activate_w;
          i_perf_op_is_rd_or_wr            <= ddrc_co_perf_op_is_rd_or_wr_w;
          i_perf_op_is_rd_activate         <= ddrc_co_perf_op_is_rd_activate_w;
          i_perf_op_is_rd                  <= ddrc_co_perf_op_is_rd_w;
          i_perf_op_is_precharge           <= ddrc_co_perf_op_is_precharge_w;
          i_perf_op_is_enter_selfref       <= ddrc_co_perf_op_is_enter_selfref_w;
          i_perf_selfref_mode              <= ddrc_co_perf_selfref_mode_w;
          i_perf_precharge_for_rdwr        <= ddrc_co_perf_precharge_for_rdwr_w;
          i_perf_precharge_for_other       <= ddrc_co_perf_precharge_for_other_w;
          i_perf_war_hazard                <= ddrc_co_perf_war_hazard_w;
          i_perf_raw_hazard                <= ddrc_co_perf_raw_hazard_w;
          i_perf_waw_hazard                <= ddrc_co_perf_waw_hazard_w;
          i_perf_ie_blk_hazard             <= ddrc_co_perf_ie_blk_hazard_w;
          i_perf_rank                      <= ddrc_co_perf_rank_w;
          i_perf_bank                      <= ddrc_co_perf_bank_w;
          i_perf_bg                        <= ddrc_co_perf_bg_w;
          i_perf_visible_window_limit_reached_rd <= ddrc_co_perf_vlimit_reached_rd_w;
          i_perf_visible_window_limit_reached_wr <= ddrc_co_perf_vlimit_reached_wr_w;
          i_perf_op_is_dqsosc_mpc       <= ddrc_co_perf_op_is_dqsosc_mpc_w;
          i_perf_op_is_dqsosc_mrr       <= ddrc_co_perf_op_is_dqsosc_mrr_w;
          i_perf_op_is_tcr_mrr          <= ddrc_co_perf_op_is_tcr_mrr_w;
          i_perf_op_is_zqstart          <= ddrc_co_perf_op_is_zqstart_w;
          i_perf_op_is_zqlatch          <= ddrc_co_perf_op_is_zqlatch_w;
       end
   end
//--------------------------------------------------
// drive output
//--------------------------------------------------
   assign    perf_hif_rd_or_wr           = i_perf_hif_rd_or_wr;
   assign    perf_hif_wr                 = i_perf_hif_wr;
   assign    perf_hif_rd                 = i_perf_hif_rd;
   assign    perf_hif_rmw                = i_perf_hif_rmw;
   assign    perf_hif_hi_pri_rd          = i_perf_hif_hi_pri_rd;
   assign    perf_read_bypass            = 1'b0;
   assign    perf_act_bypass             = 1'b0;
   assign    perf_hpr_xact_when_critical = i_perf_hpr_xact_when_critical; // hpr transaction when hpr q is critical
   assign    perf_lpr_xact_when_critical = i_perf_lpr_xact_when_critical; // lpr transaction when lpr q is critical
   assign    perf_wr_xact_when_critical  = i_perf_wr_xact_when_critical;  // wr transaction when wr q is critical
   assign    perf_op_is_activate         = i_perf_op_is_activate;
   assign    perf_op_is_rd_or_wr         = i_perf_op_is_rd_or_wr;
   assign    perf_op_is_rd_activate      = i_perf_op_is_rd_activate;
   assign    perf_op_is_rd               = i_perf_op_is_rd;
   assign    perf_op_is_wr               = i_perf_op_is_wr;
   assign    perf_op_is_mwr              = i_perf_op_is_mwr;
   assign    perf_op_is_wr16             = 1'b0;
   assign    perf_op_is_wr32             = 1'b0;
   assign    perf_op_is_rd16             = 1'b0;
   assign    perf_op_is_rd32             = 1'b0;
   assign    perf_op_is_cas             = i_perf_op_is_cas;
   assign    perf_op_is_cas_ws          = i_perf_op_is_cas_ws;
   assign    perf_op_is_cas_ws_off      = i_perf_op_is_cas_ws_off;
   assign    perf_op_is_cas_wck_sus     = i_perf_op_is_cas_wck_sus;
   assign    perf_op_is_enter_dsm       = i_perf_op_is_enter_dsm;
   assign    perf_op_is_precharge       = i_perf_op_is_precharge;
   assign    perf_precharge_for_rdwr    = i_perf_precharge_for_rdwr;
   assign    perf_precharge_for_other   = i_perf_precharge_for_other;
   assign    perf_rdwr_transitions      = i_perf_rdwr_transitions;
   assign    perf_write_combine         = i_perf_write_combine;
   assign    perf_write_combine_noecc   = i_perf_write_combine_noecc;
   assign    perf_write_combine_wrecc   = i_perf_write_combine_wrecc;
   assign    perf_war_hazard            = i_perf_war_hazard;
   assign    perf_raw_hazard            = i_perf_raw_hazard;
   assign    perf_waw_hazard            = i_perf_waw_hazard;
   assign    perf_ie_blk_hazard         = i_perf_ie_blk_hazard;
   assign    perf_op_is_enter_selfref   = i_perf_op_is_enter_selfref; //BT_replace_P80001562-505275_ mux required
   assign    perf_op_is_enter_powerdown = i_perf_op_is_enter_powerdown;
   assign    perf_op_is_enter_mpsm      = {NUM_RANKS{1'b0}};
   assign    perf_op_is_rfm             = i_perf_op_is_rfm;
   assign    perf_selfref_mode    = i_perf_selfref_mode;
   assign    perf_op_is_refresh   = i_perf_op_is_refresh;
   assign    perf_op_is_crit_ref  = i_perf_op_is_crit_ref;
   assign    perf_op_is_spec_ref  = i_perf_op_is_spec_ref;
   assign    perf_op_is_load_mode = i_perf_op_is_load_mode;
   assign    perf_op_is_zqcl      = 1'b0;
   assign    perf_op_is_zqcs      = 1'b0;
   assign    perf_rank = i_perf_rank;
   assign    perf_bank = i_perf_bank;
   assign    perf_bg   = i_perf_bg;
   assign    perf_cid  = {CID_WIDTH_DUP{1'b0}}; // // note use of <param>_DUP
   assign    perf_bypass_rank = {RANK_BITS_DUP{1'b0}}; // // note use of <param>_DUP
   assign    perf_bypass_cid  =  {CID_WIDTH_DUP{1'b0}}; // // note use of <param>_DUP
   assign    perf_bypass_bank = {`MEMC_BANK_BITS{1'b0}};
   assign    perf_bypass_bg   = {BG_BITS_DUP{1'b0}}; // // note use of <param>_DUP
   assign    perf_bsm_alloc      = 1'b0;
   assign    perf_bsm_starvation = 1'b0;
   assign    perf_num_alloc_bsm  = {(BSM_BITS+1){1'b0}};
   assign    perf_visible_window_limit_reached_rd = i_perf_visible_window_limit_reached_rd;
   assign    perf_visible_window_limit_reached_wr = i_perf_visible_window_limit_reached_wr;
   assign    perf_op_is_dqsosc_mpc = i_perf_op_is_dqsosc_mpc;
   assign    perf_op_is_dqsosc_mrr = i_perf_op_is_dqsosc_mrr;
   assign    perf_op_is_tcr_mrr= i_perf_op_is_tcr_mrr;
   assign    perf_op_is_zqstart= i_perf_op_is_zqstart;
   assign    perf_op_is_zqlatch= i_perf_op_is_zqlatch;

// -----------------------------------------
// Assertions
// -----------------------------------------
`ifndef SYNTHESIS
property p_perf_op_is_zqstart_chk;
    @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      perf_op_is_zqstart |-> ##1 (perf_op_is_zqstart==1'b0);
 endproperty

a_perf_op_is_zqstart_chk: assert property (p_perf_op_is_zqstart_chk)
else $error ("%0t perf_op_is_zqstart asserts more than one clock cycle unexpectedly ", $time);

property p_perf_op_is_zqlatch_chk;
    @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      perf_op_is_zqlatch |-> ##1 (perf_op_is_zqlatch==1'b0);
 endproperty

a_perf_op_is_zqlatch_chk: assert property (p_perf_op_is_zqlatch_chk)
else $error ("%0t perf_op_is_zqlatch asserts more than one clock cycle unexpectedly", $time);

property p_perf_op_is_tcr_dqsosc_mrr_chk;
    @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
      !(perf_op_is_tcr_mrr & perf_op_is_dqsosc_mrr);
 endproperty

a_p_perf_op_is_tcr_dqsosc_mrr_chk: assert property (p_perf_op_is_tcr_dqsosc_mrr_chk)
else $error ("%0t perf_op_is_tcr_mrr and perf_op_is_dqsosc_mrr asserts at the same time", $time);


`endif//SYNTHESIS

endmodule : dwc_ddrctl_ddrc_cpperfic

