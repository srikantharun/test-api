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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_reg_div.sv#6 $
// -------------------------------------------------------------------------
// Description:
//              Register division block
//              This block divides registers by the DDRC/DFI frequency ratio
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module dwc_ddrctl_reg_div 
import DWC_ddrctl_reg_pkg::*;
#( 
) (

   input logic  [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_in
  ,output logic  [T_ZQ_LONG_NOP_WIDTH-1:0]  reg_ddrc_t_zq_long_nop_out
  ,input logic [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_in
  ,output logic [T_ZQ_SHORT_NOP_WIDTH-1:0]   reg_ddrc_t_zq_short_nop_out

  ,input logic  [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_in 
  ,output logic [T_PGM_X1_X1024_WIDTH-1:0] reg_ddrc_t_pgm_x1_x1024_out 
  ,input logic                             reg_ddrc_t_pgm_x1_sel_in 
  ,output logic                            reg_ddrc_t_pgm_x1_sel_out 
  ,input logic  [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_in 
  ,output logic [T_PGMPST_X32_WIDTH-1:0]   reg_ddrc_t_pgmpst_x32_out 
  ,input logic  [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_in 
  ,output logic [T_PGM_EXIT_WIDTH-1:0]     reg_ddrc_t_pgm_exit_out 



  ,input logic [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_in
  ,output logic [T_ZQ_RESET_NOP_WIDTH-1:0] reg_ddrc_t_zq_reset_nop_out


   // DERATEINT
  ,input logic [MR4_READ_INTERVAL_WIDTH-1:0] reg_ddrc_mr4_read_interval_in
  ,output logic [MR4_READ_INTERVAL_WIDTH-1:0] reg_ddrc_mr4_read_interval_out

   // ECCCFG0
  ,input logic [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0] reg_ddrc_blk_channel_idle_time_x32_in
  ,output logic [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0] reg_ddrc_blk_channel_idle_time_x32_out


   // RFSHTMG
  ,input logic  [T_RFC_MIN_WIDTH-1:0]        reg_ddrc_t_rfc_min_in
  ,output logic [T_RFC_MIN_WIDTH-1:0]        reg_ddrc_t_rfc_min_out
  ,input logic  [T_RFC_MIN_AB_WIDTH-1:0]     reg_ddrc_t_rfc_min_ab_in
  ,output logic [T_RFC_MIN_AB_WIDTH-1:0]     reg_ddrc_t_rfc_min_ab_out
  ,input logic  [T_REFI_X1_X32_WIDTH-1:0] reg_ddrc_t_refi_x1_x32_in
  ,output logic [T_REFI_X1_X32_WIDTH-1:0] reg_ddrc_t_refi_x1_x32_out
   // RFSHCTL0
  ,input logic  [REFRESH_MARGIN_WIDTH-1:0] reg_ddrc_refresh_margin_in
  ,output logic [REFRESH_MARGIN_WIDTH-1:0] reg_ddrc_refresh_margin_out
  ,input logic  [REFRESH_TO_X1_X32_WIDTH-1:0] reg_ddrc_refresh_to_x1_x32_in
  ,output logic [REFRESH_TO_X1_X32_WIDTH-1:0] reg_ddrc_refresh_to_x1_x32_out
  ,input logic  [REFRESH_TO_AB_X32_WIDTH-1:0] reg_ddrc_refresh_to_ab_x32_in
  ,output logic [REFRESH_TO_AB_X32_WIDTH-1:0] reg_ddrc_refresh_to_ab_x32_out


   // DERATEVAL0 
  ,input logic  [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_in
  ,output logic [DERATED_T_RCD_WIDTH-1:0]      reg_ddrc_derated_t_rcd_out
                                                            
  ,input logic  [DERATED_T_RAS_MIN_WIDTH-1:0]  reg_ddrc_derated_t_ras_min_in
  ,output logic [DERATED_T_RAS_MIN_WIDTH-1:0]  reg_ddrc_derated_t_ras_min_out
                                                            
  ,input logic  [DERATED_T_RP_WIDTH-1:0]       reg_ddrc_derated_t_rp_in
  ,output logic [DERATED_T_RP_WIDTH-1:0]       reg_ddrc_derated_t_rp_out
                                                            
  ,input logic  [DERATED_T_RRD_WIDTH-1:0]      reg_ddrc_derated_t_rrd_in
  ,output logic [DERATED_T_RRD_WIDTH-1:0]      reg_ddrc_derated_t_rrd_out
                                                            
   // DERATEVAL1                                            
  ,input logic  [DERATED_T_RC_WIDTH-1:0]       reg_ddrc_derated_t_rc_in
  ,output logic [DERATED_T_RC_WIDTH-1:0]       reg_ddrc_derated_t_rc_out

   // RFSHTMG1
  ,input logic [T_PBR2PBR_WIDTH-1:0]       reg_ddrc_t_pbr2pbr_in
  ,output logic [T_PBR2PBR_WIDTH-1:0]      reg_ddrc_t_pbr2pbr_out

  ,input logic  [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_in
  ,output logic [T_RFMPB_WIDTH-1:0] reg_ddrc_t_rfmpb_out

   // RANKCTL
  ,input logic [DIFF_RANK_RD_GAP_WIDTH-1:0]      reg_ddrc_diff_rank_rd_gap_in
  ,output logic [DIFF_RANK_RD_GAP_WIDTH-1:0]     reg_ddrc_diff_rank_rd_gap_out

  ,input logic [DIFF_RANK_WR_GAP_WIDTH-1:0]      reg_ddrc_diff_rank_wr_gap_in
  ,output logic [DIFF_RANK_WR_GAP_WIDTH-1:0]     reg_ddrc_diff_rank_wr_gap_out

  ,input logic [RD2WR_DR_WIDTH-1:0]            reg_ddrc_rd2wr_dr_in
  ,output logic [RD2WR_DR_WIDTH-1:0]           reg_ddrc_rd2wr_dr_out

  ,input logic [WR2RD_DR_WIDTH-1:0]            reg_ddrc_wr2rd_dr_in
  ,output logic [WR2RD_DR_WIDTH-1:0]           reg_ddrc_wr2rd_dr_out

   // RFSHCTL1
  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_in
  ,output logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer0_start_value_x32_out
  ,input logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_in
  ,output logic [REFRESH_TIMER0_START_VALUE_X32_WIDTH-1:0] reg_ddrc_refresh_timer1_start_value_x32_out

   // DRAMSET1TMG0
  ,input logic [T_RAS_MIN_WIDTH-1:0] reg_ddrc_t_ras_min_in
  ,output logic [T_RAS_MIN_WIDTH-1:0] reg_ddrc_t_ras_min_out
  ,input logic [T_RAS_MAX_WIDTH-1:0] reg_ddrc_t_ras_max_in
  ,output logic [T_RAS_MAX_WIDTH-1:0] reg_ddrc_t_ras_max_out
  ,input logic [T_FAW_WIDTH-1:0] reg_ddrc_t_faw_in
  ,output logic [T_FAW_WIDTH-1:0] reg_ddrc_t_faw_out
  ,input logic [WR2PRE_WIDTH-1:0] reg_ddrc_wr2pre_in
  ,output logic [WR2PRE_WIDTH-1:0] reg_ddrc_wr2pre_out

   // DRAMSET1TMG25
  ,input logic [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_in
  ,output logic [LPDDR4_DIFF_BANK_RWA2PRE_WIDTH-1:0] reg_ddrc_lpddr4_diff_bank_rwa2pre_out
  ,input logic [WRA2PRE_WIDTH-1:0] reg_ddrc_wra2pre_in
  ,output logic [WRA2PRE_WIDTH-1:0] reg_ddrc_wra2pre_out
  ,input logic [RDA2PRE_WIDTH-1:0] reg_ddrc_rda2pre_in
  ,output logic [RDA2PRE_WIDTH-1:0] reg_ddrc_rda2pre_out

   // DRAMSET1TMG1
  ,input logic [T_RC_WIDTH-1:0] reg_ddrc_t_rc_in
  ,output logic [T_RC_WIDTH-1:0] reg_ddrc_t_rc_out
  ,input logic [RD2PRE_WIDTH-1:0] reg_ddrc_rd2pre_in
  ,output logic [RD2PRE_WIDTH-1:0] reg_ddrc_rd2pre_out
  ,input logic [T_XP_WIDTH-1:0] reg_ddrc_t_xp_in
  ,output logic [T_XP_WIDTH-1:0] reg_ddrc_t_xp_out

   // DRAMTMG2
  ,input logic [WR2RD_WIDTH-1:0] reg_ddrc_wr2rd_in
  ,output logic [WR2RD_WIDTH-1:0] reg_ddrc_wr2rd_out
  ,input logic [RD2WR_WIDTH-1:0] reg_ddrc_rd2wr_in
  ,output logic [RD2WR_WIDTH-1:0] reg_ddrc_rd2wr_out
  ,input logic [READ_LATENCY_WIDTH-1:0] reg_ddrc_read_latency_in
  ,output logic [READ_LATENCY_WIDTH-1:0] reg_ddrc_read_latency_out
  ,input logic [WRITE_LATENCY_WIDTH-1:0] reg_ddrc_write_latency_in
  ,output logic [WRITE_LATENCY_WIDTH-1:0] reg_ddrc_write_latency_out

   // DRAMTMG3
  ,input logic [RD2MR_WIDTH-1:0] reg_ddrc_rd2mr_in
  ,output logic [RD2MR_WIDTH-1:0] reg_ddrc_rd2mr_out
  ,input logic [T_MR_WIDTH-1:0] reg_ddrc_t_mr_in
  ,output logic [T_MR_WIDTH-1:0] reg_ddrc_t_mr_out
  ,input logic [WR2MR_WIDTH-1:0] reg_ddrc_wr2mr_in
  ,output logic [WR2MR_WIDTH-1:0] reg_ddrc_wr2mr_out

   // DRAMTMG4
  ,input logic [T_RP_WIDTH-1:0] reg_ddrc_t_rp_in
  ,output logic [T_RP_WIDTH-1:0] reg_ddrc_t_rp_out
  ,input logic [T_RRD_WIDTH-1:0] reg_ddrc_t_rrd_in
  ,output logic [T_RRD_WIDTH-1:0] reg_ddrc_t_rrd_out
  ,input logic [T_CCD_WIDTH-1:0] reg_ddrc_t_ccd_in
  ,output logic [T_CCD_WIDTH-1:0] reg_ddrc_t_ccd_out
  ,input logic [T_RCD_WIDTH-1:0] reg_ddrc_t_rcd_in
  ,output logic [T_RCD_WIDTH-1:0] reg_ddrc_t_rcd_out

   // DRAMTMG5
  ,input logic [T_CKE_WIDTH-1:0] reg_ddrc_t_cke_in
  ,output logic [T_CKE_WIDTH-1:0] reg_ddrc_t_cke_out
  ,input logic [T_CKESR_WIDTH-1:0] reg_ddrc_t_ckesr_in
  ,output logic [T_CKESR_WIDTH-1:0] reg_ddrc_t_ckesr_out
  ,input logic [T_CKSRE_WIDTH-1:0] reg_ddrc_t_cksre_in
  ,output logic [T_CKSRE_WIDTH-1:0] reg_ddrc_t_cksre_out
  ,input logic [T_CKSRX_WIDTH-1:0] reg_ddrc_t_cksrx_in
  ,output logic [T_CKSRX_WIDTH-1:0] reg_ddrc_t_cksrx_out

   // DRAMTMG6
  ,input logic [T_CKCSX_WIDTH-1:0] reg_ddrc_t_ckcsx_in
  ,output logic [T_CKCSX_WIDTH-1:0] reg_ddrc_t_ckcsx_out
   // DRAMTMG8

   // DRAMTMG9

  ,input logic [WR2RD_S_WIDTH-1:0] reg_ddrc_wr2rd_s_in
  ,output logic [WR2RD_S_WIDTH-1:0] reg_ddrc_wr2rd_s_out
  ,input logic [T_RRD_S_WIDTH-1:0] reg_ddrc_t_rrd_s_in
  ,output logic [T_RRD_S_WIDTH-1:0] reg_ddrc_t_rrd_s_out
  ,input logic [T_CCD_S_WIDTH-1:0] reg_ddrc_t_ccd_s_in
  ,output logic [T_CCD_S_WIDTH-1:0] reg_ddrc_t_ccd_s_out
  ,input logic [T_CMDCKE_WIDTH-1:0] reg_ddrc_t_cmdcke_in
  ,output logic [T_CMDCKE_WIDTH-1:0] reg_ddrc_t_cmdcke_out

   // DRAMTMG13
  ,input logic [T_CCD_MW_WIDTH-1:0] reg_ddrc_t_ccd_mw_in
  ,output logic [T_CCD_MW_WIDTH-1:0] reg_ddrc_t_ccd_mw_out
  ,input logic [ODTLOFF_WIDTH-1:0] reg_ddrc_odtloff_in
  ,output logic [ODTLOFF_WIDTH-1:0] reg_ddrc_odtloff_out
  ,input logic [T_PPD_WIDTH-1:0] reg_ddrc_t_ppd_in
  ,output logic [T_PPD_WIDTH-1:0] reg_ddrc_t_ppd_out


   // DRAMTMG14
  ,input logic [T_XSR_WIDTH-1:0] reg_ddrc_t_xsr_in
  ,output logic [T_XSR_WIDTH-1:0] reg_ddrc_t_xsr_out
  ,input logic [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_in
  ,output logic [T_OSCO_WIDTH-1:0] reg_ddrc_t_osco_out

   // DRAMTMG17
  ,input logic [T_VRCG_DISABLE_WIDTH-1:0] reg_ddrc_t_vrcg_disable_in
  ,output logic [T_VRCG_DISABLE_WIDTH-1:0] reg_ddrc_t_vrcg_disable_out
  ,input logic [T_VRCG_ENABLE_WIDTH-1:0] reg_ddrc_t_vrcg_enable_in
  ,output logic [T_VRCG_ENABLE_WIDTH-1:0] reg_ddrc_t_vrcg_enable_out



//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: not used, reserved for future
//spyglass enable_block W240

  ,input logic                                                  reg_ddrc_lpddr5


  ,input logic                                                  reg_ddrc_frequency_ratio
);

localparam ROUNDING_BITS_FR2 = 1;
localparam ROUNDING_BITS_FR4 = 2;

// In LPDDR5, core_clk and DRAM clk is 1:1. And the unit of t_pgm* is DRAM clk cycle. No need to device.
// reg_ddrc_t_pgm_x1_x1024
assign reg_ddrc_t_pgm_x1_x1024_out = reg_ddrc_t_pgm_x1_x1024_in;
// reg_ddrc_t_pgm_x1_x1024
assign reg_ddrc_t_pgm_x1_sel_out = reg_ddrc_t_pgm_x1_sel_in;  
// reg_ddrc_t_pgmpst_x32
assign reg_ddrc_t_pgmpst_x32_out = reg_ddrc_t_pgmpst_x32_in;
// reg_ddrc_t_pgm_exit
assign reg_ddrc_t_pgm_exit_out = reg_ddrc_t_pgm_exit_in;

// reg_ddrc_t_zq_long_nop
logic[$bits(reg_ddrc_t_zq_long_nop_in)-1:0] reg_ddrc_t_zq_long_nop_int;
logic[$bits(reg_ddrc_t_zq_long_nop_in)-1:0] reg_ddrc_t_zq_long_nop_int_fr2;
logic[$bits(reg_ddrc_t_zq_long_nop_in)-1:0] reg_ddrc_t_zq_long_nop_int_fr4;
assign reg_ddrc_t_zq_long_nop_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_zq_long_nop_in[$bits(reg_ddrc_t_zq_long_nop_in)-1:ROUNDING_BITS_FR2]} +
                ((|reg_ddrc_t_zq_long_nop_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_zq_long_nop_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_zq_long_nop_int_fr2){1'b0}});
assign reg_ddrc_t_zq_long_nop_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_zq_long_nop_in[$bits(reg_ddrc_t_zq_long_nop_in)-1:ROUNDING_BITS_FR4]} +
                ((|reg_ddrc_t_zq_long_nop_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_zq_long_nop_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_zq_long_nop_int_fr4){1'b0}});
assign reg_ddrc_t_zq_long_nop_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_zq_long_nop_int_fr4 : reg_ddrc_t_zq_long_nop_int_fr2;
assign reg_ddrc_t_zq_long_nop_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_zq_long_nop_in : reg_ddrc_t_zq_long_nop_int;

// reg_ddrc_t_zq_short_nop
logic[$bits(reg_ddrc_t_zq_short_nop_in)-1:0] reg_ddrc_t_zq_short_nop_int;
logic[$bits(reg_ddrc_t_zq_short_nop_in)-1:0] reg_ddrc_t_zq_short_nop_int_fr2;
logic[$bits(reg_ddrc_t_zq_short_nop_in)-1:0] reg_ddrc_t_zq_short_nop_int_fr4;
assign reg_ddrc_t_zq_short_nop_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_zq_short_nop_in[$bits(reg_ddrc_t_zq_short_nop_in)-1:ROUNDING_BITS_FR2]} +
                ((|reg_ddrc_t_zq_short_nop_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_zq_short_nop_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_zq_short_nop_int_fr2){1'b0}});
assign reg_ddrc_t_zq_short_nop_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_zq_short_nop_in[$bits(reg_ddrc_t_zq_short_nop_in)-1:ROUNDING_BITS_FR4]} +
                ((|reg_ddrc_t_zq_short_nop_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_zq_short_nop_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_zq_short_nop_int_fr4){1'b0}});
assign reg_ddrc_t_zq_short_nop_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_zq_short_nop_int_fr4 : reg_ddrc_t_zq_short_nop_int_fr2;
assign reg_ddrc_t_zq_short_nop_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_zq_short_nop_in : reg_ddrc_t_zq_short_nop_int;

// reg_ddrc_t_zq_reset_nop
logic[$bits(reg_ddrc_t_zq_reset_nop_in)-1:0] reg_ddrc_t_zq_reset_nop_int;
logic[$bits(reg_ddrc_t_zq_reset_nop_in)-1:0] reg_ddrc_t_zq_reset_nop_int_fr2;
logic[$bits(reg_ddrc_t_zq_reset_nop_in)-1:0] reg_ddrc_t_zq_reset_nop_int_fr4;
assign reg_ddrc_t_zq_reset_nop_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_zq_reset_nop_in[$bits(reg_ddrc_t_zq_reset_nop_in)-1:ROUNDING_BITS_FR2]} +
                ((|reg_ddrc_t_zq_reset_nop_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_zq_reset_nop_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_zq_reset_nop_out){1'b0}});
assign reg_ddrc_t_zq_reset_nop_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_zq_reset_nop_in[$bits(reg_ddrc_t_zq_reset_nop_in)-1:ROUNDING_BITS_FR4]} +
                ((|reg_ddrc_t_zq_reset_nop_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_zq_reset_nop_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_zq_reset_nop_out){1'b0}});
assign reg_ddrc_t_zq_reset_nop_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_zq_reset_nop_int_fr4 : reg_ddrc_t_zq_reset_nop_int_fr2;
assign reg_ddrc_t_zq_reset_nop_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_zq_reset_nop_in : reg_ddrc_t_zq_reset_nop_int;





   // DERATEINT
// reg_ddrc_mr4_read_interval
logic[$bits(reg_ddrc_mr4_read_interval_in)-1:0] reg_ddrc_mr4_read_interval_int;
logic[$bits(reg_ddrc_mr4_read_interval_in)-1:0] reg_ddrc_mr4_read_interval_int_fr2;
logic[$bits(reg_ddrc_mr4_read_interval_in)-1:0] reg_ddrc_mr4_read_interval_int_fr4;
assign reg_ddrc_mr4_read_interval_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_mr4_read_interval_in[$bits(reg_ddrc_mr4_read_interval_in)-1:ROUNDING_BITS_FR2]} +
                ((|reg_ddrc_mr4_read_interval_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_mr4_read_interval_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_mr4_read_interval_out){1'b0}});
assign reg_ddrc_mr4_read_interval_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_mr4_read_interval_in[$bits(reg_ddrc_mr4_read_interval_in)-1:ROUNDING_BITS_FR4]} +
                ((|reg_ddrc_mr4_read_interval_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_mr4_read_interval_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_mr4_read_interval_out){1'b0}});
assign reg_ddrc_mr4_read_interval_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_mr4_read_interval_int_fr4 : reg_ddrc_mr4_read_interval_int_fr2;
assign reg_ddrc_mr4_read_interval_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_mr4_read_interval_in : reg_ddrc_mr4_read_interval_int;

   // ECCCFG0
// reg_ddrc_blk_channel_idle_time_x32
logic[$bits(reg_ddrc_blk_channel_idle_time_x32_in)-1:0] reg_ddrc_blk_channel_idle_time_x32_int;
logic[$bits(reg_ddrc_blk_channel_idle_time_x32_in)-1:0] reg_ddrc_blk_channel_idle_time_x32_int_fr2;
logic[$bits(reg_ddrc_blk_channel_idle_time_x32_in)-1:0] reg_ddrc_blk_channel_idle_time_x32_int_fr4;
assign reg_ddrc_blk_channel_idle_time_x32_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_blk_channel_idle_time_x32_in[$bits(reg_ddrc_blk_channel_idle_time_x32_in)-1:ROUNDING_BITS_FR2]} +
                ((|reg_ddrc_blk_channel_idle_time_x32_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_blk_channel_idle_time_x32_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_blk_channel_idle_time_x32_int_fr2){1'b0}});
assign reg_ddrc_blk_channel_idle_time_x32_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_blk_channel_idle_time_x32_in[$bits(reg_ddrc_blk_channel_idle_time_x32_in)-1:ROUNDING_BITS_FR4]} +
                ((|reg_ddrc_blk_channel_idle_time_x32_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_blk_channel_idle_time_x32_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_blk_channel_idle_time_x32_int_fr4){1'b0}});
assign reg_ddrc_blk_channel_idle_time_x32_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_blk_channel_idle_time_x32_int_fr4 : reg_ddrc_blk_channel_idle_time_x32_int_fr2;
assign reg_ddrc_blk_channel_idle_time_x32_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_blk_channel_idle_time_x32_in : reg_ddrc_blk_channel_idle_time_x32_int;


// reg_ddrc_t_rfc_min
logic [$bits(reg_ddrc_t_rfc_min_in)-1:0] reg_ddrc_t_rfc_min_int;
logic [$bits(reg_ddrc_t_rfc_min_in)-1:0] reg_ddrc_t_rfc_min_int_fr2;
logic [$bits(reg_ddrc_t_rfc_min_in)-1:0] reg_ddrc_t_rfc_min_int_fr4;
assign reg_ddrc_t_rfc_min_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rfc_min_in[$bits(reg_ddrc_t_rfc_min_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rfc_min_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rfc_min_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rfc_min_int_fr2){1'b0}});
assign reg_ddrc_t_rfc_min_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rfc_min_in[$bits(reg_ddrc_t_rfc_min_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rfc_min_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rfc_min_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rfc_min_int_fr4){1'b0}});
assign reg_ddrc_t_rfc_min_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rfc_min_int_fr4 : reg_ddrc_t_rfc_min_int_fr2;
assign reg_ddrc_t_rfc_min_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_rfc_min_in : reg_ddrc_t_rfc_min_int;

// reg_ddrc_t_rfc_min_ab
logic [$bits(reg_ddrc_t_rfc_min_ab_in)-1:0] reg_ddrc_t_rfc_min_ab_int;
logic [$bits(reg_ddrc_t_rfc_min_ab_in)-1:0] reg_ddrc_t_rfc_min_ab_int_fr2;
logic [$bits(reg_ddrc_t_rfc_min_ab_in)-1:0] reg_ddrc_t_rfc_min_ab_int_fr4;
assign reg_ddrc_t_rfc_min_ab_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rfc_min_ab_in[$bits(reg_ddrc_t_rfc_min_ab_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rfc_min_ab_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rfc_min_ab_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rfc_min_ab_int_fr2){1'b0}});
assign reg_ddrc_t_rfc_min_ab_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rfc_min_ab_in[$bits(reg_ddrc_t_rfc_min_ab_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rfc_min_ab_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rfc_min_ab_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rfc_min_ab_int_fr4){1'b0}});
assign reg_ddrc_t_rfc_min_ab_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rfc_min_ab_int_fr4 : reg_ddrc_t_rfc_min_ab_int_fr2;
assign reg_ddrc_t_rfc_min_ab_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_rfc_min_ab_in : reg_ddrc_t_rfc_min_ab_int;

// reg_ddrc_t_refi_x1_x32
logic [$bits(reg_ddrc_t_refi_x1_x32_in)-1:0] reg_ddrc_t_refi_x1_x32_int;
logic [$bits(reg_ddrc_t_refi_x1_x32_in)-1:0] reg_ddrc_t_refi_x1_x32_int_fr2;
logic [$bits(reg_ddrc_t_refi_x1_x32_in)-1:0] reg_ddrc_t_refi_x1_x32_int_fr4;
assign reg_ddrc_t_refi_x1_x32_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_refi_x1_x32_in[$bits(reg_ddrc_t_refi_x1_x32_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_t_refi_x1_x32_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_refi_x1_x32_in[$bits(reg_ddrc_t_refi_x1_x32_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_t_refi_x1_x32_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_refi_x1_x32_int_fr4 : reg_ddrc_t_refi_x1_x32_int_fr2;
assign reg_ddrc_t_refi_x1_x32_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_refi_x1_x32_in : reg_ddrc_t_refi_x1_x32_int;

// reg_ddrc_refresh_margin
logic [$bits(reg_ddrc_refresh_margin_in)-1:0] reg_ddrc_refresh_margin_int;
logic [$bits(reg_ddrc_refresh_margin_in)-1:0] reg_ddrc_refresh_margin_int_fr2;
logic [$bits(reg_ddrc_refresh_margin_in)-1:0] reg_ddrc_refresh_margin_int_fr4;
assign reg_ddrc_refresh_margin_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_refresh_margin_in[$bits(reg_ddrc_refresh_margin_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_refresh_margin_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_refresh_margin_in[$bits(reg_ddrc_refresh_margin_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_refresh_margin_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_refresh_margin_int_fr4 : reg_ddrc_refresh_margin_int_fr2;
assign reg_ddrc_refresh_margin_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_refresh_margin_in : reg_ddrc_refresh_margin_int;

// reg_ddrc_refresh_to_x1_x32
logic[$bits(reg_ddrc_refresh_to_x1_x32_in)-1:0] reg_ddrc_refresh_to_x1_x32_int;
logic[$bits(reg_ddrc_refresh_to_x1_x32_in)-1:0] reg_ddrc_refresh_to_x1_x32_int_fr2;
logic[$bits(reg_ddrc_refresh_to_x1_x32_in)-1:0] reg_ddrc_refresh_to_x1_x32_int_fr4;
assign reg_ddrc_refresh_to_x1_x32_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_refresh_to_x1_x32_in[$bits(reg_ddrc_refresh_to_x1_x32_in)-1:ROUNDING_BITS_FR2]};
assign reg_ddrc_refresh_to_x1_x32_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_refresh_to_x1_x32_in[$bits(reg_ddrc_refresh_to_x1_x32_in)-1:ROUNDING_BITS_FR4]};
assign reg_ddrc_refresh_to_x1_x32_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_refresh_to_x1_x32_int_fr4 : reg_ddrc_refresh_to_x1_x32_int_fr2;
assign reg_ddrc_refresh_to_x1_x32_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_refresh_to_x1_x32_in : reg_ddrc_refresh_to_x1_x32_int;

// reg_ddrc_refresh_to_ab_x32
logic[$bits(reg_ddrc_refresh_to_ab_x32_in)-1:0] reg_ddrc_refresh_to_ab_x32_int;
logic[$bits(reg_ddrc_refresh_to_ab_x32_in)-1:0] reg_ddrc_refresh_to_ab_x32_int_fr2;
logic[$bits(reg_ddrc_refresh_to_ab_x32_in)-1:0] reg_ddrc_refresh_to_ab_x32_int_fr4;
assign reg_ddrc_refresh_to_ab_x32_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_refresh_to_ab_x32_in[$bits(reg_ddrc_refresh_to_ab_x32_in)-1:ROUNDING_BITS_FR2]} +
                ((|reg_ddrc_refresh_to_ab_x32_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_refresh_to_ab_x32_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_refresh_to_ab_x32_int_fr2){1'b0}});
assign reg_ddrc_refresh_to_ab_x32_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_refresh_to_ab_x32_in[$bits(reg_ddrc_refresh_to_ab_x32_in)-1:ROUNDING_BITS_FR4]} +
                ((|reg_ddrc_refresh_to_ab_x32_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_refresh_to_ab_x32_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_refresh_to_ab_x32_int_fr4){1'b0}});
assign reg_ddrc_refresh_to_ab_x32_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_refresh_to_ab_x32_int_fr4 : reg_ddrc_refresh_to_ab_x32_int_fr2;
assign reg_ddrc_refresh_to_ab_x32_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_refresh_to_ab_x32_in : reg_ddrc_refresh_to_ab_x32_int;



logic[$bits(reg_ddrc_refresh_timer0_start_value_x32_in)-1:0] reg_ddrc_refresh_timer0_start_value_x32_int;
logic[$bits(reg_ddrc_refresh_timer0_start_value_x32_in)-1:0] reg_ddrc_refresh_timer0_start_value_x32_int_fr2;
logic[$bits(reg_ddrc_refresh_timer0_start_value_x32_in)-1:0] reg_ddrc_refresh_timer0_start_value_x32_int_fr4;
assign reg_ddrc_refresh_timer0_start_value_x32_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_refresh_timer0_start_value_x32_in[$bits(reg_ddrc_refresh_timer0_start_value_x32_in) - 1 : ROUNDING_BITS_FR2]};
assign reg_ddrc_refresh_timer0_start_value_x32_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_refresh_timer0_start_value_x32_in[$bits(reg_ddrc_refresh_timer0_start_value_x32_in) - 1 : ROUNDING_BITS_FR4]};
assign reg_ddrc_refresh_timer0_start_value_x32_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_refresh_timer0_start_value_x32_int_fr4 : reg_ddrc_refresh_timer0_start_value_x32_int_fr2;
assign reg_ddrc_refresh_timer0_start_value_x32_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_refresh_timer0_start_value_x32_in : reg_ddrc_refresh_timer0_start_value_x32_int;
logic[$bits(reg_ddrc_refresh_timer1_start_value_x32_in)-1:0] reg_ddrc_refresh_timer1_start_value_x32_int;
logic[$bits(reg_ddrc_refresh_timer1_start_value_x32_in)-1:0] reg_ddrc_refresh_timer1_start_value_x32_int_fr2;
logic[$bits(reg_ddrc_refresh_timer1_start_value_x32_in)-1:0] reg_ddrc_refresh_timer1_start_value_x32_int_fr4;
assign reg_ddrc_refresh_timer1_start_value_x32_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_refresh_timer1_start_value_x32_in[$bits(reg_ddrc_refresh_timer1_start_value_x32_in) - 1 : ROUNDING_BITS_FR2]};
assign reg_ddrc_refresh_timer1_start_value_x32_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_refresh_timer1_start_value_x32_in[$bits(reg_ddrc_refresh_timer1_start_value_x32_in) - 1 : ROUNDING_BITS_FR4]};
assign reg_ddrc_refresh_timer1_start_value_x32_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_refresh_timer1_start_value_x32_int_fr4 : reg_ddrc_refresh_timer1_start_value_x32_int_fr2;
assign reg_ddrc_refresh_timer1_start_value_x32_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_refresh_timer1_start_value_x32_in : reg_ddrc_refresh_timer1_start_value_x32_int;



logic[$bits(reg_ddrc_derated_t_rcd_in)-1:0] reg_ddrc_derated_t_rcd_int;
logic[$bits(reg_ddrc_derated_t_rcd_in)-1:0] reg_ddrc_derated_t_rcd_int_fr2;
logic[$bits(reg_ddrc_derated_t_rcd_in)-1:0] reg_ddrc_derated_t_rcd_int_fr4;
assign reg_ddrc_derated_t_rcd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_derated_t_rcd_in[$bits(reg_ddrc_derated_t_rcd_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_derated_t_rcd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_derated_t_rcd_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rcd_out){1'b0}}); 
assign reg_ddrc_derated_t_rcd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_derated_t_rcd_in[$bits(reg_ddrc_derated_t_rcd_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_derated_t_rcd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_derated_t_rcd_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rcd_out){1'b0}}); 
assign reg_ddrc_derated_t_rcd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_derated_t_rcd_int_fr4 : reg_ddrc_derated_t_rcd_int_fr2;
assign reg_ddrc_derated_t_rcd_out = (reg_ddrc_lpddr5) ? reg_ddrc_derated_t_rcd_in : reg_ddrc_derated_t_rcd_int;
 

logic[$bits(reg_ddrc_derated_t_ras_min_in)-1:0] reg_ddrc_derated_t_ras_min_int;
logic[$bits(reg_ddrc_derated_t_ras_min_in)-1:0] reg_ddrc_derated_t_ras_min_int_fr2;
logic[$bits(reg_ddrc_derated_t_ras_min_in)-1:0] reg_ddrc_derated_t_ras_min_int_fr4;
assign reg_ddrc_derated_t_ras_min_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_derated_t_ras_min_in[$bits(reg_ddrc_derated_t_ras_min_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_derated_t_ras_min_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_derated_t_ras_min_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_ras_min_out){1'b0}}); 
assign reg_ddrc_derated_t_ras_min_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_derated_t_ras_min_in[$bits(reg_ddrc_derated_t_ras_min_in) - 1: ROUNDING_BITS_FR4]} +
        ((reg_ddrc_derated_t_ras_min_in[ROUNDING_BITS_FR4-1:0]==2'b11) ? {{($bits(reg_ddrc_derated_t_ras_min_out)-2){1'b0}},2'b10} : {{($bits(reg_ddrc_derated_t_ras_min_out)-1){1'b0}},1'b1});
assign reg_ddrc_derated_t_ras_min_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_derated_t_ras_min_int_fr4 : reg_ddrc_derated_t_ras_min_int_fr2;
assign reg_ddrc_derated_t_ras_min_out = (reg_ddrc_lpddr5) ? reg_ddrc_derated_t_ras_min_in : reg_ddrc_derated_t_ras_min_int;
 

logic[$bits(reg_ddrc_derated_t_rp_in)-1:0] reg_ddrc_derated_t_rp_int;
logic[$bits(reg_ddrc_derated_t_rp_in)-1:0] reg_ddrc_derated_t_rp_int_fr2;
logic[$bits(reg_ddrc_derated_t_rp_in)-1:0] reg_ddrc_derated_t_rp_int_fr4;
assign reg_ddrc_derated_t_rp_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_derated_t_rp_in[$bits(reg_ddrc_derated_t_rp_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_derated_t_rp_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_derated_t_rp_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rp_out){1'b0}}); 
assign reg_ddrc_derated_t_rp_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_derated_t_rp_in[$bits(reg_ddrc_derated_t_rp_in) - 1: ROUNDING_BITS_FR4]} +
        ((reg_ddrc_derated_t_rp_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_derated_t_rp_out)-1){1'b0}},1'b1} :
                                                                      {  $bits(reg_ddrc_derated_t_rp_out)   {1'b0}});
assign reg_ddrc_derated_t_rp_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_derated_t_rp_int_fr4 : reg_ddrc_derated_t_rp_int_fr2;
assign reg_ddrc_derated_t_rp_out = (reg_ddrc_lpddr5) ? reg_ddrc_derated_t_rp_in : reg_ddrc_derated_t_rp_int;
 

logic[$bits(reg_ddrc_derated_t_rrd_in)-1:0] reg_ddrc_derated_t_rrd_int;
logic[$bits(reg_ddrc_derated_t_rrd_in)-1:0] reg_ddrc_derated_t_rrd_int_fr2;
logic[$bits(reg_ddrc_derated_t_rrd_in)-1:0] reg_ddrc_derated_t_rrd_int_fr4;
assign reg_ddrc_derated_t_rrd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_derated_t_rrd_in[$bits(reg_ddrc_derated_t_rrd_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_derated_t_rrd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_derated_t_rrd_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rrd_out){1'b0}}); 
assign reg_ddrc_derated_t_rrd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_derated_t_rrd_in[$bits(reg_ddrc_derated_t_rrd_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_derated_t_rrd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_derated_t_rrd_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rrd_out){1'b0}}); 
assign reg_ddrc_derated_t_rrd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_derated_t_rrd_int_fr4 : reg_ddrc_derated_t_rrd_int_fr2;
assign reg_ddrc_derated_t_rrd_out = (reg_ddrc_lpddr5) ? reg_ddrc_derated_t_rrd_in : reg_ddrc_derated_t_rrd_int;
 

logic[$bits(reg_ddrc_derated_t_rc_in)-1:0] reg_ddrc_derated_t_rc_int;
logic[$bits(reg_ddrc_derated_t_rc_in)-1:0] reg_ddrc_derated_t_rc_int_fr2;
logic[$bits(reg_ddrc_derated_t_rc_in)-1:0] reg_ddrc_derated_t_rc_int_fr4;
assign reg_ddrc_derated_t_rc_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_derated_t_rc_in[$bits(reg_ddrc_derated_t_rc_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_derated_t_rc_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_derated_t_rc_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rc_out){1'b0}}); 
assign reg_ddrc_derated_t_rc_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_derated_t_rc_in[$bits(reg_ddrc_derated_t_rc_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_derated_t_rc_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_derated_t_rc_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_derated_t_rc_out){1'b0}}); 
assign reg_ddrc_derated_t_rc_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_derated_t_rc_int_fr4 : reg_ddrc_derated_t_rc_int_fr2;
assign reg_ddrc_derated_t_rc_out = (reg_ddrc_lpddr5) ? reg_ddrc_derated_t_rc_in : reg_ddrc_derated_t_rc_int;
 

logic[$bits(reg_ddrc_t_pbr2pbr_in)-1:0] reg_ddrc_t_pbr2pbr_int;
logic[$bits(reg_ddrc_t_pbr2pbr_in)-1:0] reg_ddrc_t_pbr2pbr_int_fr2;
logic[$bits(reg_ddrc_t_pbr2pbr_in)-1:0] reg_ddrc_t_pbr2pbr_int_fr4;
assign reg_ddrc_t_pbr2pbr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_pbr2pbr_in[$bits(reg_ddrc_t_pbr2pbr_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_pbr2pbr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_pbr2pbr_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_pbr2pbr_out){1'b0}});
assign reg_ddrc_t_pbr2pbr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_pbr2pbr_in[$bits(reg_ddrc_t_pbr2pbr_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_pbr2pbr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_pbr2pbr_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_pbr2pbr_out){1'b0}});
assign reg_ddrc_t_pbr2pbr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_pbr2pbr_int_fr4 : reg_ddrc_t_pbr2pbr_int_fr2;
assign reg_ddrc_t_pbr2pbr_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_pbr2pbr_in : reg_ddrc_t_pbr2pbr_int;
 


logic [$bits(reg_ddrc_t_rfmpb_in)-1:0] reg_ddrc_t_rfmpb_int;
logic [$bits(reg_ddrc_t_rfmpb_in)-1:0] reg_ddrc_t_rfmpb_int_fr2;
logic [$bits(reg_ddrc_t_rfmpb_in)-1:0] reg_ddrc_t_rfmpb_int_fr4;
assign reg_ddrc_t_rfmpb_int_fr2  = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rfmpb_in[$bits(reg_ddrc_t_rfmpb_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rfmpb_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rfmpb_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rfmpb_int_fr2){1'b0}});
assign reg_ddrc_t_rfmpb_int_fr4  = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rfmpb_in[$bits(reg_ddrc_t_rfmpb_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rfmpb_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rfmpb_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rfmpb_int_fr4){1'b0}});
assign reg_ddrc_t_rfmpb_int      = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rfmpb_int_fr4 : reg_ddrc_t_rfmpb_int_fr2;
assign reg_ddrc_t_rfmpb_out      = (reg_ddrc_lpddr5) ? reg_ddrc_t_rfmpb_in : reg_ddrc_t_rfmpb_int;


// reg_ddrc_diff_rank_rd_gap
logic [$bits(reg_ddrc_diff_rank_rd_gap_in)-1:0] reg_ddrc_diff_rank_rd_gap_int;
logic [$bits(reg_ddrc_diff_rank_rd_gap_in)-1:0] reg_ddrc_diff_rank_rd_gap_int_fr2;
logic [$bits(reg_ddrc_diff_rank_rd_gap_in)-1:0] reg_ddrc_diff_rank_rd_gap_int_fr4;
assign reg_ddrc_diff_rank_rd_gap_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_diff_rank_rd_gap_in[$bits(reg_ddrc_diff_rank_rd_gap_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_diff_rank_rd_gap_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_diff_rank_rd_gap_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_diff_rank_rd_gap_int_fr2){1'b0}});
assign reg_ddrc_diff_rank_rd_gap_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_diff_rank_rd_gap_in[$bits(reg_ddrc_diff_rank_rd_gap_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_diff_rank_rd_gap_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_diff_rank_rd_gap_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_diff_rank_rd_gap_int_fr4){1'b0}});
assign reg_ddrc_diff_rank_rd_gap_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_diff_rank_rd_gap_int_fr4 : reg_ddrc_diff_rank_rd_gap_int_fr2;
assign reg_ddrc_diff_rank_rd_gap_out = (reg_ddrc_lpddr5) ? reg_ddrc_diff_rank_rd_gap_in : reg_ddrc_diff_rank_rd_gap_int;

// reg_ddrc_diff_rank_wr_gap
logic [$bits(reg_ddrc_diff_rank_wr_gap_in)-1:0] reg_ddrc_diff_rank_wr_gap_int;
logic [$bits(reg_ddrc_diff_rank_wr_gap_in)-1:0] reg_ddrc_diff_rank_wr_gap_int_fr2;
logic [$bits(reg_ddrc_diff_rank_wr_gap_in)-1:0] reg_ddrc_diff_rank_wr_gap_int_fr4;
assign reg_ddrc_diff_rank_wr_gap_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_diff_rank_wr_gap_in[$bits(reg_ddrc_diff_rank_wr_gap_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_diff_rank_wr_gap_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_diff_rank_wr_gap_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_diff_rank_wr_gap_int_fr2){1'b0}});
assign reg_ddrc_diff_rank_wr_gap_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_diff_rank_wr_gap_in[$bits(reg_ddrc_diff_rank_wr_gap_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_diff_rank_wr_gap_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_diff_rank_wr_gap_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_diff_rank_wr_gap_int_fr4){1'b0}});
assign reg_ddrc_diff_rank_wr_gap_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_diff_rank_wr_gap_int_fr4 : reg_ddrc_diff_rank_wr_gap_int_fr2;
assign reg_ddrc_diff_rank_wr_gap_out = (reg_ddrc_lpddr5) ? reg_ddrc_diff_rank_wr_gap_in : reg_ddrc_diff_rank_wr_gap_int;

// reg_ddrc_rd2wr_dr
logic [$bits(reg_ddrc_rd2wr_dr_in)-1:0] reg_ddrc_rd2wr_dr_int;
logic [$bits(reg_ddrc_rd2wr_dr_in)-1:0] reg_ddrc_rd2wr_dr_int_fr2;
logic [$bits(reg_ddrc_rd2wr_dr_in)-1:0] reg_ddrc_rd2wr_dr_int_fr4;
assign reg_ddrc_rd2wr_dr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_rd2wr_dr_in[$bits(reg_ddrc_rd2wr_dr_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_rd2wr_dr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_rd2wr_dr_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2wr_dr_int_fr2){1'b0}});
assign reg_ddrc_rd2wr_dr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_rd2wr_dr_in[$bits(reg_ddrc_rd2wr_dr_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_rd2wr_dr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_rd2wr_dr_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2wr_dr_int_fr4){1'b0}});
assign reg_ddrc_rd2wr_dr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_rd2wr_dr_int_fr4 : reg_ddrc_rd2wr_dr_int_fr2;
assign reg_ddrc_rd2wr_dr_out = (reg_ddrc_lpddr5) ? reg_ddrc_rd2wr_dr_in : reg_ddrc_rd2wr_dr_int;

// reg_ddrc_wr2rd_dr
logic [$bits(reg_ddrc_wr2rd_dr_in)-1:0] reg_ddrc_wr2rd_dr_int;
logic [$bits(reg_ddrc_wr2rd_dr_in)-1:0] reg_ddrc_wr2rd_dr_int_fr2;
logic [$bits(reg_ddrc_wr2rd_dr_in)-1:0] reg_ddrc_wr2rd_dr_int_fr4;
assign reg_ddrc_wr2rd_dr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_wr2rd_dr_in[$bits(reg_ddrc_wr2rd_dr_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_wr2rd_dr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_wr2rd_dr_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2rd_dr_int_fr2){1'b0}});
assign reg_ddrc_wr2rd_dr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_wr2rd_dr_in[$bits(reg_ddrc_wr2rd_dr_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_wr2rd_dr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_wr2rd_dr_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2rd_dr_int_fr4){1'b0}});
assign reg_ddrc_wr2rd_dr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_wr2rd_dr_int_fr4 : reg_ddrc_wr2rd_dr_int_fr2;
assign reg_ddrc_wr2rd_dr_out = (reg_ddrc_lpddr5) ? reg_ddrc_wr2rd_dr_in : reg_ddrc_wr2rd_dr_int;


// reg_ddrc_t_ras_min
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_int;
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_div;
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_div_fr2;
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_div_fr4;
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_round;
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_round_fr2;
logic [$bits(reg_ddrc_t_ras_min_in)-1:0] reg_ddrc_t_ras_min_round_fr4;
logic [$bits(reg_ddrc_t_ras_min_int):0]  reg_ddrc_t_ras_min_int_wider;

assign reg_ddrc_t_ras_min_div_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ras_min_in[$bits(reg_ddrc_t_ras_min_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_t_ras_min_div_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ras_min_in[$bits(reg_ddrc_t_ras_min_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_t_ras_min_div = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ras_min_div_fr4 : reg_ddrc_t_ras_min_div_fr2;

assign reg_ddrc_t_ras_min_round_fr2 = ((|reg_ddrc_t_ras_min_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ras_min_round_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ras_min_round_fr2){1'b0}});
assign reg_ddrc_t_ras_min_round_fr4 = (reg_ddrc_t_ras_min_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_t_ras_min_round_fr4)-2){1'b0}},2'b10} :
                                                                                                {{($bits(reg_ddrc_t_ras_min_round_fr4)-1){1'b0}},1'b1};
assign reg_ddrc_t_ras_min_round = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ras_min_round_fr4 : reg_ddrc_t_ras_min_round_fr2;
assign reg_ddrc_t_ras_min_int_wider = reg_ddrc_t_ras_min_div + reg_ddrc_t_ras_min_round;
assign reg_ddrc_t_ras_min_int = reg_ddrc_t_ras_min_int_wider[$bits(reg_ddrc_t_ras_min_int)-1:0];

assign reg_ddrc_t_ras_min_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_ras_min_in : reg_ddrc_t_ras_min_int;

// reg_ddrc_t_ras_max
logic [$bits(reg_ddrc_t_ras_max_in)-1:0] reg_ddrc_t_ras_max_m1;
logic [$bits(reg_ddrc_t_ras_max_in)-1:0] reg_ddrc_t_ras_max_int;
logic [$bits(reg_ddrc_t_ras_max_in)-1:0] reg_ddrc_t_ras_max_int_fr2;
logic [$bits(reg_ddrc_t_ras_max_in)-1:0] reg_ddrc_t_ras_max_int_fr4;
assign reg_ddrc_t_ras_max_m1      = reg_ddrc_t_ras_max_in - {{($bits(reg_ddrc_t_ras_max_m1)-1){1'b0}},1'b1};
assign reg_ddrc_t_ras_max_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ras_max_m1[$bits(reg_ddrc_t_ras_max_m1) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_t_ras_max_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ras_max_m1[$bits(reg_ddrc_t_ras_max_m1) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_t_ras_max_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ras_max_int_fr4 : reg_ddrc_t_ras_max_int_fr2;
assign reg_ddrc_t_ras_max_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_ras_max_in : reg_ddrc_t_ras_max_int;

// reg_ddrc_t_faw
logic [$bits(reg_ddrc_t_faw_in)-1:0] reg_ddrc_t_faw_int;
logic [$bits(reg_ddrc_t_faw_in)-1:0] reg_ddrc_t_faw_int_fr2;
logic [$bits(reg_ddrc_t_faw_in)-1:0] reg_ddrc_t_faw_int_fr4;
assign reg_ddrc_t_faw_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_faw_in[$bits(reg_ddrc_t_faw_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_faw_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_faw_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_faw_int_fr2){1'b0}});
assign reg_ddrc_t_faw_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_faw_in[$bits(reg_ddrc_t_faw_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_faw_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_faw_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_faw_int_fr4){1'b0}});
assign reg_ddrc_t_faw_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_faw_int_fr4 : reg_ddrc_t_faw_int_fr2;
assign reg_ddrc_t_faw_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_faw_in : reg_ddrc_t_faw_int;

// reg_ddrc_wr2pre
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_int;
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_div;
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_div_fr2;
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_div_fr4;
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_round;
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_round_fr2;
logic [$bits(reg_ddrc_wr2pre_in)-1:0] reg_ddrc_wr2pre_round_fr4;
logic [$bits(reg_ddrc_wr2pre_int):0] reg_ddrc_wr2pre_int_wider;
assign reg_ddrc_wr2pre_div_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_wr2pre_in[$bits(reg_ddrc_wr2pre_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_wr2pre_div_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_wr2pre_in[$bits(reg_ddrc_wr2pre_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_wr2pre_div = (reg_ddrc_frequency_ratio) ? reg_ddrc_wr2pre_div_fr4 : reg_ddrc_wr2pre_div_fr2;

assign reg_ddrc_wr2pre_round_fr2 = ((|reg_ddrc_wr2pre_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_wr2pre_round_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2pre_round_fr2){1'b0}});
assign reg_ddrc_wr2pre_round_fr4 = ((reg_ddrc_wr2pre_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_wr2pre_round_fr4)-2){1'b0}},2'b10} :
                                                                                           {{($bits(reg_ddrc_wr2pre_round_fr4)-1){1'b0}},1'b1});
assign reg_ddrc_wr2pre_round = (reg_ddrc_frequency_ratio) ? reg_ddrc_wr2pre_round_fr4 : reg_ddrc_wr2pre_round_fr2;
assign reg_ddrc_wr2pre_int_wider = reg_ddrc_wr2pre_div + reg_ddrc_wr2pre_round;
assign reg_ddrc_wr2pre_int = reg_ddrc_wr2pre_int_wider[$bits(reg_ddrc_wr2pre_int)-1:0];
assign reg_ddrc_wr2pre_out = (reg_ddrc_lpddr5) ? reg_ddrc_wr2pre_in : reg_ddrc_wr2pre_int;

// reg_ddrc_lpddr4_diff_bank_rwa2pre
assign reg_ddrc_lpddr4_diff_bank_rwa2pre_out = reg_ddrc_lpddr4_diff_bank_rwa2pre_in;


// reg_ddrc_wra2pre
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_int;
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_div;
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_div_fr2;
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_div_fr4;
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_round;
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_round_fr2;
logic [$bits(reg_ddrc_wra2pre_in)-1:0] reg_ddrc_wra2pre_round_fr4;
logic [$bits(reg_ddrc_wra2pre_int):0] reg_ddrc_wra2pre_int_wider;
assign reg_ddrc_wra2pre_div_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_wra2pre_in[$bits(reg_ddrc_wra2pre_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_wra2pre_div_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_wra2pre_in[$bits(reg_ddrc_wra2pre_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_wra2pre_div = (reg_ddrc_frequency_ratio) ? reg_ddrc_wra2pre_div_fr4 : reg_ddrc_wra2pre_div_fr2;

assign reg_ddrc_wra2pre_round_fr2 = ((|reg_ddrc_wra2pre_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_wra2pre_round_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wra2pre_round_fr2){1'b0}});
assign reg_ddrc_wra2pre_round_fr4 = ((reg_ddrc_wra2pre_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_wra2pre_round_fr4)-2){1'b0}},2'b10} :
                                                                                             {{($bits(reg_ddrc_wra2pre_round_fr4)-1){1'b0}},1'b1});
assign reg_ddrc_wra2pre_round = (reg_ddrc_frequency_ratio) ? reg_ddrc_wra2pre_round_fr4 : reg_ddrc_wra2pre_round_fr2;
assign reg_ddrc_wra2pre_int_wider = reg_ddrc_wra2pre_div + reg_ddrc_wra2pre_round;
assign reg_ddrc_wra2pre_int = reg_ddrc_wra2pre_int_wider[$bits(reg_ddrc_wra2pre_int)-1:0];
assign reg_ddrc_wra2pre_out = (reg_ddrc_lpddr5) ? reg_ddrc_wra2pre_in : reg_ddrc_wra2pre_int;


// reg_ddrc_t_xp
logic [$bits(reg_ddrc_t_xp_in)-1:0] reg_ddrc_t_xp_int;
logic [$bits(reg_ddrc_t_xp_in)-1:0] reg_ddrc_t_xp_int_fr2;
logic [$bits(reg_ddrc_t_xp_in)-1:0] reg_ddrc_t_xp_int_fr4;
assign reg_ddrc_t_xp_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_xp_in[$bits(reg_ddrc_t_xp_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_xp_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_xp_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_xp_int_fr2){1'b0}});
assign reg_ddrc_t_xp_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_xp_in[$bits(reg_ddrc_t_xp_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_xp_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_xp_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_xp_int_fr4){1'b0}});
assign reg_ddrc_t_xp_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_xp_int_fr4 : reg_ddrc_t_xp_int_fr2;
assign reg_ddrc_t_xp_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_xp_in : reg_ddrc_t_xp_int;

// reg_ddrc_rd2pre
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_int;
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_div;
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_div_fr2;
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_div_fr4;
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_round;
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_round_fr2;
logic [$bits(reg_ddrc_rd2pre_int):0] reg_ddrc_rd2pre_int_wider;
logic [$bits(reg_ddrc_rd2pre_in)-1:0] reg_ddrc_rd2pre_round_fr4;
assign reg_ddrc_rd2pre_div_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_rd2pre_in[$bits(reg_ddrc_rd2pre_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_rd2pre_div_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_rd2pre_in[$bits(reg_ddrc_rd2pre_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_rd2pre_div = (reg_ddrc_frequency_ratio) ? reg_ddrc_rd2pre_div_fr4 : reg_ddrc_rd2pre_div_fr2;

assign reg_ddrc_rd2pre_round_fr2 = ((|reg_ddrc_rd2pre_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_rd2pre_round_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2pre_round_fr2){1'b0}});
assign reg_ddrc_rd2pre_round_fr4 = ((reg_ddrc_rd2pre_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_rd2pre_round_fr4)-2){1'b0}},2'b10} :
                                                                                           {{($bits(reg_ddrc_rd2pre_round_fr4)-1){1'b0}},1'b1});
assign reg_ddrc_rd2pre_round = (reg_ddrc_frequency_ratio) ? reg_ddrc_rd2pre_round_fr4 : reg_ddrc_rd2pre_round_fr2;
assign reg_ddrc_rd2pre_int_wider = reg_ddrc_rd2pre_div + reg_ddrc_rd2pre_round;
assign reg_ddrc_rd2pre_int = reg_ddrc_rd2pre_int_wider[$bits(reg_ddrc_rd2pre_int)-1:0];
assign reg_ddrc_rd2pre_out = (reg_ddrc_lpddr5) ? reg_ddrc_rd2pre_in : reg_ddrc_rd2pre_int;

// reg_ddrc_rda2pre
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_int;
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_div;
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_div_fr2;
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_div_fr4;
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_round;
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_round_fr2;
logic [$bits(reg_ddrc_rda2pre_in)-1:0] reg_ddrc_rda2pre_round_fr4;
logic [$bits(reg_ddrc_rda2pre_int):0] reg_ddrc_rda2pre_int_wider;
assign reg_ddrc_rda2pre_div_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_rda2pre_in[$bits(reg_ddrc_rda2pre_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_rda2pre_div_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_rda2pre_in[$bits(reg_ddrc_rda2pre_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_rda2pre_div = (reg_ddrc_frequency_ratio) ? reg_ddrc_rda2pre_div_fr4 : reg_ddrc_rda2pre_div_fr2;

assign reg_ddrc_rda2pre_round_fr2 = ((|reg_ddrc_rda2pre_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_rda2pre_round_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rda2pre_round_fr2){1'b0}});
assign reg_ddrc_rda2pre_round_fr4 = ((reg_ddrc_rda2pre_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_rda2pre_round_fr4)-2){1'b0}},2'b10} :
                                                                                             {{($bits(reg_ddrc_rda2pre_round_fr4)-1){1'b0}},1'b1});
assign reg_ddrc_rda2pre_round = (reg_ddrc_frequency_ratio) ? reg_ddrc_rda2pre_round_fr4 : reg_ddrc_rda2pre_round_fr2;
assign reg_ddrc_rda2pre_int_wider = reg_ddrc_rda2pre_div + reg_ddrc_rda2pre_round;
assign reg_ddrc_rda2pre_int = reg_ddrc_rda2pre_int_wider[$bits(reg_ddrc_rda2pre_int)-1:0];
assign reg_ddrc_rda2pre_out = (reg_ddrc_lpddr5) ? reg_ddrc_rda2pre_in : reg_ddrc_rda2pre_int;

// reg_ddrc_t_rc
logic [$bits(reg_ddrc_t_rc_in)-1:0] reg_ddrc_t_rc_int;
logic [$bits(reg_ddrc_t_rc_in)-1:0] reg_ddrc_t_rc_int_fr2;
logic [$bits(reg_ddrc_t_rc_in)-1:0] reg_ddrc_t_rc_int_fr4;
assign reg_ddrc_t_rc_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rc_in[$bits(reg_ddrc_t_rc_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rc_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rc_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rc_int_fr2){1'b0}});
assign reg_ddrc_t_rc_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rc_in[$bits(reg_ddrc_t_rc_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rc_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rc_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rc_int_fr4){1'b0}});
assign reg_ddrc_t_rc_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rc_int_fr4 : reg_ddrc_t_rc_int_fr2;
assign reg_ddrc_t_rc_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_rc_in : reg_ddrc_t_rc_int;


// reg_ddrc_write_latency
logic [$bits(reg_ddrc_write_latency_in)-1:0] reg_ddrc_write_latency_int;
logic [$bits(reg_ddrc_write_latency_in)-1:0] reg_ddrc_write_latency_int_fr2;
logic [$bits(reg_ddrc_write_latency_in)-1:0] reg_ddrc_write_latency_int_fr4;
assign reg_ddrc_write_latency_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_write_latency_in[$bits(reg_ddrc_write_latency_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_write_latency_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_write_latency_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_write_latency_int_fr2){1'b0}});
assign reg_ddrc_write_latency_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_write_latency_in[$bits(reg_ddrc_write_latency_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_write_latency_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_write_latency_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_write_latency_int_fr4){1'b0}});
assign reg_ddrc_write_latency_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_write_latency_int_fr4 : reg_ddrc_write_latency_int_fr2;
assign reg_ddrc_write_latency_out = (reg_ddrc_lpddr5) ? reg_ddrc_write_latency_in : reg_ddrc_write_latency_int;

// reg_ddrc_read_latency
logic [$bits(reg_ddrc_read_latency_in)-1:0] reg_ddrc_read_latency_int;
logic [$bits(reg_ddrc_read_latency_in)-1:0] reg_ddrc_read_latency_int_fr2;
logic [$bits(reg_ddrc_read_latency_in)-1:0] reg_ddrc_read_latency_int_fr4;
assign reg_ddrc_read_latency_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_read_latency_in[$bits(reg_ddrc_read_latency_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_read_latency_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_read_latency_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_read_latency_int_fr2){1'b0}});
assign reg_ddrc_read_latency_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_read_latency_in[$bits(reg_ddrc_read_latency_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_read_latency_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_read_latency_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_read_latency_int_fr4){1'b0}});
assign reg_ddrc_read_latency_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_read_latency_int_fr4 : reg_ddrc_read_latency_int_fr2;
assign reg_ddrc_read_latency_out = (reg_ddrc_lpddr5) ? reg_ddrc_read_latency_in : reg_ddrc_read_latency_int;

// reg_ddrc_rd2wr
logic [$bits(reg_ddrc_rd2wr_in)-1:0] reg_ddrc_rd2wr_int;
logic [$bits(reg_ddrc_rd2wr_in)-1:0] reg_ddrc_rd2wr_int_fr2;
logic [$bits(reg_ddrc_rd2wr_in)-1:0] reg_ddrc_rd2wr_int_fr4;
assign reg_ddrc_rd2wr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_rd2wr_in[$bits(reg_ddrc_rd2wr_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_rd2wr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_rd2wr_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2wr_int_fr2){1'b0}});
assign reg_ddrc_rd2wr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_rd2wr_in[$bits(reg_ddrc_rd2wr_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_rd2wr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_rd2wr_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2wr_int_fr4){1'b0}});
assign reg_ddrc_rd2wr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_rd2wr_int_fr4 : reg_ddrc_rd2wr_int_fr2;
assign reg_ddrc_rd2wr_out = (reg_ddrc_lpddr5) ? reg_ddrc_rd2wr_in : reg_ddrc_rd2wr_int;

// reg_ddrc_wr2rd
logic [$bits(reg_ddrc_wr2rd_in)-1:0] reg_ddrc_wr2rd_int;
logic [$bits(reg_ddrc_wr2rd_in)-1:0] reg_ddrc_wr2rd_int_fr2;
logic [$bits(reg_ddrc_wr2rd_in)-1:0] reg_ddrc_wr2rd_int_fr4;
assign reg_ddrc_wr2rd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_wr2rd_in[$bits(reg_ddrc_wr2rd_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_wr2rd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_wr2rd_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2rd_int_fr2){1'b0}});
assign reg_ddrc_wr2rd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_wr2rd_in[$bits(reg_ddrc_wr2rd_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_wr2rd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_wr2rd_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2rd_int_fr4){1'b0}});
assign reg_ddrc_wr2rd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_wr2rd_int_fr4 : reg_ddrc_wr2rd_int_fr2;
assign reg_ddrc_wr2rd_out = (reg_ddrc_lpddr5) ? reg_ddrc_wr2rd_in : reg_ddrc_wr2rd_int;

// reg_ddrc_wr2mr
logic[$bits(reg_ddrc_wr2mr_in)-1:0] reg_ddrc_wr2mr_int;
logic[$bits(reg_ddrc_wr2mr_in)-1:0] reg_ddrc_wr2mr_int_fr2;
logic[$bits(reg_ddrc_wr2mr_in)-1:0] reg_ddrc_wr2mr_int_fr4;
assign reg_ddrc_wr2mr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_wr2mr_in[$bits(reg_ddrc_wr2mr_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_wr2mr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_wr2mr_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2mr_out){1'b0}});
assign reg_ddrc_wr2mr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_wr2mr_in[$bits(reg_ddrc_wr2mr_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_wr2mr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_wr2mr_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2mr_out){1'b0}});
assign reg_ddrc_wr2mr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_wr2mr_int_fr4 : reg_ddrc_wr2mr_int_fr2;
assign reg_ddrc_wr2mr_out = (reg_ddrc_lpddr5) ? reg_ddrc_wr2mr_in : reg_ddrc_wr2mr_int;
 

// reg_ddrc_t_mr
logic [$bits(reg_ddrc_t_mr_in)-1:0] reg_ddrc_t_mr_int;
logic [$bits(reg_ddrc_t_mr_in)-1:0] reg_ddrc_t_mr_int_fr2;
logic [$bits(reg_ddrc_t_mr_in)-1:0] reg_ddrc_t_mr_int_fr4;
assign reg_ddrc_t_mr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_mr_in[$bits(reg_ddrc_t_mr_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_mr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_mr_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_mr_int_fr2){1'b0}});
assign reg_ddrc_t_mr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_mr_in[$bits(reg_ddrc_t_mr_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_mr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_mr_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_mr_int_fr4){1'b0}});
assign reg_ddrc_t_mr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_mr_int_fr4 : reg_ddrc_t_mr_int_fr2;
assign reg_ddrc_t_mr_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_mr_in : reg_ddrc_t_mr_int;

// reg_ddrc_rd2mr
logic [$bits(reg_ddrc_rd2mr_in)-1:0] reg_ddrc_rd2mr_int;
logic [$bits(reg_ddrc_rd2mr_in)-1:0] reg_ddrc_rd2mr_int_fr2;
logic [$bits(reg_ddrc_rd2mr_in)-1:0] reg_ddrc_rd2mr_int_fr4;
assign reg_ddrc_rd2mr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_rd2mr_in[$bits(reg_ddrc_rd2mr_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_rd2mr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_rd2mr_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2mr_int_fr2){1'b0}});
assign reg_ddrc_rd2mr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_rd2mr_in[$bits(reg_ddrc_rd2mr_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_rd2mr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_rd2mr_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_rd2mr_int_fr4){1'b0}});
assign reg_ddrc_rd2mr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_rd2mr_int_fr4 : reg_ddrc_rd2mr_int_fr2;
assign reg_ddrc_rd2mr_out = (reg_ddrc_lpddr5) ? reg_ddrc_rd2mr_in : reg_ddrc_rd2mr_int;


// reg_ddrc_t_rcd
logic [$bits(reg_ddrc_t_rcd_in)-1:0] reg_ddrc_t_rcd_int;
logic [$bits(reg_ddrc_t_rcd_in)-1:0] reg_ddrc_t_rcd_int_fr2;
logic [$bits(reg_ddrc_t_rcd_in)-1:0] reg_ddrc_t_rcd_int_fr4;
assign reg_ddrc_t_rcd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rcd_in[$bits(reg_ddrc_t_rcd_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rcd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rcd_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rcd_int_fr2){1'b0}});
assign reg_ddrc_t_rcd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rcd_in[$bits(reg_ddrc_t_rcd_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rcd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rcd_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rcd_int_fr4){1'b0}});
assign reg_ddrc_t_rcd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rcd_int_fr4 : reg_ddrc_t_rcd_int_fr2;
assign reg_ddrc_t_rcd_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_rcd_in : reg_ddrc_t_rcd_int;

// reg_ddrc_t_ccd
logic [$bits(reg_ddrc_t_ccd_in)-1:0] reg_ddrc_t_ccd_int;
logic [$bits(reg_ddrc_t_ccd_in)-1:0] reg_ddrc_t_ccd_int_fr2;
logic [$bits(reg_ddrc_t_ccd_in)-1:0] reg_ddrc_t_ccd_int_fr4;
assign reg_ddrc_t_ccd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ccd_in[$bits(reg_ddrc_t_ccd_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_ccd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ccd_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ccd_int_fr2){1'b0}});
assign reg_ddrc_t_ccd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ccd_in[$bits(reg_ddrc_t_ccd_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_ccd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_ccd_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ccd_int_fr4){1'b0}});
assign reg_ddrc_t_ccd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ccd_int_fr4 : reg_ddrc_t_ccd_int_fr2;
assign reg_ddrc_t_ccd_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_ccd_in : reg_ddrc_t_ccd_int;

// reg_ddrc_t_rrd
logic [$bits(reg_ddrc_t_rrd_in)-1:0] reg_ddrc_t_rrd_int;
logic [$bits(reg_ddrc_t_rrd_in)-1:0] reg_ddrc_t_rrd_int_fr2;
logic [$bits(reg_ddrc_t_rrd_in)-1:0] reg_ddrc_t_rrd_int_fr4;
assign reg_ddrc_t_rrd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rrd_in[$bits(reg_ddrc_t_rrd_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rrd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rrd_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rrd_int_fr2){1'b0}});
assign reg_ddrc_t_rrd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rrd_in[$bits(reg_ddrc_t_rrd_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rrd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rrd_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rrd_int_fr4){1'b0}});
assign reg_ddrc_t_rrd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rrd_int_fr4 : reg_ddrc_t_rrd_int_fr2;
assign reg_ddrc_t_rrd_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_rrd_in : reg_ddrc_t_rrd_int;

// reg_ddrc_t_rp
logic [$bits(reg_ddrc_t_rp_in)-1:0] reg_ddrc_t_rp_int;
logic [$bits(reg_ddrc_t_rp_in)-1:0] reg_ddrc_t_rp_int_fr2;
logic [$bits(reg_ddrc_t_rp_in)-1:0] reg_ddrc_t_rp_int_fr4;
logic [$bits(reg_ddrc_t_rp_out):0] reg_ddrc_t_rp_out_wider;
assign reg_ddrc_t_rp_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rp_in[$bits(reg_ddrc_t_rp_in) - 1: ROUNDING_BITS_FR2]};
assign reg_ddrc_t_rp_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rp_in[$bits(reg_ddrc_t_rp_in) - 1: ROUNDING_BITS_FR4]};
assign reg_ddrc_t_rp_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rp_int_fr4 : reg_ddrc_t_rp_int_fr2;
logic [$bits(reg_ddrc_t_rp_out)-1:0] reg_ddrc_t_rp_round_int;
logic [$bits(reg_ddrc_t_rp_out)-1:0] reg_ddrc_t_rp_round_fr2;
logic [$bits(reg_ddrc_t_rp_out)-1:0] reg_ddrc_t_rp_round_fr4;
logic [$bits(reg_ddrc_t_rp_out)-1:0] reg_ddrc_t_rp_round;
assign reg_ddrc_t_rp_round_fr2 = ((|reg_ddrc_t_rp_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rp_round_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rp_round_fr2){1'b0}});
assign reg_ddrc_t_rp_round_fr4 = ((reg_ddrc_t_rp_in[ROUNDING_BITS_FR4-1:0] == 2'b11) ? {{($bits(reg_ddrc_t_rp_round_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rp_round_fr4){1'b0}});
assign reg_ddrc_t_rp_round = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rp_round_fr4 : reg_ddrc_t_rp_round_fr2;
assign reg_ddrc_t_rp_out_wider = reg_ddrc_t_rp_int + reg_ddrc_t_rp_round;
assign reg_ddrc_t_rp_round_int = reg_ddrc_t_rp_out_wider[$bits(reg_ddrc_t_rp_out)-1:0];
assign reg_ddrc_t_rp_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_rp_in : reg_ddrc_t_rp_round_int;


// reg_ddrc_t_cksrx
logic [$bits(reg_ddrc_t_cksrx_in)-1:0] reg_ddrc_t_cksrx_int;
logic [$bits(reg_ddrc_t_cksrx_in)-1:0] reg_ddrc_t_cksrx_int_fr2;
logic [$bits(reg_ddrc_t_cksrx_in)-1:0] reg_ddrc_t_cksrx_int_fr4;
assign reg_ddrc_t_cksrx_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_cksrx_in[$bits(reg_ddrc_t_cksrx_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_cksrx_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_cksrx_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cksrx_int_fr2){1'b0}});
assign reg_ddrc_t_cksrx_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_cksrx_in[$bits(reg_ddrc_t_cksrx_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_cksrx_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_cksrx_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cksrx_int_fr4){1'b0}});
assign reg_ddrc_t_cksrx_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_cksrx_int_fr4 : reg_ddrc_t_cksrx_int_fr2;
assign reg_ddrc_t_cksrx_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_cksrx_in : reg_ddrc_t_cksrx_int;

// reg_ddrc_t_cksre
logic [$bits(reg_ddrc_t_cksre_in)-1:0] reg_ddrc_t_cksre_int;
logic [$bits(reg_ddrc_t_cksre_in)-1:0] reg_ddrc_t_cksre_int_fr2;
logic [$bits(reg_ddrc_t_cksre_in)-1:0] reg_ddrc_t_cksre_int_fr4;
assign reg_ddrc_t_cksre_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_cksre_in[$bits(reg_ddrc_t_cksre_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_cksre_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_cksre_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cksre_int_fr2){1'b0}});
assign reg_ddrc_t_cksre_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_cksre_in[$bits(reg_ddrc_t_cksre_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_cksre_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_cksre_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cksre_int_fr4){1'b0}});
assign reg_ddrc_t_cksre_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_cksre_int_fr4 : reg_ddrc_t_cksre_int_fr2;
assign reg_ddrc_t_cksre_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_cksre_in : reg_ddrc_t_cksre_int;

// reg_ddrc_t_ckesr
logic [$bits(reg_ddrc_t_ckesr_in)-1:0] reg_ddrc_t_ckesr_int;
logic [$bits(reg_ddrc_t_ckesr_in)-1:0] reg_ddrc_t_ckesr_int_fr2;
logic [$bits(reg_ddrc_t_ckesr_in)-1:0] reg_ddrc_t_ckesr_int_fr4;
assign reg_ddrc_t_ckesr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ckesr_in[$bits(reg_ddrc_t_ckesr_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_ckesr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ckesr_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ckesr_int_fr2){1'b0}});
assign reg_ddrc_t_ckesr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ckesr_in[$bits(reg_ddrc_t_ckesr_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_ckesr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_ckesr_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ckesr_int_fr4){1'b0}});
assign reg_ddrc_t_ckesr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ckesr_int_fr4 : reg_ddrc_t_ckesr_int_fr2;
assign reg_ddrc_t_ckesr_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_ckesr_in : reg_ddrc_t_ckesr_int;

// reg_ddrc_t_cke
logic [$bits(reg_ddrc_t_cke_in)-1:0] reg_ddrc_t_cke_int;
logic [$bits(reg_ddrc_t_cke_in)-1:0] reg_ddrc_t_cke_int_fr2;
logic [$bits(reg_ddrc_t_cke_in)-1:0] reg_ddrc_t_cke_int_fr4;
assign reg_ddrc_t_cke_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_cke_in[$bits(reg_ddrc_t_cke_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_cke_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_cke_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cke_int_fr2){1'b0}});
assign reg_ddrc_t_cke_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_cke_in[$bits(reg_ddrc_t_cke_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_cke_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_cke_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cke_int_fr4){1'b0}});
assign reg_ddrc_t_cke_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_cke_int_fr4 : reg_ddrc_t_cke_int_fr2;
assign reg_ddrc_t_cke_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_cke_in : reg_ddrc_t_cke_int;

logic[$bits(reg_ddrc_t_ckcsx_in)-1:0] reg_ddrc_t_ckcsx_int;
logic[$bits(reg_ddrc_t_ckcsx_in)-1:0] reg_ddrc_t_ckcsx_int_fr2;
logic[$bits(reg_ddrc_t_ckcsx_in)-1:0] reg_ddrc_t_ckcsx_int_fr4;
assign reg_ddrc_t_ckcsx_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ckcsx_in[$bits(reg_ddrc_t_ckcsx_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_ckcsx_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ckcsx_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ckcsx_out){1'b0}});
assign reg_ddrc_t_ckcsx_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ckcsx_in[$bits(reg_ddrc_t_ckcsx_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_ckcsx_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_ckcsx_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ckcsx_out){1'b0}});
assign reg_ddrc_t_ckcsx_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ckcsx_int_fr4 : reg_ddrc_t_ckcsx_int_fr2;
assign reg_ddrc_t_ckcsx_out = (reg_ddrc_lpddr5) ? reg_ddrc_t_ckcsx_in : reg_ddrc_t_ckcsx_int;
 




// reg_ddrc_t_ccd_s
logic [$bits(reg_ddrc_t_ccd_s_in)-1:0] reg_ddrc_t_ccd_s_int;
logic [$bits(reg_ddrc_t_ccd_s_in)-1:0] reg_ddrc_t_ccd_s_int_fr2;
logic [$bits(reg_ddrc_t_ccd_s_in)-1:0] reg_ddrc_t_ccd_s_int_fr4;
assign reg_ddrc_t_ccd_s_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ccd_s_in[$bits(reg_ddrc_t_ccd_s_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_ccd_s_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ccd_s_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ccd_s_int_fr2){1'b0}});
assign reg_ddrc_t_ccd_s_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ccd_s_in[$bits(reg_ddrc_t_ccd_s_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_ccd_s_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_ccd_s_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ccd_s_int_fr4){1'b0}});
assign reg_ddrc_t_ccd_s_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ccd_s_int_fr4 : reg_ddrc_t_ccd_s_int_fr2;
assign reg_ddrc_t_ccd_s_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_ccd_s_in : reg_ddrc_t_ccd_s_int;

// reg_ddrc_t_rrd_s
logic [$bits(reg_ddrc_t_rrd_s_in)-1:0] reg_ddrc_t_rrd_s_int;
logic [$bits(reg_ddrc_t_rrd_s_in)-1:0] reg_ddrc_t_rrd_s_int_fr2;
logic [$bits(reg_ddrc_t_rrd_s_in)-1:0] reg_ddrc_t_rrd_s_int_fr4;
assign reg_ddrc_t_rrd_s_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_rrd_s_in[$bits(reg_ddrc_t_rrd_s_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_rrd_s_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_rrd_s_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rrd_s_int_fr2){1'b0}});
assign reg_ddrc_t_rrd_s_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_rrd_s_in[$bits(reg_ddrc_t_rrd_s_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_rrd_s_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_rrd_s_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_rrd_s_int_fr4){1'b0}});
assign reg_ddrc_t_rrd_s_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_rrd_s_int_fr4 : reg_ddrc_t_rrd_s_int_fr2;
assign reg_ddrc_t_rrd_s_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_rrd_s_in : reg_ddrc_t_rrd_s_int;

// reg_ddrc_wr2rd_s
logic [$bits(reg_ddrc_wr2rd_s_in)-1:0] reg_ddrc_wr2rd_s_int;
logic [$bits(reg_ddrc_wr2rd_s_in)-1:0] reg_ddrc_wr2rd_s_int_fr2;
logic [$bits(reg_ddrc_wr2rd_s_in)-1:0] reg_ddrc_wr2rd_s_int_fr4;
assign reg_ddrc_wr2rd_s_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_wr2rd_s_in[$bits(reg_ddrc_wr2rd_s_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_wr2rd_s_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_wr2rd_s_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2rd_s_int_fr2){1'b0}});
assign reg_ddrc_wr2rd_s_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_wr2rd_s_in[$bits(reg_ddrc_wr2rd_s_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_wr2rd_s_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_wr2rd_s_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_wr2rd_s_int_fr4){1'b0}});
assign reg_ddrc_wr2rd_s_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_wr2rd_s_int_fr4 : reg_ddrc_wr2rd_s_int_fr2;
assign reg_ddrc_wr2rd_s_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_wr2rd_s_in : reg_ddrc_wr2rd_s_int;


logic[$bits(reg_ddrc_t_cmdcke_in)-1:0] reg_ddrc_t_cmdcke_int;
logic[$bits(reg_ddrc_t_cmdcke_in)-1:0] reg_ddrc_t_cmdcke_int_fr2;
logic[$bits(reg_ddrc_t_cmdcke_in)-1:0] reg_ddrc_t_cmdcke_int_fr4;
assign reg_ddrc_t_cmdcke_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_cmdcke_in[$bits(reg_ddrc_t_cmdcke_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_cmdcke_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_cmdcke_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cmdcke_out){1'b0}});
assign reg_ddrc_t_cmdcke_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_cmdcke_in[$bits(reg_ddrc_t_cmdcke_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_cmdcke_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_cmdcke_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_cmdcke_out){1'b0}});
assign reg_ddrc_t_cmdcke_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_cmdcke_int_fr4 : reg_ddrc_t_cmdcke_int_fr2;
assign reg_ddrc_t_cmdcke_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_cmdcke_in : reg_ddrc_t_cmdcke_int;

 

logic[$bits(reg_ddrc_odtloff_in)-1:0] reg_ddrc_odtloff_int;
logic[$bits(reg_ddrc_odtloff_in)-1:0] reg_ddrc_odtloff_int_fr2;
logic[$bits(reg_ddrc_odtloff_in)-1:0] reg_ddrc_odtloff_int_fr4;
assign reg_ddrc_odtloff_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_odtloff_in[$bits(reg_ddrc_odtloff_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_odtloff_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_odtloff_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_odtloff_out){1'b0}});
assign reg_ddrc_odtloff_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_odtloff_in[$bits(reg_ddrc_odtloff_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_odtloff_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_odtloff_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_odtloff_out){1'b0}});
assign reg_ddrc_odtloff_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_odtloff_int_fr4 : reg_ddrc_odtloff_int_fr2;
assign reg_ddrc_odtloff_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_odtloff_in : reg_ddrc_odtloff_int;
 
logic[$bits(reg_ddrc_t_ccd_mw_in)-1:0] reg_ddrc_t_ccd_mw_int;
logic[$bits(reg_ddrc_t_ccd_mw_in)-1:0] reg_ddrc_t_ccd_mw_int_fr2;
logic[$bits(reg_ddrc_t_ccd_mw_in)-1:0] reg_ddrc_t_ccd_mw_int_fr4;
assign reg_ddrc_t_ccd_mw_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ccd_mw_in[$bits(reg_ddrc_t_ccd_mw_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_ccd_mw_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ccd_mw_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ccd_mw_out){1'b0}});
assign reg_ddrc_t_ccd_mw_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ccd_mw_in[$bits(reg_ddrc_t_ccd_mw_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_ccd_mw_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_ccd_mw_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ccd_mw_out){1'b0}});
assign reg_ddrc_t_ccd_mw_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ccd_mw_int_fr4 : reg_ddrc_t_ccd_mw_int_fr2;
assign reg_ddrc_t_ccd_mw_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_ccd_mw_in : reg_ddrc_t_ccd_mw_int;
 
logic[$bits(reg_ddrc_t_ppd_in)-1:0] reg_ddrc_t_ppd_int;
logic[$bits(reg_ddrc_t_ppd_in)-1:0] reg_ddrc_t_ppd_int_fr2;
logic[$bits(reg_ddrc_t_ppd_in)-1:0] reg_ddrc_t_ppd_int_fr4;
assign reg_ddrc_t_ppd_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_ppd_in[$bits(reg_ddrc_t_ppd_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_ppd_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_ppd_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ppd_out){1'b0}});
assign reg_ddrc_t_ppd_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_ppd_in[$bits(reg_ddrc_t_ppd_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_ppd_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_ppd_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_ppd_out){1'b0}});
assign reg_ddrc_t_ppd_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_ppd_int_fr4 : reg_ddrc_t_ppd_int_fr2;
assign reg_ddrc_t_ppd_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_ppd_in : reg_ddrc_t_ppd_int;

logic[$bits(reg_ddrc_t_xsr_in)-1:0] reg_ddrc_t_xsr_int;
logic[$bits(reg_ddrc_t_xsr_in)-1:0] reg_ddrc_t_xsr_int_fr2;
logic[$bits(reg_ddrc_t_xsr_in)-1:0] reg_ddrc_t_xsr_int_fr4;
assign reg_ddrc_t_xsr_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_xsr_in[$bits(reg_ddrc_t_xsr_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_xsr_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_xsr_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_xsr_out){1'b0}});
assign reg_ddrc_t_xsr_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_xsr_in[$bits(reg_ddrc_t_xsr_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_xsr_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_xsr_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_xsr_out){1'b0}});
assign reg_ddrc_t_xsr_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_xsr_int_fr4 : reg_ddrc_t_xsr_int_fr2;
assign reg_ddrc_t_xsr_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_xsr_in : reg_ddrc_t_xsr_int;

logic[$bits(reg_ddrc_t_osco_in)-1:0] reg_ddrc_t_osco_int;
logic[$bits(reg_ddrc_t_osco_in)-1:0] reg_ddrc_t_osco_int_fr2;
logic[$bits(reg_ddrc_t_osco_in)-1:0] reg_ddrc_t_osco_int_fr4;
assign reg_ddrc_t_osco_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_osco_in[$bits(reg_ddrc_t_osco_in) - 1: ROUNDING_BITS_FR2]} +
        ((|reg_ddrc_t_osco_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_osco_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_osco_out){1'b0}});
assign reg_ddrc_t_osco_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_osco_in[$bits(reg_ddrc_t_osco_in) - 1: ROUNDING_BITS_FR4]} +
        ((|reg_ddrc_t_osco_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_osco_out)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_osco_out){1'b0}});
assign reg_ddrc_t_osco_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_osco_int_fr4 : reg_ddrc_t_osco_int_fr2;
assign reg_ddrc_t_osco_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_osco_in : reg_ddrc_t_osco_int;
 





// reg_ddrc_t_vrcg_enable
logic [$bits(reg_ddrc_t_vrcg_enable_in)-1:0] reg_ddrc_t_vrcg_enable_int;
logic [$bits(reg_ddrc_t_vrcg_enable_in)-1:0] reg_ddrc_t_vrcg_enable_int_fr2;
logic [$bits(reg_ddrc_t_vrcg_enable_in)-1:0] reg_ddrc_t_vrcg_enable_int_fr4;
assign reg_ddrc_t_vrcg_enable_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_vrcg_enable_in[$bits(reg_ddrc_t_vrcg_enable_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_vrcg_enable_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_vrcg_enable_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_vrcg_enable_int_fr2){1'b0}});
assign reg_ddrc_t_vrcg_enable_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_vrcg_enable_in[$bits(reg_ddrc_t_vrcg_enable_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_vrcg_enable_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_vrcg_enable_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_vrcg_enable_int_fr4){1'b0}});
assign reg_ddrc_t_vrcg_enable_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_vrcg_enable_int_fr4 : reg_ddrc_t_vrcg_enable_int_fr2;
assign reg_ddrc_t_vrcg_enable_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_vrcg_enable_in : reg_ddrc_t_vrcg_enable_int;

// reg_ddrc_t_vrcg_disable
logic [$bits(reg_ddrc_t_vrcg_disable_in)-1:0] reg_ddrc_t_vrcg_disable_int;
logic [$bits(reg_ddrc_t_vrcg_disable_in)-1:0] reg_ddrc_t_vrcg_disable_int_fr2;
logic [$bits(reg_ddrc_t_vrcg_disable_in)-1:0] reg_ddrc_t_vrcg_disable_int_fr4;
assign reg_ddrc_t_vrcg_disable_int_fr2 = {{ROUNDING_BITS_FR2{1'b0}},reg_ddrc_t_vrcg_disable_in[$bits(reg_ddrc_t_vrcg_disable_in) - 1: ROUNDING_BITS_FR2]} +
                                   ((|reg_ddrc_t_vrcg_disable_in[ROUNDING_BITS_FR2-1:0]) ? {{($bits(reg_ddrc_t_vrcg_disable_int_fr2)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_vrcg_disable_int_fr2){1'b0}});
assign reg_ddrc_t_vrcg_disable_int_fr4 = {{ROUNDING_BITS_FR4{1'b0}},reg_ddrc_t_vrcg_disable_in[$bits(reg_ddrc_t_vrcg_disable_in) - 1: ROUNDING_BITS_FR4]} +
                                   ((|reg_ddrc_t_vrcg_disable_in[ROUNDING_BITS_FR4-1:0]) ? {{($bits(reg_ddrc_t_vrcg_disable_int_fr4)-1){1'b0}},1'b1} : {$bits(reg_ddrc_t_vrcg_disable_int_fr4){1'b0}});
assign reg_ddrc_t_vrcg_disable_int = (reg_ddrc_frequency_ratio) ? reg_ddrc_t_vrcg_disable_int_fr4 : reg_ddrc_t_vrcg_disable_int_fr2;
assign reg_ddrc_t_vrcg_disable_out = ( reg_ddrc_lpddr5 ) ? reg_ddrc_t_vrcg_disable_in : reg_ddrc_t_vrcg_disable_int;

endmodule
