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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cpfdp_if.svh#3 $
// -------------------------------------------------------------------------
// Description:
//     SV interface between CPF and DP

`ifndef __GUARD__DWC_DDRCTL_DDRC_CPFDP_IF__SVH__
`define __GUARD__DWC_DDRCTL_DDRC_CPFDP_IF__SVH__

`include "DWC_ddrctl_all_defs.svh"

interface dwc_ddrctl_ddrc_cpfdp_if #(
   parameter      NO_OF_BT                     = `MEMC_NO_OF_BLK_TOKEN,   
   parameter      BT_BITS                      = $clog2(NO_OF_BT),

   parameter      NO_OF_BRT                    = `MEMC_NO_OF_BRT,   
   parameter      BRT_BITS                     = $clog2(NO_OF_BRT),
   parameter      ECC_INFO_WIDTH               = 35,

   parameter      MWR_BITS                     = `DDRCTL_MWR_BITS,

   parameter      PARTIAL_WR_BITS              = `UMCTL2_PARTIAL_WR_BITS,
   parameter      PARTIAL_WR_BITS_LOG2         = $clog2(PARTIAL_WR_BITS),

   parameter      PW_NUM_DB                    = PARTIAL_WR_BITS,
   parameter      PW_FACTOR_HBW                = 2*`MEMC_FREQ_RATIO,

   parameter      PW_WORD_VALID_WD_HBW         = PW_NUM_DB*PW_FACTOR_HBW,

   parameter      PW_WORD_VALID_WD_MAX         = PW_WORD_VALID_WD_HBW,
   parameter      PW_WORD_CNT_WD_MAX           = $clog2(PW_WORD_VALID_WD_MAX),

   parameter      NO_OF_BWT                    = `MEMC_NO_OF_BWT,   
   parameter      BWT_BITS                     = $clog2(NO_OF_BWT),
   parameter      IE_WR_TYPE_BITS              = `IE_WR_TYPE_BITS,
   parameter      IE_BURST_NUM_BITS            = `MEMC_BURST_LENGTH==16 ? 5 : 3,

   parameter      RMW_TYPE_BITS                = 2,                            // 2-bit RMW type
   parameter      WORD_BITS                    = `MEMC_WORD_BITS,              // address a word within a burst
   parameter      WR_CAM_ADDR_WIDTH            = `MEMC_WRCMD_ENTRY_BITS,       // bits to address into write CAM
   parameter      WR_CAM_ADDR_WIDTH_IE         = WR_CAM_ADDR_WIDTH + `MEMC_INLINE_ECC_EN 
   );
   logic                                                      rd_ih_free_brt_vld;
   logic  [BRT_BITS-1:0]                                      rd_ih_free_brt;
   logic  [BT_BITS-1:0]                                       rd_ih_lkp_brt_by_bt;
   logic  [BT_BITS-1:0]                                       rd_ih_lkp_bwt_by_bt;

   logic                                                      wu_ih_flow_cntrl_req;

   logic [1:0]                                                wu_te_enable_wr;
   logic [WR_CAM_ADDR_WIDTH-1:0]                              wu_te_entry_num;
   logic [MWR_BITS-1:0]                                       wu_te_mwr;
   logic [PARTIAL_WR_BITS-1:0]                                wu_te_wr_word_valid;
   logic [PARTIAL_WR_BITS_LOG2-1:0]                           wu_te_ram_raddr_lsb_first;
   logic [PW_WORD_CNT_WD_MAX-1:0]                             wu_te_pw_num_beats_m1;
   logic [PW_WORD_CNT_WD_MAX-1:0]                             wu_te_pw_num_cols_m1;

   logic                                                      mr_ih_free_bwt_vld;
   logic  [BWT_BITS-1:0]                                      mr_ih_free_bwt;
   logic  [BT_BITS-1:0]                                       mr_ih_lkp_bwt_by_bt;
   logic  [BT_BITS-1:0]                                       mr_ih_lkp_brt_by_bt;

   logic [BRT_BITS-1:0]                                       ih_rd_ie_brt;
   logic                                                      ih_rd_ie_rd_cnt_inc;
   logic                                                      ih_rd_ie_blk_rd_end;
   logic [BRT_BITS-1:0]                                       ih_rd_lkp_brt;
   logic [BWT_BITS-1:0]                                       ih_rd_lkp_bwt;
   logic                                                      ih_rd_lkp_bwt_vld;

   logic                                                      ih_wu_wr_valid;
   logic                                                      ih_wu_wr_valid_addr_err;
   logic  [RMW_TYPE_BITS-1:0]                                 ih_wu_rmw_type;
   logic  [WR_CAM_ADDR_WIDTH-1:0]                             ih_wu_wr_entry;
   logic  [WORD_BITS-1:0]                                     ih_wu_critical_word;

   logic                                                      te_wu_wr_retry;
   logic  [WR_CAM_ADDR_WIDTH-1:0]                             te_wu_entry_num;
   logic                                                      te_wu_ie_flowctrl_req;

   logic  [BRT_BITS-1:0]                                      ih_mr_ie_brt;
   logic                                                      ih_mr_ie_brt_vld;
   logic  [BWT_BITS-1:0]                                      ih_mr_ie_bwt;
   logic  [NO_OF_BWT-1:0]                                     ih_mr_ie_wr_cnt_dec_vct;
   logic                                                      ih_mr_ie_wr_cnt_inc;
   logic                                                      ih_mr_ie_blk_wr_end;
   logic  [BWT_BITS-1:0]                                      ih_mr_lkp_bwt;
   logic                                                      ih_mr_lkp_bwt_vld;
   logic  [BRT_BITS-1:0]                                      ih_mr_lkp_brt;
   logic                                                      ih_mr_lkp_brt_vld;

   logic  [WR_CAM_ADDR_WIDTH_IE-1:0]                          te_mr_wr_ram_addr;

   logic  [BT_BITS-1:0]                                       te_mr_ie_bt;
   logic  [IE_WR_TYPE_BITS-1:0]                               te_mr_ie_wr_type;
   logic  [IE_BURST_NUM_BITS-1:0]                             te_mr_ie_blk_burst_num;
   logic                                                      te_mr_eccap;

   logic                                                      mr_yy_free_wr_entry_valid;    //from mr to ih
   logic  [WR_CAM_ADDR_WIDTH_IE-1:0]                          mr_yy_free_wr_entry;
   logic                                                      te_yy_wr_combine;             //from te to wu, also goes to IH/WU

   logic [PARTIAL_WR_BITS-1:0]                                te_pi_wr_word_valid;          //from te to mr


//interface on dp side
modport o_rd_mp (
    output rd_ih_lkp_brt_by_bt
   ,output rd_ih_lkp_bwt_by_bt
   ,output rd_ih_free_brt_vld
   ,output rd_ih_free_brt
   );

modport i_ih_rd_mp ( 
    input  ih_rd_ie_brt
   ,input  ih_rd_ie_rd_cnt_inc
   ,input  ih_rd_ie_blk_rd_end
   ,input  ih_rd_lkp_brt
   ,input  ih_rd_lkp_bwt
   ,input  ih_rd_lkp_bwt_vld
   );

modport i_ih_wu_mp (
    input  ih_wu_rmw_type
   ,input  ih_wu_wr_entry
   ,input  ih_wu_critical_word
   ,input  ih_wu_wr_valid
   ,input  ih_wu_wr_valid_addr_err
   );

modport i_te_wu_mp (
    input  te_wu_wr_retry
   ,input  te_wu_entry_num
   ,input  te_wu_ie_flowctrl_req
   ,input  te_yy_wr_combine
   );

modport i_ih_mr_mp (
    input  ih_mr_ie_brt
   ,input  ih_mr_ie_brt_vld
   ,input  ih_mr_ie_bwt
   ,input  ih_mr_ie_wr_cnt_dec_vct
   ,input  ih_mr_ie_wr_cnt_inc
   ,input  ih_mr_ie_blk_wr_end
   ,input  ih_mr_lkp_bwt
   ,input  ih_mr_lkp_bwt_vld
   ,input  ih_mr_lkp_brt
   ,input  ih_mr_lkp_brt_vld
   );

modport i_te_mr_mp (
    input  te_mr_wr_ram_addr
   ,input  te_mr_ie_bt
   ,input  te_mr_ie_wr_type
   ,input  te_mr_ie_blk_burst_num
   ,input  te_mr_eccap
   ,input  te_pi_wr_word_valid
   );

modport o_mr_mp (
    output mr_yy_free_wr_entry_valid
   ,output mr_yy_free_wr_entry
   ,output mr_ih_free_bwt_vld
   ,output mr_ih_free_bwt
   ,output mr_ih_lkp_bwt_by_bt
   ,output mr_ih_lkp_brt_by_bt
   );

modport o_wu_mp (
    output wu_ih_flow_cntrl_req

   ,output wu_te_enable_wr
   ,output wu_te_entry_num
   ,output wu_te_mwr
   ,output wu_te_wr_word_valid
   ,output wu_te_ram_raddr_lsb_first
   ,output wu_te_pw_num_beats_m1
   ,output wu_te_pw_num_cols_m1
   );

//interface on cpf side
modport i_rd_ih_mp (
    input  rd_ih_lkp_brt_by_bt
   ,input  rd_ih_lkp_bwt_by_bt
   ,input  rd_ih_free_brt_vld
   ,input  rd_ih_free_brt
   );

modport i_wu_ih_mp (
    input  wu_ih_flow_cntrl_req
   );

modport i_wu_te_mp (
    input  wu_te_enable_wr
   ,input  wu_te_entry_num
   ,input  wu_te_mwr
   ,input  wu_te_wr_word_valid
   ,input  wu_te_ram_raddr_lsb_first
   ,input  wu_te_pw_num_beats_m1
   ,input  wu_te_pw_num_cols_m1
   );

modport i_mr_ih_mp (
    input  mr_yy_free_wr_entry_valid
   ,input  mr_yy_free_wr_entry
   ,input  mr_ih_free_bwt_vld
   ,input  mr_ih_free_bwt
   ,input  mr_ih_lkp_bwt_by_bt
   ,input  mr_ih_lkp_brt_by_bt
   );

//modport i_mr_te_mp ();

modport o_ih_mp (
    output ih_wu_rmw_type
   ,output ih_wu_wr_entry
   ,output ih_wu_critical_word
   ,output ih_rd_ie_brt
   ,output ih_rd_ie_rd_cnt_inc
   ,output ih_rd_ie_blk_rd_end
   ,output ih_rd_lkp_brt
   ,output ih_rd_lkp_bwt
   ,output ih_rd_lkp_bwt_vld

   ,output ih_wu_wr_valid
   ,output ih_wu_wr_valid_addr_err

   ,output ih_mr_ie_brt
   ,output ih_mr_ie_brt_vld
   ,output ih_mr_ie_bwt
   ,output ih_mr_ie_wr_cnt_dec_vct
   ,output ih_mr_ie_wr_cnt_inc
   ,output ih_mr_ie_blk_wr_end
   ,output ih_mr_lkp_bwt
   ,output ih_mr_lkp_bwt_vld
   ,output ih_mr_lkp_brt
   ,output ih_mr_lkp_brt_vld
   );
 
modport o_te_mp (
    output te_wu_wr_retry
   ,output te_wu_entry_num
   ,output te_wu_ie_flowctrl_req
   ,output te_mr_wr_ram_addr
   ,output te_mr_ie_bt
   ,output te_mr_ie_wr_type
   ,output te_mr_ie_blk_burst_num
   ,output te_mr_eccap
   ,output te_yy_wr_combine
   ,output te_pi_wr_word_valid
   );

endinterface : dwc_ddrctl_ddrc_cpfdp_if

`endif // __GUARD__DWC_DDRCTL_DDRC_CPFDP_IF__SVH__
