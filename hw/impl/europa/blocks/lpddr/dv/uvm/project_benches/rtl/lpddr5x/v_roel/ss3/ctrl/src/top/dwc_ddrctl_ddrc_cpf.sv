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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cpf.sv#7 $
// -------------------------------------------------------------------------
// Description:
//    DDRC CPF wrapper module
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module dwc_ddrctl_ddrc_cpf
import DWC_ddrctl_reg_pkg::*;
 #(
    parameter       RANK_BITS                   = `MEMC_RANK_BITS,
    parameter       CMD_TYPE_BITS               = 2,
    parameter       NUM_TOTAL_BANKS             =`MEMC_NUM_TOTAL_BANKS,
    parameter       PARTIAL_WR_BITS             = `UMCTL2_PARTIAL_WR_BITS,
    parameter       PARTIAL_WR_BITS_LOG2        = `log2(PARTIAL_WR_BITS),
    parameter       PW_NUM_DB                   = PARTIAL_WR_BITS,
    parameter       PW_FACTOR_HBW               = 2*`MEMC_FREQ_RATIO,
    parameter       PW_WORD_VALID_WD_HBW        = PW_NUM_DB*PW_FACTOR_HBW,
    parameter       PW_WORD_VALID_WD_MAX        = PW_WORD_VALID_WD_HBW,
    parameter       PW_WORD_CNT_WD_MAX          = `log2(PW_WORD_VALID_WD_MAX),
    parameter       PW_BC_SEL_BITS              = 3,
    parameter       NUM_TOTAL_BSMS              = `UMCTL2_NUM_BSM,
    parameter       BSM_BITS                    = `UMCTL2_BSM_BITS,
    parameter       NUM_LRANKS                  = `UMCTL2_NUM_LRANKS_TOTAL,         // max supported logical ranks (chip selects * chip ID(for DDR4 3DS))

    parameter       CORE_ADDR_INT_WIDTH         = (`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS),
    parameter       CORE_TAG_WIDTH              = `MEMC_TAGBITS,                    // width of tag
    parameter       CMD_LEN_BITS                = 1,                                // command length bit width
    parameter       WR_CAM_ADDR_WIDTH           = `MEMC_WRCMD_ENTRY_BITS,           // bits to address into write CAM
    parameter       WR_ECC_CAM_ADDR_WIDTH       = 0,
    parameter       WR_CAM_ADDR_WIDTH_IE        = 0,
    parameter       RD_CAM_ADDR_WIDTH           = `MEMC_RDCMD_ENTRY_BITS,           // bits to address into read CAM
    parameter       RMW_TYPE_BITS               = 2,                                // 2-bit RMW type
    parameter       WRDATA_CYCLES               = 2,
    parameter       RD_LATENCY_BITS             = `UMCTL2_XPI_RQOS_TW,
    parameter       WR_LATENCY_BITS             = `UMCTL2_XPI_WQOS_TW,
    parameter       NO_OF_BT                    = `MEMC_NO_OF_BLK_TOKEN,
    parameter       NO_OF_BWT                   = `MEMC_NO_OF_BWT,
    parameter       NO_OF_BRT                   = `MEMC_NO_OF_BRT,
    parameter       BWT_BITS                    = `log2(NO_OF_BWT),
    parameter       BRT_BITS                    = `log2(NO_OF_BRT),
    parameter       NO_OF_BLK_CHN               = `MEMC_NO_OF_BLK_CHANNEL,
    parameter       BLK_CHN_BITS                = `log2(NO_OF_BLK_CHN),
    parameter       IE_WR_TYPE_BITS             = `IE_WR_TYPE_BITS,
    parameter       BT_BITS                     = `log2(NO_OF_BT),
    parameter       IE_BURST_NUM_BITS           = `MEMC_BURST_LENGTH==16 ? 4 : 3,
    parameter       IE_RD_TYPE_BITS             = `IE_RD_TYPE_BITS,
    parameter       WDATA_PTR_BITS              = `MEMC_WDATA_PTR_BITS,
    parameter       MWR_BITS                    = `DDRCTL_MWR_BITS,
    parameter       CHANNEL_NUM                 = 0,
    parameter       LRANK_BITS                  = `UMCTL2_LRANK_BITS,
    parameter       BANK_BITS                   = `MEMC_BANK_BITS,
    parameter       PAGE_BITS                   = `MEMC_PAGE_BITS,
    parameter       BLK_BITS                    = `MEMC_BLK_BITS,                   // 2 column bits are critical word
    parameter       OTHER_WR_ENTRY_BITS         = RMW_TYPE_BITS ,
    parameter       WORD_BITS                   = `MEMC_WORD_BITS,                  // address a word within a burst
    parameter       ECCAP_BITS                  = `MEMC_ECCAP_EN,
    parameter       IE_TAG_BITS                 = (`MEMC_INLINE_ECC_EN==1) ? IE_RD_TYPE_BITS + IE_BURST_NUM_BITS + BT_BITS + ECCAP_BITS : 0,
    parameter       AUTOPRE_BITS                =(`MEMC_INLINE_ECC_EN==1)? 2 : 1,
    parameter       OTHER_RD_ENTRY_BITS         = (CORE_TAG_WIDTH+((`MEMC_ADDR_ERR==1) ? 1: 0) + ((`MEMC_USE_RMW_EN==1) ? (WR_CAM_ADDR_WIDTH + RMW_TYPE_BITS) : 0)), 
    parameter       MAX_CAM_ADDR_WIDTH          = 0,
    parameter       RD_CAM_ENTRIES              = 0,
    parameter       WR_CAM_ENTRIES              = 0,
    parameter       WR_CAM_ENTRIES_IE           = 0,
    parameter       WR_ECC_CAM_ENTRIES          = 0,
    parameter       BG_BANK_BITS                = `MEMC_BG_BANK_BITS,
    parameter       BG_BITS                     = `MEMC_BG_BITS,
    parameter       NUM_OF_BG                   = (1 << `MEMC_BG_BITS),
    parameter       RANKBANK_BITS               = LRANK_BITS + BG_BANK_BITS,
    parameter       RETRY_FIFO_DEPTH            = `DDRCTL_RETRY_FIFO_DEPTH,
    parameter       RETRY_RD_BITS               = 1,
    parameter       RETRY_WR_BITS               = 1,
    parameter       RETRY_TIMES_WIDTH           = 3,
    parameter       ENTRY_RETRY_TIMES_WIDTH     = 4,
    parameter       ECC_INFO_WIDTH   = 35,
    parameter       DDR4_COL3_BITS   = 1,
    parameter       LP_COL4_BITS     = 1,
    parameter       AM_DCH_WIDTH     = 6,
    parameter       AM_CS_WIDTH      = 6,
    parameter       AM_CID_WIDTH     = 6,
    parameter       AM_BANK_WIDTH    = 6,
    parameter       AM_BG_WIDTH      = 6,
    parameter       AM_ROW_WIDTH     = 5,
    parameter       AM_COL_WIDTH_H   = 5,
    parameter       AM_COL_WIDTH_L   = 4,
    parameter       HIF_KEYID_WIDTH  = `DDRCTL_HIF_KEYID_WIDTH
    )
    (
     input                                                       core_ddrc_core_clk
    ,input                                                       core_ddrc_rstn
    ,input                                                       ddrc_cg_en

    //,dwc_ddrctl_ddrc_cpfcpe_if.o_bm_mp                            o_bm_cpfcpeif
    //,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_bm_mp                         i_gs_bm_cpfcpeif
    //,dwc_ddrctl_ddrc_cpfcpe_if.i_bs_bm_mp                         i_bs_bm_cpfcpeif
    //,dwc_ddrctl_ddrc_cpfcpe_if.o_ih_mp                            o_ih_cpfcpeif
    ,output logic                                                ih_gs_rdlow_empty
    ,output logic                                                ih_gs_rdhigh_empty
    ,output logic                                                ih_gs_any_vpr_timed_out
    ,output logic                                                ih_gs_any_vpw_timed_out

    //,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_ih_mp                         i_gs_ih_cpfcpeif

    //,dwc_ddrctl_ddrc_cpfcpe_if.o_be_mp                            o_be_cpfcpeif
    //,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_be_mp                         i_gs_be_cpfcpeif
    ,input  logic                                                gs_be_op_is_activate
    ,input  logic                                                gs_be_op_is_precharge
    ,input  logic                                                gs_be_op_is_rdwr
    ,input  logic [BSM_BITS-1:0]                                 gs_be_rdwr_bsm_num
    ,input  logic [BSM_BITS-1:0]                                 gs_be_act_bsm_num
    ,input  logic [BSM_BITS-1:0]                                 gs_be_pre_bsm_num
    //,dwc_ddrctl_ddrc_cpfcpe_if.i_bs_be_mp                         i_bs_be_cpfcpeif

    //,dwc_ddrctl_ddrc_cpfcpe_if.o_te_mp                            o_te_cpfcpeif
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_page_hit
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_valid
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wr_page_hit
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wr_valid
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_bank_page_hit
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wr_bank_page_hit
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_hi
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wrecc_btt
    ,output logic [NUM_TOTAL_BSMS*RD_CAM_ADDR_WIDTH-1:0]         te_os_rd_entry_table
    ,output logic [NUM_TOTAL_BSMS*WR_CAM_ADDR_WIDTH_IE-1:0]      te_os_wr_entry_table
    ,output logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                 te_os_rd_page_table
    ,output logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                 te_os_wr_page_table
    ,output logic [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]              te_os_rd_cmd_autopre_table
    ,output logic [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]              te_os_wr_cmd_autopre_table
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_os_rd_pageclose_autopre
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_os_wr_pageclose_autopre
    ,output logic [NUM_TOTAL_BSMS*CMD_LEN_BITS-1:0]              te_os_rd_length_table
    ,output logic [NUM_TOTAL_BSMS*WORD_BITS-1:0]                 te_os_rd_critical_word_table
    ,output logic [NUM_TOTAL_BSMS*MWR_BITS-1:0]                  te_os_mwr_table
    ,output logic [NUM_TOTAL_BSMS-1:0]                           te_b3_bit
    ,output logic [NUM_TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0]      te_os_wr_mr_ram_raddr_lsb_first_table
    ,output logic [NUM_TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]        te_os_wr_mr_pw_num_beats_m1_table

    ,output logic [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0]               te_os_rd_ie_tag_table
    ,output logic [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0]               te_os_wr_ie_tag_table
    ,output logic [BSM_BITS-1:0]                                 te_os_hi_bsm_hint
    ,output logic [BSM_BITS-1:0]                                 te_os_lo_bsm_hint
    ,output logic [BSM_BITS-1:0]                                 te_os_wr_bsm_hint
    ,output logic [BSM_BITS-1:0]                                 te_os_wrecc_bsm_hint
    ,output logic [BSM_BITS-1:0]                                 te_os_lo_act_bsm_hint
    ,output logic [BSM_BITS-1:0]                                 te_os_wr_act_bsm_hint
    ,output logic                                                te_gs_rd_flush
    ,output logic                                                te_gs_wr_flush
    ,output logic                                                te_gs_block_wr
    ,output logic                                                te_gs_any_rd_pending
    ,output logic                                                te_gs_any_wr_pending
    ,output logic                                                te_gs_any_vpr_timed_out
    ,output logic                                                te_gs_any_vpr_timed_out_w
    ,output logic                                                te_gs_any_vpw_timed_out
    ,output logic                                                te_gs_any_vpw_timed_out_w
    ,output logic [NUM_LRANKS-1:0]                               te_gs_rank_wr_pending
    ,output logic [NUM_LRANKS-1:0]                               te_gs_rank_rd_pending
    ,output logic [NUM_TOTAL_BANKS-1:0]                          te_gs_bank_wr_pending
    ,output logic [NUM_TOTAL_BANKS-1:0]                          te_gs_bank_rd_pending
    ,output logic [NUM_LRANKS-1:0]                               te_gs_rank_rd_valid
    ,output logic [NUM_LRANKS-1:0]                               te_gs_rank_wr_valid
    ,output logic [RANK_BITS-1:0]                                te_gs_rank_rd_prefer
    ,output logic [RANK_BITS-1:0]                                te_gs_rank_wr_prefer
    ,output logic [PAGE_BITS-1:0]                                te_pi_rd_addr_ecc_row
    ,output logic [BLK_BITS-1:0]                                 te_pi_rd_addr_blk
//    ,output logic [WORD_BITS-1:0]                                te_pi_rd_critical_word
//    ,output logic [CMD_LEN_BITS-1:0]                             te_pi_rd_length
    ,output logic [CORE_TAG_WIDTH-1:0]                           te_pi_rd_tag
    ,output logic [RMW_TYPE_BITS-1:0]                            te_pi_rd_rmw_type
    ,output logic [WR_CAM_ADDR_WIDTH-1:0]                        te_pi_rd_link_addr
    ,output logic                                                te_pi_rd_addr_err
    ,output logic [BLK_BITS-1:0]                                 te_pi_wr_addr_blk


//`ifdef UMCTL2_PARTIAL_WR  
//   `ifdef MEMC_DDR4
//    ,output logic [2:0]                                          te_pi_wr_bc_sel
//   `endif // MEMC_DDR4
//`endif // UMCTL2_PARTIAL_WR

    ,output logic [BT_BITS-1:0]                                  te_pi_ie_bt
    ,output logic [IE_RD_TYPE_BITS-1:0]                          te_pi_ie_rd_type
    ,output logic [IE_BURST_NUM_BITS-1:0]                        te_pi_ie_blk_burst_num
    ,output logic                                                te_pi_eccap

    ,input  logic                                                gs_te_op_is_rd
    ,input  logic                                                gs_te_op_is_wr
    ,input  logic                                                gs_te_op_is_activate
    ,input  logic                                                gs_te_op_is_precharge
    ,input  logic [BSM_BITS-1:0]                                 gs_te_bsm_num4pre
    ,input  logic [BSM_BITS-1:0]                                 gs_te_bsm_num4rdwr
    ,input  logic [BSM_BITS-1:0]                                 gs_te_bsm_num4act
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
    ,input  logic [CMD_LEN_BITS-1:0]                             gs_te_rd_length
    ,input  logic [WORD_BITS-1:0]                                gs_te_rd_word
      ,input  logic [PARTIAL_WR_BITS_LOG2-1:0]                     gs_te_raddr_lsb_first
        ,input  logic [PW_WORD_CNT_WD_MAX-1:0]                       gs_te_pw_num_beats_m1      
  `endif //SYNTHESIS
`endif //SNPS_ASSERT


//spyglass disable_block W240
//SMD: input never read
//SJ: used in te assertion
//spyglass enable_block W240
    ,input  logic                                                gs_te_wr_mode
    ,input  logic [NUM_TOTAL_BSMS-1:0]                           gs_te_wr_possible
    ,input  logic                                                gs_te_pri_level

    ,input  logic [MAX_CAM_ADDR_WIDTH-1:0]                       os_te_rdwr_entry
    ,input  logic [IE_TAG_BITS-1:0]                              os_te_rdwr_ie_tag

    ,input  [2:0]                                                ddrc_reg_operating_mode_w
    ,input                                                       reg_ddrc_lpddr4
    ,input                                                       reg_ddrc_lpddr5
    ,input  [BANK_ORG_WIDTH-1:0]                                 reg_ddrc_bank_org
    ,input  [2:0]                                                reg_ddrc_nonbinary_device_density
    ,input                                                       reg_ddrc_dis_hif
    ,input                                                       hif_cmd_valid
    ,input  [CMD_TYPE_BITS-1:0]                                  hif_cmd_type
    ,input  [1:0]                                                hif_cmd_pri
    ,input  [CORE_ADDR_INT_WIDTH-1:0]                            hif_cmd_addr
    ,input  [CMD_LEN_BITS-1:0]                                   hif_cmd_length
    ,input  [CORE_TAG_WIDTH-1:0]                                 hif_cmd_token
    ,input  [WDATA_PTR_BITS-1:0]                                 hif_cmd_wdata_ptr
    ,input                                                       hif_cmd_autopre
    ,input                                                       hif_cmd_ecc_region
    ,input  [WRDATA_CYCLES-1:0]                                  hif_cmd_wdata_mask_full_ie
    ,input  [RD_LATENCY_BITS-1:0]                                hif_cmd_latency
    ,input                                                       gsfsm_sr_co_if_stall
    ,output                                                      hif_cmd_stall
    ,output                                                      ih_busy
    ,output                                                      ih_te_ppl_wr_empty
    ,output                                                      ih_te_ppl_rd_empty
    ,output                                                      ih_fifo_rd_empty
    ,output                                                      ih_fifo_wr_empty
    ,output [WDATA_PTR_BITS-1:0]                                 hif_wdata_ptr
    ,output                                                      hif_wdata_ptr_valid
    ,output                                                      hif_wdata_ptr_addr_err
    ,output                                                      hif_wr_credit
    ,output [`MEMC_HIF_CREDIT_BITS-1:0]                          hif_lpr_credit
    ,output [`MEMC_HIF_CREDIT_BITS-1:0]                          hif_hpr_credit
    ,input                                                       reg_ddrc_lpr_num_entries_changed
    ,input                                                       wu_ih_flow_cntrl_req
    ,input                                                       reg_ddrc_ecc_type
    ,output [1:0]                                                hif_wrecc_credit
    ,input  [2:0]                                                reg_ddrc_ecc_mode
    ,input                                                       reg_ddrc_ecc_region_remap_en
    ,input  [6:0]                                                reg_ddrc_ecc_region_map
    ,input  [1:0]                                                reg_ddrc_ecc_region_map_granu
    ,input                                                       reg_ddrc_ecc_region_map_other
    ,input                                                       reg_ddrc_ecc_region_parity_lock
    ,input                                                       reg_ddrc_ecc_region_waste_lock
    ,input  [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0]                reg_ddrc_blk_channel_idle_time_x32
    ,input  [4:0]                                                reg_ddrc_active_blk_channel
    ,input                                                       reg_ddrc_blk_channel_active_term
    ,input [SELFREF_SW_WIDTH-1:0]                                reg_ddrc_selfref_sw
    ,input                                                       reg_ddrc_ecc_ap_en
    ,output                                                      ih_te_rd_valid
    ,output                                                      ih_yy_wr_valid
    ,output                                                      ih_wu_wr_valid
    ,output                                                      ih_te_rd_valid_addr_err
    ,output                                                      ih_yy_wr_valid_addr_err
    ,output [RMW_TYPE_BITS-1:0]                                  ih_yy_rmw_type
    ,output [WR_CAM_ADDR_WIDTH_IE-1:0]                           ih_yy_wr_entry
    ,output [WORD_BITS-1:0]                                      ih_wu_critical_word
    ,input  [WR_CAM_ADDR_WIDTH_IE-1:0]                           mr_yy_free_wr_entry
    ,input                                                       mr_yy_free_wr_entry_valid
    ,output                                                      te_ih_retry
    ,output                                                      te_yy_wr_combine
    ,output                                                      te_yy_wr_combine_noecc
    ,output                                                      te_yy_wr_combine_wrecc
    ,output                                                      ih_yy_xact_valid
    ,output                                                      ih_gs_wr_empty
    ,output                                                      ih_gs_wrecc_empty
    ,input                                                       te_ih_re_done_i
    ,input  [BT_BITS-1:0]                                        te_ih_re_done_bt
    ,output [BRT_BITS-1:0]                                       ih_rd_ie_brt
    ,output                                                      ih_rd_ie_rd_cnt_inc
    ,output                                                      ih_rd_ie_blk_rd_end
    ,output [BWT_BITS-1:0]                                       ih_mr_ie_bwt
    ,output [BRT_BITS-1:0]                                       ih_mr_ie_brt
    ,output                                                      ih_mr_ie_brt_vld
    ,output [NO_OF_BWT-1:0]                                      ih_mr_ie_wr_cnt_dec_vct
    ,output                                                      ih_mr_ie_wr_cnt_inc
    ,output                                                      ih_mr_ie_blk_wr_end
    ,input                                                       mr_ih_free_bwt_vld
    ,input  [BWT_BITS-1:0]                                       mr_ih_free_bwt
    ,input                                                       rd_ih_free_brt_vld
    ,input  [BRT_BITS-1:0]                                       rd_ih_free_brt
    ,input  [BT_BITS-1:0]                                        mr_ih_lkp_bwt_by_bt
    ,input  [BT_BITS-1:0]                                        mr_ih_lkp_brt_by_bt
    ,input  [BT_BITS-1:0]                                        rd_ih_lkp_brt_by_bt
    ,input  [BT_BITS-1:0]                                        rd_ih_lkp_bwt_by_bt
    ,output [BWT_BITS-1:0]                                       ih_mr_lkp_bwt
    ,output                                                      ih_mr_lkp_bwt_vld
    ,output [BRT_BITS-1:0]                                       ih_mr_lkp_brt
    ,output                                                      ih_mr_lkp_brt_vld
    ,output [BRT_BITS-1:0]                                       ih_rd_lkp_brt
    ,output                                                      ih_rd_lkp_brt_vld
    ,output [BWT_BITS-1:0]                                       ih_rd_lkp_bwt
    ,output                                                      ih_rd_lkp_bwt_vld
    ,output                                                      ih_ie_busy
    ,input                                                       rd_ih_ie_re_rdy
    ,input  [RD_CAM_ADDR_WIDTH-1:0]                              reg_ddrc_lpr_num_entries
    ,input   [AM_BANK_WIDTH-1:0]     reg_ddrc_addrmap_bank_b0
    ,input   [AM_BANK_WIDTH-1:0]     reg_ddrc_addrmap_bank_b1
    ,input   [AM_BANK_WIDTH-1:0]     reg_ddrc_addrmap_bank_b2
    ,input   [AM_BG_WIDTH-1:0]       reg_ddrc_addrmap_bg_b0
    ,input   [AM_BG_WIDTH-1:0]       reg_ddrc_addrmap_bg_b1
    ,input   [AM_CS_WIDTH-1:0]       reg_ddrc_addrmap_cs_bit0
    ,input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b3
    ,input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b4
    ,input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b5
    ,input   [AM_COL_WIDTH_L-1:0]    reg_ddrc_addrmap_col_b6
    ,input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b7
    ,input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b8
    ,input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b9
    ,input   [AM_COL_WIDTH_H-1:0]    reg_ddrc_addrmap_col_b10
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b0
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b1
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b2
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b3
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b4
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b5
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b6
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b7
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b8
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b9
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b10
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b11
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b12
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b13
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b14
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b15
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b16
    ,input   [AM_ROW_WIDTH-1:0]      reg_ddrc_addrmap_row_b17
    ,output [RD_CAM_ADDR_WIDTH:0]                                ddrc_reg_dbg_hpr_q_depth
    ,output                                                      ddrc_reg_dbg_stall
    ,output [WR_CAM_ADDR_WIDTH:0]                                ddrc_reg_dbg_wrecc_q_depth
//spyglass disable_block W240
//SMD: A signal or variable is set but never read
//SJ: used in te assertion
    ,input  [BURST_RDWR_WIDTH-1:0]                               reg_ddrc_burst_rdwr
//spyglass enable_block W240
    ,output [WR_CAM_ADDR_WIDTH:0]                                ddrc_reg_dbg_w_q_depth
    ,output [RD_CAM_ADDR_WIDTH:0]                                ddrc_reg_dbg_lpr_q_depth
//spyglass disable_block W240
//SMD: A signal or variable is set but never read
//SJ: the inputs are not used in some configuration
    ,input                                                       reg_ddrc_frequency_ratio
//spyglass enable_block W240

    ,input                                                       reg_ddrc_pageclose
    ,input  [7:0]                                                reg_ddrc_pageclose_timer
    ,input  [2:0]                                                reg_ddrc_page_hit_limit_rd
    ,input  [2:0]                                                reg_ddrc_page_hit_limit_wr
    ,input                                                       reg_ddrc_opt_hit_gt_hpr
    ,input  [2:0]                                                reg_ddrc_visible_window_limit_rd
    ,input  [2:0]                                                reg_ddrc_visible_window_limit_wr
    ,input                                                       reg_ddrc_dis_opt_ntt_by_act
    ,input                                                       reg_ddrc_dis_opt_ntt_by_pre
    ,input                                                       reg_ddrc_autopre_rmw
    ,input                                                       reg_ddrc_dis_wc
    ,output [NUM_TOTAL_BANKS-1:0]                                te_dh_rd_page_hit
    ,output [NUM_TOTAL_BANKS-1:0]                                te_dh_rd_valid
    ,output [NUM_TOTAL_BANKS-1:0]                                te_dh_wr_page_hit
    ,output [NUM_TOTAL_BANKS-1:0]                                te_dh_wr_valid
    ,output [NUM_TOTAL_BANKS-1:0]                                te_dh_rd_hi
    ,input                                                       ih_te_rd_valid_no_addrerr
    ,input                                                       ih_yy_wr_valid_no_addrerr
    ,input  [OTHER_WR_ENTRY_BITS-1:0]                            ih_te_wr_other_fields
    ,input                                                       ih_yy_rd_addr_err
    ,input  [1:0]                                                wu_te_enable_wr
    ,input  [WR_CAM_ADDR_WIDTH-1:0]                              wu_te_entry_num
    ,input  [PARTIAL_WR_BITS-1:0]                                wu_te_wr_word_valid
    ,input  [PARTIAL_WR_BITS_LOG2-1:0]                           wu_te_ram_raddr_lsb_first
    ,input  [PW_WORD_CNT_WD_MAX-1:0]                             wu_te_pw_num_beats_m1
    ,input  [PW_WORD_CNT_WD_MAX-1:0]                             wu_te_pw_num_cols_m1
    ,output [WR_CAM_ADDR_WIDTH_IE-1:0]                           te_mr_wr_ram_addr
    ,output [WR_CAM_ADDR_WIDTH-1:0]                              te_wu_entry_num
    ,input  [MWR_BITS-1:0]                                       wu_te_mwr
//     ,input  [AUTOPRE_BITS-1:0]                                   ts_rdwr_cmd_autopre
    ,output                                                      ddrc_co_perf_war_hazard_w
    ,output                                                      ddrc_co_perf_raw_hazard_w
    ,output                                                      ddrc_co_perf_waw_hazard_w
    ,output                                                      ddrc_co_perf_ie_blk_hazard_w
    ,output                                                      ddrc_co_perf_vlimit_reached_rd_w
    ,output                                                      ddrc_co_perf_vlimit_reached_wr_w
    ,input                                                       ts_te_autopre
    ,output [NUM_TOTAL_BSMS-1:0]                                 te_ts_vpw_valid
    ,output [NUM_TOTAL_BSMS-1:0]                                 te_ts_vpr_valid
    ,output                                                      te_wu_wr_retry
    ,output [PARTIAL_WR_BITS-1:0]                                te_pi_wr_word_valid
   // ,output [PARTIAL_WR_BITS_LOG2-1:0]                           te_mr_ram_raddr_lsb_first
   // ,output [PW_WORD_CNT_WD_MAX-1:0]                             te_mr_pw_num_beats_m1
    ,input  [PAGE_BITS-1:0]                                      ts_act_page
    ,input                                                       reg_ddrc_dis_opt_wrecc_collision_flush

    ,output [BT_BITS-1:0]                                        te_mr_ie_bt
    ,output [IE_WR_TYPE_BITS-1:0]                                te_mr_ie_wr_type
    ,output [IE_BURST_NUM_BITS-1:0]                              te_mr_ie_blk_burst_num
    ,output                                                      te_mr_eccap
    ,input  [NUM_TOTAL_BSMS-1:0]                                 ts_te_sel_act_wr
    ,output [NUM_TOTAL_BSMS-1:0]                                 te_rws_wr_col_bank
    ,output [NUM_TOTAL_BSMS-1:0]                                 te_rws_rd_col_bank
    ,output [WR_CAM_ADDR_WIDTH_IE:0]                             te_num_wr_pghit_entries
    ,output [RD_CAM_ADDR_WIDTH:0]                                te_num_rd_pghit_entries
    ,output [WR_CAM_ADDR_WIDTH:0]                                te_wr_entry_avail
   ,output [WR_CAM_ADDR_WIDTH:0]                                 te_wrecc_entry_avail      // Number of non-valid entries (WRECCCAM only, not include WR CAM), valid status
   ,output [WR_CAM_ADDR_WIDTH:0]                                 te_wrecc_entry_loaded     // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   ,input                                                        ts_te_force_btt

    ,output [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                       be_os_page_table


`ifdef SNPS_ASSERT_ON
    ,output [WR_CAM_ENTRIES_IE-1:0]                              te_ts_wr_entry_valid  // valid write entry in CAM, over entire CAM
    ,output [RD_CAM_ENTRIES-1:0]                                 te_ts_rd_entry_valid  // valid read entry in CAM, over entire CAM
    ,output [WR_CAM_ENTRIES_IE-1:0]                              te_ts_wr_page_hit_entries  // page-hit entry in CAM
    ,output [RD_CAM_ENTRIES-1:0]                                 te_ts_rd_page_hit_entries 
    ,input  [1:0]                                                reg_ddrc_data_bus_width
`endif // SNPS_ASSERT_ON

    ,output                                                      te_rd_bank_pghit_vld_prefer
    ,output                                                      te_wr_bank_pghit_vld_prefer


    ,input                                              reg_ddrc_bank_hash_en
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
    ,input                                             reg_ddrc_opt_vprw_sch
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
    ,input                                             core_ddrc_core_clk_te
    ,output                                            input_fifo_empty
    ,output                                            ih_te_ppl_empty
    );


    wire    [CMD_LEN_BITS-1:0]                                   ih_te_rd_length;
    wire    [LRANK_BITS-1:0]                                     ih_te_rd_rank_num;
    wire    [LRANK_BITS-1:0]                                     ih_te_wr_rank_num;
    wire    [`MEMC_BG_BITS -1:0]                                 ih_te_rd_bankgroup_num;
    wire    [`MEMC_BG_BITS -1:0]                                 ih_te_wr_bankgroup_num;
    wire    [BG_BANK_BITS-1:0]                                   ih_te_rd_bg_bank_num;
    wire    [BG_BANK_BITS-1:0]                                   ih_te_wr_bg_bank_num;
    wire    [BANK_BITS-1:0]                                      ih_te_rd_bank_num;
    wire    [BANK_BITS-1:0]                                      ih_te_wr_bank_num;
    wire    [PAGE_BITS-1:0]                                      ih_te_rd_page_num;
    wire    [PAGE_BITS-1:0]                                      ih_te_wr_page_num;
    wire    [BLK_BITS-1:0]                                       ih_te_rd_block_num;
    wire    [BLK_BITS-1:0]                                       ih_te_wr_block_num;
    wire    [WORD_BITS-1:0]                                      ih_te_critical_dword;
    wire    [RD_CAM_ADDR_WIDTH-1:0]                              ih_te_lo_rd_prefer;
    wire    [WR_CAM_ADDR_WIDTH-1:0]                              ih_te_wr_prefer;
    wire    [WR_ECC_CAM_ADDR_WIDTH-1:0]                          ih_te_wrecc_prefer;
    wire    [RD_CAM_ADDR_WIDTH-1:0]                              ih_te_rd_entry;
    wire                                                         ih_te_rd_autopre;
    wire                                                         ih_te_wr_autopre;
    wire    [1:0]                                                ih_te_rd_hi_pri;
    wire    [1:0]                                                ih_te_wr_hi_pri;
    wire    [RD_CAM_ADDR_WIDTH-1:0]                              ih_te_hi_rd_prefer;
    wire    [RD_LATENCY_BITS-1:0]                                ih_te_rd_latency;
    wire    [WR_LATENCY_BITS-1:0]                                ih_te_wr_latency;
    wire    [RD_CAM_ADDR_WIDTH-1:0]                              te_ih_free_rd_entry;
    wire                                                         te_ih_free_rd_entry_valid;
    wire    [BT_BITS-1:0]                                        ih_te_ie_bt;
    wire    [IE_RD_TYPE_BITS-1:0]                                ih_te_ie_rd_type;
    wire    [IE_WR_TYPE_BITS-1:0]                                ih_te_ie_wr_type;
    wire    [IE_BURST_NUM_BITS-1:0]                              ih_te_ie_blk_burst_num;
    wire    [`MEMC_BLK_BITS-1:0]                                 ih_te_ie_block_num;
    wire    [NO_OF_BT-1:0]                                       ih_te_ie_re_vct;
    wire    [NO_OF_BT-1:0]                                       ih_te_ie_btt_vct;
    wire                                                         ih_te_rd_eccap;
    wire                                                         ih_te_wr_eccap;
`ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
    `endif // SYNTHESIS
`endif // SNPS_ASSERT_ON
    wire    [LRANK_BITS-1:0]                                     ih_yy_rank_num_wr;
    wire    [BG_BANK_BITS-1:0]                                   ih_yy_bg_bank_num_wr;
    wire                                                         ih_be_hi_pri_rd_xact_unused;
    wire    [MWR_BITS-1:0]                                       ih_te_mwr;
    wire    [PARTIAL_WR_BITS-1:0]                                ih_te_wr_word_valid;
    wire    [PARTIAL_WR_BITS_LOG2-1:0]                           ih_te_wr_ram_raddr_lsb_first;
    wire    [PW_WORD_CNT_WD_MAX-1:0]                             ih_te_wr_pw_num_beats_m1;
    wire    [PW_WORD_CNT_WD_MAX-1:0]                             ih_te_wr_pw_num_cols_m1;

    wire                                                         be_te_page_hit;
    wire                                                         be_te_wr_page_hit;
    wire                                                         be_wr_page_hit;
    wire    [BSM_BITS-1:0]                                       te_be_bsm_num;
    wire    [PAGE_BITS-1:0]                                      te_be_page_num;
    wire                                                         te_gs_hi_rd_page_hit_vld_unused;
    wire    [OTHER_WR_ENTRY_BITS-1:0]                            te_pi_wr_other_fields_wr_unused;

    wire    [PARTIAL_WR_BITS-1:0]                                te_pi_wr_word_valid_w;
    wire    [WR_CAM_ADDR_WIDTH_IE-1:0]                           te_mr_wr_ram_addr_w;

    wire    [CORE_TAG_WIDTH-1:0]                                 ih_te_rd_tag;

    wire                                                         te_ih_rd_retry;

    wire    [LRANK_BITS-1:0]                                     ih_yy_rank_num_rd;
    wire    [BG_BANK_BITS-1:0]                                   ih_yy_bg_bank_num_rd;
    wire    [PAGE_BITS -1:0]                                     ih_be_page_num;
    wire                                                         gs_te_op_is_precharge_int; // For per-bank pre-charge
    wire                                                         gs_be_op_is_precharge_int; // For per-bank pre-charge


wire   [WR_CAM_ADDR_WIDTH-1:0]        ih_yy_wr_entry_rmw;


wire                    ih_busy_w;



`ifdef SNPS_ASSERT_ON
`endif // SNPS_ASSERT_ON


//`DDRCTL_LLC
//`endif // DDRCTL_LLC


//------------------------------------------------------------------------------
// IH (Input Handler) block
//------------------------------------------------------------------------------

assign ih_busy = ih_busy_w;

`ifdef SNPS_ASSERT_ON
`endif // SNPS_ASSERT_ON


localparam DDRCTL_DDR_EN                       = `DDRCTL_DDR_EN;
localparam SELFREF_SW_WIDTH_INT = (`DDRCTL_DDR_EN == 1) ? SELFREF_SW_WIDTH/`MEMC_NUM_RANKS : SELFREF_SW_WIDTH;

wire [SELFREF_SW_WIDTH_INT-1:0]                                reg_ddrc_selfref_sw_w;

//spyglass disable_block W164b
//SMD: LHS: 'reg_ddrc_selfref_sw_w' width 2 is greater than RHS:
// 'reg_ddrc_selfref_sw[(SELFREF_SW_WIDTH - 1):0] ' width 1
// assignment
//SJ: MSB are not used in DDR4 controller
//
assign reg_ddrc_selfref_sw_w = reg_ddrc_selfref_sw[SELFREF_SW_WIDTH-1:0];
//spyglass enable_block W164b

ih

        #(      .CORE_ADDR_WIDTH                (CORE_ADDR_INT_WIDTH)
               ,.IH_TAG_WIDTH                   (CORE_TAG_WIDTH)
               ,.CMD_LEN_BITS                   (CMD_LEN_BITS)
               ,.WRCMD_ENTRY_BITS               (WR_CAM_ADDR_WIDTH)
               ,.WRECCCMD_ENTRY_BITS            (WR_ECC_CAM_ADDR_WIDTH)
               ,.WRCMD_ENTRY_BITS_IE            (WR_CAM_ADDR_WIDTH_IE)
               ,.RDCMD_ENTRY_BITS               (RD_CAM_ADDR_WIDTH)
               ,.RMW_TYPE_BITS                  (RMW_TYPE_BITS)
               ,.WRDATA_CYCLES                  (WRDATA_CYCLES)
               ,.RD_LATENCY_BITS                (RD_LATENCY_BITS)
               ,.WR_LATENCY_BITS                (WR_LATENCY_BITS)
               ,.BT_BITS                        (BT_BITS         )
               ,.BWT_BITS                       (BWT_BITS         )
               ,.BRT_BITS                       (BRT_BITS         )
               ,.NO_OF_BT                       (NO_OF_BT         )
               ,.NO_OF_BWT                      (NO_OF_BWT        )
               ,.NO_OF_BRT                      (NO_OF_BRT        )
               ,.NO_OF_BLK_CHN                  (NO_OF_BLK_CHN    )
               ,.BLK_CHN_BITS                   (BLK_CHN_BITS     )
               ,.IE_RD_TYPE_BITS                (IE_RD_TYPE_BITS  )
               ,.IE_WR_TYPE_BITS                (IE_WR_TYPE_BITS  )
               ,.IE_BURST_NUM_BITS              (IE_BURST_NUM_BITS)
               ,.WDATA_PTR_BITS                 (WDATA_PTR_BITS)
               ,.MWR_BITS                       (MWR_BITS)
               ,.PARTIAL_WR_BITS                (PARTIAL_WR_BITS)
               ,.PARTIAL_WR_BITS_LOG2           (PARTIAL_WR_BITS_LOG2)
               ,.RETRY_TIMES_WIDTH              (RETRY_TIMES_WIDTH)
               ,.PW_WORD_CNT_WD_MAX             (PW_WORD_CNT_WD_MAX)

               ,.AM_DCH_WIDTH           (AM_DCH_WIDTH     )
               ,.AM_CS_WIDTH            (AM_CS_WIDTH      )
               ,.AM_CID_WIDTH           (AM_CID_WIDTH     )
               ,.AM_BANK_WIDTH          (AM_BANK_WIDTH    )
               ,.AM_BG_WIDTH            (AM_BG_WIDTH      )
               ,.AM_ROW_WIDTH           (AM_ROW_WIDTH     )
               ,.AM_COL_WIDTH_H         (AM_COL_WIDTH_H   )
               ,.AM_COL_WIDTH_L         (AM_COL_WIDTH_L   )
 
               ,.HIF_KEYID_WIDTH        (HIF_KEYID_WIDTH  )
 
                )
        ih (
                .co_ih_clk                      (core_ddrc_core_clk),
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .ddrc_cg_en                     (ddrc_cg_en),
                .dh_ih_operating_mode           (ddrc_reg_operating_mode_w),
                .reg_ddrc_lpddr5                (reg_ddrc_lpddr5),
                .reg_ddrc_bank_org              (reg_ddrc_bank_org),
                .dh_ih_nonbinary_device_density (reg_ddrc_nonbinary_device_density),
                .dh_ih_dis_hif                  (reg_ddrc_dis_hif),

                .hif_cmd_valid                  (hif_cmd_valid),
                .hif_cmd_type                   (hif_cmd_type),
                .hif_cmd_pri                    (hif_cmd_pri),
                .hif_cmd_addr                   (hif_cmd_addr),
                .hif_cmd_length                 (hif_cmd_length),
                .hif_cmd_token                  (hif_cmd_token),
                .hif_cmd_wdata_ptr              (hif_cmd_wdata_ptr),
                .hif_cmd_autopre                (hif_cmd_autopre),
                .hif_cmd_ecc_region             (hif_cmd_ecc_region     ),
                .hif_cmd_wdata_mask_full_ie     (hif_cmd_wdata_mask_full_ie),
                .hif_cmd_latency                (hif_cmd_latency),

                .gsfsm_sr_co_if_stall           (gsfsm_sr_co_if_stall),
                .hif_cmd_stall                  (hif_cmd_stall),
                .ih_busy                        (ih_busy_w),
                .ih_te_ppl_wr_empty             (ih_te_ppl_wr_empty),
                .ih_te_ppl_rd_empty             (ih_te_ppl_rd_empty),
                .ih_fifo_rd_empty               (ih_fifo_rd_empty),
                .ih_fifo_wr_empty               (ih_fifo_wr_empty),
                .hif_wdata_ptr                  (hif_wdata_ptr),
                .hif_wdata_ptr_valid            (hif_wdata_ptr_valid),
                .hif_wdata_ptr_addr_err         (hif_wdata_ptr_addr_err),
                .hif_wr_credit                  (hif_wr_credit),
                .hif_lpr_credit                 (hif_lpr_credit),
                .hif_hpr_credit                 (hif_hpr_credit),
                .co_ih_lpr_num_entries_changed  (reg_ddrc_lpr_num_entries_changed),
                .wu_ih_flow_cntrl_req           (wu_ih_flow_cntrl_req),
                .reg_ddrc_ecc_type              (reg_ddrc_ecc_type),
                .hif_wrecc_credit               (hif_wrecc_credit),
                .reg_ddrc_ecc_mode              (reg_ddrc_ecc_mode),
                .reg_ddrc_ecc_region_remap_en   (reg_ddrc_ecc_region_remap_en),
                .reg_ddrc_ecc_region_map        (reg_ddrc_ecc_region_map),
                .reg_ddrc_ecc_region_map_granu  (reg_ddrc_ecc_region_map_granu),
                .reg_ddrc_ecc_region_map_other  (reg_ddrc_ecc_region_map_other),
                .reg_ddrc_ecc_region_parity_lock (reg_ddrc_ecc_region_parity_lock),
                .reg_ddrc_ecc_region_waste_lock (reg_ddrc_ecc_region_waste_lock),
                .reg_ddrc_blk_channel_idle_time_x32 (reg_ddrc_blk_channel_idle_time_x32),
                .reg_ddrc_active_blk_channel    (reg_ddrc_active_blk_channel),
                .reg_ddrc_blk_channel_active_term (reg_ddrc_blk_channel_active_term),
                //for low power
                .reg_ddrc_selfref_sw            (reg_ddrc_selfref_sw_w[SELFREF_SW_WIDTH-1:0]),
                .reg_ddrc_ecc_ap_en             (reg_ddrc_ecc_ap_en),

                .ih_te_rd_valid                 (ih_te_rd_valid),
                .ih_te_wr_valid                 (ih_yy_wr_valid),
                .ih_wu_wr_valid                 (ih_wu_wr_valid),
                .ih_te_rd_valid_addr_err        (ih_te_rd_valid_addr_err),
                .ih_te_wr_valid_addr_err        (ih_yy_wr_valid_addr_err),
                .ih_te_rd_length                (ih_te_rd_length),
                .ih_te_rd_tag                   (ih_te_rd_tag),
                .ih_te_rmwtype                  (ih_yy_rmw_type),
                .ih_te_rd_rank_num              (ih_te_rd_rank_num),
                .ih_te_wr_rank_num              (ih_te_wr_rank_num),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used in TB.
                .ih_te_rd_bankgroup_num         (ih_te_rd_bankgroup_num),
                .ih_te_wr_bankgroup_num         (ih_te_wr_bankgroup_num),
                .ih_te_rd_bg_bank_num           (ih_te_rd_bg_bank_num),
                .ih_te_wr_bg_bank_num           (ih_te_wr_bg_bank_num),
                .ih_te_rd_bank_num              (ih_te_rd_bank_num),
                .ih_te_wr_bank_num              (ih_te_wr_bank_num),

                .ih_te_rd_page_num              (ih_te_rd_page_num),
                .ih_te_wr_page_num              (ih_te_wr_page_num),
                .ih_te_rd_block_num             (ih_te_rd_block_num),
                .ih_te_wr_block_num             (ih_te_wr_block_num),
                .ih_te_critical_dword           (ih_te_critical_dword),
                .ih_te_lo_rd_prefer             (ih_te_lo_rd_prefer),
                .ih_te_wr_prefer                (ih_te_wr_prefer),
                .ih_te_wrecc_prefer             (ih_te_wrecc_prefer),
//spyglass enable_block W528
                .ih_te_rd_entry                 (ih_te_rd_entry),
                .ih_te_wr_entry                 (ih_yy_wr_entry),
                .ih_te_wr_entry_rmw             (ih_yy_wr_entry_rmw),
                .ih_wu_critical_dword           (ih_wu_critical_word),
                .ih_te_rd_autopre               (ih_te_rd_autopre),
                .ih_te_wr_autopre               (ih_te_wr_autopre),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used only in certain config, but signal should always exist (used in TB).
                .ih_te_rd_hi_pri                (ih_te_rd_hi_pri),
                .ih_te_wr_hi_pri                (ih_te_wr_hi_pri),
                .ih_te_hi_rd_prefer             (ih_te_hi_rd_prefer),
//spyglass enable_block W528
                .ih_te_rd_latency               (ih_te_rd_latency),
                .ih_te_wr_latency               (ih_te_wr_latency),

                .te_ih_free_rd_entry            (te_ih_free_rd_entry),
                .te_ih_free_rd_entry_valid      (te_ih_free_rd_entry_valid),
                .mr_ih_free_wr_entry            (mr_yy_free_wr_entry),
                .mr_ih_free_wr_entry_valid      (mr_yy_free_wr_entry_valid),
                .te_ih_retry                    (te_ih_retry),
                .te_ih_wr_combine               (te_yy_wr_combine),

                .ih_yy_xact_valid               (ih_yy_xact_valid),
                .ih_gs_rdlow_empty              (ih_gs_rdlow_empty),
                .ih_gs_wr_empty                 (ih_gs_wr_empty),
                .ih_gs_wrecc_empty              (ih_gs_wrecc_empty),

                .ih_gs_rdhigh_empty             (ih_gs_rdhigh_empty),

                .te_gs_any_vpr_timed_out        (te_gs_any_vpr_timed_out),
                .ih_gs_any_vpr_timed_out        (ih_gs_any_vpr_timed_out),
                .ih_gs_any_vpw_timed_out        (ih_gs_any_vpw_timed_out),

                .te_ih_re_done_i                (te_ih_re_done_i        ),
                .te_ih_re_done_bt               (te_ih_re_done_bt       ),
                .ih_te_ie_bt                    (ih_te_ie_bt            ),
                .ih_te_ie_rd_type               (ih_te_ie_rd_type       ),
                .ih_te_ie_wr_type               (ih_te_ie_wr_type       ),
                .ih_te_ie_blk_burst_num         (ih_te_ie_blk_burst_num ),  //only for the Data command
                .ih_te_ie_block_num             (ih_te_ie_block_num     ),
                .ih_rd_ie_brt                   (ih_rd_ie_brt           ),
                .ih_rd_ie_rd_cnt_inc            (ih_rd_ie_rd_cnt_inc    ),
                .ih_rd_ie_blk_rd_end            (ih_rd_ie_blk_rd_end    ),
                .ih_mr_ie_bwt                   (ih_mr_ie_bwt           ),
                .ih_mr_ie_brt                   (ih_mr_ie_brt           ),
                .ih_mr_ie_brt_vld               (ih_mr_ie_brt_vld       ),
                .ih_mr_ie_wr_cnt_dec_vct        (ih_mr_ie_wr_cnt_dec_vct),
                .ih_ie_empty                    (ih_ie_empty_unused     ), // not used
                .ih_mr_ie_wr_cnt_inc            (ih_mr_ie_wr_cnt_inc    ),
                .ih_mr_ie_blk_wr_end            (ih_mr_ie_blk_wr_end    ),
                .mr_ih_free_bwt_vld             (mr_ih_free_bwt_vld     ),
                .mr_ih_free_bwt                 (mr_ih_free_bwt         ),
                .rd_ih_free_brt_vld             (rd_ih_free_brt_vld     ),
                .rd_ih_free_brt                 (rd_ih_free_brt         ),
   //signals for look up BT table
                .mr_ih_lkp_bwt_by_bt            (mr_ih_lkp_bwt_by_bt ),
                .mr_ih_lkp_brt_by_bt            (mr_ih_lkp_brt_by_bt ),
                .rd_ih_lkp_brt_by_bt            (rd_ih_lkp_brt_by_bt ),
                .rd_ih_lkp_bwt_by_bt            (rd_ih_lkp_bwt_by_bt ),
                .ih_mr_lkp_bwt                  (ih_mr_lkp_bwt       ),
                .ih_mr_lkp_bwt_vld              (ih_mr_lkp_bwt_vld   ),
                .ih_mr_lkp_brt                  (ih_mr_lkp_brt       ),
                .ih_mr_lkp_brt_vld              (ih_mr_lkp_brt_vld   ),
                .ih_rd_lkp_brt                  (ih_rd_lkp_brt       ),
                .ih_rd_lkp_brt_vld              (ih_rd_lkp_brt_vld   ),
                .ih_rd_lkp_bwt                  (ih_rd_lkp_bwt       ),
                .ih_rd_lkp_bwt_vld              (ih_rd_lkp_bwt_vld   ),
                .ih_ie_busy                     (ih_ie_busy          ),
                .rd_ih_ie_re_rdy                (rd_ih_ie_re_rdy     ),
                .ih_te_ie_re_vct                (ih_te_ie_re_vct     ),
                .ih_te_ie_btt_vct               (ih_te_ie_btt_vct    ),
                .ih_te_rd_eccap                 (ih_te_rd_eccap      ),
                .ih_te_wr_eccap                 (ih_te_wr_eccap      ),

`ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
    `endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
                .ih_be_rank_num_rd              (ih_yy_rank_num_rd),
                .ih_be_rank_num_wr              (ih_yy_rank_num_wr),
                .ih_be_bg_bank_num_rd           (ih_yy_bg_bank_num_rd),
                .ih_be_bg_bank_num_wr           (ih_yy_bg_bank_num_wr),
                .ih_be_page_num                 (ih_be_page_num),
//spyglass enable_block W528
                .ih_be_hi_pri_rd_xact           (ih_be_hi_pri_rd_xact_unused),
                .dh_ih_lpr_num_entries          (reg_ddrc_lpr_num_entries),
                .dh_ih_addrmap_rank_b0          (reg_ddrc_addrmap_cs_bit0),
                .dh_ih_addrmap_bank_b0          (reg_ddrc_addrmap_bank_b0),
                .dh_ih_addrmap_bank_b1          (reg_ddrc_addrmap_bank_b1),
                .dh_ih_addrmap_bank_b2          (reg_ddrc_addrmap_bank_b2),
                .dh_ih_addrmap_bg_b0            (reg_ddrc_addrmap_bg_b0),
                .dh_ih_addrmap_bg_b1            (reg_ddrc_addrmap_bg_b1),
                .dh_ih_addrmap_col_b3           (reg_ddrc_addrmap_col_b3),
                .dh_ih_addrmap_col_b4           (reg_ddrc_addrmap_col_b4),
                .dh_ih_addrmap_col_b5           (reg_ddrc_addrmap_col_b5),
                .dh_ih_addrmap_col_b6           (reg_ddrc_addrmap_col_b6),
                .dh_ih_addrmap_col_b7           (reg_ddrc_addrmap_col_b7),
                .dh_ih_addrmap_col_b8           (reg_ddrc_addrmap_col_b8),
                .dh_ih_addrmap_col_b9           (reg_ddrc_addrmap_col_b9),
                .dh_ih_addrmap_col_b10          (reg_ddrc_addrmap_col_b10),
                .dh_ih_addrmap_row_b0           (reg_ddrc_addrmap_row_b0),
                .dh_ih_addrmap_row_b1           (reg_ddrc_addrmap_row_b1),
                .dh_ih_addrmap_row_b2           (reg_ddrc_addrmap_row_b2),
                .dh_ih_addrmap_row_b3           (reg_ddrc_addrmap_row_b3),
                .dh_ih_addrmap_row_b4           (reg_ddrc_addrmap_row_b4),
                .dh_ih_addrmap_row_b5           (reg_ddrc_addrmap_row_b5),
                .dh_ih_addrmap_row_b6           (reg_ddrc_addrmap_row_b6),
                .dh_ih_addrmap_row_b7           (reg_ddrc_addrmap_row_b7),
                .dh_ih_addrmap_row_b8           (reg_ddrc_addrmap_row_b8),
                .dh_ih_addrmap_row_b9           (reg_ddrc_addrmap_row_b9),
                .dh_ih_addrmap_row_b10          (reg_ddrc_addrmap_row_b10),
                .dh_ih_addrmap_row_b11          (reg_ddrc_addrmap_row_b11),
                .dh_ih_addrmap_row_b12          (reg_ddrc_addrmap_row_b12),
                .dh_ih_addrmap_row_b13          (reg_ddrc_addrmap_row_b13),
                .dh_ih_addrmap_row_b14          (reg_ddrc_addrmap_row_b14),
                .dh_ih_addrmap_row_b15          (reg_ddrc_addrmap_row_b15),
                .dh_ih_addrmap_row_b16          (reg_ddrc_addrmap_row_b16),
                .dh_ih_addrmap_row_b17          (reg_ddrc_addrmap_row_b17),
                .ih_dh_hpr_q_depth              (ddrc_reg_dbg_hpr_q_depth),

                .ih_dh_stall                    (ddrc_reg_dbg_stall),
                .ih_dh_wrecc_q_depth            (ddrc_reg_dbg_wrecc_q_depth),
                .reg_ddrc_burst_rdwr            (reg_ddrc_burst_rdwr),
                .ih_dh_wr_q_depth               (ddrc_reg_dbg_w_q_depth),
                .ih_dh_lpr_q_depth              (ddrc_reg_dbg_lpr_q_depth)
                ,.ih_te_mwr                     (ih_te_mwr)
                ,.ih_te_wr_word_valid           (ih_te_wr_word_valid)
                ,.reg_ddrc_frequency_ratio      (reg_ddrc_frequency_ratio)

                ,.ih_te_wr_ram_raddr_lsb_first  (ih_te_wr_ram_raddr_lsb_first)
                ,.ih_te_wr_pw_num_beats_m1      (ih_te_wr_pw_num_beats_m1)
                ,.ih_te_wr_pw_num_cols_m1       (ih_te_wr_pw_num_cols_m1)

       ,.reg_ddrc_bank_hash_en                     (reg_ddrc_bank_hash_en                         )
               ,.input_fifo_empty               (input_fifo_empty)
               ,.ih_te_ppl_empty                (ih_te_ppl_empty)
);

//------------------------------------------------------------------------------
// TE (Transaction Evaluation) block : contains CAMs and next tables
//------------------------------------------------------------------------------
teengine
 #(
                .CHANNEL_NUM            (CHANNEL_NUM),
                .RANK_BITS              (RANK_BITS),
                .LRANK_BITS             (LRANK_BITS),
                .BANK_BITS              (BANK_BITS),
                .PAGE_BITS              (PAGE_BITS),
                .BLK_BITS               (BLK_BITS),
                .WORD_BITS              (WORD_BITS),
                .CMD_LEN_BITS           (CMD_LEN_BITS),
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(1 + CMD_LEN_BITS)' found in module 'ddrc_ctrl'
//SJ: This coding style is acceptable and there is no plan to change it.
                .OTHER_RD_ENTRY_BITS    (OTHER_RD_ENTRY_BITS),   // critical dword
//spyglass enable_block SelfDeterminedExpr-ML
                .OTHER_WR_ENTRY_BITS    (OTHER_WR_ENTRY_BITS),   // critical dword, RMW type
                .OTHER_RD_RMW_LSB       (`MEMC_TAGBITS),            // LSB of RMW type for RD_OTHER field
                .OTHER_RD_RMW_TYPE_BITS (RMW_TYPE_BITS),        // no if bits of RMW type for RD_OTHER field
                .PW_BC_SEL_BITS         (PW_BC_SEL_BITS),
                .MWR_BITS               (MWR_BITS),
                .PARTIAL_WR_BITS        (PARTIAL_WR_BITS),
                .PW_WORD_CNT_WD_MAX     (PW_WORD_CNT_WD_MAX),
                .RD_LATENCY_BITS        (`UMCTL2_XPI_RQOS_TW),
                .WR_LATENCY_BITS        (`UMCTL2_XPI_WQOS_TW),
                .HI_PRI_BITS            (2),
                .BT_BITS                (BT_BITS),
                .NO_OF_BT               (NO_OF_BT),
                .IE_RD_TYPE_BITS        (IE_RD_TYPE_BITS),
                .IE_WR_TYPE_BITS        (IE_WR_TYPE_BITS),
                .IE_BURST_NUM_BITS      (IE_BURST_NUM_BITS),
                .IE_MASKED_BITS         (1),
                .IE_TAG_BITS            (IE_TAG_BITS),
                .AUTOPRE_BITS           (AUTOPRE_BITS),
                .ECCAP_BITS             (ECCAP_BITS),

                .ENTRY_RETRY_TIMES_WIDTH (ENTRY_RETRY_TIMES_WIDTH), // == RETRY_TIMES_WIDTH + 1, if DDRCTL_ANY_RETRY is enabled
                .RETRY_TIMES_WIDTH      (RETRY_TIMES_WIDTH), 
                .RETRY_WR_BITS          (RETRY_WR_BITS    ),
                .RETRY_RD_BITS          (RETRY_RD_BITS    ),
                .DDR4_COL3_BITS         (DDR4_COL3_BITS),
                .LP_COL4_BITS           (LP_COL4_BITS),
                .RMW_BITS               (1),
                .WP_BITS                (NUM_TOTAL_BSMS), // only For DDR5/4 ,LPDDR5/4
                .RD_CAM_ADDR_BITS       (RD_CAM_ADDR_WIDTH),
                .WR_CAM_ADDR_BITS       (WR_CAM_ADDR_WIDTH),
                .WR_ECC_CAM_ADDR_BITS   (WR_ECC_CAM_ADDR_WIDTH),
                .WR_CAM_ADDR_BITS_IE    (WR_CAM_ADDR_WIDTH_IE),
                .MAX_CAM_ADDR_BITS      (MAX_CAM_ADDR_WIDTH),
                .RD_CAM_ENTRIES         (RD_CAM_ENTRIES),
                .WR_CAM_ENTRIES         (WR_CAM_ENTRIES),
                .WR_CAM_ENTRIES_IE      (WR_CAM_ENTRIES_IE),
                .WR_ECC_CAM_ENTRIES     (WR_ECC_CAM_ENTRIES),
                .AM_COL_WIDTH_H         (AM_COL_WIDTH_H   ),
                .AM_COL_WIDTH_L         (AM_COL_WIDTH_L   ),
                .HIF_KEYID_WIDTH        (HIF_KEYID_WIDTH  )
 )


        teengine (
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .co_te_clk                      (core_ddrc_core_clk_te),
                .ddrc_cg_en                     (ddrc_cg_en),
                .dh_te_pageclose                (reg_ddrc_pageclose),
                .dh_te_pageclose_timer          (reg_ddrc_pageclose_timer),
                .reg_ddrc_page_hit_limit_rd     (reg_ddrc_page_hit_limit_rd),
                .reg_ddrc_page_hit_limit_wr     (reg_ddrc_page_hit_limit_wr),
                .reg_ddrc_opt_hit_gt_hpr        (reg_ddrc_opt_hit_gt_hpr),
                .reg_ddrc_visible_window_limit_rd (reg_ddrc_visible_window_limit_rd),
                .reg_ddrc_visible_window_limit_wr (reg_ddrc_visible_window_limit_wr),
                .reg_ddrc_dis_opt_ntt_by_act    (reg_ddrc_dis_opt_ntt_by_act),
                .reg_ddrc_dis_opt_ntt_by_pre    (reg_ddrc_dis_opt_ntt_by_pre),
                .reg_ddrc_autopre_rmw           (reg_ddrc_autopre_rmw),
                .dh_te_dis_wc                   (reg_ddrc_dis_wc),
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Debug pins. Not currently used in all configs.
                .te_dh_rd_page_hit              (te_dh_rd_page_hit),
                .te_dh_rd_valid                 (te_dh_rd_valid),
                .te_dh_wr_page_hit              (te_dh_wr_page_hit),
                .te_dh_wr_valid                 (te_dh_wr_valid),
                .te_dh_rd_hi                    (te_dh_rd_hi),
//spyglass enable_block W528
                .ih_te_rd_entry_num             (ih_te_rd_entry),
                .ih_te_rd_valid                 (ih_te_rd_valid_no_addrerr),
                .ih_te_wr_entry_num             (ih_yy_wr_entry),
                .ih_te_wr_valid                 (ih_yy_wr_valid_no_addrerr),
                .ih_te_rd_autopre               (ih_te_rd_autopre),
                .ih_te_wr_autopre               (ih_te_wr_autopre),
                .ih_te_rd_latency               (ih_te_rd_latency),
                .te_gs_any_vpr_timed_out        (te_gs_any_vpr_timed_out),
                .te_gs_any_vpr_timed_out_w      (te_gs_any_vpr_timed_out_w),
                .ih_te_wr_latency               (ih_te_wr_latency),
                .te_gs_any_vpw_timed_out        (te_gs_any_vpw_timed_out),
                .te_gs_any_vpw_timed_out_w      (te_gs_any_vpw_timed_out_w),
                .ih_te_rd_hi_pri                (ih_te_rd_hi_pri),
                .ih_te_wr_hi_pri                (ih_te_wr_hi_pri),
                .ih_te_rd_rmw                   (!(ih_yy_rmw_type==`MEMC_RMW_TYPE_NO_RMW)),
                .ih_te_rd_rank_num              (ih_te_rd_rank_num),
                .ih_te_wr_rank_num              (ih_te_wr_rank_num),
                .ih_te_rd_bg_bank_num           (ih_te_rd_bg_bank_num),
                .ih_te_wr_bg_bank_num           (ih_te_wr_bg_bank_num),
                .ih_te_rd_page_num              (ih_te_rd_page_num),
                .ih_te_wr_page_num              (ih_te_wr_page_num),
                .ih_te_rd_block_num             (ih_te_rd_block_num),
                .ih_te_wr_block_num             (ih_te_wr_block_num),

                .ih_te_wr_other_fields          (ih_te_wr_other_fields),
                .ih_te_rd_length                (ih_te_rd_length),
                .ih_te_critical_dword           (ih_te_critical_dword),
                .ih_te_rd_other_fields          ({
                                                  ih_yy_rd_addr_err,
                                                  ih_yy_wr_entry_rmw[WR_CAM_ADDR_WIDTH-1:0], // ???_PT (Entry in WR ECC CAM never becomes write part)
                                                  ih_yy_rmw_type,
                                                  ih_te_rd_tag
                                                  }),

                .te_ih_retry                    (te_ih_retry),
                .te_ih_free_rd_entry_valid      (te_ih_free_rd_entry_valid),
                .te_ih_free_rd_entry            (te_ih_free_rd_entry),

                .wu_te_enable_wr                (wu_te_enable_wr),
                .wu_te_entry_num                (wu_te_entry_num),

                .wu_te_wr_word_valid            (wu_te_wr_word_valid),
                .wu_te_ram_raddr_lsb_first      (wu_te_ram_raddr_lsb_first),
                .wu_te_pw_num_beats_m1          (wu_te_pw_num_beats_m1),
                .wu_te_pw_num_cols_m1           (wu_te_pw_num_cols_m1),

                .te_mr_wr_ram_addr              (te_mr_wr_ram_addr_w),
                .te_wu_entry_num                (te_wu_entry_num),
                .te_yy_wr_combine               (te_yy_wr_combine),
                .te_yy_wr_combine_noecc         (te_yy_wr_combine_noecc),
                .te_yy_wr_combine_wrecc         (te_yy_wr_combine_wrecc),

                .be_te_page_hit                 (be_te_page_hit),
                .be_te_wr_page_hit              (be_te_wr_page_hit),
                .be_wr_page_hit                 (be_wr_page_hit),
                .wu_te_mwr                      (wu_te_mwr),
                .te_os_rd_entry_table           (te_os_rd_entry_table),
                .te_os_wr_entry_table           (te_os_wr_entry_table),
                .te_os_rd_page_table            (te_os_rd_page_table),
                .te_os_wr_page_table            (te_os_wr_page_table),
                .te_os_rd_cmd_autopre_table     (te_os_rd_cmd_autopre_table),
                .te_os_wr_cmd_autopre_table     (te_os_wr_cmd_autopre_table),
                .te_os_rd_pageclose_autopre     (te_os_rd_pageclose_autopre),
                .te_os_wr_pageclose_autopre     (te_os_wr_pageclose_autopre),
                .te_os_rd_length_table          (te_os_rd_length_table),
                .te_os_rd_critical_word_table   (te_os_rd_critical_word_table),
                .te_os_mwr_table                (te_os_mwr_table),
                .te_b3_bit                      (te_b3_bit),
                .te_os_wr_mr_ram_raddr_lsb_first_table (te_os_wr_mr_ram_raddr_lsb_first_table),
                .te_os_wr_mr_pw_num_beats_m1_table     (te_os_wr_mr_pw_num_beats_m1_table),
                .os_te_rdwr_entry               (os_te_rdwr_entry),
//                 .ts_rdwr_cmd_autopre            (ts_rdwr_cmd_autopre),
                .ddrc_co_perf_war_hazard        (ddrc_co_perf_war_hazard_w),
                .ddrc_co_perf_raw_hazard        (ddrc_co_perf_raw_hazard_w),
                .ddrc_co_perf_waw_hazard        (ddrc_co_perf_waw_hazard_w),
                .ddrc_co_perf_ie_blk_hazard     (ddrc_co_perf_ie_blk_hazard_w),
                .ddrc_co_perf_vlimit_reached_rd (ddrc_co_perf_vlimit_reached_rd_w),
                .ddrc_co_perf_vlimit_reached_wr (ddrc_co_perf_vlimit_reached_wr_w),
                .te_be_bsm_num                  (te_be_bsm_num),
                .te_be_page_num                 (te_be_page_num),
                .ts_te_autopre                  (ts_te_autopre),
                .gs_te_bsm_num4pre              (gs_te_bsm_num4pre),
                .gs_te_bsm_num4rdwr             (gs_te_bsm_num4rdwr),
                .gs_te_bsm_num4act              (gs_te_bsm_num4act),
                .gs_te_op_is_rd                 (gs_te_op_is_rd),
                .gs_te_op_is_wr                 (gs_te_op_is_wr),
                .gs_te_op_is_precharge          (gs_te_op_is_precharge_int),
                .gs_te_op_is_activate           (gs_te_op_is_activate),
                .gs_te_wr_mode                  (gs_te_wr_mode),
                .gs_te_wr_possible              (gs_te_wr_possible),
                .gs_te_pri_level                (gs_te_pri_level),
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
                .gs_te_rd_length                (gs_te_rd_length),
                .gs_te_rd_word                  (gs_te_rd_word),
                .gs_te_raddr_lsb_first          (gs_te_raddr_lsb_first),
                .gs_te_pw_num_beats_m1          (gs_te_pw_num_beats_m1),      
`endif
`endif //SNPS_ASSERT
                .te_gs_hi_rd_page_hit_vld       (te_gs_hi_rd_page_hit_vld_unused),
                .te_bs_rd_hi                    (te_bs_rd_hi),
                .te_bs_wrecc_btt                (te_bs_wrecc_btt),
                .te_bs_rd_page_hit              (te_bs_rd_page_hit),
                .te_bs_rd_valid                 (te_bs_rd_valid),
                .te_bs_wr_page_hit              (te_bs_wr_page_hit),
                .te_bs_wr_valid                 (te_bs_wr_valid),
                .te_ts_vpw_valid                (te_ts_vpw_valid),
                .te_ts_vpr_valid                (te_ts_vpr_valid),
                .te_bs_rd_bank_page_hit         (te_bs_rd_bank_page_hit),
                .te_bs_wr_bank_page_hit         (te_bs_wr_bank_page_hit),
                .te_gs_rd_flush                 (te_gs_rd_flush),
                .te_gs_wr_flush                 (te_gs_wr_flush),
                .te_gs_any_rd_pending           (te_gs_any_rd_pending),
                .te_gs_any_wr_pending           (te_gs_any_wr_pending),
                .te_os_hi_bsm_hint              (te_os_hi_bsm_hint),
                .te_os_lo_bsm_hint              (te_os_lo_bsm_hint),
                .te_os_wr_bsm_hint              (te_os_wr_bsm_hint),
                .te_os_wrecc_bsm_hint           (te_os_wrecc_bsm_hint),
                .te_os_rd_ie_tag_table          (te_os_rd_ie_tag_table),
                .te_os_wr_ie_tag_table          (te_os_wr_ie_tag_table),
                .os_te_rdwr_ie_tag              (os_te_rdwr_ie_tag),
                .te_gs_block_wr                 (te_gs_block_wr), // Write is not allowed this cycle

                .te_os_lo_act_bsm_hint          (te_os_lo_act_bsm_hint),
                .te_os_wr_act_bsm_hint          (te_os_wr_act_bsm_hint),
                .te_wu_wr_retry                 (te_wu_wr_retry),
                .te_pi_rd_addr_ecc_row          (te_pi_rd_addr_ecc_row),
                .te_pi_rd_addr_blk              (te_pi_rd_addr_blk),
                .te_pi_rd_other_fields_rd       ({
                                                  te_pi_rd_addr_err,
                                                  te_pi_rd_link_addr,
                                                  te_pi_rd_rmw_type,
                                                  te_pi_rd_tag}),
                .te_pi_wr_addr_blk              (te_pi_wr_addr_blk),
                .te_pi_wr_other_fields_wr       (te_pi_wr_other_fields_wr_unused),
                .te_pi_wr_word_valid            (te_pi_wr_word_valid_w),
//    `ifdef MEMC_DDR4
//                .te_pi_wr_bc_sel                (te_pi_wr_bc_sel),
//    `endif // MEMC_DDR4
//                .te_mr_ram_raddr_lsb_first      (te_mr_ram_raddr_lsb_first),
//                .te_mr_pw_num_beats_m1          (te_mr_pw_num_beats_m1),

                .ts_act_page                    (ts_act_page)

               ,.te_gs_rank_rd_pending          (te_gs_rank_rd_pending)
               ,.te_gs_rank_wr_pending          (te_gs_rank_wr_pending)
               ,.te_gs_bank_wr_pending          (te_gs_bank_wr_pending)
               ,.te_gs_bank_rd_pending          (te_gs_bank_rd_pending)
               ,.reg_ddrc_dis_opt_wrecc_collision_flush (reg_ddrc_dis_opt_wrecc_collision_flush)

`ifdef SNPS_ASSERT_ON
    `ifndef SYNTHESIS
               ,.reg_ddrc_ecc_type              (reg_ddrc_ecc_type)       // used in te_assertions
               ,.reg_ddrc_ecc_mode              (reg_ddrc_ecc_mode)
               ,.reg_ddrc_burst_rdwr            (reg_ddrc_burst_rdwr)
               ,.reg_ddrc_addrmap_col_b3        (reg_ddrc_addrmap_col_b3 )
               ,.reg_ddrc_addrmap_col_b4        (reg_ddrc_addrmap_col_b4 )
               ,.reg_ddrc_addrmap_col_b5        (reg_ddrc_addrmap_col_b5 )
               ,.reg_ddrc_addrmap_col_b6        (reg_ddrc_addrmap_col_b6 )
               ,.reg_ddrc_addrmap_col_b7        (reg_ddrc_addrmap_col_b7 )
               ,.reg_ddrc_addrmap_col_b8        (reg_ddrc_addrmap_col_b8 )
               ,.reg_ddrc_addrmap_col_b9        (reg_ddrc_addrmap_col_b9 )
               ,.reg_ddrc_addrmap_col_b10       (reg_ddrc_addrmap_col_b10)
                ,.wu_ih_flow_cntrl_req          (wu_ih_flow_cntrl_req) // used in assertions in te_wr_cam
    `endif // SYNTHESIS
`endif // SNPS_ASSERT_ON
                ,.ih_te_mwr                    (ih_te_mwr)
                ,.ih_te_wr_word_valid          (ih_te_wr_word_valid)

                ,.ih_te_wr_ram_raddr_lsb_first (ih_te_wr_ram_raddr_lsb_first)
                ,.ih_te_wr_pw_num_beats_m1     (ih_te_wr_pw_num_beats_m1)
                ,.ih_te_wr_pw_num_cols_m1      (ih_te_wr_pw_num_cols_m1)
                ,.ih_te_ie_bt                  (ih_te_ie_bt)
                ,.ih_te_ie_rd_type             (ih_te_ie_rd_type)
                ,.ih_te_ie_wr_type             (ih_te_ie_wr_type)
                ,.ih_te_ie_blk_burst_num       (ih_te_ie_blk_burst_num)  //only for the Data command
                ,.te_mr_ie_bt                  (te_mr_ie_bt)
                ,.te_mr_ie_wr_type             (te_mr_ie_wr_type)
                ,.te_mr_ie_blk_burst_num       (te_mr_ie_blk_burst_num)

                ,.te_pi_ie_bt                  (te_pi_ie_bt)
                ,.te_pi_ie_rd_type             (te_pi_ie_rd_type)
                ,.te_pi_ie_blk_burst_num       (te_pi_ie_blk_burst_num)
                ,.ih_te_ie_block_num           (ih_te_ie_block_num)
                ,.ih_te_ie_re_vct              (ih_te_ie_re_vct)
                ,.ih_te_ie_btt_vct             (ih_te_ie_btt_vct)
                ,.ih_te_rd_eccap               (ih_te_rd_eccap)
                ,.ih_te_wr_eccap               (ih_te_wr_eccap)
                ,.te_pi_eccap                  (te_pi_eccap)
                ,.te_mr_eccap                  (te_mr_eccap)

                ,.te_gs_rank_rd_valid          (te_gs_rank_rd_valid)
                ,.te_gs_rank_wr_valid          (te_gs_rank_wr_valid)
                ,.ts_te_sel_act_wr             (ts_te_sel_act_wr) //tell TE the activate command is for write or read.
                ,.te_rws_wr_col_bank           (te_rws_wr_col_bank) // entry of colliding bank (1bit for 1bank)
                ,.te_rws_rd_col_bank           (te_rws_rd_col_bank) // entry of colliding bank (1bit for 1bank)
                ,.te_num_wr_pghit_entries      (te_num_wr_pghit_entries)
                ,.te_num_rd_pghit_entries      (te_num_rd_pghit_entries)
                ,.te_wr_entry_avail            (te_wr_entry_avail)           // Number of non-valid entries (WRCAM only, not include WRECC CAM)
             ,.te_wrecc_entry_avail         (te_wrecc_entry_avail)
             ,.te_wrecc_entry_loaded        (te_wrecc_entry_loaded)
             ,.ts_te_force_btt              (ts_te_force_btt)
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
                ,.te_wr_entry_valid            (te_ts_wr_entry_valid)
                ,.te_rd_entry_valid            (te_ts_rd_entry_valid)
                ,.te_wr_page_hit_entries       (te_ts_wr_page_hit_entries)
                ,.te_rd_page_hit               (te_ts_rd_page_hit_entries)
                ,.reg_ddrc_data_bus_width      (reg_ddrc_data_bus_width)
`endif //SNPS_ASSERT_ON
`endif // SYNTHESIS
                ,.reg_ddrc_lpddr4              (reg_ddrc_lpddr4)
                ,.ih_gs_rdhigh_empty           (ih_gs_rdhigh_empty)
                ,.ih_gs_rdlow_empty            (ih_gs_rdlow_empty)
                ,.te_gs_rank_rd_prefer         (te_gs_rank_rd_prefer) 
                ,.te_gs_rank_wr_prefer         (te_gs_rank_wr_prefer) 
                ,.te_rd_bank_pghit_vld_prefer  (te_rd_bank_pghit_vld_prefer)
                ,.te_wr_bank_pghit_vld_prefer  (te_wr_bank_pghit_vld_prefer)
   `ifdef SNPS_ASSERT_ON
   `endif
`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
               ,.reg_ddrc_opt_vprw_sch        (reg_ddrc_opt_vprw_sch    )
`endif //SNPS_ASSERT_ON
`endif //SYNTHESIS
                );


//------------------------------------------------------------------------------
// BE (Bypass Evaluation) block : contains page table
//------------------------------------------------------------------------------
bypass

              #(.RANKBANK_BITS                  (RANKBANK_BITS),
                .PAGE_BITS                      (PAGE_BITS),
                .BANK_BITS                      (BANK_BITS),
                .LRANK_BITS                     (LRANK_BITS) )
        bypass (
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .co_be_clk                      (core_ddrc_core_clk),
// JIRA___ID: Temporary Fix Bug 4430
// ih_yy_rank_num_rd/ih_yy_bg_bank_num_rd/ih_be_page_num are not correct for generated ECC commands.
// So connect ih_te_rd_rank_num, ih_te_rd_bg_bank_num, ih_te_rd_page_num instead.
// This temporary fix is correct in terms of functionality, but should be fixed properly for Synthesis timing.
                .ih_be_bsm_num_rd               ({
                                                  ih_te_rd_rank_num,
                                                  ih_te_rd_bg_bank_num}),
                .ih_be_bsm_num_wr               ({
                                                  ih_yy_rank_num_wr,
                                                  ih_yy_bg_bank_num_wr}),
                .bm_be_rd_bsm_alloc             (1'b1),
                .bm_be_wr_bsm_alloc             (1'b1),
                .be_os_page_table               (be_os_page_table),
                .te_be_bsm_num                  (te_be_bsm_num),
// JIRA___ID: Temporary Fix Bug 4430
// ih_yy_rank_num_rd/ih_yy_bg_bank_num_rd/ih_be_page_num are not correct for generated ECC commands.
// So connect ih_te_rd_rank_num, ih_te_rd_bg_bank_num, ih_te_rd_page_num instead.
// This temporary fix is correct in terms of functionality, but should be fixed properly for Synthesis timing.
                .ih_be_page_num                 (ih_te_rd_page_num),

                .ih_wr_page_num                 (ih_te_wr_page_num),
                .te_be_page_addr                (ts_act_page),
                .te_be_page_num                 (te_be_page_num),
                .be_te_page_hit                 (be_te_page_hit),
                .be_te_wr_page_hit              (be_te_wr_page_hit),
                .be_wr_page_hit                 (be_wr_page_hit),
                .gs_be_rdwr_bsm_num             (gs_be_rdwr_bsm_num),
                .gs_be_act_bsm_num              (gs_be_act_bsm_num),
                .gs_be_pre_bsm_num              (gs_be_pre_bsm_num),
                .gs_be_op_is_activate           (gs_be_op_is_activate),
                .gs_be_op_is_precharge          (gs_be_op_is_precharge_int),
                .gs_be_op_is_rdwr               (gs_be_op_is_rdwr),
                .ts_te_autopre                  (ts_te_autopre));








  assign gs_te_op_is_precharge_int = gs_te_op_is_precharge;
  assign gs_be_op_is_precharge_int = gs_be_op_is_precharge;






  assign te_pi_wr_word_valid = te_pi_wr_word_valid_w;
  assign te_mr_wr_ram_addr   = te_mr_wr_ram_addr_w;


endmodule : dwc_ddrctl_ddrc_cpf

