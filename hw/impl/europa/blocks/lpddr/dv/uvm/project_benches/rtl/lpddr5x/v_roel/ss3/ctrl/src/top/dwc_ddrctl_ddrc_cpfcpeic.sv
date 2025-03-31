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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cpfcpeic.sv#5 $
// -------------------------------------------------------------------------
// Description:
//     CPF to CPE select

`include "DWC_ddrctl_all_defs.svh"
`include "top/dwc_ddrctl_ddrc_cpfcpe_if.svh"


module dwc_ddrctl_ddrc_cpfcpeic 
#(
   // parameter from ddrc_cpfcpeif
    parameter       LRANK_BITS                  = `UMCTL2_LRANK_BITS
   ,parameter       BG_BANK_BITS                = `MEMC_BG_BANK_BITS
   ,parameter       RANKBANK_BITS               = LRANK_BITS + BG_BANK_BITS
   ,parameter       NUM_LRANKS                  = `UMCTL2_NUM_LRANKS_TOTAL         // max supported logical ranks
   ,parameter       NUM_TOTAL_BANKS             = `MEMC_NUM_TOTAL_BANKS            // max supported banks
   ,parameter       RANK_BITS                   = `MEMC_RANK_BITS
   ,parameter       LRANK_BITS_DDRC             = `DDRCTL_DDRC_LRANK_BITS
   ,parameter       NUM_LRANKS_DDRC             = `DDRCTL_DDRC_NUM_LRANKS_TOTAL         // max supported logical ranks (chip selects * chip ID(for DDR4 3DS))
   ,parameter       RANKBANK_BITS_DDRC          = LRANK_BITS_DDRC + BG_BANK_BITS
   ,parameter       NUM_TOTAL_BANKS_DDRC        = `DDRCTL_DDRC_NUM_TOTAL_BANKS
   ,parameter       BSM_BITS                    = `UMCTL2_BSM_BITS
   ,parameter       CORE_TAG_WIDTH              = `MEMC_TAGBITS                    // width of tag
   ,parameter       RMW_TYPE_BITS               = 2                                // 2-bit RMW type
   ,parameter       WR_CAM_ADDR_WIDTH_IE        = 0
   ,parameter       BLK_BITS                    = `MEMC_BLK_BITS                   // 2 column bits are critical word
   ,parameter       WORD_BITS                   = `MEMC_WORD_BITS                  // address a word within a burst
   ,parameter       CMD_LEN_BITS                = 1                                // command length bit width
   ,parameter       NUM_TOTAL_BSMS              = `UMCTL2_NUM_BSM                 // max supported BSMs
   ,parameter       PAGE_BITS                   = `MEMC_PAGE_BITS
   ,parameter       RD_CAM_ADDR_WIDTH           = `MEMC_RDCMD_ENTRY_BITS           // bits to address into read CAM
   ,parameter       AUTOPRE_BITS                = (`MEMC_INLINE_ECC_EN==1)? 2 : 1
   ,parameter       MWR_BITS                    = `DDRCTL_MWR_BITS
   ,parameter       PARTIAL_WR_BITS             = `UMCTL2_PARTIAL_WR_BITS
   ,parameter       PARTIAL_WR_BITS_LOG2        = `log2(PARTIAL_WR_BITS)
   ,parameter       PW_NUM_DB                   = PARTIAL_WR_BITS                  // added for PW_WORD_CNT_WD_MAX
   ,parameter       PW_FACTOR_HBW               = 2*`MEMC_FREQ_RATIO               // added for PW_WORD_CNT_WD_MAX
   ,parameter       PW_WORD_VALID_WD_HBW        = PW_NUM_DB*PW_FACTOR_HBW          // added for PW_WORD_CNT_WD_MAX
   ,parameter       PW_WORD_VALID_WD_MAX        = PW_WORD_VALID_WD_HBW             // added for PW_WORD_CNT_WD_MAX
   ,parameter       PW_WORD_CNT_WD_MAX          = $clog2(PW_WORD_VALID_WD_MAX)
   ,parameter       IE_WR_TYPE_BITS             = `IE_WR_TYPE_BITS
   ,parameter       IE_RD_TYPE_BITS             = `IE_RD_TYPE_BITS                 // added for IE_TAG_BITS
   ,parameter       IE_BURST_NUM_BITS           = `MEMC_BURST_LENGTH==16 ? 4 : 3   // added for IE_TAG_BITS
   ,parameter       NO_OF_BT                    = `MEMC_NO_OF_BLK_TOKEN            // added for IE_TAG_BITS
   ,parameter       BT_BITS                     = `log2(NO_OF_BT)                   // added for IE_TAG_BITS
   ,parameter       ECCAP_BITS                  = `MEMC_ECCAP_EN                   // added for IE_TAG_BITS
   ,parameter       IE_TAG_BITS                 = (`MEMC_INLINE_ECC_EN==1) ? IE_RD_TYPE_BITS + IE_BURST_NUM_BITS + BT_BITS + ECCAP_BITS : 0
   ,parameter       WR_CAM_ADDR_WIDTH           = `MEMC_WRCMD_ENTRY_BITS           // bits to address into write CAM
   ,parameter       MAX_CAM_ADDR_WIDTH          = 0
   ,parameter       HIF_KEYID_WIDTH               = `DDRCTL_HIF_KEYID_WIDTH

   // parameter from ddrc_cpfcpeif

)
(
   // IO list
   //IF FROM DDRC_CPE
//spyglass disable_block W241
//SMD: Outputs unused_w is never set 
//SJ: used to avoid empty modport
    dwc_ddrctl_ddrc_cpfcpe_if.o_bm_mp                           o_bm_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.o_ih_mp                           o_ih_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.o_be_mp                           o_be_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.o_te_mp                           o_te_mp_ddrc
//spyglass enable_block W241

//spyglass disable_block W240
//SMD: Inputs unused_w declared but not read
//SJ: used to avoid empty modport
   ,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_bm_mp                        i_gs_bm_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.i_bs_bm_mp                        i_bs_bm_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.i_bs_te_mp                        i_bs_te_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_ih_mp                        i_gs_ih_mp_ddrc
//spyglass enable_block W240


   ,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_be_mp                        i_gs_be_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.i_bs_be_mp                        i_bs_be_mp_ddrc

   ,dwc_ddrctl_ddrc_cpfcpe_if.i_gs_te_mp                        i_gs_te_mp_ddrc
   ,dwc_ddrctl_ddrc_cpfcpe_if.i_os_te_mp                        i_os_te_mp_ddrc




   //MUX TO DDRC_CPF


   ,input  logic                                                ih_gs_rdlow_empty
   ,input  logic                                                ih_gs_rdhigh_empty
   ,input  logic                                                ih_gs_any_vpr_timed_out
   ,input  logic                                                ih_gs_any_vpw_timed_out

   ,input  logic                                                ih_busy
   ,input  logic                                                ih_yy_xact_valid
   ,output logic                                                gsfsm_sr_co_if_stall

   ,input  logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                 be_os_page_table
   ,output logic                                                gs_be_op_is_activate
   ,output logic                                                gs_be_op_is_precharge
   ,output logic                                                gs_be_op_is_rdwr
   ,output logic [BSM_BITS-1:0]                                 gs_be_rdwr_bsm_num
   ,output logic [BSM_BITS-1:0]                                 gs_be_act_bsm_num
   ,output logic [BSM_BITS-1:0]                                 gs_be_pre_bsm_num

   ,output logic [PAGE_BITS-1:0]                                ts_act_page

   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_page_hit
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_valid
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wr_page_hit
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wr_valid
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_bank_page_hit
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wr_bank_page_hit
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_rd_hi
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_bs_wrecc_btt
   ,input  logic [NUM_TOTAL_BSMS*RD_CAM_ADDR_WIDTH-1:0]         te_os_rd_entry_table
   ,input  logic [NUM_TOTAL_BSMS*WR_CAM_ADDR_WIDTH_IE-1:0]      te_os_wr_entry_table
   ,input  logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                 te_os_rd_page_table
   ,input  logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                 te_os_wr_page_table
   ,input  logic [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]              te_os_rd_cmd_autopre_table
   ,input  logic [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]              te_os_wr_cmd_autopre_table
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_os_rd_pageclose_autopre
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_os_wr_pageclose_autopre
   ,input  logic [NUM_TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0]      te_os_wr_mr_ram_raddr_lsb_first_table
   ,input  logic [NUM_TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]        te_os_wr_mr_pw_num_beats_m1_table
   ,input  logic [NUM_TOTAL_BSMS*CMD_LEN_BITS-1:0]              te_os_rd_length_table
   ,input  logic [NUM_TOTAL_BSMS*WORD_BITS-1:0]                 te_os_rd_critical_word_table
   ,input  logic [NUM_TOTAL_BSMS*MWR_BITS-1:0]                  te_os_mwr_table
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_b3_bit
   ,input  logic [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0]               te_os_rd_ie_tag_table
   ,input  logic [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0]               te_os_wr_ie_tag_table
   ,input  logic [BSM_BITS-1:0]                                 te_os_hi_bsm_hint
   ,input  logic [BSM_BITS-1:0]                                 te_os_lo_bsm_hint
   ,input  logic [BSM_BITS-1:0]                                 te_os_wr_bsm_hint
   ,input  logic [BSM_BITS-1:0]                                 te_os_wrecc_bsm_hint
   ,input  logic [BSM_BITS-1:0]                                 te_os_lo_act_bsm_hint
   ,input  logic [BSM_BITS-1:0]                                 te_os_wr_act_bsm_hint
   ,input  logic                                                te_gs_rd_flush
   ,input  logic                                                te_gs_wr_flush
   ,input  logic                                                te_gs_block_wr
   ,input  logic                                                te_gs_any_rd_pending
   ,input  logic                                                te_gs_any_wr_pending
   ,input  logic                                                te_gs_any_vpr_timed_out
   ,input  logic                                                te_gs_any_vpr_timed_out_w
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_ts_vpr_valid
   ,input  logic                                                te_gs_any_vpw_timed_out
   ,input  logic                                                te_gs_any_vpw_timed_out_w
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_ts_vpw_valid
   ,input  logic [NUM_LRANKS-1:0]                               te_gs_rank_wr_pending
   ,input  logic [NUM_LRANKS-1:0]                               te_gs_rank_rd_pending
   ,input  logic [NUM_TOTAL_BANKS-1:0]                          te_gs_bank_wr_pending
   ,input  logic [NUM_TOTAL_BANKS-1:0]                          te_gs_bank_rd_pending
   ,input  logic [NUM_LRANKS-1:0]                               te_gs_rank_rd_valid
   ,input  logic [NUM_LRANKS-1:0]                               te_gs_rank_wr_valid
   ,input  logic [RANK_BITS-1:0]                                te_gs_rank_rd_prefer
   ,input  logic [RANK_BITS-1:0]                                te_gs_rank_wr_prefer
   ,input  logic [PAGE_BITS-1:0]                                te_pi_rd_addr_ecc_row
   ,input  logic [BLK_BITS-1:0]                                 te_pi_rd_addr_blk
   ,input  logic [CORE_TAG_WIDTH-1:0]                           te_pi_rd_tag
   ,input  logic [RMW_TYPE_BITS-1:0]                            te_pi_rd_rmw_type
   ,input  logic [WR_CAM_ADDR_WIDTH-1:0]                        te_pi_rd_link_addr
   ,input  logic                                                te_pi_rd_addr_err
   ,input  logic [BLK_BITS-1:0]                                 te_pi_wr_addr_blk
   ,input  logic [WORD_BITS-1:0]                                te_pi_wr_word
   ,input  logic [BT_BITS-1:0]                                  te_pi_ie_bt
   ,input  logic [IE_RD_TYPE_BITS-1:0]                          te_pi_ie_rd_type
   ,input  logic [IE_BURST_NUM_BITS-1:0]                        te_pi_ie_blk_burst_num
   ,input  logic                                                te_pi_eccap
   ,output logic [NUM_TOTAL_BSMS-1:0]                           ts_te_sel_act_wr
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_rws_wr_col_bank         
   ,input  logic [NUM_TOTAL_BSMS-1:0]                           te_rws_rd_col_bank         
   ,input  logic [WR_CAM_ADDR_WIDTH_IE:0]                       te_num_wr_pghit_entries    
   ,input  logic [RD_CAM_ADDR_WIDTH:0]                          te_num_rd_pghit_entries    
   ,input  logic [WR_CAM_ADDR_WIDTH:0]                          te_wr_entry_avail          
   ,input  logic [WR_CAM_ADDR_WIDTH:0]                          te_wrecc_entry_avail      // Number of non-valid entries (WRECCCAM only, not include WR CAM), valid status
   ,input  logic [WR_CAM_ADDR_WIDTH:0]                          te_wrecc_entry_loaded     // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   ,output logic                                                ts_te_force_btt

   ,input  logic                                                te_rd_bank_pghit_vld_prefer
   ,input  logic                                                te_wr_bank_pghit_vld_prefer

   ,output logic                                                gs_te_op_is_rd
   ,output logic                                                gs_te_op_is_wr
   ,output logic                                                gs_te_op_is_activate
   ,output logic                                                gs_te_op_is_precharge
   ,output logic [BSM_BITS-1:0]                                 gs_te_bsm_num4pre
   ,output logic [BSM_BITS-1:0]                                 gs_te_bsm_num4rdwr
   ,output logic [BSM_BITS-1:0]                                 gs_te_bsm_num4act

`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
    ,output   logic [CMD_LEN_BITS-1:0]                          gs_te_rd_length
    ,output   logic [WORD_BITS-1:0]                             gs_te_rd_word
      ,output   logic [PARTIAL_WR_BITS_LOG2-1:0]                gs_te_raddr_lsb_first
        ,output   logic [PW_WORD_CNT_WD_MAX-1:0]                gs_te_pw_num_beats_m1
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON


   ,output logic                                                gs_te_wr_mode
   ,output logic [NUM_TOTAL_BSMS-1:0]                           gs_te_wr_possible
   ,output logic                                                gs_te_pri_level

   ,output logic [MAX_CAM_ADDR_WIDTH-1:0]                       os_te_rdwr_entry
   ,output logic [IE_TAG_BITS-1:0]                              os_te_rdwr_ie_tag


   ,output  logic                                               ts_te_autopre
);


////////////////////FROM CPF to DDRC_CPE//////////////////////////

assign o_ih_mp_ddrc.ih_gs_rdlow_empty           = ih_gs_rdlow_empty;
assign o_ih_mp_ddrc.ih_gs_rdhigh_empty          = ih_gs_rdhigh_empty;
assign o_ih_mp_ddrc.ih_gs_any_vpr_timed_out     = ih_gs_any_vpr_timed_out; 
assign o_ih_mp_ddrc.ih_gs_any_vpw_timed_out     = ih_gs_any_vpw_timed_out;
assign o_ih_mp_ddrc.ih_busy                     = ih_busy;
assign o_ih_mp_ddrc.ih_yy_xact_valid            = ih_yy_xact_valid;

assign o_be_mp_ddrc.be_os_page_table            = be_os_page_table; 

assign o_te_mp_ddrc.te_bs_rd_page_hit           = te_bs_rd_page_hit;
assign o_te_mp_ddrc.te_bs_wr_page_hit           = te_bs_wr_page_hit;
assign o_te_mp_ddrc.te_bs_rd_valid              = te_bs_rd_valid;
assign o_te_mp_ddrc.te_bs_wr_valid              = te_bs_wr_valid;
assign o_te_mp_ddrc.te_bs_rd_bank_page_hit      = te_bs_rd_bank_page_hit;
assign o_te_mp_ddrc.te_bs_wr_bank_page_hit      = te_bs_wr_bank_page_hit;
assign o_te_mp_ddrc.te_bs_rd_hi                 = te_bs_rd_hi;
assign o_te_mp_ddrc.te_bs_wrecc_btt             = te_bs_wrecc_btt;
assign o_te_mp_ddrc.te_os_rd_entry_table        = te_os_rd_entry_table;
assign o_te_mp_ddrc.te_os_wr_entry_table        = te_os_wr_entry_table;
assign o_te_mp_ddrc.te_os_rd_page_table         = te_os_rd_page_table;
assign o_te_mp_ddrc.te_os_wr_page_table         = te_os_wr_page_table;
assign o_te_mp_ddrc.te_os_rd_cmd_autopre_table  = te_os_rd_cmd_autopre_table;
assign o_te_mp_ddrc.te_os_wr_cmd_autopre_table  = te_os_wr_cmd_autopre_table;
assign o_te_mp_ddrc.te_os_wr_mr_ram_raddr_lsb_first_table = te_os_wr_mr_ram_raddr_lsb_first_table;
assign o_te_mp_ddrc.te_os_wr_mr_pw_num_beats_m1_table     = te_os_wr_mr_pw_num_beats_m1_table;
assign o_te_mp_ddrc.te_os_rd_length_table        = te_os_rd_length_table;
assign o_te_mp_ddrc.te_os_rd_critical_word_table = te_os_rd_critical_word_table;
assign o_te_mp_ddrc.te_os_rd_pageclose_autopre  = te_os_rd_pageclose_autopre;
assign o_te_mp_ddrc.te_os_wr_pageclose_autopre  = te_os_wr_pageclose_autopre;
assign o_te_mp_ddrc.te_os_mwr_table             = te_os_mwr_table;
assign o_te_mp_ddrc.te_b3_bit                   = te_b3_bit;
assign o_te_mp_ddrc.te_os_rd_ie_tag_table       = te_os_rd_ie_tag_table;
assign o_te_mp_ddrc.te_os_wr_ie_tag_table       = te_os_wr_ie_tag_table;
assign o_te_mp_ddrc.te_os_hi_bsm_hint           = te_os_hi_bsm_hint;
assign o_te_mp_ddrc.te_os_lo_bsm_hint           = te_os_lo_bsm_hint;
assign o_te_mp_ddrc.te_os_wr_bsm_hint           = te_os_wr_bsm_hint;
assign o_te_mp_ddrc.te_os_wrecc_bsm_hint        = te_os_wrecc_bsm_hint;
assign o_te_mp_ddrc.te_os_lo_act_bsm_hint       = te_os_lo_act_bsm_hint;
assign o_te_mp_ddrc.te_os_wr_act_bsm_hint       = te_os_wr_act_bsm_hint;
assign o_te_mp_ddrc.te_gs_rd_flush              = te_gs_rd_flush;
assign o_te_mp_ddrc.te_gs_wr_flush              = te_gs_wr_flush;
assign o_te_mp_ddrc.te_gs_block_wr              = te_gs_block_wr;
assign o_te_mp_ddrc.te_gs_any_rd_pending        = te_gs_any_rd_pending;
assign o_te_mp_ddrc.te_gs_any_wr_pending        = te_gs_any_wr_pending;
assign o_te_mp_ddrc.te_gs_any_vpr_timed_out     = te_gs_any_vpr_timed_out;
assign o_te_mp_ddrc.te_gs_any_vpr_timed_out_w   = te_gs_any_vpr_timed_out_w;
assign o_te_mp_ddrc.te_ts_vpr_valid             = te_ts_vpr_valid;
assign o_te_mp_ddrc.te_gs_any_vpw_timed_out     = te_gs_any_vpw_timed_out;
assign o_te_mp_ddrc.te_gs_any_vpw_timed_out_w   = te_gs_any_vpw_timed_out_w;
assign o_te_mp_ddrc.te_ts_vpw_valid             = te_ts_vpw_valid;
assign o_te_mp_ddrc.te_gs_rank_wr_pending       = te_gs_rank_wr_pending[NUM_LRANKS_DDRC-1:0];
assign o_te_mp_ddrc.te_gs_rank_rd_pending       = te_gs_rank_rd_pending[NUM_LRANKS_DDRC-1:0];
assign o_te_mp_ddrc.te_gs_bank_wr_pending       = te_gs_bank_wr_pending[NUM_TOTAL_BANKS_DDRC-1:0];
assign o_te_mp_ddrc.te_gs_bank_rd_pending       = te_gs_bank_rd_pending[NUM_TOTAL_BANKS_DDRC-1:0];
assign o_te_mp_ddrc.te_gs_rank_rd_valid         = te_gs_rank_rd_valid[NUM_LRANKS_DDRC-1:0];
assign o_te_mp_ddrc.te_gs_rank_wr_valid         = te_gs_rank_wr_valid[NUM_LRANKS_DDRC-1:0];
assign o_te_mp_ddrc.te_gs_rank_rd_prefer        = te_gs_rank_rd_prefer;
assign o_te_mp_ddrc.te_gs_rank_wr_prefer        = te_gs_rank_wr_prefer;
assign o_te_mp_ddrc.te_pi_rd_addr_ecc_row       = te_pi_rd_addr_ecc_row;
assign o_te_mp_ddrc.te_pi_rd_addr_blk           = te_pi_rd_addr_blk;
assign o_te_mp_ddrc.te_pi_rd_tag                = te_pi_rd_tag;
assign o_te_mp_ddrc.te_pi_rd_rmw_type           = te_pi_rd_rmw_type;
assign o_te_mp_ddrc.te_pi_rd_link_addr          = te_pi_rd_link_addr;
assign o_te_mp_ddrc.te_pi_rd_addr_err           = te_pi_rd_addr_err;
assign o_te_mp_ddrc.te_pi_wr_addr_blk           = te_pi_wr_addr_blk;
assign o_te_mp_ddrc.te_pi_wr_word               = te_pi_wr_word;
assign o_te_mp_ddrc.te_pi_ie_bt                 = te_pi_ie_bt;
assign o_te_mp_ddrc.te_pi_ie_rd_type            = te_pi_ie_rd_type;
assign o_te_mp_ddrc.te_pi_ie_blk_burst_num      = te_pi_ie_blk_burst_num;
assign o_te_mp_ddrc.te_pi_eccap                 = te_pi_eccap;
assign o_te_mp_ddrc.te_rws_wr_col_bank          = te_rws_wr_col_bank;         
assign o_te_mp_ddrc.te_rws_rd_col_bank          = te_rws_rd_col_bank;         
assign o_te_mp_ddrc.te_num_wr_pghit_entries     = te_num_wr_pghit_entries;    
assign o_te_mp_ddrc.te_num_rd_pghit_entries     = te_num_rd_pghit_entries;    
assign o_te_mp_ddrc.te_wr_entry_avail           = te_wr_entry_avail;          
assign o_te_mp_ddrc.te_wrecc_entry_avail        = te_wrecc_entry_avail;          
assign o_te_mp_ddrc.te_wrecc_entry_loaded       = te_wrecc_entry_loaded;          
assign o_te_mp_ddrc.te_rd_bank_pghit_vld_prefer = te_rd_bank_pghit_vld_prefer;
assign o_te_mp_ddrc.te_wr_bank_pghit_vld_prefer = te_wr_bank_pghit_vld_prefer;

////////////////////FROM CPF to PAS_CPE//////////////////////////


////////////////////FROM DDRC_CPE/PAS_CPE to CPF//////////////////////////


always_comb begin
      gsfsm_sr_co_if_stall       = i_gs_ih_mp_ddrc.gsfsm_sr_co_if_stall;
      gs_be_op_is_activate       = i_gs_be_mp_ddrc.gs_be_op_is_activate;
      gs_be_op_is_precharge      = i_gs_be_mp_ddrc.gs_be_op_is_precharge;
      gs_be_op_is_rdwr           = i_gs_be_mp_ddrc.gs_be_op_is_rdwr;
      gs_be_rdwr_bsm_num         = i_gs_be_mp_ddrc.gs_be_rdwr_bsm_num;
      gs_be_act_bsm_num          = i_gs_be_mp_ddrc.gs_be_act_bsm_num;
      gs_be_pre_bsm_num          = i_gs_be_mp_ddrc.gs_be_pre_bsm_num;
      ts_act_page                = i_bs_be_mp_ddrc.ts_act_page;
      ts_te_sel_act_wr           = i_bs_te_mp_ddrc.ts_te_sel_act_wr;
      ts_te_force_btt            = i_bs_te_mp_ddrc.te_force_btt;          
      gs_te_op_is_rd             = i_gs_te_mp_ddrc.gs_te_op_is_rd;
      gs_te_op_is_wr             = i_gs_te_mp_ddrc.gs_te_op_is_wr;
      gs_te_op_is_activate       = i_gs_te_mp_ddrc.gs_te_op_is_activate;
      gs_te_op_is_precharge      = i_gs_te_mp_ddrc.gs_te_op_is_precharge;
      gs_te_bsm_num4pre          = i_gs_te_mp_ddrc.gs_te_bsm_num4pre;
      gs_te_bsm_num4rdwr         = i_gs_te_mp_ddrc.gs_te_bsm_num4rdwr;
      gs_te_bsm_num4act          = i_gs_te_mp_ddrc.gs_te_bsm_num4act;
      gs_te_wr_mode              = i_gs_te_mp_ddrc.gs_te_wr_mode;
      gs_te_wr_possible          = {NUM_TOTAL_BSMS{i_gs_te_mp_ddrc.gs_te_wr_possible}};
      gs_te_pri_level            = i_gs_te_mp_ddrc.gs_te_pri_level;
      os_te_rdwr_entry           = i_os_te_mp_ddrc.os_te_rdwr_entry;
      os_te_rdwr_ie_tag          = i_os_te_mp_ddrc.os_te_rdwr_ie_tag;
   `ifdef SNPS_ASSERT_ON
      `ifndef SYNTHESIS
      gs_te_rd_length            = i_gs_te_mp_ddrc.gs_te_rd_length;
      gs_te_rd_word              = i_gs_te_mp_ddrc.gs_te_rd_word;
      gs_te_raddr_lsb_first      = i_gs_te_mp_ddrc.gs_te_raddr_lsb_first;
      gs_te_pw_num_beats_m1      = i_gs_te_mp_ddrc.gs_te_pw_num_beats_m1;
      `endif //SYNTHESIS
   `endif //SNPS_ASSERT_ON
      ts_te_autopre              = i_os_te_mp_ddrc.os_te_autopre;
end

endmodule
