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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_cpfcpe_if.svh#5 $
// -------------------------------------------------------------------------
// Description:
//     SV interface between CPF and CPE

`ifndef __GUARD__DWC_DDRCTL_DDRC_CPFCPE_IF__SVH__
`define __GUARD__DWC_DDRCTL_DDRC_CPFCPE_IF__SVH__

`include "DWC_ddrctl_all_defs.svh"

interface dwc_ddrctl_ddrc_cpfcpe_if #(
   parameter       RANK_BITS                   = `MEMC_RANK_BITS,
   parameter       NUM_LRANKS                  = `DDRCTL_DDRC_NUM_LRANKS_TOTAL,    // max supported logical ranks (chip selects * chip ID(for DDR4 3DS))
   parameter       LRANK_BITS                  = `DDRCTL_DDRC_LRANK_BITS,
   parameter       BG_BANK_BITS                = `MEMC_BG_BANK_BITS,
   parameter       RANKBANK_BITS               = LRANK_BITS + BG_BANK_BITS,
   parameter       NUM_TOTAL_BANKS             = `DDRCTL_DDRC_NUM_TOTAL_BANKS,     // max supported banks
   parameter       NUM_TOTAL_BSMS              = `UMCTL2_NUM_BSM,                  // max supported BSMs
   parameter       RD_CAM_ADDR_WIDTH           = `MEMC_RDCMD_ENTRY_BITS,           // bits to address into read CAM
   parameter       WR_CAM_ADDR_WIDTH_IE        = 0,
   parameter       PAGE_BITS                   = `MEMC_PAGE_BITS,
   parameter       AUTOPRE_BITS                = (`MEMC_INLINE_ECC_EN==1)? 2 : 1,
   parameter       MWR_BITS                    = `DDRCTL_MWR_BITS,
   parameter       PARTIAL_WR_BITS             = `UMCTL2_PARTIAL_WR_BITS,          // added for PW_WORD_CNT_WD_MAX
   parameter       PARTIAL_WR_BITS_LOG2        = $clog2(PARTIAL_WR_BITS),
   parameter       PW_NUM_DB                   = PARTIAL_WR_BITS,                  // added for PW_WORD_CNT_WD_MAX
   parameter       PW_FACTOR_HBW               = 2*`MEMC_FREQ_RATIO,               // added for PW_WORD_CNT_WD_MAX
   parameter       PW_WORD_VALID_WD_HBW        = PW_NUM_DB*PW_FACTOR_HBW,          // added for PW_WORD_CNT_WD_MAX
   parameter       PW_WORD_VALID_WD_MAX        = PW_WORD_VALID_WD_HBW,             // added for PW_WORD_CNT_WD_MAX
   parameter       PW_WORD_CNT_WD_MAX          = $clog2(PW_WORD_VALID_WD_MAX),
   parameter       IE_RD_TYPE_BITS             = `IE_RD_TYPE_BITS,                 // added for IE_TAG_BITS
   parameter       IE_BURST_NUM_BITS           = `MEMC_BURST_LENGTH==16 ? 4 : 3,   // added for IE_TAG_BITS
   parameter       NO_OF_BT                    = `MEMC_NO_OF_BLK_TOKEN,            // added for IE_TAG_BITS
   parameter       BT_BITS                     = $clog2(NO_OF_BT),                   // added for IE_TAG_BITS
   parameter       ECCAP_BITS                  = `MEMC_ECCAP_EN,                   // added for IE_TAG_BITS
   parameter       IE_TAG_BITS                 = (`MEMC_INLINE_ECC_EN==1) ? IE_RD_TYPE_BITS + IE_BURST_NUM_BITS + BT_BITS + ECCAP_BITS : 0,
   parameter       WORD_BITS                   = `MEMC_WORD_BITS,                  // address a word within a burst
   parameter       BLK_BITS                    = `MEMC_BLK_BITS,                   // 2 column bits are critical word
   parameter       BSM_BITS                    = `UMCTL2_BSM_BITS,
   parameter       PW_BC_SEL_BITS              = 3,

   parameter       CMD_LEN_BITS                = 1,                                // command length bit width
   parameter       CORE_TAG_WIDTH              = `MEMC_TAGBITS,                    // width of tag
   parameter       RMW_TYPE_BITS               = 2,                                // 2-bit RMW type
   parameter       WR_CAM_ADDR_WIDTH           = `MEMC_WRCMD_ENTRY_BITS,           // bits to address into write CAM
   parameter       MAX_CAM_ADDR_WIDTH          = 0,
   parameter       HIF_KEYID_WIDTH             = `DDRCTL_HIF_KEYID_WIDTH

   );




   logic                                                      ih_gs_rdlow_empty;
   logic                                                      ih_gs_rdhigh_empty;
   logic                                                      ih_gs_any_vpr_timed_out;
   logic                                                      ih_gs_any_vpw_timed_out;


   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_rd_page_hit;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_rd_valid;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_wr_page_hit;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_wr_valid;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_rd_bank_page_hit;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_wr_bank_page_hit;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_rd_hi;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_bs_wrecc_btt;

   logic [NUM_TOTAL_BSMS*RD_CAM_ADDR_WIDTH-1:0]               te_os_rd_entry_table;
   logic [NUM_TOTAL_BSMS*WR_CAM_ADDR_WIDTH_IE-1:0]            te_os_wr_entry_table;
   logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                       te_os_rd_page_table;
   logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                       te_os_wr_page_table;
   logic [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]                    te_os_rd_cmd_autopre_table;
   logic [NUM_TOTAL_BSMS*AUTOPRE_BITS-1:0]                    te_os_wr_cmd_autopre_table;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_os_rd_pageclose_autopre;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_os_wr_pageclose_autopre;
   logic [NUM_TOTAL_BSMS*MWR_BITS-1:0]                        te_os_mwr_table;
   logic [NUM_TOTAL_BSMS-1:0]                                 te_b3_bit;
   logic [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0]                     te_os_rd_ie_tag_table;
   logic [NUM_TOTAL_BSMS*IE_TAG_BITS-1:0]                     te_os_wr_ie_tag_table;
   logic [NUM_TOTAL_BSMS*PARTIAL_WR_BITS_LOG2-1:0]            te_os_wr_mr_ram_raddr_lsb_first_table;
   logic [NUM_TOTAL_BSMS*PW_WORD_CNT_WD_MAX-1:0]              te_os_wr_mr_pw_num_beats_m1_table; 
   logic [NUM_TOTAL_BSMS*CMD_LEN_BITS-1:0]                    te_os_rd_length_table;
   logic [NUM_TOTAL_BSMS*WORD_BITS-1:0]                       te_os_rd_critical_word_table;

   logic [BSM_BITS-1:0]                                       te_os_hi_bsm_hint;
   logic [BSM_BITS-1:0]                                       te_os_lo_bsm_hint;
   logic [BSM_BITS-1:0]                                       te_os_wr_bsm_hint;
   logic [BSM_BITS-1:0]                                       te_os_wrecc_bsm_hint;
   logic [BSM_BITS-1:0]                                       te_os_lo_act_bsm_hint;
   logic [BSM_BITS-1:0]                                       te_os_wr_act_bsm_hint;

   logic [PAGE_BITS-1:0]                                      te_pi_rd_addr_ecc_row;
   logic [BLK_BITS-1:0]                                       te_pi_rd_addr_blk;
   logic [CORE_TAG_WIDTH-1:0]                                 te_pi_rd_tag;
   logic [RMW_TYPE_BITS-1:0]                                  te_pi_rd_rmw_type;
   logic [WR_CAM_ADDR_WIDTH-1:0]                              te_pi_rd_link_addr;
   logic                                                      te_pi_rd_addr_err;
   logic [BLK_BITS-1:0]                                       te_pi_wr_addr_blk;
   logic [WORD_BITS-1:0]                                      te_pi_wr_word;

   logic [BT_BITS-1:0]                                        te_pi_ie_bt;
   logic [IE_RD_TYPE_BITS-1:0]                                te_pi_ie_rd_type;
   logic [IE_BURST_NUM_BITS-1:0]                              te_pi_ie_blk_burst_num;
   logic                                                      te_pi_eccap;



   logic                                                      gs_be_op_is_activate;
   logic                                                      gs_be_op_is_precharge;
   logic                                                      gs_be_op_is_rdwr;
   logic [BSM_BITS-1:0]                                       gs_be_rdwr_bsm_num;
   logic [BSM_BITS-1:0]                                       gs_be_act_bsm_num;
   logic [BSM_BITS-1:0]                                       gs_be_pre_bsm_num;


   logic                                                      gs_te_op_is_rd;
   logic                                                      gs_te_op_is_wr;
   logic                                                      gs_te_op_is_activate;
   logic                                                      gs_te_op_is_precharge;
   logic [BSM_BITS-1:0]                                       gs_te_bsm_num4pre;
   logic [BSM_BITS-1:0]                                       gs_te_bsm_num4rdwr;
   logic [BSM_BITS-1:0]                                       gs_te_bsm_num4act;
   logic                                                      gs_te_wr_mode;
   logic                                                      gs_te_wr_possible;
   logic                                                      gs_te_pri_level;

`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
     logic [CMD_LEN_BITS-1:0]                                   gs_te_rd_length;
     logic [WORD_BITS-1:0]                                      gs_te_rd_word;
      logic [PARTIAL_WR_BITS_LOG2-1:0]                          gs_te_raddr_lsb_first;
        logic [PW_WORD_CNT_WD_MAX-1:0]                          gs_te_pw_num_beats_m1;
  `endif
`endif


   logic [MAX_CAM_ADDR_WIDTH-1:0]                             os_te_rdwr_entry;
   logic [IE_TAG_BITS-1:0]                                    os_te_rdwr_ie_tag;

   logic                                                      te_gs_rd_flush;
   logic                                                      te_gs_wr_flush;
   logic                                                      te_gs_block_wr;

   logic                                                      te_gs_any_rd_pending;
   logic                                                      te_gs_any_wr_pending;
   logic                                                      te_gs_any_vpr_timed_out;
   logic                                                      te_gs_any_vpr_timed_out_w;
   logic                                                      te_gs_any_vpw_timed_out;
   logic                                                      te_gs_any_vpw_timed_out_w;


   logic [NUM_LRANKS-1:0]                                     te_gs_rank_wr_pending; // WR command pending in the CAM per rank
   logic [NUM_LRANKS-1:0]                                     te_gs_rank_rd_pending; // RD command pending in the CAM per rank
   logic [NUM_TOTAL_BANKS-1:0]                                te_gs_bank_wr_pending; // WR command pending in the CAM per rank/bank
   logic [NUM_TOTAL_BANKS-1:0]                                te_gs_bank_rd_pending; // RD command pending in the CAM per rank/bank

   logic [NUM_LRANKS-1:0]                                     te_gs_rank_rd_valid;
   logic [NUM_LRANKS-1:0]                                     te_gs_rank_wr_valid;

   logic [RANK_BITS-1:0]                                      te_gs_rank_rd_prefer;
   logic [RANK_BITS-1:0]                                      te_gs_rank_wr_prefer;

   logic                                                      gsfsm_sr_co_if_stall;       //from gs to ih
   logic [NUM_TOTAL_BSMS-1:0]                                 te_ts_vpr_valid;            //from te to bs 
   logic [NUM_TOTAL_BSMS-1:0]                                 te_ts_vpw_valid;            //from te to bs
   logic [PAGE_BITS-1:0]                                      ts_act_page;                //from bs to te/be/pi
   logic [NUM_TOTAL_BSMS-1:0]                                 ts_te_sel_act_wr;           //from bs to te
   logic [NUM_TOTAL_BSMS-1:0]                                 te_rws_wr_col_bank;         //from te to be
   logic [NUM_TOTAL_BSMS-1:0]                                 te_rws_rd_col_bank;         //from te to bs
   logic [WR_CAM_ADDR_WIDTH_IE:0]                             te_num_wr_pghit_entries;    //from te to bs
   logic [RD_CAM_ADDR_WIDTH:0]                                te_num_rd_pghit_entries;    //from te to bs
   logic [WR_CAM_ADDR_WIDTH:0]                                te_wr_entry_avail;          //from te to bs
   logic [WR_CAM_ADDR_WIDTH:0]                                te_wrecc_entry_avail;       // Number of non-valid entries (WRECCCAM only, not include WR CAM), valid status
   logic [WR_CAM_ADDR_WIDTH:0]                                te_wrecc_entry_loaded;      // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   logic                                                      te_force_btt;
   logic [NUM_TOTAL_BSMS*PAGE_BITS-1:0]                       be_os_page_table;           //from be to os 
   logic                                                      te_rd_bank_pghit_vld_prefer;   //from te to gs
   logic                                                      te_wr_bank_pghit_vld_prefer;   //from te to gs
   logic                                                      ih_busy;        //from ih to gs
   logic                                                      ih_yy_xact_valid;
   logic                                                      unused_w;



   logic                                                      os_te_autopre;              //from os to te/bs/pi


//interface on cpf side
modport o_bm_mp (
    output unused_w
   );

modport i_gs_bm_mp (
    input  unused_w
   );
       
modport i_bs_bm_mp(
    input  unused_w
   );

modport o_ih_mp (
    output ih_gs_rdlow_empty
   ,output ih_gs_rdhigh_empty
   ,output ih_gs_any_vpr_timed_out
   ,output ih_gs_any_vpw_timed_out
   ,output ih_busy
   ,output ih_yy_xact_valid
  );
 
modport i_gs_ih_mp (
    input  gsfsm_sr_co_if_stall
   );

modport o_be_mp(
    output  be_os_page_table 
   );

modport i_gs_be_mp (
    input  gs_be_op_is_activate
   ,input  gs_be_op_is_precharge
   ,input  gs_be_op_is_rdwr
   ,input  gs_be_rdwr_bsm_num
   ,input  gs_be_act_bsm_num
   ,input  gs_be_pre_bsm_num
   );

modport i_bs_be_mp (
    input  ts_act_page 
   );

modport o_te_mp (
    output te_bs_rd_page_hit
   ,output te_bs_rd_valid
   ,output te_bs_wr_page_hit
   ,output te_bs_wr_valid
   ,output te_bs_rd_bank_page_hit
   ,output te_bs_wr_bank_page_hit
   ,output te_bs_rd_hi
   ,output te_bs_wrecc_btt
   ,output te_os_rd_entry_table
   ,output te_os_wr_entry_table
   ,output te_os_rd_page_table
   ,output te_os_wr_page_table
   ,output te_os_rd_cmd_autopre_table
   ,output te_os_wr_cmd_autopre_table
   ,output te_os_rd_length_table 
   ,output te_os_rd_critical_word_table
   ,output te_os_wr_mr_ram_raddr_lsb_first_table
   ,output te_os_wr_mr_pw_num_beats_m1_table
   ,output te_os_rd_pageclose_autopre
   ,output te_os_wr_pageclose_autopre
   ,output te_os_mwr_table
   ,output te_b3_bit
   ,output te_os_rd_ie_tag_table
   ,output te_os_wr_ie_tag_table
   ,output te_os_hi_bsm_hint
   ,output te_os_lo_bsm_hint
   ,output te_os_wr_bsm_hint
   ,output te_os_wrecc_bsm_hint
   ,output te_os_lo_act_bsm_hint
   ,output te_os_wr_act_bsm_hint
   ,output te_gs_rd_flush
   ,output te_gs_wr_flush
   ,output te_gs_block_wr
   ,output te_gs_any_rd_pending
   ,output te_gs_any_wr_pending
   ,output te_gs_any_vpr_timed_out
   ,output te_gs_any_vpr_timed_out_w
   ,output te_ts_vpr_valid 
   ,output te_gs_any_vpw_timed_out
   ,output te_gs_any_vpw_timed_out_w
   ,output te_ts_vpw_valid
   ,output te_gs_rank_wr_pending // WR command pending in the CAM per rank
   ,output te_gs_rank_rd_pending // RD command pending in the CAM per rank
   ,output te_gs_bank_wr_pending // WR command pending in the CAM per rank/bank
   ,output te_gs_bank_rd_pending // RD command pending in the CAM per rank/bank
   ,output te_gs_rank_rd_valid
   ,output te_gs_rank_wr_valid
   ,output te_gs_rank_rd_prefer
   ,output te_gs_rank_wr_prefer
   ,output te_pi_rd_addr_ecc_row
   ,output te_pi_rd_addr_blk
   ,output te_pi_rd_tag
   ,output te_pi_rd_rmw_type
   ,output te_pi_rd_link_addr
   ,output te_pi_rd_addr_err
   ,output te_pi_wr_addr_blk
   ,output te_pi_wr_word

   ,output te_pi_ie_bt
   ,output te_pi_ie_rd_type
   ,output te_pi_ie_blk_burst_num
   ,output te_pi_eccap
   ,output te_rws_wr_col_bank
   ,output te_rws_rd_col_bank
   ,output te_num_wr_pghit_entries
   ,output te_num_rd_pghit_entries
   ,output te_wr_entry_avail
   ,output  te_wrecc_entry_avail      // Number of non-valid entries (WRECCCAM only, not include WR CAM), valid status
   ,output  te_wrecc_entry_loaded     // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   ,output te_rd_bank_pghit_vld_prefer
   ,output te_wr_bank_pghit_vld_prefer
   );

modport i_retry_mp (
    input  unused_w
   );

modport o_retry_mp (
    input  unused_w
   );

modport i_bs_te_mp(
    input  unused_w
   ,input  ts_te_sel_act_wr
   ,input  te_force_btt
   );

modport i_gs_te_mp (
    input  gs_te_op_is_rd
   ,input  gs_te_op_is_wr
   ,input  gs_te_op_is_activate
   ,input  gs_te_op_is_precharge
   ,input  gs_te_bsm_num4pre
   ,input  gs_te_bsm_num4rdwr
   ,input  gs_te_bsm_num4act
`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
   ,input  gs_te_rd_length
   ,input  gs_te_rd_word
   ,input  gs_te_raddr_lsb_first
   ,input  gs_te_pw_num_beats_m1 
`endif
`endif

   ,input  gs_te_wr_mode
   ,input  gs_te_wr_possible
   ,input  gs_te_pri_level
   );

modport i_os_te_mp (
    input  os_te_rdwr_entry
   ,input  os_te_rdwr_ie_tag
   ,input  os_te_autopre
   );

//modport i_pi_te_mp();


//interface on cpe side
modport o_gs_mp (
    output gs_be_op_is_activate
   ,output gs_be_op_is_precharge
   ,output gs_be_op_is_rdwr
   ,output gs_be_rdwr_bsm_num
   ,output gs_be_act_bsm_num
   ,output gs_be_pre_bsm_num

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
   ,output  gs_te_rd_length
   ,output  gs_te_rd_word
   ,output  gs_te_raddr_lsb_first
   ,output  gs_te_pw_num_beats_m1 
`endif
`endif




   ,output gs_te_op_is_rd
   ,output gs_te_op_is_wr
   ,output gs_te_op_is_activate
   ,output gs_te_op_is_precharge
   ,output gs_te_bsm_num4pre
   ,output gs_te_bsm_num4rdwr
   ,output gs_te_bsm_num4act
   ,output gs_te_wr_mode
   ,output gs_te_wr_possible
   ,output gs_te_pri_level
   ,output gsfsm_sr_co_if_stall
   );

modport o_bs_mp (
    output ts_act_page
   ,output ts_te_sel_act_wr
   ,output te_force_btt
   );

modport o_os_mp (
    output os_te_rdwr_entry
   ,output os_te_rdwr_ie_tag
   ,output os_te_autopre
   );

//modport i_bm_gs_mp ();

modport i_bm_bs_mp (
    input  unused_w
   );


modport i_be_gs_mp (
    input  unused_w
   );

//modport i_be_bs_mp(); //same with i_be_gs_mp

modport i_ih_gs_mp (
    input  ih_gs_rdlow_empty
   ,input  ih_gs_rdhigh_empty
   ,input  ih_gs_any_vpr_timed_out
   ,input  ih_gs_any_vpw_timed_out
   ,input  ih_busy
   ,input  ih_yy_xact_valid
   );
   
modport i_ih_bs_mp (
    input  unused_w
   );

modport i_te_bs_mp (
    input  te_bs_rd_page_hit
   ,input  te_bs_rd_valid
   ,input  te_bs_wr_page_hit
   ,input  te_bs_wr_valid
   ,input  te_bs_rd_bank_page_hit
   ,input  te_bs_wr_bank_page_hit
   ,input  te_bs_rd_hi
   ,input  te_bs_wrecc_btt
   ,input  te_ts_vpr_valid 
   ,input  te_ts_vpw_valid
   ,input  te_rws_wr_col_bank
   ,input  te_rws_rd_col_bank
   ,input  te_num_wr_pghit_entries
   ,input  te_num_rd_pghit_entries
   ,input  te_wr_entry_avail
   ,input  te_wrecc_entry_avail      // Number of non-valid entries (WRECCCAM only, not include WR CAM), valid status
   ,input  te_wrecc_entry_loaded     // Number of loaded entries (WRECCCAM only, not include WR CAM), regardless of valid status.
   );

modport i_te_os_mp (
    input  te_os_rd_entry_table
   ,input  te_os_wr_entry_table
   ,input  te_os_rd_page_table
   ,input  te_os_wr_page_table
   ,input  te_os_rd_cmd_autopre_table
   ,input  te_os_wr_cmd_autopre_table
   ,input  te_os_rd_length_table 
   ,input  te_os_rd_critical_word_table
   ,input  te_os_wr_mr_ram_raddr_lsb_first_table
   ,input  te_os_wr_mr_pw_num_beats_m1_table
   ,input  te_os_rd_pageclose_autopre
   ,input  te_os_wr_pageclose_autopre
   ,input  te_os_mwr_table
   ,input  te_b3_bit
   ,input  te_os_rd_ie_tag_table
   ,input  te_os_wr_ie_tag_table
   ,input  te_os_hi_bsm_hint
   ,input  te_os_lo_bsm_hint
   ,input  te_os_wr_bsm_hint
   ,input  te_os_wrecc_bsm_hint
   ,input  te_os_lo_act_bsm_hint
   ,input  te_os_wr_act_bsm_hint
   );

modport i_te_gs_mp (
    input  te_gs_rd_flush
   ,input  te_gs_wr_flush
   ,input  te_gs_block_wr
   ,input  te_gs_any_rd_pending
   ,input  te_gs_any_wr_pending
   ,input  te_gs_any_vpr_timed_out
   ,input  te_gs_any_vpr_timed_out_w
   ,input  te_gs_any_vpw_timed_out
   ,input  te_gs_any_vpw_timed_out_w
   ,input  te_gs_rank_wr_pending // WR command pending in the CAM per rank
   ,input  te_gs_rank_rd_pending // RD command pending in the CAM per rank
   ,input  te_gs_bank_wr_pending // WR command pending in the CAM per rank/bank
   ,input  te_gs_bank_rd_pending // RD command pending in the CAM per rank/bank
   ,input  te_gs_rank_rd_valid
   ,input  te_gs_rank_wr_valid
   ,input  te_gs_rank_rd_prefer
   ,input  te_gs_rank_wr_prefer
   ,input  te_rd_bank_pghit_vld_prefer
   ,input  te_wr_bank_pghit_vld_prefer
   );


modport i_be_os_mp (
    input  be_os_page_table 
   );

modport i_te_pi_mp (   
    input   te_pi_rd_addr_blk
   ,input   te_pi_rd_tag
   ,input   te_pi_rd_addr_ecc_row
   ,input   te_pi_rd_rmw_type
   ,input   te_pi_rd_link_addr
   ,input   te_pi_rd_addr_err
   ,input   te_pi_wr_addr_blk
   ,input   te_pi_wr_word

   ,input   te_pi_ie_bt
   ,input   te_pi_ie_rd_type
   ,input   te_pi_ie_blk_burst_num
   ,input   te_pi_eccap
   ,input   te_gs_any_rd_pending
   ,input   te_gs_any_wr_pending
   );



modport i_ih_pi_mp(
    input  ih_yy_xact_valid
   );

//modport o_pi_mp();


endinterface : dwc_ddrctl_ddrc_cpfcpe_if

`endif // __GUARD__DWC_DDRCTL_DDRC_CPFCPE_IF__SVH__
