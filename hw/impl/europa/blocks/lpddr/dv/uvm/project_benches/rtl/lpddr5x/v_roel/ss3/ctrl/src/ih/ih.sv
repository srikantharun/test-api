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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih.sv#7 $
// -------------------------------------------------------------------------
// Description:
//
// This is the top level of IH module.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module ih 
import DWC_ddrctl_reg_pkg::*;
#(
    //------------------------------ PARAMETERS ------------------------------------
     parameter CORE_ADDR_WIDTH   = (`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS) 
    ,parameter IH_TAG_WIDTH      = `MEMC_TAGBITS                 // width of token/tag field from core
    ,parameter CMD_LEN_BITS      = 1                             // bits for command length, when used
    ,parameter RDCMD_ENTRY_BITS  = `MEMC_RDCMD_ENTRY_BITS        // bits to address all entries in read CAM
    ,parameter WRCMD_ENTRY_BITS  = `MEMC_WRCMD_ENTRY_BITS        // bits to address all entries in write CAM
    ,parameter WRECCCMD_ENTRY_BITS = 0                           // overridden 
    ,parameter WRCMD_ENTRY_BITS_IE = 0                           // overridden 
    ,parameter RMW_TYPE_BITS     = 2                             // 2 bits for RMW type
                                                                 //  (partial write, atomic RMW, scrub, or none)
    ,parameter WDATA_PTR_BITS    = `MEMC_WDATA_PTR_BITS 
    ,parameter CMD_TYPE_BITS     = 2                             // any change will require RTL modifications in IC
    
    ,parameter WRDATA_ENTRY_BITS = WRCMD_ENTRY_BITS + 1          // write data RAM entries
                                                                 // (only support 2 datas per command at the moment)
    ,parameter WRDATA_CYCLES     = `MEMC_WRDATA_CYCLES 
    ,parameter RD_LATENCY_BITS   = `UMCTL2_XPI_RQOS_TW 
    ,parameter WR_LATENCY_BITS   = `UMCTL2_XPI_WQOS_TW 
    ,parameter BT_BITS           = 4  
    ,parameter BWT_BITS          = 4  
    ,parameter BRT_BITS          = 4  
    ,parameter NO_OF_BT          = 16    
    ,parameter NO_OF_BWT         = 16    
    ,parameter NO_OF_BRT         = 16    
    ,parameter NO_OF_BLK_CHN     = 16    
    ,parameter BLK_CHN_BITS      = 4    
    ,parameter IE_RD_TYPE_BITS   = `IE_RD_TYPE_BITS
    ,parameter IE_WR_TYPE_BITS   = `IE_WR_TYPE_BITS
    ,parameter IE_BURST_NUM_BITS = 5
    ,parameter MWR_BITS = `DDRCTL_MWR_BITS
    ,parameter PARTIAL_WR_BITS = `UMCTL2_PARTIAL_WR_BITS 
    ,parameter PARTIAL_WR_BITS_LOG2 = 1 
//    `ifdef DDRCTL_ANY_RETRY
    ,parameter RETRY_TIMES_WIDTH  = 3
//    `endif
    ,parameter PW_WORD_CNT_WD_MAX = 1 
    ,parameter       AM_DCH_WIDTH     = 6
    ,parameter       AM_CS_WIDTH      = 6
    ,parameter       AM_CID_WIDTH     = 6
    ,parameter       AM_BANK_WIDTH    = 6
    ,parameter       AM_BG_WIDTH      = 6
    ,parameter       AM_ROW_WIDTH     = 5
    ,parameter       AM_COL_WIDTH_H   = 5
    ,parameter       AM_COL_WIDTH_L   = 4
    ,parameter       HIF_KEYID_WIDTH  = `DDRCTL_HIF_KEYID_WIDTH
    )
    (
    //-------------------------- INPUTS AND OUTPUTS --------------------------------    
     input                               co_ih_clk                 // clock
    ,input                               core_ddrc_rstn            // reset
    ,input                           ddrc_cg_en             // DDRC clock gating signal

    //////////////////////
    // Core Interface
    //////////////////////
    ,input                               hif_cmd_valid             // valid command
    ,input [CMD_TYPE_BITS-1:0]           hif_cmd_type              // command type:
                                                                   //  00 - block write
                                                                   //  01 - read
                                                                   //  10 - rmw
                                                                   //  11 - reserved

    ,input [CORE_ADDR_WIDTH-1:0]         hif_cmd_addr              // address
    ,input [IH_TAG_WIDTH-1:0]            hif_cmd_token             // read token returned w/ read data
    ,input [1:0]                         hif_cmd_pri               // priority:
                                                                   //  00 - low priority, 01 - VPR
                                                                   //  10 - high priority, 11 - Unused
    ,input [CMD_LEN_BITS-1:0]            hif_cmd_length            // length (1 word or 2)
                                                                   //  1 - 1 word
                                                                   //  0 - 2 words
    ,input [WDATA_PTR_BITS-1:0]          hif_cmd_wdata_ptr         //
    ,input                               hif_cmd_autopre           // auto precharge enable
    ,input [RD_LATENCY_BITS-1:0]         hif_cmd_latency 
    ,input                               gsfsm_sr_co_if_stall 
    ,output                              ih_busy                   // is high when a cmd comes into IH and when the FIFO's are non-empty
    ,output                              ih_te_ppl_wr_empty
    ,output                              ih_te_ppl_rd_empty
    ,output                              ih_fifo_wr_empty 
    ,output                              ih_fifo_rd_empty 
    ,output                              hif_cmd_stall             // cmd stall
    ,output [WDATA_PTR_BITS-1:0]         hif_wdata_ptr 
    ,output                              hif_wdata_ptr_valid 
    ,output                              hif_wdata_ptr_addr_err 
    ,output                              hif_wr_credit 
    ,output [`MEMC_HIF_CREDIT_BITS-1:0]  hif_lpr_credit 
    ,output [`MEMC_HIF_CREDIT_BITS-1:0]  hif_hpr_credit 
    ,output [`MEMC_HIF_CREDIT_BITS-1:0]  hif_wrecc_credit
    ,input                               co_ih_lpr_num_entries_changed 
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in ih_assertions module
    ,input [2:0]                         dh_ih_operating_mode       // global schedule FSM state
//spyglass enable_block W240
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used at uMCTL2
//spyglass enable_block W240
    ,input [2:0]                         dh_ih_nonbinary_device_density
    ,input                               reg_ddrc_lpddr5
    ,input [BANK_ORG_WIDTH-1:0]          reg_ddrc_bank_org
    ,input                               dh_ih_dis_hif             // disable (stall) hif
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
    ,input [BURST_RDWR_WIDTH-1:0]        reg_ddrc_burst_rdwr 
//spyglass enable_block W240
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
    ,input                               reg_ddrc_ecc_type
//spyglass enable_block W240
    ,input   [2:0]                       reg_ddrc_ecc_mode
    ,input                               reg_ddrc_ecc_region_remap_en
    ,input   [6:0]                       reg_ddrc_ecc_region_map
    ,input   [1:0]                       reg_ddrc_ecc_region_map_granu
    ,input                               reg_ddrc_ecc_region_map_other
    ,input                               reg_ddrc_ecc_region_parity_lock
    ,input                               reg_ddrc_ecc_region_waste_lock
    ,input   [BLK_CHANNEL_IDLE_TIME_X32_WIDTH-1:0]                       reg_ddrc_blk_channel_idle_time_x32 
    ,input   [4:0]                       reg_ddrc_active_blk_channel
    ,input                               reg_ddrc_blk_channel_active_term
    ,input [SELFREF_SW_WIDTH-1:0]        reg_ddrc_selfref_sw
    ,input                               reg_ddrc_ecc_ap_en
    /////////////////
    // WU Interface
    /////////////////
    ,input                               wu_ih_flow_cntrl_req      // wu_wdata_if fifo in WU is full
    
    /////////////////
    // TE Interface
    /////////////////
    ,output                              ih_te_rd_valid 
    ,output                              ih_te_wr_valid 
    ,output                              ih_wu_wr_valid 
    ,output                              ih_te_rd_valid_addr_err 
    ,output                              ih_te_wr_valid_addr_err 
    ,output [CMD_LEN_BITS-1:0]           ih_te_rd_length 
    ,output [IH_TAG_WIDTH-1:0]           ih_te_rd_tag 
    ,output [RMW_TYPE_BITS-1:0]          ih_te_rmwtype             // 00 - partial write
                                                                   // 01 - atomic RMW commands
                                                                   // 10 - scrub
                                                                   // 11 - no RMW
    ,output [MWR_BITS-1:0]               ih_te_mwr 
    ,input                               reg_ddrc_frequency_ratio
    ,output [PARTIAL_WR_BITS-1:0]        ih_te_wr_word_valid 
    ,output [PARTIAL_WR_BITS_LOG2-1:0]   ih_te_wr_ram_raddr_lsb_first 
    ,output [PW_WORD_CNT_WD_MAX-1:0]     ih_te_wr_pw_num_beats_m1 
    ,output [PW_WORD_CNT_WD_MAX-1:0]     ih_te_wr_pw_num_cols_m1 
    ,output [`UMCTL2_LRANK_BITS -1:0]    ih_te_rd_rank_num         // rank of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`UMCTL2_LRANK_BITS -1:0]    ih_te_wr_rank_num         // rank of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BG_BITS -1:0]         ih_te_rd_bankgroup_num    // bankgroup of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BG_BITS -1:0]         ih_te_wr_bankgroup_num    // bankgroup of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BG_BANK_BITS -1:0]    ih_te_rd_bg_bank_num      // bank & bg of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BG_BANK_BITS -1:0]    ih_te_wr_bg_bank_num      // bank & bg of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BANK_BITS -1:0]       ih_te_rd_bank_num         // bank of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BANK_BITS -1:0]       ih_te_wr_bank_num         // bank of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_PAGE_BITS -1:0]       ih_te_rd_page_num         // page/row of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_PAGE_BITS -1:0]       ih_te_wr_page_num         // page/row of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BLK_BITS  -1:0]       ih_te_rd_block_num        // block  of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_BLK_BITS  -1:0]       ih_te_wr_block_num        // block  of request to TE, qualified by (ih_te_rd_valid or ih_te_wr_valid)
    ,output [`MEMC_WORD_BITS-1:0]        ih_te_critical_dword      // for reads only, critical word within a block - not currently supported
                                                                   // would be qualified by ((ih_te_rd_valid | ih_te_wr_valid) & ih_te_rd))
                                                                   // for rmw, this is forced to 0
    ,output [RDCMD_ENTRY_BITS-1:0]       ih_te_rd_entry 
    ,output [WRCMD_ENTRY_BITS_IE-1:0]    ih_te_wr_entry 
    ,output [WRCMD_ENTRY_BITS-1:0]       ih_te_wr_entry_rmw 
    ,output [WRCMD_ENTRY_BITS-1:0]       ih_te_wr_prefer 
    ,output [WRECCCMD_ENTRY_BITS-1:0]    ih_te_wrecc_prefer 
    ,output [RDCMD_ENTRY_BITS-1:0]       ih_te_lo_rd_prefer 
    ,output [RDCMD_ENTRY_BITS-1:0]       ih_te_hi_rd_prefer 
    ,output [1:0]                        ih_te_rd_hi_pri           // priority of read request
    ,output [1:0]                        ih_te_wr_hi_pri           // priority of write request
    ,output                              ih_te_rd_autopre 
    ,output                              ih_te_wr_autopre 
    ,output [RD_LATENCY_BITS-1:0]        ih_te_rd_latency 
    ,output                              ih_gs_any_vpr_timed_out 
    ,output [WR_LATENCY_BITS-1:0]        ih_te_wr_latency 
    ,output                              ih_gs_any_vpw_timed_out 
    ,output [`MEMC_WORD_BITS-1:0]        ih_wu_critical_dword      // for reads only, critical word within a block - not currently supported
                                                                   //  would be qualified by ((ih_te_rd_valid | ih_te_wr_valid) & ih_te_rd))
                                                                   // for rmw, this is NOT forced to 0
    ,input [RDCMD_ENTRY_BITS-1:0]        te_ih_free_rd_entry       // read CAM entry # to be freed, when te_ih_free_rd_entry_valid=1
    ,input                               te_ih_free_rd_entry_valid // a read CAM entry # is being freed
    ,input [WRCMD_ENTRY_BITS_IE-1:0]     mr_ih_free_wr_entry       // write CAM entry # to be freed, when mr_ih_free_wr_entry_valid=1
    ,input                               mr_ih_free_wr_entry_valid // a write CAM entry # is being freed
    ,input                               te_ih_retry               // collision detected. stall IH outputs.
    ,input                               te_ih_wr_combine          // collision detected. stall IH outputs.
    ,input                               te_gs_any_vpr_timed_out 
    
    `ifdef SNPS_ASSERT_ON
     `ifndef SYNTHESIS
     `endif // SYNTHESIS
    `endif // SNPS_ASSERT_ON
    
    /////////////////
    // TS Interface
    /////////////////
    ,output                              ih_yy_xact_valid          // any valid request from IH (read or write)
    ,output                              ih_gs_rdlow_empty         // transaction queue is empty
    ,output                              ih_gs_wr_empty            // transaction queue is empty
    ,output                              ih_gs_rdhigh_empty        // transaction queue is empty
    ,output                              ih_gs_wrecc_empty         // transaction queue is empty
    
    /////////////////
    // BE Interface
    /////////////////
    ,output                              ih_be_hi_pri_rd_xact      // hi priority read transaction valid
    ,output [`UMCTL2_LRANK_BITS -1:0]    ih_be_rank_num_rd 
    ,output [`UMCTL2_LRANK_BITS -1:0]    ih_be_rank_num_wr 
    ,output [`MEMC_BG_BANK_BITS -1:0]    ih_be_bg_bank_num_rd 
    ,output [`MEMC_BG_BANK_BITS -1:0]    ih_be_bg_bank_num_wr 
    ,output [`MEMC_PAGE_BITS -1:0]       ih_be_page_num 
    
    /////////////////
    // Inline ECC interface
    /////////////////
    ,input                               te_ih_re_done_i
    ,input   [BT_BITS-1:0]               te_ih_re_done_bt
    ,output  [BT_BITS-1:0]               ih_te_ie_bt
    ,output  [IE_RD_TYPE_BITS-1:0]       ih_te_ie_rd_type
    ,output  [IE_WR_TYPE_BITS-1:0]       ih_te_ie_wr_type
    ,output  [IE_BURST_NUM_BITS-1:0]     ih_te_ie_blk_burst_num  //only for the Data command
    ,output  [`MEMC_BLK_BITS-1:0]        ih_te_ie_block_num
    ,output  [BRT_BITS-1:0]              ih_rd_ie_brt
    ,output                              ih_rd_ie_rd_cnt_inc
    ,output                              ih_rd_ie_blk_rd_end
    ,output  [BWT_BITS-1:0]              ih_mr_ie_bwt
    ,output  [BRT_BITS-1:0]              ih_mr_ie_brt
    ,output                              ih_mr_ie_brt_vld
    ,output                              ih_mr_ie_wr_cnt_inc
    ,output                              ih_mr_ie_blk_wr_end
    ,output  [NO_OF_BWT-1:0]             ih_mr_ie_wr_cnt_dec_vct
    ,output                              ih_ie_empty
    ,input                               mr_ih_free_bwt_vld
    ,input   [BWT_BITS-1:0]              mr_ih_free_bwt
    ,input                               rd_ih_free_brt_vld
    ,input   [BRT_BITS-1:0]              rd_ih_free_brt
    ,input                               hif_cmd_ecc_region     
    ,input  [WRDATA_CYCLES-1:0]          hif_cmd_wdata_mask_full_ie 
   //signals for BTT and RDECC_RDY
    ,input                               rd_ih_ie_re_rdy
    ,output [NO_OF_BT-1:0]               ih_te_ie_re_vct
    ,output [NO_OF_BT-1:0]               ih_te_ie_btt_vct

   //signals for look up BT table
    ,input  [BT_BITS-1:0]                mr_ih_lkp_bwt_by_bt
    ,input  [BT_BITS-1:0]                mr_ih_lkp_brt_by_bt
    ,input  [BT_BITS-1:0]                rd_ih_lkp_brt_by_bt
    ,input  [BT_BITS-1:0]                rd_ih_lkp_bwt_by_bt
    ,output [BWT_BITS-1:0]               ih_mr_lkp_bwt
    ,output                              ih_mr_lkp_bwt_vld
    ,output [BRT_BITS-1:0]               ih_mr_lkp_brt
    ,output                              ih_mr_lkp_brt_vld
    ,output [BRT_BITS-1:0]               ih_rd_lkp_brt
    ,output                              ih_rd_lkp_brt_vld
    ,output [BWT_BITS-1:0]               ih_rd_lkp_bwt
    ,output                              ih_rd_lkp_bwt_vld
    ,output                              ih_ie_busy      //ih_ie_busy will assert ddrc_cg_en
    ,output                              ih_te_rd_eccap
    ,output                              ih_te_wr_eccap
    /////////////////////////////////////////
    //  Retry Ctrl Interface
    /////////////////////////////////////////
   
    ////////////////////////
    // Register Interface
    ////////////////////////
    ,input [RDCMD_ENTRY_BITS-1:0]        dh_ih_lpr_num_entries 
    // Address mapping inputs
    ,input   [AM_CS_WIDTH-1:0]           dh_ih_addrmap_rank_b0 
    ,input   [AM_BANK_WIDTH-1:0]         dh_ih_addrmap_bank_b0 
    ,input   [AM_BANK_WIDTH-1:0]         dh_ih_addrmap_bank_b1 
    ,input   [AM_BANK_WIDTH-1:0]         dh_ih_addrmap_bank_b2 
    ,input   [AM_BG_WIDTH-1:0]           dh_ih_addrmap_bg_b0 
    ,input   [AM_BG_WIDTH-1:0]           dh_ih_addrmap_bg_b1 
    ,input   [AM_COL_WIDTH_L-1:0]        dh_ih_addrmap_col_b3 
    ,input   [AM_COL_WIDTH_L-1:0]        dh_ih_addrmap_col_b4 
    ,input   [AM_COL_WIDTH_L-1:0]        dh_ih_addrmap_col_b5 
    ,input   [AM_COL_WIDTH_L-1:0]        dh_ih_addrmap_col_b6 
    ,input   [AM_COL_WIDTH_H-1:0]        dh_ih_addrmap_col_b7 
    ,input   [AM_COL_WIDTH_H-1:0]        dh_ih_addrmap_col_b8 
    ,input   [AM_COL_WIDTH_H-1:0]        dh_ih_addrmap_col_b9 
    ,input   [AM_COL_WIDTH_H-1:0]        dh_ih_addrmap_col_b10 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b0 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b1 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b2 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b3 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b4 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b5 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b6 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b7 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b8 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b9 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b10 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b11 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b12 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b13 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b14 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b15 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b16 
    ,input   [AM_ROW_WIDTH-1:0]          dh_ih_addrmap_row_b17 

    ,input                                                     reg_ddrc_bank_hash_en
    

    ////////////////////////
    // IME Interface
    ////////////////////////

    ////////////////////
    // Debug signals
    ////////////////////
    ,output                              ih_dh_stall 
    ,output [RDCMD_ENTRY_BITS:0]         ih_dh_hpr_q_depth       // number of valid entries in the high priority read queue
    ,output [RDCMD_ENTRY_BITS:0]         ih_dh_lpr_q_depth       // number of valid entries in the low priority read queue
    ,output [WRCMD_ENTRY_BITS:0]         ih_dh_wr_q_depth        // number of valid entries in the write queue
    ,output [WRCMD_ENTRY_BITS:0]         ih_dh_wrecc_q_depth        // number of valid entries in the write queue
    ,output                              input_fifo_empty
    ,output                              ih_te_ppl_empty
    );

localparam IE_CMD_BITS         =1;
localparam IE_CMD_IVLD_ADDR_BITS =1;
localparam ECC_HOLE_BITS       =2;
localparam IE_MASK_FULL_BITS   =WRDATA_CYCLES;
localparam IE_FIFO_DATA_BITS   = IE_CMD_BITS +
                                 IE_CMD_IVLD_ADDR_BITS +
                                 ECC_HOLE_BITS +
                                 IE_MASK_FULL_BITS +
                                 IE_BURST_NUM_BITS +
                                 `MEMC_BLK_BITS;

wire [IE_FIFO_DATA_BITS-1:0] input_fifo_din_ie;
wire [IE_FIFO_DATA_BITS-1:0] input_fifo_dout_ie;
wire                         te_ih_retry_ie_cmd;
wire                         ie_cmd_active ;
wire                         ecc_region_invalid;
wire                         rxcmd_ptc_vld;
wire                         ie_rd_vld;
wire                         ie_wr_vld;
wire [CMD_LEN_BITS-1:0]      ie_rd_length; // <- full
wire [IH_TAG_WIDTH-1:0]      ie_rd_tag;    // <- 0;
wire [RMW_TYPE_BITS-1:0]     ie_rmwtype; 
wire [1:0]                   ie_hi_pri; 
wire                         ie_autopre;

wire                         is_wecc_cmd;  // indicate it is write ecc command.
wire                         is_recc_cmd;  // indicate it is read ecc command.

wire [`UMCTL2_LRANK_BITS-1:0]    ie_rank_num;
wire [`MEMC_BG_BANK_BITS-1:0]    ie_bg_bank_num;
wire [`MEMC_BLK_BITS-1:0]        ie_block_num;
wire [`MEMC_PAGE_BITS-1:0]       ie_page_num;
wire [`MEMC_WORD_BITS-1:0]       ie_critical_dword;

wire [BWT_BITS-1:0]              ih_te_ie_bwt;
wire                             ih_mr_ie_wr_cnt_dec;
reg  [NO_OF_BWT-1:0]             ih_mr_ie_wr_cnt_dec_vct_r;

wire [5:0]                       highest_col_bit;  // the bit in hif address for the highest column address.
wire [3:0]                       highest_col_num;  // the number of column address.

wire assert_ie_cmd             ;
wire assert_ie_cmd_invalid_addr;
wire assert_dis_dm             ;


wire   te_ih_core_in_stall; //it indicate block the input fifo, will be assert when te_ih_retry or ie_cmd_active assert 
wire   te_ppl_ih_stall;
wire   te_ih_retry_i;
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in ih_assertions module.
assign te_ih_core_in_stall = te_ih_retry_ie_cmd;
assign te_ih_retry_i       = te_ih_retry | (is_wecc_cmd & ih_te_wr_valid) | (is_recc_cmd & ih_te_rd_valid);
//spyglass enable_block W528
////////////////////////////
// WIRES 
////////////////////////////
wire                            hif_rcmd_stall;
wire                            hif_wcmd_stall;

assign hif_cmd_stall = hif_rcmd_stall | hif_wcmd_stall;

wire                            rxcmd_valid;
wire [CORE_ADDR_WIDTH-1:0]      rxcmd_addr;
wire [CMD_TYPE_BITS-1:0]        rxcmd_type;
wire [IH_TAG_WIDTH-1:0]         rxcmd_token;
wire [CMD_LEN_BITS-1:0]         rxcmd_length;
wire [WDATA_PTR_BITS-1:0]       rxcmd_wdata_ptr;        
wire [RD_LATENCY_BITS-1:0]      rxcmd_rd_latency;
wire [WR_LATENCY_BITS-1:0]      rxcmd_wr_latency;

wire [CORE_ADDR_WIDTH-1:0]      rxcmd_addr_dup;

wire                            ih_te_autopre;          // auto precharge enable flag
wire                            rxcmd_autopre;
wire                            rxcmd_invalid_addr_nonbinary;
wire                            rxcmd_invalid_addr;
wire                            rxcmd_invalid_addr_row13_12;
wire                            rxcmd_invalid_addr_row14_13;
wire                            rxcmd_invalid_addr_row15_14;
wire                            rxcmd_invalid_addr_row16_15;
wire                            rxcmd_invalid_addr_row17_16;



wire [1:0]                      rxcmd_pri;
wire [1:0]                      ih_te_hi_pri;           // priority that is affected by the force_low_pri_n signal
wire [1:0]                      ih_te_hi_pri_int;       // internal priority signal, same as the incoming co_rxcmd_pri

wire [RDCMD_ENTRY_BITS:0]       hpr_fifo_fill_level;


wire [WRECCCMD_ENTRY_BITS:0]     wrecc_fifo_fill_level;


wire [WRCMD_ENTRY_BITS:0]       wr_fifo_fill_level;
wire [RDCMD_ENTRY_BITS:0]       lpr_fifo_fill_level;

// Based on address mapper widths, regardless of bits used by
//  any particular design instance
wire [`UMCTL2_LRANK_BITS-1:0]   mapped_rank_num;
wire [`MEMC_BG_BANK_BITS-1:0]   mapped_bg_bank_num;
wire [`MEMC_PAGE_BITS-1:0]      mapped_page_num;

wire [`MEMC_BLK_BITS-1:0]       mapped_block_num;
wire [`MEMC_WORD_BITS-1:0]      critical_dword;

wire [`UMCTL2_LRANK_BITS-1:0]   mapped_rank_num_to_te;
wire [`MEMC_BG_BANK_BITS-1:0]   mapped_bg_bank_num_to_te;
wire [`MEMC_PAGE_BITS-1:0]      mapped_page_num_to_te;

wire [`MEMC_BLK_BITS-1:0]       mapped_block_num_to_te;
wire [`MEMC_WORD_BITS-1:0]      critical_dword_to_te;

wire                            mapped_addr_eccap_to_te;
wire                            rxcmd_addr_eccap;



wire [`UMCTL2_LRANK_BITS-1:0]   ih_yy_rank_num;
wire [`MEMC_BG_BANK_BITS-1:0]   ih_yy_bg_bank_num;
wire [`MEMC_PAGE_BITS-1:0]      ih_yy_page_num;
wire [`MEMC_PAGE_BITS-1:0]      ih_yy_page_num_corr;




wire                            ih_te_eccap;

wire [`UMCTL2_LRANK_BITS -1:0]  ih_te_rank_num;
wire [`MEMC_BG_BITS-1:0]        ih_te_bankgroup_num;
wire [`MEMC_BG_BANK_BITS -1:0]  ih_te_bg_bank_num;
wire [`MEMC_BANK_BITS -1:0]     ih_te_bank_num;
wire [`MEMC_PAGE_BITS-1:0]      ih_te_page_num_corr;
wire [`MEMC_BLK_BITS -1:0]      ih_te_block_num;

wire                            input_fifo_full;
wire                            ih_in_busy;

wire                            lpr_cam_empty ;
wire                            lpr_cam_full  ;
wire                            hpr_cam_empty ;
wire                            hpr_cam_full  ;
wire                            wr_cam_empty  ;
wire                            wr_cam_full   ;
wire                            wrecc_cam_empty  ;
wire                            wrecc_cam_full   ;
wire                            wr_cam_full_unused;




wire                            bg_b16_addr_mode;

// signals for IH_TE_PIPELINE  -- begin -- //
wire [WDATA_PTR_BITS-1:0]         ppl_rxcmd_wdata_ptr;        

wire                              ih_ppl_te_rd_valid; 
wire                              ih_ppl_te_wr_valid; 
wire                              ih_ppl_wu_wr_valid; 
wire                              ih_ppl_te_rd_valid_addr_err; 
wire                              ih_ppl_te_wr_valid_addr_err; 
wire [CMD_LEN_BITS-1:0]           ih_ppl_te_rd_length; 
wire [IH_TAG_WIDTH-1:0]           ih_ppl_te_rd_tag; 
wire [RMW_TYPE_BITS-1:0]          ih_ppl_te_rmwtype; 

wire [1:0]                        ih_ppl_te_hi_pri; 
wire [1:0]                        ih_ppl_te_hi_pri_int;

wire [RD_LATENCY_BITS-1:0]        ih_ppl_te_rd_latency;
wire                              ih_ppl_gs_any_vpr_timed_out; 
wire [WR_LATENCY_BITS-1:0]        ih_ppl_te_wr_latency; 
wire                              ih_ppl_gs_any_vpw_timed_out; 
wire                              ih_ppl_te_autopre;
wire                              ih_ppl_te_eccap;
wire [`UMCTL2_LRANK_BITS -1:0]    ih_ppl_te_rank_num;
wire [`MEMC_BG_BITS-1:0]          ih_ppl_te_bankgroup_num;
wire [`MEMC_BG_BANK_BITS -1:0]    ih_ppl_te_bg_bank_num;
wire [`MEMC_BANK_BITS -1:0]       ih_ppl_te_bank_num;
wire [`MEMC_PAGE_BITS -1:0]       ih_ppl_te_page_num;
wire [`MEMC_PAGE_BITS-1:0]        ih_ppl_te_page_num_corr; 
wire [`MEMC_BLK_BITS -1:0]        ih_ppl_te_block_num;
wire [`MEMC_WORD_BITS-1:0]        ih_ppl_te_critical_dword;
wire [`MEMC_WORD_BITS-1:0]        ih_ppl_wu_critical_dword;



wire [MWR_BITS-1:0]               ih_ppl_te_mwr;
wire [PARTIAL_WR_BITS-1:0]        ih_ppl_te_wr_word_valid;
wire [PARTIAL_WR_BITS_LOG2-1:0]   ih_ppl_te_wr_ram_raddr_lsb_first;
wire [PW_WORD_CNT_WD_MAX-1:0]     ih_ppl_te_wr_pw_num_beats_m1;
wire [PW_WORD_CNT_WD_MAX-1:0]     ih_ppl_te_wr_pw_num_cols_m1;

wire [BT_BITS-1:0]                ih_ppl_te_ie_bt;
wire [BWT_BITS-1:0]               ih_ppl_te_ie_bwt;
wire [IE_RD_TYPE_BITS-1:0]        ih_ppl_te_ie_rd_type;
wire [IE_WR_TYPE_BITS-1:0]        ih_ppl_te_ie_wr_type;
wire [IE_BURST_NUM_BITS-1:0]      ih_ppl_te_ie_blk_burst_num;  //only for the Data command
wire [`MEMC_BLK_BITS-1:0]         ih_ppl_te_ie_block_num;
wire [NO_OF_BT-1:0]               ih_te_ie_btt_vct_ctl;
// Signals for IH_TE_PIPELINE  -- end -- //

// Signals for ih_retry_mux -- begin -- //
   //data in from IH
wire                              i_ih_te_rd_valid;
wire                              i_ih_te_wr_valid;
wire                              i_ih_wu_wr_valid;
wire [RMW_TYPE_BITS-1:0]          i_ih_te_rmwtype;
wire                              i_ih_te_wr_valid_addr_err;
wire                              i_ih_te_rd_valid_addr_err;
wire [RD_LATENCY_BITS-1:0]        i_ih_te_rd_latency; 
wire [WR_LATENCY_BITS-1:0]        i_ih_te_wr_latency; 
wire [CMD_LEN_BITS-1:0]           i_ih_te_rd_length; 
wire [IH_TAG_WIDTH-1:0]           i_ih_te_rd_tag;




wire  [1:0]                       i_ih_te_hi_pri;          // priority that is affected by the force_low_pri_n signal
wire  [1:0]                       i_ih_te_hi_pri_int;      
wire                              i_ih_te_autopre;         // auto precharge enable flag
wire   [`UMCTL2_LRANK_BITS -1:0]  i_ih_te_rank_num;
wire   [`MEMC_BG_BITS-1:0]        i_ih_te_bankgroup_num;
wire   [`MEMC_BG_BANK_BITS -1:0]  i_ih_te_bg_bank_num;
wire   [`MEMC_BANK_BITS -1:0]     i_ih_te_bank_num;
wire   [`MEMC_PAGE_BITS -1:0]     i_ih_te_page_num_corr;
wire   [`MEMC_BLK_BITS -1:0]      i_ih_te_block_num;
wire   [`MEMC_WORD_BITS-1:0]      i_ih_te_critical_dword;      // for reads only, critical word within a block - not currently supported
wire   [`MEMC_WORD_BITS-1:0]      i_ih_wu_critical_dword;     // for reads only, critical word within a block - not currently supported



wire  [`MEMC_BG_BITS-1:0]        retryctrl_bankgroup_num;

// Signals for ih_retry_mux -- end -- //






integer i;
//generate ih_mr_ie_wr_cnt_dec_vct when write combine happened
assign  ih_mr_ie_wr_cnt_dec = ih_te_wr_valid & (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E) & ~te_ih_retry & te_ih_wr_combine;

always @ (posedge co_ih_clk or negedge core_ddrc_rstn) begin
   if(~core_ddrc_rstn) begin
      ih_mr_ie_wr_cnt_dec_vct_r <= {NO_OF_BWT{1'b0}};
   end else if(ddrc_cg_en) begin
      if(ih_mr_ie_wr_cnt_dec) begin
         for(i=0; i<NO_OF_BWT; i=i+1)
            ih_mr_ie_wr_cnt_dec_vct_r[i] <= (i==ih_te_ie_bwt) ? 1'b1 : 1'b0;
      end else begin
         ih_mr_ie_wr_cnt_dec_vct_r <= {NO_OF_BWT{1'b0}};
      end
   end
end
assign ih_mr_ie_wr_cnt_dec_vct = ih_mr_ie_wr_cnt_dec_vct_r;

assign  is_wecc_cmd              = (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW) ? 1'b1 : 1'b0;
assign  is_recc_cmd              = (ih_te_ie_rd_type == `IE_RD_TYPE_RE_B) ? 1'b1 : 1'b0;
assign  ih_ppl_te_ie_block_num   = ie_block_num;

reg  [NO_OF_BT-1:0] btt_mask;
wire push_wr_wdeorwebw;
wire pop_wr_webw;

assign push_wr_wdeorwebw = ((ih_ppl_te_ie_wr_type == `IE_WR_TYPE_WD_E || ih_ppl_te_ie_wr_type == `IE_WR_TYPE_WE_BW) && ih_ppl_te_wr_valid == 1'b1 && !te_ppl_ih_stall) ? 1'b1 : 1'b0;

assign pop_wr_webw = (ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW && ih_te_wr_valid == 1'b1 && !te_ih_retry) ? 1'b1: 1'b0;

always @(posedge co_ih_clk or negedge core_ddrc_rstn)
begin
   if(!core_ddrc_rstn) begin
        btt_mask<={NO_OF_BT{1'b0}};
   end else if(ddrc_cg_en) begin
      for(int i=0;i<NO_OF_BT;i=i+1) begin
        if(ih_ppl_te_ie_bt==ih_te_ie_bt) begin
           if(push_wr_wdeorwebw & ($unsigned(i)==ih_ppl_te_ie_bt[BT_BITS-1:0]))
                btt_mask[i]<=1'b1;
           else if(pop_wr_webw & ($unsigned(i)==ih_te_ie_bt[BT_BITS-1:0]))
                btt_mask[i]<=1'b0;
        end
        else begin
           if(pop_wr_webw & ($unsigned(i)==ih_te_ie_bt[BT_BITS-1:0]))
              btt_mask[i]<=1'b0;
           if(push_wr_wdeorwebw & ($unsigned(i)==ih_ppl_te_ie_bt[BT_BITS-1:0]))
              btt_mask[i]<=1'b1;
        end
      end
   end
end

assign ih_te_ie_btt_vct = ~btt_mask & ih_te_ie_btt_vct_ctl;

//------------------------------------------------------------------
// ECC region remap
//------------------------------------------------------------------
reg  [CORE_ADDR_WIDTH-1:0]     inv_addr;
reg  [CORE_ADDR_WIDTH-1:0]     shift_inv_addr_all;
reg  [CORE_ADDR_WIDTH-1:0]     shift_inv_addr_part;
wire [CORE_ADDR_WIDTH-1:0]     hif_cmd_addr_remap_all;
wire [CORE_ADDR_WIDTH-1:0]     hif_cmd_addr_remap_part;
wire [CORE_ADDR_WIDTH-1:0]     hif_cmd_addr_remap;

wire remap_en;
wire remap_part_ecc_region;
wire [5:0] bits_offset;
wire [1:0] granu;
wire       hif_addr_granu_a1;

//for DDR4/LPDDR4, Col9 is highest column address, and C[9:7] map to highest 3 HIF address.
//for DDR3/LPDDR3, Col11/10/9 could be highest column address.
//for LPDDR2, Col11/10/9/8/7/6 could be highest column address. don't support this case.

assign highest_col_num    =
                            dh_ih_addrmap_col_b10 != 5'h1F ? 4'd10 : 
                            dh_ih_addrmap_col_b9  != 5'h1F ? 4'd9 : 
                                                             4'd8;

wire [1:0] am_column_base_shift = 2'd0;
wire [5:0] col4_bit= `UMCTL2_AM_COLUMN_BASE+4+dh_ih_addrmap_col_b4;
assign bits_offset = col4_bit;

assign highest_col_bit    =
                            dh_ih_addrmap_col_b10 != 5'h1F ? `UMCTL2_AM_COLUMN_BASE+10+dh_ih_addrmap_col_b10-am_column_base_shift:
                            dh_ih_addrmap_col_b9  != 5'h1F ? `UMCTL2_AM_COLUMN_BASE+9 +dh_ih_addrmap_col_b9 -am_column_base_shift:
                                                             `UMCTL2_AM_COLUMN_BASE+8 +dh_ih_addrmap_col_b8 -am_column_base_shift;
assign granu       = reg_ddrc_ecc_region_map_granu;

assign remap_en    = (reg_ddrc_ecc_region_remap_en ==1'b1) & (reg_ddrc_ecc_mode!=3'b0) & (reg_ddrc_ecc_type==1'b1);
assign remap_part_ecc_region = reg_ddrc_ecc_region_map_granu !=2'b00 & reg_ddrc_ecc_region_map == 7'b0000001 & reg_ddrc_ecc_region_map_other == 1'b0;


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(highest_col_bit - 8)' found in module 'ih'
//SJ: This coding style is acceptable and there is no plan to change it.
always @ *
begin
    for(i=0; i<CORE_ADDR_WIDTH; i=i+1)
       if(i>=highest_col_bit-8 && i<=highest_col_bit-3) begin //shift for the remain
          inv_addr[i] = ~hif_cmd_addr[i];
       end else begin
          inv_addr[i] = hif_cmd_addr[i];
       end
end
//spyglass enable_block SelfDeterminedExpr-ML

localparam ADDR_IDX = `UMCTL_LOG2(CORE_ADDR_WIDTH);
localparam CORE_ADDR_WIDTH_EXTEND = 2**(ADDR_IDX);
wire  [ADDR_IDX-1:0] highest_col_index5;
wire  [ADDR_IDX-1:0] highest_col_index4;
wire  [ADDR_IDX-1:0] highest_col_index3;
wire  [ADDR_IDX-1:0] highest_col_index;
wire [CORE_ADDR_WIDTH_EXTEND-1:0] inv_addr_tmp;
wire [CORE_ADDR_WIDTH_EXTEND-1:0] hif_cmd_addr_tmp;
//CORE_ADDR_WIDTH_EXTEND >= CORE_ADDR_WIDTH
generate
  if(CORE_ADDR_WIDTH_EXTEND == CORE_ADDR_WIDTH) begin:CORE_ADDR_WIDTH_pow2
assign inv_addr_tmp     = inv_addr;
assign hif_cmd_addr_tmp = hif_cmd_addr;
  end else begin:CORE_ADDR_WIDTH_pow2
assign inv_addr_tmp     = {{(CORE_ADDR_WIDTH_EXTEND-CORE_ADDR_WIDTH){1'b0}},inv_addr};
assign hif_cmd_addr_tmp = {{(CORE_ADDR_WIDTH_EXTEND-CORE_ADDR_WIDTH){1'b0}},hif_cmd_addr};
  end
endgenerate

assign highest_col_index5 = ADDR_IDX < 6 ? (highest_col_bit[ADDR_IDX-1:0]-5) : (highest_col_bit-5+{ADDR_IDX{1'b0}});
assign highest_col_index4 = ADDR_IDX < 6 ? (highest_col_bit[ADDR_IDX-1:0]-4) : (highest_col_bit-4+{ADDR_IDX{1'b0}});
assign highest_col_index3 = ADDR_IDX < 6 ? (highest_col_bit[ADDR_IDX-1:0]-3) : (highest_col_bit-3+{ADDR_IDX{1'b0}});
assign highest_col_index  = ADDR_IDX < 6 ?  highest_col_bit[ADDR_IDX-1:0]    : (highest_col_bit+{ADDR_IDX{1'b0}});


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(highest_col_bit - 5)' found in module 'ih'
//SJ: This coding style is acceptable and there is no plan to change it.
//
//Cyclic left shift 3bits within HIF[highest_col_bit-3 : bits_offset]
always @ *
begin
// use two for loop (0..2, 3..CORE_ADDR_WIDTH) to avoid below error.
//Illegal bit select. Index -3 for "inv_addr" is out of range [30:0] in expression: "inv_addr[(i - 3)]"
//the min value of bits_offset is 2, so bits_offset+1>=3.
    for(i=0; i<3; i=i+1)
       if (i==bits_offset) begin
          shift_inv_addr_all[i] = inv_addr_tmp[highest_col_index5];
       end else begin
          shift_inv_addr_all[i] = inv_addr[i];
       end

    for(i=3; i<CORE_ADDR_WIDTH; i=i+1)
       if (i==bits_offset) begin
          shift_inv_addr_all[i] = inv_addr_tmp[highest_col_index5];
       end else if (i==bits_offset+1) begin
          shift_inv_addr_all[i] = inv_addr_tmp[highest_col_index4];
       end else if (i==bits_offset+2) begin
          shift_inv_addr_all[i] = inv_addr_tmp[highest_col_index3];
       end else if(i>=bits_offset+3 && i<=highest_col_bit-3) begin //shift for the remain
          shift_inv_addr_all[i] = inv_addr[i-3];
       end else begin
          shift_inv_addr_all[i] = inv_addr[i];
       end
end

//Cyclic left shift 3bits within HIF[highest_col_bit-(3+granu) : bits_offset]
always @ *
begin
// use two for loop (0..2, 3..CORE_ADDR_WIDTH) to avoid below error.
//Illegal bit select. Index -3 for "inv_addr" is out of range [30:0] in expression: "inv_addr[(i - 3)]"
//the min value of bits_offset is 2, so bits_offset+1>=3.
    for(i=0; i<3; i=i+1)
       if (i==bits_offset) begin
          shift_inv_addr_part[i] = inv_addr_tmp[highest_col_index5-granu];
       end else begin
          shift_inv_addr_part[i] = inv_addr[i];
       end

    for(i=3; i<CORE_ADDR_WIDTH; i=i+1)
       if (i==bits_offset) begin
          shift_inv_addr_part[i] = inv_addr_tmp[highest_col_index5-granu];
       end else if (i==bits_offset+1) begin
          shift_inv_addr_part[i] = inv_addr_tmp[highest_col_index4-granu];
       end else if (i==bits_offset+2) begin
          shift_inv_addr_part[i] = inv_addr_tmp[highest_col_index3-granu];
       end else if (i>=bits_offset+3 && i<=highest_col_bit-(3+granu)) begin //shift for the remain
          shift_inv_addr_part[i] = inv_addr[i-3];
       end else begin
          shift_inv_addr_part[i] = inv_addr[i];
       end
end
//spyglass enable_block SelfDeterminedExpr-ML


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(highest_col_bit - 3)' found in module 'ih'
//SJ: This coding style is acceptable and there is no plan to change it.
assign hif_addr_granu_a1 = granu==2'b01 ? &hif_cmd_addr_tmp[highest_col_index3-:1] :
                           granu==2'b10 ? &hif_cmd_addr_tmp[highest_col_index3-:2] :
                           granu==2'b11 ? &hif_cmd_addr_tmp[highest_col_index3-:3] :
                                          1'b1;
//spyglass enable_block SelfDeterminedExpr-ML

assign hif_cmd_addr_remap_all  = &hif_cmd_addr_tmp[highest_col_index-:3] ? shift_inv_addr_all :  hif_cmd_addr;   //remap all the ECC region

assign hif_cmd_addr_remap_part = (&hif_cmd_addr_tmp[highest_col_index-:3] & hif_addr_granu_a1)  ? shift_inv_addr_part : 
                                  &hif_cmd_addr_tmp[highest_col_index-:3] ? inv_addr : 
                                                                      hif_cmd_addr ; //remap 1/2, 1/4, 1/8 ECC region. the remain ECC region still has address inversion.

assign hif_cmd_addr_remap = remap_en ? remap_part_ecc_region ? hif_cmd_addr_remap_part : hif_cmd_addr_remap_all : hif_cmd_addr;



assign ih_dh_stall = hif_cmd_stall;

// drive dual ih_te_rd*/ih_te_wr* outputs from single internal signals
// as both RD/WR are same for ih.v
assign ih_te_rd_rank_num = ih_te_rank_num;
assign ih_te_wr_rank_num = ih_te_rank_num;
assign ih_te_rd_bankgroup_num = ih_te_bankgroup_num;  
assign ih_te_wr_bankgroup_num = ih_te_bankgroup_num;
assign ih_te_rd_bg_bank_num = ih_te_bg_bank_num;
assign ih_te_wr_bg_bank_num = ih_te_bg_bank_num;
assign ih_te_rd_bank_num = ih_te_bank_num;
assign ih_te_wr_bank_num = ih_te_bank_num;
assign ih_te_rd_page_num = ih_te_page_num_corr;
assign ih_te_wr_page_num = ih_te_page_num_corr;
assign ih_te_rd_block_num = ih_te_block_num;
assign ih_te_wr_block_num = ih_te_block_num;
assign ih_te_rd_autopre = ih_te_autopre;
assign ih_te_wr_autopre = ih_te_autopre;
assign ih_te_rd_hi_pri  = ih_te_hi_pri;
assign ih_te_wr_hi_pri  = ih_te_hi_pri;
assign ih_te_rd_eccap   = ih_te_eccap;
assign ih_te_wr_eccap   = ih_te_eccap;

// There are 4 signals that contribute to this:
//
// (1) ih_in_busy:
//     - Signal goes high in the clock in which the input command valid arrives (hif_cmd_valid)
//     - In the next cycle, input_fifo_empty goes low and that keeps the ih_in_busy signal high
//
// (2) In the following cycle, the FIFO control empty signals go low and that will again keep ih_busy high
// This will go LOW only when all the FIFO's are empty (indicating no more cmds inside DDRC) and no new input cmd
//
// (3) ECC scrub requests are pending. When both the 'entry_avail' signals are high, it indicates both rd and wr scrub 
//     requests have been serviced
//
// (4) w_fifo_fill_level: this ensures that all write credits have been returned
//

assign  ih_busy         =    ih_in_busy
                          || (~ih_gs_rdhigh_empty)
                          || (~ih_gs_rdlow_empty) 
                          || (~ih_gs_wr_empty)
                          || (|wr_fifo_fill_level)
                          || (~ih_gs_wrecc_empty)
                          || (|wrecc_fifo_fill_level)
                          || (~ih_te_ppl_empty)
                           ;


// When OPT_TIMING is defined, the address map module is instantiated before the input flops
// Hence get the mapped_* group of signal on the RHS, instead of the rxcmd_addr_*
wire [CORE_ADDR_WIDTH-1:0] mapped_addr;
assign mapped_addr = (CORE_ADDR_WIDTH)'({
                               mapped_rank_num,
                               mapped_bg_bank_num,mapped_page_num,mapped_block_num,critical_dword
                          });
wire mapped_addr_eccap;
assign mapped_addr_eccap = (reg_ddrc_ecc_ap_en == 1'b0 
                           ) ? 1'b0 : // Disable this feature
                               (^mapped_rank_num) ^
                               (^mapped_bg_bank_num) ^ 
                               (^mapped_page_num) ^ 
                               (^mapped_block_num)   
                               ^ ( (reg_ddrc_burst_rdwr[3]==1'b0)? (critical_dword[3]) :  // for BL8, use col[3]
                                  1'b0) 
                           ; 


//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(((((3 + 4) + 18) + 9) + 3) - 1)' found in module 'ih'
//SJ: This coding style is acceptable and there is no plan to change it.

//--------------------
// This section uses the duplicate flops rxcmd_addr flop coming out of the input fifo
// The ih_yy_* signals are used to drive the BE, BS & PI modules
//--------------------

     assign ih_yy_rank_num   = rxcmd_addr_dup[`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:
                                              `MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS];

     assign ih_yy_bg_bank_num   = rxcmd_addr_dup[`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:
                                                 `MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS];

     assign ih_yy_page_num   = rxcmd_addr_dup[`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:
                                              `MEMC_BLK_BITS+`MEMC_WORD_BITS];


//--------------------
// This section allocates the rank, bank, page & block addresses when the address map
// is present externally (before the input fifo). rxcmd_addr is the output of the input_fifo
// These signals go to the ih_te_if module
//--------------------

  assign mapped_rank_num_to_te = rxcmd_addr[`UMCTL2_LRANK_BITS+`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:
                                            `MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS];

  assign mapped_bg_bank_num_to_te = rxcmd_addr[`MEMC_BG_BANK_BITS+`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:
                                              `MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS];

  assign mapped_page_num_to_te = rxcmd_addr[`MEMC_PAGE_BITS+`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:
                                            `MEMC_BLK_BITS+`MEMC_WORD_BITS];

  assign mapped_block_num_to_te = rxcmd_addr[`MEMC_BLK_BITS+`MEMC_WORD_BITS-1:`MEMC_WORD_BITS];

  assign critical_dword_to_te = rxcmd_addr[`MEMC_WORD_BITS-1:0];
  
  assign mapped_addr_eccap_to_te = rxcmd_addr_eccap;

//--------------------
// This section allocates the rank, bank, page & block addresses when the address map
// is present internally (after the input fifo). mapped_* signals are the outputs of the 
// address_map module. The mapped_*_to_te signals go to the ih_te_if module
//--------------------
//spyglass enable_block SelfDeterminedExpr-ML


      assign rxcmd_invalid_addr_row13_12 = ( (dh_ih_nonbinary_device_density == 3'b001) && (ih_ppl_te_page_num[13:12] == 2'b11)) ? 1'b1 : 1'b0;
      assign rxcmd_invalid_addr_row14_13 = ( (dh_ih_nonbinary_device_density == 3'b010) && (ih_ppl_te_page_num[14:13] == 2'b11)) ? 1'b1 : 1'b0;
      assign rxcmd_invalid_addr_row15_14 = ( (dh_ih_nonbinary_device_density == 3'b011) && (ih_ppl_te_page_num[15:14] == 2'b11)) ? 1'b1 : 1'b0;
      assign rxcmd_invalid_addr_row16_15 = ( (dh_ih_nonbinary_device_density == 3'b100) && (ih_ppl_te_page_num[16:15] == 2'b11)) ? 1'b1 : 1'b0;
      assign rxcmd_invalid_addr_row17_16 = ( (dh_ih_nonbinary_device_density == 3'b101) && (ih_ppl_te_page_num[17:16] == 2'b11)) ? 1'b1 : 1'b0;

      assign ih_ppl_te_page_num_corr[`MEMC_PAGE_BITS-1:12] =
                                                          rxcmd_invalid_addr_row13_12 ? {ih_ppl_te_page_num[`MEMC_PAGE_BITS-1:14],2'b10} :
                                                          rxcmd_invalid_addr_row14_13 ? {ih_ppl_te_page_num[`MEMC_PAGE_BITS-1:14],1'b0,ih_ppl_te_page_num[12]} :
                                                          rxcmd_invalid_addr_row15_14 ? {ih_ppl_te_page_num[`MEMC_PAGE_BITS-1:15],1'b0,ih_ppl_te_page_num[13:12]} :
                                                          rxcmd_invalid_addr_row16_15 ? {ih_ppl_te_page_num[`MEMC_PAGE_BITS-1:16],1'b0,ih_ppl_te_page_num[14:12]} :
                                                          rxcmd_invalid_addr_row17_16 ? {ih_ppl_te_page_num[`MEMC_PAGE_BITS-1:17],1'b0,ih_ppl_te_page_num[15:12]} :
                                                          ih_ppl_te_page_num[`MEMC_PAGE_BITS-1:12];

      assign ih_ppl_te_page_num_corr[11:0]                 = ih_ppl_te_page_num[11:0];
      assign ih_yy_page_num_corr[`MEMC_PAGE_BITS-1:12] =
                                                          rxcmd_invalid_addr_row13_12 ? {ih_yy_page_num[`MEMC_PAGE_BITS-1:14],2'b10} :
                                                          rxcmd_invalid_addr_row14_13 ? {ih_yy_page_num[`MEMC_PAGE_BITS-1:14],1'b0,ih_yy_page_num[12]} :
                                                          rxcmd_invalid_addr_row15_14 ? {ih_yy_page_num[`MEMC_PAGE_BITS-1:15],1'b0,ih_yy_page_num[13:12]} :
                                                          rxcmd_invalid_addr_row16_15 ? {ih_yy_page_num[`MEMC_PAGE_BITS-1:16],1'b0,ih_yy_page_num[14:12]} :
                                                          rxcmd_invalid_addr_row17_16 ? {ih_yy_page_num[`MEMC_PAGE_BITS-1:17],1'b0,ih_yy_page_num[15:12]} :
                                                          ih_yy_page_num[`MEMC_PAGE_BITS-1:12];

      assign ih_yy_page_num_corr[11:0]                 = ih_yy_page_num[11:0];

      assign rxcmd_invalid_addr_nonbinary = rxcmd_invalid_addr_row13_12 || rxcmd_invalid_addr_row14_13 || rxcmd_invalid_addr_row15_14 || rxcmd_invalid_addr_row16_15 || rxcmd_invalid_addr_row17_16
                                             ;
      assign rxcmd_invalid_addr = rxcmd_invalid_addr_nonbinary
                                  ;
                                  

// ccx_cond:;;10; Redundant for now. 8B mode is not supported.
assign bg_b16_addr_mode = reg_ddrc_lpddr5 && (reg_ddrc_bank_org != {{($bits(reg_ddrc_bank_org)-1){1'b0}},1'b1});


localparam RXCMD_SRC_WIDTH = `DDRCTL_SRC_WIDTH;
wire  [RXCMD_SRC_WIDTH-1:0] rxcmd_rmw_src;
assign rxcmd_rmw_src    = ppl_rxcmd_wdata_ptr[RXCMD_SRC_WIDTH-1:0];



ih_core_in_if
      #(
   .IE_FIFO_DATA_BITS   (IE_FIFO_DATA_BITS),
   .WRCMD_ENTRY_BITS    (WRCMD_ENTRY_BITS),
   .CORE_ADDR_WIDTH     (CORE_ADDR_WIDTH),
   .IH_TAG_WIDTH        (IH_TAG_WIDTH),
   .CMD_LEN_BITS        (CMD_LEN_BITS),
   .WDATA_PTR_BITS      (WDATA_PTR_BITS),
   .RD_LATENCY_BITS     (RD_LATENCY_BITS),
   .WR_LATENCY_BITS     (WR_LATENCY_BITS),
  .REFRESH_EN_BITS      (0),
  .WDATA_MASK_FULL_BITS (0),
  .HIF_KEYID_WIDTH      (HIF_KEYID_WIDTH),
  .CMD_TYPE_BITS        (CMD_TYPE_BITS) )

  ih_core_in_if(

  .co_ih_clk            (co_ih_clk),
  .core_ddrc_rstn       (core_ddrc_rstn),

  .hif_cmd_valid        (hif_cmd_valid),
  .hif_cmd_type         (hif_cmd_type),
  .hif_cmd_addr         (mapped_addr),
  .hif_cmd_token        (hif_cmd_token),
  .hif_cmd_pri          (hif_cmd_pri),
  .hif_cmd_length       (hif_cmd_length),
  .hif_cmd_wdata_ptr    (hif_cmd_wdata_ptr),
  .hif_cmd_autopre      (hif_cmd_autopre),
  .hif_cmd_latency      (hif_cmd_latency),
  .wu_ih_flow_cntrl_req (wu_ih_flow_cntrl_req),
  .input_fifo_full      (input_fifo_full),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in ih_assertions module and under different `ifdefs.
  .input_fifo_empty     (input_fifo_empty),
//spyglass enable_block W528
  .ih_in_busy           (ih_in_busy),
  .hif_cmd_stall       (hif_cmd_stall),
  .te_ih_retry         (te_ih_core_in_stall),
  .ih_fifo_rd_empty    (ih_fifo_rd_empty),
  .ih_fifo_wr_empty    (ih_fifo_wr_empty),
  .input_fifo_din_ie   (input_fifo_din_ie ),
  .input_fifo_dout_ie  (input_fifo_dout_ie),
  .mapped_addr_eccap   (mapped_addr_eccap),
  .rxcmd_addr_eccap    (rxcmd_addr_eccap),


  .rxcmd_addr_dup      (rxcmd_addr_dup),

  .rxcmd_valid         (rxcmd_valid),
  .rxcmd_addr          (rxcmd_addr),
  .rxcmd_type          (rxcmd_type),
  .rxcmd_token         (rxcmd_token),
  .rxcmd_autopre       (rxcmd_autopre),
  .rxcmd_pri           (rxcmd_pri),
  .rxcmd_length        (rxcmd_length),
   .rxcmd_rd_latency   (rxcmd_rd_latency),
   .ih_gs_any_vpr_timed_out (ih_ppl_gs_any_vpr_timed_out),
   .rxcmd_wr_latency   (rxcmd_wr_latency),
   .ih_gs_any_vpw_timed_out (ih_ppl_gs_any_vpw_timed_out),
  .rxcmd_wdata_ptr     (ppl_rxcmd_wdata_ptr),  //to ih-te pipeline
  .reg_ddrc_ecc_type   (reg_ddrc_ecc_type)
  );


ih_core_out_if
      #(
  .RDCMD_ENTRY_BITS    (RDCMD_ENTRY_BITS),
  .WRCMD_ENTRY_BITS    (WRCMD_ENTRY_BITS),
  .WRECCCMD_ENTRY_BITS (WRECCCMD_ENTRY_BITS),
  .RMW_TYPE_BITS       (RMW_TYPE_BITS),
  .WDATA_PTR_BITS      (WDATA_PTR_BITS),
  .CMD_TYPE_BITS       (CMD_TYPE_BITS)   )

  ih_core_out_if(

  .co_ih_clk                (co_ih_clk),
  .core_ddrc_rstn           (core_ddrc_rstn),

  .rxcmd_wdata_ptr          (rxcmd_wdata_ptr),   //from ih-te pipeline 
  .ih_te_rd_valid           (ih_te_rd_valid),
  .ih_te_wr_valid           (ih_te_wr_valid),
  .ih_te_wr_valid_addr_err  (ih_te_wr_valid_addr_err),
  .ih_te_hi_pri             (ih_te_hi_pri_int),
  .te_ih_rd_retry           (te_ih_retry),
  .te_ih_wr_retry           (te_ih_retry),
  .wr_fifo_fill_level       (wr_fifo_fill_level),
  .lpr_fifo_fill_level      (lpr_fifo_fill_level),
  .hpr_fifo_fill_level      (hpr_fifo_fill_level),
  .wrecc_fifo_fill_level    (wrecc_fifo_fill_level),
  .is_wecc_cmd              (is_wecc_cmd),  
  .dh_ih_dis_hif            (dh_ih_dis_hif),
  .dh_ih_lpr_num_entries    (dh_ih_lpr_num_entries),
  .hif_wrecc_credit            (hif_wrecc_credit[0]),


  .input_fifo_full_rd       (input_fifo_full),
  .input_fifo_full_wr       (input_fifo_full),
  .gsfsm_sr_co_if_stall     (gsfsm_sr_co_if_stall),
  .hif_rcmd_stall           (hif_rcmd_stall),
  .hif_wcmd_stall           (hif_wcmd_stall),
  .hif_wdata_ptr            (hif_wdata_ptr),
  .hif_wdata_ptr_valid      (hif_wdata_ptr_valid),
  .hif_wdata_ptr_addr_err   (hif_wdata_ptr_addr_err),
  .hif_lpr_credit           (hif_lpr_credit[0]),
  .hif_hpr_credit           (hif_hpr_credit[0]),
  .hif_wr_credit            (hif_wr_credit),
  .co_ih_lpr_num_entries_changed   (co_ih_lpr_num_entries_changed)
  );




ih_address_map_wrapper
 
       #(
                .AM_DCH_WIDTH           (AM_DCH_WIDTH     )
               ,.AM_CS_WIDTH            (AM_CS_WIDTH      )
               ,.AM_CID_WIDTH           (AM_CID_WIDTH     )
               ,.AM_BANK_WIDTH          (AM_BANK_WIDTH    )
               ,.AM_BG_WIDTH            (AM_BG_WIDTH      )
               ,.AM_ROW_WIDTH           (AM_ROW_WIDTH     )
               ,.AM_COL_WIDTH_H         (AM_COL_WIDTH_H   )
               ,.AM_COL_WIDTH_L         (AM_COL_WIDTH_L   )
        )
  ih_address_map_wrapper
        (
        .bg_b16_addr_mode               (bg_b16_addr_mode),
        .am_block                       (mapped_block_num),
        .am_critical_dword              (critical_dword),
        .am_row                         (mapped_page_num),
        .am_bg_bank                     (mapped_bg_bank_num),
        .am_rank                        (mapped_rank_num),

        .am_cpu_address                 (hif_cmd_addr_remap[`MEMC_HIF_ADDR_WIDTH-1:0]),

        .am_cs_offset_bit0              (dh_ih_addrmap_rank_b0),
        .am_bs_offset_bit0              (dh_ih_addrmap_bank_b0),
        .am_bs_offset_bit1              (dh_ih_addrmap_bank_b1),
        .am_bs_offset_bit2              (dh_ih_addrmap_bank_b2),
        .am_bg_offset_bit0              (dh_ih_addrmap_bg_b0),
        .am_bg_offset_bit1              (dh_ih_addrmap_bg_b1),
        .am_row_offset_bit0             (dh_ih_addrmap_row_b0),
        .am_row_offset_bit1             (dh_ih_addrmap_row_b1),
        .am_row_offset_bit2             (dh_ih_addrmap_row_b2),
        .am_row_offset_bit3             (dh_ih_addrmap_row_b3),
        .am_row_offset_bit4             (dh_ih_addrmap_row_b4),
        .am_row_offset_bit5             (dh_ih_addrmap_row_b5),
        .am_row_offset_bit6             (dh_ih_addrmap_row_b6),
        .am_row_offset_bit7             (dh_ih_addrmap_row_b7),
        .am_row_offset_bit8             (dh_ih_addrmap_row_b8),
        .am_row_offset_bit9             (dh_ih_addrmap_row_b9),
        .am_row_offset_bit10            (dh_ih_addrmap_row_b10),
        .am_row_offset_bit11            (dh_ih_addrmap_row_b11),
        .am_row_offset_bit12            (dh_ih_addrmap_row_b12),
        .am_row_offset_bit13            (dh_ih_addrmap_row_b13),
        .am_row_offset_bit14            (dh_ih_addrmap_row_b14),
        .am_row_offset_bit15            (dh_ih_addrmap_row_b15),
        .am_row_offset_bit16            (dh_ih_addrmap_row_b16),
        .am_row_offset_bit17            (dh_ih_addrmap_row_b17),
        .am_column_offset_bit3          (dh_ih_addrmap_col_b3),
        .am_column_offset_bit4          (dh_ih_addrmap_col_b4),
        .am_column_offset_bit5          (dh_ih_addrmap_col_b5),
        .am_column_offset_bit6          (dh_ih_addrmap_col_b6),
        .am_column_offset_bit7          (dh_ih_addrmap_col_b7),
        .am_column_offset_bit8          (dh_ih_addrmap_col_b8),
        .am_column_offset_bit9          (dh_ih_addrmap_col_b9),
        .am_column_offset_bit10         (dh_ih_addrmap_col_b10)


//I/O for het rank mapping
       ,.reg_ddrc_lpddr5                             (reg_ddrc_lpddr5                          ) 
       ,.reg_ddrc_bank_hash_en                       (reg_ddrc_bank_hash_en                    )
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
        ,.co_ih_clk                                  (co_ih_clk                                )
        ,.core_ddrc_rstn                             (core_ddrc_rstn                           )
        ,.cmd_valid                                  (hif_cmd_valid                            )
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON
);

ih_te_if
      #(
  .IH_TAG_WIDTH      (IH_TAG_WIDTH),
  .CMD_LEN_BITS      (CMD_LEN_BITS),
  .RMW_TYPE_BITS     (RMW_TYPE_BITS),
  .RD_LATENCY_BITS   (RD_LATENCY_BITS),
  .WR_LATENCY_BITS   (WR_LATENCY_BITS),
  .RXCMD_SRC_WIDTH  (RXCMD_SRC_WIDTH),
  .CMD_TYPE_BITS     (CMD_TYPE_BITS)    )

  ih_te_if (

  .bg_b16_addr_mode               (bg_b16_addr_mode),
  .reg_ddrc_ecc_type              (reg_ddrc_ecc_type),

  // from core_if
  .rxcmd_valid                    (rxcmd_valid),
  .rxcmd_type                     (rxcmd_type),
  .rxcmd_token                    (rxcmd_token),
  .rxcmd_autopre                  (rxcmd_autopre),
  .rxcmd_pri                      (rxcmd_pri),
  .rxcmd_rd_latency               (rxcmd_rd_latency),
  .rxcmd_wr_latency               (rxcmd_wr_latency),
  .rxcmd_length                   (rxcmd_length),
  .rxcmd_invalid_addr             (rxcmd_invalid_addr),

  // Address from address_map module
  .am_rank                        (mapped_rank_num_to_te[`UMCTL2_LRANK_BITS-1:0]),
  .am_bg_bank                     (mapped_bg_bank_num_to_te[`MEMC_BG_BANK_BITS-1:0]),
  .am_row                         (mapped_page_num_to_te[`MEMC_PAGE_BITS-1:0]),
  .am_block                       (mapped_block_num_to_te),
  .am_critical_dword              (critical_dword_to_te),
  .am_eccap                       (mapped_addr_eccap_to_te),

  .rxcmd_rmw_src        (rxcmd_rmw_src),

  .ie_cmd_active            (ie_cmd_active ),
  .ecc_region_invalid       (ecc_region_invalid),
  .rxcmd_ptc_vld            (rxcmd_ptc_vld),
  .ie_rd_vld                (ie_rd_vld),
  .ie_wr_vld                (ie_wr_vld),
  .ie_rd_length             (ie_rd_length),
  .ie_rd_tag                (ie_rd_tag), 
  .ie_rmwtype               (ie_rmwtype),
  .ie_hi_pri                (ie_hi_pri),
  .ie_autopre               (ie_autopre),
  .ie_rank_num              (ie_rank_num),
  .ie_bg_bank_num           (ie_bg_bank_num),
  .ie_block_num             (ie_block_num),
  .ie_page_num              (ie_page_num),
  .ie_critical_dword        (ie_critical_dword),
  // outputs for TE
  .ih_te_rd_valid       (ih_ppl_te_rd_valid),   
  .ih_te_wr_valid       (ih_ppl_te_wr_valid),   
  .ih_wu_wr_valid       (ih_ppl_wu_wr_valid),   
  .ih_te_rd_valid_addr_err (ih_ppl_te_rd_valid_addr_err),  
  .ih_te_wr_valid_addr_err (ih_ppl_te_wr_valid_addr_err),  
  .ih_te_rd_length      (ih_ppl_te_rd_length),  
  .ih_te_rd_tag         (ih_ppl_te_rd_tag),     
  .ih_te_rmwtype        (ih_ppl_te_rmwtype),    
  .ih_te_hi_pri         (ih_ppl_te_hi_pri),     
  .ih_te_hi_pri_int     (ih_ppl_te_hi_pri_int), 

  .ih_te_rd_latency     (ih_ppl_te_rd_latency), 
  .ih_te_wr_latency     (ih_ppl_te_wr_latency), 
  .ih_te_autopre        (ih_ppl_te_autopre),    
  .ih_te_eccap          (ih_ppl_te_eccap),      
  .ih_te_rank_num       (ih_ppl_te_rank_num), 
  .ih_te_bankgroup_num  (ih_ppl_te_bankgroup_num),
  .ih_te_bg_bank_num    (ih_ppl_te_bg_bank_num), 
  .ih_te_bank_num       (ih_ppl_te_bank_num), 
  .ih_te_page_num       (ih_ppl_te_page_num), 
  .ih_te_block_num      (ih_ppl_te_block_num), 
  .ih_te_critical_dword (ih_ppl_te_critical_dword),
  .ih_wu_critical_dword (ih_ppl_wu_critical_dword)
);


ih_be_if
  ih_be_if (

  // from core_if
  .ih_te_rd_valid           (ih_te_rd_valid),
  .ih_te_hi_pri             (ih_te_hi_pri),

   .te_gs_any_vpr_timed_out (te_gs_any_vpr_timed_out),
   .ih_gs_any_vpr_timed_out (ih_gs_any_vpr_timed_out),


  // outputs for BE
  .ih_be_hi_pri_rd_xact     (ih_be_hi_pri_rd_xact)
  );






        assign ih_be_rank_num_rd    = ih_yy_rank_num;
        assign ih_be_bg_bank_num_rd = ih_yy_bg_bank_num;
////        `ifndef MEMC_LPDDR3
////        assign ih_be_page_num   = ih_yy_page_num;
////        `else
        assign ih_be_page_num       = ih_yy_page_num_corr;
////        `endif






// for BE, some come from wr
      assign ih_be_rank_num_wr   = ih_te_wr_rank_num;
      assign ih_be_bg_bank_num_wr= ih_te_wr_bg_bank_num;

ih_fifo_if
  #(
  .RDCMD_ENTRY_BITS    (RDCMD_ENTRY_BITS),
  .WRCMD_ENTRY_BITS    (WRCMD_ENTRY_BITS),
  .WRECCCMD_ENTRY_BITS (WRECCCMD_ENTRY_BITS),
  .WRCMD_ENTRY_BITS_IE (WRCMD_ENTRY_BITS_IE),
  .RMW_TYPE_BITS       (RMW_TYPE_BITS) )    
  
  ih_fifo_if (

  .co_ih_clk                (co_ih_clk),
  .core_ddrc_rstn           (core_ddrc_rstn),
  // inputs from te_if
  .rd_valid                 (ih_te_rd_valid),
  .wr_valid                 (ih_te_wr_valid),
        .rd_valid_addr_err              (ih_te_rd_valid_addr_err),
        .wr_valid_addr_err              (ih_te_wr_valid_addr_err),
        .rmwtype                        (ih_te_rmwtype),
  .pri                      (ih_te_hi_pri_int),
  .rd_entry                 (ih_te_rd_entry),
  .wr_entry                 (ih_te_wr_entry),
  .lo_rd_prefer             (ih_te_lo_rd_prefer),
  .wr_prefer                (ih_te_wr_prefer),
  .hi_rd_prefer             (ih_te_hi_rd_prefer),
  .wrecc_prefer             (ih_te_wrecc_prefer),

  .rd_retry                 (te_ih_retry),
  .wr_retry                 (te_ih_retry),
  .wr_combine               (te_ih_wr_combine),

  
  .free_rd_entry            (te_ih_free_rd_entry),
  .free_rd_entry_valid      (te_ih_free_rd_entry_valid),
  .free_wr_entry            (mr_ih_free_wr_entry),
  .free_wr_entry_valid      (mr_ih_free_wr_entry_valid),
  .wr_cam_full              (wr_cam_full ),
  .lpr_cam_empty            (lpr_cam_empty),
  .hpr_cam_empty            (hpr_cam_empty),
  .wr_cam_empty             (wr_cam_empty),
  .wrecc_cam_empty          (wrecc_cam_empty),
  .wrecc_cam_full           (wrecc_cam_full),
  .lpr_cam_full             (lpr_cam_full),
  .hpr_cam_full             (hpr_cam_full),
// TS Interface
  .any_xact                 (ih_yy_xact_valid),
  .rdlow_empty              (ih_gs_rdlow_empty),
  .wr_empty                 (ih_gs_wr_empty),
  .rdhigh_empty             (ih_gs_rdhigh_empty),
  .wrecc_empty              (ih_gs_wrecc_empty),
  .lpr_fifo_fill_level      (lpr_fifo_fill_level),
  .hpr_fifo_fill_level      (hpr_fifo_fill_level),
  .wr_fifo_fill_level       (wr_fifo_fill_level),
  .wrecc_fifo_fill_level    (wrecc_fifo_fill_level),


  .dh_ih_lpr_num_entries    (dh_ih_lpr_num_entries),
  .is_wecc_cmd              (is_wecc_cmd),
  .ih_dh_wrecc_q_depth      (ih_dh_wrecc_q_depth),

  .ih_dh_lpr_q_depth        (ih_dh_lpr_q_depth),
  .ih_dh_hpr_q_depth        (ih_dh_hpr_q_depth),
  .ih_dh_wr_q_depth         (ih_dh_wr_q_depth)
);


ih_ie_cmd_ctl

#(
    .HIF_ADDR_WIDTH   (`MEMC_HIF_ADDR_WIDTH)
   ,.CORE_ADDR_WIDTH  (CORE_ADDR_WIDTH)
   ,.IH_TAG_WIDTH     (IH_TAG_WIDTH)    // width of token/tag field from core
   ,.CMD_LEN_BITS     (CMD_LEN_BITS)    // bits for command length, when used
   ,.RMW_TYPE_BITS    (RMW_TYPE_BITS)
   ,.WDATA_PTR_BITS   (WDATA_PTR_BITS)
   ,.CMD_TYPE_BITS    (CMD_TYPE_BITS)    
   ,.WRDATA_CYCLES    (WRDATA_CYCLES)

   ,.BT_BITS          (BT_BITS)    
   ,.BWT_BITS         (BWT_BITS)    
   ,.BRT_BITS         (BRT_BITS)    
   ,.NO_OF_BT         (NO_OF_BT)    
   ,.NO_OF_BWT        (NO_OF_BWT)    
   ,.NO_OF_BRT        (NO_OF_BRT)    
   ,.NO_OF_BLK_CHN    (NO_OF_BLK_CHN)
   ,.BLK_CHN_BITS     (BLK_CHN_BITS)
   ,.IE_RD_TYPE_BITS  (IE_RD_TYPE_BITS)
   ,.IE_WR_TYPE_BITS  (IE_WR_TYPE_BITS)
   ,.IE_CMD_BITS      (IE_CMD_BITS      )
   ,.ECC_HOLE_BITS    (ECC_HOLE_BITS    )
   ,.IE_MASK_FULL_BITS(IE_MASK_FULL_BITS)
   ,.IE_BURST_NUM_BITS(IE_BURST_NUM_BITS)
   ,.IE_FIFO_DATA_BITS(IE_FIFO_DATA_BITS)

   ,.MWR_BITS             (MWR_BITS)
   ,.PARTIAL_WR_BITS      (PARTIAL_WR_BITS) 
   ,.PARTIAL_WR_BITS_LOG2 (PARTIAL_WR_BITS_LOG2)
   ,.PW_WORD_CNT_WD_MAX   (PW_WORD_CNT_WD_MAX) 

)
ih_ie_cmd_ctl
(  
    .core_ddrc_core_clk             (co_ih_clk)
   ,.core_ddrc_rstn                 (core_ddrc_rstn)
   ,.ddrc_cg_en                     (ddrc_cg_en)
   // register 
   ,.reg_ddrc_nonbinary_device_density (dh_ih_nonbinary_device_density)
   ,.reg_ddrc_ecc_type              (reg_ddrc_ecc_type)
   ,.reg_ddrc_ecc_mode              (reg_ddrc_ecc_mode)
   ,.reg_ddrc_ecc_region_map        (reg_ddrc_ecc_region_map)
   ,.reg_ddrc_ecc_region_map_granu  (reg_ddrc_ecc_region_map_granu)
   ,.reg_ddrc_ecc_region_map_other  (reg_ddrc_ecc_region_map_other)
   ,.reg_ddrc_ecc_region_parity_lock(reg_ddrc_ecc_region_parity_lock)
   ,.reg_ddrc_ecc_region_waste_lock (reg_ddrc_ecc_region_waste_lock)
   ,.reg_ddrc_blk_channel_idle_time_x32      (reg_ddrc_blk_channel_idle_time_x32)
   ,.reg_ddrc_active_blk_channel    (reg_ddrc_active_blk_channel)
   ,.reg_ddrc_blk_channel_active_term (reg_ddrc_blk_channel_active_term)
   ,.reg_ddrc_burst_rdwr            (reg_ddrc_burst_rdwr)  
   ,.dh_ih_dis_hif                  (dh_ih_dis_hif)
   ,.gsfsm_sr_co_if_stall           (gsfsm_sr_co_if_stall)
   ,.reg_ddrc_selfref_sw            (reg_ddrc_selfref_sw)
   ,.highest_col_bit                (highest_col_bit          )// the bit in hif address for the highest column address.
   ,.highest_col_num                (highest_col_num          )// the number of column address.

   // HIF Interface
   ,.hif_cmd_valid            (hif_cmd_valid) // valid command
   ,.hif_cmd_length           (hif_cmd_length)
   ,.hif_cmd_type             (hif_cmd_type) // command type:
                                                              //  00 - block write
                                                              //  01 - read
                                                              //  10 - rmw
                                                              //  11 - reserved
   ,.hif_cmd_addr             ( hif_cmd_addr_remap) // address
   ,.hif_cmd_ecc_region       ( hif_cmd_ecc_region     ) // HIF BLK sideband signal, 
   ,.hif_cmd_wdata_mask_full  (hif_cmd_wdata_mask_full_ie) // HIF BLK sideband signal,
   ,.hif_lpr_credit_ie        (hif_lpr_credit[1])
   ,.hif_hpr_credit_ie        (hif_hpr_credit[1])
   ,.hif_wrecc_credit_ie      (hif_wrecc_credit[1])
 

   // mapped dram address before input FIFO
   ,.mapped_block_num_b4_inpff     (mapped_block_num)
   ,.mapped_critical_dword_b4_inpff(critical_dword)
   ,.mapped_page_num_b4_inpff      (mapped_page_num)
   // Received command after input FIFO
   ,.rxcmd_valid              (rxcmd_valid)
   ,.rxcmd_type               (rxcmd_type)
   ,.rxcmd_pri                (rxcmd_pri)
   ,.rxcmd_autopre            (rxcmd_autopre)
   ,.mapped_page_num          (mapped_page_num_to_te)
   ,.mapped_rank_num          (mapped_rank_num_to_te)
   ,.mapped_bg_bank_num       (mapped_bg_bank_num_to_te)
   ,.mapped_block_num         (mapped_block_num_to_te)
   ,.mapped_critical_dword    (critical_dword_to_te)
   // Mapped address from address_map module
   ,.lpr_cam_empty            (lpr_cam_empty )
   ,.lpr_cam_full             (lpr_cam_full )
   ,.hpr_cam_empty            (hpr_cam_empty )
   ,.hpr_cam_full             (hpr_cam_full )
   ,.wr_cam_empty             (wr_cam_empty )
   ,.wr_cam_full              (wr_cam_full )
   ,.wrecc_cam_empty          (wrecc_cam_empty )
   ,.wrecc_cam_full           (wrecc_cam_full )
   ,.input_fifo_empty         (input_fifo_empty)
   //
   ,.te_ih_re_done_i          (te_ih_re_done_i)
   ,.te_ih_re_done_bt         (te_ih_re_done_bt)
   ,.te_ih_retry              (te_ppl_ih_stall)
   ,.te_ih_retry_ie_cmd       (te_ih_retry_ie_cmd)
   // INPUT FIFO EXTRA DATA
   ,.input_fifo_din_ie        (input_fifo_din_ie)
   ,.input_fifo_dout_ie       (input_fifo_dout_ie)
   ,.ie_cmd_active            (ie_cmd_active )
   ,.ecc_region_invalid       (ecc_region_invalid)
   ,.rxcmd_ptc_vld            (rxcmd_ptc_vld)
   // output to TE after Mux with IH_TE_IF
   ,.ie_rd_vld                (ie_rd_vld) 
   ,.ie_wr_vld                (ie_wr_vld) 
   ,.ie_rd_length             (ie_rd_length)
   ,.ie_rd_tag                (ie_rd_tag   )
   ,.ie_rmwtype               (ie_rmwtype  )
   ,.ie_hi_pri                (ie_hi_pri   )
   ,.ie_autopre               (ie_autopre)
   ,.ie_rank_num              (ie_rank_num)
   ,.ie_bg_bank_num           (ie_bg_bank_num)
   ,.ie_block_num             (ie_block_num)
   ,.ie_page_num              (ie_page_num)
   ,.ie_critical_dword        (ie_critical_dword)
   //output for both ECC and Data command
   ,.ih_te_ie_bt              (ih_ppl_te_ie_bt              )   
   ,.ih_te_ie_bwt             (ih_ppl_te_ie_bwt             )   
   ,.ih_te_ie_rd_type         (ih_ppl_te_ie_rd_type         ) 
   ,.ih_te_ie_wr_type         (ih_ppl_te_ie_wr_type         ) 
   ,.ih_te_ie_blk_burst_num   (ih_ppl_te_ie_blk_burst_num   ) //only for the Data command
   ,.ih_te_mwr                (ih_ppl_te_mwr)
   ,.reg_ddrc_frequency_ratio (reg_ddrc_frequency_ratio)
   ,.ih_te_wr_word_valid      (ih_ppl_te_wr_word_valid)
   ,.ih_te_wr_ram_raddr_lsb_first (ih_ppl_te_wr_ram_raddr_lsb_first)
   ,.ih_te_wr_pw_num_beats_m1     (ih_ppl_te_wr_pw_num_beats_m1)
   ,.ih_te_wr_pw_num_cols_m1      (ih_ppl_te_wr_pw_num_cols_m1)
   //Token manager
   ,.mr_ih_free_bwt_vld       (mr_ih_free_bwt_vld       )
   ,.mr_ih_free_bwt           (mr_ih_free_bwt           )
   ,.rd_ih_free_brt_vld       (rd_ih_free_brt_vld       )
   ,.rd_ih_free_brt           (rd_ih_free_brt           )

   ,.ih_rd_ie_brt             (ih_rd_ie_brt             ) 
   ,.ih_rd_ie_rd_cnt_inc      (ih_rd_ie_rd_cnt_inc      )
   ,.ih_rd_ie_blk_rd_end      (ih_rd_ie_blk_rd_end      )
   ,.ih_mr_ie_bwt             (ih_mr_ie_bwt             ) 
   ,.ih_mr_ie_brt             (ih_mr_ie_brt             ) 
   ,.ih_mr_ie_brt_vld         (ih_mr_ie_brt_vld         ) 
   ,.ih_mr_ie_wr_cnt_inc      (ih_mr_ie_wr_cnt_inc      )
   ,.ih_mr_ie_blk_wr_end      (ih_mr_ie_blk_wr_end      )

   ,.ih_ie_empty              (ih_ie_empty              )
   ,.ih_ie_busy               (ih_ie_busy               )
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in RTL assertion (ih_assertions)
   ,.assert_ie_cmd             (assert_ie_cmd             )
   ,.assert_ie_cmd_invalid_addr(assert_ie_cmd_invalid_addr)
   ,.assert_dis_dm             (assert_dis_dm             )
//spyglass enable_block W528

   //signals for BTT and RDECC_RDY
   ,.rd_ih_ie_re_rdy     (rd_ih_ie_re_rdy)
   ,.ie_re_vct           (ih_te_ie_re_vct)
   ,.ie_btt_vct          (ih_te_ie_btt_vct_ctl)
   //signals for look up BT table
   ,.mr_ih_lkp_bwt_by_bt(mr_ih_lkp_bwt_by_bt)
   ,.mr_ih_lkp_brt_by_bt(mr_ih_lkp_brt_by_bt)
   ,.rd_ih_lkp_brt_by_bt(rd_ih_lkp_brt_by_bt)
   ,.rd_ih_lkp_bwt_by_bt(rd_ih_lkp_bwt_by_bt)
   ,.ih_mr_lkp_bwt      (ih_mr_lkp_bwt      )   
   ,.ih_mr_lkp_bwt_vld  (ih_mr_lkp_bwt_vld  )
   ,.ih_mr_lkp_brt      (ih_mr_lkp_brt      )   
   ,.ih_mr_lkp_brt_vld  (ih_mr_lkp_brt_vld  )
   ,.ih_rd_lkp_brt      (ih_rd_lkp_brt      )   
   ,.ih_rd_lkp_brt_vld  (ih_rd_lkp_brt_vld  )
   ,.ih_rd_lkp_bwt      (ih_rd_lkp_bwt      )   
   ,.ih_rd_lkp_bwt_vld  (ih_rd_lkp_bwt_vld  )
);


ih_te_pipeline
 #(
     .CMD_LEN_BITS   (CMD_LEN_BITS)
    ,.IH_TAG_WIDTH   (IH_TAG_WIDTH)
    ,.RMW_TYPE_BITS  (RMW_TYPE_BITS)
    ,.WDATA_PTR_BITS (WDATA_PTR_BITS)
    ,.RD_LATENCY_BITS   (RD_LATENCY_BITS)
    ,.WR_LATENCY_BITS   (WR_LATENCY_BITS)
    ,.BT_BITS              (BT_BITS)
    ,.BWT_BITS             (BWT_BITS)
    ,.IE_RD_TYPE_BITS      (IE_RD_TYPE_BITS)
    ,.IE_WR_TYPE_BITS      (IE_WR_TYPE_BITS)
    ,.IE_BURST_NUM_BITS    (IE_BURST_NUM_BITS)
    ,.MWR_BITS             (MWR_BITS)
    ,.PARTIAL_WR_BITS      (PARTIAL_WR_BITS)
    ,.PARTIAL_WR_BITS_LOG2 (PARTIAL_WR_BITS_LOG2)
    ,.PW_WORD_CNT_WD_MAX   (PW_WORD_CNT_WD_MAX)
    ,.HIF_KEYID_WIDTH      (HIF_KEYID_WIDTH)

)
ih_te_pipeline(

   .te_ih_retry              (te_ih_retry)
  ,.co_ih_clk                (co_ih_clk)
  ,.core_ddrc_rstn           (core_ddrc_rstn)
  ,.ddrc_cg_en               (ddrc_cg_en)
  ,.wu_ih_flow_cntrl_req     (wu_ih_flow_cntrl_req)
   //control signal of pipeline
  ,.ih_te_ppl_empty          (ih_te_ppl_empty)
  ,.ih_te_ppl_wr_empty       (ih_te_ppl_wr_empty)
  ,.ih_te_ppl_rd_empty       (ih_te_ppl_rd_empty)
  ,.te_ppl_ih_stall          (te_ppl_ih_stall)


  ,.reg_ddrc_ecc_type        (reg_ddrc_ecc_type)

   //data out of pipeline
  ,.rxcmd_wdata_ptr      (rxcmd_wdata_ptr)
  ,.ih_te_rd_valid       (i_ih_te_rd_valid)   
  ,.ih_te_wr_valid       (i_ih_te_wr_valid)   
  ,.ih_wu_wr_valid       (i_ih_wu_wr_valid)   
  ,.ih_te_rd_valid_addr_err (i_ih_te_rd_valid_addr_err)  
  ,.ih_te_wr_valid_addr_err (i_ih_te_wr_valid_addr_err)  
  ,.ih_te_rd_length      (i_ih_te_rd_length)  
  ,.ih_te_rd_tag         (i_ih_te_rd_tag)     
  ,.ih_te_rmwtype        (i_ih_te_rmwtype)    
  ,.ih_te_hi_pri         (i_ih_te_hi_pri)     
  ,.ih_te_hi_pri_int     (i_ih_te_hi_pri_int) 

  ,.ih_te_rd_latency     (i_ih_te_rd_latency) 
  ,.ih_gs_any_vpr_timed_out (ih_gs_any_vpr_timed_out)
  ,.ih_te_wr_latency     (i_ih_te_wr_latency) 
  ,.ih_gs_any_vpw_timed_out (ih_gs_any_vpw_timed_out)
  ,.ih_te_autopre        (i_ih_te_autopre)    
  ,.ih_te_eccap          (ih_te_eccap)      
  ,.ih_te_rank_num       (i_ih_te_rank_num) 
  ,.ih_te_bankgroup_num  (i_ih_te_bankgroup_num)
  ,.ih_te_bg_bank_num    (i_ih_te_bg_bank_num) 
  ,.ih_te_bank_num       (i_ih_te_bank_num) 
  ,.ih_te_page_num       (i_ih_te_page_num_corr) 
  ,.ih_te_block_num      (i_ih_te_block_num) 
  ,.ih_te_critical_dword (i_ih_te_critical_dword)
  ,.ih_wu_critical_dword (i_ih_wu_critical_dword)
  ,.ih_te_ie_bt           (ih_te_ie_bt              )   
  ,.ih_te_ie_bwt          (ih_te_ie_bwt             )   
  ,.ih_te_ie_rd_type      (ih_te_ie_rd_type         ) 
  ,.ih_te_ie_wr_type      (ih_te_ie_wr_type         ) 
  ,.ih_te_ie_blk_burst_num(ih_te_ie_blk_burst_num   ) //only for the Data command
  ,.ih_te_ie_block_num    (ih_te_ie_block_num       )

  ,.ih_te_mwr                (ih_te_mwr)
  ,.ih_te_wr_word_valid      (ih_te_wr_word_valid)
  ,.ih_te_wr_ram_raddr_lsb_first (ih_te_wr_ram_raddr_lsb_first)
  ,.ih_te_wr_pw_num_beats_m1     (ih_te_wr_pw_num_beats_m1)
  ,.ih_te_wr_pw_num_cols_m1      (ih_te_wr_pw_num_cols_m1)

   //data in of pipeline
  ,.ppl_rxcmd_wdata_ptr      (ppl_rxcmd_wdata_ptr)
  ,.ih_ppl_te_rd_valid       (ih_ppl_te_rd_valid)   
  ,.ih_ppl_te_wr_valid       (ih_ppl_te_wr_valid)   
  ,.ih_ppl_wu_wr_valid       (ih_ppl_wu_wr_valid)   
  ,.ih_ppl_te_rd_valid_addr_err (ih_ppl_te_rd_valid_addr_err)  
  ,.ih_ppl_te_wr_valid_addr_err (ih_ppl_te_wr_valid_addr_err)  
  ,.ih_ppl_te_rd_length      (ih_ppl_te_rd_length)  
  ,.ih_ppl_te_rd_tag         (ih_ppl_te_rd_tag)     
  ,.ih_ppl_te_rmwtype        (ih_ppl_te_rmwtype)    
  ,.ih_ppl_te_hi_pri         (ih_ppl_te_hi_pri)     
  ,.ih_ppl_te_hi_pri_int     (ih_ppl_te_hi_pri_int) 

  ,.ih_ppl_te_rd_latency     (ih_ppl_te_rd_latency) 
  ,.ih_ppl_gs_any_vpr_timed_out (ih_ppl_gs_any_vpr_timed_out) 
  ,.ih_ppl_te_wr_latency     (ih_ppl_te_wr_latency) 
  ,.ih_ppl_gs_any_vpw_timed_out (ih_ppl_gs_any_vpw_timed_out) 
  ,.ih_ppl_te_autopre        (ih_ppl_te_autopre)    
  ,.ih_ppl_te_eccap          (ih_ppl_te_eccap)      
  ,.ih_ppl_te_rank_num       (ih_ppl_te_rank_num) 
  ,.ih_ppl_te_bankgroup_num  (ih_ppl_te_bankgroup_num)
  ,.ih_ppl_te_bg_bank_num    (ih_ppl_te_bg_bank_num) 
  ,.ih_ppl_te_bank_num       (ih_ppl_te_bank_num) 
  ,.ih_ppl_te_page_num       (ih_ppl_te_page_num_corr) 
  ,.ih_ppl_te_block_num      (ih_ppl_te_block_num) 
  ,.ih_ppl_te_critical_dword (ih_ppl_te_critical_dword)
  ,.ih_ppl_wu_critical_dword (ih_ppl_wu_critical_dword)

  ,.ih_ppl_te_ie_bt           (ih_ppl_te_ie_bt              )   
  ,.ih_ppl_te_ie_bwt          (ih_ppl_te_ie_bwt             )   
  ,.ih_ppl_te_ie_rd_type      (ih_ppl_te_ie_rd_type         ) 
  ,.ih_ppl_te_ie_wr_type      (ih_ppl_te_ie_wr_type         ) 
  ,.ih_ppl_te_ie_blk_burst_num(ih_ppl_te_ie_blk_burst_num   ) //only for the Data command
  ,.ih_ppl_te_ie_block_num    (ih_ppl_te_ie_block_num       )

  ,.ih_ppl_te_mwr                (ih_ppl_te_mwr)
  ,.ih_ppl_te_wr_word_valid      (ih_ppl_te_wr_word_valid)
  ,.ih_ppl_te_wr_ram_raddr_lsb_first (ih_ppl_te_wr_ram_raddr_lsb_first)
  ,.ih_ppl_te_wr_pw_num_beats_m1     (ih_ppl_te_wr_pw_num_beats_m1)
  ,.ih_ppl_te_wr_pw_num_cols_m1      (ih_ppl_te_wr_pw_num_cols_m1)

);

ih_retry_mux
 #(
    //------------------------------ PARAMETERS ------------------------------------
      .RMW_TYPE_BITS (RMW_TYPE_BITS)
//fdef DDRCTL_ANY_RETRY
     ,.RETRY_TIMES_WIDTH (RETRY_TIMES_WIDTH)
//`ifdef DDRCTL_RD_CRC_RETRY
     ,.CMD_LEN_BITS      (CMD_LEN_BITS)
     ,.IH_TAG_WIDTH      (IH_TAG_WIDTH)
     ,.RD_LATENCY_BITS   (`UMCTL2_XPI_RQOS_TW)
     ,.WR_LATENCY_BITS   (`UMCTL2_XPI_WQOS_TW)
     ,.HIF_KEYID_WIDTH   (HIF_KEYID_WIDTH)
//`endif
//`endif
    ) u_ih_retry_mux
    (
    //-------------------------- INPUTS AND OUTPUTS --------------------------------  
   //data out of pipeline
   .ih_te_rd_valid      (ih_te_rd_valid)
  ,.ih_te_wr_valid      (ih_te_wr_valid)
  ,.ih_wu_wr_valid      (ih_wu_wr_valid)
  ,.ih_te_rmwtype       (ih_te_rmwtype)    
  ,.ih_te_wr_valid_addr_err   (ih_te_wr_valid_addr_err)
  ,.ih_te_rd_valid_addr_err   (ih_te_rd_valid_addr_err)
  ,.ih_te_hi_pri        (ih_te_hi_pri)
  ,.ih_te_hi_pri_int    (ih_te_hi_pri_int)
  ,.ih_te_rd_latency    (ih_te_rd_latency) 
  ,.ih_te_wr_latency    (ih_te_wr_latency) 
  ,.ih_te_autopre       (ih_te_autopre)   // auto precharge enable flag
  ,.ih_te_rank_num      (ih_te_rank_num)
  ,.ih_te_bankgroup_num  (ih_te_bankgroup_num)
  ,.ih_te_bg_bank_num    (ih_te_bg_bank_num   ) 
  ,.ih_te_bank_num       (ih_te_bank_num      ) 
  ,.ih_te_page_num       (ih_te_page_num_corr ) 
  ,.ih_te_block_num      (ih_te_block_num     ) 
  ,.ih_te_critical_dword (ih_te_critical_dword)      // for reads only, critical word within a block - not currently supported
  ,.ih_wu_critical_dword (ih_wu_critical_dword)      // for reads only, critical word within a block - not currently supported
  ,.ih_te_wr_entry_rmw   (ih_te_wr_entry_rmw  )
  ,.ih_te_rd_length      (ih_te_rd_length     )
  ,.ih_te_rd_tag         (ih_te_rd_tag        )

   //data in from IH
  ,.i_ih_te_rd_valid     (i_ih_te_rd_valid)
  ,.i_ih_te_wr_valid     (i_ih_te_wr_valid)
  ,.i_ih_wu_wr_valid     (i_ih_wu_wr_valid)
  ,.i_ih_te_rmwtype      (i_ih_te_rmwtype)    
  ,.i_ih_te_wr_valid_addr_err (i_ih_te_wr_valid_addr_err)
  ,.i_ih_te_rd_valid_addr_err (i_ih_te_rd_valid_addr_err)
  ,.i_ih_te_hi_pri       (i_ih_te_hi_pri)
  ,.i_ih_te_hi_pri_int   (i_ih_te_hi_pri_int)
  ,.i_ih_te_rd_latency   (i_ih_te_rd_latency) 
  ,.i_ih_te_wr_latency   (i_ih_te_wr_latency) 
  ,.i_ih_te_autopre      (i_ih_te_autopre)    // auto precharge enable flag
  ,.i_ih_te_rank_num     (i_ih_te_rank_num)
  ,.i_ih_te_bankgroup_num(i_ih_te_bankgroup_num)
  ,.i_ih_te_bg_bank_num       (i_ih_te_bg_bank_num    )
  ,.i_ih_te_bank_num          (i_ih_te_bank_num       )
  ,.i_ih_te_page_num          (i_ih_te_page_num_corr  )
  ,.i_ih_te_block_num         (i_ih_te_block_num      )
  ,.i_ih_te_critical_dword    (i_ih_te_critical_dword )  // for reads only, critical word within a block - not currently supported
  ,.i_ih_wu_critical_dword    (i_ih_wu_critical_dword )  // for reads only, critical word within a block - not currently supported
  ,.i_ih_te_wr_entry          (ih_te_wr_entry[WRCMD_ENTRY_BITS-1:0]) // used to generate ih_te_wr_entry_rmw
  ,.i_ih_te_rd_length         (i_ih_te_rd_length      )
  ,.i_ih_te_rd_tag            (i_ih_te_rd_tag         )

);




`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

ih_assertions
  #(
  .RDCMD_ENTRY_BITS    (RDCMD_ENTRY_BITS),
  .WRCMD_ENTRY_BITS    (WRCMD_ENTRY_BITS_IE),
  .CORE_ADDR_WIDTH     (CORE_ADDR_WIDTH),
  .IH_TAG_WIDTH        (IH_TAG_WIDTH),
  .CMD_LEN_BITS        (CMD_LEN_BITS),
  .RMW_TYPE_BITS       (RMW_TYPE_BITS),
  .WDATA_PTR_BITS      (WDATA_PTR_BITS),
  .CMD_TYPE_BITS       (CMD_TYPE_BITS)
  ,.BT_BITS            (BT_BITS)
  ,.BWT_BITS           (BWT_BITS)
  ,.BRT_BITS           (BRT_BITS)
  ,.NO_OF_BT           (NO_OF_BT) 
  ,.IE_BURST_NUM_BITS  (IE_BURST_NUM_BITS) 
)

  ih_assertions(

        .co_ih_clk                      (co_ih_clk),
        .core_ddrc_rstn                 (core_ddrc_rstn),

        .dh_ih_operating_mode           (dh_ih_operating_mode),
        .hif_cmd_valid                  (hif_cmd_valid),
        .hif_cmd_type                   (hif_cmd_type),
        .hif_cmd_addr                   (hif_cmd_addr_remap),
        .hif_cmd_token                  (hif_cmd_token),
        .hif_cmd_pri                    (hif_cmd_pri),
        .hif_cmd_length                 (hif_cmd_length),
        .hif_cmd_wdata_ptr              (hif_cmd_wdata_ptr),
        .hif_cmd_ecc_region             (hif_cmd_ecc_region),
        .hif_cmd_wdata_mask_full        (hif_cmd_wdata_mask_full_ie), // HIF BLK sideband signal,
        .hif_cmd_latency                (hif_cmd_latency),

        .hif_cmd_stall                  (hif_cmd_stall),
        .hif_wdata_ptr                  (hif_wdata_ptr),
        .hif_wdata_ptr_valid            (hif_wdata_ptr_valid),
        .hif_lpr_credit                 (hif_lpr_credit),
        .hif_hpr_credit                 (hif_hpr_credit),
        .hif_wr_credit                  (hif_wr_credit),
        .hif_wrecc_credit               (hif_wrecc_credit),
        .dh_ih_blk_channel_active_term  (reg_ddrc_blk_channel_active_term),

        // WU Interface
        .wu_ih_flow_cntrl_req           (wu_ih_flow_cntrl_req),

        // outputs for TE
        .ih_te_rd_valid                 (ih_te_rd_valid),
        .ih_te_wr_valid                 (ih_te_wr_valid),
        .ih_te_ie_rd_type               (ih_te_ie_rd_type),
        .ih_te_ie_wr_type               (ih_te_ie_wr_type),
        .ih_te_ie_bt                    (ih_te_ie_bt),
        .ih_te_ie_blk_burst_num         (ih_te_ie_blk_burst_num),
        .free_bt_vld                    (ih_ie_cmd_ctl.free_bt_vld),
        .free_bt                        (ih_ie_cmd_ctl.free_bt),
        .ih_te_ie_btt_vct               (ih_te_ie_btt_vct),
        .ih_te_rd_valid_addr_err        (ih_te_rd_valid_addr_err),
        .ih_te_wr_valid_addr_err        (ih_te_wr_valid_addr_err),
        .ih_te_rd_latency               (ih_te_rd_latency),
        .ih_te_rd_length                (ih_te_rd_length),
        .ih_te_rd_tag                   (ih_te_rd_tag),
        .ih_te_rmwtype                  (ih_te_rmwtype),
        .ih_te_rank_num                 (ih_te_rank_num),
        .ih_te_bg_bank_num              (ih_te_bg_bank_num),
        .ih_te_page_num                 (ih_te_page_num_corr),
        .ih_te_block_num                (ih_te_block_num),
        .ih_te_critical_dword           (ih_te_critical_dword),
        .ih_te_rd_entry                 (ih_te_rd_entry),
        .ih_te_wr_entry                 (ih_te_wr_entry),
        .ih_te_lo_rd_prefer             (ih_te_lo_rd_prefer),
        .ih_te_wr_prefer                (ih_te_wr_prefer),

        .ih_te_hi_pri                   (ih_te_hi_pri),
        .ih_te_hi_rd_prefer             (ih_te_hi_rd_prefer),

        .ih_gs_rdhigh_empty             (ih_gs_rdhigh_empty),
        .ih_be_hi_pri_rd_xact           (ih_be_hi_pri_rd_xact),
        .dh_ih_lpr_num_entries          (dh_ih_lpr_num_entries),

        .ih_be_rank_num                 (ih_be_rank_num_rd),
        .ih_be_bg_bank_num              (ih_be_bg_bank_num_rd),
        .ih_be_page_num                 (ih_be_page_num),

        .te_ih_free_rd_entry            (te_ih_free_rd_entry),
        .te_ih_free_rd_entry_valid      (te_ih_free_rd_entry_valid),
        .mr_ih_free_wr_entry            (mr_ih_free_wr_entry),
        .mr_ih_free_wr_entry_valid      (mr_ih_free_wr_entry_valid),
        .te_ih_retry                    (te_ih_retry),
        .te_ih_retry_i                  (te_ih_retry_i),
        .te_ih_core_in_stall            (te_ih_core_in_stall),
        .te_ih_wr_combine               (te_ih_wr_combine)
       ,.assert_ie_cmd                  (assert_ie_cmd             )
       ,.assert_ie_cmd_invalid_addr     (assert_ie_cmd_invalid_addr)
       ,.assert_dis_dm                  (assert_dis_dm             )
       ,.ih_te_rd_eccap                 (ih_te_rd_eccap)
       ,.ih_te_wr_eccap                 (ih_te_wr_eccap)
       ,.reg_ddrc_ecc_ap_en             (reg_ddrc_ecc_ap_en)
       ,.input_fifo_empty               (input_fifo_empty)
       ,.ih_te_fifo_empty               (ih_te_ppl_empty)
       ,.reg_ddrc_ecc_type              (reg_ddrc_ecc_type)
);

   property ih_te_ie_btt_vct_mask;
      @(posedge co_ih_clk) disable iff(~core_ddrc_rstn)
         ih_te_wr_valid == 1'b1 && (ih_te_ie_wr_type == `IE_WR_TYPE_WD_E || ih_te_ie_wr_type == `IE_WR_TYPE_WE_BW) && (!te_ih_retry) |-> ih_te_ie_btt_vct[ih_te_ie_bt]==1'b0;
   endproperty 
   assert_ih_te_ie_btt_vct_mask: assert property(ih_te_ie_btt_vct_mask);

   property ih_te_wde_webw;
      @(posedge co_ih_clk) disable iff(~core_ddrc_rstn)
         ih_ppl_te_ie_wr_type == `IE_WR_TYPE_WD_E && ih_ppl_te_wr_valid==1'b1 && (!te_ppl_ih_stall)  ##1 !te_ppl_ih_stall |-> ih_ppl_te_wr_valid==1'b1 && ih_ppl_te_ie_wr_type==`IE_WR_TYPE_WE_BW;
   endproperty
   assert_ih_te_wde_webw: assert property(ih_te_wde_webw);

`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

endmodule
