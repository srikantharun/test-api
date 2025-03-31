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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/rd/rd.sv#13 $
// -------------------------------------------------------------------------
// Description:
//===========================================================================
//
//                Read Data (RD) unit.  This block is responsible for handling
//                all ECC checking and correcting on read response data.
//                Data is then passed to the write update engine and the
//                response assembler.  This block is fully combinatorial.
//                All outputs from this block are qualified by a valid
//                indicator from the response tracker. 
//
//                Supports 64-bit core data bus width (1-lane ECC)
//                PHY-DDRC data width is 80-bits - this contains 64-bits data, 8-bit SECDED ECC, and 8 dummy bits
//                Dummy bits are removed before giving the data to the ECC decode engine
//
//===========================================================================
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module rd 
import DWC_ddrctl_reg_pkg::*;
#(
    parameter CMD_LEN_BITS        = 1
   ,parameter PHY_DATA_WIDTH      = 288                  // width of data to/from PHY (2x the DQ bus)
   ,parameter PHY_DBI_WIDTH       = 18                   // width of data mask bits from the PHY
   ,parameter CORE_DATA_WIDTH     = 256                  // data width to/from core logic
   ,parameter CORE_METADATA_WIDTH     = `DDRCTL_HIF_METADATA_WIDTH                                                                                                                                                                                                                                                                                          
   ,parameter RMW_TYPE_BITS       = 2                    // 2-bit read-modify-write type.  See ddrc_parameters.v for encodings
   ,parameter RA_INFO_WIDTH       = 47                   // width of bits from RT to be passed through to RA
   ,parameter ECC_INFO_WIDTH      = 35                   // width of read info from RT to be passed
   ,parameter CRC_INFO_WIDTH      = 35                   // width of read info from RT to be passed

   ,parameter WU_INFO_WIDTH       = 47                   // width of bits from RT to be passed through to WU
  
   ,parameter NO_OF_BRT           = 16 // Override
   ,parameter BWT_BITS            = 4 // Override
   ,parameter IE_RD_TYPE_BITS     = `IE_RD_TYPE_BITS     // Override
   ,parameter IE_WR_TYPE_BITS     = `IE_WR_TYPE_BITS     // Override
   ,parameter IE_BURST_NUM_BITS   = 3
   ,parameter ECC_ERR_RAM_DEPTH     = 16
   ,parameter ECC_ERR_RAM_ADDR_BITS = `log2(ECC_ERR_RAM_DEPTH)
   ,parameter BT_BITS             = 4 // Override
   ,parameter BRT_BITS            = 4 // Override
   ,parameter ECC_RAM_DEPTH         = `MEMC_ECC_RAM_DEPTH
   ,parameter ECC_RAM_ADDR_BITS     = `log2(ECC_RAM_DEPTH)
   ,parameter ECC_ERR_RAM_WIDTH      = 16 //MEMC_WRDATA_CYCLES*SECDED_LANES;
   ,parameter ECCAP_TH_WIDTH      = 4
   
   ,parameter OCPAR_EN            = 0
   ,parameter CORE_MASK_WIDTH     = `MEMC_DFI_DATA_WIDTH/8
   
   ,parameter OCECC_EN            = 0
   ,parameter OCECC_XPI_RD_GRANU  = 64
   ,parameter OCECC_MR_RD_GRANU   = 8
   ,parameter OCECC_MR_BNUM_WIDTH = 5
   ,parameter UMCTL2_WDATARAM_PAR_DW = 40
   
   ,parameter RANK_BITS           = `MEMC_RANK_BITS
   ,parameter LRANK_BITS          = `UMCTL2_LRANK_BITS
   ,parameter CID_WIDTH           = `UMCTL2_CID_WIDTH
   ,parameter BG_BITS             = `MEMC_BG_BITS
   ,parameter BANK_BITS           = `MEMC_BANK_BITS
   ,parameter BG_BANK_BITS        = `MEMC_BG_BANK_BITS
   ,parameter ROW_BITS            = `MEMC_PAGE_BITS
   ,parameter WORD_BITS           = `MEMC_WORD_BITS      // address a word within a burst
   ,parameter BLK_BITS            = `MEMC_BLK_BITS       // 2 column bits are critical word
   ,parameter COL_BITS            = WORD_BITS + BLK_BITS
   
   ,parameter CORE_ECC_WIDTH      = `MEMC_DFI_ECC_WIDTH

   ,parameter SECDED_1B_LANE_WIDTH    = `MEMC_ECC_SYNDROME_WIDTH_RD    // width of a single SEC/DED lane
                                                   // (that is one single-error-correcting / double-error-detecting unit)
   ,parameter ECC_LANE_WIDTH_1B       = `MEMC_SECDED_ECC_WIDTH_BITS  // # of error-correction bits
   ,parameter SECDED_CORESIDE_LANE_WIDTH = `MEMC_DRAM_DATA_WIDTH//width of SECDED lane after error correction
   ,parameter SECDED_LANES            = `MEMC_DFI_TOTAL_DATA_WIDTH / SECDED_1B_LANE_WIDTH
   ,parameter ECC_BITS                = SECDED_LANES*ECC_LANE_WIDTH_1B         // width of all ECC bits

   // widths used for some outputs of rd that would be
   // [X-1:0]=>[-1:0]
   // wide otherwise as X=0 sometimes
   ,parameter       RANK_BITS_DUP   = (RANK_BITS==0)       ? 1 : RANK_BITS
   ,parameter       BG_BITS_DUP     = (BG_BITS==0)         ? 1 : BG_BITS
   ,parameter       CID_WIDTH_DUP   = (CID_WIDTH==0)       ? 1 : CID_WIDTH
   ,parameter       CORE_ECC_WIDTH_DUP = (CORE_ECC_WIDTH==0)  ? 1 : CORE_ECC_WIDTH



   ,parameter       SECDED_LANES_DUP = (SECDED_LANES==0) ? 1 : SECDED_LANES

   ,parameter       RD_IE_PAR_ERR_PIPELINE = 0
   ,parameter       MAX_NUM_NIBBLES = 18
   ,parameter       DRAM_BYTE_NUM   = `MEMC_DRAM_TOTAL_BYTE_NUM
   ,parameter       DDRCTL_A_NPORTS_LG2    = `UMCTL2_A_NPORTS_LG2
   ,parameter       DDRCTL_INT_NPORTS_DATA = `UMCTL2_INT_NPORTS_DATA 
   ,parameter      RSD_KBD_WIDTH = 1
   ,parameter       DDRCTL_IME_DP_WIDTH     = `MEMC_DRAM_DATA_WIDTH*2*`MEMC_FREQ_RATIO
   ,parameter       DDRCTL_IME_OFFSET_WIDTH = (DDRCTL_IME_DP_WIDTH==256)? 1 : (DDRCTL_IME_DP_WIDTH==128)? 2 : 1
   ,parameter       DDRCTL_IME_LENGTH_WIDTH = DDRCTL_IME_OFFSET_WIDTH
)
(
    input                           co_yy_clk              // 1X clock
   ,input                           core_ddrc_rstn         // active low reset
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in SVA file and under certain configs
   ,input                           ddrc_cg_en             // clock gating enable
   ,input                           dh_rd_frequency_ratio  // Frequency ratio
//spyglass enable_block W240
   ,input  [1:0]                    dh_rd_data_bus_width   // Data bus width:
                                                            //  00: full data bus
                                                            //  01: 1/2 data bus
                                                            //  10: 1/4 data bus
                                                            //  11: RESERVED

   ,input   [BURST_RDWR_WIDTH-1:0]  reg_ddrc_burst_rdwr    
   ,input                           reg_ddrc_med_ecc_en      // 0: SECDED  1: MED
   ,input                           reg_ddrc_lpddr4
   ,input                           reg_ddrc_lpddr5
   ,input                           reg_ddrc_rd_link_ecc_enable
   ,input                           reg_ddrc_rd_link_ecc_uncorr_cnt_clr
   ,input                           reg_ddrc_rd_link_ecc_uncorr_intr_clr
   ,input                           reg_ddrc_rd_link_ecc_uncorr_intr_en
   ,input                           reg_ddrc_rd_link_ecc_corr_cnt_clr
   ,input                           reg_ddrc_rd_link_ecc_corr_intr_clr
   ,input                           reg_ddrc_rd_link_ecc_corr_intr_en
   ,input  [DRAM_BYTE_NUM-1:0]      reg_ddrc_linkecc_poison_byte_sel
   ,input                           reg_ddrc_linkecc_poison_rw
   ,input                           reg_ddrc_linkecc_poison_type
   ,input                           reg_ddrc_linkecc_poison_inject_en
   ,input  [ECC_INFO_WIDTH-1:0]     rt_rd_link_ecc_info // address, etc. from RT and provided to Link ECC registers
   ,input  [RD_LINK_ECC_ERR_RANK_SEL_WIDTH  -1:0] reg_ddrc_rd_link_ecc_err_rank_sel
   ,input  [RD_LINK_ECC_ERR_BYTE_SEL_WIDTH  -1:0] reg_ddrc_rd_link_ecc_err_byte_sel
   ,input  [PHY_DBI_WIDTH-1:0]      ph_rd_rdbi_n           // all bits read from DDR,
   ,input  [PHY_DATA_WIDTH-1:0]     ph_rd_rdata            // all bits read from DDR,
                                                            //  re-organized for ECC if SEC/DED mode
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
   ,input                           rt_rd_rd_valid         // valid read data from PHY
   ,input                           rt_rd_eod              // end of data from RT
   ,input  [CMD_LEN_BITS-1:0]       rt_rd_partial          // indicates that the current read is a non-block read
                                                            //  (for which RD may have to discard excess data)
   ,input  [RA_INFO_WIDTH-1:0]      rt_rd_ra_info          // address and RMW type from RT for RMW and ECC scrubs
   
   ,input                           rt_rd_rd_addr_err      // read address error flag
   
   ,input  [BT_BITS-1:0]            rt_rd_ie_bt
   ,input  [IE_RD_TYPE_BITS-1:0]    rt_rd_ie_rd_type
   ,input  [IE_BURST_NUM_BITS-1:0]  rt_rd_ie_blk_burst_num //only for the Data command
   ,input  [BRT_BITS-1:0]           ih_rd_ie_brt
   ,input                           ih_rd_ie_rd_cnt_inc
   ,input                           ih_rd_ie_blk_rd_end
 
   //ECC RAM/ACC interface   
   ,input  [CORE_DATA_WIDTH-1:0]    ecc_ram_rd_rdata
   ,input  [CORE_DATA_WIDTH-1:0]    ecc_acc_rd_rdata_2
   ,input  [CORE_MASK_WIDTH-1:0]    ecc_acc_rd_rdata_mask_n_2
// ECC ERR RAM interface
   ,input                               mr_ecc_err_rd
   ,input  [ECC_ERR_RAM_ADDR_BITS-1:0]  mr_ecc_err_raddr
 
   ,input  [BRT_BITS-1:0]           ih_rd_lkp_brt
   ,input  [BWT_BITS-1:0]           ih_rd_lkp_bwt
   ,input                           ih_rd_lkp_bwt_vld 

   ,output                          rd_ih_ie_re_rdy
   ,output                          rd_ih_free_brt_vld
   ,output [BRT_BITS-1:0]           rd_ih_free_brt

   ,output                          rd_ecc_ram_wr
   ,output [ECC_RAM_ADDR_BITS-1:0]  rd_ecc_ram_waddr
   ,output [CORE_DATA_WIDTH-1:0]    rd_ecc_ram_wdata
   ,output [CORE_MASK_WIDTH-1:0]    rd_ecc_ram_wdata_mask_n //should be all 1, no mask. 
   ,output [CORE_MASK_WIDTH-1:0]    rd_ecc_ram_wdata_par
   
   ,output [ECC_RAM_ADDR_BITS-1:0]  rd_ecc_ram_raddr
 
   ,output [ECC_RAM_ADDR_BITS-1:0]  rd_ecc_acc_raddr_2
 
   ,output [ECC_ERR_RAM_WIDTH-1:0]      ecc_err_mr_rdata

   ,output [BT_BITS-1:0]     rd_ih_lkp_bwt_by_bt
   ,output [BT_BITS-1:0]     rd_ih_lkp_brt_by_bt
 

   ,input                           rt_rd_eccap
   ,input                           reg_ddrc_ecc_ap_en
   ,input                           reg_ddrc_ecc_ap_err_intr_clr
   ,input  [ECCAP_TH_WIDTH-1:0]     reg_ddrc_ecc_ap_err_threshold
   ,output                          ddrc_reg_ecc_ap_err
   ,input                           reg_ddrc_phy_dbi_mode  // DBI implemented in DDRC or PHY
   ,input                           reg_ddrc_rd_dbi_en     // read DBI enable
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
   
   ,input                           reg_ddrc_ecc_type 
   ,input   [2:0]                   dh_rd_ecc_mode         // ECC mode:
   ,input   [ECC_INFO_WIDTH-1:0]    rt_rd_ecc_info             // address, etc. from RT and provided to ECC registers
   ,input   [WORD_BITS-1:0]         rt_rd_ecc_word             // address, etc. from RT and provided to ECC registers

                                                                              // 1 - correction, 0 - no correction
                                                                              // only data correction is indicated, no check bits
   ,input                           reg_ddrc_ecc_clr_corr_err      // Clear corrected error interrupt
   ,input                           reg_ddrc_ecc_clr_uncorr_err    // Clear uncorrected error interrupt
   
   ,input                           reg_ddrc_ecc_clr_corr_err_cnt  // Clear correctable ECC error count
   ,input                           reg_ddrc_ecc_clr_uncorr_err_cnt // Clear uncorrectable ECC error count
   
   ,output [`DDRCTL_HIF_DRAM_ADDR_WIDTH-1:0] rd_ra_dram_addr
   ,output                          rd_wu_ecc_corrected_err    // single-bit error that will be corrected, per lane
   ,output                          rd_wu_ecc_uncorrected_err  // double-bit error detected in read data, per lane
   ,output                          rd_ra_ecc_corrected_err   // correctable error indication, sync with rd_ra_rdata_valid
   ,output                          rd_ra_ecc_uncorrected_err // uncorrectable error indication, sync with rd_ra_rdata_valid

   ,output  [ECC_CORRECTED_ERR_WIDTH-1:0]        rd_dh_ecc_corrected_err   // single-bit error that will be corrected, per lane
   ,output  [ECC_UNCORRECTED_ERR_WIDTH-1:0]      rd_dh_ecc_uncorrected_err // double-bit error detected in read data, per lane
   ,output  [`MEMC_ECC_SYNDROME_WIDTH-1:0]  rd_dh_ecc_corr_syndromes   // data pattern that resulted in an error;
   ,output  [`MEMC_ECC_SYNDROME_WIDTH-1:0]  rd_dh_ecc_uncorr_syndromes // data pattern that resulted in an error;
   ,output  [6:0]                           rd_dh_ecc_corrected_bit_num// bit number corrected by single-bit error
   ,output  [`MEMC_ECC_SYNDROME_WIDTH-1:0]  rd_dh_ecc_corr_bit_mask   // mask for the bit that is corrected

   ,output  [15:0]                  ddrc_reg_ecc_corr_err_cnt      // Count of correctable ECC errors
   ,output  [15:0]                  ddrc_reg_ecc_uncorr_err_cnt    // Count of uncorrectable ECC errors

   ,output  [RANK_BITS_DUP-1:0]     rd_dh_ecc_corr_rank
   ,output  [RANK_BITS_DUP-1:0]     rd_dh_ecc_uncorr_rank
   
   ,output  [BANK_BITS-1:0]         rd_dh_ecc_corr_bank
   ,output  [BANK_BITS-1:0]         rd_dh_ecc_uncorr_bank
   
   ,output  [BG_BITS_DUP-1:0]       rd_dh_ecc_corr_bg
   ,output  [BG_BITS_DUP-1:0]       rd_dh_ecc_uncorr_bg
   
   
   ,output  [CID_WIDTH_DUP-1:0]     rd_dh_ecc_corr_cid
   ,output  [CID_WIDTH_DUP-1:0]     rd_dh_ecc_uncorr_cid
   
   ,output  [ROW_BITS-1:0]          rd_dh_ecc_corr_row
   ,output  [ROW_BITS-1:0]          rd_dh_ecc_uncorr_row
   ,output  [COL_BITS-1:0]          rd_dh_ecc_corr_col
   ,output  [COL_BITS-1:0]          rd_dh_ecc_uncorr_col

   ,output                                                         ddrc_reg_advecc_corrected_err
   ,output                                                         ddrc_reg_advecc_uncorrected_err
   ,output [ADVECC_NUM_ERR_SYMBOL_WIDTH-1:0] ddrc_reg_advecc_num_err_symbol
   ,output [ADVECC_ERR_SYMBOL_POS_WIDTH-1:0] ddrc_reg_advecc_err_symbol_pos
   ,output [ADVECC_ERR_SYMBOL_BITS_WIDTH-1:0] ddrc_reg_advecc_err_symbol_bits





   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_eighth
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_seventh
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_sixth
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_fifth
   
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_fourth
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_third
   
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_second
   ,output     [SECDED_LANES_DUP-1:0]   rd_wu_ecc_uncorrected_err_first

   ,output                              rd_wu_rd_crc_err

   ,output     [CORE_ECC_WIDTH_DUP-1:0] rd_ra_ecc_rdata           // ECC data going to the RA module and then to the production test logic

//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used in generate block
   ,input                           reg_ddrc_oc_parity_en // enables on-chip parity
   ,input                           reg_ddrc_par_poison_en // enable ocpar poison
   ,input                           reg_ddrc_par_poison_loc_rd_iecc_type
   ,input                           reg_ddrc_par_rdata_err_intr_clr
   ,input                           reg_ddrc_oc_parity_type // selects parity type. 0 even, 1 odd
//spyglass enable_block W240
   ,input                           reg_ddrc_read_data_parity_en // read data parity enable, needed with inline ECC
   ,output                          par_rdata_in_err_ecc_pulse
   
   ,input   [RMW_TYPE_BITS-1:0]        rt_rd_rmwtype          // 2-bit RMW type indicator.  See ddrc_parameters.v for encodings.
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
   ,input                              rt_rd_rmw_word_sel     // selects which word to return to RA
//spyglass enable_block W240
   ,input   [WU_INFO_WIDTH-1:0]        rt_rd_wu_info          // address and RMW type from RT for RMW and ECC scrubs
   ,output                             rd_wu_rdata_end        // end data out of this block
   ,output                             rd_wu_rdata_valid      // valid data out of this block
   ,output     [WU_INFO_WIDTH-1:0]     rd_wu_info             // address, RMW type, etc. from RT and provided to WU
   ,output                             rd_rw_rdata_valid      // valid data out of this block (to read-mod-write
   ,output     [CORE_DATA_WIDTH-1:0]   rd_rw_rdata            // read data in from IOLM, corrected for
   ,output     [UMCTL2_WDATARAM_PAR_DW-1:0]   rd_rw_rdata_par
   ,output     [WORD_BITS-1:0]         rd_wu_word_num         // start column address, etc. from RT and provided to wu
   ,output                             rd_wu_burst_chop_rd
   ,output     [CORE_METADATA_WIDTH-1:0]   rd_rw_rdata_meta            // read data in from IOLM, corrected for                                                                                                                                                                                                                                                                                                                                             
   ,output                             rd_wu_rd32_eobl16      // end of BL16 data of RD32 data
   ,output     [1:0]                   rd_wu_rdata_type       // read data type (0:RD16 data, 1:RD32 1st data, 2:RD32 2nd data)

   ,output                             rd_ra_rdata_valid      // valid data out of this block
   ,output     [CORE_DATA_WIDTH-1:0]   rd_ra_rdata            // read data in from IOLM, corrected for
   ,output     [CORE_MASK_WIDTH-1:0]   rd_ra_rdata_parity     // calculated parity for read data
   ,output                             rd_ra_eod              // end of data from RD
   ,output     [CMD_LEN_BITS-1:0]      rd_wu_partial          // partial read 
   ,output     [RA_INFO_WIDTH-1:0]     rd_ra_info             // tag, etc. from RT to be provided to RA for data return

   ,output     [CORE_METADATA_WIDTH-1:0]   rd_ra_rdata_meta            // read data in from IOLM, corrected for                                                                                                               
   ,output                             rd_ra_rdata_valid_retry //no-masked rdata valid to retry_ctrl
   ,output                             rd_wu_rdata_valid_retry //no-masked rdata valid to retry_ctrl 
   ,output                             rd_ra_eod_retry
   ,output  [RA_INFO_WIDTH-1:0]        rd_ra_info_retry
   ,output                             rd_crc_err_retry
   ,output                             rd_ra_ecc_uncorrected_err_retry
   
   ,output [CMD_LEN_BITS-1:0]          rd_ra_partial_retry

   ,output                             rd_ra_rd_addr_err      // read address error flag

   ,input                           rt_rd_rd_mrr_sod
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: Used only under `ifdef MEMC_LPDDR4 in this file but signal should always exist under `ifdef MEMC_LPDDR2_OR_DDR4
   ,input                           rt_rd_rd_mrr
//spyglass enable_block W240
   ,input                           rt_rd_rd_mrr_ext
   ,output                          rd_mrr_data_valid
   ,output                          sel_rt_rd_rd_mrr_ext
   ,output  [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0] rd_mrr_data
   ,input                           reg_ddrc_mrr_done_clr
   ,output                          ddrc_reg_mrr_done
   ,output  [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0]   ddrc_reg_mrr_data
   ,output                          rd_mr4_data_valid

//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate block.

// OCECC
   ,input                           ocecc_en
   ,input                           ocecc_poison_egen_mr_rd_1
   ,input [OCECC_MR_BNUM_WIDTH-1:0] ocecc_poison_egen_mr_rd_1_bnum
   ,input                           ocecc_poison_egen_xpi_rd_0
   ,input                           ocecc_poison_single
   ,input                           ocecc_poison_pgen_rd
   ,input                           ocecc_uncorr_err_intr_clr
//spyglass enable_block W240
   ,input                           rt_rd_rd_mrr_snoop

   ,output [RANK_BITS_DUP-1:0]      rd_dh_rd_crc_err_rank
   ,output [CID_WIDTH_DUP-1:0]      rd_dh_rd_crc_err_cid
   ,output [BG_BITS_DUP-1:0]        rd_dh_rd_crc_err_bg
   ,output [BANK_BITS-1:0]          rd_dh_rd_crc_err_bank
   ,output [ROW_BITS-1:0]           rd_dh_rd_crc_err_row
   ,output [COL_BITS-1:0]           rd_dh_rd_crc_err_col
   ,output                          rd_dh_crc_poison_inject_complete
   ,output [MAX_NUM_NIBBLES-1:0]    rd_dh_rd_crc_err_max_reached_int_nibble
   ,output                          rd_dh_rd_crc_err_max_reached_int
   ,output [MAX_NUM_NIBBLES*12-1:0] rd_dh_rd_crc_err_cnt_nibble
   ,output                          rd_crc_err

   ,output                                        ddrc_reg_rd_linkecc_poison_complete
   ,output [RD_LINK_ECC_UNCORR_CNT_WIDTH    -1:0] ddrc_reg_rd_link_ecc_uncorr_cnt
   ,output [RD_LINK_ECC_CORR_CNT_WIDTH      -1:0] ddrc_reg_rd_link_ecc_corr_cnt
   ,output [RD_LINK_ECC_ERR_SYNDROME_WIDTH  -1:0] ddrc_reg_rd_link_ecc_err_syndrome
   ,output [RD_LINK_ECC_UNCORR_ERR_INT_WIDTH-1:0] ddrc_reg_rd_link_ecc_uncorr_err_int
   ,output [RD_LINK_ECC_CORR_ERR_INT_WIDTH  -1:0] ddrc_reg_rd_link_ecc_corr_err_int
   ,output                                        rd_link_ecc_uncorr_err

   ,output [RANK_BITS_DUP-1:0]                     ddrc_reg_link_ecc_corr_rank
   ,output [BG_BITS_DUP-1:0]                       ddrc_reg_link_ecc_corr_bg
   ,output [BANK_BITS-1:0]                         ddrc_reg_link_ecc_corr_bank
   ,output [ROW_BITS-1:0]                          ddrc_reg_link_ecc_corr_row
   ,output [COL_BITS-1:0]                          ddrc_reg_link_ecc_corr_col
   ,output [RANK_BITS_DUP-1:0]                     ddrc_reg_link_ecc_uncorr_rank
   ,output [BG_BITS_DUP-1:0]                       ddrc_reg_link_ecc_uncorr_bg
   ,output [BANK_BITS-1:0]                         ddrc_reg_link_ecc_uncorr_bank
   ,output [ROW_BITS-1:0]                          ddrc_reg_link_ecc_uncorr_row
   ,output [COL_BITS-1:0]                          ddrc_reg_link_ecc_uncorr_col



   ,output  [7:0]                              rd_dh_ecc_cb_corr_syndromes   // data pattern that resulted in an error;
   ,output  [7:0]                              rd_dh_ecc_cb_uncorr_syndromes // data pattern that resulted in an error;
   ,output  [`DDRCTL_HIF_KBD_WIDTH-1:0]        rd_ra_kbd
   ,output  [`DDRCTL_HIF_KBD_WIDTH-1:0]        rd_rw_kbd
   ,output                                     rd_dh_scrubber_read_ecc_ce
   ,output                                     rd_dh_scrubber_read_ecc_ue 
   ,output  [`MEMC_ECC_SYNDROME_WIDTH-1:0]     rd_dh_ecc_corr_rsd_data   // RSD data pattern that resulted in an error;
   ,output  [`MEMC_ECC_SYNDROME_WIDTH-1:0]     rd_dh_ecc_uncorr_rsd_data // RSD data pattern that resulted in an error;
   ,output [ADVECC_CE_KBD_STAT_WIDTH-1:0]      ddrc_reg_advecc_ce_kbd_stat
   ,output [`MEMC_FREQ_RATIO/2-1:0]            ddrc_reg_advecc_ue_kbd_stat
   ,output                                     rd_dh_scrubber_read_advecc_ce
   ,output                                     rd_dh_scrubber_read_advecc_ue
   ,output [ECC_CORR_ERR_PER_RANK_INTR_WIDTH-1:0]  ddrc_reg_ecc_corr_err_per_rank_intr
   ,output [ECC_CORR_ERR_CNT_RANK_WIDTH-1:0]   ddrc_reg_ecc_corr_err_cnt_rank0
   ,output [ECC_CORR_ERR_CNT_RANK_WIDTH-1:0]   ddrc_reg_ecc_corr_err_cnt_rank1
   ,output [ECC_CORR_ERR_CNT_RANK_WIDTH-1:0]   ddrc_reg_ecc_corr_err_cnt_rank2
   ,output [ECC_CORR_ERR_CNT_RANK_WIDTH-1:0]   ddrc_reg_ecc_corr_err_cnt_rank3
   ,output [`DDRCTL_EAPAR_SIZE*SECDED_LANES-1:0] ddrc_reg_eapar_error
   ,output [15:0]                              ddrc_reg_eapar_err_cnt      // Count of correctable ECC errors//
   ,output  [`DDRCTL_EAPAR_SIZE-1:0]           rd_wu_eapar
   ,output                                     rd_wu_eapar_err
   ,output                                     rd_ra_eapar_err
   ,output  [RANK_BITS_DUP-1:0]                ddrc_reg_eapar_err_rank
   ,output  [BANK_BITS-1:0]                    ddrc_reg_eapar_err_bank
   ,output  [BG_BITS_DUP-1:0]                  ddrc_reg_eapar_err_bg
   ,output  [CID_WIDTH_DUP-1:0]                ddrc_reg_eapar_err_cid
   ,output  [ROW_BITS-1:0]                     ddrc_reg_eapar_err_row
   ,output  [COL_BITS-1:0]                     ddrc_reg_eapar_err_col
   ,output  [`MEMC_ECC_SYNDROME_WIDTH-1:0]     ddrc_reg_eapar_err_syndromes 
   ,output  [7:0]                              ddrc_reg_eapar_err_cb_syndromes
   ,output                                     ddrc_reg_eapar_err_sbr_rd
   ,output                                       ime_i_rd_dec_req
   ,output [DDRCTL_IME_LENGTH_WIDTH-1:0]         ime_i_rd_dec_length
   ,output [DDRCTL_IME_OFFSET_WIDTH-1:0]         ime_i_rd_dec_offset
   ,output                                       ime_i_rd_dec_bypass
   ,output [$clog2(`MEMC_RT_FIFO_DEPTH)-1:0]     ime_i_rd_twk_val_index
   ,output [DDRCTL_IME_DP_WIDTH-1:0]             ime_i_rd_cipher_data
   ,output                                       ime_i_rd_cipher_data_valid
   ,output                                       ime_i_rd_cipher_data_last
   ,output [CORE_METADATA_WIDTH-1:0]             ime_i_rd_passthru
                    );

//------------------------------------------------------------------------------
// Parameters
//------------------------------------------------------------------------------
// data_bus_width encodings
localparam      DATA_BUS_WIDTH_FULL     = 2'b00;        // use whole data bus
localparam      DATA_BUS_WIDTH_HALF     = 2'b01;        // use whole data bus
localparam      DATA_BUS_WIDTH_QUARTER  = 2'b10;        // use whole data bus

localparam      DATA_WIDTH_NO_ECC       = CORE_DATA_WIDTH;
// ecc_mode encodings
localparam      ECC_MODE_NO_ECC            = 3'b000; 
localparam      ECC_MODE_PARITY            = 3'b010;
localparam      ECC_MODE_SECDED            = 3'b100;
localparam      ECC_MODE_ADVECC            = 3'b101;       

// ocpar
localparam      OCPAR_SLICE_DW            = 8;
localparam      ECC_EN                    = `MEMC_ECC_SUPPORT;
localparam      FR                        = `MEMC_FREQ_RATIO;

// signal width adapt
localparam      ADVECC_WIDTH_ADAPT        = (ECC_EN == 3) ? 2 : 1;

localparam     [DDRCTL_A_NPORTS_LG2-1:0] DDRCTL_SBR_PORT_NUM  = DDRCTL_INT_NPORTS_DATA - 1;

localparam EAPAR_SIZE_SECDED_LANES = `DDRCTL_EAPAR_SIZE*SECDED_LANES;


//----------------------- outputs that require reg in certain configs -----------------------------
// following signals are register drivers of outputs depending on certain ifdef
// Was prev defined as output reg xxx inisde ifedef but changed to:
// output (wire - implicit) xxx [always there]
// Then depedning on ifdef:
// reg i<xxx;
// assign xxx = i_xxx;
// Reset of logic uses i_xxx instead of xxx;
// 

  reg                      i_rd_wu_ecc_corrected_err;
  reg                      i_rd_wu_ecc_uncorrected_err;

  assign                   rd_wu_ecc_corrected_err   = i_rd_wu_ecc_corrected_err;
  assign                   rd_wu_ecc_uncorrected_err = i_rd_wu_ecc_uncorrected_err;








//-----------------------------------------------------------------

//-----------------------------------------------------------------

   reg                         i_rd_wu_rdata_valid;
   reg [WU_INFO_WIDTH-1:0]     i_rd_wu_info;
   reg                         i_rd_rw_rdata_valid;
   reg [CORE_DATA_WIDTH-1:0]   i_rd_rw_rdata;
   reg [UMCTL2_WDATARAM_PAR_DW-1:0]   i_rd_rw_rdata_par;

//-------------------------------------------------------------------------------------------------------------

   assign                      rd_wu_rdata_valid = i_rd_wu_rdata_valid ;
   assign                      rd_wu_info        = i_rd_wu_info;
   assign                      rd_rw_rdata_valid = i_rd_rw_rdata_valid;
   assign                      rd_rw_rdata       = i_rd_rw_rdata;
   assign                      rd_rw_rdata_par   = i_rd_rw_rdata_par;
   reg [WORD_BITS-1:0]         i_rd_wu_word_num;  

   assign                      rd_wu_word_num = i_rd_wu_word_num;




   reg                       i_rd_ra_rd_addr_err;
   wire                       i_rd_ra_rd_addr_err_mux;

   assign                    rd_ra_rd_addr_err = i_rd_ra_rd_addr_err_mux;


   reg                       mrr_recieved_r;
   reg  [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0] mrr_data_r;

wire [PHY_DBI_WIDTH-1:0]     sel_ph_rd_rdbi_n;
wire [PHY_DATA_WIDTH-1:0]    sel_ph_rd_rdata;
wire                         sel_rt_rd_rd_valid;
wire                         sel_rt_rd_eod;
wire [CMD_LEN_BITS-1:0]      sel_rt_rd_partial;
wire [RA_INFO_WIDTH-1:0]     sel_rt_rd_ra_info;
wire                         sel_rt_rd_rd_mrr;
//wire                         sel_rt_rd_rd_mrr_ext;
wire                         sel_rt_rd_rd_mrr_snoop;
wire                         sel_rt_rd_rd_mrr_sod;
wire  [RMW_TYPE_BITS-1:0]    sel_rt_rd_rmwtype;
wire  [WU_INFO_WIDTH-1:0]    sel_rt_rd_wu_info;
wire                         sel_rt_rd_rmw_word_sel;
wire [BT_BITS-1:0]           sel_rt_rd_ie_bt;
wire [IE_RD_TYPE_BITS-1:0]   sel_rt_rd_ie_rd_type;
wire [IE_BURST_NUM_BITS-1:0] sel_rt_rd_ie_blk_burst_num;
wire  [ECC_INFO_WIDTH-1:0]   sel_rt_rd_ecc_info;
wire  [WORD_BITS-1:0]        sel_rt_rd_ecc_word;
wire                         sel_rt_rd_eccap;
wire                         sel_rt_rd_rd_addr_err;

   






wire      rdcrc_or_retry;


//----------------------- drive undriven outputs -----------------------------





// else of ifndef => `ifdef MEMC_ECC case
   assign rd_dh_ecc_corr_cid    = {CID_WIDTH_DUP{1'b0}};
   assign rd_dh_ecc_uncorr_cid  = {CID_WIDTH_DUP{1'b0}};
   
   assign ddrc_reg_advecc_corrected_err   = 1'b0;
   assign ddrc_reg_advecc_uncorrected_err = 1'b0;
   assign ddrc_reg_advecc_num_err_symbol  = {ADVECC_NUM_ERR_SYMBOL_WIDTH{1'b0}};
   assign ddrc_reg_advecc_err_symbol_pos  = {ADVECC_ERR_SYMBOL_POS_WIDTH{1'b0}};
   assign ddrc_reg_advecc_err_symbol_bits = {ADVECC_ERR_SYMBOL_BITS_WIDTH{1'b0}};
   assign ddrc_reg_advecc_ce_kbd_stat     = {ADVECC_CE_KBD_STAT_WIDTH{1'b0}};
   assign ddrc_reg_advecc_ue_kbd_stat     = {`MEMC_FREQ_RATIO/2{1'b0}};

   assign rd_wu_ecc_uncorrected_err_eighth  = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_seventh = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_sixth   = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_fifth   = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_fourth  = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_third   = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_second  = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_ecc_uncorrected_err_first   = {SECDED_LANES_DUP{1'b0}};
   assign rd_wu_rd_crc_err                  = 1'b0;

   assign rd_ra_ecc_rdata                   = {CORE_ECC_WIDTH_DUP{1'b0}};
 

   assign rd_rw_rdata_meta    = {CORE_METADATA_WIDTH{1'b0}};     

// else of ifndef => `ifdef MEMC_USE_RMW case
  //

   assign rd_wu_burst_chop_rd = 1'b0;
   assign rd_wu_rd32_eobl16   = 1'b0;
   assign rd_wu_rdata_type    = 2'b00;



//------------------------------------------------------------------------------
// Wires and registers
//------------------------------------------------------------------------------

reg                             i_rd_ra_rdata_valid;
reg     [CORE_DATA_WIDTH-1:0]   i_rd_ra_rdata;
reg     [CORE_MASK_WIDTH-1:0]   i_rd_ra_rdata_parity;
reg                             i_rd_ra_eod;
reg     [CMD_LEN_BITS-1:0]      i_rd_wu_partial;
reg     [CMD_LEN_BITS-1:0]      i_rd_ra_partial;
reg     [RA_INFO_WIDTH-1:0]     i_rd_ra_info;
reg [`DDRCTL_HIF_DRAM_ADDR_WIDTH-1:0] i_rd_ra_dram_addr;
wire                             i_rd_ra_rdata_valid_mux;
wire     [CORE_DATA_WIDTH-1:0]   i_rd_ra_rdata_mux;
wire     [CORE_MASK_WIDTH-1:0]   i_rd_ra_rdata_parity_mux;
wire                             i_rd_ra_eod_mux;
wire     [CMD_LEN_BITS-1:0]      i_rd_wu_partial_mux;
wire     [CMD_LEN_BITS-1:0]      i_rd_ra_partial_mux;
wire     [RA_INFO_WIDTH-1:0]     i_rd_ra_info_mux;
wire [`DDRCTL_HIF_DRAM_ADDR_WIDTH-1:0] i_rd_ra_dram_addr_mux;

assign rd_wu_rdata_end = i_rd_ra_eod;  // 

assign rd_ra_rdata_valid  = i_rd_ra_rdata_valid_mux;
assign rd_ra_rdata        = i_rd_ra_rdata_mux;
assign rd_ra_rdata_parity = i_rd_ra_rdata_parity_mux;
assign rd_ra_eod          = i_rd_ra_eod_mux;
assign rd_wu_partial      = i_rd_wu_partial_mux;
assign rd_ra_partial_retry = i_rd_ra_partial_mux;
assign rd_ra_info         = i_rd_ra_info_mux;
assign rd_ra_rdata_meta    = {CORE_METADATA_WIDTH{1'b0}};
assign rd_ra_dram_addr    = i_rd_ra_dram_addr_mux;

wire rd_ra_rdata_valid_w;
wire rd_wu_rdata_valid_w;

wire                       rt_rd_rd_valid_int;
wire                       rt_rd_data_valid_int;
wire                       mrr_operation_on_int;
wire rd_rw_rdata_valid_w;
wire   [RMW_TYPE_BITS-1:0] rt_rd_rmwtype_int;
wire   [WU_INFO_WIDTH-1:0] rt_rd_wu_info_int;
wire                       rt_rd_eod_int;
wire   [CMD_LEN_BITS-1:0]  rt_rd_partial_int;
wire   [RA_INFO_WIDTH-1:0] rt_rd_ra_info_int;
wire                       rt_rd_rd_addr_err_int;  // read address error flag

wire [ECC_INFO_WIDTH-1:0]  rt_rd_ra_ecc_info_int;
wire [WORD_BITS-1:0]       rt_rd_ra_ecc_word_int; 
wire [ECC_INFO_WIDTH-1:0]  rt_rd_ra_ecc_info_int_w;
wire [WORD_BITS-1:0]       rt_rd_ra_ecc_word_int_w; 
wire                       rt_rd_data_valid_int_w;
wire                       mrr_operation_on_int_w;
wire   [RMW_TYPE_BITS-1:0] rt_rd_rmwtype_int_w;
wire   [WU_INFO_WIDTH-1:0] rt_rd_wu_info_int_w;
wire                       rt_rd_eod_int_w;
wire   [CMD_LEN_BITS-1:0]  rt_rd_partial_int_w;
wire   [RA_INFO_WIDTH-1:0] rt_rd_ra_info_int_w;
wire   [CORE_DATA_WIDTH-1:0] i_rd_ra_rdata_w;
wire   [CORE_MASK_WIDTH-1:0] i_rd_ra_rdata_parity_w;
wire                       rt_rd_rd_addr_err_int_w;
wire                       i_rd_ra_rd_addr_err_w;
wire [`DDRCTL_HIF_DRAM_ADDR_WIDTH-1:0] i_rd_ra_dram_addr_w;


wire                      rd_wu_ecc_uncorrected_err_w;
wire                      rd_wu_ecc_corrected_err_w;
wire                      rd_wu_ecc_uncorrected_err_w_ie;
wire                      rd_wu_ecc_corrected_err_w_ie;


assign rd_wu_ecc_uncorrected_err_w = 
                                     reg_ddrc_ecc_type ? rd_wu_ecc_uncorrected_err_w_ie :
                                                        1'b0
                                                        ;

assign rd_wu_ecc_corrected_err_w = 
                                     reg_ddrc_ecc_type ? rd_wu_ecc_corrected_err_w_ie :
                                                        1'b0
                                                        ;



wire    [ECC_INFO_WIDTH-1:0]    rd_dh_ecc_corr_info;
wire    [ECC_INFO_WIDTH-1:0]    rd_dh_ecc_uncorr_info;
wire    [5:0]                   rd_dh_ecc_corr_word_num;
wire    [5:0]                   rd_dh_ecc_uncorr_word_num;



wire    [ECC_INFO_WIDTH-1:0]    rd_dh_ecc_corr_info_ie;
wire    [ECC_INFO_WIDTH-1:0]    rd_dh_ecc_uncorr_info_ie;
wire    [5:0]                   rd_dh_ecc_corr_word_num_ie;
wire    [5:0]                   rd_dh_ecc_uncorr_word_num_ie;

// Below is log registers for SECDEC mode
wire    [`MEMC_ECC_SYNDROME_WIDTH-1:0]          rd_dh_ecc_corr_syndromes_ie;
wire    [`MEMC_ECC_SYNDROME_WIDTH-1:0]          rd_dh_ecc_uncorr_syndromes_ie;
wire    [`MEMC_ECC_SYNDROME_WIDTH-1:0]          rd_dh_ecc_corr_bit_mask_ie;
wire    [15:0]                                  ddrc_reg_ecc_corr_err_cnt_ie;      
wire    [15:0]                                  ddrc_reg_ecc_uncorr_err_cnt_ie;    
wire    [6:0]                                   rd_dh_ecc_corrected_bit_num_ie;

//wire    [SECDED_LANES-1:0]                      rd_dh_ecc_corrected_err_ie;   
//wire    [SECDED_LANES-1:0]                      rd_dh_ecc_uncorrected_err_ie; 
wire                                            rd_dh_ecc_corrected_err_ie;   
wire                                            rd_dh_ecc_uncorrected_err_ie; 




assign rd_dh_ecc_corr_info      = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_corr_info_ie : {ECC_INFO_WIDTH{1'b0}}
//`endif // MEMC_INLINE_ECC
                                                                              ;


assign rd_dh_ecc_uncorr_info     = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_uncorr_info_ie :
                                                       {ECC_INFO_WIDTH{1'b0}}
                                                                                ;


assign rd_dh_ecc_corr_word_num   = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_corr_word_num_ie :
                                                       6'b0 
                                                                                ;


assign rd_dh_ecc_uncorr_word_num = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_uncorr_word_num_ie :
                                                       6'b0 
                                                                                ;

assign rd_dh_ecc_corr_syndromes      = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_corr_syndromes_ie :
                                                       {`MEMC_ECC_SYNDROME_WIDTH{1'b0}}
                                                                                ;

assign rd_dh_ecc_uncorr_syndromes      = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_uncorr_syndromes_ie :
                                                       {`MEMC_ECC_SYNDROME_WIDTH{1'b0}}
                                                                                ;

assign rd_dh_ecc_corr_bit_mask        = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_corr_bit_mask_ie :
                                                       {`MEMC_ECC_SYNDROME_WIDTH{1'b0}}
                                                                                ;
assign ddrc_reg_ecc_corr_err_cnt      = 
                                   reg_ddrc_ecc_type ? ddrc_reg_ecc_corr_err_cnt_ie :
                                                       {16{1'b0}}
                                                                ;

assign ddrc_reg_ecc_uncorr_err_cnt    = 
                                   reg_ddrc_ecc_type ? ddrc_reg_ecc_uncorr_err_cnt_ie :
                                                       {16{1'b0}}
                                                                                ;

assign rd_dh_ecc_corrected_bit_num    = 
                                   reg_ddrc_ecc_type ? rd_dh_ecc_corrected_bit_num_ie :
                                                       {7{1'b0}}
                                                                                ;

assign rd_dh_ecc_corrected_err    = 
                                   reg_ddrc_ecc_type ? 
                                                       rd_dh_ecc_corrected_err_ie :
                                                       {SECDED_LANES_DUP{1'b0}}
                                                                                ;

assign rd_dh_ecc_uncorrected_err    = 
                                   reg_ddrc_ecc_type ? 
                                                       rd_dh_ecc_uncorrected_err_ie :
                                                       {SECDED_LANES_DUP{1'b0}}
                                                                                ;
assign rd_dh_ecc_cb_corr_syndromes      = 
                                   reg_ddrc_ecc_type ? {8{1'b0}} :
                                                       {8{1'b0}}
                                                                 ;

assign rd_dh_ecc_cb_uncorr_syndromes      = 
                                   reg_ddrc_ecc_type ? {8{1'b0}} :
                                                       {`MEMC_ECC_SYNDROME_WIDTH{1'b0}}
                                                                                ;

assign rd_dh_scrubber_read_ecc_ce   = 
                                   reg_ddrc_ecc_type ? 1'b0 :
                                                       1'b0
                                                                                ;
assign rd_dh_scrubber_read_ecc_ue  =  
                                   reg_ddrc_ecc_type ? 1'b0 :
                                                       1'b0
                                                                                ;

assign rd_dh_scrubber_read_advecc_ce   = 
                                   reg_ddrc_ecc_type ? 1'b0 :
                                                      1'b0
                                                                                ;
assign rd_dh_scrubber_read_advecc_ue  =  
                                   reg_ddrc_ecc_type ? 1'b0 :
                                                      1'b0
                                                                                ;







wire                            mr4;
wire                            i_rd_mr4_data_valid;
reg                             r_rd_mr4_data_valid;
wire                            mrr_ext;
wire                            mrr_operation_on;
wire                            mrr_operation_on_r;
wire                            i_rd_mrr_data_valid;
reg                             r_rd_mrr_data_valid;
wire [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0] i_rd_mrr_data;
reg  [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0] r_rd_mrr_data;

//------------------------------------------------------------------------------
// Internal Wires and registers
//------------------------------------------------------------------------------
reg     [PHY_DATA_WIDTH-1:0]    ph_rd_rdata_dbi;                // read data DBI
wire                            read_dbi_enable;        // read data DBI enable 
wire    [PHY_DATA_WIDTH-1:0]    ph_rd_rdata_no_dbi;             // read data no DBI

wire    [4:0]                   word_num;               // count of valid_words - x [1 for each ECC lane] - max of 32 QBW 1:1 MEMC_BURST_LENGTH=16
wire    [4:0]                   word_num_int;               // count of valid_words - x [1 for each ECC lane] - max of 32 QBW 1:1 MEMC_BURST_LENGTH=16
reg     [5:0]                   word_num_wider;         // used to check that overflow does not occur

reg                             r_half_data_bus_width;  // dh_rd_data_bus_width==2'b01, flopped locally

wire    [PHY_DATA_WIDTH-1:0]    data_out;
wire    [PHY_DATA_WIDTH-1:0]    data_out_w;
wire    [CORE_MASK_WIDTH-1:0]   parity_out;
wire    [CORE_MASK_WIDTH-1:0]   parity_out_w;

wire    [PHY_DATA_WIDTH-1:0]    data_out_non_sb;



// DBI logic
wire    [PHY_DBI_WIDTH-1:0]     rd_rdbi;

wire                             lpddr_mode;
assign lpddr_mode = reg_ddrc_lpddr4 | reg_ddrc_lpddr5;

assign rd_rdbi = 
            (lpddr_mode)? ~sel_ph_rd_rdbi_n :
                           sel_ph_rd_rdbi_n;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(i * 8)' found in module 'rd'
//SJ: This coding style is acceptable and there is no plan to change it.
integer i;
always @(*)
    for (i=0; i<PHY_DBI_WIDTH; i=i+1) begin
        ph_rd_rdata_dbi[i*8+:8] = (rd_rdbi[i]) ? sel_ph_rd_rdata[i*8+:8] : ~sel_ph_rd_rdata[i*8+:8];
    end 
//spyglass enable_block SelfDeterminedExpr-ML

  assign read_dbi_enable = ~reg_ddrc_phy_dbi_mode & reg_ddrc_rd_dbi_en;
//`else
//  assign read_dbi_enable = 1'b0;
assign ph_rd_rdata_no_dbi = 
                            ((read_dbi_enable) ? ph_rd_rdata_dbi : sel_ph_rd_rdata)
                     ;

// flopped bus width signals
always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    r_half_data_bus_width       <= 1'b0;
  end
  else if(ddrc_cg_en) begin     // flops not in reset
    r_half_data_bus_width       <= (dh_rd_data_bus_width==DATA_BUS_WIDTH_HALF);
  end

//------------------------------------------------------------------------------
// ECC section
//     - Flopping all the inputs - flop it twince in the case of BW < 64
//     - Test mode instance
//     - ECC decoder instance
//     - Data Out Mux
//------------------------------------------------------------------------------

wire    [PHY_DATA_WIDTH-1:0]     ph_rd_rdata_r;
wire                             rt_rd_rd_valid_r;        // valid read data from PHY
wire  [CORE_DATA_WIDTH-1:0]      data_out_ecc;
wire  [CORE_DATA_WIDTH-1:0]      data_no_ecc_unused;



// When NoECC && DDR5(Read-CRC) && FREQ_RATIO=4, add extra one pipeline.
//  - Read-CRC is enabled : Extra one pipeline
//  - Read-CRC is disabled: Bypass this pipeline

wire                             rt_rd_rd_valid_w;       // valid read data from PHY
wire                             rt_rd_eod_w;            // end of data from RT
wire    [CMD_LEN_BITS-1:0]       rt_rd_partial_w;        // indicates that the current read is a non-block read
wire    [RA_INFO_WIDTH-1:0]      rt_rd_ra_info_w;        // address and RMW type from RT for RMW and ECC scrubs
wire                             mrr_operation_on_w;
wire                             rt_rd_rd_addr_err_w;    // read address error flag
wire    [RMW_TYPE_BITS-1:0]      rt_rd_rmwtype_w;        // 2-bit RMW type indicator.  See ddrc_parameters.v for encodings.
wire    [WU_INFO_WIDTH-1:0]      rt_rd_wu_info_w;        // address and RMW type from RT for RMW and ECC scrubs



assign rt_rd_rd_valid_w    =  sel_rt_rd_rd_valid;
assign rt_rd_eod_w         =  sel_rt_rd_eod;
assign rt_rd_partial_w     =  sel_rt_rd_partial;
assign rt_rd_ra_info_w     =  sel_rt_rd_ra_info;
assign mrr_operation_on_w  =  mrr_operation_on;
assign rt_rd_rd_addr_err_w =  sel_rt_rd_rd_addr_err;
assign rt_rd_rmwtype_w        =  sel_rt_rd_rmwtype;
assign rt_rd_wu_info_w        =  sel_rt_rd_wu_info;



//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Unused in some configs. Decided to keep current coding style.
     
// needed in OCPAR module
assign ph_rd_rdata_r    = {PHY_DATA_WIDTH{1'b0}};
assign rt_rd_rd_valid_r = rt_rd_rd_valid_w;
assign data_out_ecc     = {CORE_DATA_WIDTH{1'b0}};
//spyglass enable_block W528

//-------------------------------------
// End SIDEBAND ECC Section
//-------------------------------------

//----------------------------------------------------
// Non-ECC section (also used for IE case in SB=1 & IE=1 case)
//    - assembling the data in HBW & QBW modes
//    - mux to select the appropriate data based on bus width mode
//    - data_out generation
//----------------------------------------------------

//spyglass disable_block W528
//SMD: Signal declared but not read
//SJ: Used opcpar_rd_gen
wire [PHY_DATA_WIDTH-1:0] ph_rd_rdata_no_dbi_exp;
//spyglass enable_block W528



reg [CORE_DATA_WIDTH-1:0] ph_rd_rdata_no_dbi_core_width;


  // reduce width to strip out ecc byte 
  // - 2 of them in FR=1
  // - 4 of them in FR=2
  // this strip down data signal is passed to data_out if IE=1

  //spyglass disable_block SelfDeterminedExpr-ML
  //SMD: Self determined expression '(FR * 2)' found in module 'rd'
  //SJ: This coding style is acceptable and there is no plan to change it.

  always @(*) begin  : ph_rd_rdata_no_dbi_core_width_ie_PROC
  integer x,y;
    for (x=0; x<(CORE_DATA_WIDTH/(FR*2)); x=x+1) begin
      for (y=0; y<FR*2; y=y+1) begin
        ph_rd_rdata_no_dbi_core_width[x+(y*(CORE_DATA_WIDTH/(FR*2)))] = ph_rd_rdata_no_dbi[x+(y*(PHY_DATA_WIDTH/(FR*2)))];
      end
    end
  end
  //spyglass enable_block SelfDeterminedExpr-ML
  

   
//spyglass disable_block W528
//SMD: Signal declared but not read
//SJ: Used opcpar_rd_gen
wire [PHY_DATA_WIDTH-1:0] ph_rd_rdata_no_dbi_exp_ie;
wire [PHY_DATA_WIDTH-1:0] ph_rd_rdata_no_dbi_exp_non_ie;


  // padd upper bits with 0s
  assign ph_rd_rdata_no_dbi_exp_ie =  { {(PHY_DATA_WIDTH-CORE_DATA_WIDTH){1'b0}}, ph_rd_rdata_no_dbi_core_width};

  assign ph_rd_rdata_no_dbi_exp_non_ie = ph_rd_rdata_no_dbi;
  
  assign ph_rd_rdata_no_dbi_exp = (reg_ddrc_ecc_type) ? ph_rd_rdata_no_dbi_exp_ie : ph_rd_rdata_no_dbi_exp_non_ie;
  
  //spyglass enable_block W528



  // Data alignment for FBW - SW 1:2 mode
   wire [(CORE_DATA_WIDTH/2)-1:0]       lwr_half_ph_rd_rdata;
   reg  [(CORE_DATA_WIDTH/2)-1:0]       lwr_half_data_ff;

// Data is arranged differently in partially populated (aka HBW, QBW), DFI 1:2 mode
  
   assign lwr_half_ph_rd_rdata     = ph_rd_rdata_no_dbi_core_width[(CORE_DATA_WIDTH/2)-1:0];

//spyglass disable_block W528
//SMD: A signal or variable is set but never read - lwr_half_data_ff
//SJ: Used under different `ifdefs. Decided to keep current implementation.

   // When only using partial data bus, flop data until a full core-side transfer has arrived
   always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
     if (~core_ddrc_rstn) begin
        lwr_half_data_ff      <= {(CORE_DATA_WIDTH/2){1'b0}};
     end
     else if(ddrc_cg_en)
         begin 
            // flop the lower half of the data bus (post-ECC, if applicable)
            if(sel_rt_rd_rd_valid) begin
               lwr_half_data_ff      <= lwr_half_ph_rd_rdata;
            end
         end // flops not in reset
//spyglass enable_block W528


   // assign output data for configurations without ECC support
    assign      data_out_non_sb          = 
                                          (!dh_rd_frequency_ratio) ? {lwr_half_ph_rd_rdata, lwr_half_data_ff} : // FR2
                                                                      ph_rd_rdata_no_dbi_core_width;



//-------------------------------------
// End Non-ECC Section
//-------------------------------------

   assign data_out = data_out_non_sb;



  assign rd_dh_ecc_corr_rsd_data =
                          {`MEMC_ECC_SYNDROME_WIDTH{1'b0}};

  assign rd_dh_ecc_uncorr_rsd_data =
                          {`MEMC_ECC_SYNDROME_WIDTH{1'b0}};

//-------------------------------------------------------------------------
// INLINE ECC Section
//-------------------------------------------------------------------------
localparam CMD_INFO_WIDTH = RA_INFO_WIDTH      //rt_rd_ra_info
                            + 1                //rt_rd_rd_addr_err
                            + CMD_LEN_BITS     //rt_rd_partial 
                            + ECC_INFO_WIDTH   //rt_rd_ecc_info        // address, etc. from RT and provided to ECC registers //_replace_P80001562-505275_ if need
                            + WORD_BITS        //rt_rd_ecc_word        // address, etc. from RT and provided to ECC registers //_replace_P80001562-505275_ if need
                            + RMW_TYPE_BITS    //rt_rd_rmwtype          // 2-bit RMW type indicator.  See ddrc_parameters.v for encodings.
                            + 1                //rt_rd_rmw_word_sel     // selects which word to return to RA
                            + WU_INFO_WIDTH    //rt_rd_wu_info          // address and RMW type from RT for RMW and ECC scrubs
                            ;

wire [CMD_INFO_WIDTH-1:0]   ie_rt_rd_cmd_info;
wire                        ie_mrr_operation_on;

wire [RA_INFO_WIDTH-1:0]    ie_rt_rd_ra_info;  
wire [CMD_LEN_BITS-1:0]     ie_rt_rd_partial; 
wire [ECC_INFO_WIDTH-1:0]   ie_rt_rd_ecc_info;
wire [WORD_BITS-1:0]        ie_rt_rd_ecc_word;
wire                        ie_rt_rd_rd_addr_err;
wire [RMW_TYPE_BITS-1:0]    ie_rt_rd_rmwtype;   
wire                        ie_rt_rd_rmw_word_sel_unused; 
wire [WU_INFO_WIDTH-1:0]    ie_rt_rd_wu_info;     

wire [CORE_DATA_WIDTH-1:0]  ie_data_in;
wire [CORE_MASK_WIDTH-1:0]  ie_data_par;
wire [CORE_DATA_WIDTH-1:0]  ie_data_out;
wire                        ie_data_out_vld;
wire                        ie_data_out_eod;

wire [CMD_INFO_WIDTH-1:0]   rt_rd_cmd_info;
wire                        ie_ecc_corrected_err;
wire                        ie_ecc_uncorrected_err;

wire                        rt_rd_ie_ecc_vld;

wire [PHY_DATA_WIDTH-1:0]  ie_data_out_phy;
assign ie_data_out_phy = ie_data_out;


assign rt_rd_cmd_info = {
                           sel_rt_rd_ra_info
                           ,sel_rt_rd_rd_addr_err
                           ,sel_rt_rd_partial 
                           ,sel_rt_rd_ecc_info        // address, etc. from RT and provided to ECC registers
                           ,sel_rt_rd_ecc_word        // address, etc. from RT and provided to ECC registers
                           ,sel_rt_rd_rmwtype          // 2-bit RMW type indicator.  See ddrc_parameters.v for encodings.
                           ,sel_rt_rd_rmw_word_sel     // selects which word to return to RA
                           ,sel_rt_rd_wu_info          // address and RMW type from RT for RMW and ECC scrubs
                       };
assign {
                           ie_rt_rd_ra_info
                           ,ie_rt_rd_rd_addr_err
                           ,ie_rt_rd_partial 
                           ,ie_rt_rd_ecc_info        // address, etc. from RT and provided to ECC registers
                           ,ie_rt_rd_ecc_word        // address, etc. from RT and provided to ECC registers
                           ,ie_rt_rd_rmwtype          // 2-bit RMW type indicator.  See ddrc_parameters.v for encodings.
                           ,ie_rt_rd_rmw_word_sel_unused // selects which word to return to RA
                           ,ie_rt_rd_wu_info          // address and RMW type from RT for RMW and ECC scrubs
         } = ie_rt_rd_cmd_info;

assign ie_data_in   = data_out[CORE_DATA_WIDTH-1:0];  // it is after bus width coversion.
assign ie_data_par  = parity_out;

assign rd_wu_ecc_uncorrected_err_w_ie = ie_ecc_uncorrected_err;
assign rd_wu_ecc_corrected_err_w_ie   = ie_ecc_corrected_err;

wire [UMCTL2_WDATARAM_PAR_DW-1:0] ecc_out_rw_unused;
wire [CORE_MASK_WIDTH-1:0]        ecc_out_ra_unused;

//wire                              rdcrc_or_retry;

rd_ie_rdata_ctl

#(
    .CORE_DATA_WIDTH     (CORE_DATA_WIDTH  )
   ,.CORE_MASK_WIDTH     (CORE_MASK_WIDTH  )
   ,.RDCAM_ADDR_WIDTH    (`MEMC_RDCMD_ENTRY_BITS)
   ,.NO_OF_BRT           (NO_OF_BRT        )
   ,.BT_BITS             (BT_BITS          )
   ,.BWT_BITS            (BWT_BITS         )
   ,.BRT_BITS            (BRT_BITS         )
   ,.IE_RD_TYPE_BITS     (IE_RD_TYPE_BITS  )
   ,.IE_BURST_NUM_BITS   (IE_BURST_NUM_BITS)
   ,.WORD_BITS           (WORD_BITS)
   ,.CMD_INFO_WIDTH      (CMD_INFO_WIDTH)
   ,.ECC_INFO_WIDTH      (ECC_INFO_WIDTH)
   ,.ECC_RAM_ADDR_BITS   (ECC_RAM_ADDR_BITS)
   ,.ECC_ERR_RAM_DEPTH   (ECC_ERR_RAM_DEPTH)
   ,.ECC_ERR_RAM_ADDR_BITS(ECC_ERR_RAM_ADDR_BITS)
   ,.ECC_ERR_RAM_WIDTH   (ECC_ERR_RAM_WIDTH)
   ,.ECCAP_TH_WIDTH      (ECCAP_TH_WIDTH)
   ,.RMW_TYPE_BITS       (RMW_TYPE_BITS     )
   ,.OCECC_EN            (OCECC_EN          )
   ,.OCECC_XPI_RD_GRANU  (OCECC_XPI_RD_GRANU)
   ,.OCECC_MR_RD_GRANU   (OCECC_MR_RD_GRANU )
   ,.OCECC_MR_BNUM_WIDTH (OCECC_MR_BNUM_WIDTH)
   ,.OCECC_MR_RD_ECCW    (UMCTL2_WDATARAM_PAR_DW)
   ,.RD_IE_PAR_ERR_PIPELINE  (RD_IE_PAR_ERR_PIPELINE)
) 
rd_ie_rdata_ctl
(  
    .core_ddrc_core_clk  (co_yy_clk         )
   ,.core_ddrc_rstn      (core_ddrc_rstn    )
   ,.ddrc_cg_en          (ddrc_cg_en        )
   ,.reg_ddrc_burst_rdwr (reg_ddrc_burst_rdwr)  
   ,.reg_ddrc_data_bus_width (dh_rd_data_bus_width)
   // data in after asm
   ,.data_in             (ie_data_in        )
   ,.data_par            (ie_data_par       )
   ,.rt_rd_rd_valid      (rt_rd_data_valid_int)  
   ,.rt_rd_eod           (sel_rt_rd_eod     )
   ,.rt_rd_ecc_word      (sel_rt_rd_ecc_word)
   ,.rt_rd_cmd_info      (rt_rd_cmd_info    )
   ,.mrr_operation_on    (mrr_operation_on  )
//Inline ECC information
   ,.rt_rd_ie_bt         (sel_rt_rd_ie_bt   )
   ,.rt_rd_ie_rd_type    (sel_rt_rd_ie_rd_type)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
   ,.rt_rd_ie_ecc_vld    (rt_rd_ie_ecc_vld  )
//spyglass enable_block W528
   ,.rt_rd_ie_blk_burst_num (sel_rt_rd_ie_blk_burst_num)  //only for the Data command
// IH to RD for IE
   ,.ih_rd_ie_brt        (ih_rd_ie_brt        )
   ,.ih_rd_ie_rd_cnt_inc (ih_rd_ie_rd_cnt_inc )
   ,.ih_rd_ie_blk_rd_end (ih_rd_ie_blk_rd_end )
// CMD info output
   ,.ie_rt_rd_cmd_info   (ie_rt_rd_cmd_info   )
   
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current implementation.
   ,.ie_mrr_operation_on (ie_mrr_operation_on )
//spyglass enable_block W528

// ocpar
   ,.par_rdata_err_pulse (par_rdata_in_err_ecc_pulse )
// RD to IH for free BRT
   ,.rd_ih_free_brt_vld  (rd_ih_free_brt_vld  )
   ,.rd_ih_free_brt      (rd_ih_free_brt      )
   ,.data_out            (ie_data_out         )
   ,.data_out_vld        (ie_data_out_vld     )
   ,.data_out_eod        (ie_data_out_eod     )
   ,.ecc_uncorrected_err (ie_ecc_uncorrected_err)
   ,.ecc_corrected_err   (ie_ecc_corrected_err  )
   
// OCECC
   ,.ocecc_en                       (ocecc_en)
   ,.ocecc_poison_egen_mr_rd_1      (ocecc_poison_egen_mr_rd_1)
   ,.ocecc_poison_egen_mr_rd_1_bnum (ocecc_poison_egen_mr_rd_1_bnum)
   ,.ocecc_poison_egen_xpi_rd_0     (ocecc_poison_egen_xpi_rd_0)
   ,.ocecc_poison_single            (ocecc_poison_single)
   ,.ecc_out_rw                     (ecc_out_rw_unused)
   ,.ecc_out_ra                     (ecc_out_ra_unused)
    
// ECC RAM/ACC interface
   ,.rd_ecc_ram_wr            (rd_ecc_ram_wr          )
   ,.rd_ecc_ram_waddr         (rd_ecc_ram_waddr       )
   ,.rd_ecc_ram_wdata         (rd_ecc_ram_wdata       )
   ,.rd_ecc_ram_wdata_mask_n  (rd_ecc_ram_wdata_mask_n) //should be all 1, no mask. 
   ,.rd_ecc_ram_wdata_par     (rd_ecc_ram_wdata_par   )
   
   ,.rd_ecc_ram_raddr         (rd_ecc_ram_raddr         )
   ,.ecc_ram_rd_rdata         (ecc_ram_rd_rdata         )
   ,.rd_ecc_acc_raddr_2       (rd_ecc_acc_raddr_2       )
   ,.ecc_acc_rd_rdata_2       (ecc_acc_rd_rdata_2       )
   ,.ecc_acc_rd_rdata_mask_n_2(ecc_acc_rd_rdata_mask_n_2)
// ECC ERR RAM interface
   ,.mr_ecc_err_rd            (mr_ecc_err_rd       )
   ,.mr_ecc_err_raddr         (mr_ecc_err_raddr    )
   ,.ecc_err_mr_rdata         (ecc_err_mr_rdata    )
// TOKEN look up interface                                
   ,.rd_ih_lkp_bwt_by_bt      (rd_ih_lkp_bwt_by_bt ) 
   ,.rd_ih_lkp_brt_by_bt      (rd_ih_lkp_brt_by_bt ) 
   ,.ih_rd_lkp_brt            (ih_rd_lkp_brt       ) 
   ,.ih_rd_lkp_bwt            (ih_rd_lkp_bwt       ) 
   ,.ih_rd_lkp_bwt_vld        (ih_rd_lkp_bwt_vld   ) 
// Read CRC error on Read ECC

//Regiser Interfaces 
   ,.reg_ddrc_ecc_mode               (dh_rd_ecc_mode   )
   ,.reg_ddrc_med_ecc_en             (reg_ddrc_med_ecc_en)
   ,.ie_rt_rd_ecc_info               (ie_rt_rd_ecc_info)  // address, etc. from RT and provided to ECC wire
   ,.ie_rt_rd_rmwtype                (ie_rt_rd_rmwtype )
   ,.reg_ddrc_oc_parity_en           (reg_ddrc_read_data_parity_en   )
   ,.reg_ddrc_oc_parity_type         (reg_ddrc_oc_parity_type        )
   ,.reg_ddrc_ecc_clr_corr_err       (reg_ddrc_ecc_clr_corr_err      ) // Clear corrected error interrupt
   ,.reg_ddrc_ecc_clr_uncorr_err     (reg_ddrc_ecc_clr_uncorr_err    ) // Clear uncorrected error interrupt
   ,.reg_ddrc_ecc_clr_corr_err_cnt   (reg_ddrc_ecc_clr_corr_err_cnt  ) // Clear correctable ECC error count
   ,.reg_ddrc_ecc_clr_uncorr_err_cnt (reg_ddrc_ecc_clr_uncorr_err_cnt) // Clear uncorrectable ECC error count
   ,.ddrc_reg_ecc_corrected_bit_num  (rd_dh_ecc_corrected_bit_num_ie )
   ,.ddrc_reg_ecc_corrected_err      (rd_dh_ecc_corrected_err_ie     )
   ,.ddrc_reg_ecc_uncorrected_err    (rd_dh_ecc_uncorrected_err_ie   )
   ,.ddrc_reg_ecc_corr_err_cnt       (ddrc_reg_ecc_corr_err_cnt_ie   ) // Count of correctable ECC errors
   ,.ddrc_reg_ecc_uncorr_err_cnt     (ddrc_reg_ecc_uncorr_err_cnt_ie ) // Count of uncorrectable ECC errors
   ,.rd_dh_ecc_corr_syndromes        (rd_dh_ecc_corr_syndromes_ie    ) // data pattern that resulted in an error;
   ,.rd_dh_ecc_uncorr_syndromes      (rd_dh_ecc_uncorr_syndromes_ie  ) // data pattern that resulted in an error;
   ,.rd_dh_ecc_corr_bit_mask         (rd_dh_ecc_corr_bit_mask_ie     ) // mask for the bit that is corrected
   ,.rd_dh_ecc_corr_info             (rd_dh_ecc_corr_info_ie         ) // for (un)corr error address 
   ,.rd_dh_ecc_uncorr_info           (rd_dh_ecc_uncorr_info_ie       ) // for (un)corr error address 
   ,.rd_dh_ecc_corr_word_num         (rd_dh_ecc_corr_word_num_ie     ) // for (un)corr error address 
   ,.rd_dh_ecc_uncorr_word_num       (rd_dh_ecc_uncorr_word_num_ie   ) // for (un)corr error address 
   ,.rt_rd_eccap                     (sel_rt_rd_eccap)
   ,.ddrc_reg_ecc_ap_err             (ddrc_reg_ecc_ap_err)
   ,.reg_ddrc_ecc_ap_en              (reg_ddrc_ecc_ap_en)
   ,.reg_ddrc_ecc_ap_err_intr_clr    (reg_ddrc_ecc_ap_err_intr_clr)
   ,.reg_ddrc_ecc_ap_err_threshold   (reg_ddrc_ecc_ap_err_threshold)

);






//------------------------------------------------------------------------------
// ECC section
//    - All the ECC error reporting logic and their associated flops
//------------------------------------------------------------------------------


//---------------------------------------------
//Generate ECC error address according to ecc_info
//the logic is shared with any ECC mode

wire [RANK_BITS-1:0] rd_dh_ecc_corr_rank_w;
wire [RANK_BITS-1:0] rd_dh_ecc_uncorr_rank_w;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(((((BLK_BITS + ROW_BITS) + BANK_BITS) + BG_BITS) + LRANK_BITS) - 1)' found in module 'rd'
//SJ: This coding style is acceptable and there is no plan to change it.

assign rd_dh_ecc_corr_rank_w   = rd_dh_ecc_corr_info  [BLK_BITS+ROW_BITS+BANK_BITS+BG_BITS+RANK_BITS-1 : BLK_BITS+ROW_BITS+BANK_BITS+BG_BITS];
assign rd_dh_ecc_uncorr_rank_w = rd_dh_ecc_uncorr_info  [BLK_BITS+ROW_BITS+BANK_BITS+BG_BITS+RANK_BITS-1 : BLK_BITS+ROW_BITS+BANK_BITS+BG_BITS];


assign rd_dh_ecc_corr_rank      = rd_dh_ecc_corr_rank_w;
assign rd_dh_ecc_uncorr_rank    = rd_dh_ecc_uncorr_rank_w;

assign rd_dh_ecc_corr_bank    = rd_dh_ecc_corr_info  [BLK_BITS+ROW_BITS+BG_BITS+BANK_BITS-1 : BLK_BITS+ROW_BITS+BG_BITS];
assign rd_dh_ecc_uncorr_bank  = rd_dh_ecc_uncorr_info[BLK_BITS+ROW_BITS+BG_BITS+BANK_BITS-1 : BLK_BITS+ROW_BITS+BG_BITS];

assign rd_dh_ecc_corr_bg      = rd_dh_ecc_corr_info  [BLK_BITS+ROW_BITS+BG_BITS-1 : BLK_BITS+ROW_BITS];
assign rd_dh_ecc_uncorr_bg    = rd_dh_ecc_uncorr_info[BLK_BITS+ROW_BITS+BG_BITS-1 : BLK_BITS+ROW_BITS];

assign rd_dh_ecc_corr_row       = rd_dh_ecc_corr_info  [BLK_BITS+ROW_BITS-1 : BLK_BITS];
assign rd_dh_ecc_uncorr_row     = rd_dh_ecc_uncorr_info[BLK_BITS+ROW_BITS-1 : BLK_BITS];

//spyglass enable_block SelfDeterminedExpr-ML

//-------------------------------------------------------------------
// Column assignment for various modes and configurations
//-------------------------------------------------------------------
//
// BL8 configuration
//      FBW mode
//            BL16 - NA
//            BL8  - {block,cw,1'b0}
//            BL4  - {block,cw,2'b00}
//            BL2  - {block,cw,3'b000}
//      HBW mode
//            BL16 - {block,cw,1'b0}
//            BL8  - {block,cw,2'b00}
//            BL4  - {block,cw,3'b000}
//            BL2  - {block,cw,4'b0000}
//
// BL4 configuration
//      FBW mode
//            BL16 - NA
//            BL8  - NA
//            BL4  - {block,cw[1],1'b0}
//            BL2  - {block,cw[1],2'b00}
//      HBW mode
//            BL16 - NA
//            BL8  - {block,cw[1],1'b0}
//            BL4  - {block,cw[1],2'b00}
//            BL2  - {block,cw[1],3'b000}
//
//--------------------------------------------------------------------

wire [COL_BITS-1:0] rd_dh_ecc_corr_col_fbw;
wire [COL_BITS-1:0] rd_dh_ecc_uncorr_col_fbw;
assign rd_dh_ecc_corr_col_fbw   = {rd_dh_ecc_corr_info[BLK_BITS-1:0], rd_dh_ecc_corr_word_num[WORD_BITS-1:0]};
assign rd_dh_ecc_uncorr_col_fbw = {rd_dh_ecc_uncorr_info[BLK_BITS-1:0], rd_dh_ecc_uncorr_word_num[WORD_BITS-1:0]};

wire [COL_BITS-1:0] rd_dh_ecc_corr_col_hbw;
wire [COL_BITS-1:0] rd_dh_ecc_uncorr_col_hbw;
// Note: Only MEMC_FREQ_RATIO_4 is considered here, because other configuraiton is not supported now.
assign rd_dh_ecc_corr_col_hbw   = {rd_dh_ecc_corr_info[BLK_BITS-1:0], rd_dh_ecc_corr_word_num[WORD_BITS-1:3], rd_dh_ecc_corr_word_num[1:0], 1'b0};
assign rd_dh_ecc_uncorr_col_hbw = {rd_dh_ecc_uncorr_info[BLK_BITS-1:0], rd_dh_ecc_uncorr_word_num[WORD_BITS-1:3], rd_dh_ecc_uncorr_word_num[1:0], 1'b0};




assign rd_dh_ecc_corr_col    = (reg_ddrc_ecc_type) ? 
                                                     (r_half_data_bus_width ? rd_dh_ecc_corr_col_hbw : rd_dh_ecc_corr_col_fbw) :
                                                     {COL_BITS{1'b0}};

assign rd_dh_ecc_uncorr_col  = (reg_ddrc_ecc_type) ? 
                                                     (r_half_data_bus_width ? rd_dh_ecc_uncorr_col_hbw : rd_dh_ecc_uncorr_col_fbw) :
                                                     {COL_BITS{1'b0}};



//-------------------------------------
// End ECC Section
//-------------------------------------


//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current implementation.
assign rt_rd_rd_valid_int   = rt_rd_rd_valid_w;
assign mrr_operation_on_int = mrr_operation_on_w;
assign rt_rd_rmwtype_int    = rt_rd_rmwtype_w;
assign rt_rd_wu_info_int    = rt_rd_wu_info_w;
assign rt_rd_eod_int        = rt_rd_eod_w;
assign rt_rd_partial_int    = rt_rd_partial_w;
assign rt_rd_ra_info_int    = rt_rd_ra_info_w;
assign rt_rd_rd_addr_err_int = rt_rd_rd_addr_err_w;
assign rt_rd_ra_ecc_info_int = sel_rt_rd_ecc_info;
assign rt_rd_ra_ecc_word_int = sel_rt_rd_ecc_word;
//spyglass enable_block W528

// Word number
always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    word_num_wider     <= 6'b0;
  end
  else if(ddrc_cg_en) begin     // flops not in reset
    word_num_wider     <= ((rt_rd_eod_int & rt_rd_rd_valid_int)
                              | mrr_operation_on_int
                          ) ? 5'b0 : (word_num_wider[4:0] + {4'b0000, rt_rd_rd_valid_int});
  end
  
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in MEMC_FREQ_RATIO_4 or MEMC_SIDEBAND_ECC. When MEMC_FREQ_RATIO_4 is always enabled, this is not needed.
assign word_num = word_num_wider[4:0]; 
assign word_num_int = word_num; 
//spyglass enable_block W528

assign rt_rd_data_valid_int = rt_rd_rd_valid_int
                              & ( 
                               // In PROG FREQ RATIO, SW 1:2 mode - only lower lane data valid
                               // so need to combine data {lwr_lane1,lwr_lane0} and generate valid accordingly
                               (!dh_rd_frequency_ratio)
                               ? (word_num[0])  
                               :  
                                 (1'b1)  
                               ) 
                               ;


//MUX between "Inline ECC" and "Not Inline ECC"
// For inline ECC case, mux between cases based on ecc_type
assign rt_rd_data_valid_int_w = (reg_ddrc_ecc_type) ? ie_data_out_vld        : rt_rd_data_valid_int;
assign mrr_operation_on_int_w = (reg_ddrc_ecc_type) ? ie_mrr_operation_on    : mrr_operation_on_int;
assign rt_rd_rmwtype_int_w    = (reg_ddrc_ecc_type) ? ie_rt_rd_rmwtype       : rt_rd_rmwtype_int;
assign rt_rd_wu_info_int_w    = (reg_ddrc_ecc_type) ? ie_rt_rd_wu_info       : rt_rd_wu_info_int;
assign rt_rd_eod_int_w        = (reg_ddrc_ecc_type) ? ie_data_out_eod        : rt_rd_eod_int;
assign rt_rd_partial_int_w    = (reg_ddrc_ecc_type) ? ie_rt_rd_partial       : rt_rd_partial_int;
assign rt_rd_ra_info_int_w    = (reg_ddrc_ecc_type) ? ie_rt_rd_ra_info       : rt_rd_ra_info_int;
//`ifdef DDRCTL_RD_CRC_RETRY //DO not support IECC yet
//assign rd_crc_limit_reach_pre_int_w    = (reg_ddrc_ecc_type) ? ie_rd_crc_limit_reach_pre       : rd_crc_limit_reach_pre_int;
//`endif
assign rt_rd_rd_addr_err_int_w= (reg_ddrc_ecc_type) ? ie_rt_rd_rd_addr_err   : rt_rd_rd_addr_err_int;
assign data_out_w             = (reg_ddrc_ecc_type) ? ie_data_out_phy        : data_out; // data_out_w has 1 or 2 cycles delay compared with "data_out".
assign rt_rd_ra_ecc_info_int_w = (reg_ddrc_ecc_type) ? ie_rt_rd_ecc_info : rt_rd_ra_ecc_info_int;
assign rt_rd_ra_ecc_word_int_w = (reg_ddrc_ecc_type) ? ie_rt_rd_ecc_word : rt_rd_ra_ecc_word_int;



assign rd_rw_rdata_valid_w = rt_rd_data_valid_int_w
                             &  ~mrr_operation_on_int_w                          // No valid to WU when MRR is ON
                             & (rt_rd_rmwtype_int_w != `MEMC_RMW_TYPE_NO_RMW) // No valid for normal read operations. only for RMW.
                           ;
     
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
assign rd_wu_rdata_valid_w = rt_rd_data_valid_int_w
                             &  ~mrr_operation_on_int_w // No valid to WU when MRR is ON
                           ;
//spyglass enable_block W528

assign rd_ra_rdata_valid_w =  rt_rd_data_valid_int_w
                             & ((rt_rd_rmwtype_int_w==`MEMC_RMW_TYPE_RMW_CMD)       ||
                                (rt_rd_rmwtype_int_w==`MEMC_RMW_TYPE_NO_RMW)          )
                             & ~mrr_operation_on_int_w
                          ;


//---------------------------
// Flopped outputs to WU & RW modules
//---------------------------
wire i_rd_ra_ecc_corrected_err;
assign i_rd_ra_ecc_corrected_err = rd_wu_ecc_corrected_err;
wire i_rd_ra_ecc_uncorrected_err;
assign i_rd_ra_ecc_uncorrected_err = rd_wu_ecc_uncorrected_err;
assign rd_ra_ecc_corrected_err = i_rd_ra_ecc_corrected_err;
assign rd_ra_ecc_uncorrected_err = i_rd_ra_ecc_uncorrected_err;


wire i_rd_wu_ecc_uncorrected_err_w;
wire i_rd_wu_ecc_corrected_err_w;
reg  i_rd_wu_ecc_corrected_err_r;
wire i_rd_wu_ecc_uncorrected_err_mux;
wire i_rd_wu_ecc_corrected_err_mux;

assign i_rd_wu_ecc_uncorrected_err_w = rd_wu_ecc_uncorrected_err_w & rd_wu_rdata_valid_w
                                        & ~rt_rd_rd_addr_err_int_w    // Ignore ECC when address is wrong
                                        ;

assign i_rd_wu_ecc_corrected_err_w   = rd_wu_ecc_corrected_err_w & rd_wu_rdata_valid_w
                                        & ~rt_rd_rd_addr_err_int_w    // Ignore ECC when address is wrong
                                        ;

assign i_rd_wu_ecc_uncorrected_err_mux = i_rd_wu_ecc_uncorrected_err_w;
assign i_rd_wu_ecc_corrected_err_mux = i_rd_wu_ecc_corrected_err_w;

//assign rd_ra_ecc_corrected_err   = rd_wu_ecc_corrected_err;     // copy ecc_corrected_err to wu and ra.
//assign rd_ra_ecc_uncorrected_err = rd_wu_ecc_uncorrected_err; // copy ecc_uncorrected_err to wu and ra.
always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
   if (~core_ddrc_rstn) begin
      i_rd_wu_ecc_corrected_err     <= 1'b0;
      i_rd_wu_ecc_uncorrected_err   <= 1'b0;
   end else if(ddrc_cg_en) begin     // flops not in reset
    // flop the uncorr error signal before giving to output - sync with rd_ra_rdata_valid
    i_rd_wu_ecc_uncorrected_err       <= i_rd_wu_ecc_uncorrected_err_mux;
    i_rd_wu_ecc_corrected_err         <= i_rd_wu_ecc_corrected_err_mux;
   end


wire [UMCTL2_WDATARAM_PAR_DW-1:0] rd_rw_rdata_parity_w;
// spyglass disable_block W164b
// SMD: LHS: 'rd_rw_rdata_parity_w' width 80 is greater than RHS: 'parity_out_w' width 64 in assignment
// SJ: Waived for Backward compatibility
assign rd_rw_rdata_parity_w = parity_out_w;
// spyglass enable_block W164b

always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin
    i_rd_wu_rdata_valid   <= 1'b0;
    i_rd_rw_rdata_valid   <= 1'b0;
    i_rd_wu_info          <= {WU_INFO_WIDTH{1'b0}};
    i_rd_rw_rdata         <= {CORE_DATA_WIDTH{1'b0}};
    i_rd_rw_rdata_par     <= {UMCTL2_WDATARAM_PAR_DW{1'b0}};
    i_rd_wu_word_num      <= {WORD_BITS{1'b0}};
  end
  else if(ddrc_cg_en) begin     // flops not in reset

    i_rd_wu_rdata_valid   <= rd_wu_rdata_valid_w;
    i_rd_wu_info          <= rt_rd_wu_info_int_w;
    i_rd_rw_rdata         <= data_out_w[CORE_DATA_WIDTH-1:0];
    i_rd_rw_rdata_valid   <= rd_rw_rdata_valid_w;
    i_rd_rw_rdata_par     <= rd_rw_rdata_parity_w;
    i_rd_wu_word_num      <= ie_rt_rd_ecc_word;
    // `ifdef DDRCTL_METADATA_EN_1
    // i_rd_rw_rdata_meta     <= data_out_meta_w;
    // `endif   
  end






wire [CORE_MASK_WIDTH-1:0]  rd_ra_rdata_parity_w;
assign rd_ra_rdata_parity_w = parity_out_w;

wire [CORE_MASK_WIDTH-1:0]  default_rdata_parity_w;
assign default_rdata_parity_w = {CORE_MASK_WIDTH{reg_ddrc_oc_parity_type}};


assign i_rd_ra_rdata_w =
                           (rt_rd_rd_addr_err_int_w == 1'b1) ? {DATA_WIDTH_NO_ECC{1'b0}} : 
                           data_out_w[CORE_DATA_WIDTH-1:0];

assign i_rd_ra_rdata_parity_w =
                        (rt_rd_rd_addr_err_int_w == 1'b1) ? default_rdata_parity_w : 
                         rd_ra_rdata_parity_w;

assign i_rd_ra_rd_addr_err_w = rt_rd_rd_addr_err_int_w & rd_ra_rdata_valid_w;

assign i_rd_ra_dram_addr_w =                           (rt_rd_rd_addr_err_int_w == 1'b1) ? {ECC_INFO_WIDTH+WORD_BITS{1'b0}} : 
                           {rt_rd_ra_ecc_info_int_w, rt_rd_ra_ecc_word_int_w};



//--------------------------
// Flopped outputs to RA
//--------------------------
always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
  if (~core_ddrc_rstn) begin

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
    i_rd_ra_rdata_valid   <= 1'b0;
 //spyglass enable_block W528
    i_rd_ra_eod           <= 1'b0;
    i_rd_wu_partial       <= {CMD_LEN_BITS{1'b0}};
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
    i_rd_ra_partial       <= {CMD_LEN_BITS{1'b0}};
//spyglass enable_block W528
    i_rd_ra_info          <= {RA_INFO_WIDTH{1'b0}};
    i_rd_ra_rdata         <= {DATA_WIDTH_NO_ECC{1'b0}};
    i_rd_ra_rdata_parity  <= {CORE_MASK_WIDTH{1'b0}};
    i_rd_ra_rd_addr_err <= 1'b0;
    i_rd_ra_dram_addr    <= {`DDRCTL_HIF_DRAM_ADDR_WIDTH{1'b0}};
  end
  else if(ddrc_cg_en) begin     // flops not in reset
    // Assert data valid in the same cycle as the last data is received;
    //  calculated as the cycle before the last data is received, then flopped
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
    i_rd_ra_rdata_valid   <= rd_ra_rdata_valid_w;
//spyglass enable_block W528
    i_rd_ra_eod           <= rt_rd_eod_int_w;
    i_rd_wu_partial       <= rt_rd_partial_int_w;
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
    i_rd_ra_partial       <= rt_rd_partial_int_w;
//spyglass enable_block W528
    i_rd_ra_info          <= rt_rd_ra_info_int_w;
    i_rd_ra_rdata         <= i_rd_ra_rdata_w;
    i_rd_ra_rdata_parity <= i_rd_ra_rdata_parity_w;
    i_rd_ra_rd_addr_err <= i_rd_ra_rd_addr_err_w;
    i_rd_ra_dram_addr  <= i_rd_ra_dram_addr_w;
  end


// the MRR operation is a BL4 operation on the DRAM
// it results in 2 cycles of read data on the DFI interface
// the actual MRR data is 8-bits wide and is contained in the 
// least significant 8-bits of the 1st clock of the MRR data on the DFI bus

   assign mr4                =
                      //`ifdef MEMC_FREQ_RATIO_4
                      //`endif // MEMC_FREQ_RATIO_4
                              (!sel_rt_rd_rd_mrr_snoop) & 
                               sel_rt_rd_rd_mrr     & sel_rt_rd_rd_valid;

  wire mrr_snoop;
  assign mrr_snoop           = sel_rt_rd_rd_mrr_snoop & sel_rt_rd_rd_mrr & sel_rt_rd_rd_valid;     

   assign mrr_ext            = sel_rt_rd_rd_mrr_ext & sel_rt_rd_rd_valid;

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in testbench file (ddrc_dbgcam_mon.sv)
  // goes high when the MRR valid data is on the bus
  // used to disable the normal read data valid going to other modules
   assign mrr_operation_on   = 
                               mr4 || 
                               mrr_snoop ||
                               mrr_ext;
//spyglass enable_block W528

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
       assign mrr_operation_on_r = 1'b0;
//spyglass enable_block W528

// MRR data - coming through the ECC decoder
   assign i_rd_mrr_data        = ph_rd_rdata_no_dbi[`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0];

// generating a one cycle pulse for the MRR data valid
// data_out used in the above logic is flopped (coming through the ECC decoder)
// and so the MRR data valid is alsp generated from the flopped signals

   assign i_rd_mrr_data_valid  = 
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
                                 mrr_ext & sel_rt_rd_rd_mrr_sod;
   assign i_rd_mr4_data_valid  = 
                              //`ifdef MEMC_FREQ_RATIO_4
                              //`endif // MEMC_FREQ_RATIO_4
                                 lpddr_mode    ? mr4 & sel_rt_rd_rd_mrr_sod :
                                 1'b0;


// All the flops related to MRR operation
   always @ (posedge co_yy_clk or negedge core_ddrc_rstn)
     if (~core_ddrc_rstn) begin
          r_rd_mrr_data         <= {`MEMC_DRAM_TOTAL_DATA_WIDTH{1'b0}};
          r_rd_mrr_data_valid   <= 1'b0;
          r_rd_mr4_data_valid   <= 1'b0;
     end
     else if(ddrc_cg_en) begin
          r_rd_mrr_data       <= i_rd_mrr_data;
          r_rd_mrr_data_valid <= i_rd_mrr_data_valid;
          r_rd_mr4_data_valid <= i_rd_mr4_data_valid;
     end

   // drive output from registered signals
   assign rd_mrr_data        = r_rd_mrr_data;
   assign rd_mrr_data_valid  = r_rd_mrr_data_valid;
   assign rd_mr4_data_valid  = r_rd_mr4_data_valid;

   // Latch MRR data
   always_ff @ (posedge co_yy_clk, negedge core_ddrc_rstn) begin
      if (~core_ddrc_rstn) begin
         mrr_data_r <= {`MEMC_DRAM_TOTAL_DATA_WIDTH{1'b0}};
      end
      else if (rd_mrr_data_valid) begin
         mrr_data_r <= rd_mrr_data;
      end
   end

   always_ff @ (posedge co_yy_clk, negedge core_ddrc_rstn) begin
      if (~core_ddrc_rstn) begin
         mrr_recieved_r <= 1'b0;
      end
      else if (reg_ddrc_mrr_done_clr) begin
         mrr_recieved_r <= 1'b0;
      end
      else if (rd_mrr_data_valid) begin
         mrr_recieved_r <= 1'b1;
      end
   end

   assign ddrc_reg_mrr_done = mrr_recieved_r;
   assign ddrc_reg_mrr_data = mrr_data_r;

// OCPAR section
//spyglass disable_block W528
//SMD: A signal or variable is set but never read - "parity_out"
//SJ: Used in generate statement and therefore must always exist.
generate
if (OCPAR_EN==1 || OCECC_EN==1) begin: OC_PAR_OR_ECC_en
   wire [PHY_DATA_WIDTH-1:0]     poison_data;
   wire                          poison_valid, poison_valid_w;
   wire                          uncorr_err, corr_err;
   wire    [CORE_MASK_WIDTH-1:0] parity_ncorr, parity_ncorr_w;
   wire                          op_is_scrub;
   wire [RMW_TYPE_BITS-1:0]      rmw_type;
   wire                          iecc_en;
   wire  [CORE_DATA_WIDTH-1:0]   data_in_post_dec;
   wire                          i_reg_ddrc_par_poison_loc_rd_iecc_type;
   wire                          advecc_en;


      assign op_is_scrub   = 1'b0;
   

      // only used by ocpar_rd_gen and only if INLINE_ECC=1
      assign iecc_en  = (reg_ddrc_ecc_type) ? |dh_rd_ecc_mode : 1'b0;

      assign data_in_post_dec = (reg_ddrc_ecc_type) ? data_out_w[CORE_DATA_WIDTH-1:0] : data_out_ecc;
      assign poison_valid     = (reg_ddrc_ecc_type) ? (rt_rd_ie_ecc_vld & ~reg_ddrc_par_poison_loc_rd_iecc_type)   : rt_rd_rd_valid_r;
      assign poison_valid_w   = (reg_ddrc_ecc_type) ? (rd_ra_rdata_valid_w & reg_ddrc_par_poison_loc_rd_iecc_type) : rd_ra_rdata_valid_w;
      assign i_reg_ddrc_par_poison_loc_rd_iecc_type = (reg_ddrc_ecc_type) ? reg_ddrc_par_poison_loc_rd_iecc_type : 1'b0;

   
   assign uncorr_err    = rd_wu_ecc_uncorrected_err_w;
   assign corr_err      = rd_wu_ecc_corrected_err_w;
   assign rmw_type      = {RMW_TYPE_BITS{1'b0}};

   assign advecc_en = 1'b0;

   ocpar_rd_gen
   
   #(
      .CORE_DATA_WIDTH  (CORE_DATA_WIDTH),
      .PHY_DATA_WIDTH   (PHY_DATA_WIDTH),
      .DRAM_DATA_WIDTH  (SECDED_CORESIDE_LANE_WIDTH),
      .SECDED_LW        (SECDED_1B_LANE_WIDTH),
      .SECDED_LANES     (SECDED_LANES),
      .ECC_EN           (ECC_EN),
      .SIDEBAND_ECC     (0),
      .INLINE_ECC       (`MEMC_INLINE_ECC_EN),
      .FREQ_RATIO       (FR),
      .SLICE_DW         (OCPAR_SLICE_DW),
      .PAR_DW           (CORE_MASK_WIDTH),
      .RSD_PIPELINE   (`DDRCTL_RSD_PIPELINE_EN))
   rd_parity_gen
   (
      .core_ddrc_core_clock   (co_yy_clk),
      .core_ddrc_rstn         (core_ddrc_rstn),
      .parity_en              (OCECC_EN==1 ? ocecc_en : reg_ddrc_oc_parity_en),
      .parity_type            (OCECC_EN==1 ? 1'b0 : reg_ddrc_oc_parity_type),
      .frequency_ratio        (dh_rd_frequency_ratio),
      .rd_valid               (sel_rt_rd_rd_valid),
      .uncorr_err             (uncorr_err),
      .corr_err               (corr_err),
      .iecc_en                (iecc_en),
      .ecc_mode_is_advecc     (1'b0),
      .data_in                (ph_rd_rdata_no_dbi_exp),
      .data_in_ecc            (data_in_post_dec),
      .parity_out             (parity_ncorr),
      .parity_out_w           (parity_ncorr_w));

   // poison the parity
   ocpar_poison
   
   #(
      .DATA_WIDTH    (PHY_DATA_WIDTH),
      .PAR_WIDTH     (CORE_MASK_WIDTH),
      .DATA_PATH_POISON (`MEMC_INLINE_ECC_EN), // only for INLINE_ECC case
      .DATA_PATH_POISON_SW (`MEMC_SIDEBAND_ECC_EN), // only for SIDEBAND_ECC case
      .BYTE_WIDTH    (OCPAR_SLICE_DW),
      .BYTE_POISON   (0), 
      .BYTE_POISON_SW(0) 
    )
   poison_rdata
   (
     .clk           (co_yy_clk),
     .rst_n         (core_ddrc_rstn),
     .corrupt_twice (1'b0), // this is used only for IECC write path
     .data_valid    (poison_valid), 
     .data_valid_w  (poison_valid_w),
     .parity_in     (parity_ncorr),
     .parity_in_w   (parity_ncorr_w),
     .byte_num      (1'b0), // not used
      .dpp_support_en (reg_ddrc_ecc_type), // only data path poison support if IE case
     .pbp_support_en (1'b0), // not used
     .poison_en     (OCECC_EN==1 ? ocecc_poison_pgen_rd : reg_ddrc_par_poison_en),
     .poison_ie_type(i_reg_ddrc_par_poison_loc_rd_iecc_type),
     .poison_ie_clr (OCECC_EN==1 ? ocecc_uncorr_err_intr_clr : reg_ddrc_par_rdata_err_intr_clr),
     .parity_out    (parity_out),
     .parity_out_w  (parity_out_w));


end
else begin: OC_PAR_OR_ECC_nen
   assign parity_out          = {CORE_MASK_WIDTH{1'b0}};
   assign parity_out_w        = {CORE_MASK_WIDTH{1'b0}};
end
endgenerate
//spyglass enable_block W528



// Generate rd_ih_ie_re_rdy to it_bt_item to indicate read ecc is return (re_rdy=1), 
// we think read ie data is not return if detected crc err on the ie data.
assign rd_ih_ie_re_rdy = rd_ecc_ram_wr;


//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ:  This is temporary. It should be connected to APB register
assign rd_dh_rd_crc_err_rank = {RANK_BITS_DUP{1'b0}};
assign rd_dh_rd_crc_err_cid  = {CID_WIDTH_DUP{1'b0}};
assign rd_dh_rd_crc_err_bg   = {BG_BITS_DUP{1'b0}};
assign rd_dh_rd_crc_err_bank = {BANK_BITS{1'b0}};
assign rd_dh_rd_crc_err_row  = {ROW_BITS{1'b0}};
assign rd_dh_rd_crc_err_col  = {COL_BITS{1'b0}};
assign rd_dh_crc_poison_inject_complete = 1'b0;
assign rd_dh_rd_crc_err_max_reached_int_nibble = {MAX_NUM_NIBBLES{1'b0}};
assign rd_dh_rd_crc_err_max_reached_int = 1'b0;
assign rd_dh_rd_crc_err_cnt_nibble = {(MAX_NUM_NIBBLES*12){1'b0}};
assign rd_crc_err = 1'b0;
//spyglass enable_block W528


//------------------------------------------------------------
// LPDDR5 Link-ECC decoder instantiation
//------------------------------------------------------------
// - rt signals are delayed extra 2-cycles
// - rdata will be corrected when 1-bit error happens
//------------------------------------------------------------
wire rd_link_ecc_uncorr_err_w;
rd_linkecc_decoder

 #(
       .CMD_LEN_BITS      (CMD_LEN_BITS)
      ,.PHY_DATA_WIDTH    (PHY_DATA_WIDTH)
      ,.PHY_DBI_WIDTH     (PHY_DBI_WIDTH)
      ,.RMW_TYPE_BITS     (RMW_TYPE_BITS)
      ,.RA_INFO_WIDTH     (RA_INFO_WIDTH)
      ,.ECC_INFO_WIDTH    (ECC_INFO_WIDTH)
      ,.WU_INFO_WIDTH     (WU_INFO_WIDTH)
      ,.IE_RD_TYPE_BITS   (IE_RD_TYPE_BITS)
      ,.IE_BURST_NUM_BITS (IE_BURST_NUM_BITS)
      ,.BT_BITS           (BT_BITS)
      ,.WORD_BITS         (WORD_BITS)
      ,.BLK_BITS          (BLK_BITS)
      ,.CORE_MASK_WIDTH   (CORE_MASK_WIDTH)
      ,.DRAM_BYTE_NUM     (DRAM_BYTE_NUM)
      ,.LRANK_BITS        (LRANK_BITS)
)
rd_linkecc_decoder (
       .co_yy_clk                   (co_yy_clk)
      ,.core_ddrc_rstn              (core_ddrc_rstn)
      ,.ddrc_cg_en                  (ddrc_cg_en)
      ,.reg_ddrc_rd_link_ecc_enable         (reg_ddrc_rd_link_ecc_enable)
      ,.reg_ddrc_rd_link_ecc_uncorr_cnt_clr (reg_ddrc_rd_link_ecc_uncorr_cnt_clr)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_clr(reg_ddrc_rd_link_ecc_uncorr_intr_clr)
      ,.reg_ddrc_rd_link_ecc_uncorr_intr_en (reg_ddrc_rd_link_ecc_uncorr_intr_en)
      ,.reg_ddrc_rd_link_ecc_corr_cnt_clr   (reg_ddrc_rd_link_ecc_corr_cnt_clr)
      ,.reg_ddrc_rd_link_ecc_corr_intr_clr  (reg_ddrc_rd_link_ecc_corr_intr_clr)
      ,.reg_ddrc_rd_link_ecc_corr_intr_en   (reg_ddrc_rd_link_ecc_corr_intr_en)
      ,.reg_ddrc_linkecc_poison_byte_sel    (reg_ddrc_linkecc_poison_byte_sel)
      ,.reg_ddrc_linkecc_poison_rw          (reg_ddrc_linkecc_poison_rw)
      ,.reg_ddrc_linkecc_poison_type        (reg_ddrc_linkecc_poison_type)
      ,.reg_ddrc_linkecc_poison_inject_en   (reg_ddrc_linkecc_poison_inject_en)
      ,.rt_rd_link_ecc_info                 (rt_rd_link_ecc_info)
      ,.reg_ddrc_rd_link_ecc_err_rank_sel   (reg_ddrc_rd_link_ecc_err_rank_sel)
      ,.reg_ddrc_rd_link_ecc_err_byte_sel   (reg_ddrc_rd_link_ecc_err_byte_sel)

      ,.ddrc_reg_link_ecc_corr_rank         (ddrc_reg_link_ecc_corr_rank)
      ,.ddrc_reg_link_ecc_corr_bg           (ddrc_reg_link_ecc_corr_bg)
      ,.ddrc_reg_link_ecc_corr_bank         (ddrc_reg_link_ecc_corr_bank)
      ,.ddrc_reg_link_ecc_corr_row          (ddrc_reg_link_ecc_corr_row)
      ,.ddrc_reg_link_ecc_corr_col          (ddrc_reg_link_ecc_corr_col)
      ,.ddrc_reg_link_ecc_uncorr_rank       (ddrc_reg_link_ecc_uncorr_rank)
      ,.ddrc_reg_link_ecc_uncorr_bg         (ddrc_reg_link_ecc_uncorr_bg)
      ,.ddrc_reg_link_ecc_uncorr_bank       (ddrc_reg_link_ecc_uncorr_bank)
      ,.ddrc_reg_link_ecc_uncorr_row        (ddrc_reg_link_ecc_uncorr_row)
      ,.ddrc_reg_link_ecc_uncorr_col        (ddrc_reg_link_ecc_uncorr_col)

      // input from rt module
      ,.ph_rd_rdbi_n                (ph_rd_rdbi_n)
      ,.ph_rd_rdata                 (ph_rd_rdata)
      ,.rt_rd_rd_valid              (rt_rd_rd_valid)
      ,.rt_rd_eod                   (rt_rd_eod)
      ,.rt_rd_partial               (rt_rd_partial)
      ,.rt_rd_ra_info               (rt_rd_ra_info)
      ,.rt_rd_rd_mrr                (rt_rd_rd_mrr)
      ,.rt_rd_rd_mrr_ext            (rt_rd_rd_mrr_ext)
      ,.rt_rd_rd_mrr_snoop          (rt_rd_rd_mrr_snoop)
      ,.rt_rd_rd_mrr_sod            (rt_rd_rd_mrr_sod)
      ,.rt_rd_rmwtype               (rt_rd_rmwtype)
      ,.rt_rd_wu_info               (rt_rd_wu_info)
      ,.rt_rd_rmw_word_sel          (rt_rd_rmw_word_sel)
      ,.rt_rd_ie_bt                 (rt_rd_ie_bt)
      ,.rt_rd_ie_rd_type            (rt_rd_ie_rd_type)
      ,.rt_rd_ie_blk_burst_num      (rt_rd_ie_blk_burst_num)
      ,.rt_rd_ecc_info              (rt_rd_ecc_info)
      ,.rt_rd_ecc_word              (rt_rd_ecc_word)
      ,.rt_rd_eccap                 (rt_rd_eccap)
      ,.rt_rd_rd_addr_err           (rt_rd_rd_addr_err)

      // output selected rt signals
      ,.sel_ph_rd_rdbi_n            (sel_ph_rd_rdbi_n)
      ,.sel_ph_rd_rdata             (sel_ph_rd_rdata)
      ,.sel_rt_rd_rd_valid          (sel_rt_rd_rd_valid)
      ,.sel_rt_rd_eod               (sel_rt_rd_eod)
      ,.sel_rt_rd_partial           (sel_rt_rd_partial)
      ,.sel_rt_rd_ra_info           (sel_rt_rd_ra_info)
      ,.sel_rt_rd_rd_mrr            (sel_rt_rd_rd_mrr)
      ,.sel_rt_rd_rd_mrr_ext        (sel_rt_rd_rd_mrr_ext)
      ,.sel_rt_rd_rd_mrr_snoop      (sel_rt_rd_rd_mrr_snoop)
      ,.sel_rt_rd_rd_mrr_sod        (sel_rt_rd_rd_mrr_sod)
      ,.sel_rt_rd_rmwtype           (sel_rt_rd_rmwtype)
      ,.sel_rt_rd_wu_info           (sel_rt_rd_wu_info)
      ,.sel_rt_rd_rmw_word_sel      (sel_rt_rd_rmw_word_sel)
      ,.sel_rt_rd_ie_bt             (sel_rt_rd_ie_bt)
      ,.sel_rt_rd_ie_rd_type        (sel_rt_rd_ie_rd_type)
      ,.sel_rt_rd_ie_blk_burst_num  (sel_rt_rd_ie_blk_burst_num)
      ,.sel_rt_rd_ecc_info          (sel_rt_rd_ecc_info)
      ,.sel_rt_rd_ecc_word          (sel_rt_rd_ecc_word)
      ,.sel_rt_rd_eccap             (sel_rt_rd_eccap)
      ,.sel_rt_rd_rd_addr_err       (sel_rt_rd_rd_addr_err)
      ,.ddrc_reg_rd_linkecc_poison_complete (ddrc_reg_rd_linkecc_poison_complete)
      ,.ddrc_reg_rd_link_ecc_uncorr_cnt     (ddrc_reg_rd_link_ecc_uncorr_cnt)
      ,.ddrc_reg_rd_link_ecc_corr_cnt       (ddrc_reg_rd_link_ecc_corr_cnt)
      ,.ddrc_reg_rd_link_ecc_err_syndrome   (ddrc_reg_rd_link_ecc_err_syndrome)
      ,.ddrc_reg_rd_link_ecc_uncorr_err_int (ddrc_reg_rd_link_ecc_uncorr_err_int)
      ,.ddrc_reg_rd_link_ecc_corr_err_int   (ddrc_reg_rd_link_ecc_corr_err_int)
      ,.rd_link_ecc_uncorr_err              (rd_link_ecc_uncorr_err_w)
);

// Align rd_link_ecc_uncorr_err to the read data
localparam RD_LINK_ECC_UE_DELAY_MAX =
  1                                     // datapath delay at i_rd_ra_rdata
 + 2     // datapath delay in rd_ie_rdata_ctl
  ;
wire[`log2(RD_LINK_ECC_UE_DELAY_MAX-1):0] rd_link_ecc_ue_delay_idx =
  0                                     // 0 = +1 -1. +1 from datapath delay at i_rd_ra_rdata. -1 due to INDEX is delay - 1
  + (dh_rd_ecc_mode>0 ? 2 : 0)          // datapath delay in rd_ie_rdata_ctl
  ;

reg [RD_LINK_ECC_UE_DELAY_MAX-1:0] rd_link_ecc_uncorr_err_d;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  integer i;
  if (~core_ddrc_rstn) begin
    rd_link_ecc_uncorr_err_d <= 0;
  end else if(ddrc_cg_en) begin
    for (i = 0; i < RD_LINK_ECC_UE_DELAY_MAX; i=i+1)
      //spyglass disable_block SelfDeterminedExpr-ML
      //SMD: Self determined expression '(i - 1)' found in module 'rd'
      //SJ: 'i-1' can never be a negative since it's gated by the i==0?, so i-1 is safe
      rd_link_ecc_uncorr_err_d[i] <= i==0 ? rd_link_ecc_uncorr_err_w : rd_link_ecc_uncorr_err_d[i-1];
      //spyglass enable_block SelfDeterminedExpr-ML
  end
end

genvar le_ue_dly_idx;
wire [RD_LINK_ECC_UE_DELAY_MAX-1:0] rd_link_ecc_uncorr_err_d_per_dly;
reg                                 rd_link_ecc_uncorr_err_tmp;

generate
  for (le_ue_dly_idx=0; le_ue_dly_idx<RD_LINK_ECC_UE_DELAY_MAX; le_ue_dly_idx=le_ue_dly_idx+1) begin : gen_rd_link_ecc_uncorr_err_d_per_dly
      assign rd_link_ecc_uncorr_err_d_per_dly[le_ue_dly_idx] = (le_ue_dly_idx==rd_link_ecc_ue_delay_idx)? rd_link_ecc_uncorr_err_d[le_ue_dly_idx] : 1'b0;
  end
endgenerate

always @(*) begin
  rd_link_ecc_uncorr_err_tmp = 1'b0;
  for (int i=0; i<RD_LINK_ECC_UE_DELAY_MAX; i++) begin
      rd_link_ecc_uncorr_err_tmp = rd_link_ecc_uncorr_err_tmp | rd_link_ecc_uncorr_err_d_per_dly[i];
  end
end

assign rd_link_ecc_uncorr_err = rd_link_ecc_uncorr_err_tmp;




assign rd_rw_kbd = {`DDRCTL_HIF_KBD_WIDTH{1'b0}};
assign rd_ra_kbd = {`DDRCTL_HIF_KBD_WIDTH{1'b0}};



//-----------------------------------------------------------------------------
// No Extra pipeline (Non-RETRY-config, Non-DDR5-config, FREQ_RATIO=2 config)
assign i_rd_ra_rdata_valid_mux   = i_rd_ra_rdata_valid;
assign i_rd_ra_rdata_mux         = i_rd_ra_rdata;
assign i_rd_ra_rdata_parity_mux  = i_rd_ra_rdata_parity;
assign i_rd_ra_eod_mux           = i_rd_ra_eod;
assign i_rd_wu_partial_mux       = i_rd_wu_partial;
assign i_rd_ra_partial_mux       = i_rd_ra_partial;
assign i_rd_ra_info_mux          = i_rd_ra_info;
assign i_rd_ra_dram_addr_mux     = i_rd_ra_dram_addr;
assign i_rd_ra_rd_addr_err_mux   = i_rd_ra_rd_addr_err;



assign rd_ra_rdata_valid_retry = 1'b0;
assign rd_wu_rdata_valid_retry = 1'b0;
assign rd_ra_eod_retry = 1'b0;
assign rd_ra_info_retry = {RA_INFO_WIDTH{1'b0}};
assign rd_crc_err_retry = 1'b0;
assign rd_ra_ecc_uncorrected_err_retry = 1'b0;


  assign ddrc_reg_ecc_corr_err_per_rank_intr      = {ECC_CORR_ERR_PER_RANK_INTR_WIDTH{1'b0}};
  assign ddrc_reg_ecc_corr_err_cnt_rank0          = {ECC_CORR_ERR_CNT_RANK_WIDTH{1'b0}};
  assign ddrc_reg_ecc_corr_err_cnt_rank1          = {ECC_CORR_ERR_CNT_RANK_WIDTH{1'b0}};
  assign ddrc_reg_ecc_corr_err_cnt_rank2          = {ECC_CORR_ERR_CNT_RANK_WIDTH{1'b0}};
  assign ddrc_reg_ecc_corr_err_cnt_rank3          = {ECC_CORR_ERR_CNT_RANK_WIDTH{1'b0}};

//-----------------------------------------------------------------------------
// Driving to 0 for non EAPAR config
//-----------------------------------------------------------------------------
assign ddrc_reg_eapar_error            = {EAPAR_SIZE_SECDED_LANES{1'b0}}; 
assign ddrc_reg_eapar_err_cnt          = 16'd0;
assign ddrc_reg_eapar_err_syndromes    = {`MEMC_ECC_SYNDROME_WIDTH{1'b0}};
assign ddrc_reg_eapar_err_cb_syndromes = {8{1'b0}};
assign ddrc_reg_eapar_err_sbr_rd       = 1'b0;
assign ddrc_reg_eapar_err_col          = {COL_BITS{1'b0}};
assign ddrc_reg_eapar_err_bank         = {BANK_BITS{1'b0}};
assign ddrc_reg_eapar_err_bg           = {BG_BITS{1'b0}};
assign ddrc_reg_eapar_err_row          = {ROW_BITS{1'b0}};
assign ddrc_reg_eapar_err_cid          = {CID_WIDTH_DUP{1'b0}};
assign ddrc_reg_eapar_err_rank         = {RANK_BITS_DUP{1'b0}};
assign rd_wu_eapar_err                 = 1'b0;
assign rd_ra_eapar_err                 = 1'b0;
assign rd_wu_eapar                     = {`DDRCTL_EAPAR_SIZE{1'b0}};

  assign ime_i_rd_dec_req           = {$bits(ime_i_rd_dec_req          ){1'b0}};
  assign ime_i_rd_dec_length        = {$bits(ime_i_rd_dec_length       ){1'b0}};
  assign ime_i_rd_dec_offset        = {$bits(ime_i_rd_dec_offset       ){1'b0}};
  assign ime_i_rd_dec_bypass        = {$bits(ime_i_rd_dec_bypass       ){1'b0}};
  assign ime_i_rd_twk_val_index     = {$bits(ime_i_rd_twk_val_index    ){1'b0}};
  assign ime_i_rd_cipher_data       = {$bits(ime_i_rd_cipher_data      ){1'b0}};
  assign ime_i_rd_cipher_data_valid = {$bits(ime_i_rd_cipher_data_valid){1'b0}};
  assign ime_i_rd_cipher_data_last  = {$bits(ime_i_rd_cipher_data_last ){1'b0}};
  assign ime_i_rd_passthru          = {$bits(ime_i_rd_passthru         ){1'b0}};                       

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

  localparam CATEGORY = 5; // Allows groups of assertions to be enabled/disabled at the same time

  //word_num overflow
  assert_never #(0, 0, "word_num overflow", CATEGORY) a_word_num_overflow
    (co_yy_clk, core_ddrc_rstn, (word_num_wider[5]==1'b1)); 

  // VCS coverage off
  wire le_uncorr_detected = |(rd_linkecc_decoder.uncorr_err_byte);
  bit [PHY_DATA_WIDTH-1:0]  le_corr_rdata_ue[$], le_corr_rdata_ue_front;
  always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if(le_uncorr_detected) begin
      le_corr_rdata_ue.push_back(rd_linkecc_decoder.corr_rdata[             0 +:PHY_DATA_WIDTH]); // push lower half of data which has UE
      le_corr_rdata_ue.push_back(rd_linkecc_decoder.corr_rdata[PHY_DATA_WIDTH +:PHY_DATA_WIDTH]); // push upper half of data which has UE
      le_corr_rdata_ue_front <= le_corr_rdata_ue[0];  // set le_corr_rdata_ue_front to be lower half
    end
    if(rd_link_ecc_uncorr_err) begin
      le_corr_rdata_ue.pop_front(); // remove lower half
      le_corr_rdata_ue_front <= le_corr_rdata_ue.size()>0 ? le_corr_rdata_ue[0] : 0;  // set le_corr_rdata_ue_front to be upper half
    end
  end
  // VCS coverage on

  // Check if read Link ECC UE signal is aligned to the read data containing UE
  //   When rd_linkecc_decoder detects UE, read data is stored to le_corr_rdata_ue.
  //   If output HIF rdata rd_ra_rdata is the same to previously captured le_corr_rdata_ue while output UE signal is high, we can say data with UE and UE signal is aligned
  property p_le_uncorr_align_check;
    @(negedge co_yy_clk) disable iff(!core_ddrc_rstn || i_rd_ra_rd_addr_err)
      rd_link_ecc_uncorr_err |-> $countones(rd_ra_rdata ^ le_corr_rdata_ue_front) <= 0  // (HIF rddata) ^ (rd_linecc_decoder data). Basically they should be the same - the result of xor should be 0
        + (rd_wu_ecc_corrected_err            ? (`MEMC_DRAM_DATA_WIDTH * 16 / 64) : 0)  // Allow up to (MEMC_DRAM_DATA_WIDTH * 16 / 64) bits of flip as 1 hif-beat can have the same bits of CE in Inline ECC
      ;                                                                                 // Note that Link ECC nor Inline ECC doesn't modify rdata if there is UE
  endproperty
  a_le_uncorr_align_check : assert property (p_le_uncorr_align_check)
    else $error ("%0t ERROR: read Link ECC UE is not aligned to the read data containing an error. expected=%h, actual=%h", $time, le_corr_rdata_ue.size>0 ? le_corr_rdata_ue[0] : 12'hbad, rd_ra_rdata);

  logic [2:0] link_ecc_ue_edge;
  logic [2:0] link_ecc_ce_edge;
  logic       link_ecc_ue_data_align;
  logic       link_ecc_ce_data_align;
  always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if(!core_ddrc_rstn) begin
      link_ecc_ue_edge <= 3'b0;
      link_ecc_ce_edge <= 3'b0;
    end else begin
      link_ecc_ue_edge[0] <= $rose(|ddrc_reg_rd_link_ecc_uncorr_err_int) ? 1'b1 : 1'b0;
      link_ecc_ce_edge[0] <= $rose(|ddrc_reg_rd_link_ecc_corr_err_int)   ? 1'b1 : 1'b0;
      link_ecc_ue_edge[2:1] <= link_ecc_ue_edge[1:0];
      link_ecc_ce_edge[2:1] <= link_ecc_ce_edge[1:0];
    end 
  end
  assign link_ecc_ue_data_align = link_ecc_ue_edge[2];
  assign link_ecc_ce_data_align = link_ecc_ce_edge[2];

  //This covergroup is to observe whether the Link ECC and Inline ECC comb is verifyed.
  covergroup cg_link_ecc_inline_ecc_comb @(posedge co_yy_clk);
    cp_link_ecc_inline_ecc_err_comb: coverpoint ({rd_ra_rdata_valid, link_ecc_ue_data_align,link_ecc_ce_data_align,rd_ra_ecc_uncorrected_err,rd_ra_ecc_corrected_err}) iff(core_ddrc_rstn && (dh_rd_ecc_mode == 3'b100) && reg_ddrc_rd_link_ecc_enable) {

      bins link_dmi_ue           = {5'b1_1000}; // Link ECC UE at DMI bit
      bins link_ce_only          = {5'b1_0100}; // Link ECC CE without Inline ECC err
      //The following 2 bins don't use rd_ra_rdata_valid intentionally. Because these bins observe that the link ECC error happens on the Inline ECC parity data. 
      //The Inline ECC parity data are not propagated to HIF then rd_ra_rdata_valid is not asserted.
      bins link_ue_ecc_parity    = {5'b0_1000}; // Link ECC UE on the Inline ECC parity.
      bins link_ce_ecc_parity    = {5'b0_0100}; // Link ECC CE on the Inline ECC parity.

      wildcard bins link_ue_inline_ue     = {5'b1_1?1?}; // Link ECC UE and Inline ECC UE
      wildcard bins link_ue_inline_ce     = {5'b1_1??1}; // Link ECC UE and Inline ECC CE
      wildcard bins link_ce_inline_ue     = {5'b1_?11?}; // Link ECC CE and Inline ECC UE
      wildcard bins link_ce_inline_ce     = {5'b1_?1?1}; // Link ECC CE and Inline ECC CE
    }
  endgroup : cg_link_ecc_inline_ecc_comb
  cg_link_ecc_inline_ecc_comb cg_link_ecc_inline_ecc_comb_inst = new;








`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON 


endmodule  // rd: read data handler
