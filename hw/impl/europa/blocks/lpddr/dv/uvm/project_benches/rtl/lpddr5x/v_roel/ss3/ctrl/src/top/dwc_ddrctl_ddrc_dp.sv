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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/top/dwc_ddrctl_ddrc_dp.sv#12 $
// -------------------------------------------------------------------------
// Description:
//     DDRC data path wrapper module
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "top/dwc_ddrctl_ddrc_cpfdp_if.svh"
`include "top/dwc_ddrctl_ddrc_cpedp_if.svh"

module dwc_ddrctl_ddrc_dp 
import DWC_ddrctl_reg_pkg::*;
#(
    parameter       CORE_DATA_WIDTH             = `MEMC_DFI_DATA_WIDTH,                 // internal data width
    parameter       CORE_MASK_WIDTH             = `MEMC_DFI_DATA_WIDTH/8,               // data mask width
    parameter       WRSRAM_DATA_WIDTH           = `MEMC_DFI_DATA_WIDTH,                 // WR-SRAM data width
    parameter       WRSRAM_MASK_WIDTH           = `MEMC_DFI_DATA_WIDTH/8,               // WR-SRAM data mask width
    parameter       CORE_ECC_WIDTH              = `MEMC_DFI_ECC_WIDTH,                  // width of the internal ECC bus
    parameter       PHY_DATA_WIDTH              = `MEMC_DFI_TOTAL_DATA_WIDTH,           // data width to PHY
    parameter       PHY_MASK_WIDTH              = `MEMC_DFI_TOTAL_DATA_WIDTH/8,         // data mask width (internal to uMCTL2);
    parameter       WR_CAM_ADDR_WIDTH           = `MEMC_WRCMD_ENTRY_BITS,               // bits to address into write CAM
    parameter       WR_CAM_ADDR_WIDTH_IE        = WR_CAM_ADDR_WIDTH + `MEMC_INLINE_ECC_EN,
    parameter       WRDATA_RAM_ADDR_WIDTH       = `UMCTL2_WDATARAM_AW,
    parameter       UMCTL2_WDATARAM_DW          = `UMCTL2_WDATARAM_DW,
    parameter       PARTIAL_WR_BITS             = `UMCTL2_PARTIAL_WR_BITS,
    parameter       PARTIAL_WR_BITS_LOG2        = `log2(PARTIAL_WR_BITS),
    parameter       PW_NUM_DB                   = PARTIAL_WR_BITS,
    parameter       PW_FACTOR_HBW               = 2*`MEMC_FREQ_RATIO,
    parameter       PW_WORD_VALID_WD_HBW        = PW_NUM_DB*PW_FACTOR_HBW,
    parameter       PW_WORD_VALID_WD_MAX        = PW_WORD_VALID_WD_HBW,
    parameter       PW_WORD_CNT_WD_MAX          = `log2(PW_WORD_VALID_WD_MAX),

    parameter       WRDATA_CYCLES               = 2,

    parameter       NO_OF_BT                    = `MEMC_NO_OF_BLK_TOKEN,
    parameter       NO_OF_BWT                   = `MEMC_NO_OF_BWT,
    parameter       NO_OF_BRT                   = `MEMC_NO_OF_BRT,

    parameter       BT_BITS                     = `log2(NO_OF_BT),
    parameter       BWT_BITS                    = `log2(NO_OF_BWT),
    parameter       BRT_BITS                    = `log2(NO_OF_BRT),
    parameter       IE_WR_TYPE_BITS             = `IE_WR_TYPE_BITS,
    parameter       IE_BURST_NUM_BITS           = `MEMC_BURST_LENGTH==16 ? 5 : 3,

    parameter       ECC_RAM_DEPTH               = `MEMC_ECC_RAM_DEPTH,
    parameter       ECC_ERR_RAM_DEPTH           = NO_OF_BRT * 8,    //each burst use one entry, total have 8*BRT entries.
    parameter       DATA_BITS_PER_LANE          = 64,               // data bits per ECC engine
    parameter       ECC_BITS_PER_LANE           = 8,                // ecc bits per ECC engine
    parameter       CORE_DATA_WIDTH_EXT         = (CORE_DATA_WIDTH<DATA_BITS_PER_LANE) ? DATA_BITS_PER_LANE : CORE_DATA_WIDTH,
    parameter       ECC_DATA_WIDTH_EXT          = (CORE_DATA_WIDTH<DATA_BITS_PER_LANE) ? ECC_BITS_PER_LANE  : CORE_DATA_WIDTH/8,
    parameter       IE_SECDED_LANES             = CORE_DATA_WIDTH_EXT / DATA_BITS_PER_LANE, // number of data lanes for SEC/DED
    parameter       ECC_RAM_ADDR_BITS           = `log2(ECC_RAM_DEPTH),
    parameter       ECC_ERR_RAM_ADDR_BITS       = `log2(ECC_ERR_RAM_DEPTH),
    parameter       ECC_ERR_RAM_WIDTH           = WRDATA_CYCLES * IE_SECDED_LANES,
    parameter       IE_RD_TYPE_BITS             = `IE_RD_TYPE_BITS,

    parameter       WDATARAM_RD_LATENCY         = `DDRCTL_WDATARAM_RD_LATENCY,
    parameter       MAX_CMD_DELAY               = `UMCTL2_MAX_CMD_DELAY,
    parameter       CMD_DELAY_BITS              = `UMCTL2_CMD_DELAY_BITS,
    parameter       OCPAR_EN                    = 0,                                    // enables on-chip parity
    parameter       OCECC_EN                    = 0,                                    // enables on-chip ECC
    parameter       OCPAR_OR_OCECC_EN           = (OCPAR_EN==1 || OCECC_EN==1),
    parameter       CMD_LEN_BITS                = 1,                                    // command length bit width
    parameter       OCCAP_EN                    = 0,                                    // enables on-chip command/address path protection
    parameter       OCCAP_PIPELINE_EN           = 0,                                    // enables on-chip command/address path protection
    parameter       OCECC_MR_RD_GRANU           = 8,
    parameter       WDATA_PAR_WIDTH             = `UMCTL2_WDATARAM_PAR_DW,
    parameter       WDATA_PAR_WIDTH_EXT         = `UMCTL2_WDATARAM_PAR_DW_EXT,

    parameter       OCECC_XPI_RD_GRANU          = 64,
    parameter       OCECC_MR_BNUM_WIDTH         = 5,
    parameter       PHY_DBI_WIDTH               = `MEMC_DFI_TOTAL_DATA_WIDTH/8,         // read data DBI width from PHY
    parameter       CORE_TAG_WIDTH              = `MEMC_TAGBITS,                        // width of tag
    parameter       LRANK_BITS                  = `UMCTL2_LRANK_BITS,
    parameter       BG_BITS                     = `MEMC_BG_BITS,
    parameter       BANK_BITS                   = `MEMC_BANK_BITS,
    parameter       RANKBANK_BITS_FULL          = LRANK_BITS + BG_BITS + BANK_BITS,
    parameter       BG_BANK_BITS                = `MEMC_BG_BANK_BITS,
    parameter       PAGE_BITS                   = `MEMC_PAGE_BITS,
    parameter       BLK_BITS                    = `MEMC_BLK_BITS,                       // 2 column bits are critical word
    parameter       MWR_BITS                    = `DDRCTL_MWR_BITS,
    parameter       ECCAP_TH_WIDTH              = `MEMC_MAX_INLINE_ECC_PER_BURST_BITS,
    parameter       CMD_RMW_BITS                = 1,                                    // unused, but '0' breaks things still...
    parameter       RMW_TYPE_BITS               = 2,                                    // 2-bit RMW type
    parameter       RANK_BITS                   = `MEMC_RANK_BITS,
    parameter       RANK_BITS_DUP               = (RANK_BITS==0)       ? 1 : RANK_BITS,
    parameter       BG_BITS_DUP                 = (BG_BITS==0)         ? 1 : BG_BITS,
    parameter       CID_WIDTH                   = `UMCTL2_CID_WIDTH,
    parameter       CID_WIDTH_DUP               = (CID_WIDTH==0)       ? 1 : CID_WIDTH,
    parameter       CORE_ECC_WIDTH_DUP          = (CORE_ECC_WIDTH==0)  ? 1 : CORE_ECC_WIDTH,

    parameter       RETRY_MAX_ADD_RD_LAT        = 2,
    parameter       RETRY_MAX_ADD_RD_LAT_LG2    = 1,

    parameter       WORD_BITS                   = `MEMC_WORD_BITS,                      // address a word within a burst
    parameter       COL_BITS                    = WORD_BITS + BLK_BITS,
    parameter       UMCTL2_SEQ_BURST_MODE       = 0,                                    // Applies LPDDR4 like squential burst mode only

    parameter       MEMC_ECC_SUPPORT            = 0,
    parameter       NUM_RANKS                   = `MEMC_NUM_RANKS,                      // max supported ranks (chip selects);

    parameter       WRDATA_RAM_DEPTH            = `UMCTL2_WDATARAM_DEPTH,               // write data RAM depth
    parameter       ECC_POISON_REG_WIDTH        = `ECC_POISON_REG_WIDTH,
    
    parameter MAX_CMD_NUM                       = 2,

    parameter       MAX_NUM_NIBBLES             = 18,
    parameter       DRAM_BYTE_NUM               = `MEMC_DRAM_TOTAL_BYTE_NUM
    ,parameter       RSD_KBD_WIDTH                     = 1
    ,parameter       HIF_KEYID_WIDTH                  = `DDRCTL_HIF_KEYID_WIDTH
    )
    (
     input                                                       core_ddrc_core_clk
    ,input                                                       core_ddrc_rstn

     //cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.o_rd_mp                             o_rd_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.i_ih_rd_mp                          i_ih_rd_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.i_ih_wu_mp                          i_ih_wu_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.i_te_wu_mp                          i_te_wu_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.i_ih_mr_mp                          i_ih_mr_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.i_te_mr_mp                          i_te_mr_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.o_mr_mp                             o_mr_cpfdpif
    ,dwc_ddrctl_ddrc_cpfdp_if.o_wu_mp                             o_wu_cpfdpif
     //ddrc_cpedpif
    ,dwc_ddrctl_ddrc_cpedp_if.i_gs_mr_mp                          i_gs_mr_ddrc_cpedpif
    ,dwc_ddrctl_ddrc_cpedp_if.i_pi_dfid_mp                        i_pi_dfid_ddrc_cpedpif
    ,dwc_ddrctl_ddrc_cpedp_if.i_pi_rt_mp                          i_pi_rt_ddrc_cpedpif
    ,dwc_ddrctl_ddrc_cpedp_if.o_wu_mp                             o_wu_ddrc_cpedpif
    ,dwc_ddrctl_ddrc_cpedp_if.o_mr_mp                             o_mr_ddrc_cpedpif

    ,input                                                       ddrc_cg_en
    ,input                                                       reg_ddrc_ecc_type
    ,input  [2:0]                                                reg_ddrc_ecc_mode 

    ,input  [1:0]                                                reg_ddrc_data_bus_width
    ,input                                                       reg_ddrc_en_2t_timing_mode
    ,input                                                       reg_ddrc_frequency_ratio
    ,input                                                       reg_ddrc_lpddr4
    ,input                                                       reg_ddrc_lpddr5
    ,input                                                       reg_ddrc_lp_optimized_write
    ,input                                                       ts_pi_mwr 

  //,input  [CORE_DATA_WIDTH-1:0]                                me_mr_rdata
    ,input  [WRSRAM_DATA_WIDTH-1:0]                              me_mr_rdata
    ,input  [WDATA_PAR_WIDTH_EXT-1:0]                            me_mr_rdata_par
    ,input                                                       write_data_parity_en
    ,input                                                       reg_ddrc_oc_parity_type
    ,input                                                       reg_ddrc_par_poison_en
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: not used in all configs 
    ,input                                                       reg_ddrc_par_wdata_err_intr_clr 
    ,input                                                       reg_ddrc_med_ecc_en
//spyglass enable_block W240
    ,output                                                      wdata_ocpar_error
    ,output                                                      wdata_ocpar_error_ie
    ,output [WRDATA_RAM_ADDR_WIDTH-1:0]                          mr_me_raddr
    ,output                                                      mr_me_re
    
  ,output [CORE_MASK_WIDTH-1:0]                                  dfi_wrdata_ecc
  ,input                                                         reg_ddrc_wr_link_ecc_enable
  ,input                                                         reg_ddrc_rd_link_ecc_enable
  ,input                                                         reg_ddrc_rd_link_ecc_uncorr_cnt_clr
  ,input                                                         reg_ddrc_rd_link_ecc_uncorr_intr_clr
  ,input                                                         reg_ddrc_rd_link_ecc_uncorr_intr_en
  ,input                                                         reg_ddrc_rd_link_ecc_corr_cnt_clr
  ,input                                                         reg_ddrc_rd_link_ecc_corr_intr_clr
  ,input                                                         reg_ddrc_rd_link_ecc_corr_intr_en
  ,input  [DRAM_BYTE_NUM-1:0]                                    reg_ddrc_linkecc_poison_byte_sel
  ,input  [DRAM_BYTE_NUM-1:0]                                    reg_ddrc_linkecc_poison_dmi_sel
  ,input                                                         reg_ddrc_linkecc_poison_rw
  ,input                                                         reg_ddrc_linkecc_poison_type
  ,input                                                         reg_ddrc_linkecc_poison_inject_en
  ,input  [RD_LINK_ECC_ERR_RANK_SEL_WIDTH  -1:0]                 reg_ddrc_rd_link_ecc_err_rank_sel
  ,input  [RD_LINK_ECC_ERR_BYTE_SEL_WIDTH  -1:0]                 reg_ddrc_rd_link_ecc_err_byte_sel
  ,output                                                        ddrc_reg_linkecc_poison_complete
  ,output [RD_LINK_ECC_UNCORR_CNT_WIDTH    -1:0]                 ddrc_reg_rd_link_ecc_uncorr_cnt
  ,output [RD_LINK_ECC_CORR_CNT_WIDTH      -1:0]                 ddrc_reg_rd_link_ecc_corr_cnt
  ,output [RD_LINK_ECC_ERR_SYNDROME_WIDTH  -1:0]                 ddrc_reg_rd_link_ecc_err_syndrome
  ,output [RD_LINK_ECC_UNCORR_ERR_INT_WIDTH-1:0]                 ddrc_reg_rd_link_ecc_uncorr_err_int
  ,output [RD_LINK_ECC_CORR_ERR_INT_WIDTH  -1:0]                 ddrc_reg_rd_link_ecc_corr_err_int
  ,output                                                        ddrc_hif_rdata_uncorr_linkecc_err

  ,output [RANK_BITS-1:0]                                        ddrc_reg_link_ecc_corr_rank
  ,output [BG_BITS-1:0]                                          ddrc_reg_link_ecc_corr_bg
  ,output [BANK_BITS-1:0]                                        ddrc_reg_link_ecc_corr_bank
  ,output [PAGE_BITS-1:0]                                        ddrc_reg_link_ecc_corr_row
  ,output [COL_BITS-1:0]                                         ddrc_reg_link_ecc_corr_col
  ,output [RANK_BITS-1:0]                                        ddrc_reg_link_ecc_uncorr_rank
  ,output [BG_BITS-1:0]                                          ddrc_reg_link_ecc_uncorr_bg
  ,output [BANK_BITS-1:0]                                        ddrc_reg_link_ecc_uncorr_bank
  ,output [PAGE_BITS-1:0]                                        ddrc_reg_link_ecc_uncorr_row
  ,output [COL_BITS-1:0]                                         ddrc_reg_link_ecc_uncorr_col
    ,input                                                       reg_ddrc_phy_dbi_mode
    ,input                                                       reg_ddrc_wr_dbi_en
    ,input                                                       reg_ddrc_dm_en
    ,input  [BURST_RDWR_WIDTH-1:0]                               reg_ddrc_burst_rdwr_int
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
    ,input  [6:0]                                                reg_ddrc_dfi_t_rddata_en
    ,input  [DFI_TPHY_WRLAT_WIDTH-1:0]                           reg_ddrc_dfi_tphy_wrlat
    ,input  [5:0]                                                reg_ddrc_dfi_tphy_wrdata
    ,input                                                       reg_ddrc_dfi_lp_en_data
    ,input  [DFI_TWCK_EN_RD_WIDTH-1:0]                           reg_ddrc_dfi_twck_en_rd     // WCK enable read timing
    ,input  [DFI_TWCK_EN_WR_WIDTH-1:0]                           reg_ddrc_dfi_twck_en_wr     // WCK enable write timing
    ,input                                                       reg_ddrc_wck_on
    ,input  [`MEMC_NUM_RANKS-1:0]                                reg_ddrc_active_ranks
    ,input  [DFI_TWCK_EN_FS_WIDTH-1:0]                           reg_ddrc_dfi_twck_en_fs
    ,input  [EXTRA_GAP_FOR_DFI_LP_DATA_WIDTH-1:0]                reg_ddrc_extra_gap_for_dfi_lp_data
    ,output [CMD_DELAY_BITS-1:0]                                 dfi_cmd_delay
    ,output [CMD_DELAY_BITS-1:0]                                 ddrc_reg_dfi_cmd_delay
    ,output [1:0]                                                mr_t_wrdata_add_sdr
    ,output [DFI_TPHY_WRLAT_WIDTH-1:0]                           mr_t_wrlat
    ,output [5:0]                                                mr_t_wrdata
    ,output [6:0]                                                mr_t_rddata_en
    ,output [DFI_TWCK_EN_RD_WIDTH-2:0]                           mr_lp_data_rd
    ,output [DFI_TWCK_EN_WR_WIDTH-2:0]                           mr_lp_data_wr
    ,input                                                       ocecc_en
    ,input                                                       ocecc_poison_pgen_mr_ecc
    ,input                                                       ocecc_uncorr_err_intr_clr
    ,output                                                      ocecc_mr_rd_corr_err
    ,output                                                      ocecc_mr_rd_uncorr_err
    ,output [CORE_DATA_WIDTH/OCECC_MR_RD_GRANU-1:0]              ocecc_mr_rd_byte_num
    ,input                                                       ddrc_cmp_en
    ,input                                                       reg_ddrc_occap_ddrc_data_poison_seq
    ,input                                                       reg_ddrc_occap_ddrc_data_poison_parallel
    ,input                                                       reg_ddrc_occap_ddrc_data_poison_err_inj
    ,output                                                      occap_ddrc_data_err_mr
    ,output                                                      occap_ddrc_data_poison_parallel_err_mr
    ,output                                                      occap_ddrc_data_poison_seq_err_mr
    ,output                                                      occap_ddrc_data_poison_complete_mr

    ,input  [BURST_RDWR_WIDTH-1:0]                               reg_ddrc_burst_rdwr
    ,input                                                       reg_ddrc_rd_dbi_en
    ,output                                                      hif_rdata_corr_ecc_err
    ,output                                                      hif_rdata_uncorr_ecc_err
    ,output [ECC_CORRECTED_ERR_WIDTH-1:0]                        ddrc_reg_ecc_corrected_err
    ,output [ECC_UNCORRECTED_ERR_WIDTH-1:0]                      ddrc_reg_ecc_uncorrected_err
    ,output [`MEMC_ECC_SYNDROME_WIDTH-1:0]                       ddrc_reg_ecc_corr_syndromes
    ,output [`MEMC_ECC_SYNDROME_WIDTH-1:0]                       ddrc_reg_ecc_uncorr_syndromes
    ,output [6:0]                                                ddrc_reg_ecc_corrected_bit_num
    ,output [`MEMC_ECC_SYNDROME_WIDTH-1:0]                       ddrc_reg_ecc_corr_bit_mask
    ,input                                                       reg_ddrc_ecc_clr_corr_err
    ,input                                                       reg_ddrc_ecc_clr_uncorr_err
    ,output [15:0]                                               ddrc_reg_ecc_corr_err_cnt
    ,output [15:0]                                               ddrc_reg_ecc_uncorr_err_cnt
    ,input                                                       reg_ddrc_ecc_clr_corr_err_cnt
    ,input                                                       reg_ddrc_ecc_clr_uncorr_err_cnt
    ,output [RANK_BITS-1:0]                                      ddrc_reg_ecc_corr_rank
    ,output [RANK_BITS-1:0]                                      ddrc_reg_ecc_uncorr_rank
    ,output [BG_BITS-1:0]                                        ddrc_reg_ecc_corr_bg
    ,output [BG_BITS-1:0]                                        ddrc_reg_ecc_uncorr_bg
    ,output [BANK_BITS-1:0]                                      ddrc_reg_ecc_corr_bank
    ,output [BANK_BITS-1:0]                                      ddrc_reg_ecc_uncorr_bank
    ,output [PAGE_BITS-1:0]                                      ddrc_reg_ecc_corr_row
    ,output [PAGE_BITS-1:0]                                      ddrc_reg_ecc_uncorr_row
    ,output [COL_BITS-1:0]                                       ddrc_reg_ecc_corr_col
    ,output [COL_BITS-1:0]                                       ddrc_reg_ecc_uncorr_col
    ,input                                                       reg_ddrc_oc_parity_en
    ,input                                                       read_data_parity_en
    ,input                                                       reg_ddrc_par_poison_loc_rd_iecc_type
    ,input                                                       reg_ddrc_par_rdata_err_intr_clr
    ,output                                                      par_rdata_in_err_ecc_pulse
    ,output                                                      rd_wu_rdata_valid
    ,output [CORE_DATA_WIDTH-1:0]                                rd_rw_rdata
    ,output [CORE_TAG_WIDTH-1:0]                                 hif_rdata_token
    ,output                                                      rd_ih_ie_re_rdy
    ,output                                                      ddrc_reg_ecc_ap_err
    ,input                                                       reg_ddrc_ecc_ap_en
    ,input                                                       reg_ddrc_ecc_ap_err_intr_clr
    ,input  [ECCAP_TH_WIDTH-1:0]                                 reg_ddrc_ecc_ap_err_threshold
    ,output                                                      hif_rdata_addr_err
    ,output                                                      rt_rd_rd_mrr_ext
    ,output [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0]                    hif_mrr_data
    ,output                                                      hif_mrr_data_valid
    ,output                                                      rd_mr4_data_valid
    ,input                                                       reg_ddrc_mrr_done_clr
    ,output                                                      ddrc_reg_mrr_done
    ,output [`MEMC_DRAM_TOTAL_DATA_WIDTH-1:0]                    ddrc_reg_mrr_data
    ,output                                                      hif_rdata_end
    ,output                                                      hif_rdata_valid
    ,output [CORE_DATA_WIDTH-1:0]                                hif_rdata
    ,output [CORE_MASK_WIDTH-1:0]                                hif_rdata_parity
    ,input                                                       ocecc_poison_egen_mr_rd_1
    ,input  [OCECC_MR_BNUM_WIDTH-1:0]                            ocecc_poison_egen_mr_rd_1_byte_num
    ,input                                                       ocecc_poison_egen_xpi_rd_0
    ,input                                                       ocecc_poison_single
    ,input                                                       ocecc_poison_pgen_rd
    ,output                                                      occap_ddrc_data_err_rd
    ,output                                                      occap_ddrc_data_poison_parallel_err_rd
    ,output                                                      occap_ddrc_data_poison_seq_err_rd
    ,output                                                      occap_ddrc_data_poison_complete_rd

    ,input  [`MEMC_DFI_TOTAL_DATAEN_WIDTH-1:0]                   dfi_rddata_valid
    ,input  [PHY_DATA_WIDTH-1:0]                                 dfi_rddata
    ,input  [PHY_DBI_WIDTH-1:0]                                  dfi_rddata_dbi 
    ,output [PHY_DATA_WIDTH/16-1:0]                              dfi_rddata_valid_int
    ,output [PHY_DATA_WIDTH-1:0]                                 dfi_rddata_int
    ,output [PHY_DBI_WIDTH-1:0]                                  dfi_rddata_dbi_int

    ,input                                                       reg_ddrc_occap_en
    ,input                                                       reg_ddrc_occap_en_r
    ,output                                                      ddrc_occap_rtfifo_parity_err
    ,output                                                      ddrc_occap_rtctrl_parity_err

    ,input  [PHY_DATA_WIDTH/16-1:0]                              phy_ddrc_rdatavld
    ,input  [PHY_DBI_WIDTH-1:0]                                  phy_ddrc_rdbi_n
    ,input  [PHY_DATA_WIDTH-1:0]                                 phy_ddrc_rdata
    ,output                                                      rt_gs_empty
    ,output                                                      rt_gs_empty_delayed

    ,output                                                      ddrc_occap_wufifo_parity_err
    ,output                                                      ddrc_occap_wuctrl_parity_err
    ,input                                                       hif_wdata_valid
    ,input  [CORE_DATA_WIDTH-1:0]                                hif_wdata
    ,input  [CORE_MASK_WIDTH-1:0]                                hif_wdata_mask
    ,input  [WDATA_PAR_WIDTH-1:0]                                hif_wdata_parity
    ,output                                                      hif_wdata_stall
    ,input                                                       hif_wdata_end
    ,input                                                       mr_wu_free_wr_entry_valid
    ,input                                                       reg_ddrc_burst_mode
    ,input  [CORE_DATA_WIDTH-1:0]                                rw_wu_rdata
    ,output                                                      wu_fifo_empty
    ,output                                                      wu_me_wvalid
//  ,output [CORE_MASK_WIDTH-1:0]                                wu_me_wmask
//  ,output [CORE_DATA_WIDTH-1:0]                                wu_me_wdata
    ,output [WRSRAM_MASK_WIDTH-1:0]                              wu_me_wmask
    ,output [WRSRAM_DATA_WIDTH-1:0]                              wu_me_wdata
    ,output [WDATA_PAR_WIDTH_EXT-1:0]                            wu_me_wdata_par
    ,output [WRDATA_RAM_ADDR_WIDTH-1:0]                          wu_me_waddr
    ,input                                                       hwffc_hif_wd_stall

    ,output                                                      ddrc_occap_dfidata_parity_err
    ,output                                                      dfi_wr_q_empty
    ,output [`MEMC_DFI_TOTAL_DATAEN_WIDTH-1:0]                   dfi_wrdata_en
    ,output [PHY_DATA_WIDTH-1:0]                                 dfi_wrdata
    ,output [`MEMC_DFI_TOTAL_MASK_WIDTH-1:0]                     dfi_wrdata_mask
    ,output [`MEMC_DFI_TOTAL_DATAEN_WIDTH-1:0]                   dfi_rddata_en


    ,output                                                      ddrc_occap_eccaccarray_parity_err
    ,output [`MEMC_DFI_TOTAL_DATAEN_WIDTH*4-1:0]                 dwc_ddrphy_snoop_en
    ,input                                                       dis_regs_ecc_syndrome


    ,output                                                      ddrc_reg_sbr_read_ecc_ce
    ,output                                                      ddrc_reg_sbr_read_ecc_ue


`ifndef SYNTHESIS
`ifdef DDRCTL_DFI_RAS_MODEL
`endif // DDRCTL_EXT_CRC_EN
`endif // SYNTHESIS

`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
    );

    wire    [CORE_MASK_WIDTH-1:0]                                wu_mr_rdata_mask_pre; // JIRA___ID temporary changing
    wire    [CORE_MASK_WIDTH-1:0]                                wu_mr_rdata_mask = wu_mr_rdata_mask_pre; // JIRA___ID temporary changing
//  wire    [WRSRAM_MASK_WIDTH-1:0]                              wu_mr_rdata_mask_pre; // JIRA___ID temporary changing
//  wire    [WRSRAM_MASK_WIDTH-1:0]                              wu_mr_rdata_mask = wu_mr_rdata_mask_pre `ifdef MEMC_DDR5 | {WRSRAM_MASK_WIDTH{ci_manual_wr_mode}} `endif; // JIRA___ID temporary changing
    wire    [WRDATA_RAM_ADDR_WIDTH-1:0]                          mr_wu_raddr;
    wire    [CORE_MASK_WIDTH-1:0]                                ocpar_wdata_err_vec_unused;
    wire                                                         mr_ecc_acc_wr;
    wire    [ECC_RAM_ADDR_BITS-1:0]                              mr_ecc_acc_waddr;
    wire    [CORE_DATA_WIDTH-1:0]                                mr_ecc_acc_wdata;
    wire    [CORE_MASK_WIDTH-1:0]                                mr_ecc_acc_wdata_par;
    wire    [CORE_MASK_WIDTH-1:0]                                mr_ecc_acc_wdata_mask_n;
    wire                                                         mr_ecc_acc_rd;
    wire    [ECC_RAM_ADDR_BITS-1:0]                              mr_ecc_acc_raddr;
    wire    [CORE_DATA_WIDTH-1:0]                                ecc_acc_mr_rdata;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_acc_mr_rdata_par;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_acc_mr_rdata_mask_n;
    wire    [ECC_RAM_ADDR_BITS-1:0]                              mr_ecc_ram_raddr_2;
    wire    [CORE_DATA_WIDTH-1:0]                                ecc_ram_mr_rdata_2;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_ram_mr_rdata_par_2;
    wire                                                         mr_ecc_err_rd;
    wire    [ECC_ERR_RAM_ADDR_BITS-1:0]                          mr_ecc_err_raddr;
    wire    [ECC_ERR_RAM_WIDTH-1:0]                              ecc_err_mr_rdata;
    wire                                                         mr_ecc_acc_flush_en;
    wire    [BWT_BITS-1:0]                                       mr_ecc_acc_flush_addr;
    wire    [1:0]                                                mr_t_wrlat_add_sdr;
    wire    [1:0]                                                mr_t_rddata_en_add_sdr;

    wire    [PHY_DBI_WIDTH-1:0]                                  rt_rd_rdbi_n;
    wire    [PHY_DATA_WIDTH-1:0]                                 rt_rd_rdata;
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
    wire                                                         rt_rd_rd_valid;
    wire                                                         rt_rd_eod;
    wire    [CMD_LEN_BITS-1:0]                                   rt_rd_partial;
    wire    [RANKBANK_BITS_FULL-1:0]                             rt_rd_rankbank_num;
    wire    [PAGE_BITS-1:0]                                      rt_rd_page_num;
    wire    [BLK_BITS-1:0]                                       rt_rd_block_num;
    wire    [WORD_BITS-1:0]                                      rt_rd_critical_word;
    //wire    [WORD_BITS-1:0]                                      rt_rd_critical_word;
    wire                                                         rd_wu_ecc_corrected_err_unused;
    wire                                                         rd_wu_ecc_uncorrected_err_unused;
    wire    [WR_CAM_ADDR_WIDTH-1:0]                              rt_rd_wr_ram_addr;
    wire    [CMD_RMW_BITS-1:0]                                   rt_rd_rmwcmd;          // atomic RMW command instruction
    wire    [RMW_TYPE_BITS-1:0]                                  rt_rd_rmwtype;
    wire    [WORD_BITS-1:0]                                      rd_wu_word_num;
    wire                                                         rd_rw_rdata_valid_unused;
    wire    [WDATA_PAR_WIDTH-1:0]                                rd_rw_rdata_par;
    wire    [CORE_TAG_WIDTH-1:0]                                 rt_rd_rd_tag;
    wire    [BT_BITS-1:0]                                        rt_rd_ie_bt;
    wire    [IE_RD_TYPE_BITS-1:0]                                rt_rd_ie_rd_type;
    wire    [IE_BURST_NUM_BITS-1:0]                              rt_rd_ie_blk_burst_num;
    wire    [ECC_RAM_ADDR_BITS-1:0]                              rd_ecc_ram_waddr;
    wire    [CORE_DATA_WIDTH-1:0]                                rd_ecc_ram_wdata;
    wire    [CORE_MASK_WIDTH-1:0]                                rd_ecc_ram_wdata_mask_n;
    wire    [CORE_MASK_WIDTH-1:0]                                rd_ecc_ram_wdata_par;
    wire    [ECC_RAM_ADDR_BITS-1:0]                              rd_ecc_ram_raddr;
    wire    [CORE_DATA_WIDTH-1:0]                                ecc_ram_rd_rdata;
    wire    [ECC_RAM_ADDR_BITS-1:0]                              rd_ecc_acc_raddr_2;
    wire    [CORE_DATA_WIDTH-1:0]                                ecc_acc_rd_rdata_2;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_acc_rd_rdata_mask_n_2;
    wire                                                         rt_rd_eccap;
    wire                                                         rt_rd_rd_addr_err;
    wire                                                         rt_rd_rd_mrr_sod;
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
    wire                                                         rt_rd_rd_mrr;
    wire    [CMD_LEN_BITS-1:0]                                   rd_wu_partial;

    wire    [RMW_TYPE_BITS-1:0]                                  rd_yy_rmwtype;         // read-mod-write type (to RW and WU)
    wire                                                         rd_wu_rdata_end;
    wire    [WR_CAM_ADDR_WIDTH-1:0]                              rd_wu_wr_ram_addr;
    wire    [RANKBANK_BITS_FULL-1:0]                             rd_wu_rankbank_num;    // {rank #, bank #}
    wire    [PAGE_BITS-1:0]                                      rd_wu_page_num;
    wire    [BLK_BITS-1:0]                                       rd_wu_block_num;
    wire    [CMD_RMW_BITS-1:0]                                   rd_rw_rmwcmd_unused;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_acc_rd_rdata_par_2_unused;

    wire    [CORE_MASK_WIDTH-1:0]                                ecc_ram_rd_rdata_par_unused;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_ram_rd_rdata_mask_n_unconnected;
    wire    [CORE_MASK_WIDTH-1:0]                                ecc_ram_mr_rdata_mask_n_2_unconnected;
    wire                                                         ddrc_occap_eccram_parity_err_unconnected;

    wire                                                         ddrc_phy_wdata_vld_early;
    wire    [PHY_DATA_WIDTH-1:0]                                 ddrc_phy_wdata;
    wire    [PHY_MASK_WIDTH-1:0]                                 ddrc_phy_dm;
    wire    [PHY_MASK_WIDTH-1:0]                                 ddrc_phy_lecc;

    wire                                                         rt_rd_rd_mrr_ext_w;

    wire                                                         rt_rd_rd_mrr_snoop;
    
   // DP --> CPE
   wire     [1:0]                                                wu_gs_enable_wr;
   wire                                                          mr_gs_empty_w;
   wire                                                          rt_gs_empty_w;
   wire     [DFI_TPHY_WRLAT_WIDTH-1:0]                           mr_t_wrlat_w;
   wire     [6:0]                                                mr_t_rddata_en_w;
   wire     [CMD_DELAY_BITS-1:0]                                 dfi_cmd_delay_w;

   // CPE --> DP

   logic  [PARTIAL_WR_BITS_LOG2-1:0]                             gs_mr_ram_raddr_lsb_first;
   logic  [PW_WORD_CNT_WD_MAX-1:0]                               gs_mr_pw_num_beats_m1;


   wire                                                          gs_mr_write;
   wire     [NUM_RANKS-1:0]                                      mr_wr_empty_per_rank;
//`ifdef MEMC_FREQ_RATIO_4
   wire     [1:0]                                                gs_mr_write_ph;
   wire     [1:0]                                                gs_mr_read_ph;
//`endif // MEMC_FREQ_RATIO_4
   wire     [`MEMC_FREQ_RATIO-1:0]                               pi_ph_dfi_rddata_en;
   wire     [`MEMC_FREQ_RATIO-1:0]                               pi_ph_dfi_wrdata_en;
   wire                                                          pi_rt_rd_vld;
   wire     [CMD_LEN_BITS-1:0]                                   pi_rt_rd_partial;
   wire     [WR_CAM_ADDR_WIDTH-1:0]                              pi_rt_wr_ram_addr;
   wire     [RMW_TYPE_BITS-1:0]                                  pi_rt_rmwtype;
   wire     [CMD_RMW_BITS-1:0]                                   pi_rt_rmwcmd;
   wire                                                          pi_rt_rd_mrr_snoop;
   wire     [3:0]                                                pi_ph_snoop_en;
   wire                                                          pi_rt_rd_mrr_ext;
   wire                                                          pi_rt_rd_mrr;
   wire     [CORE_TAG_WIDTH-1:0]                                 pi_rt_rd_tag;
   wire                                                          pi_rt_rd_addr_err;
   wire     [RANKBANK_BITS_FULL-1:0]                             pi_rt_rankbank_num;
   wire     [PAGE_BITS-1:0]                                      pi_rt_page_num;
   wire     [BLK_BITS-1:0]                                       pi_rt_block_num;
   wire     [WORD_BITS-1:0]                                      pi_rt_critical_word;
   wire                                                          pi_rt_eccap;
   wire [BT_BITS-1:0]                                            pi_rt_ie_bt;
   wire [IE_RD_TYPE_BITS-1:0]                                    pi_rt_ie_rd_type;
   wire [IE_BURST_NUM_BITS-1:0]                                  pi_rt_ie_blk_burst_num;


   wire [MWR_BITS-1:0]                                           wu_te_mwr_unused;


//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4

   wire  [`MEMC_ECC_SYNDROME_WIDTH-1:0]                          ddrc_reg_ecc_corr_syndromes_w;
   wire  [`MEMC_ECC_SYNDROME_WIDTH-1:0]                          ddrc_reg_ecc_uncorr_syndromes_w;





`ifndef SYNTHESIS
`ifdef DDRCTL_DFI_RAS_MODEL
`endif 
`endif 
  localparam DDRCTL_IME_DP_WIDTH     = `MEMC_DRAM_DATA_WIDTH*2*`MEMC_FREQ_RATIO;
  localparam DDRCTL_IME_OFFSET_WIDTH = (DDRCTL_IME_DP_WIDTH==256)? 1 : (DDRCTL_IME_DP_WIDTH==128)? 2 : 1;
  localparam DDRCTL_IME_LENGTH_WIDTH = DDRCTL_IME_OFFSET_WIDTH;


// sel_rt_rd_rd_mrr_ext signal is always there in rd_wrapper module for OCPAR. so it can use
// this signal regardless HW-parameter MEMC_LINK_ECC. however decided to use rt output signal
// in order to keep original code when MEMC_LINK_ECC=0 config.
  wire    sel_rt_rd_rd_mrr_ext;
  assign rt_rd_rd_mrr_ext = sel_rt_rd_rd_mrr_ext;


wire            ddrc_reg_wr_linkecc_poison_complete;
wire            ddrc_reg_rd_linkecc_poison_complete;
assign ddrc_reg_linkecc_poison_complete = ddrc_reg_wr_linkecc_poison_complete | ddrc_reg_rd_linkecc_poison_complete;

//------------------------------------------------------------------------------
// Connection between CPE and DP
//------------------------------------------------------------------------------
   // DDRC_CPE --> DP
   assign gs_mr_write          = i_gs_mr_ddrc_cpedpif.gs_mr_write;
 //`ifdef MEMC_FREQ_RATIO_4
   assign gs_mr_write_ph       = 2'b00;
   assign gs_mr_read_ph        = 2'b00;
 //`endif // MEMC_FREQ_RATIO_4
   assign gs_mr_ram_raddr_lsb_first = i_gs_mr_ddrc_cpedpif.gs_pi_rdwr_ram_raddr_lsb_first;
   assign gs_mr_pw_num_beats_m1     = i_gs_mr_ddrc_cpedpif.gs_pi_rdwr_pw_num_beats_m1;

   assign pi_ph_dfi_rddata_en  = {`MEMC_FREQ_RATIO{i_pi_dfid_ddrc_cpedpif.pi_ph_dfi_rddata_en}};
   assign pi_ph_dfi_wrdata_en  = i_pi_dfid_ddrc_cpedpif.pi_ph_dfi_wrdata_en;
   assign pi_rt_rd_vld         = i_pi_rt_ddrc_cpedpif.pi_rt_rd_vld;
   assign pi_rt_rd_partial     = i_pi_rt_ddrc_cpedpif.pi_rt_rd_partial;
   assign pi_rt_wr_ram_addr    = i_pi_rt_ddrc_cpedpif.pi_rt_wr_ram_addr;
   assign pi_rt_rmwtype        = i_pi_rt_ddrc_cpedpif.pi_rt_rmwtype;
   assign pi_rt_rmwcmd         = i_pi_rt_ddrc_cpedpif.pi_rt_rmwcmd;
   assign pi_rt_rd_mrr_snoop   = i_pi_rt_ddrc_cpedpif.pi_rt_rd_mrr_snoop;
   assign pi_ph_snoop_en       = i_pi_dfid_ddrc_cpedpif.pi_ph_snoop_en;
   assign pi_rt_rd_mrr_ext     = i_pi_rt_ddrc_cpedpif.pi_rt_rd_mrr_ext;
   assign pi_rt_rd_mrr         = i_pi_rt_ddrc_cpedpif.pi_rt_rd_mrr;
   assign pi_rt_rd_tag         = i_pi_rt_ddrc_cpedpif.pi_rt_rd_tag;
   assign pi_rt_rd_addr_err    = i_pi_rt_ddrc_cpedpif.pi_rt_rd_addr_err;
   assign pi_rt_rankbank_num   = i_pi_rt_ddrc_cpedpif.pi_rt_rankbank_num;
   assign pi_rt_page_num       = i_pi_rt_ddrc_cpedpif.pi_rt_page_num;
   assign pi_rt_block_num      = i_pi_rt_ddrc_cpedpif.pi_rt_block_num;
   assign pi_rt_critical_word  = i_pi_rt_ddrc_cpedpif.pi_rt_critical_word;
   assign pi_rt_eccap          = i_pi_rt_ddrc_cpedpif.pi_rt_eccap;
   assign pi_rt_ie_bt          = i_pi_rt_ddrc_cpedpif.pi_rt_ie_bt;
   assign pi_rt_ie_rd_type     = i_pi_rt_ddrc_cpedpif.pi_rt_ie_rd_type;
   assign pi_rt_ie_blk_burst_num = i_pi_rt_ddrc_cpedpif.pi_rt_ie_blk_burst_num;
   
   // DP --> DDRC_CPE
   assign o_wu_ddrc_cpedpif.wu_gs_enable_wr = wu_gs_enable_wr;
   assign o_mr_ddrc_cpedpif.mr_gs_empty     = mr_gs_empty_w;

   assign rt_gs_empty          = rt_gs_empty_w;
   assign mr_t_wrlat           = mr_t_wrlat_w;
   assign mr_t_rddata_en       = mr_t_rddata_en_w;
   assign dfi_cmd_delay        = dfi_cmd_delay_w;


//------------------------------------------------------------------------------
// MR_WRAPPER of MR (Memory Read) block : read data from RAM to perform DDR Writes
//------------------------------------------------------------------------------
mr_wrapper
    #(
                .CORE_DATA_WIDTH                (CORE_DATA_WIDTH),
                .CORE_MASK_WIDTH                (CORE_MASK_WIDTH),
                .WRSRAM_DATA_WIDTH              (WRSRAM_DATA_WIDTH),
                .WRSRAM_MASK_WIDTH              (WRSRAM_MASK_WIDTH),
                .NUM_RANKS                      (NUM_RANKS),
                .PHY_DATA_WIDTH                 (PHY_DATA_WIDTH),
                .PHY_MASK_WIDTH                 (PHY_MASK_WIDTH),
                .WRCAM_ADDR_WIDTH               (WR_CAM_ADDR_WIDTH),
                .WRCAM_ADDR_WIDTH_IE            (WR_CAM_ADDR_WIDTH_IE),
                .WRDATA_RAM_ADDR_WIDTH          (WRDATA_RAM_ADDR_WIDTH),
                .PARTIAL_WR_BITS                (PARTIAL_WR_BITS),
                .PW_WORD_CNT_WD_MAX             (PW_WORD_CNT_WD_MAX),
                .NO_OF_BWT                      (NO_OF_BWT),
                .BT_BITS                        (BT_BITS),
                .BWT_BITS                       (BWT_BITS),
                .BRT_BITS                       (BRT_BITS),
                .IE_WR_TYPE_BITS                (IE_WR_TYPE_BITS),
                .IE_BURST_NUM_BITS              (IE_BURST_NUM_BITS),
                .ECC_RAM_ADDR_BITS              (ECC_RAM_ADDR_BITS),
                .ECC_ERR_RAM_ADDR_BITS          (ECC_ERR_RAM_ADDR_BITS),
                .ECC_ERR_RAM_WIDTH              (ECC_ERR_RAM_WIDTH),
                .WDATARAM_RD_LATENCY            (WDATARAM_RD_LATENCY),
                .MAX_CMD_DELAY                  (MAX_CMD_DELAY),
                .CMD_DELAY_BITS                 (CMD_DELAY_BITS),
                .OCPAR_EN                       (OCPAR_OR_OCECC_EN),
                .WRDATA_CYCLES                  (WRDATA_CYCLES),
                .CMD_LEN_BITS                   (CMD_LEN_BITS),
                .OCCAP_EN                       (OCCAP_EN),
                .CMP_REG                        (OCCAP_PIPELINE_EN), // pipelining on comparator inputs for OCCAP

                .OCECC_EN                       (OCECC_EN),
                .OCECC_MR_RD_GRANU              (OCECC_MR_RD_GRANU),
                .WDATA_PAR_WIDTH                (WDATA_PAR_WIDTH),
                .WDATA_PAR_WIDTH_EXT            (WDATA_PAR_WIDTH_EXT),
                .DRAM_BYTE_NUM                  (DRAM_BYTE_NUM)
              )
        mr_wrapper (
                .co_yy_clk                      (core_ddrc_core_clk),
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .ddrc_cg_en                     (ddrc_cg_en),
                .reg_ddrc_ecc_type              (reg_ddrc_ecc_type),
                .dh_mr_ecc_mode                 (reg_ddrc_ecc_mode),
                .dh_mr_data_bus_width           (reg_ddrc_data_bus_width),
                .dh_mr_en_2t_timing_mode        (reg_ddrc_en_2t_timing_mode),
                .dh_mr_frequency_ratio          (reg_ddrc_frequency_ratio),
                .dh_mr_lpddr4                   (reg_ddrc_lpddr4),
                .reg_ddrc_lpddr5                (reg_ddrc_lpddr5),
                .reg_ddrc_lp_optimized_write    (reg_ddrc_lp_optimized_write),
                .ts_pi_mwr                      (ts_pi_mwr),
                .gs_mr_write                    (gs_mr_write),
//`ifdef MEMC_FREQ_RATIO_4
                .gs_mr_write_ph                 (gs_mr_write_ph),
                .gs_mr_read_ph                  (gs_mr_read_ph),
//`endif // MEMC_FREQ_RATIO_4
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: output must always exist
                .mr_wr_empty_per_rank           (mr_wr_empty_per_rank),
//spyglass enable_block W528
                .te_mr_wr_ram_addr              (i_te_mr_cpfdpif.te_mr_wr_ram_addr),
                .te_pi_wr_word_valid            (i_te_mr_cpfdpif.te_pi_wr_word_valid),
                .te_mr_ram_raddr_lsb_first      (gs_mr_ram_raddr_lsb_first),
                .te_mr_pw_num_beats_m1          (gs_mr_pw_num_beats_m1),

                .dfi_wrdata_ecc                 (ddrc_phy_lecc),
                .reg_ddrc_wr_link_ecc_enable    (reg_ddrc_wr_link_ecc_enable),
                .reg_ddrc_linkecc_poison_byte_sel    (reg_ddrc_linkecc_poison_byte_sel),
                .reg_ddrc_linkecc_poison_dmi_sel     (reg_ddrc_linkecc_poison_dmi_sel),
                .reg_ddrc_linkecc_poison_rw          (reg_ddrc_linkecc_poison_rw),
                .reg_ddrc_linkecc_poison_type        (reg_ddrc_linkecc_poison_type),
                .reg_ddrc_linkecc_poison_inject_en   (reg_ddrc_linkecc_poison_inject_en),
                .ddrc_reg_wr_linkecc_poison_complete (ddrc_reg_wr_linkecc_poison_complete),
                .me_mr_rdata                    (me_mr_rdata),
                .me_mr_rdatamask                (wu_mr_rdata_mask),
                .mr_ph_wdatamask                (ddrc_phy_dm),
                .me_mr_rdatapar                 (me_mr_rdata_par),

                .oc_parity_en                   (write_data_parity_en),
                .oc_parity_type                 (reg_ddrc_oc_parity_type),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
                .wdata_par_err                  (wdata_ocpar_error),
                .wdata_par_err_ie               (wdata_ocpar_error_ie),
//spyglass enable_block W528
                .wdata_par_err_vec              (ocpar_wdata_err_vec_unused),
                .mr_gs_empty                    (mr_gs_empty_w),
                .mr_me_raddr                    (mr_me_raddr),
                .mr_wu_raddr                    (mr_wu_raddr),
                .mr_me_re                       (mr_me_re),
                .mr_yy_free_wr_entry_valid      (o_mr_cpfdpif.mr_yy_free_wr_entry_valid),
                .mr_yy_free_wr_entry            (o_mr_cpfdpif.mr_yy_free_wr_entry),
                .mr_ph_wdatavld_early           (ddrc_phy_wdata_vld_early),
                .mr_ph_wdata                    (ddrc_phy_wdata),
//spyglass disable_block W287b
//SMD: Instance output port is not connected
//SJ: The outputs were used for retry, but it's never used any more.
                .mr_ph_wdatamask_retry          (),
                .mr_ph_wdatavld_early_retry     (),
                .mr_ph_wdata_retry              ()
//spyglass enable_block W287b
                ,.reg_ddrc_phy_dbi_mode          (reg_ddrc_phy_dbi_mode)
                ,.reg_ddrc_wr_dbi_en             (reg_ddrc_wr_dbi_en)
                ,.reg_ddrc_dm_en                 (reg_ddrc_dm_en)

                ,.reg_ddrc_burst_rdwr            (reg_ddrc_burst_rdwr_int)
   // TE to MR for receive data
                ,.te_mr_ie_bt                   (i_te_mr_cpfdpif.te_mr_ie_bt)
                ,.te_mr_ie_wr_type              (i_te_mr_cpfdpif.te_mr_ie_wr_type)
                ,.te_mr_ie_blk_burst_num        (i_te_mr_cpfdpif.te_mr_ie_blk_burst_num)  //only for the Data command
  // IH to MR for load BWT
                ,.ih_mr_ie_brt                  (i_ih_mr_cpfdpif.ih_mr_ie_brt)
                ,.ih_mr_ie_brt_vld              (i_ih_mr_cpfdpif.ih_mr_ie_brt_vld)
                ,.ih_mr_ie_bwt                  (i_ih_mr_cpfdpif.ih_mr_ie_bwt)
                ,.ih_mr_ie_wr_cnt_dec_vct       (i_ih_mr_cpfdpif.ih_mr_ie_wr_cnt_dec_vct)
                ,.ih_mr_ie_wr_cnt_inc           (i_ih_mr_cpfdpif.ih_mr_ie_wr_cnt_inc)
                ,.ih_mr_ie_blk_wr_end           (i_ih_mr_cpfdpif.ih_mr_ie_blk_wr_end)
  // MR to IH for free BWT
                ,.mr_ih_free_bwt_vld            (o_mr_cpfdpif.mr_ih_free_bwt_vld)
                ,.mr_ih_free_bwt                (o_mr_cpfdpif.mr_ih_free_bwt)

                ,.rd_mr_free_brt_vld            (o_rd_cpfdpif.rd_ih_free_brt_vld)
                ,.rd_mr_free_brt                (o_rd_cpfdpif.rd_ih_free_brt)

                ,.mr_ih_lkp_bwt_by_bt           (o_mr_cpfdpif.mr_ih_lkp_bwt_by_bt)
                ,.ih_mr_lkp_bwt                 (i_ih_mr_cpfdpif.ih_mr_lkp_bwt)
                ,.ih_mr_lkp_bwt_vld             (i_ih_mr_cpfdpif.ih_mr_lkp_bwt_vld)
                ,.mr_ih_lkp_brt_by_bt           (o_mr_cpfdpif.mr_ih_lkp_brt_by_bt)
                ,.ih_mr_lkp_brt                 (i_ih_mr_cpfdpif.ih_mr_lkp_brt)
                ,.ih_mr_lkp_brt_vld             (i_ih_mr_cpfdpif.ih_mr_lkp_brt_vld)
// ECC ACC and ECC RAM interface
                ,.mr_ecc_acc_wr                 (mr_ecc_acc_wr)
                ,.mr_ecc_acc_waddr              (mr_ecc_acc_waddr)
                ,.mr_ecc_acc_wdata              (mr_ecc_acc_wdata)
                ,.mr_ecc_acc_wdata_par          (mr_ecc_acc_wdata_par)
                ,.mr_ecc_acc_wdata_mask_n       (mr_ecc_acc_wdata_mask_n)
                ,.mr_ecc_acc_rd                 (mr_ecc_acc_rd)
                ,.mr_ecc_acc_raddr              (mr_ecc_acc_raddr)
                ,.ecc_acc_mr_rdata              (ecc_acc_mr_rdata)
                ,.ecc_acc_mr_rdata_par          (ecc_acc_mr_rdata_par)
                ,.ecc_acc_mr_rdata_mask_n       (ecc_acc_mr_rdata_mask_n)
                ,.mr_ecc_ram_raddr_2            (mr_ecc_ram_raddr_2)
                ,.ecc_ram_mr_rdata_2            (ecc_ram_mr_rdata_2)
                ,.ecc_ram_mr_rdata_par_2        (ecc_ram_mr_rdata_par_2)
                ,.mr_ecc_err_rd                 (mr_ecc_err_rd)
                ,.mr_ecc_err_raddr              (mr_ecc_err_raddr)
                ,.ecc_err_mr_rdata              (ecc_err_mr_rdata)
                ,.mr_ecc_acc_flush_en           (mr_ecc_acc_flush_en)
                ,.mr_ecc_acc_flush_addr         (mr_ecc_acc_flush_addr)
                ,.te_mr_eccap                   (i_te_mr_cpfdpif.te_mr_eccap)
               ,.reg_ddrc_dfi_t_rddata_en       (reg_ddrc_dfi_t_rddata_en)
               ,.reg_ddrc_dfi_tphy_wrlat        (reg_ddrc_dfi_tphy_wrlat)
               ,.reg_ddrc_dfi_tphy_wrdata       (reg_ddrc_dfi_tphy_wrdata)
               ,.reg_ddrc_dfi_lp_en_data        (reg_ddrc_dfi_lp_en_data)
               ,.reg_ddrc_dfi_twck_en_rd        (reg_ddrc_dfi_twck_en_rd)
               ,.reg_ddrc_dfi_twck_en_wr        (reg_ddrc_dfi_twck_en_wr)
               ,.reg_ddrc_wck_on                (reg_ddrc_wck_on)
               ,.reg_ddrc_active_ranks          (reg_ddrc_active_ranks)
               ,.reg_ddrc_dfi_twck_en_fs        (reg_ddrc_dfi_twck_en_fs)
               ,.reg_ddrc_extra_gap_for_dfi_lp_data     (reg_ddrc_extra_gap_for_dfi_lp_data)
               ,.dfi_cmd_delay                  (dfi_cmd_delay_w)
               ,.ddrc_reg_dfi_cmd_delay         (ddrc_reg_dfi_cmd_delay)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: output must always exist
               ,.mr_t_wrlat_add_sdr             (mr_t_wrlat_add_sdr)
               ,.mr_t_wrdata_add_sdr            (mr_t_wrdata_add_sdr)
               ,.mr_t_rddata_en_add_sdr         (mr_t_rddata_en_add_sdr)
//spyglass enable_block W528
               ,.mr_t_wrlat                     (mr_t_wrlat_w)
               ,.mr_t_wrdata                    (mr_t_wrdata)
               ,.mr_t_rddata_en                 (mr_t_rddata_en_w)
               ,.mr_lp_data_rd                  (mr_lp_data_rd)
               ,.mr_lp_data_wr                  (mr_lp_data_wr)

               ,.ocecc_en                       (ocecc_en)
               ,.ocecc_poison_pgen_mr_ecc       (ocecc_poison_pgen_mr_ecc)
               ,.ocecc_uncorr_err_intr_clr      (ocecc_uncorr_err_intr_clr)

               ,.ocecc_mr_rd_corr_err           (ocecc_mr_rd_corr_err)
               ,.ocecc_mr_rd_uncorr_err         (ocecc_mr_rd_uncorr_err)
               ,.ocecc_mr_rd_byte_num           (ocecc_mr_rd_byte_num)

// occap specific input/output
               ,.ddrc_cmp_en                    (ddrc_cmp_en)
               ,.ddrc_data_cmp_poison           (reg_ddrc_occap_ddrc_data_poison_seq)
               ,.ddrc_data_cmp_poison_full      (reg_ddrc_occap_ddrc_data_poison_parallel)
               ,.ddrc_data_cmp_poison_err_inj   (reg_ddrc_occap_ddrc_data_poison_err_inj)
               ,.ddrc_data_cmp_error_mr         (occap_ddrc_data_err_mr)
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
               ,.ddrc_data_cmp_error_full_mr    (occap_ddrc_data_poison_parallel_err_mr)
               ,.ddrc_data_cmp_error_seq_mr     (occap_ddrc_data_poison_seq_err_mr)
               ,.ddrc_data_cmp_poison_complete_mr  (occap_ddrc_data_poison_complete_mr)
//spyglass enable_block W528

// for manual write and read

`ifndef SYNTHESIS
`ifdef DDRCTL_DFI_RAS_MODEL
`endif 
`endif 
        ); // end mr_wrapper instantiation


//------------------------------------------------------------------------------
// RD (Read Data) block
//------------------------------------------------------------------------------
rd_wrapper
      #(
                .CMD_LEN_BITS                   (CMD_LEN_BITS),
                .PHY_DATA_WIDTH                 (PHY_DATA_WIDTH),
                .OCPAR_EN                       (OCPAR_EN),
                .CORE_MASK_WIDTH                (CORE_MASK_WIDTH),
                .OCECC_EN                       (OCECC_EN),
                .OCECC_XPI_RD_GRANU             (OCECC_XPI_RD_GRANU),
                .OCECC_MR_RD_GRANU              (OCECC_MR_RD_GRANU),
                .OCECC_MR_BNUM_WIDTH            (OCECC_MR_BNUM_WIDTH),
                .UMCTL2_WDATARAM_PAR_DW         (WDATA_PAR_WIDTH),
                .PHY_DBI_WIDTH                  (PHY_DBI_WIDTH),
                .CORE_DATA_WIDTH                (CORE_DATA_WIDTH),
                .RA_INFO_WIDTH                  (CORE_TAG_WIDTH),
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((RANKBANK_BITS_FULL + PAGE_BITS) + BLK_BITS)' found in module 'ddrc'
//SJ: This coding style is acceptable and there is no plan to change it.
                .ECC_INFO_WIDTH                 (RANKBANK_BITS_FULL + PAGE_BITS + BLK_BITS),
                .CRC_INFO_WIDTH                 (RANKBANK_BITS_FULL + PAGE_BITS + BLK_BITS + 2)
//spyglass enable_block SelfDeterminedExpr-ML
                ,.NO_OF_BRT                     (NO_OF_BRT)
                ,.BT_BITS                       (BT_BITS)
                ,.BWT_BITS                      (BWT_BITS)
                ,.BRT_BITS                      (BRT_BITS)
                ,.IE_RD_TYPE_BITS               (IE_RD_TYPE_BITS)
                ,.IE_WR_TYPE_BITS               (IE_WR_TYPE_BITS)
                ,.IE_BURST_NUM_BITS             (IE_BURST_NUM_BITS)
                ,.ECC_RAM_DEPTH                 (ECC_RAM_DEPTH)
                ,.ECC_RAM_ADDR_BITS             (ECC_RAM_ADDR_BITS)
                ,.ECC_ERR_RAM_DEPTH             (ECC_ERR_RAM_DEPTH)
                ,.ECC_ERR_RAM_ADDR_BITS         (ECC_ERR_RAM_ADDR_BITS)
                ,.ECC_ERR_RAM_WIDTH             (ECC_ERR_RAM_WIDTH) //MEMC_WRDATA_CYCLES*SECDED_LANES;
                ,.ECCAP_TH_WIDTH                (ECCAP_TH_WIDTH)
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((RANKBANK_BITS_FULL + PAGE_BITS) + BLK_BITS)' found in module 'ddrc'
//SJ: This coding style is acceptable and there is no plan to change it.
                , .WU_INFO_WIDTH                (RANKBANK_BITS_FULL + PAGE_BITS + BLK_BITS +
                                                 CMD_RMW_BITS + RMW_TYPE_BITS + WR_CAM_ADDR_WIDTH)
//spyglass enable_block SelfDeterminedExpr-ML
                  // widths used for some outputs of rd that would be
                // [X-1:0]=>[-1:0]
                // wide otherwise as X=0 sometimes
                ,.RANK_BITS_DUP                  (RANK_BITS_DUP)
                ,.BG_BITS_DUP                    (BG_BITS_DUP)
                ,.CID_WIDTH_DUP                  (CID_WIDTH_DUP)
                ,.CORE_ECC_WIDTH_DUP             (CORE_ECC_WIDTH_DUP)
                ,.OCCAP_EN                       (OCCAP_EN)
                ,.CMP_REG                        (OCCAP_PIPELINE_EN) // pipelining on comparator inputs for OCCAP
                ,.MAX_NUM_NIBBLES                (MAX_NUM_NIBBLES)
                ,.DRAM_BYTE_NUM                  (DRAM_BYTE_NUM)
                ,.LRANK_BITS                     (LRANK_BITS)
                ,.RSD_KBD_WIDTH                  (RSD_KBD_WIDTH)
                ,.DDRCTL_IME_DP_WIDTH            (DDRCTL_IME_DP_WIDTH)
                ,.DDRCTL_IME_OFFSET_WIDTH        (DDRCTL_IME_OFFSET_WIDTH)
                ,.DDRCTL_IME_LENGTH_WIDTH        (DDRCTL_IME_LENGTH_WIDTH)
               )

        rd_wrapper (
                .co_yy_clk                      (core_ddrc_core_clk),
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .ddrc_cg_en                     (ddrc_cg_en),
                .dh_rd_frequency_ratio          (reg_ddrc_frequency_ratio),
                .dh_rd_data_bus_width           (reg_ddrc_data_bus_width),
                .reg_ddrc_burst_rdwr            (reg_ddrc_burst_rdwr),
                .reg_ddrc_med_ecc_en            (reg_ddrc_med_ecc_en),
                .reg_ddrc_lpddr4                (reg_ddrc_lpddr4),
                .reg_ddrc_lpddr5                (reg_ddrc_lpddr5),
                .reg_ddrc_rd_link_ecc_enable         (reg_ddrc_rd_link_ecc_enable),
                .reg_ddrc_rd_link_ecc_uncorr_cnt_clr (reg_ddrc_rd_link_ecc_uncorr_cnt_clr),
                .reg_ddrc_rd_link_ecc_uncorr_intr_clr(reg_ddrc_rd_link_ecc_uncorr_intr_clr),
                .reg_ddrc_rd_link_ecc_uncorr_intr_en (reg_ddrc_rd_link_ecc_uncorr_intr_en),
                .reg_ddrc_rd_link_ecc_corr_cnt_clr   (reg_ddrc_rd_link_ecc_corr_cnt_clr),
                .reg_ddrc_rd_link_ecc_corr_intr_clr  (reg_ddrc_rd_link_ecc_corr_intr_clr),
                .reg_ddrc_rd_link_ecc_corr_intr_en   (reg_ddrc_rd_link_ecc_corr_intr_en),
                .reg_ddrc_linkecc_poison_byte_sel    (reg_ddrc_linkecc_poison_byte_sel),
                .reg_ddrc_linkecc_poison_rw          (reg_ddrc_linkecc_poison_rw),
                .reg_ddrc_linkecc_poison_type        (reg_ddrc_linkecc_poison_type),
                .reg_ddrc_linkecc_poison_inject_en   (reg_ddrc_linkecc_poison_inject_en),
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(RANKBANK_BITS_FULL - 1)' found in module 'ddrc'
//SJ: This coding style is acceptable and there is no plan to change it.
                .rt_rd_link_ecc_info                 ({
                                                       rt_rd_rankbank_num[RANKBANK_BITS_FULL-1:0],
                                                       rt_rd_page_num,
                                                       rt_rd_block_num[BLK_BITS-1:0]}),
//spyglass enable_block SelfDeterminedExpr-ML
                .reg_ddrc_rd_link_ecc_err_rank_sel   (reg_ddrc_rd_link_ecc_err_rank_sel),
                .reg_ddrc_rd_link_ecc_err_byte_sel   (reg_ddrc_rd_link_ecc_err_byte_sel),
                .ddrc_reg_rd_linkecc_poison_complete (ddrc_reg_rd_linkecc_poison_complete),
                .ddrc_reg_rd_link_ecc_uncorr_cnt     (ddrc_reg_rd_link_ecc_uncorr_cnt),
                .ddrc_reg_rd_link_ecc_corr_cnt       (ddrc_reg_rd_link_ecc_corr_cnt),
                .ddrc_reg_rd_link_ecc_err_syndrome   (ddrc_reg_rd_link_ecc_err_syndrome),
                .ddrc_reg_rd_link_ecc_uncorr_err_int (ddrc_reg_rd_link_ecc_uncorr_err_int),
                .ddrc_reg_rd_link_ecc_corr_err_int   (ddrc_reg_rd_link_ecc_corr_err_int),
                .rd_link_ecc_uncorr_err              (ddrc_hif_rdata_uncorr_linkecc_err),

                .ddrc_reg_link_ecc_corr_rank         (ddrc_reg_link_ecc_corr_rank),
                .ddrc_reg_link_ecc_corr_bg           (ddrc_reg_link_ecc_corr_bg),
                .ddrc_reg_link_ecc_corr_bank         (ddrc_reg_link_ecc_corr_bank),
                .ddrc_reg_link_ecc_corr_row          (ddrc_reg_link_ecc_corr_row),
                .ddrc_reg_link_ecc_corr_col          (ddrc_reg_link_ecc_corr_col),
                .ddrc_reg_link_ecc_uncorr_rank       (ddrc_reg_link_ecc_uncorr_rank),
                .ddrc_reg_link_ecc_uncorr_bg         (ddrc_reg_link_ecc_uncorr_bg),
                .ddrc_reg_link_ecc_uncorr_bank       (ddrc_reg_link_ecc_uncorr_bank),
                .ddrc_reg_link_ecc_uncorr_row        (ddrc_reg_link_ecc_uncorr_row),
                .ddrc_reg_link_ecc_uncorr_col        (ddrc_reg_link_ecc_uncorr_col),
                .ph_rd_rdbi_n                   (rt_rd_rdbi_n), // full bus width used
                .ph_rd_rdata                    (rt_rd_rdata),  // full bus width used
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
                .rt_rd_rd_valid                 (rt_rd_rd_valid),               // read data valid from PHY
                .rt_rd_eod                      (rt_rd_eod),
                .rt_rd_partial                  (rt_rd_partial),                // this read is partial
                .reg_ddrc_phy_dbi_mode  (reg_ddrc_phy_dbi_mode),
                .reg_ddrc_rd_dbi_en             (reg_ddrc_rd_dbi_en),
                .reg_ddrc_ecc_type              (reg_ddrc_ecc_type),
                .dh_rd_ecc_mode                 (reg_ddrc_ecc_mode),
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(RANKBANK_BITS_FULL - 1)' found in module 'ddrc'
//SJ: This coding style is acceptable and there is no plan to change it.
                .rt_rd_ecc_info                 ({
                                                  rt_rd_rankbank_num[RANKBANK_BITS_FULL-1:0],
                                                  rt_rd_page_num,
                                                  rt_rd_block_num[BLK_BITS-1:0]}),
//spyglass enable_block SelfDeterminedExpr-ML
                .rt_rd_ecc_word                 (rt_rd_critical_word),
                .rd_ra_ecc_corrected_err        (hif_rdata_corr_ecc_err),
                .rd_ra_ecc_uncorrected_err      (hif_rdata_uncorr_ecc_err),
                .rd_wu_ecc_corrected_err        (rd_wu_ecc_corrected_err_unused),
                .rd_wu_ecc_uncorrected_err      (rd_wu_ecc_uncorrected_err_unused),
                .rd_dh_ecc_corrected_err        (ddrc_reg_ecc_corrected_err),       // 1 bit per ECC lane
                .rd_dh_ecc_uncorrected_err      (ddrc_reg_ecc_uncorrected_err),     // 1 bit per ECC lane
                .rd_dh_ecc_corr_syndromes       (ddrc_reg_ecc_corr_syndromes_w),      // 72 bits
                .rd_dh_ecc_uncorr_syndromes     (ddrc_reg_ecc_uncorr_syndromes_w),    // 72 bits
                .rd_dh_ecc_corrected_bit_num    (ddrc_reg_ecc_corrected_bit_num),
                .rd_dh_ecc_corr_bit_mask        (ddrc_reg_ecc_corr_bit_mask),
                .reg_ddrc_ecc_clr_corr_err      (reg_ddrc_ecc_clr_corr_err),
                .reg_ddrc_ecc_clr_uncorr_err    (reg_ddrc_ecc_clr_uncorr_err),
                .ddrc_reg_ecc_corr_err_cnt      (ddrc_reg_ecc_corr_err_cnt),
                .ddrc_reg_ecc_uncorr_err_cnt    (ddrc_reg_ecc_uncorr_err_cnt),
                .reg_ddrc_ecc_clr_corr_err_cnt  (reg_ddrc_ecc_clr_corr_err_cnt),
                .reg_ddrc_ecc_clr_uncorr_err_cnt (reg_ddrc_ecc_clr_uncorr_err_cnt),
                .rd_dh_ecc_corr_rank            (ddrc_reg_ecc_corr_rank),
                .rd_dh_ecc_uncorr_rank          (ddrc_reg_ecc_uncorr_rank),
                .rd_dh_ecc_corr_bg             (ddrc_reg_ecc_corr_bg),
                .rd_dh_ecc_uncorr_bg           (ddrc_reg_ecc_uncorr_bg),

                .rd_dh_ecc_corr_bank            (ddrc_reg_ecc_corr_bank),
                .rd_dh_ecc_uncorr_bank          (ddrc_reg_ecc_uncorr_bank),
                .rd_dh_ecc_corr_row             (ddrc_reg_ecc_corr_row),
                .rd_dh_ecc_uncorr_row           (ddrc_reg_ecc_uncorr_row),
                .rd_dh_ecc_corr_col             (ddrc_reg_ecc_corr_col),
                .rd_dh_ecc_uncorr_col           (ddrc_reg_ecc_uncorr_col),

                .reg_ddrc_oc_parity_en          (reg_ddrc_oc_parity_en),
                .reg_ddrc_read_data_parity_en   (read_data_parity_en),
                .reg_ddrc_oc_parity_type        (reg_ddrc_oc_parity_type),

                .reg_ddrc_par_poison_en         (reg_ddrc_par_poison_en),
                .reg_ddrc_par_poison_loc_rd_iecc_type (reg_ddrc_par_poison_loc_rd_iecc_type),
                .reg_ddrc_par_rdata_err_intr_clr(reg_ddrc_par_rdata_err_intr_clr),
                .par_rdata_in_err_ecc_pulse     (par_rdata_in_err_ecc_pulse),
                .rt_rd_rmwtype                  (rt_rd_rmwtype),
                .rt_rd_rmw_word_sel             (rt_rd_rmwcmd[CMD_RMW_BITS-1]), // upper-most bit for RMW command
                                                                                // select, which work to return to RA
                .rt_rd_wu_info                  ({
                                                  rt_rd_rankbank_num,
                                                  rt_rd_page_num,
                                                  rt_rd_block_num,
                                                  rt_rd_rmwtype,
                                                  rt_rd_rmwcmd,
                                                  rt_rd_wr_ram_addr}),
                .rd_wu_rdata_end                (rd_wu_rdata_end), 
                .rd_wu_rdata_valid              (rd_wu_rdata_valid),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read - rd_wu_rankbank_num/rd_wu_page_num/rd_wu_block_num
//SJ: Used under different `ifdefs, but output must always exist
                .rd_wu_info                     ({
                                                  rd_wu_rankbank_num,
                                                  rd_wu_page_num,
                                                  rd_wu_block_num,
                                                  rd_yy_rmwtype,
                                                  rd_rw_rmwcmd_unused,
                                                  rd_wu_wr_ram_addr}),
//spyglass enable_block W528
                .rd_wu_word_num                 (rd_wu_word_num),
                .rd_rw_rdata                    (rd_rw_rdata),
                .rd_rw_rdata_valid              (rd_rw_rdata_valid_unused),
                .rd_rw_rdata_par                (rd_rw_rdata_par),
                .rt_rd_ra_info                  (rt_rd_rd_tag),
                .rd_ra_info                     (hif_rdata_token),
                .rt_rd_ie_bt                    (rt_rd_ie_bt),
                .rt_rd_ie_rd_type               (rt_rd_ie_rd_type),
                .rt_rd_ie_blk_burst_num         (rt_rd_ie_blk_burst_num),
                .ih_rd_ie_brt                   (i_ih_rd_cpfdpif.ih_rd_ie_brt),
                .ih_rd_ie_rd_cnt_inc            (i_ih_rd_cpfdpif.ih_rd_ie_rd_cnt_inc),
                .ih_rd_ie_blk_rd_end            (i_ih_rd_cpfdpif.ih_rd_ie_blk_rd_end),
                .rd_ih_free_brt                 (o_rd_cpfdpif.rd_ih_free_brt),
                .rd_ih_free_brt_vld             (o_rd_cpfdpif.rd_ih_free_brt_vld),
                .rd_ih_ie_re_rdy                (rd_ih_ie_re_rdy),
                .rd_ecc_ram_wr                  (rd_ecc_ram_wr),
                .rd_ecc_ram_waddr               (rd_ecc_ram_waddr),
                .rd_ecc_ram_wdata               (rd_ecc_ram_wdata),
                .rd_ecc_ram_wdata_mask_n        (rd_ecc_ram_wdata_mask_n), //should be all 1, no mask.
                .rd_ecc_ram_wdata_par           (rd_ecc_ram_wdata_par),
                .rd_ecc_ram_raddr               (rd_ecc_ram_raddr),
                .ecc_ram_rd_rdata               (ecc_ram_rd_rdata),
                .rd_ecc_acc_raddr_2             (rd_ecc_acc_raddr_2),
                .ecc_acc_rd_rdata_2             (ecc_acc_rd_rdata_2),
                .ecc_acc_rd_rdata_mask_n_2      (ecc_acc_rd_rdata_mask_n_2),
                .mr_ecc_err_rd                  (mr_ecc_err_rd),
                .mr_ecc_err_raddr               (mr_ecc_err_raddr),
                .ecc_err_mr_rdata               (ecc_err_mr_rdata),
                .rd_ih_lkp_bwt_by_bt            (o_rd_cpfdpif.rd_ih_lkp_bwt_by_bt),
                .rd_ih_lkp_brt_by_bt            (o_rd_cpfdpif.rd_ih_lkp_brt_by_bt),
                .ih_rd_lkp_brt                  (i_ih_rd_cpfdpif.ih_rd_lkp_brt),
                .ih_rd_lkp_bwt                  (i_ih_rd_cpfdpif.ih_rd_lkp_bwt),
                .ih_rd_lkp_bwt_vld              (i_ih_rd_cpfdpif.ih_rd_lkp_bwt_vld),
                .rt_rd_eccap                    (rt_rd_eccap),
                .ddrc_reg_ecc_ap_err            (ddrc_reg_ecc_ap_err),
                .reg_ddrc_ecc_ap_en             (reg_ddrc_ecc_ap_en),
                .reg_ddrc_ecc_ap_err_intr_clr   (reg_ddrc_ecc_ap_err_intr_clr),
                .reg_ddrc_ecc_ap_err_threshold  (reg_ddrc_ecc_ap_err_threshold),
                .rt_rd_rd_addr_err              (rt_rd_rd_addr_err),
                .rd_ra_rd_addr_err              (hif_rdata_addr_err),
                .rt_rd_rd_mrr_sod               (rt_rd_rd_mrr_sod),
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
                .rt_rd_rd_mrr                   (rt_rd_rd_mrr),
                .rt_rd_rd_mrr_ext               (rt_rd_rd_mrr_ext_w),
                .rd_mrr_data                    (hif_mrr_data),
                .rd_mrr_data_valid              (hif_mrr_data_valid),
                .sel_rt_rd_rd_mrr_ext           (sel_rt_rd_rd_mrr_ext),
                .rd_mr4_data_valid              (rd_mr4_data_valid),
                .reg_ddrc_mrr_done_clr          (reg_ddrc_mrr_done_clr),
                .ddrc_reg_mrr_done              (ddrc_reg_mrr_done),
                .ddrc_reg_mrr_data              (ddrc_reg_mrr_data),
                .rd_ra_eod                      (hif_rdata_end),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Kept for debug purposes
                .rd_wu_partial                  (rd_wu_partial),
//spyglass enable_block W528
                .rd_ra_rdata_valid              (hif_rdata_valid),
                .rd_ra_rdata                    (hif_rdata),
                .rd_ra_rdata_parity             (hif_rdata_parity),
                .ocecc_en                       (ocecc_en),
                .ocecc_poison_egen_mr_rd_1      (ocecc_poison_egen_mr_rd_1),
                .ocecc_poison_egen_mr_rd_1_bnum (ocecc_poison_egen_mr_rd_1_byte_num),
                .ocecc_poison_egen_xpi_rd_0     (ocecc_poison_egen_xpi_rd_0),
                .ocecc_poison_single            (ocecc_poison_single),
                .ocecc_poison_pgen_rd           (ocecc_poison_pgen_rd),
                .ocecc_uncorr_err_intr_clr      (ocecc_uncorr_err_intr_clr),

                // occap specific input/output
                .ddrc_cmp_en                    (ddrc_cmp_en),
                .ddrc_data_cmp_poison           (reg_ddrc_occap_ddrc_data_poison_seq),
                .ddrc_data_cmp_poison_full      (reg_ddrc_occap_ddrc_data_poison_parallel),
                .ddrc_data_cmp_poison_err_inj   (reg_ddrc_occap_ddrc_data_poison_err_inj),
                .ddrc_data_cmp_error_rd         (occap_ddrc_data_err_rd),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in generate block
                .ddrc_data_cmp_error_full_rd    (occap_ddrc_data_poison_parallel_err_rd),
                .ddrc_data_cmp_error_seq_rd     (occap_ddrc_data_poison_seq_err_rd),
                .ddrc_data_cmp_poison_complete_rd  (occap_ddrc_data_poison_complete_rd)
//spyglass enable_block W528
                ,.rt_rd_rd_mrr_snoop            (rt_rd_rd_mrr_snoop)


                ,.rd_dh_scrubber_read_ecc_ce     (ddrc_reg_sbr_read_ecc_ce)
                ,.rd_dh_scrubber_read_ecc_ue     (ddrc_reg_sbr_read_ecc_ue)
        ); // end rd_wrapper block instantiation

//------------------------------------------------------------------------------
// Mask ddrc_reg_ecc_corr_syndromes/ddrc_reg_ecc_uncorr_syndromes if dis_regs_ecc_syndrome is set
//------------------------------------------------------------------------------
    assign ddrc_reg_ecc_corr_syndromes = dis_regs_ecc_syndrome ? {`MEMC_ECC_SYNDROME_WIDTH{1'b0}} : ddrc_reg_ecc_corr_syndromes_w;
    assign ddrc_reg_ecc_uncorr_syndromes = dis_regs_ecc_syndrome ? {`MEMC_ECC_SYNDROME_WIDTH{1'b0}} : ddrc_reg_ecc_uncorr_syndromes_w;
//------------------------------------------------------------------------------

//process retry_add_rd_lat_inst.v

// wire directly to dfi_rddata*_int

assign dfi_rddata_valid_int = dfi_rddata_valid[PHY_DATA_WIDTH/16-1:0];
assign dfi_rddata_int       = dfi_rddata;

assign dfi_rddata_dbi_int   = dfi_rddata_dbi;





//------------------------------------------------------------------------------
// RT block
//------------------------------------------------------------------------------
// Pass all info that is needed for reads or part of RMWs
rt
 #(
                .CMD_LEN_BITS                   (CMD_LEN_BITS),
                .PHY_DATA_WIDTH                 (PHY_DATA_WIDTH),
                .FREQ_RATIO                     (`MEMC_FREQ_RATIO),
                .CORE_TAG_WIDTH                 (`MEMC_TAGBITS),
                .NUM_RANKS                      (NUM_RANKS),
                .RANK_BITS                      (RANK_BITS),
//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(((((RANKBANK_BITS_FULL + PAGE_BITS) + BLK_BITS) + WORD_BITS) + 2) + CORE_TAG_WIDTH)' found in module 'ddrc'
//SJ: This coding style is acceptable and there is no plan to change it.

                .RT_TAG_WIDTH                   (
                                                 1 +
                                                 BT_BITS +
                                                 IE_RD_TYPE_BITS +
                                                 IE_BURST_NUM_BITS + 
                                                  1 +
                                                  RANKBANK_BITS_FULL + PAGE_BITS + BLK_BITS + WORD_BITS +  
                                                  RMW_TYPE_BITS + CMD_RMW_BITS + WR_CAM_ADDR_WIDTH +
                                                  1 +
                                                  2 +
                                                  CORE_TAG_WIDTH ),
//spyglass enable_block SelfDeterminedExpr-ML       
// `ifdef DDRCTL_EXT_SBECC_EN_1
// `ifdef DDRCTL_BF_ECC_EN_1   
                // .RSD_KBD_WIDTH                    (RSD_KBD_WIDTH),
// `endif//DDRCTL_BF_ECC_EN_1
// `endif //DDRCTL_EXT_SBECC_EN_1         
                .OCCAP_EN                         (OCCAP_EN),
                .OCCAP_PIPELINE_EN                (OCCAP_PIPELINE_EN)

      )

  rt (
                .co_yy_clk                      (core_ddrc_core_clk),
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .ddrc_cg_en                     (ddrc_cg_en),
                .reg_ddrc_occap_en              (reg_ddrc_occap_en),
                .reg_ddrc_occap_en_r            (reg_ddrc_occap_en_r),
                .ddrc_occap_rtfifo_parity_err   (ddrc_occap_rtfifo_parity_err),
                .ddrc_occap_rtctrl_parity_err   (ddrc_occap_rtctrl_parity_err),
                .dh_rt_burst_rdwr               (reg_ddrc_burst_rdwr),
                .dh_rt_frequency_ratio          (reg_ddrc_frequency_ratio),
                .dh_rt_data_bus_width           (reg_ddrc_data_bus_width),
                .dh_rt_lpddr4                   (reg_ddrc_lpddr4),
                .reg_ddrc_lpddr5                (reg_ddrc_lpddr5),
                .reg_ddrc_rd_link_ecc_enable    (reg_ddrc_rd_link_ecc_enable),
                .pi_rt_rd_vld                   (pi_rt_rd_vld),
                .pi_rt_rd_tag                   ({
                                                  pi_rt_eccap,
                                                  pi_rt_ie_bt,
                                                  pi_rt_ie_rd_type,
                                                  pi_rt_ie_blk_burst_num,
                                                  pi_rt_rd_addr_err,
                                                  pi_rt_rankbank_num,
                                                  pi_rt_page_num,
                                                  pi_rt_block_num,
                                                  pi_rt_critical_word,
                                                  pi_rt_wr_ram_addr,
                                                  pi_rt_rmwtype,
                                                  pi_rt_rmwcmd,
                                                  pi_rt_rd_mrr_snoop,
                                                  pi_rt_rd_mrr_ext,
                                                  pi_rt_rd_mrr,
                                                  pi_rt_rd_tag}),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read - rt_rd_critical_word
//SJ: Used in MEMC_ECC configs, but signal must always exist
                .rt_rd_rd_tag                   ({
                                                  rt_rd_eccap,
                                                  rt_rd_ie_bt,
                                                  rt_rd_ie_rd_type,
                                                  rt_rd_ie_blk_burst_num,
                                                  rt_rd_rd_addr_err,
                                                  rt_rd_rankbank_num,
                                                  rt_rd_page_num,
                                                  rt_rd_block_num,
                                                  rt_rd_critical_word,
                                                  rt_rd_wr_ram_addr,
                                                  rt_rd_rmwtype,
                                                  rt_rd_rmwcmd,
                                                  rt_rd_rd_mrr_snoop,
                                                  rt_rd_rd_mrr_ext_w,
                                                  rt_rd_rd_mrr,
                                                  rt_rd_rd_tag}),
//spyglass enable_block W528
                .pi_rt_rd_partial               (pi_rt_rd_partial),
                .ph_rt_rdatavld                 (phy_ddrc_rdatavld),
                .reg_ddrc_rd_dbi_en             (reg_ddrc_rd_dbi_en),
                .ph_rt_rdbi_n                   (phy_ddrc_rdbi_n),
                .ph_rt_rdata                    (phy_ddrc_rdata),
                .rt_rd_rdbi_n                   (rt_rd_rdbi_n),
                .rt_rd_rdata                    (rt_rd_rdata),
                .rt_gs_empty                    (rt_gs_empty_w),
                .rt_gs_empty_delayed            (rt_gs_empty_delayed),
                .rt_rd_rd_valid                 (rt_rd_rd_valid),
                .rt_rd_rd_partial               (rt_rd_partial),
                .rt_rd_rd_mrr_sod               (rt_rd_rd_mrr_sod),
//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
                .rt_rd_eod                      (rt_rd_eod)


`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
`endif // SNPS_ASSERT_ON
`endif // SYNTHESIS
);


//------------------------------------------------------------------------------
// WU (Write Update) block
//------------------------------------------------------------------------------
// Write Update Engine
// Only required when read-modify-writes are supported in some form
// (that includes partial writes with ECC or without DM)
memc_wu
 #(
                .CMD_LEN_BITS                   (CMD_LEN_BITS),
                .WRCAM_ADDR_WIDTH               (WR_CAM_ADDR_WIDTH),
                .WRDATA_RAM_ADDR_WIDTH          (WRDATA_RAM_ADDR_WIDTH),
                .CORE_DATA_WIDTH                (CORE_DATA_WIDTH),
                .CORE_MASK_WIDTH                (CORE_MASK_WIDTH),
                .WRSRAM_DATA_WIDTH              (WRSRAM_DATA_WIDTH),
                .WRSRAM_MASK_WIDTH              (WRSRAM_MASK_WIDTH),
                .WDATA_PAR_WIDTH                (WDATA_PAR_WIDTH),
                .WDATA_PAR_WIDTH_EXT            (WDATA_PAR_WIDTH_EXT),
                .BANK_BITS                      (BANK_BITS),
                .BG_BITS                        (BG_BITS),
                .BG_BANK_BITS                   (BG_BANK_BITS),
                .ROW_BITS                       (PAGE_BITS),
                .BLK_BITS                       (BLK_BITS),
                .WORD_BITS                      (WORD_BITS),
                .MWR_BITS                       (MWR_BITS),
                .PARTIAL_WR_BITS                (PARTIAL_WR_BITS),
                .PW_WORD_CNT_WD_MAX             (PW_WORD_CNT_WD_MAX),
                .UMCTL2_SEQ_BURST_MODE          (UMCTL2_SEQ_BURST_MODE),
                .OCCAP_EN                       (OCCAP_EN),
                .OCCAP_PIPELINE_EN              (OCCAP_PIPELINE_EN)
        )
   memc_wu (
                .co_yy_clk                      (core_ddrc_core_clk),
                .core_ddrc_rstn                 (core_ddrc_rstn),
                .ddrc_cg_en                     (ddrc_cg_en),
                .reg_ddrc_occap_en              (reg_ddrc_occap_en),
                .reg_ddrc_occap_en_r            (reg_ddrc_occap_en_r),
                .ddrc_occap_wufifo_parity_err   (ddrc_occap_wufifo_parity_err),
                .ddrc_occap_wuctrl_parity_err   (ddrc_occap_wuctrl_parity_err),



                .dh_wu_lpddr4                   (reg_ddrc_lpddr4),
                .reg_ddrc_lpddr5                (reg_ddrc_lpddr5),
                .reg_ddrc_data_bus_width        (reg_ddrc_data_bus_width),
                .co_wu_wdata_valid              (hif_wdata_valid),
                .co_wu_wdata                    (hif_wdata),
                .co_wu_wdata_mask               (hif_wdata_mask),
                .co_wu_wdata_par                (hif_wdata_parity),

                .wu_co_wdata_stall              (hif_wdata_stall),

                .ih_wu_wr_valid                 (i_ih_wu_cpfdpif.ih_wu_wr_valid),
                .ih_wu_wr_valid_addr_err        (i_ih_wu_cpfdpif.ih_wu_wr_valid_addr_err),
                .ih_wu_rmw_type                 (i_ih_wu_cpfdpif.ih_wu_rmw_type),
                .ih_wu_wr_entry_num             (i_ih_wu_cpfdpif.ih_wu_wr_entry),
                .ih_wu_critical_word            (i_ih_wu_cpfdpif.ih_wu_critical_word),

                .co_wu_data_end                 (hif_wdata_end),


                .te_wu_wr_retry                 (i_te_wu_cpfdpif.te_wu_wr_retry),       // in future, create a signal for this
                .te_wu_wr_combine               (i_te_wu_cpfdpif.te_yy_wr_combine),
                .te_wu_entry_num                (i_te_wu_cpfdpif.te_wu_entry_num),
                .mr_wu_free_wr_entry            (o_mr_cpfdpif.mr_yy_free_wr_entry[WR_CAM_ADDR_WIDTH-1:0]),
                .mr_wu_free_wr_entry_valid      (mr_wu_free_wr_entry_valid),
                .reg_ddrc_burst_mode            (reg_ddrc_burst_mode),

//              .ra_wu_rdata_end                (hif_rdata_end), 
                .ra_wu_rdata_end                (rd_wu_rdata_end), 
                .rd_wu_rdata_valid              (rd_wu_rdata_valid),
                .rd_wu_partial                  (rd_wu_partial),
                .rd_wu_rmw_type                 (rd_yy_rmwtype),
                .rd_wu_wr_ram_addr              (rd_wu_wr_ram_addr),
                .rd_wu_word_num                 (rd_wu_word_num),
                .rd_wu_rdata                    (rw_wu_rdata),                  // data goes thru RMW for any updates first
                .rd_wu_rdata_par                (rd_rw_rdata_par),

                .te_wu_ie_flowctrl_req         (i_te_wu_cpfdpif.te_wu_ie_flowctrl_req),

                .mr_wu_raddr                    (mr_wu_raddr),
                .wu_mr_rdata_mask               (wu_mr_rdata_mask_pre),             // byte enables to be written to DRAM
                .wu_ih_flow_cntrl_req           (o_wu_cpfdpif.wu_ih_flow_cntrl_req),
//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used in conditional selection based on hardware parameter value
                .wu_fifo_empty                  (wu_fifo_empty),
//spyglass enable_block W528

                .wu_te_enable_wr                (o_wu_cpfdpif.wu_te_enable_wr),
                .wu_gs_enable_wr                (wu_gs_enable_wr),
                .wu_te_entry_num                (o_wu_cpfdpif.wu_te_entry_num),
                .dh_wu_dm_en                    (reg_ddrc_dm_en),
                .wu_te_mwr                      (o_wu_cpfdpif.wu_te_mwr),
                .reg_ddrc_burst_rdwr            (reg_ddrc_burst_rdwr),
                .reg_ddrc_frequency_ratio       (reg_ddrc_frequency_ratio),
                .wu_te_wr_word_valid            (o_wu_cpfdpif.wu_te_wr_word_valid),
                .wu_te_ram_raddr_lsb_first      (o_wu_cpfdpif.wu_te_ram_raddr_lsb_first),
                .wu_te_pw_num_beats_m1          (o_wu_cpfdpif.wu_te_pw_num_beats_m1),
                .wu_te_pw_num_cols_m1           (o_wu_cpfdpif.wu_te_pw_num_cols_m1),


                .wu_me_wvalid                   (wu_me_wvalid),
                .wu_me_wmask                    (wu_me_wmask),
                .wu_me_wdata                    (wu_me_wdata),
                .wu_me_wdata_par                (wu_me_wdata_par),
                .wu_me_waddr                    (wu_me_waddr)

              , .hwffc_hif_wd_stall             (hwffc_hif_wd_stall)
        ); // end wu instantiation


//------------------------------------------------------------------------------
// DFI_data block
//------------------------------------------------------------------------------

dfi_data
 #(

             .MEMC_ECC_SUPPORT              (MEMC_ECC_SUPPORT),
             .PHY_DATA_WIDTH                (PHY_DATA_WIDTH),
             .PHY_MASK_WIDTH                (PHY_MASK_WIDTH),
             .NUM_RANKS                     (NUM_RANKS),
             .MAX_CMD_DELAY                 (MAX_CMD_DELAY),
             .CMD_DELAY_BITS                (CMD_DELAY_BITS),
             .OCCAP_EN                      (OCCAP_EN),
             .OCCAP_PIPELINE_EN             (OCCAP_PIPELINE_EN)
             )
  dfi_data (
             // Inputs
             .core_ddrc_core_clk            (core_ddrc_core_clk),
             .core_ddrc_rstn                (core_ddrc_rstn),
             .ddrc_cg_en                    (ddrc_cg_en),
             .reg_ddrc_occap_en             (reg_ddrc_occap_en),
             .reg_ddrc_occap_en_r           (reg_ddrc_occap_en_r),
             .ddrc_occap_dfidata_parity_err (ddrc_occap_dfidata_parity_err),
             .reg_ddrc_frequency_ratio      (reg_ddrc_frequency_ratio),
             .ddrc_phy_wdata_vld_early      (ddrc_phy_wdata_vld_early),
             .pi_ph_dfi_rddata_en           (pi_ph_dfi_rddata_en),
             .pi_ph_dfi_wrdata_en           (pi_ph_dfi_wrdata_en),
             .ddrc_phy_wdata                (ddrc_phy_wdata),
             .ddrc_phy_dm                   (ddrc_phy_dm),
             .reg_ddrc_wr_link_ecc_enable   (reg_ddrc_wr_link_ecc_enable),
             .ddrc_phy_lecc                 (ddrc_phy_lecc),
             .dfi_wr_lecc                   (dfi_wrdata_ecc),

             .mr_dfi_empty                  (mr_gs_empty_w),
             .dfi_wr_q_empty                (dfi_wr_q_empty),
             .mr_t_wrlat_add_sdr            (mr_t_wrlat_add_sdr),
             .mr_t_rddata_en_add_sdr        (mr_t_rddata_en_add_sdr),

//`ifdef MEMC_FREQ_RATIO_4
//`endif // MEMC_FREQ_RATIO_4
             .reg_ddrc_lpddr4               (reg_ddrc_lpddr4),
             .reg_ddrc_lpddr5               (reg_ddrc_lpddr5),
             .reg_ddrc_dm_en                (reg_ddrc_dm_en),
             .reg_ddrc_phy_dbi_mode         (reg_ddrc_phy_dbi_mode),
             .reg_ddrc_wr_dbi_en            (reg_ddrc_wr_dbi_en),
               //Outputs
             .dfi_wrdata_en                 (dfi_wrdata_en),
             .dfi_wrdata                    (dfi_wrdata),
             .dfi_wrdata_mask               (dfi_wrdata_mask),
             .dfi_rddata_en                 (dfi_rddata_en)

            ,.pi_ph_snoop_en                (pi_ph_snoop_en)
            ,.dwc_ddrphy_snoop_en           (dwc_ddrphy_snoop_en)
           );



// Encrypt RAM instance this is for development

//-------------------------------------------------------------------
// ECC ACC array in write path
// ------------------------------------------------------------------
// ECC Accumulator array
// each token has one ECC Accumulator, which store 1 Burst ECC for 8 Burst data.
// that is made by a ECC RAM
// ECC RAM has two read port, one for MR, one for RD
// ECC read port1 (for MR) has read clear funcion if RD_CLR=1.
ie_ecc_ram
 #(
                .WIDTH                          (CORE_DATA_WIDTH)
               ,.MASK_WIDTH                     (CORE_MASK_WIDTH)
               ,.DEPTH                          (ECC_RAM_DEPTH)
               ,.ADDR_BITS                      (ECC_RAM_ADDR_BITS)
               ,.OCPAR_EN                       (`UMCTL2_OCPAR_EN)
               ,.OCECC_EN                       (OCECC_EN)
               ,.RD_CLR                         (0)                         // enable read clear
               ,.FLS_EN                         (1)                         // enable read clear
               ,.FLS_BLK_BITS                   (`log2(WRDATA_CYCLES))       // enable read clear
               ,.DUAL_RD                        (1)         // 1: dual read port, 0: single read port
               ,.REGOUT                         (1'b0)      //1: rdata is valid in the next cycle of raddr, like RAM;
                                                            //0: rdata is valid in the same cycle with raddr, like ROM;
               ,.MASK_USED                      (1)         // rdata_mask_n/rdata_mask_n_2 are used signals
               ,.OCCAP_EN                       (OCCAP_EN)  // rdata_mask_n/rdata_mask_n_2 generation protected via pgen/pchk
               ,.OCCAP_PIPELINE_EN              (OCCAP_PIPELINE_EN)
               )
U_ecc_acc_array (
//port start
                .clk                            (core_ddrc_core_clk)
               ,.rstn                           (core_ddrc_rstn)
               ,.wr                             (mr_ecc_acc_wr)
               ,.waddr                          (mr_ecc_acc_waddr)
               ,.wdata                          (mr_ecc_acc_wdata)
               ,.wdata_mask_n                   (mr_ecc_acc_wdata_mask_n)
               ,.wdata_par                      (mr_ecc_acc_wdata_par)
               ,.rd                             (mr_ecc_acc_rd)
               ,.raddr                          (mr_ecc_acc_raddr)
               ,.rdata                          (ecc_acc_mr_rdata)
               ,.rdata_mask_n                   (ecc_acc_mr_rdata_mask_n)
               ,.rdata_par                      (ecc_acc_mr_rdata_par)
               ,.raddr_2                        (rd_ecc_acc_raddr_2)
               ,.rdata_2                        (ecc_acc_rd_rdata_2)
               ,.rdata_mask_n_2                 (ecc_acc_rd_rdata_mask_n_2)
               ,.rdata_par_2                    (ecc_acc_rd_rdata_par_2_unused)
               ,.flush_en                       (mr_ecc_acc_flush_en)
               ,.flush_addr                     (mr_ecc_acc_flush_addr)
               ,.reg_ddrc_occap_en              (reg_ddrc_occap_en)
               ,.reg_ddrc_occap_en_r            (reg_ddrc_occap_en_r)
               ,.ddrc_occap_ieeccram_parity_err (ddrc_occap_eccaccarray_parity_err)
               );


//-------------------------------------------------------------------
// ECC array in read path
// ------------------------------------------------------------------
// ECC RAM
// Store all the token's ECC burst,
ie_ecc_ram
 #(
                .WIDTH                          (CORE_DATA_WIDTH)
               ,.MASK_WIDTH                     (CORE_MASK_WIDTH)
               ,.DEPTH                          (ECC_RAM_DEPTH)
               ,.ADDR_BITS                      (ECC_RAM_ADDR_BITS)
               ,.OCPAR_EN                       (`UMCTL2_OCPAR_EN)
               ,.OCECC_EN                       (OCECC_EN)
               ,.RD_CLR                         (1'b0)   // don't enable read clear
               ,.FLS_EN                         (0)      // don't enable flush
               ,.FLS_BLK_BITS                   (1)
               ,.DUAL_RD                        (1'b1)   //1: dual read port
               ,.REGOUT                         (1'b0)   //1: rdata is valid in the next cycle of raddr, like RAM;
                                                         //0: rdata is valid in the same cycle with raddr, like ROM;
               ,.MASK_USED                      (0)      // rdata_mask_n/rdata_mask_n_2 are unused signals
               ,.OCCAP_EN                       (0)      // rdata_mask_n/rdata_mask_n_2 unused in this instance so no nedd to protect via pgen/pchk
               ,.OCCAP_PIPELINE_EN              (OCCAP_PIPELINE_EN) // setting OCCAP_PIPELINE_EN even though OCCAP_EN=0, will have no effect 
)
U_ecc_ram (
                .clk                            (core_ddrc_core_clk)
               ,.rstn                           (core_ddrc_rstn)
               ,.wr                             (rd_ecc_ram_wr)
               ,.wdata                          (rd_ecc_ram_wdata)
               ,.wdata_mask_n                   (rd_ecc_ram_wdata_mask_n)
               ,.wdata_par                      (rd_ecc_ram_wdata_par)
               ,.waddr                          (rd_ecc_ram_waddr)
               ,.rd                             (1'b1)     //the value is "don't care" since RD_CLR is 0.
               ,.raddr                          (rd_ecc_ram_raddr)
               ,.rdata                          (ecc_ram_rd_rdata)
               ,.rdata_par                      (ecc_ram_rd_rdata_par_unused)
               ,.rdata_mask_n                   (ecc_ram_rd_rdata_mask_n_unconnected)   // unused output
               ,.raddr_2                        (mr_ecc_ram_raddr_2)
               ,.rdata_2                        (ecc_ram_mr_rdata_2)
               ,.rdata_mask_n_2                 (ecc_ram_mr_rdata_mask_n_2_unconnected) // unused output
               ,.rdata_par_2                    (ecc_ram_mr_rdata_par_2)
               ,.flush_en                       (1'b0)
               ,.flush_addr                     ({(ECC_RAM_ADDR_BITS-1){1'b0}})
               ,.reg_ddrc_occap_en              (reg_ddrc_occap_en)
               ,.reg_ddrc_occap_en_r            (reg_ddrc_occap_en_r)
               ,.ddrc_occap_ieeccram_parity_err (ddrc_occap_eccram_parity_err_unconnected) // unused output
            );

 endmodule : dwc_ddrctl_ddrc_dp
