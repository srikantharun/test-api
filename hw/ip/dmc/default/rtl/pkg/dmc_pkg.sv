// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// This package contains all the needed info / config for the DataMovementCluster
///
package dmc_pkg;
  parameter int unsigned DMC_PWORD_WIDTH = 512;
  parameter int unsigned DMC_BWORD_WIDTH = 128;

  parameter int unsigned DMC_NR_IFDS = 6;
  parameter int unsigned DMC_NR_ODRS = 2;
  parameter int unsigned DMC_NR_IFDS_ODRS = DMC_NR_IFDS + DMC_NR_ODRS;
  parameter int unsigned DMC_NR_RV_FEEDTHROUGHS = 8;

  parameter int unsigned DMC_IRQ_W = DMC_NR_IFDS_ODRS;

  typedef enum int {
    m_ifd0_idx = 'd0,
    m_ifd1_idx = 'd1,
    m_ifd2_idx = 'd2,
    m_ifdw_idx = 'd3,
    d_ifd0_idx = 'd4,
    d_ifd1_idx = 'd5,
    m_odr_idx  = 'd6,
    d_odr_idx  = 'd7
  } dmc_dev_select_e;

  parameter bit [DMC_NR_IFDS_ODRS-1:0] DMC_DEV_HAS_DECOMP = '{
    m_ifd0_idx: 1'b0,
    m_ifd1_idx: 1'b0,
    m_ifd2_idx: 1'b0,
    m_ifdw_idx: 1'b1,
    d_ifd0_idx: 1'b0,
    d_ifd1_idx: 1'b0,
    m_odr_idx:  1'b1,
    d_odr_idx:  1'b1
  };
  parameter bit [DMC_NR_IFDS_ODRS-1:0] DMC_DEV_HAS_VTRSP  = '{
    m_ifd0_idx: 1'b0,
    m_ifd1_idx: 1'b0,
    m_ifd2_idx: 1'b0,
    m_ifdw_idx: 1'b1,
    d_ifd0_idx: 1'b0,
    d_ifd1_idx: 1'b0,
    m_odr_idx:  1'b1,
    d_odr_idx:  1'b1
  };

  ////////////////////////
  /// tokens, including timestamp:
  parameter int unsigned DMC_TOKENS_PROD = token_mgr_mapping_aic_pkg::TOK_MGR_CFG.max_num_prod;
  parameter int unsigned DMC_TOKENS_CONS = token_mgr_mapping_aic_pkg::TOK_MGR_CFG.max_num_cons;

  /////////////////////////
  /// addressing:
  parameter int unsigned DMC_NR_AXI_DEVS = DMC_NR_IFDS_ODRS;
  parameter int unsigned DMC_L1_BASE_ADDR_WIDTH = aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH -
                                                  aic_common_pkg::AIC_VA_BASE_LSB;

  // Regions:
  typedef longint aic_region_t[3];
  parameter int DMC_NR_REGIONS = 3 * DMC_NR_AXI_DEVS;
  parameter int DMC_REGION_SLAVE_ID[DMC_NR_REGIONS] = {
    m_ifdw_idx, m_ifdw_idx, m_ifdw_idx,
    m_ifd0_idx, m_ifd0_idx, m_ifd0_idx,
    m_ifd1_idx, m_ifd1_idx, m_ifd1_idx,
    m_ifd2_idx, m_ifd2_idx, m_ifd2_idx,
    m_odr_idx,  m_odr_idx,  m_odr_idx,
    d_ifd0_idx, d_ifd0_idx, d_ifd0_idx,
    d_ifd1_idx, d_ifd1_idx, d_ifd1_idx,
    d_odr_idx,  d_odr_idx,  d_odr_idx
  };

  parameter logic[aic_common_pkg::AIC_BLOCK_ID_WIDTH-1:0] DMC_BLOCK_ID[DMC_NR_AXI_DEVS] = {
    aic_common_pkg::AIC_BLOCK_ID_M_IFDW,
    aic_common_pkg::AIC_BLOCK_ID_M_IFD0,
    aic_common_pkg::AIC_BLOCK_ID_M_IFD1,
    aic_common_pkg::AIC_BLOCK_ID_M_IFD2,
    aic_common_pkg::AIC_BLOCK_ID_M_ODR,
    aic_common_pkg::AIC_BLOCK_ID_D_IFD0,
    aic_common_pkg::AIC_BLOCK_ID_D_IFD1,
    aic_common_pkg::AIC_BLOCK_ID_D_ODR
  };

  // generic IFD / ODR parameters::
  parameter int unsigned DMC_IFD_MAX_OUTST_CMDS = 4;
  parameter int unsigned DMC_IFD_CMD_FIFO_DEPTH = 16;
  parameter int unsigned DMC_IFD_CMD_FIFO_WIDTH = 288; // 4.5 words, fallback is 2 entries, 9 words
  parameter int unsigned DMC_IFD_DM_DEPTH = 128;

  parameter int unsigned DMC_ODR_MAX_OUTST_CMDS = 4;
  parameter int unsigned DMC_ODR_CMD_FIFO_DEPTH = 16;
  parameter int unsigned DMC_ODR_CMD_FIFO_WIDTH = 288; // 4.5 words, fallback is 2 entries, 9 words
  parameter int unsigned DMC_ODR_DM_DEPTH = 128;

  parameter int unsigned DMC_MAX_L1_LATENCY = 10;
endpackage
