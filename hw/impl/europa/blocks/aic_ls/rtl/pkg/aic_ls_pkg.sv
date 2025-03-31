// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

/// Parameters for AIC_LS

package aic_ls_pkg;
  import aipu_addr_map_pkg::*;
  typedef int unsigned uint_t;

  parameter int unsigned RvvPortSizeWidth = $clog2(cva6v_ai_core_pkg::MemPortBeWidth);

  parameter uint_t AIC_LS_BUS_OSR = 16; // no big area impact, should be large enough to cover latency to MVM / DID

  // Addressing regions:
  import aic_addr_map_pkg::*;
  parameter int AIC_LS_NR_AXI_DEVS = 3;
  parameter int AIC_LS_NR_REGIONS = 3 * AIC_LS_NR_AXI_DEVS + 1;
  parameter int AIC_LS_REGION_SLAVE_ID[AIC_LS_NR_REGIONS] = {
    32'd2, 32'd2, 32'd2,
    32'd1, 32'd1, 32'd1, 32'd1,
    32'd0, 32'd0, 32'd0
  };
  parameter longint AIC_LS_REGION_ST_ADDR[AIC_LS_NR_REGIONS] = {
    AIC_LOC_DMC_REGION_ST_ADDR[0], AIC_LOC_DMC_REGION_ST_ADDR[1], AIC_LOC_DMC_REGION_ST_ADDR[2],
    AIC_LOC_MID_REGION_ST_ADDR[0], AIC_LOC_MID_REGION_ST_ADDR[1], AIC_LOC_MID_REGION_ST_ADDR[2], AIC_LOC_MID_REGION_ST_ADDR[3],
    AIC_LOC_DID_REGION_ST_ADDR[0], AIC_LOC_DID_REGION_ST_ADDR[1], AIC_LOC_DID_REGION_ST_ADDR[2]
  };
  parameter longint AIC_LS_REGION_END_ADDR[AIC_LS_NR_REGIONS] = {
    AIC_LOC_DMC_REGION_END_ADDR[0], AIC_LOC_DMC_REGION_END_ADDR[1], AIC_LOC_DMC_REGION_END_ADDR[2],
    AIC_LOC_MID_REGION_END_ADDR[0], AIC_LOC_MID_REGION_END_ADDR[1], AIC_LOC_MID_REGION_END_ADDR[2], AIC_LOC_MID_REGION_END_ADDR[3],
    AIC_LOC_DID_REGION_END_ADDR[0], AIC_LOC_DID_REGION_END_ADDR[1], AIC_LOC_DID_REGION_END_ADDR[2]
  };

  // DMC regions:
  parameter int AIC_LS_DMC_REGION_SLAVE_ID[dmc_pkg::DMC_NR_REGIONS] = {
    dmc_pkg::m_ifdw_idx, dmc_pkg::m_ifdw_idx, dmc_pkg::m_ifdw_idx,
    dmc_pkg::m_ifd0_idx, dmc_pkg::m_ifd0_idx, dmc_pkg::m_ifd0_idx,
    dmc_pkg::m_ifd1_idx, dmc_pkg::m_ifd1_idx, dmc_pkg::m_ifd1_idx,
    dmc_pkg::m_ifd2_idx, dmc_pkg::m_ifd2_idx, dmc_pkg::m_ifd2_idx,
    dmc_pkg::m_odr_idx,  dmc_pkg::m_odr_idx,  dmc_pkg::m_odr_idx,
    dmc_pkg::d_ifd0_idx, dmc_pkg::d_ifd0_idx, dmc_pkg::d_ifd0_idx,
    dmc_pkg::d_ifd1_idx, dmc_pkg::d_ifd1_idx, dmc_pkg::d_ifd1_idx,
    dmc_pkg::d_odr_idx,  dmc_pkg::d_odr_idx,  dmc_pkg::d_odr_idx
  };
  parameter longint AIC_LS_DMC_REGION_ST_ADDR[dmc_pkg::DMC_NR_REGIONS] = {
    AIC_LOC_M_IFD_W_REGION_ST_ADDR[0], AIC_LOC_M_IFD_W_REGION_ST_ADDR[1], AIC_LOC_M_IFD_W_REGION_ST_ADDR[2],
    AIC_LOC_M_IFD_0_REGION_ST_ADDR[0], AIC_LOC_M_IFD_0_REGION_ST_ADDR[1], AIC_LOC_M_IFD_0_REGION_ST_ADDR[2],
    AIC_LOC_M_IFD_1_REGION_ST_ADDR[0], AIC_LOC_M_IFD_1_REGION_ST_ADDR[1], AIC_LOC_M_IFD_1_REGION_ST_ADDR[2],
    AIC_LOC_M_IFD_2_REGION_ST_ADDR[0], AIC_LOC_M_IFD_2_REGION_ST_ADDR[1], AIC_LOC_M_IFD_2_REGION_ST_ADDR[2],
    AIC_LOC_M_ODR_REGION_ST_ADDR[0],   AIC_LOC_M_ODR_REGION_ST_ADDR[1],   AIC_LOC_M_ODR_REGION_ST_ADDR[2],
    AIC_LOC_D_IFD_0_REGION_ST_ADDR[0], AIC_LOC_D_IFD_0_REGION_ST_ADDR[1], AIC_LOC_D_IFD_0_REGION_ST_ADDR[2],
    AIC_LOC_D_IFD_1_REGION_ST_ADDR[0], AIC_LOC_D_IFD_1_REGION_ST_ADDR[1], AIC_LOC_D_IFD_1_REGION_ST_ADDR[2],
    AIC_LOC_D_ODR_REGION_ST_ADDR[0],   AIC_LOC_D_ODR_REGION_ST_ADDR[1],   AIC_LOC_D_ODR_REGION_ST_ADDR[2]
  };
  parameter longint AIC_LS_DMC_REGION_END_ADDR[dmc_pkg::DMC_NR_REGIONS] = {
    AIC_LOC_M_IFD_W_REGION_END_ADDR[0], AIC_LOC_M_IFD_W_REGION_END_ADDR[1], AIC_LOC_M_IFD_W_REGION_END_ADDR[2],
    AIC_LOC_M_IFD_0_REGION_END_ADDR[0], AIC_LOC_M_IFD_0_REGION_END_ADDR[1], AIC_LOC_M_IFD_0_REGION_END_ADDR[2],
    AIC_LOC_M_IFD_1_REGION_END_ADDR[0], AIC_LOC_M_IFD_1_REGION_END_ADDR[1], AIC_LOC_M_IFD_1_REGION_END_ADDR[2],
    AIC_LOC_M_IFD_2_REGION_END_ADDR[0], AIC_LOC_M_IFD_2_REGION_END_ADDR[1], AIC_LOC_M_IFD_2_REGION_END_ADDR[2],
    AIC_LOC_M_ODR_REGION_END_ADDR[0],   AIC_LOC_M_ODR_REGION_END_ADDR[1],   AIC_LOC_M_ODR_REGION_END_ADDR[2],
    AIC_LOC_D_IFD_0_REGION_END_ADDR[0], AIC_LOC_D_IFD_0_REGION_END_ADDR[1], AIC_LOC_D_IFD_0_REGION_END_ADDR[2],
    AIC_LOC_D_IFD_1_REGION_END_ADDR[0], AIC_LOC_D_IFD_1_REGION_END_ADDR[1], AIC_LOC_D_IFD_1_REGION_END_ADDR[2],
    AIC_LOC_D_ODR_REGION_END_ADDR[0],   AIC_LOC_D_ODR_REGION_END_ADDR[1],   AIC_LOC_D_ODR_REGION_END_ADDR[2]
  };

  // IFD/ODR dev regions:
    // odd requirement for spylgass, redeclare indexes...
  typedef enum int {
    ls_m_ifd0_idx = dmc_pkg::m_ifd0_idx,
    ls_m_ifd1_idx = dmc_pkg::m_ifd1_idx,
    ls_m_ifd2_idx = dmc_pkg::m_ifd2_idx,
    ls_m_ifdw_idx = dmc_pkg::m_ifdw_idx,
    ls_d_ifd0_idx = dmc_pkg::d_ifd0_idx,
    ls_d_ifd1_idx = dmc_pkg::d_ifd1_idx,
    ls_m_odr_idx  = dmc_pkg::m_odr_idx,
    ls_d_odr_idx  = dmc_pkg::d_odr_idx
  } ls_dmc_dev_select_e;
  parameter aic_region_t AIC_LS_DMC_DEV_REGION_ST_ADDR[dmc_pkg::DMC_NR_AXI_DEVS] = '{
    ls_m_ifdw_idx: AIC_LOC_M_IFD_W_REGION_ST_ADDR,
    ls_m_ifd0_idx: AIC_LOC_M_IFD_0_REGION_ST_ADDR,
    ls_m_ifd1_idx: AIC_LOC_M_IFD_1_REGION_ST_ADDR,
    ls_m_ifd2_idx: AIC_LOC_M_IFD_2_REGION_ST_ADDR,
    ls_m_odr_idx:  AIC_LOC_M_ODR_REGION_ST_ADDR,
    ls_d_ifd0_idx: AIC_LOC_D_IFD_0_REGION_ST_ADDR,
    ls_d_ifd1_idx: AIC_LOC_D_IFD_1_REGION_ST_ADDR,
    ls_d_odr_idx:  AIC_LOC_D_ODR_REGION_ST_ADDR
  };
  parameter aic_region_t AIC_LS_DMC_DEV_REGION_END_ADDR[dmc_pkg::DMC_NR_AXI_DEVS] = '{
    ls_m_ifdw_idx: AIC_LOC_M_IFD_W_REGION_END_ADDR,
    ls_m_ifd0_idx: AIC_LOC_M_IFD_0_REGION_END_ADDR,
    ls_m_ifd1_idx: AIC_LOC_M_IFD_1_REGION_END_ADDR,
    ls_m_ifd2_idx: AIC_LOC_M_IFD_2_REGION_END_ADDR,
    ls_m_odr_idx:  AIC_LOC_M_ODR_REGION_END_ADDR,
    ls_d_ifd0_idx: AIC_LOC_D_IFD_0_REGION_END_ADDR,
    ls_d_ifd1_idx: AIC_LOC_D_IFD_1_REGION_END_ADDR,
    ls_d_odr_idx:  AIC_LOC_D_ODR_REGION_END_ADDR
  };

  parameter l1_pkg::mem_map_cfg_t AIC_LS_L1_DAISY_CHAIN_MAPPING[l1_pkg::L1_NR_SUB_BANKS * l1_pkg::DEFAULT_L1_NUM_BANKS * 1] =  '{
    0:  l1_pkg::mem_map_cfg_t'{sb:3, mb:10, m:0},
    1:  l1_pkg::mem_map_cfg_t'{sb:3, mb:9,  m:0},
    2:  l1_pkg::mem_map_cfg_t'{sb:3, mb:8,  m:0},
    3:  l1_pkg::mem_map_cfg_t'{sb:3, mb:7,  m:0},
    4:  l1_pkg::mem_map_cfg_t'{sb:3, mb:6,  m:0},
    5:  l1_pkg::mem_map_cfg_t'{sb:2, mb:11, m:0},
    6:  l1_pkg::mem_map_cfg_t'{sb:2, mb:12, m:0},
    7:  l1_pkg::mem_map_cfg_t'{sb:2, mb:13, m:0},
    8:  l1_pkg::mem_map_cfg_t'{sb:2, mb:14, m:0},
    9:  l1_pkg::mem_map_cfg_t'{sb:2, mb:15, m:0},
    10: l1_pkg::mem_map_cfg_t'{sb:3, mb:0,  m:0},
    11: l1_pkg::mem_map_cfg_t'{sb:2, mb:5,  m:0},
    12: l1_pkg::mem_map_cfg_t'{sb:2, mb:4,  m:0},
    13: l1_pkg::mem_map_cfg_t'{sb:2, mb:3,  m:0},
    14: l1_pkg::mem_map_cfg_t'{sb:2, mb:2,  m:0},
    15: l1_pkg::mem_map_cfg_t'{sb:2, mb:1,  m:0},
    16: l1_pkg::mem_map_cfg_t'{sb:2, mb:0,  m:0},
    17: l1_pkg::mem_map_cfg_t'{sb:1, mb:5,  m:0},
    18: l1_pkg::mem_map_cfg_t'{sb:1, mb:6,  m:0},
    19: l1_pkg::mem_map_cfg_t'{sb:1, mb:7,  m:0},
    20: l1_pkg::mem_map_cfg_t'{sb:1, mb:8,  m:0},
    21: l1_pkg::mem_map_cfg_t'{sb:1, mb:9,  m:0},
    22: l1_pkg::mem_map_cfg_t'{sb:1, mb:10, m:0},
    23: l1_pkg::mem_map_cfg_t'{sb:0, mb:14, m:0},
    24: l1_pkg::mem_map_cfg_t'{sb:0, mb:13, m:0},
    25: l1_pkg::mem_map_cfg_t'{sb:0, mb:12, m:0},
    26: l1_pkg::mem_map_cfg_t'{sb:0, mb:11, m:0},
    27: l1_pkg::mem_map_cfg_t'{sb:0, mb:10, m:0},
    28: l1_pkg::mem_map_cfg_t'{sb:0, mb:0,  m:0},
    29: l1_pkg::mem_map_cfg_t'{sb:0, mb:1,  m:0},
    30: l1_pkg::mem_map_cfg_t'{sb:0, mb:2,  m:0},
    31: l1_pkg::mem_map_cfg_t'{sb:0, mb:3,  m:0},
    32: l1_pkg::mem_map_cfg_t'{sb:0, mb:4,  m:0},
    33: l1_pkg::mem_map_cfg_t'{sb:0, mb:5,  m:0},
    34: l1_pkg::mem_map_cfg_t'{sb:0, mb:15, m:0},
    35: l1_pkg::mem_map_cfg_t'{sb:1, mb:0,  m:0},
    36: l1_pkg::mem_map_cfg_t'{sb:0, mb:6,  m:0},
    37: l1_pkg::mem_map_cfg_t'{sb:0, mb:7,  m:0},
    38: l1_pkg::mem_map_cfg_t'{sb:0, mb:8,  m:0},
    39: l1_pkg::mem_map_cfg_t'{sb:0, mb:9,  m:0},
    40: l1_pkg::mem_map_cfg_t'{sb:1, mb:4,  m:0},
    41: l1_pkg::mem_map_cfg_t'{sb:1, mb:3,  m:0},
    42: l1_pkg::mem_map_cfg_t'{sb:1, mb:2,  m:0},
    43: l1_pkg::mem_map_cfg_t'{sb:1, mb:1,  m:0},
    44: l1_pkg::mem_map_cfg_t'{sb:1, mb:11, m:0},
    45: l1_pkg::mem_map_cfg_t'{sb:1, mb:12, m:0},
    46: l1_pkg::mem_map_cfg_t'{sb:1, mb:13, m:0},
    47: l1_pkg::mem_map_cfg_t'{sb:1, mb:14, m:0},
    48: l1_pkg::mem_map_cfg_t'{sb:1, mb:15, m:0},
    49: l1_pkg::mem_map_cfg_t'{sb:2, mb:10, m:0},
    50: l1_pkg::mem_map_cfg_t'{sb:2, mb:9,  m:0},
    51: l1_pkg::mem_map_cfg_t'{sb:2, mb:8,  m:0},
    52: l1_pkg::mem_map_cfg_t'{sb:2, mb:7,  m:0},
    53: l1_pkg::mem_map_cfg_t'{sb:2, mb:6,  m:0},
    54: l1_pkg::mem_map_cfg_t'{sb:3, mb:1,  m:0},
    55: l1_pkg::mem_map_cfg_t'{sb:3, mb:2,  m:0},
    56: l1_pkg::mem_map_cfg_t'{sb:3, mb:3,  m:0},
    57: l1_pkg::mem_map_cfg_t'{sb:3, mb:4,  m:0},
    58: l1_pkg::mem_map_cfg_t'{sb:3, mb:5,  m:0},
    59: l1_pkg::mem_map_cfg_t'{sb:3, mb:15, m:0},
    60: l1_pkg::mem_map_cfg_t'{sb:3, mb:14, m:0},
    61: l1_pkg::mem_map_cfg_t'{sb:3, mb:13, m:0},
    62: l1_pkg::mem_map_cfg_t'{sb:3, mb:12, m:0},
    63: l1_pkg::mem_map_cfg_t'{sb:3, mb:11, m:0}
  };

endpackage
