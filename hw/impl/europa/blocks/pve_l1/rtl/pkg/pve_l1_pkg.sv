// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>


/// PVE L1 europa implementation package
///
package pve_l1_pkg;
  import cva6v_pve_pkg::*;

  parameter int unsigned PVE_L1_MEM_ADDR_W = 22;
  parameter int unsigned PVE_L1_BASE_ADDR_W = chip_pkg::CHIP_AXI_ADDR_W - PVE_L1_MEM_ADDR_W;
  typedef logic [PVE_L1_BASE_ADDR_W-1:0] pve_l1_base_addr_t;

  // Types - MEM
  typedef logic [pve_pkg::PVE_CLUSTER_N_CPU*MemPortCount                 -1:0] pve_l1_mem_logic_t;
  typedef logic [pve_pkg::PVE_CLUSTER_N_CPU*MemPortCount*MemPortBeWidth  -1:0] pve_l1_mem_be_t;
  typedef logic [pve_pkg::PVE_CLUSTER_N_CPU*MemPortCount*MemPortWidth    -1:0] pve_l1_mem_data_t;
  typedef logic [pve_pkg::PVE_CLUSTER_N_CPU*MemPortCount*MemPortAddrWidth-1:0] pve_l1_mem_addr_t;

  parameter int unsigned PVE_L1_NUM_MACRO = l1_pkg::L1_NR_SUB_BANKS * pve_pkg::PVE_CLUSTER_N_CPU * MemPortCount * 1;
  parameter l1_pkg::mem_map_cfg_t PVE_L1_DAISY_CHAIN_MAPPING[PVE_L1_NUM_MACRO] =  '{
    0:  l1_pkg::mem_map_cfg_t'{sb:3, mb:7,  m:0},
    1:  l1_pkg::mem_map_cfg_t'{sb:3, mb:8,  m:0},
    2:  l1_pkg::mem_map_cfg_t'{sb:3, mb:9,  m:0},
    3:  l1_pkg::mem_map_cfg_t'{sb:3, mb:0,  m:0},
    4:  l1_pkg::mem_map_cfg_t'{sb:2, mb:15, m:0},
    5:  l1_pkg::mem_map_cfg_t'{sb:2, mb:14, m:0},
    6:  l1_pkg::mem_map_cfg_t'{sb:2, mb:5,  m:0},
    7:  l1_pkg::mem_map_cfg_t'{sb:2, mb:6,  m:0},
    8:  l1_pkg::mem_map_cfg_t'{sb:2, mb:7,  m:0},
    9:  l1_pkg::mem_map_cfg_t'{sb:1, mb:14, m:0},
    10: l1_pkg::mem_map_cfg_t'{sb:1, mb:13, m:0},
    11: l1_pkg::mem_map_cfg_t'{sb:1, mb:12, m:0},
    12: l1_pkg::mem_map_cfg_t'{sb:1, mb:3,  m:0},
    13: l1_pkg::mem_map_cfg_t'{sb:1, mb:4,  m:0},
    14: l1_pkg::mem_map_cfg_t'{sb:1, mb:5,  m:0},
    15: l1_pkg::mem_map_cfg_t'{sb:0, mb:12, m:0},
    16: l1_pkg::mem_map_cfg_t'{sb:0, mb:11, m:0},
    17: l1_pkg::mem_map_cfg_t'{sb:0, mb:10, m:0},
    18: l1_pkg::mem_map_cfg_t'{sb:0, mb:0,  m:0},
    19: l1_pkg::mem_map_cfg_t'{sb:0, mb:1,  m:0},
    20: l1_pkg::mem_map_cfg_t'{sb:0, mb:2,  m:0},
    21: l1_pkg::mem_map_cfg_t'{sb:0, mb:3,  m:0},
    22: l1_pkg::mem_map_cfg_t'{sb:0, mb:4,  m:0},
    23: l1_pkg::mem_map_cfg_t'{sb:0, mb:5,  m:0},
    24: l1_pkg::mem_map_cfg_t'{sb:0, mb:13, m:0},
    25: l1_pkg::mem_map_cfg_t'{sb:0, mb:14, m:0},
    26: l1_pkg::mem_map_cfg_t'{sb:0, mb:15, m:0},
    27: l1_pkg::mem_map_cfg_t'{sb:1, mb:0,  m:0},
    28: l1_pkg::mem_map_cfg_t'{sb:0, mb:6,  m:0},
    29: l1_pkg::mem_map_cfg_t'{sb:0, mb:7,  m:0},
    30: l1_pkg::mem_map_cfg_t'{sb:0, mb:8,  m:0},
    31: l1_pkg::mem_map_cfg_t'{sb:0, mb:9,  m:0},
    32: l1_pkg::mem_map_cfg_t'{sb:1, mb:1,  m:0},
    33: l1_pkg::mem_map_cfg_t'{sb:1, mb:2,  m:0},
    34: l1_pkg::mem_map_cfg_t'{sb:1, mb:11, m:0},
    35: l1_pkg::mem_map_cfg_t'{sb:1, mb:10, m:0},
    36: l1_pkg::mem_map_cfg_t'{sb:1, mb:9,  m:0},
    37: l1_pkg::mem_map_cfg_t'{sb:1, mb:8,  m:0},
    38: l1_pkg::mem_map_cfg_t'{sb:1, mb:7,  m:0},
    39: l1_pkg::mem_map_cfg_t'{sb:1, mb:6,  m:0},
    40: l1_pkg::mem_map_cfg_t'{sb:1, mb:15, m:0},
    41: l1_pkg::mem_map_cfg_t'{sb:2, mb:0,  m:0},
    42: l1_pkg::mem_map_cfg_t'{sb:2, mb:1,  m:0},
    43: l1_pkg::mem_map_cfg_t'{sb:2, mb:2,  m:0},
    44: l1_pkg::mem_map_cfg_t'{sb:2, mb:3,  m:0},
    45: l1_pkg::mem_map_cfg_t'{sb:2, mb:4,  m:0},
    46: l1_pkg::mem_map_cfg_t'{sb:2, mb:13, m:0},
    47: l1_pkg::mem_map_cfg_t'{sb:2, mb:12, m:0},
    48: l1_pkg::mem_map_cfg_t'{sb:2, mb:11, m:0},
    49: l1_pkg::mem_map_cfg_t'{sb:2, mb:10, m:0},
    50: l1_pkg::mem_map_cfg_t'{sb:2, mb:9,  m:0},
    51: l1_pkg::mem_map_cfg_t'{sb:2, mb:8,  m:0},
    52: l1_pkg::mem_map_cfg_t'{sb:3, mb:1,  m:0},
    53: l1_pkg::mem_map_cfg_t'{sb:3, mb:2,  m:0},
    54: l1_pkg::mem_map_cfg_t'{sb:3, mb:3,  m:0},
    55: l1_pkg::mem_map_cfg_t'{sb:3, mb:4,  m:0},
    56: l1_pkg::mem_map_cfg_t'{sb:3, mb:5,  m:0},
    57: l1_pkg::mem_map_cfg_t'{sb:3, mb:6,  m:0},
    58: l1_pkg::mem_map_cfg_t'{sb:3, mb:15, m:0},
    59: l1_pkg::mem_map_cfg_t'{sb:3, mb:14, m:0},
    60: l1_pkg::mem_map_cfg_t'{sb:3, mb:13, m:0},
    61: l1_pkg::mem_map_cfg_t'{sb:3, mb:12, m:0},
    62: l1_pkg::mem_map_cfg_t'{sb:3, mb:11, m:0},
    63: l1_pkg::mem_map_cfg_t'{sb:3, mb:10, m:0}
    };
endpackage
