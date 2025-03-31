// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>


/// Few fixed parameters / typedefs for the TokenManager in general
package token_manager_pkg;

  typedef int unsigned uint_t;

  typedef struct {
    bit    present;
    uint_t max_num_prod;
    uint_t max_num_cons;
    uint_t nr_loc_devs;
    uint_t nr_cntrs;
    uint_t prod_cntr_width;
    uint_t cons_cntr_width;
    bit    loc_is_sw_only; // only used for top
  } tokmgr_cfg_t;

  typedef struct {
    uint_t r2h_lsb;
    uint_t r2h_dw;
    uint_t h2r_lsb;
    uint_t h2r_dw;
  } tokmgr_csr_info_t;

  typedef tokmgr_csr_info_t TokMgrCsrInfo_t[15];

  typedef enum int {
    swep_prod_idx = 0,
    swep_cons_idx = 1,
    irq_swep_prod_sat_idx = 2,
    irq_en_swep_prod_sat_idx = 3,
    irq_swep_cons_sat_idx = 4,
    irq_en_swep_cons_sat_idx = 5,
    irq_swep_cons_non_zero_idx = 6,
    irq_en_swep_cons_non_zero_idx = 7,
    irq_prod_idx = 8,
    irq_en_prod_idx = 9,
    prod_cnt_idx = 10,
    irq_cons_idx = 11,
    irq_en_cons_idx = 12,
    cons_cnt_idx = 13,
    irq_top_map_idx=14
  } tok_mgr_csr_info_e;

  parameter uint_t TOKEN_MANAGER_UID_W    = 6;
  parameter uint_t TOKEN_MANAGER_DEV_W    = 2; // (V)UID is build up with CoreID(4 bits) and DevId (2 bits)
  parameter uint_t TOKEN_MANAGER_MAX_VUID = 44;

  typedef logic [TOKEN_MANAGER_UID_W-1:0] tokmgr_uid_t;

  typedef struct packed {
    tokmgr_uid_t rsvd;
    tokmgr_uid_t dma_ch1;
    tokmgr_uid_t dma_ch0;
    tokmgr_uid_t acd;
  } tokmgr_uid_acd_t;

  typedef struct packed {
    tokmgr_uid_t ch3;
    tokmgr_uid_t ch2;
    tokmgr_uid_t ch1;
    tokmgr_uid_t ch0;
  } tokmgr_uid_sdma_t;

  typedef struct packed {
    tokmgr_uid_t apu;
    tokmgr_uid_sdma_t sdma1;
    tokmgr_uid_sdma_t sdma0;
    tokmgr_uid_acd_t aic7;
    tokmgr_uid_acd_t aic6;
    tokmgr_uid_acd_t aic5;
    tokmgr_uid_acd_t aic4;
    tokmgr_uid_acd_t aic3;
    tokmgr_uid_acd_t aic2;
    tokmgr_uid_acd_t aic1;
    tokmgr_uid_acd_t aic0;
    tokmgr_uid_acd_t rsvd;
  } tokmgr_uid_all_t;


endpackage
