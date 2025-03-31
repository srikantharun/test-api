// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

/// SPM IP module package
`ifndef SPM_PACKAGE_SV
`define SPM_PACKAGE_SV

package spm_pkg;
  // =======================================
  // Parameter definition
  // =======================================
  parameter int unsigned OOR_ERR_EN        = 1;

  parameter int unsigned SPM_ERR_SYNDROME_W = 8;
  parameter int unsigned SPM_ERR_INDEX_W    = 20;
  parameter int unsigned SPM_MEM_ADDR_MAX_WIDTH = 23; // 8k

  // =======================================
  // Type definition
  // =======================================

  // Just a QoL type
  typedef struct packed {
    logic wr;
    logic rd;
  } spm_access_t;

  // -- FSMs
  typedef enum logic [0:0] {
    ST_SPM_IDLE   = 1'b0,
    ST_SPM_LOCKED = 1'b1
  } state_t;

  // -- ECC
  //    . error          (0:not present, 1: present)
  //    . error_type     (0:single error, 1: double error)
  //    . error_index    (index/line in mem)
  //    . 8-bit syndrome (index within double-word/line)
  typedef enum logic {
      SINGLE = 1'b0,
      DOUBLE = 1'b1
  } spm_ecc_err_type_t;

  typedef logic [SPM_ERR_SYNDROME_W-1:0] spm_ecc_err_syndrome_t;
  typedef logic [SPM_ERR_INDEX_W-1:0]    spm_ecc_err_index_t;

  typedef struct packed {
    spm_ecc_err_index_t    ecc_err_index;
    spm_ecc_err_syndrome_t ecc_err_syndrome;
    spm_ecc_err_type_t     ecc_err_type;
    logic                  ecc_err;
  } spm_error_status_t;

  // -- Base memory address types
  typedef struct packed {
    logic  [0:0] sel;
    logic [13:0] sram_addr;
  } spm_mem_addr_ab_t;

  // daisy chain mapping:
  typedef int unsigned uint_t;

  typedef struct packed {
    int bank_idx;
    int subbank_idx;
    int minibank_idx;
    int srams_idx;
  } spm_mem_map_cfg_t;

  typedef struct packed {
    logic irq;
    logic mem_rvalid;
    logic mem_we;
    logic mem_req;
    logic rsp_fifo_pop;
    logic rsp_fifo_push;
    logic waiting_for_rmw;
    logic state;
    logic axi2reg_rsp_rd_err;
    logic axi2reg_rsp_rd_rsp;
    logic axi2reg_ready_rd;
    logic axi2reg_req_rd_en;
    logic axi2reg_rsp_wr_err;
    logic axi2reg_rsp_wr_rsp;
    logic axi2reg_ready_wr;
    logic axi2reg_req_wr_en;
  } spm_obs_t;
 endpackage
`endif  //SPM_PACKAGE_SV
