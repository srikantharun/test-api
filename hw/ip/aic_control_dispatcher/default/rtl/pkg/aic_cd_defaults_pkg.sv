// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// This provides some defaults to match the europa aic_infra implmenetation
///
package aic_cd_defaults_pkg;
  parameter int unsigned AXI_S_ID_WIDTH   = 7;
  parameter int unsigned AXI_S_ADDR_WIDTH = 40;
  parameter int unsigned AXI_S_DATA_WIDTH = 64;

  typedef logic [AXI_S_ID_WIDTH    -1:0] axi_s_id_t;
  typedef logic [AXI_S_ADDR_WIDTH  -1:0] axi_s_addr_t;
  typedef logic [AXI_S_DATA_WIDTH  -1:0] axi_s_data_t;
  typedef logic [AXI_S_DATA_WIDTH/8-1:0] axi_s_strb_t;

  typedef struct packed {
    axi_s_id_t           id;
    axi_s_addr_t         addr;
    axi_pkg::axi_len_t   len;
    axi_pkg::axi_size_t  size;
    axi_pkg::axi_burst_t burst;
    logic                lock;
    axi_pkg::axi_cache_t cache;
    axi_pkg::axi_prot_t  prot;
  } axi_s_aw_t;

  typedef struct packed {
    axi_s_data_t data;
    axi_s_strb_t strb;
    logic        last;
  } axi_s_w_t;

  typedef struct packed {
    axi_s_id_t          id;
    axi_pkg::axi_resp_t resp;
  } axi_s_b_t;

  typedef struct packed {
    axi_s_id_t           id;
    axi_s_addr_t         addr;
    axi_pkg::axi_len_t   len;
    axi_pkg::axi_size_t  size;
    axi_pkg::axi_burst_t burst;
    logic                lock;
    axi_pkg::axi_cache_t cache;
    axi_pkg::axi_prot_t  prot;
  } axi_s_ar_t;

  typedef struct packed {
    axi_s_id_t          id;
    axi_s_data_t        data;
    axi_pkg::axi_resp_t resp;
    logic               last;
  } axi_s_r_t;


  parameter int unsigned AXI_M_ID_WIDTH   = 6;
  parameter int unsigned AXI_M_ADDR_WIDTH = 40;
  parameter int unsigned AXI_M_DATA_WIDTH = 64;

  typedef logic [AXI_M_ID_WIDTH    -1:0] axi_m_id_t;
  typedef logic [AXI_M_ADDR_WIDTH  -1:0] axi_m_addr_t;
  typedef logic [AXI_M_DATA_WIDTH  -1:0] axi_m_data_t;
  typedef logic [AXI_M_DATA_WIDTH/8-1:0] axi_m_strb_t;

  typedef struct packed {
    axi_m_id_t           id;
    axi_m_addr_t         addr;
    axi_pkg::axi_len_t   len;
    axi_pkg::axi_size_t  size;
    axi_pkg::axi_burst_t burst;
    logic                lock;
    axi_pkg::axi_cache_t cache;
    axi_pkg::axi_prot_t  prot;
  } axi_m_aw_t;

  typedef struct packed {
    axi_m_data_t data;
    axi_m_strb_t strb;
    logic        last;
  } axi_m_w_t;

  typedef struct packed {
    axi_m_id_t          id;
    axi_pkg::axi_resp_t resp;
  } axi_m_b_t;

  typedef struct packed {
    axi_m_id_t           id;
    axi_m_addr_t         addr;
    axi_pkg::axi_len_t   len;
    axi_pkg::axi_size_t  size;
    axi_pkg::axi_burst_t burst;
    logic                lock;
    axi_pkg::axi_cache_t cache;
    axi_pkg::axi_prot_t  prot;
  } axi_m_ar_t;

  typedef struct packed {
    axi_m_id_t          id;
    axi_m_data_t        data;
    axi_pkg::axi_resp_t resp;
    logic               last;
  } axi_m_r_t;

endpackage
