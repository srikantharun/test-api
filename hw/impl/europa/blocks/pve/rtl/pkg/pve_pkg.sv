// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>
//        Matt Morris <matt.morris@axelera.ai>


/// PVE Package File
///

package pve_pkg;

  import axi_pkg::*;
  import chip_pkg::*;

  typedef int unsigned uint_t;

  // PVE specific AXI parameters
  parameter uint_t PVE_LT_S_ID_W = cva6v_pve_pkg::AxiIdWidth;
  typedef logic [PVE_LT_S_ID_W-1:0] pve_lt_axi_s_id_t;
  parameter uint_t PVE_HT_S_ID_W = 8;
  typedef logic [PVE_HT_S_ID_W-1:0] pve_ht_axi_s_id_t;

  // PVE Primary parameters
  parameter uint_t PVE_N_CLUSTERS = 4;
  parameter uint_t PVE_CLUSTER_N_CPU = 2;
  parameter uint_t PVE_N_CPU = PVE_N_CLUSTERS * PVE_CLUSTER_N_CPU;
  parameter uint_t PVE_HART_BASE_W = 6;
  parameter uint_t PVE_N_DMA = 2;
  parameter uint_t PVE_N_DMA_CHNLS = 4;
  parameter uint_t PVE_N_DMA_PORTS = 2;
  parameter uint_t PVE_SYNC_STAGES = 3;

  // FABRIC PARAMETERS - LT FABRIC

  parameter uint_t PVE_FABRIC_N_LT_S_EXT_PORTS = 9;
  parameter uint_t PVE_FABRIC_N_LT_M_EXT_PORTS = 6;
  parameter uint_t PVE_FABRIC_N_HT_S_EXT_PORTS = 4;
  parameter uint_t PVE_FABRIC_N_HT_M_EXT_PORTS = 5;

  parameter uint_t PVE_FABRIC_N_LT_S_INT_PORTS = 1;
  parameter uint_t PVE_FABRIC_N_LT_M_INT_PORTS = 1;
  parameter uint_t PVE_FABRIC_N_HT_S_INT_PORTS = 1;
  parameter uint_t PVE_FABRIC_N_HT_M_INT_PORTS = 1;

  parameter uint_t PVE_FABRIC_N_LT_S_PORTS = PVE_FABRIC_N_LT_S_EXT_PORTS + PVE_FABRIC_N_LT_S_INT_PORTS;
  parameter uint_t PVE_FABRIC_N_LT_M_PORTS = PVE_FABRIC_N_LT_M_EXT_PORTS + PVE_FABRIC_N_LT_M_INT_PORTS;
  parameter uint_t PVE_FABRIC_N_HT_S_PORTS = PVE_FABRIC_N_HT_S_EXT_PORTS + PVE_FABRIC_N_HT_S_INT_PORTS;
  parameter uint_t PVE_FABRIC_N_HT_M_PORTS = PVE_FABRIC_N_HT_M_EXT_PORTS + PVE_FABRIC_N_HT_M_INT_PORTS;

  // Port Indexes
  parameter uint_t PVE_LT_S_PRTIDX_W = $clog2(PVE_FABRIC_N_LT_S_PORTS);
  typedef logic[PVE_LT_S_PRTIDX_W-1:0] pve_lt_s_port_idx_t;

  parameter uint_t PVE_LT_M_PRTIDX_W = $clog2(PVE_FABRIC_N_LT_M_PORTS);
  typedef logic[PVE_LT_M_PRTIDX_W-1:0] pve_lt_m_port_idx_t;

  parameter uint_t PVE_HT_S_PRTIDX_W = $clog2(PVE_FABRIC_N_HT_S_PORTS);
  typedef logic[PVE_HT_S_PRTIDX_W-1:0] pve_ht_s_port_idx_t;

  parameter uint_t PVE_HT_M_PRTIDX_W = $clog2(PVE_FABRIC_N_HT_M_PORTS);
  typedef logic[PVE_HT_M_PRTIDX_W-1:0] pve_ht_m_port_idx_t;

  // Types - input to LT and MT XBAR
  parameter uint_t PVE_LT_M_ID_W = PVE_LT_S_ID_W + PVE_LT_S_PRTIDX_W;
  parameter uint_t PVE_HT_M_ID_W = PVE_HT_S_ID_W + PVE_HT_S_PRTIDX_W;
  typedef logic [PVE_LT_M_ID_W-1:0] pve_lt_axi_m_id_t;
  typedef logic [PVE_HT_M_ID_W-1:0] pve_ht_axi_m_id_t;

  // AXI LT S types
  typedef struct packed {
    pve_lt_axi_s_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
    axi_atop_t        atop;
  } pve_lt_s_aw_t;

  typedef struct packed {
    chip_axi_lt_data_t  data;
    chip_axi_lt_wstrb_t strb;
    logic               last;
  } pve_lt_w_t;

  typedef struct packed {
    pve_lt_axi_s_id_t id;
    axi_resp_e        resp;
  } pve_lt_s_b_t;

  typedef struct packed {
    pve_lt_axi_s_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
  } pve_lt_s_ar_t;

  typedef struct packed {
    pve_lt_axi_s_id_t  id;
    chip_axi_lt_data_t data;
    axi_resp_e         resp;
    logic              last;
  } pve_lt_s_r_t;

  // AXI LT M types
  typedef struct packed {
    pve_lt_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
    axi_atop_t        atop;
  } pve_lt_m_aw_t;

  typedef struct packed {
    pve_lt_axi_m_id_t id;
    axi_resp_e        resp;
  } pve_lt_m_b_t;

  typedef struct packed {
    pve_lt_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
  } pve_lt_m_ar_t;

  typedef struct packed {
    pve_lt_axi_m_id_t  id;
    chip_axi_lt_data_t data;
    axi_resp_e         resp;
    logic              last;
  } pve_lt_m_r_t;

  // PVE LT M request
  typedef struct packed {
    pve_lt_m_aw_t aw;
    logic         aw_valid;
    pve_lt_w_t    w;
    logic         w_valid;
    logic         b_ready;
    pve_lt_m_ar_t ar;
    logic         ar_valid;
    logic         r_ready;
  } pve_lt_m_req_t;

  // PVE LT M response
  typedef struct packed {
    logic        aw_ready;
    logic        ar_ready;
    logic        w_ready;
    logic        b_valid;
    pve_lt_m_b_t b;
    logic        r_valid;
    pve_lt_m_r_t r;
  } pve_lt_m_rsp_t;

  // LT Address rules struct
  typedef struct packed {
    pve_lt_m_port_idx_t index;
    chip_axi_addr_t     addr_start;
    chip_axi_addr_t     addr_end;
  } pve_lt_xbar_rule_t;

  //  LT XBAR
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL0CPU0 = pve_lt_s_port_idx_t'(0);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL0CPU1 = pve_lt_s_port_idx_t'(1);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL1CPU0 = pve_lt_s_port_idx_t'(2);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL1CPU1 = pve_lt_s_port_idx_t'(3);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL2CPU0 = pve_lt_s_port_idx_t'(4);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL2CPU1 = pve_lt_s_port_idx_t'(5);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL3CPU0 = pve_lt_s_port_idx_t'(6);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_CL3CPU1 = pve_lt_s_port_idx_t'(7);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_EXT     = pve_lt_s_port_idx_t'(8);
  parameter pve_lt_s_port_idx_t PVE_LT_S_PRTIDX_INTHT   = pve_lt_s_port_idx_t'(9);

  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_DMA0    = pve_lt_m_port_idx_t'(0);
  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_DMA1    = pve_lt_m_port_idx_t'(1);
  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_CLINT   = pve_lt_m_port_idx_t'(2);
  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_PERFC   = pve_lt_m_port_idx_t'(3);
  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_SPM     = pve_lt_m_port_idx_t'(4);
  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_EXT     = pve_lt_m_port_idx_t'(5);
  parameter pve_lt_m_port_idx_t PVE_LT_M_PRTIDX_INTHT   = pve_lt_m_port_idx_t'(6);

  //  ROUTING:                                                  //
  //  ========                                                  //
  //                                                            //
  //  MNG->   | 0 | 1 | 2 | 3 | 4 | 5 | 6 |                     //
  //  --------|---|---|---|---|---|---|---|                     //
  //  SUB  0  | . | . | . | . | . | . | . |                     //
  //  SUB  1  | . | . | . | . | . | . | . |                     //
  //  SUB  2  | . | . | . | . | . | . | . |                     //
  //  SUB  3  | . | . | . | . | . | . | . |                     //
  //  SUB  4  | . | . | . | . | . | . | . |                     //
  //  SUB  5  | . | . | . | . | . | . | . |                     //
  //  SUB  6  | . | . | . | . | . | . | . |                     //
  //  SUB  7  | . | . | . | . | . | . | . |                     //
  //  SUB  8  | . | . | . | . | . | X | . |                     //
  //  SUB  9  | . | . | . | . | . | X | X |                     //

  parameter logic [PVE_FABRIC_N_LT_S_PORTS-1:0][PVE_FABRIC_N_LT_M_PORTS:0] PVE_LT_CONNECTIVITY = {
      7'h1f, 7'h5f, 7'h7f, 7'h7f, 7'h7f, 7'h7f, 7'h7f, 7'h7f, 7'h7f, 7'h7f };

  // Address Map
  typedef logic[PVE_HART_BASE_W-1:0] pve_hart_base_t;
  parameter pve_hart_base_t PVE0_HART_BASE = 14;
  parameter pve_hart_base_t PVE1_HART_BASE = 22;

  parameter int unsigned PVE_AXI_ADDR_W             = 28;
  parameter chip_axi_addr_t PVE0_BASE_ADDR          = chip_axi_addr_t'('h9000_0000);
  parameter chip_axi_addr_t PVE1_BASE_ADDR          = chip_axi_addr_t'('ha000_0000);

  parameter chip_axi_addr_t PVE_TGT_DMA0_MMAP_BASE  = chip_axi_addr_t'('h0000_0000);
  parameter chip_axi_addr_t PVE_TGT_DMA0_MMAP_SIZE  = chip_axi_addr_t'('h0004_0000);
  parameter chip_axi_addr_t PVE_TGT_DMA0_MMAP_TOP   = PVE_TGT_DMA0_MMAP_BASE + PVE_TGT_DMA0_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter chip_axi_addr_t PVE_TGT_DMA1_MMAP_BASE  = chip_axi_addr_t'('h0004_0000);
  parameter chip_axi_addr_t PVE_TGT_DMA1_MMAP_SIZE  = chip_axi_addr_t'('h0004_0000);
  parameter chip_axi_addr_t PVE_TGT_DMA1_MMAP_TOP   = PVE_TGT_DMA1_MMAP_BASE + PVE_TGT_DMA1_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter int unsigned    PVE_TGT_DMA_MMAP_W      = 18;
  parameter chip_axi_addr_t PVE_TGT_CLINT_MMAP_BASE = chip_axi_addr_t'('h0008_0000);
  parameter chip_axi_addr_t PVE_TGT_CLINT_MMAP_SIZE = chip_axi_addr_t'('h0001_0000);
  parameter chip_axi_addr_t PVE_TGT_CLINT_MMAP_TOP  = PVE_TGT_CLINT_MMAP_BASE + PVE_TGT_CLINT_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter chip_axi_addr_t PVE_TGT_PERFC_MMAP_BASE = chip_axi_addr_t'('h0009_0000);
  parameter chip_axi_addr_t PVE_TGT_PERFC_MMAP_SIZE = chip_axi_addr_t'('h0001_0000);
  parameter chip_axi_addr_t PVE_TGT_PERFC_MMAP_TOP  = PVE_TGT_PERFC_MMAP_BASE + PVE_TGT_PERFC_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter chip_axi_addr_t PVE_TGT_SPM_MMAP_BASE   = chip_axi_addr_t'('h0400_0000);
  parameter chip_axi_addr_t PVE_TGT_SPM_MMAP_SIZE   = chip_axi_addr_t'('h0004_0000);
  parameter chip_axi_addr_t PVE_TGT_SPM_MMAP_TOP    = PVE_TGT_SPM_MMAP_BASE + PVE_TGT_SPM_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter int unsigned    PVE_TGT_SPM_MMAP_W      = 18;

  typedef logic[PVE_TGT_DMA_MMAP_W-1:0] dma_conf_addr_t;
  typedef logic[PVE_TGT_SPM_MMAP_W-1:0] spm_addr_t;

  parameter chip_axi_addr_t PVE_TGT_CL0L1_MMAP_BASE = chip_axi_addr_t'('h0800_0000);
  parameter chip_axi_addr_t PVE_TGT_CL0L1_MMAP_SIZE = chip_axi_addr_t'('h0040_0000);
  parameter chip_axi_addr_t PVE_TGT_CL0L1_MMAP_TOP  = PVE_TGT_CL0L1_MMAP_BASE + PVE_TGT_CL0L1_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter chip_axi_addr_t PVE_TGT_CL1L1_MMAP_BASE = chip_axi_addr_t'('h0840_0000);
  parameter chip_axi_addr_t PVE_TGT_CL1L1_MMAP_SIZE = chip_axi_addr_t'('h0040_0000);
  parameter chip_axi_addr_t PVE_TGT_CL1L1_MMAP_TOP  = PVE_TGT_CL1L1_MMAP_BASE + PVE_TGT_CL1L1_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter chip_axi_addr_t PVE_TGT_CL2L1_MMAP_BASE = chip_axi_addr_t'('h0880_0000);
  parameter chip_axi_addr_t PVE_TGT_CL2L1_MMAP_SIZE = chip_axi_addr_t'('h0040_0000);
  parameter chip_axi_addr_t PVE_TGT_CL2L1_MMAP_TOP  = PVE_TGT_CL2L1_MMAP_BASE + PVE_TGT_CL2L1_MMAP_SIZE - chip_axi_addr_t'(1);
  parameter chip_axi_addr_t PVE_TGT_CL3L1_MMAP_BASE = chip_axi_addr_t'('h08C0_0000);
  parameter chip_axi_addr_t PVE_TGT_CL3L1_MMAP_SIZE = chip_axi_addr_t'('h0040_0000);
  parameter chip_axi_addr_t PVE_TGT_CL3L1_MMAP_TOP  = PVE_TGT_CL3L1_MMAP_BASE + PVE_TGT_CL3L1_MMAP_SIZE - chip_axi_addr_t'(1);

  // FABRIC PARAMETERS - HT FABRIC

  // AXI HT S types
  typedef struct packed {
    pve_ht_axi_s_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
    axi_atop_t        atop;
  } pve_ht_s_aw_t;

  typedef struct packed {
    chip_axi_ht_data_t  data;
    chip_axi_ht_wstrb_t strb;
    logic               last;
  } pve_ht_w_t;

  typedef struct packed {
    pve_ht_axi_s_id_t id;
    axi_resp_e        resp;
  } pve_ht_s_b_t;

  typedef struct packed {
    pve_ht_axi_s_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
  } pve_ht_s_ar_t;

  typedef struct packed {
    pve_ht_axi_s_id_t  id;
    chip_axi_ht_data_t data;
    axi_resp_e         resp;
    logic              last;
  } pve_ht_s_r_t;

  // AXI HT M types
  typedef struct packed {
    pve_ht_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
    axi_atop_t        atop;
  } pve_ht_m_aw_t;

  typedef struct packed {
    pve_ht_axi_m_id_t id;
    axi_resp_e        resp;
  } pve_ht_m_b_t;

  typedef struct packed {
    pve_ht_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
  } pve_ht_m_ar_t;

  typedef struct packed {
    pve_ht_axi_m_id_t  id;
    chip_axi_ht_data_t data;
    axi_resp_e         resp;
    logic              last;
  } pve_ht_m_r_t;

  // AXI HT M type with reduced AXI LT S ID
  typedef struct packed {
    pve_lt_axi_s_id_t  id;
    chip_axi_ht_data_t data;
    axi_resp_e         resp;
    logic              last;
  } pve_ht_m_ltid_r_t;

  // HT Address rules struct
  typedef struct packed {
    pve_ht_m_port_idx_t index;
    chip_axi_addr_t     addr_start;
    chip_axi_addr_t     addr_end;
  } pve_ht_xbar_rule_t;

  //  HT XBAR
  parameter pve_ht_s_port_idx_t PVE_HT_S_PRTIDX_DMA0PRT0 = pve_ht_s_port_idx_t'(0);
  parameter pve_ht_s_port_idx_t PVE_HT_S_PRTIDX_DMA0PRT1 = pve_ht_s_port_idx_t'(1);
  parameter pve_ht_s_port_idx_t PVE_HT_S_PRTIDX_DMA1PRT0 = pve_ht_s_port_idx_t'(2);
  parameter pve_ht_s_port_idx_t PVE_HT_S_PRTIDX_DMA1PRT1 = pve_ht_s_port_idx_t'(3);
  parameter pve_ht_s_port_idx_t PVE_HT_S_PRTIDX_INTLT    = pve_ht_s_port_idx_t'(4);

  parameter pve_ht_m_port_idx_t PVE_HT_M_PRTIDX_CL0L1    = pve_ht_m_port_idx_t'(0);
  parameter pve_ht_m_port_idx_t PVE_HT_M_PRTIDX_CL1L1    = pve_ht_m_port_idx_t'(1);
  parameter pve_ht_m_port_idx_t PVE_HT_M_PRTIDX_CL2L1    = pve_ht_m_port_idx_t'(2);
  parameter pve_ht_m_port_idx_t PVE_HT_M_PRTIDX_CL3L1    = pve_ht_m_port_idx_t'(3);
  parameter pve_ht_m_port_idx_t PVE_HT_M_PRTIDX_EXT      = pve_ht_m_port_idx_t'(4);
  parameter pve_ht_m_port_idx_t PVE_HT_M_PRTIDX_INTLT    = pve_ht_m_port_idx_t'(5);

  //  ROUTING:                                                     //
  //  ========                                                     //
  //                                                               //
  //  MNG->  | 0 | 1 | 2 | 3 | 4 | 5 |                             //
  //  -------|---|---|---|---|---|---|                             //
  //  SUB  0 | X | X | X | X | . | . |                             //
  //  SUB  1 | . | . | . | . | X | X |                             //
  //  SUB  2 | X | X | X | X | . | . |                             //
  //  SUB  3 | . | . | . | . | X | X |                             //
  //  SUB  4 | . | . | . | . | X | X |                             //

  parameter logic [PVE_FABRIC_N_HT_S_PORTS:0][PVE_FABRIC_N_HT_M_PORTS-1:0] PVE_HT_CONNECTIVITY = {
      6'h0f, 6'h0f, 6'h30, 6'h0f, 6'h30 };

  // CLINT LT types
  typedef struct packed {
    pve_lt_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_t        size;
  } clint_lt_aw_t;

  typedef struct packed {
    pve_lt_axi_m_id_t id;
    axi_resp_t        resp;
  } clint_lt_b_t;

  typedef struct packed {
    pve_lt_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_t        size;
  } clint_lt_ar_t;

  typedef struct packed {
    pve_lt_axi_m_id_t  id;
    chip_axi_lt_data_t data;
    axi_resp_t         resp;
    logic              last;
  } clint_lt_r_t;

  // CLINT LT request
  typedef struct packed {
    clint_lt_aw_t aw;
    logic         aw_valid;
    pve_lt_w_t    w;
    logic         w_valid;
    logic         b_ready;
    clint_lt_ar_t ar;
    logic         ar_valid;
    logic         r_ready;
  } clint_lt_req_t;

  // CLINT LT response
  typedef struct packed {
    logic        aw_ready;
    logic        ar_ready;
    logic        w_ready;
    logic        b_valid;
    clint_lt_b_t b;
    logic        r_valid;
    clint_lt_r_t r;
  } clint_lt_rsp_t;

  // PERF COUNTERS LT types
  typedef struct packed {
    pve_lt_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
    axi_qos_t         qos;
    axi_region_t      region;
    axi_atop_t        atop;
    logic             user;
  } perfc_lt_aw_t;

  typedef struct packed {
    chip_axi_lt_data_t  data;
    chip_axi_lt_wstrb_t strb;
    logic               last;
    logic               user;
  } perfc_lt_w_t;

  typedef struct packed {
    pve_lt_axi_m_id_t id;
    axi_resp_e        resp;
    logic             user;
  } perfc_lt_b_t;

  typedef struct packed {
    pve_lt_axi_m_id_t id;
    chip_axi_addr_t   addr;
    axi_len_t         len;
    axi_size_e        size;
    axi_burst_e       burst;
    logic             lock;
    axi_cache_e       cache;
    axi_prot_t        prot;
    axi_qos_t         qos;
    axi_region_t      region;
    logic             user;
  } perfc_lt_ar_t;

  typedef struct packed {
    pve_lt_axi_m_id_t  id;
    chip_axi_lt_data_t data;
    axi_resp_e         resp;
    logic              last;
    logic              user;
  } perfc_lt_r_t;

  // PERF COUNTERS LT request
  typedef struct packed {
    perfc_lt_aw_t aw;
    logic         aw_valid;
    perfc_lt_w_t  w;
    logic         w_valid;
    logic         b_ready;
    perfc_lt_ar_t ar;
    logic         ar_valid;
    logic         r_ready;
  } perfc_lt_req_t;

  // PERF COUNTERS LT response
  typedef struct packed {
    logic        aw_ready;
    logic        ar_ready;
    logic        w_ready;
    logic        b_valid;
    perfc_lt_b_t b;
    logic        r_valid;
    perfc_lt_r_t r;
  } perfc_lt_rsp_t;

endpackage
