// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>


///
package sdma_pkg;
    import token_mgr_mapping_sdma_pkg::*;
    // AXI Init - HT
    parameter int unsigned SDMA_AXI_HT_ID_W = 8;
    typedef logic [SDMA_AXI_HT_ID_W-1:0] sdma_axi_ht_id_t;
    // AXI Init - LT
    parameter int unsigned SDMA_AXI_LT_ID_W = 4;
    typedef logic [SDMA_AXI_LT_ID_W-1:0] sdma_axi_lt_id_t;
    // AXI Targ - LT
    parameter int unsigned SDMA_AXI_SYSCFG_ID_W = 4;
    typedef logic [SDMA_AXI_SYSCFG_ID_W-1:0] sdma_axi_syscfg_id_t;

    parameter int unsigned NUM_PORTS = 2;
    parameter int unsigned NUM_CHNLS = 4;
    parameter int unsigned NR_TOK_PROD = 0;
    parameter int unsigned NR_TOK_CONS = 0;
    parameter int unsigned NR_TOP_TOK_PROD = token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.max_num_prod;
    parameter int unsigned NR_TOP_TOK_CONS = token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG.max_num_cons;


    parameter int unsigned SDMA_ADDR_CAP = aipu_addr_map_pkg::SDMA_0_END_ADDR -  aipu_addr_map_pkg::SDMA_0_ST_ADDR + 1;
    parameter int unsigned SDMA_CAPPED_AW = $clog2(SDMA_ADDR_CAP);
    parameter int unsigned SDMA_AXI_ENDPOINTS = 4;

    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_DMA_ST_ADDR  = aipu_addr_map_pkg::SDMA_0_DMA_ST_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_DMA_END_ADDR = aipu_addr_map_pkg::SDMA_0_DMA_END_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_TIMESTAMP_CSR_ST_ADDR  = aipu_addr_map_pkg::SDMA_0_TIMESTAMP_UNIT_CSR_ST_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_TIMESTAMP_CSR_END_ADDR = aipu_addr_map_pkg::SDMA_0_TIMESTAMP_UNIT_CSR_END_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_TIMESTAMP_MEM_ST_ADDR  = aipu_addr_map_pkg::SDMA_0_TIMESTAMP_UNIT_MEM_ST_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_TIMESTAMP_MEM_END_ADDR = aipu_addr_map_pkg::SDMA_0_TIMESTAMP_UNIT_MEM_END_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_TOK_MNGR_ST_ADDR  = aipu_addr_map_pkg::SDMA_0_TOKEN_MANAGER_ST_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_TOK_MNGR_END_ADDR = aipu_addr_map_pkg::SDMA_0_TOKEN_MANAGER_END_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_CSR_ST_ADDR  = aipu_addr_map_pkg::SDMA_0_CSR_ST_ADDR;
    parameter logic [SDMA_CAPPED_AW-1:0] SDMA_CSR_END_ADDR = aipu_addr_map_pkg::SDMA_0_CSR_END_ADDR;

    typedef enum int {
      dma_idx = 'd0,
      ts_idx  = 'd1,
      tok_idx = 'd2,
      csr_idx = 'd3
    } sdma_ep_idx_e;

    parameter longint SDMA_REGION_ST_ADDR[SDMA_AXI_ENDPOINTS] = '{
      dma_idx: SDMA_DMA_ST_ADDR,
      ts_idx : SDMA_TIMESTAMP_CSR_ST_ADDR,
      tok_idx: SDMA_TOK_MNGR_ST_ADDR,
      csr_idx: SDMA_CSR_ST_ADDR
    };
    parameter longint SDMA_REGION_END_ADDR[SDMA_AXI_ENDPOINTS] = '{
      dma_idx: SDMA_DMA_END_ADDR,
      ts_idx : SDMA_TIMESTAMP_MEM_END_ADDR,
      tok_idx: SDMA_TOK_MNGR_END_ADDR,
      csr_idx: SDMA_CSR_END_ADDR
    };
    parameter int SDMA_REGION_IDX[SDMA_AXI_ENDPOINTS] = '{
      dma_idx: dma_idx,
      ts_idx : ts_idx,
      tok_idx: tok_idx,
      csr_idx: csr_idx
    };
    parameter bit SDMA_REGION_PRIV[SDMA_AXI_ENDPOINTS] = '{
      dma_idx: 1'b0,
      ts_idx : 1'b1,
      tok_idx: 1'b0,
      csr_idx: 1'b1
    };
endpackage
