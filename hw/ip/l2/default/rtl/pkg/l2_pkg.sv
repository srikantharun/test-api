// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L2 generic package
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef L2_PKG_SV
`define L2_PKG_SV

package l2_pkg;
  import l2_cfg_pkg::*;

  // =======================================================================
  // Derived configuration
  // =======================================================================

  // =======================================
  // Parameter definition
  // =======================================

  typedef int unsigned req_lantecy_arrys [L2_NUM_BANKS];
  function automatic req_lantecy_arrys get_req_bank_latency(
    int unsigned max_latency,
    int unsigned wire_latency[L2_NUM_BANKS]
  );
    int unsigned bank_latency[L2_NUM_BANKS];
    for(int bank = 0; bank < L2_NUM_BANKS; bank++) begin
      bank_latency[bank] = max_latency - 1 - wire_latency[bank];
    end
    return bank_latency;
  endfunction

  function automatic int unsigned get_req_max_wire_latency(
    int unsigned wire_latency[L2_NUM_BANKS]
  );
    int unsigned max_latency = 0;
    for(int bank = 0; bank < L2_NUM_BANKS; bank++) begin
      if (wire_latency[bank] > max_latency)
        max_latency = wire_latency[bank];
    end
    return max_latency;
  endfunction

  typedef int unsigned rsp_latency_arrys [L2_RSP_GROUPS];
  function automatic rsp_latency_arrys get_rsp_group_latency(
    int unsigned max_latency,
    int unsigned group_latency[L2_RSP_GROUPS]
  );
    int unsigned stage_latency[L2_RSP_GROUPS];
    for(int group = 0; group < L2_RSP_GROUPS; group++) begin
      stage_latency[group] = max_latency - 1 - group_latency[group];
    end
    return stage_latency;
  endfunction

  function automatic int unsigned get_rsp_max_stage_latency(
    int unsigned group_latency[L2_RSP_GROUPS]
  );
    int unsigned max_latency = 0;
    for(int group = 0; group < L2_RSP_GROUPS; group++) begin
      if (group_latency[group] > max_latency)
        max_latency = group_latency[group];
    end
    return max_latency;
  endfunction

  parameter int unsigned L2_MEMORY_RESP_LATENCY = L2_REQ_LATENCY + L2_RSP_LATENCY + 1;

  parameter int unsigned L2_REQ_BANK_LATENCY[L2_NUM_BANKS] = get_req_bank_latency(L2_REQ_LATENCY
                                                                                 ,L2_REQ_WIRE_LATENCY);

  parameter int unsigned L2_MAX_WIRE_REQ_LATENCY = get_req_max_wire_latency(L2_REQ_WIRE_LATENCY);

  parameter int unsigned L2_RSP_GROUP_LATENCY[L2_RSP_GROUPS] = get_rsp_group_latency(L2_RSP_LATENCY
                                                                                    ,L2_RSP_STAGE_LATENCY);

  parameter int unsigned L2_MAX_STAGE_RSP_LATENCY = get_rsp_max_stage_latency(L2_RSP_STAGE_LATENCY);


  // L2 AXI configuraton
  // ---------------------
  parameter int unsigned L2_AXI_STRB_WIDTH = L2_AXI_DATA_WIDTH / 8 + (L2_AXI_DATA_WIDTH % 8 != 0);

  // L2 bank instance
  //-------------------
  parameter int unsigned L2_BANK_INDEX_WIDTH = cc_math_pkg::index_width(L2_NUM_BANKS);

  // L2 Tech RAM instance
  //-----------------

  // Number of macro instances depends on the data width
  parameter int unsigned L2_SRAM_WBE_WIDTH = L2_SRAM_DATA_WIDTH / 8
                                           + (L2_SRAM_DATA_WIDTH % 8 != 0);
  parameter int unsigned L2_SRAM_INDEX_WIDTH = cc_math_pkg::index_width(L2_SRAM_DATA_DEPTH);

  // L2 RAM instances
  //-------------------
  parameter int unsigned L2_RAM_ROW_BYTES = L2_AXI_STRB_WIDTH;
  parameter int unsigned L2_RAM_WORD_OFFSET = cc_math_pkg::index_width(L2_RAM_ROW_BYTES);
  parameter int unsigned L2_RAM_INDEX_WIDTH = cc_math_pkg::index_width(L2_NUM_RAMS);

  // =======================================
  // Type definition
  // =======================================

  // L2 AXI interface
  //-------------------
  typedef logic [L2_AXI_DATA_WIDTH-1:0] l2_axi_data_t;
  typedef logic [L2_AXI_STRB_WIDTH-1:0] l2_axi_strb_t;
  typedef logic [L2_AXI_ADDR_WIDTH-1:0] l2_axi_addr_t;
  typedef logic   [L2_AXI_ID_WIDTH-1:0] l2_axi_id_t;

  // L2 mem interface
  //-------------------
  typedef struct packed {
    logic [L2_BANK_INDEX_WIDTH-1:0] bank;
    logic  [L2_RAM_INDEX_WIDTH-1:0] ram;
    logic [L2_SRAM_INDEX_WIDTH-1:0] sram;
    logic  [L2_RAM_WORD_OFFSET-1:0] fixed;
  } l2_mem_addr_t;

  typedef union packed {
    l2_mem_addr_t mem;
    l2_axi_addr_t axi;
  } l2_addr_t;

  // Tech RAM width
  typedef logic[L2_SRAM_DATA_WIDTH-1:0] l2_sram_data_t;
  typedef logic [L2_SRAM_WBE_WIDTH-1:0] l2_sram_strb_t;

  typedef struct packed {
    logic                             en;
    l2_mem_addr_t                     addr;
    l2_sram_strb_t [L2_NUM_SRAMS-1:0] wbe;
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
  } l2_mem_wr_t;

  typedef struct packed {
    logic         en;
    l2_mem_addr_t addr;
  } l2_mem_rd_t;

  typedef struct packed {
    l2_mem_wr_t wr;
    l2_mem_rd_t rd;
  } l2_mem_req_t;

  typedef struct packed {
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
    logic                             wr_rsp;
    logic                             rd_rsp;
  } l2_mem_rsp_t;

  // Bank interface
  //-------------------
  typedef struct packed {
    logic  [L2_RAM_INDEX_WIDTH-1:0] ram;
    logic [L2_SRAM_INDEX_WIDTH-1:0] sram;
  } l2_bank_addr_t;

  typedef struct packed {
    l2_bank_addr_t                    addr;
    logic                             we;
    l2_sram_strb_t [L2_NUM_SRAMS-1:0] wbe;
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
  } l2_bank_t;

  typedef struct packed {
    l2_bank_t bank;
    logic     ce;
  } l2_bank_req_t;

  // RAM interface
  //-------------------
  typedef logic [L2_SRAM_INDEX_WIDTH-1:0] l2_ram_addr_t;

  typedef struct packed {
    l2_ram_addr_t                     addr;
    logic                             we;
    l2_sram_strb_t [L2_NUM_SRAMS-1:0] wbe;
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
  } l2_ram_t;

  typedef struct packed {
    l2_ram_t ram;
    logic    ce;
  } l2_ram_req_t;

  typedef struct packed {
    l2_sram_data_t [L2_NUM_SRAMS-1:0] data;
    logic                             valid;
  } l2_ram_rsp_t;

  // SRAM interface
  //-------------------
  typedef l2_ram_addr_t l2_sram_addr_t;

  typedef struct packed {
    l2_sram_addr_t addr;
    logic          we;
    l2_sram_strb_t wbe;
    l2_sram_data_t data;
  } l2_sram_t;

  typedef struct packed {
    l2_sram_t sram;
    logic     ce;
  } l2_sram_req_t;


endpackage
`endif  //L2_PKG_SV
