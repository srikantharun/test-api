// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L1 package
// Owner: Spyridoula Koumousi <koumousi.spyridoula@axelera.ai>

`ifndef L1_PKG_SV
`define L1_PKG_SV

package l1_pkg;

  typedef int unsigned uint_t;
  // =======================================
  // Parameter definition
  // =======================================
  // Following parameter uint_ts should be updated only during build time
  // Enable pipelining
  // When pipelining is enabled, a register slice is added before the
  // L1 memory inputs and outputs
  parameter uint_t L1_PIPELINE_ENABLE = 1;
  parameter uint_t L1_EXTRA_RESP_PIPELINE_ENABLE = 1;

  parameter uint_t L1_SUB_BANK_MAX_LATENCY = 5;
  parameter uint_t L1_RESP_LATENCY = L1_SUB_BANK_MAX_LATENCY + 1;

  // Number of requestors
  parameter uint_t DEFAULT_L1_NUM_DMC_WO_REQUESTS = 3;
  parameter uint_t DEFAULT_L1_NUM_DMC_RO_REQUESTS = 7;
  parameter uint_t DEFAULT_L1_NUM_RVV_REQUESTS = 8;

  //parameter uint_t L1_NUM_DMC_REQUESTS = L1_NUM_DMC_WO_REQUESTS + L1_NUM_DMC_RO_REQUESTS;

  // Bank:
  // The number of banks, width, and depth in which the L1 address space is divided
  // Total size is 4MB, divided over 16 banks, each being 512 wide and 4096 deep.
  parameter uint_t DEFAULT_L1_NUM_BANKS = 16;
  parameter uint_t L1_BANK_DATA_WIDTH = 512;
  parameter uint_t L1_BANK_DATA_DEPTH = 4096;

  // Sub-bank:
  // RVV access is 128b, so sub-bank is 128b wide and 4096 deep.
  parameter uint_t L1_SUB_BANK_WIDTH = 128;
  parameter uint_t L1_SUB_BANK_DEPTH = L1_BANK_DATA_DEPTH;
  parameter uint_t L1_SUB_BANKS_PER_BANK = L1_BANK_DATA_WIDTH / L1_SUB_BANK_WIDTH;
  parameter uint_t L1_NR_SUB_BANKS = L1_BANK_DATA_WIDTH / L1_SUB_BANK_WIDTH;

  // Macro:
  // macro selected is 128b wide and 4096 deep.
  parameter uint_t L1_MACRO_DATA_WIDTH = L1_SUB_BANK_WIDTH;
  parameter uint_t L1_MACRO_DATA_DEPTH = 4096;
  parameter        L1_MACRO_TYPE = "HS_RVT";

  ////////////////////////////////////////////////
  // Derived parameter uint_ts, do **not** overwrite!
  parameter uint_t L1_BANK_ADDR_WIDTH = $clog2(L1_BANK_DATA_DEPTH);
  parameter uint_t L1_SUB_BANK_ADDR_WIDTH = $clog2(L1_SUB_BANK_DEPTH);
  parameter uint_t L1_MACRO_ADDR_WIDTH = $clog2(L1_MACRO_DATA_DEPTH);

  parameter uint_t L1_BANK_WBE_WIDTH = (L1_BANK_DATA_WIDTH + 7) / 8;
  parameter uint_t L1_SUB_BANK_WBE_WIDTH = (L1_SUB_BANK_WIDTH + 7) / 8;
  parameter uint_t L1_MACRO_WBE_WIDTH = (L1_MACRO_DATA_WIDTH + 7) / 8;

  // =======================================
  // Type definition
  // =======================================

  // MEM interface request payload
  typedef struct packed {
    logic                               we;
    logic [L1_SUB_BANK_WBE_WIDTH-1:0]   wbe;
    logic [L1_SUB_BANK_WIDTH-1:0]       data;
  } req_payload_t;

  // MEM interface request type
  typedef struct packed {
    req_payload_t payload;
    logic         valid;
  } mem_req_t;

  // MEM interface response type
  typedef struct packed {
    logic [L1_SUB_BANK_WIDTH-1:0] data;
    logic                         valid;
  } mem_rsp_t;

  // daisy chain mapping:
  typedef struct packed {
    int unsigned sb;
    int unsigned mb;
    int unsigned m;
  } mem_map_cfg_t;
  typedef mem_map_cfg_t int_def_daisy_chain_t[L1_NR_SUB_BANKS * DEFAULT_L1_NUM_BANKS * 1];

  function automatic int_def_daisy_chain_t fill_default_l1_daisy_chain_mapping();
    fill_default_l1_daisy_chain_mapping = '{default: 0}; // default

    for (int unsigned sb=0; sb<L1_NR_SUB_BANKS; sb++) begin
      for (int unsigned mb=0; mb<DEFAULT_L1_NUM_BANKS; mb++) begin
        fill_default_l1_daisy_chain_mapping[sb * DEFAULT_L1_NUM_BANKS + mb].sb = sb;
        fill_default_l1_daisy_chain_mapping[sb * DEFAULT_L1_NUM_BANKS + mb].mb = mb;
        fill_default_l1_daisy_chain_mapping[sb * DEFAULT_L1_NUM_BANKS + mb].m  = 0;
      end
    end
  endfunction
  parameter mem_map_cfg_t DEFAULT_L1_DAISY_CHAIN_MAPPING[L1_NR_SUB_BANKS * DEFAULT_L1_NUM_BANKS * 1] = fill_default_l1_daisy_chain_mapping();
endpackage
`endif  //L1_PKG_SV
