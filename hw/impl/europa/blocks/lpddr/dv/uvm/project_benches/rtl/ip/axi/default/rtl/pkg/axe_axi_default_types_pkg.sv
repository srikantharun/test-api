// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Default example struct types
///
package axe_axi_default_types_pkg;
  //////////////////////////////////////////////////////////////
  // Example typedefs for each channel to be used as defaults //
  // Use these as reference when defining your own            //
  //////////////////////////////////////////////////////////////

  parameter int unsigned WIDTH_ID_4     = 4;
  parameter int unsigned WIDTH_ID_5     = 5;

  parameter int unsigned WIDTH_ADDR_40  = 40;
  parameter int unsigned WIDTH_ADDR_64  = 64;

  parameter int unsigned WIDTH_DATA_64  = 64;
  parameter int unsigned WIDTH_STRB_64  = WIDTH_DATA_64  / 8;
  parameter int unsigned WIDTH_DATA_512 = 512;
  parameter int unsigned WIDTH_STRB_512 = WIDTH_DATA_512 / 8;

  parameter int unsigned WIDTH_USER_4   = 4;

  parameter int unsigned NUM_PORTS      = 2;

  typedef logic [WIDTH_ID_4     -1:0] axi_id_4_t;
  typedef logic [WIDTH_ID_5     -1:0] axi_id_5_t;
  typedef logic [WIDTH_ADDR_40  -1:0] axi_addr_40_t;
  typedef logic [WIDTH_ADDR_64  -1:0] axi_addr_64_t;
  typedef logic [WIDTH_DATA_64  -1:0] axi_data_64_t;
  typedef logic [WIDTH_STRB_64  -1:0] axi_strb_64_t;
  typedef logic [WIDTH_DATA_512 -1:0] axi_data_512_t;
  typedef logic [WIDTH_STRB_512 -1:0] axi_strb_512_t;
  typedef logic [WIDTH_USER_4   -1:0] axi_user_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_addr_40_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_pkg::axi_atop_t   atop;
    axi_user_4_t          user;
  } axi_aw_4_40_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_addr_64_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_pkg::axi_atop_t   atop;
    axi_user_4_t          user;
  } axi_aw_4_64_4_t;

  typedef struct packed {
    axi_id_5_t            id;
    axi_addr_40_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_pkg::axi_atop_t   atop;
    axi_user_4_t          user;
  } axi_aw_5_40_4_t;

  typedef struct packed {
    axi_data_64_t         data;
    axi_strb_64_t         strb;
    logic                 last;
    axi_user_4_t          user;
  } axi_w_64_8_4_t;

  typedef struct packed {
    axi_data_512_t        data;
    axi_strb_512_t        strb;
    logic                 last;
    axi_user_4_t          user;
  } axi_w_512_64_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_pkg::axi_resp_e   resp;
    axi_user_4_t          user;
  } axi_b_4_4_t;

  typedef struct packed {
    axi_id_5_t            id;
    axi_pkg::axi_resp_e   resp;
    axi_user_4_t          user;
  } axi_b_5_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_addr_40_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_user_4_t          user;
  } axi_ar_4_40_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_addr_64_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_user_4_t          user;
  } axi_ar_4_64_4_t;

  typedef struct packed {
    axi_id_5_t            id;
    axi_addr_40_t         addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_e   size;
    axi_pkg::axi_burst_e  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_user_4_t          user;
  } axi_ar_5_40_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_data_64_t         data;
    axi_pkg::axi_resp_e   resp;
    logic                 last;
    axi_user_4_t          user;
  } axi_r_4_64_4_t;

  typedef struct packed {
    axi_id_5_t            id;
    axi_data_64_t         data;
    axi_pkg::axi_resp_e   resp;
    logic                 last;
    axi_user_4_t          user;
  } axi_r_5_64_4_t;

  typedef struct packed {
    axi_id_4_t            id;
    axi_data_512_t        data;
    axi_pkg::axi_resp_e   resp;
    logic                 last;
    axi_user_4_t          user;
  } axi_r_4_512_4_t;

  typedef struct packed {
    axi_id_5_t            id;
    axi_data_512_t        data;
    axi_pkg::axi_resp_e   resp;
    logic                 last;
    axi_user_4_t          user;
  } axi_r_5_512_4_t;

  /////////////////////////
  // Legacy nested types //
  /////////////////////////

  typedef struct packed {
    axi_aw_4_40_4_t aw;
    logic           aw_valid;
    axi_w_64_8_4_t  w;
    logic           w_valid;
    logic           b_ready;
    axi_ar_4_40_4_t ar;
    logic           ar_valid;
    logic           r_ready;
  } axi_req_4_40_64_4_t;

  typedef struct packed {
    logic           aw_ready;
    logic           w_ready;
    axi_b_4_4_t     b;
    logic           b_valid;
    logic           ar_ready;
    axi_r_4_64_4_t  r;
    logic           r_valid;
  } axi_rsp_4_40_64_4_t;

    typedef struct packed {
    axi_aw_5_40_4_t aw;
    logic           aw_valid;
    axi_w_64_8_4_t  w;
    logic           w_valid;
    logic           b_ready;
    axi_ar_5_40_4_t ar;
    logic           ar_valid;
    logic           r_ready;
  } axi_req_5_40_64_4_t;

  typedef struct packed {
    logic           aw_ready;
    logic           w_ready;
    axi_b_5_4_t     b;
    logic           b_valid;
    logic           ar_ready;
    axi_r_5_64_4_t  r;
    logic           r_valid;
  } axi_rsp_5_40_64_4_t;

  typedef struct packed {
    axi_aw_4_40_4_t aw;
    logic           aw_valid;
    axi_w_512_64_4_t  w;
    logic           w_valid;
    logic           b_ready;
    axi_ar_4_40_4_t ar;
    logic           ar_valid;
    logic           r_ready;
  } axi_req_4_40_512_4_t;

  typedef struct packed {
    logic           aw_ready;
    logic           w_ready;
    axi_b_4_4_t     b;
    logic           b_valid;
    logic           ar_ready;
    axi_r_4_512_4_t  r;
    logic           r_valid;
  } axi_rsp_4_40_512_4_t;


  ////////////////////////
  // Example rule types //
  ////////////////////////

  /// This is meant as a placeholder to have a specified width for the address rules
  /// 16 bit should be more than enough to uniqiely index and demux port.
  parameter int unsigned RuleIndexWidth = cc_math_pkg::index_width(NUM_PORTS);
  typedef logic[RuleIndexWidth-1:0] port_idx_t;

  /// Commonly used rule types for `axi_xbar` (64-bit addresses).
  typedef struct packed {
    port_idx_t   index;
    logic [63:0] addr_start;
    logic [63:0] addr_end;
  } xbar_rule_64_t;

  /// Commonly used rule types for `axi_xbar` (40-bit addresses).
  typedef struct packed {
    port_idx_t    index;
    axi_addr_40_t addr_start;
    axi_addr_40_t addr_end;
  } xbar_rule_40_t;

  /// Commonly used rule types for `axi_xbar` (32-bit addresses).
  typedef struct packed {
    port_idx_t   index;
    logic [31:0] addr_start;
    logic [31:0] addr_end;
  } xbar_rule_32_t;

  /////////////////////////////////////////
  // Example entry_trule for axe_axi_atu //
  /////////////////////////////////////////

  parameter int unsigned AtuNumEntries     = 2;
  parameter int unsigned AtuPageOffsetSize = 12;

  typedef logic [(WIDTH_ADDR_64-AtuPageOffsetSize)-1:0] atu_entry_addr_t;

  /// Translation lookup result (Derived internally in axe_axi_atu!)
  typedef struct packed {
    logic         hit;
    axi_addr_40_t addr;
  } atu_result_t;

  // entry expects this struct
  typedef struct packed {
    // First page number of the input range of the tlb entry
    atu_entry_addr_t first;
    // Last page number of the input range of the tlb entry
    atu_entry_addr_t last;
    // Number of output base page of the tlb entry
    atu_entry_addr_t base;
    // "Whether tlb entry is valid and should be mapped
    logic            valid;
    // Whether tlb entry maps to a read-only range
    logic            read_only;
  } atu_entry_t;


endpackage
