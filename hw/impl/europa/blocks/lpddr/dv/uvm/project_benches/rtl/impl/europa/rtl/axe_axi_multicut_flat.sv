// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Flat Europa specific axi multicut with flattened ports
/// Includes type definitions
module axe_axi_multicut_flat #(
  /// Number of Cuts
  parameter int unsigned NumCuts = 1,
  /// AXI ID Width
  parameter int unsigned AxiIdWidth = 0,
  /// AXI Address Width
  parameter int unsigned AxiAddrWidth = 0,
  /// AXI Data Width
  parameter int unsigned AxiDataWidth = 0,

  /// AXI AW User Width
  parameter int unsigned AxiAwUserWidth = 1,
  /// AXI  W User Width
  parameter int unsigned AxiWUserWidth = 1,
  /// AXI  B User Width
  parameter int unsigned AxiBUserWidth = 1,
  /// AXI AR User Width
  parameter int unsigned AxiArUserWidth = 1,
  /// AXI  R User Width
  parameter int unsigned AxiRUserWidth = 1,

  /// Dependent parameter, Axi Strb width
  localparam int unsigned AxiStbrWidth = AxiDataWidth / 8,
  /// Dependent parameter type
  localparam type axi_id_t   = logic[AxiIdWidth-1:0],
  /// Dependent parameter type
  localparam type axi_addr_t = logic[AxiAddrWidth-1:0],
  /// Dependent parameter type
  localparam type axi_data_t = logic[AxiDataWidth-1:0],
  /// Dependent parameter type
  localparam type axi_strb_t = logic[AxiStbrWidth-1:0],

  /// Dependent parameter type
  localparam type axi_aw_user_t = logic[AxiAwUserWidth-1:0],
  /// Dependent parameter type
  localparam type axi_w_user_t = logic[AxiWUserWidth-1:0],
  /// Dependent parameter type
  localparam type axi_b_user_t = logic[AxiBUserWidth-1:0],
  /// Dependent parameter type
  localparam type axi_ar_user_t = logic[AxiArUserWidth-1:0],
  /// Dependent parameter type
  localparam type axi_r_user_t = logic[AxiRUserWidth-1:0]
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_id_t              i_axi_s_aw_id,
  input  axi_addr_t            i_axi_s_aw_addr,
  input  axi_pkg::axi_len_t    i_axi_s_aw_len,
  input  axi_pkg::axi_size_t   i_axi_s_aw_size,
  input  axi_pkg::axi_burst_t  i_axi_s_aw_burst,
  input  logic                 i_axi_s_aw_lock,
  input  axi_pkg::axi_cache_t  i_axi_s_aw_cache,
  input  axi_pkg::axi_prot_t   i_axi_s_aw_prot,
  input  axi_pkg::axi_qos_t    i_axi_s_aw_qos,
  input  axi_pkg::axi_region_t i_axi_s_aw_region,
  input  axi_aw_user_t         i_axi_s_aw_user,
  input  logic                 i_axi_s_aw_valid,
  output logic                 o_axi_s_aw_ready,

  input  axi_data_t            i_axi_s_w_data,
  input  axi_strb_t            i_axi_s_w_strb,
  input  logic                 i_axi_s_w_last,
  input  axi_w_user_t          i_axi_s_w_user,
  input  logic                 i_axi_s_w_valid,
  output logic                 o_axi_s_w_ready,

  output axi_id_t              o_axi_s_b_id,
  output axi_pkg::axi_resp_t   o_axi_s_b_resp,
  output axi_b_user_t          o_axi_s_b_user,
  output logic                 o_axi_s_b_valid,
  input  logic                 i_axi_s_b_ready,

  input  axi_id_t              i_axi_s_ar_id,
  input  axi_addr_t            i_axi_s_ar_addr,
  input  axi_pkg::axi_len_t    i_axi_s_ar_len,
  input  axi_pkg::axi_size_t   i_axi_s_ar_size,
  input  axi_pkg::axi_burst_t  i_axi_s_ar_burst,
  input  logic                 i_axi_s_ar_lock,
  input  axi_pkg::axi_cache_t  i_axi_s_ar_cache,
  input  axi_pkg::axi_prot_t   i_axi_s_ar_prot,
  input  axi_pkg::axi_qos_t    i_axi_s_ar_qos,
  input  axi_pkg::axi_region_t i_axi_s_ar_region,
  input  axi_ar_user_t         i_axi_s_ar_user,
  input  logic                 i_axi_s_ar_valid,
  output logic                 o_axi_s_ar_ready,

  output axi_id_t              o_axi_s_r_id,
  output axi_data_t            o_axi_s_r_data,
  output axi_pkg::axi_resp_t   o_axi_s_r_resp,
  output logic                 o_axi_s_r_last,
  output axi_r_user_t          o_axi_s_r_user,
  output logic                 o_axi_s_r_valid,
  input  logic                 i_axi_s_r_ready,

  /////////////////////
  // Management Port //
  /////////////////////
  output axi_id_t              o_axi_m_aw_id,
  output axi_addr_t            o_axi_m_aw_addr,
  output axi_pkg::axi_len_t    o_axi_m_aw_len,
  output axi_pkg::axi_size_t   o_axi_m_aw_size,
  output axi_pkg::axi_burst_t  o_axi_m_aw_burst,
  output logic                 o_axi_m_aw_lock,
  output axi_pkg::axi_cache_t  o_axi_m_aw_cache,
  output axi_pkg::axi_prot_t   o_axi_m_aw_prot,
  output axi_pkg::axi_qos_t    o_axi_m_aw_qos,
  output axi_pkg::axi_region_t o_axi_m_aw_region,
  output logic                 o_axi_m_aw_valid,
  output axi_aw_user_t         o_axi_m_aw_user,
  input  logic                 i_axi_m_aw_ready,

  output axi_data_t            o_axi_m_w_data,
  output axi_strb_t            o_axi_m_w_strb,
  output logic                 o_axi_m_w_last,
  output axi_w_user_t          o_axi_m_w_user,
  output logic                 o_axi_m_w_valid,
  input  logic                 i_axi_m_w_ready,

  input  axi_id_t              i_axi_m_b_id,
  input  axi_pkg::axi_resp_t   i_axi_m_b_resp,
  input  axi_b_user_t          i_axi_m_b_user,
  input  logic                 i_axi_m_b_valid,
  output logic                 o_axi_m_b_ready,

  output axi_id_t              o_axi_m_ar_id,
  output axi_addr_t            o_axi_m_ar_addr,
  output axi_pkg::axi_len_t    o_axi_m_ar_len,
  output axi_pkg::axi_size_t   o_axi_m_ar_size,
  output axi_pkg::axi_burst_t  o_axi_m_ar_burst,
  output logic                 o_axi_m_ar_lock,
  output axi_pkg::axi_cache_t  o_axi_m_ar_cache,
  output axi_pkg::axi_prot_t   o_axi_m_ar_prot,
  output axi_pkg::axi_qos_t    o_axi_m_ar_qos,
  output axi_pkg::axi_region_t o_axi_m_ar_region,
  output axi_ar_user_t         o_axi_m_ar_user,
  output logic                 o_axi_m_ar_valid,
  input  logic                 i_axi_m_ar_ready,

  input  axi_id_t              i_axi_m_r_id,
  input  axi_data_t            i_axi_m_r_data,
  input  axi_pkg::axi_resp_t   i_axi_m_r_resp,
  input  logic                 i_axi_m_r_last,
  input  axi_r_user_t          i_axi_m_r_user,
  input  logic                 i_axi_m_r_valid,
  output logic                 o_axi_m_r_ready
);
  ///////////////////////////////
  // Parameters and Sanitation //
  ///////////////////////////////
  if (AxiIdWidth   == 0) $fatal(1, "Parameter: 'AxiIdWidth' Must not be 0;");
  if (AxiAddrWidth == 0) $fatal(1, "Parameter: 'AxiAddrWidth' must not be 0;");
  if (AxiDataWidth == 0) $fatal(1, "Parameter: 'AxiDataWidth' must not be 0;");
  if (AxiDataWidth % 8 != 0) $fatal(1, "Rarameter: 'AxiDataWidth' must be dicisable by 8;");

  typedef struct packed {
    axi_id_t              id;
    axi_addr_t            addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_t   size;
    axi_pkg::axi_burst_t  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_aw_user_t         user;
  } axi_aw_t;

  typedef struct packed {
    axi_data_t            data;
    axi_strb_t            strb;
    logic                 last;
    axi_w_user_t          user;
  } axi_w_t;

    typedef struct packed {
    axi_id_t              id;
    axi_pkg::axi_resp_t   resp;
    axi_b_user_t          user;
  } axi_b_t;

    typedef struct packed {
    axi_id_t              id;
    axi_addr_t            addr;
    axi_pkg::axi_len_t    len;
    axi_pkg::axi_size_t   size;
    axi_pkg::axi_burst_t  burst;
    logic                 lock;
    axi_pkg::axi_cache_t  cache;
    axi_pkg::axi_prot_t   prot;
    axi_pkg::axi_qos_t    qos;
    axi_pkg::axi_region_t region;
    axi_ar_user_t         user;
  } axi_ar_t;

  typedef struct packed {
    axi_id_t              id;
    axi_data_t            data;
    axi_pkg::axi_resp_t   resp;
    logic                 last;
    axi_r_user_t          user;
  } axi_r_t;

  ////////////////////////
  // Signal Definitions //
  ////////////////////////
  axi_aw_t axi_s_aw;
  axi_w_t  axi_s_w;
  axi_b_t  axi_s_b;
  axi_ar_t axi_s_ar;
  axi_r_t  axi_s_r;

  axi_aw_t axi_m_aw;
  axi_w_t  axi_m_w;
  axi_b_t  axi_m_b;
  axi_ar_t axi_m_ar;
  axi_r_t  axi_m_r;

  //////////////////////////////////
  // Subordinate Port Assignments //
  //////////////////////////////////

  always_comb axi_s_aw = '{
    id:     i_axi_s_aw_id,
    addr:   i_axi_s_aw_addr,
    len:    i_axi_s_aw_len,
    size:   i_axi_s_aw_size,
    burst:  i_axi_s_aw_burst,
    lock:   i_axi_s_aw_lock,
    cache:  i_axi_s_aw_cache,
    prot:   i_axi_s_aw_prot,
    qos:    i_axi_s_aw_qos,
    region: i_axi_s_aw_region,
    user:   i_axi_s_aw_user
  };

  always_comb axi_s_w = '{
    data: i_axi_s_w_data,
    strb: i_axi_s_w_strb,
    last: i_axi_s_w_last,
    user: i_axi_s_w_user
  };

  always_comb o_axi_s_b_id   = axi_s_b.id;
  always_comb o_axi_s_b_resp = axi_s_b.resp;
  always_comb o_axi_s_b_user = axi_s_b.user;

  always_comb axi_s_ar = '{
    id:     i_axi_s_ar_id,
    addr:   i_axi_s_ar_addr,
    len:    i_axi_s_ar_len,
    size:   i_axi_s_ar_size,
    burst:  i_axi_s_ar_burst,
    lock:   i_axi_s_ar_lock,
    cache:  i_axi_s_ar_cache,
    prot:   i_axi_s_ar_prot,
    qos:    i_axi_s_ar_qos,
    region: i_axi_s_ar_region,
    user:   i_axi_s_ar_user
  };

  always_comb o_axi_s_r_id   = axi_s_r.id;
  always_comb o_axi_s_r_data = axi_s_r.data;
  always_comb o_axi_s_r_resp = axi_s_r.resp;
  always_comb o_axi_s_r_last = axi_s_r.last;
  always_comb o_axi_s_r_user = axi_s_r.user;

  ///////////////////
  // Cut Instances //
  ///////////////////
  axe_axi_multicut #(
    .NumCuts (NumCuts),
    .axi_aw_t(axi_aw_t),
    .axi_w_t (axi_w_t),
    .axi_b_t (axi_b_t),
    .axi_ar_t(axi_ar_t),
    .axi_r_t (axi_r_t)
  ) u_axe_axi_multicut (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_s_aw),
    .i_axi_s_aw_valid,
    .o_axi_s_aw_ready,
    .i_axi_s_w       (axi_s_w),
    .i_axi_s_w_valid,
    .o_axi_s_w_ready,
    .o_axi_s_b       (axi_s_b),
    .o_axi_s_b_valid,
    .i_axi_s_b_ready,
    .i_axi_s_ar      (axi_s_ar),
    .i_axi_s_ar_valid,
    .o_axi_s_ar_ready,
    .o_axi_s_r       (axi_s_r),
    .o_axi_s_r_valid,
    .i_axi_s_r_ready,
    .o_axi_m_aw      (axi_m_aw),
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    .o_axi_m_w       (axi_m_w),
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    .i_axi_m_b       (axi_m_b),
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,
    .o_axi_m_ar      (axi_m_ar),
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    .i_axi_m_r       (axi_m_r),
    .i_axi_m_r_valid,
    .o_axi_m_r_ready
  );

  //////////////////////////////
  // Manager Port Assignments //
  //////////////////////////////
  always_comb o_axi_m_aw_id     = axi_m_aw.id;
  always_comb o_axi_m_aw_addr   = axi_m_aw.addr;
  always_comb o_axi_m_aw_len    = axi_m_aw.len;
  always_comb o_axi_m_aw_size   = axi_m_aw.size;
  always_comb o_axi_m_aw_burst  = axi_m_aw.burst;
  always_comb o_axi_m_aw_lock   = axi_m_aw.lock;
  always_comb o_axi_m_aw_cache  = axi_m_aw.cache;
  always_comb o_axi_m_aw_prot   = axi_m_aw.prot;
  always_comb o_axi_m_aw_qos    = axi_m_aw.qos;
  always_comb o_axi_m_aw_region = axi_m_aw.region;
  always_comb o_axi_m_aw_user   = axi_m_aw.user;

  always_comb o_axi_m_w_data    =  axi_m_w.data;
  always_comb o_axi_m_w_strb    =  axi_m_w.strb;
  always_comb o_axi_m_w_last    =  axi_m_w.last;
  always_comb o_axi_m_w_user    =  axi_m_w.user;

  always_comb axi_m_b = '{
    id:   i_axi_m_b_id,
    resp: i_axi_m_b_resp,
    user: i_axi_m_b_user
  };

  always_comb o_axi_m_ar_id     = axi_m_ar.id;
  always_comb o_axi_m_ar_addr   = axi_m_ar.addr;
  always_comb o_axi_m_ar_len    = axi_m_ar.len;
  always_comb o_axi_m_ar_size   = axi_m_ar.size;
  always_comb o_axi_m_ar_burst  = axi_m_ar.burst;
  always_comb o_axi_m_ar_lock   = axi_m_ar.lock;
  always_comb o_axi_m_ar_cache  = axi_m_ar.cache;
  always_comb o_axi_m_ar_prot   = axi_m_ar.prot;
  always_comb o_axi_m_ar_qos    = axi_m_ar.qos;
  always_comb o_axi_m_ar_region = axi_m_ar.region;
  always_comb o_axi_m_ar_user = axi_m_ar.user;

  always_comb axi_m_r = '{
    id:   i_axi_m_r_id,
    data: i_axi_m_r_data,
    resp: i_axi_m_r_resp,
    last: i_axi_m_r_last,
    user: i_axi_m_r_user
  };
endmodule
