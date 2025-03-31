// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Scratchpad top module
// Owner: Joao Martins <joao.martins@axelera.ai>

`ifndef SPM_SV
`define SPM_SV

module spm
  import spm_pkg::*;
  import axe_tcl_sram_pkg::*;
#(
  parameter int unsigned SPM_MEM_SIZE_KB = 128,
  /* Memory banking controls
  *   Total memory maths:
  *     SPM_MEM_SIZE_KB = SPM_MEM_MACRO_DEPTH_K
  *                               * SPM_NB_BANKS
  *                               * SPM_NB_SUB_BANKS
  *                               * SPM_NB_MINI_BANKS
  *                               * SPM_NB_SRAMS_PER_MINI_BANK
  *     Example:
  *     |-----------------|------------------------------------------------------------------------------------------------|
  *     | Macro Depth KB  | Macro Size KB | NB Banks | NB SubBanks | NB MiniBanks | NB SRAM per MiniBank | Total Memory KB |
  *     |-----------------|------------------------------------------------------------------------------------------------|
  *     |        2        |        16     |       2  |    2        |         2    |         2            | 256             |
  *     |        8        |        64     |       1  |    2        |         2    |         2            | 512             |
  *     |        8        |        64     |       4  |    4        |         4    |         4            | 8192            |
  *     |-----------------|------------------------------------------------------------------------------------------------|
  */
  parameter int unsigned SPM_NB_BANKS = 2,
  parameter int unsigned SPM_NB_SUB_BANKS = 2,
  parameter int unsigned SPM_NB_MINI_BANKS = 2,
  parameter int unsigned SPM_NB_SRAMS_PER_MINI_BANK = 2,
  parameter int unsigned SPM_NB_REQ_PIPELINE = 0,
  parameter int unsigned SPM_NB_RSP_PIPELINE = 0,
  /*
  * SRAM macro depth (in KB). Possible values:
  *   2 - Instantiates memory split into SRAM macros of 64b/72b by 2k lines (64KiB)
  *   4 - Instantiates memory split into SRAM macros of 64b/72b by 4k lines (32KiB)
  *   8 - Instantiates memory split into SRAM macros of 64b/72b by 8k lines (16KiB)
  *
  */
  parameter int unsigned SPM_MAX_NUM_WR_OSR = 8,
  parameter int unsigned SPM_MAX_NUM_RD_OSR = 8,
  parameter int unsigned SPM_MEM_MACRO_DEPTH_K = 8,
  parameter int unsigned ECC_PROTECTION_EN = 1,
  parameter int unsigned SPM_DAISY_CHAIN_MAPPING_OVERWRITE_EN = 0,
  parameter spm_mem_map_cfg_t SPM_DAISY_CHAIN_MAPPING[SPM_NB_BANKS * SPM_NB_SUB_BANKS * SPM_NB_MINI_BANKS * SPM_NB_SRAMS_PER_MINI_BANK] =
    '{(SPM_NB_BANKS*SPM_NB_SUB_BANKS*SPM_NB_MINI_BANKS*SPM_NB_SRAMS_PER_MINI_BANK){spm_mem_map_cfg_t'{bank_idx:0, subbank_idx:0, minibank_idx:0, srams_idx:0}}},
  /// Add logic needed to support AXI Atomic accesses (Default: 0 = disabled)
  parameter bit EN_ATOMIC_SUPPORT = 1'b0,
  /// Word width of the widest RISC-V processor that can issue requests to this module.
  /// 32 for RV32; 64 for RV64, where both 32-bit (.W suffix) and 64-bit (.D suffix) AMOs are
  /// supported if `aw_strb` is set correctly.
  parameter int unsigned RISCV_WORD_WIDTH = 64,
  // AXI types
  parameter type spm_axi_data_t = logic [64-1:0],
  parameter type spm_axi_addr_t = logic [32-1:0],
  parameter type spm_axi_strb_t = logic [8-1:0],
  parameter type spm_axi_len_t = axi_pkg::axi_len_t,
  parameter type spm_axi_id_t = logic [4-1:0], // Taken from top sys_spm.pkg
  parameter type spm_axi_size_t = axi_pkg::axi_size_t,
  parameter type spm_axi_burst_t = axi_pkg::axi_burst_t,
  parameter type spm_axi_resp_t = axi_pkg::axi_resp_e, // Default to use the enum
  parameter type spm_axi_cache_t = axi_pkg::axi_cache_t,
  parameter type spm_axi_prot_t = axi_pkg::axi_prot_t,
  parameter type spm_axi_atop_t = axi_pkg::axi_atop_t
) (
  // Clock, positive edge triggered
  input  wire i_clk,
  // Asynchronous reset, active low
  input  wire i_rst_n,

  // AXI write address channel
  input  logic            i_axi_s_awvalid,
  input  spm_axi_addr_t   i_axi_s_awaddr,
  input  spm_axi_id_t     i_axi_s_awid,
  input  spm_axi_len_t    i_axi_s_awlen,
  input  spm_axi_size_t   i_axi_s_awsize,
  input  spm_axi_burst_t  i_axi_s_awburst,
  input  logic            i_axi_s_awlock,
  input  spm_axi_cache_t  i_axi_s_awcache,
  input  spm_axi_prot_t   i_axi_s_awprot,
  output logic            o_axi_s_awready,
  input  spm_axi_atop_t   i_axi_s_awatop,
  // AXI write data channel
  input  logic           i_axi_s_wvalid,
  input  logic           i_axi_s_wlast,
  input  spm_axi_data_t  i_axi_s_wdata,
  input  spm_axi_strb_t  i_axi_s_wstrb,
  output logic           o_axi_s_wready,
  // AXI write response channel
  output logic           o_axi_s_bvalid,
  output spm_axi_id_t    o_axi_s_bid,
  output spm_axi_resp_t  o_axi_s_bresp,
  input  logic           i_axi_s_bready,
  // AXI read address channel
  input  logic            i_axi_s_arvalid,
  input  spm_axi_addr_t   i_axi_s_araddr,
  input  spm_axi_id_t     i_axi_s_arid,
  input  spm_axi_len_t    i_axi_s_arlen,
  input  spm_axi_size_t   i_axi_s_arsize,
  input  spm_axi_burst_t  i_axi_s_arburst,
  input  logic            i_axi_s_arlock,
  input  spm_axi_cache_t  i_axi_s_arcache,
  input  spm_axi_prot_t   i_axi_s_arprot,
  output logic            o_axi_s_arready,
  // AXI read data/response channel
  output logic           o_axi_s_rvalid,
  output logic           o_axi_s_rlast,
  output spm_axi_id_t    o_axi_s_rid,
  output spm_axi_data_t  o_axi_s_rdata,
  output spm_axi_resp_t  o_axi_s_rresp,
  input  logic           i_axi_s_rready,

  // Disable ECC error reporting and in flight correction.
  input  logic              i_scp_ecc_disable,
  // scp_error_status
  output spm_error_status_t o_scp_error_status,
  // Error IRQ signal
  output logic         o_irq,

  // Internal observation signals
  output spm_obs_t     o_spm_obs,

  // RAM Configuration pins
  input  impl_inp_t i_impl,
  output impl_oup_t o_impl
);

  // =====================================================
  // Localparams
  // =====================================================

  // Scratchpad memory parameters
  localparam int unsigned SPM_MEM_SIZE_B = SPM_MEM_SIZE_KB * 1024;
  localparam int unsigned SPM_MEM_MACRO_ADDR_WIDTH = 10 + $clog2(SPM_MEM_MACRO_DEPTH_K);

  // MEM data width depends on whether ECC protection is enabled.
  // Currently only support ECC protection on 64 bits
  localparam int unsigned SPM_MEM_DATA_WIDTH      = ECC_PROTECTION_EN ? 72 : 64;
  localparam int unsigned SPM_MEM_BYTE_OFFSET     = ECC_PROTECTION_EN ? $clog2((SPM_MEM_DATA_WIDTH-8) / 8) : $clog2(SPM_MEM_DATA_WIDTH / 8);
  localparam int unsigned SPM_MEM_ADDR_WIDTH      = $clog2(SPM_MEM_SIZE_B) - SPM_MEM_BYTE_OFFSET;
  localparam int unsigned SPM_MEM_WBE_WIDTH       = SPM_MEM_DATA_WIDTH / 8 + (SPM_MEM_DATA_WIDTH % 8 != 0);

  localparam int unsigned AxiIdWidth   = unsigned'($bits(i_axi_s_awid));
  localparam int unsigned AxiAddrWidth = unsigned'($bits(i_axi_s_awaddr));
  localparam int unsigned AxiDataWidth = unsigned'($bits(i_axi_s_wdata));

  typedef struct packed {
    spm_axi_id_t    id;
    spm_axi_addr_t  addr;
    spm_axi_len_t   len;
    spm_axi_size_t  size;
    spm_axi_burst_t burst;
    logic           lock;
    spm_axi_cache_t cache;
    spm_axi_prot_t  prot;
    spm_axi_atop_t  atop;
    logic           user;
  } axi_aw_t;

  typedef struct packed {
    spm_axi_data_t  data;
    spm_axi_strb_t  strb;
    logic           last;
    logic           user;
  } axi_w_t;

  typedef struct packed {
    spm_axi_id_t    id;
    spm_axi_resp_t  resp;
    logic           user;
  } axi_b_t;

  typedef struct packed {
    spm_axi_id_t    id;
    spm_axi_addr_t  addr;
    spm_axi_len_t   len;
    spm_axi_size_t  size;
    spm_axi_burst_t burst;
    logic           lock;
    spm_axi_cache_t cache;
    spm_axi_prot_t  prot;
    logic           user;
  } axi_ar_t;

  typedef struct packed {
    spm_axi_id_t    id;
    spm_axi_data_t  data;
    spm_axi_resp_t  resp;
    logic           last;
    logic           user;
  } axi_r_t;

  // =====================================================
  // Signal declarations
  // =====================================================
  axi_aw_t axi_s_aw;
  logic    axi_s_aw_valid;
  logic    axi_s_aw_ready;
  axi_w_t  axi_s_w;
  logic    axi_s_w_valid;
  logic    axi_s_w_ready;
  axi_b_t  axi_s_b;
  logic    axi_s_b_valid;
  logic    axi_s_b_ready;
  axi_ar_t axi_s_ar;
  logic    axi_s_ar_valid;
  logic    axi_s_ar_ready;
  axi_r_t  axi_s_r;
  logic    axi_s_r_valid;
  logic    axi_s_r_ready;

  logic [SPM_MEM_ADDR_WIDTH-1:0] i_mem_addr;
  logic [SPM_MEM_DATA_WIDTH-1:0] i_mem_wdata;
  logic                          i_mem_req;
  logic                          i_mem_we;
  logic [SPM_MEM_WBE_WIDTH-1:0]  i_mem_be;
  logic [SPM_MEM_DATA_WIDTH-1:0] o_mem_rdata;
  logic                          o_mem_rvalid;

  // =====================================================
  // RTL
  // =====================================================
  if (EN_ATOMIC_SUPPORT) begin : gen_amos
    axi_aw_t axi_amos_aw;
    logic    axi_amos_aw_valid;
    logic    axi_amos_aw_ready;
    axi_w_t  axi_amos_w;
    logic    axi_amos_w_valid;
    logic    axi_amos_w_ready;
    axi_b_t  axi_amos_b;
    logic    axi_amos_b_valid;
    logic    axi_amos_b_ready;
    axi_ar_t axi_amos_ar;
    logic    axi_amos_ar_valid;
    logic    axi_amos_ar_ready;
    axi_r_t  axi_amos_r;
    logic    axi_amos_r_valid;
    logic    axi_amos_r_ready;

    always_comb axi_amos_aw = axi_aw_t'{
      id:    i_axi_s_awid,
      addr:  i_axi_s_awaddr,
      len:   i_axi_s_awlen,
      size:  i_axi_s_awsize,
      burst: i_axi_s_awburst,
      lock:  i_axi_s_awlock,
      cache: i_axi_s_awcache,
      prot:  i_axi_s_awprot,
      atop:  i_axi_s_awatop,
      user:  1'b0
    };
    always_comb   axi_amos_aw_valid = i_axi_s_awvalid;
    always_comb o_axi_s_awready     =   axi_amos_aw_ready;

    always_comb axi_amos_w = axi_w_t'{
      data: i_axi_s_wdata,
      strb: i_axi_s_wstrb,
      last: i_axi_s_wlast,
      user: 1'b0
    };
    always_comb   axi_amos_w_valid = i_axi_s_wvalid;
    always_comb o_axi_s_wready     = axi_amos_w_ready;

    always_comb o_axi_s_bid        =   axi_amos_b.id;
    always_comb o_axi_s_bresp      =   axi_amos_b.resp;
    always_comb o_axi_s_bvalid     =   axi_amos_b_valid;
    always_comb   axi_amos_b_ready = i_axi_s_bready;

    always_comb axi_amos_ar = axi_ar_t'{
      id:    i_axi_s_arid,
      addr:  i_axi_s_araddr,
      len:   i_axi_s_arlen,
      size:  i_axi_s_arsize,
      burst: i_axi_s_arburst,
      lock:  i_axi_s_arlock,
      cache: i_axi_s_arcache,
      prot:  i_axi_s_arprot,
      user: 1'b0
    };
    always_comb   axi_amos_ar_valid = i_axi_s_arvalid;
    always_comb o_axi_s_arready     =   axi_amos_ar_ready;

    always_comb o_axi_s_rid        =   axi_amos_r.id;
    always_comb o_axi_s_rdata      =   axi_amos_r.data;
    always_comb o_axi_s_rresp      =   axi_amos_r.resp;
    always_comb o_axi_s_rlast      =   axi_amos_r.last;
    always_comb o_axi_s_rvalid     =   axi_amos_r_valid;
    always_comb   axi_amos_r_ready = i_axi_s_rready;

  // Atomics Adapter (Amos plus LRSC)
  axe_axi_riscv_atomics #(
    .AxiIdWidth       (AxiIdWidth),
    .AxiAddrWidth     (AxiAddrWidth),
    .AxiDataWidth     (AxiDataWidth),
    .AxiUserWidth     (1),
    .AxiMaxReadTxns   (SPM_MAX_NUM_RD_OSR),
    .AxiMaxWriteTxns  (SPM_MAX_NUM_WR_OSR),
    .RiscvWordWidth   (RISCV_WORD_WIDTH),
    .NumCuts          (1),
    .axi_aw_t         (axi_aw_t),
    .axi_w_t          (axi_w_t),
    .axi_b_t          (axi_b_t),
    .axi_ar_t         (axi_ar_t),
    .axi_r_t          (axi_r_t)
  ) u_axe_axi_riscv_atomics (
    .i_clk            (i_clk),
    .i_rst_n          (i_rst_n),
    .i_axi_s_aw       (axi_amos_aw),
    .i_axi_s_aw_valid (axi_amos_aw_valid),
    .o_axi_s_aw_ready (axi_amos_aw_ready),
    .i_axi_s_w        (axi_amos_w),
    .i_axi_s_w_valid  (axi_amos_w_valid),
    .o_axi_s_w_ready  (axi_amos_w_ready),
    .o_axi_s_b        (axi_amos_b),
    .o_axi_s_b_valid  (axi_amos_b_valid),
    .i_axi_s_b_ready  (axi_amos_b_ready),
    .i_axi_s_ar       (axi_amos_ar),
    .i_axi_s_ar_valid (axi_amos_ar_valid),
    .o_axi_s_ar_ready (axi_amos_ar_ready),
    .o_axi_s_r        (axi_amos_r),
    .o_axi_s_r_valid  (axi_amos_r_valid),
    .i_axi_s_r_ready  (axi_amos_r_ready),
    .o_axi_m_aw       (axi_s_aw),
    .o_axi_m_aw_valid (axi_s_aw_valid),
    .i_axi_m_aw_ready (axi_s_aw_ready),
    .o_axi_m_w        (axi_s_w),
    .o_axi_m_w_valid  (axi_s_w_valid),
    .i_axi_m_w_ready  (axi_s_w_ready),
    .i_axi_m_b        (axi_s_b),
    .i_axi_m_b_valid  (axi_s_b_valid),
    .o_axi_m_b_ready  (axi_s_b_ready),
    .o_axi_m_ar       (axi_s_ar),
    .o_axi_m_ar_valid (axi_s_ar_valid),
    .i_axi_m_ar_ready (axi_s_ar_ready),
    .i_axi_m_r        (axi_s_r),
    .i_axi_m_r_valid  (axi_s_r_valid),
    .o_axi_m_r_ready  (axi_s_r_ready)
  );

  end else begin : gen_conn
    always_comb axi_s_aw = axi_aw_t'{
      id:    i_axi_s_awid,
      addr:  i_axi_s_awaddr,
      len:   i_axi_s_awlen,
      size:  i_axi_s_awsize,
      burst: i_axi_s_awburst,
      lock:  i_axi_s_awlock,
      cache: i_axi_s_awcache,
      prot:  i_axi_s_awprot,
      atop:  i_axi_s_awatop,
      user:  1'b0
    };
    always_comb   axi_s_aw_valid = i_axi_s_awvalid;
    always_comb o_axi_s_awready  =   axi_s_aw_ready;

    always_comb axi_s_w = axi_w_t'{
      data: i_axi_s_wdata,
      strb: i_axi_s_wstrb,
      last: i_axi_s_wlast,
      user: 1'b0
    };
    always_comb   axi_s_w_valid = i_axi_s_wvalid;
    always_comb o_axi_s_wready  =   axi_s_w_ready;

    always_comb o_axi_s_bid     =   axi_s_b.id;
    always_comb o_axi_s_bresp   =   axi_s_b.resp;
    always_comb o_axi_s_bvalid  =   axi_s_b_valid;
    always_comb   axi_s_b_ready = i_axi_s_bready;

    always_comb axi_s_ar = axi_ar_t'{
      id:    i_axi_s_arid,
      addr:  i_axi_s_araddr,
      len:   i_axi_s_arlen,
      size:  i_axi_s_arsize,
      burst: i_axi_s_arburst,
      lock:  i_axi_s_arlock,
      cache: i_axi_s_arcache,
      prot:  i_axi_s_arprot,
      user: 1'b0
    };
    always_comb   axi_s_ar_valid = i_axi_s_arvalid;
    always_comb o_axi_s_arready  =   axi_s_ar_ready;

    always_comb o_axi_s_rid     =   axi_s_r.id;
    always_comb o_axi_s_rdata   =   axi_s_r.data;
    always_comb o_axi_s_rresp   =   axi_s_r.resp;
    always_comb o_axi_s_rlast   =   axi_s_r.last;
    always_comb o_axi_s_rvalid  =   axi_s_r_valid;
    always_comb   axi_s_r_ready = i_axi_s_rready;
  end

  // AXI to memory bridge
  spm_control #(
   .SPM_MEM_SIZE_KB     (SPM_MEM_SIZE_KB),
   .SPM_MEM_WBE_WIDTH   (SPM_MEM_WBE_WIDTH),
   .SPM_MEM_ADDR_WIDTH  (SPM_MEM_ADDR_WIDTH),
   .SPM_MEM_DATA_WIDTH  (SPM_MEM_DATA_WIDTH),
   .ECC_PROTECTION_EN   (ECC_PROTECTION_EN),
   .OOR_ERR_EN          (OOR_ERR_EN),
   .SPM_NB_REQ_PIPELINE (SPM_NB_REQ_PIPELINE),
   .SPM_NB_RSP_PIPELINE (SPM_NB_RSP_PIPELINE),
   .SPM_MAX_NUM_WR_OSR  (SPM_MAX_NUM_WR_OSR),
   .SPM_MAX_NUM_RD_OSR  (SPM_MAX_NUM_RD_OSR),
   .spm_axi_data_t (spm_axi_data_t ),
   .spm_axi_addr_t (spm_axi_addr_t ),
   .spm_axi_strb_t (spm_axi_strb_t ),
   .spm_axi_len_t  (spm_axi_len_t  ),
   .spm_axi_id_t   (spm_axi_id_t   ),
   .spm_axi_size_t (spm_axi_size_t ),
   .spm_axi_burst_t(spm_axi_burst_t),
   .spm_axi_resp_t (spm_axi_resp_t ),
   .spm_axi_cache_t(spm_axi_cache_t),
   .spm_axi_prot_t (spm_axi_prot_t )
  ) u_spm_control (
    .i_clk           (i_clk),
    .i_rst_n         (i_rst_n),
    // AXI Interface
    .i_axi_s_awvalid (axi_s_aw_valid),
    .i_axi_s_awaddr  (axi_s_aw.addr),
    .i_axi_s_awid    (axi_s_aw.id),
    .i_axi_s_awlen   (axi_s_aw.len),
    .i_axi_s_awsize  (axi_s_aw.size),
    .i_axi_s_awburst (axi_s_aw.burst),
    .i_axi_s_awlock  (axi_s_aw.lock),
    .i_axi_s_awcache (axi_s_aw.cache),
    .i_axi_s_awprot  (axi_s_aw.prot),
    .o_axi_s_awready (axi_s_aw_ready),
    .i_axi_s_wvalid  (axi_s_w_valid),
    .i_axi_s_wlast   (axi_s_w.last),
    .i_axi_s_wdata   (axi_s_w.data),
    .i_axi_s_wstrb   (axi_s_w.strb),
    .o_axi_s_wready  (axi_s_w_ready),
    .o_axi_s_bvalid  (axi_s_b_valid),
    .o_axi_s_bid     (axi_s_b.id),
    .o_axi_s_bresp   (axi_s_b.resp),
    .i_axi_s_bready  (axi_s_b_ready),
    .i_axi_s_arvalid (axi_s_ar_valid),
    .i_axi_s_araddr  (axi_s_ar.addr),
    .i_axi_s_arid    (axi_s_ar.id),
    .i_axi_s_arlen   (axi_s_ar.len),
    .i_axi_s_arsize  (axi_s_ar.size),
    .i_axi_s_arburst (axi_s_ar.burst),
    .i_axi_s_arlock  (axi_s_ar.lock),
    .i_axi_s_arcache (axi_s_ar.cache),
    .i_axi_s_arprot  (axi_s_ar.prot),
    .o_axi_s_arready (axi_s_ar_ready),
    .o_axi_s_rvalid  (axi_s_r_valid),
    .o_axi_s_rlast   (axi_s_r.last),
    .o_axi_s_rid     (axi_s_r.id),
    .o_axi_s_rdata   (axi_s_r.data),
    .o_axi_s_rresp   (axi_s_r.resp),
    .i_axi_s_rready  (axi_s_r_ready),
     // Memory i_interface signals
     .o_mem_req  (i_mem_req),
     .o_mem_we   (i_mem_we),
     .o_mem_be   (i_mem_be),
     .o_mem_addr (i_mem_addr),
     .o_mem_wdata(i_mem_wdata),
     .i_mem_rdata(o_mem_rdata),
     .i_mem_rvalid(o_mem_rvalid),
     // ECC
     .o_irq(o_irq),
     .i_scp_ecc_disable (i_scp_ecc_disable),
     .o_scp_error_status(o_scp_error_status),
     // Internal observation
     .o_spm_obs(o_spm_obs)
  );

  // Scatchpad memory
  // - Encapsulating memory into a separate module can lead to slightly cleaner
  // code when splitting it between banks for different parameterisations
  spm_mem #(
    .SPM_NB_REQ_PIPELINE(SPM_NB_REQ_PIPELINE),
    .SPM_NB_RSP_PIPELINE(SPM_NB_RSP_PIPELINE),

    .SPM_NB_BANKS              (SPM_NB_BANKS),
    .SPM_NB_SUB_BANKS          (SPM_NB_SUB_BANKS),
    .SPM_NB_MINI_BANKS         (SPM_NB_MINI_BANKS),
    .SPM_NB_SRAMS_PER_MINI_BANK(SPM_NB_SRAMS_PER_MINI_BANK),

    .SPM_MEM_MACRO_ADDR_WIDTH(SPM_MEM_MACRO_ADDR_WIDTH),
    .SPM_MEM_DATA_WIDTH      (SPM_MEM_DATA_WIDTH),
    .SPM_MEM_ADDR_WIDTH      (SPM_MEM_ADDR_WIDTH),
    .SPM_MEM_WBE_WIDTH       (SPM_MEM_WBE_WIDTH),
    .SPM_DAISY_CHAIN_MAPPING_OVERWRITE_EN(SPM_DAISY_CHAIN_MAPPING_OVERWRITE_EN),
    .SPM_DAISY_CHAIN_MAPPING (SPM_DAISY_CHAIN_MAPPING)
  ) u_spm_mem (
    // Clock signal
    .i_clk   (i_clk),
    .i_rst_n (i_rst_n),
    // RAM interface signals
    .i_req   (i_mem_req),
    .i_we    (i_mem_we),
    .i_be    (i_mem_be),
    .i_addr  (i_mem_addr),
    .i_wdata (i_mem_wdata),
    .o_rdata (o_mem_rdata),
    .o_rvalid(o_mem_rvalid),
    // RAM Configuration pins
    .i_impl  (i_impl),
    .o_impl  (o_impl)
  );

  // Assertions
  //synopsys translate_off
`ifdef ASSERTIONS_ON
  // -- Immediate assertions
  initial begin
    // Assert that the banking configuration leads to expected memory size in KiB
    // - Each SRAM will have 8Bytes * Depth (so an 8k deep SRAM holds 8*8=64KiB)
    a_spm_mem_config: assert( 8*SPM_MEM_MACRO_DEPTH_K *
                                SPM_NB_BANKS *
                                SPM_NB_SUB_BANKS *
                                SPM_NB_MINI_BANKS *
                                SPM_NB_SRAMS_PER_MINI_BANK == SPM_MEM_SIZE_KB)
                      else $error("Expected Memory Size in KiB doesn't match the banking combination");

    a_spm_num_wr_osr_config: assert(SPM_MAX_NUM_WR_OSR >= 8)
                      else $warning("Selected value for SPM_MAX_NUM_WR_OSR is less than the minimum delay throughout SPM IP");

    a_spm_num_rd_osr_config: assert(SPM_MAX_NUM_RD_OSR >= 8)
                      else $warning("Selected value for SPM_MAX_NUM_RD_OSR is less than the minimum delay throughout SPM IP");
  end
`endif  // ASSERTIONS_ON
  //synopsys translate_on
  // verilog_lint: waive-stop line-length

endmodule
`endif // SPM_SV
