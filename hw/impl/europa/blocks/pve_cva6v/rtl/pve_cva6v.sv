// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Implementation wrapper for pve_cva6v
///
module pve_cva6v
  import chip_pkg::*;
  import pve_pkg::*;
  import pve_cva6v_pkg::*; // Europa implementation package
  import axi_pkg::*;
  import axe_tcl_sram_pkg::*;
(
  input  wire                        i_clk,
  input  wire                        i_rst_n,
  // Config
  input  pve_cva6v_xwidth_t          i_boot_addr,
  input  pve_cva6v_xwidth_t          i_hart_id,
  // Memory regions
  input  pve_cva6v_memreg_addr_t     i_memreg_addr,
  input  pve_cva6v_memreg_size_t     i_memreg_size,
  input  pve_cva6v_memreg_tcdm_t     i_memreg_tcdm,
  // Interrupt inputs
  input  logic [            1:0]     i_irq,
  input  logic                       i_ipi,
  input  logic                       i_time_irq,
  input  pve_cva6v_platf_irq_t       i_platform_irq,
  // Debug
  input  logic                       i_debug_req,
  input  logic                       i_debug_rst_halt_req,
  output logic                       o_debug_stop_time,
  // Hart status
  output logic                       o_hart_is_wfi,
  output logic                       o_hart_unavail,
  output logic                       o_hart_under_reset,
  // Memory side, AXI Manager
  // AW
  output logic                       o_axi_m_awvalid,
  output pve_lt_axi_s_id_t           o_axi_m_awid,
  output chip_axi_addr_t             o_axi_m_awaddr,
  output axi_len_t                   o_axi_m_awlen,
  output axi_size_e                  o_axi_m_awsize,
  output axi_burst_e                 o_axi_m_awburst,
  output logic                       o_axi_m_awlock,
  output axi_cache_e                 o_axi_m_awcache,
  output axi_prot_t                  o_axi_m_awprot,
  output axi_atop_t                  o_axi_m_awatop,
  input  logic                       i_axi_m_awready,
  // W
  output logic                       o_axi_m_wvalid,
  output chip_axi_lt_data_t          o_axi_m_wdata,
  output chip_axi_lt_wstrb_t         o_axi_m_wstrb,
  output logic                       o_axi_m_wlast,
  input  logic                       i_axi_m_wready,
  // B
  input  logic                       i_axi_m_bvalid,
  input  pve_lt_axi_s_id_t           i_axi_m_bid,
  input  axi_resp_e                  i_axi_m_bresp,
  output logic                       o_axi_m_bready,
  // AR
  output logic                       o_axi_m_arvalid,
  output pve_lt_axi_s_id_t           o_axi_m_arid,
  output chip_axi_addr_t             o_axi_m_araddr,
  output axi_len_t                   o_axi_m_arlen,
  output axi_size_e                  o_axi_m_arsize,
  output axi_burst_e                 o_axi_m_arburst,
  output logic                       o_axi_m_arlock,
  output axi_cache_e                 o_axi_m_arcache,
  output axi_prot_t                  o_axi_m_arprot,
  input  logic                       i_axi_m_arready,
  // R
  input  logic                       i_axi_m_rvalid,
  input  pve_lt_axi_s_id_t           i_axi_m_rid,
  input  chip_axi_lt_data_t          i_axi_m_rdata,
  input  axi_resp_e                  i_axi_m_rresp,
  input  logic                       i_axi_m_rlast,
  output logic                       o_axi_m_rready,
  // Raptor memory ports
  output pve_cva6v_mem_logic_t       o_mem_req_valid,
  output pve_cva6v_mem_addr_t        o_mem_req_addr,
  output pve_cva6v_mem_logic_t       o_mem_req_we,
  output pve_cva6v_mem_be_t          o_mem_req_be,
  output pve_cva6v_mem_data_t        o_mem_req_wdata,
  input  pve_cva6v_mem_logic_t       i_mem_req_ready,
  input  pve_cva6v_mem_logic_t       i_mem_res_valid,
  input  pve_cva6v_mem_data_t        i_mem_res_rdata,
  input  pve_cva6v_mem_logic_t       i_mem_res_err,
  // Raptor performance counter signals
  output perf_cntr_fu_status_t       o_perf_cntr_fu_status,
  output logic                       o_perf_cntr_dispatch_queue_full,
  output logic                       o_perf_cntr_dispatch_queue_empty,
  output logic                       o_perf_cntr_commit_queue_full,
  output logic                       o_perf_cntr_commit_queue_empty,
  // CVA6V performance event signals
  output pve_cva6v_event_addr_full_t o_perf_event_addr_full,
  output pve_cva6v_event_addr_last_t o_perf_event_addr_last,
  output pve_cva6v_event_deltas_t    o_perf_event_deltas,
  // SRAM configuration
  input  impl_inp_t                  i_mem_impl,
  output impl_oup_t                  o_mem_impl
);

  //////////
  // AXI  //
  //////////

  cva6v_pve_pkg::axi_req_t axi_req;
  cva6v_pve_pkg::axi_rsp_t axi_resp;

  // Request
  assign o_axi_m_awvalid  = axi_req.aw_valid;
  assign o_axi_m_awid     = axi_req.aw.id;
  assign o_axi_m_awaddr   = $unsigned(axi_req.aw.addr);
  assign o_axi_m_awlen    = axi_req.aw.len;
  assign o_axi_m_awsize   = axi_size_e'(axi_req.aw.size);
  assign o_axi_m_awburst  = axi_burst_e'(axi_req.aw.burst);
  assign o_axi_m_awlock   = axi_req.aw.lock;
  assign o_axi_m_awcache  = axi_cache_e'(axi_req.aw.cache);
  assign o_axi_m_awprot   = axi_req.aw.prot;
  assign o_axi_m_awatop   = axi_req.aw.atop;
  assign o_axi_m_wvalid   = axi_req.w_valid;
  assign o_axi_m_wdata    = axi_req.w.data;
  assign o_axi_m_wstrb    = axi_req.w.strb;
  assign o_axi_m_wlast    = axi_req.w.last;
  assign o_axi_m_bready   = axi_req.b_ready;
  assign o_axi_m_arvalid  = axi_req.ar_valid;
  assign o_axi_m_arid     = axi_req.ar.id;
  assign o_axi_m_araddr   = $unsigned(axi_req.ar.addr);
  assign o_axi_m_arlen    = axi_req.ar.len;
  assign o_axi_m_arsize   = axi_size_e'(axi_req.ar.size);
  assign o_axi_m_arburst  = axi_burst_e'(axi_req.ar.burst);
  assign o_axi_m_arlock   = axi_req.ar.lock;
  assign o_axi_m_arcache  = axi_cache_e'(axi_req.ar.cache);
  assign o_axi_m_arprot   = axi_req.ar.prot;
  assign o_axi_m_rready   = axi_req.r_ready;

  // Response
  assign axi_resp.aw_ready = i_axi_m_awready;
  assign axi_resp.w_ready  = i_axi_m_wready;
  assign axi_resp.b_valid  = i_axi_m_bvalid;
  assign axi_resp.b.id     = i_axi_m_bid;
  assign axi_resp.b.resp   = axi_resp_t'(i_axi_m_bresp);
  assign axi_resp.b.user   = '0;
  assign axi_resp.ar_ready = i_axi_m_arready;
  assign axi_resp.r_valid  = i_axi_m_rvalid;
  assign axi_resp.r.id     = i_axi_m_rid;
  assign axi_resp.r.data   = i_axi_m_rdata;
  assign axi_resp.r.resp   = axi_resp_t'(i_axi_m_rresp);
  assign axi_resp.r.last   = i_axi_m_rlast;
  assign axi_resp.r.user   = '0;

  ///////////////
  // CVA6V IP  //
  ///////////////

  cva6v #(
    .axi_aw_chan_t ( cva6v_pve_pkg::axi_aw_chan_t  ),
    .axi_w_chan_t  ( cva6v_pve_pkg::axi_w_chan_t   ),
    .axi_b_chan_t  ( cva6v_pve_pkg::axi_b_chan_t   ),
    .axi_ar_chan_t ( cva6v_pve_pkg::axi_ar_chan_t  ),
    .axi_r_chan_t  ( cva6v_pve_pkg::axi_r_chan_t   ),
    .axi_req_t     ( cva6v_pve_pkg::axi_req_t      ),
    .axi_rsp_t     ( cva6v_pve_pkg::axi_rsp_t      ),
    .riscv_etrace_t( cva6v_pve_pkg::riscv_etrace_t ),
    .CVA6VConfig   ( cva6v_pve_pkg::CVA6VConfig    ),
    .impl_inp_t    ( impl_inp_t                    ),
    .impl_oup_t    ( impl_oup_t                    )
  ) u_cva6v (
    .i_clk,
    .i_rst_n,
    // Config
    .i_boot_addr,
    .i_hart_id,
    // Memory regions
    .i_memreg_addr,
    .i_memreg_size,
    .i_memreg_tcdm,
    // Interrupt inputs
    .i_irq,
    .i_ipi,
    .i_time_irq,
    .i_platform_irq,
    // Debug
    .i_debug_req,
    .i_debug_rst_halt_req,
    .o_debug_stop_time,
    // Hart status
    .o_hart_is_wfi,
    .o_hart_unavail,
    .o_hart_under_reset,
    // Memory side, AXI Master
    .o_axi_req                        ( axi_req  ),
    .i_axi_resp                       ( axi_resp ),
    // Raptor memory ports
    .o_mem_req_valid,
    .o_mem_req_addr,
    .o_mem_req_we,
    .o_mem_req_be,
    .o_mem_req_wdata,
    .i_mem_req_ready,
    .i_mem_res_valid,
    .i_mem_res_rdata,
    .i_mem_res_err,
    // Raptor performance counter signals
    .o_perf_cntr_fu_status,
    .o_perf_cntr_dispatch_queue_full,
    .o_perf_cntr_dispatch_queue_empty,
    .o_perf_cntr_commit_queue_full,
    .o_perf_cntr_commit_queue_empty,
    // CVA6V performance event signals
    .o_perf_event_addr_full,
    .o_perf_event_addr_last,
    .o_perf_event_deltas,
    // CVA6 RISC-V formal interface port
    .o_rvfi_probes                    ( /* Unused */ ),
    // Raptor tracing signals
    .o_trace_raptor                   ( /* Unused */ ),
    // RISC-V instruction tracing
    .o_etrace                         ( /* Unused */ ),
    // SRAM implementation ports.
    .i_impl                           ( i_mem_impl ),
    .o_impl                           ( o_mem_impl )
  );

endmodule : pve_cva6v
