// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Tiago Campos <tiago.campos@axelera.ai>

/// Implementation wrapper for ai_core_cva6v
///
module ai_core_cva6v
  import aic_cva6v_pkg::*;     // Europa implementation package
  import cva6v_ai_core_pkg::*; // Vendor package
  import axi_pkg::*;
  import axe_tcl_sram_pkg::*;
  import raptor_pkg::*;
(
  input  wire                  i_clk,
  input  wire                  i_rst_n,
  // Config
  input  aic_cva6v_xwidth_t    i_boot_addr,
  input  aic_cva6v_xwidth_t    i_hart_id,
  // Memory regions
  input  aic_cva6v_paddr_t     i_memreg_0_addr,
  input  aic_cva6v_psize_t     i_memreg_0_size,
  input  logic                 i_memreg_0_tcdm,
  input  aic_cva6v_paddr_t     i_memreg_1_addr,
  input  aic_cva6v_psize_t     i_memreg_1_size,
  input  logic                 i_memreg_1_tcdm,
  // Interrupt inputs
  input  logic [       2 -1:0] i_irq,
  input  logic                 i_ipi,
  input  logic                 i_time_irq,
  input  aic_cva6v_platf_irq_t i_platform_irq,
  // Debug
  input  logic                 i_debug_req,
  input  logic                 i_debug_rst_halt_req,
  output logic                 o_debug_stop_time,
  // Hart status
  output logic                 o_hart_is_wfi,
  output logic                 o_hart_unavail,
  output logic                 o_hart_under_reset,
  // Memory side, AXI Manager
  // AW
  output logic                 o_axi_m_awvalid,
  input  logic                 i_axi_m_awready,
  output aic_cva6v_axi_id_t    o_axi_m_awid,
  output aic_cva6v_axi_addr_t  o_axi_m_awaddr,
  output axi_len_t             o_axi_m_awlen,
  output axi_size_t            o_axi_m_awsize,
  output axi_burst_t           o_axi_m_awburst,
  output logic                 o_axi_m_awlock,
  output axi_cache_t           o_axi_m_awcache,
  output axi_prot_t            o_axi_m_awprot,
  output axi_qos_t             o_axi_m_awqos,
  output axi_region_t          o_axi_m_awregion,
  output axi_atop_t            o_axi_m_awatop,
  output aic_cva6v_axi_user_t  o_axi_m_awuser,
  // W
  output logic                 o_axi_m_wvalid,
  input  logic                 i_axi_m_wready,
  output aic_cva6v_axi_data_t  o_axi_m_wdata,
  output aic_cva6v_axi_strb_t  o_axi_m_wstrb,
  output logic                 o_axi_m_wlast,
  output aic_cva6v_axi_user_t  o_axi_m_wuser,
  // AR
  output logic                 o_axi_m_arvalid,
  input  logic                 i_axi_m_arready,
  output aic_cva6v_axi_id_t    o_axi_m_arid,
  output aic_cva6v_axi_addr_t  o_axi_m_araddr,
  output axi_len_t             o_axi_m_arlen,
  output axi_size_t            o_axi_m_arsize,
  output axi_burst_t           o_axi_m_arburst,
  output logic                 o_axi_m_arlock,
  output axi_cache_t           o_axi_m_arcache,
  output axi_prot_t            o_axi_m_arprot,
  output axi_qos_t             o_axi_m_arqos,
  output axi_region_t          o_axi_m_arregion,
  output aic_cva6v_axi_user_t  o_axi_m_aruser,
  // B
  input  logic                 i_axi_m_bvalid,
  output logic                 o_axi_m_bready,
  input  aic_cva6v_axi_id_t    i_axi_m_bid,
  input  axi_resp_t            i_axi_m_bresp,
  input  aic_cva6v_axi_user_t  i_axi_m_buser,
  // R
  input  logic                 i_axi_m_rvalid,
  output logic                 o_axi_m_rready,
  input  aic_cva6v_axi_id_t    i_axi_m_rid,
  input  aic_cva6v_axi_data_t  i_axi_m_rdata,
  input  axi_resp_t            i_axi_m_rresp,
  input  logic                 i_axi_m_rlast,
  input  aic_cva6v_axi_user_t  i_axi_m_ruser,
  // Raptor memory ports
  output logic                 o_mem_req_0_valid,
  input  logic                 i_mem_req_0_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_0_addr,
  output logic                 o_mem_req_0_we,
  output aic_cva6v_mem_be_t    o_mem_req_0_be,
  output aic_cva6v_mem_data_t  o_mem_req_0_wdata,
  input  logic                 i_mem_res_0_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_0_rdata,
  input  logic                 i_mem_res_0_err,
  output logic                 o_mem_req_1_valid,
  input  logic                 i_mem_req_1_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_1_addr,
  output logic                 o_mem_req_1_we,
  output aic_cva6v_mem_be_t    o_mem_req_1_be,
  output aic_cva6v_mem_data_t  o_mem_req_1_wdata,
  input  logic                 i_mem_res_1_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_1_rdata,
  input  logic                 i_mem_res_1_err,
  output logic                 o_mem_req_2_valid,
  input  logic                 i_mem_req_2_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_2_addr,
  output logic                 o_mem_req_2_we,
  output aic_cva6v_mem_be_t    o_mem_req_2_be,
  output aic_cva6v_mem_data_t  o_mem_req_2_wdata,
  input  logic                 i_mem_res_2_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_2_rdata,
  input  logic                 i_mem_res_2_err,
  output logic                 o_mem_req_3_valid,
  input  logic                 i_mem_req_3_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_3_addr,
  output logic                 o_mem_req_3_we,
  output aic_cva6v_mem_be_t    o_mem_req_3_be,
  output aic_cva6v_mem_data_t  o_mem_req_3_wdata,
  input  logic                 i_mem_res_3_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_3_rdata,
  input  logic                 i_mem_res_3_err,
  output logic                 o_mem_req_4_valid,
  input  logic                 i_mem_req_4_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_4_addr,
  output logic                 o_mem_req_4_we,
  output aic_cva6v_mem_be_t    o_mem_req_4_be,
  output aic_cva6v_mem_data_t  o_mem_req_4_wdata,
  input  logic                 i_mem_res_4_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_4_rdata,
  input  logic                 i_mem_res_4_err,
  output logic                 o_mem_req_5_valid,
  input  logic                 i_mem_req_5_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_5_addr,
  output logic                 o_mem_req_5_we,
  output aic_cva6v_mem_be_t    o_mem_req_5_be,
  output aic_cva6v_mem_data_t  o_mem_req_5_wdata,
  input  logic                 i_mem_res_5_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_5_rdata,
  input  logic                 i_mem_res_5_err,
  output logic                 o_mem_req_6_valid,
  input  logic                 i_mem_req_6_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_6_addr,
  output logic                 o_mem_req_6_we,
  output aic_cva6v_mem_be_t    o_mem_req_6_be,
  output aic_cva6v_mem_data_t  o_mem_req_6_wdata,
  input  logic                 i_mem_res_6_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_6_rdata,
  input  logic                 i_mem_res_6_err,
  output logic                 o_mem_req_7_valid,
  input  logic                 i_mem_req_7_ready,
  output aic_cva6v_mem_addr_t  o_mem_req_7_addr,
  output logic                 o_mem_req_7_we,
  output aic_cva6v_mem_be_t    o_mem_req_7_be,
  output aic_cva6v_mem_data_t  o_mem_req_7_wdata,
  input  logic                 i_mem_res_7_valid,
  input  aic_cva6v_mem_data_t  i_mem_res_7_rdata,
  input  logic                 i_mem_res_7_err,
  // Raptor performance counter signals
  output aic_cva6v_fu_status_t o_perf_cntr_fu_0_status,
  output aic_cva6v_fu_status_t o_perf_cntr_fu_1_status,
  output aic_cva6v_fu_status_t o_perf_cntr_fu_2_status,
  output logic                 o_perf_cntr_dispatch_queue_full,
  output logic                 o_perf_cntr_dispatch_queue_empty,
  output logic                 o_perf_cntr_commit_queue_full,
  output logic                 o_perf_cntr_commit_queue_empty,
  // Performance events
  output aic_cva6v_perf_addr_t        o_perf_event_0_addr,
  output aic_cva6v_perf_delta_t       o_perf_event_0_0_delta,
  output aic_cva6v_perf_delta_t       o_perf_event_0_1_delta,
  output aic_cva6v_perf_addr_t        o_perf_event_1_addr,
  output aic_cva6v_perf_delta_t       o_perf_event_1_0_delta,
  output aic_cva6v_perf_delta_t       o_perf_event_1_1_delta,
  output aic_cva6v_perf_raptor_addr_t o_perf_event_2_addr,
  output aic_cva6v_perf_delta_t       o_perf_event_2_0_delta,
  output aic_cva6v_perf_delta_t       o_perf_event_2_1_delta,
  // SRAM configuration
  input  impl_inp_t            i_mem_impl,
  output impl_oup_t            o_mem_impl
);

  //////////////////
  // Ports Concat //
  //////////////////

  ///////////////////
  // Memory Regions

  logic [MemRegionCount-1:0][CVA6Cfg.PLEN   -1:0] memreg_addr;
  logic [MemRegionCount-1:0][PAddrSizeWidth -1:0] memreg_size;
  logic [MemRegionCount-1:0]                      memreg_tcdm;

  // Region base address and sizes
  assign memreg_addr[0] = i_memreg_0_addr;
  assign memreg_size[0] = i_memreg_0_size;
  assign memreg_tcdm[0] = i_memreg_0_tcdm;
  assign memreg_addr[1] = i_memreg_1_addr;
  assign memreg_size[1] = i_memreg_1_size;
  assign memreg_tcdm[1] = i_memreg_1_tcdm;

  ////////
  // AXI

  axi_req_t axi_req;
  axi_rsp_t axi_resp;

  // Request
  assign o_axi_m_awvalid  = axi_req.aw_valid;
  assign o_axi_m_awid     = axi_req.aw.id;
  assign o_axi_m_awaddr   = axi_req.aw.addr;
  assign o_axi_m_awlen    = axi_req.aw.len;
  assign o_axi_m_awsize   = axi_req.aw.size;
  assign o_axi_m_awburst  = axi_req.aw.burst;
  assign o_axi_m_awlock   = axi_req.aw.lock;
  assign o_axi_m_awcache  = axi_req.aw.cache;
  assign o_axi_m_awprot   = axi_req.aw.prot;
  assign o_axi_m_awqos    = axi_req.aw.qos;
  assign o_axi_m_awregion = axi_req.aw.region;
  assign o_axi_m_awatop   = axi_req.aw.atop;
  assign o_axi_m_awuser   = axi_req.aw.user;
  assign o_axi_m_wvalid   = axi_req.w_valid;
  assign o_axi_m_wdata    = axi_req.w.data;
  assign o_axi_m_wstrb    = axi_req.w.strb;
  assign o_axi_m_wlast    = axi_req.w.last;
  assign o_axi_m_wuser    = axi_req.w.user;
  assign o_axi_m_bready   = axi_req.b_ready;
  assign o_axi_m_arvalid  = axi_req.ar_valid;
  assign o_axi_m_arid     = axi_req.ar.id;
  assign o_axi_m_araddr   = axi_req.ar.addr;
  assign o_axi_m_arlen    = axi_req.ar.len;
  assign o_axi_m_arsize   = axi_req.ar.size;
  assign o_axi_m_arburst  = axi_req.ar.burst;
  assign o_axi_m_arlock   = axi_req.ar.lock;
  assign o_axi_m_arcache  = axi_req.ar.cache;
  assign o_axi_m_arprot   = axi_req.ar.prot;
  assign o_axi_m_arqos    = axi_req.ar.qos;
  assign o_axi_m_arregion = axi_req.ar.region;
  assign o_axi_m_aruser   = axi_req.ar.user;
  assign o_axi_m_rready   = axi_req.r_ready;

  // Response
  assign axi_resp.aw_ready = i_axi_m_awready;
  assign axi_resp.ar_ready = i_axi_m_arready;
  assign axi_resp.w_ready  = i_axi_m_wready;
  assign axi_resp.b_valid  = i_axi_m_bvalid;
  assign axi_resp.b.id     = i_axi_m_bid;
  assign axi_resp.b.resp   = i_axi_m_bresp;
  assign axi_resp.b.user   = i_axi_m_buser;
  assign axi_resp.r_valid  = i_axi_m_rvalid;
  assign axi_resp.r.id     = i_axi_m_rid;
  assign axi_resp.r.data   = i_axi_m_rdata;
  assign axi_resp.r.resp   = i_axi_m_rresp;
  assign axi_resp.r.last   = i_axi_m_rlast;
  assign axi_resp.r.user   = i_axi_m_ruser;

  ////////////////////////
  // Raptor Memory Ports

  logic [MemPortCount-1:0]                       mem_req_valid;
  logic [MemPortCount-1:0]                       mem_req_ready;
  logic [MemPortCount-1:0][MemPortAddrWidth-1:0] mem_req_addr;
  logic [MemPortCount-1:0]                       mem_req_we;
  logic [MemPortCount-1:0][MemPortBeWidth  -1:0] mem_req_be;
  logic [MemPortCount-1:0][MemPortWidth    -1:0] mem_req_wdata;
  logic [MemPortCount-1:0]                       mem_res_valid;
  logic [MemPortCount-1:0][MemPortWidth    -1:0] mem_res_rdata;
  logic [MemPortCount-1:0]                       mem_res_err;

  // Request
  assign o_mem_req_0_valid = mem_req_valid[0];
  assign o_mem_req_0_addr  = mem_req_addr [0];
  assign o_mem_req_0_we    = mem_req_we   [0];
  assign o_mem_req_0_be    = mem_req_be   [0];
  assign o_mem_req_0_wdata = mem_req_wdata[0];
  assign o_mem_req_1_valid = mem_req_valid[1];
  assign o_mem_req_1_addr  = mem_req_addr [1];
  assign o_mem_req_1_we    = mem_req_we   [1];
  assign o_mem_req_1_be    = mem_req_be   [1];
  assign o_mem_req_1_wdata = mem_req_wdata[1];
  assign o_mem_req_2_valid = mem_req_valid[2];
  assign o_mem_req_2_addr  = mem_req_addr [2];
  assign o_mem_req_2_we    = mem_req_we   [2];
  assign o_mem_req_2_be    = mem_req_be   [2];
  assign o_mem_req_2_wdata = mem_req_wdata[2];
  assign o_mem_req_3_valid = mem_req_valid[3];
  assign o_mem_req_3_addr  = mem_req_addr [3];
  assign o_mem_req_3_we    = mem_req_we   [3];
  assign o_mem_req_3_be    = mem_req_be   [3];
  assign o_mem_req_3_wdata = mem_req_wdata[3];
  assign o_mem_req_4_valid = mem_req_valid[4];
  assign o_mem_req_4_addr  = mem_req_addr [4];
  assign o_mem_req_4_we    = mem_req_we   [4];
  assign o_mem_req_4_be    = mem_req_be   [4];
  assign o_mem_req_4_wdata = mem_req_wdata[4];
  assign o_mem_req_5_valid = mem_req_valid[5];
  assign o_mem_req_5_addr  = mem_req_addr [5];
  assign o_mem_req_5_we    = mem_req_we   [5];
  assign o_mem_req_5_be    = mem_req_be   [5];
  assign o_mem_req_5_wdata = mem_req_wdata[5];
  assign o_mem_req_6_valid = mem_req_valid[6];
  assign o_mem_req_6_addr  = mem_req_addr [6];
  assign o_mem_req_6_we    = mem_req_we   [6];
  assign o_mem_req_6_be    = mem_req_be   [6];
  assign o_mem_req_6_wdata = mem_req_wdata[6];
  assign o_mem_req_7_valid = mem_req_valid[7];
  assign o_mem_req_7_addr  = mem_req_addr [7];
  assign o_mem_req_7_we    = mem_req_we   [7];
  assign o_mem_req_7_be    = mem_req_be   [7];
  assign o_mem_req_7_wdata = mem_req_wdata[7];

  // Response
  assign mem_req_ready[0] = i_mem_req_0_ready;
  assign mem_res_valid[0] = i_mem_res_0_valid;
  assign mem_res_rdata[0] = i_mem_res_0_rdata;
  assign mem_res_err  [0] = i_mem_res_0_err;
  assign mem_req_ready[1] = i_mem_req_1_ready;
  assign mem_res_valid[1] = i_mem_res_1_valid;
  assign mem_res_rdata[1] = i_mem_res_1_rdata;
  assign mem_res_err  [1] = i_mem_res_1_err;
  assign mem_req_ready[2] = i_mem_req_2_ready;
  assign mem_res_valid[2] = i_mem_res_2_valid;
  assign mem_res_rdata[2] = i_mem_res_2_rdata;
  assign mem_res_err  [2] = i_mem_res_2_err;
  assign mem_req_ready[3] = i_mem_req_3_ready;
  assign mem_res_valid[3] = i_mem_res_3_valid;
  assign mem_res_rdata[3] = i_mem_res_3_rdata;
  assign mem_res_err  [3] = i_mem_res_3_err;
  assign mem_req_ready[4] = i_mem_req_4_ready;
  assign mem_res_valid[4] = i_mem_res_4_valid;
  assign mem_res_rdata[4] = i_mem_res_4_rdata;
  assign mem_res_err  [4] = i_mem_res_4_err;
  assign mem_req_ready[5] = i_mem_req_5_ready;
  assign mem_res_valid[5] = i_mem_res_5_valid;
  assign mem_res_rdata[5] = i_mem_res_5_rdata;
  assign mem_res_err  [5] = i_mem_res_5_err;
  assign mem_req_ready[6] = i_mem_req_6_ready;
  assign mem_res_valid[6] = i_mem_res_6_valid;
  assign mem_res_rdata[6] = i_mem_res_6_rdata;
  assign mem_res_err  [6] = i_mem_res_6_err;
  assign mem_req_ready[7] = i_mem_req_7_ready;
  assign mem_res_valid[7] = i_mem_res_7_valid;
  assign mem_res_rdata[7] = i_mem_res_7_rdata;
  assign mem_res_err  [7] = i_mem_res_7_err;

  /////////////////////////
  // Performance Counters

  raptor_pkg::fu_status_e [raptor_pkg::FunctUnitCount-1:0] perf_cntr_fu_status;

  // Performance counter functional unit status
  assign o_perf_cntr_fu_0_status = perf_cntr_fu_status[0];
  assign o_perf_cntr_fu_1_status = perf_cntr_fu_status[1];
  assign o_perf_cntr_fu_2_status = perf_cntr_fu_status[2];

  // Performance events
  logic [ CVA6Cfg.NrCommitPorts   -1:0]                    [CVA6Cfg.PLEN       -2:0] perf_event_addr_full;
  logic                                                    [PerfEventAddrWidth -1:0] perf_event_addr_last;
  logic [(CVA6Cfg.NrCommitPorts+1)-1:0][PerfEventCount-1:0][PerfEventDeltaWidth-1:0] perf_event_deltas;
  assign o_perf_event_0_addr    = perf_event_addr_full[0];
  assign o_perf_event_0_0_delta = perf_event_deltas   [0][0];
  assign o_perf_event_0_1_delta = perf_event_deltas   [0][1];
  assign o_perf_event_1_addr    = perf_event_addr_full[1];
  assign o_perf_event_1_0_delta = perf_event_deltas   [1][0];
  assign o_perf_event_1_1_delta = perf_event_deltas   [1][1];
  assign o_perf_event_2_addr    = perf_event_addr_last;
  assign o_perf_event_2_0_delta = perf_event_deltas   [2][0];
  assign o_perf_event_2_1_delta = perf_event_deltas   [2][1];

  ///////////////
  // CVA6V IP  //
  ///////////////

  cva6v #(
    .axi_aw_chan_t  ( cva6v_ai_core_pkg::axi_aw_chan_t  ),
    .axi_w_chan_t   ( cva6v_ai_core_pkg::axi_w_chan_t   ),
    .axi_b_chan_t   ( cva6v_ai_core_pkg::axi_b_chan_t   ),
    .axi_ar_chan_t  ( cva6v_ai_core_pkg::axi_ar_chan_t  ),
    .axi_r_chan_t   ( cva6v_ai_core_pkg::axi_r_chan_t   ),
    .axi_req_t      ( cva6v_ai_core_pkg::axi_req_t      ),
    .axi_rsp_t      ( cva6v_ai_core_pkg::axi_rsp_t      ),
    .riscv_etrace_t ( cva6v_ai_core_pkg::riscv_etrace_t ),
    .CVA6VConfig    ( cva6v_ai_core_pkg::CVA6VConfig    ),
    .impl_inp_t     ( axe_tcl_sram_pkg::impl_inp_t      ),
    .impl_oup_t     ( axe_tcl_sram_pkg::impl_oup_t      )
  ) u_cva6v (
    .i_clk                            ( i_clk                            ),
    .i_rst_n                          ( i_rst_n                          ),
    // Config
    .i_boot_addr                      ( i_boot_addr                      ),
    .i_hart_id                        ( i_hart_id                        ),
    // Memory regions
    .i_memreg_addr                    ( memreg_addr                      ),
    .i_memreg_size                    ( memreg_size                      ),
    .i_memreg_tcdm                    ( memreg_tcdm                      ),
    // Interrupt inputs
    .i_irq                            ( i_irq                            ),
    .i_ipi                            ( i_ipi                            ),
    .i_time_irq                       ( i_time_irq                       ),
    .i_platform_irq                   ( i_platform_irq                   ),
    // Debug
    .i_debug_req                      ( i_debug_req                      ),
    .i_debug_rst_halt_req             ( i_debug_rst_halt_req             ),
    .o_debug_stop_time                ( o_debug_stop_time                ),
    // Hart status
    .o_hart_is_wfi                    ( o_hart_is_wfi                    ),
    .o_hart_unavail                   ( o_hart_unavail                   ),
    .o_hart_under_reset               ( o_hart_under_reset               ),
    // Memory side, AXI Master
    .o_axi_req                        ( axi_req                          ),
    .i_axi_resp                       ( axi_resp                         ),
    // Raptor memory ports
    .o_mem_req_valid                  ( mem_req_valid                    ),
    .i_mem_req_ready                  ( mem_req_ready                    ),
    .o_mem_req_addr                   ( mem_req_addr                     ),
    .o_mem_req_we                     ( mem_req_we                       ),
    .o_mem_req_be                     ( mem_req_be                       ),
    .o_mem_req_wdata                  ( mem_req_wdata                    ),
    .i_mem_res_valid                  ( mem_res_valid                    ),
    .i_mem_res_rdata                  ( mem_res_rdata                    ),
    .i_mem_res_err                    ( mem_res_err                      ),
    // Raptor performance counter signals
    .o_perf_cntr_fu_status            ( perf_cntr_fu_status              ),
    .o_perf_cntr_dispatch_queue_full  ( o_perf_cntr_dispatch_queue_full  ),
    .o_perf_cntr_dispatch_queue_empty ( o_perf_cntr_dispatch_queue_empty ),
    .o_perf_cntr_commit_queue_full    ( o_perf_cntr_commit_queue_full    ),
    .o_perf_cntr_commit_queue_empty   ( o_perf_cntr_commit_queue_empty   ),
    // Performance events
    .o_perf_event_addr_full           ( perf_event_addr_full             ),
    .o_perf_event_addr_last           ( perf_event_addr_last             ),
    .o_perf_event_deltas              ( perf_event_deltas                ),
    // CVA6 RISC-V formal interface port
    .o_rvfi_probes                    ( /* Unused */                     ),
    // Raptor tracing signals
    .o_trace_raptor                   ( /* Unused */                     ),
    // RISC-V instruction tracing
    .o_etrace                         ( /* Unused */                     ),
    // SRAM implementation ports.
    .i_impl                           ( i_mem_impl                       ),
    .o_impl                           ( o_mem_impl                       )
  );

endmodule : ai_core_cva6v
