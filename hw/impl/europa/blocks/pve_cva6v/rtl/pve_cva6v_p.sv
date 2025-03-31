// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Implementation wrapper for pve_cva6v
///
module pve_cva6v_p
  import chip_pkg::*;
  import pve_pkg::*;
  import pve_cva6v_pkg::*; // Europa implementation package
  import cva6v_pve_pkg::*; // Vendor package
  import axi_pkg::*;
  import axe_tcl_sram_pkg::*;
(
  input  wire                        i_clk,
  input  wire                        i_rst_n,
  input  logic                       i_clk_en,
  // Config
  input  pve_cva6v_xwidth_t          i_boot_addr,
  input  pve_cva6v_xwidth_t          i_hart_id,
  // Memory regions
  input  pve_cva6v_memreg_addr_1d_t  i_memreg_addr,
  input  pve_cva6v_memreg_size_1d_t  i_memreg_size,
  input  pve_cva6v_memreg_tcdm_t     i_memreg_tcdm,
  // Interrupt inputs
  input  logic [               1:0]  i_irq,
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
  output pve_cva6v_mem_addr_1d_t     o_mem_req_addr,
  output pve_cva6v_mem_logic_t       o_mem_req_we,
  output pve_cva6v_mem_be_1d_t       o_mem_req_be,
  output pve_cva6v_mem_data_1d_t     o_mem_req_wdata,
  input  pve_cva6v_mem_logic_t       i_mem_req_ready,
  input  pve_cva6v_mem_logic_t       i_mem_res_valid,
  input  pve_cva6v_mem_data_1d_t     i_mem_res_rdata,
  input  pve_cva6v_mem_logic_t       i_mem_res_err,
  // Raptor performance counter signals
  output perf_cntr_fu_status_1d_t    o_perf_cntr_fu_status,
  output logic                       o_perf_cntr_dispatch_queue_full,
  output logic                       o_perf_cntr_dispatch_queue_empty,
  output logic                       o_perf_cntr_commit_queue_full,
  output logic                       o_perf_cntr_commit_queue_empty,
  // CVA6V performance event signals
  output pve_cva6v_event_addr_1d_t   o_perf_event_addr,
  output pve_cva6v_event_deltas_1d_t o_perf_event_deltas,
  // JTAG
  input  wire                        ijtag_tck,
  input  wire                        ijtag_reset,
  input  logic                       ijtag_sel,
  input  logic                       ijtag_ue,
  input  logic                       ijtag_se,
  input  logic                       ijtag_ce,
  input  logic                       ijtag_si,
  output logic                       ijtag_so,
  // DFT
  input  wire                        test_clk,
  input  logic                       test_mode,
  input  logic                       edt_update,
  input  logic                       scan_en,
  input  logic [                7:0] scan_in,
  output logic [                7:0] scan_out,
  // BIST
  input  wire                        bisr_clk,
  input  wire                        bisr_reset,
  input  logic                       bisr_shift_en,
  input  logic                       bisr_si,
  output logic                       bisr_so
);

  pve_cva6v_memreg_addr_t     memreg_addr_inp;
  pve_cva6v_memreg_size_t     memreg_size_inp;
  pve_cva6v_mem_addr_t        mem_req_addr_oup;
  pve_cva6v_mem_be_t          mem_req_be_oup;
  pve_cva6v_mem_data_t        mem_req_wdata_oup;
  pve_cva6v_mem_data_t        mem_res_rdata_inp;
  perf_cntr_fu_status_t       perf_cntr_fu_status_oup;
  pve_cva6v_event_addr_full_t perf_event_addr_full_oup;
  pve_cva6v_event_addr_last_t perf_event_addr_last_oup;
  pve_cva6v_event_deltas_t    perf_event_deltas_oup;
  wire                        clk_g;

  for (genvar I = 0; I < MemRegionCount; I++) begin: g_io1
    always_comb memreg_addr_inp[I] = i_memreg_addr[I*PLength+:PLength];
    always_comb memreg_size_inp[I] = i_memreg_size[I*PAddrSizeWidth+:PAddrSizeWidth];
  end
  for (genvar I = 0; I < MemPortCount; I++) begin: g_io2
    always_comb o_mem_req_addr[I*MemPortAddrWidth+:MemPortAddrWidth] = mem_req_addr_oup[I];
    always_comb o_mem_req_be[I*MemPortBeWidth+:MemPortBeWidth]       = mem_req_be_oup[I];
    always_comb o_mem_req_wdata[I*MemPortWidth+:MemPortWidth]        = mem_req_wdata_oup[I];
    always_comb mem_res_rdata_inp[I]                                 = i_mem_res_rdata[I*MemPortWidth+:MemPortWidth];
  end
  for (genvar I = 0; I < raptor_pkg::FunctUnitCount; I++) begin: g_io3
    always_comb o_perf_cntr_fu_status[I*4+:4] = perf_cntr_fu_status_oup[I][3:0];
  end
  for (genvar I = 0; I < EventPortCount-1; I++) begin: g_io4
    always_comb o_perf_event_addr[I*PerfEventAddrWidth+:PerfEventAddrWidth] = perf_event_addr_full_oup[I][PerfEventAddrWidth-1:0];
  end
  always_comb o_perf_event_addr[(EventPortCount-1)*PerfEventAddrWidth+:PerfEventAddrWidth] = perf_event_addr_last_oup;
  for (genvar I = 0; I < EventPortCount; I++) begin: g_io5
    for (genvar J = 0; J < PerfEventCount; J++) begin: g_io6
      always_comb o_perf_event_deltas[(I*PerfEventCount+J)*EventDelta+:EventDelta] = perf_event_deltas_oup[I][J];
    end
  end

  axe_tcl_clk_gating u_clk_gate_pwr (
    .i_clk,
    .i_en     (i_clk_en),
    .i_test_en(scan_en),
    .o_clk    (clk_g)
  );

  pve_cva6v u_cva6v (
    .i_clk                           (clk_g),
    .i_rst_n,

    // Config
    .i_boot_addr,
    .i_hart_id,
    // Memory regions
    .i_memreg_addr                   (memreg_addr_inp),
    .i_memreg_size                   (memreg_size_inp),
    .i_memreg_tcdm,
    // Interrupt inputs
    .i_irq,
    .i_ipi,
    .i_platform_irq,
    .i_time_irq,
    // Debug
    .i_debug_req,
    .i_debug_rst_halt_req,
    .o_debug_stop_time,
    // Hart status
    .o_hart_is_wfi,
    .o_hart_unavail,
    .o_hart_under_reset,
    // Memory side, AXI Manager
    // AW
    .o_axi_m_awvalid,
    .o_axi_m_awid,
    .o_axi_m_awaddr,
    .o_axi_m_awlen,
    .o_axi_m_awsize,
    .o_axi_m_awburst,
    .o_axi_m_awlock,
    .o_axi_m_awcache,
    .o_axi_m_awprot,
    .o_axi_m_awatop,
    .i_axi_m_awready,
    // W
    .o_axi_m_wvalid,
    .o_axi_m_wdata,
    .o_axi_m_wstrb,
    .o_axi_m_wlast,
    .i_axi_m_wready,
    // B
    .i_axi_m_bvalid,
    .i_axi_m_bid,
    .i_axi_m_bresp,
    .o_axi_m_bready,
    // AR
    .o_axi_m_arvalid,
    .o_axi_m_arid,
    .o_axi_m_araddr,
    .o_axi_m_arlen,
    .o_axi_m_arsize,
    .o_axi_m_arburst,
    .o_axi_m_arlock,
    .o_axi_m_arcache,
    .o_axi_m_arprot,
    .i_axi_m_arready,
    // R
    .i_axi_m_rvalid,
    .i_axi_m_rid,
    .i_axi_m_rdata,
    .i_axi_m_rresp,
    .i_axi_m_rlast,
    .o_axi_m_rready,
    // Raptor memory ports
    .o_mem_req_valid,
    .o_mem_req_addr                  (mem_req_addr_oup),
    .o_mem_req_we,
    .o_mem_req_be                    (mem_req_be_oup),
    .o_mem_req_wdata                 (mem_req_wdata_oup),
    .i_mem_req_ready,
    .i_mem_res_valid,
    .i_mem_res_rdata                 (mem_res_rdata_inp),
    .i_mem_res_err,
    // Raptor performance counter signals
    .o_perf_cntr_fu_status           (perf_cntr_fu_status_oup),
    .o_perf_cntr_dispatch_queue_full,
    .o_perf_cntr_dispatch_queue_empty,
    .o_perf_cntr_commit_queue_full,
    .o_perf_cntr_commit_queue_empty,
    // CVA6V performance event signals
    .o_perf_event_addr_full          (perf_event_addr_full_oup),
    .o_perf_event_addr_last          (perf_event_addr_last_oup),
    .o_perf_event_deltas             (perf_event_deltas_oup),
    // SRAM configuration
    .i_mem_impl                      (axe_tcl_sram_pkg::impl_inp_t'{
                                      default: '0,
                                      mcs    : axe_tcl_pkg::MCS,
                                      mcsw   : axe_tcl_pkg::MCSW,
                                      ret    : '0,
                                      pde    : '0,
                                      se     : scan_en,
                                      adme   : axe_tcl_pkg::ADME
                                      }),
    .o_mem_impl                      ( )
  );

endmodule : pve_cva6v_p
