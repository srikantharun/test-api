// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// MMIO bridge wrapper of L1
///
module pve_l1_p
  import axi_pkg::*;
  import chip_pkg::*;
  import mmio_pkg::*;
  import axe_tcl_sram_pkg::*;
  import pve_pkg::*;
  import pve_cva6v_pkg::*;
  import cva6v_pve_pkg::*;
  import pve_l1_pkg::*;
(
  /// Clock, positive edge triggered
  input  wire                    i_clk,
  /// Asynchronous reset, active low
  input  wire                    i_rst_n,

  // MMIO ports
  input  pve_l1_mem_logic_t  i_rvv_l1_mem_req_valid,
  input  pve_l1_mem_addr_t   i_rvv_l1_mem_req_addr,
  input  pve_l1_mem_logic_t  i_rvv_l1_mem_req_we,
  input  pve_l1_mem_be_t     i_rvv_l1_mem_req_be,
  input  pve_l1_mem_data_t   i_rvv_l1_mem_req_wdata,
  output pve_l1_mem_logic_t  o_rvv_l1_mem_req_ready,
  output pve_l1_mem_logic_t  o_rvv_l1_mem_rsp_valid,
  output pve_l1_mem_data_t   o_rvv_l1_mem_rsp_rdata,
  output pve_l1_mem_logic_t  o_rvv_l1_mem_rsp_err,

  // AXI write address channel
  input  logic               i_l1_axi_s_awvalid,
  input  pve_ht_axi_m_id_t   i_l1_axi_s_awid,
  input  chip_axi_addr_t     i_l1_axi_s_awaddr,
  input  axi_len_t           i_l1_axi_s_awlen,
  input  axi_size_e          i_l1_axi_s_awsize,
  input  axi_burst_e         i_l1_axi_s_awburst,
  output logic               o_l1_axi_s_awready,
  // AXI write data channel
  input  logic               i_l1_axi_s_wvalid,
  input  chip_axi_ht_data_t  i_l1_axi_s_wdata,
  input  chip_axi_ht_wstrb_t i_l1_axi_s_wstrb,
  input  logic               i_l1_axi_s_wlast,
  output logic               o_l1_axi_s_wready,
  // AXI write response channel
  output logic               o_l1_axi_s_bvalid,
  output pve_ht_axi_m_id_t   o_l1_axi_s_bid,
  output axi_resp_e          o_l1_axi_s_bresp,
  input  logic               i_l1_axi_s_bready,
  // AXI read address channel
  input  logic               i_l1_axi_s_arvalid,
  input  pve_ht_axi_m_id_t   i_l1_axi_s_arid,
  input  chip_axi_addr_t     i_l1_axi_s_araddr,
  input  axi_len_t           i_l1_axi_s_arlen,
  input  axi_size_e          i_l1_axi_s_arsize,
  input  axi_burst_e         i_l1_axi_s_arburst,
  output logic               o_l1_axi_s_arready,
  // AXI read data/response channel
  output logic               o_l1_axi_s_rvalid,
  output pve_ht_axi_m_id_t   o_l1_axi_s_rid,
  output chip_axi_ht_data_t  o_l1_axi_s_rdata,
  output axi_resp_e          o_l1_axi_s_rresp,
  output logic               o_l1_axi_s_rlast,
  input  logic               i_l1_axi_s_rready,

  // Configuration control
  input  pve_l1_base_addr_t  i_l1_base_address,

  // JTAG
  input  wire                ijtag_tck,
  input  wire                ijtag_reset,
  input  logic               ijtag_sel,
  input  logic               ijtag_ue,
  input  logic               ijtag_se,
  input  logic               ijtag_ce,
  input  logic               ijtag_si,
  output logic               ijtag_so,
  // DFT
  input  wire                test_clk,
  input  logic               test_mode,
  input  logic               edt_update,
  input  logic               scan_en,
  input  logic [        7:0] scan_in,
  output logic [        7:0] scan_out,
  // BIST
  input  wire                bisr_clk,
  input  wire                bisr_reset,
  input  logic               bisr_shift_en,
  input  logic               bisr_si,
  output logic               bisr_so
);

  pve_cva6v_mem_logic_t rvv_l1_mem_req_valid_inp[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_addr_t  rvv_l1_mem_req_addr_inp [PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t rvv_l1_mem_req_we_inp   [PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_be_t    rvv_l1_mem_req_be_inp   [PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_data_t  rvv_l1_mem_req_wdata_inp[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t rvv_l1_mem_req_ready_oup[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t rvv_l1_mem_rsp_valid_oup[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_data_t  rvv_l1_mem_rsp_rdata_oup[PVE_CLUSTER_N_CPU];
  pve_cva6v_mem_logic_t rvv_l1_mem_rsp_err_oup  [PVE_CLUSTER_N_CPU];

  for (genvar C = 0; C < PVE_CLUSTER_N_CPU; C++) begin : g_cpu
    for (genvar I = 0; I < MemPortCount; I++) begin: g_mem
      always_comb rvv_l1_mem_req_valid_inp[C][I] = i_rvv_l1_mem_req_valid[C*MemPortCount+I];
      always_comb rvv_l1_mem_req_addr_inp [C][I] = i_rvv_l1_mem_req_addr [(C*MemPortCount+I)*MemPortAddrWidth+:MemPortAddrWidth];
      always_comb rvv_l1_mem_req_we_inp   [C][I] = i_rvv_l1_mem_req_we   [C*MemPortCount+I];
      always_comb rvv_l1_mem_req_be_inp   [C][I] = i_rvv_l1_mem_req_be   [(C*MemPortCount+I)*MemPortBeWidth+:MemPortBeWidth];
      always_comb rvv_l1_mem_req_wdata_inp[C][I] = i_rvv_l1_mem_req_wdata[(C*MemPortCount+I)*MemPortWidth+:MemPortWidth];
      always_comb o_rvv_l1_mem_req_ready[C*MemPortCount+I] = rvv_l1_mem_req_ready_oup[C][I];
      always_comb o_rvv_l1_mem_rsp_valid[C*MemPortCount+I] = rvv_l1_mem_rsp_valid_oup[C][I];
      always_comb o_rvv_l1_mem_rsp_rdata[(C*MemPortCount+I)*MemPortWidth+:MemPortWidth] = rvv_l1_mem_rsp_rdata_oup[C][I];
      always_comb o_rvv_l1_mem_rsp_err  [C*MemPortCount+I] = rvv_l1_mem_rsp_err_oup  [C][I];
    end
  end

  pve_l1 u_pve_l1 (
    .i_clk,
    .i_rst_n,
    .i_scan_en(scan_en),

    // MMIO ports
    .i_rvv_l1_mem_req_valid(rvv_l1_mem_req_valid_inp),
    .i_rvv_l1_mem_req_addr (rvv_l1_mem_req_addr_inp ),
    .i_rvv_l1_mem_req_we   (rvv_l1_mem_req_we_inp   ),
    .i_rvv_l1_mem_req_be   (rvv_l1_mem_req_be_inp   ),
    .i_rvv_l1_mem_req_wdata(rvv_l1_mem_req_wdata_inp),
    .o_rvv_l1_mem_req_ready(rvv_l1_mem_req_ready_oup),
    .o_rvv_l1_mem_rsp_valid(rvv_l1_mem_rsp_valid_oup),
    .o_rvv_l1_mem_rsp_rdata(rvv_l1_mem_rsp_rdata_oup),
    .o_rvv_l1_mem_rsp_err  (rvv_l1_mem_rsp_err_oup  ),

    // AXI write address channel
    .i_l1_axi_s_awvalid,
    .i_l1_axi_s_awid,
    .i_l1_axi_s_awaddr,
    .i_l1_axi_s_awlen,
    .i_l1_axi_s_awsize,
    .i_l1_axi_s_awburst,
    .o_l1_axi_s_awready,
    // AXI write data channel
    .i_l1_axi_s_wvalid,
    .i_l1_axi_s_wdata,
    .i_l1_axi_s_wstrb,
    .i_l1_axi_s_wlast,
    .o_l1_axi_s_wready,
    // AXI write response channel
    .o_l1_axi_s_bvalid,
    .o_l1_axi_s_bid,
    .o_l1_axi_s_bresp,
    .i_l1_axi_s_bready,
    // AXI read address channel
    .i_l1_axi_s_arvalid,
    .i_l1_axi_s_arid,
    .i_l1_axi_s_araddr,
    .i_l1_axi_s_arlen,
    .i_l1_axi_s_arsize,
    .i_l1_axi_s_arburst,
    .o_l1_axi_s_arready,
    // AXI read data/response channel
    .o_l1_axi_s_rvalid,
    .o_l1_axi_s_rid,
    .o_l1_axi_s_rdata,
    .o_l1_axi_s_rresp,
    .o_l1_axi_s_rlast,
    .i_l1_axi_s_rready,

    // Configuration control
    .i_l1_base_address,

    // SRAM configuration
    .i_mem_impl            (axe_tcl_sram_pkg::impl_inp_t'{
                            default: '0,
                            mcs    : axe_tcl_pkg::MCS,
                            mcsw   : axe_tcl_pkg::MCSW,
                            ret    : '0,
                            pde    : '0,
                            se     : scan_en,
                            adme   : axe_tcl_pkg::ADME
                            }),
    .o_mem_impl            ( )
  );

endmodule
