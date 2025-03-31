// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

/// Simple SPM TB for instantiation validation
module spm_tb;
  import spm_pkg::*;
  import axe_tcl_sram_pkg::*;

  // =========================
  // Parameters
  localparam int SCP_MEM_SIZE_KB    = 128;
  localparam int ECC_PROTECTION_EN  = 0;

  // Set to 1.2 GHz
  localparam realtime TbCycleTime = 0.8333ns;
  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  // =========================
  // Datatypes
  typedef logic [64-1:0]        spm_axi_data_t;
  typedef logic [32-1:0]        spm_axi_addr_t;
  typedef logic [8-1:0]         spm_axi_strb_t;
  typedef logic [4-1:0]         spm_axi_id_t;
  typedef axi_pkg::axi_len_t    spm_axi_len_t;
  typedef axi_pkg::axi_size_t   spm_axi_size_t;
  typedef axi_pkg::axi_burst_t  spm_axi_burst_t;
  typedef axi_pkg::axi_resp_t   spm_axi_resp_t;
  typedef axi_pkg::axi_cache_t  spm_axi_cache_t;
  typedef axi_pkg::axi_prot_t   spm_axi_prot_t;

  // =========================
  // Signals
  // AXI write address channel
  logic            i_axi_s_awvalid;
  spm_axi_addr_t   i_axi_s_awaddr;
  spm_axi_id_t     i_axi_s_awid;
  spm_axi_len_t    i_axi_s_awlen;
  spm_axi_size_t   i_axi_s_awsize;
  spm_axi_burst_t  i_axi_s_awburst;
  logic            i_axi_s_awlock;
  spm_axi_cache_t  i_axi_s_awcache;
  spm_axi_prot_t   i_axi_s_awprot;
  logic            o_axi_s_awready;
  // AXI write data channel
  logic           i_axi_s_wvalid;
  logic           i_axi_s_wlast;
  spm_axi_data_t  i_axi_s_wdata;
  spm_axi_strb_t  i_axi_s_wstrb;
  logic           o_axi_s_wready;
  // AXI write response channel
  logic           o_axi_s_bvalid;
  spm_axi_id_t    o_axi_s_bid;
  spm_axi_resp_t  o_axi_s_bresp;
  logic           i_axi_s_bready;
  // AXI read address channel
  logic            i_axi_s_arvalid;
  spm_axi_addr_t   i_axi_s_araddr;
  spm_axi_id_t     i_axi_s_arid;
  spm_axi_len_t    i_axi_s_arlen;
  spm_axi_size_t   i_axi_s_arsize;
  spm_axi_burst_t  i_axi_s_arburst;
  logic            i_axi_s_arlock;
  spm_axi_cache_t  i_axi_s_arcache;
  spm_axi_prot_t   i_axi_s_arprot;
  logic            o_axi_s_arready;
  // AXI read data/response channel
  logic           o_axi_s_rvalid;
  logic           o_axi_s_rlast;
  spm_axi_id_t    o_axi_s_rid;
  spm_axi_data_t  o_axi_s_rdata;
  spm_axi_resp_t  o_axi_s_rresp;
  logic           i_axi_s_rready;

  /// Disable ECC error reporting and in flight correction.
  logic         i_scp_ecc_disable;
  /// scp_error_status
  logic [26:0]  o_scp_error_status;

  // RAM Configuration pins
  logic       i_ret;
  logic       i_pde;
  logic       i_se;
  logic       o_prn;

  // =========================
  // Clock / Reset genereration and stop of simulation
  logic tb_clk;
  logic tb_rst_n;

  localparam int unsigned ResetCycles = 5;

  initial begin : proc_clk_rst_gen
    tb_clk   = 1'b0;
    tb_rst_n = 1'b0;
    fork
      begin : fork_clk_gen
        forever begin
          #(TbCycleTime/2);
          tb_clk = ~tb_clk;
        end
      end
      begin : fork_rst_gen
        repeat (ResetCycles) @(negedge tb_clk);
        tb_rst_n = 1'b1;
      end
    join
  end

  // =========================
  // Stimuli generation


  // =========================
  // Design Under Test (DUT)

  // - Mem config
  impl_inp_t i_impl;
  impl_oup_t o_impl;
  always_comb begin
    i_impl.ret    = i_ret;
    i_impl.pde    = i_pde;
    i_impl.se     = i_se;
  end
  assign o_prn = o_impl.prn;
  // - DUT
  spm #(
    .SCP_MEM_SIZE_KB(SCP_MEM_SIZE_KB),
    .ECC_PROTECTION_EN(ECC_PROTECTION_EN),
    .spm_axi_data_t(spm_axi_data_t),
    .spm_axi_addr_t(spm_axi_addr_t),
    .spm_axi_strb_t(spm_axi_strb_t),
    .spm_axi_len_t(spm_axi_len_t),
    .spm_axi_id_t(spm_axi_id_t),
    .spm_axi_size_t(spm_axi_size_t),
    .spm_axi_burst_t(spm_axi_burst_t),
    .spm_axi_resp_t(spm_axi_resp_t),
    .spm_axi_cache_t(spm_axi_cache_t),
    .spm_axi_prot_t(spm_axi_prot_t)
  ) i_spm_dut (
    .i_clk (tb_clk),
    .i_rst_n(tb_rst_n),
    .i_axi_s_awvalid(i_axi_s_awvalid),
    .i_axi_s_awaddr(i_axi_s_awaddr),
    .i_axi_s_awid(i_axi_s_awid),
    .i_axi_s_awlen(i_axi_s_awlen),
    .i_axi_s_awsize(i_axi_s_awsize),
    .i_axi_s_awburst(i_axi_s_awburst),
    .i_axi_s_awlock(i_axi_s_awlock),
    .i_axi_s_awcache(i_axi_s_awcache),
    .i_axi_s_awprot(i_axi_s_awprot),
    .o_axi_s_awready(o_axi_s_awready),
    .i_axi_s_wvalid(i_axi_s_wvalid),
    .i_axi_s_wlast(i_axi_s_wlast),
    .i_axi_s_wdata(i_axi_s_wdata),
    .i_axi_s_wstrb(i_axi_s_wstrb),
    .o_axi_s_wready(o_axi_s_wready),
    .o_axi_s_bvalid(o_axi_s_bvalid),
    .o_axi_s_bid(o_axi_s_bid),
    .o_axi_s_bresp(o_axi_s_bresp),
    .i_axi_s_bready(i_axi_s_bready),
    .i_axi_s_arvalid(i_axi_s_arvalid),
    .i_axi_s_araddr(i_axi_s_araddr),
    .i_axi_s_arid(i_axi_s_arid),
    .i_axi_s_arlen(i_axi_s_arlen),
    .i_axi_s_arsize(i_axi_s_arsize),
    .i_axi_s_arburst(i_axi_s_arburst),
    .i_axi_s_arlock(i_axi_s_arlock),
    .i_axi_s_arcache(i_axi_s_arcache),
    .i_axi_s_arprot(i_axi_s_arprot),
    .o_axi_s_arready(o_axi_s_arready),
    .o_axi_s_rvalid(o_axi_s_rvalid),
    .o_axi_s_rlast(o_axi_s_rlast),
    .o_axi_s_rid(o_axi_s_rid),
    .o_axi_s_rdata(o_axi_s_rdata),
    .o_axi_s_rresp(o_axi_s_rresp),
    .i_axi_s_rready(i_axi_s_rready),
    // ECC
    .o_irq(/*NC*/),
    .i_scp_ecc_disable(i_scp_ecc_disable),
    .o_scp_error_status(o_scp_error_status),
    // Memory cfg
    .i_impl(i_impl),
    .o_impl(o_impl)
  );

endmodule
