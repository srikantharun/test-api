// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Joao Martins <joao.martins@axelera.ai>

module sys_spm
  import sys_spm_pkg::*;
  #(
    // AXI types
    parameter type sys_spm_axi_data_t   = chip_pkg::chip_axi_lt_data_t,
    parameter type sys_spm_axi_addr_t   = chip_pkg::chip_axi_addr_t,
    parameter type sys_spm_axi_strb_t   = chip_pkg::chip_axi_lt_wstrb_t,
    parameter type sys_spm_axi_len_t    = axi_pkg::axi_len_t,
    parameter type sys_spm_axi_id_t     = sys_spm_targ_lt_axi_id_t,
    parameter type sys_spm_axi_size_t   = axi_pkg::axi_size_t,
    parameter type sys_spm_axi_burst_t  = axi_pkg::axi_burst_t,
    parameter type sys_spm_axi_resp_t   = axi_pkg::axi_resp_t,
    parameter type sys_spm_axi_cache_t  = axi_pkg::axi_cache_t,
    parameter type sys_spm_axi_prot_t   = axi_pkg::axi_prot_t
  ) (
    // Clock and Reset
    input wire  i_clk,
    input wire  i_rst_n,

    // AXI Write Address Channel
    input  sys_spm_axi_addr_t       i_lt_axi_s_awaddr,
    input  sys_spm_targ_lt_axi_id_t i_lt_axi_s_awid,
    input  sys_spm_axi_len_t        i_lt_axi_s_awlen,
    input  sys_spm_axi_size_t       i_lt_axi_s_awsize,
    input  sys_spm_axi_burst_t      i_lt_axi_s_awburst,
    input  sys_spm_axi_cache_t      i_lt_axi_s_awcache,
    input  sys_spm_axi_prot_t       i_lt_axi_s_awprot,
    input  logic                    i_lt_axi_s_awlock,
    input  logic                    i_lt_axi_s_awvalid,
    output logic                    o_lt_axi_s_awready,

    // AXI Write Data Channel
    input  sys_spm_axi_data_t       i_lt_axi_s_wdata,
    input  sys_spm_axi_strb_t       i_lt_axi_s_wstrb,
    input  logic                    i_lt_axi_s_wlast,
    input  logic                    i_lt_axi_s_wvalid,
    output logic                    o_lt_axi_s_wready,

    // AXI Write Response Channel
    output logic                    o_lt_axi_s_bvalid,
    output sys_spm_targ_lt_axi_id_t o_lt_axi_s_bid,
    output sys_spm_axi_resp_t       o_lt_axi_s_bresp,
    input  logic                    i_lt_axi_s_bready,

    // AXI Read Address Channel
    input  sys_spm_axi_addr_t       i_lt_axi_s_araddr,
    input  sys_spm_targ_lt_axi_id_t i_lt_axi_s_arid,
    input  sys_spm_axi_len_t        i_lt_axi_s_arlen,
    input  sys_spm_axi_size_t       i_lt_axi_s_arsize,
    input  sys_spm_axi_burst_t      i_lt_axi_s_arburst,
    input  sys_spm_axi_cache_t      i_lt_axi_s_arcache,
    input  sys_spm_axi_prot_t       i_lt_axi_s_arprot,
    input  logic                    i_lt_axi_s_arlock,
    input  logic                    i_lt_axi_s_arvalid,
    output logic                    o_lt_axi_s_arready,

    // AXI Read Channel
    output logic                    o_lt_axi_s_rvalid,
    output logic                    o_lt_axi_s_rlast,
    output sys_spm_targ_lt_axi_id_t o_lt_axi_s_rid,
    output sys_spm_axi_data_t       o_lt_axi_s_rdata,
    output sys_spm_axi_resp_t       o_lt_axi_s_rresp,
    input  logic                    i_lt_axi_s_rready,

    /// Disable ECC error reporting and in flight correction.
    input  logic i_scp_ecc_disable,
    /// scp_error_status
    output spm_pkg::spm_error_status_t o_scp_error_status,

    /// Error IRQ signal
    output logic         o_irq,

    // Internal observation signals
    output spm_pkg::spm_obs_t o_spm_obs,

    // RAM Configuration pins
    input logic       i_ret,
    input logic       i_pde,
    input logic       i_se,
    output logic      o_prn
);

  // Signals
  axe_tcl_sram_pkg::impl_inp_t i_impl;
  axe_tcl_sram_pkg::impl_oup_t o_impl;

  // Structs mappigs
  always_comb begin
    // Inputs
    i_impl.ret  = i_ret;
    i_impl.pde  = i_pde;
    i_impl.se   = i_se;

    // Outputs
    o_prn = o_impl.prn;
  end

  // SPM Instance
  spm #(
    .SPM_MEM_SIZE_KB            (SYS_SPM_MEM_SIZE_KB),
    .SPM_NB_BANKS               (SYS_SPM_NB_BANKS),
    .SPM_NB_SUB_BANKS           (SYS_SPM_NB_SUB_BANKS),
    .SPM_NB_MINI_BANKS          (SYS_SPM_NB_MINI_BANKS),
    .SPM_NB_SRAMS_PER_MINI_BANK (SYS_SPM_NB_SRAMS_PER_MINI_BANK),
    .SPM_NB_REQ_PIPELINE        (SYS_SPM_NB_REQ_PIPELINE),
    .SPM_NB_RSP_PIPELINE        (SYS_SPM_NB_RSP_PIPELINE),
    .SPM_MAX_NUM_WR_OSR         (16),
    .SPM_MAX_NUM_RD_OSR         (16),
    .ECC_PROTECTION_EN          (ECC_PROTECTION_EN),
    .EN_ATOMIC_SUPPORT          (0), // Sys-SPM doesn't support Atomic transactions
    // AXI types
    .spm_axi_data_t (sys_spm_axi_data_t),
    .spm_axi_addr_t (sys_spm_axi_addr_t),
    .spm_axi_strb_t (sys_spm_axi_strb_t),
    .spm_axi_len_t  (sys_spm_axi_len_t),
    .spm_axi_id_t   (sys_spm_axi_id_t),
    .spm_axi_size_t (sys_spm_axi_size_t),
    .spm_axi_burst_t(sys_spm_axi_burst_t),
    .spm_axi_resp_t (sys_spm_axi_resp_t),
    .spm_axi_cache_t(sys_spm_axi_cache_t),
    .spm_axi_prot_t (sys_spm_axi_prot_t)
  ) u_spm (
    // Clk Rst
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    // AXI
    .i_axi_s_awvalid(i_lt_axi_s_awvalid),
    .i_axi_s_awaddr (i_lt_axi_s_awaddr),
    .i_axi_s_awid   (i_lt_axi_s_awid),
    .i_axi_s_awlen  (i_lt_axi_s_awlen),
    .i_axi_s_awsize (i_lt_axi_s_awsize),
    .i_axi_s_awburst(i_lt_axi_s_awburst),
    .i_axi_s_awlock (i_lt_axi_s_awlock),
    .i_axi_s_awcache(i_lt_axi_s_awcache),
    .i_axi_s_awprot (i_lt_axi_s_awprot),
    .o_axi_s_awready(o_lt_axi_s_awready),
    .i_axi_s_awatop ('{default:0}), // Sys-SPM doesn't support Atomic transactions
    .i_axi_s_wvalid (i_lt_axi_s_wvalid),
    .i_axi_s_wlast  (i_lt_axi_s_wlast),
    .i_axi_s_wdata  (i_lt_axi_s_wdata),
    .i_axi_s_wstrb  (i_lt_axi_s_wstrb),
    .o_axi_s_wready (o_lt_axi_s_wready),
    .o_axi_s_bvalid (o_lt_axi_s_bvalid),
    .o_axi_s_bid    (o_lt_axi_s_bid),
    .o_axi_s_bresp  (o_lt_axi_s_bresp),
    .i_axi_s_bready (i_lt_axi_s_bready),
    .i_axi_s_arvalid(i_lt_axi_s_arvalid),
    .i_axi_s_araddr (i_lt_axi_s_araddr),
    .i_axi_s_arid   (i_lt_axi_s_arid),
    .i_axi_s_arlen  (i_lt_axi_s_arlen),
    .i_axi_s_arsize (i_lt_axi_s_arsize),
    .i_axi_s_arburst(i_lt_axi_s_arburst),
    .i_axi_s_arlock (i_lt_axi_s_arlock),
    .i_axi_s_arcache(i_lt_axi_s_arcache),
    .i_axi_s_arprot (i_lt_axi_s_arprot),
    .o_axi_s_arready(o_lt_axi_s_arready),
    .o_axi_s_rvalid (o_lt_axi_s_rvalid),
    .o_axi_s_rlast  (o_lt_axi_s_rlast),
    .o_axi_s_rid    (o_lt_axi_s_rid),
    .o_axi_s_rdata  (o_lt_axi_s_rdata),
    .o_axi_s_rresp  (o_lt_axi_s_rresp),
    .i_axi_s_rready (i_lt_axi_s_rready),
    // ECC and Error
    .o_irq             (o_irq),
    .i_scp_ecc_disable (i_scp_ecc_disable),
    .o_scp_error_status(o_scp_error_status),
    // Internal observation
    .o_spm_obs(o_spm_obs),
    // Mem Cfg
    .i_impl(i_impl),
    .o_impl(o_impl)
  );

endmodule

