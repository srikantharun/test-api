
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: Axelera (Axelera@axelera.ai)

`ifndef AI_CORE_SV
`define AI_CORE_SV

module ai_core

  import aic_common_pkg::*;
  import aic_ls_pkg::*;
  import dmc_pkg::*;
  import token_mgr_mapping_aic_pkg::*;


(
  input logic   i_clk,
  input logic   i_ref_clk,
  input logic   i_c2c_clk,
  input logic   i_rst_n,
  input logic   i_ref_rst_n,
  input logic  [11:0] i_cid,
  input logic   i_test_mode,
  input logic   i_inter_core_sync,
  input logic  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_reset_vector,
  input logic   i_thermal_throttle_async,
  input logic   i_aic_throttle_async,
  input logic   i_thermal_warning_async,
  output logic   o_mvm_throttle_async,
  input logic   i_aic_boost_ack_async,
  output logic   o_aic_boost_req_async,
  output logic   o_imc_bist_busy_async,
  output logic   o_imc_bist_done_async,
  output logic   o_imc_bist_pass_async,
  output logic  [7:0] o_tok_prod_ocpl_m_maddr,
  output logic   o_tok_prod_ocpl_m_mcmd,
  input logic   i_tok_prod_ocpl_m_scmdaccept,
  output logic  [7:0] o_tok_prod_ocpl_m_mdata,
  input logic  [7:0] i_tok_cons_ocpl_s_maddr,
  input logic   i_tok_cons_ocpl_s_mcmd,
  output logic   o_tok_cons_ocpl_s_scmdaccept,
  input logic  [7:0] i_tok_cons_ocpl_s_mdata,
  output logic   o_irq,
  input logic   i_msip_async,
  input logic   i_mtip_async,
  input logic   i_debug_int_async,
  input logic   i_resethaltreq_async,
  output logic   o_stoptime_async,
  output logic   o_hart_unavail_async,
  output logic   o_hart_under_reset_async,
  inout wire   io_ibias_ts,
  inout wire   io_vsense_ts,
  output logic  [aic_common_pkg::AIC_OBS_DW-1:0] o_aic_obs,
  input logic  [4:0] i_reserved,
  output logic  [4:0] o_reserved,
  output  [aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_awaddr,
  output  [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_awid,
  output  [aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_awlen,
  output  [aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_awsize,
  output  [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_awburst,
  output  [aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_awcache,
  output  [aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_awprot,
  output   o_noc_ht_axi_m_awlock,
  output   o_noc_ht_axi_m_awvalid,
  input   i_noc_ht_axi_m_awready,
  output  [aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] o_noc_ht_axi_m_wdata,
  output  [aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] o_noc_ht_axi_m_wstrb,
  output   o_noc_ht_axi_m_wlast,
  output   o_noc_ht_axi_m_wvalid,
  input   i_noc_ht_axi_m_wready,
  input   i_noc_ht_axi_m_bvalid,
  input  [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_bid,
  input  [aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_bresp,
  output   o_noc_ht_axi_m_bready,
  output  [aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] o_noc_ht_axi_m_araddr,
  output  [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] o_noc_ht_axi_m_arid,
  output  [aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] o_noc_ht_axi_m_arlen,
  output  [aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] o_noc_ht_axi_m_arsize,
  output  [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_ht_axi_m_arburst,
  output  [aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] o_noc_ht_axi_m_arcache,
  output  [aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] o_noc_ht_axi_m_arprot,
  output   o_noc_ht_axi_m_arlock,
  output   o_noc_ht_axi_m_arvalid,
  input   i_noc_ht_axi_m_arready,
  input   i_noc_ht_axi_m_rvalid,
  input   i_noc_ht_axi_m_rlast,
  input  [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] i_noc_ht_axi_m_rid,
  input  [aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] i_noc_ht_axi_m_rdata,
  input  [aic_common_pkg::AIC_HT_AXI_RESP_WIDTH-1:0] i_noc_ht_axi_m_rresp,
  output   o_noc_ht_axi_m_rready,
  output  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_awaddr,
  output  [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_awid,
  output  [aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_awlen,
  output  [aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_awsize,
  output  [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_awburst,
  output  [aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_awcache,
  output  [aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_awprot,
  output   o_noc_lt_axi_m_awlock,
  output   o_noc_lt_axi_m_awvalid,
  input   i_noc_lt_axi_m_awready,
  output  [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_m_wdata,
  output  [aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] o_noc_lt_axi_m_wstrb,
  output   o_noc_lt_axi_m_wlast,
  output   o_noc_lt_axi_m_wvalid,
  input   i_noc_lt_axi_m_wready,
  input   i_noc_lt_axi_m_bvalid,
  input  [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_bid,
  input  [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_bresp,
  output   o_noc_lt_axi_m_bready,
  output  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] o_noc_lt_axi_m_araddr,
  output  [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_noc_lt_axi_m_arid,
  output  [aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] o_noc_lt_axi_m_arlen,
  output  [aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] o_noc_lt_axi_m_arsize,
  output  [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] o_noc_lt_axi_m_arburst,
  output  [aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] o_noc_lt_axi_m_arcache,
  output  [aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] o_noc_lt_axi_m_arprot,
  output   o_noc_lt_axi_m_arlock,
  output   o_noc_lt_axi_m_arvalid,
  input   i_noc_lt_axi_m_arready,
  input   i_noc_lt_axi_m_rvalid,
  input   i_noc_lt_axi_m_rlast,
  input  [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_noc_lt_axi_m_rid,
  input  [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_m_rdata,
  input  [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] i_noc_lt_axi_m_rresp,
  output   o_noc_lt_axi_m_rready,
  input  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_awaddr,
  input  [aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_awid,
  input  [aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_awlen,
  input  [aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_awsize,
  input  [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_awburst,
  input  [aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_awcache,
  input  [aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_awprot,
  input   i_noc_lt_axi_s_awlock,
  input   i_noc_lt_axi_s_awvalid,
  output   o_noc_lt_axi_s_awready,
  input  [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_noc_lt_axi_s_wdata,
  input  [aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] i_noc_lt_axi_s_wstrb,
  input   i_noc_lt_axi_s_wlast,
  input   i_noc_lt_axi_s_wvalid,
  output   o_noc_lt_axi_s_wready,
  output   o_noc_lt_axi_s_bvalid,
  output  [aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_bid,
  output  [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_bresp,
  input   i_noc_lt_axi_s_bready,
  input  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] i_noc_lt_axi_s_araddr,
  input  [aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] i_noc_lt_axi_s_arid,
  input  [aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] i_noc_lt_axi_s_arlen,
  input  [aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] i_noc_lt_axi_s_arsize,
  input  [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_noc_lt_axi_s_arburst,
  input  [aic_common_pkg::AIC_LT_AXI_CACHE_WIDTH-1:0] i_noc_lt_axi_s_arcache,
  input  [aic_common_pkg::AIC_LT_AXI_PROT_WIDTH-1:0] i_noc_lt_axi_s_arprot,
  input   i_noc_lt_axi_s_arlock,
  input   i_noc_lt_axi_s_arvalid,
  output   o_noc_lt_axi_s_arready,
  output   o_noc_lt_axi_s_rvalid,
  output   o_noc_lt_axi_s_rlast,
  output  [aic_common_pkg::AIC_LT_AXI_M_ID_WIDTH-1:0] o_noc_lt_axi_s_rid,
  output  [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_noc_lt_axi_s_rdata,
  output  [aic_common_pkg::AIC_LT_AXI_RESP_WIDTH-1:0] o_noc_lt_axi_s_rresp,
  input   i_noc_lt_axi_s_rready,
  input logic  [1:0] i_sram_mcs,
  input logic   i_sram_mcsw,
  input logic   i_sram_ret,
  input logic   i_sram_pde,
  input logic  [2:0] i_sram_adme,
  output logic   o_sram_prn,
  input logic   scan_en
);

  localparam uint_t RvvPortSizeWidth = $clog2(cva6v_ai_core_pkg::MemPortBeWidth);

  logic   u_aic_infra_p_to_u_aic_ls_p__o_sram_prn;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awvalid;
  logic  [aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awaddr;
  logic  [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awid;
  logic  [aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awlen;
  logic  [aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awsize;
  logic  [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awburst;
  logic  [aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awcache;
  logic  [aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awprot;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awlock;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wvalid;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wlast;
  logic  [aic_common_pkg::AIC_HT_AXI_WSTRB_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wstrb;
  logic  [aic_common_pkg::AIC_HT_AXI_DATA_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_bready;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arvalid;
  logic  [aic_common_pkg::AIC_HT_AXI_ADDR_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_araddr;
  logic  [aic_common_pkg::AIC_HT_AXI_S_ID_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arid;
  logic  [aic_common_pkg::AIC_HT_AXI_LEN_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arlen;
  logic  [aic_common_pkg::AIC_HT_AXI_SIZE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arsize;
  logic  [aic_common_pkg::AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arburst;
  logic  [aic_common_pkg::AIC_HT_AXI_CACHE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arcache;
  logic  [aic_common_pkg::AIC_HT_AXI_PROT_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arprot;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arlock;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_rready;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awvalid;
  logic  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awaddr;
  logic  [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awid;
  logic  [aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awlen;
  logic  [aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awsize;
  logic  [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awburst;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wvalid;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wlast;
  logic  [aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wstrb;
  logic  [aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_bready;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arvalid;
  logic  [aic_common_pkg::AIC_LT_AXI_ADDR_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_araddr;
  logic  [aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arid;
  logic  [aic_common_pkg::AIC_LT_AXI_LEN_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arlen;
  logic  [aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arsize;
  logic  [aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arburst;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_rready;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_wdata;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_valid;
  logic  [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_addr;
  logic   u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_we;
  logic  [cva6v_ai_core_pkg::MemPortBeWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_be;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_wdata;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifd0_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifd0_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifd1_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifd1_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifd2_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifd2_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifdw_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_ifdw_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_odr_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_odr_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_ifd0_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_ifd0_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_ifd1_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_ifd1_tok_cons_vld;
  logic  [dmc_pkg::DMC_TOKENS_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_odr_tok_prod_rdy;
  logic  [dmc_pkg::DMC_TOKENS_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_odr_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_mvm_exe_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_mvm_exe_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_mvm_prg_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_mvm_prg_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_iau_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_iau_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_dpu_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_M_DPU_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_m_dpu_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dwpu_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_dwpu_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_iau_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_IAU_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_iau_tok_cons_vld;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_PROD-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_dpu_tok_prod_rdy;
  logic  [token_mgr_mapping_aic_pkg::TOK_MGR_D_DPU_NR_TOK_CONS-1:0] u_aic_infra_p_to_u_aic_ls_p__o_d_dpu_tok_cons_vld;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_awready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_wready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bvalid;
  logic  [8:0] u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bid;
  logic  [AIC_HT_AXI_RESP_WIDTH-1:0] u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bresp;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_arready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rvalid;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rlast;
  logic  [8:0] u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rid;
  logic  [511:0] u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rdata;
  logic  [AIC_HT_AXI_RESP_WIDTH-1:0] u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rresp;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_awready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_wready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bvalid;
  logic  [8:0] u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bresp;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_arready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rvalid;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rlast;
  logic  [8:0] u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rid;
  logic  [63:0] u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rresp;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_err;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_req_ready;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_valid;
  logic  [cva6v_ai_core_pkg::MemPortWidth-1:0] u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_rdata;
  logic   u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_err;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifd0_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifd0_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifd1_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifd1_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifd2_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifd2_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifdw_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_ifdw_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_odr_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_m_odr_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_d_ifd0_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_d_ifd0_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_d_ifd1_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_d_ifd1_tok_cons_rdy;
  logic  [DMC_TOKENS_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_d_odr_tok_prod_vld;
  logic  [DMC_TOKENS_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_d_odr_tok_cons_rdy;
  logic  [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_tok_prod_vld;
  logic  [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_tok_cons_rdy;
  logic  [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_tok_prod_vld;
  logic  [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_tok_cons_rdy;
  logic  [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_tok_prod_vld;
  logic  [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_tok_cons_rdy;
  logic  [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_tok_prod_vld;
  logic  [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_tok_cons_rdy;
  logic  [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_tok_prod_vld;
  logic  [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_tok_cons_rdy;
  logic  [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_iau_tok_prod_vld;
  logic  [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_iau_tok_cons_rdy;
  logic  [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_tok_prod_vld;
  logic  [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_tok_cons_rdy;
  logic  [DMC_IRQ_W-1:0] u_aic_ls_p_to_u_aic_infra_p__o_dmc_irq;
  logic  [aic_mid_pkg::NUM_IRQS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_irq;
  logic  [2:0] u_aic_ls_p_to_u_aic_infra_p__o_did_irq;
  logic  [AIC_DMC_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_dmc_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_obs;
  logic  [AIC_TU_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_tu_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_iau_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_obs;
  logic  [7:0] u_aic_ls_p_to_u_aic_infra_p__o_dmc_ts_start;
  logic  [7:0] u_aic_ls_p_to_u_aic_infra_p__o_dmc_ts_end;
  logic  [7:0] u_aic_ls_p_to_u_aic_infra_p__o_dmc_acd_sync;
  logic  [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_ts_start;
  logic  [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_ts_end;
  logic  [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_did_acd_sync;
  logic  [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_ts_start;
  logic  [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_ts_end;
  logic  [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] u_aic_ls_p_to_u_aic_infra_p__o_mid_acd_sync;
  logic   u_aic_ls_p_to_u_aic_ls_p__o_rf_prn;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awvalid;
  logic  [39:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awaddr;
  logic  [8:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awid;
  logic  [7:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awburst;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wvalid;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wlast;
  logic  [7:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wstrb;
  logic  [63:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wdata;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_bready;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arvalid;
  logic  [39:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_araddr;
  logic  [8:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arid;
  logic  [7:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arburst;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_rready;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tvalid;
  logic  [511:0] u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tdata;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tlast;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tvalid;
  logic  [511:0] u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tdata;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tlast;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tvalid;
  logic  [511:0] u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tdata;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tlast;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tvalid;
  logic  [511:0] u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tdata;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tlast;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_m_odr_axis_s_tready;
  logic  [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_exe_tok_prod_rdy;
  logic  [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_exe_tok_cons_vld;
  logic  [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_prg_tok_prod_rdy;
  logic  [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_prg_tok_cons_vld;
  logic  [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_iau_tok_prod_rdy;
  logic  [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_iau_tok_cons_vld;
  logic  [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_dpu_tok_prod_rdy;
  logic  [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_mid_p__o_mid_dpu_tok_cons_vld;
  logic   u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awvalid;
  logic  [39:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awaddr;
  logic  [8:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awid;
  logic  [7:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awburst;
  logic   u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wvalid;
  logic   u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wlast;
  logic  [7:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wstrb;
  logic  [63:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wdata;
  logic   u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_bready;
  logic   u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arvalid;
  logic  [39:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_araddr;
  logic  [8:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arid;
  logic  [7:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arlen;
  logic  [AIC_LT_AXI_SIZE_WIDTH-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arsize;
  logic  [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arburst;
  logic   u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_rready;
  logic   u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tvalid;
  logic  [511:0] u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tdata;
  logic   u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tlast;
  logic   u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tvalid;
  logic  [511:0] u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tdata;
  logic   u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tlast;
  logic   u_aic_ls_p_to_u_aic_did_p__o_d_odr_axis_s_tready;
  logic  [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_dwpu_tok_prod_rdy;
  logic  [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_dwpu_tok_cons_vld;
  logic  [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_iau_tok_prod_rdy;
  logic  [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_iau_tok_cons_vld;
  logic  [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_dpu_tok_prod_rdy;
  logic  [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] u_aic_ls_p_to_u_aic_did_p__o_did_dpu_tok_cons_vld;
  logic   u_aic_ls_p_to_u_aic_mid_p__o_sram_prn;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_awready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_wready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bvalid;
  logic  [8:0] u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bresp;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_arready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rvalid;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rlast;
  logic  [8:0] u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rid;
  logic  [63:0] u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rresp;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_m_ifd0_axis_s_tready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_m_ifd1_axis_s_tready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_m_ifd2_axis_s_tready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_m_ifdw_axis_s_tready;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tvalid;
  logic  [511:0] u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tdata;
  logic   u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tlast;
  logic  [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_tok_prod_vld;
  logic  [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_tok_cons_rdy;
  logic  [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_tok_prod_vld;
  logic  [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_tok_cons_rdy;
  logic  [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] u_aic_mid_p_to_u_aic_ls_p__o_m_iau_tok_prod_vld;
  logic  [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_m_iau_tok_cons_rdy;
  logic  [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_tok_prod_vld;
  logic  [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_tok_cons_rdy;
  logic  [aic_mid_pkg::NUM_IRQS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_irq;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_mid_p_to_u_aic_ls_p__o_m_iau_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_obs;
  logic  [AIC_TU_OBS_DW-1:0] u_aic_mid_p_to_u_aic_ls_p__o_tu_obs;
  logic  [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_ts_start;
  logic  [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_ts_end;
  logic  [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0] u_aic_mid_p_to_u_aic_ls_p__o_acd_sync;
  logic   u_aic_mid_p_to_u_aic_did_p__o_sram_prn;
  logic   u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_awready;
  logic   u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_wready;
  logic   u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bvalid;
  logic  [8:0] u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bid;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bresp;
  logic   u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_arready;
  logic   u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rvalid;
  logic   u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rlast;
  logic  [8:0] u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rid;
  logic  [63:0] u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rdata;
  logic  [AIC_LT_AXI_RESP_WIDTH-1:0] u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rresp;
  logic   u_aic_did_p_to_u_aic_ls_p__o_ifd0_axis_s_tready;
  logic   u_aic_did_p_to_u_aic_ls_p__o_ifd1_axis_s_tready;
  logic   u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tvalid;
  logic  [511:0] u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tdata;
  logic   u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tlast;
  logic  [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] u_aic_did_p_to_u_aic_ls_p__o_dwpu_tok_prod_vld;
  logic  [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] u_aic_did_p_to_u_aic_ls_p__o_dwpu_tok_cons_rdy;
  logic  [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] u_aic_did_p_to_u_aic_ls_p__o_iau_tok_prod_vld;
  logic  [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] u_aic_did_p_to_u_aic_ls_p__o_iau_tok_cons_rdy;
  logic  [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] u_aic_did_p_to_u_aic_ls_p__o_dpu_tok_prod_vld;
  logic  [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] u_aic_did_p_to_u_aic_ls_p__o_dpu_tok_cons_rdy;
  logic  [2:0] u_aic_did_p_to_u_aic_ls_p__o_irq;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_did_p_to_u_aic_ls_p__o_dwpu_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_did_p_to_u_aic_ls_p__o_iau_obs;
  logic  [AIC_DEV_OBS_DW-1:0] u_aic_did_p_to_u_aic_ls_p__o_dpu_obs;
  logic  [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] u_aic_did_p_to_u_aic_ls_p__o_ts_start;
  logic  [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] u_aic_did_p_to_u_aic_ls_p__o_ts_end;
  logic  [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] u_aic_did_p_to_u_aic_ls_p__o_acd_sync;



aic_did_p u_aic_did_p (
  .i_clk (i_clk),
  .i_rst_n (i_rst_n),
  .o_dwpu_obs (u_aic_did_p_to_u_aic_ls_p__o_dwpu_obs),
  .o_iau_obs (u_aic_did_p_to_u_aic_ls_p__o_iau_obs),
  .o_dpu_obs (u_aic_did_p_to_u_aic_ls_p__o_dpu_obs),
  .o_ts_start (u_aic_did_p_to_u_aic_ls_p__o_ts_start),
  .o_ts_end (u_aic_did_p_to_u_aic_ls_p__o_ts_end),
  .o_acd_sync (u_aic_did_p_to_u_aic_ls_p__o_acd_sync),
  .o_irq (u_aic_did_p_to_u_aic_ls_p__o_irq),
  .i_cid (i_cid),
  .i_sram_mcs (i_sram_mcs),
  .i_sram_mcsw (i_sram_mcsw),
  .i_sram_ret (i_sram_ret),
  .i_sram_pde (u_aic_mid_p_to_u_aic_did_p__o_sram_prn),
  .i_sram_adme (i_sram_adme),
  .o_sram_prn (o_sram_prn),
  .i_ifd0_axis_s_tdata (u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tdata),
  .i_ifd0_axis_s_tlast (u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tlast),
  .i_ifd0_axis_s_tvalid (u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tvalid),
  .o_ifd0_axis_s_tready (u_aic_did_p_to_u_aic_ls_p__o_ifd0_axis_s_tready),
  .i_ifd1_axis_s_tdata (u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tdata),
  .i_ifd1_axis_s_tlast (u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tlast),
  .i_ifd1_axis_s_tvalid (u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tvalid),
  .o_ifd1_axis_s_tready (u_aic_did_p_to_u_aic_ls_p__o_ifd1_axis_s_tready),
  .o_odr_axis_m_tdata (u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tdata),
  .o_odr_axis_m_tlast (u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tlast),
  .o_odr_axis_m_tvalid (u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tvalid),
  .i_odr_axis_m_tready (u_aic_ls_p_to_u_aic_did_p__o_d_odr_axis_s_tready),
  .i_dwpu_tok_prod_rdy (u_aic_ls_p_to_u_aic_did_p__o_did_dwpu_tok_prod_rdy),
  .o_dwpu_tok_prod_vld (u_aic_did_p_to_u_aic_ls_p__o_dwpu_tok_prod_vld),
  .o_dwpu_tok_cons_rdy (u_aic_did_p_to_u_aic_ls_p__o_dwpu_tok_cons_rdy),
  .i_dwpu_tok_cons_vld (u_aic_ls_p_to_u_aic_did_p__o_did_dwpu_tok_cons_vld),
  .i_iau_tok_prod_rdy (u_aic_ls_p_to_u_aic_did_p__o_did_iau_tok_prod_rdy),
  .o_iau_tok_prod_vld (u_aic_did_p_to_u_aic_ls_p__o_iau_tok_prod_vld),
  .o_iau_tok_cons_rdy (u_aic_did_p_to_u_aic_ls_p__o_iau_tok_cons_rdy),
  .i_iau_tok_cons_vld (u_aic_ls_p_to_u_aic_did_p__o_did_iau_tok_cons_vld),
  .i_dpu_tok_prod_rdy (u_aic_ls_p_to_u_aic_did_p__o_did_dpu_tok_prod_rdy),
  .o_dpu_tok_prod_vld (u_aic_did_p_to_u_aic_ls_p__o_dpu_tok_prod_vld),
  .o_dpu_tok_cons_rdy (u_aic_did_p_to_u_aic_ls_p__o_dpu_tok_cons_rdy),
  .i_dpu_tok_cons_vld (u_aic_ls_p_to_u_aic_did_p__o_did_dpu_tok_cons_vld),
  .i_cfg_axi_s_awid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awid),
  .i_cfg_axi_s_awaddr (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awaddr),
  .i_cfg_axi_s_awlen (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awlen),
  .i_cfg_axi_s_awsize (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awsize),
  .i_cfg_axi_s_awburst (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awburst),
  .i_cfg_axi_s_awvalid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awvalid),
  .i_cfg_axi_s_wdata (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wdata),
  .i_cfg_axi_s_wstrb (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wstrb),
  .i_cfg_axi_s_wlast (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wlast),
  .i_cfg_axi_s_wvalid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wvalid),
  .i_cfg_axi_s_bready (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_bready),
  .i_cfg_axi_s_arid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arid),
  .i_cfg_axi_s_araddr (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_araddr),
  .i_cfg_axi_s_arlen (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arlen),
  .i_cfg_axi_s_arsize (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arsize),
  .i_cfg_axi_s_arburst (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arburst),
  .i_cfg_axi_s_arvalid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arvalid),
  .i_cfg_axi_s_rready (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_rready),
  .o_cfg_axi_s_awready (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_awready),
  .o_cfg_axi_s_wready (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_wready),
  .o_cfg_axi_s_bid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bid),
  .o_cfg_axi_s_bresp (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bresp),
  .o_cfg_axi_s_bvalid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bvalid),
  .o_cfg_axi_s_arready (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_arready),
  .o_cfg_axi_s_rid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rid),
  .o_cfg_axi_s_rdata (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rdata),
  .o_cfg_axi_s_rresp (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rresp),
  .o_cfg_axi_s_rlast (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rlast),
  .o_cfg_axi_s_rvalid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rvalid),
  .ijtag_tck ('0),
  .ijtag_reset ('0),
  .ijtag_sel ('0),
  .ijtag_ue ('0),
  .ijtag_se ('0),
  .ijtag_ce ('0),
  .ijtag_si ('0),
  .ijtag_so (),
  .test_clk ('0),
  .test_mode (i_test_mode),
  .edt_update ('0),
  .scan_en (scan_en),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
aic_infra_p u_aic_infra_p (
  .i_clk (i_clk),
  .i_rst_n (i_rst_n),
  .i_cid (i_cid),
  .i_inter_core_sync (i_inter_core_sync),
  .i_thermal_warning_async (i_thermal_warning_async),
  .o_reserved (o_reserved),
  .i_reserved (i_reserved),
  .i_mvm_exe_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_obs),
  .i_mvm_prg_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_obs),
  .i_m_iau_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_obs),
  .i_m_dpu_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_obs),
  .i_tu_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_tu_obs),
  .i_dwpu_obs (u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_obs),
  .i_d_iau_obs (u_aic_ls_p_to_u_aic_infra_p__o_did_iau_obs),
  .i_d_dpu_obs (u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_obs),
  .i_dmc_obs (u_aic_ls_p_to_u_aic_infra_p__o_dmc_obs),
  .o_aic_obs (o_aic_obs),
  .i_dmc_ts_start (u_aic_ls_p_to_u_aic_infra_p__o_dmc_ts_start),
  .i_dmc_ts_end (u_aic_ls_p_to_u_aic_infra_p__o_dmc_ts_end),
  .i_did_ts_start (u_aic_ls_p_to_u_aic_infra_p__o_did_ts_start),
  .i_did_ts_end (u_aic_ls_p_to_u_aic_infra_p__o_did_ts_end),
  .i_mid_ts_start (u_aic_ls_p_to_u_aic_infra_p__o_mid_ts_start),
  .i_mid_ts_end (u_aic_ls_p_to_u_aic_infra_p__o_mid_ts_end),
  .i_dmc_acd_sync (u_aic_ls_p_to_u_aic_infra_p__o_dmc_acd_sync),
  .i_did_acd_sync (u_aic_ls_p_to_u_aic_infra_p__o_did_acd_sync),
  .i_mid_acd_sync (u_aic_ls_p_to_u_aic_infra_p__o_mid_acd_sync),
  .i_cva6v_boot_addr (i_reset_vector),
  .i_cva6v_debug_req_async (i_debug_int_async),
  .i_cva6v_debug_rst_halt_req_async (i_resethaltreq_async),
  .o_cva6v_debug_stop_time_async (o_stoptime_async),
  .o_cva6v_hart_unavail_async (o_hart_unavail_async),
  .o_cva6v_hart_under_reset_async (o_hart_under_reset_async),
  .i_mtip_async (i_mtip_async),
  .i_msip_async (i_msip_async),
  .o_rvv_0_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_valid),
  .i_rvv_0_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_req_ready),
  .o_rvv_0_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_addr),
  .o_rvv_0_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_we),
  .o_rvv_0_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_be),
  .o_rvv_0_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_wdata),
  .i_rvv_0_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_valid),
  .i_rvv_0_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_rdata),
  .i_rvv_0_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_err),
  .o_rvv_1_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_valid),
  .i_rvv_1_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_req_ready),
  .o_rvv_1_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_addr),
  .o_rvv_1_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_we),
  .o_rvv_1_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_be),
  .o_rvv_1_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_wdata),
  .i_rvv_1_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_valid),
  .i_rvv_1_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_rdata),
  .i_rvv_1_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_err),
  .o_rvv_2_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_valid),
  .i_rvv_2_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_req_ready),
  .o_rvv_2_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_addr),
  .o_rvv_2_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_we),
  .o_rvv_2_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_be),
  .o_rvv_2_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_wdata),
  .i_rvv_2_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_valid),
  .i_rvv_2_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_rdata),
  .i_rvv_2_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_err),
  .o_rvv_3_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_valid),
  .i_rvv_3_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_req_ready),
  .o_rvv_3_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_addr),
  .o_rvv_3_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_we),
  .o_rvv_3_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_be),
  .o_rvv_3_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_wdata),
  .i_rvv_3_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_valid),
  .i_rvv_3_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_rdata),
  .i_rvv_3_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_err),
  .o_rvv_4_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_valid),
  .i_rvv_4_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_req_ready),
  .o_rvv_4_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_addr),
  .o_rvv_4_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_we),
  .o_rvv_4_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_be),
  .o_rvv_4_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_wdata),
  .i_rvv_4_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_valid),
  .i_rvv_4_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_rdata),
  .i_rvv_4_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_err),
  .o_rvv_5_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_valid),
  .i_rvv_5_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_req_ready),
  .o_rvv_5_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_addr),
  .o_rvv_5_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_we),
  .o_rvv_5_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_be),
  .o_rvv_5_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_wdata),
  .i_rvv_5_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_valid),
  .i_rvv_5_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_rdata),
  .i_rvv_5_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_err),
  .o_rvv_6_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_valid),
  .i_rvv_6_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_req_ready),
  .o_rvv_6_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_addr),
  .o_rvv_6_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_we),
  .o_rvv_6_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_be),
  .o_rvv_6_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_wdata),
  .i_rvv_6_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_valid),
  .i_rvv_6_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_rdata),
  .i_rvv_6_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_err),
  .o_rvv_7_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_valid),
  .i_rvv_7_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_req_ready),
  .o_rvv_7_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_addr),
  .o_rvv_7_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_we),
  .o_rvv_7_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_be),
  .o_rvv_7_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_wdata),
  .i_rvv_7_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_valid),
  .i_rvv_7_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_rdata),
  .i_rvv_7_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_err),
  .i_irq_dmc (u_aic_ls_p_to_u_aic_infra_p__o_dmc_irq),
  .i_irq_aic_mid (u_aic_ls_p_to_u_aic_infra_p__o_mid_irq),
  .i_irq_aic_did (u_aic_ls_p_to_u_aic_infra_p__o_did_irq),
  .i_sram_mcs (i_sram_mcs),
  .i_sram_mcsw (i_sram_mcsw),
  .i_sram_ret (i_sram_ret),
  .i_sram_pde (i_sram_pde),
  .i_sram_adme (i_sram_adme),
  .o_sram_prn (u_aic_infra_p_to_u_aic_ls_p__o_sram_prn),
  .o_tok_prod_ocpl_m_maddr (o_tok_prod_ocpl_m_maddr),
  .o_tok_prod_ocpl_m_mcmd (o_tok_prod_ocpl_m_mcmd),
  .o_tok_prod_ocpl_m_mdata (o_tok_prod_ocpl_m_mdata),
  .i_tok_prod_ocpl_m_scmdaccept (i_tok_prod_ocpl_m_scmdaccept),
  .i_tok_cons_ocpl_s_maddr (i_tok_cons_ocpl_s_maddr),
  .i_tok_cons_ocpl_s_mcmd (i_tok_cons_ocpl_s_mcmd),
  .i_tok_cons_ocpl_s_mdata (i_tok_cons_ocpl_s_mdata),
  .o_tok_cons_ocpl_s_scmdaccept (o_tok_cons_ocpl_s_scmdaccept),
  .o_m_ifd0_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd0_tok_prod_rdy),
  .i_m_ifd0_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd0_tok_prod_vld),
  .i_m_ifd0_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd0_tok_cons_rdy),
  .o_m_ifd0_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd0_tok_cons_vld),
  .o_m_ifd1_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd1_tok_prod_rdy),
  .i_m_ifd1_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd1_tok_prod_vld),
  .i_m_ifd1_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd1_tok_cons_rdy),
  .o_m_ifd1_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd1_tok_cons_vld),
  .o_m_ifd2_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd2_tok_prod_rdy),
  .i_m_ifd2_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd2_tok_prod_vld),
  .i_m_ifd2_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd2_tok_cons_rdy),
  .o_m_ifd2_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd2_tok_cons_vld),
  .o_m_ifdw_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifdw_tok_prod_rdy),
  .i_m_ifdw_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifdw_tok_prod_vld),
  .i_m_ifdw_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifdw_tok_cons_rdy),
  .o_m_ifdw_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifdw_tok_cons_vld),
  .o_d_ifd0_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd0_tok_prod_rdy),
  .i_d_ifd0_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd0_tok_prod_vld),
  .i_d_ifd0_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd0_tok_cons_rdy),
  .o_d_ifd0_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd0_tok_cons_vld),
  .o_d_ifd1_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd1_tok_prod_rdy),
  .i_d_ifd1_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd1_tok_prod_vld),
  .i_d_ifd1_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd1_tok_cons_rdy),
  .o_d_ifd1_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd1_tok_cons_vld),
  .o_m_odr_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_odr_tok_prod_rdy),
  .i_m_odr_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_odr_tok_prod_vld),
  .i_m_odr_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_odr_tok_cons_rdy),
  .o_m_odr_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_odr_tok_cons_vld),
  .o_d_odr_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_odr_tok_prod_rdy),
  .i_d_odr_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_d_odr_tok_prod_vld),
  .i_d_odr_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_d_odr_tok_cons_rdy),
  .o_d_odr_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_odr_tok_cons_vld),
  .o_mvm_exe_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_mvm_exe_tok_prod_rdy),
  .i_mvm_exe_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_tok_prod_vld),
  .i_mvm_exe_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_tok_cons_rdy),
  .o_mvm_exe_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_mvm_exe_tok_cons_vld),
  .o_mvm_prg_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_mvm_prg_tok_prod_rdy),
  .i_mvm_prg_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_tok_prod_vld),
  .i_mvm_prg_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_tok_cons_rdy),
  .o_mvm_prg_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_mvm_prg_tok_cons_vld),
  .o_m_iau_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_iau_tok_prod_rdy),
  .i_m_iau_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_tok_prod_vld),
  .i_m_iau_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_tok_cons_rdy),
  .o_m_iau_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_iau_tok_cons_vld),
  .o_m_dpu_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_dpu_tok_prod_rdy),
  .i_m_dpu_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_tok_prod_vld),
  .i_m_dpu_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_tok_cons_rdy),
  .o_m_dpu_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_dpu_tok_cons_vld),
  .o_dwpu_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_dwpu_tok_prod_rdy),
  .i_dwpu_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_tok_prod_vld),
  .i_dwpu_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_tok_cons_rdy),
  .o_dwpu_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_dwpu_tok_cons_vld),
  .o_d_iau_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_iau_tok_prod_rdy),
  .i_d_iau_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_did_iau_tok_prod_vld),
  .i_d_iau_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_did_iau_tok_cons_rdy),
  .o_d_iau_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_iau_tok_cons_vld),
  .o_d_dpu_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_dpu_tok_prod_rdy),
  .i_d_dpu_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_tok_prod_vld),
  .i_d_dpu_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_tok_cons_rdy),
  .o_d_dpu_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_dpu_tok_cons_vld),
  .o_noc_ht_axi_m_awvalid (o_noc_ht_axi_m_awvalid),
  .o_noc_ht_axi_m_awaddr (o_noc_ht_axi_m_awaddr),
  .o_noc_ht_axi_m_awid (o_noc_ht_axi_m_awid),
  .o_noc_ht_axi_m_awlen (o_noc_ht_axi_m_awlen),
  .o_noc_ht_axi_m_awsize (o_noc_ht_axi_m_awsize),
  .o_noc_ht_axi_m_awburst (o_noc_ht_axi_m_awburst),
  .o_noc_ht_axi_m_awcache (o_noc_ht_axi_m_awcache),
  .o_noc_ht_axi_m_awprot (o_noc_ht_axi_m_awprot),
  .o_noc_ht_axi_m_awlock (o_noc_ht_axi_m_awlock),
  .o_noc_ht_axi_m_wvalid (o_noc_ht_axi_m_wvalid),
  .o_noc_ht_axi_m_wlast (o_noc_ht_axi_m_wlast),
  .o_noc_ht_axi_m_wstrb (o_noc_ht_axi_m_wstrb),
  .o_noc_ht_axi_m_wdata (o_noc_ht_axi_m_wdata),
  .o_noc_ht_axi_m_bready (o_noc_ht_axi_m_bready),
  .o_noc_ht_axi_m_arvalid (o_noc_ht_axi_m_arvalid),
  .o_noc_ht_axi_m_araddr (o_noc_ht_axi_m_araddr),
  .o_noc_ht_axi_m_arid (o_noc_ht_axi_m_arid),
  .o_noc_ht_axi_m_arlen (o_noc_ht_axi_m_arlen),
  .o_noc_ht_axi_m_arsize (o_noc_ht_axi_m_arsize),
  .o_noc_ht_axi_m_arburst (o_noc_ht_axi_m_arburst),
  .o_noc_ht_axi_m_arcache (o_noc_ht_axi_m_arcache),
  .o_noc_ht_axi_m_arprot (o_noc_ht_axi_m_arprot),
  .o_noc_ht_axi_m_arlock (o_noc_ht_axi_m_arlock),
  .o_noc_ht_axi_m_rready (o_noc_ht_axi_m_rready),
  .i_noc_ht_axi_m_awready (i_noc_ht_axi_m_awready),
  .i_noc_ht_axi_m_wready (i_noc_ht_axi_m_wready),
  .i_noc_ht_axi_m_bvalid (i_noc_ht_axi_m_bvalid),
  .i_noc_ht_axi_m_bid (i_noc_ht_axi_m_bid),
  .i_noc_ht_axi_m_bresp (i_noc_ht_axi_m_bresp),
  .i_noc_ht_axi_m_arready (i_noc_ht_axi_m_arready),
  .i_noc_ht_axi_m_rvalid (i_noc_ht_axi_m_rvalid),
  .i_noc_ht_axi_m_rlast (i_noc_ht_axi_m_rlast),
  .i_noc_ht_axi_m_rid (i_noc_ht_axi_m_rid),
  .i_noc_ht_axi_m_rdata (i_noc_ht_axi_m_rdata),
  .i_noc_ht_axi_m_rresp (i_noc_ht_axi_m_rresp),
  .o_dmc_l1_ht_axi_m_awvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awvalid),
  .o_dmc_l1_ht_axi_m_awaddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awaddr),
  .o_dmc_l1_ht_axi_m_awid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awid),
  .o_dmc_l1_ht_axi_m_awlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awlen),
  .o_dmc_l1_ht_axi_m_awsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awsize),
  .o_dmc_l1_ht_axi_m_awburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awburst),
  .o_dmc_l1_ht_axi_m_awcache (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awcache),
  .o_dmc_l1_ht_axi_m_awprot (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awprot),
  .o_dmc_l1_ht_axi_m_awlock (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awlock),
  .o_dmc_l1_ht_axi_m_wvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wvalid),
  .o_dmc_l1_ht_axi_m_wlast (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wlast),
  .o_dmc_l1_ht_axi_m_wstrb (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wstrb),
  .o_dmc_l1_ht_axi_m_wdata (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wdata),
  .o_dmc_l1_ht_axi_m_bready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_bready),
  .o_dmc_l1_ht_axi_m_arvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arvalid),
  .o_dmc_l1_ht_axi_m_araddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_araddr),
  .o_dmc_l1_ht_axi_m_arid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arid),
  .o_dmc_l1_ht_axi_m_arlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arlen),
  .o_dmc_l1_ht_axi_m_arsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arsize),
  .o_dmc_l1_ht_axi_m_arburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arburst),
  .o_dmc_l1_ht_axi_m_arcache (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arcache),
  .o_dmc_l1_ht_axi_m_arprot (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arprot),
  .o_dmc_l1_ht_axi_m_arlock (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arlock),
  .o_dmc_l1_ht_axi_m_rready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_rready),
  .i_dmc_l1_ht_axi_m_awready (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_awready),
  .i_dmc_l1_ht_axi_m_wready (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_wready),
  .i_dmc_l1_ht_axi_m_bvalid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bvalid),
  .i_dmc_l1_ht_axi_m_bid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bid),
  .i_dmc_l1_ht_axi_m_bresp (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bresp),
  .i_dmc_l1_ht_axi_m_arready (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_arready),
  .i_dmc_l1_ht_axi_m_rvalid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rvalid),
  .i_dmc_l1_ht_axi_m_rlast (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rlast),
  .i_dmc_l1_ht_axi_m_rid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rid),
  .i_dmc_l1_ht_axi_m_rdata (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rdata),
  .i_dmc_l1_ht_axi_m_rresp (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rresp),
  .i_noc_lt_axi_s_awvalid (i_noc_lt_axi_s_awvalid),
  .i_noc_lt_axi_s_awaddr (i_noc_lt_axi_s_awaddr),
  .i_noc_lt_axi_s_awid (i_noc_lt_axi_s_awid),
  .i_noc_lt_axi_s_awlen (i_noc_lt_axi_s_awlen),
  .i_noc_lt_axi_s_awsize (i_noc_lt_axi_s_awsize),
  .i_noc_lt_axi_s_awburst (i_noc_lt_axi_s_awburst),
  .i_noc_lt_axi_s_awcache (i_noc_lt_axi_s_awcache),
  .i_noc_lt_axi_s_awprot (i_noc_lt_axi_s_awprot),
  .i_noc_lt_axi_s_awlock (i_noc_lt_axi_s_awlock),
  .i_noc_lt_axi_s_wvalid (i_noc_lt_axi_s_wvalid),
  .i_noc_lt_axi_s_wlast (i_noc_lt_axi_s_wlast),
  .i_noc_lt_axi_s_wstrb (i_noc_lt_axi_s_wstrb),
  .i_noc_lt_axi_s_wdata (i_noc_lt_axi_s_wdata),
  .i_noc_lt_axi_s_bready (i_noc_lt_axi_s_bready),
  .i_noc_lt_axi_s_arvalid (i_noc_lt_axi_s_arvalid),
  .i_noc_lt_axi_s_araddr (i_noc_lt_axi_s_araddr),
  .i_noc_lt_axi_s_arid (i_noc_lt_axi_s_arid),
  .i_noc_lt_axi_s_arlen (i_noc_lt_axi_s_arlen),
  .i_noc_lt_axi_s_arsize (i_noc_lt_axi_s_arsize),
  .i_noc_lt_axi_s_arburst (i_noc_lt_axi_s_arburst),
  .i_noc_lt_axi_s_arcache (i_noc_lt_axi_s_arcache),
  .i_noc_lt_axi_s_arprot (i_noc_lt_axi_s_arprot),
  .i_noc_lt_axi_s_arlock (i_noc_lt_axi_s_arlock),
  .i_noc_lt_axi_s_rready (i_noc_lt_axi_s_rready),
  .o_noc_lt_axi_s_awready (o_noc_lt_axi_s_awready),
  .o_noc_lt_axi_s_wready (o_noc_lt_axi_s_wready),
  .o_noc_lt_axi_s_bvalid (o_noc_lt_axi_s_bvalid),
  .o_noc_lt_axi_s_bid (o_noc_lt_axi_s_bid),
  .o_noc_lt_axi_s_bresp (o_noc_lt_axi_s_bresp),
  .o_noc_lt_axi_s_arready (o_noc_lt_axi_s_arready),
  .o_noc_lt_axi_s_rvalid (o_noc_lt_axi_s_rvalid),
  .o_noc_lt_axi_s_rlast (o_noc_lt_axi_s_rlast),
  .o_noc_lt_axi_s_rid (o_noc_lt_axi_s_rid),
  .o_noc_lt_axi_s_rdata (o_noc_lt_axi_s_rdata),
  .o_noc_lt_axi_s_rresp (o_noc_lt_axi_s_rresp),
  .o_noc_lt_axi_m_awvalid (o_noc_lt_axi_m_awvalid),
  .o_noc_lt_axi_m_awaddr (o_noc_lt_axi_m_awaddr),
  .o_noc_lt_axi_m_awid (o_noc_lt_axi_m_awid),
  .o_noc_lt_axi_m_awlen (o_noc_lt_axi_m_awlen),
  .o_noc_lt_axi_m_awsize (o_noc_lt_axi_m_awsize),
  .o_noc_lt_axi_m_awburst (o_noc_lt_axi_m_awburst),
  .o_noc_lt_axi_m_awcache (o_noc_lt_axi_m_awcache),
  .o_noc_lt_axi_m_awprot (o_noc_lt_axi_m_awprot),
  .o_noc_lt_axi_m_awlock (o_noc_lt_axi_m_awlock),
  .o_noc_lt_axi_m_wvalid (o_noc_lt_axi_m_wvalid),
  .o_noc_lt_axi_m_wlast (o_noc_lt_axi_m_wlast),
  .o_noc_lt_axi_m_wstrb (o_noc_lt_axi_m_wstrb),
  .o_noc_lt_axi_m_wdata (o_noc_lt_axi_m_wdata),
  .o_noc_lt_axi_m_bready (o_noc_lt_axi_m_bready),
  .o_noc_lt_axi_m_arvalid (o_noc_lt_axi_m_arvalid),
  .o_noc_lt_axi_m_araddr (o_noc_lt_axi_m_araddr),
  .o_noc_lt_axi_m_arid (o_noc_lt_axi_m_arid),
  .o_noc_lt_axi_m_arlen (o_noc_lt_axi_m_arlen),
  .o_noc_lt_axi_m_arsize (o_noc_lt_axi_m_arsize),
  .o_noc_lt_axi_m_arburst (o_noc_lt_axi_m_arburst),
  .o_noc_lt_axi_m_arcache (o_noc_lt_axi_m_arcache),
  .o_noc_lt_axi_m_arprot (o_noc_lt_axi_m_arprot),
  .o_noc_lt_axi_m_arlock (o_noc_lt_axi_m_arlock),
  .o_noc_lt_axi_m_rready (o_noc_lt_axi_m_rready),
  .i_noc_lt_axi_m_awready (i_noc_lt_axi_m_awready),
  .i_noc_lt_axi_m_wready (i_noc_lt_axi_m_wready),
  .i_noc_lt_axi_m_bvalid (i_noc_lt_axi_m_bvalid),
  .i_noc_lt_axi_m_bid (i_noc_lt_axi_m_bid),
  .i_noc_lt_axi_m_bresp (i_noc_lt_axi_m_bresp),
  .i_noc_lt_axi_m_arready (i_noc_lt_axi_m_arready),
  .i_noc_lt_axi_m_rvalid (i_noc_lt_axi_m_rvalid),
  .i_noc_lt_axi_m_rlast (i_noc_lt_axi_m_rlast),
  .i_noc_lt_axi_m_rid (i_noc_lt_axi_m_rid),
  .i_noc_lt_axi_m_rdata (i_noc_lt_axi_m_rdata),
  .i_noc_lt_axi_m_rresp (i_noc_lt_axi_m_rresp),
  .o_dmc_l1_lt_axi_m_awvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awvalid),
  .o_dmc_l1_lt_axi_m_awaddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awaddr),
  .o_dmc_l1_lt_axi_m_awid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awid),
  .o_dmc_l1_lt_axi_m_awlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awlen),
  .o_dmc_l1_lt_axi_m_awsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awsize),
  .o_dmc_l1_lt_axi_m_awburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awburst),
  .o_dmc_l1_lt_axi_m_wvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wvalid),
  .o_dmc_l1_lt_axi_m_wlast (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wlast),
  .o_dmc_l1_lt_axi_m_wstrb (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wstrb),
  .o_dmc_l1_lt_axi_m_wdata (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wdata),
  .o_dmc_l1_lt_axi_m_bready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_bready),
  .o_dmc_l1_lt_axi_m_arvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arvalid),
  .o_dmc_l1_lt_axi_m_araddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_araddr),
  .o_dmc_l1_lt_axi_m_arid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arid),
  .o_dmc_l1_lt_axi_m_arlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arlen),
  .o_dmc_l1_lt_axi_m_arsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arsize),
  .o_dmc_l1_lt_axi_m_arburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arburst),
  .o_dmc_l1_lt_axi_m_rready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_rready),
  .i_dmc_l1_lt_axi_m_awready (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_awready),
  .i_dmc_l1_lt_axi_m_wready (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_wready),
  .i_dmc_l1_lt_axi_m_bvalid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bvalid),
  .i_dmc_l1_lt_axi_m_bid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bid),
  .i_dmc_l1_lt_axi_m_bresp (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bresp),
  .i_dmc_l1_lt_axi_m_arready (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_arready),
  .i_dmc_l1_lt_axi_m_rvalid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rvalid),
  .i_dmc_l1_lt_axi_m_rlast (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rlast),
  .i_dmc_l1_lt_axi_m_rid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rid),
  .i_dmc_l1_lt_axi_m_rdata (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rdata),
  .i_dmc_l1_lt_axi_m_rresp (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rresp),
  .ijtag_tck ('0),
  .ijtag_reset ('0),
  .ijtag_sel ('0),
  .ijtag_ue ('0),
  .ijtag_se ('0),
  .ijtag_ce ('0),
  .ijtag_si ('0),
  .ijtag_so (),
  .test_clk ('0),
  .test_mode (i_test_mode),
  .edt_update ('0),
  .scan_en (scan_en),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
aic_ls_p u_aic_ls_p (
  .i_clk (i_clk),
  .i_rst_n (i_rst_n),
  .o_dmc_irq (u_aic_ls_p_to_u_aic_infra_p__o_dmc_irq),
  .o_m_ifd0_axis_m_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tvalid),
  .i_m_ifd0_axis_m_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifd0_axis_s_tready),
  .o_m_ifd0_axis_m_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tdata),
  .o_m_ifd0_axis_m_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tlast),
  .o_m_ifd1_axis_m_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tvalid),
  .i_m_ifd1_axis_m_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifd1_axis_s_tready),
  .o_m_ifd1_axis_m_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tdata),
  .o_m_ifd1_axis_m_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tlast),
  .o_m_ifd2_axis_m_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tvalid),
  .i_m_ifd2_axis_m_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifd2_axis_s_tready),
  .o_m_ifd2_axis_m_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tdata),
  .o_m_ifd2_axis_m_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tlast),
  .o_m_ifdw_axis_m_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tvalid),
  .i_m_ifdw_axis_m_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifdw_axis_s_tready),
  .o_m_ifdw_axis_m_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tdata),
  .o_m_ifdw_axis_m_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tlast),
  .o_d_ifd0_axis_m_tvalid (u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tvalid),
  .i_d_ifd0_axis_m_tready (u_aic_did_p_to_u_aic_ls_p__o_ifd0_axis_s_tready),
  .o_d_ifd0_axis_m_tdata (u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tdata),
  .o_d_ifd0_axis_m_tlast (u_aic_ls_p_to_u_aic_did_p__o_d_ifd0_axis_m_tlast),
  .o_d_ifd1_axis_m_tvalid (u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tvalid),
  .i_d_ifd1_axis_m_tready (u_aic_did_p_to_u_aic_ls_p__o_ifd1_axis_s_tready),
  .o_d_ifd1_axis_m_tdata (u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tdata),
  .o_d_ifd1_axis_m_tlast (u_aic_ls_p_to_u_aic_did_p__o_d_ifd1_axis_m_tlast),
  .i_m_odr_axis_s_tvalid (u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tvalid),
  .o_m_odr_axis_s_tready (u_aic_ls_p_to_u_aic_mid_p__o_m_odr_axis_s_tready),
  .i_m_odr_axis_s_tdata (u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tdata),
  .i_m_odr_axis_s_tlast (u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tlast),
  .i_d_odr_axis_s_tvalid (u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tvalid),
  .o_d_odr_axis_s_tready (u_aic_ls_p_to_u_aic_did_p__o_d_odr_axis_s_tready),
  .i_d_odr_axis_s_tdata (u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tdata),
  .i_d_odr_axis_s_tlast (u_aic_did_p_to_u_aic_ls_p__o_odr_axis_m_tlast),
  .i_rvv_0_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_valid),
  .o_rvv_0_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_req_ready),
  .i_rvv_0_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_addr),
  .i_rvv_0_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_we),
  .i_rvv_0_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_be),
  .i_rvv_0_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_0_req_wdata),
  .o_rvv_0_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_valid),
  .o_rvv_0_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_rdata),
  .o_rvv_0_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_0_res_err),
  .i_rvv_1_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_valid),
  .o_rvv_1_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_req_ready),
  .i_rvv_1_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_addr),
  .i_rvv_1_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_we),
  .i_rvv_1_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_be),
  .i_rvv_1_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_1_req_wdata),
  .o_rvv_1_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_valid),
  .o_rvv_1_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_rdata),
  .o_rvv_1_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_1_res_err),
  .i_rvv_2_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_valid),
  .o_rvv_2_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_req_ready),
  .i_rvv_2_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_addr),
  .i_rvv_2_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_we),
  .i_rvv_2_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_be),
  .i_rvv_2_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_2_req_wdata),
  .o_rvv_2_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_valid),
  .o_rvv_2_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_rdata),
  .o_rvv_2_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_2_res_err),
  .i_rvv_3_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_valid),
  .o_rvv_3_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_req_ready),
  .i_rvv_3_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_addr),
  .i_rvv_3_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_we),
  .i_rvv_3_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_be),
  .i_rvv_3_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_3_req_wdata),
  .o_rvv_3_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_valid),
  .o_rvv_3_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_rdata),
  .o_rvv_3_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_3_res_err),
  .i_rvv_4_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_valid),
  .o_rvv_4_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_req_ready),
  .i_rvv_4_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_addr),
  .i_rvv_4_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_we),
  .i_rvv_4_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_be),
  .i_rvv_4_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_4_req_wdata),
  .o_rvv_4_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_valid),
  .o_rvv_4_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_rdata),
  .o_rvv_4_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_4_res_err),
  .i_rvv_5_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_valid),
  .o_rvv_5_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_req_ready),
  .i_rvv_5_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_addr),
  .i_rvv_5_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_we),
  .i_rvv_5_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_be),
  .i_rvv_5_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_5_req_wdata),
  .o_rvv_5_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_valid),
  .o_rvv_5_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_rdata),
  .o_rvv_5_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_5_res_err),
  .i_rvv_6_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_valid),
  .o_rvv_6_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_req_ready),
  .i_rvv_6_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_addr),
  .i_rvv_6_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_we),
  .i_rvv_6_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_be),
  .i_rvv_6_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_6_req_wdata),
  .o_rvv_6_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_valid),
  .o_rvv_6_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_rdata),
  .o_rvv_6_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_6_res_err),
  .i_rvv_7_req_valid (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_valid),
  .o_rvv_7_req_ready (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_req_ready),
  .i_rvv_7_req_addr (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_addr),
  .i_rvv_7_req_we (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_we),
  .i_rvv_7_req_be (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_be),
  .i_rvv_7_req_wdata (u_aic_infra_p_to_u_aic_ls_p__o_rvv_7_req_wdata),
  .o_rvv_7_res_valid (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_valid),
  .o_rvv_7_res_rdata (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_rdata),
  .o_rvv_7_res_err (u_aic_ls_p_to_u_aic_infra_p__o_rvv_7_res_err),
  .o_m_ifd0_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd0_tok_prod_vld),
  .i_m_ifd0_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd0_tok_prod_rdy),
  .i_m_ifd0_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd0_tok_cons_vld),
  .o_m_ifd0_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd0_tok_cons_rdy),
  .o_m_ifd1_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd1_tok_prod_vld),
  .i_m_ifd1_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd1_tok_prod_rdy),
  .i_m_ifd1_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd1_tok_cons_vld),
  .o_m_ifd1_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd1_tok_cons_rdy),
  .o_m_ifd2_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd2_tok_prod_vld),
  .i_m_ifd2_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd2_tok_prod_rdy),
  .i_m_ifd2_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifd2_tok_cons_vld),
  .o_m_ifd2_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifd2_tok_cons_rdy),
  .o_m_ifdw_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_ifdw_tok_prod_vld),
  .i_m_ifdw_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_ifdw_tok_prod_rdy),
  .i_m_ifdw_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_ifdw_tok_cons_vld),
  .o_m_ifdw_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_ifdw_tok_cons_rdy),
  .o_d_ifd0_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd0_tok_prod_vld),
  .i_d_ifd0_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd0_tok_prod_rdy),
  .i_d_ifd0_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd0_tok_cons_vld),
  .o_d_ifd0_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd0_tok_cons_rdy),
  .o_d_ifd1_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd1_tok_prod_vld),
  .i_d_ifd1_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd1_tok_prod_rdy),
  .i_d_ifd1_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_ifd1_tok_cons_vld),
  .o_d_ifd1_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_d_ifd1_tok_cons_rdy),
  .o_m_odr_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_m_odr_tok_prod_vld),
  .i_m_odr_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_odr_tok_prod_rdy),
  .i_m_odr_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_odr_tok_cons_vld),
  .o_m_odr_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_m_odr_tok_cons_rdy),
  .o_d_odr_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_d_odr_tok_prod_vld),
  .i_d_odr_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_odr_tok_prod_rdy),
  .i_d_odr_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_odr_tok_cons_vld),
  .o_d_odr_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_d_odr_tok_cons_rdy),
  .o_dmc_ts_start (u_aic_ls_p_to_u_aic_infra_p__o_dmc_ts_start),
  .o_dmc_ts_end (u_aic_ls_p_to_u_aic_infra_p__o_dmc_ts_end),
  .o_dmc_acd_sync (u_aic_ls_p_to_u_aic_infra_p__o_dmc_acd_sync),
  .i_hp_axi_s_awvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awvalid),
  .i_hp_axi_s_awaddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awaddr),
  .i_hp_axi_s_awid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awid),
  .i_hp_axi_s_awlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awlen),
  .i_hp_axi_s_awsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awsize),
  .i_hp_axi_s_awburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awburst),
  .i_hp_axi_s_awcache (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awcache),
  .i_hp_axi_s_awprot (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awprot),
  .i_hp_axi_s_awlock (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_awlock),
  .o_hp_axi_s_awready (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_awready),
  .i_hp_axi_s_wvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wvalid),
  .i_hp_axi_s_wlast (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wlast),
  .i_hp_axi_s_wstrb (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wstrb),
  .i_hp_axi_s_wdata (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_wdata),
  .o_hp_axi_s_wready (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_wready),
  .o_hp_axi_s_bvalid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bvalid),
  .o_hp_axi_s_bid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bid),
  .o_hp_axi_s_bresp (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_bresp),
  .i_hp_axi_s_bready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_bready),
  .i_hp_axi_s_arvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arvalid),
  .i_hp_axi_s_araddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_araddr),
  .i_hp_axi_s_arid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arid),
  .i_hp_axi_s_arlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arlen),
  .i_hp_axi_s_arsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arsize),
  .i_hp_axi_s_arburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arburst),
  .i_hp_axi_s_arcache (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arcache),
  .i_hp_axi_s_arprot (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arprot),
  .i_hp_axi_s_arlock (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_arlock),
  .o_hp_axi_s_arready (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_arready),
  .o_hp_axi_s_rvalid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rvalid),
  .o_hp_axi_s_rlast (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rlast),
  .o_hp_axi_s_rid (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rid),
  .o_hp_axi_s_rdata (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rdata),
  .o_hp_axi_s_rresp (u_aic_ls_p_to_u_aic_infra_p__o_hp_axi_s_rresp),
  .i_hp_axi_s_rready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_ht_axi_m_rready),
  .i_cfg_axi_s_awvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awvalid),
  .i_cfg_axi_s_awaddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awaddr),
  .i_cfg_axi_s_awid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awid),
  .i_cfg_axi_s_awlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awlen),
  .i_cfg_axi_s_awsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awsize),
  .i_cfg_axi_s_awburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_awburst),
  .o_cfg_axi_s_awready (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_awready),
  .i_cfg_axi_s_wvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wvalid),
  .i_cfg_axi_s_wlast (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wlast),
  .i_cfg_axi_s_wstrb (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wstrb),
  .i_cfg_axi_s_wdata (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_wdata),
  .o_cfg_axi_s_wready (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_wready),
  .o_cfg_axi_s_bvalid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bvalid),
  .o_cfg_axi_s_bid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bid),
  .o_cfg_axi_s_bresp (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_bresp),
  .i_cfg_axi_s_bready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_bready),
  .i_cfg_axi_s_arvalid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arvalid),
  .i_cfg_axi_s_araddr (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_araddr),
  .i_cfg_axi_s_arid (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arid),
  .i_cfg_axi_s_arlen (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arlen),
  .i_cfg_axi_s_arsize (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arsize),
  .i_cfg_axi_s_arburst (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_arburst),
  .o_cfg_axi_s_arready (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_arready),
  .o_cfg_axi_s_rvalid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rvalid),
  .o_cfg_axi_s_rlast (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rlast),
  .o_cfg_axi_s_rid (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rid),
  .o_cfg_axi_s_rdata (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rdata),
  .o_cfg_axi_s_rresp (u_aic_ls_p_to_u_aic_infra_p__o_cfg_axi_s_rresp),
  .i_cfg_axi_s_rready (u_aic_infra_p_to_u_aic_ls_p__o_dmc_l1_lt_axi_m_rready),
  .i_cid (i_cid),
  .o_dmc_obs (u_aic_ls_p_to_u_aic_infra_p__o_dmc_obs),
  .i_mid_mvm_exe_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_tok_prod_vld),
  .o_mid_mvm_exe_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_exe_tok_prod_rdy),
  .o_mid_mvm_exe_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_exe_tok_cons_vld),
  .i_mid_mvm_exe_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_tok_cons_rdy),
  .o_mid_mvm_exe_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_tok_prod_vld),
  .i_mid_mvm_exe_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_mvm_exe_tok_prod_rdy),
  .i_mid_mvm_exe_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_mvm_exe_tok_cons_vld),
  .o_mid_mvm_exe_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_tok_cons_rdy),
  .i_mid_mvm_prg_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_tok_prod_vld),
  .o_mid_mvm_prg_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_prg_tok_prod_rdy),
  .o_mid_mvm_prg_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_prg_tok_cons_vld),
  .i_mid_mvm_prg_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_tok_cons_rdy),
  .o_mid_mvm_prg_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_tok_prod_vld),
  .i_mid_mvm_prg_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_mvm_prg_tok_prod_rdy),
  .i_mid_mvm_prg_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_mvm_prg_tok_cons_vld),
  .o_mid_mvm_prg_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_tok_cons_rdy),
  .i_mid_iau_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_m_iau_tok_prod_vld),
  .o_mid_iau_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_iau_tok_prod_rdy),
  .o_mid_iau_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_iau_tok_cons_vld),
  .i_mid_iau_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_m_iau_tok_cons_rdy),
  .o_mid_iau_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_tok_prod_vld),
  .i_mid_iau_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_iau_tok_prod_rdy),
  .i_mid_iau_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_iau_tok_cons_vld),
  .o_mid_iau_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_tok_cons_rdy),
  .i_mid_dpu_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_tok_prod_vld),
  .o_mid_dpu_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_dpu_tok_prod_rdy),
  .o_mid_dpu_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_dpu_tok_cons_vld),
  .i_mid_dpu_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_tok_cons_rdy),
  .o_mid_dpu_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_tok_prod_vld),
  .i_mid_dpu_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_m_dpu_tok_prod_rdy),
  .i_mid_dpu_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_m_dpu_tok_cons_vld),
  .o_mid_dpu_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_tok_cons_rdy),
  .i_mid_irq (u_aic_mid_p_to_u_aic_ls_p__o_irq),
  .o_mid_irq (u_aic_ls_p_to_u_aic_infra_p__o_mid_irq),
  .i_mid_mvm_exe_obs (u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_obs),
  .i_mid_mvm_prg_obs (u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_obs),
  .i_mid_iau_obs (u_aic_mid_p_to_u_aic_ls_p__o_m_iau_obs),
  .i_mid_dpu_obs (u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_obs),
  .i_mid_tu_obs (u_aic_mid_p_to_u_aic_ls_p__o_tu_obs),
  .o_mid_mvm_exe_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_exe_obs),
  .o_mid_mvm_prg_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_mvm_prg_obs),
  .o_mid_iau_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_iau_obs),
  .o_mid_dpu_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_dpu_obs),
  .o_mid_tu_obs (u_aic_ls_p_to_u_aic_infra_p__o_mid_tu_obs),
  .i_mid_ts_start (u_aic_mid_p_to_u_aic_ls_p__o_ts_start),
  .i_mid_ts_end (u_aic_mid_p_to_u_aic_ls_p__o_ts_end),
  .i_mid_acd_sync (u_aic_mid_p_to_u_aic_ls_p__o_acd_sync),
  .o_mid_ts_start (u_aic_ls_p_to_u_aic_infra_p__o_mid_ts_start),
  .o_mid_ts_end (u_aic_ls_p_to_u_aic_infra_p__o_mid_ts_end),
  .o_mid_acd_sync (u_aic_ls_p_to_u_aic_infra_p__o_mid_acd_sync),
  .i_did_dwpu_tok_prod_vld (u_aic_did_p_to_u_aic_ls_p__o_dwpu_tok_prod_vld),
  .o_did_dwpu_tok_prod_rdy (u_aic_ls_p_to_u_aic_did_p__o_did_dwpu_tok_prod_rdy),
  .o_did_dwpu_tok_cons_vld (u_aic_ls_p_to_u_aic_did_p__o_did_dwpu_tok_cons_vld),
  .i_did_dwpu_tok_cons_rdy (u_aic_did_p_to_u_aic_ls_p__o_dwpu_tok_cons_rdy),
  .o_did_dwpu_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_tok_prod_vld),
  .i_did_dwpu_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_dwpu_tok_prod_rdy),
  .i_did_dwpu_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_dwpu_tok_cons_vld),
  .o_did_dwpu_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_tok_cons_rdy),
  .i_did_iau_tok_prod_vld (u_aic_did_p_to_u_aic_ls_p__o_iau_tok_prod_vld),
  .o_did_iau_tok_prod_rdy (u_aic_ls_p_to_u_aic_did_p__o_did_iau_tok_prod_rdy),
  .o_did_iau_tok_cons_vld (u_aic_ls_p_to_u_aic_did_p__o_did_iau_tok_cons_vld),
  .i_did_iau_tok_cons_rdy (u_aic_did_p_to_u_aic_ls_p__o_iau_tok_cons_rdy),
  .o_did_iau_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_did_iau_tok_prod_vld),
  .i_did_iau_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_iau_tok_prod_rdy),
  .i_did_iau_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_iau_tok_cons_vld),
  .o_did_iau_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_did_iau_tok_cons_rdy),
  .i_did_dpu_tok_prod_vld (u_aic_did_p_to_u_aic_ls_p__o_dpu_tok_prod_vld),
  .o_did_dpu_tok_prod_rdy (u_aic_ls_p_to_u_aic_did_p__o_did_dpu_tok_prod_rdy),
  .o_did_dpu_tok_cons_vld (u_aic_ls_p_to_u_aic_did_p__o_did_dpu_tok_cons_vld),
  .i_did_dpu_tok_cons_rdy (u_aic_did_p_to_u_aic_ls_p__o_dpu_tok_cons_rdy),
  .o_did_dpu_tok_prod_vld (u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_tok_prod_vld),
  .i_did_dpu_tok_prod_rdy (u_aic_infra_p_to_u_aic_ls_p__o_d_dpu_tok_prod_rdy),
  .i_did_dpu_tok_cons_vld (u_aic_infra_p_to_u_aic_ls_p__o_d_dpu_tok_cons_vld),
  .o_did_dpu_tok_cons_rdy (u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_tok_cons_rdy),
  .i_did_irq (u_aic_did_p_to_u_aic_ls_p__o_irq),
  .o_did_irq (u_aic_ls_p_to_u_aic_infra_p__o_did_irq),
  .i_did_dwpu_obs (u_aic_did_p_to_u_aic_ls_p__o_dwpu_obs),
  .i_did_iau_obs (u_aic_did_p_to_u_aic_ls_p__o_iau_obs),
  .i_did_dpu_obs (u_aic_did_p_to_u_aic_ls_p__o_dpu_obs),
  .o_did_dwpu_obs (u_aic_ls_p_to_u_aic_infra_p__o_did_dwpu_obs),
  .o_did_iau_obs (u_aic_ls_p_to_u_aic_infra_p__o_did_iau_obs),
  .o_did_dpu_obs (u_aic_ls_p_to_u_aic_infra_p__o_did_dpu_obs),
  .i_did_ts_start (u_aic_did_p_to_u_aic_ls_p__o_ts_start),
  .i_did_ts_end (u_aic_did_p_to_u_aic_ls_p__o_ts_end),
  .i_did_acd_sync (u_aic_did_p_to_u_aic_ls_p__o_acd_sync),
  .o_did_ts_start (u_aic_ls_p_to_u_aic_infra_p__o_did_ts_start),
  .o_did_ts_end (u_aic_ls_p_to_u_aic_infra_p__o_did_ts_end),
  .o_did_acd_sync (u_aic_ls_p_to_u_aic_infra_p__o_did_acd_sync),
  .o_mid_cfg_axi_m_awvalid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awvalid),
  .o_mid_cfg_axi_m_awaddr (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awaddr),
  .o_mid_cfg_axi_m_awid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awid),
  .o_mid_cfg_axi_m_awlen (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awlen),
  .o_mid_cfg_axi_m_awsize (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awsize),
  .o_mid_cfg_axi_m_awburst (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awburst),
  .i_mid_cfg_axi_m_awready (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_awready),
  .o_mid_cfg_axi_m_wvalid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wvalid),
  .o_mid_cfg_axi_m_wlast (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wlast),
  .o_mid_cfg_axi_m_wstrb (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wstrb),
  .o_mid_cfg_axi_m_wdata (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wdata),
  .i_mid_cfg_axi_m_wready (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_wready),
  .i_mid_cfg_axi_m_bvalid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bvalid),
  .i_mid_cfg_axi_m_bid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bid),
  .i_mid_cfg_axi_m_bresp (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bresp),
  .o_mid_cfg_axi_m_bready (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_bready),
  .o_mid_cfg_axi_m_arvalid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arvalid),
  .o_mid_cfg_axi_m_araddr (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_araddr),
  .o_mid_cfg_axi_m_arid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arid),
  .o_mid_cfg_axi_m_arlen (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arlen),
  .o_mid_cfg_axi_m_arsize (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arsize),
  .o_mid_cfg_axi_m_arburst (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arburst),
  .i_mid_cfg_axi_m_arready (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_arready),
  .i_mid_cfg_axi_m_rvalid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rvalid),
  .i_mid_cfg_axi_m_rlast (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rlast),
  .i_mid_cfg_axi_m_rid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rid),
  .i_mid_cfg_axi_m_rdata (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rdata),
  .i_mid_cfg_axi_m_rresp (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rresp),
  .o_mid_cfg_axi_m_rready (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_rready),
  .o_did_cfg_axi_m_awvalid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awvalid),
  .o_did_cfg_axi_m_awaddr (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awaddr),
  .o_did_cfg_axi_m_awid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awid),
  .o_did_cfg_axi_m_awlen (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awlen),
  .o_did_cfg_axi_m_awsize (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awsize),
  .o_did_cfg_axi_m_awburst (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_awburst),
  .i_did_cfg_axi_m_awready (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_awready),
  .o_did_cfg_axi_m_wvalid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wvalid),
  .o_did_cfg_axi_m_wlast (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wlast),
  .o_did_cfg_axi_m_wstrb (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wstrb),
  .o_did_cfg_axi_m_wdata (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_wdata),
  .i_did_cfg_axi_m_wready (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_wready),
  .i_did_cfg_axi_m_bvalid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bvalid),
  .i_did_cfg_axi_m_bid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bid),
  .i_did_cfg_axi_m_bresp (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_bresp),
  .o_did_cfg_axi_m_bready (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_bready),
  .o_did_cfg_axi_m_arvalid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arvalid),
  .o_did_cfg_axi_m_araddr (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_araddr),
  .o_did_cfg_axi_m_arid (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arid),
  .o_did_cfg_axi_m_arlen (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arlen),
  .o_did_cfg_axi_m_arsize (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arsize),
  .o_did_cfg_axi_m_arburst (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_arburst),
  .i_did_cfg_axi_m_arready (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_arready),
  .i_did_cfg_axi_m_rvalid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rvalid),
  .i_did_cfg_axi_m_rlast (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rlast),
  .i_did_cfg_axi_m_rid (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rid),
  .i_did_cfg_axi_m_rdata (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rdata),
  .i_did_cfg_axi_m_rresp (u_aic_did_p_to_u_aic_ls_p__o_cfg_axi_s_rresp),
  .o_did_cfg_axi_m_rready (u_aic_ls_p_to_u_aic_did_p__o_did_cfg_axi_m_rready),
  .i_sram_mcs (i_sram_mcs),
  .i_sram_mcsw (i_sram_mcsw),
  .i_sram_ret (i_sram_ret),
  .i_sram_pde (u_aic_ls_p_to_u_aic_ls_p__o_rf_prn),
  .i_sram_adme (i_sram_adme),
  .o_sram_prn (u_aic_ls_p_to_u_aic_mid_p__o_sram_prn),
  .i_rf_mcs (i_sram_mcs),
  .i_rf_mcsw (i_sram_mcsw),
  .i_rf_ret (i_sram_ret),
  .i_rf_pde (u_aic_infra_p_to_u_aic_ls_p__o_sram_prn),
  .i_rf_adme (i_sram_adme),
  .o_rf_prn (u_aic_ls_p_to_u_aic_ls_p__o_rf_prn),
  .ijtag_tck ('0),
  .ijtag_reset ('0),
  .ijtag_sel ('0),
  .ijtag_ue ('0),
  .ijtag_se ('0),
  .ijtag_ce ('0),
  .ijtag_si ('0),
  .ijtag_so (),
  .test_clk ('0),
  .test_mode (i_test_mode),
  .edt_update ('0),
  .scan_en (scan_en),
  .scan_in ('0),
  .scan_out (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so ()
);
aic_mid_p u_aic_mid_p (
  .i_clk (i_clk),
  .i_rst_n (i_rst_n),
  .i_ref_clk (i_ref_clk),
  .i_ref_rst_n (i_ref_rst_n),
  .i_c2c_clk (i_c2c_clk),
  .o_imc_bist_fast_clk_en (),
  .o_mvm_exe_obs (u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_obs),
  .o_mvm_prg_obs (u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_obs),
  .o_m_iau_obs (u_aic_mid_p_to_u_aic_ls_p__o_m_iau_obs),
  .o_m_dpu_obs (u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_obs),
  .o_tu_obs (u_aic_mid_p_to_u_aic_ls_p__o_tu_obs),
  .i_aic_throttle_async (i_aic_throttle_async),
  .i_thermal_throttle_async (i_thermal_throttle_async),
  .o_mvm_throttle_async (o_mvm_throttle_async),
  .i_aic_boost_ack_async (i_aic_boost_ack_async),
  .o_aic_boost_req_async (o_aic_boost_req_async),
  .io_ibias_ts (io_ibias_ts),
  .io_vsense_ts (io_vsense_ts),
  .o_ts_start (u_aic_mid_p_to_u_aic_ls_p__o_ts_start),
  .o_ts_end (u_aic_mid_p_to_u_aic_ls_p__o_ts_end),
  .o_acd_sync (u_aic_mid_p_to_u_aic_ls_p__o_acd_sync),
  .o_irq (u_aic_mid_p_to_u_aic_ls_p__o_irq),
  .o_mvm_exe_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_tok_prod_vld),
  .i_mvm_exe_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_exe_tok_prod_rdy),
  .i_mvm_exe_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_exe_tok_cons_vld),
  .o_mvm_exe_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_mvm_exe_tok_cons_rdy),
  .o_mvm_prg_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_tok_prod_vld),
  .i_mvm_prg_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_prg_tok_prod_rdy),
  .i_mvm_prg_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_mvm_prg_tok_cons_vld),
  .o_mvm_prg_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_mvm_prg_tok_cons_rdy),
  .o_m_iau_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_m_iau_tok_prod_vld),
  .i_m_iau_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_iau_tok_prod_rdy),
  .i_m_iau_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_iau_tok_cons_vld),
  .o_m_iau_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_m_iau_tok_cons_rdy),
  .o_m_dpu_tok_prod_vld (u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_tok_prod_vld),
  .i_m_dpu_tok_prod_rdy (u_aic_ls_p_to_u_aic_mid_p__o_mid_dpu_tok_prod_rdy),
  .i_m_dpu_tok_cons_vld (u_aic_ls_p_to_u_aic_mid_p__o_mid_dpu_tok_cons_vld),
  .o_m_dpu_tok_cons_rdy (u_aic_mid_p_to_u_aic_ls_p__o_m_dpu_tok_cons_rdy),
  .i_cfg_s_awvalid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awvalid),
  .i_cfg_s_awaddr (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awaddr),
  .i_cfg_s_awid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awid),
  .i_cfg_s_awlen (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awlen),
  .i_cfg_s_awsize (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awsize),
  .i_cfg_s_awburst (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_awburst),
  .o_cfg_s_awready (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_awready),
  .i_cfg_s_wvalid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wvalid),
  .i_cfg_s_wlast (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wlast),
  .i_cfg_s_wstrb (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wstrb),
  .i_cfg_s_wdata (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_wdata),
  .o_cfg_s_wready (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_wready),
  .o_cfg_s_bvalid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bvalid),
  .o_cfg_s_bid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bid),
  .o_cfg_s_bresp (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_bresp),
  .i_cfg_s_bready (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_bready),
  .i_cfg_s_arvalid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arvalid),
  .i_cfg_s_araddr (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_araddr),
  .i_cfg_s_arid (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arid),
  .i_cfg_s_arlen (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arlen),
  .i_cfg_s_arsize (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arsize),
  .i_cfg_s_arburst (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_arburst),
  .o_cfg_s_arready (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_arready),
  .o_cfg_s_rvalid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rvalid),
  .o_cfg_s_rlast (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rlast),
  .o_cfg_s_rid (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rid),
  .o_cfg_s_rdata (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rdata),
  .o_cfg_s_rresp (u_aic_mid_p_to_u_aic_ls_p__o_cfg_s_rresp),
  .i_cfg_s_rready (u_aic_ls_p_to_u_aic_mid_p__o_mid_cfg_axi_m_rready),
  .i_m_ifdw_axis_s_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tvalid),
  .o_m_ifdw_axis_s_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifdw_axis_s_tready),
  .i_m_ifdw_axis_s_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tdata),
  .i_m_ifdw_axis_s_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifdw_axis_m_tlast),
  .i_m_ifd0_axis_s_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tvalid),
  .o_m_ifd0_axis_s_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifd0_axis_s_tready),
  .i_m_ifd0_axis_s_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tdata),
  .i_m_ifd0_axis_s_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd0_axis_m_tlast),
  .i_m_ifd1_axis_s_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tvalid),
  .o_m_ifd1_axis_s_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifd1_axis_s_tready),
  .i_m_ifd1_axis_s_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tdata),
  .i_m_ifd1_axis_s_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd1_axis_m_tlast),
  .i_m_ifd2_axis_s_tvalid (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tvalid),
  .o_m_ifd2_axis_s_tready (u_aic_mid_p_to_u_aic_ls_p__o_m_ifd2_axis_s_tready),
  .i_m_ifd2_axis_s_tdata (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tdata),
  .i_m_ifd2_axis_s_tlast (u_aic_ls_p_to_u_aic_mid_p__o_m_ifd2_axis_m_tlast),
  .o_m_odr_axis_m_tvalid (u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tvalid),
  .i_m_odr_axis_m_tready (u_aic_ls_p_to_u_aic_mid_p__o_m_odr_axis_s_tready),
  .o_m_odr_axis_m_tdata (u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tdata),
  .o_m_odr_axis_m_tlast (u_aic_mid_p_to_u_aic_ls_p__o_m_odr_axis_m_tlast),
  .i_cid (i_cid),
  .o_imc_bist_busy (o_imc_bist_busy_async),
  .o_imc_bist_done (o_imc_bist_done_async),
  .o_imc_bist_pass (o_imc_bist_pass_async),
  .i_sram_mcs (i_sram_mcs),
  .i_sram_mcsw (i_sram_mcsw),
  .i_sram_ret (i_sram_ret),
  .i_sram_pde (u_aic_ls_p_to_u_aic_mid_p__o_sram_prn),
  .i_sram_adme (i_sram_adme),
  .o_sram_prn (u_aic_mid_p_to_u_aic_did_p__o_sram_prn),
  .ijtag_tck (i_clk),
  .ijtag_reset (1'b1),
  .ijtag_sel ('0),
  .ijtag_ue ('0),
  .ijtag_se ('0),
  .ijtag_ce ('0),
  .ijtag_si ('0),
  .ijtag_so (),
  .bisr_clk ('0),
  .bisr_reset ('0),
  .bisr_shift_en ('0),
  .bisr_si ('0),
  .bisr_so (),
  .imc_bisr_clk ('0),
  .imc_bisr_reset ('0),
  .imc_bisr_shift_en ('0),
  .imc_bisr_si ('0),
  .imc_bisr_so (),
  .test_clk ('0),
  .test_mode (i_test_mode),
  .edt_update ('0),
  .scan_en (scan_en),
  .scan_in ('0),
  .scan_out ()
);


endmodule
`endif  // AI_CORE_SV
