// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Synthesis wrapper for DWPU for SF%A
///
module dwpu_synth_sf5a (
  input wire i_clk,
  input wire i_rst_n,

  input  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_axi_s_aw_id,
  input  logic [aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] i_axi_s_aw_addr,
  input  axi_pkg::axi_len_t                                      i_axi_s_aw_len,
  input  axi_pkg::axi_size_t                                     i_axi_s_aw_size,
  input  axi_pkg::axi_burst_t                                    i_axi_s_aw_burst,
  input  logic                                                   i_axi_s_aw_valid,
  output logic                                                   o_axi_s_aw_ready,

  input  logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] i_axi_s_w_data,
  input  logic [     aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH-1:0] i_axi_s_w_strb,
  input  logic                                                   i_axi_s_w_last,
  input  logic                                                   i_axi_s_w_valid,
  output logic                                                   o_axi_s_w_ready,

  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_axi_s_b_id,
  output axi_pkg::axi_resp_t                                     o_axi_s_b_resp,
  output logic                                                   o_axi_s_b_valid,
  input  logic                                                   i_axi_s_b_ready,

  input  logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] i_axi_s_ar_id,
  input  logic [aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] i_axi_s_ar_addr,
  input  axi_pkg::axi_len_t                                      i_axi_s_ar_len,
  input  axi_pkg::axi_size_t                                     i_axi_s_ar_size,
  input  axi_pkg::axi_burst_t                                    i_axi_s_ar_burst,
  input  logic                                                   i_axi_s_ar_valid,
  output logic                                                   o_axi_s_ar_ready,

  output logic [      aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH-1:0] o_axi_s_r_id,
  output logic [      aic_common_pkg::AIC_LT_AXI_DATA_WIDTH-1:0] o_axi_s_r_data,
  output axi_pkg::axi_resp_t      o_axi_s_r_resp,
  output logic                    o_axi_s_r_last,
  output logic                    o_axi_s_r_valid,
  input  logic                    i_axi_s_r_ready,

  output wire [token_mgr_mapping_aic_pkg::TOK_MGR_DWPU_NR_TOK_PROD-1:0] o_tok_prod_valid,
  input  wire [token_mgr_mapping_aic_pkg::TOK_MGR_DWPU_NR_TOK_PROD-1:0] i_tok_prod_ready,
  input  wire [token_mgr_mapping_aic_pkg::TOK_MGR_DWPU_NR_TOK_CONS-1:0]     i_tok_cons_valid,
  output wire [token_mgr_mapping_aic_pkg::TOK_MGR_DWPU_NR_TOK_CONS-1:0]     o_tok_cons_ready,

  input  logic [aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_axis_s_tdata,
  input  logic                        i_axis_s_tlast,
  input  logic                        i_axis_s_tvalid,
  output logic                        o_axis_s_tready,

  output logic [aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0]  o_axis_m_tdata,
  output logic                         o_axis_m_tlast,
  output logic                         o_axis_m_tvalid,
  input  logic                         i_axis_m_tready,

  output logic o_irq,

  output logic [aic_common_pkg::AIC_DWPU_OBS_DW-1:0] o_obs,

  input logic [     aic_common_pkg::AIC_CID_SUB_W-1:0]  i_cid,
  input logic [aic_common_pkg::AIC_BLOCK_ID_WIDTH-1:0]  i_block_id,

  input  logic [1:0] i_mcs,
  input  logic       i_mcsw,
  input  logic       i_ret,
  input  logic       i_pde,
  input  logic       i_se,
  input  logic [2:0] i_adme,

  output  logic      o_prn
);

  axe_tcl_sram_pkg::impl_inp_t dp_cmd_gen_sram_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t dp_cmd_gen_sram_impl_oup;

  always_comb dp_cmd_gen_sram_impl_inp = '{
    mcs:     i_mcs,
    mcsw:    i_mcsw,
    ret:     i_ret,
    pde:     i_pde,
    se:      i_se,
    adme:    i_adme,
    default: '0
  };
  always_comb o_prn = dp_cmd_gen_sram_impl_oup.prn;


  dwpu #(
    .AxiIdWidth      (aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH),
    .AxiAddrWidth    (aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH),
    .AxiDataWidth    (aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
    .AxiStrbWidth    (aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH),
    .NumTokenProd    (token_mgr_mapping_aic_pkg::TOK_MGR_DWPU_NR_TOK_PROD),
    .NumTokenCons    (token_mgr_mapping_aic_pkg::TOK_MGR_DWPU_NR_TOK_CONS),
    .InpAxisDataWidth(aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH),
    .OupAxisDataWidth(aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH),
    .ObserveWidth    (aic_common_pkg::AIC_DWPU_OBS_DW),
    .PerfDataWidth   (perf_tracker_pkg::PERF_DATA_W),
    .PerfCntrWidth   (perf_tracker_pkg::PERF_CNTR_W),
    .CIdWidth        (aic_common_pkg::AIC_CID_SUB_W),
    .BlockIdWidth    (aic_common_pkg::AIC_BLOCK_ID_WIDTH),
    .sram_impl_inp_t (axe_tcl_sram_pkg::impl_inp_t),
    .sram_impl_oup_t (axe_tcl_sram_pkg::impl_oup_t)
  ) u_dwpu (
    .i_clk,
    .i_rst_n,

    .i_axi_s_aw_id,
    .i_axi_s_aw_addr,
    .i_axi_s_aw_len,
    .i_axi_s_aw_size,
    .i_axi_s_aw_burst,
    .i_axi_s_aw_valid,
    .o_axi_s_aw_ready,

    .i_axi_s_w_data,
    .i_axi_s_w_strb,
    .i_axi_s_w_last,
    .i_axi_s_w_valid,
    .o_axi_s_w_ready,

    .o_axi_s_b_id,
    .o_axi_s_b_resp,
    .o_axi_s_b_valid,
    .i_axi_s_b_ready,

    .i_axi_s_ar_id,
    .i_axi_s_ar_addr,
    .i_axi_s_ar_len,
    .i_axi_s_ar_size,
    .i_axi_s_ar_burst,
    .i_axi_s_ar_valid,
    .o_axi_s_ar_ready,

    .o_axi_s_r_id,
    .o_axi_s_r_data,
    .o_axi_s_r_resp,
    .o_axi_s_r_last,
    .o_axi_s_r_valid,
    .i_axi_s_r_ready,

    .o_tok_prod_valid,
    .i_tok_prod_ready,
    .i_tok_cons_valid,
    .o_tok_cons_ready,

    .i_axis_s_tdata,
    .i_axis_s_tlast,
    .i_axis_s_tvalid,
    .o_axis_s_tready,

    .o_axis_m_tdata,
    .o_axis_m_tlast,
    .o_axis_m_tvalid,
    .i_axis_m_tready,

    .o_irq,

    .o_obs,

    .i_cid,
    .i_block_id,

    .i_dp_cmd_gen_sram_impl(dp_cmd_gen_sram_impl_inp),
    .o_dp_cmd_gen_sram_impl(dp_cmd_gen_sram_impl_oup)
  );

endmodule
