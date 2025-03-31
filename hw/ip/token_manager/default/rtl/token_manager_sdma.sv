// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: SDMA token manager, for top and local network
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module token_manager_sdma #(
  /// Configuration
  localparam token_manager_pkg::tokmgr_cfg_t TopCfg = token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG
)(
  input  wire i_clk,
  input  wire i_rst_n,

  // top info:
  input  logic i_sdma_nr,
  // UID - VUID:
  input  token_manager_pkg::tokmgr_uid_all_t i_uid_to_vuid,
  // VUID - UID:
  input  token_manager_pkg::tokmgr_uid_all_t i_vuid_to_uid,

  // Top connection via OCPL:
  output logic [7:0]  o_tok_prod_ocpl_m_maddr,
  output logic        o_tok_prod_ocpl_m_mcmd,
  input  logic        i_tok_prod_ocpl_m_scmdaccept,
  output logic [7:0]  o_tok_prod_ocpl_m_mdata,

  input  logic [7:0]  i_tok_cons_ocpl_s_maddr,
  input  logic        i_tok_cons_ocpl_s_mcmd,
  output logic        o_tok_cons_ocpl_s_scmdaccept,
  input  logic [7:0]  i_tok_cons_ocpl_s_mdata,

    // local connections for top:
  input  logic [TopCfg.max_num_prod-1:0] i_top_prod_valid[TopCfg.nr_loc_devs],
  output logic [TopCfg.max_num_prod-1:0] o_top_prod_ready[TopCfg.nr_loc_devs],

  output logic [TopCfg.max_num_cons-1:0] o_top_cons_valid[TopCfg.nr_loc_devs],
  input  logic [TopCfg.max_num_cons-1:0] i_top_cons_ready[TopCfg.nr_loc_devs],

  ///// AXI slave:
  // Write Address Channel
  input  token_manager_sdma_csr_reg_pkg::axi_a_ch_h2d_t  i_axi_s_aw,
  output logic                                          o_axi_s_aw_ready,
  // Write  Data Channel
  input  token_manager_sdma_csr_reg_pkg::axi_w_ch_h2d_t  i_axi_s_w,
  output logic                                          o_axi_s_w_ready,
  // Write Response Channel
  output token_manager_sdma_csr_reg_pkg::axi_b_ch_d2h_t  o_axi_s_b,
  input  logic                                          i_axi_s_b_ready,
  // Read Address Channel
  input  token_manager_sdma_csr_reg_pkg::axi_a_ch_h2d_t  i_axi_s_ar,
  output logic                                          o_axi_s_ar_ready,
  // Read Data Channel
  output token_manager_sdma_csr_reg_pkg::axi_r_ch_d2h_t  o_axi_s_r,
  input  logic                                          i_axi_s_r_ready,

  // interrupt:
  output logic o_irq
);

  token_manager_sdma_csr_reg_pkg::token_manager_sdma_csr_hw2reg_t csr_hw2reg;
  token_manager_sdma_csr_reg_pkg::token_manager_sdma_csr_reg2hw_t csr_reg2hw;

  logic [TopCfg.nr_loc_devs-1:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] dev_id;

  always_comb begin
    for (int i=0;i<TopCfg.nr_loc_devs;i++) begin
      dev_id[i][token_manager_pkg::TOKEN_MANAGER_UID_W-1 : 2] = (i_sdma_nr ? 'd10 : 'd9);
      dev_id[i][1:0] = token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_DEV_ID[i][1:0];
    end
  end

  token_manager_sdma_csr_reg_top u_csr (
    .clk_i(i_clk),
    .rst_ni(i_rst_n),
    .axi_aw_i(i_axi_s_aw),
    .axi_awready(o_axi_s_aw_ready),
    .axi_ar_i(i_axi_s_ar),
    .axi_arready(o_axi_s_ar_ready),
    .axi_w_i(i_axi_s_w),
    .axi_wready(o_axi_s_w_ready),
    .axi_b_o(o_axi_s_b),
    .axi_bready(i_axi_s_b_ready),
    .axi_r_o(o_axi_s_r),
    .axi_rready(i_axi_s_r_ready),
    // To HW
    .reg2hw(csr_reg2hw),
    .hw2reg(csr_hw2reg),
    // Config
    .devmode_i(1'b1)
  );

  token_manager_top #(
    /// Configuration
    .TopCfg(token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CFG),

    .TopDevIds(token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_DEV_ID),
    .TopDevTokensProd(token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_DEV_PROD_WIDTH),
    .TopDevTokensCons(token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_DEV_CONS_WIDTH),
    .TopMapProdToDev(token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_PROD_TO_DEV),
    .TopMapConsToDev(token_mgr_mapping_sdma_pkg::TOK_MGR_TOP_CONS_TO_DEV),

    .csr_reg2hw_t(token_manager_sdma_csr_reg_pkg::token_manager_sdma_csr_reg2hw_t),
    .csr_hw2reg_t(token_manager_sdma_csr_reg_pkg::token_manager_sdma_csr_hw2reg_t),
    .TOK_MAN_CSR_INFO(token_mgr_mapping_sdma_pkg::TOP_TOK_MAN_CSR_INFO)
  ) u_tok_mgr_top (
    .i_clk,
    .i_rst_n,

      // local connections for top:
    .i_top_prod_valid,
    .o_top_prod_ready,

    .o_top_cons_valid,
    .i_top_cons_ready,

    // Top info
    .i_dev_id(dev_id),
    .i_vuid_to_uid,
    .i_uid_to_vuid,

    // Top connection via OCPL:
    .o_tok_prod_ocpl_m_maddr,
    .o_tok_prod_ocpl_m_mcmd,
    .i_tok_prod_ocpl_m_scmdaccept,
    .o_tok_prod_ocpl_m_mdata,

    .i_tok_cons_ocpl_s_maddr,
    .i_tok_cons_ocpl_s_mcmd,
    .o_tok_cons_ocpl_s_scmdaccept,
    .i_tok_cons_ocpl_s_mdata,

    ///// CSR connection subordinate:
    .i_csr_reg2hw(csr_reg2hw),
    .o_csr_hw2reg(csr_hw2reg),

    // interrupt:
    .o_irq
  );

endmodule
