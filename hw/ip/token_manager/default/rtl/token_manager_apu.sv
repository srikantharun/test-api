// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: APU token manager, for top network and SWEP only
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module token_manager_apu #(
  /// Configuration
  localparam token_manager_pkg::tokmgr_cfg_t TopCfg = token_mgr_mapping_apu_pkg::TOK_MGR_TOP_CFG
)(
  input  wire i_clk,
  input  wire i_rst_n,

  // Top connection via OCPL:
  output logic [7:0]  o_tok_prod_ocpl_m_maddr,
  output logic        o_tok_prod_ocpl_m_mcmd,
  input  logic        i_tok_prod_ocpl_m_scmdaccept,
  output logic [7:0]  o_tok_prod_ocpl_m_mdata,

  input  logic [7:0]  i_tok_cons_ocpl_s_maddr,
  input  logic        i_tok_cons_ocpl_s_mcmd,
  output logic        o_tok_cons_ocpl_s_scmdaccept,
  input  logic [7:0]  i_tok_cons_ocpl_s_mdata,

  ///// AXI slave:
  // Write Address Channel
  input  token_manager_apu_csr_reg_pkg::axi_a_ch_h2d_t  i_axi_s_aw,
  output logic                                          o_axi_s_aw_ready,
  // Write  Data Channel
  input  token_manager_apu_csr_reg_pkg::axi_w_ch_h2d_t  i_axi_s_w,
  output logic                                          o_axi_s_w_ready,
  // Write Response Channel
  output token_manager_apu_csr_reg_pkg::axi_b_ch_d2h_t  o_axi_s_b,
  input  logic                                          i_axi_s_b_ready,
  // Read Address Channel
  input  token_manager_apu_csr_reg_pkg::axi_a_ch_h2d_t  i_axi_s_ar,
  output logic                                          o_axi_s_ar_ready,
  // Read Data Channel
  output token_manager_apu_csr_reg_pkg::axi_r_ch_d2h_t  o_axi_s_r,
  input  logic                                          i_axi_s_r_ready,

  // interrupt:
  output logic o_irq
);

  token_manager_apu_csr_reg_pkg::token_manager_apu_csr_hw2reg_t csr_hw2reg;
  token_manager_apu_csr_reg_pkg::token_manager_apu_csr_reg2hw_t csr_reg2hw;

  token_manager_pkg::tokmgr_uid_all_t fixed_uid_vuid;

  always_comb begin
    fixed_uid_vuid = '0; //default off, others to fixed value to make sure 1:1 translation is happening
    fixed_uid_vuid.aic0.acd     = token_manager_pkg::tokmgr_uid_t'('d4);
    fixed_uid_vuid.aic0.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d5);
    fixed_uid_vuid.aic0.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d6);
    fixed_uid_vuid.aic1.acd     = token_manager_pkg::tokmgr_uid_t'('d8);
    fixed_uid_vuid.aic1.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d9);
    fixed_uid_vuid.aic1.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d10);
    fixed_uid_vuid.aic2.acd     = token_manager_pkg::tokmgr_uid_t'('d12);
    fixed_uid_vuid.aic2.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d13);
    fixed_uid_vuid.aic2.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d14);
    fixed_uid_vuid.aic3.acd     = token_manager_pkg::tokmgr_uid_t'('d16);
    fixed_uid_vuid.aic3.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d17);
    fixed_uid_vuid.aic3.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d18);
    fixed_uid_vuid.aic4.acd     = token_manager_pkg::tokmgr_uid_t'('d20);
    fixed_uid_vuid.aic4.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d21);
    fixed_uid_vuid.aic4.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d22);
    fixed_uid_vuid.aic5.acd     = token_manager_pkg::tokmgr_uid_t'('d24);
    fixed_uid_vuid.aic5.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d25);
    fixed_uid_vuid.aic5.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d26);
    fixed_uid_vuid.aic6.acd     = token_manager_pkg::tokmgr_uid_t'('d28);
    fixed_uid_vuid.aic6.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d29);
    fixed_uid_vuid.aic6.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d30);
    fixed_uid_vuid.aic7.acd     = token_manager_pkg::tokmgr_uid_t'('d32);
    fixed_uid_vuid.aic7.dma_ch0 = token_manager_pkg::tokmgr_uid_t'('d33);
    fixed_uid_vuid.aic7.dma_ch1 = token_manager_pkg::tokmgr_uid_t'('d34);
    fixed_uid_vuid.sdma0.ch0    = token_manager_pkg::tokmgr_uid_t'('d36);
    fixed_uid_vuid.sdma0.ch1    = token_manager_pkg::tokmgr_uid_t'('d37);
    fixed_uid_vuid.sdma0.ch2    = token_manager_pkg::tokmgr_uid_t'('d38);
    fixed_uid_vuid.sdma0.ch3    = token_manager_pkg::tokmgr_uid_t'('d39);
    fixed_uid_vuid.sdma1.ch0    = token_manager_pkg::tokmgr_uid_t'('d40);
    fixed_uid_vuid.sdma1.ch1    = token_manager_pkg::tokmgr_uid_t'('d41);
    fixed_uid_vuid.sdma1.ch2    = token_manager_pkg::tokmgr_uid_t'('d42);
    fixed_uid_vuid.sdma1.ch3    = token_manager_pkg::tokmgr_uid_t'('d43);
    fixed_uid_vuid.apu          = token_manager_pkg::tokmgr_uid_t'('d44);
  end

  token_manager_apu_csr_reg_top u_csr (
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
    .TopCfg(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_CFG),

    .TopDevIds(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_DEV_ID),
    .TopDevTokensProd(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_DEV_PROD_WIDTH),
    .TopDevTokensCons(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_DEV_CONS_WIDTH),
    .TopMapProdToDev(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_PROD_TO_DEV),
    .TopMapConsToDev(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_CONS_TO_DEV),

    .csr_reg2hw_t(token_manager_apu_csr_reg_pkg::token_manager_apu_csr_reg2hw_t),
    .csr_hw2reg_t(token_manager_apu_csr_reg_pkg::token_manager_apu_csr_hw2reg_t),
    .TOK_MAN_CSR_INFO(token_mgr_mapping_apu_pkg::TOP_TOK_MAN_CSR_INFO)
  ) u_tok_mgr_top (
    .i_clk,
    .i_rst_n,

      // local connections for top:
    .i_top_prod_valid('{default: 0}),
    .o_top_prod_ready(), // ASO-UNUSED_OUTPUT: Not used in this config

    .o_top_cons_valid(), // ASO-UNUSED_OUTPUT: Not used in this config
    .i_top_cons_ready('{default: 0}),

    // Top info
    .i_dev_id(token_manager_pkg::TOKEN_MANAGER_UID_W'(token_mgr_mapping_apu_pkg::TOK_MGR_TOP_DEV_ID[0])),
    .i_vuid_to_uid(fixed_uid_vuid),
    .i_uid_to_vuid(fixed_uid_vuid),

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
