// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AIC token manager, for top and local network
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module token_manager_aic #(
  /// Configuration
  localparam token_manager_pkg::tokmgr_cfg_t LocCfg = token_mgr_mapping_aic_pkg::TOK_MGR_CFG,
  localparam token_manager_pkg::tokmgr_cfg_t TopCfg = token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG
)(
  input  wire i_clk,
  input  wire i_rst_n,

  input  logic i_sync_mvm_exe_swep_en,
  input  logic i_sync_mvm_exe_swep,

  // token interface:
  input  logic i_swep_is_acd,
  input  logic [LocCfg.max_num_prod-1:0] i_dev_prod_valid[LocCfg.nr_loc_devs],
  output logic [LocCfg.max_num_prod-1:0] o_dev_prod_ready[LocCfg.nr_loc_devs],

  output logic [LocCfg.max_num_cons-1:0] o_dev_cons_valid[LocCfg.nr_loc_devs],
  input  logic [LocCfg.max_num_cons-1:0] i_dev_cons_ready[LocCfg.nr_loc_devs],

  // ACD:
  input  logic [LocCfg.nr_loc_devs-1:0] i_acd_prod_valid,
  output logic [LocCfg.nr_loc_devs-1:0] o_acd_prod_ready,
  output logic [LocCfg.nr_loc_devs-1:0] o_acd_cons_valid,
  input  logic [LocCfg.nr_loc_devs-1:0] i_acd_cons_ready,

  // top info:
  input  logic [token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_cid,

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
  input  token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t  i_axi_s_aw,
  output logic                                          o_axi_s_aw_ready,
  // Write  Data Channel
  input  token_manager_aic_csr_reg_pkg::axi_w_ch_h2d_t  i_axi_s_w,
  output logic                                          o_axi_s_w_ready,
  // Write Response Channel
  output token_manager_aic_csr_reg_pkg::axi_b_ch_d2h_t  o_axi_s_b,
  input  logic                                          i_axi_s_b_ready,
  // Read Address Channel
  input  token_manager_aic_csr_reg_pkg::axi_a_ch_h2d_t  i_axi_s_ar,
  output logic                                          o_axi_s_ar_ready,
  // Read Data Channel
  output token_manager_aic_csr_reg_pkg::axi_r_ch_d2h_t  o_axi_s_r,
  input  logic                                          i_axi_s_r_ready,

  // interrupt:
  output logic o_irq
);

  token_manager_aic_csr_reg_pkg::token_manager_aic_csr_hw2reg_t csr_hw2reg, csr_hw2reg_loc, csr_hw2reg_top;
  token_manager_aic_csr_reg_pkg::token_manager_aic_csr_reg2hw_t csr_reg2hw;

  logic [TopCfg.nr_loc_devs-1:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] dev_id;

  logic irq_loc, irq_top;

  always_comb csr_hw2reg = csr_hw2reg_loc | csr_hw2reg_top;
  always_comb o_irq = irq_loc | irq_top;

  always_comb begin
    for (int i=0;i<TopCfg.nr_loc_devs;i++) begin
      dev_id[i][token_manager_pkg::TOKEN_MANAGER_UID_W-1 : 2] = i_cid + 1;
      dev_id[i][1:0] = token_mgr_mapping_aic_pkg::TOK_MGR_TOP_DEV_ID[i][1:0];
    end
  end

  token_manager_aic_csr_reg_top u_csr (
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

  logic [LocCfg.max_num_prod-1:0] loc_dev_prod_valid[LocCfg.nr_loc_devs];
  logic [LocCfg.max_num_prod-1:0] loc_dev_prod_ready[LocCfg.nr_loc_devs];
  logic [LocCfg.max_num_cons-1:0] loc_dev_cons_valid[LocCfg.nr_loc_devs];
  logic [LocCfg.max_num_cons-1:0] loc_dev_cons_ready[LocCfg.nr_loc_devs];
  logic [LocCfg.nr_loc_devs-1:0]  loc_acd_prod_valid;
  logic [LocCfg.nr_loc_devs-1:0]  loc_acd_prod_ready;
  logic [LocCfg.nr_loc_devs-1:0]  loc_acd_cons_valid;
  logic [LocCfg.nr_loc_devs-1:0]  loc_acd_cons_ready;
  logic loc_mvmexe_sync_valid;
  logic loc_mvmexe_sync_ready;

  /////////////////////////////////////////////////////////////
  // Mux ACD or SWEP:
  always_comb begin // mux SWEP or ACD
    // default:
    loc_dev_prod_valid = i_dev_prod_valid;
    o_dev_prod_ready = loc_dev_prod_ready;
    o_dev_cons_valid = loc_dev_cons_valid;
    loc_dev_cons_ready = i_dev_cons_ready;

    for (int unsigned dev=0; dev<LocCfg.nr_loc_devs; dev++) begin
      // dev ACD has it's own port due to the mux work around
      if (dev == token_mgr_mapping_aic_pkg::TOK_MGR_ACD_DEV_IDX) begin
        loc_dev_prod_valid[dev][0] = i_acd_prod_valid[token_mgr_mapping_aic_pkg::TOK_MGR_ACD_SW_EP_IDX];
        loc_dev_cons_ready[dev][0] = i_acd_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_ACD_SW_EP_IDX];
        loc_acd_prod_ready[token_mgr_mapping_aic_pkg::TOK_MGR_ACD_SW_EP_IDX] = loc_dev_prod_ready[dev][0];
        loc_acd_cons_valid[token_mgr_mapping_aic_pkg::TOK_MGR_ACD_SW_EP_IDX] = loc_dev_cons_valid[dev][0];

        // tie off 'normal' dev connection for ACD, as it's not used
        o_dev_prod_ready[dev][0] = 1'b1;
        o_dev_cons_valid[dev][0] = 1'b0;
      end else begin
        loc_dev_prod_valid[dev][0] = i_swep_is_acd ? 1'b0 : i_dev_prod_valid[dev][0];
        o_dev_prod_ready[dev][0]   = i_swep_is_acd ? loc_acd_prod_ready[dev]  : loc_dev_prod_ready[dev][0];

        // mux sync singal onto MVM EXE SWEP if enabled:
        o_dev_cons_valid[dev][0]   = ((dev == token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX) && i_sync_mvm_exe_swep_en) ? loc_mvmexe_sync_valid :
                                      i_swep_is_acd ? loc_acd_cons_valid[dev]  : loc_dev_cons_valid[dev][0];
        loc_dev_cons_ready[dev][0] = ((dev == token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX) && i_sync_mvm_exe_swep_en) ? 1'b1 :
                                      i_swep_is_acd ? 1'b1                     : i_dev_cons_ready[dev][0];

        // ACD counter connections:
        loc_acd_prod_valid[dev]    = i_swep_is_acd ? i_dev_prod_valid[dev][0] : 1'b0;
        loc_acd_cons_ready[dev]    = i_swep_is_acd ? i_dev_cons_ready[dev][0] : 1'b1;
      end
    end
    loc_mvmexe_sync_ready = i_sync_mvm_exe_swep_en ? i_dev_cons_ready[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_DEV_IDX][0] : 1'b1;
  end
  ///////////////////////////////////////////

  ///////////////////////////////////////////
  // ACD counters:
  localparam int unsigned ACDCounterWidht = LocCfg.prod_cntr_width;
  for (genvar i=0; i<LocCfg.nr_loc_devs; i++) begin: g_acd_cntrs
    if (i != token_mgr_mapping_aic_pkg::TOK_MGR_ACD_SW_EP_IDX) begin: g_dev_not_acd
      // SW EP consume (EP view), dev is prod view
      token_manager_cntr #(
        .ResetValueAtConsume(0),
        .CounterWidth       (ACDCounterWidht)
      ) u_acd_cons_cnt (
        .i_clk,
        .i_rst_n,

        .i_prod_valid (loc_acd_prod_valid[i]),
        .o_prod_ready (loc_acd_prod_ready[i]),
        .i_incr_value (LocCfg.prod_cntr_width'(1)),

        .o_cons_valid (o_acd_cons_valid[i]),
        .i_cons_ready (i_acd_cons_ready[i]),

        .o_current_cnt(),
        .o_saturated  ()
      );

      // SW EP produce
      token_manager_cntr #(
        .ResetValueAtConsume(0),
        .CounterWidth       (ACDCounterWidht)
      ) u_acd_prod_cnt (
        .i_clk,
        .i_rst_n,

        .i_prod_valid (i_acd_prod_valid[i]),
        .o_prod_ready (o_acd_prod_ready[i]),
        .i_incr_value (LocCfg.prod_cntr_width'(1)),

        .o_cons_valid (loc_acd_cons_valid[i]),
        .i_cons_ready (loc_acd_cons_ready[i]),

        .o_current_cnt(),
        .o_saturated  ()
      );
    end else begin : g_dev_acd
      assign o_acd_cons_valid[i] = loc_acd_cons_valid[i];
      assign o_acd_prod_ready[i] = loc_acd_prod_ready[i];
    end
  end
  ///////////////////////////////////////////

  ///////////////////////////////////////////
  // MVM EXE sync counter.
  token_manager_cntr #(
    .ResetValueAtConsume(0),
    .CounterWidth       (2)
  ) u_mvmexe_sync_cnt (
    .i_clk,
    .i_rst_n,

    .i_prod_valid (i_sync_mvm_exe_swep),
    .o_prod_ready (), // not used, can't back-pressure a pulse
    .i_incr_value (2'(1)),

    .o_cons_valid (loc_mvmexe_sync_valid),
    .i_cons_ready (loc_mvmexe_sync_ready),

    .o_current_cnt(),
    .o_saturated  ()
  );

  token_manager #(
    /// Configuration
    .LocCfg(token_mgr_mapping_aic_pkg::TOK_MGR_CFG),
    .LocMapProdToCounter(token_mgr_mapping_aic_pkg::TOK_MGR_PROD_TO_GEN),
    .LocMapConsToCounter(token_mgr_mapping_aic_pkg::TOK_MGR_CONS_TO_GEN),

    .csr_reg2hw_t(token_manager_aic_csr_reg_pkg::token_manager_aic_csr_reg2hw_t),
    .csr_hw2reg_t(token_manager_aic_csr_reg_pkg::token_manager_aic_csr_hw2reg_t),
    .TOK_MAN_CSR_INFO(token_mgr_mapping_aic_pkg::TOK_MAN_CSR_INFO)
  ) u_tok_mgr (
    .i_clk,
    .i_rst_n,

    // token interface:
    .i_dev_prod_valid(loc_dev_prod_valid),
    .o_dev_prod_ready(loc_dev_prod_ready),

    .o_dev_cons_valid(loc_dev_cons_valid),
    .i_dev_cons_ready(loc_dev_cons_ready),

    ///// CSR connection subordinate:
    .i_csr_reg2hw(csr_reg2hw),
    .o_csr_hw2reg(csr_hw2reg_loc),

    // interrupt:
    .o_irq(irq_loc)
  );

  token_manager_top #(
    /// Configuration
    .TopCfg(token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CFG),

    .TopDevIds(token_mgr_mapping_aic_pkg::TOK_MGR_TOP_DEV_ID),
    .TopDevTokensProd(token_mgr_mapping_aic_pkg::TOK_MGR_TOP_DEV_PROD_WIDTH),
    .TopDevTokensCons(token_mgr_mapping_aic_pkg::TOK_MGR_TOP_DEV_CONS_WIDTH),
    .TopMapProdToDev(token_mgr_mapping_aic_pkg::TOK_MGR_TOP_PROD_TO_DEV),
    .TopMapConsToDev(token_mgr_mapping_aic_pkg::TOK_MGR_TOP_CONS_TO_DEV),

    .csr_reg2hw_t(token_manager_aic_csr_reg_pkg::token_manager_aic_csr_reg2hw_t),
    .csr_hw2reg_t(token_manager_aic_csr_reg_pkg::token_manager_aic_csr_hw2reg_t),
    .TOK_MAN_CSR_INFO(token_mgr_mapping_aic_pkg::TOP_TOK_MAN_CSR_INFO)
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
    .o_csr_hw2reg(csr_hw2reg_top),

    // interrupt:
    .o_irq(irq_top)
  );

endmodule
