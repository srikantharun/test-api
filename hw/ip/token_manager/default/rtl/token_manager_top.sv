// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token manager, route token signals and provide software endpoint
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module token_manager_top #(
  /// Configuration
  // Make sure the parameter array will get a positive size when not used:
  parameter token_manager_pkg::tokmgr_cfg_t TopCfg = '{default: 0, nr_loc_devs:1, max_num_prod:2, max_num_cons:2},

  // TOP
  parameter int unsigned TopDevIds[TopCfg.nr_loc_devs] = '{default: 0},
  parameter int unsigned TopDevTokensProd[TopCfg.nr_loc_devs] = '{default: 0},
  parameter int unsigned TopDevTokensCons[TopCfg.nr_loc_devs] = '{default: 0},
  //// Top mapping producer to device:
  parameter int TopMapProdToDev[TopCfg.nr_loc_devs][TopCfg.max_num_prod] = '{default: 0},
  //// Top mapping consumer to device:
  parameter int TopMapConsToDev[TopCfg.nr_loc_devs][TopCfg.max_num_cons] = '{default: 0},

  // CSR:
  parameter type csr_reg2hw_t  = logic,
  parameter type csr_hw2reg_t  = logic,

  parameter token_manager_pkg::TokMgrCsrInfo_t TOK_MAN_CSR_INFO = '{default: 0}
)(
  input  wire i_clk,
  input  wire i_rst_n,

  // top info:
  input  logic [TopCfg.nr_loc_devs-1:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_dev_id,
  input  logic [token_manager_pkg::TOKEN_MANAGER_MAX_VUID:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_vuid_to_uid,
  input  logic [token_manager_pkg::TOKEN_MANAGER_MAX_VUID:0][token_manager_pkg::TOKEN_MANAGER_UID_W-1:0] i_uid_to_vuid,

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

  ///// CSR connection subordinate:
  input  csr_reg2hw_t i_csr_reg2hw,
  output csr_hw2reg_t o_csr_hw2reg,

  // interrupt:
  output logic o_irq
);
  // local params to help rtlA
  localparam int unsigned MaxNumCons = TopCfg.max_num_cons;
  localparam int unsigned MaxNumProd = TopCfg.max_num_prod;
  localparam int unsigned NrLocDevs = TopCfg.nr_loc_devs;
  localparam int unsigned ProdCntrWidth = TopCfg.prod_cntr_width;
  localparam int unsigned ConsCntrWidth = TopCfg.cons_cntr_width;

  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (!TopCfg.loc_is_sw_only) begin : g_net_param_check
    if (TopCfg.max_num_prod  < 2) $fatal(1, "Parameter: 'TopCfg.max_num_prod' must be at least 2!");
    if (TopCfg.max_num_cons  < 2) $fatal(1, "Parameter: 'TopCfg.max_num_cons' must be at least 2!");
    if (TopCfg.nr_loc_devs   < 1) $fatal(1, "Parameter: 'TopCfg.nr_loc_devs' must be at least 1!");
    if (TopCfg.nr_cntrs      < 2) $fatal(1, "Parameter: 'TopCfg.nr_cntrs' must be at least 2!");
    if (TopCfg.prod_cntr_width    < 1) $fatal(1, "Parameter: 'TopCfg.prod_cntr_width' must be at least 1!");
    if (TopCfg.cons_cntr_width    < 1) $fatal(1, "Parameter: 'TopCfg.cons_cntr_width' must be at least 1!");
  end

  function automatic int get_gen_cntr(int unsigned dev, int unsigned tok);
    int unsigned g = 0;
    for (int unsigned d=0; d<TopCfg.nr_loc_devs; d++) begin
      for (int unsigned c=0; c < TopCfg.max_num_prod; c++) begin
        if (d == dev && c==tok)
          return g;
        else if (TopMapProdToDev[d][c] != -1)
          g = g+1;
      end
    end
    return -1;
  endfunction

  function automatic int get_csr_idx_cntr(int unsigned dev, int unsigned tok, int unsigned width);
    int unsigned w = 0;
    for (int unsigned d=0; d<TopCfg.nr_loc_devs; d++) begin
      for (int unsigned c=0; c < TopCfg.max_num_prod; c++) begin
        if (d == dev && c==tok)
          return w;
        else if (TopMapProdToDev[d][c] != -1)
          w = w + width;
      end
    end
    return -1;
  endfunction

  logic [TopCfg.nr_loc_devs-1:0] [7:0]  dev_ocpl_m_maddr;
  logic [TopCfg.nr_loc_devs-1:0]        dev_ocpl_m_mcmd;
  logic [TopCfg.nr_loc_devs-1:0]        dev_ocpl_m_scmdaccept;
  logic [TopCfg.nr_loc_devs-1:0] [7:0]  dev_ocpl_m_mdata;

  logic [TopCfg.nr_loc_devs-1:0]        top_mapping_error;

  logic [TopCfg.nr_loc_devs-1:0][15:0] ocpl_arb_inp_data;
  logic [15:0] ocpl_arb_oup_data;

  logic [7:0]  dev_ocpl_s_maddr[TopCfg.nr_loc_devs];
  logic        dev_ocpl_s_mcmd[TopCfg.nr_loc_devs];
  logic        dev_ocpl_s_scmdaccept[TopCfg.nr_loc_devs];
  logic [7:0]  dev_ocpl_s_mdata[TopCfg.nr_loc_devs];

  logic [TopCfg.nr_loc_devs-1:0] ocpl_s_mcmd, ocpl_s_scmdaccept;

  logic [TopCfg.prod_cntr_width-1:0] tok_prod_cntr_val_1;
  logic [TopCfg.cons_cntr_width-1:0] tok_cons_cntr_val_1;
  logic [TopCfg.nr_cntrs -1:0] gen_vec_prod_sat;
  logic [TopCfg.nr_cntrs -1:0] gen_vec_cons_sat;

  logic [TopCfg.nr_cntrs -1:0] gen_vec_prod_vld;
  logic [TopCfg.nr_cntrs -1:0] gen_vec_prod_rdy;
  logic [TopCfg.nr_cntrs -1:0] gen_vec_cons_vld;
  logic [TopCfg.nr_cntrs -1:0] gen_vec_cons_rdy;

  logic swep_cons_vld[TopCfg.max_num_cons];
  logic swep_cons_rdy[TopCfg.max_num_cons];
  logic [TopCfg.max_num_cons-1:0][TopCfg.cons_cntr_width-1:0] swep_cons_cnt;
  logic [TopCfg.max_num_cons-1:0]                   swep_cons_sat;
  logic [TopCfg.max_num_cons-1:0]                   swep_cons_non_zero;

  logic swep_prod_vld[TopCfg.max_num_prod];
  logic swep_prod_rdy[TopCfg.max_num_prod];
  logic [TopCfg.prod_cntr_width-1:0] swep_prod_inc_val[TopCfg.max_num_prod];
  logic [TopCfg.max_num_prod-1:0][TopCfg.prod_cntr_width-1:0] swep_prod_cnt;
  logic [TopCfg.max_num_prod-1:0] swep_prod_sat;

  logic [TopCfg.max_num_cons-1:0][TopCfg.prod_cntr_width+2-1:0]  swep_cons_arr; // CNTR_W+2 to for Q and RE (and QE)
  logic [TopCfg.max_num_prod-1:0][TopCfg.prod_cntr_width+1-1:0]  swep_prod_arr; // CNTR_W+1 to for Q and QE

  logic [TOK_MAN_CSR_INFO[token_manager_pkg::prod_cnt_idx].h2r_dw-1:0] csr_prod_cnt;
  logic [TOK_MAN_CSR_INFO[token_manager_pkg::cons_cnt_idx].h2r_dw-1:0] csr_cons_cnt;
  //////////////////////

  always_comb tok_prod_cntr_val_1 = 1;
  always_comb tok_cons_cntr_val_1 = 1;

  // CSR HW2REG assignments:
  if (TopCfg.loc_is_sw_only) begin : g_swep_csr
    always_comb begin
      o_csr_hw2reg = 0; // default (other fields) 0

      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::swep_prod_idx].h2r_lsb +:
                              TOK_MAN_CSR_INFO[token_manager_pkg::swep_prod_idx].h2r_dw] = swep_prod_cnt;
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::swep_cons_idx].h2r_lsb +:
                              TOK_MAN_CSR_INFO[token_manager_pkg::swep_cons_idx].h2r_dw] = swep_cons_cnt;

      // SWEP Prod Sat
      for (int unsigned i = 0; i < TopCfg.nr_loc_devs; i++) begin
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_prod_sat_idx].h2r_lsb + 2*i] = 1; // d
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_prod_sat_idx].h2r_lsb + 2*i] = swep_prod_sat[i]; // de
      end
      // SWEP Cons Sat
      for (int unsigned i = 0; i < TopCfg.nr_loc_devs; i++) begin
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_sat_idx].h2r_lsb + 2*i] = 1; // d
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_sat_idx].h2r_lsb + 2*i] = swep_cons_sat[i]; // de
      end
      // SWEP Cons Non Zero
      for (int unsigned i = 0; i < TopCfg.nr_loc_devs; i++) begin
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_non_zero_idx].h2r_lsb + 2*i] = 1; // d
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_non_zero_idx].h2r_lsb + 2*i] = swep_cons_non_zero[i]; // de
      end
    end
  end else begin : g_nrml_csr
    always_comb begin
      o_csr_hw2reg = 0; // default (other fields) 0

      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::prod_cnt_idx].h2r_lsb +:
                    TOK_MAN_CSR_INFO[token_manager_pkg::prod_cnt_idx].h2r_dw] = csr_prod_cnt;
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::cons_cnt_idx].h2r_lsb +:
                    TOK_MAN_CSR_INFO[token_manager_pkg::cons_cnt_idx].h2r_dw] = csr_cons_cnt;
      // Cntr prod sat
      for (int unsigned i = 0; i < TopCfg.nr_cntrs; i++) begin
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].h2r_lsb + 2*i] = 1; // d
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].h2r_lsb + 2*i] = gen_vec_prod_sat[i]; // de
      end
      // Cntr cons sat
      for (int unsigned i = 0; i < TopCfg.nr_cntrs; i++) begin
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_cons_idx].h2r_lsb + 2*i] = 1; // d
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_cons_idx].h2r_lsb + 2*i] = gen_vec_cons_sat[i]; // de
      end
      // Mapping error
      for (int unsigned i = 0; i < TopCfg.nr_loc_devs; i++) begin
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_top_map_idx].h2r_lsb + 2*i] = 1; // d
        o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_top_map_idx].h2r_lsb + 2*i] = top_mapping_error[i]; // de
      end
    end
  end

  if (TopCfg.loc_is_sw_only) begin : g_swep_irq
    //////////////////
    //// Mapping to and from CSR struct vectors:
    always_comb swep_cons_arr = i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::swep_cons_idx].r2h_lsb +:
                                              TOK_MAN_CSR_INFO[token_manager_pkg::swep_cons_idx].r2h_dw];
    always_comb swep_prod_arr = i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::swep_prod_idx].r2h_lsb +:
                                              TOK_MAN_CSR_INFO[token_manager_pkg::swep_prod_idx].r2h_dw];
    // Local network IRQ generation:
    always_comb  o_irq =
                  (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_swep_prod_sat_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_swep_prod_sat_idx].r2h_dw] &  // saturation SWEP (prod) en
                      i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_prod_sat_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_prod_sat_idx].r2h_dw])) | // saturation SWEP (prod)
                  (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_swep_cons_sat_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_swep_cons_sat_idx].r2h_dw] &  // saturation SWEP (cons) en
                      i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_sat_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_sat_idx].r2h_dw])) | // saturation SWEP (cons)
                  (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_swep_cons_non_zero_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_swep_cons_non_zero_idx].r2h_dw] &  // non zero SWEP (cons) en
                      i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_non_zero_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_non_zero_idx].r2h_dw])) | // non zero SWEP (cons)
                  0;
  end else begin : g_nrml_irq
    always_comb  o_irq =
    (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_prod_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_prod_idx].r2h_dw] &  // saturation generic count (prod) en
                      i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].r2h_dw])) | // saturation generic count (prod)
    (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_cons_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_cons_idx].r2h_dw] &  // saturation generic count (cons) en
                      i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_cons_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_cons_idx].r2h_dw])) | // saturation generic count (cons)
    (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_top_map_idx].r2h_lsb +:
                                  TOK_MAN_CSR_INFO[token_manager_pkg::irq_top_map_idx].r2h_dw])) | // Mapping error
                  0;
  end
  /////////////////

  if (TopCfg.loc_is_sw_only) begin : g_swep_cntr
    for (genvar d = 0; unsigned'(d) < TopCfg.nr_loc_devs; d++) begin : g_dev
      // generate counters for software endpoint:
      for (genvar c = 0; unsigned'(c) < TopDevTokensCons[d]; c++) begin : g_cons_cnt
        localparam int GenVectorIdx = get_gen_cntr(d,c);
        // SW EP consume
        token_manager_cntr #(
          .ResetValueAtConsume(0),
          .CounterWidth       (ConsCntrWidth)
        ) u_sw_cons_cnt (
          .i_clk,
          .i_rst_n,

          .i_prod_valid (gen_vec_cons_vld[GenVectorIdx]),
          .o_prod_ready (gen_vec_cons_rdy[GenVectorIdx]),
          .i_incr_value (tok_cons_cntr_val_1),

          .o_cons_valid (), // ASO-UNUSED_OUTPUT: valid not used
          .i_cons_ready (swep_cons_arr[GenVectorIdx][0]),

          .o_current_cnt(swep_cons_cnt[GenVectorIdx]),
          .o_saturated  (swep_cons_sat[GenVectorIdx])
        );
        assign swep_cons_non_zero[GenVectorIdx] = |swep_cons_cnt[GenVectorIdx];
      end

      for (genvar c = 0; unsigned'(c) < TopDevTokensProd[d]; c++) begin : g_prod_cnt
        localparam int GenVectorIdx = get_gen_cntr(d,c);
        // SW EP produce
        token_manager_cntr #(
          .ResetValueAtConsume(0),
          .CounterWidth       (ProdCntrWidth)
        ) u_sw_prod_cnt (
          .i_clk,
          .i_rst_n,

          .i_prod_valid (swep_prod_arr[GenVectorIdx][0]),
          .o_prod_ready (), // ASO-UNUSED_OUTPUT: No backpressure possible
          .i_incr_value (swep_prod_arr[GenVectorIdx][TopCfg.prod_cntr_width:1]),

          .o_cons_valid (gen_vec_prod_vld[GenVectorIdx]),
          .i_cons_ready (gen_vec_prod_rdy[GenVectorIdx]),

          .o_current_cnt(swep_prod_cnt[GenVectorIdx]),
          .o_saturated  (swep_prod_sat[GenVectorIdx])
        );
      end
    end
  end else begin: g_nrml_cntr
    // generate counters for generic vector:
    for (genvar d = 0; unsigned'(d) < TopCfg.nr_loc_devs; d++) begin : g_dev
      for (genvar c = 0; unsigned'(c) < TopDevTokensProd[d]; c++) begin : g_prod_cnt
        localparam int GenVectorIdx = get_gen_cntr(d,c);
        localparam int CsrLogicIdx = get_csr_idx_cntr(d,c,ProdCntrWidth);

        token_manager_cntr #(
          .ResetValueAtConsume(0),
          .CounterWidth       (ProdCntrWidth)
        ) u_gen_cnt_prod (
          .i_clk,
          .i_rst_n,

          .i_prod_valid (i_top_prod_valid[d][c]),
          .o_prod_ready (o_top_prod_ready[d][c]),
          .i_incr_value (tok_prod_cntr_val_1),

          .o_cons_valid (gen_vec_prod_vld[GenVectorIdx]),
          .i_cons_ready (gen_vec_prod_rdy[GenVectorIdx]),

          .o_current_cnt(csr_prod_cnt[CsrLogicIdx+:ProdCntrWidth]),
          .o_saturated  (gen_vec_prod_sat[GenVectorIdx])
        );
      end

      for (genvar c = 0; unsigned'(c) < TopDevTokensCons[d]; c++) begin : g_cons_cnt
        localparam int GenVectorIdx = get_gen_cntr(d,c);
        localparam int CsrLogicIdx = get_csr_idx_cntr(d,c,ConsCntrWidth);

        token_manager_cntr #(
          .ResetValueAtConsume(0),
          .CounterWidth       (ConsCntrWidth)
        ) u_gen_cnt_cons (
          .i_clk,
          .i_rst_n,

          .i_prod_valid (gen_vec_cons_vld[GenVectorIdx]), //
          .o_prod_ready (gen_vec_cons_rdy[GenVectorIdx]), //
          .i_incr_value (tok_cons_cntr_val_1),

          .o_cons_valid (o_top_cons_valid[d][c]),
          .i_cons_ready (i_top_cons_ready[d][c]),

          .o_current_cnt(csr_cons_cnt[CsrLogicIdx+:ConsCntrWidth]),
          .o_saturated  (gen_vec_cons_sat[GenVectorIdx])
        );
      end
    end
  end

  // Select correct OCPL converter:
  always_comb begin
    ocpl_s_mcmd = 0; // default
    o_tok_cons_ocpl_s_scmdaccept = 1; // default

    for(int unsigned d=0; d<TopCfg.nr_loc_devs;d++) begin
      if (i_tok_cons_ocpl_s_maddr[token_manager_pkg::TOKEN_MANAGER_DEV_W-1:0] == d) begin
        o_tok_cons_ocpl_s_scmdaccept = ocpl_s_scmdaccept[d];
        ocpl_s_mcmd[d] = i_tok_cons_ocpl_s_mcmd;
      end
    end
  end

  for (genvar d = 0; unsigned'(d) < TopCfg.nr_loc_devs; d++) begin : g_dev
    ////////////////////////////////////////
    // OCPL to token conversion:
    logic [TopDevTokensCons[d]-1:0] tok_cons_cnt_vld;
    logic [TopDevTokensCons[d]-1:0] tok_cons_cnt_rdy;

    assign gen_vec_cons_vld[get_gen_cntr(d,0)+:TopDevTokensCons[d]] = tok_cons_cnt_vld;
    assign tok_cons_cnt_rdy = gen_vec_cons_rdy[get_gen_cntr(d,0)+:TopDevTokensCons[d]];

    token_manager_ocpl_to_tok #(
      // TOP
      .MaxNrTokens(MaxNumCons),
      .NrTokens(TopDevTokensCons[d]),
      //// Top mapping consumer to device:
      .TopMapConsToDev(TopMapConsToDev[d])
    ) u_ocpl2tok (
      .i_clk,
      .i_rst_n,

      // top info:
      .i_uid_to_vuid,

      // Top connection via OCPL:
      .i_ocpl_s_mcmd(ocpl_s_mcmd[d]),
      .o_ocpl_s_scmdaccept(ocpl_s_scmdaccept[d]),
      .i_ocpl_s_mdata(i_tok_cons_ocpl_s_mdata),

        // local connections for top:
      .o_cons_valid(tok_cons_cnt_vld),
      .i_cons_ready(tok_cons_cnt_rdy)
    );
    ////////////////////////////////////////
    // Token to OCPL conversion:
    logic [TopDevTokensProd[d]-1:0] tok_prod_cnt_vld;
    logic [TopDevTokensProd[d]-1:0] tok_prod_cnt_rdy;

    assign tok_prod_cnt_vld = gen_vec_prod_vld[get_gen_cntr(d,0)+:TopDevTokensProd[d]];
    assign gen_vec_prod_rdy[get_gen_cntr(d,0)+:TopDevTokensProd[d]] = tok_prod_cnt_rdy;

    token_manager_tok_to_ocpl #(
      // TOP
      .DevIds(TopDevIds[d]),
      .MaxNrTokens(MaxNumProd),
      .NrTokens(TopDevTokensProd[d]),
      //// Top mapping producer to device:
      .TopMapProdToDev(TopMapProdToDev[d])
    ) u_tok2ocpl (
      .i_clk,
      .i_rst_n,

      // top info:
      .i_dev_id(i_dev_id[d]),
      .i_vuid_to_uid,

      // Top connection via OCPL:
      .o_ocpl_m_maddr(dev_ocpl_m_maddr[d]),
      .o_ocpl_m_mcmd(dev_ocpl_m_mcmd[d]),
      .i_ocpl_m_scmdaccept(dev_ocpl_m_scmdaccept[d]),
      .o_ocpl_m_mdata(dev_ocpl_m_mdata[d]),

        // local connections for top:
      .i_prod_valid(tok_prod_cnt_vld),
      .o_prod_ready(tok_prod_cnt_rdy),

      // interrupt:
      .o_irq(top_mapping_error[d])
    );
    always_comb ocpl_arb_inp_data[d] = {dev_ocpl_m_maddr[d], dev_ocpl_m_mdata[d]};
  end

  // round robin over all OCPL paths if required:
  if (TopCfg.nr_loc_devs > 0) begin: g_ocpl_rr
    // Round robin over all OCPL's:
    cc_stream_round_robin_arbiter #(
      .data_t(logic[16-1:0]),
      .N_INP(NrLocDevs),
      .ARBITER("rr")
    ) u_rr (
      .i_clk,
      .i_rst_n,

      .inp_data_i(ocpl_arb_inp_data),
      .inp_valid_i(dev_ocpl_m_mcmd),
      .inp_ready_o(dev_ocpl_m_scmdaccept),

      .oup_data_o(ocpl_arb_oup_data),
      .oup_valid_o(o_tok_prod_ocpl_m_mcmd),
      .oup_ready_i(i_tok_prod_ocpl_m_scmdaccept)
    );
    always_comb {o_tok_prod_ocpl_m_maddr, o_tok_prod_ocpl_m_mdata} = ocpl_arb_oup_data;
  end else begin: g_no_ocpl_rr
    always_comb {o_tok_prod_ocpl_m_maddr, o_tok_prod_ocpl_m_mdata} = ocpl_arb_inp_data[0];
    always_comb o_tok_prod_ocpl_m_mcmd = dev_ocpl_m_mcmd[0];
    always_comb dev_ocpl_m_scmdaccept[0] = i_tok_prod_ocpl_m_scmdaccept;
  end

endmodule
