// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Token manager, route token signals and provide software endpoint
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef TOKEN_MGR_SV
`define TOKEN_MGR_SV

module token_manager #(
  /// Configuration
  // Make sure the parameter array will get a positive size when not used:
  parameter token_manager_pkg::tokmgr_cfg_t LocCfg = '{default: 0, nr_loc_devs:1, max_num_prod:2, max_num_cons:2},

  /// Token mapping array, from producer to counter index
  /// Note: Software endpoint located ad counter index 0
  parameter int LocMapProdToCounter[LocCfg.nr_loc_devs][LocCfg.max_num_prod-1] = '{default: 0},
  /// Token mapping array, from consumer to counter index
  /// Note: Software endpoint located ad counter index 0
  parameter int LocMapConsToCounter[LocCfg.nr_loc_devs][LocCfg.max_num_cons-1] = '{default: 0},

  // CSR:
  parameter type csr_reg2hw_t  = logic,
  parameter type csr_hw2reg_t  = logic,

  parameter token_manager_pkg::TokMgrCsrInfo_t TOK_MAN_CSR_INFO = '{default: 0}
)(
  input  wire i_clk,
  input  wire i_rst_n,

  // token interface:
  input  logic [LocCfg.max_num_prod-1:0] i_dev_prod_valid[LocCfg.nr_loc_devs],
  output logic [LocCfg.max_num_prod-1:0] o_dev_prod_ready[LocCfg.nr_loc_devs],

  output logic [LocCfg.max_num_cons-1:0] o_dev_cons_valid[LocCfg.nr_loc_devs],
  input  logic [LocCfg.max_num_cons-1:0] i_dev_cons_ready[LocCfg.nr_loc_devs],

  ///// CSR connection subordinate:
  input  csr_reg2hw_t i_csr_reg2hw,
  output csr_hw2reg_t o_csr_hw2reg,

  // interrupt:
  output logic o_irq
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (LocCfg.max_num_prod  < 2) $fatal(1, "Parameter: 'LocCfg.max_num_prod' must be at least 2!");
  if (LocCfg.max_num_cons  < 2) $fatal(1, "Parameter: 'LocCfg.max_num_cons' must be at least 2!");
  if (LocCfg.nr_loc_devs   < 1) $fatal(1, "Parameter: 'LocCfg.nr_loc_devs' must be at least 1!");
  if (LocCfg.nr_cntrs      < 2) $fatal(1, "Parameter: 'LocCfg.nr_cntrs' must be at least 2!");
  if (LocCfg.cons_cntr_width != LocCfg.prod_cntr_width) $fatal(1, "Parameter: 'LocCfg.cons_cntr_width' and 'LocCfg.prod_cntr_width' should be the same!");
  if (LocCfg.prod_cntr_width    < 1) $fatal(1, "Parameter: 'LocCfg.prod_cntr_width' must be at least 1!");

  logic [LocCfg.prod_cntr_width-1:0] tok_cntr_val_1;
  logic [LocCfg.prod_cntr_width-1:0] gen_vec_prod_cnt[LocCfg.nr_cntrs];
  logic [LocCfg.nr_cntrs -1:0] gen_vec_prod_sat;

  logic [LocCfg.nr_cntrs -1:0] gen_vec_prod_vld;
  logic [LocCfg.nr_cntrs -1:0] gen_vec_prod_rdy;
  logic [LocCfg.nr_cntrs -1:0] gen_vec_cons_vld;
  logic [LocCfg.nr_cntrs -1:0] gen_vec_cons_rdy;

  logic swep_cons_vld[LocCfg.nr_loc_devs];
  logic swep_cons_rdy[LocCfg.nr_loc_devs];
  logic [LocCfg.nr_loc_devs-1:0][LocCfg.prod_cntr_width-1:0] swep_cons_cnt;
  logic [LocCfg.nr_loc_devs-1:0]                   swep_cons_sat;
  logic [LocCfg.nr_loc_devs-1:0]                   swep_cons_non_zero;

  logic swep_prod_vld[LocCfg.nr_loc_devs];
  logic swep_prod_rdy[LocCfg.nr_loc_devs];
  logic [LocCfg.prod_cntr_width-1:0] swep_prod_inc_val[LocCfg.nr_loc_devs];
  logic [LocCfg.nr_loc_devs-1:0][LocCfg.prod_cntr_width-1:0] swep_prod_cnt;
  logic [LocCfg.nr_loc_devs-1:0] swep_prod_sat;

  logic [LocCfg.nr_loc_devs-1:0][LocCfg.prod_cntr_width+2-1:0]  swep_cons_arr; // CNTR_W+2 to for Q and RE (and QE)
  logic [LocCfg.nr_loc_devs-1:0][LocCfg.prod_cntr_width+1-1:0]  swep_prod_arr; // CNTR_W+1 to for Q and QE

  logic [TOK_MAN_CSR_INFO[token_manager_pkg::prod_cnt_idx].h2r_dw-1:0] csr_prod_cnt;
  //////////////////////

  // CSR HW2REG assignments:
  always_comb begin
    o_csr_hw2reg = 0; // default (other fields) 0

    o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::swep_prod_idx].h2r_lsb +:
                            TOK_MAN_CSR_INFO[token_manager_pkg::swep_prod_idx].h2r_dw] = swep_prod_cnt;
    o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::swep_cons_idx].h2r_lsb +:
                            TOK_MAN_CSR_INFO[token_manager_pkg::swep_cons_idx].h2r_dw] = swep_cons_cnt;

    o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::prod_cnt_idx].h2r_lsb +:
                  TOK_MAN_CSR_INFO[token_manager_pkg::prod_cnt_idx].h2r_dw] = csr_prod_cnt;

    // SWEP Prod Sat
    for (int unsigned i = 0; i < LocCfg.nr_loc_devs; i++) begin
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_prod_sat_idx].h2r_lsb + 2*i] = 1; // d
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_prod_sat_idx].h2r_lsb + 2*i] = swep_prod_sat[i]; // de
    end
    // SWEP Cons Sat
    for (int unsigned i = 0; i < LocCfg.nr_loc_devs; i++) begin
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_sat_idx].h2r_lsb + 2*i] = 1; // d
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_sat_idx].h2r_lsb + 2*i] = swep_cons_sat[i]; // de
    end
    // SWEP Cons Non Zero
    for (int unsigned i = 0; i < LocCfg.nr_loc_devs; i++) begin
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_non_zero_idx].h2r_lsb + 2*i] = 1; // d
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_swep_cons_non_zero_idx].h2r_lsb + 2*i] = swep_cons_non_zero[i]; // de
    end
    // Cntr prod sat
    for (int unsigned i = 0; i < LocCfg.nr_cntrs; i++) begin
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].h2r_lsb + 2*i] = 1; // d
      o_csr_hw2reg[TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].h2r_lsb + 2*i] = gen_vec_prod_sat[i]; // de
    end
  end

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
                (|(i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_prod_idx].r2h_lsb +:
                                TOK_MAN_CSR_INFO[token_manager_pkg::irq_en_prod_idx].r2h_dw] &  // saturation generic count (prod) en
                    i_csr_reg2hw[TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].r2h_lsb +:
                                TOK_MAN_CSR_INFO[token_manager_pkg::irq_prod_idx].r2h_dw])) | // saturation generic count (prod)
                0;
  /////////////////

  // generate counters for generic vector:
  assign tok_cntr_val_1 = 1;
  localparam int unsigned ProdCntrWidth = LocCfg.prod_cntr_width;
  for (genvar i = 0; unsigned'(i) < LocCfg.nr_cntrs; i++) begin : gen_cnt
    token_manager_cntr #(
      .ResetValueAtConsume(0),
      .CounterWidth       (ProdCntrWidth)
    ) u_gen_cnt (
      .i_clk,
      .i_rst_n,

      .i_prod_valid (gen_vec_prod_vld[i]),
      .o_prod_ready (gen_vec_prod_rdy[i]),
      .i_incr_value (tok_cntr_val_1),

      .o_cons_valid (gen_vec_cons_vld[i]),
      .i_cons_ready (gen_vec_cons_rdy[i]),

      .o_current_cnt(gen_vec_prod_cnt[i]),
      .o_saturated  (gen_vec_prod_sat[i])
    );
  end

  // generate counters for software endpoint:
  for (genvar i = 0; unsigned'(i) < LocCfg.nr_loc_devs; i++) begin : gen_swep
    // SW EP consume (EP view), dev is prod view
    token_manager_cntr #(
      .ResetValueAtConsume(1),
      .CounterWidth       (ProdCntrWidth)
    ) u_sw_cons_cnt (
      .i_clk,
      .i_rst_n,

      .i_prod_valid (i_dev_prod_valid[i][0]),
      .o_prod_ready (o_dev_prod_ready[i][0]),
      .i_incr_value (tok_cntr_val_1),

      .o_cons_valid (/* open */),
      .i_cons_ready (swep_cons_arr[i][0]),

      .o_current_cnt(swep_cons_cnt[i]),
      .o_saturated  (swep_cons_sat[i])
    );
    assign swep_cons_non_zero[i] = |swep_cons_cnt[i];

    // SW EP produce
    token_manager_cntr #(
      .ResetValueAtConsume(0),
      .CounterWidth       (ProdCntrWidth)
    ) u_sw_prod_cnt (
      .i_clk,
      .i_rst_n,

      .i_prod_valid (swep_prod_arr[i][0]),
      .o_prod_ready (/* open */),
      .i_incr_value (swep_prod_arr[i][ProdCntrWidth:1]),

      .o_cons_valid (o_dev_cons_valid[i][0]),
      .i_cons_ready (i_dev_cons_ready[i][0]),

      .o_current_cnt(swep_prod_cnt[i]),
      .o_saturated  (swep_prod_sat[i])
    );
  end

  // map input to generic vector and generic to output:
  // do +1 on the device token index, as software endpoint is located at 0 and mapping doesn't look at that
  for (genvar d = 0; unsigned'(d) < LocCfg.nr_loc_devs; d++) begin : gen_dev
    for (genvar t = 0; unsigned'(t) < LocCfg.max_num_prod - 1; t++) begin : gen_tp
      if (LocMapProdToCounter[d][t] != -1) begin : gen_connect
        always_comb gen_vec_prod_vld[LocMapProdToCounter[d][t]] = i_dev_prod_valid[d][t+1];
        always_comb o_dev_prod_ready[d][t+1] = gen_vec_prod_rdy[LocMapProdToCounter[d][t]];

        // map counters to CSR struct. Finding the start: total struct deducted with all the counters:
        localparam int CsrLogicIdx = LocMapProdToCounter[d][t] * LocCfg.prod_cntr_width ;
        localparam int VectorIdx = LocMapProdToCounter[d][t];
        assign csr_prod_cnt[CsrLogicIdx+:LocCfg.prod_cntr_width] = gen_vec_prod_cnt[VectorIdx];
      end
    end
    for (genvar t = 0; unsigned'(t) < LocCfg.max_num_cons - 1; t++) begin : gen_tc
      if (LocMapConsToCounter[d][t] != -1) begin : gen_connect
        always_comb gen_vec_cons_rdy[LocMapConsToCounter[d][t]] = i_dev_cons_ready[d][t+1];
        always_comb o_dev_cons_valid[d][t+1] = gen_vec_cons_vld[LocMapConsToCounter[d][t]];
      end
    end
  end
endmodule

`endif  // TOKEN_MGR_SV
