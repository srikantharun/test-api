
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//

module aic_did_p
  import aic_common_pkg::*;
  import token_mgr_mapping_aic_pkg::*;

#(
)(
  //-------------------------------
  // interface signals
  //-------------------------------

  //-------------------------------
  // wrapper io
  //-------------------------------
  input  wire   i_clk,
  input  wire   i_rst_n,
  output logic [AIC_DEV_OBS_DW-1:0] o_dwpu_obs,
  output logic [AIC_DEV_OBS_DW-1:0] o_iau_obs,
  output logic [AIC_DEV_OBS_DW-1:0] o_dpu_obs,
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_ts_start,
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_ts_end,
  output logic [aic_did_pkg::DID_NR_ENDPOINT_SETS-1:0] o_acd_sync,
  output logic [              2:0] o_irq,
  input  logic [AIC_CID_WIDTH-1:0] i_cid,
  input  logic [1:0] i_sram_mcs,
  input  logic  i_sram_mcsw,
  input  logic  i_sram_ret,
  input  logic  i_sram_pde,
  input  logic [2:0] i_sram_adme,
  output logic  o_sram_prn,

  //-------------------------------
  // protocol ports
  //-------------------------------

  //-------------------
  // AXIS i_ifd0_axis_s
  //-------------------

  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_ifd0_axis_s_tdata,
  input  logic i_ifd0_axis_s_tlast,
  input  logic i_ifd0_axis_s_tvalid,

  //-------------------
  // AXIS o_ifd0_axis_s
  //-------------------

  output logic o_ifd0_axis_s_tready,

  //-------------------
  // AXIS i_ifd1_axis_s
  //-------------------

  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_ifd1_axis_s_tdata,
  input  logic i_ifd1_axis_s_tlast,
  input  logic i_ifd1_axis_s_tvalid,

  //-------------------
  // AXIS o_ifd1_axis_s
  //-------------------

  output logic o_ifd1_axis_s_tready,

  //-------------------
  // AXIS o_odr_axis_m
  //-------------------

  output logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_odr_axis_m_tdata,
  output logic o_odr_axis_m_tlast,
  output logic o_odr_axis_m_tvalid,

  //-------------------
  // AXIS i_odr_axis_m
  //-------------------

  input  logic i_odr_axis_m_tready,
  //-------------------------------
  // Token o_dwpu_tok_prod
  //-------------------------------
  input  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_dwpu_tok_prod_rdy  ,
  output logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_dwpu_tok_prod_vld  ,
  //-------------------------------
  // Token i_dwpu_tok_cons
  //-------------------------------
  output logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_dwpu_tok_cons_rdy  ,
  input  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_dwpu_tok_cons_vld  ,
  //-------------------------------
  // Token o_iau_tok_prod
  //-------------------------------
  input  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_iau_tok_prod_rdy  ,
  output logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_iau_tok_prod_vld  ,
  //-------------------------------
  // Token i_iau_tok_cons
  //-------------------------------
  output logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_iau_tok_cons_rdy  ,
  input  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_iau_tok_cons_vld  ,
  //-------------------------------
  // Token o_dpu_tok_prod
  //-------------------------------
  input  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_dpu_tok_prod_rdy  ,
  output logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_dpu_tok_prod_vld  ,
  //-------------------------------
  // Token i_dpu_tok_cons
  //-------------------------------
  output logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_dpu_tok_cons_rdy  ,
  input  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_dpu_tok_cons_vld  ,

  //-------------------------------
  // AXI4 i_cfg_axi_s
  //-------------------------------
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_awid   ,
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_awaddr ,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_awlen  ,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_awsize ,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_awburst,
  input  logic i_cfg_axi_s_awvalid,
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_cfg_axi_s_wdata  ,
  input  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] i_cfg_axi_s_wstrb  ,
  input  logic i_cfg_axi_s_wlast  ,
  input  logic i_cfg_axi_s_wvalid ,
  input  logic i_cfg_axi_s_bready ,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_arid   ,
  input  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_araddr ,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_arlen  ,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_arsize ,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_arburst,
  input  logic i_cfg_axi_s_arvalid,
  input  logic i_cfg_axi_s_rready ,

  //-------------------------------
  // AXI4 o_cfg_axi_s
  //-------------------------------
  output logic o_cfg_axi_s_awready,
  output logic o_cfg_axi_s_wready ,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_bid    ,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_bresp  ,
  output logic o_cfg_axi_s_bvalid ,
  output logic o_cfg_axi_s_arready,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_rid    ,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_cfg_axi_s_rdata  ,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_rresp  ,
  output logic o_cfg_axi_s_rlast  ,
  output logic o_cfg_axi_s_rvalid ,


  //-------------------------------
  // DFT Interface
  //-------------------------------
  input  wire   ijtag_tck,
  input  wire   ijtag_reset,
  input  logic  ijtag_sel,
  input  logic  ijtag_ue,
  input  logic  ijtag_se,
  input  logic  ijtag_ce,
  input  logic  ijtag_si,
  output logic  ijtag_so,
  input  wire   test_clk,
  input  logic  test_mode,
  input  logic  edt_update,
  input  logic  scan_en,
  input  logic [12-1: 0] scan_in,
  output logic [12-1: 0] scan_out,
  input  wire   bisr_clk,
  input  wire   bisr_reset,
  input  logic  bisr_shift_en,
  input  logic  bisr_si,
  output logic  bisr_so
);

//-------------------------------
// Protocols
//-------------------------------

//-------------------------------
// AXIS SPILL for i_ifd0_axis_s
//-------------------------------
logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_ifd0_axis_s_subip_tdata;
logic i_ifd0_axis_s_subip_tlast;
logic i_ifd0_axis_s_subip_tvalid;


//-------------------------------
// AXIS SPILL for o_ifd0_axis_s
//-------------------------------
logic o_ifd0_axis_s_subip_tready;

cc_stream_spill_reg #(
    .DataWidth(AIC_PWORD_I8_AXIS_TDATA_WIDTH+1)
  ) o_ifd0_axis_s_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_flush(1'b0),
    .i_data({i_ifd0_axis_s_tdata, i_ifd0_axis_s_tlast}),
    .i_valid(i_ifd0_axis_s_tvalid),
    .o_ready(o_ifd0_axis_s_tready),
    .o_data({i_ifd0_axis_s_subip_tdata, i_ifd0_axis_s_subip_tlast}),
    .o_valid(i_ifd0_axis_s_subip_tvalid),
    .i_ready(o_ifd0_axis_s_subip_tready)
);
//-------------------------------
// AXIS SPILL for i_ifd1_axis_s
//-------------------------------
logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_ifd1_axis_s_subip_tdata;
logic i_ifd1_axis_s_subip_tlast;
logic i_ifd1_axis_s_subip_tvalid;


//-------------------------------
// AXIS SPILL for o_ifd1_axis_s
//-------------------------------
logic o_ifd1_axis_s_subip_tready;

cc_stream_spill_reg #(
    .DataWidth(AIC_PWORD_I8_AXIS_TDATA_WIDTH+1)
  ) o_ifd1_axis_s_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_flush(1'b0),
    .i_data({i_ifd1_axis_s_tdata, i_ifd1_axis_s_tlast}),
    .i_valid(i_ifd1_axis_s_tvalid),
    .o_ready(o_ifd1_axis_s_tready),
    .o_data({i_ifd1_axis_s_subip_tdata, i_ifd1_axis_s_subip_tlast}),
    .o_valid(i_ifd1_axis_s_subip_tvalid),
    .i_ready(o_ifd1_axis_s_subip_tready)
);
//-------------------------------
// AXIS SPILL for o_odr_axis_m
//-------------------------------
logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_odr_axis_m_subip_tdata;
logic o_odr_axis_m_subip_tlast;
logic o_odr_axis_m_subip_tvalid;


//-------------------------------
// AXIS SPILL for i_odr_axis_m
//-------------------------------
logic i_odr_axis_m_subip_tready;

cc_stream_spill_reg #(
    .DataWidth(AIC_PWORD_I8_AXIS_TDATA_WIDTH+1)
  ) i_odr_axis_m_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_flush(1'b0),
    .i_data({o_odr_axis_m_subip_tdata, o_odr_axis_m_subip_tlast}),
    .i_valid(o_odr_axis_m_subip_tvalid),
    .o_ready(i_odr_axis_m_subip_tready),
    .o_data({o_odr_axis_m_tdata, o_odr_axis_m_tlast}),
    .o_valid(o_odr_axis_m_tvalid),
    .i_ready(i_odr_axis_m_tready)
);


//-------------------------------
// TOKEN SPILL for o_dwpu_tok_prod
//-------------------------------
logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] o_dwpu_tok_prod_subip_vld;


//-------------------------------
// TOKEN SPILL for i_dwpu_tok_prod
//-------------------------------
logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_dwpu_tok_prod_subip_rdy;

token_cut #(
    .NumTokens(TOK_MGR_D_DWPU_NR_TOK_PROD)
  ) i_dwpu_tok_prod_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_s_valid(o_dwpu_tok_prod_subip_vld),
    .o_s_ready(i_dwpu_tok_prod_subip_rdy),
    .o_m_valid(o_dwpu_tok_prod_vld),
    .i_m_ready(i_dwpu_tok_prod_rdy)
);
//-------------------------------
// TOKEN SPILL for i_dwpu_tok_cons
//-------------------------------
logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_dwpu_tok_cons_subip_vld;


//-------------------------------
// TOKEN SPILL for o_dwpu_tok_cons
//-------------------------------
logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] o_dwpu_tok_cons_subip_rdy;

token_cut #(
    .NumTokens(TOK_MGR_D_DWPU_NR_TOK_CONS)
  ) o_dwpu_tok_cons_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_s_valid(i_dwpu_tok_cons_vld),
    .o_s_ready(o_dwpu_tok_cons_rdy),
    .o_m_valid(i_dwpu_tok_cons_subip_vld),
    .i_m_ready(o_dwpu_tok_cons_subip_rdy)
);
//-------------------------------
// TOKEN SPILL for o_iau_tok_prod
//-------------------------------
logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] o_iau_tok_prod_subip_vld;


//-------------------------------
// TOKEN SPILL for i_iau_tok_prod
//-------------------------------
logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_iau_tok_prod_subip_rdy;

token_cut #(
    .NumTokens(TOK_MGR_D_DPU_NR_TOK_PROD)
  ) i_iau_tok_prod_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_s_valid(o_iau_tok_prod_subip_vld),
    .o_s_ready(i_iau_tok_prod_subip_rdy),
    .o_m_valid(o_iau_tok_prod_vld),
    .i_m_ready(i_iau_tok_prod_rdy)
);
//-------------------------------
// TOKEN SPILL for i_iau_tok_cons
//-------------------------------
logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_iau_tok_cons_subip_vld;


//-------------------------------
// TOKEN SPILL for o_iau_tok_cons
//-------------------------------
logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] o_iau_tok_cons_subip_rdy;

token_cut #(
    .NumTokens(TOK_MGR_D_IAU_NR_TOK_CONS)
  ) o_iau_tok_cons_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_s_valid(i_iau_tok_cons_vld),
    .o_s_ready(o_iau_tok_cons_rdy),
    .o_m_valid(i_iau_tok_cons_subip_vld),
    .i_m_ready(o_iau_tok_cons_subip_rdy)
);
//-------------------------------
// TOKEN SPILL for o_dpu_tok_prod
//-------------------------------
logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] o_dpu_tok_prod_subip_vld;


//-------------------------------
// TOKEN SPILL for i_dpu_tok_prod
//-------------------------------
logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_dpu_tok_prod_subip_rdy;

token_cut #(
    .NumTokens(TOK_MGR_D_IAU_NR_TOK_PROD)
  ) i_dpu_tok_prod_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_s_valid(o_dpu_tok_prod_subip_vld),
    .o_s_ready(i_dpu_tok_prod_subip_rdy),
    .o_m_valid(o_dpu_tok_prod_vld),
    .i_m_ready(i_dpu_tok_prod_rdy)
);
//-------------------------------
// TOKEN SPILL for i_dpu_tok_cons
//-------------------------------
logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_dpu_tok_cons_subip_vld;


//-------------------------------
// TOKEN SPILL for o_dpu_tok_cons
//-------------------------------
logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] o_dpu_tok_cons_subip_rdy;

token_cut #(
    .NumTokens(TOK_MGR_D_DPU_NR_TOK_CONS)
  ) o_dpu_tok_cons_spill (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_s_valid(i_dpu_tok_cons_vld),
    .o_s_ready(o_dpu_tok_cons_rdy),
    .o_m_valid(i_dpu_tok_cons_subip_vld),
    .i_m_ready(o_dpu_tok_cons_subip_rdy)
);




//-------------------------------
// AXI SPILL for i_cfg_axi_s
//-------------------------------
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_subip_awid   ;
  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_subip_awaddr ;
  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_subip_awlen  ;
  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_subip_awsize ;
  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_subip_awburst;
  logic i_cfg_axi_s_subip_awvalid;
  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_cfg_axi_s_subip_wdata  ;
  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] i_cfg_axi_s_subip_wstrb  ;
  logic i_cfg_axi_s_subip_wlast  ;
  logic i_cfg_axi_s_subip_wvalid ;
  logic i_cfg_axi_s_subip_bready ;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_subip_arid   ;
  logic [      AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_subip_araddr ;
  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_subip_arlen  ;
  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_subip_arsize ;
  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_subip_arburst;
  logic i_cfg_axi_s_subip_arvalid;
  logic i_cfg_axi_s_subip_rready ;


//-------------------------------
// AXI SPILL for o_cfg_axi_s
//-------------------------------
  logic o_cfg_axi_s_subip_awready;
  logic o_cfg_axi_s_subip_wready ;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_subip_bid    ;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_subip_bresp  ;
  logic o_cfg_axi_s_subip_bvalid ;
  logic o_cfg_axi_s_subip_arready;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_subip_rid    ;
  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_cfg_axi_s_subip_rdata  ;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_subip_rresp  ;
  logic o_cfg_axi_s_subip_rlast  ;
  logic o_cfg_axi_s_subip_rvalid ;

axe_axi_multicut_flat #(
  .AxiIdWidth (AIC_LT_AXI_S_ID_WIDTH),
  .AxiAddrWidth (AIC_LT_AXI_ADDR_WIDTH),
  .AxiDataWidth (AIC_LT_AXI_DATA_WIDTH),
  .NumCuts(1)
  ) o_cfg_axi_s_spill_flat (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_axi_s_aw_id(i_cfg_axi_s_awid),
    .i_axi_s_aw_addr(i_cfg_axi_s_awaddr),
    .i_axi_s_aw_len(i_cfg_axi_s_awlen),
    .i_axi_s_aw_size(i_cfg_axi_s_awsize),
    .i_axi_s_aw_burst(i_cfg_axi_s_awburst),
    .i_axi_s_aw_lock('0),
    .i_axi_s_aw_cache('0),
    .i_axi_s_aw_prot('0),
    .i_axi_s_aw_qos('0),
    .i_axi_s_aw_region('0),
    .i_axi_s_aw_user('0),
    .i_axi_s_aw_valid(i_cfg_axi_s_awvalid),
    .o_axi_s_aw_ready(o_cfg_axi_s_awready),
    .i_axi_s_w_data(i_cfg_axi_s_wdata),
    .i_axi_s_w_strb(i_cfg_axi_s_wstrb),
    .i_axi_s_w_last(i_cfg_axi_s_wlast),
    .i_axi_s_w_user('0),
    .i_axi_s_w_valid(i_cfg_axi_s_wvalid),
    .o_axi_s_w_ready(o_cfg_axi_s_wready),
    .o_axi_s_b_id(o_cfg_axi_s_bid),
    .o_axi_s_b_resp(o_cfg_axi_s_bresp),
    .o_axi_s_b_user(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_s_b_valid(o_cfg_axi_s_bvalid),
    .i_axi_s_b_ready(i_cfg_axi_s_bready),
    .i_axi_s_ar_id(i_cfg_axi_s_arid),
    .i_axi_s_ar_addr(i_cfg_axi_s_araddr),
    .i_axi_s_ar_len(i_cfg_axi_s_arlen),
    .i_axi_s_ar_size(i_cfg_axi_s_arsize),
    .i_axi_s_ar_burst(i_cfg_axi_s_arburst),
    .i_axi_s_ar_lock('0),
    .i_axi_s_ar_cache('0),
    .i_axi_s_ar_prot('0),
    .i_axi_s_ar_qos('0),
    .i_axi_s_ar_region('0),
    .i_axi_s_ar_user('0),
    .i_axi_s_ar_valid(i_cfg_axi_s_arvalid),
    .o_axi_s_ar_ready(o_cfg_axi_s_arready),
    .o_axi_s_r_id(o_cfg_axi_s_rid),
    .o_axi_s_r_data(o_cfg_axi_s_rdata),
    .o_axi_s_r_resp(o_cfg_axi_s_rresp),
    .o_axi_s_r_last(o_cfg_axi_s_rlast),
    .o_axi_s_r_user(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_s_r_valid(o_cfg_axi_s_rvalid),
    .i_axi_s_r_ready(i_cfg_axi_s_rready),
    .o_axi_m_aw_id(i_cfg_axi_s_subip_awid),
    .o_axi_m_aw_addr(i_cfg_axi_s_subip_awaddr),
    .o_axi_m_aw_len(i_cfg_axi_s_subip_awlen),
    .o_axi_m_aw_size(i_cfg_axi_s_subip_awsize),
    .o_axi_m_aw_burst(i_cfg_axi_s_subip_awburst),
    .o_axi_m_aw_lock(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_aw_cache(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_aw_prot(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_aw_qos(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_aw_region(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_aw_valid(i_cfg_axi_s_subip_awvalid),
    .o_axi_m_aw_user(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .i_axi_m_aw_ready(o_cfg_axi_s_subip_awready),
    .o_axi_m_w_data(i_cfg_axi_s_subip_wdata),
    .o_axi_m_w_strb(i_cfg_axi_s_subip_wstrb),
    .o_axi_m_w_last(i_cfg_axi_s_subip_wlast),
    .o_axi_m_w_user(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_w_valid(i_cfg_axi_s_subip_wvalid),
    .i_axi_m_w_ready(o_cfg_axi_s_subip_wready),
    .i_axi_m_b_id(o_cfg_axi_s_subip_bid),
    .i_axi_m_b_resp(o_cfg_axi_s_subip_bresp),
    .i_axi_m_b_user('0),
    .i_axi_m_b_valid(o_cfg_axi_s_subip_bvalid),
    .o_axi_m_b_ready(i_cfg_axi_s_subip_bready),
    .o_axi_m_ar_id(i_cfg_axi_s_subip_arid),
    .o_axi_m_ar_addr(i_cfg_axi_s_subip_araddr),
    .o_axi_m_ar_len(i_cfg_axi_s_subip_arlen),
    .o_axi_m_ar_size(i_cfg_axi_s_subip_arsize),
    .o_axi_m_ar_burst(i_cfg_axi_s_subip_arburst),
    .o_axi_m_ar_lock(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_ar_cache(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_ar_prot(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_ar_qos(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_ar_region(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_ar_user(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .o_axi_m_ar_valid(i_cfg_axi_s_subip_arvalid),
    .i_axi_m_ar_ready(o_cfg_axi_s_subip_arready),
    .i_axi_m_r_id(o_cfg_axi_s_subip_rid),
    .i_axi_m_r_data(o_cfg_axi_s_subip_rdata),
    .i_axi_m_r_resp(o_cfg_axi_s_subip_rresp),
    .i_axi_m_r_last(o_cfg_axi_s_subip_rlast),
    .i_axi_m_r_user('0),
    .i_axi_m_r_valid(o_cfg_axi_s_subip_rvalid),
    .o_axi_m_r_ready(i_cfg_axi_s_subip_rready)
);
//-------------------------------
// Wrapped module instantiation
//-------------------------------
aic_did u_aic_did (
  .i_clk(i_clk),
  .i_rst_n(i_rst_n),
  .o_dwpu_obs(o_dwpu_obs),
  .o_iau_obs(o_iau_obs),
  .o_dpu_obs(o_dpu_obs),
  .o_ts_start(o_ts_start),
  .o_ts_end(o_ts_end),
  .o_acd_sync(o_acd_sync),
  .o_irq(o_irq),
  .i_cid(i_cid),
  .i_sram_mcs(i_sram_mcs),
  .i_sram_mcsw(i_sram_mcsw),
  .i_sram_ret(i_sram_ret),
  .i_sram_pde(i_sram_pde),
  .i_sram_se(scan_en),
  .i_sram_adme(i_sram_adme),
  .o_sram_prn(o_sram_prn),
  .i_ifd0_axis_s_tdata(i_ifd0_axis_s_subip_tdata),
  .i_ifd0_axis_s_tlast(i_ifd0_axis_s_subip_tlast),
  .i_ifd0_axis_s_tvalid(i_ifd0_axis_s_subip_tvalid),
  .o_ifd0_axis_s_tready(o_ifd0_axis_s_subip_tready),
  .i_ifd1_axis_s_tdata(i_ifd1_axis_s_subip_tdata),
  .i_ifd1_axis_s_tlast(i_ifd1_axis_s_subip_tlast),
  .i_ifd1_axis_s_tvalid(i_ifd1_axis_s_subip_tvalid),
  .o_ifd1_axis_s_tready(o_ifd1_axis_s_subip_tready),
  .o_odr_axis_m_tdata(o_odr_axis_m_subip_tdata),
  .o_odr_axis_m_tlast(o_odr_axis_m_subip_tlast),
  .o_odr_axis_m_tvalid(o_odr_axis_m_subip_tvalid),
  .i_odr_axis_m_tready(i_odr_axis_m_subip_tready),
  .o_dwpu_tok_prod_vld(o_dwpu_tok_prod_subip_vld),
  .i_dwpu_tok_prod_rdy(i_dwpu_tok_prod_subip_rdy),
  .i_dwpu_tok_cons_vld(i_dwpu_tok_cons_subip_vld),
  .o_dwpu_tok_cons_rdy(o_dwpu_tok_cons_subip_rdy),
  .o_iau_tok_prod_vld(o_iau_tok_prod_subip_vld),
  .i_iau_tok_prod_rdy(i_iau_tok_prod_subip_rdy),
  .i_iau_tok_cons_vld(i_iau_tok_cons_subip_vld),
  .o_iau_tok_cons_rdy(o_iau_tok_cons_subip_rdy),
  .o_dpu_tok_prod_vld(o_dpu_tok_prod_subip_vld),
  .i_dpu_tok_prod_rdy(i_dpu_tok_prod_subip_rdy),
  .i_dpu_tok_cons_vld(i_dpu_tok_cons_subip_vld),
  .o_dpu_tok_cons_rdy(o_dpu_tok_cons_subip_rdy),
  .i_cfg_axi_s_awid(i_cfg_axi_s_subip_awid),
  .i_cfg_axi_s_awaddr(i_cfg_axi_s_subip_awaddr),
  .i_cfg_axi_s_awlen(i_cfg_axi_s_subip_awlen),
  .i_cfg_axi_s_awsize(i_cfg_axi_s_subip_awsize),
  .i_cfg_axi_s_awburst(i_cfg_axi_s_subip_awburst),
  .i_cfg_axi_s_awvalid(i_cfg_axi_s_subip_awvalid),
  .i_cfg_axi_s_wdata(i_cfg_axi_s_subip_wdata),
  .i_cfg_axi_s_wstrb(i_cfg_axi_s_subip_wstrb),
  .i_cfg_axi_s_wlast(i_cfg_axi_s_subip_wlast),
  .i_cfg_axi_s_wvalid(i_cfg_axi_s_subip_wvalid),
  .i_cfg_axi_s_bready(i_cfg_axi_s_subip_bready),
  .i_cfg_axi_s_arid(i_cfg_axi_s_subip_arid),
  .i_cfg_axi_s_araddr(i_cfg_axi_s_subip_araddr),
  .i_cfg_axi_s_arlen(i_cfg_axi_s_subip_arlen),
  .i_cfg_axi_s_arsize(i_cfg_axi_s_subip_arsize),
  .i_cfg_axi_s_arburst(i_cfg_axi_s_subip_arburst),
  .i_cfg_axi_s_arvalid(i_cfg_axi_s_subip_arvalid),
  .i_cfg_axi_s_rready(i_cfg_axi_s_subip_rready),
  .o_cfg_axi_s_awready(o_cfg_axi_s_subip_awready),
  .o_cfg_axi_s_wready(o_cfg_axi_s_subip_wready),
  .o_cfg_axi_s_bid(o_cfg_axi_s_subip_bid),
  .o_cfg_axi_s_bresp(o_cfg_axi_s_subip_bresp),
  .o_cfg_axi_s_bvalid(o_cfg_axi_s_subip_bvalid),
  .o_cfg_axi_s_arready(o_cfg_axi_s_subip_arready),
  .o_cfg_axi_s_rid(o_cfg_axi_s_subip_rid),
  .o_cfg_axi_s_rdata(o_cfg_axi_s_subip_rdata),
  .o_cfg_axi_s_rresp(o_cfg_axi_s_subip_rresp),
  .o_cfg_axi_s_rlast(o_cfg_axi_s_subip_rlast),
  .o_cfg_axi_s_rvalid(o_cfg_axi_s_subip_rvalid)
);

endmodule
