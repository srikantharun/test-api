//`define TEMP_DEBUG

// AI CORE LS hdl top
`define AXI_VIP
`define AXI_VIP_CONN_M
`define AXI_VIP_CONN_S
`define AXI_VIP_CONN_CFG
`define MEM_DEPTH 4096

module hdl_top;
  // Time unit and precision
  timeunit 1ns; timeprecision 1ns;

  // Packages import
  import uvm_pkg::*;
  `include "uvm_macros.svh"
  import aic_common_pkg::*, aic_ls_test_pkg::*, dmc_pkg::*, aic_ls_test_pkg::*, token_mgr_mapping_aic_pkg::*, mmio_pkg::*;

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif

  realtime                                        CLK_PERIOD = 1.25ns;  // 800MHz --> 1.25ns
  int  		     aic_ls_freq_mhz   = 800; // for clk assertions
  time               clk_tol_ps        = 100;

  // Clock and reset signals
  logic                                           clk_en;
  logic                                           i_clk;
  bit                                             i_rst_n;

  logic    [dmc_pkg::DMC_IRQ_W-1:0]               o_dmc_irq;


  //RVV param
  parameter int RvvPortSizeWidth = $clog2(cva6v_ai_core_pkg::MemPortBeWidth);

  // AXIS:
  //------------------------------------------------------
  // MVM IFDW
  logic                                           o_m_ifdw_axis_m_tvalid;
  logic                                           i_m_ifdw_axis_m_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_m_ifdw_axis_m_tdata;
  logic                                           o_m_ifdw_axis_m_tlast;
  // MVM IFD0
  logic                                           o_m_ifd0_axis_m_tvalid;
  logic                                           i_m_ifd0_axis_m_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_m_ifd0_axis_m_tdata;
  logic                                           o_m_ifd0_axis_m_tlast;
  // MVM IFD1
  logic                                           o_m_ifd1_axis_m_tvalid;
  logic                                           i_m_ifd1_axis_m_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_m_ifd1_axis_m_tdata;
  logic                                           o_m_ifd1_axis_m_tlast;
  // MVM IFD2
  logic                                           o_m_ifd2_axis_m_tvalid;
  logic                                           i_m_ifd2_axis_m_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_m_ifd2_axis_m_tdata;
  logic                                           o_m_ifd2_axis_m_tlast;
  // DW IFD0
  logic                                           o_d_ifd0_axis_m_tvalid;
  logic                                           i_d_ifd0_axis_m_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_d_ifd0_axis_m_tdata;
  logic                                           o_d_ifd0_axis_m_tlast;
  // DW IFD1
  logic                                           o_d_ifd1_axis_m_tvalid;
  logic                                           i_d_ifd1_axis_m_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] o_d_ifd1_axis_m_tdata;
  logic                                           o_d_ifd1_axis_m_tlast;
  // MVM ODR
  logic                                           i_m_odr_axis_s_tvalid;
  logic                                           o_m_odr_axis_s_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_m_odr_axis_s_tdata;
  logic                                           i_m_odr_axis_s_tlast;
  // DW ODR
  logic                                           i_d_odr_axis_s_tvalid;
  logic                                           o_d_odr_axis_s_tready;
  logic    [       AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_d_odr_axis_s_tdata;
  logic                                           i_d_odr_axis_s_tlast;

  // AXI4 data slave
  //------------------------------------------------------
  // AXI write address channel
  logic                                           i_hp_axi_s_awvalid;
  logic    [           AIC_HT_AXI_ADDR_WIDTH-1:0] i_hp_axi_s_awaddr;
  logic    [           AIC_HT_AXI_S_ID_WIDTH-1:0] i_hp_axi_s_awid;
  logic    [            AIC_HT_AXI_LEN_WIDTH-1:0] i_hp_axi_s_awlen;
  logic    [           AIC_HT_AXI_SIZE_WIDTH-1:0] i_hp_axi_s_awsize;
  logic    [     AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] i_hp_axi_s_awburst;
  logic    [          AIC_HT_AXI_CACHE_WIDTH-1:0] i_hp_axi_s_awcache;
  logic    [           AIC_HT_AXI_PROT_WIDTH-1:0] i_hp_axi_s_awprot;
  logic                                           i_hp_axi_s_awlock;
  logic                                           o_hp_axi_s_awready;
  // AXI write data channel
  logic                                           i_hp_axi_s_wvalid;
  logic                                           i_hp_axi_s_wlast;
  logic    [          AIC_HT_AXI_WSTRB_WIDTH-1:0] i_hp_axi_s_wstrb;
  logic    [           AIC_HT_AXI_DATA_WIDTH-1:0] i_hp_axi_s_wdata;
  logic                                           o_hp_axi_s_wready;
  // AXI write response channel
  logic                                           o_hp_axi_s_bvalid;
  logic    [           AIC_HT_AXI_S_ID_WIDTH-1:0] o_hp_axi_s_bid;
  logic    [           AIC_HT_AXI_RESP_WIDTH-1:0] o_hp_axi_s_bresp;
  logic                                           i_hp_axi_s_bready;
  // AXI read address channel
  logic                                           i_hp_axi_s_arvalid;
  logic    [           AIC_HT_AXI_ADDR_WIDTH-1:0] i_hp_axi_s_araddr;
  logic    [           AIC_HT_AXI_S_ID_WIDTH-1:0] i_hp_axi_s_arid;
  logic    [            AIC_HT_AXI_LEN_WIDTH-1:0] i_hp_axi_s_arlen;
  logic    [           AIC_HT_AXI_SIZE_WIDTH-1:0] i_hp_axi_s_arsize;
  logic    [     AIC_HT_AXI_BURST_TYPE_WIDTH-1:0] i_hp_axi_s_arburst;
  logic    [          AIC_HT_AXI_CACHE_WIDTH-1:0] i_hp_axi_s_arcache;
  logic    [           AIC_HT_AXI_PROT_WIDTH-1:0] i_hp_axi_s_arprot;
  logic                                           i_hp_axi_s_arlock;
  logic                                           o_hp_axi_s_arready;
  // AXI read data/response channel
  logic                                           o_hp_axi_s_rvalid;
  logic                                           o_hp_axi_s_rlast;
  logic    [           AIC_HT_AXI_S_ID_WIDTH-1:0] o_hp_axi_s_rid;
  logic    [           AIC_HT_AXI_DATA_WIDTH-1:0] o_hp_axi_s_rdata;
  logic    [           AIC_HT_AXI_RESP_WIDTH-1:0] o_hp_axi_s_rresp;
  logic                                           i_hp_axi_s_rready;

  // AXI4 Config port
  //--------------------------------------------------
  // AXI write address channel
  logic                                           i_cfg_axi_s_awvalid;
  logic    [           AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_awaddr;
  logic    [           AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_awid;
  logic    [            AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_awlen;
  logic    [           AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_awsize;
  logic    [     AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_awburst;
  logic                                           o_cfg_axi_s_awready;
  // AXI write data channel
  logic                                           i_cfg_axi_s_wvalid;
  logic                                           i_cfg_axi_s_wlast;
  logic    [          AIC_LT_AXI_WSTRB_WIDTH-1:0] i_cfg_axi_s_wstrb;
  logic    [           AIC_LT_AXI_DATA_WIDTH-1:0] i_cfg_axi_s_wdata;
  logic                                           o_cfg_axi_s_wready;
  // AXI write response channel
  logic                                           o_cfg_axi_s_bvalid;
  logic    [           AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_bid;
  logic    [           AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_bresp;
  logic                                           i_cfg_axi_s_bready;
  // AXI read address channel
  logic                                           i_cfg_axi_s_arvalid;
  logic    [           AIC_LT_AXI_ADDR_WIDTH-1:0] i_cfg_axi_s_araddr;
  logic    [           AIC_LT_AXI_S_ID_WIDTH-1:0] i_cfg_axi_s_arid;
  logic    [            AIC_LT_AXI_LEN_WIDTH-1:0] i_cfg_axi_s_arlen;
  logic    [           AIC_LT_AXI_SIZE_WIDTH-1:0] i_cfg_axi_s_arsize;
  logic    [     AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_cfg_axi_s_arburst;
  logic                                           o_cfg_axi_s_arready;
  // AXI read data/response channel
  logic                                           o_cfg_axi_s_rvalid;
  logic                                           o_cfg_axi_s_rlast;
  logic    [           AIC_LT_AXI_S_ID_WIDTH-1:0] o_cfg_axi_s_rid;
  logic    [           AIC_LT_AXI_DATA_WIDTH-1:0] o_cfg_axi_s_rdata;
  logic    [           AIC_LT_AXI_RESP_WIDTH-1:0] o_cfg_axi_s_rresp;
  logic                                           i_cfg_axi_s_rready;

  logic    [               AIC_CID_WIDTH-1:0]     i_cid;
  logic    [               AIC_DMC_OBS_DW-1:0]    o_dmc_obs;

  // RVV input
  logic                                           i_rvv_0_req_valid;
  logic                                           o_rvv_0_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_0_req_addr;
  logic                                           i_rvv_0_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_0_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_0_req_wdata;
  logic                                           o_rvv_0_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_0_res_rdata;
  logic                                           o_rvv_0_res_err;
  logic                                           i_rvv_1_req_valid;
  logic                                           o_rvv_1_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_1_req_addr;
  logic                                           i_rvv_1_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_1_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_1_req_wdata;
  logic                                           o_rvv_1_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_1_res_rdata;
  logic                                           o_rvv_1_res_err;
  logic                                           i_rvv_2_req_valid;
  logic                                           o_rvv_2_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_2_req_addr;
  logic                                           i_rvv_2_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_2_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_2_req_wdata;
  logic                                           o_rvv_2_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_2_res_rdata;
  logic                                           o_rvv_2_res_err;
  logic                                           i_rvv_3_req_valid;
  logic                                           o_rvv_3_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_3_req_addr;
  logic                                           i_rvv_3_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_3_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_3_req_wdata;
  logic                                           o_rvv_3_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_3_res_rdata;
  logic                                           o_rvv_3_res_err;
  logic                                           i_rvv_4_req_valid;
  logic                                           o_rvv_4_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_4_req_addr;
  logic                                           i_rvv_4_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_4_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_4_req_wdata;
  logic                                           o_rvv_4_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_4_res_rdata;
  logic                                           o_rvv_4_res_err;
  logic                                           i_rvv_5_req_valid;
  logic                                           o_rvv_5_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_5_req_addr;
  logic                                           i_rvv_5_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_5_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_5_req_wdata;
  logic                                           o_rvv_5_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_5_res_rdata;
  logic                                           o_rvv_5_res_err;
  logic                                           i_rvv_6_req_valid;
  logic                                           o_rvv_6_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_6_req_addr;
  logic                                           i_rvv_6_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_6_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_6_req_wdata;
  logic                                           o_rvv_6_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_6_res_rdata;
  logic                                           o_rvv_6_res_err;
  logic                                           i_rvv_7_req_valid;
  logic                                           o_rvv_7_req_ready;
  logic [cva6v_ai_core_pkg::MemPortAddrWidth-1:0] i_rvv_7_req_addr;
  logic                                           i_rvv_7_req_we;
  logic [cva6v_ai_core_pkg::MemPortBeWidth  -1:0] i_rvv_7_req_be;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] i_rvv_7_req_wdata;
  logic                                           o_rvv_7_res_valid;
  logic [cva6v_ai_core_pkg::MemPortWidth    -1:0] o_rvv_7_res_rdata;
  logic                                           o_rvv_7_res_err;

    /////////////// Token ////////////
    // IFD:
    // M IFD0
  logic [DMC_TOKENS_PROD-1:0] o_m_ifd0_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_m_ifd0_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_m_ifd0_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_m_ifd0_tok_cons_rdy;
    // M IFD1
  logic [DMC_TOKENS_PROD-1:0] o_m_ifd1_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_m_ifd1_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_m_ifd1_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_m_ifd1_tok_cons_rdy;
    // M IFD2
  logic [DMC_TOKENS_PROD-1:0] o_m_ifd2_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_m_ifd2_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_m_ifd2_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_m_ifd2_tok_cons_rdy;
    // M IFDW
  logic [DMC_TOKENS_PROD-1:0] o_m_ifdw_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_m_ifdw_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_m_ifdw_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_m_ifdw_tok_cons_rdy;
    // D IFD0
  logic [DMC_TOKENS_PROD-1:0] o_d_ifd0_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_d_ifd0_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_d_ifd0_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_d_ifd0_tok_cons_rdy;
    // D IFD1
  logic [DMC_TOKENS_PROD-1:0] o_d_ifd1_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_d_ifd1_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_d_ifd1_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_d_ifd1_tok_cons_rdy;
    // ODR:
    // M ODR
  logic [DMC_TOKENS_PROD-1:0] o_m_odr_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_m_odr_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_m_odr_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_m_odr_tok_cons_rdy;
    // D ODR:
  logic [DMC_TOKENS_PROD-1:0] o_d_odr_tok_prod_vld;
  logic [DMC_TOKENS_PROD-1:0] i_d_odr_tok_prod_rdy;
  logic [DMC_TOKENS_CONS-1:0] i_d_odr_tok_cons_vld;
  logic [DMC_TOKENS_CONS-1:0] o_d_odr_tok_cons_rdy;


  ////////////////////////////////////////////////
  //////// MID feedthrough
  /////////////// Token ////////////
  //// MVM EXE:
    // MID2LS:
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mid_mvm_exe_tok_prod_vld;
  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mid_mvm_exe_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mid_mvm_exe_tok_prod_rdy;
  logic [TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0] i_mid_mvm_exe_tok_cons_vld;
  //// MVM PRG:
    // MID2LS:
  logic [TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] i_mid_mvm_prg_tok_prod_vld;
  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mid_mvm_prg_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] i_mid_mvm_prg_tok_prod_rdy;
  logic [TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0] i_mid_mvm_prg_tok_cons_vld;
  //// IAU:
    // MID2LS:
  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_mid_iau_tok_prod_vld;
  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_mid_iau_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_M_IAU_NR_TOK_PROD-1:0] i_mid_iau_tok_prod_rdy;
  logic [TOK_MGR_M_IAU_NR_TOK_CONS-1:0] i_mid_iau_tok_cons_vld;
  //// DPU:
    // MID2LS:
  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_mid_dpu_tok_prod_vld;
  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_mid_dpu_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_M_DPU_NR_TOK_PROD-1:0] i_mid_dpu_tok_prod_rdy;
  logic [TOK_MGR_M_DPU_NR_TOK_CONS-1:0] i_mid_dpu_tok_cons_vld;

  /////////////// IRQ ////////////
  logic [2:0] i_mid_irq;

  /////////////// OBS ////////////
    // MID2LS:
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0]  i_mid_ts_start;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0]  i_mid_ts_end;
  logic [aic_mid_pkg::MID_NR_ENDPOINT_SETS-1:0]  i_mid_acd_sync;

  ////////////////////////////////////////////////
  //////// DID feedthrough
  /////////////// Token ////////////
  //// DWPU:
    // MID2LS:
  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_did_dwpu_tok_prod_vld;
  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_did_dwpu_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_D_DWPU_NR_TOK_PROD-1:0] i_did_dwpu_tok_prod_rdy;
  logic [TOK_MGR_D_DWPU_NR_TOK_CONS-1:0] i_did_dwpu_tok_cons_vld;
  //// IAU:
    // MID2LS:
  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_did_iau_tok_prod_vld;
  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_did_iau_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_D_IAU_NR_TOK_PROD-1:0] i_did_iau_tok_prod_rdy;
  logic [TOK_MGR_D_IAU_NR_TOK_CONS-1:0] i_did_iau_tok_cons_vld;
  //// DPU:
    // MID2LS:
  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_did_dpu_tok_prod_vld;
  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_did_dpu_tok_cons_rdy;
    // LS2AIC:
  logic [TOK_MGR_D_DPU_NR_TOK_PROD-1:0] i_did_dpu_tok_prod_rdy;
  logic [TOK_MGR_D_DPU_NR_TOK_CONS-1:0] i_did_dpu_tok_cons_vld;

  /////////////// IRQ ////////////
  logic [2:0] i_did_irq;

  /////////////// OBS ////////////
    // DID2LS:
  logic [AIC_DEV_OBS_DW-1:0] i_did_dwpu_obs;
  logic [AIC_DEV_OBS_DW-1:0]  i_did_iau_obs;
  logic [AIC_DEV_OBS_DW-1:0]  i_did_dpu_obs;

  //------------------------------------------------------
  // AXI write address channel
  logic                                   i_mid_cfg_axi_m_awready;
  // AXI write data channel
  logic                                   i_mid_cfg_axi_m_wready;
  // AXI write response channel
  logic                                   i_mid_cfg_axi_m_bvalid;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_mid_cfg_axi_m_bid;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_mid_cfg_axi_m_bresp;
  // AXI read address channel
  logic                                   i_mid_cfg_axi_m_arready;
  // AXI read data/response channel
  logic                                   i_mid_cfg_axi_m_rvalid;
  logic                                   i_mid_cfg_axi_m_rlast;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_mid_cfg_axi_m_rid;
  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_mid_cfg_axi_m_rdata;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_mid_cfg_axi_m_rresp;

    // CFG to DID:
  //------------------------------------------------------
  // AXI write address channel
  logic                                   i_did_cfg_axi_m_awready;
  // AXI write data channel
  logic                                   i_did_cfg_axi_m_wready;
  // AXI write response channel
  logic                                   i_did_cfg_axi_m_bvalid;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_did_cfg_axi_m_bid;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_did_cfg_axi_m_bresp;
  // AXI read address channel
  logic                                   i_did_cfg_axi_m_arready;
  // AXI read data/response channel
  logic                                   i_did_cfg_axi_m_rvalid;
  logic                                   i_did_cfg_axi_m_rlast;
  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_did_cfg_axi_m_rid;
  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_did_cfg_axi_m_rdata;
  logic [      AIC_LT_AXI_RESP_WIDTH-1:0] i_did_cfg_axi_m_rresp;

  //--------------------------------------------------
  //SRAM config signals
  //--------------------------------------------------
    /// Margin adjustment control selection
  logic [1:0] i_sram_mcs;
    /// Margin adjustment control selection write
  logic       i_sram_mcsw;
    /// Retention mode enable input pin (power gating)
  logic       i_sram_ret;
    /// Power down enable, active high (power gating)
  logic       i_sram_pde;
    /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
  logic [2:0] i_sram_adme;

  //--------------------------------------------------
  //RF config signals
  //--------------------------------------------------
    /// Margin adjustment control selection
  logic [1:0] i_rf_mcs;
    /// Margin adjustment control selection write
  logic       i_rf_mcsw;
    /// Retention mode enable input pin (power gating)
  logic       i_rf_ret;
    /// Power down enable, active high (power gating)
  logic       i_rf_pde;
    /// Margin adjustment for access disturbance margin enhancement (Vmin Feature Control Pins)
  logic [2:0] i_rf_adme;

  logic  ijtag_tck;
  logic  ijtag_reset;
  logic  ijtag_sel;
  logic  ijtag_ue;
  logic  ijtag_se;
  logic  ijtag_ce;
  logic  ijtag_si;
  logic  test_clk;
  logic  test_mode;
  logic  edt_update;
  logic  scan_en;
  logic [12-1: 0] scan_in;
  logic  bisr_clk;
  logic  bisr_reset;
  logic  bisr_shift_en;
  logic  bisr_si;

  // =============================================================================================================
  // Instantiate interfaces and BFMs and assignments
  // =============================================================================================================
  assign i_cid       = 'd1;

  //RVV is nonexistant for now

  //////// MID feedthrough assignments!
  assign i_mid_mvm_exe_tok_prod_vld = 0;
  assign i_mid_mvm_exe_tok_cons_rdy = 1'b1;
  assign i_mid_mvm_exe_tok_prod_rdy = 1'b1;
  assign i_mid_mvm_exe_tok_cons_vld = 0;
  assign i_mid_mvm_prg_tok_prod_vld = 0;
  assign i_mid_mvm_prg_tok_cons_rdy = 1'b1;
  assign i_mid_mvm_prg_tok_prod_rdy = 1'b1;
  assign i_mid_mvm_prg_tok_cons_vld = 0;
  assign i_mid_iau_tok_prod_vld = 0;
  assign i_mid_iau_tok_cons_rdy = 1'b1;
  assign i_mid_iau_tok_prod_rdy = 1'b1;
  assign i_mid_iau_tok_cons_vld = 0;
  assign i_mid_dpu_tok_prod_vld = 0;
  assign i_mid_dpu_tok_cons_rdy = 1'b1;
  assign i_mid_dpu_tok_prod_rdy = 1'b1;
  assign i_mid_dpu_tok_cons_vld = 0;
  assign i_mid_irq = 0;
  assign i_mid_ts_start = 0;
  assign i_mid_ts_end = 0;
  assign i_mid_acd_sync = 0;
  assign i_did_dwpu_tok_prod_vld = 0;
  assign i_did_dwpu_tok_cons_rdy = 1'b1;
  assign i_did_dwpu_tok_prod_rdy = 1'b1;
  assign i_did_dwpu_tok_cons_vld = 0;
  assign i_did_iau_tok_prod_vld = 0;
  assign i_did_iau_tok_cons_rdy = 1'b1;
  assign i_did_iau_tok_prod_rdy = 1'b1;
  assign i_did_iau_tok_cons_vld = 0;
  assign i_did_dpu_tok_prod_vld = 0;
  assign i_did_dpu_tok_cons_rdy = 1'b1;
  assign i_did_dpu_tok_prod_rdy = 1'b1;
  assign i_did_dpu_tok_cons_vld = 0;
  assign i_did_irq = 0;
  assign i_did_dwpu_obs = 0;
  assign i_did_iau_obs = 0;
  assign i_did_dpu_obs = 0;
  assign i_mid_cfg_axi_m_awready = 1'b1;
  assign i_mid_cfg_axi_m_wready = 1'b1;
  assign i_mid_cfg_axi_m_bvalid = 0;
  assign i_mid_cfg_axi_m_bid = 0;
  assign i_mid_cfg_axi_m_bresp = 0;
  assign i_mid_cfg_axi_m_arready = 1'b1;
  assign i_mid_cfg_axi_m_rvalid = 0;
  assign i_mid_cfg_axi_m_rlast = 0;
  assign i_mid_cfg_axi_m_rid = 0;
  assign i_mid_cfg_axi_m_rdata = 0;
  assign i_mid_cfg_axi_m_rresp = 0;
  assign i_did_cfg_axi_m_awready = 1'b1;
  assign i_did_cfg_axi_m_wready = 1'b1;
  assign i_did_cfg_axi_m_bvalid = 0;
  assign i_did_cfg_axi_m_bid = 0;
  assign i_did_cfg_axi_m_bresp = 0;
  assign i_did_cfg_axi_m_arready = 1'b1;
  assign i_did_cfg_axi_m_rvalid = 0;
  assign i_did_cfg_axi_m_rlast = 0;
  assign i_did_cfg_axi_m_rid = 0;
  assign i_did_cfg_axi_m_rdata = 0;
  assign i_did_cfg_axi_m_rresp = 0;
  assign i_sram_mcs = 0;
  assign i_sram_mcsw = 0;
  assign i_sram_ret = 0;
  assign i_sram_pde = 0;
  assign i_sram_adme = 0;
  assign i_rf_mcs = 0;
  assign i_rf_mcsw = 0;
  assign i_rf_ret = 0;
  assign i_rf_pde = 0;
  assign i_rf_adme = 0;
  assign ijtag_tck = 0;
  assign ijtag_reset = 0;
  assign ijtag_sel = 0;
  assign ijtag_ue = 0;
  assign ijtag_se = 0;
  assign ijtag_ce = 0;
  assign ijtag_si = 0;
  assign test_clk = 0;
  assign test_mode = 0;
  assign edt_update = 0;
  assign scan_en = 0;
  assign scan_in = 0;
  assign bisr_clk = 0;
  assign bisr_reset = 0;
  assign bisr_shift_en = 0;
  assign bisr_si = 0;
  // assign i_m_ifd0_tok_prod_rdy = '1;  // TODO: all of the token signals will be moved to token agent once it's fully ready
  // assign i_m_ifd0_tok_cons_vld = '1;
  // assign i_m_ifd1_tok_prod_rdy = '1;
  // assign i_m_ifd1_tok_cons_vld = '1;
  // assign i_m_ifd2_tok_prod_rdy = '1;
  // assign i_m_ifd2_tok_cons_vld = '1;
  // assign i_m_ifdw_tok_prod_rdy = '1;
  // assign i_m_ifdw_tok_cons_vld = '1;
  // assign i_d_ifd0_tok_prod_rdy = '1;
  // assign i_d_ifd0_tok_cons_vld = '1;
  // assign i_d_ifd1_tok_prod_rdy = '1;
  // assign i_d_ifd1_tok_cons_vld = '1;
  // assign i_m_odr_tok_prod_rdy = '1;
  // assign i_m_odr_tok_cons_vld = '1;
  // assign i_d_odr_tok_prod_rdy = '1;
  // assign i_d_odr_tok_cons_vld = '1;

  // =============================================================================================================
  // Assign the reset pin from the reset interface to the reset pins from the VIP interface.
  // =============================================================================================================
`ifdef AXI_VIP
  assign axi_if.master_if[0].aresetn = axi_reset_if.reset; // LS CFG Slave Interface
  assign axi_if.master_if[1].aresetn = axi_reset_if.reset; // LS HP Slave Interface
  assign axi_if.master_if[2].aresetn = axi_reset_if.reset; // LS MVM ODR Slave Interface
  assign axi_if.master_if[3].aresetn = axi_reset_if.reset; // LS DWPU ODR Slave Interface

  assign axi_if.slave_if[0].aresetn  = axi_reset_if.reset; // LS MVM_IFD0 Master Interface
  assign axi_if.slave_if[1].aresetn  = axi_reset_if.reset; // LS MVM_IFD1 Master Interface
  assign axi_if.slave_if[2].aresetn  = axi_reset_if.reset; // LS MVM_IFD2 Master Interface
  assign axi_if.slave_if[3].aresetn  = axi_reset_if.reset; // LS MVM_IFDw Master Interface
  assign axi_if.slave_if[4].aresetn  = axi_reset_if.reset; // LS DWPU_IFD0 Master Interface
  assign axi_if.slave_if[5].aresetn  = axi_reset_if.reset; // LS DWPU_IFD0 Master Interface
  assign i_rst_n                     = axi_reset_if.reset;
`endif

 `include "aic_ls_dmc_connections.svh"
 `include "bind_aic_ls.svh"



  // =============================================================================================================
  // this part is an interface to check coverage. TODO: get back to this later on.
  // =============================================================================================================
  aic_ls_if if_aic_ls(`LS_DUT_PATH.i_clk);  // IF to check coverage

  logic                                           l1_cg_enable;
  logic                                           dmc_cg_enable;
  logic    [                                 1:0] l1_sw_cfg_fabric_sel;
  logic                                           l1_mem_ls;
  logic                                           l1_mem_ds;
  logic                                           l1_mem_sd;
  logic                                           l1_mem_rop;
  logic                                           l1_mem_daisy_chain_bypass_sd;
  logic                                           l1_mem_daisy_chain_bypass_ds;
  logic    [                                 6:0] l1_lc_fabric_dlock;
  logic                                           sram_sw_test1;
  logic                                           sram_sw_test_rnm;
  logic                                           sram_sw_rme;
  logic                                     [3:0] sram_sw_rm;
  logic                                     [2:0] sram_sw_wa;
  logic                                     [2:0] sram_sw_wpulse;
  logic                                           sram_sw_fiso;
  logic                                           ls_cg_en;

  // Hard-coded values
  // assign l1_mem_ls = 0;
  // assign l1_mem_ds = 0;
  // assign l1_mem_sd = 0;
  // assign l1_cg_enable = 1'b0;
  // assign dmc_cg_enable = 1'b0;
  // assign l1_mem_daisy_chain_bypass_ds = 1'b1;
  // assign l1_mem_daisy_chain_bypass_sd = 1'b1;
  // assign sram_sw_test1 = 1'b0;
  // assign sram_sw_test_rnm = 1'b0;
  // assign sram_sw_rme = 1'b0;
  // assign sram_sw_rm = 4'h4;
  // assign sram_sw_wa = 3'h4;
  // assign sram_sw_wpulse = 3'b000;
  // assign sram_sw_fiso = 1'b0;
  // assign ls_cg_en = 1'b1;
  // assign l1_sw_cfg_fabric_sel='0;

  assign if_aic_ls.reset_an_i                   = i_rst_n;
  assign if_aic_ls.cid                          = i_cid;
  assign if_aic_ls.l1_cg_enable                 = l1_cg_enable;
  assign if_aic_ls.dmc_cg_enable            = dmc_cg_enable;
  assign if_aic_ls.l1_sw_cfg_fabric_sel         = l1_sw_cfg_fabric_sel;
  assign if_aic_ls.l1_mem_ls                    = l1_mem_ls;
  assign if_aic_ls.l1_mem_ds                    = l1_mem_ds;
  assign if_aic_ls.l1_mem_sd                    = l1_mem_sd;
  assign if_aic_ls.l1_mem_rop                   = l1_mem_rop;
  assign if_aic_ls.l1_mem_daisy_chain_bypass_sd = l1_mem_daisy_chain_bypass_sd;
  assign if_aic_ls.l1_mem_daisy_chain_bypass_ds = l1_mem_daisy_chain_bypass_ds;
  assign if_aic_ls.aic_ls_obs                   = o_dmc_obs;
  assign if_aic_ls.l1_lc_fabric_dlock           = l1_lc_fabric_dlock;
  assign if_aic_ls.sram_sw_test1                = sram_sw_test1;
  assign if_aic_ls.sram_sw_test_rnm             = sram_sw_test_rnm;
  assign if_aic_ls.sram_sw_rme                  = sram_sw_rme;
  assign if_aic_ls.sram_sw_rm                   = sram_sw_rm;
  assign if_aic_ls.sram_sw_wa                   = sram_sw_wa;
  assign if_aic_ls.sram_sw_wpulse               = sram_sw_wpulse;
  assign if_aic_ls.sram_sw_fiso                 = sram_sw_fiso;
  assign if_aic_ls.ls_cg_en                     = ls_cg_en;
  assign if_aic_ls.irq_out                      = o_dmc_irq;
  // end of coverage IF

`ifdef AXI_VIP
  // VIP Interface instance representing the AXI system
  svt_axi_if axi_if ();
  assign axi_if.common_aclk = `LS_DUT_PATH.i_clk;
  // TB Interface instance to provide access to the reset signal
  axi_reset_if axi_reset_if ();
  assign axi_reset_if.clk = `LS_DUT_PATH.i_clk;
`endif

  // Use gated clock for IFD-ODR IF's
  dmc_addr_gen_if if_m_ifd0(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_ifd1(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_ifd2(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_ifdw(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_m_odr(`LS_DUT_PATH.i_clk);

  dmc_addr_gen_if if_d_ifd0(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_d_ifd1(`LS_DUT_PATH.i_clk);
  dmc_addr_gen_if if_d_odr(`LS_DUT_PATH.i_clk);

 `ifndef AI_CORE_TOP_ENV_CHECK
  // =============================================================================================================
  // AXI VIP MASTER INTERFACES
  // =============================================================================================================

  //----------------------------------------------------------
  // AXI: LS Configuration Interface -> VIP Master Interface
  //----------------------------------------------------------
`ifdef AXI_VIP_CONN_CFG
  assign i_cfg_axi_s_awvalid = axi_if.master_if[0].awvalid;
  assign i_cfg_axi_s_awaddr  = axi_if.master_if[0].awaddr;
  assign i_cfg_axi_s_awid    = axi_if.master_if[0].awid;
  assign i_cfg_axi_s_awlen   = axi_if.master_if[0].awlen;
  assign i_cfg_axi_s_awsize  = axi_if.master_if[0].awsize;
  assign i_cfg_axi_s_awburst = axi_if.master_if[0].awburst;

  assign axi_if.master_if[0].awready = o_cfg_axi_s_awready;

  assign i_cfg_axi_s_wvalid  = axi_if.master_if[0].wvalid;
  assign i_cfg_axi_s_wlast   = axi_if.master_if[0].wlast;
  assign i_cfg_axi_s_wdata   = axi_if.master_if[0].wdata;
  assign i_cfg_axi_s_wstrb   = axi_if.master_if[0].wstrb;

  assign axi_if.master_if[0].wready = o_cfg_axi_s_wready;

  assign axi_if.master_if[0].bvalid = o_cfg_axi_s_bvalid;
  assign axi_if.master_if[0].bid    = o_cfg_axi_s_bid;
  assign axi_if.master_if[0].bresp  = o_cfg_axi_s_bresp;

  assign i_cfg_axi_s_bready  = axi_if.master_if[0].bready;
  assign i_cfg_axi_s_arvalid = axi_if.master_if[0].arvalid;
  assign i_cfg_axi_s_araddr  = axi_if.master_if[0].araddr;
  assign i_cfg_axi_s_arid    = axi_if.master_if[0].arid;
  assign i_cfg_axi_s_arlen   = axi_if.master_if[0].arlen;
  assign i_cfg_axi_s_arsize  = axi_if.master_if[0].arsize;
  assign i_cfg_axi_s_arburst = axi_if.master_if[0].arburst;

  assign axi_if.master_if[0].arready = o_cfg_axi_s_arready;

  assign axi_if.master_if[0].rvalid = o_cfg_axi_s_rvalid;
  assign axi_if.master_if[0].rlast  = o_cfg_axi_s_rlast;
  assign axi_if.master_if[0].rid    = o_cfg_axi_s_rid;
  assign axi_if.master_if[0].rdata  = o_cfg_axi_s_rdata;
  assign axi_if.master_if[0].rresp  = o_cfg_axi_s_rresp;

  assign i_cfg_axi_s_rready  = axi_if.master_if[0].rready;
`endif


`ifdef AXI_VIP_CONN_M
  assign i_hp_axi_s_awvalid = axi_if.master_if[1].awvalid;
  assign i_hp_axi_s_awaddr  = axi_if.master_if[1].awaddr;
  assign i_hp_axi_s_awid    = axi_if.master_if[1].awid;
  assign i_hp_axi_s_awlen   = axi_if.master_if[1].awlen;
  assign i_hp_axi_s_awsize  = axi_if.master_if[1].awsize;
  assign i_hp_axi_s_awburst = axi_if.master_if[1].awburst;
  assign i_hp_axi_s_awlock  = axi_if.master_if[1].awlock;
  assign i_hp_axi_s_awcache = axi_if.master_if[1].awcache;
  assign i_hp_axi_s_awprot  = axi_if.master_if[1].awprot;

  assign axi_if.master_if[1].awready = o_hp_axi_s_awready;

  assign i_hp_axi_s_wvalid  = axi_if.master_if[1].wvalid;
  assign i_hp_axi_s_wlast   = axi_if.master_if[1].wlast;
  assign i_hp_axi_s_wdata   = axi_if.master_if[1].wdata;
  assign i_hp_axi_s_wstrb   = axi_if.master_if[1].wstrb;

  assign axi_if.master_if[1].wready = o_hp_axi_s_wready;

  assign axi_if.master_if[1].bvalid = o_hp_axi_s_bvalid;
  assign axi_if.master_if[1].bid    = o_hp_axi_s_bid;
  assign axi_if.master_if[1].bresp  = o_hp_axi_s_bresp;

  assign i_hp_axi_s_bready  = axi_if.master_if[1].bready;
  assign i_hp_axi_s_arvalid = axi_if.master_if[1].arvalid;
  assign i_hp_axi_s_araddr  = axi_if.master_if[1].araddr;
  assign i_hp_axi_s_arid    = axi_if.master_if[1].arid;
  assign i_hp_axi_s_arlen   = axi_if.master_if[1].arlen;
  assign i_hp_axi_s_arsize  = axi_if.master_if[1].arsize;
  assign i_hp_axi_s_arburst = axi_if.master_if[1].arburst;
  assign i_hp_axi_s_arlock  = axi_if.master_if[1].arlock;
  assign i_hp_axi_s_arcache = axi_if.master_if[1].arcache;
  assign i_hp_axi_s_arprot  = axi_if.master_if[1].arprot;

  assign axi_if.master_if[1].arready = o_hp_axi_s_arready;

  assign axi_if.master_if[1].rvalid = o_hp_axi_s_rvalid;
  assign axi_if.master_if[1].rlast  = o_hp_axi_s_rlast;
  assign axi_if.master_if[1].rid    = o_hp_axi_s_rid;
  assign axi_if.master_if[1].rdata  = o_hp_axi_s_rdata;
  assign axi_if.master_if[1].rresp  = o_hp_axi_s_rresp;

  assign i_hp_axi_s_rready  = axi_if.master_if[1].rready;
`endif

  //------------------------------------------------------
  // AXIS: LS Slaves -> VIP Master Interfaces
  //------------------------------------------------------
  // MVM ODR
  assign i_m_odr_axis_s_tvalid       = axi_if.master_if[2].tvalid; // Input
  assign axi_if.master_if[2].tready  = o_m_odr_axis_s_tready;      // Output
  assign i_m_odr_axis_s_tdata        = axi_if.master_if[2].tdata;  // Input
  assign i_m_odr_axis_s_tlast        = axi_if.master_if[2].tlast;  // Input
  // DWPU ODR
  assign i_d_odr_axis_s_tvalid      = axi_if.master_if[3].tvalid; // Input
  assign axi_if.master_if[3].tready  = o_d_odr_axis_s_tready;     // Output
  assign i_d_odr_axis_s_tdata       = axi_if.master_if[3].tdata;  // Input
  assign i_d_odr_axis_s_tlast       = axi_if.master_if[3].tlast;  // Input

  //------------------------------------------------------
  // AXIS: LS Masters -> VIP Slave Interfaces
  //------------------------------------------------------
  // MVM IFD0
  assign axi_if.slave_if[0].tvalid = o_m_ifd0_axis_m_tvalid;
  assign i_m_ifd0_axis_m_tready    = axi_if.slave_if[0].tready;
  assign axi_if.slave_if[0].tdata  = o_m_ifd0_axis_m_tdata;
  assign axi_if.slave_if[0].tlast  = o_m_ifd0_axis_m_tlast;

  // MVM IFD1
  assign axi_if.slave_if[1].tvalid = o_m_ifd1_axis_m_tvalid;
  assign i_m_ifd1_axis_m_tready    = axi_if.slave_if[1].tready;
  assign axi_if.slave_if[1].tdata  = o_m_ifd1_axis_m_tdata;
  assign axi_if.slave_if[1].tlast  = o_m_ifd1_axis_m_tlast;

   // MVM IFD2
  assign axi_if.slave_if[2].tvalid = o_m_ifd2_axis_m_tvalid;
  assign i_m_ifd2_axis_m_tready    = axi_if.slave_if[2].tready;
  assign axi_if.slave_if[2].tdata  = o_m_ifd2_axis_m_tdata;
  assign axi_if.slave_if[2].tlast  = o_m_ifd2_axis_m_tlast;

  // MVM IFDW
  assign axi_if.slave_if[3].tvalid = o_m_ifdw_axis_m_tvalid;
  assign i_m_ifdw_axis_m_tready    = axi_if.slave_if[3].tready;
  assign axi_if.slave_if[3].tdata  = o_m_ifdw_axis_m_tdata;
  assign axi_if.slave_if[3].tlast  = o_m_ifdw_axis_m_tlast;

  // DW IFD0
  assign axi_if.slave_if[4].tvalid = o_d_ifd0_axis_m_tvalid;
  assign i_d_ifd0_axis_m_tready   = axi_if.slave_if[4].tready;
  assign axi_if.slave_if[4].tdata  = o_d_ifd0_axis_m_tdata;
  assign axi_if.slave_if[4].tlast  = o_d_ifd0_axis_m_tlast;

  // DW IFD1
  assign axi_if.slave_if[5].tvalid = o_d_ifd1_axis_m_tvalid;
  assign i_d_ifd1_axis_m_tready   = axi_if.slave_if[5].tready;
  assign axi_if.slave_if[5].tdata  = o_d_ifd1_axis_m_tdata;
  assign axi_if.slave_if[5].tlast  = o_d_ifd1_axis_m_tlast;
  `endif // `ifdef AI_CORE_TOP_ENV_CHECK
  // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
`ifndef NO_DUT
  aic_ls_p dut ( // Putting signals one by one, so that the feedthrough signals are not needed.
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .o_dmc_irq(o_dmc_irq),
    .o_m_ifd0_axis_m_tvalid(o_m_ifd0_axis_m_tvalid),
    .i_m_ifd0_axis_m_tready(i_m_ifd0_axis_m_tready),
    .o_m_ifd0_axis_m_tdata(o_m_ifd0_axis_m_tdata),
    .o_m_ifd0_axis_m_tlast(o_m_ifd0_axis_m_tlast),
    .o_m_ifd1_axis_m_tvalid(o_m_ifd1_axis_m_tvalid),
    .i_m_ifd1_axis_m_tready(i_m_ifd1_axis_m_tready),
    .o_m_ifd1_axis_m_tdata(o_m_ifd1_axis_m_tdata),
    .o_m_ifd1_axis_m_tlast(o_m_ifd1_axis_m_tlast),
    .o_m_ifd2_axis_m_tvalid(o_m_ifd2_axis_m_tvalid),
    .i_m_ifd2_axis_m_tready(i_m_ifd2_axis_m_tready),
    .o_m_ifd2_axis_m_tdata(o_m_ifd2_axis_m_tdata),
    .o_m_ifd2_axis_m_tlast(o_m_ifd2_axis_m_tlast),
    .o_m_ifdw_axis_m_tvalid(o_m_ifdw_axis_m_tvalid),
    .i_m_ifdw_axis_m_tready(i_m_ifdw_axis_m_tready),
    .o_m_ifdw_axis_m_tdata(o_m_ifdw_axis_m_tdata),
    .o_m_ifdw_axis_m_tlast(o_m_ifdw_axis_m_tlast),
    .o_d_ifd0_axis_m_tvalid(o_d_ifd0_axis_m_tvalid),
    .i_d_ifd0_axis_m_tready(i_d_ifd0_axis_m_tready),
    .o_d_ifd0_axis_m_tdata(o_d_ifd0_axis_m_tdata),
    .o_d_ifd0_axis_m_tlast(o_d_ifd0_axis_m_tlast),
    .o_d_ifd1_axis_m_tvalid(o_d_ifd1_axis_m_tvalid),
    .i_d_ifd1_axis_m_tready(i_d_ifd1_axis_m_tready),
    .o_d_ifd1_axis_m_tdata(o_d_ifd1_axis_m_tdata),
    .o_d_ifd1_axis_m_tlast(o_d_ifd1_axis_m_tlast),
    .i_m_odr_axis_s_tvalid(i_m_odr_axis_s_tvalid),
    .o_m_odr_axis_s_tready(o_m_odr_axis_s_tready),
    .i_m_odr_axis_s_tdata(i_m_odr_axis_s_tdata),
    .i_m_odr_axis_s_tlast(i_m_odr_axis_s_tlast),
    .i_d_odr_axis_s_tvalid(i_d_odr_axis_s_tvalid),
    .o_d_odr_axis_s_tready(o_d_odr_axis_s_tready),
    .i_d_odr_axis_s_tdata(i_d_odr_axis_s_tdata),
    .i_d_odr_axis_s_tlast(i_d_odr_axis_s_tlast),
    .i_rvv_0_req_valid(i_rvv_0_req_valid),
    .o_rvv_0_req_ready(o_rvv_0_req_ready),
    .i_rvv_0_req_addr(i_rvv_0_req_addr),
    .i_rvv_0_req_we(i_rvv_0_req_we),
    .i_rvv_0_req_be(i_rvv_0_req_be),
    .i_rvv_0_req_wdata(i_rvv_0_req_wdata),
    .o_rvv_0_res_valid(o_rvv_0_res_valid),
    .o_rvv_0_res_rdata(o_rvv_0_res_rdata),
    .o_rvv_0_res_err(o_rvv_0_res_err),
    .i_rvv_1_req_valid(i_rvv_1_req_valid),
    .o_rvv_1_req_ready(o_rvv_1_req_ready),
    .i_rvv_1_req_addr(i_rvv_1_req_addr),
    .i_rvv_1_req_we(i_rvv_1_req_we),
    .i_rvv_1_req_be(i_rvv_1_req_be),
    .i_rvv_1_req_wdata(i_rvv_1_req_wdata),
    .o_rvv_1_res_valid(o_rvv_1_res_valid),
    .o_rvv_1_res_rdata(o_rvv_1_res_rdata),
    .o_rvv_1_res_err(o_rvv_1_res_err),
    .i_rvv_2_req_valid(i_rvv_2_req_valid),
    .o_rvv_2_req_ready(o_rvv_2_req_ready),
    .i_rvv_2_req_addr(i_rvv_2_req_addr),
    .i_rvv_2_req_we(i_rvv_2_req_we),
    .i_rvv_2_req_be(i_rvv_2_req_be),
    .i_rvv_2_req_wdata(i_rvv_2_req_wdata),
    .o_rvv_2_res_valid(o_rvv_2_res_valid),
    .o_rvv_2_res_rdata(o_rvv_2_res_rdata),
    .o_rvv_2_res_err(o_rvv_2_res_err),
    .i_rvv_3_req_valid(i_rvv_3_req_valid),
    .o_rvv_3_req_ready(o_rvv_3_req_ready),
    .i_rvv_3_req_addr(i_rvv_3_req_addr),
    .i_rvv_3_req_we(i_rvv_3_req_we),
    .i_rvv_3_req_be(i_rvv_3_req_be),
    .i_rvv_3_req_wdata(i_rvv_3_req_wdata),
    .o_rvv_3_res_valid(o_rvv_3_res_valid),
    .o_rvv_3_res_rdata(o_rvv_3_res_rdata),
    .o_rvv_3_res_err(o_rvv_3_res_err),
    .i_rvv_4_req_valid(i_rvv_4_req_valid),
    .o_rvv_4_req_ready(o_rvv_4_req_ready),
    .i_rvv_4_req_addr(i_rvv_4_req_addr),
    .i_rvv_4_req_we(i_rvv_4_req_we),
    .i_rvv_4_req_be(i_rvv_4_req_be),
    .i_rvv_4_req_wdata(i_rvv_4_req_wdata),
    .o_rvv_4_res_valid(o_rvv_4_res_valid),
    .o_rvv_4_res_rdata(o_rvv_4_res_rdata),
    .o_rvv_4_res_err(o_rvv_4_res_err),
    .i_rvv_5_req_valid(i_rvv_5_req_valid),
    .o_rvv_5_req_ready(o_rvv_5_req_ready),
    .i_rvv_5_req_addr(i_rvv_5_req_addr),
    .i_rvv_5_req_we(i_rvv_5_req_we),
    .i_rvv_5_req_be(i_rvv_5_req_be),
    .i_rvv_5_req_wdata(i_rvv_5_req_wdata),
    .o_rvv_5_res_valid(o_rvv_5_res_valid),
    .o_rvv_5_res_rdata(o_rvv_5_res_rdata),
    .o_rvv_5_res_err(o_rvv_5_res_err),
    .i_rvv_6_req_valid(i_rvv_6_req_valid),
    .o_rvv_6_req_ready(o_rvv_6_req_ready),
    .i_rvv_6_req_addr(i_rvv_6_req_addr),
    .i_rvv_6_req_we(i_rvv_6_req_we),
    .i_rvv_6_req_be(i_rvv_6_req_be),
    .i_rvv_6_req_wdata(i_rvv_6_req_wdata),
    .o_rvv_6_res_valid(o_rvv_6_res_valid),
    .o_rvv_6_res_rdata(o_rvv_6_res_rdata),
    .o_rvv_6_res_err(o_rvv_6_res_err),
    .i_rvv_7_req_valid(i_rvv_7_req_valid),
    .o_rvv_7_req_ready(o_rvv_7_req_ready),
    .i_rvv_7_req_addr(i_rvv_7_req_addr),
    .i_rvv_7_req_we(i_rvv_7_req_we),
    .i_rvv_7_req_be(i_rvv_7_req_be),
    .i_rvv_7_req_wdata(i_rvv_7_req_wdata),
    .o_rvv_7_res_valid(o_rvv_7_res_valid),
    .o_rvv_7_res_rdata(o_rvv_7_res_rdata),
    .o_rvv_7_res_err(o_rvv_7_res_err),
    .o_m_ifd0_tok_prod_vld(o_m_ifd0_tok_prod_vld),
    .i_m_ifd0_tok_prod_rdy(i_m_ifd0_tok_prod_rdy),
    .i_m_ifd0_tok_cons_vld(i_m_ifd0_tok_cons_vld),
    .o_m_ifd0_tok_cons_rdy(o_m_ifd0_tok_cons_rdy),
    .o_m_ifd1_tok_prod_vld(o_m_ifd1_tok_prod_vld),
    .i_m_ifd1_tok_prod_rdy(i_m_ifd1_tok_prod_rdy),
    .i_m_ifd1_tok_cons_vld(i_m_ifd1_tok_cons_vld),
    .o_m_ifd1_tok_cons_rdy(o_m_ifd1_tok_cons_rdy),
    .o_m_ifd2_tok_prod_vld(o_m_ifd2_tok_prod_vld),
    .i_m_ifd2_tok_prod_rdy(i_m_ifd2_tok_prod_rdy),
    .i_m_ifd2_tok_cons_vld(i_m_ifd2_tok_cons_vld),
    .o_m_ifd2_tok_cons_rdy(o_m_ifd2_tok_cons_rdy),
    .o_m_ifdw_tok_prod_vld(o_m_ifdw_tok_prod_vld),
    .i_m_ifdw_tok_prod_rdy(i_m_ifdw_tok_prod_rdy),
    .i_m_ifdw_tok_cons_vld(i_m_ifdw_tok_cons_vld),
    .o_m_ifdw_tok_cons_rdy(o_m_ifdw_tok_cons_rdy),
    .o_d_ifd0_tok_prod_vld(o_d_ifd0_tok_prod_vld),
    .i_d_ifd0_tok_prod_rdy(i_d_ifd0_tok_prod_rdy),
    .i_d_ifd0_tok_cons_vld(i_d_ifd0_tok_cons_vld),
    .o_d_ifd0_tok_cons_rdy(o_d_ifd0_tok_cons_rdy),
    .o_d_ifd1_tok_prod_vld(o_d_ifd1_tok_prod_vld),
    .i_d_ifd1_tok_prod_rdy(i_d_ifd1_tok_prod_rdy),
    .i_d_ifd1_tok_cons_vld(i_d_ifd1_tok_cons_vld),
    .o_d_ifd1_tok_cons_rdy(o_d_ifd1_tok_cons_rdy),
    .o_m_odr_tok_prod_vld(o_m_odr_tok_prod_vld),
    .i_m_odr_tok_prod_rdy(i_m_odr_tok_prod_rdy),
    .i_m_odr_tok_cons_vld(i_m_odr_tok_cons_vld),
    .o_m_odr_tok_cons_rdy(o_m_odr_tok_cons_rdy),
    .o_d_odr_tok_prod_vld(o_d_odr_tok_prod_vld),
    .i_d_odr_tok_prod_rdy(i_d_odr_tok_prod_rdy),
    .i_d_odr_tok_cons_vld(i_d_odr_tok_cons_vld),
    .o_d_odr_tok_cons_rdy(o_d_odr_tok_cons_rdy),
    .i_hp_axi_s_awvalid(i_hp_axi_s_awvalid),
    .i_hp_axi_s_awaddr(i_hp_axi_s_awaddr),
    .i_hp_axi_s_awid(i_hp_axi_s_awid),
    .i_hp_axi_s_awlen(i_hp_axi_s_awlen),
    .i_hp_axi_s_awsize(i_hp_axi_s_awsize),
    .i_hp_axi_s_awburst(i_hp_axi_s_awburst),
    .i_hp_axi_s_awcache(i_hp_axi_s_awcache),
    .i_hp_axi_s_awprot(i_hp_axi_s_awprot),
    .i_hp_axi_s_awlock(i_hp_axi_s_awlock),
    .o_hp_axi_s_awready(o_hp_axi_s_awready),
    .i_hp_axi_s_wvalid(i_hp_axi_s_wvalid),
    .i_hp_axi_s_wlast(i_hp_axi_s_wlast),
    .i_hp_axi_s_wstrb(i_hp_axi_s_wstrb),
    .i_hp_axi_s_wdata(i_hp_axi_s_wdata),
    .o_hp_axi_s_wready(o_hp_axi_s_wready),
    .o_hp_axi_s_bvalid(o_hp_axi_s_bvalid),
    .o_hp_axi_s_bid(o_hp_axi_s_bid),
    .o_hp_axi_s_bresp(o_hp_axi_s_bresp),
    .i_hp_axi_s_bready(i_hp_axi_s_bready),
    .i_hp_axi_s_arvalid(i_hp_axi_s_arvalid),
    .i_hp_axi_s_araddr(i_hp_axi_s_araddr),
    .i_hp_axi_s_arid(i_hp_axi_s_arid),
    .i_hp_axi_s_arlen(i_hp_axi_s_arlen),
    .i_hp_axi_s_arsize(i_hp_axi_s_arsize),
    .i_hp_axi_s_arburst(i_hp_axi_s_arburst),
    .i_hp_axi_s_arcache(i_hp_axi_s_arcache),
    .i_hp_axi_s_arprot(i_hp_axi_s_arprot),
    .i_hp_axi_s_arlock(i_hp_axi_s_arlock),
    .o_hp_axi_s_arready(o_hp_axi_s_arready),
    .o_hp_axi_s_rvalid(o_hp_axi_s_rvalid),
    .o_hp_axi_s_rlast(o_hp_axi_s_rlast),
    .o_hp_axi_s_rid(o_hp_axi_s_rid),
    .o_hp_axi_s_rdata(o_hp_axi_s_rdata),
    .o_hp_axi_s_rresp(o_hp_axi_s_rresp),
    .i_hp_axi_s_rready(i_hp_axi_s_rready),
    .i_cfg_axi_s_awvalid(i_cfg_axi_s_awvalid),
    .i_cfg_axi_s_awaddr(i_cfg_axi_s_awaddr),
    .i_cfg_axi_s_awid(i_cfg_axi_s_awid),
    .i_cfg_axi_s_awlen(i_cfg_axi_s_awlen),
    .i_cfg_axi_s_awsize(i_cfg_axi_s_awsize),
    .i_cfg_axi_s_awburst(i_cfg_axi_s_awburst),
    .o_cfg_axi_s_awready(o_cfg_axi_s_awready),
    .i_cfg_axi_s_wvalid(i_cfg_axi_s_wvalid),
    .i_cfg_axi_s_wlast(i_cfg_axi_s_wlast),
    .i_cfg_axi_s_wstrb(i_cfg_axi_s_wstrb),
    .i_cfg_axi_s_wdata(i_cfg_axi_s_wdata),
    .o_cfg_axi_s_wready(o_cfg_axi_s_wready),
    .o_cfg_axi_s_bvalid(o_cfg_axi_s_bvalid),
    .o_cfg_axi_s_bid(o_cfg_axi_s_bid),
    .o_cfg_axi_s_bresp(o_cfg_axi_s_bresp),
    .i_cfg_axi_s_bready(i_cfg_axi_s_bready),
    .i_cfg_axi_s_arvalid(i_cfg_axi_s_arvalid),
    .i_cfg_axi_s_araddr(i_cfg_axi_s_araddr),
    .i_cfg_axi_s_arid(i_cfg_axi_s_arid),
    .i_cfg_axi_s_arlen(i_cfg_axi_s_arlen),
    .i_cfg_axi_s_arsize(i_cfg_axi_s_arsize),
    .i_cfg_axi_s_arburst(i_cfg_axi_s_arburst),
    .o_cfg_axi_s_arready(o_cfg_axi_s_arready),
    .o_cfg_axi_s_rvalid(o_cfg_axi_s_rvalid),
    .o_cfg_axi_s_rlast(o_cfg_axi_s_rlast),
    .o_cfg_axi_s_rid(o_cfg_axi_s_rid),
    .o_cfg_axi_s_rdata(o_cfg_axi_s_rdata),
    .o_cfg_axi_s_rresp(o_cfg_axi_s_rresp),
    .i_cfg_axi_s_rready(i_cfg_axi_s_rready),
    .i_cid(i_cid),
    .o_dmc_obs(o_dmc_obs),
    .i_mid_mvm_exe_tok_prod_vld(i_mid_mvm_exe_tok_prod_vld),
    .i_mid_mvm_exe_tok_cons_rdy(i_mid_mvm_exe_tok_cons_rdy),
    .i_mid_mvm_exe_tok_prod_rdy(i_mid_mvm_exe_tok_prod_rdy),
    .i_mid_mvm_exe_tok_cons_vld(i_mid_mvm_exe_tok_cons_vld),
    .i_mid_mvm_prg_tok_prod_vld(i_mid_mvm_prg_tok_prod_vld),
    .i_mid_mvm_prg_tok_cons_rdy(i_mid_mvm_prg_tok_cons_rdy),
    .i_mid_mvm_prg_tok_prod_rdy(i_mid_mvm_prg_tok_prod_rdy),
    .i_mid_mvm_prg_tok_cons_vld(i_mid_mvm_prg_tok_cons_vld),
    .i_mid_iau_tok_prod_vld(i_mid_iau_tok_prod_vld),
    .i_mid_iau_tok_cons_rdy(i_mid_iau_tok_cons_rdy),
    .i_mid_iau_tok_prod_rdy(i_mid_iau_tok_prod_rdy),
    .i_mid_iau_tok_cons_vld(i_mid_iau_tok_cons_vld),
    .i_mid_dpu_tok_prod_vld(i_mid_dpu_tok_prod_vld),
    .i_mid_dpu_tok_cons_rdy(i_mid_dpu_tok_cons_rdy),
    .i_mid_dpu_tok_prod_rdy(i_mid_dpu_tok_prod_rdy),
    .i_mid_dpu_tok_cons_vld(i_mid_dpu_tok_cons_vld),
    .i_mid_irq(i_mid_irq),
    .i_mid_ts_start(i_mid_ts_start),
    .i_mid_ts_end(i_mid_ts_end),
    .i_mid_acd_sync(i_mid_acd_sync),
    .i_did_dwpu_tok_prod_vld(i_did_dwpu_tok_prod_vld),
    .i_did_dwpu_tok_cons_rdy(i_did_dwpu_tok_cons_rdy),
    .i_did_dwpu_tok_prod_rdy(i_did_dwpu_tok_prod_rdy),
    .i_did_dwpu_tok_cons_vld(i_did_dwpu_tok_cons_vld),
    .i_did_iau_tok_prod_vld(i_did_iau_tok_prod_vld),
    .i_did_iau_tok_cons_rdy(i_did_iau_tok_cons_rdy),
    .i_did_iau_tok_prod_rdy(i_did_iau_tok_prod_rdy),
    .i_did_iau_tok_cons_vld(i_did_iau_tok_cons_vld),
    .i_did_dpu_tok_prod_vld(i_did_dpu_tok_prod_vld),
    .i_did_dpu_tok_cons_rdy(i_did_dpu_tok_cons_rdy),
    .i_did_dpu_tok_prod_rdy(i_did_dpu_tok_prod_rdy),
    .i_did_dpu_tok_cons_vld(i_did_dpu_tok_cons_vld),
    .i_did_irq(i_did_irq),
    .i_did_dwpu_obs(i_did_dwpu_obs),
    .i_did_iau_obs(i_did_iau_obs),
    .i_did_dpu_obs(i_did_dpu_obs),
    .i_mid_cfg_axi_m_awready(i_mid_cfg_axi_m_awready),
    .i_mid_cfg_axi_m_wready(i_mid_cfg_axi_m_wready),
    .i_mid_cfg_axi_m_bvalid(i_mid_cfg_axi_m_bvalid),
    .i_mid_cfg_axi_m_bid(i_mid_cfg_axi_m_bid),
    .i_mid_cfg_axi_m_bresp(i_mid_cfg_axi_m_bresp),
    .i_mid_cfg_axi_m_arready(i_mid_cfg_axi_m_arready),
    .i_mid_cfg_axi_m_rvalid(i_mid_cfg_axi_m_rvalid),
    .i_mid_cfg_axi_m_rlast(i_mid_cfg_axi_m_rlast),
    .i_mid_cfg_axi_m_rid(i_mid_cfg_axi_m_rid),
    .i_mid_cfg_axi_m_rdata(i_mid_cfg_axi_m_rdata),
    .i_mid_cfg_axi_m_rresp(i_mid_cfg_axi_m_rresp),
    .i_did_cfg_axi_m_awready(i_did_cfg_axi_m_awready),
    .i_did_cfg_axi_m_wready(i_did_cfg_axi_m_wready),
    .i_did_cfg_axi_m_bvalid(i_did_cfg_axi_m_bvalid),
    .i_did_cfg_axi_m_bid(i_did_cfg_axi_m_bid),
    .i_did_cfg_axi_m_bresp(i_did_cfg_axi_m_bresp),
    .i_did_cfg_axi_m_arready(i_did_cfg_axi_m_arready),
    .i_did_cfg_axi_m_rvalid(i_did_cfg_axi_m_rvalid),
    .i_did_cfg_axi_m_rlast(i_did_cfg_axi_m_rlast),
    .i_did_cfg_axi_m_rid(i_did_cfg_axi_m_rid),
    .i_did_cfg_axi_m_rdata(i_did_cfg_axi_m_rdata),
    .i_did_cfg_axi_m_rresp(i_did_cfg_axi_m_rresp),
    .i_sram_mcs(i_sram_mcs),
    .i_sram_mcsw(i_sram_mcsw),
    .i_sram_ret(i_sram_ret),
    .i_sram_pde(i_sram_pde),
    .i_sram_adme(i_sram_adme),
    .i_rf_mcs(i_rf_mcs),
    .i_rf_mcsw(i_rf_mcsw),
    .i_rf_ret(i_rf_ret),
    .i_rf_pde(i_rf_pde),
    .i_rf_adme(i_rf_adme),
    .ijtag_tck(ijtag_tck),
    .ijtag_reset(ijtag_reset),
    .ijtag_sel(ijtag_sel),
    .ijtag_ue(ijtag_ue),
    .ijtag_se(ijtag_se),
    .ijtag_ce(ijtag_ce),
    .ijtag_si(ijtag_si),
    .test_clk(test_clk),
    .test_mode(test_mode),
    .edt_update(edt_update),
    .scan_en(scan_en),
    .scan_in(scan_in),
    .bisr_clk(bisr_clk),
    .bisr_reset(bisr_reset),
    .bisr_shift_en(bisr_shift_en),
    .bisr_si(bisr_si)
  );
`endif


  // TOKEN and MMIO connections
  `include "aic_ls_mmio_connections.svh"
  `include "aic_ls_rvv_connections.svh"
  `include "aic_ls_token_connections.svh"

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================

  axe_clk_generator u_aic_ls_clk_generator(.i_enable(clk_en), .o_clk(i_clk));

  // Generate the clock
  initial begin
    clk_en = 1'b1;
    u_aic_ls_clk_generator.set_clock(.freq_mhz(aic_ls_freq_mhz), .duty(50));
  end

  axe_clk_assert u_axe_clk_assert(.clk(i_clk),
				.rst_n(i_rst_n),
				.freq_mhz(aic_ls_freq_mhz),
				.tol_ps(clk_tol_ps)
				);

  // =============================================================================================================
  // Initialize all memories
  // =============================================================================================================
  initial begin
    // Input ports initializations
    $timeformat(-9, 3, " ns", 10);
    l1_inp_ports_init();
  end

  // =============================================================================================================
  // Configuration database settings
  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;
`ifdef AXI_VIP
    // Set the reset interface on the virtual sequencer
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(
        uvm_root::get(), "uvm_test_top.m_env.m_axi_virt_sqr", "reset_mp", axi_reset_if.axi_reset_modport);

    // =============================================================================================================
    // Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI
    // System ENV and the DUT through the AXI interface.
    // =============================================================================================================
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.m_env.m_axi_system_env", "vif", axi_if);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_m_ifd0_agt", "vif", if_m_ifd0);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_m_ifd1_agt", "vif", if_m_ifd1);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_m_ifd2_agt", "vif", if_m_ifd2);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_m_ifdw_agt", "vif", if_m_ifdw);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_m_odr_agt", "vif", if_m_odr);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_d_ifd0_agt", "vif", if_d_ifd0);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_d_ifd1_agt", "vif", if_d_ifd1);
    uvm_config_db#(virtual dmc_addr_gen_if)::set(null, "uvm_test_top.m_env.m_d_odr_agt", "vif", if_d_odr);

    uvm_config_db#(virtual aic_ls_if)::set(null, "uvm_test_top.m_env.m_aic_ls_agt", "vif", if_aic_ls);

    //$assertoff (0, `LS_DUT_PATH.u_aic_ls.i_l1.i_l1_tc_fabric.i_l1_stream_xbar); // buggy assertion from design, Spyri to look at it
`endif
    run_test();
  end

  initial begin // assertoffs for i_sync_fifo.check_almost* assertions.

    $assertoff(0, `LS_DUT_PATH.u_bus.i_wr_path.g_req_sh.i_req_fifo.i_sync_fifo);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[0].u_ifd.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[1].u_ifd.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[2].u_ifd.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[3].u_ifd.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[4].u_ifd.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[5].u_ifd.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_odr[7].u_odr.u_cmd_block);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_odr[6].u_odr.u_cmd_block);

    // those are reminders of what exactly we're turning of above
    //`LS_DUT_PATH.u_dmc.g_ifd[0].u_ifd.u_cmd_block.i_cmd_fifo.i_cmd_fifo.i_sync_fifo
    //`LS_DUT_PATH.u_dmc.g_odr[7].u_odr.u_cmd_block.genblk3.i_tok_prod.genblk1[7].i_tok_fifo.i_sync_fifo.check_almost_full_clr
  end



  always begin
    @(posedge if_aic_ls.disable_decomp_assertion);  // in case we're trying to check decompression irq signals, disable the assertions that prevent us from that
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[3].u_ifd.g_decomp.i_decomp);
    @(negedge if_aic_ls.disable_decomp_assertion);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[3].u_ifd.g_decomp.i_decomp);
  end

  always begin
    @(posedge if_aic_ls.disable_rdataX_aserrtion);
    $assertoff(0, dut.AIC_LT_axi_cfg_protocol_checker.axi4_errs_rdata_x);
    $assertoff(0, dut.dmc_l1_ht_axi_protocol_checker.axi4_errs_rdata_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[0].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[1].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[2].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[3].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[4].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_ifd[5].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_odr[6].u_odr.u_defmem.chk_mem_rdata_not_all_x);
    $assertoff(0, `LS_DUT_PATH.u_dmc.g_odr[7].u_odr.u_defmem.chk_mem_rdata_not_all_x);
    @(negedge if_aic_ls.disable_rdataX_aserrtion);
    $asserton(0, dut.AIC_LT_axi_cfg_protocol_checker.axi4_errs_rdata_x);
    $asserton(0, dut.dmc_l1_ht_axi_protocol_checker.axi4_errs_rdata_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[0].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[1].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[2].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[3].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[4].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_ifd[5].u_ifd.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_odr[6].u_odr.u_defmem.chk_mem_rdata_not_all_x);
    $asserton(0, `LS_DUT_PATH.u_dmc.g_odr[7].u_odr.u_defmem.chk_mem_rdata_not_all_x);
  end

  // Initializing all input masters
  task l1_inp_ports_init;
    axi_if.slave_if[0].tready = 'd1;
    axi_if.slave_if[1].tready = 'd1;
    axi_if.slave_if[2].tready = 'd1;
    axi_if.slave_if[3].tready = 'd1;
    axi_if.slave_if[4].tready = 'd1;
    axi_if.slave_if[5].tready = 'd1;
  endtask:l1_inp_ports_init
endmodule : hdl_top
