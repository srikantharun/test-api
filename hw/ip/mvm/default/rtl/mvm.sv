// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: MVM block top level module. Connects MVM-DP with MVM-cmdGen, CSR and JTAG TDR
// Has interfaces towards IFD0, IFDW, IAU, LP AXI
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>


`ifndef MVM_SV
`define MVM_SV
// verilog_lint: waive-start line-length
module mvm
  import imc_bank_pkg::*;
  import aic_common_pkg::*;
  import mvm_pkg::*;
# (
  /// Start address
  /// default address regions for CSR, CMD, and PRG. First EXE, followed by PRG:
  parameter longint REGION_ST_ADDR[6] = {'h90000, 'h91000, 'h98000, 'hA0000, 'hA1000, 'hA8000},
  /// End address
  parameter longint REGION_END_ADDR[6] = {'h90fff, 'h91fff, 'h9ffff, 'hA0fff, 'hA1fff, 'hAffff},
  /// Defines the utilisation limit structure
  parameter type util_data_t = logic [7:0],
  /// Defines the nop injection rate structure
  parameter type nop_inj_rate_t = logic [5:0]
) (
  input wire  i_clk,
  input logic i_rst_n,
`ifdef TARGET_FPGA
  input logic i_hls_ap_clk,
  input logic i_hls_ap_i_rst_n,
`endif
  input logic i_jtag_tck,
  input logic jtag_i_rst_n,

  //--------------------------------------------------
  // AXI4 Config port
  //--------------------------------------------------
  // AXI write address channel
  input  logic                                   i_ai_core_mvm_axi_s_awvalid,
  input  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] i_ai_core_mvm_axi_s_awaddr,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_ai_core_mvm_axi_s_awid,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_ai_core_mvm_axi_s_awlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_ai_core_mvm_axi_s_awsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_ai_core_mvm_axi_s_awburst,
  output logic                                   o_ai_core_mvm_axi_s_awready,
  // AXI write data channel
  input  logic                                   i_ai_core_mvm_axi_s_wvalid,
  input  logic                                   i_ai_core_mvm_axi_s_wlast,
  input  logic [     AIC_LT_AXI_WSTRB_WIDTH-1:0] i_ai_core_mvm_axi_s_wstrb,
  input  logic [      AIC_LT_AXI_DATA_WIDTH-1:0] i_ai_core_mvm_axi_s_wdata,
  output logic                                   o_ai_core_mvm_axi_s_wready,
  // AXI write response channel
  output logic                                   o_ai_core_mvm_axi_s_bvalid,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_ai_core_mvm_axi_s_bid,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_ai_core_mvm_axi_s_bresp,
  input  logic                                   i_ai_core_mvm_axi_s_bready,
  // AXI read address channel
  input  logic                                   i_ai_core_mvm_axi_s_arvalid,
  input  logic [AIC_LT_AXI_LOCAL_ADDR_WIDTH-1:0] i_ai_core_mvm_axi_s_araddr,
  input  logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] i_ai_core_mvm_axi_s_arid,
  input  logic [       AIC_LT_AXI_LEN_WIDTH-1:0] i_ai_core_mvm_axi_s_arlen,
  input  logic [      AIC_LT_AXI_SIZE_WIDTH-1:0] i_ai_core_mvm_axi_s_arsize,
  input  logic [AIC_LT_AXI_BURST_TYPE_WIDTH-1:0] i_ai_core_mvm_axi_s_arburst,
  output logic                                   o_ai_core_mvm_axi_s_arready,
  // AXI read data/response channel
  output logic                                   o_ai_core_mvm_axi_s_rvalid,
  output logic                                   o_ai_core_mvm_axi_s_rlast,
  output logic [      AIC_LT_AXI_S_ID_WIDTH-1:0] o_ai_core_mvm_axi_s_rid,
  output logic [      AIC_LT_AXI_DATA_WIDTH-1:0] o_ai_core_mvm_axi_s_rdata,
  output logic [      AIC_LT_AXI_RESP_WIDTH-1:0] o_ai_core_mvm_axi_s_rresp,
  input  logic                                   i_ai_core_mvm_axi_s_rready,

  // Tokens
  output wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0] o_ai_core_mvm_exe_tok_prod_vld,
  input wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD-1:0]  i_ai_core_mvm_exe_tok_prod_rdy,
  input wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0]      i_ai_core_mvm_exe_tok_cons_vld,
  output wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0]     o_ai_core_mvm_exe_tok_cons_rdy,

  output wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0] o_ai_core_mvm_prg_tok_prod_vld,
  input wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD-1:0]  i_ai_core_mvm_prg_tok_prod_rdy,
  input wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0]      i_ai_core_mvm_prg_tok_cons_vld,
  output wire [token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0]     o_ai_core_mvm_prg_tok_cons_rdy,

  // IFD0 AXI stream
  input  logic                                     i_mvm_ifd0_axis_s_tvalid,
  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_mvm_ifd0_axis_s_tdata,
  input  logic                                     i_mvm_ifd0_axis_s_tlast,
  output logic                                     o_mvm_ifd0_axis_s_tready,

  // IFD2 AXI stream
  input  logic                                     i_mvm_ifd2_axis_s_tvalid,
  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_mvm_ifd2_axis_s_tdata,
  input  logic                                     i_mvm_ifd2_axis_s_tlast,
  output logic                                     o_mvm_ifd2_axis_s_tready,

  // IFDW AXI stream
  input  logic                                     i_mvm_ifdw_axis_s_tvalid,
  input  logic [AIC_PWORD_I8_AXIS_TDATA_WIDTH-1:0] i_mvm_ifdw_axis_s_tdata,
  input  logic                                     i_mvm_ifdw_axis_s_tlast,
  output logic                                     o_mvm_ifdw_axis_s_tready,

  // IAU AXI stream
  output logic                                      o_mvm_iau_axis_m_tvalid,
  output logic [AIC_PWORD_I26_AXIS_TDATA_WIDTH-1:0] o_mvm_iau_axis_m_tdata,
  output logic                                      o_mvm_iau_axis_m_tlast,
  input  logic                                      i_mvm_iau_axis_m_tready,

  // Utilisation limit
  input  util_data_t                               i_mvm_util_limit_value,
  input  logic                                     i_mvm_util_limit_enable,
  output util_data_t                               o_mvm_util_average,

  // NOP injection rate
  input  nop_inj_rate_t                            i_mvm_nop_inj_rate_value,
  input  logic                                     i_mvm_nop_inj_rate_enable,

  // IRQ
  output logic o_irq,

  // DFT signals
  input  logic i_test_mode,
  input  logic i_scan_en,
  output logic o_imc_bist_fast_clk_en,

  // Observation signals
  output logic [AIC_DEV_OBS_DW-1:0] o_ai_core_mvm_exe_obs,
  output logic [AIC_DEV_OBS_DW-1:0] o_ai_core_mvm_prg_obs,

  ///// Timestamp:
  output logic o_ts_start_mvm_exe,
  output logic o_ts_start_mvm_prg,
  output logic o_ts_end_mvm_exe,
  output logic o_ts_end_mvm_prg,
  ///// ACD sync:
  output logic o_acd_sync_mvm_exe,
  output logic o_acd_sync_mvm_prg,

  //// Block Identification
  input logic [AIC_CID_SUB_W-1:0] i_cid,
  input logic [AIC_BLOCK_ID_WIDTH-1:0] i_block_id,

  // JTAG
  input  logic i_jtag_sel,
  input  logic i_jtag_se,
  input  logic i_jtag_ce,
  input  logic i_jtag_ue,
  input  logic i_jtag_td,
  output logic o_jtag_td,

  // AIC CSR:
  input  imc_bist_pkg::aic_csr_reg2hw_t i_aic_bist_csr_reg2hw,
  output imc_bist_pkg::aic_csr_hw2reg_t o_aic_bist_csr_hw2reg,

  // IMC BIST
  output logic o_imc_bist_busy,
  output logic o_imc_bist_done,
  output logic o_imc_bist_pass,

  // UTIL limit
  input  logic [MVM_UTIL_EXP_AVG_DENOMINATOR_WIDTH-1:0] i_mvm_util_average_nominator,
  input  logic [2:0] i_mvm_util_col_upscaling_factor,
  input  logic [2:0] i_mvm_util_row_upscaling_factor,

  // CSR Control
  input mvm_ramp_up_ctrl_pkg::ramp_up_ctrl_t i_ramp_budget_ctrl
);

  // Set mvm AXI params
  localparam int unsigned IDW = AIC_LT_AXI_S_ID_WIDTH;
  localparam int unsigned AW = AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  localparam int unsigned AxiDw = AIC_LT_AXI_DATA_WIDTH;
  localparam int unsigned BW = AIC_LT_AXI_LEN_WIDTH;

  mvmexe_csr_reg_pkg::mvmexe_csr_reg2hw_t exe_csr_reg2hw;
  mvmexe_csr_reg_pkg::mvmexe_csr_hw2reg_t exe_csr_hw2reg;

  mvmprg_csr_reg_pkg::mvmprg_csr_reg2hw_t prg_csr_reg2hw;
  mvmprg_csr_reg_pkg::mvmprg_csr_hw2reg_t prg_csr_hw2reg;

  mvm_exe_dp_cmd_t ifd0_exe_dp_cmd_tdata;
  logic            ifd0_exe_dp_cmd_tvalid;
  logic            ifd0_exe_dp_cmd_tready;

  mvm_exe_dp_cmd_t ifd2_exe_dp_cmd_tdata;
  logic            ifd2_exe_dp_cmd_tvalid;
  logic            ifd2_exe_dp_cmd_tready;

  logic            exe_dp_done;

  // PRG DP CMD signals
  mvm_prg_dp_cmd_t prg_dp_cmd_tdata;
  logic prg_dp_cmd_tvalid;
  logic prg_dp_cmd_tready;
  logic prg_dp_cmd_tlast;
  logic prg_dp_cmd_done;

  // PRG CMDB bypass
  logic prg_dp_bypass_on, prg_cmdb_dp_bypass_on;

  // EXE CSR signals
  mvmexe_csr_reg_pkg::axi_a_ch_h2d_t exe_csr_axi_aw_i;
  logic                              exe_csr_axi_awready;
  mvmexe_csr_reg_pkg::axi_a_ch_h2d_t exe_csr_axi_ar_i;
  logic                              exe_csr_axi_arready;
  mvmexe_csr_reg_pkg::axi_w_ch_h2d_t exe_csr_axi_w_i;
  logic                              exe_csr_axi_wready;
  mvmexe_csr_reg_pkg::axi_b_ch_d2h_t exe_csr_axi_b_o;
  logic                              exe_csr_axi_bready;
  mvmexe_csr_reg_pkg::axi_r_ch_d2h_t exe_csr_axi_r_o;
  logic                              exe_csr_axi_rready;

  // IMC BIST CSR/TDR
  imc_bist_pkg::aic_csr_reg2hw_t imc_bist_csr2hw, imc_bist_tdr2hw;
  imc_bist_pkg::aic_csr_hw2reg_t imc_bist_hw2csr, imc_bist_hw2tdr;

  // PRG CSR signals
  mvmprg_csr_reg_pkg::axi_a_ch_h2d_t prg_csr_axi_aw_i;
  logic                              prg_csr_axi_awready;
  mvmprg_csr_reg_pkg::axi_a_ch_h2d_t prg_csr_axi_ar_i;
  logic                              prg_csr_axi_arready;
  mvmprg_csr_reg_pkg::axi_w_ch_h2d_t prg_csr_axi_w_i;
  logic                              prg_csr_axi_wready;
  mvmprg_csr_reg_pkg::axi_b_ch_d2h_t prg_csr_axi_b_o;
  logic                              prg_csr_axi_bready;
  mvmprg_csr_reg_pkg::axi_r_ch_d2h_t prg_csr_axi_r_o;
  logic                              prg_csr_axi_rready;
  // Error signals
  logic                              err_ifd0_dpcmd_unaligned_tlast;
  logic                              err_ifdw_dpcmd_unaligned_tlast;
  logic                              err_bypass_when_dp_not_idle;
  logic                              err_concurrent_exe_prg_on_ws;
  logic                              err_not_enough_budget;
  logic                              warning_util_limit_trigger_nop;

  logic                              dbg_sw_interrupt;
  logic                              exe_cmdblk_cmd_dropped;

  ///////////
  // MVM DP
  mvm_dp #(
    .aic_csr_hw2reg_t(imc_bist_pkg::aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(imc_bist_pkg::aic_csr_reg2hw_t),
    .aic_csr_reg2hw_imc_status_t(imc_bist_pkg::hw2reg_imc_bist_status_reg_t),
    .nop_inj_rate_t(nop_inj_rate_t)
  ) i_mvm_dp (
    .i_clk (i_clk),
    .i_rst_n(i_rst_n),
    .jtag_tcki(i_jtag_tck),
    .jtag_i_rst_n,

    // EXE Control inputs
    .i_ifd0_exe_cmd_tdata (ifd0_exe_dp_cmd_tdata),
    .i_ifd0_exe_cmd_tvalid(ifd0_exe_dp_cmd_tvalid),
    .o_ifd0_exe_cmd_tready(ifd0_exe_dp_cmd_tready),
    // EXE Control inputs
    .i_ifd2_exe_cmd_tdata (ifd2_exe_dp_cmd_tdata),
    .i_ifd2_exe_cmd_tvalid(ifd2_exe_dp_cmd_tvalid),
    .o_ifd2_exe_cmd_tready(ifd2_exe_dp_cmd_tready),

    .o_exe_dp_done        (exe_dp_done),
    // PRG control inputs
    .prg_cmd_tdata_i (prg_dp_cmd_tdata),
    .prg_cmd_tvalid_i(prg_dp_cmd_tvalid),
    .prg_cmd_tready_o(prg_dp_cmd_tready),
    .prg_cmd_tlast_i (prg_dp_cmd_tlast),
    .prg_done        (prg_dp_cmd_done),

    // IFD0 AXI stream
    .ifd0_tvalid_i(i_mvm_ifd0_axis_s_tvalid),
    .ifd0_tdata_i (i_mvm_ifd0_axis_s_tdata),
    //.ifd0_tstrb_i ('1),
    .ifd0_tlast_i (i_mvm_ifd0_axis_s_tlast),
    .ifd0_tready_o(o_mvm_ifd0_axis_s_tready),

    // IFD2 AXI stream
    .ifd2_tvalid_i(i_mvm_ifd2_axis_s_tvalid),
    .ifd2_tdata_i (i_mvm_ifd2_axis_s_tdata),
    //.ifd2_tstrb_i ('1),
    .ifd2_tlast_i (i_mvm_ifd2_axis_s_tlast),
    .ifd2_tready_o(o_mvm_ifd2_axis_s_tready),

    // IFDW AXI stream
    .ifdw_tvalid_i(i_mvm_ifdw_axis_s_tvalid),
    .ifdw_tdata_i (i_mvm_ifdw_axis_s_tdata),
    //.ifdw_tstrb_i ('1),
    .ifdw_tlast_i (i_mvm_ifdw_axis_s_tlast),
    .ifdw_tready_o(o_mvm_ifdw_axis_s_tready),

    // DPU AXI stream
    .dpu_tvalid_o(o_mvm_iau_axis_m_tvalid),
    .dpu_tdata_o (o_mvm_iau_axis_m_tdata),
    //.dpu_tstrb_o (),
    .dpu_tlast_o (o_mvm_iau_axis_m_tlast),
    .dpu_tready_i(i_mvm_iau_axis_m_tready),

    // Util limit
    .util_limit_value_i         (i_mvm_util_limit_value),
    .util_limit_enable_i        (i_mvm_util_limit_enable),
    .util_average_nominator_i   (i_mvm_util_average_nominator),
    .i_util_col_upscaling_factor(i_mvm_util_col_upscaling_factor),
    .i_util_row_upscaling_factor(i_mvm_util_row_upscaling_factor),

    .util_average_o          (o_mvm_util_average),

    // NOP Injection
    .i_mvm_nop_inj_rate_value  (i_mvm_nop_inj_rate_value),
    .i_mvm_nop_inj_rate_enable (i_mvm_nop_inj_rate_enable),

    // Ramp Up
    .i_ramp_budget_ctrl,

    // CSR signals
    .csr_power_smooth_dummy_ops_i      (exe_csr_reg2hw.dp_ctrl.power_smooth_dummy_ops.q),
    .csr_signed_weights_i              (prg_csr_reg2hw.dp_ctrl.q),
    .csr_signed_inputs_i               (exe_csr_reg2hw.dp_ctrl.signed_inputs.q),
    .csr_disable_imc_acc_clock_gating_i(exe_csr_reg2hw.dp_ctrl.disable_imc_acc_clock_gating.q),
    .csr_imc_tm_i                      (exe_csr_reg2hw.dp_ctrl.imc_test_mode.q),

    // Status signals
    .exe_dp_status_o(exe_csr_hw2reg.dp_status),
    .prg_dp_status_o(prg_csr_hw2reg.dp_status),

    // ERR/IRQ signals
    .err_ifd0_dpcmd_unaligned_tlast_o(err_ifd0_dpcmd_unaligned_tlast),
    .err_ifd2_dpcmd_unaligned_tlast_o(/*TODO: Coneect to the CPU */),
    .err_ifdw_dpcmd_unaligned_tlast_o(err_ifdw_dpcmd_unaligned_tlast),
    .err_bypass_when_dp_not_idle_o(err_bypass_when_dp_not_idle),
    .err_concurrent_exe_prg_on_ws_o(err_concurrent_exe_prg_on_ws),
    .o_err_not_enough_budget         (err_not_enough_budget),
    .o_warning_util_limit_trigger_nop(warning_util_limit_trigger_nop),
    // DFT signals
    .test_mode_i(i_test_mode),
    .scan_en(i_scan_en),
    // IMC BIST
    .imc_bist_tdr2hw_i(imc_bist_tdr2hw),
    .imc_bist_hw2tdr_o(imc_bist_hw2tdr),
    .imc_bist_csr2hw_i(imc_bist_csr2hw),
    .imc_bist_hw2csr_o(imc_bist_hw2csr)
  );

  ///--------------------------------------------------
  /// CMD block interface
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   exe_cmd_data_packed;
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   exe_cmd_data_unpacked;
  aic_dp_cmd_gen_pkg::cmd_format_t exe_cmd_format;
  aic_dp_cmd_gen_pkg::cmd_config_t exe_cmd_config;
  logic                            exe_cmd_rdy;
  logic                            exe_cmd_vld;
  logic                            exe_cmd_done;

  mvm_prg_cmd_t                   prg_cmd_data;
  logic prg_cmd_rdy, prg_cmd_vld, prg_cmd_done;

  ///--------------------------------------------------
  /// DPcmd Gen / Shim
  mvm_exe_qcmd_t                        dpcmd_shim_data;
  aic_dp_cmd_gen_pkg::metadata_t        dpcmd_shim_metadata;
  aic_dp_cmd_gen_pkg::loop_iterations_t dpcmd_shim_iterations;
  logic                                 dpcmd_shim_last;
  logic                                 dpcmd_shim_valid;
  logic                                 dpcmd_shim_ready;

  ///--------------------------------------------------
  /// Error
  logic err_exe_illegal_cmd_opcode;
  logic err_exe_illegal_loop_iter;
  logic err_exe_illegal_loop_len;
  logic err_exe_illegal_loop_start;
  logic err_exe_qcmd_mem_addr_overflow;
  logic err_exe_inp_offset_size_overflow;
  logic err_exe_oup_offset_size_overflow;

  logic err_prg_illegal_cmd_opcode;
  logic err_prg_illegal_weight_set;
  logic err_prg_row_offset_size_overflow;
  logic err_prg_col_offset_size_overflow;

  ///// AXI slaves:
  // Write Address Channel
  logic [MVM_AXI_NR_SLVS-1:0][IDW-1:0] awid_s;
  logic [MVM_AXI_NR_SLVS-1:0][AW-1:0]  awaddr_s;
  logic [MVM_AXI_NR_SLVS-1:0][AW-1:0]  awaddr_capped_s;  // remove MSB's as slave don't like these
  logic [MVM_AXI_NR_SLVS-1:0][BW-1:0]  awlen_s;
  logic [MVM_AXI_NR_SLVS-1:0][2:0]     awsize_s;
  logic [MVM_AXI_NR_SLVS-1:0][1:0]     awburst_s;
  logic [MVM_AXI_NR_SLVS-1:0]          awvalid_s;
  logic [MVM_AXI_NR_SLVS-1:0]          awready_s;
  // Read Address Channel
  logic [MVM_AXI_NR_SLVS-1:0][IDW-1:0] arid_s;
  logic [MVM_AXI_NR_SLVS-1:0][AW-1:0]  araddr_s;
  logic [MVM_AXI_NR_SLVS-1:0][BW-1:0]  arlen_s;
  logic [MVM_AXI_NR_SLVS-1:0][2:0]     arsize_s;
  logic [MVM_AXI_NR_SLVS-1:0][1:0]     arburst_s;
  logic [MVM_AXI_NR_SLVS-1:0]          arvalid_s;
  logic [MVM_AXI_NR_SLVS-1:0]          arready_s;
  // Write  Data Channel
  logic [MVM_AXI_NR_SLVS-1:0][AxiDw-1:0]   wdata_s;
  logic [MVM_AXI_NR_SLVS-1:0][AxiDw/8-1:0] wstrb_s;
  logic [MVM_AXI_NR_SLVS-1:0]              wlast_s;
  logic [MVM_AXI_NR_SLVS-1:0]              wvalid_s;
  logic [MVM_AXI_NR_SLVS-1:0]              wready_s;
  // Read Data Channel
  logic [MVM_AXI_NR_SLVS-1:0][IDW-1:0]   rid_s;
  logic [MVM_AXI_NR_SLVS-1:0][AxiDw-1:0] rdata_s;
  logic [MVM_AXI_NR_SLVS-1:0][1:0]       rresp_s;
  logic [MVM_AXI_NR_SLVS-1:0]            rlast_s;
  logic [MVM_AXI_NR_SLVS-1:0]            rvalid_s;
  logic [MVM_AXI_NR_SLVS-1:0]            rready_s;
  // Write Response Channel
  logic [MVM_AXI_NR_SLVS-1:0][IDW-1:0] bid_s;
  logic [MVM_AXI_NR_SLVS-1:0][1:0]     bresp_s;
  logic [MVM_AXI_NR_SLVS-1:0]          bvalid_s;
  logic [MVM_AXI_NR_SLVS-1:0]          bready_s;


  ///////////////////////////
  // MVM EXE CMD BLOCK
  localparam int unsigned MvmExeTotCmdFifoDw = MVM_EXE_CMDB_CMD_DW + token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD +
                                                                        token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS;
  localparam longint CommandEndpointSize = REGION_END_ADDR[mvm_pkg::MVM_EXE_CMDB_AXI_SLV]
                                         - REGION_ST_ADDR[mvm_pkg::MVM_EXE_CMDB_AXI_SLV] + 1;
  cmdblock #(
    .IDW(IDW),
    .AW (AW),
    .DW (AxiDw),
    .BW (BW),

    .DYNAMIC_CMD_SIZE(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .NR_TOK_PROD(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_PROD),
    .NR_TOK_CONS(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS),
    .MAX_OUTST_CMDS(MVM_EXE_CMDB_MAX_OUTST_CMDS),
    .CMD_CONFIG_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CONFIG_WIDTH),

    .CMD_FIFO_DEPTH(MVM_EXE_CMDB_FIFO_DEPTH),
    .CMD_FIFO_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CMD_FIFO_WIDTH),

    .DEV_ADDR_CAP  (CommandEndpointSize),

    .NR_FORMATS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .FORMAT_NR_BYTES(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_BYTES)
  ) i_mvm_exe_cmd_block (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    // Sideband:
    .exec       (exe_csr_reg2hw.cmdblk_ctrl.exec_en.q),
    .pointer_rst(exe_csr_reg2hw.cmdblk_ctrl.ptr_rst.q),
    .cmd_dropped(exe_cmdblk_cmd_dropped),

    // status:
    .stat_cur_pointer   (exe_csr_hw2reg.cmdblk_status.in_word_ptr.d),
    .stat_cur_fifo_count(exe_csr_hw2reg.cmdblk_status.fifo_cnt.d),
    .stat_nr_outst_cmds (exe_csr_hw2reg.cmdblk_status.outst_cmds.d),
    .stat_wait_token    (exe_csr_hw2reg.cmdblk_status.wait_token.d),
    .o_stat_state         (exe_csr_hw2reg.cmdblk_status.state.d),
    .o_stat_pending_tokens(exe_csr_hw2reg.cmdblk_status.pending_tokens.d[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS-1:0]),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid_s[MVM_EXE_CMDB_AXI_SLV]),
    .awaddr(awaddr_capped_s[MVM_EXE_CMDB_AXI_SLV]),
    .awlen(awlen_s[MVM_EXE_CMDB_AXI_SLV]),
    .awsize(awsize_s[MVM_EXE_CMDB_AXI_SLV]),
    .awburst(awburst_s[MVM_EXE_CMDB_AXI_SLV]),
    .awvalid(awvalid_s[MVM_EXE_CMDB_AXI_SLV]),
    .awready(awready_s[MVM_EXE_CMDB_AXI_SLV]),
    // Read Address Channel
    .arid(arid_s[MVM_EXE_CMDB_AXI_SLV]),
    .araddr(araddr_s[MVM_EXE_CMDB_AXI_SLV]),
    .arlen(arlen_s[MVM_EXE_CMDB_AXI_SLV]),
    .arsize(arsize_s[MVM_EXE_CMDB_AXI_SLV]),
    .arburst(arburst_s[MVM_EXE_CMDB_AXI_SLV]),
    .arvalid(arvalid_s[MVM_EXE_CMDB_AXI_SLV]),
    .arready(arready_s[MVM_EXE_CMDB_AXI_SLV]),
    // Write  Data Channel
    .wdata(wdata_s[MVM_EXE_CMDB_AXI_SLV]),
    .wstrb(wstrb_s[MVM_EXE_CMDB_AXI_SLV]),
    .wlast(wlast_s[MVM_EXE_CMDB_AXI_SLV]),
    .wvalid(wvalid_s[MVM_EXE_CMDB_AXI_SLV]),
    .wready(wready_s[MVM_EXE_CMDB_AXI_SLV]),
    // Read Data Channel
    .rid(rid_s[MVM_EXE_CMDB_AXI_SLV]),
    .rdata(rdata_s[MVM_EXE_CMDB_AXI_SLV]),
    .rresp(rresp_s[MVM_EXE_CMDB_AXI_SLV]),
    .rlast(rlast_s[MVM_EXE_CMDB_AXI_SLV]),
    .rvalid(rvalid_s[MVM_EXE_CMDB_AXI_SLV]),
    .rready(rready_s[MVM_EXE_CMDB_AXI_SLV]),
    // Write Response Channel
    .bid(bid_s[MVM_EXE_CMDB_AXI_SLV]),
    .bresp(bresp_s[MVM_EXE_CMDB_AXI_SLV]),
    .bvalid(bvalid_s[MVM_EXE_CMDB_AXI_SLV]),
    .bready(bready_s[MVM_EXE_CMDB_AXI_SLV]),

    ///// Tokens:
    .tok_prod_vld(o_ai_core_mvm_exe_tok_prod_vld),
    .tok_prod_rdy(i_ai_core_mvm_exe_tok_prod_rdy),
    .tok_cons_vld(i_ai_core_mvm_exe_tok_cons_vld),
    .tok_cons_rdy(o_ai_core_mvm_exe_tok_cons_rdy),
    ///// Timestamp:
    .o_ts_start  (o_ts_start_mvm_exe),
    .o_ts_end    (o_ts_end_mvm_exe),
    ///// ACD sync:
    .o_acd_sync  (o_acd_sync_mvm_exe),

    ///// Command:
    .cmd_done(exe_cmd_done),
    .cmd_data(exe_cmd_data_packed),
    .cmd_format(exe_cmd_format),
    .cmd_config(exe_cmd_config),
    .cmd_vld(exe_cmd_vld),
    .cmd_rdy(exe_cmd_rdy)
  );
  always_comb exe_csr_hw2reg.cmdblk_status.pending_tokens.d[$bits(exe_csr_hw2reg.cmdblk_status.pending_tokens.d)-1 :
                                                                     token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMEXE_NR_TOK_CONS] = 0;

  /////////////////////////////
  //// MVM EXE CMD UNPACK
  cmdblock_cmd_unpack #(
    .NR_FIELDS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FIELDS),
    .NR_FORMATS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .TOT_WIDTH(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .FIELD_SIZE(aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_SIZES),
    .FIELD_OUTP_IDX(aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_OUTP_IDX),
    .FIELD_DEFAULT_VAL(aic_dp_cmd_gen_pkg::CMD_BLOCK_DEFAULTS),
    .FORMAT_IDX(aic_dp_cmd_gen_pkg::CMD_BLOCK_FORMAT_IDX)
  ) u_cmd_unpack (
    .format(exe_cmd_format),
    .inp(exe_cmd_data_packed),
    .outp(exe_cmd_data_unpacked)
  );

  ///////////////////////////
  // MVM EXE DP CMD GEN
  localparam longint MemoryEndpointSize = REGION_END_ADDR[mvm_pkg::MVM_EXE_QCMD_AXI_SLV]
                                        - REGION_ST_ADDR[mvm_pkg::MVM_EXE_QCMD_AXI_SLV] + 1;
  aic_dp_cmd_gen #(
    .AxiIdWidth              (IDW),
    .AxiAddrWidth            (AW),
    .AxiDataWidth            (AxiDw),
    .AxiEndpointStart        (AW'(REGION_ST_ADDR[mvm_pkg::MVM_EXE_QCMD_AXI_SLV])),
    .AxiEndpointSize         (AW'(MemoryEndpointSize)),
    .dp_command_t            (mvm_pkg::mvm_exe_qcmd_t),
    .DpCommandMemoryDepth    (mvm_pkg::MVM_EXE_QCMD_MEM_DEPTH),
    .DpCommandMemoryDataAlign(mvm_pkg::MVM_EXE_QCMD_ALIGN),
    .UseMemoryMacro          (1'b0)
  ) u_mvm_exe_dpcmd_gen (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_test_mode(i_scan_en),

    .i_cmdb_command(exe_cmd_data_unpacked),
    .i_cmdb_format(aic_dp_cmd_gen_pkg::cmd_format_e'(exe_cmd_format)),
    .i_cmdb_config(exe_cmd_config),
    .i_cmdb_valid(exe_cmd_vld),
    .o_cmdb_ready(exe_cmd_rdy),
    .o_cmdb_done(exe_cmd_done),

    .i_axi_s_aw_id(awid_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_aw_addr(awaddr_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_aw_len(awlen_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_aw_size(awsize_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_aw_burst(awburst_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_aw_valid(awvalid_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_aw_ready(awready_s[MVM_EXE_QCMD_AXI_SLV]),

    .i_axi_s_w_data(wdata_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_w_strb(wstrb_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_w_last(wlast_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_w_valid(wvalid_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_w_ready(wready_s[MVM_EXE_QCMD_AXI_SLV]),

    .o_axi_s_b_id(bid_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_b_resp(bresp_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_b_valid(bvalid_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_b_ready(bready_s[MVM_EXE_QCMD_AXI_SLV]),

    .i_axi_s_ar_id(arid_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_ar_addr(araddr_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_ar_len(arlen_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_ar_size(arsize_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_ar_burst(arburst_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_ar_valid(arvalid_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_ar_ready(arready_s[MVM_EXE_QCMD_AXI_SLV]),

    .o_axi_s_r_id(rid_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_r_data(rdata_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_r_resp(rresp_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_r_last(rlast_s[MVM_EXE_QCMD_AXI_SLV]),
    .o_axi_s_r_valid(rvalid_s[MVM_EXE_QCMD_AXI_SLV]),
    .i_axi_s_r_ready(rready_s[MVM_EXE_QCMD_AXI_SLV]),

    .o_dp_command_data(dpcmd_shim_data),
    .o_dp_command_metadata(dpcmd_shim_metadata),
    .o_dp_command_iterations(dpcmd_shim_iterations),
    .o_dp_command_last(dpcmd_shim_last),
    .o_dp_command_valid(dpcmd_shim_valid),
    .i_dp_command_ready(dpcmd_shim_ready),

    .i_dp_done(dp_done),

    .o_errors(), // TODO(manuel.oliveira,europa,silver/gold) - connect IRQ

    .i_ram_impl('{default: 0}),
    .o_ram_impl() // ASO-UNUSED_OUTPUT: MVM does not have macros
  );

  mvm_exe_cmd_shim u_mvm_exe_cmd_shim (
    .i_clk                  (i_clk),
    .i_rst_n                (i_rst_n),
    // CMD stream from CMDBlock
    .i_dp_command_data      (dpcmd_shim_data),
    .i_dp_command_metadata  (dpcmd_shim_metadata),
    .i_dp_command_iterations(dpcmd_shim_iterations),
    .i_dp_command_last      (dpcmd_shim_last),
    .i_dp_command_valid     (dpcmd_shim_valid),
    .o_dp_command_ready     (dpcmd_shim_ready),
    .o_dp_done              (dp_done),
    // DP-EXE-CMD stream
    .o_ifd0_exe_dp_cmd_tdata (ifd0_exe_dp_cmd_tdata),
    .o_ifd0_exe_dp_cmd_tvalid(ifd0_exe_dp_cmd_tvalid),
    .i_ifd0_exe_dp_cmd_tready(ifd0_exe_dp_cmd_tready),
    .o_ifd2_exe_dp_cmd_tdata (ifd2_exe_dp_cmd_tdata),
    .o_ifd2_exe_dp_cmd_tvalid(ifd2_exe_dp_cmd_tvalid),
    .i_ifd2_exe_dp_cmd_tready(ifd2_exe_dp_cmd_tready),

    .i_exe_dp_done           (exe_dp_done),
    // ERR sig
    .err_exe_inp_offset_size_overflow(err_exe_inp_offset_size_overflow),
    .err_exe_oup_offset_size_overflow(err_exe_oup_offset_size_overflow),
    .err_exe_advance_mode_even_inst  () // TODO: @(manuel.oliveira,europa,silver/gold) Connect to the IRQ
  );

  /// TODO: (manuel.oliveira, europa, silver/gold) - Check if this can be connected to the cmd IRQ
  always_comb begin
    err_exe_qcmd_mem_addr_overflow = 1'b0;
    err_exe_illegal_cmd_opcode = 1'b0;
    err_exe_illegal_loop_iter = 1'b0;
    err_exe_illegal_loop_len = 1'b0;
    err_exe_illegal_loop_start = 1'b0;
    exe_csr_hw2reg.cmdgen_status = '{default: 0};
  end

  logic prg_cmdblk_cmd_dropped;
  ///////////////////////////
  // MVM PRG CMD BLOCK
  localparam int unsigned MvmPrgTotCmdFifoDw = MVM_PRG_CMDB_CMD_DW + token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD +
                                                                      token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS;
  cmdblock #(
    .IDW(IDW),
    .AW (AW),
    .DW (AxiDw),
    .BW (BW),

    .DYNAMIC_CMD_SIZE(MVM_PRG_CMDB_CMD_DW),
    .NR_TOK_PROD(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_PROD),
    .NR_TOK_CONS(token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS),
    .MAX_OUTST_CMDS(MVM_PRG_CMDB_MAX_OUTST_CMDS),

    .CMD_FIFO_DEPTH(MVM_PRG_CMDB_FIFO_DEPTH),
    .DEV_ADDR_CAP  (MVM_PRG_CMDB_AXI_CAP)
  ) i_mvm_prg_cmd_block (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    // Sideband:
    .exec       (prg_csr_reg2hw.cmdblk_ctrl.exec_en.q),
    .pointer_rst(prg_csr_reg2hw.cmdblk_ctrl.ptr_rst.q),
    .cmd_dropped(prg_cmdblk_cmd_dropped),

    // status:
    .stat_cur_pointer   (prg_csr_hw2reg.cmdblk_status.in_word_ptr.d),
    .stat_cur_fifo_count(prg_csr_hw2reg.cmdblk_status.fifo_cnt.d),
    .stat_nr_outst_cmds (prg_csr_hw2reg.cmdblk_status.outst_cmds.d),
    .stat_wait_token    (prg_csr_hw2reg.cmdblk_status.wait_token.d),
    .o_stat_state         (prg_csr_hw2reg.cmdblk_status.state.d),
    .o_stat_pending_tokens(prg_csr_hw2reg.cmdblk_status.pending_tokens.d[token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS-1:0]),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid_s[MVM_PRG_CMDB_AXI_SLV]),
    .awaddr(awaddr_capped_s[MVM_PRG_CMDB_AXI_SLV]),
    .awlen(awlen_s[MVM_PRG_CMDB_AXI_SLV]),
    .awsize(awsize_s[MVM_PRG_CMDB_AXI_SLV]),
    .awburst(awburst_s[MVM_PRG_CMDB_AXI_SLV]),
    .awvalid(awvalid_s[MVM_PRG_CMDB_AXI_SLV]),
    .awready(awready_s[MVM_PRG_CMDB_AXI_SLV]),
    // Read Address Channel
    .arid(arid_s[MVM_PRG_CMDB_AXI_SLV]),
    .araddr(araddr_s[MVM_PRG_CMDB_AXI_SLV]),
    .arlen(arlen_s[MVM_PRG_CMDB_AXI_SLV]),
    .arsize(arsize_s[MVM_PRG_CMDB_AXI_SLV]),
    .arburst(arburst_s[MVM_PRG_CMDB_AXI_SLV]),
    .arvalid(arvalid_s[MVM_PRG_CMDB_AXI_SLV]),
    .arready(arready_s[MVM_PRG_CMDB_AXI_SLV]),
    // Write  Data Channel
    .wdata(wdata_s[MVM_PRG_CMDB_AXI_SLV]),
    .wstrb(wstrb_s[MVM_PRG_CMDB_AXI_SLV]),
    .wlast(wlast_s[MVM_PRG_CMDB_AXI_SLV]),
    .wvalid(wvalid_s[MVM_PRG_CMDB_AXI_SLV]),
    .wready(wready_s[MVM_PRG_CMDB_AXI_SLV]),
    // Read Data Channel
    .rid(rid_s[MVM_PRG_CMDB_AXI_SLV]),
    .rdata(rdata_s[MVM_PRG_CMDB_AXI_SLV]),
    .rresp(rresp_s[MVM_PRG_CMDB_AXI_SLV]),
    .rlast(rlast_s[MVM_PRG_CMDB_AXI_SLV]),
    .rvalid(rvalid_s[MVM_PRG_CMDB_AXI_SLV]),
    .rready(rready_s[MVM_PRG_CMDB_AXI_SLV]),
    // Write Response Channel
    .bid(bid_s[MVM_PRG_CMDB_AXI_SLV]),
    .bresp(bresp_s[MVM_PRG_CMDB_AXI_SLV]),
    .bvalid(bvalid_s[MVM_PRG_CMDB_AXI_SLV]),
    .bready(bready_s[MVM_PRG_CMDB_AXI_SLV]),

    ///// Tokens:
    .tok_prod_vld(o_ai_core_mvm_prg_tok_prod_vld),
    .tok_prod_rdy(i_ai_core_mvm_prg_tok_prod_rdy),
    .tok_cons_vld(i_ai_core_mvm_prg_tok_cons_vld),
    .tok_cons_rdy(o_ai_core_mvm_prg_tok_cons_rdy),
    ///// Timestamp:
    .o_ts_start  (o_ts_start_mvm_prg),
    .o_ts_end    (o_ts_end_mvm_prg),
    ///// ACD sync:
    .o_acd_sync  (o_acd_sync_mvm_prg),

    ///// Command:
    .cmd_done(prg_cmd_done),
    .cmd_data(prg_cmd_data),
    .cmd_format(),
    .cmd_config(),
    .cmd_vld(prg_cmd_vld),
    .cmd_rdy(prg_cmd_rdy)
  );
  always_comb prg_csr_hw2reg.cmdblk_status.pending_tokens.d[$bits(prg_csr_hw2reg.cmdblk_status.pending_tokens.d)-1 :
                                                                     token_mgr_mapping_aic_pkg::TOK_MGR_M_MVMPRG_NR_TOK_CONS] = 0;

  ///////////////////////////
  // MVM PRG DP CMD GEN
  mvm_prg_cmd_gen i_mvm_prg_cmd_gen (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    // Command from CMDBlock
    .cmd_done(prg_cmd_done),
    .cmd_data(prg_cmd_data),
    .cmd_vld (prg_cmd_vld),
    .cmd_rdy (prg_cmd_rdy),

    // DP-CMD stream
    .prg_dp_cmd_tdata(prg_dp_cmd_tdata),
    .prg_dp_cmd_tvalid(prg_dp_cmd_tvalid),
    .prg_dp_cmd_tready(prg_dp_cmd_tready),
    .prg_dp_cmd_tlast(prg_dp_cmd_tlast),
    .prg_dp_done(prg_dp_cmd_done),

    // Err sig
    .err_prg_illegal_cmd_opcode(err_prg_illegal_cmd_opcode),
    .err_prg_illegal_weight_set(err_prg_illegal_weight_set),
    .err_prg_row_offset_size_overflow(err_prg_row_offset_size_overflow),
    .err_prg_col_offset_size_overflow(err_prg_col_offset_size_overflow),

    // State observation
    .cmdgen_status(prg_csr_hw2reg.cmdgen_status)
  );

  ///////////
  // JTAG TDR
  // Currently for imc bist only
  mvm_jtag_tdr #(
    .aic_csr_hw2reg_t(imc_bist_pkg::aic_csr_hw2reg_t),
    .aic_csr_reg2hw_t(imc_bist_pkg::aic_csr_reg2hw_t)
  ) i_mvm_jtag_tdr (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .tcki(i_jtag_tck),
    .trsti(jtag_i_rst_n),
    .seli(i_jtag_sel),
    .sei(i_jtag_se),
    .cei(i_jtag_ce),
    .uei(i_jtag_ue),
    .tdi(i_jtag_td),
    .tdo(o_jtag_td),
    .imc_bist_fast_clk_en_o(o_imc_bist_fast_clk_en),
    .imc_bist_tdr2hw_o(imc_bist_tdr2hw),
    .imc_bist_hw2tdr_i(imc_bist_hw2tdr)
  );

  ///////////
  // MVM EXE CSR
  mvmexe_csr_reg_top i_mvm_exe_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    // APB interface
    .axi_aw_i   (exe_csr_axi_aw_i),
    .axi_awready(exe_csr_axi_awready),
    .axi_ar_i   (exe_csr_axi_ar_i),
    .axi_arready(exe_csr_axi_arready),
    .axi_w_i    (exe_csr_axi_w_i),
    .axi_wready (exe_csr_axi_wready),
    .axi_b_o    (exe_csr_axi_b_o),
    .axi_bready (exe_csr_axi_bready),
    .axi_r_o    (exe_csr_axi_r_o),
    .axi_rready (exe_csr_axi_rready),
    // REG2HW bundle
    .reg2hw     (exe_csr_reg2hw),
    .hw2reg     (exe_csr_hw2reg),
    // Config
    .devmode_i  (1'b1)
  );
  assign exe_csr_axi_aw_i.addr = awaddr_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_aw_i.id = awid_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_aw_i.len = awlen_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_aw_i.size = awsize_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_aw_i.burst = awburst_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_aw_i.valid = awvalid_s[MVM_EXE_CSR_AXI_SLV];
  assign awready_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_awready;

  assign exe_csr_axi_ar_i.addr = araddr_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_ar_i.id = arid_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_ar_i.len = arlen_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_ar_i.size = arsize_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_ar_i.burst = arburst_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_ar_i.valid = arvalid_s[MVM_EXE_CSR_AXI_SLV];
  assign arready_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_arready;

  assign exe_csr_axi_w_i.data = wdata_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_w_i.strb = wstrb_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_w_i.last = wlast_s[MVM_EXE_CSR_AXI_SLV];
  assign exe_csr_axi_w_i.valid = wvalid_s[MVM_EXE_CSR_AXI_SLV];
  assign wready_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_wready;

  assign bvalid_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_b_o.valid;
  assign bid_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_b_o.id;
  assign bresp_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_b_o.resp;
  assign exe_csr_axi_bready = bready_s[MVM_EXE_CSR_AXI_SLV];

  assign rvalid_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_r_o.valid;
  assign rid_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_r_o.id;
  assign rdata_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_r_o.data;
  assign rlast_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_r_o.last;
  assign rresp_s[MVM_EXE_CSR_AXI_SLV] = exe_csr_axi_r_o.resp;
  assign exe_csr_axi_rready = rready_s[MVM_EXE_CSR_AXI_SLV];

  assign imc_bist_csr2hw.imc_bist_cmd = i_aic_bist_csr_reg2hw.imc_bist_cmd;
  assign imc_bist_csr2hw.imc_bist_cfg = i_aic_bist_csr_reg2hw.imc_bist_cfg;
  assign imc_bist_csr2hw.imc_bist_status = i_aic_bist_csr_reg2hw.imc_bist_status;
  always_comb begin
    o_aic_bist_csr_hw2reg = '0; // default all zero, to allow or on mid level
    o_aic_bist_csr_hw2reg.imc_bist_cmd = imc_bist_hw2csr.imc_bist_cmd;
    o_aic_bist_csr_hw2reg.imc_bist_status = imc_bist_hw2csr.imc_bist_status;
  end

  assign o_imc_bist_done = imc_bist_csr2hw.imc_bist_cfg.csr_sel.q ? imc_bist_csr2hw.imc_bist_status.done.q : imc_bist_tdr2hw.imc_bist_status.done.q;
  assign o_imc_bist_pass = imc_bist_csr2hw.imc_bist_cfg.csr_sel.q ? imc_bist_csr2hw.imc_bist_status.pass.q : imc_bist_tdr2hw.imc_bist_status.pass.q;
  assign o_imc_bist_busy = imc_bist_csr2hw.imc_bist_cfg.csr_sel.q ? imc_bist_csr2hw.imc_bist_status.busy.q : imc_bist_tdr2hw.imc_bist_status.busy.q;

  ///////////
  // MVM PRG CSR
  mvmprg_csr_reg_top i_mvm_prg_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    // APB interface
    .axi_aw_i   (prg_csr_axi_aw_i),
    .axi_awready(prg_csr_axi_awready),
    .axi_ar_i   (prg_csr_axi_ar_i),
    .axi_arready(prg_csr_axi_arready),
    .axi_w_i    (prg_csr_axi_w_i),
    .axi_wready (prg_csr_axi_wready),
    .axi_b_o    (prg_csr_axi_b_o),
    .axi_bready (prg_csr_axi_bready),
    .axi_r_o    (prg_csr_axi_r_o),
    .axi_rready (prg_csr_axi_rready),
    // REG2HW bundle
    .reg2hw     (prg_csr_reg2hw),
    .hw2reg     (prg_csr_hw2reg),
    // Config
    .devmode_i  (1'b1)
  );
  assign prg_csr_axi_aw_i.addr = awaddr_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_aw_i.id = awid_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_aw_i.len = awlen_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_aw_i.size = awsize_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_aw_i.burst = awburst_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_aw_i.valid = awvalid_s[MVM_PRG_CSR_AXI_SLV];
  assign awready_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_awready;

  assign prg_csr_axi_ar_i.addr = araddr_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_ar_i.id = arid_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_ar_i.len = arlen_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_ar_i.size = arsize_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_ar_i.burst = arburst_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_ar_i.valid = arvalid_s[MVM_PRG_CSR_AXI_SLV];
  assign arready_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_arready;

  assign prg_csr_axi_w_i.data = wdata_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_w_i.strb = wstrb_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_w_i.last = wlast_s[MVM_PRG_CSR_AXI_SLV];
  assign prg_csr_axi_w_i.valid = wvalid_s[MVM_PRG_CSR_AXI_SLV];
  assign wready_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_wready;

  assign bvalid_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_b_o.valid;
  assign bid_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_b_o.id;
  assign bresp_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_b_o.resp;
  assign prg_csr_axi_bready = bready_s[MVM_PRG_CSR_AXI_SLV];

  assign rvalid_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_r_o.valid;
  assign rid_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_r_o.id;
  assign rdata_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_r_o.data;
  assign rlast_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_r_o.last;
  assign rresp_s[MVM_PRG_CSR_AXI_SLV] = prg_csr_axi_r_o.resp;
  assign prg_csr_axi_rready = rready_s[MVM_PRG_CSR_AXI_SLV];

  /////////////
  // IRQs

  // HW can only set the status to high
  assign exe_csr_hw2reg.irq_status.err_ifd0_dpcmd_unaligned_tlast.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_ifdw_dpcmd_unaligned_tlast.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_bypass_when_dp_not_idle.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_concurrent_exe_prg_on_ws.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_loop_iter.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_loop_len.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_qcmd_mem_addr_overflow.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_cmd_opcode.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_loop_start.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_inp_offset_size_overflow.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_exe_oup_offset_size_overflow.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_prg_illegal_cmd_opcode.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_prg_illegal_weight_set.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_prg_row_offset_size_overflow.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_prg_col_offset_size_overflow.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.dbg_sw_interrupt.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.exe_cmdblk_cmd_dropped.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.prg_cmdblk_cmd_dropped.d = 1'b1;
  assign exe_csr_hw2reg.irq_status.err_not_enough_budget.d = 1'd1;
  assign exe_csr_hw2reg.irq_status.warning_util_limit_trigger_nop.d = 1'd1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  assign exe_csr_hw2reg.irq_status.err_ifd0_dpcmd_unaligned_tlast.de = err_ifd0_dpcmd_unaligned_tlast;
  assign exe_csr_hw2reg.irq_status.err_ifdw_dpcmd_unaligned_tlast.de = err_ifdw_dpcmd_unaligned_tlast;
  assign exe_csr_hw2reg.irq_status.err_bypass_when_dp_not_idle.de = err_bypass_when_dp_not_idle;
  assign exe_csr_hw2reg.irq_status.err_concurrent_exe_prg_on_ws.de = err_concurrent_exe_prg_on_ws;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_loop_iter.de = err_exe_illegal_loop_iter;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_loop_len.de = err_exe_illegal_loop_len;
  assign exe_csr_hw2reg.irq_status.err_exe_qcmd_mem_addr_overflow.de = err_exe_qcmd_mem_addr_overflow;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_cmd_opcode.de = err_exe_illegal_cmd_opcode;
  assign exe_csr_hw2reg.irq_status.err_exe_illegal_loop_start.de = err_exe_illegal_loop_start;
  assign exe_csr_hw2reg.irq_status.err_exe_inp_offset_size_overflow.de = err_exe_inp_offset_size_overflow;
  assign exe_csr_hw2reg.irq_status.err_exe_oup_offset_size_overflow.de = err_exe_oup_offset_size_overflow;
  assign exe_csr_hw2reg.irq_status.err_prg_illegal_cmd_opcode.de = err_prg_illegal_cmd_opcode;
  assign exe_csr_hw2reg.irq_status.err_prg_illegal_weight_set.de = err_prg_illegal_weight_set;
  assign exe_csr_hw2reg.irq_status.err_prg_row_offset_size_overflow.de = err_prg_row_offset_size_overflow;
  assign exe_csr_hw2reg.irq_status.err_prg_col_offset_size_overflow.de = err_prg_col_offset_size_overflow;
  assign exe_csr_hw2reg.irq_status.dbg_sw_interrupt.de = dbg_sw_interrupt;
  assign exe_csr_hw2reg.irq_status.exe_cmdblk_cmd_dropped.de = exe_cmdblk_cmd_dropped;
  assign exe_csr_hw2reg.irq_status.prg_cmdblk_cmd_dropped.de = prg_cmdblk_cmd_dropped;
  assign exe_csr_hw2reg.irq_status.err_not_enough_budget.de = err_not_enough_budget;
  assign exe_csr_hw2reg.irq_status.warning_util_limit_trigger_nop.de = warning_util_limit_trigger_nop;

  // Combine all IRQs to a single IRQ
  assign o_irq = |(exe_csr_reg2hw.irq_status & exe_csr_reg2hw.irq_en);

  // Connect the DBG_SW_IRQ to the error signal
  assign dbg_sw_interrupt = exe_csr_reg2hw.dp_ctrl.dbg_sw_irq.q;

  /////////////
  // Hardware Capability
  assign exe_csr_hw2reg.hw_capability.cmd_fifo_depth.d  = MVM_EXE_CMDB_FIFO_DEPTH;
  assign exe_csr_hw2reg.hw_capability.instr_mem_depth.d = MVM_EXE_QCMD_MEM_DEPTH;
  // CSR has only one field so it is directly named `hw_capability.d ... should be `hw_capability.cmd_fifo_depth.d`
  assign prg_csr_hw2reg.hw_capability.d                 = MVM_PRG_CMDB_FIFO_DEPTH;

  /////////////
  // Observation signals
  aic_dev_obs_t mvm_exe_obs;
  always_comb mvm_exe_obs.state          = exe_csr_hw2reg.cmdblk_status.state.d;
  always_comb mvm_exe_obs.token_stall    = exe_csr_hw2reg.cmdblk_status.wait_token.d;
  always_comb mvm_exe_obs.dp_instr_stall = exe_cmd_vld & ~exe_cmd_rdy;
  always_comb mvm_exe_obs.dp_cmd_stall   = dpcmd_shim_valid & ~dpcmd_shim_ready;
  always_comb mvm_exe_obs.dp_in0_stall   = i_mvm_ifd0_axis_s_tvalid & ~o_mvm_ifd0_axis_s_tready;
  always_comb mvm_exe_obs.dp_in1_stall   = i_mvm_ifd2_axis_s_tvalid & ~o_mvm_ifd2_axis_s_tready;
  always_comb mvm_exe_obs.dp_out_stall   = o_mvm_iau_axis_m_tvalid & ~i_mvm_iau_axis_m_tready;

  aic_dev_obs_t mvm_prg_obs;
  always_comb mvm_prg_obs.state          = prg_csr_hw2reg.cmdblk_status.state.d;
  always_comb mvm_prg_obs.token_stall    = prg_csr_hw2reg.cmdblk_status.wait_token.d;
  always_comb mvm_prg_obs.dp_instr_stall = prg_cmd_vld & ~prg_cmd_rdy;
  always_comb mvm_prg_obs.dp_cmd_stall   = prg_dp_cmd_tvalid & ~prg_dp_cmd_tready;
  always_comb mvm_prg_obs.dp_in0_stall   = i_mvm_ifdw_axis_s_tvalid & ~o_mvm_ifdw_axis_s_tready;
  always_comb mvm_prg_obs.dp_in1_stall   = '0; // mvm prg only has a single stream input
  always_comb mvm_prg_obs.dp_out_stall   = '0; // mvm prg doesn't have a stream output

  assign o_ai_core_mvm_exe_obs = mvm_exe_obs;
  assign o_ai_core_mvm_prg_obs = mvm_prg_obs;

  ///////////
  logic [$clog2(MVM_AXI_NR_SLVS+1)-1:0] bus_sel_rd;
  logic [$clog2(MVM_AXI_NR_SLVS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AW),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(MVM_AXI_NR_SLVS),
    .NR_REGIONS(6),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2, 32'd3, 32'd4, -32'd1})
  ) u_ext_decode_wr (
    .addr_in(i_ai_core_mvm_axi_s_awaddr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AW),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(MVM_AXI_NR_SLVS),
    .NR_REGIONS(6),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2, 32'd3, 32'd4, -32'd1})
  ) u_ext_decode_rd (
    .addr_in(i_ai_core_mvm_axi_s_araddr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI BUS
  simple_axi_demux #(
    .NR_MASTERS(MVM_AXI_NR_SLVS),
    .IDW(IDW),
    .AW(AW),
    .DW(AxiDw),
    .BW(BW),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(8),
    .EXT_SEL(1)
  ) i_mvm_exe_bus (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    // Master:
    // write address channel:
    .s_awvalid(i_ai_core_mvm_axi_s_awvalid),
    .s_awaddr(i_ai_core_mvm_axi_s_awaddr),
    .s_awid(i_ai_core_mvm_axi_s_awid),
    .s_awlen(i_ai_core_mvm_axi_s_awlen),
    .s_awsize(i_ai_core_mvm_axi_s_awsize),
    .s_awburst(i_ai_core_mvm_axi_s_awburst),
    .s_awlock('0),
    .s_awcache('0),
    .s_awprot('0),
    .s_awready(o_ai_core_mvm_axi_s_awready),

    // write data channel:
    .s_wvalid(i_ai_core_mvm_axi_s_wvalid),
    .s_wdata (i_ai_core_mvm_axi_s_wdata),
    .s_wstrb (i_ai_core_mvm_axi_s_wstrb),
    .s_wlast (i_ai_core_mvm_axi_s_wlast),
    .s_wready(o_ai_core_mvm_axi_s_wready),

    // write response channel:
    .s_bvalid(o_ai_core_mvm_axi_s_bvalid),
    .s_bid(o_ai_core_mvm_axi_s_bid),
    .s_bresp(o_ai_core_mvm_axi_s_bresp),
    .s_bready(i_ai_core_mvm_axi_s_bready),

    // read address channel:
    .s_arvalid(i_ai_core_mvm_axi_s_arvalid),
    .s_araddr(i_ai_core_mvm_axi_s_araddr),
    .s_arid(i_ai_core_mvm_axi_s_arid),
    .s_arlen(i_ai_core_mvm_axi_s_arlen),
    .s_arsize(i_ai_core_mvm_axi_s_arsize),
    .s_arburst(i_ai_core_mvm_axi_s_arburst),
    .s_arlock('0),
    .s_arcache('0),
    .s_arprot('0),
    .s_arready(o_ai_core_mvm_axi_s_arready),

    // read response channel:
    .s_rvalid(o_ai_core_mvm_axi_s_rvalid),
    .s_rid(o_ai_core_mvm_axi_s_rid),
    .s_rdata(o_ai_core_mvm_axi_s_rdata),
    .s_rresp(o_ai_core_mvm_axi_s_rresp),
    .s_rlast(o_ai_core_mvm_axi_s_rlast),
    .s_rready(i_ai_core_mvm_axi_s_rready),

    // Slaves:
    // write address channel:
    .m_awvalid(awvalid_s),
    .m_awaddr(awaddr_s),
    .m_awid(awid_s),
    .m_awlen(awlen_s),
    .m_awsize(awsize_s),
    .m_awburst(awburst_s),
    .m_awlock(),
    .m_awcache(),
    .m_awprot(),
    .m_awready(awready_s),

    // write data channel:
    .m_wvalid(wvalid_s),
    .m_wdata (wdata_s),
    .m_wstrb (wstrb_s),
    .m_wlast (wlast_s),
    .m_wready(wready_s),

    // write response channel:
    .m_bvalid(bvalid_s),
    .m_bid(bid_s),
    .m_bresp(bresp_s),
    .m_bready(bready_s),

    // read address channel:
    .m_arvalid(arvalid_s),
    .m_araddr(araddr_s),
    .m_arid(arid_s),
    .m_arlen(arlen_s),
    .m_arsize(arsize_s),
    .m_arburst(arburst_s),
    .m_arlock(),
    .m_arcache(),
    .m_arprot(),
    .m_arready(arready_s),

    // read response channel:
    .m_rvalid(rvalid_s),
    .m_rid(rid_s),
    .m_rdata(rdata_s),
    .m_rresp(rresp_s),
    .m_rlast(rlast_s),
    .m_rready(rready_s)
  );

  localparam int unsigned ExeQcmdMemAddrMsb = $clog2(MVM_EXE_QCMD_AXI_CAP);
  localparam int unsigned ExeCmdbAddrMsb = $clog2(MVM_EXE_CMDB_AXI_CAP);
  localparam int unsigned ExeCsrAddrMsb = $clog2(MVM_EXE_CSR_AXI_CAP);
  localparam int unsigned PrgCsrAddrMsb = $clog2(MVM_PRG_CSR_AXI_CAP);
  localparam int unsigned PrgCmdbAddrMsb = $clog2(MVM_PRG_CMDB_AXI_CAP);
  assign awaddr_capped_s[MVM_EXE_QCMD_AXI_SLV] = {
    '0, awaddr_s[MVM_EXE_QCMD_AXI_SLV][ExeQcmdMemAddrMsb-1:0]
  };
  assign awaddr_capped_s[MVM_EXE_CMDB_AXI_SLV] = {
    '0, awaddr_s[MVM_EXE_CMDB_AXI_SLV][ExeCmdbAddrMsb-1:0]
  };
  assign awaddr_capped_s[MVM_EXE_CSR_AXI_SLV] = {
    '0, awaddr_s[MVM_EXE_CSR_AXI_SLV][ExeCsrAddrMsb-1:0]
  };
  assign awaddr_capped_s[MVM_PRG_CSR_AXI_SLV] = {
    '0, awaddr_s[MVM_PRG_CSR_AXI_SLV][PrgCsrAddrMsb-1:0]
  };
  assign awaddr_capped_s[MVM_PRG_CMDB_AXI_SLV] = {
    '0, awaddr_s[MVM_PRG_CMDB_AXI_SLV][PrgCmdbAddrMsb-1:0]
  };

  /////////////
  // BLOCK OBSERVATION
  assign exe_csr_hw2reg.dbg_observe.in0_lst.d = i_mvm_ifd0_axis_s_tlast;
  assign exe_csr_hw2reg.dbg_observe.in0_rdy.d = o_mvm_ifd0_axis_s_tready;
  assign exe_csr_hw2reg.dbg_observe.in0_vld.d = i_mvm_ifd0_axis_s_tvalid;
  //assign exe_csr_hw2reg.dbg_observe.in2_lst.d = i_mvm_ifd2_axis_s_tlast;
  //assign exe_csr_hw2reg.dbg_observe.in2_rdy.d = o_mvm_ifd2_axis_s_tready;
  //assign exe_csr_hw2reg.dbg_observe.in2_vld.d = i_mvm_ifd2_axis_s_tvalid;
  assign exe_csr_hw2reg.dbg_observe.out_lst.d = o_mvm_iau_axis_m_tlast;
  assign exe_csr_hw2reg.dbg_observe.out_rdy.d = i_mvm_iau_axis_m_tready;
  assign exe_csr_hw2reg.dbg_observe.out_vld.d = o_mvm_iau_axis_m_tvalid;
  assign exe_csr_hw2reg.dbg_observe.dpcmd0_lst.d = ifd0_exe_dp_cmd_tdata.par2bser_dp_cmd_sig.tlast_predict;
  assign exe_csr_hw2reg.dbg_observe.dpcmd0_rdy.d = ifd0_exe_dp_cmd_tready;
  assign exe_csr_hw2reg.dbg_observe.dpcmd0_vld.d = ifd0_exe_dp_cmd_tvalid;
  assign prg_csr_hw2reg.dbg_observe.in1_lst.d = i_mvm_ifdw_axis_s_tlast;
  assign prg_csr_hw2reg.dbg_observe.in1_rdy.d = o_mvm_ifdw_axis_s_tready;
  assign prg_csr_hw2reg.dbg_observe.in1_vld.d = i_mvm_ifdw_axis_s_tvalid;
  assign prg_csr_hw2reg.dbg_observe.dpcmd1_lst.d = prg_dp_cmd_tlast;
  assign prg_csr_hw2reg.dbg_observe.dpcmd1_rdy.d = prg_dp_cmd_tready;
  assign prg_csr_hw2reg.dbg_observe.dpcmd1_vld.d = prg_dp_cmd_tvalid;

  /////////////
  // BLOCK IDENTIFICATION
  assign exe_csr_hw2reg.dbg_id.block_id.d = i_block_id;
  assign exe_csr_hw2reg.dbg_id.ai_core_id.d = {'0, i_cid};
  assign prg_csr_hw2reg.dbg_id.ai_core_id.d = {'0, i_cid};
  assign exe_csr_hw2reg.dbg_id.hw_revision.d = MVM_HW_REVISION;
  assign prg_csr_hw2reg.dbg_id.block_id.d = i_block_id;
  assign prg_csr_hw2reg.dbg_id.hw_revision.d = MVM_HW_REVISION;

endmodule
// verilog_lint: waive-stop line-length

`endif  // MVM_SV
