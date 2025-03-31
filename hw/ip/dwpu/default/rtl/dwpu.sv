// (C) Copyright 2022 Axelera AI B.V.
// All rights reserved.
// *** Axelera AI Confidential ***
//
// Author: Stefan Mach <stefan.mach@axelera.ai>
//         Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// The DWPU is a SIMD vector processing unit which is part of the DWPU partition within the Triton AI core.
///
module dwpu #(
  parameter int unsigned AxiIdWidth = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH,
  parameter int unsigned AxiAddrWidth = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH,
  parameter int unsigned AxiDataWidth = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH,
  parameter int unsigned AxiStrbWidth = aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH,
  parameter int unsigned NumTokenProd = token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_PROD,
  parameter int unsigned NumTokenCons = token_mgr_mapping_aic_pkg::TOK_MGR_D_DWPU_NR_TOK_CONS,
  parameter int unsigned InpAxisDataWidth = aic_common_pkg::AIC_PWORD_I8_AXIS_TDATA_WIDTH,
  parameter int unsigned OupAxisDataWidth = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH,
  parameter int unsigned ObserveWidth = aic_common_pkg::AIC_DEV_OBS_DW,
  parameter int unsigned CIdWidth = aic_common_pkg::AIC_CID_SUB_W,
  parameter int unsigned BlockIdWidth = aic_common_pkg::AIC_BLOCK_ID_WIDTH,

  // default address regions for CSR, CMD, and PRG:
  parameter longint REGION_ST_ADDR[3]  = {64'h0000_0000_0000_0000, 64'h0000_0000_0000_1000, 64'h0000_0000_0000_8000},
  parameter longint REGION_END_ADDR[3] = {64'h0000_0000_0000_0fff, 64'h0000_0000_0000_1fff, 64'h0000_0000_0000_Bfff},

  /// The amount of commands that can be saved in the datapath command memory
  parameter int unsigned DpCommandMemoryDepth = 1024,
  /// Use a technology specifc memory macro for the datapath command storage
  parameter bit  UseMemoryMacro = 1'b1,
  /// Memory Implementation Key (only used if `UseMemoryMacro == 1`)
  parameter      MemImplKey = "HS_RVT",
  /// Sideband input signal type to tc_sram
  parameter type sram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram
  parameter type sram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
)(
  /// Clock, positive edge triggered
  input wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input wire  i_rst_n,
  // doc sync i_clk

  /// Test mode enable, usually open clock gates and similar
  input logic i_test_mode,

  // AXI4 Config port
  //--------------------------------------------------

  /// AXI4 Config port: AW ID
  input  logic [  AxiIdWidth-1:0] i_axi_s_aw_id,
  /// AXI4 Config port: AW Addr
  input  logic [AxiAddrWidth-1:0] i_axi_s_aw_addr,
  /// AXI4 Config port: AW Len
  input  axi_pkg::axi_len_t       i_axi_s_aw_len,
  /// AXI4 Config port: AW Size
  input  axi_pkg::axi_size_t      i_axi_s_aw_size,
  /// AXI4 Config port: AW Burst
  input  axi_pkg::axi_burst_t     i_axi_s_aw_burst,
  /// AXI4 Config port: AW Valid
  input  logic                    i_axi_s_aw_valid,
  /// AXI4 Config port: AW Ready
  output logic                    o_axi_s_aw_ready,

  /// AXI4 Config port: W Data
  input  logic [AxiDataWidth-1:0] i_axi_s_w_data,
  /// AXI4 Config port: W Strb
  input  logic [AxiStrbWidth-1:0] i_axi_s_w_strb,
  /// AXI4 Config port: W Last
  input  logic                    i_axi_s_w_last,
  /// AXI4 Config port: W Valid
  input  logic                    i_axi_s_w_valid,
  /// AXI4 Config port: W Ready
  output logic                    o_axi_s_w_ready,

  /// AXI4 Config port: B ID
  output logic [  AxiIdWidth-1:0] o_axi_s_b_id,
  /// AXI4 Config port: B Resp
  output axi_pkg::axi_resp_t      o_axi_s_b_resp,
  /// AXI4 Config port: B Valid
  output logic                    o_axi_s_b_valid,
  /// AXI4 Config port: B Ready
  input  logic                    i_axi_s_b_ready,

  /// AXI4 Config port: AR ID
  input  logic [  AxiIdWidth-1:0] i_axi_s_ar_id,
  /// AXI4 Config port: AR Addr
  input  logic [AxiAddrWidth-1:0] i_axi_s_ar_addr,
  /// AXI4 Config port: AR Len
  input  axi_pkg::axi_len_t       i_axi_s_ar_len,
  /// AXI4 Config port: AR Size
  input  axi_pkg::axi_size_t      i_axi_s_ar_size,
  /// AXI4 Config port: AR Burst
  input  axi_pkg::axi_burst_t     i_axi_s_ar_burst,
  /// AXI4 Config port: AR Valid
  input  logic                    i_axi_s_ar_valid,
  /// AXI4 Config port: AR Ready
  output logic                    o_axi_s_ar_ready,

  /// AXI4 Config port: R ID
  output logic [  AxiIdWidth-1:0] o_axi_s_r_id,
  /// AXI4 Config port: R Data
  output logic [AxiDataWidth-1:0] o_axi_s_r_data,
  /// AXI4 Config port: R Resp
  output axi_pkg::axi_resp_t      o_axi_s_r_resp,
  /// AXI4 Config port: R Last
  output logic                    o_axi_s_r_last,
  /// AXI4 Config port: R Valid
  output logic                    o_axi_s_r_valid,
  /// AXI4 Config port: R Ready
  input  logic                    i_axi_s_r_ready,

  // Tokens
  //--------------------------------------------------
  /// Producer Token Valid
  output wire [NumTokenProd-1:0] o_tok_prod_valid,
  /// Producer Token Ready
  input  wire [NumTokenProd-1:0] i_tok_prod_ready,
  /// Consumer Token Valid
  input  wire [NumTokenCons-1:0] i_tok_cons_valid,
  /// Consumer Token Ready
  output wire [NumTokenCons-1:0] o_tok_cons_ready,

  // INP AXI stream
  //--------------------------------------------------
  /// INP AXI stream TData payload
  input  logic [InpAxisDataWidth-1:0] i_axis_s_tdata,
  /// INP AXI stream TLast flag
  input  logic                        i_axis_s_tlast,
  /// INP AXI stream TValid flag
  input  logic                        i_axis_s_tvalid,
  /// INP AXI stream TReady flag
  output logic                        o_axis_s_tready,

  // OUP AXI stream
  //--------------------------------------------------
  /// OUP AXI stream TData payload
  output logic [OupAxisDataWidth-1:0] o_axis_m_tdata,
  /// OUP AXI stream TLast flag
  output logic                         o_axis_m_tlast,
  /// OUP AXI stream TValid flag
  output logic                         o_axis_m_tvalid,
  /// OUP AXI stream TReady flag
  input  logic                         i_axis_m_tready,

  /// Interrupt
  //--------------------------------------------------
  output logic o_irq,

  /// Observation signals
  //--------------------------------------------------
  output logic [ObserveWidth-1:0] o_obs,

  ///// Timestamp:
  output logic o_ts_start,
  output logic o_ts_end,
  ///// ACD sync:
  output logic o_acd_sync,

  /// Block Identification CID
  //--------------------------------------------------
  input logic [     CIdWidth-1:0] i_cid,
  /// Block Identification Block ID
  input logic [BlockIdWidth-1:0] i_block_id,

  /// Instruction memory SRAM sideband signals
  //--------------------------------------------------
  input  sram_impl_inp_t i_dp_cmd_gen_sram_impl,
  /// Instruction memory SRAM sideband signal
  output sram_impl_oup_t o_dp_cmd_gen_sram_impl
);
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////

  typedef logic [AxiIdWidth  -1:0] dwpu_axi_id_t;
  typedef logic [AxiAddrWidth-1:0] dwpu_axi_addr_t;
  typedef logic [AxiDataWidth-1:0] dwpu_axi_data_t;
  typedef logic [AxiStrbWidth-1:0] dwpu_axi_strb_t;

  ///////////////
  // AXI Demux //
  ///////////////
  // Demuxed AXI ports for subordinates
  dwpu_axi_id_t        [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_id   ;
  dwpu_axi_addr_t      [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_addr ;
  axi_pkg::axi_len_t   [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_len  ;
  axi_pkg::axi_size_t  [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_size ;
  axi_pkg::axi_burst_t [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_burst;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_valid;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] aw_ready;

  dwpu_axi_data_t      [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] w_data  ;
  dwpu_axi_strb_t      [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] w_strb  ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] w_last  ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] w_valid ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] w_ready ;

  dwpu_axi_id_t        [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] b_id    ;
  axi_pkg::axi_resp_t  [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] b_resp  ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] b_valid ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] b_ready ;

  dwpu_axi_id_t        [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_id   ;
  dwpu_axi_addr_t      [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_addr ;
  axi_pkg::axi_len_t   [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_len  ;
  axi_pkg::axi_size_t  [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_size ;
  axi_pkg::axi_burst_t [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_burst;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_valid;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] ar_ready;

  dwpu_axi_id_t        [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] r_id    ;
  dwpu_axi_data_t      [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] r_data  ;
  axi_pkg::axi_resp_t  [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] r_resp  ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] r_last  ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] r_valid ;
  logic                [dwpu_pkg::NUM_AXI_ENDPOINTS-1:0] r_ready ;


  ///////////
  logic [$clog2(dwpu_pkg::NUM_AXI_ENDPOINTS+1)-1:0] bus_sel_rd;
  logic [$clog2(dwpu_pkg::NUM_AXI_ENDPOINTS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AxiAddrWidth),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(dwpu_pkg::NUM_AXI_ENDPOINTS),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_wr (
    .addr_in(i_axi_s_aw_addr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AxiAddrWidth),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(dwpu_pkg::NUM_AXI_ENDPOINTS),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_rd (
    .addr_in(i_axi_s_ar_addr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI BUS
  simple_axi_demux #(
    .NR_MASTERS     (dwpu_pkg::NUM_AXI_ENDPOINTS),
    .IDW            (AxiIdWidth),
    .AW             (AxiAddrWidth),
    .DW             (AxiDataWidth),
    .BW             (axi_pkg::AXI_LEN_WIDTH),
    .SL_WREQ_SHIELD (2),
    .SL_RREQ_SHIELD (2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR            (8),
    .EXT_SEL(1)
  ) u_axi_demux (
    .i_clk,
    .i_rst_n,
    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),
    .s_awid   (i_axi_s_aw_id),
    .s_awaddr (i_axi_s_aw_addr),
    .s_awlen  (i_axi_s_aw_len),
    .s_awsize (i_axi_s_aw_size),
    .s_awburst(i_axi_s_aw_burst),
    .s_awlock ('0),
    .s_awprot ('0),
    .s_awcache('0),
    .s_awvalid(i_axi_s_aw_valid),
    .s_awready(o_axi_s_aw_ready),
    .s_arid   (i_axi_s_ar_id),
    .s_araddr (i_axi_s_ar_addr),
    .s_arlen  (i_axi_s_ar_len),
    .s_arsize (i_axi_s_ar_size),
    .s_arburst(i_axi_s_ar_burst),
    .s_arlock ('0),
    .s_arprot ('0),
    .s_arcache('0),
    .s_arvalid(i_axi_s_ar_valid),
    .s_arready(o_axi_s_ar_ready),
    .s_wdata  (i_axi_s_w_data),
    .s_wstrb  (i_axi_s_w_strb),
    .s_wlast  (i_axi_s_w_last),
    .s_wvalid (i_axi_s_w_valid),
    .s_wready (o_axi_s_w_ready),
    .s_rid    (o_axi_s_r_id),
    .s_rdata  (o_axi_s_r_data),
    .s_rresp  (o_axi_s_r_resp),
    .s_rlast  (o_axi_s_r_last),
    .s_rvalid (o_axi_s_r_valid),
    .s_rready (i_axi_s_r_ready),
    .s_bid    (o_axi_s_b_id),
    .s_bresp  (o_axi_s_b_resp),
    .s_bvalid (o_axi_s_b_valid),
    .s_bready (i_axi_s_b_ready),
    .m_awid   (aw_id),
    .m_awlen  (aw_len),
    .m_awaddr (aw_addr),
    .m_awsize (aw_size),
    .m_awburst(aw_burst),
    .m_awlock (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awprot (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awcache(/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awvalid(aw_valid),
    .m_awready(aw_ready),
    .m_arid   (ar_id),
    .m_arlen  (ar_len),
    .m_araddr (ar_addr),
    .m_arsize (ar_size),
    .m_arburst(ar_burst),
    .m_arlock (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arprot (/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arcache(/*open*/), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arvalid(ar_valid),
    .m_arready(ar_ready),
    .m_wdata  (w_data),
    .m_wstrb  (w_strb),
    .m_wlast  (w_last),
    .m_wvalid (w_valid),
    .m_wready (w_ready),
    .m_rid    (r_id),
    .m_rdata  (r_data),
    .m_rresp  (r_resp),
    .m_rlast  (r_last),
    .m_rvalid (r_valid),
    .m_rready (r_ready),
    .m_bid    (b_id),
    .m_bresp  (b_resp),
    .m_bvalid (b_valid),
    .m_bready (b_ready)
  );


  //////////
  // CSRs //
  //////////
  // CSR structs
  dwpu_csr_reg_pkg::dwpu_csr_reg2hw_t csr_reg2hw;  // reading
  dwpu_csr_reg_pkg::dwpu_csr_hw2reg_t csr_hw2reg;  // writing

  dwpu_csr_reg_pkg::axi_a_ch_h2d_t csr_axi_aw;
  dwpu_csr_reg_pkg::axi_a_ch_h2d_t csr_axi_ar;
  dwpu_csr_reg_pkg::axi_w_ch_h2d_t csr_axi_w;
  dwpu_csr_reg_pkg::axi_r_ch_d2h_t csr_axi_r;
  dwpu_csr_reg_pkg::axi_b_ch_d2h_t csr_axi_b;

  assign csr_axi_aw.id    = aw_id[dwpu_pkg::CSR];
  assign csr_axi_aw.addr  = aw_addr[dwpu_pkg::CSR];
  assign csr_axi_aw.len   = aw_len[dwpu_pkg::CSR];
  assign csr_axi_aw.size  = aw_size[dwpu_pkg::CSR];
  assign csr_axi_aw.burst = aw_burst[dwpu_pkg::CSR];
  assign csr_axi_aw.valid = aw_valid[dwpu_pkg::CSR];

  assign csr_axi_w.data   = w_data[dwpu_pkg::CSR];
  assign csr_axi_w.strb   = w_strb[dwpu_pkg::CSR];
  assign csr_axi_w.last   = w_last[dwpu_pkg::CSR];
  assign csr_axi_w.valid  = w_valid[dwpu_pkg::CSR];

  assign b_id[dwpu_pkg::CSR]    = csr_axi_b.id;
  assign b_resp[dwpu_pkg::CSR]  = csr_axi_b.resp;
  assign b_valid[dwpu_pkg::CSR] = csr_axi_b.valid;

  assign csr_axi_ar.id    = ar_id[dwpu_pkg::CSR];
  assign csr_axi_ar.addr  = ar_addr[dwpu_pkg::CSR];
  assign csr_axi_ar.len   = ar_len[dwpu_pkg::CSR];
  assign csr_axi_ar.size  = ar_size[dwpu_pkg::CSR];
  assign csr_axi_ar.burst = ar_burst[dwpu_pkg::CSR];
  assign csr_axi_ar.valid = ar_valid[dwpu_pkg::CSR];

  assign r_id[dwpu_pkg::CSR]    = csr_axi_r.id;
  assign r_data[dwpu_pkg::CSR]  = csr_axi_r.data;
  assign r_resp[dwpu_pkg::CSR]  = csr_axi_r.resp;
  assign r_last[dwpu_pkg::CSR]  = csr_axi_r.last;
  assign r_valid[dwpu_pkg::CSR] = csr_axi_r.valid;

  dwpu_csr_reg_top u_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    .axi_aw_i   (csr_axi_aw),
    .axi_awready(aw_ready[dwpu_pkg::CSR]),
    .axi_ar_i   (csr_axi_ar),
    .axi_arready(ar_ready[dwpu_pkg::CSR]),
    .axi_w_i    (csr_axi_w),
    .axi_wready (w_ready[dwpu_pkg::CSR]),
    .axi_b_o    (csr_axi_b),
    .axi_bready (b_ready[dwpu_pkg::CSR]),
    .axi_r_o    (csr_axi_r),
    .axi_rready (r_ready[dwpu_pkg::CSR]),
    .reg2hw     (csr_reg2hw),
    .hw2reg     (csr_hw2reg),
    .devmode_i  (1'b1)
  );


  ///////////////////
  // Command Block //
  ///////////////////
  logic                            cmd_done;
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   cmdb_cmd_packed;
  aic_dp_cmd_gen_pkg::cmd_format_t cmdb_cmd_format;
  aic_dp_cmd_gen_pkg::cmd_config_t cmdb_config;
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   cmdb_cmd;
  logic cmdb_valid, cmdb_ready;
  logic cmdblk_cmd_dropped;

  localparam longint CommandEndpointSize = REGION_END_ADDR[dwpu_pkg::CMDB] - REGION_ST_ADDR[dwpu_pkg::CMDB] + 1;

  cmdblock #(
    .IDW(AxiIdWidth),
    .AW (AxiAddrWidth),
    .DW (AxiDataWidth),
    .BW (axi_pkg::AXI_LEN_WIDTH),

    .DYNAMIC_CMD_SIZE(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .NR_TOK_PROD     (NumTokenProd),
    .NR_TOK_CONS     (NumTokenCons),
    .MAX_OUTST_CMDS  (aic_common_pkg::AIC_GEN_CMDB_MAX_OUTST_CMDS),
    .CMD_CONFIG_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CONFIG_WIDTH),

    .CMD_FIFO_DEPTH(aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH),
    .CMD_FIFO_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CMD_FIFO_WIDTH),
    .USE_MACRO     (0),
    .DEV_ADDR_CAP  (CommandEndpointSize),

    .NR_FORMATS     (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .FORMAT_NR_BYTES(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_BYTES)
  ) u_cmd_block (
    .i_clk,
    .i_rst_n,
    // Sideband
    .exec               (csr_reg2hw.cmdblk_ctrl.exec_en.q),
    .pointer_rst        (csr_reg2hw.cmdblk_ctrl.ptr_rst.q),
    .cmd_dropped        (cmdblk_cmd_dropped),
    // Status
    .stat_cur_pointer   (csr_hw2reg.cmdblk_status.in_word_ptr.d),
    .stat_cur_fifo_count(csr_hw2reg.cmdblk_status.fifo_cnt.d),
    .stat_nr_outst_cmds (csr_hw2reg.cmdblk_status.outst_cmds.d),
    .stat_wait_token    (csr_hw2reg.cmdblk_status.wait_token.d),
    .o_stat_state         (csr_hw2reg.cmdblk_status.state.d),
    .o_stat_pending_tokens(csr_hw2reg.cmdblk_status.pending_tokens.d[NumTokenCons-1:0]),
    // Axi Consumer
    .awid               (aw_id[dwpu_pkg::CMDB]),
    .awaddr             (aw_addr[dwpu_pkg::CMDB]),
    .awlen              (aw_len[dwpu_pkg::CMDB]),
    .awsize             (aw_size[dwpu_pkg::CMDB]),
    .awburst            (aw_burst[dwpu_pkg::CMDB]),
    .awvalid            (aw_valid[dwpu_pkg::CMDB]),
    .awready            (aw_ready[dwpu_pkg::CMDB]),
    .arid               (ar_id[dwpu_pkg::CMDB]),
    .araddr             (ar_addr[dwpu_pkg::CMDB]),
    .arlen              (ar_len[dwpu_pkg::CMDB]),
    .arsize             (ar_size[dwpu_pkg::CMDB]),
    .arburst            (ar_burst[dwpu_pkg::CMDB]),
    .arvalid            (ar_valid[dwpu_pkg::CMDB]),
    .arready            (ar_ready[dwpu_pkg::CMDB]),
    .wdata              (w_data[dwpu_pkg::CMDB]),
    .wstrb              (w_strb[dwpu_pkg::CMDB]),
    .wlast              (w_last[dwpu_pkg::CMDB]),
    .wvalid             (w_valid[dwpu_pkg::CMDB]),
    .wready             (w_ready[dwpu_pkg::CMDB]),
    .rid                (r_id[dwpu_pkg::CMDB]),
    .rdata              (r_data[dwpu_pkg::CMDB]),
    .rresp              (r_resp[dwpu_pkg::CMDB]),
    .rlast              (r_last[dwpu_pkg::CMDB]),
    .rvalid             (r_valid[dwpu_pkg::CMDB]),
    .rready             (r_ready[dwpu_pkg::CMDB]),
    .bid                (b_id[dwpu_pkg::CMDB]),
    .bresp              (b_resp[dwpu_pkg::CMDB]),
    .bvalid             (b_valid[dwpu_pkg::CMDB]),
    .bready             (b_ready[dwpu_pkg::CMDB]),
    // Tokens
    .tok_prod_vld       (o_tok_prod_valid),
    .tok_prod_rdy       (i_tok_prod_ready),
    .tok_cons_vld       (i_tok_cons_valid),
    .tok_cons_rdy       (o_tok_cons_ready),
    ///// Timestamp:
    .o_ts_start         (o_ts_start),
    .o_ts_end           (o_ts_end),
    ///// ACD sync:
    .o_acd_sync         (o_acd_sync),
    // Command
    .cmd_done           (cmd_done),
    .cmd_data           (cmdb_cmd_packed.view_vector),
    .cmd_format         (cmdb_cmd_format),
    .cmd_config         (cmdb_config),
    .cmd_vld            (cmdb_valid),
    .cmd_rdy            (cmdb_ready)
  );
  always_comb csr_hw2reg.cmdblk_status.pending_tokens.d[$bits(csr_hw2reg.cmdblk_status.pending_tokens.d)-1:NumTokenCons] = 0;

  cmdblock_cmd_unpack #(
    .NR_FIELDS        (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FIELDS),
    .NR_FORMATS       (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .TOT_WIDTH        (aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .FIELD_SIZE       (aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_SIZES),
    .FIELD_OUTP_IDX   (aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_OUTP_IDX),
    .FIELD_DEFAULT_VAL(aic_dp_cmd_gen_pkg::CMD_BLOCK_DEFAULTS),
    .FORMAT_IDX       (aic_dp_cmd_gen_pkg::CMD_BLOCK_FORMAT_IDX)
  ) u_cmdblock_cmd_unpack (
    .format(cmdb_cmd_format),
    .inp   (cmdb_cmd_packed.view_vector),
    .outp  (cmdb_cmd.view_vector)
  );


  //////////////////////
  // DPcmd Generation //
  //////////////////////

  aic_dp_cmd_gen_pkg::cmd_format_e cmdb_format;
  assign cmdb_format = aic_dp_cmd_gen_pkg::cmd_format_e'(cmdb_cmd_format);

  localparam longint MemoryEndpointSize = REGION_END_ADDR[dwpu_pkg::IMEM] - REGION_ST_ADDR[dwpu_pkg::IMEM] + 1;

  if (MemoryEndpointSize * 8 < DpCommandMemoryDepth * $bits(dwpu_pkg::dwpu_dp_command_t))
    $fatal(1, "Parameter: 'REGION_*_ADDR[dwpu_pkg::IMEM]' is not large enough to access configured memory;");

  dwpu_pkg::dwpu_dp_command_t           dp_command_data;
  aic_dp_cmd_gen_pkg::metadata_t        dp_command_metadata;
  aic_dp_cmd_gen_pkg::loop_iterations_t dp_command_iterations;
  logic                                 dp_command_last;
  logic                                 dp_command_valid;
  logic                                 dp_command_ready;

  aic_dp_cmd_gen_pkg::loop_errors_t     dp_cmd_gen_errors;
  logic                                 dp_done;

  aic_dp_cmd_gen #(
    .AxiIdWidth           (AxiIdWidth),
    .AxiAddrWidth         (AxiAddrWidth),
    .AxiDataWidth         (AxiDataWidth),
    .AxiEndpointStart     (AxiAddrWidth'(REGION_ST_ADDR[dwpu_pkg::IMEM])),
    .AxiEndpointSize      (AxiAddrWidth'(MemoryEndpointSize)),
    .MaxOutstanding       (3),
    .dp_command_t         (dwpu_pkg::dwpu_dp_command_t),
    .DpCommandMemoryDepth (DpCommandMemoryDepth),
    .DpCommandMemoryShield(1'b0),
    .UseMemoryMacro       (UseMemoryMacro),
    .MemImplKey           (MemImplKey),
    .ram_impl_inp_t       (sram_impl_inp_t),
    .ram_impl_oup_t       (sram_impl_oup_t)
  ) u_aic_dp_cmd_gen (
    .i_clk,
    .i_rst_n,
    .i_flush                (1'b0),
    .i_test_mode,
    .i_cmdb_command         (cmdb_cmd),
    .i_cmdb_format          (cmdb_format),
    .i_cmdb_config          (cmdb_config),
    .i_cmdb_valid           (cmdb_valid),
    .o_cmdb_ready           (cmdb_ready),
    .o_cmdb_done            (cmd_done),
    .i_axi_s_aw_id          (aw_id[dwpu_pkg::IMEM]),
    .i_axi_s_aw_addr        (aw_addr[dwpu_pkg::IMEM]),
    .i_axi_s_aw_len         (aw_len[dwpu_pkg::IMEM]),
    .i_axi_s_aw_size        (aw_size[dwpu_pkg::IMEM]),
    .i_axi_s_aw_burst       (aw_burst[dwpu_pkg::IMEM]),
    .i_axi_s_aw_valid       (aw_valid[dwpu_pkg::IMEM]),
    .o_axi_s_aw_ready       (aw_ready[dwpu_pkg::IMEM]),
    .i_axi_s_w_data         (w_data[dwpu_pkg::IMEM]),
    .i_axi_s_w_strb         (w_strb[dwpu_pkg::IMEM]),
    .i_axi_s_w_last         (w_last[dwpu_pkg::IMEM]),
    .i_axi_s_w_valid        (w_valid[dwpu_pkg::IMEM]),
    .o_axi_s_w_ready        (w_ready[dwpu_pkg::IMEM]),
    .o_axi_s_b_id           (b_id[dwpu_pkg::IMEM]),
    .o_axi_s_b_resp         (b_resp[dwpu_pkg::IMEM]),
    .o_axi_s_b_valid        (b_valid[dwpu_pkg::IMEM]),
    .i_axi_s_b_ready        (b_ready[dwpu_pkg::IMEM]),
    .i_axi_s_ar_id          (ar_id[dwpu_pkg::IMEM]),
    .i_axi_s_ar_addr        (ar_addr[dwpu_pkg::IMEM]),
    .i_axi_s_ar_len         (ar_len[dwpu_pkg::IMEM]),
    .i_axi_s_ar_size        (ar_size[dwpu_pkg::IMEM]),
    .i_axi_s_ar_burst       (ar_burst[dwpu_pkg::IMEM]),
    .i_axi_s_ar_valid       (ar_valid[dwpu_pkg::IMEM]),
    .o_axi_s_ar_ready       (ar_ready[dwpu_pkg::IMEM]),
    .o_axi_s_r_id           (r_id[dwpu_pkg::IMEM]),
    .o_axi_s_r_data         (r_data[dwpu_pkg::IMEM]),
    .o_axi_s_r_resp         (r_resp[dwpu_pkg::IMEM]),
    .o_axi_s_r_last         (r_last[dwpu_pkg::IMEM]),
    .o_axi_s_r_valid        (r_valid[dwpu_pkg::IMEM]),
    .i_axi_s_r_ready        (r_ready[dwpu_pkg::IMEM]),
    .o_dp_command_data      (dp_command_data),
    .o_dp_command_metadata  (dp_command_metadata),
    .o_dp_command_iterations(dp_command_iterations),
    .o_dp_command_last      (dp_command_last),
    .o_dp_command_valid     (dp_command_valid),
    .i_dp_command_ready     (dp_command_ready),
    .i_dp_done              (dp_done),
    .o_errors               (dp_cmd_gen_errors),
    .i_ram_impl             (i_dp_cmd_gen_sram_impl),
    .o_ram_impl             (o_dp_cmd_gen_sram_impl)
  );

  // Observation
  assign csr_hw2reg.cmdgen_status.main_index.d   = dp_command_iterations.main_index;
  assign csr_hw2reg.cmdgen_status.overall_last.d = dp_command_iterations.overall_last;

  /////////////////////////////////
  // Command to Instruction Shim //
  /////////////////////////////////
  dwpu_pkg::dp_instruction_t dp_instruction_tdata;
  logic                      dp_instruction_tlast;
  logic                      dp_instruction_tvalid;
  logic                      dp_instruction_tready;

  dwpu_dp_instr_shim #(
    .NumOperands(dwpu_pkg::NUM_OPERANDS)
  ) u_dwpu_dp_instr_shim (
    .i_clk,
    .i_rst_n,
    .i_dp_command_data      (dp_command_data),
    .i_dp_command_metadata  (dp_command_metadata),
    .i_dp_command_iterations(dp_command_iterations),
    .i_dp_command_last      (dp_command_last),
    .i_dp_command_valid     (dp_command_valid),
    .o_dp_command_ready     (dp_command_ready),
    .o_dp_instruction_tdata (dp_instruction_tdata),
    .o_dp_instruction_tlast (dp_instruction_tlast),
    .o_dp_instruction_tvalid(dp_instruction_tvalid),
    .i_dp_instruction_tready(dp_instruction_tready)
  );

  ///////////////
  // Data Path //
  ///////////////

  dwpu_pkg::config_t dwpu_config;

  assign dwpu_config = '{
      signed_img: csr_reg2hw.dp_ctrl.image_sgn.q,
      signed_wgt: csr_reg2hw.dp_ctrl.weights_sgn.q
  };

  logic dp_error_act_stream_in, dp_error_act_stream_out;

  dwpu_dp u_dwpu_dp (
    .i_clk,
    .i_rst_n,
    .i_config               (dwpu_config),
    .i_dp_instruction_tdata (dp_instruction_tdata),
    .i_dp_instruction_tlast (dp_instruction_tlast),
    .i_dp_instruction_tvalid(dp_instruction_tvalid),
    .o_dp_instruction_tready(dp_instruction_tready),
    .o_dp_done              (dp_done),
    .i_inp_tdata            (i_axis_s_tdata),
    .i_inp_tlast            (i_axis_s_tlast),
    .i_inp_tvalid           (i_axis_s_tvalid),
    .o_inp_tready           (o_axis_s_tready),
    .o_out_tdata            (o_axis_m_tdata),
    .o_out_tlast            (o_axis_m_tlast),
    .o_out_tvalid           (o_axis_m_tvalid),
    .i_out_tready           (i_axis_m_tready),
    .o_dp_status            (csr_hw2reg.dp_status),
    .o_err_act_inp_stream   (dp_error_act_stream_in),
    .o_err_act_oup_stream   (dp_error_act_stream_out)
  );


  //////////////////////////
  // CSR Stream Observers //
  //////////////////////////
  assign csr_hw2reg.dbg_observe.in0_vld.d = i_axis_s_tvalid;
  assign csr_hw2reg.dbg_observe.in0_rdy.d = o_axis_s_tready;
  assign csr_hw2reg.dbg_observe.in0_lst.d = i_axis_s_tlast;
  assign csr_hw2reg.dbg_observe.out_vld.d = o_axis_m_tvalid;
  assign csr_hw2reg.dbg_observe.out_rdy.d = i_axis_m_tready;
  assign csr_hw2reg.dbg_observe.out_lst.d = o_axis_m_tlast;
  assign csr_hw2reg.dbg_observe.dpcmd0_vld.d = dp_instruction_tvalid;
  assign csr_hw2reg.dbg_observe.dpcmd0_rdy.d = dp_instruction_tready;
  assign csr_hw2reg.dbg_observe.dpcmd0_lst.d = dp_instruction_tlast;

  //////////////////////
  // Observation Pins //
  //////////////////////
  aic_common_pkg::aic_dev_obs_t dwpu_obs;
  always_comb dwpu_obs.state          = csr_hw2reg.cmdblk_status.state.d;
  always_comb dwpu_obs.token_stall    = csr_hw2reg.cmdblk_status.wait_token.d;
  always_comb dwpu_obs.dp_instr_stall = cmdb_valid & ~ cmdb_ready;
  always_comb dwpu_obs.dp_cmd_stall   = dp_instruction_tvalid & ~dp_instruction_tready;
  always_comb dwpu_obs.dp_in0_stall   = i_axis_s_tvalid & ~o_axis_s_tready;
  always_comb dwpu_obs.dp_in1_stall   = '0; // DWPU only has one stream input
  always_comb dwpu_obs.dp_out_stall   = o_axis_m_tvalid & ~i_axis_m_tready;
  assign o_obs = dwpu_obs;


  //////////////////
  // CSR Block ID //
  //////////////////
  assign csr_hw2reg.dbg_id.block_id.d    = i_block_id;
  assign csr_hw2reg.dbg_id.ai_core_id.d  = 8'(i_cid);
  assign csr_hw2reg.dbg_id.hw_revision.d = dwpu_pkg::HARDWARE_REVISION;


  //////////
  // IRQs //
  //////////
  logic dbg_sw_interrupt;

  // HW can only set the status to high
  assign csr_hw2reg.irq_status.err_act_stream_in.d     = 1'b1;
  assign csr_hw2reg.irq_status.err_act_stream_out.d    = 1'b1;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.d      = 1'b1;
  assign csr_hw2reg.irq_status.err_illegal_format.d    = 1'b1;
  assign csr_hw2reg.irq_status.err_empty_program.d     = 1'b1;
  assign csr_hw2reg.irq_status.err_main_0_length.d     = 1'b1;
  assign csr_hw2reg.irq_status.err_main_1_length.d     = 1'b1;
  assign csr_hw2reg.irq_status.err_main_2_length.d     = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_0_length.d   = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_1_length.d   = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_0_mapping.d  = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_1_mapping.d  = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_0_segfault.d = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_1_segfault.d = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_order.d      = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_nesting.d    = 1'b1;
  assign csr_hw2reg.irq_status.err_nested_overlap.d    = 1'b1;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.d    = 1'b1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  assign csr_hw2reg.irq_status.err_act_stream_in.de     = dp_error_act_stream_in;
  assign csr_hw2reg.irq_status.err_act_stream_out.de    = dp_error_act_stream_out;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.de      = dbg_sw_interrupt;
  assign csr_hw2reg.irq_status.err_illegal_format.de    = dp_cmd_gen_errors.illegal_format;
  assign csr_hw2reg.irq_status.err_empty_program.de     = dp_cmd_gen_errors.empty_program;
  assign csr_hw2reg.irq_status.err_main_0_length.de     = dp_cmd_gen_errors.main_0_length;
  assign csr_hw2reg.irq_status.err_main_1_length.de     = dp_cmd_gen_errors.main_1_length;
  assign csr_hw2reg.irq_status.err_main_2_length.de     = dp_cmd_gen_errors.main_2_length;
  assign csr_hw2reg.irq_status.err_nested_0_length.de   = dp_cmd_gen_errors.nested_0_length;
  assign csr_hw2reg.irq_status.err_nested_1_length.de   = dp_cmd_gen_errors.nested_1_length;
  assign csr_hw2reg.irq_status.err_nested_0_mapping.de  = dp_cmd_gen_errors.nested_0_mapping;
  assign csr_hw2reg.irq_status.err_nested_1_mapping.de  = dp_cmd_gen_errors.nested_1_mapping;
  assign csr_hw2reg.irq_status.err_nested_0_segfault.de = dp_cmd_gen_errors.nested_0_segfault;
  assign csr_hw2reg.irq_status.err_nested_1_segfault.de = dp_cmd_gen_errors.nested_1_segfault;
  assign csr_hw2reg.irq_status.err_nested_order.de      = dp_cmd_gen_errors.nested_order;
  assign csr_hw2reg.irq_status.err_nested_nesting.de    = dp_cmd_gen_errors.nested_nesting;
  assign csr_hw2reg.irq_status.err_nested_overlap.de    = dp_cmd_gen_errors.nested_overlap;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.de    = cmdblk_cmd_dropped;

  // Combine all IRQs to a single IRQ
  assign o_irq = |(csr_reg2hw.irq_status & csr_reg2hw.irq_en);

  // Connect the DBG_SW_IRQ to the error signal
  assign dbg_sw_interrupt = csr_reg2hw.dp_ctrl.dbg_sw_irq.q;


  // ====================
  // Hardware Capability
  // ====================
  assign csr_hw2reg.hw_capability.cmd_fifo_depth.d      = aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH;
  assign csr_hw2reg.hw_capability.instr_mem_depth.d     = DpCommandMemoryDepth;


  // localparam int unsigned NUM_CHANNELS = aic_common_pkg::PWORD_SIZE;
  // localparam int unsigned IN_PIXEL_WIDTH = 8;
  // localparam int unsigned IN_PWORD_WIDTH = NUM_CHANNELS * IN_PIXEL_WIDTH;
  // localparam int unsigned OUT_PIXEL_WIDTH = 26;
  // localparam int unsigned OUT_PWORD_WIDTH = NUM_CHANNELS * OUT_PIXEL_WIDTH;

endmodule
