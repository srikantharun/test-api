// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA Channel
// Owner: Matt Morris <matt.morris@axelera.ai>



module dma_channel
    import dma_pkg::*;
    import dma_channel_reg_pkg::*;
    import dma_mmu_reg_pkg::*;
    import axe_tcl_sram_pkg::*;
#(  parameter  int unsigned DMA_N_BUF_IDXS = 256,
    parameter  int unsigned DMA_N_IMPL_BUF_IDXS = 256,
    parameter int unsigned NUM_PORTS = 2,
    parameter int unsigned NR_TOK_PROD = 3,
    parameter int unsigned NR_TOK_CONS = 3,
    parameter int unsigned NR_TOP_TOK_PROD = 0,
    parameter int unsigned NR_TOP_TOK_CONS = 0,
    parameter type dma_token_prod_t = logic [NR_TOK_PROD + NR_TOP_TOK_PROD -1:0],
    parameter type dma_token_cons_t = logic [NR_TOK_CONS + NR_TOP_TOK_CONS -1:0]
    )
(
    input  wire            i_clk,
    input  wire            i_rst_n,

    input  impl_inp_t [3:0] i_impl,   // TODO: parameterise properly
    output impl_oup_t [3:0] o_impl,   // TODO: parameterise properly

    input  dma_global_cfg_t i_global_cfg,
    output dma_global_sts_t o_global_sts,

    input  dma_mmu_reg_pkg::axi_a_ch_h2d_t i_chnl_mmu_axi_aw,
    output logic          o_chnl_mmu_axi_awready,
    input  dma_mmu_reg_pkg::axi_a_ch_h2d_t i_chnl_mmu_axi_ar,
    output logic          o_chnl_mmu_axi_arready,
    input  dma_mmu_reg_pkg::axi_w_ch_h2d_t i_chnl_mmu_axi_w,
    output logic          o_chnl_mmu_axi_wready,
    output dma_mmu_reg_pkg::axi_r_ch_d2h_t o_chnl_mmu_axi_r,
    input  logic          i_chnl_mmu_axi_rready,
    output dma_mmu_reg_pkg::axi_b_ch_d2h_t o_chnl_mmu_axi_b,
    input  logic          i_chnl_mmu_axi_bready,
    input  dma_channel_reg_pkg::axi_a_ch_h2d_t i_chnl_csr_axi_aw,
    output logic          o_chnl_csr_axi_awready,
    input  dma_channel_reg_pkg::axi_a_ch_h2d_t i_chnl_csr_axi_ar,
    output logic          o_chnl_csr_axi_arready,
    input  dma_channel_reg_pkg::axi_w_ch_h2d_t i_chnl_csr_axi_w,
    output logic          o_chnl_csr_axi_wready,
    output dma_channel_reg_pkg::axi_r_ch_d2h_t o_chnl_csr_axi_r,
    input  logic          i_chnl_csr_axi_rready,
    output dma_channel_reg_pkg::axi_b_ch_d2h_t o_chnl_csr_axi_b,
    input  logic          i_chnl_csr_axi_bready,
    input  dma_channel_reg_pkg::axi_a_ch_h2d_t i_chnl_cmd_axi_aw,
    output logic          o_chnl_cmd_axi_awready,
    input  dma_channel_reg_pkg::axi_a_ch_h2d_t i_chnl_cmd_axi_ar,
    output logic          o_chnl_cmd_axi_arready,
    input  dma_channel_reg_pkg::axi_w_ch_h2d_t i_chnl_cmd_axi_w,
    output logic          o_chnl_cmd_axi_wready,
    output dma_channel_reg_pkg::axi_r_ch_d2h_t o_chnl_cmd_axi_r,
    input  logic          i_chnl_cmd_axi_rready,
    output dma_channel_reg_pkg::axi_b_ch_d2h_t o_chnl_cmd_axi_b,
    input  logic          i_chnl_cmd_axi_bready,

    output logic [NUM_PORTS-1:0] o_src_xfer_req,
    input  logic [NUM_PORTS-1:0] i_src_xfer_gnt,
    output dma_rd_xfer_t         o_src_xfer,

    input  logic [NUM_PORTS-1:0] i_src_resp_req,
    output logic [NUM_PORTS-1:0] o_src_resp_gnt,
    input  dma_rd_resp_t         i_src_resp     [NUM_PORTS],

    output logic [NUM_PORTS-1:0] o_dst_xfer_req,
    input  logic [NUM_PORTS-1:0] i_dst_xfer_gnt,
    output dma_wr_xfer_t         o_dst_xfer,

    input  logic [NUM_PORTS-1:0] i_dst_resp_req,
    output logic [NUM_PORTS-1:0] o_dst_resp_gnt,
    input  dma_wr_resp_t         i_dst_resp     [NUM_PORTS],


    output dma_token_prod_t      o_tok_prod_vld,
    input  dma_token_prod_t      i_tok_prod_rdy,
    input  dma_token_cons_t      i_tok_cons_vld,
    output dma_token_cons_t      o_tok_cons_rdy,

    output logic                 o_ts_start,
    output logic                 o_ts_end,
    output logic                 o_acd_sync,
    output dma_dev_obs_t         o_obs,

    output dma_chnl_sts_t        o_sts,
    output logic                 o_int
);

  dma_desc_t    channel_desc;
  logic         channel_en;
  logic         src_busy;
  logic         buf_busy;
  logic         dst_busy;

  logic         alloc_req;
  logic         alloc_gnt;
  dma_tid_t     alloc_tid;
  dma_alloc_t   alloc;

  logic         [DMA_N_RX_IDS-1:0] buf_data_req;
  logic         [DMA_N_RX_IDS-1:0] buf_data_gnt;
  dma_bufdata_t buf_data;


  dma_channel_reg2hw_t reg2hw;
  dma_channel_hw2reg_t hw2reg;

  dma_desc_end_t desc_src;
  dma_desc_end_t desc_dst;
  dma_desc_t     desc;

  logic          en_val;
  logic          en_hus;
  logic          clr_val;
  logic          clr_hus;

  logic          cmd_vld;
  logic          cmd_rdy;
  logic          cmd_done;
  logic [DMA_CMD_SIZE-1:0] cmd_data;
  logic [$clog2(DMA_CMD_N_FORMATS)-1:0] cmd_format;

  dma_ll_t       ll;
  logic          ll_req;

  dma_mmu_reg2hw_t mmu_cfg;
  dma_channel_hw2reg_cmdblk_status_reg_t cmd_sts;

  dma_mmu_reg_top u_mmu_csr
  (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),

    .axi_aw_i   (i_chnl_mmu_axi_aw),
    .axi_awready(o_chnl_mmu_axi_awready),
    .axi_ar_i   (i_chnl_mmu_axi_ar),
    .axi_arready(o_chnl_mmu_axi_arready),
    .axi_w_i    (i_chnl_mmu_axi_w),
    .axi_wready (o_chnl_mmu_axi_wready),
    .axi_b_o    (o_chnl_mmu_axi_b),
    .axi_bready (i_chnl_mmu_axi_bready),
    .axi_r_o    (o_chnl_mmu_axi_r),
    .axi_rready (i_chnl_mmu_axi_rready),
    // To HW
    .reg2hw     (mmu_cfg), // Write
    // Config
    .devmode_i  (1'b1)
  );

  dma_channel_reg_top u_csr
  (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),

    .axi_aw_i   (i_chnl_csr_axi_aw),
    .axi_awready(o_chnl_csr_axi_awready),
    .axi_ar_i   (i_chnl_csr_axi_ar),
    .axi_arready(o_chnl_csr_axi_arready),
    .axi_w_i    (i_chnl_csr_axi_w),
    .axi_wready (o_chnl_csr_axi_wready),
    .axi_b_o    (o_chnl_csr_axi_b),
    .axi_bready (i_chnl_csr_axi_bready),
    .axi_r_o    (o_chnl_csr_axi_r),
    .axi_rready (i_chnl_csr_axi_rready),
    // To HW
    .reg2hw, // Write
    .hw2reg, // Read
    // Config
    .devmode_i  (1'b1)
  );

  always_comb hw2reg = '{ cmdblk_status : cmd_sts,
                          ch_ctrl : '{
                            enable : '{ d : en_val,
                                        de: en_hus },
                            clear  : '{ d : clr_val,
                                        de: clr_hus },
                            interrupt_clr : '{ d : 1'b0,
                                               de: 1'b0 }},
                          ch_status : 1'b0,
                          ch_err_info : '{
                            slv_err : 1'b0,
                            dec_err : 1'b0,
                            cfg_err : 1'b0,
                            ecc_err : 1'b0,
                            ecc_err_type : 1'b0,
                            ecc_err_mem_loc : 26'h0 }
                         };

  always_comb desc_dst = '{ osr_lmt     : reg2hw.ch_ctrl.dst_osr_lmt,
                            max_burstlen: reg2hw.ch_cfg.dst_burstlen,
                            yaddrstride : reg2hw.ch_yaddrstride.dst_yaddrstride,
                            yrowsize    : reg2hw.ch_yrowsize.dst_yrowsize,
                            xaddrinc    : reg2hw.ch_xaddrinc.dst_xaddrinc,
                            xbytesize   : reg2hw.ch_xbytesize.dst_xbytesize,
                            addr        : reg2hw.ch_dst_addr,
                            port        : dma_port_sel_t'(reg2hw.ch_ctrl.dst_ms) };
  always_comb desc_src = '{ osr_lmt     : reg2hw.ch_ctrl.src_osr_lmt,
                            max_burstlen: reg2hw.ch_cfg.src_burstlen,
                            yaddrstride : reg2hw.ch_yaddrstride.src_yaddrstride,
                            yrowsize    : reg2hw.ch_yrowsize.src_yrowsize,
                            xaddrinc    : reg2hw.ch_xaddrinc.src_xaddrinc,
                            xbytesize   : reg2hw.ch_xbytesize.src_xbytesize,
                            addr        : reg2hw.ch_src_addr,
                            port        : dma_port_sel_t'(reg2hw.ch_ctrl.src_ms) };
  always_comb desc     = '{ glb         : '{ trans_size  : reg2hw.ch_cfg.transize,
                                             ytype       : dma_type_e'(reg2hw.ch_cfg.ytype),
                                             xtype       : dma_type_e'(reg2hw.ch_cfg.xtype),
                                             mmu_en      : reg2hw.ch_ctrl.mmu_en,
                                             int_en      : reg2hw.ch_ctrl.interrupt_en,
                                             fill_mode   : reg2hw.ch_cfg.fillval_mode,
                                             fill_val    : reg2hw.ch_cfg.fillval },
                            dst_xfer    : '{ xfer_attr_user      : reg2hw.ch_tran_cfg.dstuserfield,
                                             xfer_attr_priv      : reg2hw.ch_tran_cfg.dstprivattr,
                                             xfer_attr_nonsecure : reg2hw.ch_tran_cfg.dstnonsecattr,
                                             xfer_attr_shareable : reg2hw.ch_tran_cfg.dstshareattr,
                                             mem_attr_hi         : reg2hw.ch_tran_cfg.dstmemattrhi,
                                             mem_attr_lo         : reg2hw.ch_tran_cfg.dstmemattrlo },
                            src_xfer    : '{ xfer_attr_user      : reg2hw.ch_tran_cfg.srcuserfield,
                                             xfer_attr_priv      : reg2hw.ch_tran_cfg.srcprivattr,
                                             xfer_attr_nonsecure : reg2hw.ch_tran_cfg.srcnonsecattr,
                                             xfer_attr_shareable : reg2hw.ch_tran_cfg.srcshareattr,
                                             mem_attr_hi         : reg2hw.ch_tran_cfg.srcmemattrhi,
                                             mem_attr_lo         : reg2hw.ch_tran_cfg.srcmemattrlo },
                            ll          : '{ port                : dma_port_sel_t'(reg2hw.ch_ctrl.ll_ms),
                                             ll_en               : reg2hw.ch_ctrl.ll_en,
                                             ll_mode             : reg2hw.ch_ctrl.ll_mode,
                                             ll_last             : reg2hw.ch_link_descr.ll_last,
                                             ll_addr             : { reg2hw.ch_link_descr.link_addr, 3'b000} },
                            dst         : desc_dst,
                            src         : desc_src };

  logic [NR_TOK_CONS + NR_TOP_TOK_CONS-1:0] pending_tokens;
  if (NR_TOK_CONS + NR_TOP_TOK_CONS > 32) begin : g_tot_cons_gt_32
    always_comb cmd_sts.pending_tokens = pending_tokens[31:0];
  end: g_tot_cons_gt_32
  else begin : g_tot_cons_le_32
    always_comb cmd_sts.pending_tokens = { {32-NR_TOK_CONS-NR_TOP_TOK_CONS{1'b0}}, pending_tokens};
  end: g_tot_cons_le_32

  ///// Timestamp:
  cmdblock #(
    .IDW                ( dma_reg_pkg::AXI_IDW ),
    .AW                 ( dma_reg_pkg::AXI_AW ),
    .DW                 ( 64 ),
    .BW                 ( 8 ),
    .DYNAMIC_CMD_SIZE   ( 'h240 ),    // CMD without token, 9 x 8 = 72B  = 10 0100 0000
    .NR_TOK_PROD        ( NR_TOK_PROD ),
    .NR_TOK_CONS        ( NR_TOK_CONS ),
    .NR_TOP_TOK_PROD    ( NR_TOP_TOK_PROD ),
    .NR_TOP_TOK_CONS    ( NR_TOP_TOK_CONS ),
    .MAX_OUTST_CMDS     ( 2 ),
    .DESC_MEM_ARB_SCHEME( 1 ),
    .CMD_FIFO_DEPTH     ( 20 ),
    .CMD_FIFO_WIDTH     ( 2*8*8 ),
    .NR_FORMATS         ( 5 ),
    .FORMAT_NR_BYTES    ( {6*8, 7*8, 8*8, 9*8, 2*8} )
  ) u_cmdblock (
    .i_clk,
    .i_rst_n,

    ///// Sideband
    .exec         (reg2hw.cmdblk_ctrl.exec_en),
    .pointer_rst  (reg2hw.cmdblk_ctrl.ptr_rst),

    .cmd_dropped  (),         // output - for irqs (dropping on the push side) (overflow) - 1 cmd per cycle of high

    // status:
    .stat_cur_pointer     (cmd_sts.in_word_ptr),   // status to csr
    .stat_cur_fifo_count  (cmd_sts.fifo_cnt),
    .stat_nr_outst_cmds   (cmd_sts.outst_cmds),
    .stat_wait_token      (cmd_sts.wait_token),
    .o_stat_state         (cmd_sts.state.d),
    .o_stat_pending_tokens(pending_tokens),

    ///// AXI slave:
    // Write Address Channel
    .awid   (i_chnl_cmd_axi_aw.id),
    .awaddr (i_chnl_cmd_axi_aw.addr),
    .awlen  (i_chnl_cmd_axi_aw.len),
    .awsize (i_chnl_cmd_axi_aw.size),
    .awburst(i_chnl_cmd_axi_aw.burst),
    // input  wire [  MT_LW-1:0] awlock,
    // input  wire [        3:0] awcache,
    // input  wire [       2:0] awprot,
    .awvalid(i_chnl_cmd_axi_aw.valid),
    .awready(o_chnl_cmd_axi_awready),
    // Read Address Channel
    .arid   (i_chnl_cmd_axi_ar.id),
    .araddr (i_chnl_cmd_axi_ar.addr),
    .arlen  (i_chnl_cmd_axi_ar.len),
    .arsize (i_chnl_cmd_axi_ar.size),
    .arburst(i_chnl_cmd_axi_ar.burst),
    // input  wire [  MT_LW-1:0] arlock,
    // input  wire [        3:0] arcache,
    // input  wire [       2:0] arprot,
    .arvalid(i_chnl_cmd_axi_ar.valid),
    .arready(o_chnl_cmd_axi_arready),
    // Write  Data Channel
    .wdata  (i_chnl_cmd_axi_w.data),
    .wstrb  (i_chnl_cmd_axi_w.strb),
    .wlast  (i_chnl_cmd_axi_w.last),
    .wvalid (i_chnl_cmd_axi_w.valid),
    .wready (o_chnl_cmd_axi_wready),
    // Read Data Channel
    .rid    (o_chnl_cmd_axi_r.id),
    .rdata  (o_chnl_cmd_axi_r.data),
    .rresp  (o_chnl_cmd_axi_r.resp),
    .rlast  (o_chnl_cmd_axi_r.last),
    .rvalid (o_chnl_cmd_axi_r.valid),
    .rready (i_chnl_cmd_axi_rready),
    // Write Response Channel
    .bid    (o_chnl_cmd_axi_b.id),
    .bresp  (o_chnl_cmd_axi_b.resp),
    .bvalid (o_chnl_cmd_axi_b.valid),
    .bready (i_chnl_cmd_axi_bready),

    ///// Tokens:
    .tok_prod_vld (o_tok_prod_vld),
    .tok_prod_rdy (i_tok_prod_rdy),
    .tok_cons_vld (i_tok_cons_vld),
    .tok_cons_rdy (o_tok_cons_rdy),

    ///// Timestamp:
    .o_ts_start,
    .o_ts_end,

    ///// ACD sync:
    .o_acd_sync,

    ///// Command:
    .cmd_done     (cmd_done), // TMP: Flag done directly
    .cmd_data     (cmd_data),
    .cmd_format   (cmd_format),
    .cmd_config   (),     // shouldn't need this - all 8b
    .cmd_vld      (cmd_vld),
    .cmd_rdy      (cmd_rdy)
  );

  dma_channel_ctrl u_ctrl (
    .i_clk,
    .i_rst_n,
    .i_en        (reg2hw.ch_ctrl.enable),
    .i_desc      (desc),
    .i_int_en    (reg2hw.ch_ctrl.interrupt_en),
    .i_int_clr   (reg2hw.ch_ctrl.clear),
    .o_int,
    .o_en_val    (en_val),
    .o_en_hus    (en_hus),
    .o_clr_val   (clr_val),
    .o_clr_hus   (clr_hus),
    .i_global_cfg,
    .o_global_sts,
    .i_cmd_vld   (cmd_vld),
    .o_cmd_rdy   (cmd_rdy),
    .o_cmd_done  (cmd_done),
    .i_cmd_data  (cmd_data),
    .i_cmd_format(cmd_format),
    .o_ll        (ll),
    .o_ll_req    (ll_req),
    .i_ll_data_req (buf_data_req[1]),
    .o_ll_data_gnt (buf_data_gnt[1]),
    .i_ll_data     (buf_data),
    .o_desc      (channel_desc),
    .o_en        (channel_en),
    .i_busy      ({dst_busy, buf_busy, src_busy})
  );

  dma_channel_src #(
    .NUM_PORTS (NUM_PORTS)
  ) u_src (
    .i_clk,
    .i_rst_n,

    .i_mmu_cfg      (mmu_cfg),
    .o_mmu_irq      (),

    .i_ll_req       (ll_req),
    .i_ll           (ll),

    .i_desc         (channel_desc),
    .i_en           (channel_en),
    .o_busy         (src_busy),

    .o_alloc_req    (alloc_req),
    .i_alloc_gnt    (alloc_gnt),
    .o_alloc        (alloc),
    .i_tid          (alloc_tid),

    .o_src_xfer_req,
    .i_src_xfer_gnt,
    .o_src_xfer

  );

  dma_channel_buffer #(
    .NUM_PORTS  (NUM_PORTS),
    .DMA_N_BUF_IDXS (DMA_N_BUF_IDXS),
    .DMA_N_IMPL_BUF_IDXS (DMA_N_IMPL_BUF_IDXS)
  ) u_buffer (
    .i_clk,
    .i_rst_n,

    .i_impl,
    .o_impl,

    .i_en          (channel_en),
    .o_busy        (buf_busy),
    .i_overalloc_mode(reg2hw.ch_ctrl.overalloc_mode),

    .i_alloc_req   (alloc_req),
    .o_alloc_gnt   (alloc_gnt),
    .i_alloc       (alloc),
    .o_tid         (alloc_tid),

    .i_src_resp_req,
    .o_src_resp_gnt,
    .i_src_resp,

    .o_rx_data_req     (buf_data_req),
    .i_rx_data_gnt     (buf_data_gnt),
    .o_rx_data         (buf_data)
  );

  dma_channel_dst #(
    .NUM_PORTS (NUM_PORTS)
  ) u_dst (
    .i_clk,
    .i_rst_n,

    .i_mmu_cfg      (mmu_cfg),
    .o_mmu_irq      (),

    .i_desc         (channel_desc),
    .i_en           (channel_en),
    .o_busy         (dst_busy),

    .i_data_req    (buf_data_req[0]),
    .o_data_gnt    (buf_data_gnt[0]),
    .i_data        (buf_data),

    .i_src_busy    (src_busy),
    .i_buf_busy    (buf_busy),

    .o_dst_xfer_req,
    .i_dst_xfer_gnt,
    .o_dst_xfer,

    .i_dst_resp_req,
    .o_dst_resp_gnt,
    .i_dst_resp
  );

  always_comb o_obs = dma_dev_obs_t'{
    state         : cmd_sts.wait_token,
    token_stall   : cmd_sts.state,
    dp_instr_stall: cmd_vld & ~cmd_rdy
  };

endmodule
