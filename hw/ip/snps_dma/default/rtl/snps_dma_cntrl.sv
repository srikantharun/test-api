// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA control module, AXI2AHB only or complete with CMD Block
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module snps_dma_cntrl
  import snps_dma_pkg::*;
#(
  // Address regions, only required in case CFG.cmdblock_present is one:
  parameter int NR_REGIONS = 1,
  parameter int REGION_SLAVE_ID[NR_REGIONS] = {
    0
  },
  parameter longint REGION_ST_ADDR[NR_REGIONS] = {
    'h0_0000
  },
  parameter longint REGION_END_ADDR[NR_REGIONS] = {
    'h0_ffff
  },

  parameter int unsigned SL_AW = 40,
  parameter int unsigned SL_DW = 64,
  parameter int unsigned SL_IDW = 6,
  parameter int unsigned SL_BW = 8,

  parameter int unsigned NR_TOK_PROD = 3,
  parameter int unsigned NR_TOK_CONS = 3,
  parameter int unsigned NR_TOP_TOK_PROD = 3,
  parameter int unsigned NR_TOP_TOK_CONS = 3,

  parameter snps_dma_cfg_t CFG = SNPS_DMA_AIC_HT_CFG,

  localparam int unsigned NR_CH = CFG.dma_nbr_channels
) (
  input   wire  i_clk,
  input   wire  i_rst_n,

  ///// AXI subordinate:
  // Write Address Channel
  input  logic [ SL_IDW-1:0] i_awid,
  input  logic [  SL_AW-1:0] i_awaddr,
  input  logic [  SL_BW-1:0] i_awlen,
  input  logic [     2:0]    i_awsize,
  input  logic [     1:0]    i_awburst,
  input  logic               i_awvalid,
  output logic               o_awready,
  // Read Address Channel
  input  logic [ SL_IDW-1:0] i_arid,
  input  logic [  SL_AW-1:0] i_araddr,
  input  logic [  SL_BW-1:0] i_arlen,
  input  logic [     2:0]    i_arsize,
  input  logic [     1:0]    i_arburst,
  input  logic               i_arvalid,
  output logic               o_arready,
  // Write  Data Channel
  input  logic [  SL_DW-1:0] i_wdata,
  input  logic [SL_DW/8-1:0] i_wstrb,
  input  logic               i_wlast,
  input  logic               i_wvalid,
  output logic               o_wready,
  // Read Data Channel
  output logic [ SL_IDW-1:0] o_rid,
  output logic [  SL_DW-1:0] o_rdata,
  output logic [     1:0]    o_rresp,
  output logic               o_rlast,
  output logic               o_rvalid,
  input  logic               i_rready,
  // Write Response Channel
  output logic [ SL_IDW-1:0] o_bid,
  output logic [     1:0]    o_bresp,
  output logic               o_bvalid,
  input  logic               i_bready,

  // AHB to DMA:
  output logic               o_hsel,
  output logic  [32-1:0]     o_haddr,
  output logic  [3-1:0]      o_hsize,
  output logic  [1:0]        o_htrans,
  output logic               o_hready,
  output logic               o_hwrite,
  output logic  [SL_DW-1: 0] o_hwdata,
  input  logic  [SL_DW-1:0]  i_hrdata,
  input  logic  [1:0]        i_hresp,
  input  logic               i_hready_resp,

  ///// Tokens:
  output logic [NR_CH-1:0][NR_TOK_PROD+NR_TOP_TOK_PROD-1:0]  o_tok_prod_vld,
  input  logic [NR_CH-1:0][NR_TOK_PROD+NR_TOP_TOK_PROD-1:0]  i_tok_prod_rdy,
  input  logic [NR_CH-1:0][NR_TOK_CONS+NR_TOP_TOK_CONS-1:0]  i_tok_cons_vld,
  output logic [NR_CH-1:0][NR_TOK_CONS+NR_TOP_TOK_CONS-1:0]  o_tok_cons_rdy,

  output logic [NR_CH-1:0] o_cmd_dropped,

  ///// Timestamp:
  output logic [NR_CH-1:0] o_ts_start,
  output logic [NR_CH-1:0] o_ts_end,
  ///// ACD sync:
  output logic [NR_CH-1:0] o_acd_sync,

  // DMA status:
  input logic [NR_CH-1:0]  debug_ch_en
);
  localparam int NR_REG_DEVS = (CFG.cmdblock_present) ? 1 + NR_CH : 1;
  /////////////////////////////////////////////
  // Reg Write path:
  logic [NR_REG_DEVS-1:0]                dev2reg_wvld;
  logic [NR_REG_DEVS-1:0]                dev2reg_wrdy;
  logic [NR_REG_DEVS-1:0][    SL_AW-1:0] dev2reg_waddr;
  logic [NR_REG_DEVS-1:0][    SL_DW-1:0] dev2reg_wdata;
  logic [NR_REG_DEVS-1:0][(SL_DW/8)-1:0] dev2reg_wstrb;
  logic [NR_REG_DEVS-1:0]                dev2reg_wresp_vld;
  logic [NR_REG_DEVS-1:0]                dev2reg_wresp_rdy;
  logic [NR_REG_DEVS-1:0]                dev2reg_wresp_error;
  logic [NR_REG_DEVS-1:0][SL_AW+SL_DW+(SL_DW/8)-1:0] dev2reg_arb_wreq_data;
  // Reg Read path:
  logic [NR_REG_DEVS-1:0]                dev2reg_rvld;
  logic [NR_REG_DEVS-1:0]                dev2reg_rrdy;
  logic [NR_REG_DEVS-1:0][SL_AW-1:0]     dev2reg_raddr;
  logic [NR_REG_DEVS-1:0]                dev2reg_rresp_vld;
  logic [NR_REG_DEVS-1:0]                dev2reg_rresp_rdy;
  logic [NR_REG_DEVS-1:0]                dev2reg_rresp_error;
  logic [NR_REG_DEVS-1:0][SL_DW-1:0]     dev2reg_rresp_data;
  logic [NR_REG_DEVS-1:0][1+SL_DW-1:0]   dev2reg_arb_rresp_data;

  ////// Reg2AHB
  // Reg Write path:
  logic                 reg2ahb_wvld;
  logic                 reg2ahb_wrdy;
  logic [    SL_AW-1:0] reg2ahb_waddr;
  logic [    SL_DW-1:0] reg2ahb_wdata;
  logic [(SL_DW/8)-1:0] reg2ahb_wstrb;
  logic                 reg2ahb_wresp_vld;
  logic                 reg2ahb_wresp_rdy;
  logic                 reg2ahb_wresp_error;
  logic [SL_AW+SL_DW+(SL_DW/8)-1:0] reg2ahb_arb_wreq_data;
  // Reg Read path:
  logic                 reg2ahb_rvld;
  logic                 reg2ahb_rrdy;
  logic [SL_AW-1:0]     reg2ahb_raddr;
  logic                 reg2ahb_rresp_vld;
  logic                 reg2ahb_rresp_rdy;
  logic                 reg2ahb_rresp_error;
  logic [SL_DW-1:0]     reg2ahb_rresp_data;
  logic [1+SL_DW-1:0]   reg2ahb_arb_rresp_data;

  /////////////////////////////////////////////
  // bus:
    // 1 AXI2AHB direct connection
    // NR_CH times CSR, and CMD
  localparam int unsigned NR_AXI_DEVS = (CFG.cmdblock_present) ? 1 + NR_CH * 2 : 1;

  logic [NR_AXI_DEVS-1:0][ SL_IDW-1:0] awid;
  logic [NR_AXI_DEVS-1:0][  SL_AW-1:0] awaddr;
  logic [NR_AXI_DEVS-1:0][  SL_BW-1:0] awlen;
  logic [NR_AXI_DEVS-1:0][     2:0]    awsize;
  logic [NR_AXI_DEVS-1:0][     1:0]    awburst;
  logic [NR_AXI_DEVS-1:0]              awvalid;
  logic [NR_AXI_DEVS-1:0]              awready;
  logic [NR_AXI_DEVS-1:0][ SL_IDW-1:0] arid;
  logic [NR_AXI_DEVS-1:0][  SL_AW-1:0] araddr;
  logic [NR_AXI_DEVS-1:0][  SL_BW-1:0] arlen;
  logic [NR_AXI_DEVS-1:0][     2:0]    arsize;
  logic [NR_AXI_DEVS-1:0][     1:0]    arburst;
  logic [NR_AXI_DEVS-1:0]              arvalid;
  logic [NR_AXI_DEVS-1:0]              arready;
  logic [NR_AXI_DEVS-1:0][  SL_DW-1:0] wdata;
  logic [NR_AXI_DEVS-1:0][SL_DW/8-1:0] wstrb;
  logic [NR_AXI_DEVS-1:0]              wlast;
  logic [NR_AXI_DEVS-1:0]              wvalid;
  logic [NR_AXI_DEVS-1:0]              wready;
  logic [NR_AXI_DEVS-1:0][ SL_IDW-1:0] rid;
  logic [NR_AXI_DEVS-1:0][  SL_DW-1:0] rdata;
  logic [NR_AXI_DEVS-1:0][     1:0]    rresp;
  logic [NR_AXI_DEVS-1:0]              rlast;
  logic [NR_AXI_DEVS-1:0]              rvalid;
  logic [NR_AXI_DEVS-1:0]              rready;
  logic [NR_AXI_DEVS-1:0][ SL_IDW-1:0] bid;
  logic [NR_AXI_DEVS-1:0][     1:0]    bresp;
  logic [NR_AXI_DEVS-1:0]              bvalid;
  logic [NR_AXI_DEVS-1:0]              bready;

  if (CFG.cmdblock_present) begin : g_cmdbs
    ///////////////////////////////////
    import snps_dma_cmdb_csr_reg_pkg::*;
    axi_a_ch_h2d_t   csr_aw[NR_CH];
    axi_a_ch_h2d_t   csr_ar[NR_CH];
    axi_w_ch_h2d_t   csr_w[NR_CH];
    axi_b_ch_d2h_t   csr_b[NR_CH];
    axi_r_ch_d2h_t   csr_r[NR_CH];
    snps_dma_cmdb_csr_reg2hw_t csr_reg2hw[NR_CH];
    snps_dma_cmdb_csr_hw2reg_t csr_hw2reg[NR_CH];

    logic [$clog2(NR_AXI_DEVS+1)-1:0] bus_sel_rd;
    logic [$clog2(NR_AXI_DEVS+1)-1:0] bus_sel_wr;
    aic_fabric_addr_decoder #(
      .AW(SL_AW),
      .DEFAULT_SLAVE('1),
      .NOT_THIS_CORE_SLAVE('1),
      .NR_SLAVES(NR_AXI_DEVS),
      .NR_REGIONS(NR_REGIONS),
      .REGION_ST_ADDR(REGION_ST_ADDR),
      .REGION_END_ADDR(REGION_END_ADDR),
      .REGION_SLAVE_ID(REGION_SLAVE_ID)
    ) u_ext_decode_wr (
      .addr_in(i_awaddr),
      .core_id('0),

      .sl_select(bus_sel_wr)
    );
    aic_fabric_addr_decoder #(
      .AW(SL_AW),
      .DEFAULT_SLAVE('1),
      .NOT_THIS_CORE_SLAVE('1),
      .NR_SLAVES(NR_AXI_DEVS),
      .NR_REGIONS(NR_REGIONS),
      .REGION_ST_ADDR(REGION_ST_ADDR),
      .REGION_END_ADDR(REGION_END_ADDR),
      .REGION_SLAVE_ID(REGION_SLAVE_ID)
    ) u_ext_decode_rd (
      .addr_in(i_araddr),
      .core_id('0),

      .sl_select(bus_sel_rd)
    );
    // AXI bus:
    simple_axi_demux #(
      .NR_MASTERS(NR_AXI_DEVS),
      .IDW(SL_IDW),
      .AW(SL_AW),
      .DW(SL_DW),
      .BW(SL_BW),
      .SL_WREQ_SHIELD(2),
      .SL_RREQ_SHIELD(2),
      .SL_WDATA_SHIELD(2),
      .SL_WRESP_SHIELD(2),
      .SL_RRESP_SHIELD(2),
      .OSR(4),
      .EXT_SEL(1)
    ) u_bus (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .i_ext_mt_sel_rd(bus_sel_rd),
      .i_ext_mt_sel_wr(bus_sel_wr),

      // IP -> DMC:
      // write address channel:
      .s_awvalid(i_awvalid),
      .s_awaddr(i_awaddr),
      .s_awid(i_awid),
      .s_awlen(i_awlen),
      .s_awsize(i_awsize),
      .s_awburst(i_awburst),
      .s_awlock('0),
      .s_awcache('0),
      .s_awprot('0),
      .s_awready(o_awready),

      // write data channel:
      .s_wvalid(i_wvalid),
      .s_wdata(i_wdata),
      .s_wstrb(i_wstrb),
      .s_wlast(i_wlast),
      .s_wready(o_wready),

      // write response channel:
      .s_bvalid(o_bvalid),
      .s_bid(o_bid),
      .s_bresp(o_bresp),
      .s_bready(i_bready),

      // read address channel:
      .s_arvalid(i_arvalid),
      .s_araddr(i_araddr),
      .s_arid(i_arid),
      .s_arlen(i_arlen),
      .s_arsize(i_arsize),
      .s_arburst(i_arburst),
      .s_arlock('0),
      .s_arcache('0),
      .s_arprot('0),
      .s_arready(o_arready),

      // read response channel:
      .s_rvalid(o_rvalid),
      .s_rid(o_rid),
      .s_rdata(o_rdata),
      .s_rresp(o_rresp),
      .s_rlast(o_rlast),
      .s_rready(i_rready),

      // DMC -> devs:
      // write address channel:
      .m_awvalid(awvalid),
      .m_awaddr(awaddr),
      .m_awid(awid),
      .m_awlen(awlen),
      .m_awsize(awsize),
      .m_awburst(awburst),
      // spyglass disable_block W287b
      .m_awlock(),
      .m_awcache(),
      .m_awprot(),
      // spyglass enable_block W287b
      .m_awready(awready),

      // write data channel:
      .m_wvalid(wvalid),
      .m_wdata (wdata),
      .m_wstrb (wstrb),
      .m_wlast (wlast),
      .m_wready(wready),

      // write response channel:
      .m_bvalid(bvalid),
      .m_bid(bid),
      .m_bresp(bresp),
      .m_bready(bready),

      // read address channel:
      .m_arvalid(arvalid),
      .m_araddr(araddr),
      .m_arid(arid),
      .m_arlen(arlen),
      .m_arsize(arsize),
      .m_arburst(arburst),
      // spyglass disable_block W287b
      .m_arlock(),
      .m_arcache(),
      .m_arprot(),
      // spyglass enable_block W287b
      .m_arready(arready),

      // read response channel:
      .m_rvalid(rvalid),
      .m_rid(rid),
      .m_rdata(rdata),
      .m_rresp(rresp),
      .m_rlast(rlast),
      .m_rready(rready)
    );

    for (genvar ch=0; ch<NR_CH; ch++) begin: g_ch
      // CSR:
      snps_dma_cmdb_csr_reg_top u_csr (
        .clk_i (i_clk),
        .rst_ni(i_rst_n),

        .axi_aw_i(csr_aw[ch]),
        .axi_awready(awready[csr_base_idx+2*ch]),
        .axi_ar_i(csr_ar[ch]),
        .axi_arready(arready[csr_base_idx+2*ch]),
        .axi_w_i(csr_w[ch]),
        .axi_wready(wready[csr_base_idx+2*ch]),
        .axi_b_o(csr_b[ch]),
        .axi_bready(bready[csr_base_idx+2*ch]),
        .axi_r_o(csr_r[ch]),
        .axi_rready(rready[csr_base_idx+2*ch]),
        // To HW:
        .reg2hw(csr_reg2hw[ch]),
        .hw2reg(csr_hw2reg[ch]),
        // Config
        .devmode_i(1'b1)
      );

      always_comb begin
        csr_aw[ch].id = awid[csr_base_idx+2*ch];
        csr_aw[ch].addr = awaddr[csr_base_idx+2*ch];
        csr_aw[ch].len = awlen[csr_base_idx+2*ch];
        csr_aw[ch].size = awsize[csr_base_idx+2*ch];
        csr_aw[ch].burst = awburst[csr_base_idx+2*ch];
        csr_aw[ch].valid = awvalid[csr_base_idx+2*ch];
        csr_ar[ch].id = arid[csr_base_idx+2*ch];
        csr_ar[ch].addr = araddr[csr_base_idx+2*ch];
        csr_ar[ch].len = arlen[csr_base_idx+2*ch];
        csr_ar[ch].size = arsize[csr_base_idx+2*ch];
        csr_ar[ch].burst = arburst[csr_base_idx+2*ch];
        csr_ar[ch].valid = arvalid[csr_base_idx+2*ch];
        csr_w[ch].data = wdata[csr_base_idx+2*ch];
        csr_w[ch].strb = wstrb[csr_base_idx+2*ch];
        csr_w[ch].last = wlast[csr_base_idx+2*ch];
        csr_w[ch].valid = wvalid[csr_base_idx+2*ch];
        bid[csr_base_idx+2*ch] = csr_b[ch].id;
        bresp[csr_base_idx+2*ch] = csr_b[ch].resp;
        bvalid[csr_base_idx+2*ch] = csr_b[ch].valid;
        rid[csr_base_idx+2*ch] = csr_r[ch].id;
        rdata[csr_base_idx+2*ch] = csr_r[ch].data;
        rresp[csr_base_idx+2*ch] = csr_r[ch].resp;
        rlast[csr_base_idx+2*ch] = csr_r[ch].last;
        rvalid[csr_base_idx+2*ch] = csr_r[ch].valid;
      end

      // CMD Block:
      // Workaround for Fusion Compiler
      localparam int unsigned CommandBlockMaxOutstandingCommands = CFG.cmdblock_max_outst_cmds;
      localparam int unsigned CommandBlockFifoDepth = CFG.cmdblock_fifo_depth;

      logic cmd_vld;
      cmdblock #(
        .IDW(SL_IDW),
        .AW (SL_AW),
        .DW (SL_DW),
        .BW (SL_BW),

        .DYNAMIC_CMD_SIZE('h100), // to be determined
        .NR_TOK_PROD(NR_TOK_PROD),
        .NR_TOK_CONS(NR_TOK_CONS),
        .NR_TOP_TOK_PROD(NR_TOP_TOK_PROD),
        .NR_TOP_TOK_CONS(NR_TOP_TOK_CONS),
        .MAX_OUTST_CMDS(CommandBlockMaxOutstandingCommands),

        .CMD_FIFO_DEPTH(CommandBlockFifoDepth),
        .CMD_FIFO_WIDTH('h100), // to be determined
        .DEV_ADDR_CAP  (REGION_END_ADDR[cmd_base_idx+2*ch] - REGION_ST_ADDR[cmd_base_idx+2*ch] + 1),

        .NR_FORMATS(1), // to be determined
        .FORMAT_NR_BYTES({'h10}) // to be determined
      ) u_cmd_block (
        .i_clk  (i_clk),
        .i_rst_n(i_rst_n),

        ///// Sideband:
        .exec(csr_reg2hw[ch].cmdblk_ctrl.exec_en.q),
        .pointer_rst(csr_reg2hw[ch].cmdblk_ctrl.ptr_rst.q),
        .cmd_dropped(o_cmd_dropped[ch]),

        // status:
        .stat_cur_pointer(csr_hw2reg[ch].cmdblk_status.in_word_ptr.d),
        .stat_cur_fifo_count(csr_hw2reg[ch].cmdblk_status.fifo_cnt.d),
        .stat_nr_outst_cmds(csr_hw2reg[ch].cmdblk_status.outst_cmds.d ),
        .stat_wait_token(csr_hw2reg[ch].cmdblk_status.wait_token.d),
        .o_stat_state(csr_hw2reg[ch].cmdblk_status.state.d),
        .o_stat_pending_tokens(csr_hw2reg[ch].cmdblk_status.pending_tokens.d),

        ///// AXI slave:
        // Write Address Channel
        .awid(awid[cmd_base_idx+2*ch]),
        .awaddr(awaddr[cmd_base_idx+2*ch]),
        .awlen(awlen[cmd_base_idx+2*ch]),
        .awsize(awsize[cmd_base_idx+2*ch]),
        .awburst(awburst[cmd_base_idx+2*ch]),
        .awvalid(awvalid[cmd_base_idx+2*ch]),
        .awready(awready[cmd_base_idx+2*ch]),
        // Read Address Channel
        .arid(arid[cmd_base_idx+2*ch]),
        .araddr(araddr[cmd_base_idx+2*ch]),
        .arlen(arlen[cmd_base_idx+2*ch]),
        .arsize(arsize[cmd_base_idx+2*ch]),
        .arburst(arburst[cmd_base_idx+2*ch]),
        .arvalid(arvalid[cmd_base_idx+2*ch]),
        .arready(arready[cmd_base_idx+2*ch]),
        // Write  Data Channel
        .wdata(wdata[cmd_base_idx+2*ch]),
        .wstrb(wstrb[cmd_base_idx+2*ch]),
        .wlast(wlast[cmd_base_idx+2*ch]),
        .wvalid(wvalid[cmd_base_idx+2*ch]),
        .wready(wready[cmd_base_idx+2*ch]),
        // Read Data Channel
        .rid(rid[cmd_base_idx+2*ch]),
        .rdata(rdata[cmd_base_idx+2*ch]),
        .rresp(rresp[cmd_base_idx+2*ch]),
        .rlast(rlast[cmd_base_idx+2*ch]),
        .rvalid(rvalid[cmd_base_idx+2*ch]),
        .rready(rready[cmd_base_idx+2*ch]),
        // Write Response Channel
        .bid(bid[cmd_base_idx+2*ch]),
        .bresp(bresp[cmd_base_idx+2*ch]),
        .bvalid(bvalid[cmd_base_idx+2*ch]),
        .bready(bready[cmd_base_idx+2*ch]),

        ///// Tokens:
        .tok_prod_vld(o_tok_prod_vld[ch]),
        .tok_prod_rdy(i_tok_prod_rdy[ch]),
        .tok_cons_vld(i_tok_cons_vld[ch]),
        .tok_cons_rdy(o_tok_cons_rdy[ch]),

        ///// Timestamp:
        .o_ts_start  (o_ts_start[ch]),
        .o_ts_end    (o_ts_end[ch]),
        ///// ACD sync:
        .o_acd_sync  (o_acd_sync[ch]),

        ///// Command: TODO, now only loop vld to done
        .cmd_done(cmd_vld),
        .cmd_data(),
        .cmd_format(),
        .cmd_config(),
        .cmd_vld(cmd_vld),
        .cmd_rdy(1'b1)
      );

      // TODO: cmdb command to DMA command conversion:
      always_comb dev2reg_wvld[1+ch] = 1'b0;
      always_comb dev2reg_wresp_rdy[1+ch] = 1'b1;
      always_comb dev2reg_wstrb[1+ch] = '0;
      always_comb dev2reg_wdata[1+ch] = '0;
      always_comb dev2reg_waddr[1+ch] = '0;
      always_comb dev2reg_rvld[1+ch] = 1'b0;
      always_comb dev2reg_rresp_rdy[1+ch] = 1'b1;
      always_comb dev2reg_raddr[1+ch] = '0;
      always_comb csr_hw2reg[ch].hw_capability.d = '0;
    end
  end else begin: g_no_bus
    always_comb begin
      awid[legacy_idx] = i_awid;
      awaddr[legacy_idx] = i_awaddr;
      awlen[legacy_idx] = i_awlen;
      awsize[legacy_idx] = i_awsize;
      awburst[legacy_idx] = i_awburst;
      awvalid[legacy_idx] = i_awvalid;
      o_awready = awready[legacy_idx];
      // Read Address Channel
      arid[legacy_idx] = i_arid;
      araddr[legacy_idx] = i_araddr;
      arlen[legacy_idx] = i_arlen;
      arsize[legacy_idx] = i_arsize;
      arburst[legacy_idx] = i_arburst;
      arvalid[legacy_idx] = i_arvalid;
      o_arready = arready[legacy_idx];
      // Write  Data Channel
      wdata[legacy_idx] = i_wdata;
      wstrb[legacy_idx] = i_wstrb;
      wlast[legacy_idx] = i_wlast;
      wvalid[legacy_idx] = i_wvalid;
      o_wready = wready[legacy_idx];
      // Read Data Channel
      o_rid = rid[legacy_idx];
      o_rdata = rdata[legacy_idx];
      o_rresp = rresp[legacy_idx];
      o_rlast = rlast[legacy_idx];
      o_rvalid = rvalid[legacy_idx];
      rready[legacy_idx] = i_rready;
      // Write Response Channel
      o_bid = bid[legacy_idx];
      o_bresp = bresp[legacy_idx];
      o_bvalid = bvalid[legacy_idx];
      bready[legacy_idx] = i_bready;
    end
  end
  /////////////////////////////////////////////
  ///// AXI 2 AHB conversion for legacy
  // AXI2REG
  axi2reg #(
    .IDW(SL_IDW),
    .AW(SL_AW),
    .DW(SL_DW),
    .BW(SL_BW),
    .NR_WR_REQS(2),
    .NR_RD_REQS(2),
    .WBUF(2),
    .RD_RESP_DEPTH(2),
    .WR_RESP_DEPTH(2),
    .OSR(4)
  ) u_axi2reg (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid[legacy_idx]),
    .awaddr(awaddr[legacy_idx]),
    .awlen(awlen[legacy_idx]),
    .awsize(awsize[legacy_idx]),
    .awburst(awburst[legacy_idx]),
    .awvalid(awvalid[legacy_idx]),
    .awready(awready[legacy_idx]),
    // Read Address Channel
    .arid(arid[legacy_idx]),
    .araddr(araddr[legacy_idx]),
    .arlen(arlen[legacy_idx]),
    .arsize(arsize[legacy_idx]),
    .arburst(arburst[legacy_idx]),
    .arvalid(arvalid[legacy_idx]),
    .arready(arready[legacy_idx]),
    // Write  Data Channel
    .wdata(wdata[legacy_idx]),
    .wstrb(wstrb[legacy_idx]),
    .wlast(wlast[legacy_idx]),
    .wvalid(wvalid[legacy_idx]),
    .wready(wready[legacy_idx]),
    // Read Data Channel
    .rid(rid[legacy_idx]),
    .rdata(rdata[legacy_idx]),
    .rresp(rresp[legacy_idx]),
    .rlast(rlast[legacy_idx]),
    .rvalid(rvalid[legacy_idx]),
    .rready(rready[legacy_idx]),
    // Write Response Channel
    .bid(bid[legacy_idx]),
    .bresp(bresp[legacy_idx]),
    .bvalid(bvalid[legacy_idx]),
    .bready(bready[legacy_idx]),

    ////// reg master:
    // Write path:
    .reg_wvld(dev2reg_wvld[legacy_idx]),
    .reg_wrdy(dev2reg_wrdy[legacy_idx]),
    .reg_waddr(dev2reg_waddr[legacy_idx]),
    .reg_wdata(dev2reg_wdata[legacy_idx]),
    .reg_wstrb(dev2reg_wstrb[legacy_idx]),
    .reg_wresp_vld(dev2reg_wresp_vld[legacy_idx]),
    .reg_wresp_rdy(dev2reg_wresp_rdy[legacy_idx]),
    .reg_wresp_error(dev2reg_wresp_error[legacy_idx]),

    // Read path:
    .reg_rvld(dev2reg_rvld[legacy_idx]),
    .reg_rrdy(dev2reg_rrdy[legacy_idx]),
    .reg_raddr(dev2reg_raddr[legacy_idx]),
    .reg_rresp_vld(dev2reg_rresp_vld[legacy_idx]),
    .reg_rresp_rdy(dev2reg_rresp_rdy[legacy_idx]),
    .reg_rresp_error(dev2reg_rresp_error[legacy_idx]),
    .reg_rresp_data(dev2reg_rresp_data[legacy_idx])
  );

  if (NR_REG_DEVS > 1) begin: g_str_bus
    snps_dma_reg_str_bus #(
      .OSR(10), // large enough
      .REQ_DW($bits(reg2ahb_arb_wreq_data)),
      .RESP_DW(1),
      .NR_SUBS(NR_REG_DEVS)
    ) u_dev2reg_wr_bus (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      .i_req_vld(dev2reg_wvld),
      .o_req_rdy(dev2reg_wrdy),
      .i_req_data(dev2reg_arb_wreq_data),
      .o_resp_vld(dev2reg_wresp_vld),
      .i_resp_rdy(dev2reg_wresp_rdy),
      .o_resp_data(dev2reg_wresp_error),

      .o_req_vld(reg2ahb_wvld),
      .i_req_rdy(reg2ahb_wrdy),
      .o_req_data(reg2ahb_arb_wreq_data),
      .i_resp_vld(reg2ahb_wresp_vld),
      .o_resp_rdy(reg2ahb_wresp_rdy),
      .i_resp_data(reg2ahb_wresp_error)
    );

    snps_dma_reg_str_bus #(
      .OSR(10), // large enough
      .REQ_DW($bits(reg2ahb_raddr)),
      .RESP_DW($bits(reg2ahb_arb_rresp_data)),
      .NR_SUBS(NR_REG_DEVS)
    ) u_dev2reg_rd_bus (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      .i_req_vld(dev2reg_rvld),
      .o_req_rdy(dev2reg_rrdy),
      .i_req_data(dev2reg_raddr),
      .o_resp_vld(dev2reg_rresp_vld),
      .i_resp_rdy(dev2reg_rresp_rdy),
      .o_resp_data(dev2reg_arb_rresp_data),

      .o_req_vld(reg2ahb_rvld),
      .i_req_rdy(reg2ahb_rrdy),
      .o_req_data(reg2ahb_raddr),
      .i_resp_vld(reg2ahb_rresp_vld),
      .o_resp_rdy(reg2ahb_rresp_rdy),
      .i_resp_data(reg2ahb_arb_rresp_data)
    );
  end else begin: g_no_str_bus
    always_comb begin
      // req
      reg2ahb_wvld             = dev2reg_wvld[legacy_idx];
      reg2ahb_arb_wreq_data    = dev2reg_arb_wreq_data[legacy_idx];
      dev2reg_wrdy[legacy_idx] = reg2ahb_wrdy;
      reg2ahb_rvld             = dev2reg_rvld[legacy_idx];
      reg2ahb_raddr            = dev2reg_raddr[legacy_idx];
      dev2reg_rrdy[legacy_idx] = reg2ahb_rrdy;
      // resp
      dev2reg_wresp_vld[legacy_idx]       = reg2ahb_wresp_vld;
      dev2reg_wresp_error[legacy_idx]     = reg2ahb_wresp_error;
      reg2ahb_wresp_rdy                   = dev2reg_wresp_rdy;
      dev2reg_rresp_vld[legacy_idx]       = reg2ahb_rresp_vld;
      dev2reg_arb_rresp_data[legacy_idx]  = reg2ahb_arb_rresp_data;
      reg2ahb_rresp_rdy                   = dev2reg_rresp_rdy;
    end
  end
  always_comb {reg2ahb_waddr, reg2ahb_wdata, reg2ahb_wstrb} = reg2ahb_arb_wreq_data;
  always_comb reg2ahb_arb_rresp_data = {reg2ahb_rresp_error, reg2ahb_rresp_data};

  for (genvar dev = 0; dev < NR_REG_DEVS; dev++) begin: g_sig_combine
    always_comb dev2reg_arb_wreq_data[dev] = {dev2reg_waddr[dev], dev2reg_wdata[dev], dev2reg_wstrb[dev]};
    always_comb {dev2reg_rresp_error[dev], dev2reg_rresp_data[dev]} = dev2reg_arb_rresp_data[dev];
  end

  // REG2AHB
  snps_dma_reg2ahb #(
    .AW(SL_AW),
    .DW(SL_DW)
  ) u_reg2ahb (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    ////// reg interface:
    // Write path:
    .i_reg_wvld(reg2ahb_wvld),
    .o_reg_wrdy(reg2ahb_wrdy),
    .i_reg_waddr(reg2ahb_waddr),
    .i_reg_wdata(reg2ahb_wdata),
    .i_reg_wstrb(reg2ahb_wstrb),
    .o_reg_wresp_vld(reg2ahb_wresp_vld),
    .i_reg_wresp_rdy(reg2ahb_wresp_rdy),
    .o_reg_wresp_error(reg2ahb_wresp_error),

    // Read path:
    .i_reg_rvld(reg2ahb_rvld),
    .o_reg_rrdy(reg2ahb_rrdy),
    .i_reg_raddr(reg2ahb_raddr),
    .o_reg_rresp_vld(reg2ahb_rresp_vld),
    .i_reg_rresp_rdy(reg2ahb_rresp_rdy),
    .o_reg_rresp_error(reg2ahb_rresp_error),
    .o_reg_rresp_data(reg2ahb_rresp_data),

    ////// AHB master
    // AHB slave
    .o_hsel(o_hsel),
    .o_haddr(o_haddr),
    .o_hsize(o_hsize),
    .o_htrans(o_htrans),
    .o_hready(o_hready),
    .o_hwrite(o_hwrite),
    .o_hwdata(o_hwdata),
    .i_hrdata(i_hrdata),
    .i_hresp(i_hresp),
    .i_hready_resp(i_hready_resp)
  );
  /////////////////////////////////////////////

endmodule
