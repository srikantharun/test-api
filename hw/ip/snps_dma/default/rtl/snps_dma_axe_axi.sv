// Description: Wrapper around snps_dma to handle axelera AXI fabric

module snps_dma_axe_axi
  import snps_dma_pkg::*;
#(
  parameter DMA_VERSION = "aic_lt",

  parameter int unsigned AXI_S_ADDR_W = 40,
  parameter int unsigned AXI_S_DATA_W = 64,
  parameter int unsigned AXI_S_ID_W = 4,
  parameter int unsigned AXI_S_LEN_W = 8,

  // AXI channels for sub port
  parameter type axi_s_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type axi_s_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type axi_s_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type axi_s_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type axi_s_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t,

  // AXI channels for manager port(s)
  parameter type axi_m_aw_t = axe_axi_default_types_pkg::axi_aw_5_40_4_t,
  parameter type axi_m_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type axi_m_b_t  = axe_axi_default_types_pkg::axi_b_5_4_t,
  parameter type axi_m_ar_t = axe_axi_default_types_pkg::axi_ar_5_40_4_t,
  parameter type axi_m_r_t  = axe_axi_default_types_pkg::axi_r_5_64_4_t,

  parameter SRAM_IMPL_KEY = "HS_RVT",

  localparam snps_dma_cfg_t CFG =
    (DMA_VERSION == "aic_lt") ? SNPS_DMA_AIC_LT_CFG :
    (DMA_VERSION == "aic_ht") ? SNPS_DMA_AIC_HT_CFG :
    (DMA_VERSION == "apu")    ? SNPS_DMA_APU_CFG : SNPS_DMA_APU_CFG,

  localparam int unsigned MT_DW = CFG.axi_port_dw,
  localparam int unsigned MT_AW = CFG.axi_port_aw,

  localparam int unsigned MT_IDW = CFG.axi_port_idw,
  localparam int unsigned MT_BLW = CFG.axi_port_len,

  localparam int unsigned NR_CH = CFG.dma_nbr_channels,
  localparam int unsigned NR_MT = CFG.dma_nbr_ports,

  // debug signals:
  localparam int unsigned LOG2_ARB_RD_REQ_W = $clog2(NR_CH)+2,
  localparam int unsigned LOG2_ARB_WR_REQ_W = $clog2(NR_CH)+2,
  localparam int unsigned DBG_W = NR_MT*LOG2_ARB_RD_REQ_W + NR_MT*LOG2_ARB_WR_REQ_W + ((NR_MT * 3) + 1) * NR_CH + 12
) (
  input wire  i_clk,
  input wire  i_rst_n,
  input logic i_test_mode,

  // Subordinate Port
  input  axi_s_aw_t i_axi_s_aw,
  input  logic      i_axi_s_aw_valid,
  output logic      o_axi_s_aw_ready,
  input  axi_s_w_t  i_axi_s_w,
  input  logic      i_axi_s_w_valid,
  output logic      o_axi_s_w_ready,
  output axi_s_b_t  o_axi_s_b,
  output logic      o_axi_s_b_valid,
  input  logic      i_axi_s_b_ready,
  input  axi_s_ar_t i_axi_s_ar,
  input  logic      i_axi_s_ar_valid,
  output logic      o_axi_s_ar_ready,
  output axi_s_r_t  o_axi_s_r,
  output logic      o_axi_s_r_valid,
  input  logic      i_axi_s_r_ready,

  // Manager Port(s)
  output axi_m_aw_t o_axi_m_aw[NR_MT],
  output logic      o_axi_m_aw_valid[NR_MT],
  input  logic      i_axi_m_aw_ready[NR_MT],
  output axi_m_w_t  o_axi_m_w[NR_MT],
  output logic      o_axi_m_w_valid[NR_MT],
  input  logic      i_axi_m_w_ready[NR_MT],
  input  axi_m_b_t  i_axi_m_b[NR_MT],
  input  logic      i_axi_m_b_valid[NR_MT],
  output logic      o_axi_m_b_ready[NR_MT],
  output axi_m_ar_t o_axi_m_ar[NR_MT],
  output logic      o_axi_m_ar_valid[NR_MT],
  input  logic      i_axi_m_ar_ready[NR_MT],
  input  axi_m_r_t  i_axi_m_r[NR_MT],
  input  logic      i_axi_m_r_valid[NR_MT],
  output logic      o_axi_m_r_ready[NR_MT],

  // Interrupts
  output logic [NR_CH-1: 0] o_irq_ch,
  output logic              o_irq_cmn,

   // SRAM config registers
  input  axe_tcl_sram_pkg::impl_inp_t i_impl_inp,
  output axe_tcl_sram_pkg::impl_oup_t o_impl_oup,

  // Debug signals
  input  logic [cc_math_pkg::index_width(NR_CH)-1:0] i_debug_ch_num,
  output logic [DBG_W-1: 0]                          o_dma_debug
);

  // Write Address Channel
  logic [NR_MT-1:0][MT_IDW-1: 0] o_axi_m_awid;
  logic [NR_MT-1:0][MT_AW-1: 0]  o_axi_m_awaddr;
  logic [NR_MT-1:0][MT_BLW-1: 0] o_axi_m_awlen;
  logic [NR_MT-1:0][2:0]         o_axi_m_awsize;
  logic [NR_MT-1:0][1:0]         o_axi_m_awburst;
  logic [NR_MT-1:0]              o_axi_m_awlock;
  logic [NR_MT-1:0][3:0]         o_axi_m_awcache;
  logic [NR_MT-1:0][2:0]         o_axi_m_awprot;
  logic [NR_MT-1:0]              o_axi_m_awvalid;
  logic [NR_MT-1:0]              i_axi_m_awready;
  always_comb begin
    foreach(i_axi_m_awready[i]) begin
      o_axi_m_aw[i].id    = o_axi_m_awid[i];
      o_axi_m_aw[i].addr  = o_axi_m_awaddr[i];
      o_axi_m_aw[i].len   = o_axi_m_awlen[i];
      o_axi_m_aw[i].size  = axi_pkg::axi_size_e'(o_axi_m_awsize[i]);
      o_axi_m_aw[i].burst = axi_pkg::axi_burst_e'(o_axi_m_awburst[i]);
      o_axi_m_aw[i].lock  = o_axi_m_awlock[i];
      o_axi_m_aw[i].cache = o_axi_m_awcache[i];
      o_axi_m_aw[i].prot  = o_axi_m_awprot[i];
      o_axi_m_aw_valid[i] = o_axi_m_awvalid[i];
      i_axi_m_awready[i]  = i_axi_m_aw_ready[i];

      o_axi_m_aw[i].atop   = 'b0;
      o_axi_m_aw[i].qos    = 'b0;
      o_axi_m_aw[i].region = 'b0;
      o_axi_m_aw[i].user   = 'b0;
    end
  end
  // Read Address Channel
  logic [NR_MT-1:0][MT_IDW-1: 0] o_axi_m_arid;
  logic [NR_MT-1:0][MT_AW-1: 0]  o_axi_m_araddr;
  logic [NR_MT-1:0][MT_BLW-1: 0] o_axi_m_arlen;
  logic [NR_MT-1:0][2:0]         o_axi_m_arsize;
  logic [NR_MT-1:0][1:0]         o_axi_m_arburst;
  logic [NR_MT-1:0]              o_axi_m_arlock;
  logic [NR_MT-1:0][3:0]         o_axi_m_arcache;
  logic [NR_MT-1:0][2:0]         o_axi_m_arprot;
  logic [NR_MT-1:0]              o_axi_m_arvalid;
  logic [NR_MT-1:0]              i_axi_m_arready;
  always_comb begin
    foreach(i_axi_m_arready[i]) begin
      o_axi_m_ar[i].id    = o_axi_m_arid[i];
      o_axi_m_ar[i].addr  = o_axi_m_araddr[i];
      o_axi_m_ar[i].len   = o_axi_m_arlen[i];
      o_axi_m_ar[i].size  = axi_pkg::axi_size_e'(o_axi_m_arsize[i]);
      o_axi_m_ar[i].burst = axi_pkg::axi_burst_e'(o_axi_m_arburst[i]);
      o_axi_m_ar[i].lock  = o_axi_m_arlock[i];
      o_axi_m_ar[i].cache = o_axi_m_arcache[i];
      o_axi_m_ar[i].prot  = o_axi_m_arprot[i];
      o_axi_m_ar_valid[i] = o_axi_m_arvalid[i];
      i_axi_m_arready[i]  = i_axi_m_ar_ready[i];

      o_axi_m_ar[i].qos    = 'b0;
      o_axi_m_ar[i].region = 'b0;
      o_axi_m_ar[i].user   = 'b0;
    end
  end
  // Write  Data Channel
  logic [NR_MT-1:0][MT_DW-1: 0]   o_axi_m_wdata;
  logic [NR_MT-1:0][MT_DW/8-1: 0] o_axi_m_wstrb;
  logic [NR_MT-1:0]               o_axi_m_wlast;
  logic [NR_MT-1:0]               o_axi_m_wvalid;
  logic [NR_MT-1:0]               i_axi_m_wready;
  always_comb begin
    foreach(i_axi_m_wready[i]) begin
      o_axi_m_w[i].data  = o_axi_m_wdata[i];
      o_axi_m_w[i].strb  = o_axi_m_wstrb[i];
      o_axi_m_w[i].last  = o_axi_m_wlast[i];
      o_axi_m_w_valid[i] = o_axi_m_wvalid[i];
      i_axi_m_wready[i]  = i_axi_m_w_ready[i];

      o_axi_m_w[i].user = 'b0;
    end
  end
  // Read Data Channel
  logic [NR_MT-1:0][MT_IDW-1: 0] i_axi_m_rid;
  logic [NR_MT-1:0][MT_DW-1: 0]  i_axi_m_rdata;
  logic [NR_MT-1:0][1:0]         i_axi_m_rresp;
  logic [NR_MT-1:0]              i_axi_m_rlast;
  logic [NR_MT-1:0]              i_axi_m_rvalid;
  logic [NR_MT-1:0]              o_axi_m_rready;
  always_comb begin
    foreach(o_axi_m_rready[i]) begin
      i_axi_m_rid        = i_axi_m_r[i].id;
      i_axi_m_rdata      = i_axi_m_r[i].data;
      i_axi_m_rresp      = i_axi_m_r[i].resp;
      i_axi_m_rlast      = i_axi_m_r[i].last;
      i_axi_m_rvalid[i]  = i_axi_m_r_valid[i];
      o_axi_m_r_ready[i] = o_axi_m_rready[i];
    end
  end
  // Write Response Channel
  logic [NR_MT-1:0][MT_IDW-1: 0] i_axi_m_bid;
  logic [NR_MT-1:0][1:0]         i_axi_m_bresp;
  logic [NR_MT-1:0]              i_axi_m_bvalid;
  logic [NR_MT-1:0]              o_axi_m_bready;
  always_comb begin
    foreach(o_axi_m_bready[i]) begin
      i_axi_m_bid        = i_axi_m_b[i].id;
      i_axi_m_bresp      = i_axi_m_b[i].resp;
      i_axi_m_bvalid[i]  = i_axi_m_b_valid[i];
      o_axi_m_b_ready[i] = o_axi_m_bready[i];
    end
  end

  snps_dma #(
    .DMA_VERSION(DMA_VERSION),
    .SRAM_IMPL_KEY(SRAM_IMPL_KEY),
    .SL_AW(AXI_S_ADDR_W),
    .SL_DW(AXI_S_DATA_W),
    .SL_IDW(AXI_S_ID_W),
    .SL_BW(AXI_S_LEN_W)
  ) u_snps_dma (
    ///// AXI subordinate:
    // Write Address Channel
    .i_awid(i_axi_s_aw.id),
    .i_awaddr(i_axi_s_aw.addr),
    .i_awlen(i_axi_s_aw.len),
    .i_awsize(i_axi_s_aw.size),
    .i_awburst(i_axi_s_aw.burst),
    .i_awvalid(i_axi_s_aw_valid),
    .o_awready(o_axi_s_aw_ready),
    // Read Address Channel
    .i_arid(i_axi_s_ar.id),
    .i_araddr(i_axi_s_ar.addr),
    .i_arlen(i_axi_s_ar.len),
    .i_arsize(i_axi_s_ar.size),
    .i_arburst(i_axi_s_ar.burst),
    .i_arvalid(i_axi_s_ar_valid),
    .o_arready(o_axi_s_ar_ready),
    // Write  Data Channel
    .i_wdata(i_axi_s_w.data),
    .i_wstrb(i_axi_s_w.strb),
    .i_wlast(i_axi_s_w.last),
    .i_wvalid(i_axi_s_w_valid),
    .o_wready(o_axi_s_w_ready),
    // Read Data Channel
    .o_rid(o_axi_s_r.id),
    .o_rdata(o_axi_s_r.data),
    .o_rresp(o_axi_s_r.resp[axi_pkg::AXI_RESP_WIDTH-1:0]),
    .o_rlast(o_axi_s_r.last),
    .o_rvalid(o_axi_s_r_valid),
    .i_rready(i_axi_s_r_ready),
    // Write Response Channel
    .o_bid(o_axi_s_b.id),
    .o_bresp(o_axi_s_b.resp[axi_pkg::AXI_RESP_WIDTH-1:0]),
    .o_bvalid(o_axi_s_b_valid),
    .i_bready(i_axi_s_b_ready),

    ///// Tokens:
    .o_tok_prod_vld(),
    .i_tok_prod_rdy('1),
    .i_tok_cons_vld('0),
    .o_tok_cons_rdy(),

    ///// Timestamp:
    .o_ts_start(),
    .o_ts_end(),
    ///// ACD sync:
    .o_acd_sync(),

    .*
  );

endmodule
