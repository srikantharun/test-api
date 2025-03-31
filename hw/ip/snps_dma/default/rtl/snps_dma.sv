// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA wrapper, including dma, optional memories and other simple logic
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module snps_dma
  import snps_dma_pkg::*;
#(
    parameter DMA_VERSION = "aic_lt",
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

    parameter int unsigned NR_TOK_PROD = 1,
    parameter int unsigned NR_TOK_CONS = 1,

    parameter int unsigned NR_TOP_TOK_PROD = 1,
    parameter int unsigned NR_TOP_TOK_CONS = 1,

    localparam snps_dma_cfg_t CFG =
      (DMA_VERSION == "aic_lt") ? SNPS_DMA_AIC_LT_CFG :
      (DMA_VERSION == "aic_ht") ? SNPS_DMA_AIC_HT_CFG :
      (DMA_VERSION == "apu")    ? SNPS_DMA_APU_CFG : SNPS_DMA_APU_CFG,

    localparam int unsigned MT_DW = CFG.axi_port_dw,
    localparam int unsigned MT_AW = CFG.axi_port_aw,

    localparam int unsigned MT_IDW = CFG.axi_port_idw,
    localparam int unsigned MT_BLW = CFG.axi_port_len,

    parameter int unsigned MACRO_WIDTH = CFG.dma_macro_width,
    parameter SRAM_IMPL_KEY = "HS_RVT",

    localparam int unsigned NR_CH = CFG.dma_nbr_channels,
    localparam int unsigned NR_MT = CFG.dma_nbr_ports,

    localparam bit EXT_RAM = CFG.dma_external_ram,
    localparam int unsigned CH_FIFO_DEPTH = CFG.dma_channel_fifo_depth,

    // debug signals:
    localparam int unsigned LOG2_ARB_RD_REQ_W = $clog2(NR_CH)+2,
    localparam int unsigned LOG2_ARB_WR_REQ_W = $clog2(NR_CH)+2,
    localparam int unsigned DBG_W = NR_MT*LOG2_ARB_RD_REQ_W + NR_MT*LOG2_ARB_WR_REQ_W + ((NR_MT * 3) + 1) * NR_CH + 12
) (
    input   wire  i_clk,
    input   wire  i_rst_n,
    input   logic i_test_mode,

    ///// AXI subordinate:
    // Write Address Channel
    input  logic [ SL_IDW-1:0] i_awid,
    input  logic [  SL_AW-1:0] i_awaddr,
    input  logic [  SL_BW-1:0] i_awlen,
    input  logic [     2:0] i_awsize,
    input  logic [     1:0] i_awburst,
    input  logic            i_awvalid,
    output logic            o_awready,
    // Read Address Channel
    input  logic [ SL_IDW-1:0] i_arid,
    input  logic [  SL_AW-1:0] i_araddr,
    input  logic [  SL_BW-1:0] i_arlen,
    input  logic [     2:0] i_arsize,
    input  logic [     1:0] i_arburst,
    input  logic            i_arvalid,
    output logic            o_arready,
    // Write  Data Channel
    input  logic [  SL_DW-1:0] i_wdata,
    input  logic [SL_DW/8-1:0] i_wstrb,
    input  logic            i_wlast,
    input  logic            i_wvalid,
    output logic            o_wready,
    // Read Data Channel
    output logic [ SL_IDW-1:0] o_rid,
    output logic [  SL_DW-1:0] o_rdata,
    output logic [     1:0] o_rresp,
    output logic            o_rlast,
    output logic            o_rvalid,
    input  logic            i_rready,
    // Write Response Channel
    output logic [ SL_IDW-1:0] o_bid,
    output logic [     1:0] o_bresp,
    output logic            o_bvalid,
    input  logic            i_bready,

    ///// AXI managers:
    // Write Address Channel
    output  logic [NR_MT-1:0][MT_IDW-1: 0]         o_axi_m_awid,
    output  logic [NR_MT-1:0][MT_AW-1: 0]          o_axi_m_awaddr,
    output  logic [NR_MT-1:0][MT_BLW-1: 0]         o_axi_m_awlen,
    output  logic [NR_MT-1:0][2:0]                 o_axi_m_awsize,
    output  logic [NR_MT-1:0][1:0]                 o_axi_m_awburst,
    output  logic [NR_MT-1:0]                      o_axi_m_awlock,
    output  logic [NR_MT-1:0][3:0]                 o_axi_m_awcache,
    output  logic [NR_MT-1:0][2:0]                 o_axi_m_awprot,
    output  logic [NR_MT-1:0]                      o_axi_m_awvalid,
    input   logic [NR_MT-1:0]                      i_axi_m_awready,
    // Read Address Channel
    output  logic [NR_MT-1:0][MT_IDW-1: 0]         o_axi_m_arid,
    output  logic [NR_MT-1:0][MT_AW-1: 0]          o_axi_m_araddr,
    output  logic [NR_MT-1:0][MT_BLW-1: 0]         o_axi_m_arlen,
    output  logic [NR_MT-1:0][2:0]                 o_axi_m_arsize,
    output  logic [NR_MT-1:0][1:0]                 o_axi_m_arburst,
    output  logic [NR_MT-1:0]                      o_axi_m_arlock,
    output  logic [NR_MT-1:0][3:0]                 o_axi_m_arcache,
    output  logic [NR_MT-1:0][2:0]                 o_axi_m_arprot,
    output  logic [NR_MT-1:0]                      o_axi_m_arvalid,
    input   logic [NR_MT-1:0]                      i_axi_m_arready,
    // Write  Data Channel
    output  logic [NR_MT-1:0][MT_DW-1: 0]          o_axi_m_wdata,
    output  logic [NR_MT-1:0][MT_DW/8-1: 0]        o_axi_m_wstrb,
    output  logic [NR_MT-1:0]                      o_axi_m_wlast,
    output  logic [NR_MT-1:0]                      o_axi_m_wvalid,
    input   logic [NR_MT-1:0]                      i_axi_m_wready,
    // Read Data Channel
    input   logic [NR_MT-1:0][MT_IDW-1: 0]         i_axi_m_rid,
    input   logic [NR_MT-1:0][MT_DW-1: 0]          i_axi_m_rdata,
    input   logic [NR_MT-1:0][1:0]                 i_axi_m_rresp,
    input   logic [NR_MT-1:0]                      i_axi_m_rlast,
    input   logic [NR_MT-1:0]                      i_axi_m_rvalid,
    output  logic [NR_MT-1:0]                      o_axi_m_rready,
    // Write Response Channel
    input   logic [NR_MT-1:0][MT_IDW-1: 0]         i_axi_m_bid,
    input   logic [NR_MT-1:0][1:0]                 i_axi_m_bresp,
    input   logic [NR_MT-1:0]                      i_axi_m_bvalid,
    output  logic [NR_MT-1:0]                      o_axi_m_bready,

    // Interrupts
    output  logic [NR_CH-1: 0]                     o_irq_ch,
    output  logic                                  o_irq_cmn,

    ///// Tokens:
    output logic [NR_CH-1:0][NR_TOK_PROD+NR_TOP_TOK_PROD-1:0]      o_tok_prod_vld,
    input  logic [NR_CH-1:0][NR_TOK_PROD+NR_TOP_TOK_PROD-1:0]      i_tok_prod_rdy,
    input  logic [NR_CH-1:0][NR_TOK_CONS+NR_TOP_TOK_CONS-1:0]      i_tok_cons_vld,
    output logic [NR_CH-1:0][NR_TOK_CONS+NR_TOP_TOK_CONS-1:0]      o_tok_cons_rdy,

    ///// Timestamp:
    output logic [NR_CH-1:0] o_ts_start,
    output logic [NR_CH-1:0] o_ts_end,
    ///// ACD sync:
    output logic [NR_CH-1:0] o_acd_sync,

     // SRAM config registers
    input  axe_tcl_sram_pkg::impl_inp_t i_impl_inp,
    output axe_tcl_sram_pkg::impl_oup_t o_impl_oup,

    // Debug signals
    input logic [cc_math_pkg::index_width(NR_CH)-1:0] i_debug_ch_num,
    output logic [DBG_W-1: 0]                         o_dma_debug

);

    localparam int unsigned ECC_DW = 0; // no support for ECC (yet)

    /////////////////////////////////////////////
    // AHB:
    logic                 hsel;
    logic  [31:0]         haddr;
    logic  [2:0]          hsize;
    logic  [1:0]          htrans;
    logic                 hready;
    logic                 hwrite;
    logic  [SL_DW-1: 0]   hwdata;
    logic  [SL_DW-1:0]    hrdata;
    logic  [1:0]          hresp;
    logic                 hready_resp;
    /////////////////////////////////////////////

    logic                    dmac_core_clock;
    logic                    dmac_core_resetn;
    logic                    scan_mode;

    logic [NR_CH-1: 0]        intr_ch;
    logic                     intr_cmnreg;
    logic [cc_math_pkg::index_width(NR_CH)-1:0] debug_ch_num_i;

    always_comb o_irq_ch = intr_ch;
    always_comb o_irq_cmn = intr_cmnreg;
    always_comb debug_ch_num_i = i_debug_ch_num;

    // Low Power Interface
    logic                    dmac_lp_req;
    logic [NR_CH:1]          ch_lp_req;
    logic                    sbiu_lp_req;
    logic [NR_MT-1:0]        mxif_arch_lp_req;
    logic [NR_MT-1:0]        mxif_arch_oclk_lp_req;
    logic [NR_MT-1:0]        mxif_awch_lp_req;
    logic [NR_MT-1:0]        mxif_awch_oclk_lp_req;
    logic [NR_MT-1:0]        mxif_wch_lp_req;
    logic [NR_MT-1:0]        mxif_wch_oclk_lp_req;
    logic [NR_MT-1:0]        mxif_bch_lp_req;
    logic [NR_MT-1:0]        mxif_bch_oclk_lp_req;
    logic [NR_MT-1:0]        mxif_rch_lp_req;
    logic [NR_MT-1:0]        mxif_rch_oclk_lp_req;
    logic [NR_MT-1:0]        mxif_r_ch_idle;
    logic [NR_MT-1:0]        mxif_b_ch_idle;

    // Debug signals:
    logic [LOG2_ARB_RD_REQ_W-1:0] debug_grant_index_ar_ch_m1;
    logic [LOG2_ARB_WR_REQ_W-1:0] debug_grant_index_aw_ch_m1;
    logic [NR_CH-1:0]             debug_ch_wr_arb_req_m1;
    logic [NR_CH-1:0]             debug_ch_rd_arb_req_m1;
    logic [NR_CH-1:0]             debug_ch_lli_rd_req_m1;
    logic [LOG2_ARB_RD_REQ_W-1:0] debug_grant_index_ar_ch_m2;
    logic [LOG2_ARB_WR_REQ_W-1:0] debug_grant_index_aw_ch_m2;
    logic [NR_CH-1:0]             debug_ch_wr_arb_req_m2;
    logic [NR_CH-1:0]             debug_ch_rd_arb_req_m2;
    logic [NR_CH-1:0]             debug_ch_lli_rd_req_m2;
    logic                         debug_ch_src_blk_tfr_done;
    logic                         debug_ch_dst_blk_tfr_done;
    logic                         debug_ch_blk_tfr_done;
    logic                         debug_ch_src_trans_done;
    logic                         debug_ch_dst_trans_done;
    logic                         debug_ch_dma_tfr_done;
    logic                         debug_ch_src_trans_req;
    logic                         debug_ch_dst_trans_req;
    logic                         debug_ch_src_is_in_str;
    logic                         debug_ch_dst_is_in_str;
    logic                         debug_ch_shadowreg_or_lli_invalid_err;
    logic                         debug_ch_suspended;
    logic [NR_CH-1:0]             debug_ch_en;

    // channel FIFO dma port:
    logic                             dmac_ch1_fifomem_clk;
    logic                             dmac_ch1_fifomem_wcen;
    logic                             dmac_ch1_fifomem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch1_fifomem_waddr;
    logic [MT_DW-1:0]                 dmac_ch1_fifomem_wdata;
    logic                             dmac_ch1_fifomem_rcen;
    logic                             dmac_ch1_fifomem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch1_fifomem_raddr;
    logic [MT_DW-1:0]                 dmac_ch1_fifomem_rdata;
    logic                             dmac_ch2_fifomem_clk;
    logic                             dmac_ch2_fifomem_wcen;
    logic                             dmac_ch2_fifomem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch2_fifomem_waddr;
    logic [MT_DW-1:0]                 dmac_ch2_fifomem_wdata;
    logic                             dmac_ch2_fifomem_rcen;
    logic                             dmac_ch2_fifomem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch2_fifomem_raddr;
    logic [MT_DW-1:0]                 dmac_ch2_fifomem_rdata;
    logic                             dmac_ch3_fifomem_clk;
    logic                             dmac_ch3_fifomem_wcen;
    logic                             dmac_ch3_fifomem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch3_fifomem_waddr;
    logic [MT_DW-1:0]                 dmac_ch3_fifomem_wdata;
    logic                             dmac_ch3_fifomem_rcen;
    logic                             dmac_ch3_fifomem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch3_fifomem_raddr;
    logic [MT_DW-1:0]                 dmac_ch3_fifomem_rdata;
    logic                             dmac_ch4_fifomem_clk;
    logic                             dmac_ch4_fifomem_wcen;
    logic                             dmac_ch4_fifomem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch4_fifomem_waddr;
    logic [MT_DW-1:0]                 dmac_ch4_fifomem_wdata;
    logic                             dmac_ch4_fifomem_rcen;
    logic                             dmac_ch4_fifomem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch4_fifomem_raddr;
    logic [MT_DW-1:0]                 dmac_ch4_fifomem_rdata;

    // UID channel FIFO dma port:
    logic                             dmac_ch1_uidmem_clk;
    logic                             dmac_ch1_uidmem_wcen;
    logic                             dmac_ch1_uidmem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch1_uidmem_waddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch1_uidmem_wdata;
    logic                             dmac_ch1_uidmem_rcen;
    logic                             dmac_ch1_uidmem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch1_uidmem_raddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch1_uidmem_rdata;
    logic                             dmac_ch2_uidmem_clk;
    logic                             dmac_ch2_uidmem_wcen;
    logic                             dmac_ch2_uidmem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch2_uidmem_waddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch2_uidmem_wdata;
    logic                             dmac_ch2_uidmem_rcen;
    logic                             dmac_ch2_uidmem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch2_uidmem_raddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch2_uidmem_rdata;
    logic                             dmac_ch3_uidmem_clk;
    logic                             dmac_ch3_uidmem_wcen;
    logic                             dmac_ch3_uidmem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch3_uidmem_waddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch3_uidmem_wdata;
    logic                             dmac_ch3_uidmem_rcen;
    logic                             dmac_ch3_uidmem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch3_uidmem_raddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch3_uidmem_rdata;
    logic                             dmac_ch4_uidmem_clk;
    logic                             dmac_ch4_uidmem_wcen;
    logic                             dmac_ch4_uidmem_wen;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch4_uidmem_waddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch4_uidmem_wdata;
    logic                             dmac_ch4_uidmem_rcen;
    logic                             dmac_ch4_uidmem_ren;
    logic [$clog2(CH_FIFO_DEPTH)-1:0] dmac_ch4_uidmem_raddr;
    logic [MT_DW+ECC_DW-1:0]          dmac_ch4_uidmem_rdata;

    // Master port wires:
       ///// Master 1:
    // Write Address Channel
    logic [MT_IDW-1: 0]     awid_m1;
    logic [MT_AW-1: 0]      awaddr_m1;
    logic [MT_BLW-1: 0]     awlen_m1;
    logic [2:0]             awsize_m1;
    logic [1:0]             awburst_m1;
    logic                   awlock_m1;
    logic [3:0]             awcache_m1;
    logic [2:0]             awprot_m1;
    logic                   awvalid_m1;
    logic                   awready_m1;
    // Read Address Channel
    logic [MT_IDW-1: 0]     arid_m1;
    logic [MT_AW-1: 0]      araddr_m1;
    logic [MT_BLW-1: 0]     arlen_m1;
    logic [2:0]             arsize_m1;
    logic [1:0]             arburst_m1;
    logic                   arlock_m1;
    logic [3:0]             arcache_m1;
    logic [2:0]             arprot_m1;
    logic                   arvalid_m1;
    logic                   arready_m1;
    // Write  Data Channel
    logic [MT_DW-1: 0]      wdata_m1;
    logic [MT_DW/8-1: 0]    wstrb_m1;
    logic                   wlast_m1;
    logic                   wvalid_m1;
    logic                   wready_m1;
    // Read Data Channel
    logic [MT_IDW-1: 0]     rid_m1;
    logic [MT_DW-1: 0]      rdata_m1;
    logic [1:0]             rresp_m1;
    logic                   rlast_m1;
    logic                   rvalid_m1;
    logic                   rready_m1;
    // Write Response Channel
    logic [MT_IDW-1: 0]     bid_m1;
    logic [1:0]             bresp_m1;
    logic                   bvalid_m1;
    logic                   bready_m1;
       ///// Master 2:
    // Write Address Channel
    logic [MT_IDW-1: 0]     awid_m2;
    logic [MT_AW-1: 0]      awaddr_m2;
    logic [MT_BLW-1: 0]     awlen_m2;
    logic [2:0]             awsize_m2;
    logic [1:0]             awburst_m2;
    logic                   awlock_m2;
    logic [3:0]             awcache_m2;
    logic [2:0]             awprot_m2;
    logic                   awvalid_m2;
    logic                   awready_m2;
    // Read Address Channel
    logic [MT_IDW-1: 0]     arid_m2;
    logic [MT_AW-1: 0]      araddr_m2;
    logic [MT_BLW-1: 0]     arlen_m2;
    logic [2:0]             arsize_m2;
    logic [1:0]             arburst_m2;
    logic                   arlock_m2;
    logic [3:0]             arcache_m2;
    logic [2:0]             arprot_m2;
    logic                   arvalid_m2;
    logic                   arready_m2;
    // Write  Data Channel
    logic [MT_DW-1: 0]      wdata_m2;
    logic [MT_DW/8-1: 0]    wstrb_m2;
    logic                   wlast_m2;
    logic                   wvalid_m2;
    logic                   wready_m2;
    // Read Data Channel
    logic [MT_IDW-1: 0]     rid_m2;
    logic [MT_DW-1: 0]      rdata_m2;
    logic [1:0]             rresp_m2;
    logic                   rlast_m2;
    logic                   rvalid_m2;
    logic                   rready_m2;
    // Write Response Channel
    logic [MT_IDW-1: 0]     bid_m2;
    logic [1:0]             bresp_m2;
    logic                   bvalid_m2;
    logic                   bready_m2;


    // channel FIFO memory connections:
    logic [NR_CH:1]                              ch_fifomem_clk;
    logic [NR_CH:1]                              ch_fifomem_wcen;
    logic [NR_CH:1]                              ch_fifomem_wen;
    logic [NR_CH:1] [$clog2(CH_FIFO_DEPTH)-1:0]  ch_fifomem_waddr;
    logic [NR_CH:1] [MT_DW-1:0]                  ch_fifomem_wdata;
    logic [NR_CH:1]                              ch_fifomem_rcen;
    logic [NR_CH:1]                              ch_fifomem_ren;
    logic [NR_CH:1] [$clog2(CH_FIFO_DEPTH)-1:0]  ch_fifomem_raddr;
    logic [NR_CH:1] [MT_DW-1:0]                  ch_fifomem_rdata;
    logic [NR_CH:1]                              ch_uidmem_clk;
    logic [NR_CH:1]                              ch_uidmem_wcen;
    logic [NR_CH:1]                              ch_uidmem_wen;
    logic [NR_CH:1] [$clog2(CH_FIFO_DEPTH)-1:0]  ch_uidmem_waddr;
    logic [NR_CH:1] [MT_DW+ECC_DW-1:0]           ch_uidmem_wdata;
    logic [NR_CH:1]                              ch_uidmem_rcen;
    logic [NR_CH:1]                              ch_uidmem_ren;
    logic [NR_CH:1] [$clog2(CH_FIFO_DEPTH)-1:0]  ch_uidmem_raddr;
    logic [NR_CH:1] [MT_DW+ECC_DW-1:0]           ch_uidmem_rdata;

    /////////////////////////////////////////////
    ///// AXI 2 AHB conversion
    snps_dma_cntrl #(
      .NR_REGIONS(NR_REGIONS),
      .REGION_SLAVE_ID(REGION_SLAVE_ID),
      .REGION_ST_ADDR(REGION_ST_ADDR),
      .REGION_END_ADDR(REGION_END_ADDR),
      .NR_TOK_PROD(NR_TOK_PROD),
      .NR_TOK_CONS(NR_TOK_CONS),
      .NR_TOP_TOK_PROD(NR_TOP_TOK_PROD),
      .NR_TOP_TOK_CONS(NR_TOP_TOK_CONS),
      .SL_AW(SL_AW),
      .SL_DW(SL_DW),
      .SL_IDW(SL_IDW),
      .SL_BW(SL_BW),
      .CFG(CFG)
    ) u_dma_cntrl (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      ///// AXI subordinate:
      // Write Address Channel
      .i_awid(i_awid),
      .i_awaddr(i_awaddr),
      .i_awlen(i_awlen),
      .i_awsize(i_awsize),
      .i_awburst(i_awburst),
      .i_awvalid(i_awvalid),
      .o_awready(o_awready),
      // Read Address Channel
      .i_arid(i_arid),
      .i_araddr(i_araddr),
      .i_arlen(i_arlen),
      .i_arsize(i_arsize),
      .i_arburst(i_arburst),
      .i_arvalid(i_arvalid),
      .o_arready(o_arready),
      // Write  Data Channel
      .i_wdata(i_wdata),
      .i_wstrb(i_wstrb),
      .i_wlast(i_wlast),
      .i_wvalid(i_wvalid),
      .o_wready(o_wready),
      // Read Data Channel
      .o_rid(o_rid),
      .o_rdata(o_rdata),
      .o_rresp(o_rresp),
      .o_rlast(o_rlast),
      .o_rvalid(o_rvalid),
      .i_rready(i_rready),
      // Write Response Channel
      .o_bid(o_bid),
      .o_bresp(o_bresp),
      .o_bvalid(o_bvalid),
      .i_bready(i_bready),

      // AHB to DMA:
      .o_hsel(hsel),
      .o_haddr(haddr),
      .o_hsize(hsize),
      .o_htrans(htrans),
      .o_hready(hready),
      .o_hwrite(hwrite),
      .o_hwdata(hwdata),
      .i_hrdata(hrdata),
      .i_hresp(hresp),
      .i_hready_resp(hready_resp),

      .o_cmd_dropped(), // TODO: where do you we connect this to? PLIC?

      ///// Tokens:
      .o_tok_prod_vld(o_tok_prod_vld),
      .i_tok_prod_rdy(i_tok_prod_rdy),
      .i_tok_cons_vld(i_tok_cons_vld),
      .o_tok_cons_rdy(o_tok_cons_rdy),

      ///// Timestamp:
      .o_ts_start(o_ts_start),
      .o_ts_end(o_ts_end),
      ///// ACD sync:
      .o_acd_sync(o_acd_sync),

      // DMA status:
      .debug_ch_en(debug_ch_en)
    );
    /////////////////////////////////////////////

    // Get the actual DMA, based on DMA_VERSION, and memory instances
    // single DMA for core and sys:
    case (DMA_VERSION)
      "aic_lt" : begin : g_lt
        aic_lt_DW_axi_dmac i_dma(.*);
      end
      "aic_ht" : begin : g_ht
        aic_ht_DW_axi_dmac i_dma(.*);
      end
      "apu" : begin : g_apu
        apu_DW_axi_dmac i_dma(.*);
      end
      default : begin : g_def
        apu_DW_axi_dmac i_dma(.*);
      end
    endcase

    /////////////////////////////////////////
    /// attach logics to / from ports that are not directly as we want
        // clk & reset:
    always_comb dmac_core_clock    = i_clk;
    always_comb dmac_core_resetn   = i_rst_n;
    always_comb scan_mode          = i_test_mode;

    //channel fifo memory:
    always_comb begin
        ch_fifomem_clk[1]        = dmac_ch1_fifomem_clk;
        ch_fifomem_wcen[1]       = dmac_ch1_fifomem_wcen;
        ch_fifomem_wen[1]        = dmac_ch1_fifomem_wen;
        ch_fifomem_waddr[1]      = dmac_ch1_fifomem_waddr;
        ch_fifomem_wdata[1]      = dmac_ch1_fifomem_wdata;
        ch_fifomem_rcen[1]       = dmac_ch1_fifomem_rcen;
        ch_fifomem_ren[1]        = dmac_ch1_fifomem_ren;
        ch_fifomem_raddr[1]      = dmac_ch1_fifomem_raddr;
        dmac_ch1_fifomem_rdata   = ch_fifomem_rdata[1];
    end
    if (CFG.dma_has_uid) begin: g_ch1_uid
      always_comb begin
        ch_uidmem_clk[1]        = dmac_ch1_uidmem_clk;
        ch_uidmem_wcen[1]       = dmac_ch1_uidmem_wcen;
        ch_uidmem_wen[1]        = dmac_ch1_uidmem_wen;
        ch_uidmem_waddr[1]      = dmac_ch1_uidmem_waddr;
        ch_uidmem_wdata[1]      = dmac_ch1_uidmem_wdata;
        ch_uidmem_rcen[1]       = dmac_ch1_uidmem_rcen;
        ch_uidmem_ren[1]        = dmac_ch1_uidmem_ren;
        ch_uidmem_raddr[1]      = dmac_ch1_uidmem_raddr;
        dmac_ch1_uidmem_rdata   = ch_uidmem_rdata[1];
      end
    end
    if(NR_CH > 1) begin : g_ch2 // version of 2 or more channels
        always_comb begin
            ch_fifomem_clk[2]        = dmac_ch2_fifomem_clk;
            ch_fifomem_wcen[2]       = dmac_ch2_fifomem_wcen;
            ch_fifomem_wen[2]        = dmac_ch2_fifomem_wen;
            ch_fifomem_waddr[2]      = dmac_ch2_fifomem_waddr;
            ch_fifomem_wdata[2]      = dmac_ch2_fifomem_wdata;
            ch_fifomem_rcen[2]       = dmac_ch2_fifomem_rcen;
            ch_fifomem_ren[2]        = dmac_ch2_fifomem_ren;
            ch_fifomem_raddr[2]      = dmac_ch2_fifomem_raddr;
            dmac_ch2_fifomem_rdata   = ch_fifomem_rdata[2];
        end
        if (CFG.dma_has_uid) begin: g_ch2_uid
          always_comb begin
            ch_uidmem_clk[2]        = dmac_ch2_uidmem_clk;
            ch_uidmem_wcen[2]       = dmac_ch2_uidmem_wcen;
            ch_uidmem_wen[2]        = dmac_ch2_uidmem_wen;
            ch_uidmem_waddr[2]      = dmac_ch2_uidmem_waddr;
            ch_uidmem_wdata[2]      = dmac_ch2_uidmem_wdata;
            ch_uidmem_rcen[2]       = dmac_ch2_uidmem_rcen;
            ch_uidmem_ren[2]        = dmac_ch2_uidmem_ren;
            ch_uidmem_raddr[2]      = dmac_ch2_uidmem_raddr;
            dmac_ch2_uidmem_rdata   = ch_uidmem_rdata[2];
          end
        end
    end
    if(NR_CH > 2) begin : g_ch34 // version of 4 channels
        always_comb begin
            ch_fifomem_clk[3]        = dmac_ch3_fifomem_clk;
            ch_fifomem_wcen[3]       = dmac_ch3_fifomem_wcen;
            ch_fifomem_wen[3]        = dmac_ch3_fifomem_wen;
            ch_fifomem_waddr[3]      = dmac_ch3_fifomem_waddr;
            ch_fifomem_wdata[3]      = dmac_ch3_fifomem_wdata;
            ch_fifomem_rcen[3]       = dmac_ch3_fifomem_rcen;
            ch_fifomem_ren[3]        = dmac_ch3_fifomem_ren;
            ch_fifomem_raddr[3]      = dmac_ch3_fifomem_raddr;
            dmac_ch3_fifomem_rdata   = ch_fifomem_rdata[3];
        end
        always_comb begin
            ch_fifomem_clk[4]        = dmac_ch4_fifomem_clk;
            ch_fifomem_wcen[4]       = dmac_ch4_fifomem_wcen;
            ch_fifomem_wen[4]        = dmac_ch4_fifomem_wen;
            ch_fifomem_waddr[4]      = dmac_ch4_fifomem_waddr;
            ch_fifomem_wdata[4]      = dmac_ch4_fifomem_wdata;
            ch_fifomem_rcen[4]       = dmac_ch4_fifomem_rcen;
            ch_fifomem_ren[4]        = dmac_ch4_fifomem_ren;
            ch_fifomem_raddr[4]      = dmac_ch4_fifomem_raddr;
            dmac_ch4_fifomem_rdata   = ch_fifomem_rdata[4];
        end
        if (CFG.dma_has_uid) begin: g_ch34_uid
          always_comb begin
            ch_uidmem_clk[3]        = dmac_ch3_uidmem_clk;
            ch_uidmem_wcen[3]       = dmac_ch3_uidmem_wcen;
            ch_uidmem_wen[3]        = dmac_ch3_uidmem_wen;
            ch_uidmem_waddr[3]      = dmac_ch3_uidmem_waddr;
            ch_uidmem_wdata[3]      = dmac_ch3_uidmem_wdata;
            ch_uidmem_rcen[3]       = dmac_ch3_uidmem_rcen;
            ch_uidmem_ren[3]        = dmac_ch3_uidmem_ren;
            ch_uidmem_raddr[3]      = dmac_ch3_uidmem_raddr;
            dmac_ch3_uidmem_rdata   = ch_uidmem_rdata[3];
          end
          always_comb begin
            ch_uidmem_clk[4]        = dmac_ch4_uidmem_clk;
            ch_uidmem_wcen[4]       = dmac_ch4_uidmem_wcen;
            ch_uidmem_wen[4]        = dmac_ch4_uidmem_wen;
            ch_uidmem_waddr[4]      = dmac_ch4_uidmem_waddr;
            ch_uidmem_wdata[4]      = dmac_ch4_uidmem_wdata;
            ch_uidmem_rcen[4]       = dmac_ch4_uidmem_rcen;
            ch_uidmem_ren[4]        = dmac_ch4_uidmem_ren;
            ch_uidmem_raddr[4]      = dmac_ch4_uidmem_raddr;
            dmac_ch4_uidmem_rdata   = ch_uidmem_rdata[4];
          end
        end
    end

    // Master ports:
    always_comb begin
        // Write Address Channel
        o_axi_m_awid[0] = awid_m1;
        o_axi_m_awaddr[0] = awaddr_m1;
        o_axi_m_awlen[0] = awlen_m1;
        o_axi_m_awsize[0] = awsize_m1;
        o_axi_m_awburst[0] = awburst_m1;
        o_axi_m_awlock[0] = awlock_m1;
        o_axi_m_awcache[0] = awcache_m1;
        o_axi_m_awprot[0] = awprot_m1;
        o_axi_m_awvalid[0] = awvalid_m1;
        awready_m1 = i_axi_m_awready[0];
        // Read Address Channel
        o_axi_m_arid[0] = arid_m1;
        o_axi_m_araddr[0] = araddr_m1;
        o_axi_m_arlen[0] = arlen_m1;
        o_axi_m_arsize[0] = arsize_m1;
        o_axi_m_arburst[0] = arburst_m1;
        o_axi_m_arlock[0] = arlock_m1;
        o_axi_m_arcache[0] = arcache_m1;
        o_axi_m_arprot[0] = arprot_m1;
        o_axi_m_arvalid[0] = arvalid_m1;
        arready_m1 = i_axi_m_arready[0];
        // Write  Data Channel
        o_axi_m_wdata[0] = wdata_m1;
        o_axi_m_wstrb[0] = wstrb_m1;
        o_axi_m_wlast[0] = wlast_m1;
        o_axi_m_wvalid[0] = wvalid_m1;
        wready_m1 = i_axi_m_wready[0];
        // Read Data Channel
        rid_m1 = i_axi_m_rid[0];
        rdata_m1 = i_axi_m_rdata[0];
        rresp_m1 = i_axi_m_rresp[0];
        rlast_m1 = i_axi_m_rlast[0];
        rvalid_m1 = i_axi_m_rvalid[0];
        o_axi_m_rready[0] = rready_m1;
        // Write Response Channel
        bid_m1 = i_axi_m_bid[0];
        bresp_m1 = i_axi_m_bresp[0];
        bvalid_m1 = i_axi_m_bvalid[0];
        o_axi_m_bready[0] = bready_m1;
    end
    if(NR_MT > 1) begin : g_mt2_ // version of 2 or more channels
        always_comb begin
            // Write Address Channel
            o_axi_m_awid[1] = awid_m2;
            o_axi_m_awaddr[1] = awaddr_m2;
            o_axi_m_awlen[1] = awlen_m2;
            o_axi_m_awsize[1] = awsize_m2;
            o_axi_m_awburst[1] = awburst_m2;
            o_axi_m_awlock[1] = awlock_m2;
            o_axi_m_awcache[1] = awcache_m2;
            o_axi_m_awprot[1] = awprot_m2;
            o_axi_m_awvalid[1] = awvalid_m2;
            awready_m2 = i_axi_m_awready[1];
            // Read Address Channel
            o_axi_m_arid[1] = arid_m2;
            o_axi_m_araddr[1] = araddr_m2;
            o_axi_m_arlen[1] = arlen_m2;
            o_axi_m_arsize[1] = arsize_m2;
            o_axi_m_arburst[1] = arburst_m2;
            o_axi_m_arlock[1] = arlock_m2;
            o_axi_m_arcache[1] = arcache_m2;
            o_axi_m_arprot[1] = arprot_m2;
            o_axi_m_arvalid[1] = arvalid_m2;
            arready_m2 = i_axi_m_arready[1];
            // Write  Data Channel
            o_axi_m_wdata[1] = wdata_m2;
            o_axi_m_wstrb[1] = wstrb_m2;
            o_axi_m_wlast[1] = wlast_m2;
            o_axi_m_wvalid[1] = wvalid_m2;
            wready_m2 = i_axi_m_wready[1];
            // Read Data Channel
            rid_m2 = i_axi_m_rid[1];
            rdata_m2 = i_axi_m_rdata[1];
            rresp_m2 = i_axi_m_rresp[1];
            rlast_m2 = i_axi_m_rlast[1];
            rvalid_m2 = i_axi_m_rvalid[1];
            o_axi_m_rready[1] = rready_m2;
            // Write Response Channel
            bid_m2 = i_axi_m_bid[1];
            bresp_m2 = i_axi_m_bresp[1];
            bvalid_m2 = i_axi_m_bvalid[1];
            o_axi_m_bready[1] = bready_m2;
        end
    end

    // debug signal assignement:
    if (NR_MT>1) begin : g_dbg_2mt
      always_comb o_dma_debug ={
                        debug_grant_index_ar_ch_m1,
                        debug_grant_index_aw_ch_m1,
                        debug_ch_wr_arb_req_m1,
                        debug_ch_rd_arb_req_m1,
                        debug_ch_lli_rd_req_m1,
                        debug_grant_index_ar_ch_m2,
                        debug_grant_index_aw_ch_m2,
                        debug_ch_wr_arb_req_m2,
                        debug_ch_rd_arb_req_m2,
                        debug_ch_lli_rd_req_m2,
                        debug_ch_src_blk_tfr_done,
                        debug_ch_dst_blk_tfr_done,
                        debug_ch_blk_tfr_done,
                        debug_ch_src_trans_done,
                        debug_ch_dst_trans_done,
                        debug_ch_dma_tfr_done,
                        debug_ch_src_trans_req,
                        debug_ch_dst_trans_req,
                        debug_ch_src_is_in_str,
                        debug_ch_dst_is_in_str,
                        debug_ch_shadowreg_or_lli_invalid_err,
                        debug_ch_suspended,
                        debug_ch_en};
    end else begin : g_dbg_1mt
      always_comb o_dma_debug = {
                        debug_grant_index_ar_ch_m1,
                        debug_grant_index_aw_ch_m1,
                        debug_ch_wr_arb_req_m1,
                        debug_ch_rd_arb_req_m1,
                        debug_ch_lli_rd_req_m1,
                        debug_ch_src_blk_tfr_done,
                        debug_ch_dst_blk_tfr_done,
                        debug_ch_blk_tfr_done,
                        debug_ch_src_trans_done,
                        debug_ch_dst_trans_done,
                        debug_ch_dma_tfr_done,
                        debug_ch_src_trans_req,
                        debug_ch_dst_trans_req,
                        debug_ch_src_is_in_str,
                        debug_ch_dst_is_in_str,
                        debug_ch_shadowreg_or_lli_invalid_err,
                        debug_ch_suspended,
                        debug_ch_en};
    end
    /////////////////////////////////////////

    /////////////////////////////////////////
    // memories for the channel FIFO's:
    localparam int unsigned UID_NR_CH = CFG.dma_has_uid ? NR_CH : 0;
    axe_tcl_sram_pkg::impl_inp_t [NR_CH+UID_NR_CH:1] impl_inp_ram;
    axe_tcl_sram_pkg::impl_oup_t [NR_CH+UID_NR_CH:1] impl_oup_ram;

    axe_tcl_sram_cfg #(
        .NUM_SRAMS(NR_CH+UID_NR_CH)
    ) u_sram_cfg_impl (
        .i_s(i_impl_inp),
        .o_s(o_impl_oup),
        .o_m(impl_inp_ram),
        .i_m(impl_oup_ram)
    );

    for (genvar i=1; i<=NR_CH; i++) begin : g_fifo_rams
        snps_dma_dp_ram #(
            .RAM_DEPTH(CH_FIFO_DEPTH),
            .RAM_WIDTH(MT_DW),
            .MACRO_WIDTH(MACRO_WIDTH),
            .SRAM_IMPL_KEY(SRAM_IMPL_KEY)
        ) u_ram (
            .i_clk(ch_fifomem_clk[i]),
            .i_rst_n,
            .i_wcen(ch_fifomem_wcen[i]),
            .i_wen(ch_fifomem_wen[i]),
            .i_waddr(ch_fifomem_waddr[i]),
            .i_wdata(ch_fifomem_wdata[i]),
            .i_rcen(ch_fifomem_rcen[i]),
            .i_ren(ch_fifomem_ren[i]),
            .i_raddr(ch_fifomem_raddr[i]),
            .o_rdata(ch_fifomem_rdata[i]),
            .i_impl_inp(impl_inp_ram[i]),
            .o_impl_oup(impl_oup_ram[i])
        );
    end
    if (CFG.dma_has_uid) begin: g_uid_ext_ram
      for (genvar i=1; i<=NR_CH; i++) begin : g_fifo_rams
          snps_dma_dp_ram #(
              .RAM_DEPTH(CH_FIFO_DEPTH),
              .RAM_WIDTH(MT_DW+ECC_DW),
              .MACRO_WIDTH(MACRO_WIDTH),
              .SRAM_IMPL_KEY(SRAM_IMPL_KEY)
          ) u_ram (
              .i_clk(ch_uidmem_clk[i]),
              .i_rst_n,
              .i_wcen(ch_uidmem_wcen[i]),
              .i_wen(ch_uidmem_wen[i]),
              .i_waddr(ch_uidmem_waddr[i]),
              .i_wdata(ch_uidmem_wdata[i]),
              .i_rcen(ch_uidmem_rcen[i]),
              .i_ren(ch_uidmem_ren[i]),
              .i_raddr(ch_uidmem_raddr[i]),
              .o_rdata(ch_uidmem_rdata[i]),
              .i_impl_inp(impl_inp_ram[i+NR_CH]),
              .o_impl_oup(impl_oup_ram[i+NR_CH])
          );
      end
    end

endmodule
