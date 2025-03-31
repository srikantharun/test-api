// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DPU top stub. Connects DPU-DP with CMD Block CMDGen and CSR.
// Has interfaces: AXI config, AXI data, AXIS from IAU, IFD1 and towards ODR.
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

module dpu
  import dpu_pkg::*;
  import dpu_csr_reg_pkg::*;
#(
  // AXI parameters
  localparam int unsigned AxiLpLocalAddrW = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH,
  localparam int unsigned AxiLpBurstTypeW = aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH,
  localparam int unsigned AxiLpSubIdW     = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH,
  localparam int unsigned AxiLpLenW       = aic_common_pkg::AIC_LT_AXI_LEN_WIDTH,
  localparam int unsigned AxiLpSizeW      = aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH,
  localparam int unsigned AxiLpRespW      = aic_common_pkg::AIC_LT_AXI_RESP_WIDTH,
  localparam int unsigned AxiLpWstrbW     = aic_common_pkg::AIC_LT_AXI_WSTRB_WIDTH,
  localparam int unsigned AxiLpDataW      = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH,

  // default address regions for CSR, CMD, and PRG:
  parameter longint REGION_ST_ADDR[3]  = {64'h0000_0000_0000_0000, 64'h0000_0000_0000_1000, 64'h0000_0000_0000_8000},
  parameter longint REGION_END_ADDR[3] = {64'h0000_0000_0000_0fff, 64'h0000_0000_0000_1fff, 64'h0000_0000_0000_ffff},

  // SRAM daisy chain
  parameter int unsigned SRAM_DAISY_ORDERING[DPU_NUM_MACROS] = DPU_MACRO_DAISY_DEFAULT
) (
  input wire i_clk,
  input wire i_rst_n,

  //--------------------------------------------------
  // AXI4 slave config port
  //--------------------------------------------------
  // AXI S read address channel
  input  logic [AxiLpLocalAddrW-1:0] i_dpu_cfg_axi_s_araddr,
  input  logic [AxiLpBurstTypeW-1:0] i_dpu_cfg_axi_s_arburst,
  input  logic [    AxiLpSubIdW-1:0] i_dpu_cfg_axi_s_arid,
  input  logic [      AxiLpLenW-1:0] i_dpu_cfg_axi_s_arlen,
  input  logic [     AxiLpSizeW-1:0] i_dpu_cfg_axi_s_arsize,
  input  logic                       i_dpu_cfg_axi_s_arvalid,
  output logic                       o_dpu_cfg_axi_s_arready,
  // AXI S write address channel
  input  logic [AxiLpLocalAddrW-1:0] i_dpu_cfg_axi_s_awaddr,
  input  logic [AxiLpBurstTypeW-1:0] i_dpu_cfg_axi_s_awburst,
  input  logic [    AxiLpSubIdW-1:0] i_dpu_cfg_axi_s_awid,
  input  logic [      AxiLpLenW-1:0] i_dpu_cfg_axi_s_awlen,
  input  logic [     AxiLpSizeW-1:0] i_dpu_cfg_axi_s_awsize,
  input  logic                       i_dpu_cfg_axi_s_awvalid,
  output logic                       o_dpu_cfg_axi_s_awready,
  // AXI S write response channel
  output logic [    AxiLpSubIdW-1:0] o_dpu_cfg_axi_s_bid,
  output logic [     AxiLpRespW-1:0] o_dpu_cfg_axi_s_bresp,
  output logic                       o_dpu_cfg_axi_s_bvalid,
  input  logic                       i_dpu_cfg_axi_s_bready,
  // AXI S read data/response channel
  output logic [     AxiLpDataW-1:0] o_dpu_cfg_axi_s_rdata,
  output logic [    AxiLpSubIdW-1:0] o_dpu_cfg_axi_s_rid,
  output logic                       o_dpu_cfg_axi_s_rlast,
  output logic [     AxiLpRespW-1:0] o_dpu_cfg_axi_s_rresp,
  output logic                       o_dpu_cfg_axi_s_rvalid,
  input  logic                       i_dpu_cfg_axi_s_rready,
  // AXI S write data channel
  input  logic [     AxiLpDataW-1:0] i_dpu_cfg_axi_s_wdata,
  input  logic                       i_dpu_cfg_axi_s_wlast,
  input  logic [    AxiLpWstrbW-1:0] i_dpu_cfg_axi_s_wstrb,
  input  logic                       i_dpu_cfg_axi_s_wvalid,
  output logic                       o_dpu_cfg_axi_s_wready,

  // Tokens
  output wire [NR_TOK_PROD-1:0] o_dpu_tok_prod_vld,
  input  wire [NR_TOK_PROD-1:0] i_dpu_tok_prod_rdy,
  input  wire [NR_TOK_CONS-1:0] i_dpu_tok_cons_vld,
  output wire [NR_TOK_CONS-1:0] o_dpu_tok_cons_rdy,

  // IAU AXI stream
  input  logic [PW_IAU_W-1:0] i_dpu_iau_axis_s_data,
  input  logic                i_dpu_iau_axis_s_last,
  input  logic                i_dpu_iau_axis_s_valid,
  output logic                o_dpu_iau_axis_s_ready,

  // IFD1 AXI stream
  input  logic [PW_IO_W-1:0] i_dpu_ifd1_axis_s_data,
  input  logic               i_dpu_ifd1_axis_s_last,
  input  logic               i_dpu_ifd1_axis_s_valid,
  output logic               o_dpu_ifd1_axis_s_ready,

  // ODR AXI stream
  output logic [PW_IO_W-1:0] o_dpu_odr_axis_m_data,
  output logic               o_dpu_odr_axis_m_last,
  output logic               o_dpu_odr_axis_m_valid,
  input  logic               i_dpu_odr_axis_m_ready,

  // IRQ
  output logic o_irq,

  // Observation
  output logic [OBS_W-1:0] o_obs,

  ///// Timestamp:
  output logic o_ts_start,
  output logic o_ts_end,
  ///// ACD sync:
  output logic o_acd_sync,

  // Block identification
  input logic [     CID_W-1:0] i_cid,
  input logic [BLOCK_ID_W-1:0] i_block_id,

  // SRAM sideband signals
  input  axe_tcl_sram_pkg::impl_inp_t i_sram_impl,
  output axe_tcl_sram_pkg::impl_oup_t o_sram_impl
);

  //--------------------------------------------------
  // AXI4 config demux
  //--------------------------------------------------
  // Read address channel
  logic [NR_AXI_SLV-1:0][AxiLpLocalAddrW-1:0] demux_araddr;
  logic [NR_AXI_SLV-1:0][AxiLpBurstTypeW-1:0] demux_arburst;
  logic [NR_AXI_SLV-1:0][AxiLpSubIdW-1:0] demux_arid;
  logic [NR_AXI_SLV-1:0][AxiLpLenW-1:0] demux_arlen;
  logic [NR_AXI_SLV-1:0][AxiLpSizeW-1:0] demux_arsize;
  logic [NR_AXI_SLV-1:0] demux_arvalid;
  logic [NR_AXI_SLV-1:0] demux_arready;
  // Write address channel
  logic [NR_AXI_SLV-1:0][AxiLpLocalAddrW-1:0] demux_awaddr;
  logic [NR_AXI_SLV-1:0][AxiLpBurstTypeW-1:0] demux_awburst;
  logic [NR_AXI_SLV-1:0][AxiLpSubIdW-1:0] demux_awid;
  logic [NR_AXI_SLV-1:0][AxiLpLenW-1:0] demux_awlen;
  logic [NR_AXI_SLV-1:0][AxiLpSizeW-1:0] demux_awsize;
  logic [NR_AXI_SLV-1:0] demux_awvalid;
  logic [NR_AXI_SLV-1:0] demux_awready;
  // Write response channel
  logic [NR_AXI_SLV-1:0][AxiLpSubIdW-1:0] demux_bid;
  logic [NR_AXI_SLV-1:0][AxiLpRespW-1:0] demux_bresp;
  logic [NR_AXI_SLV-1:0] demux_bvalid;
  logic [NR_AXI_SLV-1:0] demux_bready;
  // Read data/response channel
  logic [NR_AXI_SLV-1:0][AxiLpDataW-1:0] demux_rdata;
  logic [NR_AXI_SLV-1:0][AxiLpSubIdW-1:0] demux_rid;
  logic [NR_AXI_SLV-1:0] demux_rlast;
  logic [NR_AXI_SLV-1:0][AxiLpRespW-1:0] demux_rresp;
  logic [NR_AXI_SLV-1:0] demux_rvalid;
  logic [NR_AXI_SLV-1:0] demux_rready;
  // Write data channel
  logic [NR_AXI_SLV-1:0][AxiLpDataW-1:0] demux_wdata;
  logic [NR_AXI_SLV-1:0] demux_wlast;
  logic [NR_AXI_SLV-1:0][AxiLpWstrbW-1:0] demux_wstrb;
  logic [NR_AXI_SLV-1:0] demux_wvalid;
  logic [NR_AXI_SLV-1:0] demux_wready;

  //--------------------------------------------------
  // CSR
  //--------------------------------------------------
  // CSR AXI interface
  axi_a_ch_h2d_t csr_axi_aw;
  logic csr_axi_awready;
  axi_a_ch_h2d_t csr_axi_ar;
  logic csr_axi_arready;
  axi_w_ch_h2d_t csr_axi_w;
  logic csr_axi_wready;
  axi_r_ch_d2h_t csr_axi_r;
  logic csr_axi_rready;
  axi_b_ch_d2h_t csr_axi_b;
  logic csr_axi_bready;
  // CSR HW interface
  dpu_csr_reg2hw_t csr_reg2hw;
  dpu_csr_hw2reg_t csr_hw2reg;

  // IRQs
  dpu_csr_dp_irq_status_reg_t dp_error;
  dpu_csr_cmdgen_irq_status_reg_t cmdgen_error;
  logic cmdblk_cmd_dropped;

  //--------------------------------------------------
  // CMD Block
  //--------------------------------------------------
  aic_dp_cmd_gen_pkg::cmdb_cmd_t cmd_data;
  aic_dp_cmd_gen_pkg::cmdb_cmd_t packed_cmd_data;
  aic_dp_cmd_gen_pkg::cmd_format_t cmd_format;
  aic_dp_cmd_gen_pkg::cmd_config_t cmd_config;
  logic cmd_vld;
  logic cmd_rdy;
  logic cmd_done;

  //--------------------------------------------------
  // DPcmd Gen / Shim
  //--------------------------------------------------
  dpu_dp_cmd_t dpcmd_data;
  aic_dp_cmd_gen_pkg::metadata_t dpcmd_metadata;
  aic_dp_cmd_gen_pkg::loop_iterations_t dpcmd_iterations;
  logic dpcmd_last;
  logic dpcmd_valid;
  logic dpcmd_ready;

  dpu_instr_t instruction_data;
  logic instruction_last;
  logic instruction_valid;
  logic instruction_ready;

  //--------------------------------------------------
  // DPU DP
  //--------------------------------------------------
  logic [IAU_W-1:0] dp_iau_axis_data[PW_LEN];
  logic [IO_W-1:0] dp_ifd1_axis_data[PW_LEN];
  logic [IO_W-1:0] dp_odr_axis_data[PW_LEN];
  logic dp_done;

  //--------------------------------------------------
  // AXI Demux
  //--------------------------------------------------
  logic [$clog2(NR_AXI_SLV+1)-1:0] bus_sel_rd;
  logic [$clog2(NR_AXI_SLV+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AxiLpLocalAddrW),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(NR_AXI_SLV),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_wr (
    .addr_in(i_dpu_cfg_axi_s_awaddr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AxiLpLocalAddrW),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(NR_AXI_SLV),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_rd (
    .addr_in(i_dpu_cfg_axi_s_araddr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  simple_axi_demux #(
    .IDW(AxiLpSubIdW),
    .AW (AxiLpLocalAddrW),
    .DW (AxiLpDataW),
    .BW (AxiLpLenW),

    .NR_MASTERS(NR_AXI_SLV),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(8),
    .EXT_SEL(1)
  ) i_dpu_axi_demux (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    // AXI S read address channel
    .s_araddr (i_dpu_cfg_axi_s_araddr),
    .s_arburst(i_dpu_cfg_axi_s_arburst),
    .s_arcache('0),
    .s_arid   (i_dpu_cfg_axi_s_arid),
    .s_arlen  (i_dpu_cfg_axi_s_arlen),
    .s_arlock ('0),
    .s_arprot ('0),
    .s_arsize (i_dpu_cfg_axi_s_arsize),
    .s_arvalid(i_dpu_cfg_axi_s_arvalid),
    .s_arready(o_dpu_cfg_axi_s_arready),
    // AXI S write address channel
    .s_awaddr (i_dpu_cfg_axi_s_awaddr),
    .s_awburst(i_dpu_cfg_axi_s_awburst),
    .s_awcache('0),
    .s_awid   (i_dpu_cfg_axi_s_awid),
    .s_awlen  (i_dpu_cfg_axi_s_awlen),
    .s_awlock ('0),
    .s_awprot ('0),
    .s_awsize (i_dpu_cfg_axi_s_awsize),
    .s_awvalid(i_dpu_cfg_axi_s_awvalid),
    .s_awready(o_dpu_cfg_axi_s_awready),
    // AXI S write response channel
    .s_bid    (o_dpu_cfg_axi_s_bid),
    .s_bresp  (o_dpu_cfg_axi_s_bresp),
    .s_bvalid (o_dpu_cfg_axi_s_bvalid),
    .s_bready (i_dpu_cfg_axi_s_bready),
    // AXI S read data/response channel
    .s_rid    (o_dpu_cfg_axi_s_rid),
    .s_rdata  (o_dpu_cfg_axi_s_rdata),
    .s_rlast  (o_dpu_cfg_axi_s_rlast),
    .s_rresp  (o_dpu_cfg_axi_s_rresp),
    .s_rvalid (o_dpu_cfg_axi_s_rvalid),
    .s_rready (i_dpu_cfg_axi_s_rready),
    // AXI S write data channel
    .s_wdata  (i_dpu_cfg_axi_s_wdata),
    .s_wlast  (i_dpu_cfg_axi_s_wlast),
    .s_wstrb  (i_dpu_cfg_axi_s_wstrb),
    .s_wvalid (i_dpu_cfg_axi_s_wvalid),
    .s_wready (o_dpu_cfg_axi_s_wready),

    // Demuxed read address channel
    .m_araddr (demux_araddr),
    .m_arburst(demux_arburst),
    .m_arcache(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arid   (demux_arid),
    .m_arlen  (demux_arlen),
    .m_arlock (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arprot (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arsize (demux_arsize),
    .m_arvalid(demux_arvalid),
    .m_arready(demux_arready),
    // Demuxed write address channel
    .m_awaddr (demux_awaddr),
    .m_awburst(demux_awburst),
    .m_awcache(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awid   (demux_awid),
    .m_awlen  (demux_awlen),
    .m_awlock (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awprot (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awsize (demux_awsize),
    .m_awvalid(demux_awvalid),
    .m_awready(demux_awready),
    // Demuxed write response channel
    .m_bid    (demux_bid),
    .m_bresp  (demux_bresp),
    .m_bvalid (demux_bvalid),
    .m_bready (demux_bready),
    // Demuxed read data/response channel
    .m_rdata  (demux_rdata),
    .m_rid    (demux_rid),
    .m_rlast  (demux_rlast),
    .m_rresp  (demux_rresp),
    .m_rvalid (demux_rvalid),
    .m_rready (demux_rready),
    // Demuxed write data channel
    .m_wdata  (demux_wdata),
    .m_wlast  (demux_wlast),
    .m_wstrb  (demux_wstrb),
    .m_wvalid (demux_wvalid),
    .m_wready (demux_wready)
  );

  //--------------------------------------------------
  // CSRs
  //--------------------------------------------------
  assign csr_axi_ar.addr  = demux_araddr[AXI_S_IDX_CSR];
  assign csr_axi_ar.burst = demux_arburst[AXI_S_IDX_CSR];
  assign csr_axi_ar.id    = demux_arid[AXI_S_IDX_CSR];
  assign csr_axi_ar.len   = demux_arlen[AXI_S_IDX_CSR];
  assign csr_axi_ar.size  = demux_arsize[AXI_S_IDX_CSR];
  assign csr_axi_ar.valid = demux_arvalid[AXI_S_IDX_CSR];
  assign demux_arready[AXI_S_IDX_CSR] = csr_axi_arready;

  assign csr_axi_aw.addr  = demux_awaddr[AXI_S_IDX_CSR];
  assign csr_axi_aw.burst = demux_awburst[AXI_S_IDX_CSR];
  assign csr_axi_aw.id    = demux_awid[AXI_S_IDX_CSR];
  assign csr_axi_aw.len   = demux_awlen[AXI_S_IDX_CSR];
  assign csr_axi_aw.size  = demux_awsize[AXI_S_IDX_CSR];
  assign csr_axi_aw.valid = demux_awvalid[AXI_S_IDX_CSR];
  assign demux_awready[AXI_S_IDX_CSR] = csr_axi_awready;

  assign demux_bid[AXI_S_IDX_CSR]    = csr_axi_b.id;
  assign demux_bresp[AXI_S_IDX_CSR]  = csr_axi_b.resp;
  assign demux_bvalid[AXI_S_IDX_CSR] = csr_axi_b.valid;
  assign csr_axi_bready = demux_bready[AXI_S_IDX_CSR];

  assign demux_rdata[AXI_S_IDX_CSR]  = csr_axi_r.data;
  assign demux_rid[AXI_S_IDX_CSR]    = csr_axi_r.id;
  assign demux_rlast[AXI_S_IDX_CSR]  = csr_axi_r.last;
  assign demux_rresp[AXI_S_IDX_CSR]  = csr_axi_r.resp;
  assign demux_rvalid[AXI_S_IDX_CSR] = csr_axi_r.valid;
  assign csr_axi_rready = demux_rready[AXI_S_IDX_CSR];

  assign csr_axi_w.data  = demux_wdata[AXI_S_IDX_CSR];
  assign csr_axi_w.last  = demux_wlast[AXI_S_IDX_CSR];
  assign csr_axi_w.strb  = demux_wstrb[AXI_S_IDX_CSR];
  assign csr_axi_w.valid = demux_wvalid[AXI_S_IDX_CSR];
  assign demux_wready[AXI_S_IDX_CSR] = csr_axi_wready;

  // AXI stream debug
  assign csr_hw2reg.dbg_observe.in0_lst.d = i_dpu_iau_axis_s_last;
  assign csr_hw2reg.dbg_observe.in0_rdy.d = o_dpu_iau_axis_s_ready;
  assign csr_hw2reg.dbg_observe.in0_vld.d = i_dpu_iau_axis_s_valid;
  assign csr_hw2reg.dbg_observe.in1_lst.d = i_dpu_ifd1_axis_s_last;
  assign csr_hw2reg.dbg_observe.in1_rdy.d = o_dpu_ifd1_axis_s_ready;
  assign csr_hw2reg.dbg_observe.in1_vld.d = i_dpu_ifd1_axis_s_valid;
  assign csr_hw2reg.dbg_observe.out_lst.d = o_dpu_odr_axis_m_last;
  assign csr_hw2reg.dbg_observe.out_rdy.d = i_dpu_odr_axis_m_ready;
  assign csr_hw2reg.dbg_observe.out_vld.d = o_dpu_odr_axis_m_valid;

  // Observation pins
  aic_common_pkg::aic_dev_obs_t dpu_obs;
  always_comb dpu_obs.state = csr_hw2reg.cmdblk_status.state.d;
  always_comb dpu_obs.token_stall = csr_hw2reg.cmdblk_status.wait_token.d;
  always_comb dpu_obs.dp_instr_stall = cmd_vld & ~cmd_rdy;
  always_comb dpu_obs.dp_cmd_stall = dpcmd_valid & ~dpcmd_ready;
  always_comb dpu_obs.dp_in0_stall = i_dpu_iau_axis_s_valid & ~o_dpu_iau_axis_s_ready;
  always_comb dpu_obs.dp_in1_stall = i_dpu_ifd1_axis_s_valid & ~o_dpu_ifd1_axis_s_ready;
  always_comb dpu_obs.dp_out_stall = o_dpu_odr_axis_m_valid & ~i_dpu_odr_axis_m_ready;
  assign o_obs = dpu_obs;

  // Block id
  assign csr_hw2reg.dbg_id.block_id.d    = i_block_id;
  assign csr_hw2reg.dbg_id.ai_core_id.d  = 8'(i_cid);
  assign csr_hw2reg.dbg_id.hw_revision.d = DPU_HW_REVISION;

  axe_tcl_sram_pkg::impl_inp_t [DPU_NUM_MACROS-1:0] sram_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t [DPU_NUM_MACROS-1:0] sram_impl_oup;
  axe_tcl_sram_pkg::impl_inp_t [DPU_NUM_MACROS-1:0] sram_impl_inp_daisy;
  axe_tcl_sram_pkg::impl_oup_t [DPU_NUM_MACROS-1:0] sram_impl_oup_daisy;

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(DPU_NUM_MACROS)
  ) u_sram_cfg_impl (
    .i_s(i_sram_impl),
    .o_s(o_sram_impl),
    .o_m(sram_impl_inp),
    .i_m(sram_impl_oup)
  );

  always_comb
    foreach (sram_impl_inp[i]) sram_impl_inp_daisy[SRAM_DAISY_ORDERING[i]] = sram_impl_inp[i];

  always_comb
    foreach (sram_impl_oup[i]) sram_impl_oup[i] = sram_impl_oup_daisy[SRAM_DAISY_ORDERING[i]];

  dpu_csr_reg_top i_dpu_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    // Interface: APB
    .axi_ar_i   (csr_axi_ar),
    .axi_arready(csr_axi_arready),
    .axi_aw_i   (csr_axi_aw),
    .axi_awready(csr_axi_awready),
    .axi_b_o    (csr_axi_b),
    .axi_bready (csr_axi_bready),
    .axi_r_o    (csr_axi_r),
    .axi_rready (csr_axi_rready),
    .axi_w_i    (csr_axi_w),
    .axi_wready (csr_axi_wready),
    // Interface: CSR <=> HW
    .hw2reg     (csr_hw2reg),
    .reg2hw     (csr_reg2hw),
    // Config
    .devmode_i  (1'b1)
  );

  //--------------------------------------------------
  // IRQs
  //--------------------------------------------------

  // HW can only set the status to high
  assign csr_hw2reg.irq_status.err_act_stream_in0.d = 1'b1;
  assign csr_hw2reg.irq_status.err_act_stream_in1.d = 1'b1;
  assign csr_hw2reg.irq_status.err_act_stream_out.d = 1'b1;
  assign csr_hw2reg.irq_status.err_illegal_format.d = 1'b1;
  assign csr_hw2reg.irq_status.err_empty_program.d = 1'b1;
  assign csr_hw2reg.irq_status.err_init_segfault.d = 1'b1;
  assign csr_hw2reg.irq_status.err_loop_segfault.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i0_termination.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i1_termination.d = 1'b1;
  assign csr_hw2reg.irq_status.err_id_illegal_instr.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i0_of.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i0_uf.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i0_nx.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i1_of.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i1_uf.d = 1'b1;
  assign csr_hw2reg.irq_status.err_i1_nx.d = 1'b1;
  assign csr_hw2reg.irq_status.err_madd_op_of.d = 1'b1;
  assign csr_hw2reg.irq_status.err_madd_op_uf.d = 1'b1;
  assign csr_hw2reg.irq_status.err_madd_op_nx.d = 1'b1;
  assign csr_hw2reg.irq_status.err_madd_op_nv.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sumr_op_of.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sumr_op_nx.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sumr_op_nv.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sfu_op_of.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sfu_op_uf.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sfu_op_nx.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sfu_op_nv.d = 1'b1;
  assign csr_hw2reg.irq_status.err_sfu_op_zr.d = 1'b1;
  assign csr_hw2reg.irq_status.err_o_of.d = 1'b1;
  assign csr_hw2reg.irq_status.err_o_uf.d = 1'b1;
  assign csr_hw2reg.irq_status.err_o_nx.d = 1'b1;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.d = 1'b1;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.d = 1'b1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  assign csr_hw2reg.irq_status.err_act_stream_in0.de = dp_error.err_act_stream_in0;
  assign csr_hw2reg.irq_status.err_act_stream_in1.de = dp_error.err_act_stream_in1;
  assign csr_hw2reg.irq_status.err_act_stream_out.de = dp_error.err_act_stream_out;
  assign csr_hw2reg.irq_status.err_illegal_format.de = cmdgen_error.err_illegal_format;
  assign csr_hw2reg.irq_status.err_empty_program.de = cmdgen_error.err_empty_program;
  assign csr_hw2reg.irq_status.err_init_segfault.de = cmdgen_error.err_init_segfault;
  assign csr_hw2reg.irq_status.err_loop_segfault.de = cmdgen_error.err_loop_segfault;
  assign csr_hw2reg.irq_status.err_i0_termination.de = dp_error.err_i0_termination;
  assign csr_hw2reg.irq_status.err_i1_termination.de = dp_error.err_i1_termination;
  assign csr_hw2reg.irq_status.err_id_illegal_instr.de = dp_error.err_id_illegal_instr;
  assign csr_hw2reg.irq_status.err_i0_of.de = dp_error.err_i0_of;
  assign csr_hw2reg.irq_status.err_i0_uf.de = dp_error.err_i0_uf;
  assign csr_hw2reg.irq_status.err_i0_nx.de = dp_error.err_i0_nx;
  assign csr_hw2reg.irq_status.err_i1_of.de = dp_error.err_i1_of;
  assign csr_hw2reg.irq_status.err_i1_uf.de = dp_error.err_i1_uf;
  assign csr_hw2reg.irq_status.err_i1_nx.de = dp_error.err_i1_nx;
  assign csr_hw2reg.irq_status.err_madd_op_of.de = dp_error.err_madd_op_of;
  assign csr_hw2reg.irq_status.err_madd_op_uf.de = dp_error.err_madd_op_uf;
  assign csr_hw2reg.irq_status.err_madd_op_nx.de = dp_error.err_madd_op_nx;
  assign csr_hw2reg.irq_status.err_madd_op_nv.de = dp_error.err_madd_op_nv;
  assign csr_hw2reg.irq_status.err_sumr_op_of.de = dp_error.err_sumr_op_of;
  assign csr_hw2reg.irq_status.err_sumr_op_nx.de = dp_error.err_sumr_op_nx;
  assign csr_hw2reg.irq_status.err_sumr_op_nv.de = dp_error.err_sumr_op_nv;
  assign csr_hw2reg.irq_status.err_sfu_op_of.de = dp_error.err_sfu_op_of;
  assign csr_hw2reg.irq_status.err_sfu_op_uf.de = dp_error.err_sfu_op_uf;
  assign csr_hw2reg.irq_status.err_sfu_op_nx.de = dp_error.err_sfu_op_nx;
  assign csr_hw2reg.irq_status.err_sfu_op_nv.de = dp_error.err_sfu_op_nv;
  assign csr_hw2reg.irq_status.err_sfu_op_zr.de = dp_error.err_sfu_op_zr;
  assign csr_hw2reg.irq_status.err_o_of.de = dp_error.err_o_of;
  assign csr_hw2reg.irq_status.err_o_uf.de = dp_error.err_o_uf;
  assign csr_hw2reg.irq_status.err_o_nx.de = dp_error.err_o_nx;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.de = csr_reg2hw.dp_ctrl.dbg_sw_irq.q;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.de = cmdblk_cmd_dropped;

  // Combine all enabled IRQs to a single IRQ
  assign o_irq = |(csr_reg2hw.irq_status & csr_reg2hw.irq_en);

  //--------------------------------------------------
  // Hardware Capability
  //--------------------------------------------------
  assign csr_hw2reg.hw_capability.cmd_fifo_depth.d = CMDB_FIFO_DEPTH;
  assign csr_hw2reg.hw_capability.instr_mem_depth.d = PRG_MEM_DEPTH;

  //--------------------------------------------------
  // CMD Block
  //--------------------------------------------------
  localparam longint CommandEndpointSize = REGION_END_ADDR[dpu_pkg::DPU_IDX_CMDB] - REGION_ST_ADDR[dpu_pkg::DPU_IDX_CMDB] + 1;

  cmdblock #(
    .IDW(AxiLpSubIdW),
    .AW (AxiLpLocalAddrW),
    .DW (AxiLpDataW),
    .BW (AxiLpLenW),

    .DYNAMIC_CMD_SIZE(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .NR_TOK_PROD     (NR_TOK_PROD),
    .NR_TOK_CONS     (NR_TOK_CONS),
    .MAX_OUTST_CMDS  (CMDB_MAX_OUTST_CMDS),
    .CMD_CONFIG_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CONFIG_WIDTH),

    .CMD_FIFO_DEPTH(CMDB_FIFO_DEPTH),
    .CMD_FIFO_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CMD_FIFO_WIDTH),

    .NR_FORMATS     (aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .FORMAT_NR_BYTES(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_BYTES),

    .USE_MACRO   (0),
    .DEV_ADDR_CAP(CommandEndpointSize)
  ) u_dpu_cmdblock (
    .i_clk                (i_clk),
    .i_rst_n              (i_rst_n),
    // Sideband
    .exec                 (csr_reg2hw.cmdblk_ctrl.exec_en.q),
    .pointer_rst          (csr_reg2hw.cmdblk_ctrl.ptr_rst.q),
    .cmd_dropped          (cmdblk_cmd_dropped),
    // Status
    .o_stat_state         (csr_hw2reg.cmdblk_status.state.d),
    .stat_wait_token      (csr_hw2reg.cmdblk_status.wait_token.d),
    .stat_cur_pointer     (csr_hw2reg.cmdblk_status.in_word_ptr.d),
    .stat_cur_fifo_count  (csr_hw2reg.cmdblk_status.fifo_cnt.d),
    .stat_nr_outst_cmds   (csr_hw2reg.cmdblk_status.outst_cmds.d),
    .o_stat_pending_tokens(csr_hw2reg.cmdblk_status.pending_tokens.d[NR_TOK_CONS-1:0]),

    // Demuxed read address channel
    .araddr (demux_araddr[AXI_S_IDX_CMD_BLOCK]),
    .arburst(demux_arburst[AXI_S_IDX_CMD_BLOCK]),
    .arid   (demux_arid[AXI_S_IDX_CMD_BLOCK]),
    .arlen  (demux_arlen[AXI_S_IDX_CMD_BLOCK]),
    .arsize (demux_arsize[AXI_S_IDX_CMD_BLOCK]),
    .arvalid(demux_arvalid[AXI_S_IDX_CMD_BLOCK]),
    .arready(demux_arready[AXI_S_IDX_CMD_BLOCK]),
    // Demuxed write address channel
    .awaddr (demux_awaddr[AXI_S_IDX_CMD_BLOCK]),
    .awburst(demux_awburst[AXI_S_IDX_CMD_BLOCK]),
    .awid   (demux_awid[AXI_S_IDX_CMD_BLOCK]),
    .awlen  (demux_awlen[AXI_S_IDX_CMD_BLOCK]),
    .awsize (demux_awsize[AXI_S_IDX_CMD_BLOCK]),
    .awvalid(demux_awvalid[AXI_S_IDX_CMD_BLOCK]),
    .awready(demux_awready[AXI_S_IDX_CMD_BLOCK]),
    // Demuxed write response channel
    .bid    (demux_bid[AXI_S_IDX_CMD_BLOCK]),
    .bresp  (demux_bresp[AXI_S_IDX_CMD_BLOCK]),
    .bvalid (demux_bvalid[AXI_S_IDX_CMD_BLOCK]),
    .bready (demux_bready[AXI_S_IDX_CMD_BLOCK]),
    // Demuxed read data/response channel
    .rdata  (demux_rdata[AXI_S_IDX_CMD_BLOCK]),
    .rid    (demux_rid[AXI_S_IDX_CMD_BLOCK]),
    .rlast  (demux_rlast[AXI_S_IDX_CMD_BLOCK]),
    .rresp  (demux_rresp[AXI_S_IDX_CMD_BLOCK]),
    .rvalid (demux_rvalid[AXI_S_IDX_CMD_BLOCK]),
    .rready (demux_rready[AXI_S_IDX_CMD_BLOCK]),
    // Demuxed write data channel
    .wdata  (demux_wdata[AXI_S_IDX_CMD_BLOCK]),
    .wlast  (demux_wlast[AXI_S_IDX_CMD_BLOCK]),
    .wstrb  (demux_wstrb[AXI_S_IDX_CMD_BLOCK]),
    .wvalid (demux_wvalid[AXI_S_IDX_CMD_BLOCK]),
    .wready (demux_wready[AXI_S_IDX_CMD_BLOCK]),

    // Tokens
    .tok_prod_vld(o_dpu_tok_prod_vld),
    .tok_prod_rdy(i_dpu_tok_prod_rdy),
    .tok_cons_vld(i_dpu_tok_cons_vld),
    .tok_cons_rdy(o_dpu_tok_cons_rdy),
    ///// Timestamp:
    .o_ts_start  (o_ts_start),
    .o_ts_end    (o_ts_end),
    ///// ACD sync:
    .o_acd_sync  (o_acd_sync),
    // Command
    .cmd_done,
    .cmd_data    (packed_cmd_data),
    .cmd_format,
    .cmd_config  (cmd_config),
    .cmd_vld,
    .cmd_rdy
  );
  always_comb
    csr_hw2reg.cmdblk_status.pending_tokens.d[$bits(csr_hw2reg.cmdblk_status.pending_tokens.d)-
                                              1:NR_TOK_CONS] = 0;

  cmdblock_cmd_unpack #(
    .NR_FIELDS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FIELDS),
    .NR_FORMATS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .TOT_WIDTH(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .FIELD_SIZE(aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_SIZES),
    .FIELD_OUTP_IDX(aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_OUTP_IDX),
    .FIELD_DEFAULT_VAL(aic_dp_cmd_gen_pkg::CMD_BLOCK_DEFAULTS),
    .FORMAT_IDX(aic_dp_cmd_gen_pkg::CMD_BLOCK_FORMAT_IDX)
  ) i_cmd_unpack (
    .format(cmd_format),
    .inp   (packed_cmd_data),
    .outp  (cmd_data)
  );


  //--------------------------------------------------
  // DPcmd Gen
  //--------------------------------------------------
  localparam longint MemoryEndpointSize = REGION_END_ADDR[dpu_pkg::DPU_IDX_IMEM] - REGION_ST_ADDR[dpu_pkg::DPU_IDX_IMEM] + 1;

  if (MemoryEndpointSize * 8 < dpu_pkg::PRG_MEM_DEPTH * $bits(dpu_pkg::dpu_dp_cmd_t))
    $fatal(
        1,
        "Parameter: 'REGION_*_ADDR[dpu_pkg::DPU_IDX_IMEM]' is not large enough to access configured memory;"
    );

  aic_dp_cmd_gen #(
    .AxiIdWidth              (AxiLpSubIdW),
    .AxiAddrWidth            (AxiLpLocalAddrW),
    .AxiDataWidth            (AxiLpDataW),
    .AxiEndpointStart        (AxiLpLocalAddrW'(REGION_ST_ADDR[dpu_pkg::DPU_IDX_IMEM])),
    .AxiEndpointSize         (AxiLpLocalAddrW'(MemoryEndpointSize)),
    .dp_command_t            (dpu_pkg::dpu_dp_cmd_t),
    .DpCommandMemoryDepth    (dpu_pkg::PRG_MEM_DEPTH),
    .DpCommandMemoryDataAlign(32),
    .UseMemoryMacro          (dpu_pkg::USE_IMEM_MACRO)
  ) u_dpu_dpcmd_gen (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_test_mode(i_sram_impl.se),

    .i_cmdb_command(cmd_data),
    .i_cmdb_format(aic_dp_cmd_gen_pkg::cmd_format_e'(cmd_format)),
    .i_cmdb_config(cmd_config),
    .i_cmdb_valid(cmd_vld),
    .o_cmdb_ready(cmd_rdy),
    .o_cmdb_done(cmd_done),

    .i_axi_s_aw_id(demux_awid[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_addr(demux_awaddr[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_len(demux_awlen[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_size(demux_awsize[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_burst(demux_awburst[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_valid(demux_awvalid[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_aw_ready(demux_awready[AXI_S_IDX_DPCMD_GEN]),

    .i_axi_s_w_data (demux_wdata[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_w_strb (demux_wstrb[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_w_last (demux_wlast[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_w_valid(demux_wvalid[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_w_ready(demux_wready[AXI_S_IDX_DPCMD_GEN]),

    .o_axi_s_b_id(demux_bid[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_b_resp(demux_bresp[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_b_valid(demux_bvalid[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_b_ready(demux_bready[AXI_S_IDX_DPCMD_GEN]),

    .i_axi_s_ar_id(demux_arid[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_addr(demux_araddr[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_len(demux_arlen[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_size(demux_arsize[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_burst(demux_arburst[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_valid(demux_arvalid[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_ar_ready(demux_arready[AXI_S_IDX_DPCMD_GEN]),

    .o_axi_s_r_id(demux_rid[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_data(demux_rdata[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_resp(demux_rresp[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_last(demux_rlast[AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_valid(demux_rvalid[AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_r_ready(demux_rready[AXI_S_IDX_DPCMD_GEN]),

    .o_dp_command_data(dpcmd_data),
    .o_dp_command_metadata(dpcmd_metadata), // ASO-UNUSED_VARIABLE : Not all metadata fields are used.
    .o_dp_command_iterations(dpcmd_iterations), // ASO-UNUSED_VARIABLE : Not all iteration fields are used.
    .o_dp_command_last(dpcmd_last),
    .o_dp_command_valid(dpcmd_valid),
    .i_dp_command_ready(dpcmd_ready),

    .i_dp_done(dp_done),

    .o_errors(),  // TODO(tiago,europa,silver/gold) - connect IRQ

    .i_ram_impl(sram_impl_inp_daisy[DPU_MACRO_INSTR]),
    .o_ram_impl(sram_impl_oup_daisy[DPU_MACRO_INSTR])
  );


  //--------------------------------------------------
  // Pre-Decode Shim
  //--------------------------------------------------
  // TODO(@stefan.mach): pre-decode shim as its own module??
  // - Handle bypass mode
  // - Translate non-bypass DPC into instructions
  // - Attach vector mode to instructions
  // - Downgrade writes to LAST if not in final iteration

  // Offset/Broadcast
  dpc_offset_bcast_info_t              dpc_offset_bcast_info;
  aic_dp_cmd_gen_pkg::loop_iteration_t offset_bcast_iter;
  logic                                src1_offsettable;
  operand_t                            bc_src1_mask;
  operand_t                            bc_src1_size;
  instr_bcast_info_t                   instr_bcast_info;
  // MVC requires a state "counter" (1 bit)
  logic                                mvc_ctr_q;
  logic                                mvc_ctr_ena;
  always_comb begin : pre_decode_shim
    // By default, just translate DPC into instr by prepending the vector mode
    instruction_data      = {dpcmd_metadata.cfg.vector_mode, dpcmd_data};
    instruction_valid     = dpcmd_valid;
    instruction_last      = dpcmd_last;
    dpcmd_ready           = instruction_ready;
    // Just extract src2 where the broadcast config is for ops that use it
    dpc_offset_bcast_info = dpc_offset_bcast_info_t'(dpcmd_data.src2);
    // Select the correct loop metadata
    unique case (dpc_offset_bcast_info.loop_sel)
      MAIN:    offset_bcast_iter = dpcmd_iterations.main;
      NESTED0: offset_bcast_iter = dpcmd_iterations.main;
      NESTED1: offset_bcast_iter = dpcmd_iterations.main;
      default: offset_bcast_iter = '0;  // default for illegal choices
    endcase
    // Offset doesn't apply to stream sources
    src1_offsettable = dpcmd_data.src1 inside {A_PREFIX, BC_PREFIX};
    bc_src1_mask     = dpcmd_data.src1 inside {A_PREFIX} ? A_MASK : BC_MASK;
    bc_src1_size     = dpcmd_data.src1 inside {A_PREFIX} ? A_DEPTH : B_DEPTH;  // c same as b
    // Broadcast information to be put in src2 of supported ops, off by default
    instr_bcast_info = '{bcast_enable: 1'b0, bcast_index: '0};
    // By default, MVC counter holds its value and is off
    mvc_ctr_ena      = 1'b0;
    // Handle DP commands which require translation / changes
    if (dpcmd_metadata.format == aic_dp_cmd_gen_pkg::Bypass) begin
      // Bypass: emit the canonical bypass instruction
      instruction_data = {dpcmd_metadata.cfg.vector_mode, CANONICAL_BYPASS_DPC};
    end else begin
      // All writes to the output stream with TLAST set are downgraded to regular pushes unless the
      // DP command is emitted for the last time in the program (i.e. in the very last iteration)
      if (!dpcmd_iterations.overall_last && dpcmd_data.dst inside {S1_PREFIX}) begin
        instruction_data.dst ^= (S1_MASK ^ S0_MASK);
      end
      // Translate VM-dependent integer format to either INT or INTW for the datapath
      // TODO(@stefan.mach): this probably overwrites fields for operations that don't have src
      // TODO(@stefan.mach): therefore this is better happen in the decode itself -> do it there, the spec is dumb
      // if (dpcmd_metadata.cfg.vector_mode) begin
      //   if (dpcmd_data.src0 inside {S0_PREFIX, S1_PREFIX} && dpcmd_data.src0.as_str.fmt == FMT_INT) begin
      //     instruction_data.src0.as_str.fmt = FMT_INTW;
      //   end
      //   if (dpcmd_data.src1 inside {S0_PREFIX, S1_PREFIX} && dpcmd_data.src1.as_str.fmt == FMT_INT) begin
      //     instruction_data.src1.as_str.fmt = FMT_INTW;
      //   end
      //   if (dpcmd_data.src2 inside {S0_PREFIX, S1_PREFIX} && dpcmd_data.src2.as_str.fmt == FMT_INT) begin
      //     instruction_data.src2.as_str.fmt = FMT_INTW;
      //   end
      //   if (dpcmd_data.dst inside {S0_PREFIX, S1_PREFIX} && dpcmd_data.dst.as_str.fmt == FMT_INT) begin
      //     instruction_data.dst.as_str.fmt = FMT_INTW;
      //   end
      // end
      // Decide on which opcodes to translate
      unique case (dpcmd_data.opcode)
        // Offset/Broadcast Binary Operations
        OPC_MUL, OPC_ADD, OPC_SUB, OPC_MAX, OPC_MIN, OPC_PRELU, OPC_CMADD: begin
          // The feature is enabled using bit0 in src2, and bit1 switches offset/broadcast
          if (dpc_offset_bcast_info.enable_feature) begin
            if (dpc_offset_bcast_info.bcast_enable) begin
              // Broadcast Mode: src1 = src1 + (loop_ctr // 64) % src1_size
              if (src1_offsettable) begin
                instruction_data.src1 = bc_src1_mask |
                  ((dpcmd_data.src1 + offset_bcast_iter / PW_LEN) % bc_src1_size);
              end
              // Broadcast Mode: src2 = loop_ctr % 64
              instr_bcast_info = '{bcast_enable: 1'b1, bcast_index: offset_bcast_iter % PW_LEN};
            end else begin
              // Offset Mode: src1 = src1 + loop_ctr % src1_size
              instruction_data.src1 = bc_src1_mask |
                  operand_t'((dpcmd_data.src1 + offset_bcast_iter) % bc_src1_size);
            end
          end
          // Insert broadcast info in src2
          instruction_data.src2 = instr_bcast_info;
        end
        // Decode operations that explicitly need translation
        OPC_PSEUDO: begin
          unique case (dpcmd_data.src2)
            // MVC: [mvc c, src] => [mv cl, src; mv ch, src]
            PSEUDO_MVC: begin
              // Depending on mvc_ctr, we emit a move to cl or ch
              instruction_data.opcode = OPC_UNARY;
              instruction_data.src1   = mvc_ctr_q ? FUNC_MVCH : FUNC_MVCL;
              instruction_data.src2   = dpcmd_data.src1;  // Mask information of mvc is in src1
              // Gate downstream instr_last to only trigger on the second of the two ops
              instruction_last        = dpcmd_last & mvc_ctr_q;
              // Stall upstream until both emitted instructions are accepted by the DP
              dpcmd_ready             = instruction_ready & mvc_ctr_q;
              // Increment the counter on a successful handshake
              mvc_ctr_ena             = instruction_valid & instruction_ready;
            end
            // Illegal instructions, but we just feed them through as the DP does the checking
            default: ;
          endcase
        end
        // Defaults apply otherwise
        default: ;
      endcase
    end
  end
  // MVC counter
  // FFL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) mvc_ctr_q <= '0;
    else if (mvc_ctr_ena) mvc_ctr_q <= ~mvc_ctr_q;
  end

  // TODO(tiago,europa,silver) - leftover wires from previous cmdgen implementation
  assign cmdgen_error = '0;
  assign csr_hw2reg.cmdgen_status = '0;

  // DPcmd debug
  assign csr_hw2reg.dbg_observe.dpcmd0_lst.d = dpcmd_last;
  assign csr_hw2reg.dbg_observe.dpcmd0_rdy.d = dpcmd_ready;
  assign csr_hw2reg.dbg_observe.dpcmd0_vld.d = dpcmd_valid;


  //--------------------------------------------------
  // DPU DP
  //--------------------------------------------------
  dpu_dp i_dpu_dp (
    .clk_i              (i_clk),
    .rst_ni             (i_rst_n),
    // DPcmd stream
    .instruction_data_i (instruction_data),
    .instruction_last_i (instruction_last),
    .instruction_valid_i(instruction_valid),
    .instruction_ready_o(instruction_ready),
    // DP done
    .dp_done_o          (dp_done),
    // IAU AXI stream
    .iau_axis_data_i    (i_dpu_iau_axis_s_data),
    .iau_axis_last_i    (i_dpu_iau_axis_s_last),
    .iau_axis_valid_i   (i_dpu_iau_axis_s_valid),
    .iau_axis_ready_o   (o_dpu_iau_axis_s_ready),
    // IFD1 AXI stream
    .ifd1_axis_data_i   (i_dpu_ifd1_axis_s_data),
    .ifd1_axis_last_i   (i_dpu_ifd1_axis_s_last),
    .ifd1_axis_valid_i  (i_dpu_ifd1_axis_s_valid),
    .ifd1_axis_ready_o  (o_dpu_ifd1_axis_s_ready),
    // ODR AXI stream
    .odr_axis_data_o    (o_dpu_odr_axis_m_data),
    .odr_axis_last_o    (o_dpu_odr_axis_m_last),
    .odr_axis_valid_o   (o_dpu_odr_axis_m_valid),
    .odr_axis_ready_i   (i_dpu_odr_axis_m_ready),
    // CSR configuration
    .dp_ctrl_i          (csr_reg2hw.dp_ctrl),
    // State observation
    .dp_status_o        (csr_hw2reg.dp_status),
    // CSR IRQ errors
    .error_irqs_o       (dp_error),
    //Memory SRAM sideband signals
    .sram_impl_b_i      (sram_impl_inp_daisy[DPU_MACRO_B_STORE]),
    .sram_impl_b_o      (sram_impl_oup_daisy[DPU_MACRO_B_STORE]),
    .sram_impl_c_i      (sram_impl_inp_daisy[DPU_MACRO_C_STORE]),
    .sram_impl_c_o      (sram_impl_oup_daisy[DPU_MACRO_C_STORE])
  );

endmodule
