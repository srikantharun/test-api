// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// IAU block top-level module. Integrates the IAU datapath with the IAU DPcmd generator.
// Also includes a CMD block and CSRs for the control path. Through CSR the IAU can be set to
// a SW DPcmd bypass mode, where the IAU datapath is directly controlled via instructions sent
// through the AXI interface to the SW override CMD FIFO. The IAU block top-level module contains
// all relevant interfaces: config AXI-LP, input and output AXIS, token intf, and IRQ.
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

`ifndef IAU_SV
`define IAU_SV

// verilog_lint: waive-start line-length
module iau
  import iau_pkg::*;
#(
  // Token parameters
  localparam int unsigned NrTokProd = token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_PROD,
  localparam int unsigned NrTokCons = token_mgr_mapping_aic_pkg::TOK_MGR_M_IAU_NR_TOK_CONS,
  // Bitwidth parameters
  localparam int unsigned InWordDw = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE,
  localparam int unsigned OutWordDw = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH / aic_common_pkg::AIC_PWORD_SIZE,
  localparam int unsigned PWordSize = aic_common_pkg::AIC_PWORD_SIZE,
  localparam int unsigned AxiSIW = aic_common_pkg::AIC_PWORD_I26_AXIS_TDATA_WIDTH,
  localparam int unsigned AxiSOW = aic_common_pkg::AIC_PWORD_I32_AXIS_TDATA_WIDTH,
  //localparam int unsigned AXIS_ISW    = AxiSIW / 8,
  //localparam int unsigned AXIS_OSW    = AxiSOW / 8,
  localparam int unsigned AxiIdW = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH,
  localparam int unsigned AxiAw = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH,
  localparam int unsigned AxiDw = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH,
  localparam int unsigned AxiLw = aic_common_pkg::AIC_LT_AXI_LEN_WIDTH,
  localparam int unsigned AxiSzw = aic_common_pkg::AIC_LT_AXI_SIZE_WIDTH,
  localparam int unsigned AxiBw = aic_common_pkg::AIC_LT_AXI_BURST_TYPE_WIDTH,
  // CMD parameters
  localparam int unsigned CmdbMaxOutStCmds = aic_common_pkg::AIC_GEN_CMDB_MAX_OUTST_CMDS,
  localparam int unsigned CmdbFifoDepth = aic_common_pkg::AIC_GEN_CMDB_CMD_FIFO_DEPTH,
  // Observation parameters
  localparam int unsigned ObsW = aic_common_pkg::AIC_DEV_OBS_DW,
  // Block identification parameters
  localparam int unsigned CidW = aic_common_pkg::AIC_CID_SUB_W,
  localparam int unsigned BlockIdW = aic_common_pkg::AIC_BLOCK_ID_WIDTH,

  // default address regions for CSR, CMD, and PRG:
  parameter longint REGION_ST_ADDR[3]  = {64'h0000_0000_0000_0000, 64'h0000_0000_0000_1000, 64'h0000_0000_0000_8000},
  parameter longint REGION_END_ADDR[3] = {64'h0000_0000_0000_0fff, 64'h0000_0000_0000_1fff, 64'h0000_0000_0000_ffff}
) (
  input wire i_clk,
  input wire i_rst_n,

  //// AXI subordinate
  // Write Address Channel
  input  logic [ AxiIdW-1:0] i_axi_s_awid,
  input  logic [  AxiAw-1:0] i_axi_s_awaddr,
  input  logic [  AxiLw-1:0] i_axi_s_awlen,
  input  logic [ AxiSzw-1:0] i_axi_s_awsize,
  input  logic [  AxiBw-1:0] i_axi_s_awburst,
  input  logic               i_axi_s_awvalid,
  output logic               o_axi_s_awready,
  // Read Address Channel
  input  logic [ AxiIdW-1:0] i_axi_s_arid,
  input  logic [  AxiAw-1:0] i_axi_s_araddr,
  input  logic [  AxiLw-1:0] i_axi_s_arlen,
  input  logic [ AxiSzw-1:0] i_axi_s_arsize,
  input  logic [  AxiBw-1:0] i_axi_s_arburst,
  input  logic               i_axi_s_arvalid,
  output logic               o_axi_s_arready,
  // Write  Data Channel
  input  logic [  AxiDw-1:0] i_axi_s_wdata,
  input  logic [AxiDw/8-1:0] i_axi_s_wstrb,
  input  logic               i_axi_s_wlast,
  input  logic               i_axi_s_wvalid,
  output logic               o_axi_s_wready,
  // Read Data Channel
  output logic [ AxiIdW-1:0] o_axi_s_rid,
  output logic [  AxiDw-1:0] o_axi_s_rdata,
  output logic [        1:0] o_axi_s_rresp,
  output logic               o_axi_s_rlast,
  output logic               o_axi_s_rvalid,
  input  logic               i_axi_s_rready,
  // Write Response Channel
  output logic [ AxiIdW-1:0] o_axi_s_bid,
  output logic [        1:0] o_axi_s_bresp,
  output logic               o_axi_s_bvalid,
  input  logic               i_axi_s_bready,

  //// Token System
  output logic [NrTokProd-1:0] o_iau_tok_prod_vld,
  input  logic [NrTokProd-1:0] i_iau_tok_prod_rdy,
  input  logic [NrTokCons-1:0] i_iau_tok_cons_vld,
  output logic [NrTokCons-1:0] o_iau_tok_cons_rdy,

  //// AXIS subordinate
  input  logic              i_axis_s_tvalid,
  input  logic [AxiSIW-1:0] i_axis_s_tdata,
  input  logic              i_axis_s_tlast,
  output logic              o_axis_s_tready,

  //// AXIS manager
  output logic              o_axis_m_tvalid,
  output logic [AxiSOW-1:0] o_axis_m_tdata,
  output logic              o_axis_m_tlast,
  input  logic              i_axis_m_tready,

  //// IRQ
  output logic o_irq,

  //// Observation
  output logic [ObsW-1:0] o_obs,

  ///// Timestamp:
  output logic o_ts_start,
  output logic o_ts_end,
  ///// ACD sync:
  output logic o_acd_sync,

  //// Block Identification
  input logic [    CidW-1:0] i_cid,
  input logic [BlockIdW-1:0] i_block_id,

  /// For scan mode
  input logic i_scan_en
);

  //// AXI Demux
  // Write Address Channel
  logic [IAU_AXI_S_COUNT-1:0][AxiIdW-1:0] awid_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiAw-1:0] awaddr_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiLw-1:0] awlen_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiSzw-1:0] awsize_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiBw-1:0] awburst_s;
  logic [IAU_AXI_S_COUNT-1:0]awvalid_s;
  logic [IAU_AXI_S_COUNT-1:0]awready_s;
  // Read Address Channel
  logic [IAU_AXI_S_COUNT-1:0][AxiIdW-1:0] arid_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiAw-1:0] araddr_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiLw-1:0] arlen_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiSzw-1:0] arsize_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiBw-1:0] arburst_s;
  logic [IAU_AXI_S_COUNT-1:0]arvalid_s;
  logic [IAU_AXI_S_COUNT-1:0]arready_s;
  // Write  Data Channel
  logic [IAU_AXI_S_COUNT-1:0][AxiDw-1:0] wdata_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiDw/8-1:0] wstrb_s;
  logic [IAU_AXI_S_COUNT-1:0]wlast_s;
  logic [IAU_AXI_S_COUNT-1:0]wvalid_s;
  logic [IAU_AXI_S_COUNT-1:0]wready_s;
  // Read Data Channel
  logic [IAU_AXI_S_COUNT-1:0][AxiIdW-1:0] rid_s;
  logic [IAU_AXI_S_COUNT-1:0][AxiDw-1:0] rdata_s;
  logic [IAU_AXI_S_COUNT-1:0][1:0] rresp_s;
  logic [IAU_AXI_S_COUNT-1:0]rlast_s;
  logic [IAU_AXI_S_COUNT-1:0]rvalid_s;
  logic [IAU_AXI_S_COUNT-1:0]rready_s;
  // Write Response Channel
  logic [IAU_AXI_S_COUNT-1:0][AxiIdW-1:0] bid_s;
  logic [IAU_AXI_S_COUNT-1:0][1:0] bresp_s;
  logic [IAU_AXI_S_COUNT-1:0]bvalid_s;
  logic [IAU_AXI_S_COUNT-1:0]bready_s;

  //// CSRs
  // CSR AXI interface
  iau_csr_reg_pkg::axi_a_ch_h2d_t csr_axi_aw;
  logic csr_axi_awready;
  iau_csr_reg_pkg::axi_a_ch_h2d_t csr_axi_ar;
  logic csr_axi_arready;
  iau_csr_reg_pkg::axi_w_ch_h2d_t csr_axi_w;
  logic csr_axi_wready;
  iau_csr_reg_pkg::axi_r_ch_d2h_t csr_axi_r;
  logic csr_axi_rready;
  iau_csr_reg_pkg::axi_b_ch_d2h_t csr_axi_b;
  logic csr_axi_bready;

  // CSR HW interface
  iau_csr_reg_pkg::iau_csr_reg2hw_t csr_reg2hw;
  iau_csr_reg_pkg::iau_csr_hw2reg_t csr_hw2reg;

  // Error signals
  logic err_act_stream_in;
  logic err_act_stream_out;
  logic err_early_tlast_stream_in;
  logic err_early_tlast_stream_out;
  logic err_prg_segfault;
  logic err_prg_len_zero;
  logic err_loop_iter_zero;
  logic err_illegal_rfs_instr;
  logic dbg_sw_interrupt;
  logic cmdblk_cmd_dropped;

  //// CMD Block
  logic                            cmd_done;
  logic                            dp_done;
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   cmd_data_packed;
  aic_dp_cmd_gen_pkg::cmdb_cmd_t   cmd_data_unpacked;
  aic_dp_cmd_gen_pkg::cmd_format_t cmd_format;
  aic_dp_cmd_gen_pkg::cmd_config_t cmd_config;
  logic                            cmd_vld;
  logic                            cmd_rdy;

  //// IAU DPcmd Gen
  iau_dp_cmd_t dpcmd_tdata;
  logic dpcmd_tlast;
  logic dpcmd_tvalid;
  logic dpcmd_tready;

  //--------------------------------------------------
  // DPcmd Gen / Shim
  //--------------------------------------------------
  iau_dp_cmd_t                          dpcmd_shim_data;
  aic_dp_cmd_gen_pkg::metadata_t        dpcmd_shim_metadata;
  aic_dp_cmd_gen_pkg::loop_iterations_t dpcmd_shim_iterations;
  logic                                 dpcmd_shim_last;
  logic                                 dpcmd_shim_valid;
  logic                                 dpcmd_shim_ready;

  /////////////
  logic [$clog2(IAU_AXI_S_COUNT+1)-1:0] bus_sel_rd;
  logic [$clog2(IAU_AXI_S_COUNT+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AxiAw),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(IAU_AXI_S_COUNT),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_wr (
    .addr_in(i_axi_s_awaddr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AxiAw),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(IAU_AXI_S_COUNT),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_rd (
    .addr_in(i_axi_s_araddr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI Demux
  simple_axi_demux #(
    .NR_MASTERS(IAU_AXI_S_COUNT),
    .IDW(AxiIdW),
    .AW(AxiAw),
    .DW(AxiDw),
    .BW(AxiLw),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(8),
    .EXT_SEL(1)
  ) i_iau_axi_demux (
    .i_clk      (i_clk),
    .i_rst_n    (i_rst_n),
    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),
    //// AXI subordinate
    // Write Address Channel
    .s_awid   (i_axi_s_awid),
    .s_awaddr (i_axi_s_awaddr),
    .s_awlen  (i_axi_s_awlen),
    .s_awsize (i_axi_s_awsize),
    .s_awburst(i_axi_s_awburst),
    .s_awlock ('0),
    .s_awprot ('0),
    .s_awcache('0),
    .s_awvalid(i_axi_s_awvalid),
    .s_awready(o_axi_s_awready),
    // Read Address Channel
    .s_arid   (i_axi_s_arid),
    .s_araddr (i_axi_s_araddr),
    .s_arlen  (i_axi_s_arlen),
    .s_arsize (i_axi_s_arsize),
    .s_arburst(i_axi_s_arburst),
    .s_arlock ('0),
    .s_arprot ('0),
    .s_arcache('0),
    .s_arvalid(i_axi_s_arvalid),
    .s_arready(o_axi_s_arready),
    // Write  Data Channel
    .s_wdata  (i_axi_s_wdata),
    .s_wstrb  (i_axi_s_wstrb),
    .s_wlast  (i_axi_s_wlast),
    .s_wvalid (i_axi_s_wvalid),
    .s_wready (o_axi_s_wready),
    // Read Data Channel
    .s_rid    (o_axi_s_rid),
    .s_rdata  (o_axi_s_rdata),
    .s_rresp  (o_axi_s_rresp),
    .s_rlast  (o_axi_s_rlast),
    .s_rvalid (o_axi_s_rvalid),
    .s_rready (i_axi_s_rready),
    // Write Response Channel
    .s_bid    (o_axi_s_bid),
    .s_bresp  (o_axi_s_bresp),
    .s_bvalid (o_axi_s_bvalid),
    .s_bready (i_axi_s_bready),
    //// AXI manager
    // Write Address Channel
    .m_awid   (awid_s),
    .m_awaddr (awaddr_s),
    .m_awlen  (awlen_s),
    .m_awsize (awsize_s),
    .m_awburst(awburst_s),
    .m_awlock (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awprot (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awcache(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_awvalid(awvalid_s),
    .m_awready(awready_s),
    // Read Address Channel
    .m_arid   (arid_s),
    .m_araddr (araddr_s),
    .m_arlen  (arlen_s),
    .m_arsize (arsize_s),
    .m_arburst(arburst_s),
    .m_arlock (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arprot (), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arcache(), // ASO-UNUSED_OUTPUT : Not used AXI protocol feature
    .m_arvalid(arvalid_s),
    .m_arready(arready_s),
    // Write  Data Channel
    .m_wdata  (wdata_s),
    .m_wstrb  (wstrb_s),
    .m_wlast  (wlast_s),
    .m_wvalid (wvalid_s),
    .m_wready (wready_s),
    // Read Resp Channel
    .m_rid    (rid_s),
    .m_rdata  (rdata_s),
    .m_rresp  (rresp_s),
    .m_rlast  (rlast_s),
    .m_rvalid (rvalid_s),
    .m_rready (rready_s),
    // Write Resp Channel
    .m_bid    (bid_s),
    .m_bresp  (bresp_s),
    .m_bvalid (bvalid_s),
    .m_bready (bready_s)
  );

  /////////////
  // CSRs
  iau_csr_reg_top i_iau_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    // Interface: APB
    .axi_aw_i   (csr_axi_aw),
    .axi_awready(csr_axi_awready),
    .axi_ar_i   (csr_axi_ar),
    .axi_arready(csr_axi_arready),
    .axi_w_i    (csr_axi_w),
    .axi_wready (csr_axi_wready),
    .axi_r_o    (csr_axi_r),
    .axi_rready (csr_axi_rready),
    .axi_b_o    (csr_axi_b),
    .axi_bready (csr_axi_bready),
    // Interface: CSR <=> HW
    .reg2hw     (csr_reg2hw),
    .hw2reg     (csr_hw2reg),
    // Config
    .devmode_i  (1'b1)
  );

  assign csr_axi_aw.id = awid_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_aw.addr = awaddr_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_aw.len = awlen_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_aw.size = awsize_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_aw.burst = awburst_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_aw.valid = awvalid_s[IAU_AXI_S_IDX_CSR];
  assign awready_s[IAU_AXI_S_IDX_CSR] = csr_axi_awready;

  assign csr_axi_ar.id = arid_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_ar.addr = araddr_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_ar.len = arlen_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_ar.size = arsize_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_ar.burst = arburst_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_ar.valid = arvalid_s[IAU_AXI_S_IDX_CSR];
  assign arready_s[IAU_AXI_S_IDX_CSR] = csr_axi_arready;

  assign csr_axi_w.data = wdata_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_w.strb = wstrb_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_w.last = wlast_s[IAU_AXI_S_IDX_CSR];
  assign csr_axi_w.valid = wvalid_s[IAU_AXI_S_IDX_CSR];
  assign wready_s[IAU_AXI_S_IDX_CSR] = csr_axi_wready;

  assign rid_s[IAU_AXI_S_IDX_CSR] = csr_axi_r.id;
  assign rdata_s[IAU_AXI_S_IDX_CSR] = csr_axi_r.data;
  assign rresp_s[IAU_AXI_S_IDX_CSR] = csr_axi_r.resp;
  assign rlast_s[IAU_AXI_S_IDX_CSR] = csr_axi_r.last;
  assign rvalid_s[IAU_AXI_S_IDX_CSR] = csr_axi_r.valid;
  assign csr_axi_rready = rready_s[IAU_AXI_S_IDX_CSR];

  assign bid_s[IAU_AXI_S_IDX_CSR] = csr_axi_b.id;
  assign bresp_s[IAU_AXI_S_IDX_CSR] = csr_axi_b.resp;
  assign bvalid_s[IAU_AXI_S_IDX_CSR] = csr_axi_b.valid;
  assign csr_axi_bready = bready_s[IAU_AXI_S_IDX_CSR];

  /////////////
  // IRQs

  // HW can only set the status to high
  assign csr_hw2reg.irq_status.err_act_stream_in.d = 1'b1;
  assign csr_hw2reg.irq_status.err_act_stream_out.d = 1'b1;
  assign csr_hw2reg.irq_status.err_early_tlast_stream_in.d = 1'b1;
  assign csr_hw2reg.irq_status.err_early_tlast_stream_out.d = 1'b1;
  assign csr_hw2reg.irq_status.err_prg_segfault.d = 1'b1;
  assign csr_hw2reg.irq_status.err_prg_len_zero.d = 1'b1;
  assign csr_hw2reg.irq_status.err_loop_iter_zero.d = 1'b1;
  assign csr_hw2reg.irq_status.err_illegal_rfs_instr.d = 1'b1;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.d = 1'b1;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.d = 1'b1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  assign csr_hw2reg.irq_status.err_act_stream_in.de = err_act_stream_in;
  assign csr_hw2reg.irq_status.err_act_stream_out.de = err_act_stream_out;
  assign csr_hw2reg.irq_status.err_early_tlast_stream_in.de = err_early_tlast_stream_in;
  assign csr_hw2reg.irq_status.err_early_tlast_stream_out.de = err_early_tlast_stream_out;
  assign csr_hw2reg.irq_status.err_prg_segfault.de = err_prg_segfault;
  assign csr_hw2reg.irq_status.err_prg_len_zero.de = err_prg_len_zero;
  assign csr_hw2reg.irq_status.err_loop_iter_zero.de = err_loop_iter_zero;
  assign csr_hw2reg.irq_status.err_illegal_rfs_instr.de = err_illegal_rfs_instr;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.de = dbg_sw_interrupt;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.de = cmdblk_cmd_dropped;

  // Combine all IRQs to a single IRQ
  assign o_irq = |(csr_reg2hw.irq_status & csr_reg2hw.irq_en);

  // Connect the DBG_SW_IRQ to the error signal
  assign dbg_sw_interrupt = csr_reg2hw.dp_ctrl.dbg_sw_irq.q;

  /////////////
  // Hardware Capability
  assign csr_hw2reg.hw_capability.cmd_fifo_depth.d = CmdbFifoDepth;
  assign csr_hw2reg.hw_capability.instr_mem_depth.d = IAU_PRG_MEM_DEPTH;

  /////////////
  // IAU CMD Block
  localparam longint CommandEndpointSize = REGION_END_ADDR[iau_pkg::IAU_AXI_S_IDX_CMD_BLOCK]
                                         - REGION_ST_ADDR[iau_pkg::IAU_AXI_S_IDX_CMD_BLOCK] + 1;
  cmdblock #(
    .IDW(AxiIdW),
    .AW (AxiAw),
    .DW (AxiDw),
    .BW (AxiLw),

    .DYNAMIC_CMD_SIZE(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .NR_TOK_PROD     (NrTokProd),
    .NR_TOK_CONS     (NrTokCons),
    .MAX_OUTST_CMDS  (CmdbMaxOutStCmds),
    .CMD_CONFIG_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CONFIG_WIDTH),

    .CMD_FIFO_DEPTH(CmdbFifoDepth),
    .CMD_FIFO_WIDTH(aic_dp_cmd_gen_pkg::CMD_BLOCK_CMD_FIFO_WIDTH),

    .USE_MACRO     (0),
    .DEV_ADDR_CAP  (CommandEndpointSize),

    .NR_FORMATS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .FORMAT_NR_BYTES(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_BYTES)
  ) i_iau_cmdblock (
    .i_clk                (i_clk),
    .i_rst_n              (i_rst_n),
    //// Sideband
    .exec               (csr_reg2hw.cmdblk_ctrl.exec_en.q),
    .pointer_rst        (csr_reg2hw.cmdblk_ctrl.ptr_rst.q),
    .cmd_dropped        (cmdblk_cmd_dropped),
    //// Status
    .stat_cur_pointer   (csr_hw2reg.cmdblk_status.in_word_ptr.d),
    .stat_cur_fifo_count(csr_hw2reg.cmdblk_status.fifo_cnt.d),
    .stat_nr_outst_cmds (csr_hw2reg.cmdblk_status.outst_cmds.d),
    .stat_wait_token    (csr_hw2reg.cmdblk_status.wait_token.d),
    .o_stat_state       (csr_hw2reg.cmdblk_status.state.d),
    .o_stat_pending_tokens(csr_hw2reg.cmdblk_status.pending_tokens.d[NrTokCons-1:0]),
    //// AXI subordinate
    // Write Address Channel
    .awid               (awid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .awaddr             (awaddr_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .awlen              (awlen_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .awsize             (awsize_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .awburst            (awburst_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .awvalid            (awvalid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .awready            (awready_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    // Read Address Channel
    .arid               (arid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .araddr             (araddr_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .arlen              (arlen_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .arsize             (arsize_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .arburst            (arburst_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .arvalid            (arvalid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .arready            (arready_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    // Write Data Channel
    .wdata              (wdata_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .wstrb              (wstrb_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .wlast              (wlast_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .wvalid             (wvalid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .wready             (wready_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    // Read Data Channel
    .rid                (rid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .rdata              (rdata_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .rresp              (rresp_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .rlast              (rlast_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .rvalid             (rvalid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .rready             (rready_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    // Write Response Channel
    .bid                (bid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .bresp              (bresp_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .bvalid             (bvalid_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    .bready             (bready_s[IAU_AXI_S_IDX_CMD_BLOCK]),
    //// Tokens
    .tok_prod_vld       (o_iau_tok_prod_vld),
    .tok_prod_rdy       (i_iau_tok_prod_rdy),
    .tok_cons_vld       (i_iau_tok_cons_vld),
    .tok_cons_rdy       (o_iau_tok_cons_rdy),
    ///// Timestamp:
    .o_ts_start         (o_ts_start),
    .o_ts_end           (o_ts_end),
    ///// ACD sync:
    .o_acd_sync         (o_acd_sync),
    //// Command
    .cmd_done           (cmd_done),
    .cmd_data           (cmd_data_packed),
    .cmd_format         (cmd_format),
    .cmd_config         (cmd_config),
    .cmd_vld            (cmd_vld),
    .cmd_rdy            (cmd_rdy)
  );
  always_comb csr_hw2reg.cmdblk_status.pending_tokens.d[$bits(csr_hw2reg.cmdblk_status.pending_tokens.d)-1:NrTokCons] = 0;

  /////////////
  // IAU CMD unpacking
  cmdblock_cmd_unpack #(
    .NR_FIELDS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FIELDS),
    .NR_FORMATS(aic_dp_cmd_gen_pkg::CMD_BLOCK_NUM_FORMATS),
    .TOT_WIDTH(aic_dp_cmd_gen_pkg::CommandBlockCommandWidth),
    .FIELD_SIZE(aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_SIZES),
    .FIELD_OUTP_IDX(aic_dp_cmd_gen_pkg::CMD_BLOCK_FIELD_OUTP_IDX),
    .FIELD_DEFAULT_VAL(aic_dp_cmd_gen_pkg::CMD_BLOCK_DEFAULTS),
    .FORMAT_IDX(aic_dp_cmd_gen_pkg::CMD_BLOCK_FORMAT_IDX)
  ) u_cmd_unpack (
    .format(cmd_format),
    .inp   (cmd_data_packed),
    .outp  (cmd_data_unpacked)
  );

  /////////////
  // IAU DPcmd Gen
  localparam longint MemoryEndpointSize = REGION_END_ADDR[iau_pkg::IAU_AXI_S_IDX_DPCMD_GEN]
                                        - REGION_ST_ADDR[iau_pkg::IAU_AXI_S_IDX_DPCMD_GEN] + 1;
  aic_dp_cmd_gen #(
    .AxiIdWidth              (AxiIdW),
    .AxiAddrWidth            (AxiAw),
    .AxiDataWidth            (AxiDw),
    .AxiEndpointStart        (AxiAw'(REGION_ST_ADDR[iau_pkg::IAU_AXI_S_IDX_DPCMD_GEN])),
    .AxiEndpointSize         (AxiAw'(MemoryEndpointSize)),
    .dp_command_t            (iau_pkg::iau_dp_cmd_t),
    .DpCommandMemoryDepth    (iau_pkg::IAU_PRG_MEM_DEPTH),
    .DpCommandMemoryDataAlign(iau_pkg::IAU_DP_CMD_DW),
    .UseMemoryMacro          (1'b0)
  ) u_iau_dpcmd_gen (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_test_mode(i_scan_en),

    .i_cmdb_command(cmd_data_unpacked),
    .i_cmdb_format(aic_dp_cmd_gen_pkg::cmd_format_e'(cmd_format)),
    .i_cmdb_config(cmd_config),
    .i_cmdb_valid(cmd_vld),
    .o_cmdb_ready(cmd_rdy),
    .o_cmdb_done(cmd_done),

    .i_axi_s_aw_id(awid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_addr(awaddr_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_len(awlen_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_size(awsize_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_burst(awburst_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_aw_valid(awvalid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_aw_ready(awready_s[IAU_AXI_S_IDX_DPCMD_GEN]),

    .i_axi_s_w_data(wdata_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_w_strb(wstrb_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_w_last(wlast_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_w_valid(wvalid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_w_ready(wready_s[IAU_AXI_S_IDX_DPCMD_GEN]),

    .o_axi_s_b_id(bid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_b_resp(bresp_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_b_valid(bvalid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_b_ready(bready_s[IAU_AXI_S_IDX_DPCMD_GEN]),

    .i_axi_s_ar_id(arid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_addr(araddr_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_len(arlen_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_size(arsize_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_burst(arburst_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_ar_valid(arvalid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_ar_ready(arready_s[IAU_AXI_S_IDX_DPCMD_GEN]),

    .o_axi_s_r_id(rid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_data(rdata_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_resp(rresp_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_last(rlast_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .o_axi_s_r_valid(rvalid_s[IAU_AXI_S_IDX_DPCMD_GEN]),
    .i_axi_s_r_ready(rready_s[IAU_AXI_S_IDX_DPCMD_GEN]),

    .o_dp_command_data(dpcmd_shim_data),
    .o_dp_command_metadata(dpcmd_shim_metadata), // ASO-UNUSED_VARIABLE : Not all signals used.
    .o_dp_command_iterations(dpcmd_shim_iterations), // ASO-UNUSED_VARIABLE : Not all signals used
    .o_dp_command_last(dpcmd_shim_last),
    .o_dp_command_valid(dpcmd_shim_valid),
    .i_dp_command_ready(dpcmd_shim_ready),

    .i_dp_done(dp_done),

    .o_errors(), // TODO(manuel.oliveira,europa,silver/gold) - connect IRQ

    .i_ram_impl('{default: 0}),
    .o_ram_impl() // ASO-UNUSED_OUTPUT: IAU does not have macros
  );


  // TODO:(manuel.oliveira, euroap, silver/gold) - Remove csr_hw2reg.cmdgen_status and csr_reg2hw.dp_ctrl.ignore_segfault
  always_comb csr_hw2reg.cmdgen_status = '0;

  always_comb err_prg_segfault   = '0; // TODO(manuel.oliveira, europa, silver/gold) - remove those signals or find something similar in the IBCO
  always_comb err_prg_len_zero   = '0; // TODO(manuel.oliveira, europa, silver/gold) - remove those signals or find something similar in the IBCO
  always_comb err_loop_iter_zero = '0; // TODO(manuel.oliveira, europa, silver/gold) - remove those signals or find something similar in the IBCO

  always_comb begin : proc_dpcmd_tdata_shim_comb
    if(dpcmd_shim_metadata.format == aic_dp_cmd_gen_pkg::Bypass) begin
      dpcmd_tdata = CANONICAL_BYPASS_INSTR;
    end else begin
      dpcmd_tdata = dpcmd_shim_data;
      // Only the last loop iteration of a program is allowed to push to the l0 stream reg
      // (IAU DP pushes to output stream with TLAST set to low if destination is o0 = 4'b1000)
      // (IAU DP pushes to output stream with TLAST set to high if destination is l0 = 4'b1001)
      if (dpcmd_tdata.dst[3]) begin
        if (!dpcmd_shim_iterations.overall_last) begin
          dpcmd_tdata.dst[0] = 1'b0;
        end
      end
    end

    dpcmd_tlast = dpcmd_shim_last;
    dpcmd_tvalid = dpcmd_shim_valid;
    dpcmd_shim_ready = dpcmd_tready;

  end

  assign csr_hw2reg.dbg_observe.dpcmd0_lst.d = dpcmd_tlast;
  assign csr_hw2reg.dbg_observe.dpcmd0_rdy.d = dpcmd_tready;
  assign csr_hw2reg.dbg_observe.dpcmd0_vld.d = dpcmd_tvalid;

  /////////////
  // IAU DP
  iau_dp i_iau_dp (
    .i_clk                         (i_clk),
    .i_rst_n                       (i_rst_n),
    .i_scan_en,
    // CSR configuration
    .csr_signed_operation_i      (csr_reg2hw.dp_ctrl.signed_op.q),
    .csr_saturated_add_i         (csr_reg2hw.dp_ctrl.sat_op.q),
    // DPcmd AXI stream
    .dpcmd_tvalid_i              (dpcmd_tvalid),
    .dpcmd_tdata_i               (dpcmd_tdata),
    .dpcmd_tvector_mode_i        (dpcmd_shim_metadata.cfg.vector_mode),
    .dpcmd_tlast_i               (dpcmd_tlast),
    .dpcmd_tready_o              (dpcmd_tready),
    // DP done
    .dp_done_o                   (dp_done),
    // Input AXI stream
    .in_tvalid_i                 (i_axis_s_tvalid),
    .in_tdata_i                  (i_axis_s_tdata),
    //.in_tstrb_i  (axis_s_tstrb_i ),
    .in_tlast_i                  (i_axis_s_tlast),
    .in_tready_o                 (o_axis_s_tready),
    // Output AXI stream
    .out_tvalid_o                (o_axis_m_tvalid),
    .out_tdata_o                 (o_axis_m_tdata),
    //.out_tstrb_o  (axis_m_tstrb_o ),
    .out_tlast_o                 (o_axis_m_tlast),
    .out_tready_i                (i_axis_m_tready),
    // State observers
    .dp_status_o                 (csr_hw2reg.dp_status),
    // Error signals
    .err_act_in_stream_o         (err_act_stream_in),
    .err_act_out_stream_o        (err_act_stream_out),
    .err_early_tlast_stream_in_o (err_early_tlast_stream_in),
    .err_early_tlast_stream_out_o(err_early_tlast_stream_out),
    .err_illegal_rfs_instr_o     (err_illegal_rfs_instr)
  );

  assign csr_hw2reg.dbg_observe.in0_lst.d = i_axis_s_tlast;
  assign csr_hw2reg.dbg_observe.in0_rdy.d = o_axis_s_tready;
  assign csr_hw2reg.dbg_observe.in0_vld.d = i_axis_s_tvalid;
  assign csr_hw2reg.dbg_observe.out_lst.d = o_axis_m_tlast;
  assign csr_hw2reg.dbg_observe.out_rdy.d = i_axis_m_tready;
  assign csr_hw2reg.dbg_observe.out_vld.d = o_axis_m_tvalid;

  /////////////
  // OBSERVATION PINS
  aic_common_pkg::aic_dev_obs_t iau_obs;
  always_comb iau_obs.state          = csr_hw2reg.cmdblk_status.state.d;
  always_comb iau_obs.token_stall    = csr_hw2reg.cmdblk_status.wait_token.d;
  always_comb iau_obs.dp_instr_stall = cmd_vld & ~cmd_rdy;
  always_comb iau_obs.dp_cmd_stall   = dpcmd_tvalid & ~dpcmd_tready;
  always_comb iau_obs.dp_in0_stall   = i_axis_s_tvalid & ~o_axis_s_tready;
  always_comb iau_obs.dp_in1_stall   = '0; // IAU only has one stream input
  always_comb iau_obs.dp_out_stall   = o_axis_m_tvalid & ~i_axis_m_tready;
  assign o_obs = iau_obs;

  /////////////
  // BLOCK IDENTIFICATION
  assign csr_hw2reg.dbg_id.block_id.d    = i_block_id;
  assign csr_hw2reg.dbg_id.ai_core_id.d  = 8'(i_cid);
  assign csr_hw2reg.dbg_id.hw_revision.d = IAU_HW_REVISION;

endmodule
// verilog_lint: waive-stop line-length

`endif  // IAU_SV
