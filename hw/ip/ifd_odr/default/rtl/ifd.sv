// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of IFD
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _IFD_SV_
`define _IFD_SV_

module ifd #(
  parameter int unsigned IDW = 4,
  parameter int unsigned AW = 36,
  parameter int unsigned AXI_AW = 36,
  parameter int unsigned AXI_DW = 64,
  parameter int unsigned DW = 512,
  parameter int unsigned BW = 6,
  parameter int unsigned L1_LAT = 8,
  parameter logic [ifd_odr_pkg::IFD_ODR_DP_AW-1:0] L1_ST_ADDR = 'h18000000,
  parameter logic [ifd_odr_pkg::IFD_ODR_DP_AW-1:0] L1_END_ADDR = 'h18400000,

  parameter int unsigned NR_TOK_PROD = 3,
  parameter int unsigned NR_TOK_CONS = 3,
  parameter int unsigned MAX_OUTST_CMDS = 3,
  parameter int unsigned CMD_FIFO_DEPTH = 4,
  parameter int unsigned CMD_FIFO_WIDTH = ifd_odr_pkg::IFD_ODR_CMDB_MAX_CMD_DW + NR_TOK_PROD + NR_TOK_CONS,

  parameter int unsigned DEFMEM_DEPTH = 20,

  parameter int unsigned HAS_DECOMP = 0,
  parameter int unsigned HAS_VTRSP = 0,

  // Observation parameters
  parameter int unsigned OBS_W = aic_common_pkg::AIC_DEV_OBS_DW,

  // Block identification parameters
  parameter int unsigned CID_W = aic_common_pkg::AIC_CID_SUB_W,
  parameter int unsigned BLOCK_ID_W = aic_common_pkg::AIC_BLOCK_ID_WIDTH,

  // default address regions for CSR, CMD, and PRG:
  parameter longint REGION_ST_ADDR[3] = {64'h0, 64'h1000, 64'h8000},
  parameter longint REGION_END_ADDR[3] = {64'hfff, 64'h1fff, 64'hffff}
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic scan_en,

  output logic irq,

  ///// AXI slave:
  // Write Address Channel
  input  wire [     IDW-1:0] awid,
  input  wire [  AXI_AW-1:0] awaddr,
  input  wire [      BW-1:0] awlen,
  input  wire [         2:0] awsize,
  input  wire [         1:0] awburst,
  input  wire                awvalid,
  output wire                awready,
  // Read Address Channel
  input  wire [     IDW-1:0] arid,
  input  wire [  AXI_AW-1:0] araddr,
  input  wire [      BW-1:0] arlen,
  input  wire [         2:0] arsize,
  input  wire [         1:0] arburst,
  input  wire                arvalid,
  output wire                arready,
  // Write  Data Channel
  input  wire [  AXI_DW-1:0] wdata,
  input  wire [AXI_DW/8-1:0] wstrb,
  input  wire                wlast,
  input  wire                wvalid,
  output wire                wready,
  // Read Data Channel
  output wire [     IDW-1:0] rid,
  output wire [  AXI_DW-1:0] rdata,
  output wire [         1:0] rresp,
  output wire                rlast,
  output wire                rvalid,
  input  wire                rready,
  // Write Response Channel
  output wire [     IDW-1:0] bid,
  output wire [         1:0] bresp,
  output wire                bvalid,
  input  wire                bready,

  ///// Tokens:
  output wire [NR_TOK_PROD-1:0] tok_prod_vld,
  input  wire [NR_TOK_PROD-1:0] tok_prod_rdy,
  input  wire [NR_TOK_CONS-1:0] tok_cons_vld,
  output wire [NR_TOK_CONS-1:0] tok_cons_rdy,

  ///// MMIO:
  output mmio_pkg::mmio_dmc_ro_req_t mm_req,
  input  mmio_pkg::mmio_dmc_ro_rsp_t mm_rsp,

  ///// AXIS:
  output logic              axis_m_valid,
  input  logic              axis_m_ready,
  output logic [    DW-1:0] axis_m_data,
  output logic              axis_m_last,

  ///// Observation
  output logic [OBS_W-1:0] obs,

  ///// Timestamp:
  output logic o_ts_start,
  output logic o_ts_end,
  ///// ACD sync:
  output logic o_acd_sync,

  ///// Block Identification
  input logic [                           CID_W-1:0] cid,
  input logic [                      BLOCK_ID_W-1:0] block_id,

  input  axe_tcl_sram_pkg::impl_inp_t i_sram_impl,
  output axe_tcl_sram_pkg::impl_oup_t o_sram_impl
);

  import ifd_odr_pkg::*;
  import ifd_csr_reg_pkg::*;
  import aic_common_pkg::AIC_VA_BASE_LSB;
  import aic_common_pkg::AIC_CID_LSB;

  localparam int unsigned DynamicCmdSize = IFD_ODR_CMDB_MAX_CMD_DW;
  localparam int unsigned TotCmdFifoDw = DynamicCmdSize + NR_TOK_PROD + NR_TOK_CONS;

  localparam int unsigned DefmemRowDw = $clog2(DEFMEM_DEPTH);

  axi_a_ch_h2d_t   csr_aw;
  axi_a_ch_h2d_t   csr_ar;
  axi_w_ch_h2d_t   csr_w;
  axi_b_ch_d2h_t   csr_b;
  axi_r_ch_d2h_t   csr_r;
  ifd_csr_reg2hw_t csr_reg2hw;
  ifd_csr_hw2reg_t csr_hw2reg;

  ifd_csr_hw2reg_dp_status_reg_t dp_status, decomp_status, vtrsp_status;

  aic_common_pkg::aic_dev_obs_t ifd_obs;

  logic exec;
  logic pointer_rst;
  logic cmd_done;

  logic dp_done, dp_done_q_vld, dp_done_q_rdy;

  // Data path axis out, IFD DP & Decomp & VTRSP
  logic dp_axis_m_valid[1+HAS_DECOMP+HAS_VTRSP];
  logic dp_axis_m_ready[1+HAS_DECOMP+HAS_VTRSP];
  logic [DW-1:0] dp_axis_m_data[1+HAS_DECOMP+HAS_VTRSP];
  logic dp_axis_m_last[1+HAS_DECOMP+HAS_VTRSP];

  logic [IFD_ODR_AG_DECOMP_EN_DW-1:0] decomp_cmd_data;
  logic decomp_cmd_vld;
  logic decomp_cmd_rdy;
  logic decomp_done;
  logic decomp_done_q_vld, decomp_done_q_rdy;

  logic [1+HAS_DECOMP+HAS_VTRSP-1:0] cmd_vld_cast;
  logic [1+HAS_DECOMP+HAS_VTRSP-1:0] cmd_rdy_cast;

  logic [7:0] stat_cur_pointer;
  logic [7:0] stat_cur_fifo_count;
  logic [7:0] stat_nr_outst_cmds;

  logic vtrsp_access_error;
  logic vtrsp_irq;
  logic vtrsp_done;
  logic vtrsp_done_q_vld, vtrsp_done_q_rdy;

  logic decomp_access_error;
  logic decomp_invalid_stream_header;
  logic decomp_invalid_scheme_header;
  logic decomp_invalid_compressed_size;
  logic decomp_invalid_uncompressed_size;
  logic decomp_fvc_decomp_stuck;

  logic mmio_addr_error;
  logic err_addr_out_of_range;
  logic dbg_sw_interrupt;
  logic cmdblk_cmd_dropped;

  logic [IFD_ODR_CMDB_MAX_CMD_DW-1:0] cmdb_cmd_data;
  logic [IFD_ODR_UNROLL_CMD_DW-1:0] cmd_data_unpacked;
  logic [CMD_FMT_DW-1:0] cmd_format;
  logic cmd_config;
  logic cmd_vld;
  logic cmd_rdy;

  logic [IFD_ODR_UNROLL_CMD_DW-1:0] cmd_unroll_data;
  logic [CMD_FMT_DW-1:0] cmd_unroll_format;
  logic cmd_unroll_config;
  logic cmd_unroll_vld;
  logic cmd_unroll_rdy;

  // AG dp connections
  logic ag_dpc_vld;
  logic ag_dpc_rdy;
  logic [ IFD_ODR_DPC_CMD_DW-1:0] ag_dpc_data;
  logic ag_dpc_config;

  // defmem
  logic defmem_rvld, defmem_rrdy, defmem_resp_vld;
  logic [IFD_ODR_DEFMEM_WIDTH-1:0] defmem_resp_data;
  logic [DefmemRowDw-1:0] defmem_raddr;

  ///// AXI slaves:
  // Write Address Channel
  logic [IFD_ODR_NR_AXI_DEVS-1:0][IDW-1:0] awid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_AW-1:0] awaddr_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_AW-1:0] awaddr_capped_s;  // remove MSB's as slave don't like those
  logic [IFD_ODR_NR_AXI_DEVS-1:0][BW-1:0] awlen_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][2:0] awsize_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][1:0] awburst_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]awvalid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]awready_s;
  // Read Address Channel
  logic [IFD_ODR_NR_AXI_DEVS-1:0][IDW-1:0] arid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_AW-1:0] araddr_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_AW-1:0] araddr_capped_s;  // remove MSB's as slave don't like those
  logic [IFD_ODR_NR_AXI_DEVS-1:0][BW-1:0] arlen_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][2:0] arsize_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][1:0] arburst_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]arvalid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]arready_s;
  // Write  Data Channel
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_DW-1:0] wdata_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_DW/8-1:0] wstrb_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]wlast_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]wvalid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]wready_s;
  // Read Data Channel
  logic [IFD_ODR_NR_AXI_DEVS-1:0][IDW-1:0] rid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][AXI_DW-1:0] rdata_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][1:0] rresp_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]rlast_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]rvalid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]rready_s;
  // Write Response Channel
  logic [IFD_ODR_NR_AXI_DEVS-1:0][IDW-1:0] bid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0][1:0] bresp_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]bvalid_s;
  logic [IFD_ODR_NR_AXI_DEVS-1:0]bready_s;

  // Error signals to CSR
  logic err_illegal_data_conversion;

  logic mmio_error_nc;
  always_comb mmio_error_nc = mm_rsp.payload.error; // ASO-UNUSED_VARIABLE: mmio response error is not used, L1 doesn't do error checking anymore (not needed)

`ifndef IFD_ODR_DPC_RANGE
  `define  IFD_ODR_DPC_RANGE(i)  IFD_ODR_DPC_``i``_LSB+ IFD_ODR_DPC_``i``_DW-1: IFD_ODR_DPC_``i``_LSB
`endif

  // zero assign reserved fields to help spyglass
  assign ag_dpc_data[ IFD_ODR_DPC_ADDR_LSB+ IFD_ODR_DPC_ADDR_FIELD_W-1: IFD_ODR_DPC_ADDR_LSB+ IFD_ODR_DPC_ADDR_DW] =
                {( IFD_ODR_DPC_ADDR_FIELD_W -  IFD_ODR_DPC_ADDR_DW){1'b0}};
  assign ag_dpc_data[ IFD_ODR_DPC_CTRL_LSB+ IFD_ODR_DPC_CTRL_FIELD_W-1: IFD_ODR_DPC_CTRL_LSB+ IFD_ODR_DPC_CTRL_DW] =
                {( IFD_ODR_DPC_CTRL_FIELD_W -  IFD_ODR_DPC_CTRL_DW){1'b0}};
  // no vtrsp cmd needed in ag_dpc_data:
  assign ag_dpc_data[ IFD_ODR_DPC_VTRSP_EN_LSB+: IFD_ODR_DPC_VTRSP_EN_DW] = '0;
  assign ag_dpc_data[ IFD_ODR_DPC_DECOMP_EN_LSB+: IFD_ODR_DPC_DECOMP_EN_DW] = '0;

  ifd_odr_addr_gen #(
    .cmdgen_status_reg_t(ifd_csr_hw2reg_cmdgen_status_reg_t)
  ) u_addr_gen (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    // output
    .dpc_vld(ag_dpc_vld),
    .dpc_rdy(ag_dpc_rdy),
    .dpc_addr(ag_dpc_data[`IFD_ODR_DPC_RANGE(ADDR)]),
    .dpc_msk(ag_dpc_data[`IFD_ODR_DPC_RANGE(MSK)]),
    .dpc_format(ag_dpc_data[`IFD_ODR_DPC_RANGE(FORMAT)]),
    .dpc_config(ag_dpc_config),
    .dpc_pad(ag_dpc_data[`IFD_ODR_DPC_RANGE(PAD)]),
    .dpc_pad_val(ag_dpc_data[`IFD_ODR_DPC_RANGE(PAD_VAL)]),
    .dpc_intra_pad_val(ag_dpc_data[`IFD_ODR_DPC_RANGE(INTRA_PAD_VAL)]),
    .dpc_last(ag_dpc_data[`IFD_ODR_DPC_RANGE(LAST)]),
    .err_addr_out_of_range(err_addr_out_of_range),

    .ag_cmd(cmd_data_unpacked[IFD_ODR_AG_CMD_DW-1:0]),
    .ag_config(cmd_unroll_config),
    .ag_vld(cmd_vld_cast[0]),
    .ag_rdy(cmd_rdy_cast[0]),

    .cmdgen_status(csr_hw2reg.cmdgen_status)
  );

  logic [IFD_ODR_DP_AW-1:0] full_mmio_addr;
  always_comb mm_req.payload.addr = full_mmio_addr[$bits(mm_req.payload.addr)-1:0];
  // mmio address check:
  always_comb mmio_addr_error = mm_req.valid & ((full_mmio_addr >= L1_END_ADDR) | (full_mmio_addr < L1_ST_ADDR));

  ifd_dp #(
    .FIFO_DEPTH(L1_LAT + 2),
    .PWORD64_LEN(IFD_ODR_PWORD64_LEN),
    .PWORD32_LEN(IFD_ODR_PWORD32_LEN),
    .EL_DW(IFD_ODR_EL_DW),
    .EL8_DW(IFD_ODR_EL8_DW),
    .AW(IFD_ODR_DP_AW)
  ) u_dp (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    // DPcmd:
    .dpc_addr(ag_dpc_data[`IFD_ODR_DPC_RANGE(ADDR)]),
    .dpc_pad(ag_dpc_data[`IFD_ODR_DPC_RANGE(PAD)]),
    .dpc_msk(ag_dpc_data[`IFD_ODR_DPC_RANGE(MSK)]),
    .dpc_format(ag_dpc_data[`IFD_ODR_DPC_RANGE(FORMAT)]),
    .dpc_config(ag_dpc_config),
    .dpc_last(ag_dpc_data[`IFD_ODR_DPC_RANGE(LAST)]),
    .dpc_vld(ag_dpc_vld),
    .dpc_rdy(ag_dpc_rdy),
    .dpc_pad_val(ag_dpc_data[`IFD_ODR_DPC_RANGE(PAD_VAL)]),
    .dpc_intra_pad_val(ag_dpc_data[`IFD_ODR_DPC_RANGE(INTRA_PAD_VAL)]),

    // MMIO:
    // req:
    .mm_addr(full_mmio_addr),
    .mm_valid(mm_req.valid),
    .mm_ready(mm_rsp.ready),

    // resp:
    .mm_rdata      (mm_rsp.payload.data),
    .mm_resp_ready (mm_req.rsp_ready),
    .mm_ack        (mm_rsp.ack),

    //AXIS:
    .axis_m_valid(dp_axis_m_valid[0]),
    .axis_m_ready(dp_axis_m_ready[0]),
    .axis_m_data (dp_axis_m_data[0]),
    .axis_m_last (dp_axis_m_last[0]),

    // status and opt config
    .last_rcvd(dp_done),
    .o_err_illegal_data_conv(err_illegal_data_conversion),

    // State observation
    .dp_status(dp_status)
  );

  if(HAS_DECOMP+HAS_VTRSP>0) begin: g_done_sync
    cc_stream_buffer #(
      .DEPTH(MAX_OUTST_CMDS),
      .DW(1)
    ) u_dp_done_buffer (
      .i_clk,
      .i_rst_n,

      .wr_vld(dp_done),
      .wr_data('0),
      .wr_rdy(), // ASO-UNUSED_OUTPUT: not used, can't backpressure

      .rd_rdy(dp_done_q_rdy),
      .rd_data(), // ASO-UNUSED_OUTPUT: not used
      .rd_vld(dp_done_q_vld)
    );

    cc_stream_join #(
      .NumStreams(1+HAS_DECOMP+HAS_VTRSP)
    ) u_done_join (
      .i_select({1'b1, bit'(HAS_DECOMP), bit'(HAS_VTRSP)}),
      .i_valid({dp_done_q_vld, decomp_done_q_vld, vtrsp_done_q_vld}),
      .o_ready({dp_done_q_rdy, decomp_done_q_rdy, vtrsp_done_q_rdy}),
      .o_valid(cmd_done),
      .i_ready(1'b1) // can't backpressure
    );
  end else begin: g_no_done_sync
    always_comb cmd_done = dp_done;
  end

  // command block:
  cmdblock #(
    .IDW(IDW),
    .AW (AXI_AW),
    .DW (AXI_DW),
    .BW (BW),

    .DYNAMIC_CMD_SIZE(DynamicCmdSize),
    .NR_TOK_PROD(NR_TOK_PROD),
    .NR_TOK_CONS(NR_TOK_CONS),
    .MAX_OUTST_CMDS(MAX_OUTST_CMDS),

    .CMD_FIFO_DEPTH(CMD_FIFO_DEPTH),
    .CMD_FIFO_WIDTH(CMD_FIFO_WIDTH),
    .DEV_ADDR_CAP  (REGION_END_ADDR[IFD_ODR_CMDB_S_IDX]-REGION_ST_ADDR[IFD_ODR_CMDB_S_IDX]+1),

    .NR_FORMATS(CMD_NR_FORMATS),
    .FORMAT_NR_BYTES(IFD_ODR_CMDB_FORMAT_NR_BYTES)
  ) u_cmd_block (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    ///// Sideband:
    .exec(exec),
    .pointer_rst(pointer_rst),
    .cmd_dropped(cmdblk_cmd_dropped),

    // status:
    .stat_cur_pointer(stat_cur_pointer),
    .stat_cur_fifo_count(stat_cur_fifo_count),
    .stat_nr_outst_cmds(stat_nr_outst_cmds),
    .stat_wait_token(csr_hw2reg.cmdblk_status.wait_token.d),
    .o_stat_state(csr_hw2reg.cmdblk_status.state.d),
    .o_stat_pending_tokens(csr_hw2reg.cmdblk_status.pending_tokens.d[NR_TOK_CONS-1:0]),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid_s[IFD_ODR_CMDB_S_IDX]),
    .awaddr(awaddr_capped_s[IFD_ODR_CMDB_S_IDX]),
    .awlen(awlen_s[IFD_ODR_CMDB_S_IDX]),
    .awsize(awsize_s[IFD_ODR_CMDB_S_IDX]),
    .awburst(awburst_s[IFD_ODR_CMDB_S_IDX]),
    .awvalid(awvalid_s[IFD_ODR_CMDB_S_IDX]),
    .awready(awready_s[IFD_ODR_CMDB_S_IDX]),
    // Read Address Channel
    .arid(arid_s[IFD_ODR_CMDB_S_IDX]),
    .araddr(araddr_capped_s[IFD_ODR_CMDB_S_IDX]),
    .arlen(arlen_s[IFD_ODR_CMDB_S_IDX]),
    .arsize(arsize_s[IFD_ODR_CMDB_S_IDX]),
    .arburst(arburst_s[IFD_ODR_CMDB_S_IDX]),
    .arvalid(arvalid_s[IFD_ODR_CMDB_S_IDX]),
    .arready(arready_s[IFD_ODR_CMDB_S_IDX]),
    // Write  Data Channel
    .wdata(wdata_s[IFD_ODR_CMDB_S_IDX]),
    .wstrb(wstrb_s[IFD_ODR_CMDB_S_IDX]),
    .wlast(wlast_s[IFD_ODR_CMDB_S_IDX]),
    .wvalid(wvalid_s[IFD_ODR_CMDB_S_IDX]),
    .wready(wready_s[IFD_ODR_CMDB_S_IDX]),
    // Read Data Channel
    .rid(rid_s[IFD_ODR_CMDB_S_IDX]),
    .rdata(rdata_s[IFD_ODR_CMDB_S_IDX]),
    .rresp(rresp_s[IFD_ODR_CMDB_S_IDX]),
    .rlast(rlast_s[IFD_ODR_CMDB_S_IDX]),
    .rvalid(rvalid_s[IFD_ODR_CMDB_S_IDX]),
    .rready(rready_s[IFD_ODR_CMDB_S_IDX]),
    // Write Response Channel
    .bid(bid_s[IFD_ODR_CMDB_S_IDX]),
    .bresp(bresp_s[IFD_ODR_CMDB_S_IDX]),
    .bvalid(bvalid_s[IFD_ODR_CMDB_S_IDX]),
    .bready(bready_s[IFD_ODR_CMDB_S_IDX]),

    ///// Tokens:
    .tok_prod_vld(tok_prod_vld),
    .tok_prod_rdy(tok_prod_rdy),
    .tok_cons_vld(tok_cons_vld),
    .tok_cons_rdy(tok_cons_rdy),

    ///// Timestamp:
    .o_ts_start  (o_ts_start),
    .o_ts_end    (o_ts_end),
    ///// ACD sync:
    .o_acd_sync  (o_acd_sync),

    ///// Command:
    .cmd_done(cmd_done),
    .cmd_data(cmdb_cmd_data),
    .cmd_format(cmd_format),
    .cmd_config(cmd_config), // to be used for int16 feature
    .cmd_vld(cmd_vld),
    .cmd_rdy(cmd_rdy)
  );

  ifd_odr_loop_unroll #(
    .DEFMEM_ROW_DW(DefmemRowDw)
  ) u_loop_unroll (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .cmdb_vld(cmd_vld),
    .cmdb_cmd(cmdb_cmd_data),
    .cmdb_format(cmd_format),
    .cmdb_config(cmd_config),
    .cmdb_rdy(cmd_rdy),

    .ag_vld(cmd_unroll_vld),
    .ag_cmd(cmd_unroll_data),
    .ag_format(cmd_unroll_format),
    .ag_config(cmd_unroll_config),
    .ag_rdy(cmd_unroll_rdy),

    .defmem_raddr(defmem_raddr),
    .defmem_rvld (defmem_rvld),
    .defmem_rrdy (defmem_rrdy),

    .defmem_resp_data(defmem_resp_data),
    .defmem_resp_vld (defmem_resp_vld)
  );

  // CMD unpack, depending on format:
  cmdblock_cmd_unpack #(
    .NR_FIELDS(IFD_ODR_AG_CMD_NR_FIELDS),
    .NR_FORMATS(CMD_NR_FORMATS),
    .TOT_WIDTH(IFD_ODR_UNROLL_CMD_DW),
    .FIELD_SIZE(IFD_ODR_AG_IFD_ODR_CMD_FIELD_SIZES),
    .FIELD_OUTP_IDX(IFD_ODR_CMD_FIELD_LSBS),
    .FIELD_DEFAULT_VAL(IFD_ODR_CMD_FIELD_DEF_VALS),
    .FORMAT_IDX(IFD_ODR_CMD_FORMAT_IDX)
  ) u_cmd_unpack (
    .format(cmd_unroll_format),
    .inp(cmd_unroll_data),
    .outp(cmd_data_unpacked)
  );

  /////////////////////////////////////////////////////////////////////////////////
  cmdblock_str_multicast #(
    .NR_OUTPUTS(1 + HAS_DECOMP + HAS_VTRSP)
  ) u_cast_cmd (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .s_vld(cmd_unroll_vld),
    .s_rdy(cmd_unroll_rdy),

    .m_vld(cmd_vld_cast),
    .m_rdy(cmd_rdy_cast)
  );

  /////// Decompression:
  if (HAS_DECOMP) begin : g_decomp
    assign csr_hw2reg.hw_capability.decomp_present.d = 1'b1;
    assign decomp_access_error = 1'b0;

    // Instantiation of the decompress module.
    decompress i_decomp (
      // Clock and reset signals
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      // =====================================================
      // Inteface to manager AXI-S port
      // =====================================================
      .axis_m_valid(dp_axis_m_valid[0]),
      .axis_m_ready(dp_axis_m_ready[0]),
      .axis_m_data (dp_axis_m_data[0]),
      .axis_m_last (dp_axis_m_last[0]),

      // =====================================================
      // Inteface to subordinate AXI-S port
      // =====================================================
      .axis_s_valid(dp_axis_m_valid[1]),
      .axis_s_ready(dp_axis_m_ready[1]),
      .axis_s_data (dp_axis_m_data[1]),
      .axis_s_last (dp_axis_m_last[1]),

      // =====================================================
      // Inteface to instruction commands
      // =====================================================
      .cmd_valid(cmd_vld_cast[1]),
      .cmd_data (cmd_data_unpacked[IFD_ODR_AG_DECOMP_EN_LSB]),
      .cmd_ready(cmd_rdy_cast[1]),

      // =====================================================
      // State observation
      // =====================================================
      .decomp_status(decomp_status),
      .decomp_invalid_stream_header(decomp_invalid_stream_header),
      .decomp_invalid_scheme_header(decomp_invalid_scheme_header),
      .decomp_invalid_compressed_size(decomp_invalid_compressed_size),
      .decomp_invalid_uncompressed_size(decomp_invalid_uncompressed_size),
      .decomp_fvc_decomp_stuck(decomp_fvc_decomp_stuck)
    );
    always_comb decomp_done = decomp_status.decomp_stream_done;

    cc_stream_buffer #(
      .DEPTH(MAX_OUTST_CMDS),
      .DW(1)
    ) u_decomp_done_buffer (
      .i_clk,
      .i_rst_n,

      .wr_vld(decomp_done),
      .wr_data('0),
      .wr_rdy(), // ASO-UNUSED_OUTPUT: not used,can't backpressure

      .rd_rdy(decomp_done_q_rdy),
      .rd_data(),  // ASO-UNUSED_OUTPUT: not used
      .rd_vld(decomp_done_q_vld)
    );
  end else begin : g_no_decomp
    assign decomp_status = '0;
    assign decomp_invalid_stream_header = 1'b0;
    assign decomp_invalid_scheme_header = 1'b0;
    assign decomp_invalid_compressed_size = 1'b0;
    assign decomp_invalid_uncompressed_size = 1'b0;
    assign decomp_fvc_decomp_stuck = 1'b0;

    assign csr_hw2reg.hw_capability.decomp_present.d = 1'b0;
    assign decomp_access_error = cmd_data_unpacked[IFD_ODR_AG_DECOMP_EN_LSB] & cmd_unroll_vld;

    if (HAS_VTRSP)
      always_comb decomp_done_q_vld = 1'b1;
  end
  /////// VTRSP:
  if (HAS_VTRSP) begin : g_vtrsp
    assign csr_hw2reg.hw_capability.vtrsp_present.d = 1'b1;
    assign vtrsp_access_error = 1'b0;

    // Instantiation of the decompress module.
    vtrsp #(
      .PWORD_LEN(IFD_ODR_PWORD64_LEN),
      .DW(DW),
      .status_t(ifd_csr_reg_pkg::ifd_csr_hw2reg_dp_status_reg_t)
    ) u_vtrsp (
      // Clock and reset signals
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),
      .i_scan_en(scan_en),

      // AXI-Stream Subordinate Interface (incoming data intf)
      .axis_s_tvalid(dp_axis_m_valid[HAS_DECOMP]),
      .axis_s_tready(dp_axis_m_ready[HAS_DECOMP]),
      .axis_s_tdata (dp_axis_m_data[HAS_DECOMP]),
      .axis_s_tlast (dp_axis_m_last[HAS_DECOMP]),

      // AXI-S Subordinate Interface for command (incoming cmd intf)
      .cmd_valid(cmd_vld_cast[1+HAS_DECOMP]),
      .cmd_data (cmd_data_unpacked[IFD_ODR_AG_VTRSP_EN_LSB+:IFD_ODR_AG_VTRSP_EN_DW]),
      .cmd_ready(cmd_rdy_cast[1+HAS_DECOMP]),

      // AXI-Stream Manager Interface (outgoing data intf)
      .axis_m_tvalid(dp_axis_m_valid[1+HAS_DECOMP]),
      .axis_m_tready(dp_axis_m_ready[1+HAS_DECOMP]),
      .axis_m_tdata (dp_axis_m_data[1+HAS_DECOMP]),
      .axis_m_tlast (dp_axis_m_last[1+HAS_DECOMP]),

      // Interrupts
      .vtrsp_irq(vtrsp_irq),

      // Status bus from VTRSP module to be captured in a CSR
      .vtrsp_status
    );

    cc_stream_buffer #(
      .DEPTH(MAX_OUTST_CMDS),
      .DW(1)
    ) u_vrtsp_done_buffer (
      .i_clk,
      .i_rst_n,

      // use last as done signal for the vtrsp:
      .wr_vld(dp_axis_m_valid[1+HAS_DECOMP] & dp_axis_m_ready[1+HAS_DECOMP] & dp_axis_m_last[1+HAS_DECOMP]),
      .wr_data('0),
      .wr_rdy(), // ASO-UNUSED_OUTPUT: not used,can't backpressure

      .rd_rdy(vtrsp_done_q_rdy),
      .rd_data(), // ASO-UNUSED_OUTPUT: not used
      .rd_vld(vtrsp_done_q_vld)
    );
  end else begin : g_no_vtrsp
    assign vtrsp_status = '0;
    assign vtrsp_irq = '0;

    assign csr_hw2reg.hw_capability.vtrsp_present.d = 1'b0;
    assign vtrsp_access_error = (|cmd_data_unpacked[IFD_ODR_AG_VTRSP_EN_LSB+:IFD_ODR_AG_VTRSP_EN_DW]) & cmd_unroll_vld;
    if (HAS_DECOMP)
      always_comb vtrsp_done_q_vld = 1'b1;
  end

  always_comb dp_axis_m_ready[HAS_DECOMP+HAS_VTRSP] = axis_m_ready;
  always_comb {axis_m_data, axis_m_last, axis_m_valid} = {
    dp_axis_m_data[HAS_DECOMP+HAS_VTRSP], dp_axis_m_last[HAS_DECOMP+HAS_VTRSP], dp_axis_m_valid[HAS_DECOMP+HAS_VTRSP]
  };

  /////////////////////////////////////////////////////////////////

  // CSR:
  ifd_csr_reg_top i_ifd_csr (
    .clk_i (i_clk),
    .rst_ni(i_rst_n),

    .axi_aw_i(csr_aw),
    .axi_awready(awready_s[IFD_ODR_CSR_S_IDX]),
    .axi_ar_i(csr_ar),
    .axi_arready(arready_s[IFD_ODR_CSR_S_IDX]),
    .axi_w_i(csr_w),
    .axi_wready(wready_s[IFD_ODR_CSR_S_IDX]),
    .axi_b_o(csr_b),
    .axi_bready(bready_s[IFD_ODR_CSR_S_IDX]),
    .axi_r_o(csr_r),
    .axi_rready(rready_s[IFD_ODR_CSR_S_IDX]),
    // To HW:
    .reg2hw(csr_reg2hw),
    .hw2reg(csr_hw2reg),
    // Config
    .devmode_i(1'b1)
  );

  assign csr_aw.id = awid_s[IFD_ODR_CSR_S_IDX];
  assign csr_aw.addr = awaddr_s[IFD_ODR_CSR_S_IDX];
  assign csr_aw.len = awlen_s[IFD_ODR_CSR_S_IDX];
  assign csr_aw.size = awsize_s[IFD_ODR_CSR_S_IDX];
  assign csr_aw.burst = awburst_s[IFD_ODR_CSR_S_IDX];
  assign csr_aw.valid = awvalid_s[IFD_ODR_CSR_S_IDX];
  assign csr_ar.id = arid_s[IFD_ODR_CSR_S_IDX];
  assign csr_ar.addr = araddr_s[IFD_ODR_CSR_S_IDX];
  assign csr_ar.len = arlen_s[IFD_ODR_CSR_S_IDX];
  assign csr_ar.size = arsize_s[IFD_ODR_CSR_S_IDX];
  assign csr_ar.burst = arburst_s[IFD_ODR_CSR_S_IDX];
  assign csr_ar.valid = arvalid_s[IFD_ODR_CSR_S_IDX];
  assign csr_w.data = wdata_s[IFD_ODR_CSR_S_IDX];
  assign csr_w.strb = wstrb_s[IFD_ODR_CSR_S_IDX];
  assign csr_w.last = wlast_s[IFD_ODR_CSR_S_IDX];
  assign csr_w.valid = wvalid_s[IFD_ODR_CSR_S_IDX];
  assign bid_s[IFD_ODR_CSR_S_IDX] = csr_b.id;
  assign bresp_s[IFD_ODR_CSR_S_IDX] = csr_b.resp;
  assign bvalid_s[IFD_ODR_CSR_S_IDX] = csr_b.valid;
  assign rid_s[IFD_ODR_CSR_S_IDX] = csr_r.id;
  assign rdata_s[IFD_ODR_CSR_S_IDX] = csr_r.data;
  assign rresp_s[IFD_ODR_CSR_S_IDX] = csr_r.resp;
  assign rlast_s[IFD_ODR_CSR_S_IDX] = csr_r.last;
  assign rvalid_s[IFD_ODR_CSR_S_IDX] = csr_r.valid;

  assign csr_hw2reg.cmdblk_status.in_word_ptr.d = stat_cur_pointer;
  assign csr_hw2reg.cmdblk_status.fifo_cnt.d = stat_cur_fifo_count;
  assign csr_hw2reg.cmdblk_status.outst_cmds.d = stat_nr_outst_cmds;
  always_comb csr_hw2reg.cmdblk_status.pending_tokens.d[$bits(csr_hw2reg.cmdblk_status.pending_tokens.d)-1:NR_TOK_CONS] = 0;

  assign csr_hw2reg.dbg_observe.out_lst.d = axis_m_last;
  assign csr_hw2reg.dbg_observe.out_rdy.d = axis_m_ready;
  assign csr_hw2reg.dbg_observe.out_vld.d = axis_m_valid;
  assign csr_hw2reg.dbg_observe.dpcmd0_lst.d = ag_dpc_data[`IFD_ODR_DPC_RANGE(LAST)];
  assign csr_hw2reg.dbg_observe.dpcmd0_rdy.d = ag_dpc_rdy;
  assign csr_hw2reg.dbg_observe.dpcmd0_vld.d = ag_dpc_vld;

  assign csr_hw2reg.dbg_id.block_id.d = block_id;
  assign csr_hw2reg.dbg_id.ai_core_id.d = {(8-CID_W)'(0), cid};
  assign csr_hw2reg.dbg_id.hw_revision.d = IFD_ODR_IFD_HW_REVISION;

  assign csr_hw2reg.dp_status = dp_status | decomp_status | vtrsp_status;

  assign exec = csr_reg2hw.cmdblk_ctrl.exec_en.q;
  assign pointer_rst = csr_reg2hw.cmdblk_ctrl.ptr_rst.q;

  always_comb ifd_obs.state          = csr_hw2reg.cmdblk_status.state.d;
  always_comb ifd_obs.token_stall    = csr_hw2reg.cmdblk_status.wait_token.d;
  always_comb ifd_obs.dp_instr_stall = cmd_vld & ~cmd_rdy;
  always_comb ifd_obs.dp_cmd_stall   = ag_dpc_vld & ~ag_dpc_rdy;
  always_comb ifd_obs.dp_in0_stall   = '0; // Not required
  always_comb ifd_obs.dp_in1_stall   = '0; // Not required
  always_comb ifd_obs.dp_out_stall   = '0; // Not required
  assign obs = ifd_obs;

  //// IRQs
  // HW can only set the status to high
  assign csr_hw2reg.irq_status.err_addr_out_of_range.d = 1'b1;
  assign csr_hw2reg.irq_status.err_illegal_addr.d = 1'b1;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.d = 1'b1;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.d = 1'b1;
  assign csr_hw2reg.irq_status.err_vtrsp.d = 1'b1;
  assign csr_hw2reg.irq_status.dp_vtrsp_access_error.d = 1'b1;
  assign csr_hw2reg.irq_status.dp_decomp_access_error.d = 1'b1;
  assign csr_hw2reg.irq_status.decomp_invalid_stream_header.d = 1'b1;
  assign csr_hw2reg.irq_status.decomp_invalid_scheme_header.d = 1'b1;
  assign csr_hw2reg.irq_status.decomp_invalid_compressed_size.d = 1'b1;
  assign csr_hw2reg.irq_status.decomp_invalid_uncompressed_size.d = 1'b1;
  assign csr_hw2reg.irq_status.decomp_fvc_decomp_stuck.d = 1'b1;
  assign csr_hw2reg.irq_status.err_illegal_data_conversion.d = 1'b1;

  // Error signals can level trigger the interrupt if its IRQ is enabled
  assign csr_hw2reg.irq_status.err_addr_out_of_range.de = err_addr_out_of_range & ag_dpc_vld; // only check for out of range when dpc cmd vld
  assign csr_hw2reg.irq_status.err_illegal_addr.de = mmio_addr_error;
  assign csr_hw2reg.irq_status.dbg_sw_interrupt.de = dbg_sw_interrupt;
  assign csr_hw2reg.irq_status.cmdblk_cmd_dropped.de = cmdblk_cmd_dropped;
  assign csr_hw2reg.irq_status.err_vtrsp.de = vtrsp_irq;
  assign csr_hw2reg.irq_status.dp_vtrsp_access_error.de = vtrsp_access_error;
  assign csr_hw2reg.irq_status.dp_decomp_access_error.de = decomp_access_error;
  assign csr_hw2reg.irq_status.decomp_invalid_stream_header.de = decomp_invalid_stream_header;
  assign csr_hw2reg.irq_status.decomp_invalid_scheme_header.de = decomp_invalid_scheme_header;
  assign csr_hw2reg.irq_status.decomp_invalid_compressed_size.de = decomp_invalid_compressed_size;
  assign csr_hw2reg.irq_status.decomp_invalid_uncompressed_size.de = decomp_invalid_uncompressed_size;
  assign csr_hw2reg.irq_status.decomp_fvc_decomp_stuck.de = decomp_fvc_decomp_stuck;
  assign csr_hw2reg.irq_status.err_illegal_data_conversion.de = err_illegal_data_conversion;

  // Combine all IRQs to a single IRQ
  assign irq = |(csr_reg2hw.irq_status & csr_reg2hw.irq_en);
  // Connect the DBG_SW_IRQ to the error signal
  assign dbg_sw_interrupt = csr_reg2hw.dp_ctrl.q;
  // assign dbg_sw_interrupt = csr_reg2hw.dp_ctrl.dbg_sw_irq.q;

  //// HW Capability
  assign csr_hw2reg.hw_capability.cmd_fifo_depth.d = CMD_FIFO_DEPTH;
  assign csr_hw2reg.hw_capability.static_cmd_present.d = 0;

  ///////////////////////////////////
  /// Loop memory
  cmdblock_desc_mem #(
    .IDW(IDW),
    .AW (AXI_AW),
    .DW (AXI_DW),
    .BW (BW),

    .MEM_DEPTH(DEFMEM_DEPTH),
    .MEM_WIDTH(IFD_ODR_DEFMEM_WIDTH),
    .ARB_SCHEME(1),
    .ADDR_CAP(REGION_END_ADDR[IFD_ODR_DEFMEM_S_IDX] - REGION_ST_ADDR[IFD_ODR_DEFMEM_S_IDX] + 1),
    .OUTP_SHIELD(0),
    .USE_MACRO(1),
    .SRAM_IMPL_KEY("HS_RVT")
  ) u_defmem (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),
    .scan_mode(scan_en),

    ///// AXI slave:
    // Write Address Channel
    .awid(awid_s[IFD_ODR_DEFMEM_S_IDX]),
    .awaddr(awaddr_capped_s[IFD_ODR_DEFMEM_S_IDX]),
    .awlen(awlen_s[IFD_ODR_DEFMEM_S_IDX]),
    .awsize(awsize_s[IFD_ODR_DEFMEM_S_IDX]),
    .awburst(awburst_s[IFD_ODR_DEFMEM_S_IDX]),
    .awvalid(awvalid_s[IFD_ODR_DEFMEM_S_IDX]),
    .awready(awready_s[IFD_ODR_DEFMEM_S_IDX]),
    // Read Address Channel
    .arid(arid_s[IFD_ODR_DEFMEM_S_IDX]),
    .araddr(araddr_capped_s[IFD_ODR_DEFMEM_S_IDX]),
    .arlen(arlen_s[IFD_ODR_DEFMEM_S_IDX]),
    .arsize(arsize_s[IFD_ODR_DEFMEM_S_IDX]),
    .arburst(arburst_s[IFD_ODR_DEFMEM_S_IDX]),
    .arvalid(arvalid_s[IFD_ODR_DEFMEM_S_IDX]),
    .arready(arready_s[IFD_ODR_DEFMEM_S_IDX]),
    // Write  Data Channel
    .wdata(wdata_s[IFD_ODR_DEFMEM_S_IDX]),
    .wstrb(wstrb_s[IFD_ODR_DEFMEM_S_IDX]),
    .wlast(wlast_s[IFD_ODR_DEFMEM_S_IDX]),
    .wvalid(wvalid_s[IFD_ODR_DEFMEM_S_IDX]),
    .wready(wready_s[IFD_ODR_DEFMEM_S_IDX]),
    // Read Data Channel
    .rid(rid_s[IFD_ODR_DEFMEM_S_IDX]),
    .rdata(rdata_s[IFD_ODR_DEFMEM_S_IDX]),
    .rresp(rresp_s[IFD_ODR_DEFMEM_S_IDX]),
    .rlast(rlast_s[IFD_ODR_DEFMEM_S_IDX]),
    .rvalid(rvalid_s[IFD_ODR_DEFMEM_S_IDX]),
    .rready(rready_s[IFD_ODR_DEFMEM_S_IDX]),
    // Write Response Channel
    .bid(bid_s[IFD_ODR_DEFMEM_S_IDX]),
    .bresp(bresp_s[IFD_ODR_DEFMEM_S_IDX]),
    .bvalid(bvalid_s[IFD_ODR_DEFMEM_S_IDX]),
    .bready(bready_s[IFD_ODR_DEFMEM_S_IDX]),

    ////// row read slave:
    .rd_row_rvalid(defmem_rvld),
    .rd_row_raddr (defmem_raddr),
    .rd_row_rready(defmem_rrdy),

    .rd_resp_vld (defmem_resp_vld),
    .rd_resp_data(defmem_resp_data),

    ///// SRAM Sideband Signals
    .i_sram_impl(i_sram_impl),
    .o_sram_impl(o_sram_impl)
  );

  ///////////////////////////////////
  logic [$clog2(IFD_ODR_NR_AXI_DEVS+1)-1:0] bus_sel_rd;
  logic [$clog2(IFD_ODR_NR_AXI_DEVS+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AXI_AW),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(IFD_ODR_NR_AXI_DEVS),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_wr (
    .addr_in(awaddr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AXI_AW),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(IFD_ODR_NR_AXI_DEVS),
    .NR_REGIONS(3),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({32'd0, 32'd1, 32'd2})
  ) u_ext_decode_rd (
    .addr_in(araddr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI bus:
  simple_axi_demux #(
    .NR_MASTERS(IFD_ODR_NR_AXI_DEVS),
    .IDW(IDW),
    .AW(AXI_AW),
    .DW(AXI_DW),
    .BW(BW),
    .SL_WREQ_SHIELD(2),
    .SL_RREQ_SHIELD(2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(8),
    .EXT_SEL(1)
  ) u_bus (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    // Master:
    // write address channel:
    .s_awvalid(awvalid),
    .s_awaddr(awaddr),
    .s_awid(awid),
    .s_awlen(awlen),
    .s_awsize(awsize),
    .s_awburst(awburst),
    .s_awlock('0),
    .s_awcache('0),
    .s_awprot('0),
    .s_awready(awready),

    // write data channel:
    .s_wvalid(wvalid),
    .s_wdata (wdata),
    .s_wstrb (wstrb),
    .s_wlast (wlast),
    .s_wready(wready),

    // write response channel:
    .s_bvalid(bvalid),
    .s_bid(bid),
    .s_bresp(bresp),
    .s_bready(bready),

    // read address channel:
    .s_arvalid(arvalid),
    .s_araddr(araddr),
    .s_arid(arid),
    .s_arlen(arlen),
    .s_arsize(arsize),
    .s_arburst(arburst),
    .s_arlock('0),
    .s_arcache('0),
    .s_arprot('0),
    .s_arready(arready),

    // read response channel:
    .s_rvalid(rvalid),
    .s_rid(rid),
    .s_rdata(rdata),
    .s_rresp(rresp),
    .s_rlast(rlast),
    .s_rready(rready),

    // Slaves:
    // write address channel:
    .m_awvalid(awvalid_s),
    .m_awaddr(awaddr_s),
    .m_awid(awid_s),
    .m_awlen(awlen_s),
    .m_awsize(awsize_s),
    .m_awburst(awburst_s),
    .m_awlock(), // ASO-UNUSED_OUTPUT: not used
    .m_awcache(), // ASO-UNUSED_OUTPUT: not used
    .m_awprot(), // ASO-UNUSED_OUTPUT: not used
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
    .m_arlock(), // ASO-UNUSED_OUTPUT: not used
    .m_arcache(), // ASO-UNUSED_OUTPUT: not used
    .m_arprot(), // ASO-UNUSED_OUTPUT: not used
    .m_arready(arready_s),

    // read response channel:
    .m_rvalid(rvalid_s),
    .m_rid(rid_s),
    .m_rdata(rdata_s),
    .m_rresp(rresp_s),
    .m_rlast(rlast_s),
    .m_rready(rready_s)
  );
  assign awaddr_capped_s[IFD_ODR_CSR_S_IDX]     = {(AXI_AW-(IFD_ODR_CSR_ADDR_MSB+1)   )'(0), awaddr_s[IFD_ODR_CSR_S_IDX][IFD_ODR_CSR_ADDR_MSB:0]};
  assign awaddr_capped_s[IFD_ODR_CMDB_S_IDX]    = {(AXI_AW-(IFD_ODR_CMDB_ADDR_MSB+1)  )'(0), awaddr_s[IFD_ODR_CMDB_S_IDX][IFD_ODR_CMDB_ADDR_MSB:0]};
  assign awaddr_capped_s[IFD_ODR_DEFMEM_S_IDX]  = {(AXI_AW-(IFD_ODR_DEFMEM_ADDR_MSB+1))'(0), awaddr_s[IFD_ODR_DEFMEM_S_IDX][IFD_ODR_DEFMEM_ADDR_MSB:0]};
  assign araddr_capped_s[IFD_ODR_CSR_S_IDX]     = {(AXI_AW-(IFD_ODR_CSR_ADDR_MSB+1)   )'(0), araddr_s[IFD_ODR_CSR_S_IDX][IFD_ODR_CSR_ADDR_MSB:0]};
  assign araddr_capped_s[IFD_ODR_CMDB_S_IDX]    = {(AXI_AW-(IFD_ODR_CMDB_ADDR_MSB+1)  )'(0), araddr_s[IFD_ODR_CMDB_S_IDX][IFD_ODR_CMDB_ADDR_MSB:0]};
  assign araddr_capped_s[IFD_ODR_DEFMEM_S_IDX]  = {(AXI_AW-(IFD_ODR_DEFMEM_ADDR_MSB+1))'(0), araddr_s[IFD_ODR_DEFMEM_S_IDX][IFD_ODR_DEFMEM_ADDR_MSB:0]};

endmodule

`endif  // _IFD_SV_
