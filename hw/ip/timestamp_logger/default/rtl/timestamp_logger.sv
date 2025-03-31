// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

/// Captures events with a timestamp.
module timestamp_logger #(
  /// Number of timestamp event groups
  parameter int unsigned NumGroups = 2,

  parameter int unsigned AxiSIdWidth  = 4,
  parameter int unsigned AxiMIdWidth  = 4,
  parameter int unsigned AxiAddrWidth = 36,
  parameter int unsigned AxiDataWidth = 64,

  /// Default depth of the message fifo for the groups
  parameter int unsigned GroupDefaultFifoDepth = 2,
  /// Width of the message per group
  parameter int unsigned GroupMsgWidth[NumGroups] = '{default:0},
  /// Depth of the message fifo per group
  parameter int unsigned GroupFifoDepth[NumGroups] = '{default:GroupDefaultFifoDepth},

  /// Depth of the FIFO of the timestamps
  parameter int unsigned TimestampFifoDepth = 4,

  /// Implementation input type for the sram
  parameter type sram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Implementation output type for the sram
  parameter type sram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t,

  /// Depth of the internal memory
  parameter int unsigned MemDepth = 16,

  parameter int unsigned UseMacro = 0,
  parameter SramImplKey = "HS_RVT",

  /// Start address regions for CSR, and MEM:
  parameter longint REGION_ST_ADDR[2] = {40'h0, 40'h4000},
  /// End address regions for CSR, and MEM:
  parameter longint REGION_END_ADDR[2] = {40'hfff, 40'h7fff},

  localparam type axi_s_id_t = logic[AxiSIdWidth     -1:0],
  localparam type axi_m_id_t = logic[AxiMIdWidth     -1:0],
  localparam type axi_addr_t = logic[AxiAddrWidth    -1:0],
  localparam type axi_data_t = logic[AxiDataWidth    -1:0],
  localparam type axi_strb_t = logic[(AxiDataWidth/8)-1:0]
) (
  /// Clock, positive edge triggered
  input  wire                 i_clk,
  /// Asynchronous reset
  input  wire                 i_rst_n,

  /// Clock_gate bypass enable
  input  logic                i_scan_en,

  /// Trigger for each group
  input  logic [NumGroups-1:0]                                           i_group_trigger,
  /// Message for each group
  input  logic [NumGroups-1:0][timestamp_logger_pkg::TimeLogMaxMsgW-1:0] i_group_message,

  /// Synchronous start of the counter
  input  logic                i_sync_start,

  ///// AXI subordinate:
  // Write Address Channel
  /// AXI4 Config port: AW ID
  input  axi_s_id_t           i_axi_s_aw_id,
  /// AXI4 Config port: AW Addr
  input  axi_addr_t           i_axi_s_aw_addr,
  /// AXI4 Config port: AW Len
  input  axi_pkg::axi_len_t   i_axi_s_aw_len,
  /// AXI4 Config port: AW Size
  input  axi_pkg::axi_size_t  i_axi_s_aw_size,
  /// AXI4 Config port: AW Burst
  input  axi_pkg::axi_burst_t i_axi_s_aw_burst,
  /// AXI4 Config port: AW Valid
  input  logic                i_axi_s_aw_valid,
  /// AXI4 Config port: AW Ready
  output logic                o_axi_s_aw_ready,
  // Write  Data Channel
  /// AXI4 Config port: W Data
  input  axi_data_t           i_axi_s_w_data,
  /// AXI4 Config port: W Strb
  input  axi_strb_t           i_axi_s_w_strb,
  /// AXI4 Config port: W Last
  input  logic                i_axi_s_w_last,
  /// AXI4 Config port: W Valid
  input  logic                i_axi_s_w_valid,
  /// AXI4 Config port: W Ready
  output logic                o_axi_s_w_ready,
  // Write Response Channel
  /// AXI4 Config port: B ID
  output axi_s_id_t           o_axi_s_b_id,
  /// AXI4 Config port: B Resp
  output axi_pkg::axi_resp_t  o_axi_s_b_resp,
  /// AXI4 Config port: B Valid
  output logic                o_axi_s_b_valid,
  /// AXI4 Config port: B Ready
  input  logic                i_axi_s_b_ready,
  // Read Address Channel
  /// AXI4 Config port: AR ID
  input  axi_s_id_t           i_axi_s_ar_id,
  /// AXI4 Config port: AR Addr
  input  axi_addr_t           i_axi_s_ar_addr,
  /// AXI4 Config port: AR Len
  input  axi_pkg::axi_len_t   i_axi_s_ar_len,
  /// AXI4 Config port: AR Size
  input  axi_pkg::axi_size_t  i_axi_s_ar_size,
  /// AXI4 Config port: AR Burst
  input  axi_pkg::axi_burst_t i_axi_s_ar_burst,
  /// AXI4 Config port: AR Valid
  input  logic                i_axi_s_ar_valid,
  /// AXI4 Config port: AR Ready
  output logic                o_axi_s_ar_ready,
  // Read Data Channel
  /// AXI4 Config port: R ID
  output axi_s_id_t           o_axi_s_r_id,
  /// AXI4 Config port: R Data
  output axi_data_t           o_axi_s_r_data,
  /// AXI4 Config port: R Resp
  output axi_pkg::axi_resp_t  o_axi_s_r_resp,
  /// AXI4 Config port: R Last
  output logic                o_axi_s_r_last,
  /// AXI4 Config port: R Valid
  output logic                o_axi_s_r_valid,
  /// AXI4 Config port: R Ready
  input  logic                i_axi_s_r_ready,

  ///// AXI manager:
  // Write Address Channel
  /// AXI4 Manager port: AW ID
  output axi_m_id_t           o_axi_m_aw_id,
  /// AXI4 Manager port: AW Addr
  output axi_addr_t           o_axi_m_aw_addr,
  /// AXI4 Manager port: AW Len
  output axi_pkg::axi_len_t   o_axi_m_aw_len,
  /// AXI4 Manager port: AW Size
  output axi_pkg::axi_size_t  o_axi_m_aw_size,
  /// AXI4 Manager port: AW Burst
  output axi_pkg::axi_burst_t o_axi_m_aw_burst,
  /// AXI4 Manager port: AW Valid
  output logic                o_axi_m_aw_valid,
  /// AXI4 Manager port: AW Ready
  input  logic                i_axi_m_aw_ready,
  // Write  Data Channel
  /// AXI4 Manager port: W Data
  output axi_data_t           o_axi_m_w_data,
  /// AXI4 Manager port: W Strb
  output axi_strb_t           o_axi_m_w_strb,
  /// AXI4 Manager port: W Last
  output logic                o_axi_m_w_last,
  /// AXI4 Manager port: W Valid
  output logic                o_axi_m_w_valid,
  /// AXI4 Manager port: W Ready
  input  logic                i_axi_m_w_ready,
  // Write Response Channel
  /// AXI4 Manager port: B ID
  input  axi_m_id_t           i_axi_m_b_id,
  /// AXI4 Manager port: B Resp
  input  axi_pkg::axi_resp_t  i_axi_m_b_resp,
  /// AXI4 Manager port: B Valid
  input  logic                i_axi_m_b_valid,
  /// AXI4 Manager port: B Ready
  output logic                o_axi_m_b_ready,
  // Read Address Channel
  /// AXI4 Manager port: AR ID
  output axi_m_id_t           o_axi_m_ar_id,
  /// AXI4 Manager port: AR Addr
  output axi_addr_t           o_axi_m_ar_addr,
  /// AXI4 Manager port: AR Len
  output axi_pkg::axi_len_t   o_axi_m_ar_len,
  /// AXI4 Manager port: AR Size
  output axi_pkg::axi_size_t  o_axi_m_ar_size,
  /// AXI4 Manager port: AR Burst
  output axi_pkg::axi_burst_t o_axi_m_ar_burst,
  /// AXI4 Manager port: AR Valid
  output logic                o_axi_m_ar_valid,
  /// AXI4 Manager port: AR Ready
  input  logic                i_axi_m_ar_ready,
  // Read Data Channel
  /// AXI4 Manager port: R ID
  input  axi_m_id_t           i_axi_m_r_id,
  /// AXI4 Manager port: R Data
  input  axi_data_t           i_axi_m_r_data,
  /// AXI4 Manager port: R Resp
  input  axi_pkg::axi_resp_t  i_axi_m_r_resp,
  /// AXI4 Manager port: R Last
  input  logic                i_axi_m_r_last,
  /// AXI4 Manager port: R Valid
  input  logic                i_axi_m_r_valid,
  /// AXI4 Manager port: R Ready
  output logic                o_axi_m_r_ready,

  /// IP specific CSR connection
  //--------------------------------------------------
  output timestamp_logger_csr_reg_pkg::apb_h2d_t o_ip_csr_req,
  /// IP specific CSR connection
  input  timestamp_logger_csr_reg_pkg::apb_d2h_t i_ip_csr_rsp,

  /// Memory SRAM sideband signals
  //--------------------------------------------------
  input  sram_impl_inp_t      i_sram_impl,
  /// Memory SRAM sideband signal
  output sram_impl_oup_t      o_sram_impl
);

  import timestamp_logger_csr_reg_pkg::*;

  localparam int unsigned AxiNrSubs = 2; // memory and CSR
  localparam int unsigned MemAddrW = $clog2(MemDepth);
  localparam int unsigned MemAlignW = $clog2(timestamp_logger_pkg::TimeLogEntryDW/8);
  localparam int unsigned GroupNrW = $clog2(NumGroups);

  //--------------------------------------------------
  // AXI slave's:
  //   Write Address Channel
  axi_s_id_t           [AxiNrSubs-1:0] awid_s;
  axi_addr_t           [AxiNrSubs-1:0] awaddr_s;
  axi_pkg::axi_len_t   [AxiNrSubs-1:0] awlen_s;
  axi_pkg::axi_size_t  [AxiNrSubs-1:0] awsize_s;
  axi_pkg::axi_burst_t [AxiNrSubs-1:0] awburst_s;
  logic                [AxiNrSubs-1:0] awvalid_s;
  logic                [AxiNrSubs-1:0] awready_s;
  //   Read Address Channel
  axi_s_id_t           [AxiNrSubs-1:0] arid_s;
  axi_addr_t           [AxiNrSubs-1:0] araddr_s;
  axi_pkg::axi_len_t   [AxiNrSubs-1:0] arlen_s;
  axi_pkg::axi_size_t  [AxiNrSubs-1:0] arsize_s;
  axi_pkg::axi_burst_t [AxiNrSubs-1:0] arburst_s;
  logic                [AxiNrSubs-1:0] arvalid_s;
  logic                [AxiNrSubs-1:0] arready_s;
  //   Write  Data Channel
  axi_data_t           [AxiNrSubs-1:0] wdata_s;
  axi_strb_t           [AxiNrSubs-1:0] wstrb_s;
  logic                [AxiNrSubs-1:0] wlast_s;
  logic                [AxiNrSubs-1:0] wvalid_s;
  logic                [AxiNrSubs-1:0] wready_s;
  //   Read Data Channel
  axi_s_id_t           [AxiNrSubs-1:0] rid_s;
  axi_data_t           [AxiNrSubs-1:0] rdata_s;
  axi_pkg::axi_resp_t  [AxiNrSubs-1:0] rresp_s;
  logic                [AxiNrSubs-1:0] rlast_s;
  logic                [AxiNrSubs-1:0] rvalid_s;
  logic                [AxiNrSubs-1:0] rready_s;
  //   Write Response Channel
  axi_s_id_t           [AxiNrSubs-1:0] bid_s;
  axi_pkg::axi_resp_t  [AxiNrSubs-1:0] bresp_s;
  logic                [AxiNrSubs-1:0] bvalid_s;
  logic                [AxiNrSubs-1:0] bready_s;
  //--------------------------------------------------

  //--------------------------------------------------
  // CSR
  axi_a_ch_h2d_t csr_aw;
  axi_a_ch_h2d_t csr_ar;
  axi_w_ch_h2d_t csr_w;
  axi_b_ch_d2h_t csr_b;
  axi_r_ch_d2h_t csr_r;
  timestamp_logger_csr_reg2hw_t csr_reg2hw;
  timestamp_logger_csr_hw2reg_t csr_hw2reg;
  //--------------------------------------------------

  logic synced_en_q;
  logic cntr_en, cntr_rst;

  logic [NumGroups-1:0] enabled_triggers;
  logic [NumGroups-1:0] masked_triggers; // mask out those with full FIFO
  logic [NumGroups-1:0] trigger_overflow;
  logic group_overflow;

  logic [NumGroups-1:0] group_wrdy;
  logic [NumGroups-1:0] group_rvld;
  logic [NumGroups-1:0] group_rrdy;
  logic [NumGroups-1:0] [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] group_rdata;

  logic stamp_wvld, stamp_wrdy, stamp_rvld, stamp_rrdy;
  logic stamp_overflow;

  logic [timestamp_logger_pkg::TimeLogEntryTimestampW-1:0] timestamp, entry_timestamp;
  logic [NumGroups-1:0] entry_triggers;

  logic log_rdy, log_vld;
  logic [timestamp_logger_pkg::TimeLogEntryDW-1:0] log_data;
  logic [MemAddrW:0] log_addr_row_d;
  logic [MemAddrW:0] log_addr_row_q;
  logic log_addr_row_en;
  logic log_full, log_drop;

  logic ext_mode, log_mode_wrap;
  logic ext_hit_end_log;

  logic capture_en;
  // only capture when counter is running (synced start or not) and configured to capture.
  always_comb capture_en = (csr_reg2hw.ctrl.capture_enable.q & cntr_en);

  logic [timestamp_logger_pkg::TimeLogMaxNrGroups-1:0] all_group_en;
  always_comb all_group_en = {csr_reg2hw.group_en_64_127, csr_reg2hw.group_en_0_63};

  ////////////////////////////////////////////////////
  // Group FIFO's
  always_comb enabled_triggers = {NumGroups{capture_en}} & all_group_en[NumGroups-1:0] & i_group_trigger;
  always_comb trigger_overflow = enabled_triggers & ~group_wrdy;
  always_comb group_overflow = |(trigger_overflow); // there is a group overflowing when rdy is done and trigger arrives
  always_comb masked_triggers = enabled_triggers & group_wrdy; // mask out the groups that can't store the message

  always_comb begin
    for (int unsigned i=0; i<128; i++) begin
      csr_hw2reg.group_trigger_overflow[i].d  = 1'b1;
      if (i<NumGroups)
        csr_hw2reg.group_trigger_overflow[i].de = trigger_overflow[i] | (stamp_overflow & enabled_triggers[i]);
      else
        csr_hw2reg.group_trigger_overflow[i].de = 1'b0;
    end
    csr_hw2reg.stamp_overflow.d  = 1'b1;
    csr_hw2reg.stamp_overflow.de = stamp_overflow;
  end

  logic drain_fifo;
  always_comb drain_fifo = ext_mode & ext_hit_end_log;

  for (genvar g=0; g<NumGroups; g++) begin: g_grp
    if (GroupMsgWidth[g] > 0) begin: g_grp_fifo
      cc_stream_buffer #(
        .DEPTH(GroupFifoDepth[g]),
        .DW(GroupMsgWidth[g]),
        .USE_MACRO(0)
      ) u_fifo (
        .i_clk,
        .i_rst_n,

        .wr_vld(enabled_triggers[g] & stamp_wrdy),
        .wr_data(i_group_message[g][GroupMsgWidth[g]-1:0]),
        .wr_rdy(group_wrdy[g]),

        .rd_rdy(group_rrdy[g] | drain_fifo),
        .rd_data(group_rdata[g][GroupMsgWidth[g]-1:0]),
        .rd_vld(group_rvld[g])
      );
      if (GroupMsgWidth[g]<timestamp_logger_pkg::TimeLogMaxMsgW)
        assign group_rdata[g][timestamp_logger_pkg::TimeLogMaxMsgW-1:GroupMsgWidth[g]] = '0;

    end else begin: g_grp_no_fifo
      always_comb group_wrdy[g]  = 1'b1; // don't backpressure this group if no message is present
      always_comb group_rvld[g] = 1'b1; // act like there is something in the message FIFO (if it's ever used...)
      always_comb group_rdata[g] = timestamp_logger_pkg::TimeLogMaxMsgW'(0);
    end
  end

  //////////////////////
  // Group Assertions //
  //////////////////////

  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON
  bit disable_ovfl_property;
  initial begin
    if (!$value$plusargs("TIMESTAMP_LOGGER_ALLOW_GROUP_OVFL=%d", disable_ovfl_property))
      disable_ovfl_property = 1'b0;
  end

  for (genvar i=0; i<NumGroups; i++) begin: g_grp_assert
    property p_grp_drop;
      @(posedge i_clk) disable iff (!i_rst_n | disable_ovfl_property)
      (!trigger_overflow[i]);
    endproperty : p_grp_drop
    check_p_grp_drop: assert property (p_grp_drop);
  end

  property p_stamp_drop;
    @(posedge i_clk) disable iff (!i_rst_n | disable_ovfl_property)
    (!stamp_overflow);
  endproperty : p_stamp_drop
  check_p_stamp_drop: assert property (p_stamp_drop);

  `endif
  `endif

  /////////////////////////////////////////
  ////////////////////////////////////////////////////


  ////////////////////////////////////////////////////
  // Timestamp counter with attached triggers
  always_comb stamp_wvld = |masked_triggers;
  always_comb stamp_overflow = stamp_wvld & ~stamp_wrdy;
  cc_stream_buffer #(
    .DEPTH(TimestampFifoDepth),
    .DW(timestamp_logger_pkg::TimeLogEntryTimestampW + NumGroups),
    .USE_MACRO(0)
  ) u_fifo (
    .i_clk,
    .i_rst_n,

    .wr_vld(stamp_wvld), // if there is any group triggering, store it
    .wr_data({timestamp, masked_triggers}),
    .wr_rdy(stamp_wrdy),

    .rd_rdy(stamp_rrdy | drain_fifo),
    .rd_data({entry_timestamp, entry_triggers}),
    .rd_vld(stamp_rvld)
  );
  ////////////////////////////////////////////////////

  ///////////////////////////////////////////////////
  // Message arbiter, serve each group of same timestamp
  logic [NumGroups-1:0] groups_served_d, groups_served_q;
  logic groups_served_en;

  logic [NumGroups-1:0] group_arb_vld, group_arb_rdy;
  logic [timestamp_logger_pkg::TimeLogMaxMsgW-1:0] entry_msg;
  logic [GroupNrW-1:0] entry_group;
  logic entry_vld, entry_rdy;

  // capture which groups have been served already and remove them from the current list:
  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n)
      groups_served_q <= NumGroups'(0);
    else if (groups_served_en)
      groups_served_q <= groups_served_d;
  end

  always_comb begin
    groups_served_en = entry_vld & entry_rdy; // default when message is send out
    groups_served_d = groups_served_q | group_arb_rdy; // default current masked with served
    stamp_rrdy = 1'b0;

    if ((groups_served_q | group_arb_rdy) == entry_triggers) begin // nothing left to serve: start from zero
      groups_served_d = NumGroups'(0);
      stamp_rrdy = 1'b1; // and accept stamp
    end
  end

  always_comb group_arb_vld = stamp_rvld ? entry_triggers & ~groups_served_q : NumGroups'(0);
  rr_arb_tree #(
    .NumIn      (NumGroups),
    .DataWidth  (timestamp_logger_pkg::TimeLogMaxMsgW),
    .ExtPrio    (1'b1),
    .AxiVldRdy  (1'b1),
    .LockIn     (1'b0)
  ) u_msg_arb (
    .i_clk,
    .i_rst_n,
    .flush_i('0),
    .rr_i   ('0),
    .req_i  (group_arb_vld),
    .gnt_o  (group_arb_rdy),
    .data_i (group_rdata),
    .req_o  (entry_vld),
    .gnt_i  (entry_rdy),
    .data_o (entry_msg),
    .idx_o  (entry_group)
  );
  always_comb group_rrdy = group_arb_rdy;

  // stall when full, drop when asked to
  always_comb log_vld = entry_vld & ~log_full;
  always_comb entry_rdy = (log_rdy & ~log_full) | (log_drop); // drop in case requested
  //////////////////////////////////////////////////

  //////////////////////////////////////////////////
  // Logic to control the buffer writing (provide buffer addr and enable)
  // set the current address when enable bit is set, or when a trace entry is written
  logic [MemAddrW-1:0] log_st_addr_row;
  logic [MemAddrW:0]   log_size_row;
  logic entries_in_mem_add, entries_in_mem_sub, entries_in_mem_clr;
  logic [MemAddrW:0] entries_in_mem_d, entries_in_mem_q;
  logic entries_in_mem_en;
  logic [MemAddrW:0] entries_in_mem_ext_d, entries_in_mem_ext_q;
  logic entries_in_mem_ext_rd, entries_in_mem_ext_en;

  always_comb ext_mode = csr_reg2hw.ctrl.external_mode.q;

  always_comb log_st_addr_row = ext_mode ? MemAddrW'(0)             : csr_reg2hw.st_addr.q[MemAlignW+:MemAddrW];
  always_comb log_size_row    = ext_mode ? (MemAddrW+1)'(MemDepth)  : csr_reg2hw.log_size.q[MemAlignW+:(MemAddrW+1)];
  always_comb log_mode_wrap   = ext_mode ? 1'b1                     : csr_reg2hw.ctrl.trace_mode.q;

  always_comb begin
    log_full = 1'b0;
    log_drop = drain_fifo;
    log_addr_row_d = log_addr_row_q + MemAddrW'(1);

    log_addr_row_en    = entry_vld & log_rdy;
    entries_in_mem_add = entry_vld & log_rdy; // add when writing

    if (log_mode_wrap == 1'b0) begin  // drop mode
      // check for end, (st + size)
      if (log_addr_row_q == ({1'b0,log_st_addr_row} + {log_size_row})) begin
        // drop if end is reached (end address passed)
        log_full = 1'b1;
        log_drop = 1'b1;
        log_addr_row_en = 1'b0;
        entries_in_mem_add = 1'b0;
      end
    end else begin
      if (log_addr_row_q == ({1'b0,log_st_addr_row} + {log_size_row})-1) log_addr_row_d = {1'b0,log_st_addr_row};

      if (ext_mode == 1'b1 && (entries_in_mem_q == MemDepth)) begin // drive full in case buffer is not emptied in time (ext mode)
        log_full = 1'b1;
        log_addr_row_en = 1'b0;
        entries_in_mem_add = 1'b0;
      end
    end

    if (csr_reg2hw.ctrl.capture_enable.qe & csr_reg2hw.ctrl.capture_enable.q) begin  // new trace
      log_addr_row_d = ext_mode ? MemAddrW'(0) : csr_reg2hw.st_addr.q[MemAlignW+:MemAddrW];
      log_addr_row_en = 1'b1;
      entries_in_mem_add = 1'b0;
    end
  end

  //////////////////////////////////////////////
  // Count the buffer / tracking
  // one for checking if local buffer is full
  // one for telling external move what is still left to move
  always_comb begin // count entries in buffer for ext read purposes
    if (entries_in_mem_add && !entries_in_mem_sub)
      entries_in_mem_d = entries_in_mem_q + MemAddrW'(1);
    else
      entries_in_mem_d = entries_in_mem_q - MemAddrW'(1);

    if (entries_in_mem_add && !entries_in_mem_ext_rd)
      entries_in_mem_ext_d = entries_in_mem_ext_q + MemAddrW'(1);
    else
      entries_in_mem_ext_d = entries_in_mem_ext_q - MemAddrW'(1);

    if (entries_in_mem_clr)
      entries_in_mem_d = MemAddrW'(0);

    entries_in_mem_en = entries_in_mem_clr | (entries_in_mem_add ^ entries_in_mem_sub); // only update when changed
    entries_in_mem_ext_en = (entries_in_mem_add ^ entries_in_mem_ext_rd); // only update when changed
  end

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n) begin
      // entry_cntr_q <= '0;
      log_addr_row_q <= MemAddrW'(0);
      entries_in_mem_q <= MemAddrW'(0);
      entries_in_mem_ext_q <= MemAddrW'(0);
    end else begin
      if (log_addr_row_en) log_addr_row_q <= log_addr_row_d;
      if (entries_in_mem_en) entries_in_mem_q <= entries_in_mem_d;
      if (entries_in_mem_ext_en) entries_in_mem_ext_q <= entries_in_mem_ext_d;
    end
  end

  always_comb csr_hw2reg.entry_count = timestamp_logger_csr_reg_pkg::timestamp_logger_csr_hw2reg_entry_count_reg_t'(entries_in_mem_q);

  //////////////////////////////////////////
  always_comb entries_in_mem_clr = csr_reg2hw.ctrl.capture_enable.qe & csr_reg2hw.ctrl.capture_enable.q;

  // won't do ext reads:
  always_comb o_axi_m_ar_valid = 1'b0;
  always_comb o_axi_m_ar_id = 1'b0;
  always_comb o_axi_m_ar_addr = 1'b0;
  always_comb o_axi_m_ar_len = 1'b0;
  always_comb o_axi_m_ar_size = 1'b0;
  always_comb o_axi_m_ar_burst = 1'b0;
  always_comb o_axi_m_r_ready  = 1'b0;

  /////////////////////////////////////////
  // counter:
  always_comb cntr_en = csr_reg2hw.counter_ctrl.sync_ctrl.q ? synced_en_q // sync
                          : csr_reg2hw.ctrl.capture_enable.q; // no sync: run when enabled
  always_comb cntr_rst = csr_reg2hw.counter_ctrl.reset.qe | // reset when writing to reset or
                          (csr_reg2hw.counter_ctrl.sync_ctrl.q & i_sync_start); // getting sync start

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n)
      synced_en_q <= 1'b0;
    else begin
      if (csr_reg2hw.counter_ctrl.sync_ctrl.q && i_sync_start)
        synced_en_q <= 1'b1;
      else if (csr_reg2hw.counter_ctrl.stop.qe)
        synced_en_q <= 1'b0;
    end
  end

  timestamp_logger_cntr u_cnt (
    .i_clk,
    .i_rst_n,

    .i_cntr_en(cntr_en),
    .i_cntr_rst(cntr_rst),
    .i_scale_val(csr_reg2hw.ctrl.cntr_division.q),
    .o_timestamp(timestamp)
  );

   ////////////////////////
   // Counter Assertions //
  /////////////////////////

  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON

    property p_cntr_no_inc_when_disabled;
      @(posedge i_clk) disable iff (!i_rst_n)
      ##1 (!(cntr_en) && $stable(cntr_en)) |-> (timestamp === $past(timestamp)) | $past(cntr_rst);
    endproperty : p_cntr_no_inc_when_disabled
    check_p_cntr_no_inc_when_disabled: assert property (p_cntr_no_inc_when_disabled);

    property p_cntr_inc_implies_en;
      @(posedge i_clk) disable iff (!i_rst_n)
      ##1 (timestamp !== $past(timestamp)) |-> $past(cntr_en) | $past(cntr_rst);
    endproperty : p_cntr_inc_implies_en
    check_p_cntr_inc_implies_en: assert property (p_cntr_inc_implies_en);

    property p_cntr_rst_implies_timestamp_eq0;
      @(posedge i_clk) disable iff (!i_rst_n)
      cntr_rst |-> ##1 timestamp === '0;
    endproperty : p_cntr_rst_implies_timestamp_eq0
    check_p_cntr_rst_implies_timestamp_eq0: assert property (p_cntr_rst_implies_timestamp_eq0);

    property p_cntr_inc_by_one;
      @(posedge i_clk) disable iff (!i_rst_n)
      ##1 (timestamp !== $past(timestamp)) |-> (timestamp === '0) || (timestamp === $past(timestamp)+1);
    endproperty : p_cntr_inc_by_one
    check_p_cntr_inc_by_one: assert property (p_cntr_inc_by_one);

  `endif
  `endif

  /////////////////////////////////////////

  // // Decouple FIFO (TODO: needed?)
  // cc_stream_fifo #(
  //   .Depth      (2),
  //   .DataWidth  (TimeLogEntryDW + LOG_ADDR_W),
  //   .FallThrough(1'b0)
  // ) u_cmd_fifo (
  //   .i_clk,
  //   .i_rst_n,
  //   .i_flush(1'b0),
  //   .i_data ({trace_entry, trace_addr_q}),
  //   .i_valid(trace_vld),
  //   .o_ready(trace_rdy),
  //   .o_data ({trace_entry_q, log_addr_row}),
  //   .o_valid(log_vld),
  //   .i_ready(log_rdy),
  //   .o_usage(/* open */),
  //   .o_full (/* open */),
  //   .o_empty(/* open */)
  // );
  ///////////////////////////////////////

  always_comb begin
    // pack:
    log_data = 0; // default
    log_data[timestamp_logger_pkg::TimeLogEntryMessageLsb   +: timestamp_logger_pkg::TimeLogMaxMsgW]          = entry_msg;
    log_data[timestamp_logger_pkg::TimeLogEntryGroupLsb     +: GroupNrW]                                      = GroupNrW'(entry_group);
    log_data[timestamp_logger_pkg::TimeLogEntryTimestampLsb +: timestamp_logger_pkg::TimeLogEntryTimestampW]  = entry_timestamp;
  end

  ///////////////////////////////////
  logic [$clog2(AxiNrSubs+1)-1:0] bus_sel_rd;
  logic [$clog2(AxiNrSubs+1)-1:0] bus_sel_wr;
  aic_fabric_addr_decoder #(
    .AW(AxiAddrWidth),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(AxiNrSubs),
    .NR_REGIONS(2),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({timestamp_logger_pkg::csr_idx, timestamp_logger_pkg::mem_idx})
  ) u_ext_decode_wr (
    .addr_in(i_axi_s_aw_addr),
    .core_id('0),

    .sl_select(bus_sel_wr)
  );
  aic_fabric_addr_decoder #(
    .AW(AxiAddrWidth),
    .DEFAULT_SLAVE('1),
    .NOT_THIS_CORE_SLAVE('1),
    .NR_SLAVES(AxiNrSubs),
    .NR_REGIONS(2),
    .REGION_ST_ADDR(REGION_ST_ADDR),
    .REGION_END_ADDR(REGION_END_ADDR),
    .REGION_SLAVE_ID({timestamp_logger_pkg::csr_idx, timestamp_logger_pkg::mem_idx})
  ) u_ext_decode_rd (
    .addr_in(i_axi_s_ar_addr),
    .core_id('0),

    .sl_select(bus_sel_rd)
  );
  // AXI bus:
  simple_axi_demux #(
    .NR_MASTERS     (AxiNrSubs),
    .IDW            (AxiSIdWidth),
    .AW             (AxiAddrWidth),
    .DW             (AxiDataWidth),
    .BW             (axi_pkg::AXI_LEN_WIDTH),
    .SL_WREQ_SHIELD (2),
    .SL_RREQ_SHIELD (2),
    .SL_WDATA_SHIELD(2),
    .SL_WRESP_SHIELD(2),
    .SL_RRESP_SHIELD(2),
    .OSR(8),
    .EXT_SEL(1)
  ) u_bus (
    .i_clk,
    .i_rst_n,

    .i_ext_mt_sel_rd(bus_sel_rd),
    .i_ext_mt_sel_wr(bus_sel_wr),

    // Manager:
    // write address channel:
    .s_awid   (i_axi_s_aw_id),
    .s_awaddr (i_axi_s_aw_addr),
    .s_awlen  (i_axi_s_aw_len),
    .s_awsize (i_axi_s_aw_size),
    .s_awburst(i_axi_s_aw_burst),
    .s_awlock ('0),
    .s_awcache('0),
    .s_awprot ('0),
    .s_awvalid(i_axi_s_aw_valid),
    .s_awready(o_axi_s_aw_ready),

    // write data channel:
    .s_wdata (i_axi_s_w_data),
    .s_wstrb (i_axi_s_w_strb),
    .s_wlast (i_axi_s_w_last),
    .s_wvalid(i_axi_s_w_valid),
    .s_wready(o_axi_s_w_ready),

    // write response channel:
    .s_bid   (o_axi_s_b_id),
    .s_bresp (o_axi_s_b_resp),
    .s_bvalid(o_axi_s_b_valid),
    .s_bready(i_axi_s_b_ready),

    // read address channel:
    .s_arid   (i_axi_s_ar_id),
    .s_araddr (i_axi_s_ar_addr),
    .s_arlen  (i_axi_s_ar_len),
    .s_arsize (i_axi_s_ar_size),
    .s_arburst(i_axi_s_ar_burst),
    .s_arlock ('0),
    .s_arcache('0),
    .s_arprot ('0),
    .s_arvalid(i_axi_s_ar_valid),
    .s_arready(o_axi_s_ar_ready),

    // read response channel:
    .s_rid   (o_axi_s_r_id),
    .s_rdata (o_axi_s_r_data),
    .s_rresp (o_axi_s_r_resp),
    .s_rlast (o_axi_s_r_last),
    .s_rvalid(o_axi_s_r_valid),
    .s_rready(i_axi_s_r_ready),

    // Slaves:
    // write address channel:
    .m_awid   (awid_s),
    .m_awaddr (awaddr_s),
    .m_awlen  (awlen_s),
    .m_awsize (awsize_s),
    .m_awburst(awburst_s),
    .m_awlock (/* not used */),
    .m_awcache(/* not used */),
    .m_awprot (/* not used */),
    .m_awvalid(awvalid_s),
    .m_awready(awready_s),

    // write data channel:
    .m_wdata (wdata_s),
    .m_wstrb (wstrb_s),
    .m_wlast (wlast_s),
    .m_wvalid(wvalid_s),
    .m_wready(wready_s),

    // write response channel:
    .m_bid   (bid_s),
    .m_bresp (bresp_s),
    .m_bvalid(bvalid_s),
    .m_bready(bready_s),

    // read address channel:
    .m_arid   (arid_s),
    .m_araddr (araddr_s),
    .m_arlen  (arlen_s),
    .m_arsize (arsize_s),
    .m_arburst(arburst_s),
    .m_arlock (/* not used */),
    .m_arcache(/* not used */),
    .m_arprot (/* not used */),
    .m_arvalid(arvalid_s),
    .m_arready(arready_s),

    // read response channel:
    .m_rid   (rid_s),
    .m_rdata (rdata_s),
    .m_rresp (rresp_s),
    .m_rlast (rlast_s),
    .m_rvalid(rvalid_s),
    .m_rready(rready_s)
  );

  ///////////////////////////////////////////////////////////
  // CSR:
  timestamp_logger_csr_reg_top u_csr (
    .clk_i      (i_clk),
    .rst_ni     (i_rst_n),
    .axi_aw_i   (csr_aw),
    .axi_awready(awready_s[timestamp_logger_pkg::csr_idx]),
    .axi_ar_i   (csr_ar),
    .axi_arready(arready_s[timestamp_logger_pkg::csr_idx]),
    .axi_w_i    (csr_w),
    .axi_wready (wready_s[timestamp_logger_pkg::csr_idx]),
    .axi_b_o    (csr_b),
    .axi_bready (bready_s[timestamp_logger_pkg::csr_idx]),
    .axi_r_o    (csr_r),
    .axi_rready (rready_s[timestamp_logger_pkg::csr_idx]),
    .apb_win_o  (o_ip_csr_req),
    .apb_win_i  (i_ip_csr_rsp),
    .reg2hw     (csr_reg2hw),
    .hw2reg     (csr_hw2reg),
    .devmode_i  (1'b1)
  );

  always_comb csr_aw = '{
    id:    awid_s[timestamp_logger_pkg::csr_idx],
    addr:  awaddr_s[timestamp_logger_pkg::csr_idx],
    len:   awlen_s[timestamp_logger_pkg::csr_idx],
    size:  awsize_s[timestamp_logger_pkg::csr_idx],
    burst: awburst_s[timestamp_logger_pkg::csr_idx],
    valid: awvalid_s[timestamp_logger_pkg::csr_idx]
  };
  always_comb csr_w = '{
    data: wdata_s[timestamp_logger_pkg::csr_idx],
    strb: wstrb_s[timestamp_logger_pkg::csr_idx],
    last: wlast_s[timestamp_logger_pkg::csr_idx],
    valid: wvalid_s[timestamp_logger_pkg::csr_idx]
  };

  always_comb bid_s[timestamp_logger_pkg::csr_idx]    = csr_b.id;
  always_comb bresp_s[timestamp_logger_pkg::csr_idx]  = csr_b.resp;
  always_comb bvalid_s[timestamp_logger_pkg::csr_idx] = csr_b.valid;

  always_comb csr_ar = '{
    id:    arid_s[timestamp_logger_pkg::csr_idx],
    addr:  araddr_s[timestamp_logger_pkg::csr_idx],
    len:   arlen_s[timestamp_logger_pkg::csr_idx],
    size:  arsize_s[timestamp_logger_pkg::csr_idx],
    burst: arburst_s[timestamp_logger_pkg::csr_idx],
    valid: arvalid_s[timestamp_logger_pkg::csr_idx]
  };

  always_comb rid_s[timestamp_logger_pkg::csr_idx]    = csr_r.id;
  always_comb rdata_s[timestamp_logger_pkg::csr_idx]  = csr_r.data;
  always_comb rresp_s[timestamp_logger_pkg::csr_idx]  = csr_r.resp;
  always_comb rlast_s[timestamp_logger_pkg::csr_idx]  = csr_r.last;
  always_comb rvalid_s[timestamp_logger_pkg::csr_idx] = csr_r.valid;
  ////////////////////////////////////////////////////////////


  /////////////////////////////////////////////////////////
  // Memory access:
  logic ram_we;
  logic ram_re;
  logic [MemAddrW-1:0] ram_addr;
  logic [timestamp_logger_pkg::TimeLogEntryDW-1:0] ram_wdata;
  logic [timestamp_logger_pkg::TimeLogEntryDW-1:0] ram_rdata;
  logic ext_req_valid;
  logic ext_req_ready;
  logic [MemAddrW-1:0] ext_req_addr_row;
  logic ext_rsp_valid;
  logic ext_rsp_ready;
  logic [timestamp_logger_pkg::TimeLogEntryDW-1:0] ext_rsp_data;

  timestamp_logger_mem_arb #(
    .AxiIdWidth     (AxiSIdWidth),
    .AxiAddrWidth   (AxiAddrWidth),
    .AxiDataWidth   (AxiDataWidth),
    .MemoryWidth    (timestamp_logger_pkg::TimeLogEntryDW),
    .MemoryDepth    (MemDepth),
    .AddrCapacity   (REGION_END_ADDR[timestamp_logger_pkg::mem_idx] - REGION_ST_ADDR[timestamp_logger_pkg::mem_idx] + 1)
  ) u_arb (
    .i_clk,
    .i_rst_n,

    // write address channel:
    .i_axi_s_aw_id   (awid_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_aw_addr (awaddr_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_aw_len  (awlen_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_aw_size (awsize_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_aw_burst(awburst_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_aw_valid(awvalid_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_aw_ready(awready_s[timestamp_logger_pkg::mem_idx]),

    // write data channel:
    .i_axi_s_w_data (wdata_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_w_strb (wstrb_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_w_last (wlast_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_w_valid(wvalid_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_w_ready(wready_s[timestamp_logger_pkg::mem_idx]),

    // write response channel:
    .o_axi_s_b_id   (bid_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_b_resp (bresp_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_b_valid(bvalid_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_b_ready(bready_s[timestamp_logger_pkg::mem_idx]),

    // read address channel:
    .i_axi_s_ar_id   (arid_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_ar_addr (araddr_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_ar_len  (arlen_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_ar_size (arsize_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_ar_burst(arburst_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_ar_valid(arvalid_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_ar_ready(arready_s[timestamp_logger_pkg::mem_idx]),

    // read response channel:
    .o_axi_s_r_id   (rid_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_r_data (rdata_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_r_resp (rresp_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_r_last (rlast_s[timestamp_logger_pkg::mem_idx]),
    .o_axi_s_r_valid(rvalid_s[timestamp_logger_pkg::mem_idx]),
    .i_axi_s_r_ready(rready_s[timestamp_logger_pkg::mem_idx]),

    .i_log_req_valid    (log_vld & (~drain_fifo)),
    .o_log_req_ready    (log_rdy),
    .i_log_req_data     (log_data),
    .i_log_req_addr_row (log_addr_row_q[MemAddrW-1:0]),
    .o_log_rsp_valid    (/* no need for a response */),
    .i_log_rsp_ready    (1'b1),

    .i_ext_req_valid    (ext_req_valid),
    .o_ext_req_ready    (ext_req_ready),
    .i_ext_req_addr_row (ext_req_addr_row),
    .o_ext_rsp_valid    (ext_rsp_valid),
    .i_ext_rsp_ready    (ext_rsp_ready),
    .o_ext_rsp_data     (ext_rsp_data),

    .o_ram_we   (ram_we),
    .o_ram_re   (ram_re),
    .o_ram_addr (ram_addr),
    .o_ram_wdata(ram_wdata),
    .i_ram_rdata(ram_rdata)
  );


  /////////////////////////////////////
  // External move
    // only put a FIFO in for the non-static signals. strb, size and burst are hardcoded stable
  axi_addr_t           ext_mv_aw_addr;
  axi_pkg::axi_len_t   ext_mv_aw_len;
  logic                ext_mv_aw_valid;
  logic                ext_mv_aw_ready;
  axi_data_t           ext_mv_w_data;
  logic                ext_mv_w_last;
  logic                ext_mv_w_valid;
  logic                ext_mv_w_ready;

  timestamp_logger_ext_move #(
      .MemDepth(MemDepth),
      .MemWidth(timestamp_logger_pkg::TimeLogEntryDW),
      .AxiAddrWidth(AxiAddrWidth),
      .AxiDataWidth(AxiDataWidth)
  ) u_ext_move (
    .i_clk,
    .i_rst_n,

    .i_csr_reg2hw(csr_reg2hw),

    .i_capture_en(capture_en),
    .o_hit_end_log(ext_hit_end_log),
    .i_writing_to_buf(log_vld),

    // info about the buffer fillness:
    .i_entries_in_mem(entries_in_mem_ext_q),
    .o_entries_in_mem_sub(entries_in_mem_sub), // data moved out, can be used in logger
    .o_entries_in_mem_rd(entries_in_mem_ext_rd), // data read request out

    // local memory access:
    .o_mem_req_valid(ext_req_valid),
    .i_mem_req_ready(ext_req_ready),
    .o_mem_req_addr_row(ext_req_addr_row),
    .i_mem_rsp_valid(ext_rsp_valid),
    .o_mem_rsp_ready(ext_rsp_ready),
    .i_mem_rsp_data(ext_rsp_data),

    // external access:
    .o_axi_m_aw_valid(ext_mv_aw_valid),
    .i_axi_m_aw_ready(ext_mv_aw_ready),
    .o_axi_m_aw_addr(ext_mv_aw_addr),
    .o_axi_m_aw_len(ext_mv_aw_len),
    .o_axi_m_aw_size,
    .o_axi_m_aw_burst,

    // Write  Data Channel
    .o_axi_m_w_data(ext_mv_w_data),
    .o_axi_m_w_strb,
    .o_axi_m_w_last(ext_mv_w_last),
    .o_axi_m_w_valid(ext_mv_w_valid),
    .i_axi_m_w_ready(ext_mv_w_ready),
    // Write Response Channel
    .i_axi_m_b_resp,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,

    // some sort of debug / irq:
    .o_bus_error()
  );

  // AXI shields:
  cc_stream_buffer #(
    .DEPTH(2),
    .DW($bits(axi_addr_t) + $bits(axi_pkg::axi_len_t))
  ) u_axi_shield_aw (
    .i_clk  ,
    .i_rst_n,

    .wr_vld (ext_mv_aw_valid),
    .wr_data({ext_mv_aw_len, ext_mv_aw_addr}),
    .wr_rdy (ext_mv_aw_ready),

    .rd_rdy (i_axi_m_aw_ready),
    .rd_data({o_axi_m_aw_len, o_axi_m_aw_addr}),
    .rd_vld (o_axi_m_aw_valid)
  );

  cc_stream_buffer #(
    .DEPTH(2),
    .DW(1 + $bits(axi_data_t))
  ) u_axi_shield_w (
    .i_clk  ,
    .i_rst_n,

    .wr_vld (ext_mv_w_valid),
    .wr_data({ext_mv_w_last, ext_mv_w_data}),
    .wr_rdy (ext_mv_w_ready),

    .rd_rdy (i_axi_m_w_ready),
    .rd_data({o_axi_m_w_last, o_axi_m_w_data}),
    .rd_vld (o_axi_m_w_valid)
  );
  always_comb o_axi_m_aw_id = AxiMIdWidth'(0);

  if (UseMacro) begin: g_mem
    axe_tcl_ram_1rwp #(
      .NumWords  (MemDepth),
      .DataWidth (timestamp_logger_pkg::TimeLogEntryDW),
      .ByteWidth (timestamp_logger_pkg::TimeLogEntryDW),
      .ReadLatency(1),
      .ImplKey   (SramImplKey),
      .impl_inp_t(sram_impl_inp_t),
      .impl_oup_t(sram_impl_oup_t)
    ) u_ram (
      .i_clk,
      .i_rst_n,
      .i_req      (ram_we | ram_re),
      .i_addr     (ram_addr),
      .i_wr_enable(ram_we),
      .i_wr_data  (ram_wdata),
      .i_wr_mask  (1'b1),
      .o_rd_data  (ram_rdata),
      .i_impl     (i_sram_impl),
      .o_impl     (o_sram_impl)
    );
  end else begin: g_flops
    logic memory_clk;

    // Use a overlooking clock-gate for gating the entire array of flops:
    axe_tcl_clk_gating u_cg (
      .i_clk(i_clk),
      .i_en(ram_we),
      .i_test_en(i_scan_en),
      .o_clk(memory_clk)
    );
    logic [timestamp_logger_pkg::TimeLogEntryDW-1:0] memory_q[MemDepth];

    always_ff @(posedge memory_clk) begin // no gate of ram_re, as entire thing is guarded by single clock-gate
      memory_q[ram_addr] <= ram_wdata;
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)
        ram_rdata <= timestamp_logger_pkg::TimeLogEntryDW'(0);
      else if (ram_re)
        ram_rdata <= memory_q[ram_addr];
    end
  end
endmodule

