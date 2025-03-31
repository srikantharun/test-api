// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of simple AXI demux, it doesn't have fancy axi bus features
// like out of order completion, locking, etc; but not required for end points.
// At least it's configurable in sizes, addresses etc
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _SIMPLE_AXI_DEMUX_PATH_SV_
`define _SIMPLE_AXI_DEMUX_PATH_SV_

module simple_axi_demux_path #(
  parameter int unsigned NR_MASTERS = 2,
  parameter int unsigned SL_CAP = 32'h4000,
  parameter int MT_ST_ADDR[NR_MASTERS] = '{default:-1},
  parameter int MT_CAP[NR_MASTERS] = '{default:-1},
  parameter int unsigned IDW = 4,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = 64,
  parameter int unsigned BW = 6,
  parameter int unsigned OSR = 2,
  parameter int unsigned SL_REQ_SHIELD = 0,
  parameter int unsigned SL_WDATA_SHIELD = 0,
  parameter int unsigned SL_RESP_SHIELD = 0,
  parameter int unsigned WRITE = 1,
  parameter int unsigned EXT_SEL = 0
) (
  input wire i_clk,
  input wire i_rst_n,

  input logic [$clog2(NR_MASTERS+1)-1:0] i_ext_mt_sel,

  ///// AXI slave:
  // Address Channel
  input  logic [IDW-1:0] s_id,
  input  logic [ BW-1:0] s_len,
  input  logic [ AW-1:0] s_addr,
  input  logic [    2:0] s_size,
  input  logic [    1:0] s_burst,
  input  logic           s_lock,
  input  logic [    2:0] s_prot,
  input  logic [    3:0] s_cache,
  input  logic           s_valid,
  output logic           s_ready,

  // Write  Data Channel
  input  logic [  DW-1:0] s_wdata,
  input  logic [DW/8-1:0] s_wstrb,
  input  logic            s_wlast,
  input  logic            s_wvalid,
  output logic            s_wready,

  // Resp Data Channel
  output logic [IDW-1:0] s_rid,
  output logic [ DW-1:0] s_rdata,
  output logic [    1:0] s_rresp,
  output logic           s_rlast,
  output logic           s_rvalid,
  input  logic           s_rready,

  ///// AXI Master:
  // Address Channel
  output logic [NR_MASTERS-1:0][IDW-1:0] m_id   ,
  output logic [NR_MASTERS-1:0][ BW-1:0] m_len  ,
  output logic [NR_MASTERS-1:0][ AW-1:0] m_addr ,
  output logic [NR_MASTERS-1:0][    2:0] m_size ,
  output logic [NR_MASTERS-1:0][    1:0] m_burst,
  output logic [NR_MASTERS-1:0]          m_lock ,
  output logic [NR_MASTERS-1:0][    2:0] m_prot ,
  output logic [NR_MASTERS-1:0][    3:0] m_cache,
  output logic [NR_MASTERS-1:0]          m_valid,
  input  logic [NR_MASTERS-1:0]          m_ready,

  // Write  Data Channel
  output logic [NR_MASTERS-1:0][  DW-1:0] m_wdata ,
  output logic [NR_MASTERS-1:0][DW/8-1:0] m_wstrb ,
  output logic [NR_MASTERS-1:0]           m_wlast ,
  output logic [NR_MASTERS-1:0]           m_wvalid,
  input  logic [NR_MASTERS-1:0]           m_wready,

  // Resp Data Channel
  input  logic [NR_MASTERS-1:0][IDW-1:0] m_rid   ,
  input  logic [NR_MASTERS-1:0][ DW-1:0] m_rdata ,
  input  logic [NR_MASTERS-1:0][    1:0] m_rresp ,
  input  logic [NR_MASTERS-1:0]          m_rlast ,
  input  logic [NR_MASTERS-1:0]          m_rvalid,
  output logic [NR_MASTERS-1:0]          m_rready
);

  localparam int unsigned SelW = $clog2(NR_MASTERS);
  localparam int unsigned ExtSelW = $clog2(NR_MASTERS+1);

  localparam int unsigned RespDw = WRITE ? 1 : DW;

  typedef struct packed {
    logic [IDW-1:0] id;
    logic [AW-1:0] addr;
    logic [BW-1:0] len;
    logic [2:0]    size;
    logic [1:0]    burst;
    logic [2:0]    prot;
    logic          lock;
    logic [3:0]    cache;
    logic [$bits(i_ext_mt_sel)-1:0] ext_mt_sel;
  } req_t;

  req_t req, req_q;
  logic req_rdy, req_vld;

  typedef struct packed {
    logic [DW-1:0] data;
    logic [(DW/8)-1:0] strb;
    logic last;
  } wdata_t;

  wdata_t wdata, wdata_q;
  logic wdata_rdy, wdata_vld;

  typedef struct packed {
    logic [IDW-1:0]    id;
    logic [RespDw-1:0] data;
    logic [1:0]        resp;
    logic              last;
  } resp_t;

  resp_t resp, resp_q;
  logic resp_wrdy, resp_wvld;

  typedef struct packed {
    logic [IDW-1:0]   id;
    logic [SelW-1:0] mt;
    logic             err;
    logic [BW-1:0]    len;
  } sel_t;

  sel_t sel, resp_sel_q;
  logic resp_sel_wrdy, resp_sel_wvld;
  logic resp_sel_rrdy, resp_sel_rvld;

  sel_t wdata_sel_q;
  logic wdata_sel_wrdy, wdata_sel_wvld;
  logic wdata_sel_rrdy, wdata_sel_rvld;
  logic wdata_last_wrdy, wdata_last_wvld;
  logic wdata_last_rrdy, wdata_last_rvld;

  logic addr_err;

  logic rd_err_cnt_rst;
  logic rd_err_cnt_inc;
  logic [BW-1:0] rd_err_cnt;

  logic not_used_for_read_path_nc;
  if (WRITE==0)
    always_comb not_used_for_read_path_nc = (|s_wdata) | (|s_wstrb) | s_wlast | s_wvalid | (|m_wready); // ASO-UNUSED_VARIABLE: not used in read path

  // assign incomming request to internal struct:
  assign req.id    = s_id;
  assign req.addr  = s_addr;
  assign req.len   = s_len;
  assign req.size  = s_size;
  assign req.burst = s_burst;
  assign req.prot  = s_prot;
  assign req.lock  = s_lock;
  assign req.cache = s_cache;
  assign req.ext_mt_sel = i_ext_mt_sel;

  // assign incomming wdata to internal struct:
  if (WRITE)
    always_comb begin
      wdata.data  = s_wdata;
      wdata.strb = s_wstrb;
      wdata.last  = s_wlast;
    end

  // assign internal resp struct to output:
  assign s_rid   = resp_q.id;
  assign s_rdata = {{DW-RespDw{1'b0}}, resp_q.data};
  assign s_rresp = resp_q.resp;
  assign s_rlast = resp_q.last;

  ////////////////
  //// address check
  if (EXT_SEL == 0) begin: g_int_addr_check
  always_comb begin : addr_check
    sel.err = 1'b1;  // default error, unless address match found
    sel.mt  = '0;
    sel.id  = req_q.id;
    sel.len = req_q.len;

    for (int i = 0; i < NR_MASTERS; i++) begin
      if ((req_q.addr[$clog2(SL_CAP)-1:0] >= MT_ST_ADDR[i]) &&
            ({1'b0, req_q.addr[$clog2(SL_CAP)-1:0]} < ({1'b0, MT_ST_ADDR[i]} + {1'b0, MT_CAP[i]}))) begin  // master found
        sel.mt  = i;
        sel.err = 0;
      end
    end
  end
  end else begin: g_ext_addr_check
    always_comb begin
      sel.err = (req_q.ext_mt_sel == '1) ? 1'b1 : 1'b0;
      sel.mt = req_q.ext_mt_sel;
      sel.id = req_q.id;
      sel.len = req_q.len;
    end
  end

  ////////////////
  //// response select
  always_comb begin : resp_sel
    resp_sel_rrdy = 1'b0;
    resp_wvld = 1'b0;
    resp = '0;

    for (int unsigned i = 0; i < NR_MASTERS; i++) m_rready[i] = 1'b0;

    if (resp_sel_q.err == 1'b1) begin  // error, generate 2'b11 as response else logic through
      resp_wvld = resp_sel_rvld & wdata_last_rvld;

      resp.id   = resp_sel_q.id;
      resp.resp = 2'b11;  // dec error
      resp.data = '1;

      if (WRITE==0) begin  // error on read requires response for each read beat (AXI spec)
        rd_err_cnt_rst = resp_wrdy && resp_sel_rvld && (rd_err_cnt == resp_sel_q.len);
        rd_err_cnt_inc = resp_wrdy && resp_sel_rvld;  // in else of rst, no need to check len
        resp_sel_rrdy = resp_wrdy && (rd_err_cnt == resp_sel_q.len);
        resp.last = (rd_err_cnt == resp_sel_q.len) ? 1'b1 : 1'b0;
      end else begin
        resp_sel_rrdy = resp_wrdy & wdata_last_rvld;  // block resp until last has passed
        wdata_last_rrdy = resp_sel_rvld & resp_wrdy;  // block last popping until resp is vld
        resp.last = 1'b1;
      end
    end else begin  // logic through based on selected master
      if (WRITE)
        wdata_last_rrdy = '0;
      else begin
        rd_err_cnt_rst = '0;
        rd_err_cnt_inc = '0;
      end

      for (int unsigned i = 0; i < NR_MASTERS; i++) begin
        if (resp_sel_q.mt == i) begin  // master found
          // only one range will be active at the time
          // spyglass disable_block W415a
          resp_wvld = m_rvalid[i] & resp_sel_rvld & wdata_last_rvld;
          m_rready[i] = resp_wrdy & resp_sel_rvld;
          // remove sel item when master transfered response and was last item:
          resp_sel_rrdy = (m_rlast[i] | WRITE) & m_rvalid[i] & resp_wrdy & wdata_last_rvld;
          if (WRITE) wdata_last_rrdy = (m_rlast[i] | WRITE) & m_rvalid[i] & resp_sel_rvld & resp_wrdy; // block last popping until resp is vld
          // spyglass enable_block W415a

          resp.id = m_rid[i];
          resp.resp = m_rresp[i];
          resp.data = m_rdata[i][RespDw-1:0];
          resp.last = m_rlast[i];
        end
      end
    end
  end

  ////////////////
  //// rd error response burst counter
  if (WRITE==0) begin : g_wr_err
    always_ff @(posedge i_clk, negedge i_rst_n) begin : i_rd_err_cnt
      if (i_rst_n == 1'b0) begin
        rd_err_cnt <= '0;
      end else begin
        if (rd_err_cnt_rst) rd_err_cnt <= '0;
        else if (rd_err_cnt_inc) rd_err_cnt <= rd_err_cnt + 1;
      end
    end
  end

  ////////////////
  //// write data select
  if (WRITE) begin: g_wdata_sel
    always_comb begin
      // handle non-existing master error by default:
      wdata_rdy       = wdata_sel_q.err & wdata_sel_rvld & wdata_last_wrdy;
      wdata_sel_rrdy  = wdata_sel_q.err & wdata_q.last & wdata_vld & wdata_last_wrdy;
      wdata_last_wvld = wdata_sel_q.err & wdata_q.last & wdata_vld & wdata_sel_rvld;

      for (int unsigned i = 0; i < NR_MASTERS; i++) begin
        m_wvalid[i] = 1'b0;

        // logic data and such to all masters
        m_wdata[i]  = wdata_q.data;
        m_wstrb[i]  = wdata_q.strb;
        m_wlast[i]  = wdata_q.last;
      end

      for (int unsigned i = 0; i < NR_MASTERS; i++) begin
        if (wdata_sel_q.mt == i) begin  // master found
          // only one range will be active at the time
          // spyglass disable_block W415a
          wdata_last_wvld = wdata_q.last & wdata_vld & m_wready[i] & wdata_sel_rvld;
          wdata_rdy = (m_wready[i] | wdata_sel_q.err) & wdata_sel_rvld & wdata_last_wrdy;
          m_wvalid[i]  = wdata_vld & wdata_sel_rvld & wdata_last_wrdy & (~wdata_sel_q.err); // only pass along data if there was no error
          // remove sel item when master transfered response and was last item:
          wdata_sel_rrdy = wdata_q.last & m_wready[i] & wdata_vld & wdata_last_wrdy;
          // spyglass enable_block W415a
        end
      end
    end
  end

  ////////////////
  //// address select
  always_comb begin : addr_sel
    // Default drive ready and select in case there was an error
    req_rdy = resp_sel_wrdy & wdata_sel_wrdy & sel.err;
    resp_sel_wvld = req_vld & wdata_sel_wrdy & sel.err;
    if (WRITE) wdata_sel_wvld = req_vld & resp_sel_wrdy & sel.err;

    for (int unsigned i = 0; i < NR_MASTERS; i++) begin
      m_valid[i] = 1'b0;

      // logic data and such to all masters
      m_id[i] = req_q.id;
      m_len[i] = req_q.len;
      m_addr[i] = req_q.addr;
      m_size[i] = req_q.size;
      m_burst[i] = req_q.burst;
      m_lock[i] = req_q.lock;
      m_prot[i] = req_q.prot;
      m_cache[i] = req_q.cache;
    end

    // check for matching master (non-master error handled in default assign)
    for (int unsigned i = 0; i < NR_MASTERS; i++) begin
      if (sel.mt == i) begin  // master found
        // only one range will be active at the time
        // spyglass disable_block W415a
        req_rdy = resp_sel_wrdy & wdata_sel_wrdy & (m_ready[i] | sel.err);
        resp_sel_wvld = req_vld & wdata_sel_wrdy & (m_ready[i] | sel.err);
        if (WRITE) wdata_sel_wvld = req_vld & resp_sel_wrdy & (m_ready[i] | sel.err);
        m_valid[i] = req_vld & wdata_sel_wrdy & resp_sel_wrdy & ~sel.err; // only pass when no error
        // spyglass enable_block W415a
      end
    end
  end

  ////////////////////////////////////
  //// used FIFO's:
  cc_stream_buffer #(
    .DEPTH(OSR),
    .DW($bits(sel_t))
  ) i_resp_sel_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (resp_sel_wvld),
    .wr_data(sel),
    .wr_rdy (resp_sel_wrdy),

    .rd_rdy (resp_sel_rrdy),
    .rd_data(resp_sel_q),
    .rd_vld (resp_sel_rvld)
  );
  logic resp_sel_q_not_used_nc;
  always_comb resp_sel_q_not_used_nc = |resp_sel_q.len; //ASO-UNUSED_VARIABLE: len not used

  if (WRITE) begin : g_wr
    cc_stream_buffer #(
      .DEPTH(OSR),
      .DW($bits(sel_t))
    ) i_wdata_sel_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (wdata_sel_wvld),
      .wr_data(sel),
      .wr_rdy (wdata_sel_wrdy),

      .rd_rdy (wdata_sel_rrdy),
      .rd_data(wdata_sel_q),
      .rd_vld (wdata_sel_rvld)
    );
    logic wdata_sel_q_not_used_nc;
    always_comb wdata_sel_q_not_used_nc = (|wdata_sel_q.len) | (|wdata_sel_q.id); //ASO-UNUSED_VARIABLE: len and id are not used

    cc_stream_buffer #(
      .DEPTH(OSR),
      .DW(1)
    ) i_wdata_last_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (wdata_last_wvld),
      .wr_data(1'b0),
      .wr_rdy (wdata_last_wrdy),

      .rd_rdy (wdata_last_rrdy),
      .rd_data(), // ASO-UNUSED_OUTPUT: port not used
      .rd_vld (wdata_last_rvld)
     );
  end else begin : g_rd
    assign wdata_sel_wrdy  = 1'b1;
    assign wdata_last_rvld = 1'b1;
  end

  if (SL_REQ_SHIELD > 0) begin : g_req_sh
    cc_stream_buffer #(
      .DEPTH(SL_REQ_SHIELD),
      .DW($bits(req_t))
    ) i_req_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (s_valid),
      .wr_data(req),
      .wr_rdy (s_ready),

      .rd_rdy (req_rdy),
      .rd_data(req_q),
      .rd_vld (req_vld)
    );
  end else begin : g_req_pass
    assign req_q   = req;
    assign req_vld = s_valid;
    assign s_ready = req_rdy;
  end

  if (SL_RESP_SHIELD > 0) begin : g_resp_sh
    cc_stream_buffer #(
      .DEPTH(SL_RESP_SHIELD),
      .DW($bits(resp_t))
    ) i_resp_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (resp_wvld),
      .wr_data(resp),
      .wr_rdy (resp_wrdy),

      .rd_rdy (s_rready),
      .rd_data(resp_q),
      .rd_vld (s_rvalid)
    );
  end else begin : g_resp_pass
    assign resp_q = resp;
    assign s_rvalid = resp_wvld;
    assign resp_wrdy = s_rready;
  end

  if ((SL_WDATA_SHIELD > 0) & WRITE) begin : g_wdata_sh
    cc_stream_buffer #(
      .DEPTH(SL_WDATA_SHIELD),
      .DW($bits(wdata_t))
    ) i_wdata_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (s_wvalid),
      .wr_data(wdata),
      .wr_rdy (s_wready),

      .rd_rdy (wdata_rdy),
      .rd_data(wdata_q),
      .rd_vld (wdata_vld)
    );
  end else if (WRITE) begin : g_wdata_pass
    assign wdata_q   = wdata;
    assign wdata_vld = s_wvalid;
    assign s_wready  = wdata_rdy;
  end else begin : g_wdata_stub
    assign s_wready = 1'b1;
  end

endmodule

`endif  // _SIMPLE_AXI_DEMUX_PATH_SV_
