// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: top level of axi2reg block for cmdblock
// This module handles the AXI to reg transaction requests for RD and WR.
// RD and WR are handled seperatly.
// In  of burst the address is increment based on size.
// Burst types INCR and FIXED are supported, WRAP is treated as INCR
// Owner: Sander Geursen <sander.geursen@axelera.ai>

`ifndef _AXI2REG_PATH_SV_
`define _AXI2REG_PATH_SV_

module axi2reg_path #(
  parameter int unsigned IDW = 4,
  parameter int unsigned AW = 36,
  parameter int unsigned DW = 64,
  parameter int unsigned BW = 6,
  parameter int unsigned OSR = 2,
  parameter int unsigned WRITE = 0,
  parameter type         datatype_t = logic,
  parameter int unsigned NR_REQS = 2,
  parameter int unsigned RESP_DEPTH = 2,
  parameter int unsigned WBUF = NR_REQS
) (
  input wire i_clk,
  input logic i_rst_n,

  ///// AXI slave:
  // Address Channel
  input  wire [IDW-1:0] id,
  input  wire [ BW-1:0] len,
  input  wire [ AW-1:0] addr,
  input  wire [    2:0] size,
  input  wire [    1:0] burst,
  // input  wire [     1:0] lock,
  // input  wire [     2:0] prot,
  input  wire           valid,
  output wire           ready,

  // Write  Data Channel
  input  wire [  DW-1:0] wdata,
  input  wire [DW/8-1:0] wstrb,
  input  wire            wlast,  // ASO-UNUSED_INPUT: not used in axi2reg
  input  wire            wvalid,
  output wire            wready,

  // Resp Data Channel
  output wire [IDW-1:0] rid,
  output wire [ DW-1:0] rdata,
  output wire [    1:0] rresp,
  output wire           rlast,
  output wire           rvalid,
  input  wire           rready,

  ////// reg master:
  output wire              reg_vld,
  input  wire              reg_rdy,
  output wire [    AW-1:0] reg_addr,
  output wire [    DW-1:0] reg_wdata,
  output wire [(DW/8)-1:0] reg_wstrb,
  input  wire              reg_resp_vld,
  output wire              reg_resp_rdy,
  input  wire              reg_resp_error,
  input  wire [    DW-1:0] reg_resp_data
);

  typedef logic [AW-1:0] logic_aw_t;

  typedef struct packed {
    logic [IDW-1:0] id;
    logic_aw_t addr;
    logic [BW-1:0] len;
    logic [2:0]    size;
    logic [1:0]    burst;
  } req_t;

  req_t req, req_q;
  logic req_rdy, req_vld;

  typedef struct packed {
    logic [IDW-1:0] id;
    logic last;
  } exp_resp_t;

  datatype_t resp, resp_q;
  exp_resp_t exp_resp, exp_resp_q;
  logic exp_resp_rrdy, exp_resp_rvld;
  logic exp_resp_wrdy, exp_resp_wvld;

  logic resp_wrdy, resp_wvld;
  logic resp_rrdy, resp_rvld;

  reg [BW-1:0] burst_cnt_q;
  logic [BW-1:0] burst_cnt_in;
  logic_aw_t cur_addr_q;
  logic_aw_t nxt_addr;
  logic burst_cnt_en;

  logic wdata_rrdy;
  logic wdata_rvld;

  logic can_output;

  logic_aw_t outp_addr;

  function automatic logic_aw_t wrap_txn_size(logic [8:0] burst_incr, logic [BW-1:0] len);
    logic_aw_t txn_size;
    unique case (len)
      'h1: return logic_aw_t'({burst_incr, 1'b0});
      'h3: return logic_aw_t'({burst_incr, 2'b00});
      'h7: return logic_aw_t'({burst_incr, 3'b000});
      'hf: return logic_aw_t'({burst_incr, 4'b0000});
      default: begin
        `ifdef TARGET_SIMULATION
        $fatal(1, "Wrap requires len to be 2, 4, 8, or 16. Any other is not supported!");
        `endif
        return logic_aw_t'(burst_incr);
      end
    endcase
  endfunction

  logic not_used_for_path_nc;
  if (WRITE)
    always_comb not_used_for_path_nc = (|reg_resp_data); // ASO-UNUSED_VARIABLE: not used in write path
  else
    always_comb not_used_for_path_nc = (|wdata) | (|wstrb) | wvalid; // ASO-UNUSED_VARIABLE: not used in read path


  // assign incomming request to internal struct:
  assign req.id    = id;
  assign req.addr  = addr;
  assign req.len   = len;
  assign req.size  = size;
  assign req.burst = burst;

  // assign response struct to outgoing signals:
  assign rid       = exp_resp_q.id;
  if (WRITE==0) assign rdata = resp_q.data;
  else assign rdata = '0;
  assign rresp         = resp_q.resp;
  assign rlast         = exp_resp_q.last;

  // feed expected tracking FIFO with last and ID:
  assign exp_resp.last = (burst_cnt_q == req_q.len) ? 1'b1 : 1'b0;
  assign exp_resp.id   = req_q.id;

  // wire signals to response
  if (WRITE==0) assign resp.data = reg_resp_data;
  assign resp.resp     = {reg_resp_error, 1'b0};

  // pop from expected and resp when both are valid:
  assign rvalid        = exp_resp_rvld & resp_rvld;
  assign exp_resp_rrdy = resp_rvld & rready;
  assign resp_rrdy     = exp_resp_rvld & rready;

  assign reg_addr      = outp_addr;

  ///////////////////////////////////////////
  // burst converter / control:
  always_ff @(posedge i_clk, negedge i_rst_n) begin : burst_regs
    if (i_rst_n == 1'b0) begin
      burst_cnt_q <= '0;
      cur_addr_q  <= '0;
    end else begin
      if (burst_cnt_en == 1'b1) begin
        burst_cnt_q <= burst_cnt_in;
        cur_addr_q  <= nxt_addr;
      end
    end
  end

  // get increase value based on transfer size:
  logic [8:0] burst_incr;
  always_comb begin
    unique case (req_q.size)
      0: burst_incr = 1;
      1: burst_incr = 2;
      2: burst_incr = 4;
      3: burst_incr = 8;
      4: burst_incr = 16;
      5: burst_incr = 32;
      6: burst_incr = 64;
      7: burst_incr = 128;
      default: burst_incr = 1;
    endcase
  end

  always_comb begin : burst_cnt_ctrl
    // default assignement
    nxt_addr     = cur_addr_q;
    burst_cnt_in = burst_cnt_q;

    req_rdy      = 1'b0;  // don't remove request until all send out
    burst_cnt_en = 1'b0;

    if (can_output) begin
      burst_cnt_en = reg_rdy;  // increment / reset counter when reg accepted

      if (burst_cnt_q == req_q.len) begin  // burst done
        burst_cnt_in = '0;  // reset counter
        req_rdy      = reg_rdy;
      end else begin
        burst_cnt_in = burst_cnt_q + 1;

        // address change:
        unique case (req_q.burst)
          axi_pkg::AXI_BURST_FIXED:  // fixed, don't change current address
            nxt_addr = outp_addr;
          axi_pkg::AXI_BURST_INCR:  // incr: increase with burst incr
            nxt_addr = outp_addr + burst_incr;
          axi_pkg::AXI_BURST_WRAP: begin // wrap: increase with burst incr unless upper address is reached, wrap to lower.
            logic_aw_t wrap_bound;
            logic_aw_t txn_size;
            logic_aw_t nxt_addr_tmp;

            wrap_bound = logic_aw_t'(axi_pkg::axi_wrap_boundary(axi_pkg::axi_largest_addr_t'({1'b0,req_q.addr}), req_q.size, req_q.len));
            txn_size = wrap_txn_size(burst_incr, req_q.len);
            nxt_addr_tmp = outp_addr + burst_incr;

            if (nxt_addr_tmp == wrap_bound + txn_size) // wrap when upper is reached
              nxt_addr = wrap_bound;
            else
              nxt_addr = nxt_addr_tmp;
          end
          default: // reserved, treat as incr
            nxt_addr = outp_addr + burst_incr;
        endcase
      end
    end
  end

  // address assignement, if started with burst counter take one from fifo, else incremented one:
  assign outp_addr  = (burst_cnt_q == 0) ? req_q.addr : cur_addr_q;

  // can produce an output when expected response fifo can accept, there is a request and data
  assign can_output = exp_resp_wrdy & req_vld & wdata_rvld;
  assign reg_vld    = can_output;
  if (WRITE) assign wdata_rrdy = can_output & reg_rdy;
  assign exp_resp_wvld = can_output & reg_rdy;

  ////////////////////////////////////
  //// used FIFO's:
  cc_stream_buffer #(
    .DEPTH(NR_REQS),
    .DW($bits(req_t))
  ) i_req_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (valid),
    .wr_data(req),
    .wr_rdy (ready),

    .rd_rdy (req_rdy),
    .rd_data(req_q),
    .rd_vld (req_vld)
  );

  if (WRITE) begin : g_write_path
    cc_stream_buffer #(
      .DEPTH(WBUF),
      .DW(DW + DW / 8)
    ) i_wdata_fifo (
      .i_clk  (i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld (wvalid),
      .wr_data({wstrb, wdata}),
      .wr_rdy (wready),

      .rd_rdy (wdata_rrdy),
      .rd_data({reg_wstrb, reg_wdata}),
      .rd_vld (wdata_rvld)
    );
  end else begin : g_read_path
    assign wready     = 1'b1;
    assign wdata_rvld = 1'b1;
  end

  cc_stream_buffer #(
    .DEPTH(OSR),
    .DW($bits(exp_resp_t))
  ) i_exp_resp_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (exp_resp_wvld),
    .wr_data(exp_resp),
    .wr_rdy (exp_resp_wrdy),

    .rd_rdy (exp_resp_rrdy),
    .rd_data(exp_resp_q),
    .rd_vld (exp_resp_rvld)
  );

  cc_stream_buffer #(
    .DEPTH(RESP_DEPTH),
    .DW($bits(datatype_t))
  ) i_resp_fifo (
    .i_clk  (i_clk),
    .i_rst_n(i_rst_n),

    .wr_vld (reg_resp_vld),
    .wr_data(resp),
    .wr_rdy (reg_resp_rdy),

    .rd_rdy (resp_rrdy),
    .rd_data(resp_q),
    .rd_vld (resp_rvld)
  );

endmodule

`endif  // _AXI2REG_PATH_SV_
