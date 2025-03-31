// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Simple reg2ahb, that can be connected to the AXI2reg and DMA
// Owner: Sander Geursen <sander.geursen@axelera.ai>


module snps_dma_reg2ahb #(
  parameter int unsigned AW = 36,
  parameter int unsigned DW = 64
) (
  input wire i_clk,
  input wire i_rst_n,

  ////// reg interface:
  // Write path:
  input  logic              i_reg_wvld,
  output logic              o_reg_wrdy,
  input  logic [    AW-1:0] i_reg_waddr,
  input  logic [    DW-1:0] i_reg_wdata,
  input  logic [(DW/8)-1:0] i_reg_wstrb,
  output logic              o_reg_wresp_vld,
  input  logic              i_reg_wresp_rdy,
  output logic              o_reg_wresp_error,

  // Read path:
  input  logic              i_reg_rvld,
  output logic              o_reg_rrdy,
  input  logic [AW-1:0]     i_reg_raddr,
  output logic              o_reg_rresp_vld,
  input  logic              i_reg_rresp_rdy,
  output logic              o_reg_rresp_error,
  output logic [DW-1:0]     o_reg_rresp_data,

  ////// AHB master
    // AHB slave
  output logic              o_hsel,
  output logic  [32-1:0]    o_haddr,
  output logic  [3-1:0]     o_hsize,
  output logic  [1:0]       o_htrans,
  output logic              o_hready,
  output logic              o_hwrite,
  output logic  [DW-1: 0]   o_hwdata,
  input  logic  [DW-1:0]    i_hrdata,
  input  logic  [1:0]       i_hresp,
  input  logic              i_hready_resp
);

  typedef struct packed {
    logic [AW-1:0] addr;
    logic [DW-1:0] data;
    logic [(DW/8)-1:0] strb;
    logic we;
  } req_t;

  req_t wr_req, rd_req;
  req_t arb_req;
  logic arb_vld, arb_rdy;
  logic stall_n;

  always_comb wr_req.addr = i_reg_waddr;
  always_comb wr_req.data = i_reg_wdata;
  always_comb wr_req.strb = i_reg_wstrb;
  always_comb wr_req.we   = 1'b1;

  always_comb rd_req.addr = i_reg_raddr;
  always_comb rd_req.data = '0;
  always_comb rd_req.strb = '0;
  always_comb rd_req.we   = 1'b0;

  // round robin over the read and write stream:
  cc_stream_round_robin_arbiter #(
    .data_t(req_t),
    .N_INP(2),
    .ARBITER("rr") // "rr" or "prio"
  ) u_arb (
    .i_clk(i_clk),
    .i_rst_n(i_rst_n),

    .inp_data_i({wr_req,rd_req}),
    .inp_valid_i({i_reg_wvld, i_reg_rvld}),
    .inp_ready_o({o_reg_wrdy, o_reg_rrdy}),

    .oup_data_o(arb_req),
    .oup_valid_o(arb_vld),
    .oup_ready_i(arb_rdy)
  );

  // generate and connect stall:
  always_comb stall_n = i_hready_resp && i_reg_wresp_rdy && i_reg_rresp_rdy;
  always_comb arb_rdy = stall_n;

  // delay write data:
  reg [DW-1:0] wdata_q;
  reg req_vld_q;
  reg req_we_q;
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (i_rst_n == 1'b0) begin
      wdata_q <= '0;
      req_vld_q <= 1'b0;
      req_we_q <= 1'b0;
    end else begin
      if (arb_vld && arb_req.we && stall_n)
        wdata_q <= arb_req.data;
      if ((arb_vld || req_vld_q) && stall_n) begin
        req_vld_q <= arb_vld;
        req_we_q <= arb_req.we;
      end
    end
  end

  // strb to size:
  logic [2:0] ahb_size;
  if (DW == 32) begin : g_dw32
    always_comb
      unique case (arb_req.strb)
        'h01, 'h02, 'h04, 'h08 : ahb_size = 0;
        'h03, 'h0c             : ahb_size = 1;
        'h0f                   : ahb_size = 2;
        default : ahb_size = 2;
      endcase
  end else if (DW == 64) begin : g_dw64
    always_comb
      unique case (arb_req.strb)
      'h01, 'h02, 'h04, 'h08, 'h10, 'h20, 'h40, 'h80 : ahb_size = 0;
      'h03, 'h0c, 'h30, 'hc0 : ahb_size = 1;
      'h0f, 'hf0 : ahb_size = 2;
      'hff : ahb_size = 3;
      default : ahb_size = 3;
    endcase
  end

  // output assignments:
  always_comb begin
    // AHB:
    o_hsel    = 1'b1; // only one slave, so always select
    o_haddr   = arb_req.addr[31:0];
    o_hsize   = ahb_size;
    o_htrans  = arb_vld ? 2'b10 : 2'b00; // non seq when valid, else idle
    o_hready  = i_reg_wresp_rdy & i_reg_rresp_rdy;
    o_hwrite  = arb_req.we;
    o_hwdata  = wdata_q; // delayed version, as it's in data phase

    // reg response:
    o_reg_rresp_error = |i_hresp;
    o_reg_rresp_data  = i_hrdata;
    o_reg_rresp_vld   = req_vld_q & (~req_we_q) & stall_n;

    o_reg_wresp_error = |i_hresp;
    o_reg_wresp_vld   = req_vld_q & req_we_q & stall_n;
  end

endmodule
