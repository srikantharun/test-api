// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L1 sub_bank, containing all banked macro's for that sub_bank
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module l1_sub_bank
  import axe_tcl_sram_pkg::*, l1_pkg::*;
# (
  parameter uint_t L1_NUM_BANKS = 16,
  parameter uint_t L1_MACROS_PER_MINI_BANK = 1,

  parameter uint_t TOT_NUM_SOURCES = 18,
  localparam uint_t SRC_SEL_W = $clog2(TOT_NUM_SOURCES),
  localparam uint_t MINI_BANK_ADDR_WIDTH = L1_MACRO_ADDR_WIDTH + $clog2(L1_MACROS_PER_MINI_BANK)
) (
  // Clock signal
  input  wire       i_clk,
  input  wire       i_rst_n,

  input  logic     [L1_NUM_BANKS-1:0][SRC_SEL_W-1:0]            i_src_sel,
  input  logic     [L1_NUM_BANKS-1:0]                           i_src_vld,
  input  logic     [TOT_NUM_SOURCES-1:0][MINI_BANK_ADDR_WIDTH-1:0] i_src_req_addr,
  input  mem_req_t [TOT_NUM_SOURCES-1:0]                           i_src_req,
  output mem_rsp_t [TOT_NUM_SOURCES-1:0]                           o_src_rsp,

  input  impl_inp_t [L1_NUM_BANKS-1:0][L1_MACROS_PER_MINI_BANK-1:0] i_mem_impl,
  output impl_oup_t [L1_NUM_BANKS-1:0][L1_MACROS_PER_MINI_BANK-1:0] o_mem_impl
);
  localparam uint_t BANK_SEL_W = $clog2(L1_NUM_BANKS);

  logic     [L1_NUM_BANKS-1:0][MINI_BANK_ADDR_WIDTH-1:0] bank_req_addr;
  logic     [L1_NUM_BANKS-1:0][MINI_BANK_ADDR_WIDTH-1:0] bank_req_addr_q;
  mem_req_t [L1_NUM_BANKS-1:0]                           bank_req;
  mem_req_t [L1_NUM_BANKS-1:0]                           bank_req_q;
  mem_rsp_t [L1_NUM_BANKS-1:0]                           bank_rsp;

  logic [L1_NUM_BANKS-1:0]                              ce;
  logic [L1_NUM_BANKS-1:0]                              we;
  logic [L1_NUM_BANKS-1:0] [L1_SUB_BANK_WBE_WIDTH-1:0]  wbe;
  logic [L1_NUM_BANKS-1:0] [MINI_BANK_ADDR_WIDTH-1:0]   addr;
  logic [L1_NUM_BANKS-1:0] [L1_SUB_BANK_WIDTH-1:0]      wdata;

  logic [L1_NUM_BANKS-1:0] [L1_SUB_BANK_WIDTH-1:0]      rdata;
  logic [L1_NUM_BANKS-1:0]                              rdata_vld;

  reg [L1_NUM_BANKS-1:0] [L1_SUB_BANK_WIDTH-1:0]        rdata_q;
  reg [L1_NUM_BANKS-1:0]                                rdata_vld_q;


  logic [L1_NUM_BANKS-1:0]                      rsp_track_wr_vld;
  logic [L1_NUM_BANKS-1:0][SRC_SEL_W-1:0]       rsp_track_wr_data;
  logic [L1_NUM_BANKS-1:0]                      rsp_track_rd_vld;
  logic [TOT_NUM_SOURCES-1:0][L1_NUM_BANKS-1:0] rsp_track_rd_rdy_srced;
  logic [L1_NUM_BANKS-1:0][TOT_NUM_SOURCES-1:0] rsp_track_rd_rdy;
  logic [L1_NUM_BANKS-1:0][SRC_SEL_W-1:0]       rsp_track_rd_data;

  for (genvar s=0; s<TOT_NUM_SOURCES; s++) begin: g_nc
    logic src_vld_nc;
    always_comb src_vld_nc = i_src_req[s].valid; //ASO-UNUSED_VARIABLE: this valid is not used anymore at this stage
  end

  // =====================================================
  // Bank driving muxes
  // =====================================================
  for (genvar b=0; uint_t'(b)<L1_NUM_BANKS; b++) begin : g_req
    always_comb begin : breq_mux
      bank_req[b] = '0;
      bank_req_addr[b] = '0;
      rsp_track_wr_vld[b] = '0;
      rsp_track_wr_data[b] = '0;
      if (i_src_vld[b]) begin
        for (uint_t s=0; s<TOT_NUM_SOURCES; s++) begin
          if(s == i_src_sel[b]) begin
            bank_req[b].payload |= i_src_req[s].payload;
            bank_req[b].valid   |= 1'b1;
            bank_req_addr[b]    |= i_src_req_addr[s];

            // track response driver:
            rsp_track_wr_data[b] |= s;
            rsp_track_wr_vld[b]  |= 1'b1;
          end
        end
      end
    end

    // save source select for response:
    cc_stream_buffer #(
      .DEPTH(L1_SUB_BANK_MAX_LATENCY), // depth should be enough to cover them all, there won't be backpressure appliedif not
      .DW(SRC_SEL_W)
    ) u_rsp_track (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),

      .wr_vld(rsp_track_wr_vld[b]),
      .wr_data(rsp_track_wr_data[b]),
      .wr_rdy(), // ASO-UNUSED_OUTPUT: not used

      .rd_rdy(|rsp_track_rd_rdy[b]),
      .rd_data(rsp_track_rd_data[b]),
      .rd_vld(rsp_track_rd_vld[b])
    );
  end

  for (genvar s=0; uint_t'(s)<TOT_NUM_SOURCES; s++) begin : g_rsp
    // Mux response data into source return path:
    always_comb begin : srsp_mux
      o_src_rsp[s] = '0;
      rsp_track_rd_rdy_srced[s] = '0;

      for (uint_t b=0; b<L1_NUM_BANKS; b++) begin

        if((s == rsp_track_rd_data[b]) && rsp_track_rd_vld[b] && bank_rsp[b].valid) begin
          o_src_rsp[s].data = bank_rsp[b].data; // wire bank data on source response
          o_src_rsp[s].valid = 1'b1;
          rsp_track_rd_rdy_srced[s][b] = 1'b1; // pop entry from FIFO
        end
      end
    end
    for (genvar b=0; uint_t'(b)<L1_NUM_BANKS; b++) begin : g_rdy_reroute
      always_comb rsp_track_rd_rdy[b][s] = rsp_track_rd_rdy_srced[s][b];
    end
  end

  for (genvar b = 0; uint_t'(b) < L1_NUM_BANKS; b++) begin : g_mini_bank
    // wiring from/into request:

    // pre bank pipe:
    cc_cnt_shift_reg #(
      .data_t(req_payload_t),
      .Stages(1)
    ) u_pre_pipe_req (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_clear(1'b0),
      .i_stall(1'b0),
      .i_data(bank_req[b].payload),
      .i_data_en(bank_req[b].valid),
      .o_data(bank_req_q[b].payload),
      .o_updated(bank_req_q[b].valid)
    );
    cc_cnt_shift_reg #(
      .Width(MINI_BANK_ADDR_WIDTH),
      .Stages(1)
    ) u_pre_pipe_addr (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_clear(1'b0),
      .i_stall(1'b0),
      .i_data(bank_req_addr[b]),
      .i_data_en(bank_req[b].valid),
      .o_data(bank_req_addr_q[b]),
      .o_updated() // ASO-UNUSED_OUTPUT: not used
    );

    always_comb begin
      ce[b] = bank_req_q[b].valid;
      we[b] = bank_req_q[b].payload.we;
      wbe[b] = bank_req_q[b].payload.wbe;
      addr[b] = bank_req_addr_q[b];
      wdata[b] = bank_req_q[b].payload.data;

      bank_rsp[b].valid = rdata_vld_q[b];
      bank_rsp[b].data = rdata_q[b];
    end

    l1_mini_bank #(
      .L1_MACROS_PER_MINI_BANK(L1_MACROS_PER_MINI_BANK)
    ) u_mini_bank (
      // Clock signal
      .i_clk    (i_clk),
      .i_rst_n  (i_rst_n),
      // RAM interface signals
      .i_ce       (ce[b]),
      .i_we       (we[b]),
      .i_wbe      (wbe[b]),
      .i_addr     (addr[b]),
      .i_wdata    (wdata[b]),
      .o_rdata    (rdata[b]),
      .o_rdata_vld(rdata_vld[b]),

      .i_mem_impl (i_mem_impl[b]),
      .o_mem_impl (o_mem_impl[b])
    );

    // post bank pipe:
    cc_cnt_shift_reg #(
      .Width(L1_SUB_BANK_WIDTH),
      .Stages(1)
    ) u_post_pipe (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .i_clear(1'b0),
      .i_stall(1'b0),
      .i_data(rdata[b]),
      .i_data_en(rdata_vld[b]),
      .o_data(rdata_q[b]),
      .o_updated(rdata_vld_q[b])
    );
  end : g_mini_bank

endmodule
