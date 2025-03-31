// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

/// Description: L1 fabric
// Source selection fabric for DMC and RVV traffic

module l1_tc_fabric
  import l1_pkg::*;
#(
  parameter uint_t NUM_DMC_SOURCES = 32'd2,
  parameter uint_t NUM_RVV_SOURCES = 32'd8,

  parameter uint_t NUM_BANKS = 32'd0,
  parameter uint_t NUM_SUB_BANKS = 1'b0,
  parameter uint_t MEM_ADDR_WIDTH = 22,
  parameter uint_t BANK_DATA_WIDTH = 128,
  localparam uint_t TOT_NUM_SOURCES = NUM_DMC_SOURCES + NUM_RVV_SOURCES,
  localparam uint_t SRC_SEL_W = $clog2(TOT_NUM_SOURCES)
) (
  input  wire                    i_clk,
  input  wire                    i_rst_n,

  // input sources, DMC and RVV
  input  logic [NUM_DMC_SOURCES-1:0] i_dmc_vld,
  output logic [NUM_DMC_SOURCES-1:0] o_dmc_rdy,
  input  logic [NUM_DMC_SOURCES-1:0][MEM_ADDR_WIDTH-1:0] i_dmc_addr,
  input  logic [NUM_RVV_SOURCES-1:0] i_rvv_vld,
  output logic [NUM_RVV_SOURCES-1:0] o_rvv_rdy,
  input  logic [NUM_RVV_SOURCES-1:0][MEM_ADDR_WIDTH-1:0] i_rvv_addr,

  // non-backpressurable memory source select:
  output logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0][SRC_SEL_W-1:0] o_src_sel,
  output logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0]                o_src_vld
);

  // mini bank addr creation:            byte_offset         + sub bank sel
  localparam uint_t ADDR_BANK_LSB     = $clog2(L1_SUB_BANK_WIDTH/8) + $clog2(NUM_SUB_BANKS);
  localparam uint_t ADDR_SUB_BANK_LSB = $clog2(L1_SUB_BANK_WIDTH/8);

  // Width of the bank select signal.
  localparam uint_t BANK_SEL_W = $clog2(NUM_BANKS);
  localparam uint_t SUB_BANK_SEL_W = $clog2(NUM_SUB_BANKS);

  ////////////////////////////////////////////
  /// DMC part to generate the source select:

  // bank selects
  logic [NUM_DMC_SOURCES-1:0][BANK_SEL_W-1:0] dmc_bank_select;
  // Generate the `bank_select` signal based on the address.
  // This generates a bank interleaved addressing scheme, where consecutive
  // addresses are routed to individual banks.
  for (genvar s = 0; unsigned'(s) < NUM_DMC_SOURCES; s++) begin : g_dmc_bank_select
    always_comb dmc_bank_select[s] = i_dmc_vld[s] ? i_dmc_addr[s][ADDR_BANK_LSB+:BANK_SEL_W] : '0;
  end
  logic [NUM_DMC_SOURCES-1:0][NUM_BANKS-1:0]                dmc_bank_dmx_vld;
  logic [NUM_DMC_SOURCES-1:0][NUM_BANKS-1:0]                dmc_bank_dmx_rdy;
  logic [NUM_BANKS-1:0][NUM_DMC_SOURCES-1:0]                dmc_bank_arb_in_vld;
  logic [NUM_BANKS-1:0][NUM_DMC_SOURCES-1:0]                dmc_bank_arb_in_rdy;
  logic [NUM_BANKS-1:0][NUM_DMC_SOURCES-1:0][SRC_SEL_W-1:0] dmc_bank_arb_in_src;
  logic [NUM_BANKS-1:0]                                     dmc_bank_arb_out_vld;
  logic [NUM_BANKS-1:0]                                     dmc_bank_arb_out_rdy;
  logic [NUM_BANKS-1:0][SRC_SEL_W-1:0]                      dmc_bank_arb_out_src;
  logic [NUM_BANKS-1:0][NUM_SUB_BANKS-1:0]                  dmc_bank_sbank_arb_out_vld;
  logic [NUM_BANKS-1:0][NUM_SUB_BANKS-1:0]                  dmc_bank_sbank_arb_out_rdy_nc;
  logic [NUM_BANKS-1:0][NUM_SUB_BANKS-1:0][SRC_SEL_W-1:0]   dmc_bank_sbank_arb_out_src;

  for (genvar s=0;unsigned'(s)<NUM_DMC_SOURCES;s++) begin: g_dmc_b_dmx
    cc_stream_demux #(
      .NumStreams(NUM_BANKS),
      .DropOnError(1)
    ) u_dmc_b_dmx (
      .i_valid(i_dmc_vld[s]),
      .o_ready(o_dmc_rdy[s]),
      .i_select(dmc_bank_select[s]),
      .o_error(), // ASO-UNUSED_OUTPUT: error not used
      .o_valid(dmc_bank_dmx_vld[s]),
      .i_ready(dmc_bank_dmx_rdy[s])
    );
    // Do the switching cross of the signals.
    for (genvar b = 0; unsigned'(b) < NUM_BANKS; b++) begin : g_arb_in
      // Propagate the data from this input to all outputs.
      assign dmc_bank_arb_in_src[b][s]  = s;
      // switch handshaking
      assign dmc_bank_arb_in_vld[b][s] = dmc_bank_dmx_vld[s][b];
      assign dmc_bank_dmx_rdy[s][b]    = dmc_bank_arb_in_rdy[b][s];
    end
  end

  for (genvar b=0;unsigned'(b)<NUM_BANKS;b++) begin: g_dmc_b_arb
    rr_arb_tree #(
      .NumIn(NUM_DMC_SOURCES),
      .DataWidth(SRC_SEL_W),
      .ExtPrio(1'b0), // 0 is round robin, 1 gives priority on rr_i
      .AxiVldRdy(1'b1), // simpler arbiter and normal vld/rdy behavior
      .LockIn(1'b1),
      .FairArb(1'b1)
    ) u_dmc_src_arb (
      .i_clk(i_clk),
      .i_rst_n(i_rst_n),
      .flush_i(1'b0),
      .rr_i  ('0),
      .req_i (dmc_bank_arb_in_vld[b]),
      .gnt_o (dmc_bank_arb_in_rdy[b]),
      .data_i(dmc_bank_arb_in_src[b]),
      .req_o (dmc_bank_arb_out_vld[b]),
      .gnt_i (dmc_bank_arb_out_rdy[b]),
      .data_o(dmc_bank_arb_out_src[b]),
      .idx_o ()  // ASO-UNUSED_OUTPUT: idx not used
    );
    always_comb begin
      dmc_bank_arb_out_rdy[b] = 1'b1; // after arb there is no backpressure for DMC, as it gets prio over RVV
      for (uint_t sb = 0; sb < NUM_SUB_BANKS; sb++) begin
        dmc_bank_sbank_arb_out_vld[b][sb] = dmc_bank_arb_out_vld[b];
        dmc_bank_sbank_arb_out_src[b][sb] = dmc_bank_arb_out_src[b];
      end
    end
  end

  ////////////////////////////////////////////
  /// RVV part to generate the source select:
  logic [NUM_RVV_SOURCES-1:0][SUB_BANK_SEL_W-1:0] rvv_sbank_select;
  logic [NUM_RVV_SOURCES-1:0][BANK_SEL_W-1:0]     rvv_bank_select;

  // Generate the `bank_select` signal based on the address.
  // This generates a bank interleaved addressing scheme, where consecutive
  // addresses are routed to individual banks.
  for (genvar s = 0; unsigned'(s) < NUM_RVV_SOURCES; s++) begin : g_rvv_bank_subbank_select
    always_comb rvv_sbank_select[s] = i_rvv_addr[s][ADDR_SUB_BANK_LSB+:(SUB_BANK_SEL_W)];
    always_comb rvv_bank_select[s]  = i_rvv_addr[s][ADDR_BANK_LSB+:(BANK_SEL_W)];
  end
  logic [NUM_RVV_SOURCES-1:0][NUM_SUB_BANKS-1:0]                               rvv_sbank_dmx_vld;
  logic [NUM_RVV_SOURCES-1:0][NUM_SUB_BANKS-1:0]                               rvv_sbank_dmx_rdy;
  logic [NUM_RVV_SOURCES-1:0][NUM_SUB_BANKS-1:0][NUM_BANKS-1:0]                rvv_bank_sbank_dmx_vld;
  logic [NUM_RVV_SOURCES-1:0][NUM_SUB_BANKS-1:0][NUM_BANKS-1:0]                rvv_bank_sbank_dmx_rdy;
  logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0][NUM_RVV_SOURCES-1:0]                rvv_bank_sbank_arb_in_vld;
  logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0][NUM_RVV_SOURCES-1:0]                rvv_bank_sbank_arb_in_rdy;
  logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0][NUM_RVV_SOURCES-1:0][SRC_SEL_W-1:0] rvv_bank_sbank_arb_in_src;
  logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0]                                     rvv_bank_sbank_arb_out_vld;
  logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0]                                     rvv_bank_sbank_arb_out_rdy;
  logic [NUM_SUB_BANKS-1:0][NUM_BANKS-1:0][SRC_SEL_W-1:0]                      rvv_bank_sbank_arb_out_src;

  for (genvar s=0;unsigned'(s)<NUM_RVV_SOURCES;s++) begin: g_rvv_b_dmx
    cc_stream_demux #(
      .NumStreams(NUM_SUB_BANKS),
      .DropOnError(1)
    ) u_rvv_sb_dmx (
      .i_valid(i_rvv_vld[s]),
      .o_ready(o_rvv_rdy[s]),
      .i_select(rvv_sbank_select[s]),
      .o_error(),  // ASO-UNUSED_OUTPUT: error not used
      .o_valid(rvv_sbank_dmx_vld[s]),
      .i_ready(rvv_sbank_dmx_rdy[s])
    );
    for (genvar sb = 0; unsigned'(sb) < NUM_SUB_BANKS; sb++) begin : g_rvv_sb_dmx_in
      cc_stream_demux #(
        .NumStreams(NUM_BANKS),
        .DropOnError(1)
      ) u_rvv_sb_dmx (
        .i_valid(rvv_sbank_dmx_vld[s][sb]),
        .o_ready(rvv_sbank_dmx_rdy[s][sb]),
        .i_select(rvv_bank_select[s]),
        .o_error(),  // ASO-UNUSED_OUTPUT: error not used
        .o_valid(rvv_bank_sbank_dmx_vld[s][sb]),
        .i_ready(rvv_bank_sbank_dmx_rdy[s][sb])
      );

      // Do the switching cross of the signals.
      for (genvar b = 0; unsigned'(b) < NUM_BANKS; b++) begin : g_arb_in
        // Propagate the data from this input to all outputs.
        assign rvv_bank_sbank_arb_in_src[sb][b][s]  = s+NUM_DMC_SOURCES;
        // switch handshaking
        assign rvv_bank_sbank_arb_in_vld[sb][b][s] = rvv_bank_sbank_dmx_vld[s][sb][b];
        assign rvv_bank_sbank_dmx_rdy[s][sb][b]    = rvv_bank_sbank_arb_in_rdy[sb][b][s];
      end
    end
  end

  for (genvar sb = 0; unsigned'(sb) < NUM_SUB_BANKS; sb++) begin : g_rvv_sb_arb
    for (genvar b = 0; unsigned'(b) < NUM_BANKS; b++) begin: g_rvv_b_arb
      rr_arb_tree #(
        .NumIn(NUM_RVV_SOURCES),
        .DataWidth(SRC_SEL_W),
        .ExtPrio(1'b0), // 0 is round robin, 1 gives priority on rr_i
        .AxiVldRdy(1'b1), // simpler arbiter and normal vld/rdy behavior
        .LockIn(1'b1),
        .FairArb(1'b1)
      ) u_rvv_src_arb (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .flush_i(1'b0),
        .rr_i  ('0),
        .req_i (rvv_bank_sbank_arb_in_vld[sb][b]),
        .gnt_o (rvv_bank_sbank_arb_in_rdy[sb][b]),
        .data_i(rvv_bank_sbank_arb_in_src[sb][b]),
        .req_o (rvv_bank_sbank_arb_out_vld[sb][b]),
        .gnt_i (rvv_bank_sbank_arb_out_rdy[sb][b]),
        .data_o(rvv_bank_sbank_arb_out_src[sb][b]),
        .idx_o () // ASO-UNUSED_OUTPUT: idx not used
      );
    end
  end

  for (genvar sb = 0; unsigned'(sb) < NUM_SUB_BANKS; sb++) begin : g_end_arb_b
    for (genvar b = 0; unsigned'(b) < NUM_BANKS; b++) begin: g_end_arb_sb
      // very simple arbitration, always give DMC priority.
      rr_arb_tree #(
        .NumIn(2),
        .DataWidth(SRC_SEL_W),
        .ExtPrio(1'b1), // 0 is round robin, 1 gives priority on rr_i
        .AxiVldRdy(1'b1), // simpler arbiter and normal vld/rdy behavior
        .LockIn(1'b0),
        .FairArb(1'b1)
      ) u_end_src_arb (
        .i_clk(i_clk),
        .i_rst_n(i_rst_n),
        .flush_i(1'b0),
        .rr_i  ('0), // priority on DMC
        .req_i ({rvv_bank_sbank_arb_out_vld[sb][b], dmc_bank_sbank_arb_out_vld[b][sb]}),
        .gnt_o ({rvv_bank_sbank_arb_out_rdy[sb][b], dmc_bank_sbank_arb_out_rdy_nc[b][sb]}),
        .data_i({rvv_bank_sbank_arb_out_src[sb][b], dmc_bank_sbank_arb_out_src[b][sb]}),
        .req_o (o_src_vld[sb][b]),
        .gnt_i (1'b1), // always accept, memory won't backpressure
        .data_o(o_src_sel[sb][b]),
        .idx_o () // ASO-UNUSED_OUTPUT: idx not used
      );
    end
  end
  logic all_nc;
  always_comb all_nc = |dmc_bank_sbank_arb_out_rdy_nc; // ASO-UNUSED_VARIABLE: not used

endmodule
