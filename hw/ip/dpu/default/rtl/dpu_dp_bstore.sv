// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: bSTORE block instatiates implements multiple banks of
// dual port regfile for narrow memory.
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>
// TODO(@stefan.mach): Ensure SRAM is latching & remove elastic reg


module dpu_dp_bstore
  import dpu_pkg::*;
(
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  // Read request port
  input  b_addr_t raddr_i,      // Data read address
  input  logic    raddr_vld_i,
  output logic    raddr_rdy_o,

  // Read data port
  output pw_dpu_fp_t rdata_o,      // Output
  output logic       rdata_vld_o,
  input  logic       rdata_rdy_i,

  // Read dependency tracking information
  input logic [B_DEPTH-1:0] addr_dirty_i,  // addr hazard, 1b per location

  // Write port
  input  b_addr_t    waddr_i,      // Data write address
  input  pw_dpu_fp_t wdata_i,      // Input
  input  logic       waddr_vld_i,
  output logic       waddr_rdy_o,

  // Memory SRAM sideband signals
  input  axe_tcl_sram_pkg::impl_inp_t sram_impl_i,
  output axe_tcl_sram_pkg::impl_oup_t sram_impl_o
);

  // Write Request
  // ==============
  // Write port is always ready
  assign waddr_rdy_o = 1'b1;

  // Read Request
  // =============
  logic raddr_vld, fwd_vld;
  logic rdy, fwd;
  // FWD is only possible if no regular read data is being produced
  assign fwd = waddr_vld_i & raddr_i == waddr_i;
  // Read requests are stalled by external dependency tracking, default ready, allowed when fwding
  assign rdy = ~addr_dirty_i[raddr_i] | ~raddr_vld_i | fwd;

  // Elastic register after the memory to absorb backpressure
  logic elastic_reg_rdy;
  // Back-pressureable read request - we can only service read requests if the elastic register will
  // have room for them. FWD bypasses the memory. Default ready allows us to depend on ready.
  assign raddr_vld   = raddr_vld_i & ~fwd & rdy & elastic_reg_rdy;
  assign fwd_vld     = raddr_vld_i & fwd & elastic_reg_rdy;
  // Gate upstream ready using downstream ready (default ready)
  assign raddr_rdy_o = rdy & elastic_reg_rdy;

  // Memory Slice Control
  // =====================
  pw_dpu_fp_t rdata_mem, rdata_fwd;

  // Memory instance, read/write latency is 1 cycle
  axe_tcl_ram_1rp_1wp #(
    .NumWords   (B_DEPTH),
    .DataWidth  ($bits(pw_dpu_fp_t)),
    .ByteWidth  (8),
    .ReadLatency(1),
    .ImplKey    ("HS_RVT"),
    .impl_inp_t (axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t (axe_tcl_sram_pkg::impl_oup_t)
  ) u_axe_tcl_sram (
    .i_wr_clk  (clk_i),
    .i_wr_rst_n(rst_ni),
    .i_wr_req  (waddr_vld_i),
    .i_wr_addr (waddr_i),
    .i_wr_data (wdata_i),
    .i_wr_mask ('1),
    .i_rd_clk  (clk_i),
    .i_rd_rst_n(rst_ni),
    .i_rd_req  (raddr_vld),
    .i_rd_addr (raddr_i),
    .o_rd_data (rdata_mem),
    .i_impl    (sram_impl_i),
    .o_impl    (sram_impl_o)
  );

  // Bypass Register, to match latency of 1 cycle (and break comb path)
  // FFLNR: D-Flip-Flop, load enable, no reset
  always_ff @(posedge clk_i) begin
    if (fwd_vld) rdata_fwd <= wdata_i;
  end

  // Read Data
  // ==========
  // Delay between read request and data production is one cycle, we handle backpressure below
  logic rdata_vld, rdata_mem_vld, rdata_fwd_vld, rdata_rdy;
  // FFL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_mem_vld <= 1'b0;
      rdata_fwd_vld <= 1'b0;
    end else begin
      // TODO(@stefan.mach): load-enable flop on rdata_rdy (only if rdata stays stable)
      rdata_mem_vld <= raddr_vld;
      rdata_fwd_vld <= fwd_vld;
    end
  end

  // Select read data according to valid source
  pw_dpu_fp_t rdata;
  assign rdata     = rdata_mem_vld ? rdata_mem : rdata_fwd;
  assign rdata_vld = rdata_mem_vld | rdata_fwd_vld;

  // Read data moves through elastic regs that can absorb one cycle of backpressure
  cc_stream_reg_el #(
    .data_t(pw_dpu_fp_t)
  ) u_elastic_reg (
    .i_clk  (clk_i),
    .i_rst_n(rst_ni),
    .i_flush(1'b0),
    .i_data (rdata),
    .i_valid(rdata_vld),
    .o_ready(rdata_rdy),
    .o_data (rdata_o),
    .o_valid(rdata_vld_o),
    .i_ready(elastic_reg_rdy)
  );

  // Makes downstream input ready by default -> deadlock prevention
  assign elastic_reg_rdy = rdata_rdy_i | ~rdata_vld_o;

  // synopsys translate_off
`ifdef ASSERTIONS_ON
  `include "prim_assert.sv"
  // Assert that dual port contention never happens - failure in dependency tracking!
  `ASSERT_NEVER(bstore_contention, waddr_vld_i && raddr_vld && waddr_i == raddr_i, clk_i, !rst_ni)
  // Assert that read memory data can always be stored in the fallthrough reg
  `ASSERT_NEVER(fall_through_data_loss, rdata_vld & ~rdata_rdy, clk_i, !rst_ni)
  // Assert that memory data and forward data never collide (given, mutex and not stallable)
  `ASSERT_NEVER(fwd_collision, rdata_mem_vld & rdata_fwd_vld, clk_i, !rst_ni)
`endif
  // synopsys translate_on

endmodule
