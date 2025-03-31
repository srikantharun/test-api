// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Stefan Mach <stefan.mach@axelera.ai>

// TODO(@stefan.mach): Ensure SRAM is latching & remove spill reg
/// Sliced memory that serves as `c` storage in the DPU, configured to hold two pword64fp18 at each
/// memory address (referred to as the two "halves" of the memory). Only one slice can be written to
/// at a time, while all slices have independent read ports - synchronizing them must be done in the
/// surrounding circuitry. The memory slices are single-ported and writes always take priority over
/// reads.
module dpu_dp_cstore
  import dpu_pkg::*;
#(
  parameter  int unsigned NumSlices   = 2,
  // Dependent parameter
  localparam int unsigned SLICE_IDX_W = cc_math_pkg::index_width(NumSlices)
) (
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  // Independent read request ports
  input  c_addr_t [NumSlices-1:0] raddr_i,      // Data read address per slice
  input  logic    [NumSlices-1:0] raddr_vld_i,
  output logic    [NumSlices-1:0] raddr_rdy_o,

  // Independent read data ports
  output pw_dpu_fp_t [NumSlices-1:0] rdata_o,      // Output is sliced
  output logic       [NumSlices-1:0] rdata_vld_o,
  input  logic       [NumSlices-1:0] rdata_rdy_i,

  // Read dependency tracking information
  input logic [C_DEPTH-1:0][NumSlices-1:0] addr_dirty_i,  // addr hazard, 1b per slice location

  // Write port
  input  c_addr_t                      waddr_i,      // Data write address
  input  logic       [SLICE_IDX_W-1:0] waddr_idx_i,  // Slice index to write
  input  pw_dpu_fp_t                   wdata_i,      // Input
  input  logic                         waddr_vld_i,
  output logic                         waddr_rdy_o,

  // Memory SRAM sideband signals
  input  axe_tcl_sram_pkg::impl_inp_t sram_impl_i,
  output axe_tcl_sram_pkg::impl_oup_t sram_impl_o
);

  // Write Request
  // ==============
  // Individual slice write requests, only applies to one slice as indicated by `waddr_idx_i`.
  logic [NumSlices-1:0] mem_wr_req;
  assign mem_wr_req  = NumSlices'(waddr_vld_i) << waddr_idx_i;  // directly to slice
  // Write port is always ready due to priority
  assign waddr_rdy_o = 1'b1;

  // Shared Address Port
  // ====================
  c_addr_t [NumSlices-1:0] mem_addr;
  // Arbitrate access to the memory port, write port is always ready and has priority. Write only
  // applies to one slice of the storage as indicated by `waddr_idx_i`.
  always_comb begin : addr_port
    foreach (mem_addr[i]) mem_addr[i] = mem_wr_req[i] ? waddr_i : raddr_i[i];
  end

  // Read Request
  // =============
  // TODO(@stefan.mach): consider forwarding
  logic [NumSlices-1:0] mem_rd_req;
  logic [NumSlices-1:0] rdy;  // internal rdy essentially means "not stalled"
  always_comb begin : read_addr_rdy
    // Read requests are stalled by writes, external dependency tracking, default ready if no req.
    foreach (rdy[i]) rdy[i] = ~mem_wr_req[i] & ~addr_dirty_i[raddr_i[i]][i] | ~raddr_vld_i[i];
  end

  // Elastic register after the memory to absorb backpressure - separate slices
  logic [NumSlices-1:0] elastic_reg_rdy;

  // Back-pressureable read request - we can only service read requests if the elastic register will
  // have room for them and the write port is not used. Default ready allows us to depend on ready.
  assign mem_rd_req  = raddr_vld_i & rdy & elastic_reg_rdy;
  // Gate upstream ready using downstream ready (default ready)
  assign raddr_rdy_o = rdy & elastic_reg_rdy;

  // Memory Slice Control
  // =====================
  logic       [NumSlices-1:0] mem_req;  // memory enable
  pw_dpu_fp_t [NumSlices-1:0] mem_rdata;
  // Enable memory when there is an access (write or read) to the respective slice
  assign mem_req = mem_wr_req | mem_rd_req;

  // Interally banked
  axe_tcl_sram_pkg::impl_inp_t [NumSlices-1:0] sram_impl_inp;
  axe_tcl_sram_pkg::impl_oup_t [NumSlices-1:0] sram_impl_oup;
  axe_tcl_sram_cfg #(
    .NUM_SRAMS(NumSlices)
  ) u_sram_cfg_impl (
    .i_s(sram_impl_i),
    .o_s(sram_impl_o),
    .o_m(sram_impl_inp),
    .i_m(sram_impl_oup)
  );

  // Sliced memory instances for split writes, read/write latency is 1 cycle
  localparam int unsigned ByteEnableWidth = ($bits(pw_dpu_fp_t) + 7) / 8;
  axe_tcl_ram_1rwp #(
    .NumWords   (C_DEPTH),
    .DataWidth  ($bits(pw_dpu_fp_t)),
    .ByteWidth  (8),
    .ReadLatency(1),
    .ImplKey    ("HS_RVT"),
    .impl_inp_t (axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t (axe_tcl_sram_pkg::impl_oup_t)
  ) u_axe_tcl_sram[NumSlices-1:0] (
    .i_clk      (clk_i),
    .i_rst_n    (rst_ni),
    .i_req      (mem_req),
    .i_addr     (mem_addr),
    .i_wr_enable(mem_wr_req),
    .i_wr_data  (wdata_i),
    .i_wr_mask  ({ByteEnableWidth{1'b1}}),
    .o_rd_data  (mem_rdata),
    .i_impl     (sram_impl_inp),
    .o_impl     (sram_impl_oup)
  );

  // Read Data
  // ==========
  // Delay between read request and data production is one cycle, we handle backpressure below
  logic [NumSlices-1:0] rdata_vld, rdata_rdy;
  //`FF(rdata_vld, mem_rd_req, 1'b0, clk_i, rst_ni)
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rdata_vld <= '0;
    end else begin
      rdata_vld <= mem_rd_req;
    end
  end

  // Read data moves through elastic regs that can absorb one cycle of backpressure
  cc_stream_reg_el #(
    .data_t(pw_dpu_fp_t)
  ) u_elastic_reg[NumSlices-1:0] (
    .i_clk  (clk_i),
    .i_rst_n(rst_ni),
    .i_flush(1'b0),
    .i_data (mem_rdata),
    .i_valid(rdata_vld),
    .o_ready(rdata_rdy),         // not used as we ensure there is always room here
    .o_data (rdata_o),
    .o_valid(rdata_vld_o),
    .i_ready(elastic_reg_rdy)
  );

  // Makes downstream input ready by default -> deadlock prevention
  assign elastic_reg_rdy = rdata_rdy_i | ~rdata_vld_o;

  // synopsys translate_off
`ifdef ASSERTIONS_ON
  `include "prim_assert.sv"
  // Assert that read memory data can always be stored in the fallthrough reg
  `ASSERT_NEVER(fall_through_data_loss, rdata_vld & ~rdata_rdy, clk_i, !rst_ni)
`endif
  // synopsys translate_on

endmodule
