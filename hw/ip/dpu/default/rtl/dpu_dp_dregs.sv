// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: dREGS block for dedicated LUT storage
// Owner: Tiago Campos <tiago.campos@axelera.ai>

module dpu_dp_dregs
  import dpu_pkg::*;
(
  input wire clk_i,  // Clock
  input wire rst_ni, // Reset active low

  // Read request ports
  input  d_addr_t  raddr_i,      // Register read address
  input  logic     raddr_vld_i,
  output logic     raddr_rdy_o,

  // Read data ports
  output pw_dpu_fp_t  rdata_o,      // Output data
  output logic        rdata_vld_o,
  input  logic        rdata_rdy_i,

  // Read dependency tracking information
  input logic [D_DEPTH-1:0] addr_dirty_i,  // addr hazard, 1b per register

  // Write port
  input  d_addr_t    waddr_i,      // Register write address
  input  pw_dpu_fp_t wdata_i,      // Input data
  input  logic       waddr_vld_i,
  output logic       waddr_rdy_o
);

  // The actual FF storage
  pw_dpu_fp_t [D_DEPTH-1:0] regs;
  // Write side / the actual storage
  //`FFLNR(regs[waddr_i], wdata_i, waddr_vld_i, clk_i)
  always_ff @(posedge clk_i) begin
    if (waddr_vld_i) begin
      regs[waddr_i] <= (wdata_i);
    end
  end
  // Write is always possible
  assign waddr_rdy_o = 1'b1;

  // Read side
  // Combinational data reads
  logic rdy, fwd;
  pw_dpu_fp_t rdata;

  // TODO(@stefan.mach): consider using the regfile as the ID/ISS pipe stage & just pipe the request signals!
  assign fwd   = waddr_vld_i & (raddr_i == waddr_i);
  assign rdata = fwd ? wdata_i : regs[raddr_i];
  // Read requests are stalled by external dependency tracking, default ready, allowed when fwding
  assign rdy   = ~addr_dirty_i[raddr_i] | fwd;

  // Internal handshake between comb read and spill regs
  logic spill_reg_vld, spill_reg_rdy;
  // The read of the regs is considered successful if all requests can be handled
  // The default-ready behavior of the spill register allows us to depend on the ready here
  assign spill_reg_vld = raddr_vld_i & rdy & spill_reg_rdy;
  // Gate upstream ready using downstream ready
  assign raddr_rdy_o   = rdy & spill_reg_rdy;

  // Simplified control scheme: Read data moves as one unit through the pipe
  // TODO(@stefan.mach): make individual enables for switching power as in cstore!
  // TODO(@stefan.mach): why not a simple stream_reg??
  cc_stream_spill_reg #(
    .data_t(pw_dpu_fp_t)
  ) u_spill_reg (
    .i_clk  (clk_i),
    .i_rst_n(rst_ni),
    .i_flush(1'b0),
    .i_valid(spill_reg_vld),
    .o_ready(spill_reg_rdy),
    .i_data (rdata),
    .o_valid(rdata_vld_o),
    .i_ready(rdata_rdy_i),
    .o_data (rdata_o)
  );

endmodule
