/// Description: RAM we wrapper for AX65 Cluster
///
module nds_ram_model_bit_we #(
    parameter ADDR_WIDTH = 5,
    parameter DATA_WIDTH = 32,
    parameter OUT_DELAY = 1,
    parameter [0:0] HOLD_DOUT = 1'b1,
    parameter ENABLE = "yes",
    parameter ImplKey = "HS_RVT",
    parameter CTRL_IN_WIDTH = 7,
    parameter CTRL_OUT_WIDTH = 1
) (
    input wire clk,
    input logic cs,
    input logic [(DATA_WIDTH - 1):0] we,
    input logic [(ADDR_WIDTH - 1):0] addr,
    input logic [(DATA_WIDTH - 1):0] din,
    output logic [(DATA_WIDTH - 1):0] dout,
    input logic [(CTRL_IN_WIDTH) - 1:0] ctrl_in,
    output logic [(CTRL_OUT_WIDTH) - 1:0] ctrl_out
);

  if (CTRL_IN_WIDTH  != $bits(axe_tcl_sram_pkg::impl_inp_t)) $fatal(1, "Parameter 'CTRL_IN_WIDTH' does not match impl_inp_t");
  if (CTRL_OUT_WIDTH != $bits(axe_tcl_sram_pkg::impl_oup_t)) $fatal(1, "Parameter 'CTRL_OUT_WIDTH' does not match impl_oup_t");

  localparam int unsigned NUM_WORDS = 2 ** ADDR_WIDTH;
  axe_tcl_sram_pkg::impl_inp_t impl_inp;
  axe_tcl_sram_pkg::impl_oup_t impl_oup;

  // Memory configuration pins
  always_comb impl_inp = ctrl_in;
  always_comb ctrl_out = impl_oup;

  axe_tcl_ram_1rwp #(
    .NumWords(NUM_WORDS),
    .DataWidth(DATA_WIDTH),
    .ByteWidth(1),
    .ReadLatency(1),
    .ImplKey(ImplKey),
    .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
  ) u_axe_tcl_sram (
    .i_clk(clk),
    .i_rst_n(1'b1),
    .i_req(cs),
    .i_addr(addr),
    .i_wr_enable(|we),
    .i_wr_data(din),
    .i_wr_mask(we),
    .o_rd_data(dout),
    .i_impl(impl_inp),
    .o_impl(impl_oup)
  );

endmodule
