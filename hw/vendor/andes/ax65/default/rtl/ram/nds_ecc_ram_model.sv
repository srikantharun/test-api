/// Description: ECC RAM wrapper for AX65 Cluster
///
module nds_ecc_ram_model #(
    parameter WRITE_WIDTH = 64,
    parameter ADDR_WIDTH = 5,
    parameter OUT_DELAY = 0,
    parameter IN_DELAY = 0,
    parameter INJECT_ECC = 0,
    parameter INJECT_ECC_CORR = 0,
    parameter INIT_BY_ECC_INJECT = 0,
    parameter ECC_PROBABILITY = 30,
    parameter ENABLE = "yes",
    parameter CTRL_IN_WIDTH = 7,
    parameter CTRL_OUT_WIDTH = 1
) (
    input wire clk,
    input logic we,
    input logic cs,
    input logic [(ADDR_WIDTH - 1):0] addr,
    input logic [(WRITE_WIDTH - 1):0] din,
    output logic [(WRITE_WIDTH - 1):0] dout,
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
    .DataWidth(WRITE_WIDTH),
    .ByteWidth(WRITE_WIDTH),
    .ReadLatency(1),
    .ImplKey("HS_RVT"),
    .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
  ) u_axe_tcl_sram (
    .i_clk(clk),
    .i_rst_n(1'b1),
    .i_req(cs),
    .i_addr(addr),
    .i_wr_enable(we),
    .i_wr_data(din),
    .i_wr_mask(we),
    .o_rd_data(dout),
    .i_impl(impl_inp),
    .o_impl(impl_oup)
  );

endmodule
