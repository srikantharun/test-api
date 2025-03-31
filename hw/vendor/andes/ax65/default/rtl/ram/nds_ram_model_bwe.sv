/// Description: RAM bwe wrapper for AX65 Cluster
///
module nds_ram_model_bwe #(
    parameter ADDR_WIDTH = 5,
    parameter DATA_BYTE = 4,
    parameter IN_DELAY = 0,
    parameter OUT_DELAY = 1,
    parameter [0:0] HOLD_DOUT = 1'b1,
    parameter ENABLE = "yes",
    parameter BIT_PER_BYTE = 8,
    parameter ImplKey = "HS_RVT",
    parameter CTRL_IN_WIDTH = 7,
    parameter CTRL_OUT_WIDTH = 1
) (
    input  wire                                   clk,
    input  logic                                  cs,
    input  logic [              (DATA_BYTE- 1):0] bwe,
    input  logic [            (ADDR_WIDTH - 1):0] addr,
    input  logic [(BIT_PER_BYTE*DATA_BYTE - 1):0] din,
    output logic [(BIT_PER_BYTE*DATA_BYTE - 1):0] dout,
    input  logic [(CTRL_IN_WIDTH) - 1:0] ctrl_in,
    output logic [(CTRL_OUT_WIDTH) - 1:0] ctrl_out
);

  if (CTRL_IN_WIDTH  != $bits(axe_tcl_sram_pkg::impl_inp_t)) $fatal(1, "Parameter 'CTRL_IN_WIDTH' does not match impl_inp_t");
  if (CTRL_OUT_WIDTH != $bits(axe_tcl_sram_pkg::impl_oup_t)) $fatal(1, "Parameter 'CTRL_OUT_WIDTH' does not match impl_oup_t");

  localparam int unsigned NUM_WORDS = 2 ** ADDR_WIDTH;
  localparam int unsigned DATA_WIDTH = DATA_BYTE * BIT_PER_BYTE;
  axe_tcl_sram_pkg::impl_inp_t impl_inp;
  axe_tcl_sram_pkg::impl_oup_t impl_oup;

  // Memory configuration pins
  always_comb impl_inp = ctrl_in;
  always_comb ctrl_out = impl_oup;

  if ((NUM_WORDS == 2048) && (DATA_WIDTH == 576)) begin
    /// Split the memory into smaller datawidth instances if the DATA_WIDTH is greater than 160 bits
    /// L2C DATA RAM is 2048x576
    /// split into 4*144
    localparam int unsigned DATA_WIDTH_MEM = 144;  // Each memory is 144 bits wide
    localparam int unsigned NUM_MEMS = DATA_WIDTH / DATA_WIDTH_MEM;  // 576 / 144 = 4
    localparam int unsigned NUM_BWE_PER_MEM = (DATA_WIDTH/BIT_PER_BYTE)/NUM_MEMS; // 576 / 8 / 4 = 18

    axe_tcl_sram_pkg::impl_inp_t [NUM_MEMS-1:0] impl_inp_mems;
    axe_tcl_sram_pkg::impl_oup_t [NUM_MEMS-1:0] impl_oup_mems;

    axe_tcl_sram_cfg #(
      .NUM_SRAMS(NUM_MEMS)
    ) u_sram_cfg (
      .i_s(impl_inp),
      .o_s(impl_oup),
      .o_m(impl_inp_mems),
      .i_m(impl_oup_mems)
    );

    logic [DATA_WIDTH_MEM-1:0] din_mems [NUM_MEMS-1:0];
    logic [DATA_WIDTH_MEM-1:0] dout_mems[NUM_MEMS-1:0];
    logic [NUM_BWE_PER_MEM-1:0] bwe_mems[NUM_MEMS-1:0];

    for (genvar idx = 0; idx < NUM_MEMS; idx++) begin: gen_banks
      always_comb din_mems[idx] = din[DATA_WIDTH_MEM*idx+:DATA_WIDTH_MEM];
      always_comb bwe_mems[idx] = bwe[NUM_BWE_PER_MEM*idx+:NUM_BWE_PER_MEM];
      axe_tcl_ram_1rwp #(
        .NumWords(NUM_WORDS),
        .DataWidth(DATA_WIDTH_MEM),
        .ByteWidth(BIT_PER_BYTE),
        .ReadLatency(1),
        .ImplKey(ImplKey),
        .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
        .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
      ) u_axe_tcl_sram (
        .i_clk(clk),
        .i_rst_n(1'b1),
        .i_req(cs),
        .i_addr(addr),
        .i_wr_enable(|bwe_mems[idx]),
        .i_wr_data(din_mems[idx]),
        .i_wr_mask(bwe_mems[idx]),
        .o_rd_data(dout_mems[idx]),
        .i_impl(impl_inp_mems[idx]),
        .o_impl(impl_oup_mems[idx])
      );
      always_comb dout[DATA_WIDTH_MEM*idx+:DATA_WIDTH_MEM] = dout_mems[idx];
    end
  end
  else begin
    axe_tcl_ram_1rwp #(
      .NumWords(NUM_WORDS),
      .DataWidth(DATA_WIDTH),
      .ByteWidth(BIT_PER_BYTE),
      .ReadLatency(1),
      .ImplKey(ImplKey),
      .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
      .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
    ) u_axe_tcl_sram (
      .i_clk(clk),
      .i_rst_n(1'b1),
      .i_req(cs),
      .i_addr(addr),
      .i_wr_enable(|bwe),
      .i_wr_data(din),
      .i_wr_mask(bwe),
      .o_rd_data(dout),
      .i_impl(impl_inp),
      .o_impl(impl_oup)
    );
  end

endmodule
