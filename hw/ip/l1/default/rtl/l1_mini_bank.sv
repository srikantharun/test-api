// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: L1 mini bank, containing macro's to fullfill the mini bank requirement
//
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module l1_mini_bank
  import axe_tcl_sram_pkg::*, l1_pkg::*;
# (
  parameter uint_t L1_MACROS_PER_MINI_BANK = 1,
  localparam uint_t MINI_BANK_ADDR_WIDTH = L1_MACRO_ADDR_WIDTH + $clog2(L1_MACROS_PER_MINI_BANK)
) (
  // Clock and reset signal
  input  wire                         i_clk,
  input  wire                         i_rst_n,
  // RAM interface signals
  input  logic                              i_ce,
  input  logic                              i_we,
  input  logic [MINI_BANK_ADDR_WIDTH-1:0]   i_addr,
  input  logic [L1_SUB_BANK_WIDTH-1:0]      i_wdata,
  input  logic [L1_SUB_BANK_WBE_WIDTH-1:0]  i_wbe,
  output logic [L1_SUB_BANK_WIDTH-1:0]      o_rdata,
  output logic                              o_rdata_vld,

  input  impl_inp_t [L1_MACROS_PER_MINI_BANK-1:0] i_mem_impl,
  output impl_oup_t [L1_MACROS_PER_MINI_BANK-1:0] o_mem_impl
);

  // =====================================================
  // Signal declarations
  // =====================================================
  logic [L1_MACROS_PER_MINI_BANK-1:0][L1_SUB_BANK_WIDTH-1:0] rdata;
  logic [L1_MACROS_PER_MINI_BANK-1:0][L1_SUB_BANK_WIDTH-1:0] rdata_masked;
  logic [L1_SUB_BANK_WIDTH-1:0] rdata_d;
  logic [1:0] ce_d;
  reg [1:0] ce_q;

   // only one bit can be active, and selects current macro based on the address
  logic    [L1_MACROS_PER_MINI_BANK-1:0] macro_select_d;
  reg      [L1_MACROS_PER_MINI_BANK-1:0] macro_select_q;

  // =====================================================
  // RTL
  // =====================================================
  // macro selection, based on msb's:
  if (L1_MACROS_PER_MINI_BANK > 1) begin : gen_flex
    always_comb
      for (uint_t i=0;i<L1_MACROS_PER_MINI_BANK; i++)
        macro_select_d[i] = i_addr[MINI_BANK_ADDR_WIDTH-1:L1_MACRO_ADDR_WIDTH]==i;

    // delay macro select for read:
    always_ff @(posedge i_clk, negedge i_rst_n) begin
      if (i_rst_n == 1'b0)
        macro_select_q <= '0;
      else if (i_ce & ~i_we) macro_select_q <= macro_select_d;
    end
  end else begin : gen_fixed
    always_comb macro_select_d[0] = 1'b1;
    always_comb macro_select_q[0] = 1'b1;
  end

  // mask rdata, based on macro_select_q:
  always_comb
    for (uint_t i=0;i<L1_MACROS_PER_MINI_BANK; i++)
      rdata_masked[i] = {L1_SUB_BANK_WIDTH{macro_select_q[i]}} & rdata[i];

  // assign read data with ORR:
  always_comb begin
    rdata_d = '0;
    for (uint_t i=0;i<L1_MACROS_PER_MINI_BANK; i++)
      rdata_d |= rdata_masked[i];
  end

  // insert shielding flop, use delay ce:
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (i_rst_n == 1'b0)
      o_rdata <= '0;
    else if (ce_q[0]) o_rdata <= rdata_d;
  end
  // create ce delay line:
  always_comb ce_d = {ce_q[0],i_ce};
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (i_rst_n == 1'b0)
      ce_q <= '0;
    else if ((ce_d ^ ce_q) != 0) ce_q <= ce_d;
  end
  // output valid, use ce_qq:
  always_comb o_rdata_vld = ce_q[1];

  // L1_MACROS_PER_MINI_BANK macro's of depth L1_MACRO_DATA_DEPTH:
  for (genvar i=0;uint_t'(i)<L1_MACROS_PER_MINI_BANK; i++) begin : g_macro
    axe_tcl_ram_1rwp #(
      .NumWords(L1_MACRO_DATA_DEPTH),
      .DataWidth(L1_MACRO_DATA_WIDTH),
      .ByteWidth(8),
      .ImplKey(L1_MACRO_TYPE),
      .impl_inp_t(impl_inp_t),
      .impl_oup_t(impl_oup_t),
      .FunctionalClkGate(0), // l1_mem is gated based on outstanding request, no big gain for these lower ones
      .FunctionalInputSilence(0) // inputs are driven by a flop and are thus stable, no need for and-ing with req
    ) u_macro (
      .i_clk      (i_clk),
      .i_rst_n    (i_rst_n),
      .i_impl     (i_mem_impl[i]),
      .o_impl     (o_mem_impl[i]),
      .i_req      (i_ce & macro_select_d[i]),
      .i_wr_enable(i_we),
      .i_addr     (i_addr[L1_MACRO_ADDR_WIDTH-1:0]),
      .i_wr_data  (i_wdata),
      .i_wr_mask  (i_wbe),
      .o_rd_data  (rdata[i])
    );
  end

endmodule
