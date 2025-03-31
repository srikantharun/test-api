// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: DMA ram wrapper for the dual port ram's
// Owner: Sander Geursen <sander.geursen@axelera.ai>

module snps_dma_dp_ram
  import axe_tcl_sram_pkg::impl_inp_t, axe_tcl_sram_pkg::impl_oup_t;
#(
    parameter int unsigned RAM_DEPTH = 128,
    parameter int unsigned RAM_WIDTH = 512,
    parameter int unsigned MACRO_WIDTH = RAM_WIDTH,
    parameter SRAM_IMPL_KEY = "HD"
) (
    input wire i_clk,
    input wire i_rst_n,

    input logic                         i_wcen,
    input logic                         i_wen,
    input logic [$clog2(RAM_DEPTH)-1:0] i_waddr,
    input logic [RAM_WIDTH-1:0]         i_wdata,
    input logic                         i_rcen,
    input logic                         i_ren,
    input logic [$clog2(RAM_DEPTH)-1:0] i_raddr,
    output logic [RAM_WIDTH-1:0]        o_rdata,

    input  impl_inp_t                   i_impl_inp,
    output impl_oup_t                   o_impl_oup
);

    // Use memories with a fixed width
    localparam int unsigned MACRO_DEPTH = RAM_DEPTH; // (for now) only support single macro in depth
    localparam int unsigned NUM_MACRO   = RAM_WIDTH / MACRO_WIDTH;

    impl_inp_t [NUM_MACRO-1:0] impl_inp_macro;
    impl_oup_t [NUM_MACRO-1:0] impl_oup_macro;

    axe_tcl_sram_cfg #(
        .NUM_SRAMS(NUM_MACRO)
    ) u_sram_cfg_impl (
        .i_s(i_impl_inp),
        .o_s(o_impl_oup),
        .o_m(impl_inp_macro),
        .i_m(impl_oup_macro)
    );

    logic mem_wen;
    logic mem_ren;

    assign mem_wen = i_wcen || i_wen;
    assign mem_ren = i_rcen || i_ren;

    // Generate all needed memories
    for (genvar macro = 0; unsigned'(macro) < NUM_MACRO; macro++) begin : g_macro
        axe_tcl_ram_1rp_1wp #(
            .NumWords(MACRO_DEPTH),
            .DataWidth(MACRO_WIDTH),
            .ByteWidth(8),
            .ReadLatency(1),
            .ImplKey(SRAM_IMPL_KEY),
            .impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
            .impl_oup_t(axe_tcl_sram_pkg::impl_oup_t),
            .FunctionalClkGate(0), // there is already a low power clock-gate in the DMA
            .FunctionalInputSilence(0) // stable inputs, no silencing required
        ) u_tc_ram (
            .i_wr_clk(i_clk),
            .i_wr_rst_n(i_rst_n),
            .i_wr_req(~mem_wen),
            .i_wr_addr(i_waddr),
            .i_wr_data(i_wdata[MACRO_WIDTH*macro+:MACRO_WIDTH]),
            .i_wr_mask('1),

            .i_rd_clk(i_clk),
            .i_rd_rst_n(i_rst_n),
            .i_rd_req(~mem_ren),
            .i_rd_addr(i_raddr),
            .o_rd_data(o_rdata[MACRO_WIDTH*macro+:MACRO_WIDTH]),

            .i_impl(impl_inp_macro[macro]),
            .o_impl(impl_oup_macro[macro])
        );
    end
endmodule
