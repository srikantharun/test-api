// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

module cc_cnt_lfsr_tb;

  wire        i_clk;
  wire        i_rst_n;
  logic        clear_i;
  logic        enable_i;
  logic [15:0] state_o;
  logic        flip_enable_i;
  logic [1:0]  mask_select_i;
  logic [15:0] mask_and_i;
  logic [15:0] mask_or_i;
  logic [15:0] data_o;

  localparam Seed = 117;

  initial begin
    i_rst_n = 0;
    #10ns;
    i_rst_n = 1;
  end

  always begin
    i_clk <= 1; #1ns;
    i_clk <= 0; #1ns;
  end

  cc_cnt_lfsr #(
    .Width(16),
    .Seed (Seed)
  ) i_cc_cnt_lfsr_dut (
    .i_clk,
    .i_rst_n,
    .clear_i,
    .enable_i,
    .taps_i(cc_cnt_lfsr_pkg::AX_LFSR_TAPS_016),
    .state_o,
    .flip_enable_i,
    .mask_select_i,
    .mask_and_i,
    .mask_or_i,
    .data_o
  );

  initial begin
    enable_i      = 1'b0;
    clear_i       = 1'b0;
    flip_enable_i = 1'b0;
    mask_select_i = 2'b00;
    mask_and_i    = '1;
    mask_or_i     = '0;
    #23ns;
    @(negedge i_clk);
    enable_i = 1'b1;
    for(int i = 0; i <= 29; i++) begin
      $display("Seed %0d Loop %0d: data = %16b", Seed, i, data_o);
      @(negedge i_clk);
    end
    $finish;
  end

endmodule
