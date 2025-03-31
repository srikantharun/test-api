// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Sanity testbench for the integer clock divider
///
module axe_ccl_clk_div_by_int_tb;

  ////////////////////
  // DUT Parameters //
  ////////////////////
  parameter int unsigned TbMaxDivision  = 25;
  parameter bit          TbClkOnInReset = 1'b1;

  typedef logic [cc_math_pkg::index_width(TbMaxDivision):0] tb_divisor_t;

  /////////////////////
  // Clock and Reset //
  /////////////////////
  parameter int unsigned TbResetCycles =     10;
  parameter int unsigned TbNumCycles   = 10_000;
  parameter int unsigned TbFreqMhz     =     50;

  parameter int unsigned TbSoftTimeout = 2 * TbNumCycles * int'(1000.0 / real'(TbFreqMhz));
  parameter int unsigned TbHardTimeout = 3 * TbNumCycles * int'(1000.0 / real'(TbFreqMhz));
  parameter int unsigned TbTickerTime  = 10_000;

  wire  tb_clk;
  logic tb_clk_en;
  wire  tb_rst;
  logic tb_rst_n;

  bit   tb_active, tb_done;

  axe_clk_generator u_axe_clk_generator (
    .i_enable(tb_clk_en),
    .o_clk   (tb_clk)
  );

  axe_rst_generator u_axe_rst_generator (
    .i_clk(tb_clk),
    .o_rst(tb_rst)
  );
  always_comb tb_rst_n = ~tb_rst;

  axe_timeout u_axe_timeout();

  initial begin : proc_clk
    automatic int unsigned RandCycles;
    automatic int unsigned RandSrcFreq;
    automatic int unsigned RandDstFreq;

    tb_clk_en <= 1'b1;
    tb_active <= 1'b0;
    tb_done   <= 1'b0;

    u_axe_timeout.timeout(TbSoftTimeout, TbHardTimeout);
    u_axe_timeout.ticker(TbTickerTime, "The TB is alive!");
    u_axe_clk_generator.set_clock(.freq_mhz(TbFreqMhz), .duty(50));
    u_axe_rst_generator.sync_rst(.duration_cycles(TbResetCycles));

    repeat (TbResetCycles+1) @(posedge tb_clk);

    tb_active <= 1'b1;
    $display("%t: %m: Tb is active.", $time);

    repeat (TbNumCycles) @(posedge tb_clk);
    tb_done <= 1'b1;
  end

  /////////////
  // Stimuli //
  /////////////
  tb_divisor_t tb_divisor;
  wire         tb_divided_clk;

  initial begin : proc_div_ratios
    automatic int unsigned random_division;
    automatic int unsigned random_cycles;

    random_division = tb_divisor_t'(1);
    random_cycles   = 100;

    tb_divisor      = tb_divisor_t'(TbClkOnInReset);

    @(posedge tb_rst_n);
    @(posedge tb_clk);

    forever begin
      repeat (random_cycles) @(posedge tb_clk);

      if (tb_done) begin
        $display("All sanity commands done: Success!");
        $finish();
      end

      random_division = $urandom_range(TbMaxDivision + 5);
      random_cycles   = $urandom_range(1, TbNumCycles/100);

      $display("%t: %m: Setting Division Ratio %0d.", $time, random_division);
      tb_divisor     <= tb_divisor_t'(random_division);
    end
  end

  /////////
  // DUT //
  /////////
  axe_ccl_clk_div_by_int #(
    .MaxDivision (TbMaxDivision),
    .ClkOnInReset(TbClkOnInReset)
  ) u_axe_ccl_clk_div_by_int (
    .i_clk      (tb_clk),
    .i_rst_n    (tb_rst_n),
    .i_test_mode(1'b0),
    .i_divisor  (tb_divisor),
    .o_clk      (tb_divided_clk)
  );
endmodule
