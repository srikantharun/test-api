// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Design testbench for the Ai-Core Control Dispatcher
///
module aic_cd_tb;

  // Set to 1.2 GHz
  localparam real TbFrequencyMHz    =     1_200.0;
  localparam int  TbDutyCycle       =        50;
  localparam int  TbResetDurationNs =     2_000;

  localparam int  TbSoftTimeoutNs   = 1_000_000;
  localparam int  TbHardTimeoutNs   = 1_500_000;
  localparam int  TbTickerPeriodNs  =    10_000;

  ////////////////////////////////
  // Clock and Reset Generation //
  ////////////////////////////////
  wire tb_clk;
  wire tb_rst_n;
  logic tb_clk_en;

  axe_clk_generator u_axe_clk_generator (
    .i_enable(1'b1),
    .o_clk   (tb_clk)
  );

  axe_rst_generator u_axe_rst_generator (
    .i_clk(tb_clk),
    .o_rst(tb_rst_n)
  );

  clk_if u_tb_clk_if(
    .clk(tb_clk)
  );

  axe_timeout u_axe_timeout();

  initial begin : proc_init_clk_and_rst
    tb_clk_en <= 1'b0;
    u_axe_rst_generator.async_rst(
      .duration_ns(TbResetDurationNs)
    );
    u_axe_clk_generator.set_clock(
      .freq_mhz(TbFrequencyMHz),
      .duty    (TbDutyCycle)
    );
    tb_clk_en <= 1'b1;
  end

  initial begin : proc_tb_timeout
    u_axe_timeout.timeout(
      .soft_timeout_ns(TbSoftTimeoutNs),
      .hard_timeout_ns(TbHardTimeoutNs)
    );
  end

  initial begin : proc_tb_ticker
    u_axe_timeout.ticker(
      .period_ns(TbTickerPeriodNs),
      .message  ("Testbench is alive!")
    );
  end

  ////////////////////////
  // Stimuli generation //
  ////////////////////////
  // TODO: Add some stimulies

  /////////////////////////////
  // Design Under Test (DUT) //
  /////////////////////////////
  aic_cd #(

  ) u_dut_aic_cd (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n)

  );

endmodule
