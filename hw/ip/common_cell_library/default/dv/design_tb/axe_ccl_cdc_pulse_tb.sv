// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Sanity testbench for the pulse clock domain crossing
///
module axe_ccl_cdc_pulse_tb;
  timeunit      1ns;
  timeprecision 1ps;

  ////////////////////////////////////////
  // Clock parameters for configuration //
  ////////////////////////////////////////
  localparam int unsigned TbResetCycles   =     10;
  localparam int unsigned TbNumIterations =    100;
  localparam int unsigned TbMaxWaitCycles = 10_000;
  localparam int unsigned TbMaxFreqMhz    =    900;
  localparam int unsigned TbMinFreqMhz    =    100;

  localparam int unsigned TbSoftTimeout = 2 * TbMaxWaitCycles * TbNumIterations * int'(1000.0 / real'(TbMinFreqMhz));
  localparam int unsigned TbHardTimeout = 3 * TbMaxWaitCycles * TbNumIterations * int'(1000.0 / real'(TbMinFreqMhz));
  localparam int unsigned TbTickerTime  = 1_000_000;

  ////////////////////
  // DUT Parameters //
  ////////////////////
  localparam int unsigned TbSyncStages = 3;


  wire  tb_src_clk,    tb_dst_clk;
  logic tb_src_clk_en, tb_dst_clk_en;
  wire  tb_src_rst,    tb_dst_rst;

  logic tb_src_pulse;
  logic tb_src_busy;
  logic tb_src_error;
  logic tb_dst_pulse;

  bit   tb_active, tb_done;


  axe_clk_generator u_clk_generator_src (
    .i_enable(tb_src_clk_en),
    .o_clk   (tb_src_clk)
  );
  axe_rst_generator u_rst_generator_src (
    .i_clk(tb_src_clk),
    .o_rst(tb_src_rst)
  );

  axe_clk_generator u_clk_generator_dst (
    .i_enable(tb_dst_clk_en),
    .o_clk   (tb_dst_clk)
  );
  axe_rst_generator u_rst_generator_dst (
    .i_clk(tb_dst_clk),
    .o_rst(tb_dst_rst)
  );

  axe_timeout u_timeout();

  initial begin : proc_src_clk
    automatic int unsigned RandCycles;
    automatic int unsigned RandSrcFreq;
    automatic int unsigned RandDstFreq;

    tb_src_clk_en <= 1'b1;
    tb_dst_clk_en <= 1'b1;
    tb_active     <= 1'b0;
    tb_done       <= 1'b0;

    u_timeout.timeout(TbSoftTimeout, TbHardTimeout);
    u_timeout.ticker(TbTickerTime, "The TB is alive!");
    u_clk_generator_src.set_clock(.freq_mhz(800), .duty(50));
    u_clk_generator_dst.set_clock(.freq_mhz(800), .duty(50));
    u_rst_generator_src.sync_rst(.duration_cycles(TbResetCycles));
    u_rst_generator_dst.sync_rst(.duration_cycles(TbResetCycles));

    repeat (TbResetCycles+1) @(posedge tb_src_clk);

    tb_active <= 1'b1;
    $display("%t: %m: Tb is active.", $time);


    repeat (TbNumIterations) begin
      RandCycles  = $urandom_range(TbMaxWaitCycles, 10);
      RandSrcFreq = $urandom_range(TbMaxFreqMhz, TbMinFreqMhz);
      RandDstFreq = $urandom_range(TbMaxFreqMhz, TbMinFreqMhz);
      u_clk_generator_src.set_clock(.freq_mhz(RandSrcFreq), .duty(50));
      u_clk_generator_dst.set_clock(.freq_mhz(RandDstFreq), .duty(50));
      $display("Running for %0d Cycles", RandCycles);

      repeat (RandCycles) @(posedge tb_src_clk);
    end
    tb_done <= 1'b1;
  end

  /////////////
  // Stimuli //
  /////////////
  initial begin
    tb_src_pulse <= 1'b0;
    @(posedge tb_active);

    while (!tb_done) begin
      @(posedge tb_src_clk);
      tb_src_pulse <= #1ps $urandom();
    end
    @(posedge tb_src_clk);
    tb_src_pulse <= #1ps 1'b0;
  end

  /////////////////
  // Observation //
  /////////////////

  longint unsigned src_pulses_emitted;
  longint unsigned src_pulses_captured;
  longint unsigned dst_pulses_captured;

  initial begin : proc_src
    src_pulses_emitted  = 0;
    src_pulses_captured = 0;

    @(posedge tb_active);
    forever begin
      @(posedge tb_src_clk);
      #10ps;
      if (tb_src_pulse) begin
        src_pulses_emitted++;
        if (tb_src_busy) begin
          if (!tb_src_error) $error("no error on pulse and busy");
        end else begin
          src_pulses_captured++;
        end
      end
    end
  end

  initial begin : proc_dst
    dst_pulses_captured = 0;

    @(posedge tb_active);
    forever begin
      @(posedge tb_dst_clk);
      #10ps;
      if (tb_dst_pulse) dst_pulses_captured++;
    end
  end

  initial begin : proc_finish
    @(posedge tb_done);
    repeat (20) @(posedge tb_dst_clk);
    assert (src_pulses_captured == dst_pulses_captured) else
      $fatal(1, "Number src captured: %0d dst captured: %0d", src_pulses_captured, dst_pulses_captured);
    $display("%0d Pulses emitted!", src_pulses_emitted);
    $display("%0d Pulses synchronized! Sucess!!!", src_pulses_captured);
    $finish();
  end

  axe_ccl_cdc_pulse #(
    .SyncStages(TbSyncStages)
  ) u_axe_ccl_cdc_pulse_dut (
    .i_src_clk  (tb_src_clk),
    .i_src_rst_n(~tb_src_rst),
    .i_src_pulse(tb_src_pulse),
    .o_src_busy (tb_src_busy),
    .o_src_error(tb_src_error),
    .i_dst_clk  (tb_dst_clk),
    .i_dst_rst_n(~tb_dst_rst),
    .o_dst_pulse(tb_dst_pulse)
  );



endmodule
