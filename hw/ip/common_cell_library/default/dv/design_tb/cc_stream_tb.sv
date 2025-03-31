// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfang Roenninger <wolfgang.roenninger@axelera.ai>


/// Sanity testbench for the stream handshaking modules
///
module cc_stream_tb;

  ////////////
  // Timing //
  ////////////
  // Set to 1.2 GHz
  parameter realtime TbCycleTime = 0.8333ns;

  parameter int unsigned TbRunCycles = 1_000_000;

  // Setup AT timing
  parameter realtime TbApplTime = 0.1 * TbCycleTime;
  parameter realtime TbTestTime = 0.9 * TbCycleTime;

  // Handshaking
  parameter int unsigned TbMinWaitCycles = 0;
  parameter int unsigned TbMaxWaitCycles = 5;

  ////////////////
  // Data types //
  ////////////////

  parameter int unsigned TbDataWidth = 8;
  parameter int unsigned TbNumPorts  = 3;

  localparam int unsigned TbSelWidth  = cc_math_pkg::index_width(TbNumPorts);

  typedef logic [TbDataWidth-1:0] tb_data_t;
  typedef logic [TbSelWidth -1:0] tb_select_t;

  ///////////////////////////////////////////////////////
  // Clock / Reset genereration and stop of simulation //
  ///////////////////////////////////////////////////////

  logic tb_clk;
  logic tb_rst_n;

  localparam int unsigned TbResetCycles = 5;

  initial begin : proc_clk
    tb_clk   = 1'b0;
    forever begin
      #(TbCycleTime/2);
      tb_clk = ~tb_clk;
    end
  end

  initial begin : proc_rst_n
    tb_rst_n = 1'b0;
    repeat (TbResetCycles) @(negedge tb_clk);
    tb_rst_n = 1'b1;
  end

  initial begin : proc_tb_finish
    repeat (TbRunCycles) @(negedge tb_clk);
    $display("Ran TB for %0d cycles", TbRunCycles);
    $finish();
  end


  //////////////////////////////
  // Designs Under Test (DUT) //
  //////////////////////////////

  ///////////
  // DEMUX //
  ///////////
  tb_data_t   tb_demux_inp_data;
  logic       tb_demux_inp_valid, tb_demux_inp_ready;

  tb_select_t tb_demux_select;
  logic       tb_demux_error;

  tb_data_t   tb_demux_oup_data[TbNumPorts];
  logic       tb_demux_oup_valid[TbNumPorts], tb_demux_oup_ready[TbNumPorts];

  // Drive the select
  initial begin : proc_demux_select
    automatic tb_select_t demux_rand_select;
    tb_demux_select    = tb_select_t'(0);
    forever begin
      void'(std::randomize(demux_rand_select));
      @(posedge tb_clk);
      tb_demux_select <= #TbApplTime demux_rand_select;
    end
  end

  cc_stream_rand_man #(
    .data_t       (tb_data_t),
    .MinWaitCycles(TbMinWaitCycles),
    .MaxWaitCycles(TbMaxWaitCycles),
    .ApplTime     (TbApplTime),
    .TestTime     (TbTestTime)
  ) u_demux_rand_man (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n),
    .o_data (tb_demux_inp_data),
    .o_valid(tb_demux_inp_valid),
    .i_ready(tb_demux_inp_ready)
  );

  cc_stream_demux_unpack #(
    .data_t     (tb_data_t),
    .NumStreams (TbNumPorts),
    .DropOnError(1'b1)
  ) u_dut_cc_stream_demux_unpack (
    .i_data  (tb_demux_inp_data),
    .i_select(tb_demux_select),
    .i_valid (tb_demux_inp_valid),
    .o_ready (tb_demux_inp_ready),
    .o_error (tb_demux_error),
    .o_data  (tb_demux_oup_data),
    .o_valid (tb_demux_oup_valid),
    .i_ready (tb_demux_oup_ready)
  );

  for (genvar demux_sub_idx = 0; demux_sub_idx < TbNumPorts; demux_sub_idx++) begin : gen_demux_subs
    cc_stream_rand_sub #(
      .data_t       (tb_data_t),
      .MinWaitCycles(TbMinWaitCycles + demux_sub_idx),
      .MaxWaitCycles(TbMaxWaitCycles + demux_sub_idx),
      .ApplTime     (TbApplTime),
      .TestTime     (TbTestTime),
      .Enqueue      (1'b1)
    ) u_demux_rand_sub (
      .i_clk  (tb_clk),
      .i_rst_n(tb_rst_n),
      .i_data (tb_demux_oup_data[demux_sub_idx]),
      .i_valid(tb_demux_oup_valid[demux_sub_idx]),
      .o_ready(tb_demux_oup_ready[demux_sub_idx])
    );
  end
endmodule
