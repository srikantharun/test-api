// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfang Roenninger <wolfgang.roenninger@axelera.ai>


/// Sanity testbench for the stream handshaking modules
///
module axe_ccl_stream_fifo_mem_tb;

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
  parameter int unsigned TbFifoDepth = 16;

  localparam int unsigned TbAddrWidth = cc_math_pkg::index_width(TbFifoDepth);

  typedef logic [TbDataWidth-1:0] tb_data_t;
  typedef logic [TbAddrWidth  :0] tb_usage_t;

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
  tb_data_t   tb_fifo_inp_data;
  logic       tb_fifo_inp_valid, tb_fifo_inp_ready;

  tb_usage_t  tb_fifo_usage;
  logic       tb_fifo_full;
  logic       tb_fifo_empty;

  tb_data_t   tb_fifo_oup_data;
  logic       tb_fifo_oup_valid, tb_fifo_oup_ready;

  cc_stream_rand_man #(
    .data_t       (tb_data_t),
    .MinWaitCycles(TbMinWaitCycles),
    .MaxWaitCycles(TbMaxWaitCycles),
    .ApplTime     (TbApplTime),
    .TestTime     (TbTestTime),
    .Enqueue      (1'b1)
  ) u_demux_rand_man (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n),
    .o_data (tb_fifo_inp_data),
    .o_valid(tb_fifo_inp_valid),
    .i_ready(tb_fifo_inp_ready)
  );

  axe_ccl_stream_fifo_mem #(
    .Depth     (TbFifoDepth),
    .data_t    (tb_data_t),
    .MemImplKey("default"),
    .ram_impl_inp_t(axe_tcl_sram_pkg::impl_inp_t),
    .ram_impl_oup_t(axe_tcl_sram_pkg::impl_oup_t)
  ) u_dut_axe_ccl_stream_fifo_mem (
    .i_clk     (tb_clk),
    .i_rst_n   (tb_rst_n),
    .i_flush   (1'b0),
    .i_data    (tb_fifo_inp_data),
    .i_valid   (tb_fifo_inp_valid),
    .o_ready   (tb_fifo_inp_ready),
    .o_data    (tb_fifo_oup_data),
    .o_valid   (tb_fifo_oup_valid),
    .i_ready   (tb_fifo_oup_ready),
    .o_usage   (tb_fifo_usage),
    .o_full    (tb_fifo_full),
    .o_empty   (tb_fifo_empty),
    .i_ram_impl('0),
    .o_ram_impl(/*open*/)
  );

  cc_stream_rand_sub #(
    .data_t       (tb_data_t),
    .MinWaitCycles(TbMinWaitCycles + 1),
    .MaxWaitCycles(TbMaxWaitCycles + 1),
    .ApplTime     (TbApplTime),
    .TestTime     (TbTestTime),
    .Enqueue      (1'b1)
  ) u_demux_rand_sub (
    .i_clk  (tb_clk),
    .i_rst_n(tb_rst_n),
    .i_data (tb_fifo_oup_data),
    .i_valid(tb_fifo_oup_valid),
    .o_ready(tb_fifo_oup_ready)
  );

  initial begin : proc_check_data
    tb_data_t input_data, output_data;
    longint checks;
    checks = 0;
    forever begin
      wait(u_demux_rand_sub.queue.size());
      if (!u_demux_rand_sub.queue.size())
        $error("Output quese has data while input does not.");
      input_data  = u_demux_rand_man.queue.pop_front();
      output_data = u_demux_rand_sub.queue.pop_front();
      if (input_data != output_data)
        $fatal(1,
          "Input and output data do not match:/n",
          "Input:  0x%0h/n", input_data,
          "Output: 0x%0h/n", output_data
        );
      checks++;
      if (checks % 500 == 0) begin
        $info("Performed ckecks: %0d", checks);
      end

    end
  end
endmodule
