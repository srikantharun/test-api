// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Sanity testbench for `cc_clk_div_by_2`
///
/// Randomly applies inputs, the functionality is checed using assertions inside the DUT
module axe_ccl_clk_div_by_2_tb #(
  /// The clock cycle time.
  parameter time TbCyclTime = 10ns,
  /// The width of the DUT
  parameter int unsigned TbWidth = 10,
  /// The amount of cycles the testbenmch should be running for.
  parameter int unsigned TbTestCycles = 1_000_000,
  /// The margin to account for testbench rounding errors
  parameter real TbMargin = 0.015
);

  // Setup AT timing
  localparam time TbApplTime = 0.1 * TbCyclTime;
  localparam time TbTestTime = 0.4 * TbCyclTime; // Want to be able to test if clock is propagated!

  // Clock / Reset genereration and stop of simulation
  logic tb_clk_inp, tb_rst_n;
  initial begin : proc_clk_rst_gen
    tb_clk_inp   = 1'b0;
    tb_rst_n = 1'b0;
    fork
      begin : fork_clk_gen
        forever begin
          #(TbCyclTime/2);
          tb_clk_inp = ~tb_clk_inp;
        end
      end
      begin : fork_rst_gen
        repeat (5) @(negedge tb_clk_inp);
        tb_rst_n = 1'b1;
      end
    join
  end


  initial begin : proc_sim_stop
    repeat (TbTestCycles) @(posedge tb_clk_inp);
    $finish();
  end

  // DUT signals
  logic tb_test_mode = 1'b0;
  logic tb_enable;
  logic tb_clk_oup;

  // Drive the enable randomly
  initial begin : proc_stim_en
    automatic int unsigned rand_cycles;
    tb_enable   = 1'b0;
    @(posedge tb_rst_n);
    @(posedge tb_clk_inp);

    forever begin
      // Long eneable cycle followed by short turned off cycle
      rand_cycles = $urandom_range(100000, 1);
      tb_enable <= #TbApplTime ~tb_enable;
      repeat (rand_cycles) @(posedge tb_clk_inp);
    end
  end

  axe_ccl_clk_div_by_2 u_axe_ccl_clk_div_by_2_dut (
    .i_clk      (tb_clk_inp),
    .i_rst_n    (tb_rst_n),
    .i_test_mode(tb_test_mode),
    .i_enable   (tb_enable),
    .o_clk      (tb_clk_oup)
  );
endmodule
