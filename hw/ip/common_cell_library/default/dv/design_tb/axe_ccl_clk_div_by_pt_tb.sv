// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Sanity testbench for `cc_clk_div_by_punch_through`
///
/// Randomly applies inputs, the functionality is checed using assertions inside the DUT
module axe_ccl_clk_div_by_pt_tb #(
  /// The clock cycle time.
  parameter time         TbCyclTime   = 10ns,
  /// The width of the DUT
  parameter int unsigned TbWidth      = 10,
  /// The amount of cycles the testbenmch should be running for.
  parameter int unsigned TbTestCycles = 100_000_000,
  /// The margin to account for testbench rounding errors
  parameter real         TbMargin     = 0.05
);

  // Setup AT timing
  localparam time TbApplTime = 0.1 * TbCyclTime;
  localparam time TbTestTime = 0.4 * TbCyclTime; // Want to be able to test if clock is propagated!

  // Clock / Reset genereration and stop of simulation
  logic tb_clk, tb_i_rst_n;
  initial begin : proc_clk_rst_gen
    tb_clk   = 1'b0;
    tb_i_rst_n = 1'b0;
    fork
      begin : fork_clk_gen
        forever begin
          #(TbCyclTime/2);
          tb_clk = ~tb_clk;
        end
      end
      begin : fork_rst_gen
        repeat (5) @(negedge tb_clk);
        tb_i_rst_n = 1'b1;
      end
    join
  end

  initial begin : proc_sim_stop
    repeat (TbTestCycles) @(posedge tb_clk);
    $finish();
  end

  // DUT signals
  logic               tb_test_en;
  logic               tb_enable;
  logic               tb_clear;
  logic [TbWidth-1:0] tb_increment;
  logic               tb_open_gate;
  logic               tb_clk_div;


  // Driving logic, checking is done with assertions in the module.
  // Drive the test enable
  initial begin : proc_stim_test_en
    tb_test_en = 1'b0;
    // Only toggle it once after reset have some functional in front
    repeat (2) begin
      repeat (100000) @(posedge tb_clk);
      tb_test_en <= #TbApplTime ~tb_test_en;
    end
  end

  // Drive the clear signal
  initial begin : proc_stim_clear
    automatic int unsigned rand_cycles;
    tb_clear = 1'b0;
    @(posedge tb_i_rst_n);
    forever begin
      rand_cycles = $urandom_range(TbTestCycles/10);
      repeat (rand_cycles) @(posedge tb_clk);
      // Randomly clear the counter for some cycles
      tb_clear <= #TbApplTime 1'b1;
      rand_cycles = $urandom_range(TbTestCycles/100000);
      repeat (rand_cycles) @(posedge tb_clk);
      tb_clear <= #TbApplTime 1'b0;
    end
  end

  // Drive the enable signal
  initial begin : proc_stim_en
    automatic int unsigned rand_cycles;
    tb_enable   = 1'b0;
    @(posedge tb_i_rst_n);
    @(posedge tb_clk);

    forever begin
      // Long eneable cycle followed by short turned off cycle
      rand_cycles = $urandom_range(TbTestCycles/1_000, TbTestCycles/10_000);
      tb_enable <= #TbApplTime 1'b1;
      repeat (rand_cycles) @(posedge tb_clk);

      rand_cycles = $urandom_range(TbTestCycles/100_000, TbTestCycles/1_000_000);
      tb_enable <= #TbApplTime 1'b0;
      repeat (rand_cycles) @(posedge tb_clk);
    end
  end

  // Driove the increment signal
  initial begin : proc_stim_increment
    automatic int unsigned        rand_cycles;
    automatic logic [TbWidth-1:0] stim_increment = '0;
    automatic int unsigned        min_cycles = 32'd0;

    tb_increment = '0;
    @(posedge tb_i_rst_n);
    @(posedge tb_clk);

    forever begin
      // Have the increment at least applied for 100 accumulator rounds
      stim_increment = TbWidth'($urandom());
      min_cycles     = int'(1000*(real'(2**TbWidth)/real'(stim_increment+1)));
      if (min_cycles >= (TbTestCycles/1000))
        min_cycles = TbTestCycles/1000 - 1;
      rand_cycles    = $urandom_range(TbTestCycles/100, min_cycles);
      // $display("Run incr for cycles: %d (min: %d)", rand_cycles, min_cycles);
      // Changfe the incr value randomly after some time
      repeat (rand_cycles) @(posedge tb_clk);
      tb_increment <= #TbApplTime stim_increment;
    end
  end

  // This process checks the functionality of the divider
  initial begin : proc_check
    // Counters of keeping track of the clock pulses
    automatic longint unsigned input_count    = 0;
    automatic longint unsigned output_count   = 0;
    automatic longint unsigned old_increment  = 0;
    automatic real             expected_ratio = 0;
    automatic real             actual_ratio   = 0;

    @(posedge tb_i_rst_n);
    @(posedge tb_clk);
    #TbTestTime;
    old_increment = tb_increment;
    forever begin
      @(posedge tb_clk);
      #TbTestTime;

      if (tb_test_en) begin
        // Test that on test enable the clock is eneabeld the next cycle
        @(posedge tb_clk);
        #TbTestTime;
        assert(tb_clk_div) else
            $error("test_en_i: Is '1' but clock is not fed through.");
      end else begin
        // Functional testing
        if (tb_enable & tb_clk) begin
          input_count++;
        end
        if (tb_enable & tb_clk_div) begin
          output_count++;
        end
        if (old_increment != tb_increment) begin
          // Calculate the expected and actual ratios from the old incremet
          expected_ratio = real'(old_increment) / real'(2)**real'(TbWidth);
          if (old_increment == 0) begin
            expected_ratio = real'(1);
          end
          actual_ratio = real'(output_count)  / real'(input_count);

          $display($sformatf("%t> Divided clock by: %f expected: %f", $time(), actual_ratio, expected_ratio));
          assert(actual_ratio < expected_ratio + TbMargin) else
              $fatal(1, "Actual ratio to large by: %f", expected_ratio - actual_ratio + TbMargin);
          assert(actual_ratio > expected_ratio - TbMargin) else
              $fatal(1, "Actual ratio to small by: %f", expected_ratio - actual_ratio - TbMargin);

          // Reset the counters
          input_count   = 0;
          output_count  = 0;
          old_increment = tb_increment;
        end
      end
    end
  end

  // Dut instantiation
  axe_ccl_clk_div_by_pt #(
    .PhaseAccWidth(TbWidth),
    .ResetValClkEn(1)
  ) u_axe_ccl_clk_div_by_pt_dut (
    .i_clk     (tb_clk      ),
    .i_rst_n   (tb_i_rst_n    ),
    .i_test_en (tb_test_en  ),
    .i_div_en  (tb_enable   ),
    .i_acc_clr (tb_clear    ),
    .i_acc_incr(tb_increment),
    .o_active  (tb_open_gate),
    .o_clk     (tb_clk_div  )
  );
endmodule
