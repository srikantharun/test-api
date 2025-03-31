// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>

/// Sanity testbench for `axe_ccl_cnt_phase_accumulator`
///
/// Randomly applies inputs, the functionality is checed using assertions inside the DUT
module axe_ccl_cnt_phase_acc_tb #(
  /// The clock cycle time.
  parameter time         TbCyclTime   = 10ns,
  /// The width of the DUT
  parameter int unsigned TbWidth      = 32'd16,
  /// The amount of cycles the testbenmch should be running for.
  parameter int unsigned TbTestCycles = 32'd100000
);

  // Setup AT timing
  localparam time TbApplTime = 0.1 * TbCyclTime;
  localparam time TbTestTime = 0.9 * TbCyclTime;

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
  logic               tb_clear;;
  logic [TbWidth-1:0] tb_increment;
  logic               tb_enable;
  logic               tb_pulse;
  logic [TbWidth-1:0] tb_phase;

  // Driving logic, checking is done with assertions in the module.
  initial begin : proc_stim_clear
    automatic int unsigned rand_cycles;
    tb_clear = 1'b0;
    @(posedge tb_i_rst_n);
    forever begin
      rand_cycles = $urandom_range(TbTestCycles/10);
      repeat (rand_cycles) @(posedge tb_clk);
      // Randomly clear the counter for some cycles
      tb_clear <= #TbApplTime 1'b1;
      rand_cycles = $urandom_range(TbTestCycles/10000);
      repeat (rand_cycles) @(posedge tb_clk);
      tb_clear <= #TbApplTime 1'b0;
    end
  end

  initial begin : proc_stim_increment
    automatic int unsigned rand_cycles;
    automatic int unsigned stim_increment = '0;
    tb_increment = '0;
    @(posedge tb_i_rst_n);
    forever begin
      rand_cycles = $urandom_range(TbTestCycles/100);
      stim_increment   = $urandom();
      // Changfe the incr value randomly after some time
      repeat (rand_cycles) @(posedge tb_clk);
      tb_increment <= #TbApplTime stim_increment;
    end
  end

  initial begin : proc_stim_en
    automatic bit stim_en = 1'b0;
    tb_enable = 1'b0;
    @(posedge tb_i_rst_n);
    forever begin
      // Change the enable randomly
      @(posedge tb_clk);
      stim_en = $urandom();
      tb_enable <= #TbApplTime stim_en;
    end
  end

  // Dut instantiation
  axe_ccl_cnt_phase_acc #(
    .Width(TbWidth)
  ) u_axe_ccl_cnt_phase_acc_dut (
    .i_clk     (tb_clk),
    .i_rst_n   (tb_i_rst_n),
    .i_cnt_clr (tb_clear),
    .i_cnt_incr(tb_increment),
    .i_cnt_en  (tb_enable),
    .o_pulse   (tb_pulse),
    .o_phase   (tb_phase)
  );
endmodule
