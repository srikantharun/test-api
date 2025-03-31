// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Anonymous <anonymous@axelera.ai>


/// TODO:__one_line_summary_of_ai_core_tb__
///
module ai_core_tb;

  // Set to 1.2 GHz
  localparam realtime TbCycleTime = 0.8333ns;

  // Setup AT timing
  localparam realtime TbApplTime = 0.1 * TbCycleTime;
  localparam realtime TbTestTime = 0.9 * TbCycleTime;

  // Clock / Reset genereration and stop of simulation
  logic tb_clk;
  logic tb_rst_n;

  localparam int unsigned ResetCycles = 5;

  initial begin : proc_clk_rst_gen
    tb_clk   = 1'b0;
    tb_rst_n = 1'b0;
    fork
      begin : fork_clk_gen
        forever begin
          #(TbCycleTime/2);
          tb_clk = ~tb_clk;
        end
      end
      begin : fork_rst_gen
        repeat (ResetCycles) @(negedge tb_clk);
        tb_rst_n = 1'b1;
      end
    join
  end

  // Stimuli generation
  // TODO: Add some stimulies


  // Design Under Test (DUT)
  ai_core #(

  ) i_ai_core_dut (
    .clk_i (tb_clk),
    .rst_ni(tb_rst_n),

  );

endmodule
