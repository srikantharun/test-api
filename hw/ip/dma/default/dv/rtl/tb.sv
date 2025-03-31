// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Axelera Designed DMA Testbench
// Owner: abond

module tb();

  timeunit      1ns;
  timeprecision 1ps;

  `include "uvm_macros.svh"
  import uvm_pkg::*;
  import test_pkg::*;

  // Clock - 1.2GHz
  logic clk_en, clk;
  axe_clk_generator u_axe_clk_generator(
                                          .i_enable(clk_en),
                                          .o_clk(clk)
                                       );
  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(1200), .duty(50));
    clk_en = 1'b1;
  end

  // Reset
  logic rst;
  axe_rst_generator u_axe_rst_generator(
                                          .i_clk(clk),
                                          .o_rst(rst)
                                       );

  initial begin
      u_axe_rst_generator.async_rst(.duration_ns(1000));
  end

  // UVM
  initial
  begin
    run_test();
  end
endmodule // tb
