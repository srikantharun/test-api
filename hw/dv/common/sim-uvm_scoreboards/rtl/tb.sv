// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Simple Socreboard Testbench
// Owner: abond

module tb();

  timeunit      1ns;
  timeprecision 1ps;

  `include "uvm_macros.svh"

  import uvm_pkg::*;

  import axe_uvm_scoreboard_pkg::*;

  import test_pkg::*;

  initial
  begin
    run_test();
  end
endmodule // tb
