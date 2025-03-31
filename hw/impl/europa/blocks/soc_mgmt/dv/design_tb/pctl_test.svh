// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// Test the pct instance
// Primarily check syscfg APB interface access
//
//============================================================================
task pctl_test();
  #10us;
  `uvm_info("PCTL_TEST", "TEST Start", UVM_NONE)

  // set pll
  fast_clk_setup();

  #10us;

  do_pctl_reg_check();

  #10us;
  do_syscfg_apb_no_pop();

endtask
