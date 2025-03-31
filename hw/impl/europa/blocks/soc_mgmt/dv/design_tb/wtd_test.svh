// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// wtd test for the soc management IP
//
task wtd_test ();
  `uvm_info("WTD_TEST", "TEST Start", UVM_NONE)

  #10us;
  // set pll
  fast_clk_setup();
  #10us;

  do_wtd_reg_check();
  #10us;

  do_wtd_check(5);
  #10us;

endtask

