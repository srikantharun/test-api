// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// tests for the soc management TMS IP
//
//==============================================================================
task tms_test();
  #10us;
  `uvm_info("TMS_TEST", "Test Start", UVM_NONE)

  // set pll
  fast_clk_setup();

  #10us;
  tms_reg_check();

  #10us;
  tms_jtag_reg_check();

endtask

