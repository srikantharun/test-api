// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// rtc test for the soc management IP
//
task rtc_test ();
  `uvm_info("RTC_TEST", "TEST Start", UVM_NONE)

  test_step = 1000;
  #10us;

  fast_clk_setup();
  test_step = 1001;
  #10us;

  do_rtc_reg_check();
  test_step = 1002;
  #10us;

  do_rtc_int_check();
  test_step = 1003;
  #10us;

  test_step = 9999;

endtask

