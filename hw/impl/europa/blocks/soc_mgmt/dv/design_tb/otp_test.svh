// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>


// tests for the soc management OTP IP
//
//==============================================================================

task otp_test();
  #10us;
  `uvm_info("OTP_TEST", "Test Start", UVM_NONE)

  otp_reg_check();
  #10us;

endtask
