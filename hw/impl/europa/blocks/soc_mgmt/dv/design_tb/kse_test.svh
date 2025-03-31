// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

// tests for the soc management KSE3 IP
//
//==============================================================================

task kse_test();
  #10us;
  `uvm_info("KSE_TEST", "Test Start", UVM_NONE)

  if (use_kse3_integr_rom)
    kse_integration_test();
  else
    kse_apu_test();

  kse_jtag_test();

  kse_lcs_test();

endtask
