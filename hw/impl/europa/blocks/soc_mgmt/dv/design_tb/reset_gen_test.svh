// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@axelera.ai>

// reset_gen block testbench for the soc management IP
// all the reset tasks are included in the test
//
// STAGE0 Connection summary
// =========================
//  Reset State Pin | Signal                          | Test |
// -----------------+---------------------------------+------+------
// i_clk            | ref_clk                         | NO   |
// i_rst_n          | i_por_rst_n & hw_dbnc_rst_n     | YES  | 
// i_test_mode      | i_test_mode = TIED to 0         | NO   | Tied off
// i_test_rst_n     | i_por_rst_n                     | NO   | No test mode
// i_rst_req_n      | i_ao_rst_req_n = TIED to 1      | NO   | Tied off
// i_stretch_cycles | CSR:rst_cfg_ao_rst.rst_stretch  | NO   | Use default
// i_rst_src_n      | 1                               | NO   | Tied off
// i_mask_reset_src | CSR:rst_cfg_ao_rst.rst_src_mask | NO   | Use default
// i_rst_ip_sw_n    | CSR:rst_sw_ao_rst               | NO   | SW reset breaks AXI
// i_rst_ip_force   | 0                               | NO   | Tied off
// i_ack_reset_ip   | i_ao_rst_ip_ack = TIED To 0     | NO   | Tied off
// o_rst_ack_n      | o_ao_rst_ack_n                  | NO   | Not connected. driven from in: i_ao_rst_ip_ack
// o_rst_ip_n       | o_ao_rst_ip_n                   | YES  | Check with assert
// o_rst_n          | rst_stage[0]                    | YES  | Check with assert
//
//==
//
// STAGE1 Connection summary
// =========================
//  Reset State Pin | Signal                          | Test |
// -----------------+---------------------------------+------+------
// i_clk            | ref_clk                         | NO   |
// i_rst_n          | rst_stage[0]                    | YES  | Stage 0
// i_test_mode      | i_test_mode = TIED to 0         | NO   | Tied off
// i_test_rst_n     | i_por_rst_n                     | NO   | No test mode
// i_rst_req_n      | i_dmi_rst_n                     | YES  | 
// i_stretch_cycles | CSR:rst_cfg_dmi_rst.rst_stretch | NO   | Use default
// i_rst_src_n      | i_tamper_rst_n & i_mbist_rst_n  | YES  |
// i_mask_reset_src | CSR:rst_cfg_dmi_rst.rst_src_mask| NO   | Use default
// i_rst_ip_sw_n    | CSR:rst_sw_dmi_rst              | NO   | SW reset breaks AXI
// i_rst_ip_force   | i_dmi_rst_n                     | YES  | needed four rst_src testing
// i_ack_reset_ip   | i_dmi_rst_ip_ack = TIED To 0    | NO   | Tied off
// o_rst_ack_n      | o_dmi_rst_ack_n                 | NO   | Not connected. driven from i_dmi_rst_ip_ack
// o_rst_ip_n       | o_dmi_rst_ip_n                  | YES  | Check with assert
// o_rst_n          | rst_stage[1]                    | YES  | Check with assert
//
//==
//
// STAGE2 Connection summary
// =========================
//  Reset State Pin | Signal                          | Test |
// -----------------+---------------------------------+------+------
// i_clk            | ref_clk                         | NO   |
// i_rst_n          | rst_stage[1]                    | YES  | Stage 1.No specific test code
// i_test_mode      | i_test_mode = TIED to 0         | NO   | Tied off
// i_test_rst_n     | i_por_rst_n                     | NO   | No test mode
// i_rst_req_n      | i_global_rst_req_n = TIED to 1  | NO   | Tied off           
// i_stretch_cycles | rst_cfg_global_rst.rst_stretch  | NO   | Use default
// i_rst_src_n      | i_wdt_rst_n & i_debug_rst_n     | YES  |
// i_mask_reset_src | rst_cfg_global_rst.rst_src_mask | NO   | Use default
// i_rst_ip_sw_n    | CSR:rst_sw_global_rst           | NO   | SW reset breaks AXI
// i_rst_ip_force   | 0                               | NO   | Tied off
// i_ack_reset_ip   | i_global_rst_ip_ack = TIED To 0 | NO   | Tied off
// o_rst_ack_n      | o_global_rst_ack_n              | NO   | Not connected. driven from i_global_rst_ip_ack
// o_rst_ip_n       | o_global_rst_ip_n               | YES  | Check with assert
// o_rst_n          | rst_stage[2]                    | YES  | Check with assert
//
//==
//
//==============================================================================
task reset_gen_test();
  // Control AO sw reset check
  localparam int unsigned DO_AO_SW_RESET = 0;

  `uvm_info("RESET_GEN_TEST", "Test Start", UVM_NONE)

  //============================================================================
  // STAGE 0

  //// Set power on reset
  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_por_rst();
  //end
  //#10us;

  //// Do the HW reset
  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_hw_rst();
  //end
  //#10us;

  // DO the sw reset for stage 0
  // Can bypass with DO_AO_SW_RESET
  //$display("%m DEBUG198");
  //if (DO_AO_SW_RESET) begin
  //  for (int i=0; i<10; i++) begin
  //    #10us;
  //    do_sw_rst(0);
  //$display("%m DEBUG199 %0d", i);
  //  end
  //  #10us;
  //end
  //$display("%m DEBUG199");

  //#10us;

  ////============================================================================
  //// STAGE 1
  //// i_dmi_rst_n     ->  i_rst_ip_req_n
  //// i_tamper_rst_n  ->  i_rst_src_n
  //// i_mbist_rst_n   ->  i_rst_src_n
  //// sw reset
  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_dmi_reset();
  //end
  //#10us;

  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_tamper_reset();
  //end
  //#10us;

  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_mbist_reset();
  //end
  //#10us;

  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_sw_rst(1);
  //end
  //#10us

  ////============================================================================
  //// STAGE 2
  //// i_debug_rst_n ->  i_rst_src_n (use force to set)
  //// i_wdt_rst_n   ->  i_rst_src_n (use force to set)
  //// sw reset
  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_debug_reset();
  //end
  //#10us;

  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_wdt_reset();
  //end
  //#10us;

  //for (int i=0; i<10; i++) begin
  //  #10us;
  //  do_sw_rst(2);
  //end
  #100us

  //============================================================================
  // register test
  do_rst_gen_reg_check();


  repeat(10)
  #100us;

endtask

