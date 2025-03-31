// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS Sanity Test
//      Does HW reset and operates IFD ODR to access L1
// Owner: Raymond Garcia <raymond.garcia@axelera.ai>

`ifndef GUARD_CVA6V_SANITY_TEST_SV
`define GUARD_CVA6V_SANITY_TEST_SV

class cva6v_sanity_test extends cva6v_base_test;
  `uvm_component_utils (cva6v_sanity_test);

  function new (string name="cva6v_sanity_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task test_seq();
    `uvm_info(get_name(), "Start of test", UVM_LOW)

    #20us;
    `uvm_info(get_name(), "End of test", UVM_LOW)
  endtask

endclass:cva6v_sanity_test
`endif

