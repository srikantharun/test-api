// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: This test enables int16/int8 modes testing by forcing different values
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_INT_CASTING_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_INT_CASTING_TEST_SV

class aic_ls_dmc_cmdb_int_casting_test extends aic_ls_dmc_cmdb_tc_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_int_casting_test);

  function new (string name="aic_ls_dmc_cmdb_int_casting_test", uvm_component parent);
    super.new (name, parent);
  endfunction : new

  virtual task configure_phase(uvm_phase phase);
    super.configure_phase(phase);
    phase.raise_objection(this);
    `uvm_info (get_name(), "configure_phase() started.", UVM_LOW)
    m_test_iteration = 3;
    phase.drop_objection(this);
    `uvm_info (get_name(), "configure_phase() ended.", UVM_LOW)
  endtask

endclass:aic_ls_dmc_cmdb_int_casting_test
`endif

