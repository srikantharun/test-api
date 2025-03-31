// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test
//              Using Offset Based Command Format
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_OFFSETBASED_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_OFFSETBASED_TEST_SV

class aic_ls_dmc_cmdb_offsetbased_test extends aic_ls_dmc_cmdb_defbased_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_offsetbased_test);

  function new (string name="aic_ls_dmc_cmdb_offsetbased_test", uvm_component parent);
    super.new (name, parent);
    m_command_format = CMDFORMAT_OFFSET_BASED;
  endfunction : new
endclass:aic_ls_dmc_cmdb_offsetbased_test
`endif

