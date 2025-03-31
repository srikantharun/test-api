// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test
//              Using 4D Fallback Command Format
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_4DFALLBACK_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_4DFALLBACK_TEST_SV

class aic_ls_dmc_cmdb_4Dfallback_test extends aic_ls_dmc_cmdb_3Dfallback_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_4Dfallback_test);

  function new (string name="aic_ls_dmc_cmdb_4Dfallback_test", uvm_component parent);
    super.new (name, parent);
    m_command_format = CMDFORMAT_4DIM_FALLBACK;
  endfunction : new

endclass:aic_ls_dmc_cmdb_4Dfallback_test
`endif

