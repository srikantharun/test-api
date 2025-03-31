// (C) Copyright Axelera AI 2023
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: AI Core LS IFD ODR CMD Block Test using random fabric
//              (either LC or TC) with linear patterns and lightweight
//              command
// Owner: Rafael Frangulian <rafael.frangulian@axelera.ai>

`ifndef GUARD_AIC_LS_DMC_CMDB_LIGHTCMD_TEST_SV
`define GUARD_AIC_LS_DMC_CMDB_LIGHTCMD_TEST_SV

class aic_ls_dmc_cmdb_lightcmd_test extends aic_ls_dmc_cmdb_defbased_test;
  `uvm_component_utils (aic_ls_dmc_cmdb_lightcmd_test);

  function new (string name="aic_ls_dmc_cmdb_lightcmd_test", uvm_component parent);
    super.new (name, parent);
    m_command_format = CMDFORMAT_LINEAR;
  endfunction : new

endclass:aic_ls_dmc_cmdb_lightcmd_test
`endif

