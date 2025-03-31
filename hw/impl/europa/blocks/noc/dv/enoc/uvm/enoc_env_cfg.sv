// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //
// *****************************************************************************************
// Description: This is a config class for ENOC TB ENV with control switches to en/disable
//              coverage, scoreboard and othe MISC features 
// *****************************************************************************************
`ifndef GUARD_ENOC_ENV_CFG_SV
`define GUARD_ENOC_ENV_CFG_SV

// NOC environment configuration class
class enoc_env_cfg extends uvm_object;


  /** UVM Component Utility macro */
  `uvm_object_utils(enoc_env_cfg)

 
  /** Class Constructor */
  function new (string name="enoc_env_cfg");
    super.new (name);
  endfunction:new

  bit has_coverage   = 1;
  bit has_scoreboard = 1;

endclass:enoc_env_cfg

`endif // GUARD_eNOC_ENV_CFG_SV

