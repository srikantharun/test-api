
`ifndef GUARD_AIC_DMC_AGENT_CFG_SV
`define GUARD_AIC_DMC_AGENT_CFG_SV

// AI CORE LS environment configuration class
class aic_ls_agent_cfg extends uvm_object;

  `uvm_object_utils(aic_ls_agent_cfg)

  /** Class Constructor */
  function new(string name = "aic_ls_agent_cfg");
    super.new(name);
  endfunction : new

  // Objects handles
  bit is_active      = 0;
  bit has_coverage   = 1;
endclass : aic_ls_agent_cfg

`endif 
