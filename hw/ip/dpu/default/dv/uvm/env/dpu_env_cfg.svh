
`ifndef GUARD_DPU_ENV_CFG_SV
`define GUARD_DPU_ENV_CFG_SV

class dpu_env_cfg extends uvm_object;

  `uvm_object_utils(dpu_env_cfg)
  
  function new (string name="dpu_env_cfg");
    super.new (name);
  endfunction:new

  bit has_coverage   = 1;
  bit has_scoreboard = 1;

endclass:dpu_env_cfg

`endif
