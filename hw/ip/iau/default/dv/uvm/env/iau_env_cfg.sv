
`ifndef GUARD_IAU_ENV_CFG_SV
`define GUARD_IAU_ENV_CFG_SV

// IAU_DPU memory module environment configuration class
class iau_env_cfg extends uvm_object;

  `uvm_object_utils(iau_env_cfg)
  
  /** Class Constructor */
  function new (string name="iau_env_cfg");
    super.new (name);
  endfunction:new
  static bit [31:0] iau_base_addr;
  bit has_coverage   = 0;
  
  rand bit MVM_FLOW; // selecting if working in MVM flow or DPU flow
  bit passive_env = 0;
  bit axi_test;
  
  static bit has_iau_scoreboard = 1;


endclass:iau_env_cfg

`endif // GUARD_IAU_ENV_CFG_SV
