
`ifndef GUARD_DMC_ADDR_GEN_CFG_SV
`define GUARD_DMC_ADDR_GEN_CFG_SV

// AI CORE DWPU environment configuration class
class dmc_addr_gen_cfg extends uvm_object;

  `uvm_object_utils(dmc_addr_gen_cfg)

  /** Class Constructor */
  function new(string name = "dmc_addr_gen_cfg");
    super.new(name);
  endfunction : new

  // Objects handles
  bit is_active      = 0;
  bit has_coverage   = 1;
endclass : dmc_addr_gen_cfg

`endif  // GUARD_DMC_ADDR_GEN_ENV_CFG_SV
