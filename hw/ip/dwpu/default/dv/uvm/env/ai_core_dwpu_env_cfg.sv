
`ifndef GUARD_AI_CORE_DWPU_ENV_CFG_SV
`define GUARD_AI_CORE_DWPU_ENV_CFG_SV

// AI CORE DWPU environment configuration class
class ai_core_dwpu_env_cfg extends uvm_object;

  `uvm_object_utils(ai_core_dwpu_env_cfg)

    // Objects handles
  bit ral_test;
  bit has_coverage   = 1;
  bit has_scoreboard = 1;
  bit has_scoreboard_token = 1;
  bit is_gls = 0;
  bit en_tvalid_during_rst_check = 1;

  /** Class Constructor */
  function new(string name = "ai_core_dwpu_env_cfg");
    super.new(name);
    if ($value$plusargs("GLS=%0d", is_gls)) begin
      `uvm_info(get_type_name(), $sformatf("is_gls is set to: %0d", is_gls), UVM_LOW)
    end else begin
      `uvm_info(get_type_name(), $sformatf("is_gls is set to default: %0d", is_gls), UVM_LOW)
    end
  endfunction : new

endclass : ai_core_dwpu_env_cfg

`endif  // GUARD_AI_CORE_DWPU_ENV_CFG_SV
