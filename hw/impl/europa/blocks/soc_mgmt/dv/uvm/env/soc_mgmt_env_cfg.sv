
`ifndef GUARD_SOC_MGMT_ENV_CFG_SV
`define GUARD_SOC_MGMT_ENV_CFG_SV

// AI CORE MVM environment configuration class
class soc_mgmt_env_cfg extends uvm_object;

  `uvm_object_utils(soc_mgmt_env_cfg)

  /** Class Constructor */
  function new(string name = "soc_mgmt_env_cfg");
    super.new(name);
  endfunction : new

  // Objects handles

  bit has_coverage   = 0;
  bit has_scoreboard = 1;
  /** Variable that defines if the scoreboard to token interface is enables or not.
    * By default the scoreboard for the token mechanism is turned off because the AXI random testcases, for example soc_mgmt_axi_rnd_discr_test,
    * can randomize transactions that will lead to invalid values on the header token field. This makes the scoreboard to fail with invalid access.
    */
  bit has_scoreboard_token = 0;

endclass : soc_mgmt_env_cfg

`endif  // GUARD_SOC_MGMT_ENV_CFG_SV
