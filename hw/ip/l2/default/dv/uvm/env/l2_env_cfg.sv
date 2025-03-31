
`ifndef GUARD_L2_ENV_CFG_SV
`define GUARD_L2_ENV_CFG_SV

// L2 memory module environment configuration class
class l2_env_cfg extends uvm_object;
  `uvm_object_utils(l2_env_cfg)

  /** Clock divider configuration */
 // cc_clk_div_agent_config  m_clk_div_agt_cfg;
  
  /** Class Constructor */
  function new (string name="l2_env_cfg");
    super.new (name);
    
    /** Create sub configurations */
  //  m_clk_div_agt_cfg = cc_clk_div_agent_config::type_id::create("m_clk_div_agt_cfg");
  endfunction:new

  bit has_coverage   = 0;
  bit has_scoreboard = 1;

endclass:l2_env_cfg

`endif // GUARD_L2_ENV_CFG_SV
