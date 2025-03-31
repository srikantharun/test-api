`ifndef TOKEN_AGENT_CONFIG_SV
`define TOKEN_AGENT_CONFIG_SV

/** Configuration object to token agent */
class token_agent_config extends uvm_object;
  `uvm_object_utils(token_agent_config)

  /** type of agent (by default the agent is configured as Master) */
  token_agent_type_enm m_type = TOK_AGT_MASTER;
  /** variable to specify if the agent is active or not (by default is active) */
  bit m_b_active = 1;
  /** variable to specify if the agent has consumer line (by default is active) */
  bit m_b_cons_active = 1;
  /** variable to specify if the agent has producer line (by default is active) */
  bit m_b_prod_active = 1;
  /** specify whether the monitor has to wait for reset assertion then negation before starting it's sampling */
  bit m_b_init_reset = 0;
  /** specify the value of the timeout used in consumer monitor (by default is 10ms) */
  time m_cons_timeout = 10ms;
  /** specify the value of the timeout used in producer monitor (by default is 10ms) */
  time m_prod_timeout = 10ms;

  function new (string name = "token_agent_config");
    super.new (name);
  endfunction

endclass

`endif // TOKEN_AGENT_CONFIG_SV


