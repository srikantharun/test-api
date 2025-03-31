`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_SQR_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_SQR_SVH

class ai_core_dp_cmd_gen_cmdb_sqr extends uvm_sequencer#(ai_core_dp_cmd_gen_cmdb);

  ai_core_dp_cmd_gen_env_cfg                  m_env_cfg;

  `uvm_component_utils(ai_core_dp_cmd_gen_cmdb_sqr)

  function new (string name, uvm_component parent);
    super.new (name, parent);
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    assert(uvm_config_db#(ai_core_dp_cmd_gen_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));
  endfunction

endclass : ai_core_dp_cmd_gen_cmdb_sqr

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_SQR_SVH
