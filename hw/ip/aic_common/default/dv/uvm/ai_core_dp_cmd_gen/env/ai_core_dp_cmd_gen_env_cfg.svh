`ifndef GUARD_AI_CORE_DP_CMD_GEN_ENV_CFG_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_ENV_CFG_SVH

// IAU_DPU memory module environment configuration class
class ai_core_dp_cmd_gen_env_cfg extends uvm_object;

         int unsigned  command_depth     = `AIC_DP_CMD_GEN_COMMAND_DEPTH;
    rand int           n_agents          = 1;
    rand bit           cmdb_wait_on_done = 0;
    rand int unsigned  cmdb_rate         = 0;
    rand int unsigned  cmdb_pc_error     = 100;
    rand int unsigned  n_programs        = 0;
    rand int unsigned  n_transactions    = 0;
        int            active_cmdb_agent = 0;

    constraint c_n_agents       { soft n_agents           == 1; }
    constraint c_n_programs     { soft n_programs         == 1; }
    constraint c_n_transactions { soft n_transactions inside {[10:50]}; }
    constraint c_pc_error       { soft cmdb_pc_error      == 0; }

    `uvm_object_utils_begin(ai_core_dp_cmd_gen_env_cfg)
        `uvm_field_int(command_depth,     UVM_DEFAULT)
        `uvm_field_int(n_agents,          UVM_DEFAULT)
        `uvm_field_int(cmdb_wait_on_done, UVM_DEFAULT)
        `uvm_field_int(cmdb_rate,         UVM_DEFAULT)
        `uvm_field_int(cmdb_pc_error,     UVM_DEFAULT)
        `uvm_field_int(n_programs,        UVM_DEFAULT)
        `uvm_field_int(n_transactions,    UVM_DEFAULT)
        `uvm_field_int(active_cmdb_agent, UVM_DEFAULT)
    `uvm_object_utils_end

    function new (string name="ai_core_dp_cmd_gen_env_cfg");
        super.new (name);
    endfunction:new

    function void next_cmdb_agent();
        active_cmdb_agent = (active_cmdb_agent + 1) % n_agents;
    endfunction : next_cmdb_agent

endclass : ai_core_dp_cmd_gen_env_cfg 

`endif // GUARD_AI_CORE_DP_CMD_GEN_ENV_CFG_SVH
