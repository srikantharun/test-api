// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_AGENT_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_AGENT_SVH

class ai_core_dp_cmd_gen_cmdb_agent extends uvm_agent;

    int idx = 0;

    axe_uvm_memory_allocator          m_mem_allocator;
    axe_uvm_memory_range              m_mem_range;

    ai_core_dp_cmd_gen_cmdb_drv       m_cmdb_drv;
    ai_core_dp_cmd_gen_cmdb_sqr       m_cmdb_sqr;
    ai_core_dp_cmd_gen_cmdb_mon       m_cmdb_mon;

    svt_axi_system_env                axi_system_env;

    `uvm_component_utils_begin(ai_core_dp_cmd_gen_cmdb_agent)
        `uvm_field_int(idx,            UVM_DEFAULT)
        `uvm_field_object(m_mem_range, UVM_DEFAULT)
    `uvm_component_utils_end

    function  new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        assert(uvm_config_db#(axe_uvm_memory_allocator)::get(this,    "", "m_mem_allocator", m_mem_allocator));
        assert(uvm_config_db#(ai_core_dp_cmd_gen_cmdb_sqr)::get(this, "", "m_cmdb_sqr",      m_cmdb_sqr));
        assert(uvm_config_db#(ai_core_dp_cmd_gen_cmdb_drv)::get(this, "", "m_cmdb_drv",      m_cmdb_drv));
        assert(uvm_config_db#(ai_core_dp_cmd_gen_cmdb_mon)::get(this, "", "m_cmdb_mon",      m_cmdb_mon));
        assert(uvm_config_db#(svt_axi_system_env)::get(this,          "", "axi_system_env",  axi_system_env));
    endfunction : build_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        // Allocate a command memory range
        this.m_mem_range = this.m_mem_allocator.allocate();
        this.print();

        phase.drop_objection(this);
    endtask : run_phase

endclass : ai_core_dp_cmd_gen_cmdb_agent 

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_AGENT_SVH
