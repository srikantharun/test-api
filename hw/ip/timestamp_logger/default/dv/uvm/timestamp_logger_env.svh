// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_ENV_SVH
`define GUARD_TIMESTAMP_LOGGER_ENV_SVH

class timestamp_logger_env extends uvm_env;

    `uvm_component_utils(timestamp_logger_env)

    timestamp_logger_env_cfg           m_env_cfg;
    timestamp_logger_agent             m_agent;

    function  new(string name, uvm_component parent);
        super.new(name, parent);

        // Set a timeformat
        $timeformat(-9, 3, "ns", 8);
    endfunction : new

    function void build_phase(uvm_phase phase);
        `uvm_info("build_phase", "Entered...", UVM_LOW);

        if (!uvm_config_db#(timestamp_logger_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg)) begin
            `uvm_fatal(get_full_name(), "Failed to get env_cfg from config_db")
        end

        uvm_config_db#(timestamp_logger_env_cfg)::set(this, "*", "m_env_cfg", m_env_cfg);
        m_agent = timestamp_logger_agent::type_id::create("m_agent", this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
       `uvm_info("connect_phase", "Entered...", UVM_LOW);
       `uvm_info(get_full_name(), $psprintf("\n%s", m_env_cfg.sprint()), UVM_NONE)
    endfunction : connect_phase

    task reset_phase(uvm_phase phase);
        `uvm_info("reset_phase", "Entered...", UVM_LOW);
        phase.raise_objection(this, "Reset");
        phase.drop_objection(this);
    endtask

    task run_phase(uvm_phase phase);
        `uvm_info("run_phase", "Entered...", UVM_LOW);
    endtask : run_phase

endclass : timestamp_logger_env

`endif // GUARD_TIMESTAMP_LOGGER_ENV_SVH
