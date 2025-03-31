// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_ENV_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_ENV_SVH

class ai_core_dp_cmd_gen_env extends uvm_env;

    `uvm_component_utils(ai_core_dp_cmd_gen_env)

    ai_core_dp_cmd_gen_env_cfg        m_env_cfg;

    axe_uvm_memory_allocator          m_mem_allocator;

    virtual dp_cmd_gen_cmdb_if          cmdb_vif;
    ai_core_dp_cmd_gen_cmdb_drv         m_cmdb_drv;
    ai_core_dp_cmd_gen_cmdb_sqr         m_cmdb_sqr;
    ai_core_dp_cmd_gen_cmdb_mon         m_cmdb_mon;
    ai_core_dp_cmd_gen_cmdb_cov         m_cmdb_cov;
    ai_core_dp_cmd_gen_cmdb_scoreboard  m_cmdb_sb;
    ai_core_dp_cmd_gen_cmdb_agent       m_cmdb_agent[$];

    svt_axi_system_env                axi_system_env;
    cust_svt_axi_system_configuration cfg;


    ai_core_cmd_gen_seq_base          vseq;

    ai_core_dp_cmd_gen_model#(aic_dp_cmd_gen_pkg::dummy_dp_command_t)       m_model;


    virtual dp_cmd_gen_command_if  #(aic_dp_cmd_gen_pkg::dummy_dp_command_t)  command_vif;
    ai_core_dp_cmd_gen_command_mon #(aic_dp_cmd_gen_pkg::dummy_dp_command_t)  m_command_mon;
    ai_core_dp_cmd_gen_command_scoreboard                                     m_command_sb;

    function  new(string name, uvm_component parent);
        super.new(name, parent);

        // Set a timeformat
        $timeformat(-9, 3, "ns", 8);
    endfunction : new

    function void build_phase(uvm_phase phase);

        // Testbench Configuration
        if (!uvm_config_db#(ai_core_dp_cmd_gen_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg)) begin
            `uvm_fatal(get_full_name(), "Failed to get env_cfg from config_db")
        end

        // Interfaces
        assert(uvm_config_db #(virtual dp_cmd_gen_cmdb_if)::get(this, "", "cmdb_vif",  cmdb_vif)); 
        assert(uvm_config_db #(virtual dp_cmd_gen_command_if#(aic_dp_cmd_gen_pkg::dummy_dp_command_t))::get(this, "", "command_vif", command_vif));

        // Memory Allocator
        m_mem_allocator = axe_uvm_memory_allocator::type_id::create("m_mem_allocator", this);
        m_mem_allocator.base           = 0;
        m_mem_allocator.top            = m_env_cfg.command_depth;
        m_mem_allocator.partition_size = m_env_cfg.command_depth / m_env_cfg.n_agents;

        // AXI
        cfg = cust_svt_axi_system_configuration::type_id::create("cfg");
        uvm_config_db#(svt_axi_system_configuration)::set(this, "axi_system_env", "cfg", cfg);
        axi_system_env = svt_axi_system_env::type_id::create("axi_system_env", this);
    
        uvm_config_db#(uvm_object_wrapper)::set(this, "axi_system_env.sequencer.main_phase", "default_sequence", axi_null_virtual_sequence::type_id::get());

        // Model
        m_model = ai_core_dp_cmd_gen_model#(aic_dp_cmd_gen_pkg::dummy_dp_command_t)::type_id::create("m_model", this);

        // Command Side
        uvm_config_db#(virtual dp_cmd_gen_cmdb_if)::set(this, "m_cmdb_*", "cmdb_vif",  cmdb_vif);
        uvm_config_db#(ai_core_dp_cmd_gen_env_cfg)::set(this, "m_cmdb_*", "m_env_cfg", m_env_cfg);
        m_cmdb_sqr = ai_core_dp_cmd_gen_cmdb_sqr::type_id::create("m_cmdb_sqr", this);
        m_cmdb_drv = ai_core_dp_cmd_gen_cmdb_drv::type_id::create("m_cmdb_drv", this);
        m_cmdb_mon = ai_core_dp_cmd_gen_cmdb_mon::type_id::create("m_cmdb_mon", this);
        m_cmdb_cov = ai_core_dp_cmd_gen_cmdb_cov::type_id::create("m_cmdb_cov", this);
 
        m_cmdb_sb  = ai_core_dp_cmd_gen_cmdb_scoreboard::type_id::create("m_cmdb_sb", this);

        uvm_config_db#(axe_uvm_memory_allocator)::set(this,    "m_cmdb_agent[*]", "m_mem_allocator", m_mem_allocator);
        uvm_config_db#(ai_core_dp_cmd_gen_cmdb_sqr)::set(this, "m_cmdb_agent[*]", "m_cmdb_sqr",      m_cmdb_sqr);
        uvm_config_db#(ai_core_dp_cmd_gen_cmdb_drv)::set(this, "m_cmdb_agent[*]", "m_cmdb_drv",      m_cmdb_drv);
        uvm_config_db#(ai_core_dp_cmd_gen_cmdb_mon)::set(this, "m_cmdb_agent[*]", "m_cmdb_mon",      m_cmdb_mon);
        uvm_config_db#(svt_axi_system_env)::set(this,          "m_cmdb_agent[*]", "axi_system_env",  axi_system_env);
        for (int i = 0; i < m_env_cfg.n_agents; i++) begin
           ai_core_dp_cmd_gen_cmdb_agent _agent_ = ai_core_dp_cmd_gen_cmdb_agent::type_id::create($psprintf("m_cmdb_agent[%0d]",i), this);
           _agent_.idx = i;
            m_cmdb_agent.push_back(_agent_);
        end

        // Instruction Side
        uvm_config_db#(virtual dp_cmd_gen_command_if#(aic_dp_cmd_gen_pkg::dummy_dp_command_t))::set(this, "m_command_*", "command_vif", command_vif); 

        m_command_mon = ai_core_dp_cmd_gen_command_mon#(aic_dp_cmd_gen_pkg::dummy_dp_command_t)::type_id::create("m_command_mon", this);
        m_command_sb  = ai_core_dp_cmd_gen_command_scoreboard::type_id::create("m_command_sb", this);

        // Virtual Sequence
        vseq = ai_core_cmd_gen_seq_base::type_id::create("vseq");
        vseq.set_item_context(null, null);
        assert(vseq.randomize());

        for (int i = 0; i < m_env_cfg.n_agents; i++)
        begin
            vseq.m_cmdb_agent[i] = this.m_cmdb_agent[i];
        end
    endfunction : build_phase

    function void end_of_elaboration_phase(uvm_phase phase);
        super.end_of_elaboration_phase(phase);

        // Stop the SVT VIP being so chatty
        axi_system_env.set_report_verbosity_level(UVM_NONE);
        axi_system_env.master[0].set_report_verbosity_level(UVM_NONE);
    endfunction : end_of_elaboration_phase

    function void connect_phase(uvm_phase phase);
        // Connect Sequencer to Driver
        m_cmdb_drv.seq_item_port.connect(m_cmdb_sqr.seq_item_export);

        // Connect Driver to Model
        m_cmdb_drv.ap.connect(m_model.analysis_export);

        // Connect Monitor to Coverage
        m_cmdb_mon.ap.connect(m_cmdb_cov.analysis_export);
 
        // Connect Scoreboards
        m_model.cmdb_ap.connect(m_cmdb_sb.analysis_imp_exp);
        m_cmdb_mon.ap.connect(m_cmdb_sb.analysis_imp_obs);

        m_model.command_ap.connect(m_command_sb.analysis_imp_exp);
        m_command_mon.ap.connect(m_command_sb.analysis_imp_obs);

    endfunction : connect_phase

    task reset_phase(uvm_phase phase);
        `uvm_info("reset_phase", "Entered...", UVM_LOW)
        phase.raise_objection(this, "Reset");
        phase.drop_objection(this);
    endtask

    task run_phase(uvm_phase phase);
        vseq.set_starting_phase(phase);
        vseq.start(null);
    endtask : run_phase

endclass : ai_core_dp_cmd_gen_env

`endif // GUARD_AI_CORE_DP_CMD_GEN_ENV_SVH
