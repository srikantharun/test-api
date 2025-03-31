// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_ENV_SVH
`define GUARD_NOC_MEM_ENV_SVH

class noc_mem_env extends uvm_env;

    `uvm_component_utils(noc_mem_env)

    noc_mem_env_cfg                   m_env_cfg;

    axe_uvm_memory_allocator          m_mem_allocator;

    noc_mem_sqr                       m_sqr;
    noc_mem_drv                       m_drv;
    noc_mem_mon                       m_mon;
    noc_mem_scoreboard                m_sb;

    virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) rd_vif;
    virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) wr_vif;

    noc_mem_seq_base                  seq;

    function  new(string name, uvm_component parent);
        super.new(name, parent);

        // Set a timeformat
        $timeformat(-9, 3, "ns", 8);
    endfunction : new

    function void build_phase(uvm_phase phase);

        // Testbench Configuration
        if (!uvm_config_db#(noc_mem_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg)) begin
            `uvm_fatal(get_full_name(), "Failed to get env_cfg from config_db")
        end

        // Interfaces
        assert(uvm_config_db #(virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::get(this, "", "rd_vif",  rd_vif));
        assert(uvm_config_db #(virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::get(this, "", "wr_vif",  wr_vif));

        // Memory Allocator
        m_mem_allocator = axe_uvm_memory_allocator::type_id::create("m_mem_allocator", this);
        m_mem_allocator.base           = 0;
        m_mem_allocator.top            = `DEPTH - 1;
        m_mem_allocator.partition_size = `DEPTH / m_env_cfg.n_partitions;

        uvm_config_db#(axe_uvm_memory_allocator)::set(this,                                       "m_*", "m_mem_allocator", m_mem_allocator);
        uvm_config_db#(virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::set(this, "m_*", "rd_vif",          rd_vif);
        uvm_config_db#(virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::set(this, "m_*", "wr_vif",          wr_vif);
        uvm_config_db#(noc_mem_env_cfg)::set(this, "m_*", "m_env_cfg", m_env_cfg);
        m_sqr = noc_mem_sqr::type_id::create("m_sqr", this);
        m_drv = noc_mem_drv::type_id::create("m_drv", this);
        m_mon = noc_mem_mon::type_id::create("m_mon", this);
        m_sb  = noc_mem_scoreboard::type_id::create("m_sb", this);

        //m_cov = noc_mem_cov::type_id::create("m_cmdb_cov", this);

        // Sequence
        seq = noc_mem_seq_base::type_id::create("seq");
        seq.set_item_context(null, null);
        assert(seq.randomize());

    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
        // Connect Sequencer to Driver
        m_drv.seq_item_port.connect(m_sqr.seq_item_export);

        // Connect Scoreboards
        m_drv.ap.connect(m_sb.analysis_imp_exp);
        m_mon.ap.connect(m_sb.analysis_imp_obs);

    endfunction : connect_phase

    task reset_phase(uvm_phase phase);
        phase.raise_objection(this, "Reset");
        phase.drop_objection(this);
    endtask

    task run_phase(uvm_phase phase);
        seq.set_starting_phase(phase);
        seq.start(m_sqr, null);
    endtask : run_phase

endclass : noc_mem_env

`endif // GUARD_NOC_MEM_ENV_SVH
