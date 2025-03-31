// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_AGENT_SVH
`define GUARD_TIMESTAMP_LOGGER_AGENT_SVH

class timestamp_logger_agent extends uvm_agent;

    timestamp_logger_env_cfg         m_env_cfg;
    timestamp_logger_event_drv       m_event_drv;
    timestamp_logger_event_sqr       m_event_sqr;
    timestamp_logger_event_mon       m_event_mon;
    //timestamp_logger_event_cov       m_event_cov;

    timestamp_logger_cfg_drv         m_cfg_drv;
    timestamp_logger_cfg_sqr         m_cfg_sqr;

    timestamp_logger_model           m_model;

    virtual axi_intf     #(.DW(`DW), .AW(`AW), .IDW(`MIDW)) extmem_vif;
            axi_sl_driver#(.DW(`DW), .AW(`AW), .IDW(`MIDW)) m_extmem_drv;

    timestamp_logger_vseq            vseq;

    `uvm_component_utils(timestamp_logger_agent)

    function  new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);

        assert(uvm_config_db#(virtual axi_intf#(.DW(`DW),.AW(`AW),.IDW(`MIDW)))::get(this, "", "extmem_vif",  extmem_vif));
        assert(uvm_config_db#(timestamp_logger_env_cfg)::get(this, "", "m_env_cfg", m_env_cfg));

        m_event_sqr = timestamp_logger_event_sqr::type_id::create("m_event_sqr", this);
        m_event_drv = timestamp_logger_event_drv::type_id::create("m_event_drv", this);
        m_event_mon = timestamp_logger_event_mon::type_id::create("m_event_mon", this);
        //m_event_cov = ai_core_dp_cmd_gen_cmdb_cov::type_id::create("m_event_cov", this);

        m_cfg_sqr = timestamp_logger_cfg_sqr::type_id::create("m_cfg_sqr", this);
        m_cfg_drv = timestamp_logger_cfg_drv::type_id::create("m_cfg_drv", this);

        m_model   = timestamp_logger_model::type_id::create("m_model", this);
        m_cfg_drv.m_model = m_model;

        // Slave driver
        m_extmem_drv = new("m_extmem_drv", extmem_vif);
        m_cfg_drv.m_extmem_drv = m_extmem_drv;

        // Virtual Sequence
        vseq = timestamp_logger_vseq::type_id::create("vseq");
        vseq.m_event_sqr = m_event_sqr;
        vseq.m_cfg_sqr   = m_cfg_sqr;
        vseq.m_event_drv = m_event_drv;
        vseq.m_cfg_drv   = m_cfg_drv;
        vseq.set_item_context(null, null);
        assert(vseq.randomize());

    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
        m_event_drv.seq_item_port.connect(m_event_sqr.seq_item_export);
        m_cfg_drv.seq_item_port.connect(m_cfg_sqr.seq_item_export);

        m_cfg_drv.ap.connect(m_model.analysis_imp_cfg);
        m_event_mon.ap.connect(m_model.analysis_imp_event);
    endfunction : connect_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        fork
            m_extmem_drv.run();
        join;

        vseq.set_starting_phase(phase);
        vseq.start(null);

        phase.drop_objection(this);
    endtask : run_phase

endclass : timestamp_logger_agent

`endif // GUARD_TIMESTAMP_LOGGER_AGENT_SVH
