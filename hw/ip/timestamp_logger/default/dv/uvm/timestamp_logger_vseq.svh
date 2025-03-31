// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_TIMESTAMP_LOGGER_VSEQ_SVH
`define GUARD_TIMESTAMP_LOGGER_VSEQ_SVH

class timestamp_logger_vseq extends uvm_sequence #(timestamp_logger_event_item);

    timestamp_logger_event_sqr       m_event_sqr;
    timestamp_logger_cfg_sqr         m_cfg_sqr;
    timestamp_logger_event_drv       m_event_drv;
    timestamp_logger_cfg_drv         m_cfg_drv;
    timestamp_logger_cfg_item        cfg_item;
    timestamp_logger_event_item      event_item;

    `uvm_object_utils(timestamp_logger_vseq)

    function new(string name = "");
        super.new(name);
    endfunction : new

    task pre_start();
        uvm_phase phase = get_starting_phase();
        if (phase != null)
            phase.raise_objection(this);
    endtask : pre_start

    task post_start();
        uvm_phase phase = get_starting_phase();
        #1us;
        if (phase != null)
            phase.drop_objection(this);
    endtask : post_start

    task body();
        `uvm_info(get_type_name(), $psprintf("Body %0d programs", m_event_sqr.m_env_cfg.n_programs), UVM_LOW);

        for (int i = 0; i < m_event_sqr.m_env_cfg.n_programs; i++) begin
            int transactions = 0;
            // Program and start
            `uvm_create_on(cfg_item, m_cfg_sqr)
            assert(cfg_item.randomize());
            `uvm_info(get_type_name(), $psprintf("Body program %0d (of %0d) %0d transactions", i, m_event_sqr.m_env_cfg.n_programs, cfg_item.n_transactions), UVM_LOW);
            `uvm_send(cfg_item)

            if (cfg_item.sync_ctrl) begin
                timestamp_logger_event_item event_item;
                `uvm_create_on(event_item, m_event_sqr)
                event_item.sync_start = 1;
                event_item.delay = $urandom_range(200, 100); // Must be long enough to allow register write to propagate
                `uvm_send(event_item)
            end

            // TODO - HACKY while there's a race condition
            while (m_event_drv.event_vif.capture_enable == 1'b0) @(posedge m_event_drv.event_vif.clk);

            // Send events
            while (transactions < cfg_item.n_transactions) begin
                `uvm_create_on(event_item, m_event_sqr)
                assert(event_item.randomize());
                `uvm_send(event_item)
                event_item.previous_item = event_item;
                transactions += $countones(event_item.triggers);
            end
            // Clear previous item
            event_item.previous_item = null;

            // Disable and Check
            cfg_item.capture_enable = 1'b0;
            cfg_item.stop           = cfg_item.sync_ctrl;
            `uvm_send(cfg_item)

            // TODO - HACKY while there's a race condition
            while (m_event_drv.event_vif.capture_enable == 1'b1) @(posedge m_event_drv.event_vif.clk);
        end
    endtask : body

endclass : timestamp_logger_vseq

`endif  // GUARD_TIMESTAMP_LOGGER_VSEQ_SVH
