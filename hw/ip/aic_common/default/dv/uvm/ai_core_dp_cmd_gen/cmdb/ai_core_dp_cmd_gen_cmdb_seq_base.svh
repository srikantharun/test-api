// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_CMDB_AGENT_SEQ_BASE_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_CMDB_AGENT_SEQ_BASE_SVH

class ai_core_dp_cmd_gen_cmdb_seq_base extends uvm_sequence #(ai_core_dp_cmd_gen_cmdb);

    ai_core_dp_cmd_gen_cmdb_agent         m_cmdb_agent;
    axi_master_write_random_sequence      axi_seq;

    `uvm_object_utils(ai_core_dp_cmd_gen_cmdb_seq_base)

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
        if (phase != null)
            phase.drop_objection(this);
    endtask : post_start

    task body();
        ai_core_dp_cmd_gen_cmdb_sqr _sqr;
        assert($cast(_sqr, m_sequencer));

        `uvm_info(get_type_name(), $psprintf("Body %0d programs, %0d transactions (0x%x-0x%x)", _sqr.m_env_cfg.n_programs, _sqr.m_env_cfg.n_transactions, this.m_cmdb_agent.m_mem_range.base, this.m_cmdb_agent.m_mem_range.top), UVM_LOW)

        for (int p = 0; p < _sqr.m_env_cfg.n_programs; p++) begin
            `uvm_info(get_name(), $psprintf("Program %0d of %0d", p, _sqr.m_env_cfg.n_programs), UVM_LOW);
            while (m_cmdb_agent.idx != _sqr.m_env_cfg.active_cmdb_agent) begin
                #1us;
            end

            for (int i = 0; i < _sqr.m_env_cfg.n_transactions; i++) begin
                int unsigned _pc = $urandom_range(100, 0);
                if (_pc <= _sqr.m_env_cfg.cmdb_pc_error) begin
                    ai_core_dp_cmd_gen_cmdb_illegal _req;
                    `uvm_create(_req)
                    assert($cast(req, _req));
                end
                else begin
                    `uvm_create(req)
                end
                req.base = this.m_cmdb_agent.m_mem_range.base;
                req.top  = this.m_cmdb_agent.m_mem_range.top;

                assert(req.randomize());

                // Initialise the memory
                if (i == 0) begin
                    axi_seq  = axi_master_write_random_sequence::type_id::create("axi_seq");
                    assert(axi_seq.randomize() with {
                                                        sequence_length      == (local::req.top-local::req.base+1);
                                                        cfg_addr             == (local::req.base*8);
                                                        burst_size           == svt_axi_transaction::BURST_SIZE_64BIT;
                                                        burst_type           == svt_axi_transaction::FIXED;
                                                        burst_length         == 1;
                                                        max_bw               == 8;
                                                        min_addr_valid_delay == 0;
                                                        max_addr_valid_delay == 16;
                                                        min_bready_delay     == 0;
                                                        max_bready_delay     == 16;
                                                        foreach(cfg_data[j]) { cfg_data[j] == local::req.base + j; }
                    });
                    axi_seq.print();
                    axi_seq.start(m_cmdb_agent.axi_system_env.master[0].sequencer);
                end

                // Send the Command
                `uvm_send(req)
            end

            _sqr.m_env_cfg.next_cmdb_agent();
        end
    endtask : body

endclass : ai_core_dp_cmd_gen_cmdb_seq_base

`endif // GUARD_AI_CORE_DP_CMD_GEN_CMDB_AGENT_SEQ_BASE_SVH
