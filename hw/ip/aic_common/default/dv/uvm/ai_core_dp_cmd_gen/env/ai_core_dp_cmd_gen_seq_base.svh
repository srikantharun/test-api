// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_AI_CORE_DP_CMD_GEN_SEQ_BASE_SVH
`define GUARD_AI_CORE_DP_CMD_GEN_SEQ_BASE_SVH

class ai_core_cmd_gen_seq_base extends uvm_sequence #(uvm_sequence_item);

    ai_core_dp_cmd_gen_cmdb_agent m_cmdb_agent[int];

    `uvm_object_utils(ai_core_cmd_gen_seq_base)

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

        #100ns; // Run-off
        if (phase != null)
            phase.drop_objection(this);
    endtask : post_start

    task body();
        for (int i = 0; i < m_cmdb_agent.size(); i++)
        begin
            fork
                automatic int idx = i;
                start_cmdb_agent(idx);
            join_none
        end
        wait fork;
    endtask : body

    task automatic start_cmdb_agent(int idx);
        ai_core_dp_cmd_gen_cmdb_seq_base seq;

        seq              = ai_core_dp_cmd_gen_cmdb_seq_base::type_id::create("seq");
        seq.m_cmdb_agent = m_cmdb_agent[idx];
        seq.set_item_context(this, m_cmdb_agent[idx].m_cmdb_sqr);
        assert(seq.randomize());
        seq.set_starting_phase(get_starting_phase());
        seq.start(m_cmdb_agent[idx].m_cmdb_sqr, this);
    endtask : start_cmdb_agent
endclass : ai_core_cmd_gen_seq_base

`endif // GUARD_AI_CORE_DP_CMD_GEN_SEQ_BASE_SVH
