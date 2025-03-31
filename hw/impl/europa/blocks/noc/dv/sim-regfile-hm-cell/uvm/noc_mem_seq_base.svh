// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner: abond

`ifndef GUARD_NOC_MEM_SEQ_BASE_SVH
`define GUARD_NOC_MEM_SEQ_BASE_SVH

class noc_mem_seq_base extends uvm_sequence #(noc_mem_item);

    noc_mem_sqr          m_sqr;

    `uvm_object_utils(noc_mem_seq_base)

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

    task pre_body();
        // Initialize the memory
        assert($cast(m_sqr, m_sequencer));

        for (int i = m_sqr.m_mem_allocator.base; i < m_sqr.m_mem_allocator.top; i++) begin
            `uvm_create(req)
            req.wr_en  = 1'b1;
            req.wr_addr   = i;
            req.wr_data   = i;
            req.wr_ben    = '1;
            `uvm_send(req)
        end
    endtask : pre_body

    task body();
        begin
        end
    endtask : body

endclass : noc_mem_seq_base

class noc_mem_capacity_seq extends noc_mem_seq_base;

    `uvm_object_utils(noc_mem_capacity_seq)

    function new(string name = "");
        super.new(name);
    endfunction : new

    task body();
        for (int i = m_sqr.m_mem_allocator.base; i < m_sqr.m_mem_allocator.top; i++) begin
            `uvm_create(req)
            req.rd_en     = 1'b1;
            req.rd_addr   = i;
            `uvm_send(req)
        end
    endtask : body
endclass : noc_mem_capacity_seq

class noc_mem_random_seq extends noc_mem_seq_base;

    axe_uvm_memory_range mem_range;

    `uvm_object_utils(noc_mem_random_seq)

    function new(string name = "");
        super.new(name);
    endfunction : new

    task body();
        int          n;
        int unsigned rd_addr, wr_addr;

        n = 0;
        while (n < m_sqr.m_env_cfg.n_transactions) begin
            int i = $urandom_range(32, 1);
            mem_range = m_sqr.m_mem_allocator.allocate();

            `uvm_info(get_name(), $psprintf("%0d transactions in range 0x%x-0x%x", i, mem_range.base, mem_range.top), UVM_NONE);
            repeat(i) begin
                rd_addr = $urandom_range(mem_range.top, mem_range.base);
                wr_addr = $urandom_range(mem_range.top, mem_range.base);
                `uvm_create(req)
                assert(req.randomize() with { wr_addr == local::wr_addr; rd_addr == local::rd_addr; });
                `uvm_send(req)
            end
            m_sqr.m_mem_allocator.free(mem_range);
            n += i;
        end
    endtask : body
endclass : noc_mem_random_seq
`endif // GUARD_NOC_MEM_SEQ_BASE_SVH
