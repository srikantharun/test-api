`ifndef DMA_TEST_SVH
`define DMA_TEST_SVH


class dma_base_test extends uvm_test;

    `uvm_component_utils(dma_base_test)

    dma_env m_env;

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        m_env = dma_env::type_id::create("m_env", this);
    endfunction : build_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        // TODO
        this.print();

        phase.drop_objection(this);    
    endtask : run_phase  
endclass : dma_base_test

`endif // DMA_TEST_SVH
