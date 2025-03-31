`ifndef TEST_SV
`define TEST_SV


class test extends uvm_test;

    axe_uvm_incrementor         m_incrementor;
    axe_uvm_bitwise_incrementor m_bitwise_incrementor;

    `uvm_component_utils(test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        m_incrementor        = axe_uvm_incrementor#(int)::type_id::create("m_incrementor", this);
        m_incrementor.value  = 0;
        m_incrementor.stride = 10;

        m_bitwise_incrementor        = axe_uvm_bitwise_incrementor#(int)::type_id::create("m_bitwise_incrementor", this);
        m_bitwise_incrementor.value  = 1;
        m_bitwise_incrementor.stride = 1;
    endfunction : build_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);

        begin
            m_incrementor.print();
            for (int i = 0; i < 3; i++) begin
                `uvm_info(get_type_name(), $sformatf("Head = %0d Next= %0d", m_incrementor.head(), m_incrementor.next()), UVM_NONE)
            end
            m_incrementor.print();
        end
        begin
            m_bitwise_incrementor.print();
            for (int i = 0; i < 3; i++) begin
                `uvm_info(get_type_name(), $sformatf("Head = %0d Next= %0d", m_bitwise_incrementor.head(), m_bitwise_incrementor.next()), UVM_NONE)
            end
            m_bitwise_incrementor.print();
        end
        phase.drop_objection(this);    
    endtask : run_phase  
endclass : test

`endif // TEST_SV
