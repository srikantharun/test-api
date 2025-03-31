`ifndef TEST_SV
`define TEST_SV

class int_allocator extends axe_uvm_resource_allocator #(int);
  
    `uvm_component_utils_begin(int_allocator)
        `uvm_field_queue_int(available, UVM_DEFAULT)
        `uvm_field_queue_int(reserved,  UVM_DEFAULT)
    `uvm_component_utils_end

    function new (string name, uvm_component parent);
        super.new(name, parent);
        policy = ALLOCATE_RANDOM;
    endfunction : new

    virtual function void initialize();
        for (int i = 0; i < 20 ; i++) available.push_back(i);
    endfunction : initialize

endclass : int_allocator

class test extends uvm_test;

    int_allocator            m_int_allocator;
    axe_uvm_memory_allocator m_mem_allocator;


    `uvm_component_utils(test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        m_int_allocator = int_allocator::type_id::create("m_int_allocator", this);
        m_mem_allocator = axe_uvm_memory_allocator::type_id::create("m_mem_allocator", this);
        m_mem_allocator.base           = 64'h00000;
        m_mem_allocator.top            = 64'h10000;
        m_mem_allocator.partition_size = 64'h01000;
    endfunction : build_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        m_int_allocator.print();
        for (int i = 0; i < 10; i++) begin
            `uvm_info(get_type_name(), $sformatf("Allocated %0d", m_int_allocator.allocate()), UVM_NONE)
        end
        m_int_allocator.print();

        begin
            axe_uvm_memory_range mr[$];
            m_mem_allocator.print();
            for (int i = 0; i < 3; i++) begin
                mr.push_back(m_mem_allocator.allocate());
                `uvm_info(get_type_name(), $sformatf("Allocated\n%s", mr[i].sprint()), UVM_NONE)
            end
            m_mem_allocator.print();
            m_mem_allocator.free(mr[0]);
            m_mem_allocator.print();
        end

        phase.drop_objection(this);    
    endtask : run_phase  
endclass : test

`endif // TEST_SV
