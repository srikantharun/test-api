`ifndef TEST_SV
`define TEST_SV


class test extends uvm_test;

    typedef logic unsigned [1:0]  small_unsigned_t;
    typedef logic signed   [7:0]  medium_signed_t;

    axe_uvm_numeric#(small_unsigned_t)        m_small_unsigned_numeric;
    axe_uvm_numeric#(medium_signed_t)         m_medium_signed_numeric;
    `uvm_component_utils(test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    function void build_phase(uvm_phase phase);
        m_small_unsigned_numeric = axe_uvm_numeric#(small_unsigned_t)::type_id::create("m_small_unsigned_numeric", this);
        m_medium_signed_numeric  = axe_uvm_numeric#(medium_signed_t)::type_id::create("m_medium_signed_numeric", this); 
    endfunction : build_phase

    task run_phase(uvm_phase phase);
        phase.raise_objection(this);
        m_small_unsigned_numeric.print();
        m_medium_signed_numeric.print();

        for (int i = 0; i < 100; i++)
        begin
            `uvm_info(get_type_name(), $sformatf("Value = %0d", m_medium_signed_numeric.get_random(0)), UVM_NONE)
        end

        // Test Distributions
        begin
            int res[int unsigned];
            axe_uvm_distribution distribution = new();
  
            // Uniform dist
            distribution.add_range(10,  0,  9);
            distribution.add_range(50, 10, 19);
            distribution.add_range(20, 20, 24);
            distribution.add_range(1,  25, 100);

            for (int i = 0; i < 100; i++)
                res[i] = 0;
            for (int i = 0; i < 100000; i++)
                res[distribution.next()] += 1;
            for (int i = 0; i < 100; i++)
                $display("%0d, %0d", i, res[i]);
        end

        begin
            int res[int unsigned];
            axe_uvm_distribution distribution = new();
  
            // Uniform dist
            distribution.add_rate(1,  50);
            for (int i = 0; i < 100; i++)
                res[i] = 0;
            for (int i = 0; i < 100000; i++)
                res[distribution.next()] += 1;
            for (int i = 0; i < 100; i++)
                $display("%0d, %0d", i, res[i]);
        end
        phase.drop_objection(this);    
    endtask : run_phase  
endclass : test

`endif // TEST_SV
