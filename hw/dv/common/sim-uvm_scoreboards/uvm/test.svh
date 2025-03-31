`ifndef TEST_SV
`define TEST_SV

class test_item extends uvm_transaction;

    rand int      my_int;
    rand bit[1:0] my_index;

    `uvm_object_utils_begin(test_item)
        `uvm_field_int(my_int,   UVM_DEFAULT)
        `uvm_field_int(my_index, UVM_DEFAULT)
    `uvm_object_utils_end

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the test_item class
       Returns:

          Instance of test_item 
    */
    function new(string name = "test_item", uvm_component initiator = null);
        super.new(name, initiator);
    endfunction : new
endclass : test_item

class test_idx_sb extends axe_uvm_indexed_scoreboard #(test_item, test_item, int);

    `uvm_component_utils(test_idx_sb)

    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    virtual function indices_t indices();
        return '{0, 1, 2, 3};
    endfunction : indices

    virtual function int index(test_item t);
        return t.my_index;
    endfunction : index
endclass : test_idx_sb

class test extends uvm_test;

    typedef axe_uvm_scoreboard #(test_item, test_item) sb_type;
    sb_type     m_sb;
    test_idx_sb m_idx_sb;


    uvm_analysis_port #(test_item) m_port;

    `uvm_component_utils(test)

    function new(string name, uvm_component parent);
        super.new(name, parent);
        m_port = new("m_port", this);
    endfunction : new

    function void build_phase(uvm_phase phase);
      m_sb     = sb_type::type_id::create("m_sb", this);
      m_idx_sb = test_idx_sb::type_id::create("m_idx_sb", this);
    endfunction : build_phase

    function void connect_phase(uvm_phase phase);
        m_port.connect(m_sb.analysis_imp_exp);
        m_port.connect(m_sb.analysis_imp_obs);

        m_port.connect(m_idx_sb.analysis_imp_exp);
        m_port.connect(m_idx_sb.analysis_imp_obs);        
    endfunction : connect_phase

    task run_phase(uvm_phase phase);
        test_item item;
        phase.raise_objection(this);
        for (int i = 0; i < 100; i++) begin
          item = new();
          assert(item.randomize());
          #10;
          m_port.write(item);
        end
        phase.drop_objection(this);    
    endtask : run_phase  
endclass : test

`endif // TEST_SV
