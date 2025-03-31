// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style resource allocator
// Devide memory range into pool of fixed sized ranges
// Owner: abond

// Class : axe_uvm_memory_range
class axe_uvm_memory_range extends uvm_object;

    typedef bit [63:0] uint64;

    uint64 base;
    uint64 top;

    `uvm_object_utils_begin(axe_uvm_memory_range)
        `uvm_field_int(base, UVM_DEFAULT)
        `uvm_field_int(top,  UVM_DEFAULT)
    `uvm_object_utils_end

    /* Function: new

       Constructor

       Parameters:

          name - Name of the class
          base - base address
          top  - top address

       Returns:

          Instance axe_uvm_memory_range
    */
    function new (string name="", uint64 base=0, uint64 top=0);
        super.new(name);
        this.base = base;
        this.top  = top;
    endfunction : new

endclass : axe_uvm_memory_range

// Class : axe_uvm_resource_allocator
class axe_uvm_memory_allocator extends axe_uvm_resource_allocator #(axe_uvm_memory_range);

    typedef bit [63:0] uint64;

    uint64 base;
    uint64 top;
    uint64 partition_size;

    `uvm_component_utils_begin(axe_uvm_memory_allocator)
        `uvm_field_int(base,               UVM_DEFAULT)
        `uvm_field_int(top,                UVM_DEFAULT)
        `uvm_field_int(partition_size,     UVM_DEFAULT)
        `uvm_field_queue_object(available, UVM_DEFAULT)
        `uvm_field_queue_object(reserved,  UVM_DEFAULT)
    `uvm_component_utils_end

    /* Function: new

       Constructor

       Parameters:

          name - Name of the scoreboard class
          parent - Parent class

       Returns:

          Instance axe_uvm_resource_allocator
    */
    function new (string name, uvm_component parent);
        super.new(name, parent);
        policy = ALLOCATE_RANDOM;
    endfunction : new

    /* Function: initialize

        Initialize pool

    */
    virtual function void initialize();
        uint64 addr = base;

        if ((available.size() + reserved.size()) > 0) begin
            `uvm_fatal(get_type_name(), $sformatf("Allocator is already initialized"))
        end

        while (addr <= top-partition_size+1) begin
           axe_uvm_memory_range r = new($sformatf("0x%x-0x%x", addr, addr+partition_size-1), addr, addr+partition_size-1);
           available.push_back(r);
           addr += partition_size;
        end
    endfunction : initialize
endclass : axe_uvm_memory_allocator
