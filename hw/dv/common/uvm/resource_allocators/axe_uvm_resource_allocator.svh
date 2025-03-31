// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style resource allocator
// Define a pool of resources and provide methods to allocate
// Owner: abond

// Class : axe_uvm_resource_allocator
class axe_uvm_resource_allocator #(type T=uvm_object) extends uvm_component;

    typedef axe_uvm_resource_allocator #(T) this_t;

    resource_allocation_policy_t policy;
    T                            available[$];
    T                            reserved [$];

    `uvm_component_param_utils(this_t)

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
    endfunction : new

    /* Function:start_of_simulation_phase
       UVM Start of Simulation phase

       Parameters:
        phase - UVM built-in
    */
    virtual function void start_of_simulation_phase(uvm_phase phase);
        initialize();
    endfunction : start_of_simulation_phase

    /* Function: initialize

        Initialize pool

    */
    virtual function void initialize();
        // To be overriden
        assert(0);
    endfunction : initialize

    /* Function: allocate

        Allocate from pool

        Returns:
            Pool element class

    */
    virtual function T allocate();
        T retVal;

        case(policy)
            ALLOCATE_FRONT  : retVal = available.pop_front();
            ALLOCATE_BACK   : retVal = available.pop_back();
            ALLOCATE_RANDOM :
            begin
                int idx;
                idx    = $urandom_range(available.size()-1);
                retVal = available[idx];
                available.delete(idx);
            end
            default         : assert(0);
        endcase

        reserved.push_back(retVal);
        return retVal;
    endfunction : allocate

   /* Function:  Free

        Return to Pool

    */
    virtual function void free(T t);
        T   val;
        int idx = -1;
        for (int i = 0; i < reserved.size(); i++) begin
            if (t == reserved[i]) begin
                idx = i;
            end
        end

        if (idx == -1) assert(0);
        else           reserved.delete(idx);

        available.push_back(t);
    endfunction : free
endclass : axe_uvm_resource_allocator
