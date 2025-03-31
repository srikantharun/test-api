// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style incrementor 
// Simple atomic update of shared value - bitshift
// Owner: abond

// Class : axe_uvm_incrementor
class axe_uvm_bitwise_incrementor #(type T=int) extends axe_uvm_incrementor;

    typedef axe_uvm_bitwise_incrementor #(T) this_t;

    `uvm_component_param_utils(this_t)

    /* Function: new 

       Constructor

       Parameters:

          name - Name of the incrementor class
          parent - Parent class

       Returns:

          Instance axe_uvm_incrementor
    */
    function new (string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    /* Function: next

       Get next value in sequence

       Returns:

          Next value
    */
    virtual function T next();
        T retVal = value;
        value <<= stride;
        return retVal;
    endfunction : next

endclass : axe_uvm_bitwise_incrementor
