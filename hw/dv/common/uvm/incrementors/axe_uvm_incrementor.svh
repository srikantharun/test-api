// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// UVM Style incrementor 
// Simple atomic update of shared value
// Owner: abond

// Class : axe_uvm_incrementor
class axe_uvm_incrementor #(type T=int) extends uvm_component;

    typedef axe_uvm_incrementor #(T) this_t;

    T value;
    T stride;

    `uvm_component_param_utils_begin(this_t)
        `uvm_field_int(value,  UVM_DEFAULT)
        `uvm_field_int(stride, UVM_DEFAULT)
    `uvm_component_utils_end

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

    /* Function: head

       Get head of sequence

       Returns:

         value
    */
    virtual function T head();
        return value;
    endfunction : head

    /* Function: next

       Get next value in sequence

       Returns:

          Next value
    */
    virtual function T next();
        T retVal = value;
        value += stride;
        return retVal;
    endfunction : next

endclass : axe_uvm_incrementor
