/**
* Same steps and interation as ai_core_dwpu_standard_test
* but set the max_iter variable to 50 instead of 10 to make sure more test scenarios occur
*/
class ai_core_dwpu_extensive_standard_test extends ai_core_dwpu_standard_test;

  /** UVM Component Utility macro */
  `uvm_component_utils (ai_core_dwpu_extensive_standard_test)

  /** Class Constructor */
  function new (string name, uvm_component parent);
    super.new (name, parent);
    /** Set the value of max_iter to 50 to make sure that randomization gets more scenarios */
    max_iter=50;
  endfunction : new

endclass : ai_core_dwpu_extensive_standard_test

