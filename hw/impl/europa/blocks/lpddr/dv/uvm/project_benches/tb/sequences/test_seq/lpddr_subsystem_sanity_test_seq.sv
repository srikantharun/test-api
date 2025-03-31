//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_sanity_test_seq.sv
// Unit Name   : lpddr_subsystem_sanity_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_subsystem_sanity_test_seq
//--------------------------------------------------------------------------------------

class lpddr_subsystem_sanity_test_seq extends lpddr_subsystem_base_virtual_seq ;

  `uvm_object_utils(lpddr_subsystem_sanity_test_seq)

  function new ( string name = "lpddr_subsystem_sanity_test_seq");
    super.new(name);
  endfunction : new

  virtual task body();
  endtask

endclass
