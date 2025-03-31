//
// File: lpddr_subsystem_sanity_test.svh
// pcie_subsystem_base_test
// Generated from Questa VIP Configurator (20240520)
// Generated using Questa VIP Library ( 2024.2 : 05/29/2024:10:31 )
//
class lpddr_subsystem_sanity_test extends lpddr_subsystem_base_test;

  `uvm_component_utils(lpddr_subsystem_sanity_test)

  function new ( string name = "lpddr_subsystem_sanity_test", uvm_component parent = null);
    super.new(name, parent);
  endfunction

  function void build_phase ( uvm_phase phase);
    super.build_phase( phase );
    uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_sanity_test_seq::type_id::get());
  endfunction: build_phase

endclass: lpddr_subsystem_sanity_test
