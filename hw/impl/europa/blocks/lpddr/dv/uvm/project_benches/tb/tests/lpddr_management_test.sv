class lpddr_management_test extends lpddr_subsystem_base_test;

   `uvm_component_utils(lpddr_management_test)

	 function new ( string name = "lpddr_management_test",uvm_component parent = null );
        super.new(name, parent);
    endfunction

	 function void build_phase ( uvm_phase phase);
    super.build_phase( phase );
    uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_management_test_seq::type_id::get());
  endfunction: build_phase

endclass
