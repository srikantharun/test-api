//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_page_policy_test.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_page_policy_test
//Parent			: lpddr_subsystem_base_test
//Description	: starts the sequence for page policy feature
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_page_policy_test extends lpddr_subsystem_base_test;
	`uvm_component_utils(lpddr_subsystem_page_policy_test)

	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name,parent
	//Description	:
	//-------------------------------------------------------------------------------------------	
	function new(string name="lpddr_subsystem_page_policy_test",uvm_component parent=null);
		super.new(name,parent);
	endfunction: new


	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
    uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_page_policy_test_seq::type_id::get());
	endfunction: build_phase

endclass: lpddr_subsystem_page_policy_test

