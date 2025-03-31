//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_page_match_test.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_page_match_test
//Parent			: lpddr_subsystem_base_test
//Description	:
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_page_match_test extends lpddr_subsystem_base_test;
	`uvm_component_utils(lpddr_subsystem_page_match_test)

	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name,parent
	//Description	: overriding class constructor
	//-------------------------------------------------------------------------------------------	
	function new(string name ="lpddr_subsystem_page_match_test",uvm_component parent=null);
		super.new(name,parent);
	endfunction: new

	//-------------------------------------------------------------------------------------------
	//Method 			: build_phase
	//Arguement		: phase
	//Description	: sets the default sequence for page match test 
	//-------------------------------------------------------------------------------------------	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
   	uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_page_match_test_seq::type_id::get());
	endfunction: build_phase

endclass: lpddr_subsystem_page_match_test
