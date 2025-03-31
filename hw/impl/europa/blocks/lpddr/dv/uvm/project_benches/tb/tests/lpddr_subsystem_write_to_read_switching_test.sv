//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_write_to_read_switching_test.sv
// Unit Name   : lpddr_subsystem_write_to_read_switching_test
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_write_to_read_switching_test
//Parent			: lpddr_subsystem_base_test
//Description	: this test starts the write to read switching test seq
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_write_to_read_switching_test extends lpddr_subsystem_base_test;
	`uvm_component_utils(lpddr_subsystem_write_to_read_switching_test)

		//-------------------------------------------------------------------------------------------
		//Method 			: new 
		//Arguement		: name,parent
		//Description	: 
		//-------------------------------------------------------------------------------------------	
		function new(string name="lpddr_subsystem_write_to_read_switching_test", uvm_component parent=null);
			super.new(name,parent);
		endfunction:new 

		//-------------------------------------------------------------------------------------------
		//Method 			: build_phase
		//Arguement		: phase
		//Description	:
		//-------------------------------------------------------------------------------------------	
		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
    	uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_write_to_read_switching_test_seq::type_id::get());
		endfunction: build_phase

endclass:lpddr_subsystem_write_to_read_switching_test
