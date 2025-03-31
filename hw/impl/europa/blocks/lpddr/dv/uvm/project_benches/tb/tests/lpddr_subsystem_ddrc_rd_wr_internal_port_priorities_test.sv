//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test.sv
// Unit Name   : lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test
//Parent			: lpddr_subsystem_base_test
//Description	: 
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test extends lpddr_subsystem_base_test;	
	`uvm_component_utils(lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test)

		//-------------------------------------------------------------------------------------------
		//Method 			: new 
		//Arguement		: name,parent
		//Description	: 
		//-------------------------------------------------------------------------------------------	
		function new(string name, uvm_component parent);
			super.new(name,parent);
		endfunction: new 

		//-------------------------------------------------------------------------------------------
		//Method 			: build_phase
		//Arguement		: phase
		//Description	: sets the masked write seq as default seq
		//-------------------------------------------------------------------------------------------	
		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
    	uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq::type_id::get());
		endfunction: build_phase

endclass:lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test
