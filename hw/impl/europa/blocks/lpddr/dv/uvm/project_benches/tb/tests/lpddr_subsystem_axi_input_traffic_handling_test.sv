// TODO Kunal: modify; change the seq starting mechanism by setting  default seq 
// TODO Kunal: runcomment; the super.phases in all the phases 
//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_axi_input_traffic_handling_test.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : test for axi traffic. normal operation and errors
//------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_axi_input_traffic_handling_test
//Parent			: lpddr_subsystem_base_test
//Description	: this test starts the sequence for axi input traffic 
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_axi_input_traffic_handling_test extends lpddr_subsystem_base_test;
	`uvm_component_utils(lpddr_subsystem_axi_input_traffic_handling_test)

		lpddr_subsystem_axi_traffic_handling_test_seq seqh;

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
		//Description	:
		//-------------------------------------------------------------------------------------------	
		virtual function void build_phase(uvm_phase phase);
			super.build_phase(phase);
    	uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_axi_traffic_handling_test_seq::type_id::get());
		endfunction: build_phase

endclass: lpddr_subsystem_axi_input_traffic_handling_test
		
