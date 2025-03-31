//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_addr_collision_handling_and_write_combine_test.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
////Class 			: lpddr_subsystem_addr_collision_handling_and_write_combine_test
////Parent			: lpddr_subsystem_base_test
////Description	:
////-------------------------------------------------------------------------------------------
//clasa
class lpddr_subsystem_addr_collision_handling_and_write_combine_test extends lpddr_subsystem_base_test; 
	`uvm_component_utils(lpddr_subsystem_addr_collision_handling_and_write_combine_test)

	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name,parent
	//Description	: overriding class constructor 
	//-------------------------------------------------------------------------------------------	
	function new (string name="lpddr_subsystem_addr_collision_handling_and_write_combine_test", uvm_component parent=this);
		super.new(name,parent);
	endfunction: new
	//-------------------------------------------------------------------------------------------
	//Method 			: build_phase
	//Arguement		: phase
	//Description	: sets the default sequence for this test 
	//-------------------------------------------------------------------------------------------	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		// setting virtual sequence
		uvm_config_db#(uvm_object_wrapper)::set(this,"environment.virtual_sequencer.main_phase","default_sequence",lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq::type_id::get());
	endfunction: build_phase
	
	//-------------------------------------------------------------------------------------------
	//Method 			: run_phase
	//Arguement		: phase
	//Description	:
	//-------------------------------------------------------------------------------------------	
	virtual task run_phase(uvm_phase phase);
// TODO Kunal: remove;		
		#10 `uvm_info("KUNNU'S>> ADDR_COLL_TEST",$sformatf("inside run_phase"), UVM_LOW)	
	endtask: run_phase
endclass: lpddr_subsystem_addr_collision_handling_and_write_combine_test
