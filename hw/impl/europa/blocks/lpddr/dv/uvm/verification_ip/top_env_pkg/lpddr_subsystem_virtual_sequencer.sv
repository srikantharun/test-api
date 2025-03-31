// --------------------------------------------------------------------------------------
// File name   : lpddr_subsystem_virtual_sequencer 
// Description : This virtual sequencer is coordinates with other sequencer
//               (axi, apb, lpddr sequencers ) and start the sequences. 
// --------------------------------------------------------------------------------------
//typedef class lpddr_subsystem_environment;
//typedef class lpddr_subsystem_axi_scheduler_seq;

class lpddr_subsystem_virtual_sequencer extends uvm_sequencer;
  
	`uvm_component_param_utils(lpddr_subsystem_virtual_sequencer)

//	lpddr_subsystem_environment env;

	//decler sequencer 
	mvc_sequencer apb0_sqr;
	mvc_sequencer apb1_sqr;
  mvc_sequencer axi_sqr;
  //mvc_sequencer axi4_master_0_sqr;
  string UNIQUE_ID = "";
	//sequence 
	lpddr_subsystem_axi_scheduler_seq axi_lpddr_scheduler_seq_inst;

	// new function 
	function new(string name = "lpddr_subsystem_virtual_sequencer", uvm_component parent);
	  super.new(name, parent);
	endfunction : new

	//--------------------------------------------------------------------------------------
  // Task        : build_phase
  // Description : this phase in which all the class objects are constructed
  //--------------------------------------------------------------------------------------
	virtual function void build_phase (uvm_phase phase);
	  super.build_phase(phase);
    axi_lpddr_scheduler_seq_inst = lpddr_subsystem_axi_scheduler_seq::type_id::create("axi_lpddr_scheduler_seq_inst");
	endfunction : build_phase 


	function void end_of_elaboration_phase ( uvm_phase phase);
super.end_of_elaboration_phase(phase);

    if(!uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,{UNIQUE_ID,"apb_master_0"},apb0_sqr))
	    `uvm_error("MVC_SEQUENCER","Not found sequence apb_master_0")
    if(!uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,{UNIQUE_ID,"apb_master_1"},apb1_sqr))
	    `uvm_error("MVC_SEQUENCER","Not found sequence apb_master_1")
    if(!uvm_config_db #(mvc_sequencer)::get(null,UVMF_SEQUENCERS,{UNIQUE_ID,"axi4_master_0"},axi_sqr))
	    `uvm_error("MVC_SEQUENCER","Not found sequence axi4_master_0")

endfunction : end_of_elaboration_phase 

	//--------------------------------------------------------------------------------------
  // Task        : run_phase
  // Description : this method vall the run_phase method of parent 
  //--------------------------------------------------------------------------------------
	task run_phase (uvm_phase phase);
		super.run_phase(phase);
	  fork 
	    axi_lpddr_scheduler_start();
		 join_none
	endtask : run_phase

  
	//--------------------------------------------------------------------------------------
  // Task        : axi_lpddr_scheduler_start
  // Description : start axi scheduler sequence
  //--------------------------------------------------------------------------------------
  virtual task axi_lpddr_scheduler_start ();
	  axi_lpddr_scheduler_seq_inst.start(this);
  endtask : axi_lpddr_scheduler_start

endclass : lpddr_subsystem_virtual_sequencer

