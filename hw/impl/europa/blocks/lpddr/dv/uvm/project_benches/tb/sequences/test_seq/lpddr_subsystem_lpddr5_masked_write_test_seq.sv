//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_lpddr5_masked_write_test_seq.sv
// Unit Name   : lpddr_subsystem_lpddr5_masked_write_test
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------
// Class 				: lpddr_subsystem_lpddr5_masked_write_test_seq
// Parent				: lpddr_subsystem_base_virtual_seq
// Description	: 
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_lpddr5_masked_write_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_lpddr5_masked_write_test_seq)

	int no_of_iter=10;	// no of iterations for body method 

	uvm_status_e reg_status; 

	bit rand_lp_optimized_write;
	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name 
	//Description	: overriding class constructor 
	//-------------------------------------------------------------------------------------------	
	function new (string name="lpddr_subsystem_lpddr5_masked_write_test_seq");
		super.new(name);
		set_automatic_phase_objection(1);
	endfunction:new
	
	//-------------------------------------------------------------------------------------------
	//Method 			: body 
	//Arguement		: NONE
	//Description	: 
	//-------------------------------------------------------------------------------------------	
// FIXME Kunal: take care of the traffic (send using schedular(inser delay to reflect) or send custom packets)
	virtual task body;
		super.body();
		//
		// disabling schedular traffic 
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();

		rand_lp_optimized_write=$urandom; 

/*
		`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DFIMISC | field: lp_optimized_write | value: %0b",rand_lp_optimized_write),UVM_HIGH)	
// TODO Kunal: modify; DBIMISC is a quasi-dyn group 3 reg. Implement that logic 
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"lp_optimized_write",rand_lp_optimized_write}})); 

		if(reg_status == UVM_NOT_OK)
			`uvm_fatal("MASKED_WRITE_SEQ","can't write reg field DFIMISC.lp_optimized_write")

		if(rand_lp_optimized_write)
			begin 
// TODO Kunal: modify;	wr_dbi_en is quasi-dyn group 1 field. 
				`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DBICTL | field: wr_dbi_en | value: 1"),UVM_HIGH)	
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"wr_dbi_en",1'b1}}));
// TODO Kunal: modify;	dbi_en is a staic field 				
				`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DBICTL | field: dm_en | value: 1"),UVM_HIGH)	
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",1'b1}}));
				`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DFIMISC | field: phy_dbi_mode | value: 0"),UVM_HIGH)	
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"phy_dbi_mode",1'b0}})); 
			end 
*/

		`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DFIMISC | field: lp_optimized_write | value: %0b",rand_lp_optimized_write),UVM_HIGH)	
		write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"lp_optimized_write",rand_lp_optimized_write}});

		if(rand_lp_optimized_write)
			begin 
// TODO Kunal: modify;	wr_dbi_en is quasi-dyn group 1 field. 
				`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DBICTL | field: wr_dbi_en | value: 1"),UVM_HIGH)	
				write_qd_reg(QD_GROUP_1,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"wr_dbi_en",1'b1}});
				`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DFIMISC | field: phy_dbi_mode | value: 0"),UVM_HIGH)	
				write_qd_reg(QD_GROUP_1,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"phy_dbi_mode",1'b0}});
			end 
		// enabling schedular traffic 
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_axi_scheduler();

	endtask:body

	//-------------------------------------------------------------------------------------------
	//Method 			: configure_static_reg_during_reset
	//Arguement		: NONE
	//Description	: overriding the method present in base class to write static
	//							registers during reset 
	//-------------------------------------------------------------------------------------------	
// FIXME Kunal: this should'nt work as DBICTL is a static reg which depends
// 							upon the qd group 1 reg as this works before run, 
// 							Possible correction: make this field 1 irrespective of the qd
// 							group 1 reg
	virtual task configure_static_reg_during_reset();
		if(rand_lp_optimized_write)
			begin 
				`uvm_info("KUNNU'S>> MASKED_WRITE_SEQ",$sformatf("reg: DBICTL | field: dm_en | value: 1"),UVM_HIGH)	
				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",1'b1}}));
			end 
	endtask:configure_static_reg_during_reset

endclass:lpddr_subsystem_lpddr5_masked_write_test_seq
