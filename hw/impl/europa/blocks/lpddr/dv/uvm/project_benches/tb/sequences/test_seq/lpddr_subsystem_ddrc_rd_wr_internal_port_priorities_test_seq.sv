//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq.sv
// Unit Name   : lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq
//Parent			: lpddr_subsystem_base_virtual_seq
//Description	:
//-------------------------------------------------------------------------------------------
`ifndef	MEMC_BURST_LENGTH
	`define MEMC_BURST_LENGTH 16
`endif

`ifndef MEMC_RDCMD_ENTRY_BITS
	`define MEMC_RDCMD_ENTRY_BITS 13
`endif

class lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq)
	
	// axi pkt
	axi_trans_t axi_xtn;
	axi_trans_t axi_wr_xtn;
	axi_trans_t axi_rd_xtn;

	int no_of_iter = 10;

	uvm_status_e reg_status; 

	// reg fields
	// SCHED0
// TODO Kunal: modify; macro is undefined
	rand bit [(`MEMC_RDCMD_ENTRY_BITS+7):8]rand_lpr_num_entries;
	// PCFGR
	rand bit [9:0]rand_rd_port_priority; 
	// PCFGW
	rand bit [9:0]rand_wr_port_priority; 
	// DBICTL 
	// randc: to generate alternate values everytime
	randc bit rand_dm_en;

	// reg_field constraints 
	constraint valid_rand_rd_port_priority {rand_rd_port_priority[4:0] == '1;}
	constraint valid_rand_wr_port_priority {rand_wr_port_priority[4:0] == '1;}
	
	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name
	//Description	: overriding class constructor
	//-------------------------------------------------------------------------------------------
	function new(string name="lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq");
		super.new(name);
		set_automatic_phase_objection(1);
	endfunction:new

	//-------------------------------------------------------------------------------------------
	//Method 			: body
	//Arguement		: NONE
	//Description	: generates and sends axi packets to the axi sequencer. Also
	//							configures the registers responsible for enabling internal
	//							port priority feature
	//-------------------------------------------------------------------------------------------
	virtual task body();
		super.body();

		repeat(no_of_iter)
			begin 
				
				p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
				p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();
				p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();

				axi_xtn=axi_trans_t::type_id::create("axi_xtn");
				axi_wr_xtn=axi_trans_t::type_id::create("axi_wr_xtn");
				axi_rd_xtn=axi_trans_t::type_id::create("axi_rd_xtn");
				// partial reads and writes
				if (rand_dm_en) 
					begin: data_mask
						fork 
							begin: partial_write
								assert(axi_wr_xtn.randomize with {read_or_write 	== AXI4_TRANS_WRITE;})
									else `uvm_error("RD_WR_INT_PORT_PRIO_SEQ","Couldn't randomize axi transaction")

								p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtn);
							end //partial_write
							begin: partial_read
								assert(axi_rd_xtn.randomize with {read_or_write 	== AXI4_TRANS_READ;})
									else `uvm_error("RD_WR_INT_PORT_PRIO_SEQ","Couldn't randomize axi transaction")

								p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtn);
							end //partial_read
						join
					end //if
				else if (!rand_dm_en)	
					begin:rmw
// TODO Kunal: modify; add bur	st length constraint					
						assert(axi_xtn.randomize with {	read_or_write == AXI4_TRANS_WRITE;
// TODO Kunal: modify;																						//(addr % `MEMC_BURST_LENGTH) != 0; 
																						(addr % `MEMC_BURST_LENGTH) != 0;
																						burst_length < `MEMC_BURST_LENGTH;})
							else `uvm_error("RD_WR_INT_PORT_PRIO_SEQ","Couldn't randomize axi transaction")

						p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_xtn);
					end //else_if

				p_sequencer.axi_lpddr_scheduler_seq_inst.enable_axi_scheduler();
				p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
				p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();



			end //repeat
	endtask:body

	//-------------------------------------------------------------------------------------------
	//Method 			: configure_static_reg_during_reset
	//Arguement		: NONE
	//Description	: overriding the method present in base class to write static
	//							registers during reset 
	//-------------------------------------------------------------------------------------------	
	virtual task configure_static_reg_during_reset();
// TODO Kunal: add; field rd_port_aging_en,wr_port_aging_en?		
		`uvm_info("KUNNU'S>> RD_WR_INT_PORT_PRIO_SEQ",$sformatf("Configuring static registers"), UVM_HIGH)	

		`uvm_info("KUNNU'S>> RD_WR_INT_PORT_PRIO_SEQ",$sformatf("reg: PCFGR | field : rd_port_priority | value: %0b",rand_rd_port_priority), UVM_HIGH)	
		reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR,'{'{"rd_port_priority",rand_rd_port_priority}}));

		`uvm_info("KUNNU'S>> RD_WR_INT_PORT_PRIO_SEQ",$sformatf("reg: PCFGW | field : wr_port_priority | value: %0b",rand_wr_port_priority), UVM_HIGH)	
		reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW,'{'{"wr_port_priority",rand_wr_port_priority}}));

		`uvm_info("KUNNU'S>> RD_WR_INT_PORT_PRIO_SEQ",$sformatf("reg: DBICTL | field : dm_en | value: %0b",rand_dm_en), UVM_HIGH)	
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",rand_dm_en}}));

		`uvm_info("KUNNU'S>> RD_WR_INT_PORT_PRIO_SEQ",$sformatf("reg: SCHED0 | field : lpr_num_entries | value: %0b",rand_lpr_num_entries), UVM_HIGH)	
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0,'{'{"lpr_num_entries",rand_lpr_num_entries}}));
	endtask:configure_static_reg_during_reset
endclass: lpddr_subsystem_ddrc_rd_wr_internal_port_priorities_test_seq

