//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_write_to_read_switching_test_seq.sv
// Unit Name   : lpddr_subsystem_write_to_read_switching_test
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_write_to_read_switching_test_seq
//Parent			: lpddr_subsystem_base_virtual_seq
//Description	:
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_write_to_read_switching_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_write_to_read_switching_test_seq)
	
	int no_of_iter=10;	// no of iterations for body method 
	uvm_status_e reg_status; 
	// packets
	axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;

	// reg_field_variables
	// PCFGQOS0
	bit [31:24] rand_rqos_map_region2;
	bit [23:20] rand_rqos_map_region1; 
	bit [19:16] rand_rqos_map_region0;
	bit [15:8] 	rand_rqos_map_level2;
	bit [7:0] 	rand_rqos_map_level1;

	// PCFGWQOS rand_
	rand bit [31:24]	rand_wqos_map_region2;
	rand bit [23:20]	rand_wqos_map_region1;
	rand bit [19:16]	rand_wqos_map_region0;
	rand bit [15:8] 	rand_wqos_map_level2;
	rand bit [7:0]  	rand_wqos_map_level1;
			
	// PCFGQOS1
	rand bit [31:16] 	rand_rqos_map_timeoutr;
	rand bit [15:0] 	rand_rqos_map_timeoutb;
	
	// PCFGWQOS1rand_
	rand bit [31:16] 	rand_wqos_map_timeout2;
	rand bit [15:0] 	rand_wqos_map_timeout1;
	
	// SCHED4
	rand bit [31:24] 	rand_wr_page_exp_cycles;
	rand bit [23:16]	rand_rd_page_exp_cycles;
 	rand bit [15:8] 	rand_wr_act_idle_gap;
	rand bit [7:0] 		rand_rd_act_idle_gap;

	// SCHED3
	rand bit [15:8] rand_wrcam_highthresh;
	rand bit [7:0] 	rand_wrcam_lowthresh; 

	// Constraints for reg fields
// FIXME Kunal: map level 2 inside 0:15 or 0:14?		
	constraint con_valid_rqos_map_level { (rand_rqos_map_level1 inside {[0:14]}) -> (rand_rqos_map_level2 inside {[(rand_rqos_map_level1+1):15]});
																					solve rand_rqos_map_level1 before rand_rqos_map_level2;}

	constraint con_valid_rqos_map_region {rand_rqos_map_region0 inside {[0:2]};
																				rand_rqos_map_region1 inside {[0:2]};
																				rand_rqos_map_region2 inside {[1:2]};}

	constraint con_valid_wqos_map_level {(rand_wqos_map_level1 inside {[0:13]}) -> rand_wqos_map_level2 inside {[(rand_wqos_map_level1+1):14]};
																					solve rand_wqos_map_level1 before rand_wqos_map_level2;}

	constraint con_valid_wqos_map_region {rand_wqos_map_region0 inside {[1:2]};
                                        rand_wqos_map_region1 inside {[0:1]};
                                        rand_wqos_map_region2 inside {[0:1]};}

	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name 
	//Description	: overriding class constructor 
	//-------------------------------------------------------------------------------------------	
	function new(string name="lpddr_subsystem_write_to_read_switching_test_seq");
		super.new(name);
		//automatically raise and drop objections before and after the body subroutine
		set_automatic_phase_objection(1);
	endfunction: new

	//-------------------------------------------------------------------------------------------
	//Method 			:	body 
	//Arguement		: NONE
	//Description	:
	//-------------------------------------------------------------------------------------------	
	virtual task body();
		super.body();
// TODO Kunal: remove? add after the reg configs 
		dis_schedular_traffic();
		repeat(no_of_iter)
			begin 
				// PCFGQOS0 configuration 
// FIXME Kunal:whats RAQ? for rqos_map_level_1				
// FIXME Kunal: write consttraint for the values of this register (esp for X) 
				`uvm_info("KUNNU'S>> SEQ_NOT_RUNNING",$sformatf("in body of seq; before reg configs"), UVM_LOW)	
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS0,'{'{"rqos_map_level1",rand_rqos_map_level1}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS0,'{'{"rqos_map_level2",rand_rqos_map_level2}}); 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS0,'{'{"rqos_map_region0",rand_rqos_map_region0}}); 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS0,'{'{"rqos_map_region1",rand_rqos_map_region1}}); 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS0,'{'{"rqos_map_region2",rand_rqos_map_region2}}); 
				`uvm_info("KUNNU'S>> SEQ_NOT_RUNNING",$sformatf("in body of seq; before reg configs"), UVM_LOW)	
				// PCFGWQOS0 configurations 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS0,'{'{"wqos_map_level1",rand_wqos_map_level1}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS0,'{'{"wqos_map_level2",rand_wqos_map_level2}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS0,'{'{"wqos_map_region0",rand_wqos_map_region0}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS0,'{'{"wqos_map_region1",rand_wqos_map_region1}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS0,'{'{"wqos_map_region2",rand_wqos_map_region2}});

				// PCFGQOS1 configurations 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS1,'{'{"rqos_map_timeoutb",rand_rqos_map_timeoutb}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS1,'{'{"rqos_map_timeoutr",rand_rqos_map_timeoutr}});
				
				// PCFGWQOS1 configurations 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS1,'{'{"wqos_map_timeout1",rand_wqos_map_timeout1}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS1,'{'{"wqos_map_timeout2",rand_wqos_map_timeout2}});

// TODO Kunal: add;					// rd_act_idle_gap and wr_act_idle_gap to 0 and non zero values ?? 
// TODO Kunal: add;	
				// SCHED4
				//DWC_ddrctl_map_REGB_DDRC_CH0
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED4,'{'{"rd_act_idle_gap",rand_rd_act_idle_gap}}); //TODO: make dist constraint  
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED4,'{'{"wr_act_idle_gap",rand_wr_act_idle_gap}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED4,'{'{"wr_page_exp_cycles",rand_wr_page_exp_cycles}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED4,'{'{"rd_page_exp_cycles",rand_rd_page_exp_cycles}});

				// SCHED3
// TODO Kunal: modify;	 
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED3,'{'{"wrcam_highthresh",rand_wrcam_highthresh}});
				write_qd_reg(QD_GROUP_3,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED3,'{'{"wrcam_lowthresh",rand_wrcam_lowthresh}});

// FIXME Kunal: the below thread  				
				`uvm_info("KUNNU'S>> SEQ_NOT_RUNNING",$sformatf("in body of seq; before traffic"), UVM_LOW)	
				fork 
					begin 
						axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");
						p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_rd_xtnh);
						`uvm_info("KUNNU'S>> WR_TO_RD_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
					end 
					begin 
						axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");
						p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_wr_xtnh);
						`uvm_info("KUNNU'S>> WR_TO_RD_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	
					end 
				join 

			end //repeat

		en_schedular_traffic();
	endtask:body

	//-------------------------------------------------------------------------------------------
	//Method 			: dis_schedular_traffic
	//Arguement		: NONE
	//Description	: disables the axi schedular and enables the user to send 
	//							date packets 
	//-------------------------------------------------------------------------------------------	
// FIXME Kunal: should include the following method in base_class?  
	virtual function void dis_schedular_traffic;
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();
	endfunction: dis_schedular_traffic

	//-------------------------------------------------------------------------------------------
	//Method 			: en_schedular_traffic
	//Arguement		: NONE
	//Description	: enables the axi schedular and disables the user to send 
	//							date packets 
	//-------------------------------------------------------------------------------------------	
// FIXME Kunal: should include the following method in base_class?  
	virtual function void en_schedular_traffic;
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_axi_scheduler();
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();
	endfunction: en_schedular_traffic

endclass: lpddr_subsystem_write_to_read_switching_test_seq

