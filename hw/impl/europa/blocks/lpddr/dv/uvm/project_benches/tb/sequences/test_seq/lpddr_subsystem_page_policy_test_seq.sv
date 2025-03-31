//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_page_policy_test_seq.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : generates stimuli for verifying page policy feature
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
//Class 			:	lpddr_subsystem_page_policy_test_seq
//Parent			: lpddr_subsystem_base_virtual_seq
//Description	:
//-------------------------------------------------------------------------------------------	
// FIXME Kunal: remove KUNNU'S from infos	
// FIXME Kunal: remove debug infos(UVM_LOW)
class lpddr_subsystem_page_policy_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_page_policy_test_seq)

	// transactions 
	axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;

	int no_of_iter=10;

	int scn;
	int test_scenario;

	// status for register writes
	uvm_status_e reg_status;

	// reg fields
	rand bit rand_pageclose;
	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name 
	//Description	: class constructor 
	//-------------------------------------------------------------------------------------------	
	function new(string name = "lpddr_subsystem_page_policy_test_seq");
		super.new(name);
		test_scenario = ($value$plusargs("TEST_SCENARIO=%d",scn));
	endfunction: new 

	//-------------------------------------------------------------------------------------------
	//Method 			: body
	//Arguement		: NONE
	//Description	: generates axi input transactions and configure the registers
	//							responsible for page policy feature
	//-------------------------------------------------------------------------------------------	
	virtual task body;
// TODO Kunal: remove;		
		`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("sequence started"), UVM_LOW)
		case (test_scenario)
		0 : begin 
					//------------------------------------------------------------------------------
					// Scenario			: 0
					// Description	: this scenario sends axi traffic after disabling
					// 								the page close feature. 
					//------------------------------------------------------------------------------
// TODO Kunal: add; dynamic resets for changing static registers
					`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("scenario 0 started | no_of_iter: %0d",no_of_iter), UVM_LOW)	
					repeat(no_of_iter) 
						begin
							// generating the axi packets 
							axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");
							axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");
			
							//page_close: 0
							//reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0,'{'{"pageclose",1'b0}}));
							// randomizing the packets 
// FIXME Kunal: change the transaction  constraints for different page addresses// 
							assert(axi_rd_xtnh.randomize with {	read_or_write == AXI4_TRANS_READ;})
								else `uvm_error("PAGE_POLICY_SEQ","read transaction randomization failed")
						
							assert(axi_wr_xtnh.randomize with {	read_or_write == AXI4_TRANS_WRITE;})
								else `uvm_error("PAGE_POLICY_SEQ","write transaction randomization failed")

							// disabling schedular traffic 
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
							p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();
							p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();

							repeat(no_of_iter)
// FIXME Kunal: will `uvm_do re-create the packets?  					
								fork 
									begin: wr_xtn_pc_0
										`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	
			  						p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtnh);
									end //wr_xtn_pc_0
									begin: rd_xtn
										`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
										p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);
									end //rd_xtn

							// enabling schedular traffic 
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();

								join //repeat
						end //repeat
				end //case_statement_0
// TODO Kunal: remove;	
/*
		1 : begin 
					//------------------------------------------------------------------------------
					// Scenario			: 1
					// Description	: this scenario sends axi traffic after enabling
					// 								the page close feature. 
					//------------------------------------------------------------------------------
					`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("scenario 0 started | no_of_iter: %0d",no_of_iter), UVM_LOW)	
					repeat(no_of_iter) 
						begin
							// generating the axi packets 
// TODO Kunal: randomize the transactions 				
			
							//page_close: 1
							reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0,'{'{"pageclose",1'b1}}));
						
							// disabling schedular traffic 
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
							p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();
							p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();
						
							// pageclose_timer_zero
							repeat(no_of_iter)
								begin: pc_time_0
									reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0,'{'{"pageclose_timer",'0}}));
// FIXME Kunal: will `uvm_do re-create the packets?  					
									send_read_write_pkt(); 
								end //repeat
							// pageclose_timer_NON_zero
repeat(no_of_iter)
		begin: pc_time_non_0
									reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0,'{'{"pageclose_timer",$urandom_range(1,255)}}));
// FIXME Kunal: will `uvm_do re-create the packets?  					
									send_read_write_pkt(); 
								end //repeat
							
							// enabling schedular traffic 
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();
							p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();

						end //repeat
				end //case_statement_0
*/
		endcase
	endtask: body

	//-------------------------------------------------------------------------------------------
	//Method 			: configure_static_reg_during_reset
	//Arguement		: NONE
	//Description	: overriding the method in base to write register static
	//							registers in reset 
	//-------------------------------------------------------------------------------------------	
	virtual task configure_static_reg_during_reset();
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0,'{'{"pageclose",$urandom_range(0,1)}}));
		if(rand_pageclose)
			begin 
				reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0,'{'{"pageclose_timer",'0}}));
				reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0,'{'{"pageclose_timer",$urandom_range(1,255)}}));
			end 
	endtask:configure_static_reg_during_reset

	//-------------------------------------------------------------------------------------------
	//Method 			: send_read_write_pkt
	//Arguement		: NONE
	//Description	: sends read and write packets parallely 
	//-------------------------------------------------------------------------------------------	
// FIXME Kunal: drive the incremental burst(same page address)? 
	task send_read_write_pkt;
		fork 
			begin: wr_xtn

				axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");

				assert(axi_wr_xtnh.randomize with {read_or_write == AXI4_TRANS_WRITE;})
					else `uvm_error("PAGE_POLICY_SEQ","write transaction randomization failed")

				`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	
				p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtnh);

			end //wr_xtn

			begin: rd_xtn 
				axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");
				
				assert(axi_rd_xtnh.randomize with {read_or_write == AXI4_TRANS_READ;})
					else `uvm_error("PAGE_POLICY_SEQ","read transaction randomization failed")

				`uvm_info("KUNNU'S>> PAGE_POLICY_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
				p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);

			end //rd_xtn
		join 
	endtask: send_read_write_pkt
endclass: lpddr_subsystem_page_policy_test_seq
