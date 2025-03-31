//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------

//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq
//Parent			: lpddr_subsystem_base_virtual_seq
//Description	:
//-------------------------------------------------------------------------------------------	

class lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq)

	// general packet
	axi_trans_t axi_xtnh;
	// dedicated packets for write and read
	axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;

	// status for register writes
	uvm_status_e reg_status;

	int scn;
	int no_of_iter= 10; 

	rand bit rand_dis_wc;
	rand bit rand_wr_link_ecc_enable;
	//-------------------------------------------------------------------------------------------
	//Method 			: new 							
	//Arguement		: name,parent 
	//Description	: 						
	//-------------------------------------------------------------------------------------------
	function new(string name="lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq");	
	  super.new(name);
	endfunction: new 																

	virtual task body();
// TODO Kunal: remove;		
		`uvm_info("KUNNU'S>> ADDR_COLL_SEQ",$sformatf("sequence started | scenario: %0d",scn), UVM_LOW)	
		super.body();
		// disabling schedular traffic
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();
		case (test_scenario)
		1 : begin 
				//------------------------------------------------------------------------------
				// Scenario			: 1
				// Description	: covers the back to back reads and writes randomly 
				//------------------------------------------------------------------------------
				// random rd/wr after random rd/wr
// TODO Kunal: remove;		
					`uvm_info("KUNNU'S>> ADDR_COLL_SEQ",$sformatf("scenario 0 started | no_of_iter: %0d",no_of_iter), UVM_LOW)	
// TODO Kunal: add; reset the dut to configure static reg
					repeat(no_of_iter)
						begin 
							// back to back read/write randomly 
							back_2_back();
						end //repeat
				end // case_statement_1
		2 : begin 
				//------------------------------------------------------------------------------
				// Scenario			: 2
				// Description	: covers the back to back writes at the same address
				// 								with write combine enabled and disabled 
				//------------------------------------------------------------------------------
					`uvm_info("KUNNU'S>> ADDR_COLL_SEQ",$sformatf("scenario 1 started | no_of_iter: %0d",no_of_iter), UVM_LOW)	
					repeat(no_of_iter)
						begin
// TODO Kunal: add; reset the dut to configure static reg
							if(!rand_dis_wc)	
								begin: wc_off
									back_2_back(AXI4_TRANS_WRITE,AXI4_TRANS_WRITE);
								end 
							else	
								begin: wc_on
									back_2_back(AXI4_TRANS_WRITE,AXI4_TRANS_WRITE);
								end 
						end //repeat
				end // case_statement_1
		3 : begin
				//------------------------------------------------------------------------------
				// Scenario			: 3
				// Description	: RMW scenario
				//------------------------------------------------------------------------------
// TODO Kunal: modify? will require sequencer arbitration? make it sequential
					repeat(no_of_iter)
						fork 
							begin:rmw_after_read
								axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");
								assert(axi_rd_xtnh.randomize with {read_or_write == AXI4_TRANS_READ;})
									else `uvm_error("ADDR_COLL_TEST","Randomization failed for axi_rd_xtnh")

								p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);
										`uvm_info("ADDR_COLL_TEST",$sformatf("Queued transaction sent to driver: read \n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
								//rmw transaction
								drive_rmw_cmd();
							end //rmw_after_read

							begin:rmw_after_write
								axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");
								assert(axi_wr_xtnh.randomize with {read_or_write == AXI4_TRANS_WRITE;})
									else `uvm_error("ADDR_COLL_TEST","Randomization failed for axi_wr_xtnh")

								p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_wr_xtnh);
										`uvm_info("ADDR_COLL_TEST",$sformatf("Queued transaction sent to driver: write \n%s",axi_wr_xtnh.sprint), UVM_HIGH)	

								//rmw transaction
								drive_rmw_cmd();
							end //rmw_after_write

							begin:write_after_rmw 
								//rmw transaction
								drive_rmw_cmd();

								axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");
								assert(axi_wr_xtnh.randomize with {read_or_write == AXI4_TRANS_WRITE;})
									else `uvm_error("ADDR_COLL_TEST","Randomization failed for axi_wr_xtnh")

								p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_wr_xtnh);
										`uvm_info("ADDR_COLL_TEST",$sformatf("Queued transaction sent to driver: write \n%s",axi_wr_xtnh.sprint), UVM_HIGH)	
							end //write_after_rmw
						join 
				end // case_statement_3
// TODO Kunal: remove;	scenario				
		4 : begin  
				//------------------------------------------------------------------------------
				// Scenario			: 2
				// Description	: new read/write colliding with both read and write
				//------------------------------------------------------------------------------
				repeat(no_of_iter)	
					begin 
// TODO Kunal: add; manipulate reg ECCCFG0.ecc_mode=3'b100 for turning on RMW transs
							`uvm_do_on_with(axi_xtnh, p_sequencer.axi_sqr, {	addr 					== $urandom;
																																//burst_length 	== 0;		// one transfer 
																																lock 					== AXI4_NORMAL;})

							`uvm_do_on_with(axi_xtnh, p_sequencer.axi_sqr, {	read_or_write ==AXI4_TRANS_READ; 
																																addr 					== $urandom;
																																//burst_length 	== 0;		// one transfer 
																																lock 					== AXI4_NORMAL;})

							`uvm_do_on_with(axi_xtnh, p_sequencer.axi_sqr, {	read_or_write ==AXI4_TRANS_WRITE; 
																																addr 					== $urandom;
																																//burst_length 	== 0;		// one transfer 
																																lock 					== AXI4_NORMAL;})
					end // repeat
				end // case_stateement_2
		endcase // case_scenario
		// enabling schedular traffic
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_axi_scheduler();
		#(50 *1ns);
	endtask: body 
	
	//-------------------------------------------------------------------------------------------
	//Method 			: configure_static_reg_during_reset
	//Arguement		: NONE
	//Description	: overriding the method present in base class to write static
	//							registers during reset 
	//-------------------------------------------------------------------------------------------	
	virtual task configure_static_reg_during_reset();
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL0.write(	reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL0,'{'{"dis_wc",rand_dis_wc}}));
// TODO Kunal: modify;	uvm_fatal to uvm_error 		
		if(reg_status == UVM_NOT_OK)
			`uvm_fatal("ADDR_COLL_SEQ","can't write register OPCTRL0.dis_wc")
		reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.LNKECCCTL0.write(	reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.LNKECCCTL0,'{'{"wr_link_ecc_enable",rand_wr_link_ecc_enable}}));
// TODO Kunal: modify;	uvm_fatal to uvm_error 		
		if(reg_status == UVM_NOT_OK)
			`uvm_fatal("ADDR_COLL_SEQ","can't write register LNKECCCTL0.wr_link_ecc_enable")

		// registers for rmw generation. ref: DWC_ddrctl_lpddr54_lpddr5x_databook.pdf 3.1.1.3.1
		// setting ecc mode to 3'b100
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ECCCFG0.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ECCCFG0,'{'{"ecc_mode",3'b100}}));
		// disable data mask
		reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL,'{'{"dm_en",1'b0}}));

	endtask:configure_static_reg_during_reset

	//-------------------------------------------------------------------------------------------
// TODO Kunal: modify; name of the method 
	//Method 			: back_2_back_commands
	//Arguement		: first_cmd: axi read/write at queued position 
	//							sec_cmd: axi read/write at new position 
	//Description	: drives back to back read/write commands to the design 
	//							at random address locations 
	//-------------------------------------------------------------------------------------------
	virtual task back_2_back(axi4_rw_e first_cmd=$urandom_range(0,1),sec_cmd=$urandom_range(0,1));
		bit [32:0] tmp_addr=$urandom_range(1,'1);
		axi_trans_t axi_trans;

		axi_trans=axi_trans_t::type_id::create("axi_trans");
		assert(axi_trans.randomize with {	read_or_write == first_cmd; 
																			addr 					== tmp_addr;
																			lock 					== AXI4_NORMAL;})
			else `uvm_error("ADDR_COLL_TEST","Randomization failed for axi_trans")

		if(first_cmd==AXI4_TRANS_WRITE)
			begin 
				p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_trans);
				`uvm_info("ADDR_COLL_TEST",$sformatf("Queued transaction sent to driver: write \n%s",axi_trans.sprint), UVM_HIGH)	
			end 	

		if(first_cmd==AXI4_TRANS_READ)
			begin 
				p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_trans);
				`uvm_info("ADDR_COLL_TEST",$sformatf("Queued transaction sent to driver: read \n%s",axi_trans.sprint), UVM_HIGH)	
			end 	

		#($urandom_range(1,10) * 1ns);

// TODO Kunal: modify? change the one axi_trans to 2 different axi_transactions 
		assert(axi_trans.randomize with {	read_or_write == sec_cmd;
																			addr 					== tmp_addr;
																			burst_length 	== axi_trans.burst_length;
																			size 					== axi_trans.size; 	
																			burst 				== axi_trans.burst; 
																			lock 					== axi_trans.lock;})
			else `uvm_error("ADDR_COLL_TEST","Randomization failed for axi_trans")

		if(sec_cmd==AXI4_TRANS_WRITE)
			begin 
				p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_trans);
				`uvm_info("ADDR_COLL_TEST",$sformatf("New transaction sent to driver: write \n%s",axi_trans.sprint), UVM_HIGH)	
			end 	

		if(sec_cmd==AXI4_TRANS_READ)
			begin 
				p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_trans);
				`uvm_info("ADDR_COLL_TEST",$sformatf("New transaction sent to driver: write \n%s",axi_trans.sprint), UVM_HIGH)	
			end 	
	endtask:back_2_back

	//-------------------------------------------------------------------------------------------
	//Method 			: drive_rmw_cmd
	//Arguement		: NONE
	//Description	: sends a rmw transactio to axi seqr 
	//-------------------------------------------------------------------------------------------	
	virtual task drive_rmw_cmd();
		axi_trans_t axi_trans_rmw;

		axi_trans_rmw=axi_trans_t::type_id::create("axi_trans_rmw");
		axi_trans_rmw.write_data_words.constraint_mode(0);
		assert(axi_trans_rmw.randomize with {	read_or_write == AXI4_TRANS_WRITE;
	                                       	burst_length 	== 15;
	                                       	//size 					== axi_trans.size; 	
	                                       	burst 				== AXI4_WRAP;
	                                       	wdata_words.size < burst_length;		// necessary for rmw 
																				})
			else `uvm_error("ADDR_COLL_TEST","can't randomize rmw transaction")

		p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_trans_rmw);
		`uvm_info("ADDR_COLL_TEST",$sformatf("RMW transaction sent to driver \n%s",axi_trans_rmw.sprint), UVM_HIGH)	
	endtask:drive_rmw_cmd
endclass: lpddr_subsystem_addr_collision_handling_and_write_combine_test_seq
