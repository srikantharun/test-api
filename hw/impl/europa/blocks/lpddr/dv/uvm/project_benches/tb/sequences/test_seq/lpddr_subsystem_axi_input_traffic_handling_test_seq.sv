// TODO Kunal: modify; make all infos UVM_HIGH
// TODO Kunal: remove; kunnu's from infos
// TODO Kunal: modify; indentation (esp in body method )
// TODO Kunal: add;	guard statements
// TODO Kunal: modify; try the atomic acess 
// TODO Kunal: modify; 	check the scenarios with fixed valid and ready delays
// 											(present in master RW transaction	)
// TODO Kunal: uncomment; credit signals 
//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : 
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------
//`ifndef MEMC_DRAM_DATA_WIDTH
//	`define MEMC_DRAM_DATA_WIDTH 32
//`endif
//`ifndef MEMC_BURST_LENGTH
//	`define MEMC_BURST_LENGTH 16
//`endif

// TODO Kunal: modify; the following macro to randomize the transactions and send to driver as well 
//-------------------------------------------------------------------------------------------
// Macro name 	: create_corrupt_packet
// Arguement 		:	PKT: Name of the err packet
// 								CON: Constraint that needs to be turned off
// description 	: creates the packet and turns the provided constraint off 
//-------------------------------------------------------------------------------------------
`define create_corrupt_packet(PKT,CON)	\
	//if(get_type_name(PKT)!=axi_trans_t)\
		//`uvm_fatal("AXI_TRAFFIC_HANDLING_SEQ","send_err_pkt : packet not of type axi4 rw");\
	PKT=axi_trans_t::type_id::create("PKT");\
	PKT.CON.constraint_mode(0);\

//-------------------------------------------------------------------------------------------
// Class 				: lpddr_subsystem_axi_traffic_handling_test_seq
// Parent				: 
// TODO Kunal: complete description 
// Description	: virtual sequence for all the sequences related to axi
// 								traffic handling test
//-------------------------------------------------------------------------------------------	
// TODO Kunal: modify; extend the class from base virtual seq
class lpddr_subsystem_axi_traffic_handling_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_axi_traffic_handling_test_seq)

	axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;

	// err packet 
	axi_trans_t axi_wr_err_pkt;
	axi_trans_t axi_rd_err_pkt;
	axi_trans_t axi_err_pkt;
	
	//-------------------------------------------------------------------------------------------
	// Method 			: new 
	// Arguement		: name
	// Description	: class constructor method
	//-------------------------------------------------------------------------------------------	
	function new (string name ="lpddr_subsystem_axi_traffic_handling_test_seq");
		super.new(name);
		set_automatic_phase_objection(1);
	endfunction: new

	//-------------------------------------------------------------------------------------------
	// Method 			: body
	// Arguement		: N/A
	// Description	: includes the packet generation, and sends it to the
	// 								axi sequencer after disabling schedular traffic
	//------------------------------------------------------------------------------------------- 	
	virtual task body();
	// TODO Kunal:remove; Debug info
// TODO Kunal: add; reset logic and initialization subroutine
// TODO Kunal: remove; the following temp vars
// NOTE Kunal:	these variables are used to create the same adresses for
// 							a write and a read xtn 
		// local vars for xtn constraints
		//bit [AXI4_ADDRESS_WIDTH-1:0] 	rand_addr; 
		//bit [7:0] 										rand_burst_len;
		//bit [3:0] 										rand_burst_size;
		super.body();
	 	$display("@%t ", $time, "kunnu's>> Start of axi input traffic seq " ,"Location: ",`__FILE__ ,"Des:");
		//super.body();
		// disabling schedular traffic
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();

		case(test_scenario)
		1 : begin 
					`uvm_info("KUNNU'S>> ",$sformatf("in scenario 1"), UVM_LOW)	
					//------------------------------------------------------------------------------
					// Scenario			: 1
					// Description	: This scenario covers all the incremental burst
					// 								related transactions. aligned and unaligned
					// 								addresses are verified. 
					//------------------------------------------------------------------------------
					
					axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");
					axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");

					// aligned addresses
					repeat(5)
						begin: aligned_addr_trans
							// write trans 
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));

							assert(axi_wr_xtnh.randomize with {	read_or_write == AXI4_TRANS_WRITE; 
																									addr % size 	== 0 ;		// address aligned to size
																									//burst_length 	== 0;	
																									//size 					== AXI4_BYTES_32; 
																									burst 				== AXI4_INCR; 
																									lock 					== AXI4_NORMAL;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","write transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtnh);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	

							// read_trans: reading the same mem locations as writing         
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));

							assert(axi_rd_xtnh.randomize with {	read_or_write == AXI4_TRANS_READ; 
																									addr 					== axi_wr_xtnh.addr; 
																									burst_length 	== axi_wr_xtnh.burst_length; 			
																									size 					== axi_wr_xtnh.size; 	
																									burst 				== AXI4_INCR; 
																									lock 					== AXI4_NORMAL;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","read transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
						end // repeat
						
					// unaligned addresses
					repeat(5)
						begin: unaligned_addr_trans
							// write trans 
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0
	
							assert(axi_wr_xtnh.randomize with {	read_or_write == AXI4_TRANS_WRITE; 
																									addr % size 	!= 0 ;		// address NOT aligned to size
																									//burst_length 	== 0;	
																									//size 					== AXI4_BYTES_32; 
																									burst 				== AXI4_INCR; 
																									lock 					== AXI4_NORMAL;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","write transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtnh);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	

							// read_trans: reading the same mem locations as writing         
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));

							assert(axi_rd_xtnh.randomize with {	read_or_write == AXI4_TRANS_READ; 
																									addr 					== axi_wr_xtnh.addr; 
																									burst_length 	== axi_wr_xtnh.burst_length; 			
																									size 					== axi_wr_xtnh.size; 	
																									burst 				== AXI4_INCR; 
																									lock 					== AXI4_NORMAL;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","read transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	

						end // repeat
				end // case_incr_1

		2 : begin 
					`uvm_info("KUNNU'S>> ",$sformatf("in scenario 2"), UVM_LOW)	
					//------------------------------------------------------------------------------
					// Scenario			: 2
					// Description	: This scenario verifies the wrap burst
					// 								transactions.
					//------------------------------------------------------------------------------

					axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");
					axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");

					repeat(10)
						begin: wrap_trans
							// write trans 
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));
	
							assert(axi_wr_xtnh.randomize with {	read_or_write == AXI4_TRANS_WRITE; 
																									//addr 				 	== $urandom ;	
																									//burst_length 	== 0;	// TODO: Kunal; Can make this more directed
																									burst 				== AXI4_WRAP; 
																									lock 					== AXI4_NORMAL;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","write transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtnh);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	

							// read_trans: reading the same mem locations as writing         
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));

							assert(axi_rd_xtnh.randomize with {	read_or_write == AXI4_TRANS_READ; 
																									addr 					== axi_wr_xtnh.addr; 
																									burst_length 	== axi_wr_xtnh.burst_length; 			
																									size 					== axi_wr_xtnh.size; 	
																									burst 				== AXI4_WRAP; 
																									lock 					== AXI4_NORMAL;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","read transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	

						end // repeat
// TODO Kunal: add;	overwriting wraps					
				end // case_wrap_2
		3 :	begin
					`uvm_info("KUNNU'S>> ",$sformatf("in scenario 3"), UVM_LOW)	
					//------------------------------------------------------------------------------
					// Scenario			: 3
					// Description	: This scenario verify all the corner cases for axi
					// 								traffic 
					//------------------------------------------------------------------------------
// TODO Kunal: add;	checksum
// TODO Kunal: add;	flow control
// TODO Kunal: add;	invalid region
					randcase
						1 : begin 
// TODO Kunal: add; err_scenario										
									//---------------------------------------------------
									// incomplete burst: 	the no_of_beats are less than 
									// 										the the burst length 
									//---------------------------------------------------
								end 
						1 : begin  
									//---------------------------------------------------
									// Burst transfer err : incremental burst
									//---------------------------------------------------

									//axi_err_pkt=axi_trans_t::type_id::create("axi_err_pkt");
									//axi_err_pkt.addr_align2.constraint_mode(0);
									// disabling 4KB boundary condition constraint 
									`create_corrupt_packet(axi_err_pkt,addr_align2)

									start_item(axi_err_pkt,,p_sequencer.axi_sqr);
									assert (axi_err_pkt.randomize with {	burst 				== AXI4_INCR;
																												// err constraint 
																												addr % 4096 + ((2 ** size) * (burst_length + 1)) > 4096;
          				                                    	lock 					== AXI4_NORMAL;})
										else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","error transaction randomization failed")

									finish_item(axi_err_pkt);
								end
						1 : begin 
									//---------------------------------------------------
									// Transfer size violation : wrap burst 
									//---------------------------------------------------
									//axi_err_pkt=axi_trans_t::type_id::create("axi_err_pkt");
									//axi_err_pkt.len_align_wrap.constraint_mode(0);
									// disabling burst length constraint for wrap burst
									`create_corrupt_packet(axi_err_pkt,len_align_wrap)
									start_item(axi_err_pkt,,p_sequencer.axi_sqr);
									assert (axi_err_pkt.randomize with {	burst 				== AXI4_WRAP;
																												// err constraint: length should not be equal to 2,4,8,16
																												!(burst_length 	inside {1,3,7,15});
          				                                    	lock 					== AXI4_NORMAL;})
										else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","error transaction randomization failed")
									finish_item(axi_err_pkt);
								end
						1 : begin
									//---------------------------------------------------
									// addressing error : wrap burst 
									//---------------------------------------------------
									//axi_err_pkt=axi_trans_t::type_id::create("axi_err_pkt");
									//axi_err_pkt.addr_align1.constraint_mode(0);
									
									// disabling start address aligning constraint for wrap burst
									`create_corrupt_packet(axi_err_pkt,addr_align1)
									start_item(axi_err_pkt,,p_sequencer.axi_sqr);
									assert (axi_err_pkt.randomize with {	burst 								== AXI4_WRAP;
																												// err constraint: address unaligned 
																												addr % ( 1 << size ) 	!= 0; 
				                                              	lock 									== AXI4_NORMAL;})
										else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","error transaction randomization failed")
									finish_item(axi_err_pkt);
								end 
					endcase
				
					//---------------------------------------------------
					// error recovery packets 
					//---------------------------------------------------
					repeat(5)
						begin 
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));
							
							axi_wr_err_pkt=axi_trans_t::type_id::create("axi_wr_err_pkt");
							axi_rd_err_pkt=axi_trans_t::type_id::create("axi_rd_err_pkt");

							assert(axi_wr_err_pkt.randomize with {read_or_write == AXI4_TRANS_WRITE;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","write transaction randomization failed")
              assert(axi_rd_err_pkt.randomize with {read_or_write == AXI4_TRANS_READ;})
								else `uvm_error("AXI_TRAFFIC_HANDLING_SEQ","read transaction randomization failed")

							p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_err_pkt);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	

							p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_err_pkt);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	

						end 
				end // case_err_3
// TODO Kunal: remove;	scenario				
		4:begin 
				axi_wr_err_pkt=axi_trans_t::type_id::create("axi_wr_err_pkt");
				axi_rd_err_pkt=axi_trans_t::type_id::create("axi_rd_err_pkt");
			// test scenario 
				 	repeat(10) 
						begin
							//write_trans
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));
	
//							`uvm_do_on_with(axi_wr_xtnh, p_sequencer.axi_sqr, {	read_or_write == AXI4_TRANS_WRITE; 
//																																	addr 					== $urandom;
//																																	burst_length 	== 0;		// one transfer 
//																																	size 					== AXI4_BYTES_32; 
//																																	burst 				== AXI4_FIXED ; 
//																																	lock 					== AXI4_NORMAL;})

							//`uvm_info("KUNNU'S >> TRIAL_SEQ",$sformatf("write transaction sent to driver"), UVM_LOW)	
							//axi_wr_xtnh.print;
							
							p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_err_pkt);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	

							// read_trans: reading the same mem locations as writing         
							// credit mechanism signals
							//wait((m_io_vif.hpr_credit_cnt > 0) || (m_io_vif.lpr_credit_cnt > 0));

//							`uvm_do_on_with(axi_rd_xtnh, p_sequencer.axi_sqr, {	read_or_write == AXI4_TRANS_READ; 
//																																	addr 					== axi_wr_xtnh.addr; 
//																																	burst_length 	== 0; 			// one transfer
//																																	size 					== AXI4_BYTES_32; 	
//																																	burst 				== AXI4_FIXED ; 
//																																	lock 					== AXI4_NORMAL;})

							//`uvm_info("KUNNU'S >> TRIAL_SEQ",$sformatf("read transaction sent to driver"), UVM_LOW)	
							//axi_rd_xtnh.print;

							p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_err_pkt);
							`uvm_info("AXI_TRAFFIC_HANDLING_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
			end	
		end 
		endcase // test_scenario 
		// enabling schedular traffic
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_axi_scheduler();
		#(50 *1ns);
	endtask: body

endclass: lpddr_subsystem_axi_traffic_handling_test_seq
