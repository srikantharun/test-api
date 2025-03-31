//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_page_match_test_seq.sv
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : contains the seq to verify page match feature 
//------------------------------------------------------------------------------
//-------------------------------------------------------------------------------------------
//Class 			: lpddr_subsystem_page_match_test_seq
//Parent			: lpddr_subsystem_base_virtual_seq
//Description	:
//-------------------------------------------------------------------------------------------	
class lpddr_subsystem_page_match_test_seq extends lpddr_subsystem_base_virtual_seq;
	`uvm_object_utils(lpddr_subsystem_page_match_test_seq)

	// packets
	axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;

	// no_of packet iterations
	int no_of_iter=10;
	
	// status for register writes
	uvm_status_e reg_status;

	// for constraint randomizing pm_limit reg field
	rand bit rand_pagematch_limit_val; 
	rand bit rand_page_match_en_val;

	constraint CON_PM_VAL 			{rand_page_match_en_val dist {0:=1,1:=9};}			// more weight to enable 
	constraint CON_PM_LIMIT_VAL {rand_pagematch_limit_val dist {0:=2,1:=1};}		// more weight to limitless 

	//-------------------------------------------------------------------------------------------
	//Method 			: new
	//Arguement		: name
	//Description	: overriding class constructor 
	//-------------------------------------------------------------------------------------------	
	function new(string name="lpddr_subsystem_page_match_test_seq");
		super.new(name);
		set_automatic_phase_objection(1);
	endfunction: new

	//-------------------------------------------------------------------------------------------
	//Method 			: body
	//Arguement		: NONE
	//Description	: generates and sends axi read and write packets along with
	//							the register configuration to verify page match feature 
	//-------------------------------------------------------------------------------------------	
// TODO Kunal: add; timeout and high priority packets 
	virtual task body();
		super.body();
		`uvm_info("KUNNU'S>> SEQ_NOT_RUNNING",$sformatf("body method started"), UVM_LOW)	
		
		// disabling schedular traffic 
		dis_schedular_traffic();

		// less no of transactions
		repeat(no_of_iter)
			begin

				`uvm_info("KUNNU'S>> SEQ_NOT_RUNNING",$sformatf("before packet sending"), UVM_LOW)	
				send_read_write_pkt(); 
			end //repeat
		
		// enabling schedular traffic 
		en_schedular_traffic();

	endtask: body 
	
	//-------------------------------------------------------------------------------------------
	//Method 			: configure_static_reg_during_reset
	//Arguement		: NONE
	//Description	: overriding the method in base to write register static
	//							registers in reset 
	//-------------------------------------------------------------------------------------------	
	virtual task configure_static_reg_during_reset();
	        super.configure_static_reg_during_reset();
		// enabling rd and wr pagematch
		reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW,'{'{"wr_port_pagematch_en",rand_page_match_en_val}}));
		reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR,'{'{"rd_port_pagematch_en",rand_page_match_en_val}}));
		// configuring pageclose_timer
		reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCCFG.write(reg_status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCCFG,'{'{"pagematch_limit",rand_pagematch_limit_val}}));
	endtask:configure_static_reg_during_reset
	//-------------------------------------------------------------------------------------------
	//Method 			: send_read_write_pkt
// TODO Kunal: modify; include parameters for read and write packets 
	//Arguement		: NONE
	//Description	: sends read and write packets parallely 
	//-------------------------------------------------------------------------------------------	
// FIXME Kunal: drive the incremental burst(same page address)?
// FIXME Kunal: drive the fixed burst with length 0 (different page address)? 
	task send_read_write_pkt;
		fork 
			begin: wr_xtn
				axi_wr_xtnh=axi_trans_t::type_id::create("axi_wr_xtnh");

				assert(axi_wr_xtnh.randomize with {read_or_write == AXI4_TRANS_WRITE;})
					else `uvm_error("PAGE_MATCH_SEQ","write transaction randomization failed")

				`uvm_info("KUNNU'S>> PAGE_MATCH_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_xtnh.sprint), UVM_HIGH)	
				p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_xtnh);
			end //wr_xtn

			begin: rd_xtn 
				axi_rd_xtnh=axi_trans_t::type_id::create("axi_rd_xtnh");
				
				assert(axi_rd_xtnh.randomize with {read_or_write == AXI4_TRANS_READ;})
					else `uvm_error("PAGE_MATCH_SEQ","read transaction randomization failed")

				`uvm_info("KUNNU'S>> PAGE_MATCH_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_xtnh.sprint), UVM_HIGH)	
				p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_xtnh);
			end //rd_xtn
		join 
	endtask: send_read_write_pkt

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

endclass: lpddr_subsystem_page_match_test_seq
