//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : 
// Unit Name   : 
//------------------------------------------------------------------------------
// Description : 
//------------------------------------------------------------------------------

//--------------------------------------------------------------------------------------
// Class name : lpddr_subsystem_addr_translation_test_seq
//--------------------------------------------------------------------------------------
// TODO Kunal: add; ADDRMAP0 reg configuration
// TODO Kunal: add; ADDRMAP1.bit1,bit2,bit3 
// TODO Kunal: add; directed scenario for address map recommendation  
// TODO Kunal: add; constraint for addr bits higher than the lowe bits  i.e.
// 									bit1	> bit0
class lpddr_subsystem_addr_translation_test_seq extends lpddr_subsystem_base_virtual_seq;
  
	`uvm_object_utils(lpddr_subsystem_addr_translation_test_seq)

  function new(string name = "lpddr_subsystem_addr_translation_test_seq");
    super.new(name);
	endfunction : new
  
 	axi_trans_t axi_wr_pkt;
 	axi_trans_t axi_rd_pkt;

	// status for register writes
	uvm_status_e status;

  rand bit [5:0] addrmap1_bit0,addrmap1_bit1,addrmap1_bit2,addrmap1_bit3; //rank
  rand bit [5:0] addrmap3_bank0, addrmap3_bank1, addrmap3_bank2; //bank
  rand bit [5:0] addrmap4_bg_b0, addrmap4_bg_b1; //bank group
  rand bit [4:0] addrmap6_col_b3, addrmap6_col_b4, addrmap6_col_b5, addrmap6_col_b6, addrmap5_col_b7, addrmap5_col_b8, addrmap5_col_b9, addrmap5_col_b10;  //coloumb
  rand bit [4:0] addrmap_row [18]; //row

	rand bit [1:0] rand_bank_org;
	rand bit rand_bank_hash_en;

	rand bit [2:0] rand_nonbinary_device_density;

	constraint valid_rand_bank_org {rand_bank_org inside {0,2};}
	constraint valid_nonbinary_device_density {rand_nonbinary_device_density inside {[0:5]};} 

// TODO Kunal: modify; invalid addresses
	//constraint nonbinary_device_desity_addr_err {(rand_nonbinary_device_density == 1) -> ();
																									//}

  constraint addrmap_constraints {
    //rank 
    addrmap1_bit0 inside {[0:33],63};
    addrmap1_bit1 inside {[0:32],63};
    addrmap1_bit2 inside {[0:27],63};
    addrmap1_bit3 inside {[0:26],63};

// TODO Kunal: modify?	 
    //bank 
    addrmap3_bank1 == addrmap3_bank0;
    addrmap3_bank2 == addrmap3_bank1;
 
    addrmap3_bank0 inside {[0:36],63};
    addrmap3_bank1 inside {[0:35],63};
    addrmap3_bank2 inside {[0:34],63};
 
    //bank group
    addrmap4_bg_b1 == addrmap4_bg_b0;
 
    addrmap4_bg_b0 inside {[0:36],63};
    addrmap4_bg_b1 inside {[0:35],63};
 
    //colomb
    addrmap6_col_b4 	== addrmap6_col_b3;
    addrmap6_col_b5 	== addrmap6_col_b4;
    addrmap6_col_b6 	== addrmap6_col_b5;
    addrmap5_col_b7 	== addrmap6_col_b6; 
    addrmap5_col_b8 	== addrmap5_col_b7;
    addrmap5_col_b9 	== addrmap5_col_b8;
    addrmap5_col_b10 	== addrmap5_col_b9;

    addrmap6_col_b3 	inside {[0:7]};
    addrmap6_col_b4 	inside {[0:7],15};
    addrmap6_col_b5 	inside {[0:7],15};
    addrmap6_col_b6 	inside {[0:7],15};
    addrmap5_col_b7 	inside {[0:7],15};
    addrmap5_col_b8 	inside {[0:7],15};
    addrmap5_col_b9 	inside {[0:7],15};
    addrmap5_col_b10 	inside {[0:7],15};
 
    //row
    foreach (addrmap_row[i]) 
      if(i<17) 
        addrmap_row[i+1] ==  addrmap_row[i];
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        addrmap_row[i] >= 0 && addrmap_row[i] <= 16;

 
    // not equal 
    (addrmap1_bit0 + 6) != (addrmap3_bank0 + 3);
    (addrmap1_bit0 + 6) != (addrmap3_bank1 + 4);
    (addrmap1_bit0 + 6) != (addrmap3_bank2 + 5);
    (addrmap1_bit0 + 6) != (addrmap4_bg_b0 + 3);
    (addrmap1_bit0 + 6) != (addrmap4_bg_b1 + 4);
    (addrmap1_bit0 + 6) != (addrmap6_col_b3 + 3);
    (addrmap1_bit0 + 6) != (addrmap6_col_b4 + 4);
    (addrmap1_bit0 + 6) != (addrmap6_col_b5 + 5);
    (addrmap1_bit0 + 6) != (addrmap6_col_b6 + 6);
    (addrmap1_bit0 + 6) != (addrmap5_col_b7 + 7);
    (addrmap1_bit0 + 6) != (addrmap5_col_b8 + 8);
    (addrmap1_bit0 + 6) != (addrmap5_col_b9 + 9);
    (addrmap1_bit0 + 6) != (addrmap5_col_b10 + 10);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap1_bit0 + 6) != (addrmap_row[i] + i + 6);
 
 
    (addrmap3_bank0 + 3) != (addrmap4_bg_b0 + 3);
    (addrmap3_bank0 + 3) != (addrmap4_bg_b1 + 4);
    (addrmap3_bank0 + 3) != (addrmap6_col_b3 + 3);
    (addrmap3_bank0 + 3) != (addrmap6_col_b4 + 4);
    (addrmap3_bank0 + 3) != (addrmap6_col_b5 + 5);
    (addrmap3_bank0 + 3) != (addrmap6_col_b6 + 6);
    (addrmap3_bank0 + 3) != (addrmap5_col_b7 + 7);
    (addrmap3_bank0 + 3) != (addrmap5_col_b8 + 8);
    (addrmap3_bank0 + 3) != (addrmap5_col_b9 + 9);
    (addrmap3_bank0 + 3) != (addrmap5_col_b9 + 10);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap3_bank0 + 3) != (addrmap_row[i] + i + 6);
    (addrmap3_bank1 + 4) != (addrmap4_bg_b0 + 3);
    (addrmap3_bank1 + 4) != (addrmap4_bg_b1 + 4);
    (addrmap3_bank1 + 4) != (addrmap6_col_b3 + 3);
    (addrmap3_bank1 + 4) != (addrmap6_col_b4 + 4);
    (addrmap3_bank1 + 4) != (addrmap6_col_b5 + 5);
    (addrmap3_bank1 + 4) != (addrmap6_col_b6 + 6);
    (addrmap3_bank1 + 4) != (addrmap5_col_b7 + 7);
    (addrmap3_bank1 + 4) != (addrmap5_col_b8 + 8);
    (addrmap3_bank1 + 4) != (addrmap5_col_b9 + 9);
    (addrmap3_bank1 + 4) != (addrmap5_col_b9 + 10);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap3_bank1 + 4) != (addrmap_row[i] + i + 6);
 
    (addrmap3_bank2 + 5) != (addrmap4_bg_b0 + 3);
    (addrmap3_bank2 + 5) != (addrmap4_bg_b1 + 4);
    (addrmap3_bank2 + 5) != (addrmap4_bg_b0 + 3);
    (addrmap3_bank2 + 5) != (addrmap4_bg_b1 + 4);
    (addrmap3_bank2 + 5) != (addrmap6_col_b3 + 3);
    (addrmap3_bank2 + 5) != (addrmap6_col_b4 + 4);
    (addrmap3_bank2 + 5) != (addrmap6_col_b5 + 5);
    (addrmap3_bank2 + 5) != (addrmap6_col_b6 + 6);
    (addrmap3_bank2 + 5) != (addrmap5_col_b7 + 7);
    (addrmap3_bank2 + 5) != (addrmap5_col_b8 + 8);
    (addrmap3_bank2 + 5) != (addrmap5_col_b9 + 9);
    (addrmap3_bank2 + 5) != (addrmap5_col_b9 + 10);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap3_bank2 + 5) != (addrmap_row[i] + i + 6);
 
    (addrmap4_bg_b0 + 3) != (addrmap6_col_b3 + 3);
    (addrmap4_bg_b0 + 3) != (addrmap6_col_b4 + 4);
    (addrmap4_bg_b0 + 3) != (addrmap6_col_b5 + 5);
    (addrmap4_bg_b0 + 3) != (addrmap6_col_b6 + 6);
    (addrmap4_bg_b0 + 3) != (addrmap5_col_b7 + 7);
    (addrmap4_bg_b0 + 3) != (addrmap5_col_b8 + 8);
    (addrmap4_bg_b0 + 3) != (addrmap5_col_b9 + 9);
    (addrmap4_bg_b0 + 3) != (addrmap5_col_b9 + 10);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap4_bg_b0 + 3) != (addrmap_row[i] + i + 6);
 
    (addrmap4_bg_b1 + 4) != (addrmap6_col_b3 + 3);
    (addrmap4_bg_b1 + 4) != (addrmap6_col_b4 + 4);
    (addrmap4_bg_b1 + 4) != (addrmap6_col_b5 + 5);
    (addrmap4_bg_b1 + 4) != (addrmap6_col_b6 + 6);
    (addrmap4_bg_b1 + 4) != (addrmap5_col_b7 + 7);
    (addrmap4_bg_b1 + 4) != (addrmap5_col_b8 + 8);
    (addrmap4_bg_b1 + 4) != (addrmap5_col_b9 + 9);
    (addrmap4_bg_b1 + 4) != (addrmap5_col_b9 + 10);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap4_bg_b1 + 4) != (addrmap_row[i] + i + 6);
 
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap6_col_b3 + 3) != (addrmap_row[i] + i + 6);
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap6_col_b4 + 4) != (addrmap_row[i] + i + 6);
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap6_col_b5 + 5) != (addrmap_row[i] + i + 6);
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap6_col_b6 + 6) != (addrmap_row[i] + i + 6);
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap5_col_b7 + 7) != (addrmap_row[i] + i + 6);
 
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap5_col_b8 + 8) != (addrmap_row[i] + i + 6);
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap5_col_b9 + 9) != (addrmap_row[i] + i + 6);
 
    foreach (addrmap_row[i]) 
      if(i<17) 
        (addrmap5_col_b10 + 7) != (addrmap_row[i] + i + 6);
 
  }

  
	//-------------------------------------------------------------------------------------------
	//Method 			: body
	//Arguements	: NONE
	//Description	: Generate and send stimuli for address translation test seq
	//-------------------------------------------------------------------------------------------	
  virtual task body ();
   //trans rand. //rand with.
   //axi_trans_t rd_trans;

   //assert(rd_trans.randomize with {});


   //p_sequencer.axi_lpddr_scheduler_seq_inst.task ()
// TODO Kunal: remove;	
    $display("rank addrmap1_bit0 = %0d",  addrmap1_bit0 + 6);
    $display("bank addrmap3_bank0 = %0d, addrmap3_bank1 = %0d, addrmap3_bank2 = %0d ", addrmap3_bank0 + 3,  addrmap3_bank1 + 4,  addrmap3_bank2 + 5);
    $display ("bank group addrmap4_bg_b0 = %0d, addrmap4_bg_b1 = %0d",  addrmap4_bg_b0 + 3,  addrmap4_bg_b1 + 4);
    $display("colomb addrmap6_col_b3 = %0d, addrmap6_col_b4 =%0d, addrmap6_col_b5 = %0d, addrmap6_col_b6 = %0d, addrmap5_col_b7 = %0d, addrmap5_col_b8 = %0d, addrmap5_col_b9 = %0d, addrmap5_col_b10 = %0d",  addrmap6_col_b3 + 3,  addrmap6_col_b4 + 4,  addrmap6_col_b5 + 5,  addrmap6_col_b6 + 6,  addrmap5_col_b7 + 7,  addrmap5_col_b8 + 8,  addrmap5_col_b9 + 9,  addrmap5_col_b10 + 10);
    foreach ( addrmap_row[i]) begin
      $display ("Row addrmap_row[%0d] = %0d",i,  addrmap_row[i] + i + 6);  
    end

		// disabling schedular traffic
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_axi_scheduler();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_rd_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_user_wr_data();

    //#20; //TODO : need to chnage delay based upon transaction timing.

    //#20; //TODO : need to chnage delay based upon transaction timing.

    //add logic for bank_org
    //reg_model.DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1.OPCTRL1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0_OPCTRL1.OPCTRL1,'{'{"dis_dq",1'b1}}));

		axi_wr_pkt=axi_trans_t::type_id::create("axi_wr_pkt");
		axi_rd_pkt=axi_trans_t::type_id::create("axi_rd_pkt");

		repeat(100)
			begin 
				write_qd_reg(	QD_GROUP_1,
											reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DRAMSET1TMG24,
											'{'{"bank_org",rand_bank_org}});
				
				assert(axi_wr_pkt.randomize with {read_or_write == AXI4_TRANS_WRITE;})
					else `uvm_error("ADDR_TRANS_TEST_SEQ","write transaction randomization failed")
        assert(axi_rd_pkt.randomize with {read_or_write == AXI4_TRANS_READ;})
					else `uvm_error("ADDR_TRANS_TEST_SEQ","read transaction randomization failed")

				p_sequencer.axi_lpddr_scheduler_seq_inst.write_data_in(axi_wr_pkt);
				`uvm_info("ADDR_TRANS_TEST_SEQ",$sformatf("write transaction sent to driver :\n%s",axi_wr_pkt.sprint), UVM_HIGH)	

				p_sequencer.axi_lpddr_scheduler_seq_inst.read_data_in(axi_rd_pkt);
				`uvm_info("ADDR_TRANS_TEST_SEQ",$sformatf("read transaction sent to driver :\n%s",axi_rd_pkt.sprint), UVM_HIGH)	
			
			end // repeat(100)
		// enabling schedular traffic
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_rd_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.disable_user_wr_data();
		p_sequencer.axi_lpddr_scheduler_seq_inst.enable_axi_scheduler();
		#(50 *1ns);
  endtask : body
  
	//-------------------------------------------------------------------------------------------
	//Method 			: configure_static_reg_during_reset
	//Arguements	: NONE
	//Description	: Overiding base class method to write static registers 
	//-------------------------------------------------------------------------------------------	
	virtual task configure_static_reg_during_reset();
    // TODO : didn't found addrmap0_dch_bit & addrmap1_cs_bit_1 in RAL
    // rank : addrmap1.cs_bit0  //DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP1,'{'{"addrmap_cs_bit0",addrmap1_bit0}}));
// TODO Kunal: remove; un-comment and merge with above 
 		//reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1.ADDRMAP1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1.ADDRMAP1,'{'{"addrmap_cs_bit1",addrmap1_bit1}}));
    //reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1.ADDRMAP1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1.ADDRMAP1,'{'{"addrmap_cs_bit2",addrmap1_bit2}}));
    //reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1.ADDRMAP1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0_ADDRMAP1.ADDRMAP1,'{'{"addrmap_cs_bit3",addrmap1_bit3}}));
    // bank :addrmap3
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP3.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP3,'{'{"addrmap_bank_b0",addrmap3_bank0},'{"addrmap_bank_b1",addrmap3_bank1},'{"addrmap_bank_b2",addrmap3_bank2}}));
    // bankgroup :addrmap4
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP4,'{'{"addrmap_bg_b0",addrmap4_bg_b0},'{"addrmap_bg_b1",addrmap4_bg_b0}}));
    //colomb : addrmap5
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP5.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP5,'{'{"addrmap_col_b7",addrmap5_col_b7},'{"addrmap_col_b8",addrmap5_col_b8},'{"addrmap_col_b9",addrmap5_col_b9},'{"addrmap_col_b10",10}}));
    //addrmap6
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP6.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP6,'{'{"addrmap_col_b3",addrmap6_col_b3},'{"addrmap_col_b4",addrmap6_col_b4},'{"addrmap_col_b5",addrmap6_col_b5},'{"addrmap_col_b6",addrmap6_col_b6}}));
    //addrmap7
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP7.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP7,'{'{"addrmap_row_b14",addrmap_row[14]},'{"addrmap_row_b15",addrmap_row[15]},'{"addrmap_row_b16",addrmap_row[16]},'{"addrmap_col_b17",addrmap_row[17]}}));
    //addrmap8
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP8.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP8,'{'{"addrmap_row_b10",addrmap_row[10]},'{"addrmap_row_b11",addrmap_row[11]},'{"addrmap_row_b12",addrmap_row[12]},'{"addrmap_col_b13",addrmap_row[13]}}));
    //addrmap9
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP9.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP9,'{'{"addrmap_row_b6",addrmap_row[6]},'{"addrmap_row_b7",addrmap_row[7]},'{"addrmap_row_b8",addrmap_row[8]},'{"addrmap_col_b9",addrmap_row[9]}}));
    //addrmap10
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP10.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP10,'{'{"addrmap_row_b2",addrmap_row[2]},'{"addrmap_row_b3",addrmap_row[3]},'{"addrmap_row_b4",addrmap_row[4]},'{"addrmap_col_b5",addrmap_row[5]}}));
    //addrmap11
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP11.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP11,'{'{"addrmap_row_b1",addrmap_row[1]},'{"addrmap_row_b0",addrmap_row[0]}}));
		// addrmap12 configs
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP12.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP12,'{'{"bank_hash_en",rand_bank_hash_en}}));
    reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP12.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ADDR_MAP0.ADDRMAP12,'{'{"nonbinary_device_density",rand_nonbinary_device_density}}));
  endtask:configure_static_reg_during_reset

endclass : lpddr_subsystem_addr_translation_test_seq
