//------------------------------------------------------------------------------
// Project     : Axelera LPDDR Subsystem
// File Name   : lpddr_subsystem_error_handling_test_seq.sv
// Unit Name   : lpddr_subsystem_error_handling_test_seq.sv
//------------------------------------------------------------------------------
// Description :
//------------------------------------------------------------------------------
//--------------------------------------------------------------------------------------
// Class name : lpddr_subsystem_error_handling_test_seq
//--------------------------------------------------------------------------------------

class lpddr_subsystem_error_handling_test_seq extends lpddr_subsystem_base_virtual_seq;

  `uvm_object_utils(lpddr_subsystem_error_handling_test_seq)

  lpddr_subsystem_axi_scheduler_seq scheduler_seq;

  axi_trans_t axi_rd_xtnh;
	axi_trans_t axi_wr_xtnh;
  
  uvm_status_e status;
  rand bit poison;
  rand bit poisoncfg_poison_intr_clr, poisoncfg_poison_slverr_en, poisoncfg_poison_intr_en;
  rand bit poisonstat_poison_intr_0;
  real test_scenario;

  //Constarints
  constraint poison_con   {poison inside {0,1};}
  constraint slverr_con   {poisoncfg_poison_slverr_en inside {0,1};}
  constraint intr_en_con  {poisoncfg_poison_intr_en inside {0,1};}
  constraint intr_clr_con {poisoncfg_poison_intr_clr inside {0,1};}
  constraint intr_con     {poisonstat_poison_intr_0 inside {0,1};}

  //-------------------------------------------------------------------------
  // Function       : new
  // Arguments      : string name - Name of the object.
  // Description    : Constructor for fpga base scoreboard class objects.
  //-------------------------------------------------------------------------
  function new (string name = "lpddr_subsystem_error_handling_test_seq");
    super.new(name);
		scheduler_seq = lpddr_subsystem_axi_scheduler_seq::type_id::create("scheduler_seq");
  endfunction : new

  //-------------------------------------------------------------------------
  // Function       : randomize_poison_registers
  // Arguments      : None
  // Description    : This method used to randomize APB Poison Registers.
  //-------------------------------------------------------------------------
  virtual task randomize_poison_registers();
    if(!this.randomize()) begin
			$fatal("Randomization Failed");
		end
    randcase
      1 : begin
            `uvm_do_on_with(axi_rd_xtnh, p_sequencer.axi_sqr,{read_or_write     == AXI4_TRANS_READ;
                                                              addr_user_data[0]	== poison;})
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG,'{'{"rd_poison_slverr_en",poisoncfg_poison_slverr_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG,'{'{"rd_poison_intr_en",poisoncfg_poison_intr_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG,'{'{"rd_poison_intr_clr",poisoncfg_poison_intr_clr}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONSTAT.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONSTAT,'{'{"rd_poison_intr_0",poisonstat_poison_intr_0}}));
          end
      1 : begin
            `uvm_do_on_with(axi_wr_xtnh, p_sequencer.axi_sqr,{read_or_write     == AXI4_TRANS_WRITE;
                                                              addr_user_data[0]	== poison;})
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG,'{'{"wr_poison_slverr_en",poisoncfg_poison_slverr_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG,'{'{"wr_poison_intr_en",poisoncfg_poison_intr_en}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG,'{'{"wr_poison_intr_clr",poisoncfg_poison_intr_clr}}));
            reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONSTAT.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONSTAT,'{'{"wr_poison_intr_0",poisonstat_poison_intr_0}}));
          end
    endcase
  endtask: randomize_poison_registers

  //-------------------------------------------------------------------------
  // Function       : run_ppr_sequence
  // Arguments      : None
  // Description    : This method used to execute PPR Sequence described in
  //                  Table 12-7 of DWC_ddrctl_lpddr54_lpddr5x_databook.pdf.
  //-------------------------------------------------------------------------
  virtual task run_ppr_sequence();
    //1. Disable all low power features:
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_sw",0}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"dsm_en",0}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"selfref_en",0}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL,'{'{"powerdown_en",0}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL,'{'{"hw_lp_en",0}}));
    //TODO: Implement do while loop here for: Poll STAT.operating_mode untill it is '1'
    //2. Disable all periodic calibration features:
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DQSOSCCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DQSOSCCTL0,'{'{"dqsosc_enable",0}}));
    //In databook register for below line is DBG1, but there is no such register, looks like a typo, added correct register name here
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ZQCTL0,'{'{"dis_auto_zq",1}}));
    reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFIUPDTMG2.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFIUPDTMG2,'{'{"ppt2_en",0}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0,'{'{"dis_auto_ctrlupd",1}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DERATECTL0,'{'{"derate_mr4_pause_fc",1}}));
    //TODO: Implement do while loop here for: Poll STAT0.dqsosc_state untill it is '0'
    //3. Disable all traffic:
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL1,'{'{"dis_dq",1}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0,'{'{"dis_auto_refresh",1}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4,'{'{"wck_on",0}}));
    reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL,'{'{"scrub_en",0}}));
    //4. Stop WCK:
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLCMD.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRLCMD,'{'{"ctrlupd",1}}));
    //TODO: Implement do while loop here for: Poll OPCTRLSTAT.ctrlupd_busy untill it is '0'
    //5. Enter PPR:
    //TODO: Send MRW to MR41 with OP[4]=1
    //6. Send Guard Key:
    //TODO: Send MRW to MR42 four times, with values specified in JEDEC specification
    //7. Program the target rank/bank/row into the following registers:
    //TODO: Target rank: MRCTRL0.mr_rank
    //TODO: Target bank: MRCTRL0.mr_addr
    //TODO: Target row : MRCTRL0.mr_data
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_type",0}}));
    //8. Start PPR:
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"ppr_en",1}}));
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_wr",1}}));
    //9. Wait untill PPR completes:
    //TODO: Implement do while loop here for: Poll MRSTAT.ppr_done untill it is '1'
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"ppr_en",0}}));
    //10. Exit PPR:
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"ppr_pgmpst_en",1}}));
    //TODO: Send MRW to MR41 with OP[4]=0
    //TODO: Implement do while loop here for: Poll MRSTAT.mr_wr_busy untill it is '0'
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"ppr_pgmpst_en",0}}));
    //11. Reset LPDDR DRAM:
    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC,'{'{"dfi_reset_n",0}}));
    //12. Reboot. Reset DDRCTL and PHY.
    //TODO: Apply reset for this step.
  endtask : run_ppr_sequence
  
  //-------------------------------------------------------------------------
  // Function       : body
  // Arguments      : None
  // Description    : 
  //-------------------------------------------------------------------------
  virtual task body();
    super.body();
  
      case(test_scenario)

				//Scenario for 2.6: Transaction Poisoning Test
				1 : begin
              `uvm_do_on_with(axi_rd_xtnh, p_sequencer.axi_sqr,{read_or_write     == AXI4_TRANS_READ;
                                                                addr_user_data[0]	== 0;})
              `uvm_do_on_with(axi_wr_xtnh, p_sequencer.axi_sqr,{read_or_write     == AXI4_TRANS_WRITE;
                                                                addr_user_data[0]	== 0;})
              repeat(10) begin
  			        randomize_poison_registers(); 
              end
              repeat(2) begin
                `uvm_do_on_with(axi_rd_xtnh, p_sequencer.axi_sqr,{read_or_write     == AXI4_TRANS_READ;
                                                                  addr_user_data[0]	== 0;})
              end
              repeat(2) begin
                `uvm_do_on_with(axi_wr_xtnh, p_sequencer.axi_sqr,{read_or_write     == AXI4_TRANS_WRITE;
                                                                  addr_user_data[0]	== 0;})
              end
			      end
			  //Scenario for 7.2: LPDDR5 Post Package Repair Test
			  2 : begin
              //Before PPR sequence, ensure the following registers are programmed correctly along with the other registers:
              //TODO:Implement below line
              //Set DDR4PRTMG0/1
              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR,'{'{"dfi_phymstr_en",0}}));
              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIUPD0,'{'{"dfi_phyupd_en",0}}));
              repeat(2) begin
                run_ppr_sequence();
              end
              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.write(status,generate_write_value(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0,'{'{"mr_wr",0}}));
					  end
	    endcase
  endtask : body
endclass : lpddr_subsystem_error_handling_test_seq
