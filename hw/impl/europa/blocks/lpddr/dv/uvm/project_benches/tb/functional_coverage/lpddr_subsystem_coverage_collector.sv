//---------------------------------------------------------------------------
// Project    : Axelera LPDDR Subsystem
// File name  : lpddr_subsystem_coverage_collector.sv
// Unit       : lpddr_subsystem_coverage_collector
//---------------------------------------------------------------------------
//Description :
//---------------------------------------------------------------------------

`ifndef LPDDR_SUBSYSTEM_COVERAGE_COLLECTOR_SV
`define LPDDR_SUBSYSTEM_COVERAGE_COLLECTOR_SV

`uvm_analysis_imp_decl(_axi_mngr_cov)

//------------------------------------------------------------------------------
// Class       : lpddr_subsystem_coverage_collector
// Parent      : uvm_component
// Description : 
//------------------------------------------------------------------------------

class lpddr_subsystem_coverage_collector extends uvm_component;

  `uvm_component_utils(lpddr_subsystem_coverage_collector)

	// Declar ports to get data from Monitor 
	uvm_analysis_imp_axi_mngr_cov#(mvc_sequence_item_base, lpddr_subsystem_coverage_collector) analysis_port_axi;
	//uvm_analysis_imp#(apb3_host_trans_t, lpddr_subsystem_coverage_collector) analysis_port_apb;
	//uvm_analysis_imp#(amem_command_class, lpddr_subsystem_coverage_collector) analysis_port_lpddr;

	axi_trans_t trans_axi;
	apb3_host_trans_t trans_apb;
	amem_command_class trans_lpddr;

  lpddr_subsystem_ral_chip_pkg::lpddr_subsystem_apb_reg_block reg_model;

	virtual axi4_if_t m_axi4_if;

  event trigger_coverage;
	time last_txn_time;
  time current_txn_time;
	time axi_idle_time;
  //Instance of covergroup
  cg_initalization_reg m_cg_initalization_reg;

  cg_mode_reg_rd_wr m_cg_mode_reg_rd_wr;

  cg_transaction_poisoning_test m_wr_cg_transaction_poisoning_test;
  cg_transaction_poisoning_test m_rd_cg_transaction_poisoning_test;

  cg_post_package_repair_test m_cg_post_package_repair_test;

  cg_data_bus_inversion m_cg_data_bus_inversion;

  cg_wcl_clocking m_cg_wcl_clocking;

  cg_scrubber_status m_cg_scrubber_status;

	cg_axi_input_traffic m_cg_axi_input_traffic;
	cg_addr_collision_handling m_cg_addr_collision_handling;
	cg_address_translation m_cg_address_translation;
	cg_pagematch m_cg_pagematch;
	cg_page_policy m_cg_page_policy;
	cg_wr_to_rd_switching m_cg_wr_to_rd_switching;
	cg_ddrc_rd_wr_internal_port_priorities m_cg_ddrc_rd_wr_internal_port_priorities;
	cg_lpddr5_masked_write m_cg_lpddr5_masked_write;

  perf_signal_covergroup#("axi_input_traffic") m_cg_perf_axi_input_traffic_test;
  perf_signal_covergroup#("self_refresh") m_cg_perf_selfref;
  perf_signal_covergroup#("precharge_powerdown") m_cg_perf_precharge_powerdown;
  perf_signal_covergroup#("deep_sleep") m_cg_perf_deep_sleep;

  cg_self_refresh m_cg_self_refresh;
  cg_pre_charge_power_down m_cg_pre_charge_power_down;
  cg_deep_sleep_mode m_cg_deep_sleep_mode;

	cg_refresh_management m_cg_refresh_management;
	cg_all_bank_refresh_using_auto_refresh m_cg_all_bank_refresh_using_auto_refresh;
	cg_per_bank_refresh_using_auto_refresh_feature m_cg_per_bank_refresh_using_auto_refresh_feature;
  cg_software_refresh_command m_cg_software_refresh_command;	

  //----------------------------------------------------------------------------
  // Function Name : new
  // Arguments     : string name
  //                 uvm_component parent
  //----------------------------------------------------------------------------
	function new(string name = "lpddr_subsystem_coverage_collector", uvm_component parent = null);
	  super.new(name, parent);
		//Creating analysis port
	  analysis_port_axi = new("analysis_port_axi", this);
	  //analysis_port_apb = new("analysis_port_apb", this);
	  //analysis_port_lpddr = new("analysis_port_lpddr", this);

		//covere group new()
    //cg_paddr_25_22 = new();
	endfunction : new 

  //----------------------------------------------------------------------------
  // Function Name : build_phase
  // Arguments     : uvm_phase phase
  //----------------------------------------------------------------------------
  virtual function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    trans_axi  = axi_trans_t::type_id::create("trans_axi");
		trans_apb  = apb3_host_trans_t::type_id::create("trans_apb");
		trans_lpddr= amem_command_class::type_id::create("trans_lpddr");

    if(!uvm_config_db#(lpddr_subsystem_ral_chip_pkg::lpddr_subsystem_apb_reg_block)::get(null,"","reg_model",reg_model)) begin
      `uvm_error("lpddr_subsystem_apb_reg_block","reg model not found")
    end
// TODO Kunal: modify; for axi reset. change fatal to error 
		//if(uvm_config_db#(axi4_if_t)::get(null,"","null",m_axi4_if)) 
			//begin 
      	//`uvm_fatal("coverage collector","can't get axi interface")
			//end 
    m_cg_initalization_reg = new();
    m_cg_initalization_reg.set_inst_name({get_full_name(),".m_cg_initalization_reg"});
    m_cg_initalization_reg.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-1.1.");

    m_cg_mode_reg_rd_wr = new();
    m_cg_mode_reg_rd_wr.set_inst_name({get_full_name(),".m_cg_mode_reg_rd_wr"});
    m_cg_mode_reg_rd_wr.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-1.3.");

    m_wr_cg_transaction_poisoning_test = new();
    m_wr_cg_transaction_poisoning_test.set_inst_name({get_full_name(),".m_wr_cg_transaction_poisoning_test"});
    m_wr_cg_transaction_poisoning_test.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-2.7.");

    m_rd_cg_transaction_poisoning_test = new();
    m_rd_cg_transaction_poisoning_test.set_inst_name({get_full_name(),".m_rd_cg_transaction_poisoning_test"});
    m_rd_cg_transaction_poisoning_test.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-2.7.");

    m_cg_post_package_repair_test = new();
    m_cg_post_package_repair_test.set_inst_name({get_full_name(),".m_cg_post_package_repair_test"});
    m_cg_post_package_repair_test.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-7.2.");

    m_cg_data_bus_inversion = new();
    m_cg_data_bus_inversion.set_inst_name({get_full_name(),".m_cg_data_bus_inversion"});
    m_cg_data_bus_inversion.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-1.4.");

    m_cg_wcl_clocking = new();
    m_cg_wcl_clocking.set_inst_name({get_full_name(),".m_cg_wcl_clocking"});
    m_cg_wcl_clocking.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-2.3.");

    m_cg_scrubber_status = new();
    m_cg_scrubber_status.set_inst_name({get_full_name(),".m_cg_scrubber_status"});
    m_cg_scrubber_status.option.comment = $psprintf("This Covergroup covers Transaction Poisoning Coverage from Testplan-7.4.");

		m_cg_axi_input_traffic=new();
		m_cg_axi_input_traffic.set_inst_name({get_full_name(),".m_cg_axi_input_traffic"}); 
		m_cg_axi_input_traffic.option.comment="This covergroup covers axi input traffic";

		m_cg_addr_collision_handling=new();
		m_cg_addr_collision_handling.set_inst_name({get_full_name(),".m_cg_addr_collision_handling"}); 
		m_cg_addr_collision_handling.option.comment="This covergroup covers address collision handling feature";

		m_cg_address_translation=new();
		m_cg_address_translation.set_inst_name({get_full_name,".m_cg_address_translation"});
		m_cg_address_translation.option.comment="This covergroup covers address transalation";
	
		m_cg_pagematch=new();
		m_cg_pagematch.set_inst_name({get_full_name(),".m_cg_pagematch"}); 
		m_cg_pagematch.option.comment="This covergroup covers the pagematch feature";
	
		m_cg_page_policy=new();
		m_cg_page_policy.set_inst_name({get_full_name(),".m_cg_page_policy"}); 
		m_cg_page_policy.option.comment="This covergroup covers the page policy";
	
		m_cg_wr_to_rd_switching=new();
		m_cg_wr_to_rd_switching.set_inst_name({get_full_name,".m_cg_wr_to_rd_switching"});
		m_cg_wr_to_rd_switching.option.comment="This covergroup covers the write to read switching feature";
	
		m_cg_ddrc_rd_wr_internal_port_priorities=new();
		m_cg_ddrc_rd_wr_internal_port_priorities.set_inst_name({get_full_name,".m_cg_ddrc_rd_wr_internal_port_priorities"});
		m_cg_ddrc_rd_wr_internal_port_priorities.option.comment="This covergroup covers the write to read switching feature";

		m_cg_lpddr5_masked_write=new();
		m_cg_lpddr5_masked_write.set_inst_name({get_full_name,".m_cg_lpddr5_masked_write"});
		m_cg_lpddr5_masked_write.option.comment="This covergroup covers the lpddr5 masked write feature";


		// performance logging covergroups
		m_cg_perf_axi_input_traffic_test=new();
// TODO Kunal: modify; can't give a comment as this is a class not a covergroup
		//m_cg_perf_axi_input_traffic_test.set_inst_name({get_full_name,".cg_perf_axi_input_traffic_test"});
		//m_cg_perf_axi_input_traffic_test.option.comment="This covergroup covers the performance logging signal for axi input handling test";

		m_cg_self_refresh = new();
    m_cg_self_refresh.set_inst_name({get_full_name(),".m_cg_self_refresh"});
    m_cg_self_refresh.option.comment = $psprintf("This Covergroup covers self refresh Coverage from Testplan-2.6.2");

		//m_cg_perf_selfref = new("m_cg_perf_selfref",this);
   // m_cg_perf_selfref.set_inst_name({get_full_name(),".m_cg_perf_selfref"});
    //m_cg_perf_selfref.option.comment = $psprintf("This Covergroup covers self refresh perf signals Coverage from Testplan-2.6.2");

		m_cg_pre_charge_power_down = new();
    m_cg_pre_charge_power_down.set_inst_name({get_full_name(),".m_cg_pre_charge_power_down"});
    m_cg_pre_charge_power_down.option.comment = $psprintf("This Covergroup covers self refresh perf signals Coverage from Testplan-2.6.2");

		//m_cg_perf_precharge_powerdown = new();
    //m_cg_perf_precharge_powerdown.set_inst_name({get_full_name(),".m_cg_perf_precharge_powerdown"});
    //m_cg_perf_precharge_powerdown.option.comment = $psprintf("This Covergroup covers self refresh perf signals Coverage from Testplan-2.6.2");

		m_cg_deep_sleep_mode = new();
    m_cg_deep_sleep_mode.set_inst_name({get_full_name(),".m_cg_deep_sleep_mode"});
    m_cg_deep_sleep_mode.option.comment = $psprintf("This Covergroup covers self refresh perf signals Coverage from Testplan-2.6.2");

		//m_cg_perf_deep_sleep = new();
    //m_cg_perf_deep_sleep.set_inst_name({get_full_name(),".m_cg_perf_deep_sleep"});
    //m_cg_perf_deep_sleep.option.comment = $psprintf("This Covergroup covers self refresh perf signals Coverage from Testplan-2.6.2");

  	m_cg_refresh_management = new();
    m_cg_refresh_management.set_inst_name({get_full_name(),".m_cg_refresh_management"});
    m_cg_refresh_management.option.comment = $psprintf("This Covergroup covers refresh management coverage from the Testplan-2.4.5");

		m_cg_all_bank_refresh_using_auto_refresh = new();
    m_cg_all_bank_refresh_using_auto_refresh.set_inst_name({get_full_name(),".m_cg_all_bank_refresh_using_auto_refresh"});
    m_cg_all_bank_refresh_using_auto_refresh.option.comment = $psprintf("This Covergroup covers refresh management coverage from the Testplan-2.4.5");

		m_cg_per_bank_refresh_using_auto_refresh_feature = new();
    m_cg_per_bank_refresh_using_auto_refresh_feature.set_inst_name({get_full_name(),".m_cg_per_bank_refresh_using_auto_refresh_feature"});
    m_cg_per_bank_refresh_using_auto_refresh_feature.option.comment = $psprintf("This Covergroup covers refresh management coverage from the Testplan-2.4.5");

		m_cg_software_refresh_command = new();
    m_cg_software_refresh_command.set_inst_name({get_full_name(),".m_cg_per_bank_refresh_using_auto_refresh_feature"});
    m_cg_software_refresh_command.option.comment = $psprintf("This Covergroup covers refresh management coverage from the Testplan-2.4.5");
  endfunction: build_phase
	
  //----------------------------------------------------------------------------
  // Function Name : connect_phase
  // Arguments     : uvm_phase phase
  //----------------------------------------------------------------------------
  virtual function void connect_phase (uvm_phase phase);
    super.connect_phase(phase);
  endfunction: connect_phase

  //----------------------------------------------------------------------------
  // Function Name : run_phase
  // Arguments     : uvm_phase phase
  // Description   : In this phase the TB execution starts.
  //----------------------------------------------------------------------------
  virtual task run_phase (uvm_phase phase);
    super.run_phase(phase);
    fork
      sample_initialization_coverage();
      sample_mode_reg_rd_wr_coverage();
      sample_transaction_poisoning_coverage();
      sample_data_bus_inversion_coverage();
      sample_post_package_repair_coverage();
      sample_wck_clocking_coverage();
      sample_scrubber_coverage();
			sample_selfref_coverage();
			sample_precharge_powerdown();
			sample_deep_sleep();
			sample_refresh_management();
			sample_all_bank_refresh();
			sample_per_bank_refresh();
			sample_software_refresh_command();
    join_none
  endtask: run_phase

  //----------------------------------------------------------------------------
  // Function Name : sample_mode_reg_rd_wr_coverage
  // Arguments     : N/A
  // Description   : This task samples mode register read/write coverage.
  //----------------------------------------------------------------------------
  virtual task sample_mode_reg_rd_wr_coverage();
    bit hif_mrr_data_valid;
    bit [31:0] hif_mrr_data;
    forever@(trigger_coverage) begin
      m_cg_mode_reg_rd_wr.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.mr_rank.get(),
                                 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.mr_addr.get(),
                                 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL1.mr_data.get(),
																 hif_mrr_data,
																 hif_mrr_data_valid,
																 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.mr_type.get(),
                                 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.mrr_done_clr.get(),
                                 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRSTAT.mrr_done.get());
    end
  endtask : sample_mode_reg_rd_wr_coverage
  
  //----------------------------------------------------------------------------
  // Function Name : sample_transaction_poisoning_coverage
  // Arguments     : N/A
  // Description   : This task samples transaction poisoning coverage.
  //----------------------------------------------------------------------------
  virtual task sample_transaction_poisoning_coverage();
    forever@(trigger_coverage) begin
      if (trans_axi.read_or_write == AXI4_TRANS_READ) begin
        m_rd_cg_transaction_poisoning_test.sample(trans_axi.addr_user_data[0],
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.rd_poison_slverr_en.get(),
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.rd_poison_intr_en.get(),
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.rd_poison_intr_clr.get(),
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONSTAT.rd_poison_intr_0.get());
      end
      else begin
        m_wr_cg_transaction_poisoning_test.sample(trans_axi.addr_user_data[0],
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.wr_poison_slverr_en.get(),
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.wr_poison_intr_en.get(),
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONCFG.wr_poison_intr_clr.get(),
		  																			      reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.POISONSTAT.wr_poison_intr_0.get());
      end
    end
  endtask : sample_transaction_poisoning_coverage
  
  //----------------------------------------------------------------------------
  // Function Name : sample_data_bus_inversion_coverage
  // Arguments     : N/A
  // Description   : This task samples data bus inversion coverage.
  //----------------------------------------------------------------------------
  virtual task sample_data_bus_inversion_coverage();
    forever@(trigger_coverage) begin
      if (trans_axi.read_or_write == AXI4_TRANS_READ) begin
        m_cg_data_bus_inversion.sample(/*trans_axi.rdata_words[],
                                      */ reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.phy_dbi_mode.get(),
                                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.rd_dbi_en.get(),
                                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.dm_en.get());
      end
      else begin
        m_cg_data_bus_inversion.sample(/*trans_axi.wdata_words[],
                                      */ reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.phy_dbi_mode.get(),
                                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.wr_dbi_en.get(),
                                       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.dm_en.get());
      end
    end
  endtask : sample_data_bus_inversion_coverage

  //----------------------------------------------------------------------------
  // Function Name : sample_post_package_repair_coverage
  // Arguments     : N/A
  // Description   : This task samples post package repair coverage.
  //----------------------------------------------------------------------------
  virtual task sample_post_package_repair_coverage();
    forever@(trigger_coverage) begin
      m_cg_post_package_repair_test.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.ppr_en.get(),
		  																		 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.mr_wr.get(),
		  																		 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRCTRL0.ppr_pgmpst_en.get(),
		  																		 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MRSTAT.ppr_done.get());
    end
  endtask : sample_post_package_repair_coverage

  //----------------------------------------------------------------------------
  // Function Name : sample_initialization_coverage
  // Arguments     : N/A
  // Description   : This task samples initialization coverage.
  //----------------------------------------------------------------------------
  virtual task sample_initialization_coverage();
    logic core_ddrc_rstn, Reset, Reset_async;
    forever@(trigger_coverage) begin
      m_cg_initalization_reg.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.INITTMG0.skip_dram_init.get(),
                                    core_ddrc_rstn,
                                    Reset_async,
																    Reset,
		  															reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.dfi_init_start.get(),
		  															reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFISTAT.dfi_init_complete.get(),
                                    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.operating_mode.get(),
                                    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR0.burst_rdwr.get(),
                                    reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR0.data_bus_width.get(),
		  															reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR0.active_ranks.get());
    end
  endtask : sample_initialization_coverage

  //----------------------------------------------------------------------------
  // Function Name : sample_wck_clocking_coverage
  // Arguments     : N/A
  // Description   : This task samples wck clocking coverage.
  //----------------------------------------------------------------------------
  virtual task sample_wck_clocking_coverage();
    forever@(trigger_coverage) begin
      m_cg_wcl_clocking.sample(reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG4.get(),
                               reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.DFITMG5.get(),
															 reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.TMGCFG.frequency_ratio.get(),
															 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.wck_on.get(),
														 	 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.wck_suspend_en.get(),
														 	 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.MSTR4.ws_off_en.get());
    end
  endtask : sample_wck_clocking_coverage

  //----------------------------------------------------------------------------
  // Function Name : sample_scrubber_coverage
  // Arguments     : N/A
  // Description   : This task samples scrubber coverage.
  //----------------------------------------------------------------------------
  virtual task sample_scrubber_coverage();
    bit sbr_resetn;
    forever@(trigger_coverage) begin
      m_cg_scrubber_status.sample(sbr_resetn,
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.scrub_interval.get(),
																	reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.PWRTMG.powerdown_to_x32.get(),
																	reg_model.DWC_ddrctl_map_REGB_FREQ2_CH0.PWRTMG.selfref_to_x32.get(),
                                  reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.scrub_en.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTART0.sbr_address_start_mask_0.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTART1.sbr_address_start_mask_1.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRRANGE0.sbr_address_range_mask_0.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRRANGE1.sbr_address_range_mask_1.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT.scrub_busy.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRSTAT.scrub_done.get(),
																	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.SBRCTL.scrub_during_lowpower.get(),
																	reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.powerdown_en.get(),
																	reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_en.get(),
																	reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_sw.get());
    end
  endtask : sample_scrubber_coverage

	//-------------------------------------------------------------------------------------------
	//Method 			: sample_axi_input_traffic_cov
	//Arguement		: NONE
	//Description	: This tasks sasmple axi input traffic covergroup 
	//-------------------------------------------------------------------------------------------	
	virtual task sample_input_axi_traffic_cov();
// TODO Kunal: modify;	change to reset from axi interface	
	bit arst_n;
		forever@(trigger_coverage)
			begin 
				m_cg_axi_input_traffic.sample(trans_axi.burst,
																			trans_axi.size,
																			trans_axi.burst_length,
																			trans_axi.qos,
																			trans_axi.addr, 
																			//arst_n
																			m_axi4_if.ARESETn
																			);
				m_cg_perf_axi_input_traffic_test.sample;
			end 
	endtask:sample_input_axi_traffic_cov

	//-------------------------------------------------------------------------------------------
	//Method 			: sample_address_translation_cov
	//Arguement		: NONE
	//Description	: This task samples address translation covergroup 
	//-------------------------------------------------------------------------------------------	
	virtual task sample_address_translation_cov();
		forever@(trigger_coverage)
			begin 
				//m_cg_address_translation.sample();
			end 
	endtask:sample_address_translation_cov

	//-------------------------------------------------------------------------------------------
	//Method 			: sample_pagematch_cov
	//Arguement		: NONE
	//Description	: This task samples pagematch covergroup
	//-------------------------------------------------------------------------------------------	
	virtual task sample_pagematch_cov();
		forever@(trigger_coverage)
			begin 
				m_cg_pagematch.sample(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW.get("wr_port_pagematch_en"),
															reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR.get("rd_port_pagematch_en"),
															reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCCFG.get("pagematch_limit"),
															trans_axi.addr);

				`uvm_info("KUNNU'S>> SAMPLE_PAGEMATCH_COV",$sformatf("wr_port_pagematch_en: %0d | rd_port_pagematch_en: %0d | pagematch_timer: %0d",reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW.get("wr_port_pagematch_en"),reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR.get("rd_port_pagematch_en"),reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCCFG.get("pagematch_limit")), UVM_DEBUG)	
			end 
	endtask:sample_pagematch_cov

	//-------------------------------------------------------------------------------------------
	//Method 			: sample_page_policy_cov
	//Arguement		: NONE
	//Description	: This task samples page policy covergroup 
	//-------------------------------------------------------------------------------------------	
	virtual task sample_page_policy_cov();
// TODO Kunal: remove; and pass the value from lpddr transaction 	
	bit a10_ap;
		forever@(trigger_coverage)
			begin 
				m_cg_page_policy.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0.get("pageclose"),
																reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.SCHEDTMG0.get("pageclose_timer"),
																a10_ap
																);
				`uvm_info("KUNNU'S>> SAMPLE_PAGE_POLICY_COV",$sformatf(""), UVM_DEBUG)
			end 
	endtask:sample_page_policy_cov
	
	//-------------------------------------------------------------------------------------------
	//Method 			: sample_wr_to_rd_switching_cov
	//Arguement		: NONE
	//Description	: This task samples write to read switching covergroup 
	//-------------------------------------------------------------------------------------------	
	virtual task sample_wr_to_rd_switching_cov();
		forever@(trigger_coverage)
			begin 
// TODO Kunal: add;	debug info			
				m_cg_wr_to_rd_switching.sample(	reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS0.get(),
																				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGQOS1.get(),
																				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS0.get(),
																				reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGWQOS1.get(),
																				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED4.get(),
																				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED3.get(),
																				trans_axi.qos,
																				trans_axi.read_or_write
																				);
			end 
	endtask:sample_wr_to_rd_switching_cov

	//-------------------------------------------------------------------------------------------
	//Method 			: sample_ddrc_rd_wr_internal_port_priorities_cov
	//Arguement		: NONE
	//Description	: This task samples write to read switching covergroup 
	//-------------------------------------------------------------------------------------------	
// TODO Kunal: modify; add axi pkt variables
// TODO Kunal: add;  debug info
	virtual task sample_ddrc_rd_wr_internal_port_priorities_cov();
		forever@(trigger_coverage)
			begin 
				m_cg_ddrc_rd_wr_internal_port_priorities.sample(reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGR.get("rd_port_priority"),
																												reg_model.DWC_ddrctl_map_REGB_ARB_PORT0.PCFGW.get("wr_port_priority"),
																												reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.SCHED0.get("lpr_num_entries"),
																												reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.get("dm_en"),
																												trans_axi.burst_length							
																												);
			end 
	endtask:sample_ddrc_rd_wr_internal_port_priorities_cov
	
	//-------------------------------------------------------------------------------------------
	//Method 			: sample_lpddr5_masked_write_cov
	//Arguement		: NONE
	//Description	: 
	//-------------------------------------------------------------------------------------------	
	virtual task sample_lpddr5_masked_write_cov();
		forever@(trigger_coverage)
			begin 
				m_cg_lpddr5_masked_write.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.get("lp_optimized_write"),
																				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.get("wr_dbi_en"),
																				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.get("dm_en"),
																				reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.get("phy_dbi_mode")
																				);

			`uvm_info("KUNNU'S>> SAMPLE_MASKED_WRITE_COV",$sformatf("lp_optimized_write: %0d | wr_dbi_en: %0d | dm_en: %0d | phy_dbi_mode: %0d",reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.get("lp_optimized_write"),reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.get("wr_dbi_en"),reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.get("dm_en"),reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIMISC.get("phy_dbi_mode")), UVM_DEBUG)	
			end 
	endtask:sample_lpddr5_masked_write_cov
	
	//-------------------------------------------------------------------------------------------
	//Method 			: sample_addr_collision_handling
	//Arguement		: NONE
	//Description	: 
	//-------------------------------------------------------------------------------------------	
	virtual task sample_addr_collision_handling();
		forever@(trigger_coverage)
			begin 
				m_cg_addr_collision_handling.sample(trans_axi.read_or_write,
																						trans_axi.addr,
																						reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPCTRL0.get("dis_wc"),
																						reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.ECCCFG0.get("ecc_mode"),
																						reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DBICTL.get("dm_en")
																						);
// TODO Kunal: add; debug variables				
				`uvm_info("KUNNU'S>> SAMPLE_ADDR_COLL_HANDLING_COV",$sformatf(""), UVM_HIGH)	
			end 
	endtask:sample_addr_collision_handling
	
	//----------------------------------------------------------------------------
  // Function Name : sample_selfref_coverage
  // Arguments     : N/A
  // Description   : This task samples self refresh coverage.
  //----------------------------------------------------------------------------
  virtual task sample_selfref_coverage();
    forever@(trans_lpddr.mem_cmd) begin
			if ( trans_lpddr.mem_cmd == AMEM_SELF_REF )begin
		    m_cg_self_refresh.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_en.get(),
			                           reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_sw.get(),
															   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.stay_in_selfref.get(),
											           reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.dfi_lp_en_sr.get(),
											           reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.selfref_to_x32.get(),
											           reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.dfi_lp_wakeup_sr.get(),
															   reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL.hw_lp_en.get(),
											           axi_idle_time
															   //reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.selfref_type.get(),
															   //reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.selfref_state.get(),
											            );
		    //m_cg_perf_selfref.sample();
			end
    end 
  endtask : sample_selfref_coverage

	//----------------------------------------------------------------------------
  // Function Name : sample_precharge_powerdown
  // Arguments     : N/A
  // Description   : This task samples precharge powerdown coverage.
  //----------------------------------------------------------------------------
	virtual task sample_precharge_powerdown();
	  forever @(trans_lpddr.mem_cmd)begin
		  if(trans_lpddr.mem_cmd == AMEM_POWER_DOWN)begin
			  m_cg_pre_charge_power_down.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_en.get(),
				                                  reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.dfi_lp_en_pd.get(),
																					reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.PWRTMG.powerdown_to_x32.get(),
																					reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.dfi_lp_wakeup_pd.get(),
																					axi_idle_time
																	        );
			//	m_cg_perf_precharge_powerdown.sample();
			end
		end
	endtask

	//----------------------------------------------------------------------------
  // Function Name : sample_deep_sleep
  // Arguments     : N/A
  // Description   : This task samples precharge powerdown coverage.
  //----------------------------------------------------------------------------
	virtual task sample_deep_sleep();
	  forever @(trans_lpddr.mem_cmd)begin
		  //TODO : which command is used for deep sleep 
			if(trans_lpddr.mem_cmd == AMEM_SLEEP )begin
			  m_cg_deep_sleep_mode.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_en.get(),
			                              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFILPCFG0.dfi_lp_en_dsm.get(),
			                              reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.dfi_lp_wakeup_sr.get(),
			                              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_sw.get(),
			                              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.PWRCTL.selfref_en.get(),
			                              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.HWLPCTL.hw_lp_en.get(),
			                              reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.DFIPHYMSTR.dfi_phymstr_en.get(),
		                                reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.STAT.selfref_state.get(),
			                              reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.dfi_lp_wakeup_dsm.get(),
			                              reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG0.dfi_lp_wakeup_pd.get(),
			                              reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG1.dfi_lp_wakeup_data.get(),
			                              reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.DFILPTMG1.dfi_tlp_resp.get()
			                              );
			
			//m_cg_perf_deep_sleep.sample();
			end
		end
	endtask
  
	
	//----------------------------------------------------------------------------
  // Function Name : sample_refresh_management
  // Arguments     : N/A
  // Description   : 
  //----------------------------------------------------------------------------
	virtual task sample_refresh_management();
	  forever@(trans_lpddr.mem_cmd == AMEM_REFRESH)begin
		  m_cg_refresh_management.sample(reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.rfm_en.get(),
			                               reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFMMOD0.rfmsbc.get()
														          );
		end
	endtask

	virtual task sample_all_bank_refresh();
	  forever@(trans_lpddr.mem_cmd == AMEM_REFRESH)begin
		  m_cg_all_bank_refresh_using_auto_refresh.sample(
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.dis_auto_refresh.get()
			,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.per_bank_refresh.get()
			,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.refresh_update_level.get()
			,reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG1.t_rfc_min_ab.get()
			,reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG3.refresh_to_ab_x32.get()
			,reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.refresh_burst.get());
		end
	endtask

	virtual task sample_per_bank_refresh();
	  forever@(trans_lpddr.mem_cmd == AMEM_REFRESH)begin
		  m_cg_per_bank_refresh_using_auto_refresh_feature.sample(
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.dis_auto_refresh.get(),
       reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.per_bank_refresh.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.refresh_update_level.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.auto_refab_en.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.per_bank_refresh.get(),
			 reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG0.refresh_to_x1_sel.get(),
			 reg_model.DWC_ddrctl_map_REGB_FREQ0_CH0.RFSHSET1TMG0.t_refi_x1_sel.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.refresh_burst.get());
		end
	endtask

	virtual task sample_software_refresh_command();
	  forever @(trans_lpddr.mem_cmd == AMEM_REFRESH)begin
		  m_cg_software_refresh_command.sample(
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.dis_auto_refresh.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHCTL0.refresh_update_level.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0.rank0_refresh.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFCTRL0.rank1_refresh.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.RFSHMOD0.per_bank_refresh.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.rank0_refresh_busy.get(),
			 reg_model.DWC_ddrctl_map_REGB_DDRC_CH0.OPREFSTAT0.rank1_refresh_busy.get()
      );
		end
	endtask

  
	
	//----------------------------------------------------------------------------
  // Function Name : write_axi_mngr_cov
  // Arguments     : axi4_manager_rw_trans_t trans
  // Description   : write method for transaction from AXI4 Manager interface of
  //                 the LPDDR Subsystem.
  //----------------------------------------------------------------------------
  virtual function void write_axi_mngr_cov (mvc_sequence_item_base trans);
    //Creating seperate copy of transaction
    assert($cast(trans_axi,trans.clone()));
    ->trigger_coverage;

		//Get the current time
		current_txn_time = $time;

		//Calculate the idle time
		if(last_txn_time != 0)begin
		  axi_idle_time = current_txn_time - last_txn_time;
		end

		//Update the last transaction time
		last_txn_time = current_txn_time;
  endfunction : write_axi_mngr_cov

endclass : lpddr_subsystem_coverage_collector
`endif // LPDDR_SUBSYSTEM_COVERAGE_COLLECTOR_SV
