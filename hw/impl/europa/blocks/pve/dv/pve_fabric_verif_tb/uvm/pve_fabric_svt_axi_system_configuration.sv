// *** (C) Copyright Axelera AI 2021        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : ana.stoisavljevic@axelera.ai  *** //

// *****************************************************************************************
// Description: Class cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************

`ifndef GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
`define GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
// Class
class cust_svt_axi_system_configuration extends svt_axi_system_configuration;


  // Factory registration
  `uvm_object_utils(cust_svt_axi_system_configuration)

  // Class Constructor
  function new(string name = "cust_svt_axi_system_configuration");
    super.new(name);

    this.num_masters = 14;
    this.num_slaves  = 12;

    //enables system monitor to perform checks
    this.system_monitor_enable = 1;
    
    //enables data integrity check across interconnect
    this.master_slave_xact_data_integrity_check_enable = 1;
    
    //enables ID based transaction correlation with unique master IDs
    //this.id_based_xact_correlation_enable = 1;
    //enables master id width to generate unique ID
    //this.source_master_info_id_width = 4;
    //sets the position of unique Master ID in AxID
    //this.source_master_info_position = svt_axi_system_configuration::AXI_MSB;
    //this.source_interconnect_id_xmit_to_slaves
    //this.source_master_id_wu_wlu_xmit_to_slaves
    //this.source_master_id_xmit_to_slaves 

    //id_based_xact_correlation_enable = 1;
    //source_master_info_id_width = 4;
    //master[1].source_master_id_xmit_to_slaves = 1; //Specifies that value of 1 is appended for transactions originating from master 1
    //source_master_info_position = LSB

    this.display_summary_report = 0;
    // svt_axi_system_configuration::display_summary_report
    // Disable timeout on ready
    this.awready_watchdog_timeout=0;
    this.wready_watchdog_timeout=100000;
    this.rready_watchdog_timeout=100000;
    // Disable timeout on ready response for streams
    this.tready_watchdog_timeout = 0;
    // Disable timeout on axi interface idle
    this.bus_inactivity_timeout = 0;

    this.allow_slaves_with_overlapping_addr = 1;
 
    //*************************************************************************************************************
    //Setting generic local address for slaves, this allows AXI's system_monitor_enable = 1 without addr errors
    //The valid addr ranges for each slave should be checked
    foreach (this.slave_cfg[i])
      this.set_addr_range(i  , 'h0 , 'hFF_FFFF_FFFF );

    //*************************************************************************************************************
    //set different clocks  
    this.common_clock_mode = 0;
    // Create port configurations
    this.create_sub_cfgs(this.num_masters, this.num_slaves);

    // AXI Master LT interface
    for(int i = 0; i < 10; i++) begin
      if(i != 9) this.master_cfg[i].ace_version = svt_axi_port_configuration::ACE_VERSION_2_0;
      if(i != 9) this.master_cfg[i].atomic_transactions_enable = 1;
      this.master_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].exclusive_access_enable = 1;
      this.master_cfg[i].exclusive_monitor_enable = 1;
      //0 : no restriction of max number of exclusive transactions
      this.master_cfg[i].max_num_exclusive_access = 0; 
      this.master_cfg[i].data_width               = 64;
      this.master_cfg[i].id_width                 = 4;
      this.master_cfg[i].addr_width = 40; 
      master_cfg[i].num_outstanding_xact = 512;
      this.master_cfg[i].protocol_checks_enable = 1;
      //this.master_cfg[i].transaction_coverage_enable = 1;
      this.master_cfg[i].is_active = 1;
      this.master_cfg[i].wysiwyg_enable = 1;
      this.master_cfg[i].default_bready = 1;
      this.master_cfg[i].default_rready = 1; 
      this.master_cfg[i].source_master_id_xmit_to_slaves = 1; //Specifies that value of 1 is appended for transactions originating from master 1
      this.master_cfg[i].read_data_interleave_size = 1;
      this.master_cfg[i].read_data_reordering_depth = 8;
      this.master_cfg[i].reasonable_constraint_mode ( 1'b1 );
      if(i != 9) this.master_cfg[i].enable_mpam = svt_axi_port_configuration::MPAM_FALSE;
    end

    // AXI Master HT interface
    for(int i = 10; i < 14; i++) begin
      this.master_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].exclusive_access_enable = 1;
      this.master_cfg[i].exclusive_monitor_enable = 1;
      //0 : no restriction of max number of exclusive transactions
      this.master_cfg[i].max_num_exclusive_access = 0; 
      this.master_cfg[i].data_width               = 512;
      this.master_cfg[i].id_width                 = 8;
      this.master_cfg[i].addr_width = 40; 
      master_cfg[i].num_outstanding_xact = 512;
      this.master_cfg[i].protocol_checks_enable = 1;
      //this.master_cfg[i].transaction_coverage_enable = 1;
      this.master_cfg[i].is_active = 1;
      this.master_cfg[i].wysiwyg_enable = 1;
      this.master_cfg[i].default_bready = 1;
      this.master_cfg[i].default_rready = 1; 
      this.master_cfg[i].source_master_id_xmit_to_slaves = 1; //Specifies that value of 1 is appended for transactions originating from master 1
      this.master_cfg[i].read_data_interleave_size = 1;
      this.master_cfg[i].read_data_reordering_depth = 8;
    end

    // AXI Slave LT interface
    for(int i = 0; i < 7; i++) begin
      if (i != 6) this.slave_cfg[i].ace_version = svt_axi_port_configuration::ACE_VERSION_2_0;
      if (i != 6) this.slave_cfg[i].atomic_transactions_enable = 1;
      this.slave_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      this.slave_cfg[i].exclusive_access_enable  = 1;
      this.slave_cfg[i].exclusive_monitor_enable = 1;
      this.slave_cfg[i].data_width               = 64; 
      this.slave_cfg[i].id_width                 = 8;
      this.slave_cfg[i].addr_width               = 40;  
      this.slave_cfg[i].num_outstanding_xact = 512;
      this.slave_cfg[i].protocol_checks_enable = 1;
      //this.slave_cfg[i].transaction_coverage_enable = 1;
      this.slave_cfg[i].wysiwyg_enable = 1;
      this.slave_cfg[i].is_active = 1;
      this.slave_cfg[i].default_awready = 1;
      this.slave_cfg[i].default_wready = 1; 
      this.slave_cfg[i].default_arready = 1;
      this.slave_cfg[i].default_rready = 1; 
      this.slave_cfg[i].read_data_interleave_size = 1;
      this.slave_cfg[i].read_data_reordering_depth = 8;
      this.slave_cfg[i].reasonable_constraint_mode( 1'b1 );
      if (i != 6) this.slave_cfg[i].enable_mpam = svt_axi_port_configuration::MPAM_FALSE;
    end

    // AXI Slave HT interface
    for(int i = 7; i < 12; i++) begin
      this.slave_cfg[i].axi_interface_type = svt_axi_port_configuration::AXI4;
      this.slave_cfg[i].exclusive_access_enable  = 1;
      this.slave_cfg[i].exclusive_monitor_enable = 1;
      this.slave_cfg[i].data_width               = 512; 
      this.slave_cfg[i].id_width                 = 11;
      this.slave_cfg[i].addr_width               = 40;  
      this.slave_cfg[i].num_outstanding_xact = 512;
      this.slave_cfg[i].protocol_checks_enable = 1;
      //this.slave_cfg[i].transaction_coverage_enable = 1;
      this.slave_cfg[i].wysiwyg_enable = 1;
      this.slave_cfg[i].is_active = 1;
      this.slave_cfg[i].default_awready = 1;
      this.slave_cfg[i].default_wready = 1; 
      this.slave_cfg[i].default_arready = 1;
      this.slave_cfg[i].default_rready = 1; 
      this.slave_cfg[i].read_data_interleave_size = 1;
      this.slave_cfg[i].read_data_reordering_depth = 8;
    end
  endfunction : new

endclass
`endif  //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV


