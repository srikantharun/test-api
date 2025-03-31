// *** (C) Copyright Axelera AI 2024        *** //
// *** All Rights Reserved                  *** //
// *** Axelera AI Confidential              *** //
// *** Owner : srinivas.prakash@axelera.ai  *** //

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

    //TODO: check configuration to enable all protocol checks
    this.num_masters = 35;
    this.num_slaves  = 34;
    //AXI_SLV = 32 ; APB4_SLV = 34; APB3_SLV = 8

    //enables system monitor to perform checks
    this.system_monitor_enable = 1;
    
    //enables data integrity check across interconnect
    
    //this.master_slave_xact_data_integrity_check_enable = 1;
    
    //enables ID based transaction correlation with unique master IDs
    //this.id_based_xact_correlation_enable = 1;
    //enables master id width to generate unique ID
    //this.source_master_info_id_width = 4;
    //sets the position of unique Master ID in AxID
    //this.source_master_info_position = svt_axi_system_configuration::AXI_MSB;
    //this.source_interconnect_id_xmit_to_slaves
    //this.source_master_id_wu_wlu_xmit_to_slaves

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
    
    //--------------------------------
    // Config for LT Intfs 
    //--------------------------------
    for(int i=e_aic_0_init_lt; i < e_dcd_dec_0_init_mt; i++ ) begin //{
      this.master_cfg[i].axi_interface_type           = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].exclusive_access_enable      = 1;
      this.master_cfg[i].exclusive_monitor_enable     = 1;
      //0 : no restrictr of exclusive transactions
      this.master_cfg[i].max_num_exclusive_access     = 0; 
      this.master_cfg[i].data_width                   = 64;
      this.master_cfg[i].addr_width                   = 40; 
      this.master_cfg[i].num_outstanding_xact         = 512; //TODO: recheck & assign
      this.master_cfg[i].protocol_checks_enable       = 1;
      //this.master_cfght].transaction_coverage_enable = 1;
      this.master_cfg[i].is_active                    = 1;
      this.master_cfg[i].wysiwyg_enable               = 1;
      this.master_cfg[i].default_bready               = 1;
      this.master_cfg[i].default_rready               = 1; 
      //this.master_cfg[init_ai_core_0_ht].reasonable_constraint_mode ( 1'b1 );
      //this.master_cfg[init_ai_core_0_ht].source_master_id_xmit_to_slaves  = init_ai_core_0_ht; 
    end //}
    //--------------------------------
    // Config for MT Intfs 
    //--------------------------------
    for(int i=e_dcd_dec_0_init_mt; i < e_aic_0_init_ht; i++ ) begin //{
      this.master_cfg[i].axi_interface_type           = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].exclusive_access_enable      = 1;
      this.master_cfg[i].exclusive_monitor_enable     = 1;
      //0 : no restrictr of exclusive transactions
      this.master_cfg[i].max_num_exclusive_access     = 0; 
      if (i != e_apu_init_mt)
        this.master_cfg[i].data_width                 = 128;
      else
        this.master_cfg[i].data_width                 = 256;
      this.master_cfg[i].addr_width                   = 40; 
      this.master_cfg[i].num_outstanding_xact         = 512;
      this.master_cfg[i].protocol_checks_enable       = 1;
      //this.master_cfght].transaction_coverage_enable = 1;
      this.master_cfg[i].is_active                    = 1;
      this.master_cfg[i].wysiwyg_enable               = 1;
      this.master_cfg[i].default_bready               = 1;
      this.master_cfg[i].default_rready               = 1; 
      //this.master_cfg[init_ai_core_0_ht].reasonable_constraint_mode ( 1'b1 );
      //this.master_cfg[init_ai_core_0_ht].source_master_id_xmit_to_slaves  = init_ai_core_0_ht; 
    end //}
    //--------------------------------
    // Config for HT Intfs 
    //--------------------------------
    for(int i=e_aic_0_init_ht; i <= e_pve_1_init_ht; i++ ) begin //{
      this.master_cfg[i].axi_interface_type           = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].exclusive_access_enable      = 1;
      this.master_cfg[i].exclusive_monitor_enable     = 1;
      //0 : no restrictr of exclusive transactions
      this.master_cfg[i].max_num_exclusive_access     = 0; 
      this.master_cfg[i].data_width                   = 512;
      this.master_cfg[i].addr_width                   = 40; 
      this.master_cfg[i].num_outstanding_xact         = 512;
      this.master_cfg[i].protocol_checks_enable       = 1;
      //this.master_cfght].transaction_coverage_enable = 1;
      this.master_cfg[i].is_active                    = 1;
      this.master_cfg[i].wysiwyg_enable               = 1;
      this.master_cfg[i].default_bready               = 1;
      this.master_cfg[i].default_rready               = 1; 
      //this.master_cfg[init_ai_core_0_ht].reasonable_constraint_mode ( 1'b1 );
      //this.master_cfg[init_ai_core_0_ht].source_master_id_xmit_to_slaves  = init_ai_core_0_ht; 
    end //}
    //--------------------------------
    // Setting IDW for each init
    //--------------------------------
    this.master_cfg[e_aic_0_init_lt].id_width           = 9;
    this.master_cfg[e_aic_1_init_lt].id_width           = 9;
    this.master_cfg[e_aic_2_init_lt].id_width           = 9;
    this.master_cfg[e_aic_3_init_lt].id_width           = 9;
    this.master_cfg[e_aic_4_init_lt].id_width           = 9;
    this.master_cfg[e_aic_5_init_lt].id_width           = 9;
    this.master_cfg[e_aic_6_init_lt].id_width           = 9;
    this.master_cfg[e_aic_7_init_lt].id_width           = 9;
    this.master_cfg[e_sdma_0_init_lt].id_width          = 4;
    this.master_cfg[e_sdma_1_init_lt].id_width          = 4;
    this.master_cfg[e_pve_0_init_lt].id_width           = 8;
    this.master_cfg[e_pve_1_init_lt].id_width           = 8;
    this.master_cfg[e_apu_init_lt].id_width             = 10;
    this.master_cfg[e_soc_mgmt_init_lt].id_width        = 4;
    this.master_cfg[e_soc_periph_init_lt].id_width      = 4;
    this.master_cfg[e_dcd_dec_0_init_mt].id_width       = 5;
    this.master_cfg[e_dcd_dec_1_init_mt].id_width       = 5;
    this.master_cfg[e_dcd_dec_2_init_mt].id_width       = 5;
    this.master_cfg[e_dcd_mcu_init_lt].id_width         = 5;
    this.master_cfg[e_apu_init_mt].id_width             = 9;
    this.master_cfg[e_pcie_init_mt].id_width            = 7;
    this.master_cfg[e_aic_0_init_ht].id_width           = 9;
    this.master_cfg[e_aic_1_init_ht].id_width           = 9;
    this.master_cfg[e_aic_2_init_ht].id_width           = 9;
    this.master_cfg[e_aic_3_init_ht].id_width           = 9;
    this.master_cfg[e_aic_4_init_ht].id_width           = 9;
    this.master_cfg[e_aic_5_init_ht].id_width           = 9;
    this.master_cfg[e_aic_6_init_ht].id_width           = 9;
    this.master_cfg[e_aic_7_init_ht].id_width           = 9;
    this.master_cfg[e_sdma_0_init_ht_0].id_width        = 8;
    this.master_cfg[e_sdma_0_init_ht_1].id_width        = 8;
    this.master_cfg[e_sdma_1_init_ht_0].id_width        = 8;
    this.master_cfg[e_sdma_1_init_ht_1].id_width        = 8;
    this.master_cfg[e_pve_0_init_ht].id_width           = 11;
    this.master_cfg[e_pve_1_init_ht].id_width           = 11;

    //--------------------------------
    // Config for all TARG Intfs
    //--------------------------------
    foreach(this.slave_cfg[t]) begin //{
      this.slave_cfg[t].axi_interface_type              = svt_axi_port_configuration::AXI4;
      this.slave_cfg[t].exclusive_access_enable         = 1;
      this.slave_cfg[t].exclusive_monitor_enable        = 1;
      if (t == e_pcie_targ_cfg_dbi)
        this.slave_cfg[e_pcie_targ_cfg_dbi].data_width  = 32; 
      else if (t == e_pcie_targ_mt)
        this.slave_cfg[e_pcie_targ_mt].data_width       = 128;
      else if ((t == e_lpddr_graph_0_targ_ht) || (t == e_lpddr_ppp_0_targ_mt) ||
              ( t == e_lpddr_graph_1_targ_ht) || (t == e_lpddr_ppp_1_targ_mt) || 
              ( t == e_lpddr_graph_2_targ_ht) || (t == e_lpddr_ppp_2_targ_mt) || 
              ( t == e_lpddr_graph_3_targ_ht) || (t == e_lpddr_ppp_3_targ_mt) )
        this.slave_cfg[t].data_width                    = 256;
      else if ((t == e_l2_0_targ_ht)|| (t == e_l2_4_targ_ht) ||
              (t == e_l2_1_targ_ht) || (t == e_l2_5_targ_ht) ||
              (t == e_l2_2_targ_ht) || (t == e_l2_6_targ_ht) ||
              (t == e_l2_3_targ_ht) || (t == e_l2_7_targ_ht) )
        this.slave_cfg[t].data_width                    = 512;
      else
        this.slave_cfg[t].data_width                    = 64;
      this.slave_cfg[t].addr_width                      = 40;  
      this.slave_cfg[t].num_outstanding_xact            = 16;
      this.slave_cfg[t].protocol_checks_enable          = 1;
      this.slave_cfg[t].is_active                       = 1;
      this.slave_cfg[t].default_awready                 = 1;
      this.slave_cfg[t].default_wready                  = 1; 
      this.slave_cfg[t].default_arready                 = 1;
      this.slave_cfg[t].default_rready                  = 1; 
      //this.slave_cfg[e_targ_l2_0_ht].transaction_coverage_enable   = 1;
    end //}
    //--------------------------------
    // Setting IDW for each targ 
    //--------------------------------
    this.slave_cfg[e_aic_0_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_1_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_2_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_3_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_4_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_5_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_6_targ_lt].id_width            = 6;
    this.slave_cfg[e_aic_7_targ_lt].id_width            = 6;
    this.slave_cfg[e_sdma_0_targ_lt].id_width           = 4;
    this.slave_cfg[e_sdma_1_targ_lt].id_width           = 4;
    this.slave_cfg[e_pve_0_targ_lt].id_width            = 4;
    this.slave_cfg[e_pve_1_targ_lt].id_width            = 4;
    this.slave_cfg[e_apu_targ_lt].id_width              = 8;
    this.slave_cfg[e_soc_mgmt_targ_lt].id_width         = 4;
    this.slave_cfg[e_soc_periph_targ_lt].id_width       = 4;
    this.slave_cfg[e_sys_spm_targ_lt].id_width          = 4;
    this.slave_cfg[e_pcie_targ_cfg_dbi].id_width        = 4;
    this.slave_cfg[e_lpddr_graph_0_targ_ht].id_width    = 8;
    this.slave_cfg[e_lpddr_graph_1_targ_ht].id_width    = 8;
    this.slave_cfg[e_lpddr_graph_2_targ_ht].id_width    = 8;
    this.slave_cfg[e_lpddr_graph_3_targ_ht].id_width    = 8;
    this.slave_cfg[e_pcie_targ_mt].id_width             = 6;
    this.slave_cfg[e_l2_0_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_1_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_2_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_3_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_4_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_5_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_6_targ_ht].id_width             = 4;
    this.slave_cfg[e_l2_7_targ_ht].id_width             = 4;
    this.slave_cfg[e_lpddr_ppp_0_targ_mt].id_width      = 8;
    this.slave_cfg[e_lpddr_ppp_1_targ_mt].id_width      = 8;
    this.slave_cfg[e_lpddr_ppp_2_targ_mt].id_width      = 8;
    this.slave_cfg[e_lpddr_ppp_3_targ_mt].id_width      = 8;

    //---------------------------------------
    // Initialize VIP signals to default 'b0 
    //---------------------------------------
    foreach(this.master_cfg[p]) begin //{ 
      this.master_cfg[p].write_addr_chan_idle_val       = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[p].write_data_chan_idle_val       = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[p].write_resp_chan_idle_val       = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[p].read_addr_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[p].read_data_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
    end //}
    foreach(this.slave_cfg[p]) begin //{
      this.slave_cfg[p].write_addr_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[p].write_data_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[p].write_resp_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[p].read_addr_chan_idle_val         = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[p].read_data_chan_idle_val         = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
    end //}
  endfunction : new

endclass
`endif  //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV

