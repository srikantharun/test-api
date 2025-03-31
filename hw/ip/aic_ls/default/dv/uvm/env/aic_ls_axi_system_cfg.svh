// *****************************************************************************************
// Description: Class aic_ls_axi_system_cfg is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate 
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are 
// required by System agent
// *****************************************************************************************
`ifndef GUARD_AIC_DMC_AXI_SYSTEM_CFG_SV
`define GUARD_AIC_DMC_AXI_SYSTEM_CFG_SV
// Class
class aic_ls_axi_system_cfg extends svt_axi_system_configuration;

  // Factory registration
  `uvm_object_utils(aic_ls_axi_system_cfg)

  // Class Constructor
  function new(string name = "aic_ls_axi_system_cfg");
    super.new(name);
    // Setting a value of 0 removes the limit on timeout
    tready_watchdog_timeout = 0;

    // Number of master/slave agents
    num_masters = 4;
    num_slaves  = 6;
    system_monitor_enable = 0;
    display_summary_report = 1;

    // Create port configurations
    create_sub_cfgs(4, 6);

    // AXI VIP Master 0 -> LS CFG Slave Interface
    master_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    master_cfg[0].data_width           = 64;
    master_cfg[0].addr_width           = 40;
    master_cfg[0].id_width             = 9;
    master_cfg[0].num_outstanding_xact = 10;
    `ifdef AI_CORE_TOP_ENV_CHECK
    master_cfg[0].is_active     = 0;
    `else
    master_cfg[0].is_active     = 1;
    `endif

    // AXI VIP Master 1 -> LS HP Slave Interface
    master_cfg[1].axi_interface_type   = svt_axi_port_configuration::AXI4;
    master_cfg[1].data_width           = 512;
    master_cfg[1].addr_width           = 40;
    master_cfg[1].id_width             = 9;
    master_cfg[1].num_outstanding_xact = 10;
    `ifdef AI_CORE_TOP_ENV_CHECK
    master_cfg[1].is_active     = 0;
    `else
    master_cfg[1].is_active     = 1;
    `endif

    // AXI VIP Master 2 -> LS MVM ODR Slave Interface
    master_cfg[2].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    master_cfg[2].tdata_width   = 512;
    `ifdef AI_CORE_TOP_ENV_CHECK
    master_cfg[2].is_active     = 0;
    `else
    master_cfg[2].is_active     = 1;
    `endif
    master_cfg[2].tkeep_enable  = 0;
    master_cfg[2].tstrb_enable  = 0;
    master_cfg[2].tid_enable    = 0;
    master_cfg[2].tdest_enable  = 0;
    master_cfg[2].tuser_enable  = 0;

    // AXI VIP Master 3 -> LS DWPU ODR Slave Interface
    master_cfg[3].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    master_cfg[3].tdata_width   = 512;
   `ifdef AI_CORE_TOP_ENV_CHECK
    master_cfg[3].is_active     = 0;
    `else
    master_cfg[3].is_active     = 1;
    `endif
    master_cfg[3].tkeep_enable  = 0;
    master_cfg[3].tstrb_enable  = 0;
    master_cfg[3].tid_enable    = 0;
    master_cfg[3].tdest_enable  = 0;
    master_cfg[3].tuser_enable  = 0;

    // Disable protocol checkers
    master_cfg[0].protocol_checks_enable = 1;
    master_cfg[1].protocol_checks_enable = 1;
    master_cfg[2].protocol_checks_enable = 1;
    master_cfg[3].protocol_checks_enable = 1;
   
    // Enable/Disable transaction level coverage
    master_cfg[0].transaction_coverage_enable = 1;
    master_cfg[1].transaction_coverage_enable = 1;
    master_cfg[2].transaction_coverage_enable = 1;
    master_cfg[3].transaction_coverage_enable = 1;

    // UVM RAL adapater enabling
    master_cfg[0].uvm_reg_enable= 1;

    // AXI VIP Slave 0 -> LS HP Master Interface
    // slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    // `ifdef AI_CORE_TOP_ENV_CHECK
    // slave_cfg[0].is_active     = 0;
    // `else
    // slave_cfg[0].is_active     = 1;
    // `endif
    // slave_cfg[0].data_width = 512;
    // slave_cfg[0].addr_width = 36;
    // slave_cfg[0].id_width   = 6;

    // AXI VIP Slave 0 -> LS MVM_IFD0 Master Interface
    slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    slave_cfg[0].tdata_width   = 512;
    slave_cfg[0].is_active     = 0;
    slave_cfg[0].tkeep_enable  = 0;
    slave_cfg[0].tstrb_enable  = 0;
    slave_cfg[0].tid_enable    = 0;
    slave_cfg[0].tdest_enable  = 0;
    slave_cfg[0].tuser_enable  = 0;

    // AXI VIP Slave 1 -> LS MVM_IFD1 Master Interface
    slave_cfg[1].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    slave_cfg[1].tdata_width   = 512;
    slave_cfg[1].is_active     = 0;
    slave_cfg[1].tkeep_enable  = 0;
    slave_cfg[1].tstrb_enable  = 0;
    slave_cfg[1].tid_enable    = 0;
    slave_cfg[1].tdest_enable  = 0;
    slave_cfg[1].tuser_enable  = 0;

    // AXI VIP Slave 2 -> LS MVM_IFD2 Master Interface
    slave_cfg[2].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    slave_cfg[2].tdata_width   = 512;
    slave_cfg[2].is_active     = 0;
    slave_cfg[2].tkeep_enable  = 0;
    slave_cfg[2].tstrb_enable  = 0;
    slave_cfg[2].tid_enable    = 0;
    slave_cfg[2].tdest_enable  = 0;
    slave_cfg[2].tuser_enable  = 0;

    // AXI VIP Slave 3 -> LS MVM_IFDW Master Interface
    slave_cfg[3].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    slave_cfg[3].tdata_width   = 512;
    slave_cfg[3].is_active     = 0;
    slave_cfg[3].tkeep_enable  = 0;
    slave_cfg[3].tstrb_enable  = 0;
    slave_cfg[3].tid_enable    = 0;
    slave_cfg[3].tdest_enable  = 0;
    slave_cfg[3].tuser_enable  = 0;

    // AXI VIP Slave 4 -> LS DWPU_IFD0 Master Interface
    slave_cfg[4].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    slave_cfg[4].tdata_width   = 512;
    slave_cfg[4].is_active     = 0;
    slave_cfg[4].tkeep_enable  = 0;
    slave_cfg[4].tstrb_enable  = 0;
    slave_cfg[4].tid_enable    = 0;
    slave_cfg[4].tdest_enable  = 0;
    slave_cfg[4].tuser_enable  = 0;

    // AXI VIP Slave 5 -> LS DWPU_IFD1 Master Interface
    slave_cfg[5].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    slave_cfg[5].tdata_width   = 512;
    slave_cfg[5].is_active     = 0;
    slave_cfg[5].tkeep_enable  = 0;
    slave_cfg[5].tstrb_enable  = 0;
    slave_cfg[5].tid_enable    = 0;
    slave_cfg[5].tdest_enable  = 0;
    slave_cfg[5].tuser_enable  = 0;

    // Disable protocol checkers
    slave_cfg[0].protocol_checks_enable = 1;
    slave_cfg[1].protocol_checks_enable = 1;
    slave_cfg[2].protocol_checks_enable = 1;
    slave_cfg[3].protocol_checks_enable = 1;
    slave_cfg[4].protocol_checks_enable = 1;
    slave_cfg[5].protocol_checks_enable = 1;

    // Transaction coverage
    slave_cfg[0].transaction_coverage_enable = 0;
    slave_cfg[1].transaction_coverage_enable = 0;
    slave_cfg[2].transaction_coverage_enable = 0;
    slave_cfg[3].transaction_coverage_enable = 0;
    slave_cfg[4].transaction_coverage_enable = 0;
    slave_cfg[5].transaction_coverage_enable = 0;

    set_addr_range(0, 36'h0, 36'hf_ffff_ffff);

  endfunction
endclass
`endif  //GUARD_AIC_DMC_AXI_SYSTEM_CFG_SV
