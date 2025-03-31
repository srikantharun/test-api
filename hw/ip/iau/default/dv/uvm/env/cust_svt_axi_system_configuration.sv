// *****************************************************************************************
// Description: Class cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate 
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are 
// required by System agent
// *****************************************************************************************
`define SLAVE_AGENT
//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE

`ifndef GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
`define GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
// Class
class cust_svt_axi_system_configuration extends svt_axi_system_configuration;

  // Factory registration
  `uvm_object_utils (cust_svt_axi_system_configuration)

  // Class Constructor
  function new (string name = "cust_svt_axi_system_configuration");
    super.new(name);

    
    this.num_masters           = 2;
    this.num_slaves            = 1;
    this.system_monitor_enable = 0;
 
    // Disable timeout on ready response for streams
    this.tready_watchdog_timeout = 0;

 
    this.create_sub_cfgs(this.num_masters, this.num_slaves);
    // AXi Config IF
    this.master_cfg[0].axi_interface_type     = svt_axi_port_configuration::AXI4; 
    this.master_cfg[0].is_active              = 1;
    this.master_cfg[0].addr_width             = 28;
    this.master_cfg[0].data_width             = 64;
    this.master_cfg[0].id_width               = 4;
    this.master_cfg[0].uvm_reg_enable         = 1;
    this.master_cfg[0].protocol_checks_enable = 1;
    this.master_cfg[0].num_outstanding_xact   = 100; 
    
    // AXI AXI STREAM
    this.master_cfg[1].axi_interface_type     = svt_axi_port_configuration::AXI4_STREAM;
    this.master_cfg[1].is_active              = 1;
    this.master_cfg[1].tdata_width            = 1664;
    this.master_cfg[1].tkeep_enable           = 0;
    this.master_cfg[1].tstrb_enable           = 0;
    this.master_cfg[1].tid_enable             = 0;
    this.master_cfg[1].tdest_enable           = 0;
    this.master_cfg[1].tuser_enable           = 0;
    this.master_cfg[1].protocol_checks_enable = 1;

    this.slave_cfg[0].axi_interface_type     = svt_axi_port_configuration::AXI4_STREAM;
    this.slave_cfg[0].is_active              = 1;
    this.slave_cfg[0].tdata_width            = 2048;
    this.slave_cfg[0].tkeep_enable           = 0;
    this.slave_cfg[0].tstrb_enable           = 0;
    this.slave_cfg[0].tid_enable             = 0;
    this.slave_cfg[0].tdest_enable           = 0;
    this.slave_cfg[0].tuser_enable           = 0;
    this.slave_cfg[0].default_tready         = 1; 
    this.slave_cfg[0].protocol_checks_enable = 1;
  endfunction
endclass
`endif //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
