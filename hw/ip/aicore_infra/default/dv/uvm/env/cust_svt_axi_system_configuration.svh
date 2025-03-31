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

    // Create a 4(3HP+1LP) AXI master agent
    this.num_masters = `MST_NUM;
    this.num_slaves  = `SLV_NUM;
    this.system_monitor_enable  = 1;
    this.display_summary_report = 1;
      
    // Disable timeout on ready
    this.awready_watchdog_timeout = 0;
    this.wready_watchdog_timeout  = 100000;
    this.rready_watchdog_timeout  = 100000;
    // Disable timeout on ready response for streams
    this.tready_watchdog_timeout  = 0;
    // Disable timeout on axi interface idle
    this.bus_inactivity_timeout   = 0;

    this.allow_slaves_with_overlapping_addr = 1;
    //*************************************************************************************************************
    //Setting generic local address for slaves, this allows AXI's system_monitor_enable = 1 without addr errors
    //The valid addr ranges for each slave should be checked
    foreach (slaves_cfg[i])
      this.set_addr_range(i  , 'h0 , 'hFF_FFFF_FFFF );
    //*************************************************************************************************************


    // Create port configurations
    this.create_sub_cfgs(this.num_masters, this.num_slaves);
    // LT M0
    foreach (master_cfg[i]) begin
      this.master_cfg[i].axi_interface_type       = svt_axi_port_configuration::AXI4;
      this.master_cfg[i].data_width               = 64;
      this.master_cfg[i].addr_width               = 40;
      this.master_cfg[i].id_width                 = 6;
      this.master_cfg[i].write_addr_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].write_data_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].write_resp_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].read_addr_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.master_cfg[i].read_data_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
    end

    foreach (slave_cfg[i]) begin
      this.slave_cfg[i].axi_interface_type       = svt_axi_port_configuration::AXI4;
      this.slave_cfg[i].is_active                = slaves_cfg[i].is_active;
      this.slave_cfg[i].data_width               = slaves_cfg[i].data_width;
      this.slave_cfg[i].addr_width               = slaves_cfg[i].addr_width;
      this.slave_cfg[i].id_width                 = slaves_cfg[i].id_width;
      this.slave_cfg[i].write_addr_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].write_data_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].write_resp_chan_idle_val = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].read_addr_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
      this.slave_cfg[i].read_data_chan_idle_val  = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;

    end

  endfunction

endclass
`endif //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
