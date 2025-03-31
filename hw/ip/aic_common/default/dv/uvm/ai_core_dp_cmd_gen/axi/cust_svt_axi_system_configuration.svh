// *****************************************************************************************
// Description: Class cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
`ifndef GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SVH
`define GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SVH


// Class
class cust_svt_axi_system_configuration extends svt_axi_system_configuration;

  // Factory registration
    `uvm_object_utils (cust_svt_axi_system_configuration)

    // Class Constructor
    function new (string name = "cust_svt_axi_system_configuration");
        super.new(name);

        // Create a signle AXI master agent
        this.num_masters           = 1;
        this.num_slaves            = 0;
        this.system_monitor_enable = 0;

        // Disable timeout on ready response for streams
        this.tready_watchdog_timeout = 0;

        // Create port configurations
        this.create_sub_cfgs(this.num_masters, this.num_slaves);

        // AXI Master 0
        this.master_cfg[0].axi_interface_type     = svt_axi_port_configuration::AXI4; 
        this.master_cfg[0].is_active              = 1;
        this.master_cfg[0].addr_width             = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
        this.master_cfg[0].data_width             = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
        this.master_cfg[0].id_width               = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH;
        this.master_cfg[0].uvm_reg_enable         = 0;
        this.master_cfg[0].protocol_checks_enable = 1;
        this.master_cfg[0].num_outstanding_xact   = 100;  // A big number 

    endfunction

endclass
`endif //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SVH
