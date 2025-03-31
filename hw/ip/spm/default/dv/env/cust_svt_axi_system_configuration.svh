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
    `uvm_object_utils (cust_svt_axi_system_configuration)

    spm_config_t spm_config;

    bit expect_ecc_error;

    logic [`SVT_AXI_MAX_ADDR_WIDTH-1:0] addr_range;

    // Class Constructor
    function new (string name = "cust_svt_axi_system_configuration");
        super.new(name);

        if(!uvm_config_db #(spm_config_t)::get(uvm_root::get(), "", "spm_config", spm_config))
                `uvm_fatal(get_full_name(), "no spm config found");

        if(!uvm_config_db #(bit)::get(uvm_root::get(), "", "expect_ecc_error", expect_ecc_error)) begin
                `uvm_info(get_full_name(), "no expect error found, setting to 0", UVM_NONE);
                expect_ecc_error = 0;
        end

        addr_range = (1<<spm_config.spm_axi_data_width) - 1;

        // Creating an acntive master and a passive slave, enabling the system monitor
        this.num_masters = 1;
        this.num_slaves = 1;
        this.system_monitor_enable = 1;

        // Create port configurations
        this.create_sub_cfgs(this.num_masters, this.num_slaves);
        this.wready_watchdog_timeout = 10000;

        this.master_slave_xact_data_integrity_check_enable = 1;
        this.set_addr_range(0, 0, addr_range);

        // AXI Master 0
        this.master_cfg[0].is_active = 1;
        this.master_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
        this.master_cfg[0].data_width = spm_config.spm_axi_data_width;
        this.master_cfg[0].addr_width = spm_config.spm_axi_addr_width;
        this.master_cfg[0].id_width   = spm_config.spm_axi_id_width;
        // Disable protocol checkers
        this.master_cfg[0].protocol_checks_enable = 1;
        this.master_cfg[0].uvm_reg_enable = 0;
        this.master_cfg[0].num_outstanding_xact = 100;

        this.master_cfg[0].default_bready = 1;
        this.master_cfg[0].default_rready = 1;

        this.master_cfg[0].wysiwyg_enable = 1;

        // do not drive X while idle
        this.master_cfg[0].write_addr_chan_idle_val       = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
        this.master_cfg[0].write_data_chan_idle_val       = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
        this.master_cfg[0].write_resp_chan_idle_val       = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
        this.master_cfg[0].read_addr_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;
        this.master_cfg[0].read_data_chan_idle_val        = svt_axi_port_configuration::INACTIVE_CHAN_LOW_VAL;


        /** Enable/Disable transaction level coverage */
        this.master_cfg[0].transaction_coverage_enable = 0;


        // AXI Slave 0
        this.slave_cfg[0].is_active = 0;
        this.slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
        this.slave_cfg[0].data_width = spm_config.spm_axi_data_width;
        this.slave_cfg[0].addr_width = spm_config.spm_axi_addr_width;
        this.slave_cfg[0].id_width   = spm_config.spm_axi_id_width;
        this.slave_cfg[0].wysiwyg_enable = 0;
        this.slave_cfg[0].num_outstanding_xact = 100;
        this.slave_cfg[0].memory_update_for_read_xact_enable = expect_ecc_error; //ecc pass fail
    endfunction

endclass
`endif //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
