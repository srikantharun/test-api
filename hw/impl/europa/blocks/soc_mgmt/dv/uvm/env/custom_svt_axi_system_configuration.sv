// *****************************************************************************************
// Description: Class cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
`define SLAVE_AGENT
//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE

`ifndef GUARD_CUSTOM_SVT_AXI_SYSTEM_CONFIGURATION_SV
`define GUARD_CUSTOM_SVT_AXI_SYSTEM_CONFIGURATION_SV
// Class
class custom_svt_axi_system_configuration extends svt_axi_system_configuration;

  bit b2b;

  // Factory registration
  `uvm_object_utils(custom_svt_axi_system_configuration)

  // Class Constructor
  function new(string name = "custom_svt_axi_system_configuration");
    super.new(name);


    // Create a signle AXI master agent
    this.num_masters = 3;
`ifdef SLAVE_AGENT
    this.num_slaves = 1;
    this.system_monitor_enable = 0;
    this.display_summary_report = 1;
    // svt_axi_system_configuration::display_summary_report
`else
    this.num_slaves = 0;
    this.system_monitor_enable = 0;
`endif
    // Disable timeout on ready
    this.awready_watchdog_timeout=0;
    // Disable timeout on ready response for streams
    this.tready_watchdog_timeout = 0;
    // Disable timeout on axi interface idle
    this.bus_inactivity_timeout = 0;
    // Create port configurations
    this.create_sub_cfgs(3, 1);
    // AXI Master 0 LP interface
    this.master_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    this.master_cfg[0].uvm_reg_enable= 1;
    this.master_cfg[0].data_width = 32; //need to change as per spec
    this.master_cfg[0].addr_width = 32; //need to change as per spec
    this.master_cfg[0].id_width   = 9;
    this.master_cfg[0].protocol_checks_enable = 1;
    this.master_cfg[0].transaction_coverage_enable = 1;
    if($test$plusargs("B2B_TEST")) begin
        $value$plusargs("B2B_TEST=%0d",b2b);
        this.master_cfg[0].num_outstanding_xact   = 20;
    end    


`ifdef SLAVE_AGENT
    // AXI Slave 0
`endif

`ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
    this.enable_complex_memory_map = 1;
`else
    this.set_addr_range(0, 28'h0, 28'hfff_ffff);
`endif
  endfunction

`ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
  function bit get_dest_slave_addr_from_global_addr(
      input bit [`SVT_AXI_MAX_ADDR_WIDTH-1:0] global_addr,
      input bit [`SVT_AMBA_MEM_MODE_WIDTH-1:0] mem_mode = 0, input string requester_name = "",
      input bit ignore_unmapped_addr = 0, output bit is_register_addr_space,
      output int slave_port_ids[$], output bit [`SVT_AXI_MAX_ADDR_WIDTH-1:0] slave_addr,
      input svt_axi_transaction xact);
    begin

      //the transactions are always routed to slave port 0. The below statement indciates the routing info of interconnect.
      slave_port_ids[0] = 0;

      //no addr translation. The below statement indicates any addr translation performed by interconnect.
      slave_addr = global_addr; //note that global_addr will be tagged with the non-secure bit if address tagging is enabled.

      //return 1
      get_dest_slave_addr_from_global_addr = 1;

    end
  endfunction
`endif

endclass
`endif  //GUARD_CUSTOM_SVT_AXI_SYSTEM_CONFIGURATION_SV
