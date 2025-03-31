// *****************************************************************************************
// Description: Class dwpu_cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE

`ifndef AI_CORE_CD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
`define AI_CORE_CD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
// Class
class ai_core_cd_cust_svt_axi_system_configuration extends svt_axi_system_configuration;

  // Factory registration
  `uvm_object_utils(ai_core_cd_cust_svt_axi_system_configuration)

  // Class Constructor
  function new(string name = "ai_core_cd_cust_svt_axi_system_configuration");
    super.new(name);


    // Create a signle AXI master agent
    this.num_masters = 1;
    this.num_slaves = 1;
    this.system_monitor_enable = 0; //ToDO: consider enabling this option for specific checks 
    this.display_summary_report = 1;
    // svt_axi_system_configuration::display_summary_report
    // Disable timeout on ready
    this.awready_watchdog_timeout=0;
    // Disable timeout on ready response for streams
    //this.tready_watchdog_timeout = 0;
    // Disable timeout on axi interface idle
    this.bus_inactivity_timeout = 0;

    // Create port configurations
    this.create_sub_cfgs(this.num_masters, this.num_slaves);
    // allow outstanding transactions to be greater than the command fifo depth
    this.master_cfg[0].num_outstanding_xact=10;   //
    // AXI Master 0 LP interface
    this.master_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    `ifdef AI_CORE_TOP_ENV_CHECK
      this.master_cfg[0].is_active     = 0;
    `else
      this.master_cfg[0].is_active     = 1;
    `endif
    this.master_cfg[0].uvm_reg_enable= 1;
    this.master_cfg[0].data_width = `ACD_M_AXI_DATA_WIDTH;
    this.master_cfg[0].addr_width = `ACD_M_AXI_ADDR_WIDTH;
    //this.master_cfg[0].id_width   = 9;  //ToDO: # UVM_WARNING /opt/synopsys/dware/eu001-1.0/vip/svt/amba_svt/S-2021.12/sverilog/src/mti/svt_axi_port_configuration.svp(7971) @ 0.000 ns: reporter [is_valid] Invalid id_width of 9 provided, must be inside { 0:8 } based on axi_interface_type(AXI4)
    this.master_cfg[0].id_width   = `ACD_S_AXI_ID_WIDTH; 
    this.master_cfg[0].protocol_checks_enable = 1;
    this.master_cfg[0].transaction_coverage_enable = 1;


    // AXI Slave 0
    //this.slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4_STREAM;
    this.slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    `ifdef AI_CORE_TOP_ENV_CHECK
      this.slave_cfg[0].is_active     = 0;
    `else
      this.slave_cfg[0].is_active     = 1;
    `endif
    //this.master_cfg[0].uvm_reg_enable= 1;
    this.slave_cfg[0].data_width = `ACD_S_AXI_DATA_WIDTH;
    this.slave_cfg[0].addr_width = `ACD_S_AXI_ADDR_WIDTH;
    this.slave_cfg[0].id_width   = `ACD_M_AXI_ID_WIDTH; 
    this.slave_cfg[0].protocol_checks_enable = 1;
    //this.slave_cfg[0].transaction_coverage_enable = 1;
    this.slave_cfg[0].transaction_coverage_enable = 0;
    //ToDO: what are the following options??
    //this.slave_cfg[0].tdata_width   = AXI_STREAM_IAU_DATA_WIDTH;
    this.slave_cfg[0].tkeep_enable  = 0;
    this.slave_cfg[0].tstrb_enable  = 0;
    this.slave_cfg[0].tid_enable    = 0;
    this.slave_cfg[0].tdest_enable  = 0;
    this.slave_cfg[0].tuser_enable  = 0;
    this.slave_cfg[0].protocol_checks_enable = 1;
    this.slave_cfg[0].default_tready = $urandom_range(1,0);

`ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
    this.enable_complex_memory_map = 1;
`else
    this.set_addr_range(0, 28'h0, 28'hfff_ffff);
    
    //this.set_addr_range(0, 28'h0, 28'h000_ffff);
    //this.set_addr_range(0, 28'h001_0000, 28'hfff_ffff, );
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
`endif  //AI_CORE_CD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
