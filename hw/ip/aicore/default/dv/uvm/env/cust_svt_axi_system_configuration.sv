// *****************************************************************************************
// Description: Class cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
`define SLAVE_AGENT
//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE
`define NUM_OF_MASTERS 1
`ifndef GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
`define GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
// Class
class cust_svt_axi_system_configuration extends svt_axi_system_configuration;

  // Factory registration
  `uvm_object_utils (cust_svt_axi_system_configuration)

  // Class Constructor
  function new (string name = "cust_svt_axi_system_configuration");
    super.new(name);

    // Create a signle AXI master agent
    this.num_masters = `NUM_OF_MASTERS;
   `ifdef SLAVE_AGENT
    this.num_slaves = 1;
    this.system_monitor_enable = 0;
    this.display_summary_report = 1;
    // svt_axi_system_configuration::display_summary_report
   `else
    this.num_slaves = 0;
    this.system_monitor_enable = 0;
   `endif
    // Create port configurations
    this.create_sub_cfgs(num_masters,num_slaves);
    this.wready_watchdog_timeout= 10000;
    this.bus_inactivity_timeout=600000;

    // AXI Master 0
    this.master_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    this.master_cfg[0].data_width = 64;
    this.master_cfg[0].addr_width = 40;
    this.master_cfg[0].id_width   = 6; 
    // Disable protocol checkers
    this.master_cfg[0].protocol_checks_enable = 1;
    this.master_cfg[0].uvm_reg_enable= 1;
    this.master_cfg[0].num_outstanding_xact= 100;

  
   `ifdef SLAVE_AGENT
    // AXI Slave 0 //ht
    this.slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    this.slave_cfg[0].is_active  = 1;
    this.slave_cfg[0].data_width = 512;
    this.slave_cfg[0].addr_width = 40;
    this.slave_cfg[0].id_width   = 9;
    this.slave_cfg[0].protocol_checks_enable = 1;
   `endif

    //// Enable protocol file generation for protocol analyzer
    //this.master_cfg[0].enable_xml_gen = 1;
    //this.master_cfg[0].pa_format_type = svt_xml_writer::FSDB;
    this.master_cfg[0].transaction_coverage_enable = 1;

    //for interleaving following configurations are needed
   `ifdef INTERLEAVING_ENABLED
    this.master_cfg[0].reordering_algorithm = svt_axi_port_configuration::ROUND_ROBIN;
    this.slave_cfg[0].reordering_algorithm = svt_axi_port_configuration::ROUND_ROBIN;
    this.slave_cfg[0].read_data_interleave_size = 2;
    this.slave_cfg[0].read_data_reordering_depth = 5;
    this.slave_cfg[1].reordering_algorithm = svt_axi_port_configuration::ROUND_ROBIN;
    this.slave_cfg[1].read_data_interleave_size = 2;
    this.slave_cfg[1].read_data_reordering_depth = 5;
    this.master_cfg[0].read_data_interleave_size = 2;
    this.master_cfg[0].read_data_reordering_depth = 5;
    //this.slave_cfg[0].write_resp_reordering_depth= 256;
   `endif

   `ifdef SLAVE_AGENT
    this.slave_cfg[0].transaction_coverage_enable = 0;
   `endif

    /** Enable/Disable transaction level coverage */
    this.master_cfg[0].transaction_coverage_enable = 0;
    //this.master_cfg[0].??? = svt_axi_port_configuration::memory_update_for_read_xacts_enable;
    //this.master_cfg[0].reordering_algorithm        = svt_axi_port_configuration::RANDOM;
    //this.master_cfg[0].write_resp_reordering_depth = `SVT_AXI_MAX_WRITE_RESP_REORDERING_DEPTH;
   `ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
    this.enable_complex_memory_map=1;
   `else
    this.allow_slaves_with_overlapping_addr = 1;
    this.set_addr_range(0,40'h0,40'hff_ffff_ffff); //slave zero
   `endif
  endfunction

   `ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
    function bit get_dest_slave_addr_from_global_addr (input bit [`SVT_AXI_MAX_ADDR_WIDTH-1:0] global_addr,
                                                       input bit [`SVT_AMBA_MEM_MODE_WIDTH-1:0] mem_mode = 0,
                                                       input string requester_name ="",
                                                       input bit ignore_unmapped_addr = 0,
                                                       output bit is_register_addr_space ,
                                                       output int slave_port_ids [$],
                                                       output bit [`SVT_AXI_MAX_ADDR_WIDTH-1:0] slave_addr ,
                                                       input svt_axi_transaction xact);
      begin

        //the transactions are always routed to slave port 0. The below statement indciates the routing info of interconnect.
        slave_port_ids[0]=0;

        //no addr translation. The below statement indicates any addr translation performed by interconnect.
        slave_addr = global_addr; //note that global_addr will be tagged with the non-secure bit if address tagging is enabled.

        //return 1
        get_dest_slave_addr_from_global_addr=1;

        //the below items can be used when applicable. In this example, they are not applicable
        /*
        * if(xact.port_cfg.port_id == 0 || xact.port_cfg.port_id == 1) begin //transactions from master[0] and master[1] will be routed to slave 0
           slave_port_ids[0]=0;
        end
        else if(xact.port_cfg.port_id == 2 || xact.port_cfg.port_id == 3) begin //transactions from master[2] and master[3] will be routed to slave 1
          slave_port_ids[0]=1;
        end

        //register transactions that terminates within the interconnect have to be specified using:
        if(global_addr>=reg_space_start_addr && global_addr<=reg_space_end_addr) begin
          is_register_addr_space=1;
          slave_port_ids[0]=-1;
          get_dest_slave_addr_from_global_addr=1;
        end
        */
      end
    endfunction
  `endif

endclass
`endif //GUARD_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
