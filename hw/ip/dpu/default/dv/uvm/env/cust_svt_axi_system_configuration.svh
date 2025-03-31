// *****************************************************************************************
// Description: Class cust_svt_axi_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
`define SLAVE_AGENT
//`define ENABLE_COMPLEX_MEMORY_MAP_FEATURE

`ifndef GUARD_AI_CORE_DPU_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
`define GUARD_AI_CORE_DPU_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
// Class
class cust_svt_axi_system_configuration extends svt_axi_system_configuration;

  svt_axi_port_configuration ai_core_dpu_axi_port_cfg;
  // Factory registration
  `uvm_object_utils (cust_svt_axi_system_configuration)

  // Class Constructor
  function new (string name = "cust_svt_axi_system_configuration");
    super.new(name);
    ai_core_dpu_axi_port_cfg = svt_axi_port_configuration::type_id::create("ai_core_dpu_axi_port_cfg");


    this.num_masters = 3;
    this.num_slaves  = 1;
    this.system_monitor_enable  = 0;
    this.display_summary_report = 1;
    this.tready_watchdog_timeout = 0;

    this.create_sub_cfgs(this.num_masters, this.num_slaves);


    // AXi Config IF
    this.master_cfg[0].axi_interface_type     = svt_axi_port_configuration::AXI4; // AXi Config IF
    this.master_cfg[0].data_width             = 64;
    this.master_cfg[0].addr_width             = 36;
    this.master_cfg[0].id_width               = 4;
    this.master_cfg[0].uvm_reg_enable         = 1;
    this.master_cfg[0].is_active              = 1;
    this.master_cfg[0].protocol_checks_enable = 1;
    this.master_cfg[0].num_outstanding_xact   = 100;

    // AXI hp (coeff) IF
    this.slave_cfg[0].axi_interface_type      = svt_axi_port_configuration::AXI4_STREAM; // ODR Axi Stream
    this.slave_cfg[0].is_active               = 1;
    this.slave_cfg[0].tdata_width             = 512;
    this.slave_cfg[0].id_width                = 4;
    this.slave_cfg[0].tkeep_enable           = 0;
    this.slave_cfg[0].tstrb_enable           = 0;
    this.slave_cfg[0].tid_enable             = 0;
    this.slave_cfg[0].tdest_enable           = 0;
    this.slave_cfg[0].tuser_enable           = 0;
    this.slave_cfg[0].default_tready         = 1; 
    this.slave_cfg[0].protocol_checks_enable = 1;



    // IAU AXI Stream
    this.master_cfg[1].axi_interface_type     = svt_axi_port_configuration::AXI4_STREAM; // IAU AXI Stream
    this.master_cfg[1].tdata_width            = 2048;
    this.master_cfg[1].is_active              = 1;
    this.master_cfg[1].protocol_checks_enable = 1;
    this.master_cfg[1].tkeep_enable           = 0;
    this.master_cfg[1].tstrb_enable           = 0;
    this.master_cfg[1].tid_enable             = 0;
    this.master_cfg[1].tdest_enable           = 0;
    this.master_cfg[1].tuser_enable           = 0;

    // IFD AXI Stream
    this.master_cfg[2].axi_interface_type     = svt_axi_port_configuration::AXI4_STREAM; // IFD AXI Stream
    this.master_cfg[2].tdata_width            = 512;
      this.master_cfg[2].is_active              = 1;
    this.master_cfg[2].tkeep_enable           = 0;
    this.master_cfg[2].tstrb_enable           = 0;
    this.master_cfg[2].tid_enable             = 0;
    this.master_cfg[2].tdest_enable           = 0;
    this.master_cfg[2].tuser_enable           = 0;
    this.master_cfg[2].protocol_checks_enable = 1;

    this.tready_watchdog_timeout              = 0;
    `ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
      this.enable_complex_memory_map = 1;
    `else
      this.set_addr_range(0, 36'h0, 36'hf_ffff_ffff);
    `endif



  endfunction

  `ifdef ENABLE_COMPLEX_MEMORY_MAP_FEATURE
    function bit get_dest_slave_addr_from_global_addr (input bit [`SVT_AXI_MAX_ADDR_WIDTH-1:0] global_addr,
                                                       input bit [`SVT_AMBA_MEM_MODE_WIDTH-1:0] mem_mode = 0,
                                        input svt_axi_transaction xact);

      begin

        //the transactions are always routed to slave port 0. The below statement indciates the routing info of interconnect.
        slave_port_ids[0]=0;

        //no addr translation. The below statement indicates any addr translation performed by interconnect.
        slave_addr = global_addr; //note that global_addr will be tagged with the non-secure bit if address tagging is enabled.

        //return 1
        get_dest_slave_addr_from_global_addr=1;

        //the below items can be used when applicable. In this example, they are not applicable

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

      end
    endfunction
  `endif

endclass
`endif //GUARD_AI_CORE_DPU_CUST_SVT_AXI_SYSTEM_CONFIGURATION_SV
