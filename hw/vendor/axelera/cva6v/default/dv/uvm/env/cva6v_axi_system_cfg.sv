// *****************************************************************************************
// Description: Class cva6v_axi_system_cfg is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************
`ifndef GUARD_CVA6V_AXI_SYSTEM_CFG_SV
`define GUARD_CVA6V_AXI_SYSTEM_CFG_SV
// Class
class cva6v_axi_system_cfg extends svt_axi_system_configuration;

  // Factory registration
  `uvm_object_utils(cva6v_axi_system_cfg)

  // Class Constructor
  function new(string name = "cva6v_axi_system_cfg");
    super.new(name);

    // Number of master/slave agents
    num_masters = 0;
    num_slaves  = 1;
    system_monitor_enable = 0;
    display_summary_report = 1;

    // Create port configurations
    create_sub_cfgs(0, 1);

    // AXI VIP Slave 0 -> CVA6V Master Interface
    // slave_cfg[0].ace_version = svt_axi_port_configuration::ACE_VERSION_2_0; for AXI5

    slave_cfg[0].axi_interface_type = svt_axi_port_configuration::AXI4;
    slave_cfg[0].is_active  = 1;
    slave_cfg[0].data_width = 64;
    slave_cfg[0].addr_width = 36; // to avoid UVM warning. but top level supports 40-bits
    slave_cfg[0].id_width   = 4;

    set_addr_range(0, 40'h0, 40'hff_ffff_ffff);

  endfunction
endclass
`endif  //GUARD_AI_CORE_LS_AXI_SYSTEM_CFG_SV
