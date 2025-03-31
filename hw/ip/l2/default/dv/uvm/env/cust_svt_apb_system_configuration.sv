// *****************************************************************************************
// Description: Class cust_svt_apb_system_configuration is used to encapsulate all the
// configuration information.  It extends the system configuration and sets the appropriate
// fields like number of masters/slaves. Createmaster/slave configurations etc, which are
// required by System agent
// *****************************************************************************************

`ifndef GUARD_CUST_SVT_APB_SYSTEM_CONFIGURATION_SV
`define GUARD_CUST_SVT_APB_SYSTEM_CONFIGURATION_SV
// Class
class cust_svt_apb_system_configuration extends svt_apb_system_configuration;

  // Factory registration
  `uvm_object_utils (cust_svt_apb_system_configuration)

  // Class Constructor
  function new (string name = "cust_svt_apb_system_configuration");
    super.new(name);
    this.master_cfg.uvm_reg_enable= 1;
    this.master_cfg.pdata_width = PDATA_WIDTH_32;
    //this.master_cfg.paddr_width = PADDR_WIDTH_32;

    endfunction

endclass
`endif //GUARD_CUST_SVT_APB_SYSTEM_CONFIGURATION_SV
