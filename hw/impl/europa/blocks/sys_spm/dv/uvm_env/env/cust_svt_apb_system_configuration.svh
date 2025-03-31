`ifndef GUARD_CUST_SYS_SPM_SVT_APB_SYSTEM_CONFIG_SV
`define GUARD_CUST_SYS_SPM_SVT_APB_SYSTEM_CONFIG_SV
// Class
class cust_sys_spm_svt_apb_system_configuration extends svt_apb_system_configuration;

  // Factory registration
  `uvm_object_utils (cust_sys_spm_svt_apb_system_configuration)

  // Class Constructor
  function new (string name = "cust_sys_spm_svt_apb_system_configuration");
  
    super.new(name);
     this.num_slaves = 1;
     this.paddr_width = 32;
     this.pdata_width = 32;
  endfunction

endclass
`endif //GUARD_CUST_SYS_SPM_SVT_APB_SYSTEM_CONFIG_SV
