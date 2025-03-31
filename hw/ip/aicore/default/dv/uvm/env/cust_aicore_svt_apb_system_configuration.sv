`ifndef GUARD_CUST_AICORE_SVT_APB_SYSTEM_CONFIG_SV
`define GUARD_CUST_AICORE_SVT_APB_SYSTEM_CONFIG_SV
// Class
class cust_aicore_svt_apb_system_configuration extends svt_apb_system_configuration;

  // Factory registration
  `uvm_object_utils (cust_aicore_svt_apb_system_configuration)

  // Class Constructor
  function new (string name = "cust_aicore_svt_apb_system_configuration");
  
    super.new(name);
    this.paddr_width = svt_apb_system_configuration::PADDR_WIDTH_16;
    this.pdata_width = svt_apb_system_configuration::PDATA_WIDTH_32;
    this.apb4_enable = 1;
    this.is_active=1; 
    this.num_slaves=0;
  endfunction

    /**
   * Checks to see that the data field values are valid, mainly making sure the
   * master and slave interface specifications are consistent. 
   */
  virtual function bit is_valid(bit silent = 1, int kind = -1);
    is_valid = 1;

    if (!super.is_valid()) begin
      if (!silent) begin
        `uvm_info("is_valid", $sformatf("Invalid Master configuration. Contents:\n%s", this.sprint()), UVM_HIGH)
      end
      is_valid = 0;   
    end 
  endfunction


endclass

  




`endif //GUARD_CUST_AICORE_SVT_APB_SYSTEM_CONFIG_SV
