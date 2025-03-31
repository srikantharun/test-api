// Manually created RAL model package for Soc Management 
package soc_mgmt_ral_pkg;
  // Packages import
  import uvm_pkg::*;
  // Macro includes
  `include "uvm_macros.svh"
  import dv_base_reg_pkg::*;

  // Manually created RAL model block for Soc Management
  class soc_mgmt_reg_block extends dv_base_reg_block;
    // Registration with factory
    `uvm_object_utils(soc_mgmt_reg_block)
    // RAL models objects
    // Reg map object
    uvm_reg_map soc_mgmt_map;

    // Class construcotr
    function new(string name = "soc_mgmt_reg_block");
      super.new(name);
    endfunction: new

   // Provide build function to supply base addr
   function void build(uvm_reg_addr_t base_addr, csr_excl_item csr_excl = null);

      // Map definition
      soc_mgmt_map = create_map(base_addr, 0, 8, UVM_LITTLE_ENDIAN, 0);
      default_map    = soc_mgmt_map;


      // soc_mgmt CSR RAL model Build
   endfunction : build
  endclass : soc_mgmt_reg_block

endpackage:soc_mgmt_ral_pkg
