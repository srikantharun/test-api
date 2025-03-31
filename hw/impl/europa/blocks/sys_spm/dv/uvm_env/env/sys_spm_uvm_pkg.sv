`define AXI_VIP
`define APB_VIP
// SPM UVM package
package sys_spm_uvm_pkg;

  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import spm_uvm_pkg::*;

  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
  import svt_apb_uvm_pkg::*;

   // Environment and environment Configurations
  `include "apb_virtual_sequencer.svh"
  `include "cust_svt_apb_system_configuration.svh"
  `include "sys_spm_env.svh"




endpackage
