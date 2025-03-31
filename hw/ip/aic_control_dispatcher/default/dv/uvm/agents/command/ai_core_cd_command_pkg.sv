
package ai_core_cd_command_pkg;

  `include "uvm_macros.svh"
  //`include "../../common/ai_core_cd_common_pkg.sv"
  import uvm_pkg::*;
  import aic_common_pkg::*;
  import ai_core_cd_common_pkg::*;
  import axe_uvm_resource_allocator_pkg::*;
  `ifdef AXI_VIP
    import svt_uvm_pkg::*;
    import svt_axi_uvm_pkg::*;
  `endif
  

  // DWPU Components
  `include "ai_core_cd_command.svh"
  `include "ai_core_cd_instructions.svh"
  //`include "ai_core_cd_command_seq_base.svh"
  `include "ai_core_cd_mem_model.svh"
  `include "ai_core_cd_mem_manager.svh"
  `include "cust_svt_axi_monitor_callback.svh"

endpackage : ai_core_cd_command_pkg

