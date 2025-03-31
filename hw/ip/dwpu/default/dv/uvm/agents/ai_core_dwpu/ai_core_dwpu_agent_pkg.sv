
package ai_core_dwpu_agent_pkg;

  `include "uvm_macros.svh"
  //`include "../../common/ai_core_dwpu_common_pkg.sv"
  import uvm_pkg::*;
  import  aic_common_pkg::*;
  import ai_core_dwpu_common_pkg::*;
  


  //Defines///////////////////////////
  localparam OBS_W   = aic_common_pkg::AIC_DEV_OBS_DW;
  localparam CID_W   = aic_common_pkg::AIC_CID_SUB_W;

  // DWPU Components
  `include "ai_core_dwpu_seq_item.svh"
  `include "ai_core_dwpu_monitor.svh"
  `include "ai_core_dwpu_agent.svh"

endpackage : ai_core_dwpu_agent_pkg

