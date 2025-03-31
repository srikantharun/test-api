`ifndef AI_CORE_DWPU_IF
`define AI_CORE_DWPU_IF

interface ai_core_dwpu_if (input clk);
  //Defines//
  localparam OBS_W   = aic_common_pkg::AIC_DEV_OBS_DW;
  localparam CID_W   = aic_common_pkg::AIC_CID_SUB_W;

  logic reset_an_i;
  logic irq_o;
  logic [OBS_W-1:0] obs_o;
  logic [CID_W-1:0] cid_i;
  logic trace_vld_o;

  clocking mon @(posedge clk);
    input reset_an_i;
    input irq_o;
    input obs_o;
    input cid_i;
    input trace_vld_o;
  endclocking

endinterface

`endif

