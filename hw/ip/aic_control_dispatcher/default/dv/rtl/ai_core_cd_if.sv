`ifndef AI_CORE_CD_IF
`define AI_CORE_CD_IF

interface ai_core_cd_if (input clk);
  //Defines//
  //localparam PARAM   = aic_common_pkg::PKG_PARAM;

  logic reset_n_i;
  logic irq_o;

  clocking mon @(posedge clk);
    input reset_n_i;
    input irq_o;
  endclocking
endinterface


interface ai_core_cd_done_if (input clk);
  logic reset_n_i;
  logic [16:0] done_o;

  clocking mon @(posedge clk);
    input reset_n_i;
    input done_o;
  endclocking

  clocking drv @(posedge clk);
    input  reset_n_i;
    output done_o;
  endclocking
endinterface


interface ai_core_cd_tms_if (input clk);
  //Defines//
  //localparam PARAM   = aic_common_pkg::PKG_PARAM;

  logic reset_n_i;
  /// The id of the timestamp
  aic_cd_pkg::timestamp_trigger_id_t timestamp_id;
  /// The pulse that the timestamp is active
  logic                              timestamp_active_pulse;

  clocking mon @(posedge clk);
    input reset_n_i;
    input timestamp_id;
    input timestamp_active_pulse;
  endclocking
endinterface

`endif

