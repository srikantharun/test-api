`ifndef CC_CLK_DIV_AGENT_IF_SV
`define CC_CLK_DIV_AGENT_IF_SV

interface cc_clk_div_agent_if (input clk);
  logic reset_n;
  
  logic [aic_common_pkg::AIC_PHASE_ACC_WIDTH-1:0] incr   ;
  logic                                   enable ;
  logic                                   clear  ;
  logic                                   cg_en  ;

  clocking mon @(posedge clk);
    input incr   ;
    input enable ;
    input clear  ;
    input cg_en  ;
  endclocking

  clocking drv @(posedge clk);
    output incr   ;
    output enable ;
    output clear  ;
    input  cg_en  ;
  endclocking

endinterface : cc_clk_div_agent_if

`endif // CC_CLK_DIV_AGENT_IF_SV

