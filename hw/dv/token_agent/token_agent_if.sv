`ifndef TOKEN_AGENT_IF_SV
`define TOKEN_AGENT_IF_SV

interface token_agent_if (input clk);
  logic reset_n;
  //consumer signals
  logic tok_cons_rdy;
  logic tok_cons_vld;
  //producer signals
  logic tok_prod_vld;
  logic tok_prod_rdy;

  clocking mon @(posedge clk);
    input tok_cons_rdy;
    input tok_cons_vld;

    input tok_prod_vld;
    input tok_prod_rdy;
  endclocking

  clocking drv_mstr @(posedge clk);
    input   tok_cons_rdy;
    output  tok_cons_vld;
    input   tok_prod_vld;
    output  tok_prod_rdy;
  endclocking

  clocking drv_slv @(posedge clk);
    output  tok_cons_rdy;
    input   tok_cons_vld;
    output  tok_prod_vld;
    input   tok_prod_rdy;
  endclocking

endinterface : token_agent_if

`endif // TOKEN_AGENT_IF_SV

