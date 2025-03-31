`ifndef IID_IF
`define IID_IF

interface iid_if (input clk);
  logic iid_i;
  logic[2:0] cid_i;
 
  clocking drv @(posedge clk);
    output iid_i;

  endclocking
  
  clocking mon @(posedge clk);
    input iid_i;
  endclocking

endinterface

`endif

