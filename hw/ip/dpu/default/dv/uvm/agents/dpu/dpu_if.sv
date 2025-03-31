`ifndef DPU_IF
`define DPU_IF

interface dpu_if (input clk);
  logic reset_an_i;
  logic irq_o;


  clocking mon @(posedge clk);
    input reset_an_i;
    input irq_o;

  endclocking

endinterface

`endif
