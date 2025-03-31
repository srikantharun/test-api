// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : Defines the Interface for the IRQ Agent
// Owner       : Sultan Khan

interface irq_if(input clk);

  localparam  NUM_IRQ_LINES = 4;     // Same defined in irq_pkg (Duplicated here as an interface cant be placed inside a pkg)

  logic [NUM_IRQ_LINES-1:0]  irq;

  // -----------------------------------------
  // Tasks to facilitate monitoring and checking of IRQ signal
  
  task automatic wait_n_clks( int n = 1 );
      repeat( n ) @( posedge clk );
  endtask : wait_n_clks

  task automatic wait_irq_set(int idx);
      if(!irq[idx]) begin
          @(posedge irq[idx]);
      end
  endtask : wait_irq_set

  function automatic get_irq_state(int idx);
      get_irq_state = irq[idx];
  endfunction : get_irq_state
  
  // -----------------------------------------

endinterface: irq_if
