// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description : Clk Interface containing Tasks to advance time
//               Instanced in top-level TB and used within Sequences and Tests (without having to rely upon #10ns type of coding)
// Owner       : Sultan Khan

interface clk_if(input clk);

  // Advance on POS-EDGE clks
  task automatic await_rising_edge( int n = 1 );
      repeat( n ) @( posedge clk );
  endtask : await_rising_edge

  // Advance on NEG-EDGE clks
  task automatic await_falling_edge( int n = 1 );
      repeat( n ) @( negedge clk );
  endtask : await_falling_edge
  
  // Advance on 1/2 CLK Period
  task automatic await_edge( int n = 1 );
      repeat( n ) @( clk );
  endtask : await_edge
    
endinterface: clk_if
