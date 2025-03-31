// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: andrew dickson <andrew.dickson@aelera.ai>


// Simple clock generator for testbenches
module tb_clkgen #(
  parameter real FREQ = 1.0
)
(
  output wire o_clk
);

//=============================================================================
real clk_per;
realtime req_period; 

logic clk;

initial begin
  clk = 0;
  #2ns;

  clk_per    = 1.0e9 / FREQ;
  req_period = time'(clk_per) * 1ns;

  forever begin
    forever begin
      #(req_period / 2);
      //#(25ns);
      clk = ~clk;
    end
  end
end

assign o_clk = clk;

endmodule
