// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>
//
// Kudelski Ring Oscillator dummy module.
//

module ro
#(parameter SEED_SEL = 8)
(
  input   logic en_i,
  output  wire  clk_o
);

assign clk_o = 1'b0;

endmodule
