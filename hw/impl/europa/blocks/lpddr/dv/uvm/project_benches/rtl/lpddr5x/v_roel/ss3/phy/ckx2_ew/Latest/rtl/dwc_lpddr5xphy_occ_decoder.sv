//------------------------------------------------------------------------
// Copyright 2024 Synopsys, Inc.
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Read the Synopsys Statement on Inclusivity and Diversity at
// https://solvnetplus.synopsys.com/s/article/Synopsys-Statement-on-Inclusivity-and-Diversity
// -----------------------------------------------------------------------

`default_nettype none  

`begin_keywords "1800-2012"

module dwc_lpddr5xphy_occ_decoder

                                  (
    input  wire logic [2:0]                               A 
  , output      logic [7:0]                               B 
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif





  assign B[0] = (A[2:0] == 3'b000);
  assign B[1] = (A[2:0] == 3'b001);
  assign B[2] = (A[2:0] == 3'b010);
  assign B[3] = (A[2:0] == 3'b011);
  assign B[4] = (A[2:0] == 3'b100);
  assign B[5] = (A[2:0] == 3'b101);
  assign B[6] = (A[2:0] == 3'b110);
  assign B[7] = (A[2:0] == 3'b111);



endmodule 

`end_keywords

`default_nettype wire  
