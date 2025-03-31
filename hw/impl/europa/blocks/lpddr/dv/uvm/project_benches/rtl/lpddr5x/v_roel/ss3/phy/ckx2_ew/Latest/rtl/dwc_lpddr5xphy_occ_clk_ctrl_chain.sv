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

module dwc_lpddr5xphy_occ_clk_ctrl_chain
#(  parameter
      pCLK_CHAIN_DEPTH             = 4         
  )

                                         (
    input  wire logic                                clk
  , input  wire logic                                se
  , input  wire logic                                si     
  , output      logic                                so
  , output      logic [pCLK_CHAIN_DEPTH          - 1 : 0 ] clk_ctrl_data
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif




  always_ff @(posedge clk) begin
      clk_ctrl_data    <= {clk_ctrl_data[pCLK_CHAIN_DEPTH-2 : 0], si};
  end

  assign   so =  clk_ctrl_data[pCLK_CHAIN_DEPTH-1];

endmodule 

`end_keywords

`default_nettype wire  

