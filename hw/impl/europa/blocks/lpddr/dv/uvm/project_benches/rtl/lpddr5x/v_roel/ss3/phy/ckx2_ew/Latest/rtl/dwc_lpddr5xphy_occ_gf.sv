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

module dwc_lpddr5xphy_occ_gf

                             (
    input  wire logic                                          fast_clk_enable
  , input  wire logic                                          slow_clk_enable
  , input  wire logic                                          pll_bypass
  , input  wire logic                                          test_mode
  , input  wire logic                                          scan_en
  , output      logic                                          fast_gate
  , output      logic                                          slow_gate
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif


  assign  fast_gate = ((fast_clk_enable & (~pll_bypass)) & (test_mode));
  assign  slow_gate = ((slow_clk_enable | pll_bypass) & test_mode & (scan_en | pll_bypass));

endmodule 

`end_keywords

`default_nettype wire 
