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

module dwc_lpddr5xphy_occ_ctrl
#(  parameter
      pCLK_CHAIN_DEPTH             = 4         
  )

                               (
    input  wire logic                    fast_clk
  , output      logic                    clk
  , input  wire logic                    cc_si
  , output      logic                    cc_so
  , input  wire logic                    slow_clk
  , input  wire logic                    test_se
  , input  wire logic                    test_mode
  , input  wire logic                    pll_reset
  , input  wire logic                    pll_bypass
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif


  logic                                      intClk;
  logic                                      ccClk;
  logic [pCLK_CHAIN_DEPTH          - 1 : 0 ] clk_ctrl_data;


  assign clk = intClk;

  dwc_lpddr5xphy_occ_clk_ctrl_chain
  
  #(
      .pCLK_CHAIN_DEPTH          ( pCLK_CHAIN_DEPTH )
    )
  u_clk_ctrl_chain
  (
      .clk                       ( ccClk            )
    , .se                        ( test_se          )
    , .si                        ( cc_si            )
    , .so                        ( cc_so            )
    , .clk_ctrl_data             ( clk_ctrl_data    )
  );

  dwc_lpddr5xphy_occ_clk_multiplexer
  
  #(
      .pCLK_CHAIN_DEPTH          ( pCLK_CHAIN_DEPTH )
    )
  u_clk_multiplexer
  (
      .fast_clk                  ( fast_clk      )
    , .test_mode                 ( test_mode     )
    , .reset                     ( pll_reset     )
    , .scan_en                   ( test_se       )
    , .pll_bypass                ( pll_bypass    )
    , .slow_clk                  ( slow_clk      )
    , .clk_enable                ( clk_ctrl_data )
    , .cc_clk                    ( ccClk         )
    , .clk                       ( intClk        )
  );

endmodule 

`end_keywords

`default_nettype wire 

