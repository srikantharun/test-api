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

module dwc_lpddr5xphy_occ_clk_multiplexer
#(  parameter
      pCLK_CHAIN_DEPTH             = 4         
  )

                                          (
    input  wire logic                                     scan_en
  , input  wire logic                                     fast_clk
  , output      logic                                     clk
  , output      logic                                     cc_clk
  , input  wire logic                                     test_mode
  , input  wire logic                                     reset
  , input  wire logic                                     pll_bypass
  , input  wire logic                                     slow_clk
  , input  wire logic [pCLK_CHAIN_DEPTH          - 1 : 0] clk_enable
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif


  logic                                     slow_gate;
  logic                                     gated_slow_clk;
  logic                                     fast_gate;
  logic                                     gated_fast_clk;
  logic                                     not_occ_bypass;

  logic                                     slow_clk_enable;
  logic                                     fast_clk_enable;
  logic                                     clkand2;


  assign not_occ_bypass = ~(test_mode & pll_bypass);


  dwc_lpddr5xphy_occ_cntrl
  
  #(
      .pCLK_CHAIN_DEPTH          ( pCLK_CHAIN_DEPTH )
   )
  u_occ_cntrl
  (
      .scan_en                   ( scan_en           )
    , .fast_clk                  ( fast_clk          )
    , .reset                     ( reset             )
    , .slow_clk                  ( slow_clk          )
    , .clk_enable                ( clk_enable        )
    , .slow_clk_enable           ( slow_clk_enable   )
    , .fast_clk_enable           ( fast_clk_enable   )
  );


  dwc_lpddr5xphy_occ_gf
   u_occ_gf
  (
      .fast_clk_enable           ( fast_clk_enable   )
    , .slow_clk_enable           ( slow_clk_enable   )
    , .pll_bypass                ( pll_bypass        )
    , .test_mode                 ( test_mode         )
    , .scan_en                   ( scan_en           )
    , .fast_gate                 ( fast_gate         )
    , .slow_gate                 ( slow_gate         )
  );

   dwc_lpddr5xphy_clkgater_te
    u_slow_gate
  (    .C        ( slow_clk          ) 
     , .D        ( slow_gate         ) 
     , .CG       ( gated_slow_clk    ) 
     , .TE       ( 1'b0              )
   );

  dwc_lpddr5xphy_clkgater_te
   u_fast_gate
  (    .C        ( fast_clk          ) 
     , .D        ( fast_gate         ) 
     , .CG       ( gated_fast_clk    ) 
     , .TE       ( 1'b0              )
   );



  dwc_lpddr5xphy_clkand2
   u_clkand2
  (
      .A        ( gated_fast_clk          )
    , .B        ( not_occ_bypass          )
    , .Y        ( clkand2                 )
  );

  dwc_lpddr5xphy_clkor2
   u_clkor2
  (
      .A        ( clkand2           )
    , .B        ( gated_slow_clk    )
    , .Y        ( clk               )
  );


  assign cc_clk = gated_slow_clk;

endmodule 

`end_keywords

`default_nettype wire 

