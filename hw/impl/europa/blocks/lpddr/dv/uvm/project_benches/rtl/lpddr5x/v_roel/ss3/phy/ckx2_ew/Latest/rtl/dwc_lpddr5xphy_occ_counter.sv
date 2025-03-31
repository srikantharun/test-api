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

module dwc_lpddr5xphy_occ_counter
#(  parameter
    pFAST_CLK_CTR_WIDTH          = 3
  )

                                  (
    input  wire logic                                     fast_clk
  , output      logic [pFAST_CLK_CTR_WIDTH        - 1 :0] count
  , input  wire logic                                     ctr_enable
  , input  wire logic                                     load_n_meta_5_l
  , input  wire logic                                     reset_n
  , output      logic                                     tercnt_n
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif


  logic                                     count_dwc_lpddr5xmphy_nc_;
  logic                                     tercnt_n_reg;
  logic [pFAST_CLK_CTR_WIDTH        - 1 :0] next_count;



  always_ff @(posedge fast_clk or negedge reset_n) begin
    if (!reset_n) begin
      count          <= {pFAST_CLK_CTR_WIDTH{1'b0}};
      tercnt_n_reg   <= 1'b0;
    end
    else begin
      count          <= next_count;
      tercnt_n_reg   <= &{next_count[2], ~next_count[1], next_count[0]};
    end
  end

  assign {count_dwc_lpddr5xmphy_nc_, next_count} = {1'b0, {pFAST_CLK_CTR_WIDTH{load_n_meta_5_l}}} & ({1'b0, count} + ctr_enable);
  assign tercnt_n = ~tercnt_n_reg;

endmodule 

`end_keywords

`default_nettype wire 
