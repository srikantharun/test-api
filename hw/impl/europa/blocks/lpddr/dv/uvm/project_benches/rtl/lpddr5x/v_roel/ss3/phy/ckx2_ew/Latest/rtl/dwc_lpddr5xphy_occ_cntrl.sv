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

module dwc_lpddr5xphy_occ_cntrl
#(  parameter
      pCLK_CHAIN_DEPTH             = 4         
  )

                                (
    input  wire logic                                     scan_en
  , input  wire logic                                     fast_clk
  , input  wire logic                                     reset
  , input  wire logic                                     slow_clk
  , input  wire logic [pCLK_CHAIN_DEPTH          - 1 : 0] clk_enable
  , output      logic                                     slow_clk_enable
  , output      logic                                     fast_clk_enable
);

  `ifndef SYNTHESIS
  timeunit 1ps;
  timeprecision 1ps;
  `endif

  localparam                     pFAST_CLK_CTR_WIDTH = 3;


  logic                                     reset_n;
  logic                                     slow_clk_enable_l_n;
  logic                                     fast_data;
  logic                                     slow_data;
  logic                                     slow_clk_enable_l;
  logic                                     fast_clk_enable_l;
  logic                                     capture_clk_enable;
  logic                                     capture_clk_enable_i;
  logic [pCLK_CHAIN_DEPTH           - 1 :0] clk_enable_i;
  logic                                     load_n_meta_5_l;
  logic                                     ctr_enable;
  logic                                     tercnt_n;
  logic [pFAST_CLK_CTR_WIDTH        - 1 :0] occ_counter_count;
  logic [                             7 :0] occ_decode_count; 


  assign reset_n             = ~reset;
  assign slow_clk_enable_l_n = ~slow_clk_enable_l;
  assign fast_data           = (~(scan_en | slow_clk_enable_l)) & capture_clk_enable;
  assign slow_data           = scan_en & (~fast_clk_enable_l);

  always_ff @(posedge slow_clk or posedge reset) begin
    if (reset) begin
      slow_clk_enable_l    <= 1'b0;
    end
    else begin
      slow_clk_enable_l    <= slow_data;
    end
  end

  always_ff @(posedge fast_clk or posedge reset) begin
    if (reset) begin
      fast_clk_enable_l    <= 1'b0;
    end
    else begin
      fast_clk_enable_l    <= fast_data;
    end
  end

  

dwc_lpddr5xphy_sync6_async_reset_occ
 #(.transport_delay(125)) zSync6_DLY125PS_load_n_meta_5_l (
            .SampleClk   (fast_clk),
            .DataIn      (slow_clk_enable_l_n),
            .Reset       (reset),
            `ifdef DWC_LPDDR5XPHY_assertions
            .InputChkDis (1'b1),
            `endif
            .DataOut     (load_n_meta_5_l)
);

  assign ctr_enable = tercnt_n & (~scan_en);

  dwc_lpddr5xphy_occ_counter
   u_occ_counter
    (
     .fast_clk    ( fast_clk               ),
     .count       ( occ_counter_count      ),
     .ctr_enable  ( ctr_enable             ),
     .load_n_meta_5_l ( load_n_meta_5_l    ),
     .reset_n         ( reset_n            ),
     .tercnt_n        ( tercnt_n           )
     );

  dwc_lpddr5xphy_occ_decoder
   u_occ_decoder
    (
     .A           ( occ_counter_count      ),
     .B           ( occ_decode_count       )
     );

  assign clk_enable_i[0] = clk_enable[0] & occ_decode_count[1];
  assign clk_enable_i[1] = clk_enable[1] & occ_decode_count[2];
  assign clk_enable_i[2] = clk_enable[2] & occ_decode_count[3];
  assign clk_enable_i[3] = clk_enable[3] & occ_decode_count[4];

  dwc_lpddr5xphy_occ_orTree
   u_occ_orTree
    (
     .a           ( clk_enable_i             ),
     .b           ( capture_clk_enable_i     )
     );

  always_ff @(posedge fast_clk or posedge reset) begin
    if (reset) begin
      capture_clk_enable <= 1'b0;
    end
    else begin
      capture_clk_enable <=  capture_clk_enable_i;
    end
  end

  assign fast_clk_enable = fast_clk_enable_l;
  assign slow_clk_enable = slow_data; 

endmodule 

  `end_keywords

  `default_nettype wire 
