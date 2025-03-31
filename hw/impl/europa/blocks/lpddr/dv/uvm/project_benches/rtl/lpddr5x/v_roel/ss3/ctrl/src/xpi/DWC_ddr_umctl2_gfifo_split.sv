//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_gfifo_split.sv#2 $
// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 43.27.35.4.TreMctl_163.DwsDdrChip_8.14.6.DwsDdrctlTop_5.9.7
// ------------------------------------------------------------------------------

//----------------------------------------------------------------------
// Filename    : DWC_ddr_umctl2_gfifo_split.v
// Description : Generic size Synchronous FIFO with splitted memory array (n words x M bits)
//----------------------------------------------------------------------

/*****************************************************************************
* Generic size Synchronous FIFO with splitted memory array (n words x M bits) *
 *****************************************************************************/

`include "DWC_ddrctl_all_defs.svh"
module DWC_ddr_umctl2_gfifo_split (
    clk,
    rst_n,
    wr,
    d,
    rd,
    par_en,
    poison_en,
    ff,
    q,
    fe,
    matched,
    wcount,
    par_err
);
  parameter WIDTH         =  32;  // RANGE 1 to 16777216
  parameter WIDTH_SPLIT   =  4;   // width of the signal that goes to the second memory array  
  parameter SPLIT         =  0;   // split the memory array
  parameter integer DEPTH =  8;   // RANGE 4 to 16777216
  parameter ADDR_WIDTH    =  3;   // RANGE 2 to 24
  parameter COUNT_WIDTH   =  4;   // RANGE 3 to 25

  parameter OCCAP_EN      =  0;
  parameter OCCAP_PIPELINE_EN = 0;
   
  localparam AE_LEVEL     = 1;    // RANGE 0 TO 255
  localparam AF_LEVEL     = 1;    // RANGE 0 TO 255
  localparam ERR_MODE     = 0;    // RANGE 0 TO 2
  localparam RST_MODE     = 0;    // RANGE 0 TO 1


  localparam SL_W         = WIDTH<8 ? WIDTH : 8;
  localparam PARW         = (OCCAP_EN==1) ? ((WIDTH%SL_W>0) ? WIDTH/SL_W+1 : WIDTH/SL_W) : 0;

  localparam WIDTH_DOWN   =  WIDTH_SPLIT;
  localparam WIDTH_UP     =  (SPLIT==1) ?  WIDTH - WIDTH_DOWN :
                                           WIDTH;

  localparam WIDTH_PAR    = WIDTH_UP+PARW;

// I/O declarations
  input                       clk;            // clk input
  input                       rst_n;          // active low async reset
  input                       wr;             // Push domain active low push reqest
  input   [WIDTH-1:0]         d;              // Push domain data input
  input                       rd;             // Pop domain active high pop request
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate blocks
  input                       par_en;
  input                       poison_en;
//spyglass enable_block W240
  output                      ff;             // Push domain Full status flag
  output  [WIDTH-1:0]         q;              // Pop domain data input
  output                      fe;             // Pop domain Empty status flag
  output  [COUNT_WIDTH-1:0]   wcount;         // word count

  output                      matched;        // The lower input matches a data inside the memory  

  output                      par_err;
   
// Internal wires
  wire    [WIDTH_UP-1:0]      d_up;          // Pop domain data upper memory
  wire    [WIDTH_UP-1:0]      q_up;          // Push domain data upper memory
  wire                        push_req_n;
  wire                        pop_req_n;

  wire    [WIDTH_PAR-1:0]     d_in;
  wire    [WIDTH_PAR-1:0]     q_out;

// Unused bcm 65 pins 
  wire                        almost_empty_unused;
  wire                        half_full_unused;
  wire                        almost_full_unused;
  wire                        error_unused;
  
  
`ifdef SNPS_ASSERT_ON
  
  //---------------------------------------------------------------------------
  //  Assertion fifo checker instance
  //---------------------------------------------------------------------------

  `ifndef SYNTHESIS
  sync_fifo_checker
   U_sync_fifo_checker 
  (
  .rst_n(rst_n),
  .clk(clk),  
  .wr(wr),
  .ff(ff),
  .rd(rd),
  .fe(fe)
   );
`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

  assign                   push_req_n = ~wr;
  assign                   pop_req_n  = ~rd;

  reg [COUNT_WIDTH-1:0] wcount;  
  always @(posedge clk or negedge rst_n)
    begin
      if (rst_n == 1'b0)
        begin
          wcount <= {COUNT_WIDTH{1'b0}};
        end
      else
        begin
          if (wr& ~ff & ( ~rd | fe))
            wcount <= wcount +1;
          else if ((~wr | ff) & rd & ~fe)
            wcount <= wcount -1;
       end
    end // always @ (posedge clk or negedge rst_b)
  
  generate
  if (OCCAP_EN==1) begin: BCM65_ATV

    
  DWC_ddrctl_bcm65_atv
   #(
    .WIDTH           (WIDTH_PAR),
    .DEPTH           (DEPTH),
    .AE_LEVEL        (AE_LEVEL),       
    .AF_LEVEL        (AF_LEVEL),
    .ERR_MODE        (ERR_MODE),
    .RST_MODE        (RST_MODE),
    .ADDR_WIDTH      (ADDR_WIDTH),
    .TMR             (1) // TMR used
    ) 
    bcm_sync_fifo (
    .clk             (clk),
    .rst_n           (rst_n),
    .init_n          (1'b1),
    .push_req_n      (push_req_n),
    .pop_req_n       (pop_req_n),
    .data_in         (d_in),
    .empty           (fe),
    .almost_empty    (almost_empty_unused),
    .half_full       (half_full_unused),
    .almost_full     (almost_full_unused),
    .full            (ff),
    .error           (error_unused),
    .data_out        (q_out)
    );

  end else begin: BCM65

  DWC_ddrctl_bcm65
   #(
    .WIDTH           (WIDTH_PAR),
    .DEPTH           (DEPTH),
    .AE_LEVEL        (AE_LEVEL),       
    .AF_LEVEL        (AF_LEVEL),
    .ERR_MODE        (ERR_MODE),
    .RST_MODE        (RST_MODE),
    .ADDR_WIDTH      (ADDR_WIDTH)
    ) 
    bcm_sync_fifo (
    .clk             (clk),
    .rst_n           (rst_n),
    .init_n          (1'b1),
    .push_req_n      (push_req_n),
    .pop_req_n       (pop_req_n),
    .data_in         (d_in),
    .empty           (fe),
    .almost_empty    (almost_empty_unused),
    .half_full       (half_full_unused),
    .almost_full     (almost_full_unused),
    .full            (ff),
    .error           (error_unused),
    .data_out        (q_out)
    );

  end
  endgenerate

  generate
  if (SPLIT==1) begin: ID_split
      // split signals
      wire    [WIDTH_DOWN-1:0]    d_down;
      wire    [WIDTH_DOWN-1:0]    q_down;
      
      wire                        empty_unconnected;
      wire                        almost_empty_unconnected;
      wire                        half_full_unconnected;
      wire                        almost_full_unconnected;
      wire                        full_unconnected;
      wire                        error_unconnected;
  
      wire [DEPTH-1:0] valid_i;
      assign d_down  = d[WIDTH_DOWN-1:0];

      DWC_ddr_umctl2_smem_array
       #(
        .WIDTH           (WIDTH_DOWN),
        .COUNT_WIDTH     (COUNT_WIDTH),
        .DEPTH           (DEPTH),
        .AE_LEVEL        (AE_LEVEL),       
        .AF_LEVEL        (AF_LEVEL),
        .ERR_MODE        (ERR_MODE),
        .RST_MODE        (RST_MODE),
        .ADDR_WIDTH      (ADDR_WIDTH)
        ) 
        bcm_sync_fifo_id (
        .clk             (clk),
        .rst_n           (rst_n),
        .init_n          (1'b1),
        .push_req_n      (push_req_n),
        .pop_req_n       (pop_req_n),
        .data_in         (d_down),
        .wcount          (wcount),
        .empty           (empty_unconnected),
        .almost_empty    (almost_empty_unconnected),
        .half_full       (half_full_unconnected),
        .almost_full     (almost_full_unconnected),
        .full            (full_unconnected),
        .error           (error_unconnected),
        .valid           (valid_i),
        .data_out        (q_down)
        );

        assign matched = |valid_i;

         assign d_up    = d[WIDTH-1:WIDTH_DOWN];
         assign q       = {q_up,q_down};

    end else begin: ID_nsplit

      assign matched    = 1'b0;

      assign d_up       = d[WIDTH-1:0];
      assign q          = q_up;


    end
    if (OCCAP_EN==1) begin: PAR_check

      wire [PARW-1:0] parity_dummy, mask_in;

      wire [PARW-1:0] d_par, q_par, parity_err;
      wire [PARW-1:0] pgen_parity_corr_unused, pcheck_parity_corr_unused;

      wire pgen_en, pcheck_en;

      assign parity_dummy  = {PARW{1'b1}};
      assign mask_in       = {PARW{1'b1}};

      assign pgen_en    = wr;
      assign pcheck_en  = par_en & rd & ~fe;


         DWC_ddr_umctl2_ocpar_calc
         
         #(
            .DW      (WIDTH),
            .CALC    (1), // parity calc
            .PAR_DW  (PARW),
            .SL_W    (SL_W)
         )
         U_pgen
         (
            .data_in       (d),
            .parity_en     (pgen_en),
            .parity_type   (poison_en),
            .parity_in     (parity_dummy),
            .mask_in       (mask_in),
            .parity_out    (d_par), // parity out
            .parity_corr   (pgen_parity_corr_unused) // not used
         );


         DWC_ddr_umctl2_ocpar_calc
         
         #(
            .DW      (WIDTH),
            .CALC    (0), // parity check
            .PAR_DW  (PARW),
            .SL_W    (SL_W)
         )
         U_pcheck
         (
            .data_in       (q),
            .parity_en     (pcheck_en),
            .parity_type   (1'b0),
            .parity_in     (q_par), // parity in
            .mask_in       (mask_in),
            .parity_out    (parity_err), // parity error
            .parity_corr   (pcheck_parity_corr_unused) // not used
         );

      assign d_in = {d_up,d_par};
      assign {q_up,q_par} = q_out;

         if (OCCAP_PIPELINE_EN==1) begin : OCCAP_PIPELINE_EN_1

           reg par_err_r;
           always @ (posedge clk or negedge rst_n) begin : par_err_r_PROC
             if (~rst_n) begin
               par_err_r <= 1'b0;
             end else begin
               par_err_r <= |parity_err;
             end
           end

           assign par_err = par_err_r;          

         end else begin : OCCAP_PIPELINE_EN_0
         
           assign par_err = |parity_err;

         end 


    end // PAR_check
    else begin: OCCAP_dis
   
      assign par_err = 1'b0;
      assign d_in    = d_up;
      assign q_up    = q_out;

    end // OCCAP_dis
    endgenerate

endmodule //DWC_ddr_umctl2_gfifo_split
