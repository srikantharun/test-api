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

// -------------------------------------------------------------------------
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_xpi_vpt.sv#2 $
// -------------------------------------------------------------------------
// Description:
//              XPI vpt transaction support module                             *
//              Instantiate counters for latency calculation                   *
//              Counter is loaded only if transaction is of type vpt (VPR/VPW) *
//              Downcount is stopped when counter reaches zero, then expired   *
//              flag is asserted at the output.                                *
//                                                                             *
`include "DWC_ddrctl_all_defs.svh"
module DWC_ddr_umctl2_xpi_vpt
   #(
      parameter         CNT_WIDTH     = 11,
      parameter integer CNT_DEPTH     = 2,
      parameter         OCCAP_EN      = 0,
      parameter         OTZ_REG_OUT   = 0,  //output_timeout_zero is generated used register sources
      parameter         OCCAP_PIPELINE_EN = 0
   )
   (
   //---------------------------------------------------------------------------
   // Interface Pins
   //---------------------------------------------------------------------------

      // inputs
      input                      e_clk, // core clock
      input                      e_rst_n, // asynch reset
      input                      push, // vpt incoming transaction in FIFO
      input                      pop, // vpt outcoming transaction in FIFO
      input  [CNT_WIDTH-1:0]     input_timeout, // reset value for counters
      input                      input_timeout_zero, // reset value zero flag
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in generate blocks
      input                      reg_ddrc_occap_en,
//spyglass enable_block W240
      // outputs
      output                     counters_empty,
      output                     counters_full,
      output                     output_timeout_zero, // vpt expired in the FIFO
      output [CNT_WIDTH-1:0]     output_timeout,  // calculated latency for vpt transaction
      output                     occap_xpi_vpt_par_err
   );

   //---------------------------------------------------------------------------
   // Local parameters
   //---------------------------------------------------------------------------
   localparam OCCAP_WIDTH = CNT_DEPTH*CNT_WIDTH + // vpt_counters
                            CNT_DEPTH +           // vpt_counter_expired
                            CNT_DEPTH +           // read_ptr
                            CNT_DEPTH             // write_ptr
                            ;
   localparam SL_W = 8;
   localparam PARW = ((OCCAP_WIDTH%SL_W>0) ? OCCAP_WIDTH/SL_W+1 : OCCAP_WIDTH/SL_W);
   localparam REG_EN_0 = 0;
  //---------------------------------------------------------------------------
  // Internal signals 
  //---------------------------------------------------------------------------

   reg  [CNT_WIDTH-1:0] vpt_counters [0:CNT_DEPTH-1];  // array of counters
   reg  [CNT_WIDTH-1:0] vpt_counters_nxt [0:CNT_DEPTH-1];  // array of counters
   wire                 vpt_counter_expired; // one of the counters has expired
   
   reg  [CNT_DEPTH-1:0] vpt_counters_valid; // flag for vpt, resetted to zero when transaction is popped, this avoids spurious zero conditions
   reg  [CNT_DEPTH-1:0] vpt_counters_valid_nxt; // flag for vpt, resetted to zero when transaction is popped, this avoids spurious zero conditions
   wire [CNT_DEPTH-1:0] expired_vpt_counters; // expired vector
   logic [CNT_DEPTH-1:0] vpt_counters_zero; // zero vector for all counters
   wire [CNT_DEPTH-1:0] load_counters; // load reset value in counters
   wire [CNT_DEPTH-1:0] unload_counters; // clear valid flag in the counters
   reg  [CNT_WIDTH-1:0] vpt_counter_output; // output latency
   
   reg  [CNT_DEPTH-1:0] read_ptr; // output mux selector
   reg  [CNT_DEPTH-1:0] read_ptr_nxt; // output mux selector
   
   reg  [CNT_DEPTH-1:0] write_ptr; // input demux selector
   reg  [CNT_DEPTH-1:0] write_ptr_nxt; // input demux selector
   wire                 counters_not_empty;
   wire [CNT_DEPTH-1:0] input_timeout_zero_vec, push_vec, pop_vec;

   wire                 push_i, pop_i;

   integer i; // for loop index
   integer j; // for loop index

   logic    vpt_counters_zero_par_err;
   logic    vpt_counters_zero_par_err_unused;
  //---------------------------------------------------------------------------
  // Main module
  //---------------------------------------------------------------------------


  //---------------------------------------------------------------------------
  // Inputs assign
  //---------------------------------------------------------------------------

   assign push_i                    = push & ~counters_full;
   assign pop_i                     = pop & counters_not_empty; 

   assign input_timeout_zero_vec    = input_timeout_zero  ? {CNT_DEPTH{1'b1}} : {CNT_DEPTH{1'b0}};
   assign push_vec                  = push_i              ? {CNT_DEPTH{1'b1}} : {CNT_DEPTH{1'b0}};
   assign pop_vec                   = pop_i               ? {CNT_DEPTH{1'b1}} : {CNT_DEPTH{1'b0}};

   assign load_counters             = write_ptr & push_vec;
   assign unload_counters           = read_ptr & pop_vec;

  //---------------------------------------------------------------------------
  // Output assign
  //---------------------------------------------------------------------------

   assign output_timeout       = vpt_counter_output; // output latency
   assign output_timeout_zero  = vpt_counter_expired; // any of the vpt inside the FIFO is expired
   assign counters_empty       = ~counters_not_empty;

  //---------------------------------------------------------------------------
  // Main processes
  //---------------------------------------------------------------------------


   // read/write pointers, ring counter. read pointer follows write pointer
   always @(*) begin: POINTERS_nxt
         if (push_i) write_ptr_nxt   = {write_ptr[CNT_DEPTH-2:0],write_ptr[CNT_DEPTH-1]};
         else        write_ptr_nxt   = write_ptr;

         if (pop_i)  read_ptr_nxt    = {read_ptr[CNT_DEPTH-2:0],read_ptr[CNT_DEPTH-1]};
         else        read_ptr_nxt    = read_ptr;
   end // always @(*)

   always @(posedge e_clk or negedge e_rst_n) begin: POINTERS_reg
      if (e_rst_n == 1'b0) begin
         read_ptr    <= {{(CNT_DEPTH-1){1'b0}},1'b1};
         write_ptr   <= {{(CNT_DEPTH-1){1'b0}},1'b1};
      end else begin
         read_ptr    <= read_ptr_nxt;
         write_ptr   <= write_ptr_nxt;
      end
   end // always @(posedge e_clk or negedge e_rst_n)

   // counters
   always @(*) begin: COUNTERS_nxt
         for (i=0; i<CNT_DEPTH; i=i+1) begin
            casez ({load_counters[i],input_timeout_zero_vec[i],vpt_counters_zero[i]})
               3'b11?: begin // push in FIFO but input value is zero
                           vpt_counters_nxt[i]         = {CNT_WIDTH{1'b0}};
                           vpt_counters_valid_nxt[i]   = 1'b1; // transaction pushed, flag valid
                        end
               3'b10?: begin // push in FIFO, input value not zero
                           vpt_counters_nxt[i]         = input_timeout - 1;
                           vpt_counters_valid_nxt[i]   = 1'b1; // transaction pushed, flag valid
                        end
               3'b0?1: begin // when counters reaches zero, stop
                           vpt_counters_nxt[i]         = {CNT_WIDTH{1'b0}};
                           if (unload_counters[i]) vpt_counters_valid_nxt[i] = 1'b0; // clear flag when transaction leaves the FIFO
                           else                    vpt_counters_valid_nxt[i] = vpt_counters_valid[i];
                        end
               default: begin // decrement counter
                           vpt_counters_nxt[i]         = vpt_counters[i] - 1;
                           if (unload_counters[i]) vpt_counters_valid_nxt[i] = 1'b0; // clear flag when transaction leaves the FIFO
                           else                    vpt_counters_valid_nxt[i] = vpt_counters_valid[i];
                        end
            endcase // casez ({load_counters[i],input_timeout_zero_vec[i],vpt_counters_zero[i]})
         end // for (i=0; i<CNT_DEPTH; i=i+1)
   end // always @(*)

   always @(posedge e_clk or negedge e_rst_n) begin: COUNTERS_reg
      if (e_rst_n == 1'b0) begin
         for (j=0; j<CNT_DEPTH; j=j+1) begin
                vpt_counters[j]         <= {(CNT_WIDTH){1'b0}};
                vpt_counters_valid[j]   <= 1'b0;
         end // for
      end else begin
         for (j=0; j<CNT_DEPTH; j=j+1) begin
            if (vpt_counters[j] != vpt_counters_nxt[j]) begin
                vpt_counters[j]         <= vpt_counters_nxt[j];
            end
                vpt_counters_valid[j]   <= vpt_counters_valid_nxt[j];
         end // for

      end
   end // always @(posedge e_clk or negedge e_rst_n)

  generate
  if (OTZ_REG_OUT==0) begin : OTZ_REG_OUT_NEN_PROC
      always @(*) begin: ZERO_detect
         for (i=0; i<CNT_DEPTH; i=i+1) begin
            vpt_counters_zero[i]    = ~|vpt_counters[i]; // zero flag
         end // for (i=0; i<CNT_DEPTH; i=i+1)
      end
  //spyglass disable_block W528
  //SMD: Variable 'vpt_counters_zero_par_err' set but not read.
  //SJ: Used in a generate block, set to 0 and not sampled in certain conditions
    assign vpt_counters_zero_par_err = 1'b0;   
  //spyglass enable_block W528
  end
  else begin : OTZ_REG_OUT_EN_PROC
      logic [CNT_DEPTH-1:0] vpt_counters_zero_nxt;
      always @(*) begin: ZERO_detect
         for (i=0; i<CNT_DEPTH; i=i+1) begin
            vpt_counters_zero_nxt[i]    = ~|vpt_counters_nxt[i]; // zero flag
         end // for (i=0; i<CNT_DEPTH; i=i+1)
      end
      
     DWC_ddr_umctl2_par_reg
      #(
      .DW                  (CNT_DEPTH),
      .OCCAP               (OCCAP_EN),
      .OCCAP_PIPELINE_EN   (OCCAP_PIPELINE_EN),
      .REG_EN              (REG_EN_0),
      .SL_W                (SL_W),
      .RESVAL              (0)
     )
      u_vpt_counters_zero (
         .clk(e_clk),
         .rst_n(e_rst_n),
         .data_in(vpt_counters_zero_nxt),
         .reg_set(1'b0),
         .parity_en(reg_ddrc_occap_en),
         .poison_en(1'b0),
         .data_out(vpt_counters_zero),
         .parity_err(vpt_counters_zero_par_err) 

     ); 

  end
  endgenerate     
   
   //spyglass disable_block W415a
   //SMD: Signal vpt_counter_output is being assigned multiple times in same always block. 
   //SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
   always @(*) begin: OUT_COUNT_mux
      vpt_counter_output   = {CNT_WIDTH{1'b0}};
      for (i=0; i<CNT_DEPTH; i=i+1) begin // output mux, final latency
         vpt_counter_output   = vpt_counter_output | (vpt_counters[i] & {CNT_WIDTH{read_ptr[i]}});
      end // for (i=0; i<CNT_DEPTH; i=i+1)
   end // always @(*)
   //spyglass enable_block W415a

   assign expired_vpt_counters   = vpt_counters_zero & vpt_counters_valid; // flag zero only for valid counters
   assign vpt_counter_expired    = |expired_vpt_counters;
   assign counters_not_empty     = |vpt_counters_valid;
   assign counters_full          = &vpt_counters_valid;

  //---------------------------------------------------------------------------
  // OCCAP_EN process
  //---------------------------------------------------------------------------

  generate
   if (OCCAP_EN==1) begin: OCCAP_en

     
     wire [OCCAP_WIDTH-1:0] pgen_in;  
     wire [OCCAP_WIDTH-1:0] pcheck_in;  

     // 
     // wiring of pgen_in/pcheck_in
     //

     reg  [CNT_WIDTH*CNT_DEPTH-1:0] vpt_counters_nxt_w;  // wire for array of counters
     reg  [CNT_WIDTH*CNT_DEPTH-1:0] vpt_counters_w;      // wire for array of counters
     
     always @ (*) begin : vpt_counters_w_PROC
      integer cnt_depth_count;
        for (cnt_depth_count=0; cnt_depth_count<CNT_DEPTH; cnt_depth_count=cnt_depth_count+1) begin
          vpt_counters_nxt_w[cnt_depth_count*CNT_WIDTH+:CNT_WIDTH] = vpt_counters_nxt[cnt_depth_count];
          vpt_counters_w[cnt_depth_count*CNT_WIDTH+:CNT_WIDTH]     = vpt_counters[cnt_depth_count];
        end
      end

     assign pgen_in    = {vpt_counters_nxt_w,
                          vpt_counters_valid_nxt,
                          read_ptr_nxt,
                          write_ptr_nxt};

     assign pcheck_in  = {vpt_counters_w,
                          vpt_counters_valid,
                          read_ptr,
                          write_ptr};


     wire [PARW-1:0]        pgen_in_par;     
     reg  [PARW-1:0]        pgen_in_par_r;     
     wire [PARW-1:0]        pcheck_par_err;  
     wire [PARW-1:0]        pgen_parity_corr_unused, pcheck_parity_corr_unused;   
     
     wire                   parity_en;
     reg                    pcheck_en;
     wire [PARW-1:0]        parity_dummy,  mask_in;
     wire                   poison_en;

     assign parity_dummy  = {PARW{1'b1}};
     assign mask_in       = {PARW{1'b1}};
     assign poison_en     = 1'b0;

     assign parity_en = reg_ddrc_occap_en;
     always @(posedge e_clk or negedge e_rst_n) begin
           if (~e_rst_n) begin
              pcheck_en <= 0;
           end
           else begin
              pcheck_en <= parity_en;
           end
        end

           
     // 
     // parity checking logic itself
     //
         DWC_ddr_umctl2_ocpar_calc
         
         
         #(
            .DW      (OCCAP_WIDTH), 
            .CALC    (1), // parity calc
            .PAR_DW  (PARW),
            .SL_W    (SL_W)
         )
         U_pgen
         (
            .data_in       (pgen_in),
            .parity_en     (parity_en),
            .parity_type   (poison_en),
            .parity_in     (parity_dummy),
            .mask_in       (mask_in),
            .parity_out    (pgen_in_par), // parity out
            .parity_corr   (pgen_parity_corr_unused) // not used
         );


         always @ (posedge e_clk or negedge e_rst_n)
           if (~e_rst_n) begin
             pgen_in_par_r <= {PARW{1'b0}};
           end
           else begin
             pgen_in_par_r <= pgen_in_par;
           end


         DWC_ddr_umctl2_ocpar_calc
         
         
         #(
            .DW      (OCCAP_WIDTH),
            .CALC    (0), // parity check
            .PAR_DW  (PARW),
            .SL_W    (SL_W)
         )
         U_pcheck
         (
            .data_in       (pcheck_in),
            .parity_en     (pcheck_en),
            .parity_type   (1'b0),
            .parity_in     (pgen_in_par_r), // parity in
            .mask_in       (mask_in),
            .parity_out    (pcheck_par_err), // parity error
            .parity_corr   (pcheck_parity_corr_unused) // not used
         );     
      
         if (OCCAP_PIPELINE_EN==1) begin : OCCAP_PIPELINE_EN_1

           reg pcheck_par_err_r;
           always @ (posedge e_clk or negedge e_rst_n) begin : pcheck_par_err_r_PROC
             if (~e_rst_n) begin
               pcheck_par_err_r <= 1'b0;
             end else begin
               pcheck_par_err_r <= |pcheck_par_err | vpt_counters_zero_par_err;
             end
           end

           assign occap_xpi_vpt_par_err = pcheck_par_err_r;          

         end else begin : OCCAP_PIPELINE_EN_0
         
           assign occap_xpi_vpt_par_err = |pcheck_par_err | vpt_counters_zero_par_err;

         end 

         
   end else begin: OCCAP_ne
      assign occap_xpi_vpt_par_err = 1'b0;
      assign vpt_counters_zero_par_err_unused = vpt_counters_zero_par_err;
    end

  endgenerate

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

   localparam CATEGORY = 5;

   //assert_never #(0, 0, "Push requested when VPT counters full", CATEGORY) a_xpi_push_when_counters_full(e_clk,e_rst_n,(push && counters_full));
   //assert_never #(0, 0, "Pop requested when VPT counters empty", CATEGORY) a_xpi_pop_when_counters_empty(e_clk,e_rst_n,(pop && !counters_not_empty));

`endif
`endif

endmodule // DWC_ddr_umctl2_xpi_vpt
