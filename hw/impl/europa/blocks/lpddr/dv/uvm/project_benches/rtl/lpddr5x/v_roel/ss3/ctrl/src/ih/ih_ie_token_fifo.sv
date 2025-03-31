//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_ie_token_fifo.sv#2 $
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

// ----------------------------------------------------------------------------
//                              DDR Controller
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//
// ----------------------------------------------------------------------------
// ----------------------------------------------------------------------------
//                              Description
//
// ----------------------------------------------------------------------------

`include "DWC_ddrctl_all_defs.svh"
module ih_ie_token_fifo
#(
    parameter DEPTH      = 16
   ,parameter WIDTH      = (DEPTH<3)?1:(DEPTH<5)?2:(DEPTH<9)?3:(DEPTH<17)?4:(DEPTH<33)?5:(DEPTH<65)?6:7
   ,parameter CNT_WIDTH  = (DEPTH<2)?1:(DEPTH<4)?2:(DEPTH<8)?3:(DEPTH<16)?4:(DEPTH<32)?5:(DEPTH<64)?6:7
)
(  
    input                    clk       
   ,input                    rstn      
   ,input                    allocate_token     // allocate token. this must be 0 when token_empty == 1
   ,output [WIDTH-1:0]       allocate_token_num // #token to be allocated. valid only when token_empty == 0 
   ,input                    release_token      // release token
   ,input  [WIDTH-1:0]       release_token_num  // #token to be released. valid only when release_token == 1
   ,output reg               token_empty        // No token available to be allocated
   ,output reg               token_full         // All token available

);

//---------------
// Declarations
//---------------

// Token array implemented as shift register
reg  [WIDTH-1:0]     token_array         [0:DEPTH-1];
reg  [WIDTH-1:0]     token_array_next    [0:DEPTH-1];

// Write pointer
wire [WIDTH-1:0]     wr_pt;

// Number of token available
reg  [CNT_WIDTH-1:0] num_tokens_avail; 

//-------
// Logic
//-------
assign wr_pt              = num_tokens_avail[WIDTH-1:0];
// CNT_WIDTH > WIDTH only when DEPTH is power of two.
// For wr_pt, only use [WIDTH-1:0] because of the followings
// e.g.) DEPTH=16, maximum value of num_tokens_avail=16 (1_0000b)
// For write (allocate_token), this can be valid only when num_tokens_avail < DEPTH
// So use only [WIDTH-1:0] 

assign allocate_token_num = token_array[0];

wire [WIDTH :0] wr_pt_m1;
assign wr_pt_m1 = wr_pt-{{(WIDTH-1){1'b0}},1'b1}; 

// Shift register logic
integer i;
always @(*) begin
    for (i=0; i<DEPTH; i=i+1) begin
        token_array_next[i] = token_array[i]; // Initial value (hold previous)
    end

    // Shift control
    if (allocate_token) begin
        for (i=1; i<DEPTH; i=i+1) begin
            token_array_next[i-1] = token_array[i]; // Shift 
        end
    end
    // Write control (overwrite) 
    
    for (i=0; i<DEPTH; i=i+1) begin
       if (release_token & allocate_token) begin
          if($unsigned(i)==wr_pt_m1[WIDTH-1:0]) begin
           token_array_next[i] = release_token_num;
          end
       end
       else if (release_token & (i==wr_pt)) begin
           token_array_next[i] = release_token_num;
       end
    end
end 

integer j;
always @ (posedge clk or negedge rstn) begin
   if(!rstn) begin
      for (j=0; j<DEPTH; j=j+1) begin
         token_array[j] <= j; // Initialize value = 0,1,2,3,4...
      end
   end 
   else begin
      for (j=0; j<DEPTH; j=j+1) begin
         token_array[j] <= token_array_next[j];
      end
   end
end

// Full/empty/pointer
always @ (posedge clk or negedge rstn) begin
   if(!rstn) begin
       token_full       <= 1'b1;
       token_empty      <= 1'b0;
       num_tokens_avail <= DEPTH;
   end
   else begin
      if (release_token & (~(allocate_token))) begin
         num_tokens_avail <= num_tokens_avail + {{(CNT_WIDTH-1){1'b0}},1'b1};
         token_empty      <= 1'b0;
         if (num_tokens_avail == (DEPTH-1)) begin
            token_full    <= 1'b1;
         end
      end
      else if ((~(release_token)) & allocate_token) begin
         num_tokens_avail <= num_tokens_avail - {{(CNT_WIDTH-1){1'b0}},1'b1};
         token_full       <= 1'b0;
         if (num_tokens_avail == {{(CNT_WIDTH-1){1'b0}},1'b1}) begin // num_tokens_avail == 1
            token_empty   <= 1'b1;
         end
      end

   end
end

`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions, Checks, etc.
//------------------------------------------------------------------------------
`ifdef SNPS_ASSERT_ON


// disable coverage collection as this is a check in SVA only        
// VCS coverage off
// Logic to check all entrys are unique (for assertion)
integer entryX;
integer entryY;
reg     not_uniq;
always @(*) begin
    not_uniq=0;
    for (entryX=0; entryX < num_tokens_avail; entryX=entryX+1) begin
        for (entryY=0; entryY < num_tokens_avail; entryY=entryY+1) begin
            if (entryX!=entryY & token_array[entryX] == token_array[entryY]) begin
                not_uniq = 1;
            end
        end
    end
end

// VCS coverage on

//-------------
// Assertions 
//-------------
property p_ie_token_fifo_no_underflow;
  @ (posedge clk) disable iff (~rstn)
  allocate_token |-> num_tokens_avail>0; 
endproperty

property p_ie_token_fifo_no_overflow; 
  @ (posedge clk) disable iff (~rstn)
  release_token |-> num_tokens_avail<DEPTH;
endproperty

property p_ie_token_fifo_full_check; 
  @ (posedge clk) disable iff (~rstn)
  ((num_tokens_avail==DEPTH) == token_full);
endproperty

property p_ie_token_fifo_empty_check; 
  @ (posedge clk) disable iff (~rstn)
  ((num_tokens_avail==0) == token_empty);
endproperty

property p_ie_token_fifo_must_be_uniq;
  @ (posedge clk) disable iff (~rstn)
  (not_uniq==0);
endproperty

property p_ie_token_fifo_num_tokens_avail_check;
  @ (posedge clk) disable iff (~rstn)
  (num_tokens_avail<= DEPTH);
endproperty

// Check that FIFO is never overflow
a_ie_token_fifo_no_underflow : assert property (p_ie_token_fifo_no_underflow)
else $error("%m %t ie_token_fifo underflow. allocate_token==1 is not allowed when token_empty==1", $time);

// Check that FIFO is never underflow
a_ie_token_fifo_no_overflow : assert property (p_ie_token_fifo_no_overflow)
else $error("%m %t ie_token_fifo overflow. release_token==1 is not allowed when no token is allocated", $time);

// Check that token_full is correct  
a_ie_token_fifo_full_check : assert property (p_ie_token_fifo_full_check)
else $error("%m %t token_full is not correct", $time);

// Check that token_empty is correct
a_ie_token_fifo_empty_check : assert property (p_ie_token_fifo_empty_check)
else $error("%m %t token_empty is not correct", $time);

// Check that all valid entrys are unique 
a_ie_token_fifo_must_be_uniq : assert property (p_ie_token_fifo_must_be_uniq)
else $error("%m %t ie_token_fifo token is not uniq.", $time);

// Check that num_tokens_avail is never exceeded to DEPTH
a_ie_token_fifo_num_tokens_avail_check : assert property (p_ie_token_fifo_num_tokens_avail_check)
else $error("%m %t num_tokens_avail must be less than or equal to DEPTH parameter.", $time);

//-------------
// Coverpoints 
//-------------
covergroup cg_ie_token_fifo @(posedge clk);

  // Observe FIFO's usage
  cp_ie_token_fifo_usage : coverpoint (num_tokens_avail) iff(rstn) {
     bins        usage[] = {[0:DEPTH]};
     bins         full   = {DEPTH};
     bins    half_full   = {DEPTH/2};
     bins almost_empty   = {1};
     bins        empty   = {0};
  }
  
  // Observe allocate and release token                      
  cp_ie_token_fifo_wr_rd : coverpoint ({allocate_token, release_token}) iff(rstn) {
     bins allocate_only        = {{1'b1,1'b0}};
     bins release_only         = {{1'b0,1'b1}};
     bins allocate_and_release = {{1'b1,1'b1}};
  }

endgroup : cg_ie_token_fifo

cg_ie_token_fifo cg_ie_token_fifo_inst = new;

`endif // SNPS_ASSERT_ON
`endif  // SYNTHESIS

endmodule
