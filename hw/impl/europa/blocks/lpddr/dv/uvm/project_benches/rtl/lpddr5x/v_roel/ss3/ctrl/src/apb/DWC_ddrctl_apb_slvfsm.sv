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

// Revision $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/apb/DWC_ddrctl_apb_slvfsm.sv#2 $
`include "DWC_ddrctl_all_defs.svh"

`include "apb/DWC_ddrctl_reg_pkg.svh"

module DWC_ddrctl_apb_slvfsm
import DWC_ddrctl_reg_pkg::*;
  #(parameter N_APBFSMSTAT =
                            5
    )
  (input                     pclk,
   input                     presetn,
   input                     psel,
   input                     penable,
   input                     pwrite,
   output [N_APBFSMSTAT-1:0] apb_slv_cs,
   output [N_APBFSMSTAT-1:0] apb_slv_ns,
   output reg                pready,
   output                    write_en,
   output                    write_en_pulse,
   output reg                write_en_s0,
   output reg                store_rqst
   );

   localparam IDLE       = 5'b00001;
   localparam ADDRDECODE = 5'b00010;
   localparam DATALATCH  = 5'b00100;
   localparam SAMPLERDY  = 5'b01000;
   localparam WAITACK    = 5'b10000;

   reg [N_APBFSMSTAT-1:0]    current_state;
   reg [N_APBFSMSTAT-1:0]    next_state;
   reg                       pready_i;

   localparam TIMEOUTW = 7;
   localparam FIXCNTW = 2;
      
   assign apb_slv_ns = next_state;
   assign apb_slv_cs = current_state;

   assign write_en = psel & penable & pwrite;
   assign write_en_pulse = (apb_slv_ns==ADDRDECODE) ? write_en : 1'b0;



   always @ (posedge pclk or negedge presetn) begin : sample_pclk_state_PROC
      if (~presetn) begin
         current_state <= 
                          IDLE;
         pready        <= 1'b0;
         write_en_s0   <= 1'b0;
      end else begin
         current_state <= next_state;
         pready        <= pready_i;
         write_en_s0   <= write_en_pulse;
      end
   end

   always @ (*) begin : next_fsm_combo_PROC
      store_rqst=1'b0;
      pready_i = 1'b0;
      case (current_state)
        IDLE: begin
           if (psel & penable) begin
              next_state = ADDRDECODE;
           end else begin
              next_state = IDLE;
           end
        end        
        ADDRDECODE: begin
           if(pwrite) begin
                 store_rqst = 1'b1;
                 next_state = SAMPLERDY;
                 pready_i   = 1'b1;
           end else begin
              next_state = DATALATCH;
           end
        end 
        DATALATCH : begin
           pready_i   = 1'b1;
           next_state = SAMPLERDY;
        end
        default   : next_state = IDLE;
      endcase
   end

endmodule
