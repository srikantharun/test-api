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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_mux.sv#2 $
// -------------------------------------------------------------------------
// Description:
// Simple mux 
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_mux 
  #(
    parameter ADDRW = 4,
    parameter NUM_INPUTS = 1 << ADDRW,
    parameter DATAW=8
    )
   (
    input   [DATAW*NUM_INPUTS -1:0]      in_port,
    input   [ADDRW-1:0]                  sel,
    output  [DATAW-1:0]                  out_port
    );
   
  localparam  NUM_INPUTS_POW2 = 2**(ADDRW);
  wire [DATAW-1:0]     in_port_a [0:NUM_INPUTS_POW2-1];
   
  genvar i;

  generate
    for (i = 0; i < NUM_INPUTS_POW2; i=i+1) begin : in_port_a_GEN
      if(NUM_INPUTS_POW2==NUM_INPUTS) begin
        assign in_port_a[i]  = in_port[i*DATAW+:DATAW];
      end else begin
        if(i<NUM_INPUTS) begin
          assign in_port_a[i]  = in_port[i*DATAW+:DATAW];
        end else begin
          assign in_port_a[i]  = {DATAW{1'b0}};
        end
      end
    end
  endgenerate

  assign out_port = in_port_a[sel];   
endmodule // te_mux

