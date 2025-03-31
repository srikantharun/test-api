
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

//
// Description : DWC_ddrctl_bcm00_mx.v Verilog module for DWC_ddrctl
//
// DesignWare IP ID: a4d0ab1b
//
////////////////////////////////////////////////////////////////////////////////


module DWC_ddrctl_bcm00_mx (
    a0,
    a1,
    s,
    z
);


// spyglass disable_block W146
// SMD: Explicit named association is recommended in instance references
// SJ: Current release uses ordered list for parameters, the design is checked and verified without errors

  input  a0;    // input a0
  input  a1;    // input a1
  input  s;     // clock select
  output z;     // output clock

`ifdef DWC_MX_SRC
  `DWC_MX_SRC
`else
  assign z = s ? // synopsys infer_mux_override
             a1 : a0;
`endif

// spyglass enable_block W146
endmodule
