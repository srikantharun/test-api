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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/select_nets/select_net_oh.sv#2 $
// -------------------------------------------------------------------------
// Description:
//           Mux using one hot input
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module select_net_oh 
  #(
    parameter NUM_INPUTS = 1,
    parameter DATAW=8
    )
   (
    input   [DATAW*NUM_INPUTS -1:0]      din,
    input   [NUM_INPUTS-1:0]             sel_oh,
    output  [DATAW-1:0]                  dout
    );
   

  wire [DATAW*NUM_INPUTS -1:0] sel_oh_ext;
  // e.g.) sel_oh = 0010, DATAW=5
  // extended_sel_oh = 00000_00000_11111_00000
  wire [DATAW*NUM_INPUTS -1:0] din_masked;
  // sel_oh_ext & din. unselected din is masked to 0
    
  wire [DATAW*NUM_INPUTS -1:0] din_masked_tr;
  // convert data
  // 01101_00000_00000_00000 -->  0000_1000_1000_0000_1000 

  assign din_masked = din & sel_oh_ext; // Mask unselected bits

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '(data_idx * NUM_INPUTS)' found in module 'select_net_oh'
//SJ: This coding style is acceptable and there is no plan to change it.
  
//spyglass disable_block TA_09
//SMD: Net 'DWC_ddrctl.U_ddrc_dch1.U_ddrc_cp_top.\ddrc_ctrl_inst[0].U_ddrc_cp .U_ddrc_cpf.teengine.RDreplace.RD_vpr_selnet.selected_in_oh[126:96]' [in 'select_net_hmatrix'] is not observable[affected by other input(s)]
//SJ: This is expected in non-power of two RD CAM depth configs because 'selected_in_oh[RD_CAM_ENTRIES_EXTEND:RD_CAM_ENTRIES]' are always 0.

  generate           
    genvar sel_idx, data_idx;

    for (data_idx=0;data_idx<DATAW;data_idx=data_idx+1) begin : data_idx_loop
      for (sel_idx=0;sel_idx<NUM_INPUTS;sel_idx=sel_idx+1) begin : sel_idx_loop
        assign sel_oh_ext[sel_idx*DATAW+data_idx] = sel_oh[sel_idx];
        // expand sel_oh

        assign din_masked_tr[data_idx*NUM_INPUTS+sel_idx] = din_masked[sel_idx*DATAW+data_idx];
      end 
      assign dout[data_idx] = (|din_masked_tr[data_idx*NUM_INPUTS+:NUM_INPUTS]); 
      // OR'd each bits
    end

  endgenerate
//spyglass enable_block TA_09
//spyglass enable_block SelfDeterminedExpr-ML

endmodule
