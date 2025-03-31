//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/xpi/DWC_ddr_umctl2_xpi_iecc_info.sv#3 $
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

/******************************************************************************
 *                                                                            *
 * DESCRIPTION: Inline ECC info generator                                     *
 *                                                                            *
 *****************************************************************************/

`include "DWC_ddrctl_all_defs.svh"
module DWC_ddr_umctl2_xpi_iecc_info
   #( 
      parameter M_ADDRW       = 32,
      parameter REG_ID_WIDTH  = 3,
      parameter BRW           = 3,
      parameter ECC_H3_WIDTH  = 6,
      parameter ECC_RM_WIDTH  = 7,
      parameter ECC_RMG_WIDTH = 2
   )
   (
      input [M_ADDRW-1:0]        addr_in,
      input [ECC_RM_WIDTH-1:0]   ecc_region_map,
      input [ECC_RMG_WIDTH-1:0]  ecc_region_map_granu,
      input                      ecc_region_map_other,
      input [BRW-1:0]            reg_xpi_burst_rdwr,
      input [ECC_H3_WIDTH-1:0]   h3_iecc_col_mask,
      input                      ecc_en,
      output                     ecc_blk_valid,
      output                     ecc_blk_end
   );

   localparam BL_MASKW  = 7;
   localparam ECC_H3_WIDTH_INT  = `UMCTL_LOG2(M_ADDRW);
   localparam M_ADDRW_NP2  = 2**(ECC_H3_WIDTH_INT);
   
   // region identifier
   wire [REG_ID_WIDTH-1:0] ecc_region_id;
   // bl mask
   reg [BL_MASKW-1:0] bl_mask;
   wire [BL_MASKW-1:0] addr_mask;
   wire ecc_hole;
   wire ext_hbits_vld;
   wire [7:0] ecc_region_map_ext; // extend ECC_RM_WIDTH to 8 bits to avoid X state.
   wire       ecc_region_map_bit7;
   wire       ecc_region_lower;
   wire       ecc_region_other;

   assign ecc_region_map_bit7 = ~|ecc_region_map_granu ? 1'b0 : ecc_region_map_other;
   assign ecc_region_map_ext = { ecc_region_map_bit7, ecc_region_map};
   
   
   wire [ECC_H3_WIDTH_INT-1:0] h3_iecc_col_mask_int;
   wire [M_ADDRW_NP2-1:0] addr_in_tmp;
   generate 
     if(M_ADDRW_NP2==M_ADDRW) begin:Proc_M_ADDRW_pow2 
       assign addr_in_tmp = addr_in; 
     end
     else begin : Proc_M_ADDRW_nt_pow2 // M_ADDRW_NP2 always > M_ADDRW if M_ADDRW_NP2 always != M_ADDRW
       assign addr_in_tmp = {{(M_ADDRW_NP2-M_ADDRW){1'b0}},addr_in};
     end
   endgenerate
   // ECC_H3_WIDTH_INT will always be > ECC_H3_WIDTH
   // Pad 0 at msb if width dont match
   generate 
     if (ECC_H3_WIDTH_INT==ECC_H3_WIDTH) begin: Proc_ecc_h3_pow2
       assign h3_iecc_col_mask_int = h3_iecc_col_mask;
     end
     else if (ECC_H3_WIDTH_INT<ECC_H3_WIDTH) begin: Proc_ecc_h3_int_lt_ext
       assign h3_iecc_col_mask_int = h3_iecc_col_mask[ECC_H3_WIDTH_INT-1:0];
     end
     else begin: Proc_ecc_h3_nt_pow2 // ECC_H3_WIDTH_INT is always >  ECC_H3_WIDTH if ECC_H3_WIDTH_INT!=ECC_H3_WIDTH
       assign h3_iecc_col_mask_int = {{(ECC_H3_WIDTH_INT-ECC_H3_WIDTH){1'b0}},h3_iecc_col_mask};
     end
   endgenerate
   
   assign ecc_hole = &addr_in_tmp[h3_iecc_col_mask_int-:REG_ID_WIDTH];

   // extract identifier from address
   
   //spyglass disable_block TA_09
   //SMD: Net 'DWC_ddrctl.h3_iecc_col_mask[5]' [in 'DWC_ddrctl'] is not observable[affected by other input(s)].
   //SJ: Functionally correct. In some configs, highest_col_bit[5] might never change its value.
   //spyglass disable_block SelfDeterminedExpr-ML
   //SMD: Self determined expression '(h3_iecc_col_mask - ecc_region_map_granu)' found in module 'DWC_ddr_umctl2_xpi_iecc_info'
   //SJ: No suitable (better) re-coding found
   wire [ECC_H3_WIDTH_INT-1:0] ecc_region_id_index;
   assign ecc_region_id_index = (h3_iecc_col_mask_int-ecc_region_map_granu);
   assign ecc_region_id = addr_in_tmp[ecc_region_id_index-:REG_ID_WIDTH];
   //spyglass enable_block SelfDeterminedExpr-ML
   //spyglass enable_block TA_09
   
   
   assign ext_hbits_vld = ecc_region_map_granu==2'b01 ? ~|addr_in_tmp[h3_iecc_col_mask_int -: 1] :
                          ecc_region_map_granu==2'b10 ? ~|addr_in_tmp[h3_iecc_col_mask_int -: 2] :
                          ecc_region_map_granu==2'b11 ? ~|addr_in_tmp[h3_iecc_col_mask_int -: 3] :
                                                         1'b1;

   assign ecc_region_lower = ext_hbits_vld & ecc_region_map_ext[ecc_region_id];

   assign ecc_region_other = ecc_region_map_other & (
                             ecc_region_map_granu==2'b01 ? |addr_in_tmp[h3_iecc_col_mask_int -: 1] :
                             ecc_region_map_granu==2'b10 ? |addr_in_tmp[h3_iecc_col_mask_int -: 2] :
                             ecc_region_map_granu==2'b11 ? |addr_in_tmp[h3_iecc_col_mask_int -: 3] :
                                                            1'b0
                              );
   // mux register setting based on identifier
   assign ecc_blk_valid = (ecc_hole ) ? 1'b0 : (ecc_region_other | ecc_region_lower) & ecc_en;

   // build mask based on SDRAM bl
   always @(*) begin: bl_mask_PROC
      case (reg_xpi_burst_rdwr)
         {{(BRW-3){1'd0}},3'd4}  : bl_mask = 7'b1000111; // bl8   
         {{(BRW-4){1'd0}},4'd8}  : bl_mask = 7'b0001111; // bl16
         default: bl_mask = {BL_MASKW{1'b1}}; // not supported 
      endcase
   end
   // OR bl mask with address LSB
   assign addr_mask = bl_mask | addr_in[BL_MASKW-1:0];
   // AND reduction to extract blk_end
   assign ecc_blk_end = ecc_hole ? 1'b0 : &addr_mask & ecc_blk_valid;

endmodule // DWC_ddr_umctl2_xpi_iecc_info
