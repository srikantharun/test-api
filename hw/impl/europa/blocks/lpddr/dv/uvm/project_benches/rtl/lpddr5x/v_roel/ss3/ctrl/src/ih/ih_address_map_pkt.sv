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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_address_map_pkt.sv#2 $
// -------------------------------------------------------------------------
// Description:
//       MAP PKT module is a packet of ih_address_map and cid_cs_rank_map
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module ih_address_map_pkt 
import DWC_ddrctl_reg_pkg::*;
#(
   // parameter list
    parameter COL_BITS         = `MEMC_BLK_BITS + `MEMC_WORD_BITS
   ,parameter CID_WIDTH        = `UMCTL2_CID_WIDTH
   ,parameter LRANK_BITS       = `UMCTL2_LRANK_BITS   
   ,parameter AM_DCH_WIDTH     = 6
   ,parameter AM_CS_WIDTH      = 6
   ,parameter AM_CID_WIDTH     = 6
   ,parameter AM_BANK_WIDTH    = 6
   ,parameter AM_BG_WIDTH      = 6
   ,parameter AM_ROW_WIDTH     = 5
   ,parameter AM_COL_WIDTH_H   = 5
   ,parameter AM_COL_WIDTH_L   = 4
   
)(
   // IO DECLARATION
    output [`MEMC_BLK_BITS-1:0]                    am_block
   ,output [`MEMC_WORD_BITS-1:0]                   am_critical_dword
   ,output [`MEMC_PAGE_BITS-1:0]                   am_row
   ,output [`MEMC_BG_BANK_BITS-1:0]                am_bg_bank

   ,output [LRANK_BITS-1:0]                        am_rank


   ,input  [`MEMC_HIF_ADDR_WIDTH-1:0]              am_cpu_address


   ,input                                          bg_b16_addr_mode


   ,input  [AM_CS_WIDTH-1:0]                       am_cs_offset_bit0

   ,input  [AM_BANK_WIDTH-1:0]                     am_bs_offset_bit0
   ,input  [AM_BANK_WIDTH-1:0]                     am_bs_offset_bit1
   ,input  [AM_BANK_WIDTH-1:0]                     am_bs_offset_bit2

   ,input  [AM_BG_WIDTH-1:0]                       am_bg_offset_bit0
   ,input  [AM_BG_WIDTH-1:0]                       am_bg_offset_bit1

   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit0
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit1
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit2
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit3
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit4
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit5
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit6
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit7
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit8
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit9
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit10
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit11
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit12
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit13
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit14
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit15
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit16
   ,input  [AM_ROW_WIDTH-1:0]                      am_row_offset_bit17

   ,input  [AM_COL_WIDTH_L-1:0]                    am_column_offset_bit3
   ,input  [AM_COL_WIDTH_L-1:0]                    am_column_offset_bit4
   ,input  [AM_COL_WIDTH_L-1:0]                    am_column_offset_bit5
   ,input  [AM_COL_WIDTH_L-1:0]                    am_column_offset_bit6
   ,input  [AM_COL_WIDTH_H-1:0]                    am_column_offset_bit7
   ,input  [AM_COL_WIDTH_H-1:0]                    am_column_offset_bit8
   ,input  [AM_COL_WIDTH_H-1:0]                    am_column_offset_bit9
   ,input  [AM_COL_WIDTH_H-1:0]                    am_column_offset_bit10


);

// Intermediate wire

    wire    [`MEMC_RANK_BITS-1:0]               cs_init;

    // For map0
    wire    [`MEMC_BLK_BITS-1:0]                map0_am_block;
    wire    [`MEMC_WORD_BITS-1:0]               map0_am_critical_dword;
    wire    [`MEMC_PAGE_BITS-1:0]               map0_am_row;
    wire    [`MEMC_BG_BANK_BITS-1:0]            map0_am_bg_bank;
    wire    [`MEMC_RANK_BITS-1:0]               map0_am_rank_int; // For Internal (before CS/CID mapping)
    wire    [LRANK_BITS-1:0]                    map0_am_rank;



    assign cs_init = map0_am_rank_int;

// Output assignment
    assign  am_block           = map0_am_block;
    assign  am_critical_dword  = map0_am_critical_dword;
    assign  am_row             = map0_am_row;
    assign  am_bg_bank         = map0_am_bg_bank;
    assign  am_rank            = map0_am_rank;


assign  map0_am_rank = cs_init[`MEMC_RANK_BITS-1:0]; 


// Instantiation

//-----------------------
// ih_address_map0 
//-----------------------
ih_address_map
 ih_address_map0 (
// Output
    .am_block                   (map0_am_block              ),
    .am_critical_dword          (map0_am_critical_dword     ),
    .am_row                     (map0_am_row                ),
    .am_bg_bank                 (map0_am_bg_bank            ),
    .am_rank                    (map0_am_rank_int           ),
// Input
    .am_cs_offset_bit0          (am_cs_offset_bit0          ),

    .am_cpu_address             (am_cpu_address             ),

    .bg_b16_addr_mode           (bg_b16_addr_mode           ),   
    .am_bg_offset_bit0          (am_bg_offset_bit0          ),
    .am_bg_offset_bit1          (am_bg_offset_bit1          ),
    .am_row_offset_bit16        (am_row_offset_bit16        ),
    .am_row_offset_bit17        (am_row_offset_bit17        ),
    .am_bs_offset_bit0          (am_bs_offset_bit0          ),
    .am_bs_offset_bit1          (am_bs_offset_bit1          ),
    .am_bs_offset_bit2          (am_bs_offset_bit2          ),
    .am_column_offset_bit3      (am_column_offset_bit3      ),
    .am_column_offset_bit4      (am_column_offset_bit4      ),
    .am_column_offset_bit5      (am_column_offset_bit5      ),
    .am_column_offset_bit6      (am_column_offset_bit6      ),
    .am_column_offset_bit7      (am_column_offset_bit7      ),
    .am_column_offset_bit8      (am_column_offset_bit8      ),
    .am_column_offset_bit9      (am_column_offset_bit9      ),
    .am_column_offset_bit10     (am_column_offset_bit10     ),
    .am_row_offset_bit0         (am_row_offset_bit0         ),
    .am_row_offset_bit1         (am_row_offset_bit1         ),
    .am_row_offset_bit2         (am_row_offset_bit2         ),
    .am_row_offset_bit3         (am_row_offset_bit3         ),
    .am_row_offset_bit4         (am_row_offset_bit4         ),
    .am_row_offset_bit5         (am_row_offset_bit5         ),
    .am_row_offset_bit6         (am_row_offset_bit6         ),
    .am_row_offset_bit7         (am_row_offset_bit7         ),
    .am_row_offset_bit8         (am_row_offset_bit8         ),
    .am_row_offset_bit9         (am_row_offset_bit9         ),
    .am_row_offset_bit10        (am_row_offset_bit10        ),
    .am_row_offset_bit11        (am_row_offset_bit11        ),
    .am_row_offset_bit12        (am_row_offset_bit12        ),
    .am_row_offset_bit13        (am_row_offset_bit13        ),
    .am_row_offset_bit14        (am_row_offset_bit14        ),
    .am_row_offset_bit15        (am_row_offset_bit15        )
);


endmodule


