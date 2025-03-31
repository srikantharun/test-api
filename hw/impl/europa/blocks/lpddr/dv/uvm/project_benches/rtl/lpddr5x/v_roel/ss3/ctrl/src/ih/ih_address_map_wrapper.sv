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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ih/ih_address_map_wrapper.sv#3 $
// -------------------------------------------------------------------------
// Description:
//       This module is a wrapper of ih_address_map
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"

module ih_address_map_wrapper 
import DWC_ddrctl_reg_pkg::*;
(
     am_block
    ,am_critical_dword
    ,am_row
    ,am_bg_bank
    ,am_cpu_address
    ,am_rank
    ,bg_b16_addr_mode
    ,am_cs_offset_bit0
    ,am_bg_offset_bit0
    ,am_bg_offset_bit1
    ,am_bs_offset_bit0
    ,am_bs_offset_bit1
    ,am_bs_offset_bit2 
    ,am_column_offset_bit3
    ,am_column_offset_bit4
    ,am_column_offset_bit5
    ,am_column_offset_bit6
    ,am_column_offset_bit7
    ,am_column_offset_bit8
    ,am_column_offset_bit9
    ,am_column_offset_bit10
    ,am_row_offset_bit0
    ,am_row_offset_bit1
    ,am_row_offset_bit2
    ,am_row_offset_bit3
    ,am_row_offset_bit4
    ,am_row_offset_bit5
    ,am_row_offset_bit6
    ,am_row_offset_bit7
    ,am_row_offset_bit8
    ,am_row_offset_bit9
    ,am_row_offset_bit10
    ,am_row_offset_bit11
    ,am_row_offset_bit12
    ,am_row_offset_bit13
    ,am_row_offset_bit14
    ,am_row_offset_bit15
    ,am_row_offset_bit16
    ,am_row_offset_bit17


 //Inputs/outputs for het mapping
    ,reg_ddrc_bank_hash_en
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
    ,co_ih_clk
    ,core_ddrc_rstn
    ,cmd_valid
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON
    ,reg_ddrc_lpddr5
);


    parameter COL_BITS         = `MEMC_BLK_BITS + `MEMC_WORD_BITS;
    parameter CID_WIDTH        = `UMCTL2_CID_WIDTH;
    parameter LRANK_BITS       = `UMCTL2_LRANK_BITS;
    parameter AM_DCH_WIDTH     = 6;
    parameter AM_CS_WIDTH      = 6;
    parameter AM_CID_WIDTH     = 6;
    parameter AM_BANK_WIDTH    = 6;
    parameter AM_BG_WIDTH      = 6;
    parameter AM_ROW_WIDTH     = 5;
    parameter AM_COL_WIDTH_H   = 5;
    parameter AM_COL_WIDTH_L   = 4;



// IO DECLARATION
    output [`MEMC_BLK_BITS-1:0]         am_block;
    output [`MEMC_WORD_BITS-1:0]        am_critical_dword;
    output [`MEMC_PAGE_BITS-1:0]        am_row;
    output [`MEMC_BG_BANK_BITS-1:0]     am_bg_bank;
    input                               bg_b16_addr_mode;
    output [LRANK_BITS-1:0]             am_rank;
    input  [`MEMC_HIF_ADDR_WIDTH-1:0]   am_cpu_address;

    input  [AM_CS_WIDTH-1:0]            am_cs_offset_bit0;

    input  [AM_BG_WIDTH-1:0]            am_bg_offset_bit0;
    input  [AM_BG_WIDTH-1:0]            am_bg_offset_bit1;

    input  [AM_BANK_WIDTH-1:0]          am_bs_offset_bit0;
    input  [AM_BANK_WIDTH-1:0]          am_bs_offset_bit1;
    input  [AM_BANK_WIDTH-1:0]          am_bs_offset_bit2;

    input  [AM_COL_WIDTH_L-1:0]         am_column_offset_bit3;
    input  [AM_COL_WIDTH_L-1:0]         am_column_offset_bit4;
    input  [AM_COL_WIDTH_L-1:0]         am_column_offset_bit5;
    input  [AM_COL_WIDTH_L-1:0]         am_column_offset_bit6;
    input  [AM_COL_WIDTH_H-1:0]         am_column_offset_bit7;
    input  [AM_COL_WIDTH_H-1:0]         am_column_offset_bit8;
    input  [AM_COL_WIDTH_H-1:0]         am_column_offset_bit9;
    input  [AM_COL_WIDTH_H-1:0]         am_column_offset_bit10;

    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit0;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit1;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit2;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit3;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit4;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit5;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit6;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit7;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit8;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit9;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit10;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit11;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit12;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit13;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit14;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit15;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit16;
    input  [AM_ROW_WIDTH-1:0]           am_row_offset_bit17;



   input                                                     reg_ddrc_bank_hash_en;
`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
   input                                                     co_ih_clk;
   input                                                     core_ddrc_rstn;
   input                                                     cmd_valid;
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON
   input                                                     reg_ddrc_lpddr5;

// Intermediate wire
    // For map0
    wire    [`MEMC_BLK_BITS-1:0]        map0_am_block;
    wire    [`MEMC_WORD_BITS-1:0]       map0_am_critical_dword;
    wire    [`MEMC_PAGE_BITS-1:0]       map0_am_row;
    wire    [`MEMC_BG_BANK_BITS-1:0]    map0_am_bg_bank;
    wire    [LRANK_BITS-1:0]            map0_am_rank;

    logic [`MEMC_BG_BANK_BITS-1:0]      map0_am_bg_bank_int;
    logic [`MEMC_BG_BANK_BITS-1:0]      map0_am_bg_bank_rev_int;
    logic [`MEMC_BG_BANK_BITS-1:0]      map0_bank_hash_in;

    localparam MUX_SEL_WIDTH               =    (`DDRCTL_DDR_EN==1) ? 2 : 1; 
    localparam TOTAL_BANK_BITS_WIDTH       =    3; 
    logic [MUX_SEL_WIDTH-1:0]                   map0_am_mux_sel;
    logic [TOTAL_BANK_BITS_WIDTH-1:0]           map0_total_bank_bits;
    logic [`MEMC_BG_BANK_BITS-1:0]              map0_bh_bg_bank;
    logic [`MEMC_BG_BANK_BITS-1:0]              map0_bh_bg_bank_rev;

   assign am_block          = map0_am_block;
   assign am_critical_dword = map0_am_critical_dword;
   assign am_row            = map0_am_row;
   assign am_bg_bank        = map0_am_bg_bank;
   assign am_rank           = map0_am_rank;


//Number of Bank bits is derived using the Address mapping registers. 
//In DDR54 configurations, the number of bank bits can be 3,4,5 
//In LPDDR54 configurations, the number of bank bits can be 3,4

   assign map0_total_bank_bits =   ({{(TOTAL_BANK_BITS_WIDTH-1){1'b0}},1'b1})  +
                                       ((am_bs_offset_bit1 != {AM_BANK_WIDTH{1'b1}}) ? {{(TOTAL_BANK_BITS_WIDTH-1){1'b0}},1'b1} : {(TOTAL_BANK_BITS_WIDTH){1'b0}}) + 
                                       ((am_bs_offset_bit2 != {AM_BANK_WIDTH{1'b1}}) ? {{(TOTAL_BANK_BITS_WIDTH-1){1'b0}},1'b1} : {(TOTAL_BANK_BITS_WIDTH){1'b0}}) + //LPDDR4 only 
                                       ((am_bg_offset_bit0 != {AM_BG_WIDTH{1'b1}})   ? {{(TOTAL_BANK_BITS_WIDTH-1){1'b0}},1'b1} : {(TOTAL_BANK_BITS_WIDTH){1'b0}}) + //LPDDR5 only
                                       ((am_bg_offset_bit1 != {AM_BG_WIDTH{1'b1}})   ? {{(TOTAL_BANK_BITS_WIDTH-1){1'b0}},1'b1} : {(TOTAL_BANK_BITS_WIDTH){1'b0}});  //LPDDR5 only
                                                                 

      assign map0_am_mux_sel = (map0_total_bank_bits == 3'h4) ? {(MUX_SEL_WIDTH){1'b1}} : {(MUX_SEL_WIDTH){1'b0}}; 


      //am_bg_bank/map0_am_bg_bank_int contains {Bank,BG}.
      //This is first inverted using the bit widths {BG,Bank}
      //In LPDDR5 mode, the switch occurs always. 
      assign map0_am_bg_bank_rev_int = (reg_ddrc_lpddr5) ? ({map0_am_bg_bank_int[1:0],map0_am_bg_bank_int[3:2]}) : 
                                                             map0_am_bg_bank_int;

      //In cases where BA1 is not used, am_mux_sel will be 3 , 
      //The Input to the Bank Hash Module is truncated accordingly. 
      //BG bits may not be used, there is no impact to this code since it is at MSB.  

     assign map0_bank_hash_in        = ((reg_ddrc_lpddr5) && (am_bs_offset_bit1 == {AM_BANK_WIDTH{1'b1}})) ? {1'b0, map0_am_bg_bank_rev_int[3:2], map0_am_bg_bank_rev_int[0]} : 
                                                                                                              map0_am_bg_bank_rev_int;       

//Mapping 0 Bank Hash Instantiation.

//Bank Hash Instantiation
  dwc_ddrctl_ih_bankhash
   #(
    .BANK_WIDTH    (`MEMC_BANK_BITS)
   ,.BG_WIDTH      (`MEMC_BG_BITS)
   ,.ROW_WIDTH     (`MEMC_PAGE_BITS)
   ,.MUX_SEL_WIDTH (MUX_SEL_WIDTH) 
  ) U_ih_bankhash_map0 (
     .am_row      (map0_am_row)
    ,.am_bg_bank  (map0_bank_hash_in)
    ,.am_mux_sel  (map0_am_mux_sel)
    ,.bh_bg_bank  (map0_bh_bg_bank_rev)
);

      //In LPDDR5 mode,the switch needs to occur. 
      // if all bits are only Bank bits. they are used directly
      assign map0_bh_bg_bank = (reg_ddrc_lpddr5) ? ((am_bs_offset_bit1 == {AM_BANK_WIDTH{1'b1}}) ? {1'b0, map0_bh_bg_bank_rev[0],  map0_bh_bg_bank_rev[2:1]}    : 
                                                                                                     {      map0_bh_bg_bank_rev[1:0],map0_bh_bg_bank_rev[3:2]}) : map0_bh_bg_bank_rev;


`ifdef SNPS_ASSERT_ON
  `ifndef SYNTHESIS
  property p_bh_bg_bank_driven_to_x;
          @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (cmd_valid && reg_ddrc_bank_hash_en) |-> ~(|((map0_bh_bg_bank === ({`MEMC_BG_BANK_BITS{1'bx}})) | (map0_bh_bg_bank === ({`MEMC_BG_BANK_BITS{1'bz}}))));
  endproperty 
  
  asrt_bh_bg_bank_driven_to_x : assert property (p_bh_bg_bank_driven_to_x)
    else $error ("%m @ %t bh_bg_bank output is set to x or z %h", $time, map0_bh_bg_bank);
  
 
  property p_invalid_bank_bit_asserted;
     @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) 
       (reg_ddrc_bank_hash_en && cmd_valid && (am_bs_offset_bit1 == 6'h3F)) |-> ~(map0_bh_bg_bank[`MEMC_BG_BANK_BITS-1]); 
  endproperty
  
  
  asrt_invalid_bank_bit_asserted : assert property (p_invalid_bank_bit_asserted)
    else $error ("%m @ %t Bank bit1 is not programmed but is being asserted in map0_bh_bg_bank %h", $time, map0_bh_bg_bank);
 
  property p_am_mux_sel_invalid;
     @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (reg_ddrc_bank_hash_en && cmd_valid) |-> ~(map0_am_mux_sel == 2'b11) ; 
  endproperty
    
  asrt_am_mux_sel_invalid : assert property (p_am_mux_sel_invalid)
    else $error ("%m @ %t am_mux_sel got invalid value - map0_am_mux_sel %h", $time, map0_am_mux_sel);
  
  property p_am_total_banks_invalid;
     @(posedge co_ih_clk) disable iff (~core_ddrc_rstn) (reg_ddrc_bank_hash_en && cmd_valid) |-> ((map0_total_bank_bits <= 5)  && (map0_total_bank_bits>=3));
  endproperty
    
  asrt_am_total_banks_invalid : assert property (p_am_total_banks_invalid)
    else $error ("%m @ %t map0_total_bank_bits got invalid value - map0_total_bank_bits %h", $time, map0_total_bank_bits);

 
  `endif //SYNTHESIS
`endif //SNPS_ASSERT_ON


  assign map0_am_bg_bank = reg_ddrc_bank_hash_en ? map0_bh_bg_bank : map0_am_bg_bank_int;


// Instantiation

//-----------------------
// ih_address_map0 
//-----------------------
ih_address_map_pkt
  #(
         .COL_BITS                      (COL_BITS                     )
        ,.CID_WIDTH                     (CID_WIDTH                    )
        ,.LRANK_BITS                    (LRANK_BITS                   )
        ,.AM_DCH_WIDTH                  (AM_DCH_WIDTH                 )
        ,.AM_CS_WIDTH                   (AM_CS_WIDTH                  )
        ,.AM_CID_WIDTH                  (AM_CID_WIDTH                 )
        ,.AM_BANK_WIDTH                 (AM_BANK_WIDTH                )
        ,.AM_BG_WIDTH                   (AM_BG_WIDTH                  )
        ,.AM_ROW_WIDTH                  (AM_ROW_WIDTH                 )
        ,.AM_COL_WIDTH_H                (AM_COL_WIDTH_H               )
        ,.AM_COL_WIDTH_L                (AM_COL_WIDTH_L               )
) ih_address_map_pkt0 (
         .am_block                      (map0_am_block                )
        ,.am_critical_dword             (map0_am_critical_dword       )
        ,.am_row                        (map0_am_row                  )
        ,.am_bg_bank                    (map0_am_bg_bank_int          )
      
        ,.am_rank                       (map0_am_rank                 )


        ,.am_cpu_address                (am_cpu_address               )

        ,.bg_b16_addr_mode              (bg_b16_addr_mode             )

        ,.am_cs_offset_bit0             (am_cs_offset_bit0            )
        ,.am_bs_offset_bit0             (am_bs_offset_bit0            )
        ,.am_bs_offset_bit1             (am_bs_offset_bit1            )
        ,.am_bs_offset_bit2             (am_bs_offset_bit2            )
        ,.am_bg_offset_bit0             (am_bg_offset_bit0            )
        ,.am_bg_offset_bit1             (am_bg_offset_bit1            )
        ,.am_row_offset_bit0            (am_row_offset_bit0           )
        ,.am_row_offset_bit1            (am_row_offset_bit1           )
        ,.am_row_offset_bit2            (am_row_offset_bit2           )
        ,.am_row_offset_bit3            (am_row_offset_bit3           )
        ,.am_row_offset_bit4            (am_row_offset_bit4           )
        ,.am_row_offset_bit5            (am_row_offset_bit5           )
        ,.am_row_offset_bit6            (am_row_offset_bit6           )
        ,.am_row_offset_bit7            (am_row_offset_bit7           )
        ,.am_row_offset_bit8            (am_row_offset_bit8           )
        ,.am_row_offset_bit9            (am_row_offset_bit9           )
        ,.am_row_offset_bit10           (am_row_offset_bit10          )
        ,.am_row_offset_bit11           (am_row_offset_bit11          )
        ,.am_row_offset_bit12           (am_row_offset_bit12          )
        ,.am_row_offset_bit13           (am_row_offset_bit13          )
        ,.am_row_offset_bit14           (am_row_offset_bit14          )
        ,.am_row_offset_bit15           (am_row_offset_bit15          )
        ,.am_row_offset_bit16           (am_row_offset_bit16          )
        ,.am_row_offset_bit17           (am_row_offset_bit17          )
        ,.am_column_offset_bit3         (am_column_offset_bit3        )
        ,.am_column_offset_bit4         (am_column_offset_bit4        )
        ,.am_column_offset_bit5         (am_column_offset_bit5        )
        ,.am_column_offset_bit6         (am_column_offset_bit6        )
        ,.am_column_offset_bit7         (am_column_offset_bit7        )
        ,.am_column_offset_bit8         (am_column_offset_bit8        )
        ,.am_column_offset_bit9         (am_column_offset_bit9        )
        ,.am_column_offset_bit10        (am_column_offset_bit10       )
);



endmodule // ih_address_map_wapper
