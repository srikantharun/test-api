//Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr_linkecc_encoder.sv#1 $
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
// ---    $Revision:
// -------------------------------------------------------------------------
// Description:
//    Write Link-ECC top module
// -------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module mr_linkecc_encoder
import DWC_ddrctl_reg_pkg::*;
#(
    parameter  PHY_DATA_WIDTH = `MEMC_DFI_TOTAL_DATA_WIDTH
   ,parameter  PHY_MASK_WIDTH = PHY_DATA_WIDTH/8
   ,parameter  DRAM_BYTE_NUM  = `MEMC_DRAM_TOTAL_BYTE_NUM
)
(
    input                        co_yy_clk
   ,input                        core_ddrc_rstn
   ,input                        ddrc_cg_en
   ,input                        reg_ddrc_wr_link_ecc_enable
   ,input  [DRAM_BYTE_NUM-1:0]   reg_ddrc_linkecc_poison_byte_sel
   ,input  [DRAM_BYTE_NUM-1:0]   reg_ddrc_linkecc_poison_dmi_sel
   ,input                        reg_ddrc_linkecc_poison_rw
   ,input                        reg_ddrc_linkecc_poison_type
   ,input                        reg_ddrc_linkecc_poison_inject_en
   ,input  [1:0]                 mr_ph_wr_ph
   ,input  [PHY_DATA_WIDTH-1:0]  mr_ph_wdata
   ,input  [PHY_MASK_WIDTH-1:0]  mr_ph_wdatamask
   ,input                        mr_ph_wdatavld
   ,input                        mr_ph_wdatavld_early

   ,output [1:0]                 sel_mr_ph_wr_ph
   ,output [PHY_DATA_WIDTH-1:0]  sel_mr_ph_wdata
   ,output [PHY_MASK_WIDTH-1:0]  sel_mr_ph_wdatamask
   ,output                       sel_mr_ph_wdatavld
   ,output                       sel_mr_ph_wdatavld_early
   ,output [PHY_MASK_WIDTH-1:0]  sel_mr_ph_wdata_link_ecc
   ,output                       ddrc_reg_wr_linkecc_poison_complete
);

//---------------------------- PARAMETERS --------------------------------------
localparam DQ_WIDTH  = `MEMC_DRAM_DATA_WIDTH;
localparam DMI_WIDTH = `MEMC_DRAM_DATA_WIDTH/8;
localparam NUM_BYTE  = `MEMC_DRAM_DATA_WIDTH/8;


//--------------------------------- WIRES --------------------------------------
wire  [PHY_MASK_WIDTH-1:0]        mr_ph_wdata_link_ecc_w;

reg   [1:0]                       mr_ph_wr_ph_1d;
reg   [1:0]                       mr_ph_wr_ph_2d;
reg                               mr_ph_wdatavld_1d;
reg                               mr_ph_wdatavld_2d;
reg   [PHY_DATA_WIDTH-1:0]        mr_ph_wdata_1d;
reg   [PHY_DATA_WIDTH-1:0]        mr_ph_wdata_2d;
reg   [PHY_MASK_WIDTH-1:0]        mr_ph_wdatamask_1d;
reg   [PHY_MASK_WIDTH-1:0]        mr_ph_wdatamask_2d;
reg                               mr_ph_wdatavld_early_1d;
reg                               mr_ph_wdatavld_early_2d;


wire  [PHY_DATA_WIDTH*2-1:0]      mr_ph_wdata_w;
wire  [PHY_MASK_WIDTH*2-1:0]      mr_ph_wdatamask_w;
reg   [PHY_MASK_WIDTH  -1:0]      lecc_cb_r;
wire  [NUM_BYTE*16-1: 0]          lecc_cb;

wire                              ram_vld_pe;
reg                               ram_vld_tgl;
reg                               ram_vld_pe_r;


//----------------------- COMBINATORIAL ASSIGNMENTS ----------------------------

// Select all output signals. If link-ECC is disabled, all signals should be bypassed.
assign sel_mr_ph_wr_ph          = (reg_ddrc_wr_link_ecc_enable)? mr_ph_wr_ph_2d          : mr_ph_wr_ph;
assign sel_mr_ph_wdata          = (reg_ddrc_wr_link_ecc_enable)? mr_ph_wdata_2d          : mr_ph_wdata;
assign sel_mr_ph_wdatamask      = (reg_ddrc_wr_link_ecc_enable)? mr_ph_wdatamask_2d      : mr_ph_wdatamask;
assign sel_mr_ph_wdatavld       = (reg_ddrc_wr_link_ecc_enable)? mr_ph_wdatavld_2d       : mr_ph_wdatavld;
assign sel_mr_ph_wdatavld_early = (reg_ddrc_wr_link_ecc_enable)? mr_ph_wdatavld_early_2d : mr_ph_wdatavld_early;
assign sel_mr_ph_wdata_link_ecc = (reg_ddrc_wr_link_ecc_enable)? mr_ph_wdata_link_ecc_w  : {PHY_MASK_WIDTH{1'b0}};


// Retiming all input signals.
always@(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(~core_ddrc_rstn) begin
    mr_ph_wr_ph_1d          <= 2'b00;
    mr_ph_wdata_1d          <= {PHY_DATA_WIDTH{1'b0}};
    mr_ph_wdatamask_1d      <= {PHY_MASK_WIDTH{1'b0}};
    mr_ph_wdatavld_1d       <= 1'b0;
    mr_ph_wdatavld_early_1d <= 1'b0;

    mr_ph_wr_ph_2d          <= 2'b00;
    mr_ph_wdata_2d          <= {PHY_DATA_WIDTH{1'b0}};
    mr_ph_wdatamask_2d      <= {PHY_MASK_WIDTH{1'b0}};
    mr_ph_wdatavld_2d       <= 1'b0;
    mr_ph_wdatavld_early_2d <= 1'b0;
  end
  else if(ddrc_cg_en) begin
    mr_ph_wr_ph_1d          <= mr_ph_wr_ph;
    mr_ph_wdata_1d          <= mr_ph_wdata;
    mr_ph_wdatamask_1d      <= mr_ph_wdatamask;
    mr_ph_wdatavld_1d       <= mr_ph_wdatavld;
    mr_ph_wdatavld_early_1d <= mr_ph_wdatavld_early;

    mr_ph_wr_ph_2d          <= mr_ph_wr_ph_1d;
    mr_ph_wdata_2d          <= mr_ph_wdata_1d;
    mr_ph_wdatamask_2d      <= mr_ph_wdatamask_1d;
    mr_ph_wdatavld_2d       <= mr_ph_wdatavld_1d;
    mr_ph_wdatavld_early_2d <= mr_ph_wdatavld_early_1d;
  end
end

// Detect poge edge of data valid
assign ram_vld_pe = mr_ph_wdatavld_1d & (~mr_ph_wdatavld_2d);

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    ram_vld_pe_r <= 0;
  end else if(ddrc_cg_en) begin
    ram_vld_pe_r <= ram_vld_pe;
  end
end

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    ram_vld_tgl <= 0;
  end else if(ddrc_cg_en) begin
      if(ram_vld_pe) begin
          ram_vld_tgl <= 1;
      end else if(mr_ph_wdatavld_2d) begin
          ram_vld_tgl <= ~ram_vld_tgl;
      end
  end
end

// All beats of wdata and wdatamask
assign mr_ph_wdata_w     = {mr_ph_wdata_1d,mr_ph_wdata_2d};
assign mr_ph_wdatamask_w = {mr_ph_wdatamask_1d, mr_ph_wdatamask_2d};

// ECC-code
assign mr_ph_wdata_link_ecc_w = (ram_vld_tgl)? lecc_cb[PHY_MASK_WIDTH-1:0] : lecc_cb_r;

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if (~core_ddrc_rstn) begin
    lecc_cb_r <= 0;
  end else if(ddrc_cg_en) begin
    lecc_cb_r <= lecc_cb[PHY_MASK_WIDTH +: PHY_MASK_WIDTH];
  end
end


// Poison complete
reg                        linkecc_poison_inject_complete;
wire                       linkecc_poison_tmg;
reg                        linkecc_poison_inject_en;
wire [DRAM_BYTE_NUM-1:0]   linkecc_poison_byte_sel;
wire [DRAM_BYTE_NUM-1:0]   linkecc_poison_dmi_sel;



assign linkecc_poison_tmg = linkecc_poison_inject_en & (~reg_ddrc_linkecc_poison_rw) & ram_vld_pe_r;
assign linkecc_poison_byte_sel = (linkecc_poison_tmg)? reg_ddrc_linkecc_poison_byte_sel : {DRAM_BYTE_NUM{1'b0}};
assign linkecc_poison_dmi_sel  = (linkecc_poison_tmg)? reg_ddrc_linkecc_poison_dmi_sel  : {DRAM_BYTE_NUM{1'b0}};

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
        linkecc_poison_inject_complete <= 1'b0;
    end else if(!reg_ddrc_linkecc_poison_inject_en) begin
        linkecc_poison_inject_complete <= 1'b0;
    end else if(reg_ddrc_linkecc_poison_inject_en && linkecc_poison_tmg) begin
        linkecc_poison_inject_complete <= 1'b1;
    end
end
assign ddrc_reg_wr_linkecc_poison_complete = linkecc_poison_inject_complete;

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
        linkecc_poison_inject_en <= 1'b0;
    end else if(!reg_ddrc_linkecc_poison_inject_en || linkecc_poison_inject_complete || linkecc_poison_tmg) begin
        linkecc_poison_inject_en <= 1'b0;
    end else if(!linkecc_poison_inject_complete && reg_ddrc_linkecc_poison_inject_en) begin
        linkecc_poison_inject_en <= 1'b1;
    end
end


// Generate ECC-code
genvar GEN_BYTES_LECC;
generate
  for (GEN_BYTES_LECC=0; GEN_BYTES_LECC<NUM_BYTE; GEN_BYTES_LECC=GEN_BYTES_LECC+1) begin : gen_lecc
       mr_linkecc_secded
       
         mr_linkecc_secded (
           .data_in ({
                          mr_ph_wdata_w[DQ_WIDTH*15 +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*14 +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*13 +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*12 +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*11 +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*10 +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*9  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*8  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*7  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*6  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*5  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*4  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*3  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*2  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*1  +GEN_BYTES_LECC*8 +: 8],
                          mr_ph_wdata_w[DQ_WIDTH*0  +GEN_BYTES_LECC*8 +: 8]
                    }),
           .mask_in ({
                          mr_ph_wdatamask_w[DMI_WIDTH*15 + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*14 + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*13 + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*12 + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*11 + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*10 + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*9  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*8  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*7  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*6  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*5  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*4  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*3  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*2  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*1  + GEN_BYTES_LECC],
                          mr_ph_wdatamask_w[DMI_WIDTH*0  + GEN_BYTES_LECC]
                    }),
           .poison_type(reg_ddrc_linkecc_poison_type),
           .poison_data(linkecc_poison_byte_sel[GEN_BYTES_LECC]),
           .poison_dmi (linkecc_poison_dmi_sel[GEN_BYTES_LECC]),
           .ecc_parity ({
                          lecc_cb[DMI_WIDTH*15 + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*14 + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*13 + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*12 + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*11 + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*10 + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*9  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*8  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*7  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*6  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*5  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*4  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*3  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*2  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*1  + GEN_BYTES_LECC],
                          lecc_cb[DMI_WIDTH*0  + GEN_BYTES_LECC]
                    })
       );
  end // gen_lecc
endgenerate


endmodule
