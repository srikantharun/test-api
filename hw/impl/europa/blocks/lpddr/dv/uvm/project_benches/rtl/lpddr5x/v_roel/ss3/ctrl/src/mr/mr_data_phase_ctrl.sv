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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/mr/mr_data_phase_ctrl.sv#4 $
// -------------------------------------------------------------------------
// Description:
//          Data phase control module.
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module mr_data_phase_ctrl #(parameter PHY_DATA_WIDTH = `MEMC_DFI_TOTAL_DATA_WIDTH,
                            parameter PHY_MASK_WIDTH = `MEMC_DFI_TOTAL_DATA_WIDTH/8
)
(
input                       core_ddrc_core_clk,
input                       core_ddrc_rstn,
//spyglass disable_block W240
//SMD: Inputs declared but not read
//SJ: MEMC_FREQ_RATIO=2 and MEMC_BURST_LENGTH=8 case. Not support this config.
input                       reg_ddrc_frequency_ratio,
//spyglass enable_block W240
input  [1:0]                wr_ph,
input                       ram_data_vld,
input  [PHY_DATA_WIDTH-1:0] wdata,
input  [PHY_MASK_WIDTH-1:0] wdata_mask,
input  [PHY_MASK_WIDTH-1:0] wlecc,
output [PHY_MASK_WIDTH-1:0] wlecc_next,
output [PHY_DATA_WIDTH-1:0] wdata_next,
output [PHY_MASK_WIDTH-1:0] wdata_mask_next
);


// VCS UNR CONSTANT declarations


wire [PHY_DATA_WIDTH/4-1:0] wdata0;
wire [PHY_DATA_WIDTH/4-1:0] wdata1;
wire [PHY_DATA_WIDTH/4-1:0] wdata2;
wire [PHY_DATA_WIDTH/4-1:0] wdata3;
wire [PHY_MASK_WIDTH/4-1:0] wdata_mask0;
wire [PHY_MASK_WIDTH/4-1:0] wdata_mask1;
wire [PHY_MASK_WIDTH/4-1:0] wdata_mask2;
wire [PHY_MASK_WIDTH/4-1:0] wdata_mask3;
wire [PHY_MASK_WIDTH/4-1:0] wlecc0;
wire [PHY_MASK_WIDTH/4-1:0] wlecc1;
wire [PHY_MASK_WIDTH/4-1:0] wlecc2;
wire [PHY_MASK_WIDTH/4-1:0] wlecc3;
wire [PHY_DATA_WIDTH/4-1:0]  wdata_sft0;
wire [PHY_DATA_WIDTH/4-1:0]  wdata_sft1;
wire [PHY_DATA_WIDTH/4-1:0]  wdata_sft2;
wire [PHY_DATA_WIDTH/4-1:0]  wdata_sft3;
wire [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft0;
wire [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft1;
wire [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft2;
wire [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft3;
wire [PHY_MASK_WIDTH/4-1:0]  wlecc_sft0;
wire [PHY_MASK_WIDTH/4-1:0]  wlecc_sft1;
wire [PHY_MASK_WIDTH/4-1:0]  wlecc_sft2;
wire [PHY_MASK_WIDTH/4-1:0]  wlecc_sft3;
reg  [PHY_DATA_WIDTH/4-1:0]  wdata_sft0_r;
reg  [PHY_DATA_WIDTH/4-1:0]  wdata_sft1_r;
reg  [PHY_DATA_WIDTH/4-1:0]  wdata_sft2_r;
reg  [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft0_r;
reg  [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft1_r;
reg  [PHY_MASK_WIDTH/4-1:0]  wdata_mask_sft2_r;
reg  [PHY_MASK_WIDTH/4-1:0]  wlecc_sft0_r;
reg  [PHY_MASK_WIDTH/4-1:0]  wlecc_sft1_r;
reg  [PHY_MASK_WIDTH/4-1:0]  wlecc_sft2_r;
reg  [1:0]                   wr_ph_r;
reg                          ram_data_vld_r;

  

// input data
assign wdata0 = wdata[0*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4];
assign wdata1 = wdata[1*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4];
assign wdata2 = wdata[2*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4];
assign wdata3 = wdata[3*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4];

assign wdata_mask0 = wdata_mask[0*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];
assign wdata_mask1 = wdata_mask[1*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];
assign wdata_mask2 = wdata_mask[2*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];
assign wdata_mask3 = wdata_mask[3*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];

assign wlecc0 = wlecc[0*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];
assign wlecc1 = wlecc[1*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];
assign wlecc2 = wlecc[2*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];
assign wlecc3 = wlecc[3*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4];


// Rotate input data
assign {wdata_sft3,wdata_sft2,wdata_sft1,wdata_sft0} = 
    (wr_ph==1)? ((reg_ddrc_frequency_ratio)? {wdata2,wdata1,wdata0,wdata3} : {wdata3,wdata2,wdata0,wdata1}) :
    (wr_ph==2)?                              {wdata1,wdata0,wdata3,wdata2} :
    (wr_ph==3)?                              {wdata0,wdata3,wdata2,wdata1} : wdata;

assign {wdata_mask_sft3,wdata_mask_sft2,wdata_mask_sft1,wdata_mask_sft0} = 
    (wr_ph==1)? ((reg_ddrc_frequency_ratio)? {wdata_mask2,wdata_mask1,wdata_mask0,wdata_mask3} : {wdata_mask3,wdata_mask2,wdata_mask0,wdata_mask1}) :
    (wr_ph==2)?                              {wdata_mask1,wdata_mask0,wdata_mask3,wdata_mask2} :
    (wr_ph==3)?                              {wdata_mask0,wdata_mask3,wdata_mask2,wdata_mask1} : wdata_mask;

assign {wlecc_sft3,wlecc_sft2,wlecc_sft1,wlecc_sft0} = 
    (wr_ph==1)? ((reg_ddrc_frequency_ratio)? {wlecc2,wlecc1,wlecc0,wlecc3} : {wlecc3,wlecc2,wlecc0,wlecc1}) :
    (wr_ph==2)?                              {wlecc1,wlecc0,wlecc3,wlecc2} :
    (wr_ph==3)?                              {wlecc0,wlecc3,wlecc2,wlecc1} : wlecc;


logic mr_data_ph_ctrl_share ;
assign mr_data_ph_ctrl_share = (wr_ph_r != wr_ph) | (ram_data_vld_r != ram_data_vld) ;

always@(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
    if(~core_ddrc_rstn) begin
        wdata_sft0_r      <= {(PHY_DATA_WIDTH/4){1'b0}};
        wdata_sft1_r      <= {(PHY_DATA_WIDTH/4){1'b0}};
        wdata_sft2_r      <= {(PHY_DATA_WIDTH/4){1'b0}};
        wdata_mask_sft0_r <= {(PHY_MASK_WIDTH/4){1'b0}};
        wdata_mask_sft1_r <= {(PHY_MASK_WIDTH/4){1'b0}};
        wdata_mask_sft2_r <= {(PHY_MASK_WIDTH/4){1'b0}};
  
        wlecc_sft0_r <= {(PHY_MASK_WIDTH/4){1'b0}};
        wlecc_sft1_r <= {(PHY_MASK_WIDTH/4){1'b0}};
        wlecc_sft2_r <= {(PHY_MASK_WIDTH/4){1'b0}};
        wr_ph_r           <= 2'b00;
        ram_data_vld_r    <= 1'b0;
    end else begin
        wdata_sft0_r      <= wdata_sft0;
        wdata_sft1_r      <= wdata_sft1;
        wdata_sft2_r      <= wdata_sft2;
        if (|(wdata_mask_sft0_r ^ wdata_mask_sft0)) begin
           wdata_mask_sft0_r <= wdata_mask_sft0;
        end
        if (|(wdata_mask_sft1_r ^ wdata_mask_sft1)) begin
           wdata_mask_sft1_r <= wdata_mask_sft1;
        end
        if (|(wdata_mask_sft2_r ^ wdata_mask_sft2)) begin
           wdata_mask_sft2_r <= wdata_mask_sft2;
        end
        wlecc_sft0_r <= wlecc_sft0;
        wlecc_sft1_r <= wlecc_sft1;
        wlecc_sft2_r <= wlecc_sft2;
        if (mr_data_ph_ctrl_share) begin
           wr_ph_r           <= wr_ph;
           ram_data_vld_r    <= ram_data_vld;
        end
    end
end
  
  // wrdata
  assign wdata_next[0*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4] =

     (ram_data_vld_r && wr_ph_r >2'd0)? wdata_sft0_r :
     (ram_data_vld   && wr_ph  ==2'd0)? wdata_sft0   : {(PHY_DATA_WIDTH/4){1'b0}};

  assign wdata_next[1*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4] =

     (ram_data_vld_r && wr_ph_r >2'd1)? wdata_sft1_r :
     (ram_data_vld   && wr_ph  <=2'd1)? wdata_sft1   : {(PHY_DATA_WIDTH/4){1'b0}};

  assign wdata_next[2*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4] =
     (reg_ddrc_frequency_ratio==1'b0)? {(PHY_DATA_WIDTH/4){1'b0}} : 

     (ram_data_vld_r && wr_ph_r >2'd2)? wdata_sft2_r :
     (ram_data_vld   && wr_ph  <=2'd2)? wdata_sft2   : {(PHY_DATA_WIDTH/4){1'b0}};

  assign wdata_next[3*(PHY_DATA_WIDTH/4)+:PHY_DATA_WIDTH/4] =
     (reg_ddrc_frequency_ratio==1'b0)? {(PHY_DATA_WIDTH/4){1'b0}} :

     (ram_data_vld                   )? wdata_sft3 : {(PHY_DATA_WIDTH/4){1'b0}};

  // wrdata mask
  assign wdata_mask_next[0*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =

     (ram_data_vld_r && wr_ph_r >2'd0)? wdata_mask_sft0_r :
     (ram_data_vld   && wr_ph  ==2'd0)? wdata_mask_sft0   : {(PHY_MASK_WIDTH/4){1'b0}};

  assign wdata_mask_next[1*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =

     (ram_data_vld_r && wr_ph_r >2'd1)? wdata_mask_sft1_r :
     (ram_data_vld   && wr_ph  <=2'd1)? wdata_mask_sft1   : {(PHY_MASK_WIDTH/4){1'b0}};

  assign wdata_mask_next[2*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =
     (reg_ddrc_frequency_ratio==1'b0)? {(PHY_MASK_WIDTH/4){1'b0}} :

     (ram_data_vld_r && wr_ph_r >2'd2)? wdata_mask_sft2_r :
     (ram_data_vld   && wr_ph  <=2'd2)? wdata_mask_sft2   : {(PHY_MASK_WIDTH/4){1'b0}};

  assign wdata_mask_next[3*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =
     (reg_ddrc_frequency_ratio==1'b0)? {(PHY_MASK_WIDTH/4){1'b0}} : 

     (ram_data_vld                   )? wdata_mask_sft3   : {(PHY_MASK_WIDTH/4){1'b0}};

  // wrdata linc ecc
  assign wlecc_next[0*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =
     (ram_data_vld_r && wr_ph_r >2'd0)? wlecc_sft0_r :
     (ram_data_vld   && wr_ph  ==2'd0)? wlecc_sft0   : {(PHY_MASK_WIDTH/4){1'b0}};

  assign wlecc_next[1*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =
     (ram_data_vld_r && wr_ph_r >2'd1)? wlecc_sft1_r :
     (ram_data_vld   && wr_ph  <=2'd1)? wlecc_sft1   : {(PHY_MASK_WIDTH/4){1'b0}};

  assign wlecc_next[2*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =
     (reg_ddrc_frequency_ratio==1'b0)? {(PHY_MASK_WIDTH/4){1'b0}} :
     (ram_data_vld_r && wr_ph_r >2'd2)? wlecc_sft2_r :
     (ram_data_vld   && wr_ph  <=2'd2)? wlecc_sft2   : {(PHY_MASK_WIDTH/4){1'b0}};

  assign wlecc_next[3*(PHY_MASK_WIDTH/4)+:PHY_MASK_WIDTH/4] =
     (reg_ddrc_frequency_ratio==1'b0)? {(PHY_MASK_WIDTH/4){1'b0}} : 
     (ram_data_vld                   )? wlecc_sft3   : {(PHY_MASK_WIDTH/4){1'b0}};




endmodule

