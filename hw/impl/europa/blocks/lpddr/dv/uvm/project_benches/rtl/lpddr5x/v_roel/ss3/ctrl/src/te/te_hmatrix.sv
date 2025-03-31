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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/te/te_hmatrix.sv#3 $
// -------------------------------------------------------------------------
// Description:
//
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
module te_hmatrix #(
    //-------------------------------- PARAMETERS ----------------------------------
     parameter  CAM_ENTRIES      = 32
    ,parameter  CAM_ADDR_BITS    = 5 
    ,parameter  NUM_COMPS        = 5 
    )
    (    
    //--------------------------- INPUTS AND OUTPUTS -------------------------------
     input                                             core_ddrc_rstn 
    ,input                                             core_ddrc_core_clk
    ,input                                             ddrc_cg_en                         // clock gating enable
    ,input                                             push
    ,input      [CAM_ADDR_BITS-1:0]                    push_entry
    ,input                                             pop
    ,input      [CAM_ADDR_BITS-1:0]                    pop_entry
    ,input      [CAM_ENTRIES*NUM_COMPS-1:0]            masks
    ,output reg [CAM_ENTRIES*NUM_COMPS-1:0]            oldest_ohs
    ,output reg [CAM_ENTRIES-1:0]                      te_vlimit_decr

);
   
reg  [CAM_ENTRIES-1:0]               valid_vct;
reg  [CAM_ENTRIES-1:0]               valid_vct_nxt;

reg  [CAM_ENTRIES*CAM_ENTRIES-1:0]   history_matrix;
reg  [CAM_ENTRIES*CAM_ENTRIES-1:0]   history_matrix_nxt;

reg  [CAM_ENTRIES*NUM_COMPS-1:0]     masks_reg;

reg                                  r_push;
reg  [CAM_ADDR_BITS-1:0]             r_push_entry;  

reg                                  r_pop;
reg  [CAM_ADDR_BITS-1:0]             r_pop_entry;  

reg  [CAM_ENTRIES-1:0]               te_vlimit_decr_nxt;


integer                              i,j,k;

//spyglass disable_block SelfDeterminedExpr-ML
//SMD: Self determined expression '((k * CAM_ENTRIES) + j)' found in module 'te_hmatrix'
//SJ: This coding style is acceptable and there is no plan to change it.

//------------------------------------//
// Logic for maintain History Matrix  //
//------------------------------------//
//spyglass disable_block W415a
//SMD: Signal valid_vct_nxt/history_matrix_nxt is being assigned multiple times in same always block. 
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
always @(*) begin
    valid_vct_nxt      = valid_vct;
    history_matrix_nxt = history_matrix;
    if (r_push) begin
        valid_vct_nxt[r_push_entry]                               = 1'b1;
        for (i=0;i<CAM_ENTRIES;i=i+1) begin
            if($unsigned(i)==r_push_entry[CAM_ADDR_BITS-1:0]) begin
            history_matrix_nxt[i*CAM_ENTRIES+:CAM_ENTRIES] = valid_vct;
            end
        end
    end
    if (r_pop) begin
        valid_vct_nxt[r_pop_entry] = 1'b0;
        for (i=0;i<CAM_ENTRIES;i=i+1) begin
            history_matrix_nxt[i*CAM_ENTRIES+r_pop_entry] = 1'b0;

        end 
    end
end
//spyglass enable_block W415a

always @(*) begin
    te_vlimit_decr_nxt = {CAM_ENTRIES{1'b0}};
    if (r_pop) begin
        for (i=0;i<CAM_ENTRIES;i=i+1) begin
            if($unsigned(i)==r_pop_entry[CAM_ADDR_BITS-1:0]) begin
               te_vlimit_decr_nxt = history_matrix[i*CAM_ENTRIES+:CAM_ENTRIES];
            end
        end
    end
end

// Flops
always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
    if (~core_ddrc_rstn) begin
        valid_vct      <= {CAM_ENTRIES{1'b0}};
        history_matrix <= {CAM_ENTRIES*CAM_ENTRIES{1'b0}};
        r_push         <= 1'b0;
        r_push_entry   <= {CAM_ADDR_BITS{1'b0}};
        r_pop          <= 1'b0;
        r_pop_entry    <= {CAM_ADDR_BITS{1'b0}};
        te_vlimit_decr <= {CAM_ENTRIES{1'b0}};
    end
    else if(ddrc_cg_en) begin
        valid_vct      <= valid_vct_nxt;
        history_matrix <= history_matrix_nxt;
        r_push         <= push;
        if (push) begin
           r_push_entry   <= push_entry;    
        end
        r_pop          <= pop;
        if (pop) begin
           r_pop_entry    <= pop_entry;   
        end
        te_vlimit_decr <= te_vlimit_decr_nxt;
    end
end

// Oldest one hot vector generated by mask information.
always @(*) begin
    for (j=0;j<CAM_ENTRIES;j=j+1) begin
       for (k=0;k<NUM_COMPS;k=k+1) begin
        oldest_ohs[(k*CAM_ENTRIES)+j] = masks_reg[(k*CAM_ENTRIES)+j] & (~|(history_matrix[j*CAM_ENTRIES+:CAM_ENTRIES] & masks_reg[(k*CAM_ENTRIES)+:CAM_ENTRIES]));
       end
    end
end
 

// Flops input for masks
// CAM depth will be multiple of 32 (32/64/96/128 ...) or 16 or 48(WRCAM=32 + Inline-ECC CAM=16)
localparam  CG_UNIT =32;
genvar cam_idx;
generate
    if(CAM_ENTRIES==8 || CAM_ENTRIES==16 || CAM_ENTRIES==24) begin
        always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
            if (~core_ddrc_rstn) begin
               masks_reg <= {CAM_ENTRIES*NUM_COMPS{1'b0}};
            end
            else begin
                if(masks_reg!= masks) begin // mask can be used anytime (e.g. for ACT/PRE) hence ddrc_cg_en signal is not used
                    masks_reg <= masks;
                end
            end
        end
    end if(CAM_ENTRIES==48) begin
        always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
            if (~core_ddrc_rstn) begin
               masks_reg[0 +: CG_UNIT*NUM_COMPS] <= {CG_UNIT*NUM_COMPS{1'b0}};
            end
            else begin
                if(masks_reg[0 +: CG_UNIT*NUM_COMPS] != masks[0 +: CG_UNIT*NUM_COMPS]) begin // mask can be used anytime (e.g. for ACT/PRE) hence ddrc_cg_en signal is not used
                   masks_reg[0 +: CG_UNIT*NUM_COMPS] <= masks[0 +: CG_UNIT*NUM_COMPS];
                end
            end
        end
        always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
            if (~core_ddrc_rstn) begin
               masks_reg[CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS/2] <= {CG_UNIT*NUM_COMPS/2{1'b0}};
            end
            else begin
                if(masks_reg[CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS/2] != masks[CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS/2]) begin // mask can be used anytime (e.g. for ACT/PRE) hence ddrc_cg_en signal is not used
                   masks_reg[CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS/2] <= masks[CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS/2];
                end
            end
        end
    end else begin
        for (cam_idx = 0;  cam_idx < (CAM_ENTRIES/CG_UNIT); cam_idx=cam_idx+1) begin: te_hmatrix_masks_reg_GEN
            always @(posedge core_ddrc_core_clk or negedge core_ddrc_rstn) begin
                if (~core_ddrc_rstn) begin
                   masks_reg[cam_idx*CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS] <= {CG_UNIT*NUM_COMPS{1'b0}};
                end
                else begin
                    if (masks_reg[cam_idx*CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS] != masks[cam_idx*CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS]) begin
                        masks_reg[cam_idx*CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS] <= masks[cam_idx*CG_UNIT*NUM_COMPS +: CG_UNIT*NUM_COMPS];
                    end
                end
            end
        end
    end
endgenerate
//spyglass enable_block SelfDeterminedExpr-ML


`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS

// This is just for waveform view
reg [CAM_ENTRIES-1:0] history_matrix_wfm [CAM_ENTRIES-1:0];
integer idx;
always @(*) begin
    for (idx=0;idx<CAM_ENTRIES;idx=idx+1) begin
        history_matrix_wfm[idx] = history_matrix[idx*CAM_ENTRIES+:CAM_ENTRIES];
    end
end 



// Push has to be done only for a non-valid entry
property p_push_valid_check;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  r_push |-> (valid_vct[r_push_entry]==1'b0);

endproperty

a_push_valid_check: assert property (p_push_valid_check);

// Pop has to be done only for a valid entry
property p_pop_valid_check;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  r_pop |-> (valid_vct[r_pop_entry]==1'b1);

endproperty

a_pop_valid_check: assert property (p_pop_valid_check);

// If push and pop are on the same cycle, the entries have to be exclusive 
property p_push_pop_exclusive;
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  (r_push & r_pop) |-> r_push_entry != r_pop_entry;

endproperty

a_push_pop_exclusive: assert property (p_push_pop_exclusive);



// If there are valid entries, one-hot vector has to be one-hot 
property p_check_vct_onehot(comp_idx);
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  ((|(valid_vct & masks_reg[CAM_ENTRIES*comp_idx+:CAM_ENTRIES])) |-> $onehot(oldest_ohs[CAM_ENTRIES*comp_idx+:CAM_ENTRIES]));

endproperty
  
// One hot vector has to be one hot or 0 always 
property p_check_vct_onehot0(comp_idx);
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  $onehot0(oldest_ohs[CAM_ENTRIES*comp_idx+:CAM_ENTRIES]);

endproperty

// Dynamic Mask is only for valid entries
property p_dyn_mask_check(comp_idx);
  @ (posedge core_ddrc_core_clk) disable iff (~core_ddrc_rstn)
  ((masks_reg[CAM_ENTRIES*comp_idx+:CAM_ENTRIES] & valid_vct) == masks_reg[CAM_ENTRIES*comp_idx+:CAM_ENTRIES]);
endproperty

genvar idx4comp;
generate
  for (idx4comp=0; idx4comp<NUM_COMPS;idx4comp=idx4comp+1) begin : assertion_loop
    a_check_vct_onehot : assert property (p_check_vct_onehot(idx4comp));
    a_check_vct_onehot0: assert property (p_check_vct_onehot0(idx4comp));
    a_dyn_mask_check   : assert property (p_dyn_mask_check(idx4comp));
  end
endgenerate
`endif
`endif

endmodule


