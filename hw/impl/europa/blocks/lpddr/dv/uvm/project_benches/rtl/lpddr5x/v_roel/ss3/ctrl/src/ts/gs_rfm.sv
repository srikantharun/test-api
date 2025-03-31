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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_rfm.sv#6 $
// -------------------------------------------------------------------------
// Description:
//                This block is responsible for scheduling LPDDR5 Refresh
//                Management (RFM) command
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module gs_rfm
import DWC_ddrctl_reg_pkg::*;
#(
   //------------------------------- PARAMETERS -----------------------------------
    parameter  RAACNT_BITS          = INIT_RAA_CNT_WIDTH
   ,parameter  BG_BANK_BITS         = `MEMC_BG_BANK_BITS
   ,parameter  NUM_BG_BANKS         = 1 << BG_BANK_BITS
   ,parameter  BANK_BITS            = `MEMC_BANK_BITS
   ,parameter  RM_BITS              = RFMTH_RM_THR_WIDTH
   ,parameter  BLK_ACT_TRFM_WDT     = 1 << BANK_BITS
   ,parameter  BLK_ACT_RAAC_WDT     = (`DDRCTL_LPDDR_RFMSBC_EN == 1) ? NUM_BG_BANKS : NUM_BG_BANKS/2
   ,parameter  RFM_DLY              = `MEMC_GS_REF_DLY // same as REF
)
(
   //------------------------- INPUTS AND OUTPUTS ---------------------------------
    input   logic                               co_yy_clk                           //
   ,input   logic                               core_ddrc_rstn                      //
   ,input   logic                               gs_ts_rank_enable                   // enable this rank
   ,input   logic                               dh_gs_lpddr5                        // LPDDR5 mode
   ,input   logic                               dh_gs_rfm_en                        // RFM enable
   ,input   logic                               dh_gs_rfmsbc                        // RFMSBC
   ,input   logic [RAAIMT_WIDTH-1:0]            dh_gs_raaimt                        // RAAIMT
   ,input   logic [RAAMULT_WIDTH-1:0]           dh_gs_raamult                       // RAAMULT
   ,input   logic [RAADEC_WIDTH-1:0]            dh_gs_raadec                        // RAADEC
   ,input   logic [RFMTH_RM_THR_WIDTH-1:0]      dh_gs_rfmth_rm_thr                  // RM threshold for RFM command
   ,input   logic [RAACNT_BITS-1:0]             dh_gs_init_raa_cnt                  // initial value of RAA counters
   ,input   logic [T_RFMPB_WIDTH-1:0]           dh_gs_t_rfmpb                       // tRFMpb
   ,input   logic [T_RRD_WIDTH-1:0]             dh_gs_t_rrd                         // tRRD: RFMpb to ACT min (LPDDR4)
   ,input   logic [DBG_RAA_BG_BANK_WIDTH-1:0]   dh_gs_dbg_raa_bg_bank               // bg/bank for RAA count status
   ,output  logic [DBG_RAA_CNT_WIDTH-1:0]       rank_dbg_raa_cnt                    // RAA count status
   ,output  logic                               gs_dh_rank_raa_cnt_gt0              // RAA count of all banks is greater than 0
   ,input   logic [T_PBR2ACT_WIDTH-1:0]         dh_gs_t_pbr2act                     // minimum time between LPDDR5 per-bank refresh act different bank
   ,input                                       dh_gs_dsm_en                        // Deep Sleep Down Mode enable
   ,input   logic [4:0]                         derate_operating_rm                 // operating Refresh Multiplier (RM) in LPDDR5 MR4:OP[4:0] or refresh rate in LPDDR4 MR4:OP[2:0]
   ,input   logic [2:0]                         gs_dh_operating_mode                // operating mode (0:init, 1:normal, 2:powerdown, 3:selfref)
   ,input                                       gsfsm_sr_entry_req                  // self-refresh entry request
   ,input   logic                               act_this_rank                       // ACT issued to this rank
   ,input   logic [BG_BANK_BITS-1:0]            act_bg_bank                         // BG/bank of ACT
   ,input   logic                               per_bank_refresh                    // per-bank refresh mode
   ,input   logic                               ref_this_rank                       // REF issued to this rank
   ,input   logic [BANK_BITS-1:0]               refpb_bank                          // bank of REF
   ,input   logic                               rfm_this_rank                       // RFM issued to this rank
   ,input   logic                               wr_mode                             // 0: RD mode, 1: WR mode
   ,input   logic [NUM_BG_BANKS-1:0]            bank_pgmiss_exvpr_valid             // page-miss expired VPR valid per BG/Bank
   ,input   logic [NUM_BG_BANKS-1:0]            bank_pgmiss_exvpw_valid             // page-miss expired VPW valid per BG/Bank

   ,output  logic                               rank_rfm_required                   // RFM request
   ,output  logic [BANK_BITS-1:0]               gs_bs_rfmpb_bank                    // bank address of RFM
   ,output  logic                               gs_bs_rfmpb_sb0                     // SB0 of RFM in single bank mode
   ,output  logic                               rank_nop_after_rfm                  // NOP/DEC required after RFM (tRFMpb)
   ,output  logic                               rank_no_load_mr_after_rfm           // No load MR required after RFM
   ,output  logic [BLK_ACT_TRFM_WDT-1:0]        gs_bs_rank_block_act_trfm_bk_nxt    // Block ACT in next cycle for each bank
   ,output  logic [BLK_ACT_RAAC_WDT-1:0]        gs_bs_rank_block_act_raa_expired    // Block ACT due to RAA counter expired
);


   localparam  NUM_BANKS            = 1 << BANK_BITS;
   localparam  NUM_RAACNT_INST      = BLK_ACT_RAAC_WDT;

   logic    [(RAAIMT_WIDTH+3)-1:0]        raaimt_cnt_w;
   logic    [(RAAIMT_WIDTH+6)-1:0]        raammt_cnt_w;
   logic    [(RAAIMT_WIDTH+5)-1:0]        raadec_cnt_w;
   logic    [NUM_RAACNT_INST-1:0]         raa_cnt_en_w;
   logic    [NUM_RAACNT_INST-1:0]         act_this_bank_w;
   logic    [NUM_RAACNT_INST-1:0]         ref_this_bank_w;
   logic    [NUM_RAACNT_INST-1:0]         rfm_this_bank_w;
   logic    [NUM_RAACNT_INST-1:0]         pgmiss_exvpr_valid_w;
   logic    [NUM_RAACNT_INST-1:0]         pgmiss_exvpw_valid_w;
   logic    [NUM_RAACNT_INST-1:0]         pgmiss_exvprw_valid_w;
   logic    [NUM_RAACNT_INST-1:0]         raa_cnt_expired_early_w;
   logic    [NUM_RAACNT_INST-1:0]         raa_cnt_expired_w;
   logic    [NUM_RAACNT_INST-1:0]         raa_cnt_eq0_w;
   logic    [RAACNT_BITS-1:0]             raa_cnt_w[NUM_RAACNT_INST];

   logic    [RFM_DLY-2:0]                 rfm_this_bank_pipe_r[NUM_RAACNT_INST];
   logic    [RFM_DLY-2:0]                 raa_cnt_expired_pipe_r[NUM_RAACNT_INST];
   logic    [NUM_RAACNT_INST-1:0]         raa_cnt_expired_dly_w;
   logic    [NUM_RAACNT_INST-1:0]         masked_raa_cnt_expired_dly_w;
   logic    [BANK_BITS-1:0]               next_rfmpb_bank_w;
   logic                                  next_rfmpb_sb0_w;
   logic                                  rfmpb_bank_update_w;
   logic    [NUM_BANKS-1:0]               rfm_this_bank_pair_w;
   logic    [T_RFMPB_WIDTH-1:0]           bank_t_rfm_timer_r[NUM_BANKS];
   logic    [BANK_BITS-1:0]               curr_rfmpb_bank_r;

   //------------------------------------------------------------------------------
   // RAA counters
   //------------------------------------------------------------------------------
   // counter settings
   assign raaimt_cnt_w     = {dh_gs_raaimt, 3'b000}; // RAAIMT x8

   always_comb begin : RAAMMT_CNT_PROC
      unique case (dh_gs_raamult)
         2'b00:      raammt_cnt_w   = {2'b00, raaimt_cnt_w, 1'b0}; // x2
         2'b01:      raammt_cnt_w   = {1'b0, raaimt_cnt_w, 2'b00}; // x4
         2'b10:      raammt_cnt_w   = {2'b00, raaimt_cnt_w, 1'b0} + {1'b0, raaimt_cnt_w, 2'b00}; // x6
         2'b11:      raammt_cnt_w   = {raaimt_cnt_w, 3'b000}; // x8
         default:    raammt_cnt_w   = {2'b00, raaimt_cnt_w, 1'b0}; // x2
      endcase
   end

   always_comb begin : RAADEC_CNT_PROC
      unique case (dh_gs_raadec)
         2'b00:      raadec_cnt_w   = {2'b00, raaimt_cnt_w}; // x1
         2'b01:      raadec_cnt_w   = {2'b00, raaimt_cnt_w} + {3'b000, raaimt_cnt_w[$bits(raaimt_cnt_w)-1:1]}; // x1.5
         2'b10:      raadec_cnt_w   = {1'b0, raaimt_cnt_w, 1'b0}; // x2
         2'b11:      raadec_cnt_w   = {raaimt_cnt_w, 2'b00}; // x4
         default:    raadec_cnt_w   = {2'b00, raaimt_cnt_w}; // x1
      endcase
   end

   generate
      for (genvar i=0; i<NUM_RAACNT_INST; i++) begin : RAACNT_GEN
         // i is defined as below. i[3] is valid in single bank mode.
         //             | i[0] | i[1] | i[2] | i[3] |
         // ------------+------+------+------+------+
         // BG mode     | BA0  | BA1  | BG0  | BG1  |
         // 16B mode    | BA0  | BA1  | BA2  | BA3  |
         // 8B mode     | BA0  | BA1  | BA2  | na   |
         assign raa_cnt_en_w[i]           = gs_ts_rank_enable & dh_gs_rfm_en
                                          & (dh_gs_rfmsbc | ($unsigned(i) < NUM_BANKS))
                                          ;
         assign act_this_bank_w[i]        = act_this_rank & (i[BANK_BITS-1:0] == act_bg_bank[BANK_BITS-1:0])
                                          & (~dh_gs_rfmsbc | (i[BG_BANK_BITS-1] == act_bg_bank[BG_BANK_BITS-1]))
                                          ;
         assign ref_this_bank_w[i]        = ref_this_rank & (~per_bank_refresh | (i[BANK_BITS-1:0] == refpb_bank));
         assign rfm_this_bank_w[i]        = rfm_this_rank & (i[BANK_BITS-1:0] == gs_bs_rfmpb_bank)
                                          & (~dh_gs_rfmsbc | (i[BG_BANK_BITS-1] == gs_bs_rfmpb_sb0))
                                          ;

         // page-miss exVPRW valid per RAA counter
         assign pgmiss_exvpr_valid_w[i]   =
                                            dh_gs_rfmsbc ?  bank_pgmiss_exvpr_valid[{i[1:0], i[3:2]}] :
                                            dh_gs_lpddr5 ?  (bank_pgmiss_exvpr_valid[{i[1:0], 1'b0, i[2]}] |
                                                            bank_pgmiss_exvpr_valid[{i[1:0], 1'b1, i[2]}]) :
                                                            bank_pgmiss_exvpr_valid[{1'b0, i[2:0]}];
         assign pgmiss_exvpw_valid_w[i]   =
                                            dh_gs_rfmsbc ?  bank_pgmiss_exvpw_valid[{i[1:0], i[3:2]}] :
                                            dh_gs_lpddr5 ?  (bank_pgmiss_exvpw_valid[{i[1:0], 1'b0, i[2]}] |
                                                            bank_pgmiss_exvpw_valid[{i[1:0], 1'b1, i[2]}]) :
                                                            bank_pgmiss_exvpw_valid[{1'b0, i[2:0]}];

         gs_raa_cnt
          #(
            .RAACNT_BITS                        (RAACNT_BITS)
         ) u_raa_cnt (
            .co_yy_clk                          (co_yy_clk),
            .core_ddrc_rstn                     (core_ddrc_rstn),
            .raa_cnt_en                         (raa_cnt_en_w[i]),
            .dh_gs_init_raa_cnt                 (dh_gs_init_raa_cnt),
            .raaimt_cnt                         ({{(RAACNT_BITS-$bits(raaimt_cnt_w)){1'b0}}, raaimt_cnt_w}),
            .raammt_cnt                         (raammt_cnt_w),
            .raadec_cnt                         ({{(RAACNT_BITS-$bits(raadec_cnt_w)){1'b0}}, raadec_cnt_w}),
            .gs_dh_operating_mode               (gs_dh_operating_mode),
            .act_this_bank                      (act_this_bank_w[i]),
            .ref_this_bank                      (ref_this_bank_w[i]),
            .rfm_this_bank                      (rfm_this_bank_w[i]),
            .raa_cnt_expired_early              (raa_cnt_expired_early_w[i]),
            .raa_cnt_expired                    (raa_cnt_expired_w[i]),
            .raa_cnt_eq0                        (raa_cnt_eq0_w[i]),
            .raa_cnt                            (raa_cnt_w[i])
         );
      end : RAACNT_GEN
   endgenerate

   //------------------------------------------------------------------------------
   // RAA status
   //------------------------------------------------------------------------------
   assign gs_dh_rank_raa_cnt_gt0 = |(~raa_cnt_eq0_w);
   assign rank_dbg_raa_cnt       = raa_cnt_w[dh_gs_dbg_raa_bg_bank];

   //------------------------------------------------------------------------------
   // RFM control
   //------------------------------------------------------------------------------
   // delayed RAA counter expired
// spyglass disable_block FlopEConst
// SMD: Enable pin EN on Flop DWC_ddrctl.U_ddrc.U_ddrc_cp_top.\ddrc_ctrl_inst[0].U_ddrc_cp .\GEN_DDRC_CPE_EN.U_ddrc_cpe .ts.gs.\rank_constraints[0].gs_rank_constraints0 .u_rfm.raa_cnt_expired_pipe_r[0] (master RTL_FDCE) is always enabled (tied high)
// SJ: raa_cnt_expired_pipe_r[0] is always enabled for single rank configs
   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         for (int i=0; i<NUM_RAACNT_INST; i++) begin
            rfm_this_bank_pipe_r[i]    <= {(RFM_DLY-1){1'b0}};
            raa_cnt_expired_pipe_r[i]  <= {(RFM_DLY-1){1'b0}};
         end
      end else if (gs_ts_rank_enable)
      begin
         for (int i=0; i<NUM_RAACNT_INST; i++) begin
            rfm_this_bank_pipe_r[i][0]             <= rfm_this_bank_w[i];
            rfm_this_bank_pipe_r[i][RFM_DLY-2:1]   <= rfm_this_bank_pipe_r[i][RFM_DLY-3:0];
            raa_cnt_expired_pipe_r[i][0]           <= raa_cnt_expired_w[i];
            raa_cnt_expired_pipe_r[i][RFM_DLY-2:1] <= raa_cnt_expired_pipe_r[i][RFM_DLY-3:0];
         end
      end
   end
// spyglass enable_block FlopEConst

   always_comb begin : RAA_CNT_EXPIRED_DLY_PROC
      for (int i=0; i<NUM_RAACNT_INST; i++) begin
         raa_cnt_expired_dly_w[i] = raa_cnt_expired_pipe_r[i][RFM_DLY-2];
      end
   end

   // BG/Bank address of RFM command
   always_comb begin : MASKED_RAA_CNT_EXPIRED_DLY_PROC
      for (int i=0; i<NUM_RAACNT_INST; i++) begin
         masked_raa_cnt_expired_dly_w[i]  = raa_cnt_expired_dly_w[i] & ~rfm_this_bank_w[i]
                                          & ~(|rfm_this_bank_pipe_r[i])
                                          ;
      end
   end

   assign pgmiss_exvprw_valid_w = wr_mode ? pgmiss_exvpw_valid_w : pgmiss_exvpr_valid_w;

//spyglass disable_block W415a
//SMD: Signal next_rfmpb_bank_w is being assigned multiple times in same always block.
//SJ: Using initialization in process to minimize code - sets the default for any hanging branches, avoids latches
   always_comb begin : NEXT_RFMPB_BANK_PROC
      next_rfmpb_bank_w = gs_bs_rfmpb_bank;
      next_rfmpb_sb0_w  = gs_bs_rfmpb_sb0;
      // page-miss expired VPRW has a priority for RFMpb bank (VPRW in current RDWR direction is higher priority than opposite direction)
      if (|(masked_raa_cnt_expired_dly_w & pgmiss_exvprw_valid_w)) begin
         for (int i=NUM_RAACNT_INST-1; i>=0; i--) begin
            if (masked_raa_cnt_expired_dly_w[i] && pgmiss_exvprw_valid_w[i]) begin
//spyglass disable_block W216
//SMD: Inappropriate range select for int_part_sel variable: "i[(BANK_BITS - 1):0] "
//SJ: All occurences of W216 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)
               next_rfmpb_bank_w = i[BANK_BITS-1:0];
//spyglass enable_block W216
//spyglass disable_block W215
//SMD: Inappropriate bitttt select for int_bit_sel variable: "i[(BG_BANK_BITS - 1)] "
//SJ: All occurences of W215 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)
               next_rfmpb_sb0_w  = i[BG_BANK_BITS-1];
//spyglass enable_block W215
            end
         end
      end else
      if (|masked_raa_cnt_expired_dly_w) begin
         for (int i=NUM_RAACNT_INST-1; i>=0; i--) begin
            if (masked_raa_cnt_expired_dly_w[i]) begin
//spyglass disable_block W216
//SMD: Inappropriate range select for int_part_sel variable: "i[(BANK_BITS - 1):0] "
//SJ: All occurences of W216 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)
               next_rfmpb_bank_w = i[BANK_BITS-1:0];
//spyglass enable_block W216
//spyglass disable_block W215
//SMD: Inappropriate bitttt select for int_bit_sel variable: "i[(BG_BANK_BITS - 1)] "
//SJ: All occurences of W215 errors have been previously waived in Leda, as they were considered safe and because no suitable re-coding was found (see bug2455)
               next_rfmpb_sb0_w  = i[BG_BANK_BITS-1];
//spyglass enable_block W215
            end
         end
      end
   end
//spyglass enable_block W415a

   assign rfmpb_bank_update_w = rank_rfm_required  ? rfm_this_rank
                                                      | (|(masked_raa_cnt_expired_dly_w & (pgmiss_exvpr_valid_w | pgmiss_exvpw_valid_w)))
                                                   : (|raa_cnt_expired_dly_w);

   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         gs_bs_rfmpb_bank  <= {BANK_BITS{1'b0}};
         gs_bs_rfmpb_sb0   <= 1'b0;
      end else if (gs_ts_rank_enable)
      begin
         if (rfmpb_bank_update_w) begin
            gs_bs_rfmpb_bank  <= next_rfmpb_bank_w;
            gs_bs_rfmpb_sb0   <= next_rfmpb_sb0_w;
         end
      end
   end

   // RFM request
   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         rank_rfm_required <= 1'b0;
      end else if (gs_ts_rank_enable)
      begin
         rank_rfm_required <= (derate_operating_rm < dh_gs_rfmth_rm_thr) & ~gsfsm_sr_entry_req & ~dh_gs_dsm_en
                              & (|(raa_cnt_expired_w & masked_raa_cnt_expired_dly_w));
      end
   end

   // RFM timing requirement
   generate
      for (genvar i=0; i<NUM_BANKS; i++) begin : BANK_T_RFM_TIMER_GEN
         assign rfm_this_bank_pair_w[i]   = rfm_this_rank & (i[BANK_BITS-1:0] == gs_bs_rfmpb_bank);

         // tRFMpb/tpbr2act/tRRD timer per bank
         always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
            if (!core_ddrc_rstn) begin
               bank_t_rfm_timer_r[i] <= {T_RFMPB_WIDTH{1'b0}};
            end else if (gs_ts_rank_enable)
            begin
               if (rfm_this_rank && !rfm_this_bank_pair_w[i] & dh_gs_lpddr5) begin // RFM to different bank pair
                  if (bank_t_rfm_timer_r[i] < {{(T_RFMPB_WIDTH - T_PBR2ACT_WIDTH){1'b0}}, dh_gs_t_pbr2act}) begin
                     // RFMpb-to-ACT diff bank (tpbr2act), which is always smaller than tRFMpb. This is to avoid overriding tRFMpb value
                     bank_t_rfm_timer_r[i] <= dh_gs_t_pbr2act - {{(T_RFMPB_WIDTH-1){1'b0}}, 1'b1};
                  end else begin
                     // if current value is greater than or equal to dh_gs_t_pbr2act, continue counting value for tRFMpb
                     bank_t_rfm_timer_r[i] <= bank_t_rfm_timer_r[i] - {{(T_RFMPB_WIDTH-1){1'b0}}, 1'b1};
                  end
               end else if (rfm_this_rank && !rfm_this_bank_pair_w[i] & !dh_gs_lpddr5) begin // RFM to different bank pair
                  if (bank_t_rfm_timer_r[i] < {{(T_RFMPB_WIDTH - T_RRD_WIDTH){1'b0}}, dh_gs_t_rrd}) begin
                     // RFMpb-to-ACT diff bank (trrd), which is always smaller than tRFMpb. This is to avoid overriding tRFMpb value
                     bank_t_rfm_timer_r[i] <= dh_gs_t_rrd - {{(T_RFMPB_WIDTH-1){1'b0}}, 1'b1};
                  end else begin
                     // if current value is greater than or equal to dh_gs_t_rrd, continue counting value for tRFMpb
                     bank_t_rfm_timer_r[i] <= bank_t_rfm_timer_r[i] - {{(T_RFMPB_WIDTH-1){1'b0}}, 1'b1};
                  end
               end else if (rfm_this_bank_pair_w[i]) begin // RFM to this bank pair
                  // RFMpb-tRFMpb this bank (tRFMpb)
                  bank_t_rfm_timer_r[i] <= dh_gs_t_rfmpb - {{(T_RFMPB_WIDTH-1){1'b0}}, 1'b1};
               end else if (|bank_t_rfm_timer_r[i]) begin
                  bank_t_rfm_timer_r[i] <= bank_t_rfm_timer_r[i] - {{(T_RFMPB_WIDTH-1){1'b0}}, 1'b1};
               end
            end
         end
      end : BANK_T_RFM_TIMER_GEN
   endgenerate

   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         curr_rfmpb_bank_r <= {BANK_BITS{1'b0}};
      end else if (gs_ts_rank_enable)
      begin
         if (rfm_this_rank) begin
            curr_rfmpb_bank_r <= gs_bs_rfmpb_bank;
         end
      end
   end

   // block any command for tRFMpb/pbr2act after RFM
   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         rank_nop_after_rfm <= 1'b0;
      end else if (gs_ts_rank_enable)
      begin
         rank_nop_after_rfm <= (|bank_t_rfm_timer_r[curr_rfmpb_bank_r][T_RFMPB_WIDTH-1:1]) | rfm_this_rank;
      end
   end

   // block load_mr for 1 cycle after RFM
   always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if (!core_ddrc_rstn) begin
         rank_no_load_mr_after_rfm <= 1'b0;
      end else if (gs_ts_rank_enable)
      begin
         rank_no_load_mr_after_rfm <= rfm_this_rank;
      end
   end

   // block ACT for tRFMpb/pbr2act after RFM and during RFM request
   always_comb begin : BLOCK_ACT_TRFM_BK_PROC
      for (int i=0; i<BLK_ACT_TRFM_WDT; i++) begin
         gs_bs_rank_block_act_trfm_bk_nxt[i] = rfm_this_rank | (|bank_t_rfm_timer_r[i][T_RFMPB_WIDTH-1:1]);
      end
   end

   always_comb begin : BLOCK_ACT_RAA_EXPIRED_PROC
      if (derate_operating_rm < dh_gs_rfmth_rm_thr) begin
         gs_bs_rank_block_act_raa_expired = raa_cnt_expired_w | raa_cnt_expired_early_w
                                          // when single-bank mode is disabled, replicate lower bits to uper bits of bank-pair
                                          | ({BLK_ACT_RAAC_WDT{~dh_gs_rfmsbc}} & ((raa_cnt_expired_w | raa_cnt_expired_early_w) << NUM_BANKS))
                                          ;
      end else begin
         gs_bs_rank_block_act_raa_expired = {BLK_ACT_RAAC_WDT{1'b0}};
      end
   end

`ifdef SNPS_ASSERT_ON
   `ifndef SYNTHESIS
   //------------------------------------------------------------------------------
   // SVA
   //------------------------------------------------------------------------------
   // Check that no ACT command issued to this bank at raa_cnt==RAAMMT
   property p_no_act_at_raammt;
      @(posedge co_yy_clk) disable iff ((!core_ddrc_rstn) || (!gs_ts_rank_enable))
      dh_gs_rfm_en && (derate_operating_rm < dh_gs_rfmth_rm_thr) && act_this_rank |-> ((act_this_bank_w & raa_cnt_expired_w) == 0);
   endproperty

   a_no_act_at_raammt : assert property (p_no_act_at_raammt)
   else $error("[%t][%m] ERROR: ACT is not expected to bank where RAA count expires", $time);

   `endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

endmodule  // gs_rfm
