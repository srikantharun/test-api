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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_load_mr.sv#5 $
// -------------------------------------------------------------------------
// Description:
//                This module is responsible for issuing Load Mode Register command
//                when the controller is NOT in Initialization mode
//
//                The load_mode request from the core is accepted if busy is low and
//                a request is issued to the gs_next_xact module. Busy is set high.
//                When the gs_next_xact schedules the load_mr command to DRAM, this
//                module waits for t_mod and then de-asserts the busy.
//
//                The load mode request is muxed in the gs_glue module with the
//                load_mode during intialization and is then sent to PI
// ----------------------------------------------------------------------------
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
`include "ts/DWC_ddrctl_ts_if.svh"
module gs_load_mr
import DWC_ddrctl_reg_pkg::*;
#(
  //------------------------------- PARAMETERS ----------------------------------
     parameter    CHANNEL_NUM                 = 0
    ,parameter    SHARED_AC                   = 0

    ,parameter    BANK_BITS                   = `MEMC_BANK_BITS // # of bank bits.  2 or 3 supported.
    ,parameter    RANK_BITS                   = `MEMC_RANK_BITS

    ,parameter    MRS_A_BITS                  = `MEMC_PAGE_BITS
    ,parameter    MRS_BA_BITS                 = `MEMC_BG_BANK_BITS

    ,parameter    GS_ST_SELFREF_ENT           = 5'b00111      // put DDR in self-refresh then power down pads
    ,parameter    GS_ST_SELFREF_ENT2          = 5'b10101      // Disable C/A Parity before SR if C/A parity had been enabled
    ,parameter    GS_ST_SELFREF_ENT_DFILP     = 5'b00011      // DFI LP I/F entry SR
    ,parameter    GS_ST_SELFREF               = 5'b01100      // DDR is in self-refresh
    ,parameter    GS_ST_SELFREF_EX_DFILP      = 5'b01101      // DFI LP I/F exit SR
    ,parameter    GS_ST_SELFREF_EX1           = 5'b01110      // power up pads
    ,parameter    GS_ST_SELFREF_EX2           = 5'b01111      // bring DDR out of self-refresh
    ,parameter    GS_ST_MPSM_ENT              = 5'b11110      // MPSM entry (output MRS)
    ,parameter    GS_ST_MPSM_ENT_DFILP        = 5'b11111      // DFI LP I/F entry MPSM
    ,parameter    GS_ST_MPSM                  = 5'b10000      // DDR is in maximum power saving mode
    ,parameter    GS_ST_MPSM_EX_DFILP         = 5'b10001      // DFI LP I/F exit MPSM
    ,parameter    GS_ST_MPSM_EX1              = 5'b10010      // power up pads
    ,parameter    GS_ST_MPSM_EX2              = 5'b10011      // bring DDR out of MPSM

    ,parameter    NUM_RANKS                   = 1 << RANK_BITS
    ,parameter    FSM_STATE_WIDTH             = 5

  )
  (
  //--------------------------- INPUTS AND OUTPUTS -------------------------------
     input                              co_yy_clk                           //
    ,input                              core_ddrc_rstn                      //
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used in RTL assertions and under different `ifdefs
    ,input                              dh_gs_frequency_ratio               // 0 - 1:2 freq ratio, 1 - 1:1 freq ratio
//spyglass enable_block W240
    ,input                              dh_gs_lpddr4                        //
    ,input                              reg_ddrc_lpddr5
    ,input      [NUM_RANKS-1:0]         dh_gs_active_ranks                  // populated DRAM ranks
    ,input      [T_MR_WIDTH-1:0]        reg_ddrc_t_mr                       // time to wait between MRS/MRW to valid command
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used only in LPDDR4 configs, but inputs exist for all HWFFC_EN configs
    ,input      [T_VRCG_ENABLE_WIDTH-1:0] dh_gs_t_vrcg_enable                 // LPDDR4: tVRCG_ENABLE
    ,input      [T_VRCG_DISABLE_WIDTH-1:0]dh_gs_t_vrcg_disable                // LPDDR4: tVRCG_DISABLE
    ,input      [T_ZQ_RESET_NOP_WIDTH-1:0]dh_gs_t_zq_reset_nop                // ZQ Reset NOP period
    ,input      [T_ZQ_STOP_WIDTH-1:0]     reg_ddrc_t_zq_stop
//spyglass enable_block W240
    ,input                              dh_gs_skip_mrw_odtvref
    ,input      [1:0]                   dh_gs_zq_interval                   // HWFFCCTL.zq_interval for LPDDR5

    ,input                              dh_gs_mr_wr                         // input from core to write mode register
                                                                            // 0000: MR0, 0001: MR1, 0010: MR2, 0011: MR3, 0100: MR4, 0101: MR5, 0110: MR6
    ,input      [MRS_A_BITS-1:0]        dh_gs_mr_data                       // mode register data to be written
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
    ,input      [3:0]                   dh_gs_mr_addr                       // input from core: mode register address
    ,input      [NUM_RANKS-1: 0]        dh_gs_mr_rank                       // user selected ranks (driven from register set)
                                                                            // user can select  subset of ranks like either even ranks only/odd ranks only/all ranks
                                                                            // due to address mirroing reuirment of UDIMM some address/bank bit are swapped (need to take care by software)
                                                                            // hence user can not select even and odd rank/ranks together
//spyglass enable_block W240
    ,output                             gs_dh_mr_wr_busy                    // indicates that mode register write operation is in progress
                                                                            // s/w should initiate a write only when this signal is 0
                                                                            // goes from 0 to 1 in the clock after 'dh_gs_mr_wr' is received
                                                                            // goes from 1 to 0 in the clock after the 'mr_wr' is received
                                                                            // any 'dh_gs_mr_wr' that comes when busy is high won't be accepted
    ,input      [15:0]                  dh_gs_mr                            // DDR4: MR0 data, LPDDR4: MR1 data
//spyglass disable_block W240
//SMD: Input declared but not read
//SJ: Used only in LPDDR4 configs, but inputs exist for all HWFFC_EN configs
    ,input      [15:0]                  dh_gs_emr                           // DDR4: MR1 data, LPDDR4: MR2 data
//spyglass enable_block W240
    ,input      [15:0]                  dh_gs_emr2                          // DDR4: MR2 data, LPDDR4: MR3 data
    ,input      [15:0]                  dh_gs_mr6                           // DDR4: MR6 data, LPDDR4: MR14 data
    ,input      [15:0]                  dh_gs_mr22                          // LPDDR4: MR22 data
    ,input      [15:0]                  dh_gs_emr3                          // DDR4: MR3 data, LPDDR4: MR13 data
    ,input      [15:0]                  dh_gs_mr4                           // DDR4: MR4 data, LPDDR4: MR11 data
    ,input      [15:0]                  dh_gs_mr5                           // DDR4: MR5 data, LPDDR4: MR12 data
    ,input                              dh_gs_dfi_phyupd_en                 // Enable for DFI PHY update logic
    ,input                              phy_dfi_phyupd_req                  // PHYUPD request.  For DDR4, we give PHYUPD request priority over automatic MRS commands (geardown entry etc.),
                                                                            // because we can otherwise violate tphyupd_resp
    ,input                              ddrc_dfi_phyupd_ack                 // PHYUPD acknowledge.  For DDR4, we give PHYUPD request priority over automatic MRS commands (geardown entry etc.),

    ,input  [3:0]                       hwffc_mr_update_start               // HWFFC: start auto load MR sequence (pulse)
    ,input                              hwffc_fsp                           // HWFFC: current FSP
    ,output                             hwffc_mr_update_done                // HWFFC: auto load MR sequence finished (pulse)
    ,output                             hwffc_st_mr_vrcg
    ,input                              reg_ddrc_hwffc_mode                 // HWFFC: indicate HWFFC mode 0:legacy 1:new
    ,input                              hwffc_no_other_load_mr
    ,input                              hwffc_vrcg                          // HWFFC: current VRCG
    ,input      [FSM_STATE_WIDTH-1:0]   gs_dh_global_fsm_state              // state machine output from gs_global_fsm

    ,input                              sr_mrrw_en                          // MRR/MRW enable during Self refresh for LPDDR4
    ,input                              load_mr_norm                        // mode register write command sent to the DRAM
    ,output reg [NUM_RANKS-1:0]         load_mr_norm_required               // mode register write request to gs_next_xact
    ,output reg [NUM_RANKS-1:0]         load_mr_norm_required_to_fsm        // mode register write request to gs_global_fsm - to wake-up from self-refresh etc

    ,output     [MRS_A_BITS-1:0]        gs_pi_mrs_a_norm                    // address line during load MR
    ,output reg                         load_mpc_zq_start                   // MCP: ZQ Start
    ,output reg                         load_mpc_zq_latch                   // MCP: ZQ Latch
    ,output                             mr4_req_o

    ,output reg [NUM_RANKS-1:0]         rank_nop_after_load_mr_norm         // NOP after issuing load_mr command

    ,input                              zqcl_due_to_sr_exit_ext             // ZQCL requested due to Self-Refresh exit
    ,input      [NUM_RANKS-1:0]         zq_calib_short_required             // ZQ Calib request - only ctive for LPDDR4 mode
    ,input                              zq_reset_req_on                     // ZQ Reset request is ON
    ,output                             zq_calib_mr_cmd                     // Load MR scheduled for ZQCS or ZQCL scheduled. inform ZQ module.
    ,output                             load_mrw_reset_norm                 // load MR of type MRW scheduled to MRW Reset (addr=63 (x3F))
    ,input                              dh_gs_derate_enable                 // enable the derating operation
    ,input                              dh_gs_mr4_req                       // input from derating module requesting for MRR operation to MR4
    ,input      [NUM_RANKS-1:0]         dh_gs_mr4_req_rank
    ,input      [NUM_RANKS-1:0]         gs_zq_calib_active_ranks            // populated DRAM ranks
//    ,output                             load_mr_mrs_a_norm_zq_lpddr2
    ,input                              zq_lat
    ,input                              dh_gs_mr_type                       // input from core to indicate read/write
    ,output                             gs_pi_mrr                           // MRR due to internal derating operation
    ,output                             gs_pi_mrr_ext                       // MRR due to external MRR request
    ,output                             mrr_op_on                           // goes high when the FSM moves from IDLE to next state due to MRR operation
                                                                            // goes low when FSM moves from NOP to IDLE state after MRR
                                                                            // used by the logic that handles clock gating
                                                                            // clock should be turned on in rt and rd modules for MRR operation

    ,output reg                         gs_hw_mr_norm_busy                  // HW-initiated load MR are issuing
    ,input                              dqsosc_loadmr_upd_req_p
    ,output                             loadmr_dqsosc_upd_done_p
    ,input [NUM_RANKS-1:0]              dqsosc_loadmr_rank
    ,input [MRS_A_BITS-1:0]             dqsosc_loadmr_a
    ,input                              dqsosc_loadmr_mpc
    ,input                              dqsosc_loadmr_mrr
    ,input  [3:0]                       dqsosc_loadmr_snoop_en
    ,input                              normal_ppt2_prepare
    ,output reg [3:0]                   gs_pi_mrr_snoop_en
    ,output reg                         load_mpc_dqsosc_start
    ,input                              ppt2_stop_clk_req
    ,input   [T_PGM_X1_X1024_WIDTH-1:0]                  reg_ddrc_t_pgm_x1_x1024
    ,input                                               reg_ddrc_t_pgm_x1_sel
    ,input   [T_PGMPST_X32_WIDTH-1:0]                    reg_ddrc_t_pgmpst_x32
    ,input   [T_PGM_EXIT_WIDTH-1:0]                      reg_ddrc_t_pgm_exit
    ,input                                               reg_ddrc_ppr_pgmpst_en
    ,input                                               reg_ddrc_ppr_en
    ,output  reg                                         ddrc_reg_ppr_done
    ,input                                               timer_pulse_x1024

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
    ,input                                               reg_ddrc_ctrlupd_after_dqsosc
`endif
`endif
  );

//---------------------------- LOCAL PARAMETERS --------------------------------
// Internal states
localparam  IDLE                      = 2'b00;
localparam  WAIT_FOR_LOAD_MR          = 2'b01;
localparam  WAIT_FOR_LOAD_MR_NOP      = 2'b10;
localparam  IDLE_PDA                  = 2'b00; // Idle state
localparam  ENTER_PDA                 = 2'b01; // To issue 1st MRS command which makes a DRAM to be PDA mode
localparam  EXIT_PDA                  = 2'b11; // To issue 3rd MRS command which makes a DRAM to exit PDA mode


localparam TIMER_BITS = T_PGM_X1_X1024_WIDTH;

localparam    TERM_TMOD                = {TIMER_BITS{1'b0}};         // Decode value to terminate tMOD time period

   //-----------------------
   // Wires
   //-----------------------

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep current coding style.
wire      lpddr_dev;
assign lpddr_dev = dh_gs_lpddr4 | reg_ddrc_lpddr5;
//spyglass enable_block W528


    wire                        mr_wr_detect;                   // detection of mr_wr request by user
   //-----------------------
   // Registers
   //-----------------------

    reg [MRS_A_BITS-1:0]        r_dh_gs_mr_data;
    wire                        mrs_pda_1st_req;                // Three MRS commands which are related to PDA should be issued
                                                                // This is the 1st command of them and comes from software
                                                                // The remaining commands are generated automatically
    wire    [1:0]               mrs_pda_req;                    // [0] 2nd(MR write) / [1] 3rd(exit PDA mode) MRS for PDA. These are issued in PDA mode
    reg [1:0]                   pda_defer_cnt;                  // dis_dq is delayed in global_fsm, so mrs_pda_1st_req assertion should be delayed.

    reg [TIMER_BITS-1:0]        mod_timer;
    reg [MRS_A_BITS-1:0]        mrs_a;
    reg                         mr_wr_busy;
    reg [1:0]                   load_mr_curr_state;

    reg [TIMER_BITS-1:0]        mod_timer_w;
    reg [NUM_RANKS-1:0]         rank_nop_after_load_mr_norm_w;
    reg [NUM_RANKS-1:0]         load_mr_norm_required_w;
    reg [MRS_A_BITS-1:0]        mrs_a_w;
    reg                         mpc_zq_start;
    reg                         mpc_zq_latch;
    wire                        mr_wr_busy_w;
    reg [1:0]                   load_mr_next_state;

    wire                        mrrw_req_in_sr_state; // external mrr/mrw request came when the controller is in any of the self-refresh states
    wire                        mrrw_req;
    reg                         mrrw_req_hold;
    reg                         mrrw_req_r;
    reg                         clear_mrrw_req;
    wire                        any_mr_req_lpddr2;
    wire                        dfi_phyupd_pending;
    wire                        any_mr_req;

    reg [1:0]                   load_mr_norm_type;
    reg [1:0]                   load_mr_norm_type_w;
    reg                         mrrw_type;
    reg                         dh_gs_derate_enable_r;
    wire                        mr4_req;
    reg                         mr4_req_hold;
    reg                         mr4_req_r;
    reg                         mr4_req_ext;
    reg                         mr4_req_ext_r;
    reg                         clear_mr4_req;

    // decoding global FSM
    wire                        global_fsm_eq_self_ref;         // self-refresh state(gs_dh_global_fsm_state[3:2] == 2'b11)
    wire                        mod_timer_expired;              // mod_timer exprired (pulse)
    wire                        hwffc_mr_update_done_w;         // HWFFC: auto load MR sequence finished (pulse)
    reg                         hwffc_load_mr_run;              // HWFFC: auto load MR running
    reg                         hwffc_load_mr_ack_mask;         // HWFFC: auto load MR acknowledge mask
    wire                        hwffc_load_mr_req;              // HWFFC: auto load MR request
    wire                        hwffc_load_mr_req_w;              // HWFFC: auto load MR request
    wire                        hwffc_load_mr_ack;              // HWFFC: auto load MR acknowledge
    wire    [MRS_A_BITS-1:0]    hwffc_load_mr_a;                // HWFFC: auto load MR address
    wire    [NUM_RANKS-1:0]     hwffc_load_mr_rank;             // HWFFC: auto load MR rank
    wire    [TIMER_BITS-1:0]    hwffc_nop_timer_value;          // HWFFC: initial value of NOP timer
    wire                        move_to_idle;                   // Transition from WAIT_FOR_LOAD_MR to IDLE
    wire                        move_to_idle_possible;          // Condition which needs to go back to IDLE state
    wire                        gs_hw_mr_norm_busy_set;         // set gs_hw_mr_norm_busy
    wire                        gs_hw_mr_norm_busy_rst;         // reset gs_hw_mr_norm_busy
    reg ddr4_ppr_use_x1024;


    logic                      dqsosc_req, dqsosc_req_hold;
    logic                      clear_dqsosc_req_p;
    logic                      mpc_dqsosc_start;
    logic                      dqsosc_cmd_in_prog;
    logic [3:0]                gs_pi_mrr_snoop_en_w;
    logic                      mrr_mask_due_to_dqsosc; // It masks periodic MR4 or SW MRR/W when dqsosc is running.

   assign gs_pi_mrr      = load_mr_norm_type[1]   // Indicates internal or external MR4 read
                           || mr4_req_ext_r       // Indicates internal or external MR4 read
                           ;
   assign gs_pi_mrr_ext  = load_mr_norm_type[0];  // Indicates any external MRR operation

    // Detect either ZQCS or ZQCL or ZQReset
    assign zq_calib_mr_cmd = load_mr_norm & (|zq_calib_short_required) &
                                ((dh_gs_lpddr4 ? (gs_pi_mrs_a_norm[15:0] == 16'h0A01) :
                                                 (gs_pi_mrs_a_norm[15:0] == 16'h1C05))  // ZQ reset
                                 || load_mpc_zq_start || load_mpc_zq_latch
                                );


    // MRW to Address 63 ('h3F) i.e. is a MRW Reset
    assign load_mrw_reset_norm = (gs_pi_mrs_a_norm[15:8] == 8'h3F) & load_mr_norm & ~mrrw_type;

    // MRR operation is ON when the FSM is not in IDLE state and when the mr_type is not 2'b00
    // mr_type = 2'b01 for external MRR and is 2'b10 for internal MR4 derating request
    assign mrr_op_on = (load_mr_next_state != IDLE) && (load_mr_norm_type_w != 2'b00);

    //----------------------------------------------
    //  Decoding global FSM
    //----------------------------------------------
    // self-refresh state(gs_dh_global_fsm_state[3:2] == 2'b11)
    assign global_fsm_eq_self_ref   = ((gs_dh_global_fsm_state == GS_ST_SELFREF)          ||
                                       (gs_dh_global_fsm_state == GS_ST_SELFREF_EX_DFILP) ||
                                       ((gs_dh_global_fsm_state == GS_ST_SELFREF_EX1)
                                        && (!lpddr_dev || !sr_mrrw_en)
                                       ) ||
                                       (gs_dh_global_fsm_state == GS_ST_SELFREF_EX2)      ||
                                       (gs_dh_global_fsm_state == GS_ST_SELFREF_ENT_DFILP)
                                    || (
                                                        zqcl_due_to_sr_exit_ext
                                       )
                                    );



    reg [1:0]         pda_curr_state;               // FSM for Per DRAM Addressability
    reg [1:0]         pda_next_state;               // FSM for Per DRAM Addressability (combinational logic)

    // Below two signals indicate inversion or not in case of  Shared-AC RDIMM
    wire   shared_ac_rdimm;                        // indicate shared-ac rdimm mode
    wire   inv_en_shac;                            // indicate inversion or not

//spyglass disable_block W528
//SMD: A signal or variable is set but never read
//SJ: Used under different `ifdefs. Decided to keep the current coding style.
    assign shared_ac_rdimm = 1'b0;
    assign inv_en_shac = 1'b0;
//spyglass enable_block W528


    //-----------------------
    // Combinational Logic
    //-----------------------

   //---------------------------------------------------------------------------------------------
   // load_mr_next_state
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               load_mr_next_state          = WAIT_FOR_LOAD_MR;         // go to next state
            end
            else begin //  any_mr_req==0
               load_mr_next_state          = IDLE;
            end
         end

         WAIT_FOR_LOAD_MR : begin
            if (move_to_idle_possible) begin
               load_mr_next_state              = IDLE;                         // move to IDLE
            end
            else if(load_mr_norm) begin                                     // MRS command issued to DRAM
               load_mr_next_state              = WAIT_FOR_LOAD_MR_NOP;         // go to next state
            end
            else begin
               load_mr_next_state              = WAIT_FOR_LOAD_MR;             // stay in curr state
            end
         end

         // WAIT_FOR_LOAD_MR_NOP :
         default :
         begin
            if(mod_timer ==  TERM_TMOD) begin                                   // t_mod satisfied
               load_mr_next_state              =
                                                  IDLE;  // go to next state
            end
            else begin
               load_mr_next_state              = WAIT_FOR_LOAD_MR_NOP;         // stay in current state
            end
        end


      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // mrs_a_w
   // mrs_ba_w
   //---------------------------------------------------------------------------------------------
   always_comb begin
      mpc_zq_start = 1'b0;
      mpc_zq_latch = 1'b0;
      mpc_dqsosc_start = 1'b0;
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               //*******************
               // DDR4
               //*******************

               //*******************
               // LPDDR4
               //*******************
                  if (hwffc_load_mr_req) begin
                     mrs_a_w                 = hwffc_load_mr_a;
                  end else
                  if (dqsosc_req) begin
                     mrs_a_w                 = dqsosc_loadmr_a;
                     mpc_dqsosc_start        = dqsosc_loadmr_mpc;
                  end else
                  if(|zq_calib_short_required) begin
                     mrs_a_w       = zq_reset_req_on ?
                                                       (dh_gs_lpddr4 ? {{(MRS_A_BITS-16){1'b0}}, 16'h0A01} :
                                                                       {{(MRS_A_BITS-16){1'b0}}, 16'h1C05}) :  // LPDDR5: MR28[0] and set default ZQ interval value 2'b01 MR28 OP[3:2]
                                                       {MRS_A_BITS{1'b0}};
                     mpc_zq_start  = ((zqcl_due_to_sr_exit_ext || !zq_reset_req_on) && !zq_lat);
                     mpc_zq_latch  = ((zqcl_due_to_sr_exit_ext || !zq_reset_req_on) &&  zq_lat);
                  end
                  else if (mr4_req == 1'b1) begin
                     mrs_a_w                  = {{(MRS_A_BITS-16){1'b0}}, 16'h0400};             // load MR4 address  - LPDDR4 format - [7:0] - data, [15:8] - address
                  end
                  else begin
                     mrs_a_w                  = r_dh_gs_mr_data;   // load the data to the address bus - different meaning in LPDDR4 and non-LPDDR4
                  end
            end
            else begin //  any_mr_req==0
               mrs_a_w                     = {MRS_A_BITS{1'b0}};
            end
         end

         WAIT_FOR_LOAD_MR : begin
            if (move_to_idle_possible) begin
               mrs_a_w                         = {MRS_A_BITS{1'b0}};           // reset address
            end
            else if(load_mr_norm) begin                                     // MRS command issued to DRAM
               mrs_a_w                     = {MRS_A_BITS{1'b0}};           // reset address
            end
            else begin
               mrs_a_w                         = mrs_a;                        // hold address
               mpc_zq_start                    = load_mpc_zq_start;
               mpc_zq_latch                    = load_mpc_zq_latch;
               mpc_dqsosc_start                = load_mpc_dqsosc_start;
            end
         end

         // WAIT_FOR_LOAD_MR_NOP :
         default :

         begin
            mpc_zq_start                    = load_mpc_zq_start;
            mpc_zq_latch                    = load_mpc_zq_latch;
            mpc_dqsosc_start                = load_mpc_dqsosc_start;
            if(mod_timer ==  TERM_TMOD) begin                                   // t_mod satisfied
               mrs_a_w                         = {MRS_A_BITS{1'b0}};           // reset address
            end
            else begin
               mrs_a_w                         = mrs_a;
            end
         end

      endcase
   end // always_comb


   //---------------------------------------------------------------------------------------------
   // mod_timer_w
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)

         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
                mod_timer_w     =
                                  (hwffc_load_mr_req) ? {{($bits(mod_timer_w)-$bits(hwffc_nop_timer_value)){1'b0}}, hwffc_nop_timer_value} :
                                  (mrs_pda_1st_req & reg_ddrc_ppr_en)            ? {{($bits(mod_timer_w)-$bits(reg_ddrc_t_pgm_x1_x1024)){1'b0}}, reg_ddrc_t_pgm_x1_x1024} :          // ACT: tPGM
                                  (pda_curr_state==ENTER_PDA & reg_ddrc_ppr_en)  ? {{($bits(mod_timer_w)-$bits(reg_ddrc_t_pgm_exit)){1'b0}}, reg_ddrc_t_pgm_exit} :                  // PRE: tPGM Exit
                                  (reg_ddrc_ppr_pgmpst_en                   )    ? {{($bits(mod_timer_w)-$bits(reg_ddrc_t_pgmpst_x32)-5){1'b0}}, reg_ddrc_t_pgmpst_x32, 5'b1_1111} : // tPGMPST(5'b1_1111 is for x32)  
                     // For LPDDR4, length of MRR/MRW command is 4 cycle.
                     // DQS oscillator command is higher priority than ZQ command.
                         (|zq_calib_short_required
                                  && (!dqsosc_req)
                                                  ) ? {($bits(mod_timer_w)){1'b0}} :
                     //JIRA___ID: LPDDR5 needs to be updated this.
                                  (dh_gs_lpddr4)       ? reg_ddrc_t_mr + ({{($bits(reg_ddrc_t_mr)-2){1'b0}},2'b10} >> dh_gs_frequency_ratio) :
                                  {{($bits(mod_timer_w)-$bits(reg_ddrc_t_mr)){1'b0}}, reg_ddrc_t_mr};
            end
            else begin //  any_mr_req==0
               mod_timer_w  = TERM_TMOD;
            end
         end


         WAIT_FOR_LOAD_MR : begin
            mod_timer_w = mod_timer;
         end

         // WAIT_FOR_LOAD_MR_NOP :
         default :
         begin
            if(mod_timer ==  TERM_TMOD) begin                     // t_mod satisfied
               mod_timer_w = TERM_TMOD;                    // reset the timer
            end
            else begin
               mod_timer_w = mod_timer - {{($bits(mod_timer)-1){1'b0}},(~ddr4_ppr_use_x1024 | timer_pulse_x1024)};   // decrement mod timer
            end
         end


      endcase

   end // always_comb


   //---------------------------------------------------------------------------------------------
   // load_mr_norm_required_w
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)

         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
                  if (hwffc_load_mr_req)
                     load_mr_norm_required_w     = hwffc_load_mr_rank;
                  else
                      if (dqsosc_req) begin
                         load_mr_norm_required_w    = dqsosc_loadmr_rank;
                      end
                      else
                     if(|zq_calib_short_required) begin     // assert mr request due to zq request - only for LPDDR4
                        load_mr_norm_required_w     = gs_zq_calib_active_ranks & zq_calib_short_required;
                     end
                     else if (mr4_req) begin                //MR4 derating request
                        load_mr_norm_required_w     = dh_gs_mr4_req_rank;
                     end
                     else
                     begin                                  // set the request to gs_next_xact (software config for MRS ranks)
                        load_mr_norm_required_w     = dh_gs_active_ranks & dh_gs_mr_rank;
                     end
            end
            else begin //  any_mr_req==0
               load_mr_norm_required_w     = {NUM_RANKS{1'b0}};
            end
         end

         WAIT_FOR_LOAD_MR : begin
            if (move_to_idle_possible || load_mr_norm) begin
               load_mr_norm_required_w         = {NUM_RANKS{1'b0}};           // deassert request
            end
            else begin
               load_mr_norm_required_w         = load_mr_norm_required;       // hold the request
            end
         end

         // WAIT_FOR_LOAD_MR_NOP :
         // WAIT_FOR_CMD_GEAR :
         default : begin
            load_mr_norm_required_w         = {NUM_RANKS{1'b0}};            // keep request deasserted
         end

      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // rank_nop_after_load_mr_norm_w
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)

         IDLE : begin
            rank_nop_after_load_mr_norm_w  = {NUM_RANKS{1'b0}};        // assert nop
         end

         WAIT_FOR_LOAD_MR : begin
            if (move_to_idle_possible) begin
               rank_nop_after_load_mr_norm_w   = {NUM_RANKS{1'b0}};            // keep rank nop 0
            end
            else if(load_mr_norm) begin                                     // MRS command issued to DRAM
               rank_nop_after_load_mr_norm_w   =
                                                  dh_gs_active_ranks &
                                                  {NUM_RANKS{1'b1}};            // assert nop
            end
            else begin
               rank_nop_after_load_mr_norm_w   = {NUM_RANKS{1'b0}};            // keep rank nop 0
            end
         end

         // WAIT_FOR_LOAD_MR_NOP :
         default :
         begin
            if(mod_timer ==  TERM_TMOD) begin                                   // t_mod satisfied
               rank_nop_after_load_mr_norm_w   = {NUM_RANKS{1'b0}};            // reset nop
            end
            else begin
               rank_nop_after_load_mr_norm_w   =
                                                  dh_gs_active_ranks &
                                                  {NUM_RANKS{1'b1}};            // assert nop
            end
         end


      endcase
   end // always_comb


   //---------------------------------------------------------------------------------------------
   // load_mr_norm_type_w
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               if (hwffc_load_mr_req) begin
                  load_mr_norm_type_w = 2'b00;
               end else
               if (dqsosc_req) begin
                  load_mr_norm_type_w  = {dqsosc_loadmr_mrr,1'b0};
               end else
               if(|zq_calib_short_required) begin
                  load_mr_norm_type_w = 2'b00;
               end else if (mr4_req == 1'b1) begin
                  load_mr_norm_type_w = 2'b10;                // code for Internal MR4 Derate Read
               end
               else if (mrs_pda_1st_req
                       ) begin
                  load_mr_norm_type_w = 2'b00;
               end
               else begin
                  if (mrrw_type == 1'b1) begin
                     load_mr_norm_type_w = 2'b01;             // External MRR operation
                  end else begin
                     load_mr_norm_type_w = 2'b00;             // External MRW operation
                  end
               end // if(|zq_calib_short_required)
            end
            else begin //  any_mr_req==0
               load_mr_norm_type_w = 2'b00;             // External MRW operation
            end
         end

         default : begin
            load_mr_norm_type_w = load_mr_norm_type;
         end
      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // gs_pi_mrr_snoop_en_w
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               if (hwffc_load_mr_req) begin
                  gs_pi_mrr_snoop_en_w = 4'b0000;
               end else
               if (dqsosc_req) begin
                  gs_pi_mrr_snoop_en_w  = dqsosc_loadmr_snoop_en;
               end else
                  gs_pi_mrr_snoop_en_w = 4'b0000;
            end
            else begin //  any_mr_req==0
               gs_pi_mrr_snoop_en_w = 4'b0000;
            end
         end

         default : begin
            gs_pi_mrr_snoop_en_w = gs_pi_mrr_snoop_en;
         end
      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // mr4_req_ext
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               if (hwffc_load_mr_req) begin
                  mr4_req_ext         = 1'b0;
               end else
               if (dqsosc_req) begin
                  mr4_req_ext         = 1'b0;
               end else
               if ((|zq_calib_short_required) || (mr4_req == 1'b1)) begin
                  mr4_req_ext         = 1'b0;
               end else begin
                  if (mrrw_type == 1'b1) begin
                     mr4_req_ext         = (r_dh_gs_mr_data[15:8] == 8'h04); // set this if the external MRR is to address MR4
                  end else begin
                     mr4_req_ext         = 1'b0;
                  end
               end // if(|zq_calib_short_required)
            end
            else begin //  any_mr_req==0
               mr4_req_ext         = 1'b0;
            end
         end

         WAIT_FOR_LOAD_MR : begin
            if (move_to_idle_possible) begin
               mr4_req_ext   = 1'b0;                         // reset req
            end
            else begin
               mr4_req_ext   = mr4_req_ext_r;
            end
         end

         default : begin
            mr4_req_ext         = 1'b0;
         end
      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // clear_mr4_req
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               if (hwffc_load_mr_req) begin
                  clear_mr4_req       = 1'b0;
               end else
               if (dqsosc_req) begin
                  clear_mr4_req        = 1'b0;
               end else
               if(!(|zq_calib_short_required) && (mr4_req == 1'b1)) begin
                  clear_mr4_req       = 1'b1;
               end
               else begin
                  clear_mr4_req       = 1'b0;
               end
            end
            else begin //  any_mr_req==0
               clear_mr4_req       = 1'b0;
            end
         end

         default : begin
            clear_mr4_req       = 1'b0;
         end
      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // clear_dqsosc_req_p
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               if (hwffc_load_mr_req) begin
                  clear_dqsosc_req_p       = 1'b0;
               end else
               if (dqsosc_req) begin
                  clear_dqsosc_req_p        = 1'b1;
               end else
               if(!(|zq_calib_short_required) && (mr4_req == 1'b1)) begin
                  clear_dqsosc_req_p       = 1'b0;
               end
               else begin
                  clear_dqsosc_req_p       = 1'b0;
               end
            end
            else begin //  any_mr_req==0
               clear_dqsosc_req_p       = 1'b0;
            end
         end

         default : begin
            clear_dqsosc_req_p       = 1'b0;
         end
      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // clear_mrrw_req
   //---------------------------------------------------------------------------------------------
   always_comb begin
      case(load_mr_curr_state)
         IDLE : begin
            if(any_mr_req) begin               // accept the mr write or read request
               if (
                     hwffc_load_mr_req |
                     (|zq_calib_short_required) |
                     (mr4_req == 1'b1)
                      | (dqsosc_req)
                    ) begin
                  clear_mrrw_req          = 1'b0;        // mrs_pda_req is issued automatically once it enters into PDA mode
               end
               else if (mrs_pda_1st_req
                       ) begin
                  clear_mrrw_req          = 1'b1;
               end
               else begin
                  clear_mrrw_req           =
                                                                  1'b1;
               end
            end
            else begin //  any_mr_req==0
               clear_mrrw_req                 = 1'b0;
            end
         end

         default : begin
            clear_mrrw_req              = 1'b0;
         end
      endcase
   end // always_comb

   //---------------------------------------------------------------------------------------------
   // mr_wr_busy_w
   //---------------------------------------------------------------------------------------------
   assign mr_wr_busy_w = (mrrw_req_hold | dh_gs_mr_wr) | (load_mr_curr_state!=IDLE && mr_wr_busy);



    //-----------------------
    // Assigning the outputs
    //-----------------------

    assign gs_pi_mrs_a_norm     = mrs_a[MRS_A_BITS-1:0];
    assign gs_dh_mr_wr_busy     = mr_wr_busy;

// asserts when the FSM moves from WAIT_FOR_LOAD_MR back to IDLE, with out completing the request
// this happens when the Controller enters SR with a pending Load MR request
// This condition should only happen if the input request arrives 2 clocks before the Controller enters self-refresh mode
// Relies on inter-dependency between and gs_global_fsm and global_fsm_eq_self_ref
// move_to_idle is used in to re-assert mrrw_req/mr4_req if they get
// superseded by self refresh entry
assign move_to_idle = (load_mr_next_state == IDLE) && (load_mr_curr_state == WAIT_FOR_LOAD_MR);

//---------------------------------------------------------------------------------------
// In WAIT_FOR_LOAD_MR state, the following is condition that FSM moves to IDLE
// +--------------+----------+----------+------------------------------------------------
// |   [LPDDR4]   |          |
// |   MRR/MRW    |  Selfref | move_to_idle_possible
// |   in Selfref |          | (This signal doesn't include state information)
// +--------------+----------+------------------------------------------------
// |      0       |     0    | 0
// |      0       |     0    | 1
// |      0       |     1    | 1
// |      0       |     1    | 1
// +--------------+----------+------------------------------------------------
// |      1       |     X    | 0
// +--------------+----------+----------+------------------------------------------------
assign move_to_idle_possible = (global_fsm_eq_self_ref
                               ) & ~sr_mrrw_en;

assign mr_wr_detect =
           |(dh_gs_active_ranks & dh_gs_mr_rank) &
       dh_gs_mr_wr;
   //-----------------------
   // All the flops
   //-----------------------
   always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if(!core_ddrc_rstn) begin
         mrrw_req_hold               <= 1'b0;
         mrrw_req_r                  <= 1'b0;
            dh_gs_derate_enable_r    <= 1'b0;
            mr4_req_hold             <= 1'b0;
            mr4_req_r                <= 1'b0;
            mrrw_type                <= 1'b0;
         r_dh_gs_mr_data             <= {MRS_A_BITS{1'b0}};
      end
      else begin
   // clear_mrrw_req indicates this transition IDLE to WAIT_FOR_LOAD_MR is by mrrw_req
   // mrrw_req_r set by clear_mr4_req
   // reset by transition back into IDLE state
   // if IDLE state was due to Self Refresh (global_fsm_eq_self_ref)
   // move_to_idle=1 will be the case
   // and mrrw_req gets re-asserted
   // More robust than prev logic that

         mrrw_req_r                  <= (clear_mrrw_req) ? 1'b1 : (load_mr_next_state == IDLE) ? 1'b0 : mrrw_req_r;  // store the request

         dh_gs_derate_enable_r       <= dh_gs_derate_enable;
   // clear_mr4_req indicates this transition IDLE to WAIT_FOR_LOAD_MR is by mr4_req
   // similar to mrrw_req above
     // we want to avoid MR4 read requests during initialization
         mr4_req_r                   <=  (clear_mr4_req) ? 1'b1 : (load_mr_next_state == IDLE) ? 1'b0 :  mr4_req_r;  // store the request
         if (mr_wr_detect) begin
           mrrw_req_hold             <= 1'b1;
            mrrw_type                <= dh_gs_mr_type;
           r_dh_gs_mr_data           <= dh_gs_mr_data;
         end
         else if (clear_mrrw_req == 1'b1)
           mrrw_req_hold             <= 1'b0;
         else if((move_to_idle == 1'b1) && mrrw_req_r)  // if FSM returned back to IDLE from WAIT_FOR_LOAD_MR (due to SRE), then re-assert the request
           mrrw_req_hold             <= 1'b1;
         // if MR request from derate module, set mr4_req
         // we want to avoid MR4 read requests during initialization
         // dh_gs_mr4_req is 1 cycle delay for dh_gs_dearte_enable, so need to use dh_gs_derate_enable_r here
         if (dh_gs_mr4_req & dh_gs_derate_enable_r)
           mr4_req_hold              <= 1'b1;
         else if ((clear_mr4_req == 1'b1))
           mr4_req_hold              <= 1'b0;
         else if ((move_to_idle == 1'b1) && mr4_req_r)  // if FSM returned back to IDLE from WAIT_FOR_LOAD_MR (due to SRE), then re-assert the request
           mr4_req_hold              <= 1'b1;
      end
   end // always @ (posedge co_yy_clk or negedge core_ddrc_rstn)

// mask mr4 or SW MRR/W request according to mrr_mask_due_to_dqsosc if needed
assign mr4_req  = mr4_req_hold & mrr_mask_due_to_dqsosc;
assign mrrw_req = mrrw_req_hold & mrr_mask_due_to_dqsosc;


// request from external MR registers OR internal MR4 derating request
// external request or mr4 request is transferred to any_mr_req only if it is not in any of the self-refresh states
// if it is in self-refresh state, this module informs gs_global_fsm through load_mr_norm_required_to_fsm, but
// the actual load_mr_norm request process isn't started until self-refresh state is exited
    // we want to avoid MR4 read requests during initialization
    assign any_mr_req_lpddr2    = (mr4_req & (!global_fsm_eq_self_ref)) | (|zq_calib_short_required)
                                | (|mrs_pda_req)
                                  ;

    assign dfi_phyupd_pending       = dh_gs_dfi_phyupd_en & phy_dfi_phyupd_req & !ddrc_dfi_phyupd_ack;

       assign any_mr_req           = ((mrrw_req & (!global_fsm_eq_self_ref) & (!hwffc_no_other_load_mr))
                                     | any_mr_req_lpddr2 | hwffc_load_mr_req) & ~dfi_phyupd_pending
                                | dqsosc_req
                                | mrs_pda_1st_req
                                ;
    assign mrs_pda_1st_req      = mrrw_req & ~mrrw_type &  reg_ddrc_ppr_en;

   assign mrrw_req_in_sr_state = mrrw_req & global_fsm_eq_self_ref;

   always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
      if(!core_ddrc_rstn) begin
         mod_timer                   <= TERM_TMOD;
         rank_nop_after_load_mr_norm <= {NUM_RANKS{1'b0}};
         load_mr_norm_required       <= {NUM_RANKS{1'b0}};
         load_mr_norm_required_to_fsm <= {NUM_RANKS{1'b0}};
            load_mr_norm_type        <= 2'b00;
            mr4_req_ext_r            <= 1'b0;
            load_mpc_zq_start        <= 1'b0;
            load_mpc_zq_latch        <= 1'b0;
            load_mpc_dqsosc_start    <= 1'b0;
            gs_pi_mrr_snoop_en       <= 4'd0;
         mrs_a                       <= {MRS_A_BITS{1'b0}};
         mr_wr_busy                  <= 1'b0;
         load_mr_curr_state          <= 2'b00;
      end
      else begin
         mod_timer                   <= mod_timer_w;
         rank_nop_after_load_mr_norm <= rank_nop_after_load_mr_norm_w;

         // Load MR Norm required signal sent out due to the assertion of this in FSM or due to
         // MRR/MRW request appearing during self-refresh state (in LPDDR4 mode)
         load_mr_norm_required       <= load_mr_norm_required_w;
         load_mr_norm_required_to_fsm <= load_mr_norm_required_w
                                         | {NUM_RANKS{mrrw_req_in_sr_state}}
                                        ;
            load_mr_norm_type        <= load_mr_norm_type_w;
            mr4_req_ext_r            <= mr4_req_ext;
            load_mpc_zq_start        <= mpc_zq_start;
            load_mpc_zq_latch        <= mpc_zq_latch;
            load_mpc_dqsosc_start   <= mpc_dqsosc_start;
            gs_pi_mrr_snoop_en      <= gs_pi_mrr_snoop_en_w;
         mrs_a                       <= mrs_a_w;
         mr_wr_busy                  <= mr_wr_busy_w;
         load_mr_curr_state          <= load_mr_next_state;
      end
   end

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      mrr_mask_due_to_dqsosc <= 1;
   end else begin
      // Below should be equivalent to mrr_mask_due_to_dqsosc <= ~(dqsosc_loadmr_mrr | normal_ppt2_prepare);
      // If ctrlupd_after_dqsosc is 1, normal_ppt2_prepare starts asserting while dqsosc_loadmr_mrr is 1
      // Checked by a_dqsosc_mrr_mask_value
      if(mrr_mask_due_to_dqsosc && dqsosc_loadmr_mrr) begin
        // Start masking when DQSOSC MRR is started
        mrr_mask_due_to_dqsosc <= 0;
      end else if(!mrr_mask_due_to_dqsosc && !(dqsosc_loadmr_mrr | normal_ppt2_prepare)) begin
        // End masking when DQSOSC MRR is finished && CTRLUPD schedule is not seend
        mrr_mask_due_to_dqsosc <= 1;
      end
   end
end

//------------------------------------------------------------------------------
//  Automatic MR update sequencer
//------------------------------------------------------------------------------
always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      hwffc_load_mr_run <= 1'b0;
   end else if (hwffc_mr_update_done) begin
      hwffc_load_mr_run <= 1'b0;
   end else if (|hwffc_mr_update_start) begin
      hwffc_load_mr_run <= 1'b1;
   end
end

always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      hwffc_load_mr_ack_mask <= 1'b0;
   end else if (load_mr_next_state == IDLE) begin
      hwffc_load_mr_ack_mask <= 1'b0;
   end else if ((|hwffc_mr_update_start) &&
                ((!move_to_idle_possible && (load_mr_next_state == WAIT_FOR_LOAD_MR)) ||
                 (load_mr_next_state != WAIT_FOR_LOAD_MR))) begin
      hwffc_load_mr_ack_mask <= 1'b1;
   end
end

assign mod_timer_expired    = (load_mr_curr_state == WAIT_FOR_LOAD_MR_NOP) & (mod_timer == TERM_TMOD);
assign hwffc_load_mr_ack = hwffc_load_mr_run & ~hwffc_load_mr_ack_mask & mod_timer_expired;
assign hwffc_load_mr_req =
                                          hwffc_load_mr_req_w;
assign hwffc_mr_update_done =
                                          hwffc_mr_update_done_w;
gs_load_mr_hwffc_seq
 #(
    .TIMER_BITS             (TIMER_BITS          ),
    .MRW_A_BITS             (MRS_A_BITS          ),
    .NUM_RANKS              (NUM_RANKS           )
) hwffc_seq (
    .clk                    (co_yy_clk                  ),
    .rstn                   (core_ddrc_rstn             ),
    .i_mr1_data             (dh_gs_mr                   ),
    .i_mr2_data             (dh_gs_emr                  ),
    .i_mr3_data             (dh_gs_emr2                 ),
    .i_mr11_data            (dh_gs_mr4                  ),
    .i_mr12_data            (dh_gs_mr5                  ),
    .i_mr13_data            (dh_gs_emr3                 ),
    .i_mr14_data            (dh_gs_mr6                  ),
    .i_mr22_data            (dh_gs_mr22                 ),
    .dh_gs_active_ranks     (dh_gs_active_ranks         ),
    .i_t_mr                 (reg_ddrc_t_mr              ),
    .i_t_vrcg_enable        (dh_gs_t_vrcg_enable        ),
    .i_t_vrcg_disable       (dh_gs_t_vrcg_disable       ),
    .i_t_zq_reset_nop       (dh_gs_t_zq_reset_nop       ),
    .i_t_zq_stop            (reg_ddrc_t_zq_stop         ),
    .i_skip_mrw_odtvref     (dh_gs_skip_mrw_odtvref     ),
    .i_mr_update_start      (hwffc_mr_update_start      ),
    .o_mr_update_done       (hwffc_mr_update_done_w     ),
    .i_curr_fsp             (hwffc_fsp                  ),
    .i_curr_vrcg            (hwffc_vrcg                 ),
    .i_zq_interval          (dh_gs_zq_interval          ),
    .i_hwffc_mode           (reg_ddrc_hwffc_mode        ),
    .o_load_mr_req          (hwffc_load_mr_req_w        ),
    .i_load_mr_ack          (hwffc_load_mr_ack          ),
    .o_load_mr_a            (hwffc_load_mr_a            ),
    .o_load_mr_rank         (hwffc_load_mr_rank         ),
    .o_nop_timer_value      (hwffc_nop_timer_value      ),
    .o_st_mr_vrcg           (hwffc_st_mr_vrcg           )
);
    // Busy output to stop other commands being issued during HW-initiated MRS accesses
    assign gs_hw_mr_norm_busy_set   =
                                        (|hwffc_mr_update_start)
                                    ;

    assign gs_hw_mr_norm_busy_rst   =
                                        hwffc_mr_update_done
                                    ;

    always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if (!core_ddrc_rstn) begin
            gs_hw_mr_norm_busy <= 1'b0;
        end else if (gs_hw_mr_norm_busy_set) begin
            gs_hw_mr_norm_busy <= 1'b1;
        end else if (gs_hw_mr_norm_busy_rst) begin
            gs_hw_mr_norm_busy <= 1'b0;
        end
    end


    //--------------------------------------------
    // Finite State Machine
    // for  Per DRAM Addressability
    //--------------------------------------------
    always @ (*) begin
        //ccx_fsm:;pda_curr_state;ENTER_PDA->IDLE_PDA;Resetting DDRCTL is required to cover.
        case (pda_curr_state)
            IDLE_PDA : pda_next_state = ((load_mr_curr_state == IDLE) & mrs_pda_1st_req)     ? ENTER_PDA : pda_curr_state;  // IDLE
            ENTER_PDA: pda_next_state = ((load_mr_curr_state == IDLE))                       ? EXIT_PDA  : pda_curr_state;  // PPR ACT
            default  : pda_next_state =  (mod_timer == TERM_TMOD)                            ? IDLE_PDA  : pda_curr_state;  // PPR PRE
        endcase
    end

    always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if(!core_ddrc_rstn) begin
            pda_curr_state <= IDLE_PDA;
        end
        else begin
            pda_curr_state <= pda_next_state;
        end
    end

    //--------------------------------------------------------------------------------------
    // ddrc_reg_ppr_done
    //     Asserted high when PPR mode is finished in hardware/DRAM
    //     Software should send acknowledge in order to terminate PPR transaction
    //     * This means software write "ppr_en" to 0
    //--------------------------------------------------------------------------------------
    always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if(!core_ddrc_rstn) begin
            ddrc_reg_ppr_done <= 1'b0;
        end
        else begin
            ddrc_reg_ppr_done <=
            ((pda_curr_state == EXIT_PDA) & (pda_next_state == IDLE_PDA)) ? 1'b1           :
            (~reg_ddrc_ppr_en                                           ) ? 1'b0           :
                                                                            ddrc_reg_ppr_done;
        end
    end

    always @ (posedge co_yy_clk or negedge core_ddrc_rstn) begin
        if(!core_ddrc_rstn) begin
            ddr4_ppr_use_x1024 <= 1'b0;
        end
        else begin
            if (reg_ddrc_ppr_en) begin
                if (load_mr_curr_state==IDLE) begin
                    if (any_mr_req && pda_curr_state==IDLE_PDA) begin
                      ddr4_ppr_use_x1024 <= ~reg_ddrc_t_pgm_x1_sel;
                    end
                    else begin
                      ddr4_ppr_use_x1024 <= 1'b0;
                    end
                end 
            end
            else begin
                ddr4_ppr_use_x1024 <= 1'b0;
            end
        end
    end

    // mrs_pda_req
    //     It creates 3rd PPR request. Note that '2nd' is reserved for WR cmd in DDR4 PPR. And 2nd is not used in LPDDR5 PPR because WR is not used.
    assign mrs_pda_req         = {((load_mr_curr_state == IDLE) &                       (pda_curr_state == ENTER_PDA)),    // 3rd PPR request (PRE) in LPDDR5 PPR
                                  (1'b0                                                                              )};   // 2nd PPR request (WR) (reserved)

    // If (oveerridden) PPT2/CTRLUPD is about to be sent, block DQSOSC MPC until CTRLUPD finishes.
    // PHY stops clock during CTRLUPD. If MPC is sent first, clock stops during oscillator is running while it is illegal.
    // In contrast, PPT2/CTRLUPD should not block DQSOSC MRR because DQSOSC blocks ctrlupd at that stage. DONT let them block each other
    assign dqsosc_req = dqsosc_req_hold & !(dqsosc_loadmr_mpc & ppt2_stop_clk_req);

    always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin : dqsosc_req_PROC
       if (!core_ddrc_rstn)
          dqsosc_req_hold  <= 1'b0;
       else if (dqsosc_loadmr_upd_req_p)
          dqsosc_req_hold  <= 1'b1;
       else if (clear_dqsosc_req_p)
          dqsosc_req_hold  <= 1'b0;
    end

    always_ff @(posedge co_yy_clk or negedge core_ddrc_rstn) begin : dqsosc_cmd_in_prog_PROC
       if (!core_ddrc_rstn)
          dqsosc_cmd_in_prog  <= 1'b0;
       else if (clear_dqsosc_req_p)
          dqsosc_cmd_in_prog  <= 1'b1;
       else if (load_mr_norm)
          dqsosc_cmd_in_prog  <= 1'b0;
    end

    assign  loadmr_dqsosc_upd_done_p =  dqsosc_cmd_in_prog & load_mr_norm;


  assign mr4_req_o = mr4_req_r;

`ifdef SNPS_ASSERT_ON
`ifndef SYNTHESIS
//------------------------------------------------------------------------------
// Assertions
//------------------------------------------------------------------------------

    covergroup cg_lp5ppr_mr @(posedge co_yy_clk);
        // Observe all t_pgm* are loaded into mod_timer_w during LPDDR5 PPR
        cp_mod_timer : coverpoint ({
            mod_timer_w == {{($bits(mod_timer_w)-$bits(reg_ddrc_t_pgmpst_x32)-5){1'b0}}, reg_ddrc_t_pgmpst_x32, 5'b1_1111},
            mod_timer_w == {{($bits(mod_timer_w)-$bits(reg_ddrc_t_pgm_exit)){1'b0}},     reg_ddrc_t_pgm_exit},
            mod_timer_w == {                                                             reg_ddrc_t_pgm_x1_x1024}
        }) iff(core_ddrc_rstn & (reg_ddrc_ppr_en | reg_ddrc_ppr_pgmpst_en) & any_mr_req) {
                    bins T_PGM          = {3'b001};
                    bins T_PGM_EXIT     = {3'b010};
                    bins T_PGMPST       = {3'b100};
            illegal_bins UNEXPECT_LOAD  = {3'b000};  // One of t_pgm* should have been loaded but did not
        }
    endgroup

    // Coverage group instantiation
    cg_lp5ppr_mr cg_lp5ppr_mr_inst = new;


    a_dqsosc_mrr_mask_value : assert property (
        @(posedge co_yy_clk) disable iff (~core_ddrc_rstn || ~reg_ddrc_ctrlupd_after_dqsosc)
            !$stable(mrr_mask_due_to_dqsosc) |=> mrr_mask_due_to_dqsosc == $past(~(dqsosc_loadmr_mrr | normal_ppt2_prepare))
    ) else $error("[%t][%m] ERROR: mrr_mask_due_to_dqsosc didn't change as expected", $time);

    a_consume_mrreq_during_dqsosc_mrr_mask : assert property (
        @(posedge co_yy_clk) disable iff (~core_ddrc_rstn)
            // mrr_mask_due_to_dqsosc==0 means MRR IS masked due to dqsosc
            ~mrr_mask_due_to_dqsosc && any_mr_req && load_mr_curr_state==IDLE |->
                !clear_mr4_req && $onehot({ hwffc_load_mr_req, mpc_zq_latch, mpc_zq_start, (zq_reset_req_on&&zq_calib_short_required), clear_dqsosc_req_p, clear_mrrw_req})
    ) else $error("[%t][%m] ERROR: If there is any mr req during mrr_mask_due_to_dqsosc, mr4 req should not be consumed. dqsosc, ZQ or mrrw should be consumed.", $time);

    a_dqsosc_mrr_not_blocked : assert property (
        @(posedge co_yy_clk) disable iff (~core_ddrc_rstn)
            dqsosc_loadmr_mrr |-> dqsosc_req == dqsosc_req_hold
    ) else $error("[%t][%m] ERROR: Overridden PPT2 attempts to block DQSOSC while DQSOSC MRR is ongoing.", $time);


`endif // SYNTHESIS
`endif // SNPS_ASSERT_ON

endmodule // gs_load_mr
