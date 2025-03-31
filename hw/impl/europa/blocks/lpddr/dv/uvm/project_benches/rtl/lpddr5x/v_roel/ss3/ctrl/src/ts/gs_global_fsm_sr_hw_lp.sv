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
// -- Revision: $Id: //dwh/ddr_iip/umctl5/DWC_ddrctl_lpddr54_MAIN_BR/DWC_ddr_umctl5/src/ts/gs_global_fsm_sr_hw_lp.sv#10 $
// -------------------------------------------------------------------------
// Description:
//
// gs_global_fsm - Global Scheduler
// This block implements the finite state machine responsible for tracking the
// global state of the DDR1/2 DRAM.  States are:
//  * init sequence
//  * "normal" (read/write) state
//  * self-refresh
// This blocks also chooses read mode/write mode and implements all
// starvations-avoidance state machines and indicates when to prefer low
// priority reads accordingly.
//------------------------------------------------------------------------------ 
// SELF-REFRESH EXIT SEQUENCE is as follows:
//  1) In SELFREF state.  End of self-refresh marked by:
//      * clearing self-refresh bit or new transaction registered by TE.
//  3) In SELFREF_EX state.  Wait for tXS in case of non DDR4 devices.
//     Wait for tXS_FAST in case of DDR4 devices.
//     The mode_exit_timer waits for dh_gs_t_xs_x32/dh_gs_t_xs_dll_x32
//     /dh_gs_t_xs_abort_x32/dh_gs_t_xs_fast_x32 pulses of the pulse_x32 
//     pulse in case of DDR4 SDRAMs, and for dh_gs_t_xsr 
//     clock cycles in case of LPDDR4 SDRAMs.
//  4) Back up and running in read or write mode (depending on prefer_wr) 
//
//
// ----------------------------------------------------------------------------
//
// Module that controls generation of Self Refresh Entry/Exit and
// responds to Hardare Low Power Interface
// 
`include "DWC_ddrctl_all_defs.svh"
`include "apb/DWC_ddrctl_reg_pkg.svh"
module gs_global_fsm_sr_hw_lp 
import DWC_ddrctl_reg_pkg::*;
#(
//------------------------------- PARAMETERS ----------------------------------
   parameter        BCM_VERIF_EN        = 1
  ,parameter        BCM_DDRC_N_SYNC     = 2

  ,parameter        NPORTS              = 1 // no. of ports (for cactive_in_ddrc width) gets overwritten by toplevel
  ,parameter [16:0] A_SYNC_TABLE        = 17'h1ffff

  ,parameter        CMD_DELAY_BITS      = `UMCTL2_CMD_DELAY_BITS

  ,parameter        FSM_STATE_WIDTH     = 5

  ,parameter    SELFREF_SW_WIDTH_INT = SELFREF_SW_WIDTH
  ,parameter    SELFREF_EN_WIDTH_INT = SELFREF_EN_WIDTH
  ,parameter    SELFREF_TYPE_WIDTH_INT = SELFREF_TYPE_WIDTH
  ,parameter        NUM_RANKS           = 1
)
(
//--------------------------- INPUTS AND OUTPUTS -------------------------------
  // clk/rst
   input                          co_yy_clk
  ,input                          core_ddrc_rstn
  ,output reg    [NUM_RANKS-1:0]  bsm_clk_en                      // Clock enable for bsm instances
  ,input         [BSM_CLK_ON_WIDTH-1:0] bsm_clk_on                // bsm_clk always on
  ,input         [NUM_RANKS-1:0]  dh_gs_active_ranks

  // signals from top
  ,input [SELFREF_SW_WIDTH_INT-1:0]   reg_ddrc_selfref_sw
  ,input                          reg_ddrc_hw_lp_en
  ,input                          reg_ddrc_hw_lp_exit_idle_en
  ,input                          startup_in_self_ref
  ,output [SELFREF_TYPE_WIDTH_INT-1:0]ddrc_reg_selfref_type
  ,input                          ih_busy
  ,input                          hif_cmd_valid
  ,input  [DFI_T_CTRL_DELAY_WIDTH-1:0]                   reg_ddrc_dfi_t_ctrl_delay
  ,input                          phy_dfi_phyupd_req
  ,input                          phy_dfi_phymstr_req
  ,input                          reg_ddrc_dfi_phymstr_en
  ,input                          reg_ddrc_dfi_phyupd_en
  ,input                          cactive_in_ddrc_sync_or
  ,input  [NPORTS-1:0]            cactive_in_ddrc_async
  ,input                          csysreq_ddrc
  ,output                         csysreq_ddrc_mux
  ,input                          csysmode_ddrc
  ,input  [4:0]                   csysfrequency_ddrc
  ,input                          csysdiscamdrain_ddrc
  ,input                          csysfsp_ddrc
  ,output                         csysack_ddrc
  ,output                         cactive_ddrc

  ,input                          load_mr_norm_required_1bit

  ,input  [FSM_STATE_WIDTH-1:0]   gsfsm_next_state
  ,input  [FSM_STATE_WIDTH-1:0]   gsfsm_current_state
  ,input                          gsfsm_state_selfref_ent_dfilp
  ,input  [DFI_TLP_RESP_WIDTH-1:0]reg_ddrc_dfi_tlp_resp
  ,input  [CMD_DELAY_BITS-1:0]    dfi_cmd_delay
  ,input                          lpddr_dev

  ,input                          gsfsm_idle
  ,input  [SELFREF_EN_WIDTH_INT-1:0]      dh_gs_selfref_en
  ,input  [SELFREF_TO_X32_WIDTH-1:0]  reg_ddrc_selfref_to_x32
  ,input  [HW_LP_IDLE_X32_WIDTH-1:0]  reg_ddrc_hw_lp_idle_x32
  ,input                          timer_pulse_x32_dram

  ,output                         gsfsm_sr_entry_req
  ,output                         gsfsm_sr_exit_req

  ,output                         gsfsm_sr_hw_lp_pd_cs_exit
  ,output                         gsfsm_sr_co_if_stall
  ,input                          gs_phymstr_sre_req
  ,input                          dh_gs_dis_cam_drain_selfref
  ,output                         gsfsm_sr_dis_dq
  ,output                         gs_bs_sre_stall
  ,output                         gs_bs_sre_hw_sw
  ,input                          normal_ppt2_prepare
  ,output reg                     gsfsm_asr_to_sre_asr
  ,input                          ddrc_reg_ppt2_burst_busy
  ,input                          ppt2_asr_to_sre_asr
  ,output reg                     gsfsm_srpd_to_sr
  ,output reg                     gsfsm_sr_no_pd_to_srx
  ,input                          dh_gs_lpddr4_sr_allowed
  ,input                          reg_ddrc_hwffc_mode
  ,output reg                     hwffc_no_other_load_mr
  ,input                          reg_ddrc_skip_zq_stop_start
  ,output reg                     hwffc_asr_to_sre_hsr
  ,output                         hwffc_dfi_init_start
  ,output reg [4:0]               hwffc_dfi_frequency
  ,output reg                     hwffc_dfi_freq_fsp
  ,input                          dfi_init_complete_hwffc
  ,output                         hwffc_in_progress
  ,output                         hwffc_freq_change
  ,output reg                     hwffc_target_freq_en
  ,output reg [TARGET_FREQUENCY_WIDTH-1:0]        hwffc_target_freq
  ,output reg [TARGET_FREQUENCY_WIDTH-1:0]        hwffc_target_freq_init
  ,output reg                     hwffc_vrcg
  ,input                          reg_ddrc_init_vrcg
  ,output reg [3:0]               hwffc_mr_update_start
  ,input                          hwffc_mr_update_done
  ,input                          hwffc_st_mr_vrcg
  ,input                          hwffc_bgzq_stopped
  ,output     [3:0]               hwffc_zq_restart                    // pulse to request zq calib before/after hwffc
  ,input                          dqsosc_stopped
  ,input                          gs_pi_op_is_load_mr_norm            // load_mr_norm command issued to DRAM
  ,input      [NUM_RANKS-1:0]     rank_nop_after_load_mr_norm         // nop time after load_mr_norm
  ,input                          gs_pi_data_pipeline_empty
  ,input                          t_rd2pd_satisfied
  ,input                          gs_wck_stop_ok
  ,input                          reg_ddrc_target_vrcg
  ,input      [1:0]               reg_ddrc_hwffc_en
  ,input      [TARGET_FREQUENCY_WIDTH-1:0]        reg_ddrc_target_frequency
  ,input                          reg_ddrc_lpddr5
  ,input                          reg_ddrc_init_fsp
  ,output                         hwffc_stay_in_selfref
  ,input                          phymstr_active
  ,input                          reg_ddrc_dvfsq_enable
  ,input                          reg_ddrc_dvfsq_enable_next
  ,output                         hwffc_mask_dfireq
  ,output                         hwffc_dis_zq_derate
  ,output                         hwffc_sre
  ,output                         hwffc_refresh_update_pulse
  ,input                          ctrlupd_req
  ,output                         hwffc_hif_wd_stall
  ,output reg                     ddrc_xpi_port_disable_req
  ,output reg                     ddrc_xpi_clock_required
  ,input [NPORTS-1:0]             xpi_ddrc_port_disable_ack
  ,input [NPORTS-2:0]             xpi_ddrc_wch_locked
   ,input                         ddrc_reg_ctrlupd_burst_busy
);

//---------------------------- LOCAL PARAMETERS --------------------------------
// define global FSM states
// NOTE: Changing any encoding will require a corresponding change to the
//       next_state MUX in the code below 

    localparam GS_ST_RESET                = 5'b00000;
    localparam GS_ST_INIT_DDR             = 5'b00010;
    localparam GS_ST_NORMAL_RD            = 5'b00100;
    localparam GS_ST_NORMAL_WR            = 5'b00101;
    localparam GS_ST_POWERDOWN_ENT        = 5'b00110;    // powerdown pads then DDR
    localparam GS_ST_POWERDOWN_ENT_DFILP  = 5'b00001;    // DFI LP I/F entry PD
    localparam GS_ST_POWERDOWN            = 5'b01000;    // in powerdown
    localparam GS_ST_POWERDOWN_EX_DFILP   = 5'b01001;    // DFI LP I/F exit PD
    localparam GS_ST_POWERDOWN_EX1        = 5'b01010;    // power up pads
    localparam GS_ST_POWERDOWN_EX2        = 5'b01011;    // power up DDR
    localparam GS_ST_SELFREF_ENT          = 5'b00111;    // put DDR in self-refresh then power down pads
    localparam GS_ST_SELFREF_ENT2         = 5'b10101;    // Disable C/A Parity before SR if C/A parity had been enabled 
    localparam GS_ST_SELFREF_ENT_DFILP    = 5'b00011;    // DFI LP I/F entry SR
    localparam GS_ST_SELFREF              = 5'b01100;    // DDR is in self-refresh
    localparam GS_ST_SELFREF_EX_DFILP     = 5'b01101;    // DFI LP I/F exit SR
    localparam GS_ST_SELFREF_EX1          = 5'b01110;    // power up pads
    localparam GS_ST_SELFREF_EX2          = 5'b01111;    // bring DDR out of self-refresh

        localparam GS_ST_DSM_ENT_DFILP    = 5'b11000;    // DFI LP I/F entry DSM
        localparam GS_ST_DSM              = 5'b11001;    // DDR is in deep sleep mode
        localparam GS_ST_DSM_EX_DFILP     = 5'b11010;    // DFI LP I/F exit DSM

// if changing, check ddrc_reg_selfref_type generation too as uses
// sr_st_curr[5] for SR_ST_SR_ASR
// sr_st_curr[4] for SR_ST_SR_HW_SW
localparam SR_ST_SIZE             = 9;
localparam SR_ST_RST_INIT         = 9'b000000001;
localparam SR_ST_NORM_PD          = 9'b000000010;
localparam SR_ST_SRE_HW_SW        = 9'b000000100;
localparam SR_ST_SRE_ASR          = 9'b000001000;
localparam SR_ST_SR_HW_SW         = 9'b000010000;
localparam SR_ST_SR_ASR           = 9'b000100000;
localparam SR_ST_SRX              = 9'b001000000;
localparam SR_ST_SRE_HW_SW_STALL  = 9'b010000000;
localparam SR_ST_DSM              = 9'b100000000;

// For HWFFC FSM
localparam HWFFC_ST_SIZE          = 4;
localparam HWFFC_ST_IDLE          = 4'b0000;
localparam HWFFC_ST_WAIT          = 4'b0001;
localparam HWFFC_ST_SRE           = 4'b0010;
////   `ifdef MEMC_LPDDR4
localparam HWFFC_ST_PHY_ST_REQ    = 4'b0101; // used only when MEMC_LPDDR4 is defined
localparam HWFFC_ST_MR_UPDATE     = 4'b0011; // used only when MEMC_LPDDR4 is defined
localparam HWFFC_ST_WAIT_ZQ_LATCH = 4'b1011; // used only when MEMC_LPDDR4 is defined and dvfsq is switching
localparam HWFFC_ST_SRPDE         = 4'b0100; // used only when MEMC_LPDDR4 is defined
localparam HWFFC_ST_WAIT_PHY_REQ_OK = 4'b1010; // used only when MEMC_LPDDR4 is defined
////   `endif // MEMC_LPDDR4
localparam HWFFC_ST_FREQ_CHANGE   = 4'b0110;
localparam HWFFC_ST_PHY_END_REQ   = 4'b0111;
localparam HWFFC_ST_SRX           = 4'b1000;
localparam HWFFC_ST_END           = 4'b1001;
////   `ifdef MEMC_DDR4
localparam HWFFC_ST_SR_ENT_EN      = 4'b1010; // used only when MEMC_DDR4 is defined
localparam HWFFC_ST_PRE_MR_UPDATE  = 4'b1011; // used only when MEMC_DDR4 is defined
localparam HWFFC_ST_POST_MR_UPDATE = 4'b1100; // used only when MEMC_DDR4 is defined
////   `endif // MEMC_DDR4 

// For AXI port control FSM
localparam XPI_ST_SIZE            = 2;
localparam XPI_ST_NORM            = 2'b00;
localparam XPI_ST_DIS_REQ         = 2'b01;
localparam XPI_ST_DISABLED        = 2'b10;
localparam XPI_ST_ENA_REQ         = 2'b11;

typedef enum logic [1:0] {
   DVFSQ_HOLD       = 2'b00
  ,DVFSQ_HIGH2LOW   = 2'b01
  ,DVFSQ_LOW2HIGH   = 2'b10
} dvfsq_switch_e;

//------------------------------------ WIRES/REGS -----------------------------------

wire                 i_csysreq_ddrc_mux;
reg [SR_ST_SIZE-1:0] sr_st_curr, sr_st_nxt;


// Input registers 
reg                         i_csysmode_ddrc_r;
reg                         csysreq_ddrc_r;
reg     [4:0]               i_csysfrequency_ddrc_r;
reg                         i_csysdiscamdrain_ddrc_r;
reg                         i_csysfsp_ddrc_r;

// Pre-process for HWFFC
reg     [1:0]               i_hwffc_en_r;
reg                         csysreq_dl;
reg                         hwffc_requested;
reg                         i_dis_drain_cam;
reg                         i_target_vrcg;
wire                        hwffc_init;
wire                        hwffc_end;
wire                        hwffc_trg;
wire                        hwffc_trg_avl;
wire                        hwffc_trg_rej;
wire                        csysreq_rise;
wire                        i_freq_cng_trg;
wire                        i_retrain_trg;
wire                        i_lp2_trg;
wire                        i_lp3_trg;
reg                         i_freq_cng_flg;
reg                         i_retrain_flg;
reg                         i_lp2_flg;
reg                         i_lp3_flg;
wire                        freq_cng_pre;
wire                        retrain_required;
wire                        lp2_required;
wire                        lp3_required;
wire                        lp23_no_zqstop;
reg                         hwffc_lp3_entered;
dvfsq_switch_e              dvfsq_switch;
wire                        freq_cng_required;
wire                        no_mr1st_update;
wire                        no_mr2nd_update;
wire                        hwffc_mask;
wire                        i_ns_srpd;
wire                        hwffc_dfi_init_start_lpddr4;

// HSFFC State M/C
reg     [HWFFC_ST_SIZE-1:0] hwffc_st_curr;
wire    [HWFFC_ST_SIZE-1:0] hwffc_st_nxt;
reg     [HWFFC_ST_SIZE-1:0] hwffc_st_nxt_wlp;
// Signals based on state
reg     [1:0]               init_start_dl_cntr;
reg     [2:0]               init_start_dl2_cntr;
reg     [1:0]               hwffc_bgzq_stopped_propagate;
reg     [1:0]               hwffc_ref_upd_r;
reg                         hwffc_accepted;
reg                         hwffc_rejected;
wire                        hwffc_st_cng;
wire                        hwffc_sr_req;
wire                        hwffc_add_hif_stall;
wire                        hwffc_srx_req;
wire                        hwffc_st_wait;
wire                        hwffc_ref_upd_pre;
wire                        mrwbuf_trg;
wire                        mr_upd_1st_trg;
wire                        mr_upd_2nd_trg;
wire                        hwffc_cactive_ddrc;
wire                        csysack_ffcproc;
wire                        hwffc_responding;
wire                        hwffc_csysack_ddrc;
reg [XPI_ST_SIZE-1:0]       xpi_st_curr, xpi_st_nxt;
wire                        xpi_st_cng;
wire                        xpi_disabled;
wire                        axi_dis_ack;
wire                        axi_enb_ack;

wire dh_gs_ddr4;
//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
assign dh_gs_ddr4 = 1'b0;
//spyglass enable_block W528

//------------------------------------ LOGIC -----------------------------------


//
// cactive_in_ddrc/csysreq_ddrc related signals
//

wire i_cactive_in_ddrc_sync_or = cactive_in_ddrc_sync_or
                               | ddrc_xpi_clock_required
                                 ;

// Select the registered version in order to improve 
// timings as there is a combinatorial path to
// cactive_ddrc output port 
assign i_csysreq_ddrc_mux = csysreq_ddrc_r;

assign csysreq_ddrc_mux = i_csysreq_ddrc_mux;

//------------------------------------------------------------
// Clock removal for bsm 
//------------------------------------------------------------
// index of CLKGATECTL.bsm_clk_on
localparam BSM_CLK_ON_RANKS = 0;
localparam BSM_CLK_ON_INIT  = 1;
localparam BSM_CLK_ON_SR    = 2;
localparam BSM_CLK_ON_SRPD  = 3;
localparam BSM_CLK_ON_PD    = 4;
localparam BSM_CLK_ON_DSM   = 5;
// clock enable signal
wire bsm_clk_en_w = ~(
// list of clock DISABLE condition
       (gsfsm_next_state==GS_ST_RESET                        ) ||
       (gsfsm_next_state==GS_ST_INIT_DDR    && ~bsm_clk_on[BSM_CLK_ON_INIT]) ||
//     (gsfsm_next_state==GS_ST_SELFREF_ENT2&& ~bsm_clk_on[BSM_CLK_ON_SR  ]) ||
       (gsfsm_next_state==GS_ST_SELFREF     && ~bsm_clk_on[BSM_CLK_ON_SRPD]) ||
       (gsfsm_next_state==GS_ST_SELFREF_EX1 && ~bsm_clk_on[BSM_CLK_ON_SR  ]) ||
//     (gsfsm_next_state==GS_ST_SELFREF_EX2 && ~bsm_clk_on[BSM_CLK_ON_SR  ]) ||
      ((gsfsm_next_state==GS_ST_POWERDOWN   && ~bsm_clk_on[BSM_CLK_ON_PD  ]) && csysreq_ddrc) ||
       (gsfsm_next_state==GS_ST_DSM         && ~bsm_clk_on[BSM_CLK_ON_DSM ])
    );

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    bsm_clk_en <= {NUM_RANKS{1'b1}};
  end else begin
    bsm_clk_en <= {NUM_RANKS{bsm_clk_en_w}}
                   & (dh_gs_active_ranks | {NUM_RANKS{bsm_clk_on[BSM_CLK_ON_RANKS]}})
    ;
  end
end

//
// Pre-process for HWFFC
//
// signal to block any other loadMR during Self-Refresh before SR-Powerdown
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_no_other_load_mr <= 1'b0;
  end else if (reg_ddrc_hwffc_mode) begin
    // Prohibit SW MR from HWFFC_ST_MR_UPDATE until HWFFC_ST_SRX
    hwffc_no_other_load_mr <=
         hwffc_st_curr==HWFFC_ST_SRPDE
      || hwffc_st_curr==HWFFC_ST_WAIT_PHY_REQ_OK
      || hwffc_st_curr==HWFFC_ST_PHY_ST_REQ
      || hwffc_st_curr==HWFFC_ST_FREQ_CHANGE
      || hwffc_st_curr==HWFFC_ST_PHY_END_REQ
      ;
  end else if (gsfsm_next_state == GS_ST_SELFREF) begin
    hwffc_no_other_load_mr <= 1'b0;
  end else if ((gsfsm_current_state == GS_ST_SELFREF_ENT2) && hwffc_mr_update_done && !hwffc_st_mr_vrcg) begin
    hwffc_no_other_load_mr <= 1'b1;
  end
end


always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_hwffc_en_r <= 2'd0;
  end else begin
    i_hwffc_en_r <= reg_ddrc_hwffc_en;
  end 
end

// csysreq_ddrc input register
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: csysreq_ddrc_r_PROC
  if(!core_ddrc_rstn) begin
    csysreq_ddrc_r <= 1'b1;
  end else begin
    csysreq_ddrc_r <= csysreq_ddrc;
  end 
end

// csysmode_ddrc input register
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_csysmode_ddrc_r_PROC
  if(!core_ddrc_rstn) begin
    i_csysmode_ddrc_r <= 1'b0;
  end else begin
    i_csysmode_ddrc_r <= csysmode_ddrc;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    csysreq_dl <= 1'b0;
  end else begin
    csysreq_dl <= i_csysreq_ddrc_mux;
  end 
end


assign hwffc_init       = ( reg_ddrc_hwffc_en[0] && !i_hwffc_en_r[0]) ? 1 : 0;    // hwffc_en[0] 0 -> 1
assign hwffc_end        = (!reg_ddrc_hwffc_en[1] &&  i_hwffc_en_r[1]) ? 1 : 0;    // hwffc_en[1] 1 -> 0

assign hwffc_trg        = (!i_csysreq_ddrc_mux &&  csysreq_dl) ? i_csysmode_ddrc_r : 0;
assign hwffc_trg_avl    = hwffc_trg & (lpddr_dev | dh_gs_ddr4) & reg_ddrc_hwffc_en[0]
  // DDRCTL won't assert this signal hwffc_trg_avl if Burst PPT2 is ongoing.
  // If hwffc_trg_avl doesn't assert, HWFFC request from system will be denied. csysack_ddrc will go high with cactive_ddrc is high.
                          & ~ddrc_reg_ppt2_burst_busy
  // DDRCTL won't assert this signal hwffc_trg_avl if core VDD change is in progress.
  // If hwffc_trg_avl doesn't assert, HWFFC request from system will be denied. csysack_ddrc will go high with cactive_ddrc is high.
                          & ~ddrc_reg_ctrlupd_burst_busy
  ;
assign hwffc_trg_rej    = hwffc_trg & ~hwffc_trg_avl;
assign csysreq_rise     = (i_csysreq_ddrc_mux &&  !csysreq_dl) ? 1 : 0;

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_requested <= 1'b0;
  end else if (hwffc_trg) begin
    hwffc_requested <= 1'b1;
  end else if (csysreq_rise) begin
    hwffc_requested <= 1'b0;
  end 
end

// csysfrequency_ddrc input register
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_csysfrequency_ddrc_r <= 5'd0;
  end else begin
    i_csysfrequency_ddrc_r <= csysfrequency_ddrc;
  end 
end


// csysdiscamdrain_ddrc input register
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_csysdiscamdrain_ddrc_r <= 1'b0;
  end else begin
    i_csysdiscamdrain_ddrc_r <= csysdiscamdrain_ddrc;
  end 
end

// csysfsp_ddrc input register
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_csysfsp_ddrc_r        <= 1'd0;
  end else begin
    i_csysfsp_ddrc_r        <= csysfsp_ddrc;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_dfi_frequency <= 5'd0;
    i_dis_drain_cam     <= 1'b0;
    i_target_vrcg       <= 1'b0;
  end else if (hwffc_trg_avl) begin
    hwffc_dfi_frequency <= i_csysfrequency_ddrc_r;
    i_dis_drain_cam     <= i_csysdiscamdrain_ddrc_r;
    i_target_vrcg       <= reg_ddrc_target_vrcg;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_dfi_freq_fsp  <= 1'b1;
  end else if (hwffc_init) begin
    hwffc_dfi_freq_fsp  <= reg_ddrc_init_fsp;
  end else if ( reg_ddrc_hwffc_mode && hwffc_trg_avl) begin
    hwffc_dfi_freq_fsp  <= i_csysfsp_ddrc_r;
  end else if (~reg_ddrc_hwffc_mode && hwffc_mr_update_done & (hwffc_st_curr == HWFFC_ST_MR_UPDATE)) begin
    // just toggle if legacy HWFFC mode
    hwffc_dfi_freq_fsp  <= ~hwffc_dfi_freq_fsp;
  end 
end

//// HWFFC mode decoding ////
/* PHY Version 1.10a_d1 October 12, 2022
dfi_frequency     function
5'b00000          P0 Relock+Retrain
5'b00011          P3 Relock+Retrain
5'b00100          P0 Fast Relock+Retrain (Only valid for LPDDR5/5x)
5'b00111          P3 Fast Relock+Retrain (Only valid for LPDDR5/5x)
--------
5'b01000          RFU
5'b01011          RFU
5'b01100          Retrain only
5'b01101          LP2 Enter/Exit
5'b01110          RFU
5'b01111          RFU
--------
5'b10000          P0 Relock only
5'b10011          P3 Relock only
5'b10100          RFU
5'b10111          RFU
--------
5'b11000          RFU
5'b11110          RFU
5'b11111          Retentaion/LP3 Enter
*/
assign i_freq_cng_trg = hwffc_trg_avl & reg_ddrc_hwffc_mode & ~i_retrain_trg & ~i_lp2_trg & ~i_lp3_trg;
assign i_retrain_trg  = hwffc_trg_avl & reg_ddrc_hwffc_mode & (i_csysfrequency_ddrc_r      == 5'b01100);
assign i_lp2_trg      = hwffc_trg_avl & reg_ddrc_hwffc_mode & (i_csysfrequency_ddrc_r      == 5'b01101);
assign i_lp3_trg      = hwffc_trg_avl & reg_ddrc_hwffc_mode & (i_csysfrequency_ddrc_r      == 5'b11111);

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_freq_cng_flg  <= 1'b0;
  end else if (i_freq_cng_trg) begin
    i_freq_cng_flg  <= 1'b1;
  end else if ((hwffc_st_curr == HWFFC_ST_END) & (hwffc_st_nxt == HWFFC_ST_IDLE)) begin
    i_freq_cng_flg  <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_retrain_flg  <= 1'b0;
  end else if (i_retrain_trg) begin
    i_retrain_flg  <= 1'b1;
  end else if ((hwffc_st_curr == HWFFC_ST_END) & (hwffc_st_nxt == HWFFC_ST_IDLE)) begin
    i_retrain_flg  <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_lp2_flg  <= 1'b0;
  end else if (i_lp2_trg) begin
    i_lp2_flg  <= 1'b1;
  end else if ((hwffc_st_curr == HWFFC_ST_END) & (hwffc_st_nxt == HWFFC_ST_IDLE)) begin
    i_lp2_flg  <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    i_lp3_flg  <= 1'b0;
  end else if (i_lp3_trg) begin
    i_lp3_flg  <= 1'b1;
  end else if ((hwffc_st_curr == HWFFC_ST_END) & (hwffc_st_nxt == HWFFC_ST_IDLE)) begin
    i_lp3_flg  <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    dvfsq_switch  <= DVFSQ_HOLD;
  end else if ({reg_ddrc_dvfsq_enable,reg_ddrc_dvfsq_enable_next}==2'b01) begin   // disable->enbale == DVFSQ High to Low voltage
    dvfsq_switch  <= DVFSQ_HIGH2LOW;
  end else if ({reg_ddrc_dvfsq_enable,reg_ddrc_dvfsq_enable_next}==2'b10) begin   // enable->disable == DVFSQ Low to High voltage
    dvfsq_switch  <= DVFSQ_LOW2HIGH;
  end else if ((hwffc_st_curr == HWFFC_ST_END) & (hwffc_st_nxt == HWFFC_ST_IDLE)) begin
    dvfsq_switch  <= DVFSQ_HOLD;
  end 
end

assign freq_cng_pre      = i_freq_cng_trg | i_freq_cng_flg;

assign freq_cng_required = freq_cng_pre   | ~reg_ddrc_hwffc_mode;
assign retrain_required  = i_retrain_trg  | i_retrain_flg;
assign lp2_required      = i_lp2_trg      | i_lp2_flg;
assign lp3_required      = i_lp3_trg      | i_lp3_flg;

// Indicates lp2 enter or lp3 enter is going to be issued but background zq calibration stop (via MR28 write) is not required.
// If DRAM is LPDDR4 or reg_ddrc_skip_zq_stop_start is high, not required.
assign lp23_no_zqstop    = (lp2_required || lp3_required) && (~reg_ddrc_lpddr5 || reg_ddrc_skip_zq_stop_start);

assign mrwbuf_trg        = 1'b0;
assign no_mr1st_update   = reg_ddrc_hwffc_mode ? ((freq_cng_pre & dvfsq_switch==DVFSQ_HOLD & !mrwbuf_trg) | retrain_required | lp23_no_zqstop) : 1'b0;
assign no_mr2nd_update   = reg_ddrc_hwffc_mode ? ((freq_cng_pre                                         ) | retrain_required | lp23_no_zqstop) : 1'b0;
 
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_lp3_entered <= 1'b0;
  end else if (lp3_required & (hwffc_st_curr == HWFFC_ST_PHY_END_REQ) & dfi_init_complete_hwffc) begin
    hwffc_lp3_entered <= 1'b1;
  end 
end

assign hwffc_mask    = (hwffc_requested | hwffc_trg) & (~csysreq_rise);

// Qualifying HW LP request
wire i_csysreq_ddrc = i_csysreq_ddrc_mux | hwffc_mask;

// register csysreq_ddrc before using it
reg i_csysreq_ddrc_r;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_csysreq_ddrc_r_PROC
  if(!core_ddrc_rstn) begin
    i_csysreq_ddrc_r <= 1'b1;
  end else begin
    i_csysreq_ddrc_r <= i_csysreq_ddrc;
  end 
end

reg i_csysreq_ddrc_r2;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_csysreq_ddrc_r2_PROC
  if(!core_ddrc_rstn) begin
    i_csysreq_ddrc_r2 <= 1'b1;
  end else begin
    i_csysreq_ddrc_r2 <= i_csysreq_ddrc_r;
  end 
end


// falling edge detection on csysreq_ddrc
// denotes a request to move to Low Power
// Only perform HW entry if enabled via software
// Only perform HW entry if cactive_in_ddrc==0 && ih_busy==0
// i.e. cactive_in_ddrc=0 if no new core commands and
// ih_busy=0 if CAM is empty
wire i_hw_e_int = (!i_csysreq_ddrc &&  i_csysreq_ddrc_r) ? reg_ddrc_hw_lp_en : 0;

// Ensure i_hw_e is consistent with cactive_ddrc; don't let ddrc_reg_ppt2_burst_busy mask HWLP enter if HWFFC is ongoing
wire i_hw_e = (!i_cactive_in_ddrc_sync_or && (!ih_busy) & (~gs_phymstr_sre_req) & (hwffc_responding ? 1'b1 : ~ddrc_reg_ppt2_burst_busy) & (~ddrc_reg_ctrlupd_burst_busy)) ? i_hw_e_int : 0;

// rising edge detection on csysreq_ddrc
wire i_hw_x = ( i_csysreq_ddrc && (!i_csysreq_ddrc_r)) ? 1 : 0;
// Store a i_hw_e condtion as 1 if it was successfully accepted
// used to exit from attempting self refresh if reg_ddrc_selfref_sw=0  while trying to move to Self Refresh
reg i_hw_e_stored;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_hw_e_stored_PROC
  if(!core_ddrc_rstn) begin
    i_hw_e_stored <= 1'b0;
  end else begin
    if (i_hw_e) begin
      if (sr_st_nxt==SR_ST_SRE_HW_SW_STALL || sr_st_nxt==SR_ST_SR_HW_SW) begin 
        i_hw_e_stored <= 1'b1;
      end else begin
        i_hw_e_stored <= 1'b0;
      end
    end else if (sr_st_nxt==SR_ST_SRX || sr_st_nxt==SR_ST_NORM_PD || sr_st_nxt==SR_ST_SRE_ASR) begin
      i_hw_e_stored <= 1'b0;
    end
    
  end 
end

reg i_hw_x_stored;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_hw_x_stored_PROC
  if(!core_ddrc_rstn) begin
    i_hw_x_stored <= 1'b0;
  end else begin
    if (i_hw_x && sr_st_nxt==SR_ST_SR_HW_SW) begin 
      i_hw_x_stored <= 1'b1;
    end else if (sr_st_nxt==SR_ST_SRX) begin
      i_hw_x_stored <= 1'b0;
    end
    
  end 
end

// signal indicating that HW LP i/f is enabled
reg i_hw_e_to_x;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_hw_e_to_x_PROC
   if(!core_ddrc_rstn) begin
      i_hw_e_to_x <= 1'b0;
   end else begin
      if (i_hw_e) begin
         i_hw_e_to_x <= 1'b1;
      end else if(i_hw_x) begin
         i_hw_e_to_x <= 1'b0;
      end else begin
         i_hw_e_to_x <= i_hw_e_to_x;
      end
   end
end

wire i_sre_dly_cnt_zero;
reg [6:0] i_sre_dly_cnt;

// set counter when entering SR state for first time i.e. SR_ST_SR_ASR or SR_ST_SR_HW_SW
// does not set if moving SR_ST_SR_ASR -> SR_ST_SR_HW_SW
wire i_sre_dly_cnt_set = (((sr_st_nxt==SR_ST_SR_HW_SW) && ((sr_st_curr==SR_ST_SRE_ASR) || (sr_st_curr==SR_ST_SRE_HW_SW))) || 
        ((sr_st_nxt==SR_ST_SR_ASR) && sr_st_curr==SR_ST_SRE_ASR)) ? 1'b1 : 1'b0;

// counts reg_ddrc_dfi_t_ctrl_delay or reg_ddrc_dfi_tlp_resp + dfi_cmd_delay + 8 (8 is chosen as a safe margin for
// time for SRE to appear on DFI or dfi_lp_ctrl_req is deasserted when the PHY did not respond and few extra cycles for safety)
wire [$bits(reg_ddrc_dfi_tlp_resp)-1:0] i_sre_wait_val;
wire [$bits(i_sre_wait_val)+1:0] i_sre_dly_cnt_val; 

assign  i_sre_wait_val = (reg_ddrc_dfi_tlp_resp > reg_ddrc_dfi_t_ctrl_delay) ? reg_ddrc_dfi_tlp_resp : reg_ddrc_dfi_t_ctrl_delay;
assign i_sre_dly_cnt_val = ({{($bits(i_sre_dly_cnt_val)-$bits(i_sre_wait_val)){1'b0}}, i_sre_wait_val} + {{($bits(i_sre_dly_cnt_val)-$bits(dfi_cmd_delay)){1'b0}}, dfi_cmd_delay} + {{($bits(i_sre_dly_cnt_val)-4){1'b0}},4'b1000});

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_sre_dly_cnt_PROC
  if(!core_ddrc_rstn) begin
    i_sre_dly_cnt <= {$bits(i_sre_dly_cnt){1'b0}};
  end else begin   
    if (i_sre_dly_cnt_set) begin
      i_sre_dly_cnt <= {{($bits(i_sre_dly_cnt)-$bits(i_sre_dly_cnt_val)){1'b0}},i_sre_dly_cnt_val};
    end else if (!i_sre_dly_cnt_zero) begin
      i_sre_dly_cnt <= i_sre_dly_cnt - {{($bits(i_sre_dly_cnt)-1){1'b0}},1'b1};
    end
  end
end


assign i_sre_dly_cnt_zero = (i_sre_dly_cnt==0) ? 1 : 0;

wire i_sre_dly_flag = (!i_sre_dly_cnt_zero) || (i_sre_dly_cnt_set) ||
                                     (gsfsm_state_selfref_ent_dfilp);

// delay csysack_ddrc setting if in SR for a no. of cycles via i_sre_dly_cnt_zero/i_sre_dly_cnt_set
reg i_csysack_ddrc_int;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_csysack_ddrc_int_PROC
  if(!core_ddrc_rstn) begin
    i_csysack_ddrc_int <= 1'b1;
  end else begin   
    
    if (!((sr_st_nxt==SR_ST_SRE_HW_SW) || (i_hw_x && sr_st_nxt==SR_ST_SR_HW_SW) ||
          (i_hw_x_stored)              || (sr_st_nxt==SR_ST_SRX) ||
    i_sre_dly_flag ) ) begin
      i_csysack_ddrc_int <= i_csysreq_ddrc_r;     
    end
  end 
end

wire   i_csysack_ddrc;
reg i_csysack_ddrc_r;

// i_cactive_ddrc_hw_e_rej=1 when a HW LP entry is being rejected
// i_cactive_ddrc_hw_e_rej=0 one cycle after csysack_ddrc goes low
// This is cover issues of cactive_ddrc going low between
// csysreq_ddrc going low and csysack_ddrc going low, 
// even though HW LP entry was rejected
// e.g.
// Covers the issue of cactive_in_ddrc going low, with ih_busy=0, 
// in between csysreq_ddrc going low and csysack_ddrc going low
// cactive_ddrc low at time => results in clocks being removed even though HW LP request was
// rejected
// Another example covered by this would be i_cactive_ddrc_idle going low in between
// a rejected csysreq_ddrc going low and corresponding csysack_ddrc going
// low
reg i_cactive_ddrc_hw_e_rej;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_cactive_ddrc_hw_e_rej_PROC
  if(!core_ddrc_rstn) begin
    i_cactive_ddrc_hw_e_rej <= 1'b0;
  end else begin   
    if (i_hw_e_int && (!i_hw_e)) begin
      i_cactive_ddrc_hw_e_rej <= 1'b1;
    end else if (!i_csysack_ddrc && i_csysack_ddrc_r) begin
      i_cactive_ddrc_hw_e_rej <= 1'b0;
    end
  end
end


// Acknowledge is delayed version of request signal if hardware low power signals are not 
// enabled, otherwise they are defined by signal i_csysack_ddrc_int
assign i_csysack_ddrc = (reg_ddrc_hw_lp_en) ? i_csysack_ddrc_int : i_csysreq_ddrc_r2;

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_csysack_ddrc_r_PROC
  if(!core_ddrc_rstn) begin
    i_csysack_ddrc_r <= 1'b1;
  end else begin
    i_csysack_ddrc_r <= i_csysack_ddrc & hwffc_csysack_ddrc;    
  end 
end

// drive output from register
assign csysack_ddrc = i_csysack_ddrc_r;

// SW entry is level sensitive
wire i_sw_e = reg_ddrc_selfref_sw
              & (~hwffc_srx_req)
              & (~(hwffc_sr_req & i_dis_drain_cam)) // HWFFC without CAM draining
              | (hwffc_sr_req & ~i_dis_drain_cam)   // HWFFC with CAM draining
              ;
              
// SW entry masked by PHY Master request
// - masking not added to i_sw_e directly becasue transition from SR_HW_SW to SRX should happen only
// if SW selfref is dropped; by masking it SR_HW_SW -> SRX transition happens unexpectedly
wire i_sw_e_phymstr_mask = i_sw_e & (~gs_phymstr_sre_req);

wire  i_sw_e_ih_idle = ~ih_busy & i_sw_e_phymstr_mask;


// SR entry due to PHY Master reqeust
wire i_phymstr_e = gs_phymstr_sre_req 
                   ;

//
// Auto Self Refresh/Auto cactive related timers
//


wire i_asr_idle_states = ((sr_st_nxt == SR_ST_NORM_PD) || 
                          (sr_st_nxt == SR_ST_SRE_ASR) ||
                          (sr_st_nxt == SR_ST_SR_ASR) ) ? 1 : 0;
      
// auto cactive counter only in NORM_PD or SRE_ASR or SR_ST_SR_ASR, same as i_asr_idle_states
wire i_cactive_ddrc_idle_states = i_asr_idle_states;

wire i_cactive_ddrc_idle_cnt_val_load = ((!i_cactive_ddrc_idle_states) || (!gsfsm_idle)) ? 1 : 0;

                                 
reg [11:0] i_cactive_ddrc_idle_cnt;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_cactive_ddrc_idle_cnt_PROC
  if(!core_ddrc_rstn) begin
     i_cactive_ddrc_idle_cnt <= 12'hFFF;
  end else begin
    if (i_cactive_ddrc_idle_cnt_val_load) begin
      i_cactive_ddrc_idle_cnt <= reg_ddrc_hw_lp_idle_x32;
    end else if (i_cactive_ddrc_idle_cnt>0) begin
      if (timer_pulse_x32_dram) begin
        i_cactive_ddrc_idle_cnt <= i_cactive_ddrc_idle_cnt - 1;
      end
    end        
  end 
end


// disable i_cactive_ddrc_idle if reg_ddrc_hw_lp_idle_x32 is all zeroes
// or if reg_ddrc_hw_lp_en=0
wire i_cactive_ddrc_idle_en =(reg_ddrc_hw_lp_idle_x32!=0) ? reg_ddrc_hw_lp_en : 0;

// only set if i_cactive_ddrc_idle_cnt==0
wire i_cactive_ddrc_idle_cnt_zero = (i_cactive_ddrc_idle_cnt==0) ? 1 : 0;

// AND of both conditions => set i_cactive_ddrc_idle=0
// Otherwise              => set i_cactive_ddrc_idle=i_cactive_ddrc_idle_en
// as i_cactive_ddrc_idle=1 if reg_ddrc_hw_lp_idle_x32==0
wire i_cactive_ddrc_idle = (i_cactive_ddrc_idle_en && i_cactive_ddrc_idle_cnt_zero) ? 0 : 1;


// exit from following immediately if any bit cactive_in_ddrc goes high
// and this feature has been enabled in SW - hw_lp_exit_idle_en (hw_lp_en=1 needs to be set too), or if HWFFC starts progress:
// - Auto Self Refresh
// - Power Down
// - Clock Stop
wire i_hw_lp_sr_pd_cs_exit = (i_cactive_in_ddrc_sync_or & reg_ddrc_hw_lp_exit_idle_en & reg_ddrc_hw_lp_en)
                          || (reg_ddrc_hwffc_mode && hwffc_in_progress)
                             ;

// reset counter if:
// - not in NORM_PD or SRE_ASR or SR_ASR &&
// - not idle &&
// - Any bit of cactive_in_ddrc is high and logic for ASR exit is enabled
wire i_asr_idle_cnt_val_load = ((!i_asr_idle_states) || (!gsfsm_idle) || i_hw_lp_sr_pd_cs_exit) ? 1 : 0;

reg [$bits(reg_ddrc_selfref_to_x32)-1:0] i_asr_idle_cnt;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_asr_idle_cnt_PROC
  if(!core_ddrc_rstn) begin
     i_asr_idle_cnt <= {$bits(i_asr_idle_cnt){1'b1}};
  end else begin
    if (i_asr_idle_cnt_val_load) begin     
      i_asr_idle_cnt <= reg_ddrc_selfref_to_x32;
    end else if (i_asr_idle_cnt>{$bits(i_asr_idle_cnt){1'b0}}) begin
      if (timer_pulse_x32_dram) begin
        i_asr_idle_cnt <= i_asr_idle_cnt - {{($bits(i_asr_idle_cnt)-1){1'b0}},1'b1};
      end
    end        
  end 
end

// Auto Self Refresh is enabled counter has reached all zeroes and 
// counter is not being loaded i.e. gsfsm_idle && !i_hw_lp_sr_pd_cs_exit
wire i_asr_en_idle = ((i_asr_idle_cnt=={$bits(i_asr_idle_cnt){1'b0}}) && gsfsm_idle && (!i_hw_lp_sr_pd_cs_exit)) ? 1 : 0;
   
// Auto Self Refresh is attempted if:
// - timer has expire - i_asr_en_idle
// - enabled via SW - dh_gs_selfref_en 
// - MR request from gs_load_mr - ~load_mr_norm_required_1bit
wire i_asr_en_tmp = i_asr_en_idle & dh_gs_selfref_en & (~load_mr_norm_required_1bit) & (~hwffc_srx_req) & (~hwffc_st_wait) & (i_dis_drain_cam | ~hwffc_sr_req | ~lpddr_dev);


wire i_asr_en = i_asr_en_tmp | (hwffc_sr_req & i_dis_drain_cam);

// drive output to gsfsm to exit PD/CS
assign gsfsm_sr_hw_lp_pd_cs_exit = i_hw_lp_sr_pd_cs_exit;

//
// Signals for State M/C transitions
//

// Added MEMC_GS_ST_SELFREF_ENT2 to i_ns_sr as SRE is guaranteed after this
// state occurs
// same for MEMC_GS_ST_SELFREF/MEMC_GS_ST_SELFREF_ENT_DFILP
// makes two state m/cs keeping in sync easier
wire i_ns_sr = (gsfsm_next_state==GS_ST_SELFREF) || (gsfsm_next_state==GS_ST_SELFREF_ENT_DFILP) ? 1 : 0;

//spyglass disable_block W528
//SMD: Variable set but not read
//SJ: Used under different `ifdefs. Decided to keep the current coding style for now.
wire i_ns_sr_ent2 = ((gsfsm_next_state==GS_ST_SELFREF_ENT2) && (lpddr_dev || dh_gs_ddr4)) ? 1 : 0;
wire i_ns_sr_ex1  = ((gsfsm_next_state==GS_ST_SELFREF_EX1)  && (lpddr_dev || dh_gs_ddr4)) ? 1 : 0;
//spyglass enable_block W528

wire i_ns_norm = (gsfsm_next_state==GS_ST_NORMAL_RD || gsfsm_next_state==GS_ST_NORMAL_WR) ? 1 : 0;

wire i_ns_rst_init = (gsfsm_next_state==GS_ST_RESET || gsfsm_next_state==GS_ST_INIT_DDR) ? 1 : 0;



assign i_ns_srpd = (gsfsm_next_state==GS_ST_SELFREF) ||
                   (gsfsm_next_state==GS_ST_SELFREF_ENT_DFILP) ||
                   (gsfsm_next_state==GS_ST_SELFREF_EX_DFILP) ? 1 : 0;

wire i_ns_dsm    = (gsfsm_next_state==GS_ST_DSM) ||
                   (gsfsm_next_state==GS_ST_DSM_ENT_DFILP) ||
                   (gsfsm_next_state==GS_ST_DSM_EX_DFILP) ? 1 : 0;

// conditions for SR_ST_SRE_ASR -> SR_ST_SR_ASR transition
// 1. LPDDR4
//    - ASR case             : when global-fsm is in in SR-PD state
//    - normal_ppt2_prepre case and
//    - dfi_phymstr_req case : when global-fsm is in SR without PD state
// 2. non-LPDDR4             : when global-fsm is in in SR state
wire asr_sre_to_sr = 
                     (lpddr_dev & i_phymstr_e) ?    (i_ns_sr_ent2 | i_ns_sr_ex1) : // LPDDR4 dfi_phymstr_req
                     (ppt2_asr_to_sre_asr) ?        1'b0 :  // preserve the SRE state as an SR without PD state while PPT2 is ongoing
                                                    i_ns_sr; // LPDDR4 ASR, no dfi_phymstr_req, or non-LPDDR4

// conditions for SR_ST_SRE_HW_SW -> SR_ST_SR_HW_SW transition
wire hsr_sre_to_sr = 
  (gsfsm_srpd_to_sr && reg_ddrc_hwffc_mode && hwffc_in_progress) ?  1'b0 :   // preserve HSR Enter state during new HWFFC
                                                                    i_ns_sr; // LPDDR4 ASR, no dfi_phymstr_req, or non-LPDDR4
// Assert while ASR(SRPD) -> HSR(SR) transition is occurring
//assign hwffc_asr_to_sre_hsr = (reg_ddrc_hwffc_mode && hwffc_in_progress) && gsfsm_srpd_to_sr && (hwffc_st_curr==HWFFC_ST_WAIT || hwffc_st_curr==HWFFC_ST_SRE);
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_hwffc_asr_to_sre_hsr
  if(!core_ddrc_rstn) begin
    hwffc_asr_to_sre_hsr <= 1'b0;
  end else if(!reg_ddrc_hwffc_mode) begin
    // ASR(SRPD) -> HSR(ASR) doesn't occur unless hwffc_mode==1
    hwffc_asr_to_sre_hsr <= 1'b0;
  end else if(sr_st_curr==SR_ST_SR_ASR && sr_st_nxt==SR_ST_SRE_HW_SW_STALL) begin
    hwffc_asr_to_sre_hsr <= 1'b1;
  end else if (!gsfsm_srpd_to_sr) begin
    hwffc_asr_to_sre_hsr <= 1'b0;
  end
end

// register i_phymstr_e
reg i_phymstr_e_r;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_phymstr_e_r_PROC
  if(!core_ddrc_rstn) begin
    i_phymstr_e_r <= 1'b0;
  end else begin
    i_phymstr_e_r <= i_phymstr_e;
  end
end

// falling edge on i_phymstr_e
wire i_phymstr_e_fed = ~i_phymstr_e & i_phymstr_e_r;

// CAM draining can be skipped if it is allowed via SW and we don't have HW SR
wire skip_dram_draining = dh_gs_dis_cam_drain_selfref & !i_hw_e & !i_hw_e_to_x;

// Transition from SR-PD to SR and back to SR-PD if allowed
wire srpd_to_sr_allowed = dh_gs_lpddr4_sr_allowed & !i_hw_e & !i_hw_e_to_x & (!ih_busy | (ih_busy & dh_gs_dis_cam_drain_selfref));
wire srpd_to_sr_allowed_hwffc = dh_gs_lpddr4_sr_allowed & (!ih_busy | (ih_busy & dh_gs_dis_cam_drain_selfref));

// if we are in SR_ST_SRE_HW_SW state (i.e. waiting for SR-PD) and there is a PHY Master request, we will first handle the request (in SR);
// after the request is handled we need to return to SR_ST_SRE_HW_SW state (to enter SR-PD without going to IDLE state first)
reg return_sre_after_phymstr;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: return_sre_after_phymstr_PROC
   if(!core_ddrc_rstn) begin
      return_sre_after_phymstr <= 1'b0;
   end else if (sr_st_curr==SR_ST_SRE_HW_SW && sr_st_nxt==SR_ST_SRE_ASR) begin
      return_sre_after_phymstr <= 1'b1;
   end else if (sr_st_nxt==SR_ST_SRE_HW_SW || sr_st_nxt==SR_ST_SRX) begin
      return_sre_after_phymstr <= 1'b0;
   end else begin
      return_sre_after_phymstr <= return_sre_after_phymstr;
   end
end

// SR_ST_SR_HW_SR -> SR_ST_SRX when
// - HW exit and no new HW entry
// - SW entry is dropped
// - no phymstr_req (only non-LPDDR4 case)
wire sr_hw_sw_to_srx = (i_hw_x || i_hw_x_stored || (!i_hw_e_stored)) && (!i_sw_e)
                        && (lpddr_dev ? 1'b1 : (!i_phymstr_e))
                        && (!hwffc_sr_req)
                        ;

//
// State M/C
//
   // FSM sequential
   always @(posedge co_yy_clk or negedge core_ddrc_rstn)
   begin: sr_st_seq_PROC
      if( !core_ddrc_rstn ) begin
        sr_st_curr <= SR_ST_RST_INIT;
      end else begin
        sr_st_curr <= sr_st_nxt;
      end
   end

   // FSM combinatorial
   always @(*)
   begin: sr_st_comb_PROC


      case(sr_st_curr)
        
        SR_ST_RST_INIT: begin
          if (!i_ns_rst_init) begin
            if (startup_in_self_ref)
              sr_st_nxt = SR_ST_SR_HW_SW;
            else
              sr_st_nxt = SR_ST_NORM_PD;
          end else begin
            sr_st_nxt = SR_ST_RST_INIT;
          end
        end

        SR_ST_NORM_PD: begin   
          if (i_ns_dsm) begin
            sr_st_nxt = SR_ST_DSM;
          end else
          if (i_sw_e_phymstr_mask && (!i_hw_e) && dh_gs_dis_cam_drain_selfref) begin
            //ccx_fsm:;sr_st_curr;SR_ST_NORM_PD->SR_ST_SRE_HW_SW;This item can be ignored. This line is used only when PWRCTL.dis_cam_drain_selfref=1, which is not supported.
            //ccx_line: ; This line can be ignored because it is used only when PWRCTL.dis_cam_drain_selfref=1, which is not supported.
            sr_st_nxt = SR_ST_SRE_HW_SW;
          end else if (i_hw_e || i_sw_e_phymstr_mask) begin
            sr_st_nxt = SR_ST_SRE_HW_SW_STALL;
          end else if (i_asr_en || i_phymstr_e) begin
            sr_st_nxt = SR_ST_SRE_ASR;      
          end else begin 
            sr_st_nxt = SR_ST_NORM_PD;
          end
        end

        SR_ST_SRE_HW_SW_STALL: begin
          if (!ih_busy) begin
            sr_st_nxt = SR_ST_SRE_HW_SW;
          end else if (i_dis_drain_cam & hwffc_sr_req) begin
            sr_st_nxt = SR_ST_SRE_ASR;
          end else begin
            sr_st_nxt = SR_ST_SRE_HW_SW_STALL;
          end
        end


        SR_ST_SRE_HW_SW: begin
          if (lpddr_dev && i_phymstr_e) begin
            sr_st_nxt = SR_ST_SRE_ASR; 
          end else
          if (hsr_sre_to_sr) begin
            sr_st_nxt = SR_ST_SR_HW_SW; 
          end else if (gsfsm_sr_no_pd_to_srx && sr_hw_sw_to_srx) begin
            sr_st_nxt = SR_ST_SRX; 
          end else begin
            sr_st_nxt = SR_ST_SRE_HW_SW;
           end
        end

        SR_ST_SRE_ASR: begin
          if (i_hw_e || i_sw_e_ih_idle) begin
            sr_st_nxt = SR_ST_SRE_HW_SW_STALL;
          end else if (asr_sre_to_sr) begin            
            sr_st_nxt = SR_ST_SR_ASR;
          end else if (i_ns_sr_ent2) begin
            sr_st_nxt = SR_ST_SRE_ASR;
          end else if (!i_asr_en && !gs_phymstr_sre_req && !ppt2_asr_to_sre_asr) begin
            sr_st_nxt = SR_ST_NORM_PD;      
          end else begin
            sr_st_nxt = SR_ST_SRE_ASR;
          end
        end
  
        SR_ST_SR_HW_SW: begin
          if (lpddr_dev && i_phymstr_e && srpd_to_sr_allowed) begin
            sr_st_nxt = SR_ST_SRE_ASR;
          end else
          if (sr_hw_sw_to_srx) begin
            sr_st_nxt = SR_ST_SRX; 
          end else begin
            sr_st_nxt = SR_ST_SR_HW_SW;
           end
        end

        SR_ST_SR_ASR: begin  
          if (lpddr_dev && reg_ddrc_hwffc_mode && hwffc_in_progress && i_ns_sr && srpd_to_sr_allowed_hwffc && gsfsm_idle) begin
            if(gsfsm_next_state==GS_ST_SELFREF
                // ASR(SRPD)->HSR(SR) must occur only if there is no transaction.
                // Wait for XPI_ST_DISABLED ensures HWFFC logic requested XPI ports stop and XPI acknowledged. Then no any XPI port will receive new data.
                // If XPI is idle but hif already received a data, srpd_to_sr_allowed_hwffc and gsfsm_idle goes to 0 so FSM can escape from the wait loop - avoids deadlock.
                && xpi_st_nxt == XPI_ST_DISABLED
            ) begin
              sr_st_nxt = SR_ST_SRE_HW_SW_STALL;  // new HWFFC only transition: ASR(SRPD) -> HSRE(SR)
            end else begin
              sr_st_nxt = SR_ST_SR_ASR;
            end
          end else
          if (lpddr_dev && i_sw_e_phymstr_mask && (!i_phymstr_e) && 
               // after finishing PHY Master request handling go directly to SW SR Entry in following cases:
               // - SRPD -> SR transition allowed and was performed - go back to SRPD
               // - we were in SR and were waiting for SRPD when PHY Master request was asserted - go back to that state
               // - CAMs are not expected to be drained upon SW SR Entry
              (srpd_to_sr_allowed || return_sre_after_phymstr || skip_dram_draining)) begin
            sr_st_nxt = SR_ST_SRE_HW_SW;
          // if SDRAM is in SR-PD state due to ASR and a phymstr_req is issued, transition to SR_ST_SRE_ASR and wait for SR entry
          end else if (lpddr_dev && i_phymstr_e && i_ns_sr) begin
            sr_st_nxt = SR_ST_SRE_ASR;
          end else
          // if SDRAM is in SR-PD state (which can be exited immediatedly) due to ASR and a ctrlupd_req(PPT2) is scheduled, transition to SR_ST_SRE_ASR and wait for SR entry
          if (lpddr_dev && normal_ppt2_prepare && i_ns_sr ) begin
            if(gsfsm_next_state==GS_ST_SELFREF) begin
              sr_st_nxt = SR_ST_SRE_ASR;
            end else begin
              sr_st_nxt = SR_ST_SR_ASR;
            end
          end else
          if ((i_hw_e || i_sw_e_ih_idle) && (!i_phymstr_e_fed)) begin
            sr_st_nxt = SR_ST_SR_HW_SW;
          end else if (i_phymstr_e_fed || (!i_asr_en && !i_phymstr_e)) begin
            sr_st_nxt = SR_ST_SRX;
          end else begin
            sr_st_nxt = SR_ST_SR_ASR;
           end
        end

        SR_ST_DSM: begin
          if (i_ns_dsm) begin
            sr_st_nxt = SR_ST_DSM;
          end else begin
            sr_st_nxt = SR_ST_SR_HW_SW;
          end
        end


        default: begin // SR_ST_SRX
          if (i_phymstr_e & (i_ns_sr_ent2 | i_ns_sr_ex1)) begin
            sr_st_nxt = SR_ST_SRE_ASR;
          end else
          if (i_ns_norm) begin
            sr_st_nxt = SR_ST_NORM_PD;      
          end else begin
            sr_st_nxt = SR_ST_SRX;
           end
        end
      
      endcase // case(sr_st_curr)
   end
        
// 
// Outputs of block based on state
// 

assign gsfsm_sr_entry_req = (sr_st_curr==SR_ST_SRE_ASR || sr_st_curr==SR_ST_SRE_HW_SW) ? 1 : 0;
assign gsfsm_sr_exit_req  = (sr_st_curr==SR_ST_SRX) ? 1 : 0;
assign gsfsm_asr_to_sre_asr = sr_st_curr==SR_ST_SR_ASR && sr_st_nxt==SR_ST_SRE_ASR;

// note use of sr_st_nxt, not sr_st_curr
// as output is later generated from register
wire [SELFREF_TYPE_WIDTH_INT-1:0] i_ddrc_reg_selfref_type_nxt;       
assign i_ddrc_reg_selfref_type_nxt =
       // for LPDDR4 phymstr_req case selfref_type={{($bits(i_ddrc_reg_selfref_type_nxt)-1){1'b0}},1'b1} is not blocked by err_window/i_sre_dly_flag
       (lpddr_dev & sr_st_nxt==SR_ST_SR_ASR & i_phymstr_e) ? {{($bits(i_ddrc_reg_selfref_type_nxt)-1){1'b0}},1'b1} :
       (lpddr_dev & sr_st_nxt==SR_ST_DSM)                  ? {{($bits(i_ddrc_reg_selfref_type_nxt)-2){1'b0}},2'b10} :
       (sr_st_nxt==SR_ST_SRE_ASR & normal_ppt2_prepare)    ? {{($bits(i_ddrc_reg_selfref_type_nxt)-2){1'b0}},2'b01} :
       // SR_ST_SR_ASR means SR due to:
       // - PHY Master request - if i_phymstr_e
       // - auto self-refreshes
       (sr_st_nxt==SR_ST_SR_ASR)   ? ((i_sre_dly_flag) ? {$bits(i_ddrc_reg_selfref_type_nxt){1'b0}} : 
                                      ((i_phymstr_e) ? {{($bits(i_ddrc_reg_selfref_type_nxt)-1){1'b0}},1'b1} : {{($bits(i_ddrc_reg_selfref_type_nxt)-2){1'b0}},2'b11})) : 
       // SR_ST_SR_HW_SW means SR due to:
       // - SW/HW SR entry request - typically
       // - PHY Master request - only non-LPDDR4, when PHY Master comes while already in SR due to SW/HW SR request
       (sr_st_nxt==SR_ST_SR_HW_SW) ? ((i_sre_dly_flag) ? {$bits(i_ddrc_reg_selfref_type_nxt){1'b0}} : 
                                      ((
                                          ~lpddr_dev &
                                          i_phymstr_e) ?  {{($bits(i_ddrc_reg_selfref_type_nxt)-1){1'b0}},1'b1} : {{($bits(i_ddrc_reg_selfref_type_nxt)-2){1'b0}},2'b10})) : 
       {$bits(i_ddrc_reg_selfref_type_nxt){1'b0}};


reg [1:0] i_ddrc_reg_selfref_type_nxt_r;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_ddrc_reg_selfref_type_nxt_r_PROC
  if(!core_ddrc_rstn) begin
    i_ddrc_reg_selfref_type_nxt_r <= {$bits(i_ddrc_reg_selfref_type_nxt_r){1'b0}};
  end else begin
    i_ddrc_reg_selfref_type_nxt_r <= i_ddrc_reg_selfref_type_nxt;
  end
end

// drive output from register
assign ddrc_reg_selfref_type = i_ddrc_reg_selfref_type_nxt_r;

wire sr_st_nxt_hw_sw = (sr_st_nxt==SR_ST_SRE_HW_SW_STALL) || (sr_st_nxt==SR_ST_SRE_HW_SW) || (sr_st_nxt==SR_ST_SR_HW_SW);
wire sr_st_nxt_dsm   = (sr_st_nxt==SR_ST_DSM);

assign gsfsm_sr_co_if_stall = (
                                 // if SR HW LP
                                 (sr_st_nxt_hw_sw && !i_sw_e)
                                 // if DSM
                                 || (sr_st_nxt_dsm)
                                 // if selfref_sw=1 and PHY Master request is not active (use i_sw_e_phymstr_mask instead of i_sw_e, because SW entry 
                                 // requests are masked by phymstr_req)
                                 || (i_sw_e_phymstr_mask && (!dh_gs_dis_cam_drain_selfref))
                                 // if SR SW and CAMs must be empty or CAM draining can be skipped but there is no data in CAMs (keep CAMs empty 
                                 // in this situation for correct selfref_cam_not_empty generation in gs_global_fsm.v)
                                 || (sr_st_nxt_hw_sw && (!dh_gs_dis_cam_drain_selfref || (dh_gs_dis_cam_drain_selfref && !ih_busy)))
                                 // PHY Master and there is no data in CAMs (keep CAMs empty in this situation for correct selfref_cam_not_empty 
                                 // generation in gs_global_fsm.v)
                                 || (((sr_st_nxt==SR_ST_SRE_ASR) || (sr_st_nxt==SR_ST_SR_ASR)) && i_phymstr_e && !ih_busy)
                                 || hwffc_add_hif_stall
                              ) ? 1'b1 : 1'b0;
                              
wire i_cactive_ddrc_sr_int  = (sr_st_nxt==SR_ST_SR_HW_SW)  ? 0 : 1;

// drive cactive_ddrc low in Self Refresh only if HW LP I/F is enabled
wire i_cactive_ddrc_sr = (reg_ddrc_hw_lp_en) ? i_cactive_ddrc_sr_int : 1;

// cactive_ddrc due to Self Refresh and due to Idle are both 1
// cactive_ddrc_int_x=1, 
// otherwise,
// cactive_ddrc_int_x=0
// Hence use of AND
wire i_cactive_ddrc_int_x = i_cactive_ddrc_sr & i_cactive_ddrc_idle;

// cactive_ddrc forced high if HW LP entry request is in flight that 
// is being rejected 
wire i_cactive_ddrc_int_y = i_cactive_ddrc_hw_e_rej;

// OR the X and Y cases
wire i_cactive_ddrc_int_x_or_y = i_cactive_ddrc_int_x | i_cactive_ddrc_int_y;

// if there's a command in CAM (ih_busy=1)
// then cactive_ddrc should be 1
wire i_cactive_ddrc_int = i_cactive_ddrc_int_x_or_y | ih_busy;

// register output
reg i_cactive_ddrc_int_r;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_cactive_ddrc_int_r_PROC
  if(!core_ddrc_rstn) begin
    i_cactive_ddrc_int_r <= 1'b1;
  end else begin
    i_cactive_ddrc_int_r <= i_cactive_ddrc_int;
  end
end

// ASYNC OR of cactive_in_ddrc port
wire i_cactive_in_ddrc_async_or = |cactive_in_ddrc_async;

// async AND of phy_dfi_phyupd_req input and SW bit
wire i_phy_dfi_phyupd_req_and_en = phy_dfi_phyupd_req & reg_ddrc_dfi_phyupd_en;

// register i_phy_dfi_phyupd_req_and_en
reg i_phy_dfi_phyupd_req_and_en_r;
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: i_phy_dfi_phyupd_req_and_en_r_PROC
  if(!core_ddrc_rstn) begin
    i_phy_dfi_phyupd_req_and_en_r <= 1'b1;
  end else begin
    i_phy_dfi_phyupd_req_and_en_r <= i_phy_dfi_phyupd_req_and_en;
  end
end

// ASYNC AND of phy_dfi_phymstr_req input and SW bit
wire i_phy_dfi_phymstr_req_and_en = phy_dfi_phymstr_req & reg_ddrc_dfi_phymstr_en;

// note asynchronous path for cactive_in_ddrc 
// note asynchronous path for hif_cmd_valid
// Means cactive_ddrc stays high, even if in Self Refresh or idle counter expired, 
// if cactive_in_ddrc goes high or if new core command (hif_cmd_valid)
// hif_cmd_valid is used in ih_busy already, so registered signal i_cactive_ddrc_int
// already uses hif_cmd_valid
// note asynchronous path related to phy_dfi_phyupd_req (as long as reg_ddrc_dfi_phyupd_en==1 as well)
// also, registered path for phy_dfi_phyupd_req/reg_ddrc_dfi_phyupd_en due to
// timing required to detect dfi_phyupd_req going low in gs_phyupd state m/c
assign cactive_ddrc = 
                      hwffc_responding ? hwffc_cactive_ddrc :
                      ddrc_reg_ppt2_burst_busy |
                      ddrc_reg_ctrlupd_burst_busy |
                      i_cactive_ddrc_int_r | i_cactive_in_ddrc_async_or | hif_cmd_valid | i_phy_dfi_phyupd_req_and_en | i_phy_dfi_phyupd_req_and_en_r | i_phy_dfi_phymstr_req_and_en;

// inform gsfsm that it can start SRE without waiting for the CAMs to be empty
// - when DFI PHY MSTR request
// - when SW entry and dis_cam_drain_selfref==1
assign gsfsm_sr_dis_dq = ((sr_st_nxt==SR_ST_SRE_ASR   && i_phymstr_e) || 
                          (sr_st_nxt==SR_ST_SRE_ASR   && hwffc_sr_req) || 
                          (sr_st_nxt==SR_ST_SRE_HW_SW && skip_dram_draining)) ? 1'b1 : 1'b0;

// indication of SR_ST_SRE_HW_SW_STALL state    
assign gs_bs_sre_stall = (sr_st_curr == SR_ST_SRE_HW_SW_STALL) ? 1'b1 : 1'b0;

// indication of SR_ST_SRE_HW_SW state
assign gs_bs_sre_hw_sw = (sr_st_curr == SR_ST_SRE_HW_SW) ? 1'b1 : 1'b0;

// allow transition from SR-PD to SR
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: gsfsm_srpd_to_sr_PROC
  if (!core_ddrc_rstn) begin
    gsfsm_srpd_to_sr <= 1'b0;
  end else if (i_ns_sr && sr_st_nxt==SR_ST_SRE_ASR) begin
    gsfsm_srpd_to_sr <= 1'b1;
  end else if ((reg_ddrc_hwffc_mode && hwffc_in_progress) && i_ns_sr && sr_st_nxt==SR_ST_SRE_HW_SW_STALL) begin
    gsfsm_srpd_to_sr <= 1'b1;
  end else if (
      gsfsm_srpd_to_sr==1 && (
           sr_st_nxt==SR_ST_SRX
        || sr_st_nxt==SR_ST_SR_HW_SW
        || i_ns_norm                            // Once entered to Normal, srpd_to_sr can be de-asserted even if not passed through SR_ST_SRX
        || gsfsm_next_state==GS_ST_SELFREF_ENT2 // PDX should have been sent once re-enter to ENT2 is done. 'srpd_to_sr' should also be done.
        )
    ) begin
    gsfsm_srpd_to_sr <= 1'b0;
  end else begin
    gsfsm_srpd_to_sr <= gsfsm_srpd_to_sr;
  end
end

// allow transition from SR directly to Normal Operating mode
// gsfsm_sr_no_pd_to_srx Lo -> Hi triggers sr_st goes to SRX and t_xs starts counting
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin: gsfsm_sr_no_pd_to_srx_PROC
   if (!core_ddrc_rstn) begin
      gsfsm_sr_no_pd_to_srx <= 1'b0;
   end else if (lpddr_dev & i_phymstr_e_fed & (sr_st_nxt==SR_ST_SRX)) begin
      gsfsm_sr_no_pd_to_srx <= 1'b1;
   end else if (lpddr_dev & reg_ddrc_hwffc_mode & (hwffc_st_curr==HWFFC_ST_END && hwffc_st_nxt==HWFFC_ST_IDLE)) begin
      // new HWFFC only transition: HSR Enter(SR w/o PD) -> HSR Exit(SRX)
      gsfsm_sr_no_pd_to_srx <= 1'b1;
   end else if (i_ns_norm || (sr_st_nxt==SR_ST_SRE_ASR)) begin
      gsfsm_sr_no_pd_to_srx <= 1'b0;
   end
end



//--------------------------- HWFFC -------------------------------
//
// HSFFC State M/C
//
   // HWFFC FSM sequential 
   always @(posedge co_yy_clk or negedge core_ddrc_rstn)
   begin: hwffc_st_seq_PROC
      if( !core_ddrc_rstn )
        hwffc_st_curr <= HWFFC_ST_IDLE;
      else begin
        hwffc_st_curr <= hwffc_st_nxt;
      end
   end
   assign hwffc_st_nxt =                           hwffc_st_nxt_wlp;

   // HWFFC FSM combinatorial 
   always_comb
   begin: hwffc_st_comb_LPDDR4_PROC
      case(hwffc_st_curr)
   
           HWFFC_ST_IDLE : begin
             if (
                xpi_disabled
             ) begin
               if(reg_ddrc_hwffc_mode) begin
                 // LPDDR54 HWFFC with dfi_fsp toggle
                 hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
               end else if (i_ns_sr_ent2) begin
                 if (i_csysdiscamdrain_ddrc_r==1 && ih_busy==0 && reg_ddrc_selfref_sw=={$bits(reg_ddrc_selfref_sw){1'b0}} &&
                     phymstr_active==0 && i_phy_dfi_phymstr_req_and_en==0 && gsfsm_sr_no_pd_to_srx==0) begin
                   hwffc_st_nxt_wlp = HWFFC_ST_MR_UPDATE;
                 end else begin
                   hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
                 end
               end else if (i_ns_srpd) begin
                 hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
               end else if (i_ns_sr_ex1) begin
                 hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
               end else begin 
                 hwffc_st_nxt_wlp = HWFFC_ST_SRE;
               end
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_IDLE;
             end
           end
   
           HWFFC_ST_WAIT : begin
             if (i_phy_dfi_phymstr_req_and_en | gs_phymstr_sre_req) begin
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
             end else if (reg_ddrc_hwffc_mode && !dqsosc_stopped) begin
               // in non-legacy mode, wait until dqsosc is idle
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
             end else if (sr_st_nxt == SR_ST_NORM_PD) begin
               hwffc_st_nxt_wlp = HWFFC_ST_SRE;
             end else if (hwffc_asr_to_sre_hsr && i_ns_sr_ent2 && sr_st_curr==SR_ST_SRE_HW_SW) begin // When HWFFC follows ASR exit without existing from SR state
               // If HWFFC follows ASR exit, PHYMSTR can interrupt between ASR exit and HWFFC start.
               // Once PHYMSTR handshaking starts, HWFFC state should stay here. Otherwise global_fsm state goes to non-HWFFC-ready state but this state says 'GO' to start HWFFC
               // Here additionally ensuring sr_st_curr is in HWFFC-ready state i.e. SR_ST_SRE_HW_SW before starting HWFFC.
               hwffc_st_nxt_wlp = HWFFC_ST_SRE;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
             end
           end
   
           HWFFC_ST_SRE : begin
             if (i_phy_dfi_phymstr_req_and_en | gs_phymstr_sre_req) begin
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT;
             end else if (~i_dis_drain_cam & ih_busy) begin
               hwffc_st_nxt_wlp = HWFFC_ST_SRE;
             end else if (reg_ddrc_hwffc_mode && (hwffc_bgzq_stopped_propagate!=2'h0 || !hwffc_bgzq_stopped)) begin
               // wait until automatic ZQ calibration is halted
               hwffc_st_nxt_wlp = HWFFC_ST_SRE;
             end else if (i_ns_sr_ent2) begin
               hwffc_st_nxt_wlp = HWFFC_ST_MR_UPDATE;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_SRE;
             end
           end
   
           HWFFC_ST_MR_UPDATE : begin
             if (hwffc_mr_update_done | no_mr1st_update) begin
               hwffc_st_nxt_wlp =
                (dvfsq_switch==DVFSQ_LOW2HIGH)                     ? HWFFC_ST_WAIT_ZQ_LATCH :   // goto SR w/o PD after ZQ latch
                (lp2_required || freq_cng_pre || retrain_required) ? HWFFC_ST_WAIT_PHY_REQ_OK : // goto SR w/o PD
                                                                     HWFFC_ST_SRPDE;            // goto SRPD
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_MR_UPDATE;
             end
           end


           HWFFC_ST_SRPDE : begin
             if (i_ns_sr) begin
               hwffc_st_nxt_wlp = HWFFC_ST_PHY_ST_REQ;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_SRPDE;
             end
           end
   
           HWFFC_ST_WAIT_ZQ_LATCH: begin
             if (hwffc_bgzq_stopped_propagate!=2'h0 || !hwffc_bgzq_stopped) begin
               // wait until ZQ latch triggered as a DVFSQ Low-to-High step is done
               // ZQ latch is triggered via hwffc_zq_restart[2] at hwffc_st_nxt_wlp's transition from HWFFC_ST_MR_UPDATE to HWFFC_ST_WAIT_PHY_REQ_OK if DVFSQ Low-to-High is active
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT_ZQ_LATCH;
             end else begin
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT_PHY_REQ_OK;
             end
           end

           // In non-legacy HWFFC enter, DDRCTL will enter to SR but without PD. Ensure ctrlupd, wck and mr4 are stopped.
           // Need to check here instead of the SRPD enter which had ensured them.
           // DDRCTL won't got to SRPD thanks to hwffc_stay_in_selfref
           HWFFC_ST_WAIT_PHY_REQ_OK: begin
             //assert(reg_ddrc_hwffc_mode); // this state is non-legacy HWFFC only
             if (ctrlupd_req) begin
               // wait until ctrlupd is idle
               //assert(hwffc_mask_dfireq);  // check that we are halting ctrlupd
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT_PHY_REQ_OK;
             end else if (reg_ddrc_lpddr5 && !gs_wck_stop_ok) begin // gs_wck_stop_ok is always 1 in lpddr4 mode.
               // wait until WCK is stopped
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT_PHY_REQ_OK;
             end else if (gs_pi_op_is_load_mr_norm || |rank_nop_after_load_mr_norm || ~gs_pi_data_pipeline_empty || ~t_rd2pd_satisfied) begin
               // Wait until mrr/mrw completes
               hwffc_st_nxt_wlp = HWFFC_ST_WAIT_PHY_REQ_OK;
             end else begin
               hwffc_st_nxt_wlp = HWFFC_ST_PHY_ST_REQ;
             end
           end
   
           HWFFC_ST_PHY_ST_REQ : begin
             if (!dfi_init_complete_hwffc) begin
               hwffc_st_nxt_wlp = HWFFC_ST_FREQ_CHANGE;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_PHY_ST_REQ;
             end
           end
   
           HWFFC_ST_FREQ_CHANGE : begin
             if (i_csysreq_ddrc_mux) begin
               hwffc_st_nxt_wlp = HWFFC_ST_PHY_END_REQ;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_FREQ_CHANGE;
             end
           end
   
           HWFFC_ST_PHY_END_REQ : begin
             if (lp3_required) begin
               hwffc_st_nxt_wlp = HWFFC_ST_PHY_END_REQ;
             end else if (dfi_init_complete_hwffc) begin
               hwffc_st_nxt_wlp = HWFFC_ST_SRX;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_PHY_END_REQ;
             end
           end
   
           HWFFC_ST_SRX : begin
             if (hwffc_mr_update_done | no_mr2nd_update) begin
               hwffc_st_nxt_wlp = HWFFC_ST_END;
             end else if ((reg_ddrc_hwffc_mode | i_target_vrcg) & (sr_st_nxt==SR_ST_SRX)) begin
               hwffc_st_nxt_wlp = HWFFC_ST_END;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_SRX;
             end
           end
   
           default : begin // HWFFC_ST_END
             if (xpi_st_nxt== XPI_ST_NORM) begin
               hwffc_st_nxt_wlp = HWFFC_ST_IDLE;
             end else begin 
               hwffc_st_nxt_wlp = HWFFC_ST_END;
             end
           end
      endcase // case (hwffc_st_curr)
   end

// 
// Outputs of block based on state
// 

assign hwffc_st_cng = (hwffc_st_curr != hwffc_st_nxt);

////////////////////
// For power control
////////////////////
assign hwffc_sr_req = (hwffc_st_curr == HWFFC_ST_SRE) |
                      ((
                         (hwffc_st_curr == HWFFC_ST_PHY_ST_REQ) |
                         (hwffc_st_curr == HWFFC_ST_MR_UPDATE) |
                         (hwffc_st_curr == HWFFC_ST_SRPDE) |
                         (hwffc_st_curr == HWFFC_ST_WAIT_ZQ_LATCH) |
                         (hwffc_st_curr == HWFFC_ST_WAIT_PHY_REQ_OK)
                      ) & lpddr_dev) |
                      (hwffc_st_curr == HWFFC_ST_PHY_END_REQ) |
                      (hwffc_st_curr == HWFFC_ST_FREQ_CHANGE);

assign hwffc_add_hif_stall = i_dis_drain_cam & (hwffc_sr_req | (hwffc_st_curr == HWFFC_ST_WAIT));
assign hwffc_hif_wd_stall  = i_dis_drain_cam & (hwffc_st_curr == HWFFC_ST_FREQ_CHANGE);
assign hwffc_stay_in_selfref = (hwffc_st_curr == HWFFC_ST_MR_UPDATE) |
                               (hwffc_st_curr == HWFFC_ST_WAIT_ZQ_LATCH) |
                               (hwffc_st_curr == HWFFC_ST_SRX) |
                               // non-legacy HWFFC hands over the DRAM in SR w/o PD to the PHY 
                               // Assert only when sr_st_curr is NOT in Automatic SR. Otherwise fsm will stack in ASRE - deadlock.
                               ((lp2_required || freq_cng_pre || retrain_required) && (sr_st_curr==SR_ST_SRE_HW_SW_STALL || sr_st_curr==SR_ST_SRE_HW_SW));

assign hwffc_srx_req = (hwffc_st_curr == HWFFC_ST_SRX);

// Note : When reg_ddrc_ctrlupd_pre_srx==1,
// ctrlupd will not be issued before SRX if HWFFC_ST_SRX is included
assign hwffc_mask_dfireq =
                         ((
                           (hwffc_st_curr == HWFFC_ST_PHY_ST_REQ    ) |
                           (hwffc_st_curr == HWFFC_ST_MR_UPDATE     ) |
                           (hwffc_st_curr == HWFFC_ST_WAIT_ZQ_LATCH ) |
                           (hwffc_st_curr == HWFFC_ST_SRPDE         ) |
                           (hwffc_st_curr == HWFFC_ST_WAIT_PHY_REQ_OK)
                         ) & lpddr_dev) | 
                           (hwffc_st_curr == HWFFC_ST_PHY_END_REQ   ) |
                           (hwffc_st_curr == HWFFC_ST_FREQ_CHANGE   );

assign hwffc_dis_zq_derate = (hwffc_st_curr == HWFFC_ST_SRE         ) |
                         ((
                           (hwffc_st_curr == HWFFC_ST_PHY_ST_REQ    ) |
                           (hwffc_st_curr == HWFFC_ST_MR_UPDATE     ) |
                           (hwffc_st_curr == HWFFC_ST_WAIT_ZQ_LATCH ) |
                           (hwffc_st_curr == HWFFC_ST_SRPDE         ) |
                           (hwffc_st_curr == HWFFC_ST_WAIT_PHY_REQ_OK)
                         ) & lpddr_dev) | 
                           (hwffc_st_curr == HWFFC_ST_PHY_END_REQ   ) |
                           (hwffc_st_curr == HWFFC_ST_FREQ_CHANGE   ) |
                           (hwffc_st_curr == HWFFC_ST_SRX           );

assign hwffc_st_wait = (hwffc_st_curr == HWFFC_ST_WAIT);
assign hwffc_sre = hwffc_st_cng & (
                   ((hwffc_st_nxt == HWFFC_ST_MR_UPDATE) & lpddr_dev) |
                   ((hwffc_st_nxt == HWFFC_ST_SRE      ) & dh_gs_ddr4  )
                   );

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      init_start_dl_cntr <= {2{1'b0}};
   end
   else if (hwffc_st_cng & 
      (((hwffc_st_nxt == HWFFC_ST_PHY_ST_REQ) & lpddr_dev) | 
       ((hwffc_st_nxt == HWFFC_ST_SRE       ) & dh_gs_ddr4  ))
   ) begin
      init_start_dl_cntr <= 2'b11;
   end else if (init_start_dl_cntr!=2'b00) begin
      init_start_dl_cntr <= init_start_dl_cntr - 2'b01;
   end
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      init_start_dl2_cntr <= {3{1'b0}};
   end
   else if (hwffc_st_cng & (hwffc_st_nxt == HWFFC_ST_PHY_END_REQ)) begin
      init_start_dl2_cntr <= 3'b111;
   end else if (init_start_dl2_cntr!=3'b000) begin
      init_start_dl2_cntr <= init_start_dl2_cntr - 3'd1;
   end
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
   if(!core_ddrc_rstn) begin
      hwffc_bgzq_stopped_propagate <= 2'b00;
   end
   else if (~hwffc_dis_zq_derate || (gsfsm_current_state!=GS_ST_SELFREF_EX1 && gsfsm_next_state==GS_ST_SELFREF_EX1)) begin
      // ZQCal can be triggered (1) when hwffc_dis_zq_derate toggles and (2) when SRX occurs.
      // Wait for hwffc_bgzq_stopped propagation after such event
      hwffc_bgzq_stopped_propagate <= 2'b11;
   end else if (|hwffc_zq_restart) begin
      // ZQCal can be triggered when this module requests ZQCal latch
      hwffc_bgzq_stopped_propagate <= 2'b11;
   end else if (hwffc_bgzq_stopped_propagate!=2'b00) begin
      hwffc_bgzq_stopped_propagate <= hwffc_bgzq_stopped_propagate - 2'd1;
   end
end



// dfi_init_start for frequency change
//   Make sure that dfi_init_start rises after dfi_cke falls, and ctrlupd_req == 0
assign hwffc_dfi_init_start_lpddr4 = ((hwffc_st_curr == HWFFC_ST_PHY_ST_REQ) | (hwffc_st_curr == HWFFC_ST_FREQ_CHANGE) | (init_start_dl2_cntr != 3'd0)) &
                                     lpddr_dev;

assign hwffc_dfi_init_start_ddr4 = 1'b0;

assign hwffc_dfi_init_start = (hwffc_dfi_init_start_ddr4 | hwffc_dfi_init_start_lpddr4) & (init_start_dl_cntr == 2'b00) & ~ctrlupd_req;

assign hwffc_freq_change = 
                           (lpddr_dev &
                              (hwffc_st_curr == HWFFC_ST_SRPDE     ) |
                              (hwffc_st_curr == HWFFC_ST_WAIT_PHY_REQ_OK) |
                              (hwffc_st_curr == HWFFC_ST_PHY_ST_REQ)
                           ) |
                           (hwffc_st_curr == HWFFC_ST_PHY_END_REQ) |
                           (hwffc_st_curr == HWFFC_ST_FREQ_CHANGE); 

////////////////////
// For frequency selection
////////////////////
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_target_freq_en <= 1'b0;
  end else if (hwffc_init) begin
    hwffc_target_freq_en <= 1'b1;
  end else if (hwffc_end) begin
    hwffc_target_freq_en <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_target_freq       <= {TARGET_FREQUENCY_WIDTH{1'b0}};
  end else if (hwffc_init) begin
    hwffc_target_freq       <= reg_ddrc_target_frequency;
  end else if (hwffc_st_cng & (hwffc_st_nxt == HWFFC_ST_PHY_END_REQ) & freq_cng_required) begin
    hwffc_target_freq       <= hwffc_dfi_frequency[TARGET_FREQUENCY_WIDTH-1:0];
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_target_freq_init <= {TARGET_FREQUENCY_WIDTH{1'b0}};
  end else if (hwffc_init) begin
    hwffc_target_freq_init <= reg_ddrc_target_frequency;
  end else if (hwffc_st_cng & (
                               (hwffc_st_nxt == HWFFC_ST_SRE) // HWFFC_ST_MR_UPDATE
                              ) & freq_cng_required) begin
    hwffc_target_freq_init <= hwffc_trg_avl ? i_csysfrequency_ddrc_r[TARGET_FREQUENCY_WIDTH-1:0] : hwffc_dfi_frequency[TARGET_FREQUENCY_WIDTH-1:0];
  end 
end

// refresh update
assign hwffc_ref_upd_pre = (hwffc_st_cng & (hwffc_st_nxt == HWFFC_ST_PHY_END_REQ) & freq_cng_required) & (hwffc_target_freq != hwffc_dfi_frequency[TARGET_FREQUENCY_WIDTH-1:0]);

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_ref_upd_r <= 2'b00;
  end else begin
    hwffc_ref_upd_r <= {hwffc_ref_upd_r[0], hwffc_ref_upd_pre};
  end 
end

assign hwffc_refresh_update_pulse = hwffc_ref_upd_r[1];

////////////////////
// For MR update
////////////////////

assign mr_upd_1st_trg = hwffc_st_cng & (hwffc_st_nxt == HWFFC_ST_MR_UPDATE) & (~no_mr1st_update);
assign mr_upd_2nd_trg = hwffc_st_cng & (hwffc_st_nxt == HWFFC_ST_SRX) & (reg_ddrc_hwffc_mode || ~i_target_vrcg) & (~no_mr2nd_update);
always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_mr_update_start <= 4'b0;
  end else begin
    if(mr_upd_1st_trg) begin
      if(mrwbuf_trg) begin
        case(dvfsq_switch)
          DVFSQ_HIGH2LOW: hwffc_mr_update_start <= 4'b1100;  // MRWBUF + ZQRESET
          DVFSQ_LOW2HIGH: hwffc_mr_update_start <= 4'b1010;  // MRWBUF + ZQSTART
          default:        hwffc_mr_update_start <= 4'b1000;  // MRWBUF only
        endcase
      end else begin
        case(dvfsq_switch)
          DVFSQ_HIGH2LOW: hwffc_mr_update_start <= 4'b0100;  // ZQRESET
          DVFSQ_LOW2HIGH: hwffc_mr_update_start <= 4'b0010;  // ZQSTART
          default:        hwffc_mr_update_start <= 4'b0001;  // ZQSTOP (required by LP2) or MR13_FSPWR (hwffc_mode=0)
        endcase
      end
    end else if(mr_upd_2nd_trg) begin
      hwffc_mr_update_start <= 4'b0010;  // ZQSTART or MR13_VRCG0
    end else if (|hwffc_mr_update_start) begin
      hwffc_mr_update_start <= 4'b0000;  // clear request
    end
  end 
end


always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_vrcg <= 1'b1;
  end
  else if (hwffc_init) begin
    hwffc_vrcg <= reg_ddrc_init_vrcg;
  end
  else if (hwffc_st_cng & 
     ((lpddr_dev & (hwffc_st_curr == HWFFC_ST_SRX        )) |
      (dh_gs_ddr4   & (hwffc_st_curr == HWFFC_ST_PHY_END_REQ)))
  ) begin
    hwffc_vrcg <= i_target_vrcg;
  end 
end

////////////////////
// Background calibration related
////////////////////

// Generate a pulse to kick a ZQ calib after HWFFC.
// Note that no need to explicitly kick it for legacy HWFFC here. PDX kicks it instead.
// Even if request is sent, gs_zq_calib may mask the request according to dh_gs_dis_srx_zqcl or dh_gs_dis_srx_zqcl_hwffc
// When DVFSQ_LOW2HIGH is active, ZQLat is kicked right before the freq change via hwffc_zq_restart[2]. No need to send it again via hwffc_zq_restart[0].
//   Still in such case, hwffc_zq_restart[3] will be sent to force reloading auto_zq_timer_x1024. hwffc_zq_restart[3] is special and won't kick a new ZQL cmd
assign  hwffc_zq_restart[0] = (freq_cng_pre | retrain_required) && (hwffc_st_curr==HWFFC_ST_SRX)       && (hwffc_st_nxt==HWFFC_ST_END) && (dvfsq_switch!=DVFSQ_LOW2HIGH);
assign  hwffc_zq_restart[1] = (lp2_required                   ) && (hwffc_st_curr==HWFFC_ST_SRX)       && (hwffc_st_nxt==HWFFC_ST_END);
assign  hwffc_zq_restart[2] =                                      (hwffc_st_curr==HWFFC_ST_MR_UPDATE) && (hwffc_st_nxt==HWFFC_ST_WAIT_ZQ_LATCH);
assign  hwffc_zq_restart[3] = (freq_cng_pre                   ) && (hwffc_st_curr==HWFFC_ST_SRX)       && (hwffc_st_nxt==HWFFC_ST_END) && (dvfsq_switch==DVFSQ_LOW2HIGH);

////////////////////
// HWFFC I/F
////////////////////
assign hwffc_cactive_ddrc = (hwffc_st_curr != HWFFC_ST_FREQ_CHANGE) & (hwffc_st_curr != HWFFC_ST_PHY_END_REQ)
                            | hwffc_lp3_entered
                            ;
assign csysack_ffcproc    = (hwffc_st_curr != HWFFC_ST_FREQ_CHANGE) & (hwffc_st_curr != HWFFC_ST_PHY_END_REQ) & 
                            (hwffc_st_curr != HWFFC_ST_SRX) & 
                            (hwffc_st_curr != HWFFC_ST_END)
                            | hwffc_lp3_entered
                            ;

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_accepted <= 1'b0;
  end else if (hwffc_trg_avl) begin
    hwffc_accepted <= 1'b1;
  end else if ((hwffc_st_curr == HWFFC_ST_END) & (hwffc_st_nxt == HWFFC_ST_IDLE)) begin
    hwffc_accepted <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    hwffc_rejected <= 1'b0;
  end else if (hwffc_trg_rej) begin
    hwffc_rejected <= 1'b1;
  end else if (csysack_ddrc) begin
    hwffc_rejected <= 1'b0;
  end 
end

assign hwffc_in_progress  = hwffc_trg_avl | hwffc_accepted;
assign hwffc_responding   = hwffc_trg | hwffc_accepted | hwffc_rejected;
assign hwffc_csysack_ddrc = (~hwffc_accepted | csysack_ffcproc) & (~hwffc_rejected | i_csysreq_ddrc_mux) & ~hwffc_trg_rej;

// xpi_ddrc_port_disable_ack/xpi_ddrc_wch_locked - already synchronized to core clock domain
wire [NPORTS-1:0] i_port_disable_ack_sync;
wire [NPORTS-2:0] i_wch_locked_sync;

assign i_port_disable_ack_sync = xpi_ddrc_port_disable_ack;
assign i_wch_locked_sync = xpi_ddrc_wch_locked;

//
// State M/C
//
   // FSM sequential
   always @(posedge co_yy_clk or negedge core_ddrc_rstn)
   begin: xpi_st_seq_PROC
      if( !core_ddrc_rstn )
        xpi_st_curr <= XPI_ST_NORM;
      else begin
        xpi_st_curr <= xpi_st_nxt;
      end
   end

   // FSM combinatorial
   always @(*)
   begin: xpi_st_comb_PROC
      case(xpi_st_curr)
        XPI_ST_NORM: begin
          if (hwffc_trg_avl) begin
            xpi_st_nxt = XPI_ST_DIS_REQ;
          end else begin
            xpi_st_nxt = XPI_ST_NORM;
          end
        end
        XPI_ST_DIS_REQ: begin
          if (axi_dis_ack) begin
            xpi_st_nxt = XPI_ST_DISABLED;
          end else begin
            xpi_st_nxt = XPI_ST_DIS_REQ;
          end
        end
        XPI_ST_DISABLED: begin
          if (hwffc_st_curr == HWFFC_ST_SRX) begin
            xpi_st_nxt = XPI_ST_ENA_REQ;
          end else begin
            xpi_st_nxt = XPI_ST_DISABLED;
          end
        end
        default: begin // XPI_ST_ENA_REQ
          if (axi_enb_ack) begin
            xpi_st_nxt = XPI_ST_NORM;
          end else begin
            xpi_st_nxt = XPI_ST_ENA_REQ;
          end
        end
      endcase // case(xpi_st_curr)
   end

assign xpi_st_cng = (xpi_st_curr != xpi_st_nxt);
assign xpi_disabled = xpi_st_cng & (xpi_st_nxt == XPI_ST_DISABLED);

assign axi_dis_ack = i_dis_drain_cam ?  (&i_wch_locked_sync) :  (&i_port_disable_ack_sync);
assign axi_enb_ack = i_dis_drain_cam ? ~(|i_wch_locked_sync) : ~(|i_port_disable_ack_sync);

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    ddrc_xpi_port_disable_req <= 1'b0;
  end else if ((xpi_st_curr == XPI_ST_NORM) & (xpi_st_nxt == XPI_ST_DIS_REQ)) begin
    ddrc_xpi_port_disable_req <= 1'b1;
  end else if ((xpi_st_curr == XPI_ST_DISABLED) & (xpi_st_nxt == XPI_ST_ENA_REQ)) begin
    ddrc_xpi_port_disable_req <= 1'b0;
  end 
end

always @(posedge co_yy_clk or negedge core_ddrc_rstn) begin
  if(!core_ddrc_rstn) begin
    ddrc_xpi_clock_required <= 1'b0;
  end else if ((xpi_st_curr == XPI_ST_NORM) & (xpi_st_nxt == XPI_ST_DIS_REQ)) begin
    ddrc_xpi_clock_required <= 1'b1;
  end else if ((xpi_st_curr == XPI_ST_DIS_REQ) & (xpi_st_nxt == XPI_ST_DISABLED)) begin
    ddrc_xpi_clock_required <= 1'b0;
  end else if ((xpi_st_curr == XPI_ST_DISABLED) & (xpi_st_nxt == XPI_ST_ENA_REQ)) begin
    ddrc_xpi_clock_required <= 1'b1;
  end else if ((xpi_st_curr == XPI_ST_ENA_REQ) & (xpi_st_nxt == XPI_ST_NORM)) begin
    ddrc_xpi_clock_required <= 1'b0;
  end 
end

//--------------------------- HWFFC -------------------------------


`ifndef SYNTHESIS
`ifdef SNPS_ASSERT_ON
  sequence s_srpd_to_sr_glitch;
    @(posedge co_yy_clk) $changed(gsfsm_srpd_to_sr)[*3];
  endsequence : s_srpd_to_sr_glitch

  a_srpd_to_sr_not_during_normal:             assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) (gsfsm_srpd_to_sr |-> !$past(i_ns_norm, 2)));
  a_srpd_to_sr_no_glitch:                     assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) ($changed(gsfsm_srpd_to_sr) |-> !s_srpd_to_sr_glitch.ended));

  // srpd_to_sr must be ongoing while hwffc_asr_to_sre_hsr==1
  a_hwffc_asr_to_sre_hsr_with_srpd_to_sr:     assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) $rose(hwffc_asr_to_sre_hsr) |=> gsfsm_srpd_to_sr);
  // Background ZQ cal must be idle while disabled in hwffc_mode=1
  // In hwffc_mode=0, hwffc_bgzq_stopped will assert while hwffc_st_curr==HWFFC_ST_SRX but safe; ZQCal will be actually sent after MRW (MR13) and after hwffc_dis_zq_derate's de-assertion.
  property p_hwffc_zq_derate_is_disabled;
    @(posedge co_yy_clk) disable iff(~core_ddrc_rstn || hwffc_st_curr==HWFFC_ST_SRE || hwffc_st_curr==HWFFC_ST_WAIT_ZQ_LATCH || hwffc_st_curr==HWFFC_ST_WAIT) // Added HWFFC_ST_WAIT as a disable iff condition. ST_SRE->ST_WAIT transition can occur if phymstr is there. Exclude HWFFC_ST_WAIT state not to fire this asesertion in such case
      reg_ddrc_hwffc_mode && hwffc_dis_zq_derate |-> hwffc_bgzq_stopped;
  endproperty
  a_hwffc_zq_derate_is_disabled:              assert property(p_hwffc_zq_derate_is_disabled);
  // Once HWFFC is done, state must go to Normal without go through ASR
  a_not_go_to_asr_after_hwffc:                assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) reg_ddrc_hwffc_mode && $fell(hwffc_in_progress)
                                                                |=> (sr_st_curr!=SR_ST_SRE_ASR && sr_st_curr!=SR_ST_SR_ASR) throughout i_ns_norm[->1]);
  a_dvfsq_switch_only_during_freq_change:     assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) dvfsq_switch!=DVFSQ_HOLD |-> reg_ddrc_lpddr5 && reg_ddrc_hwffc_mode && i_freq_cng_flg);
  // hwffc_st_nxt_wlp must go through HWFFC_ST_MR_UPDATE until dfi_init_start asserts, if dvfsq will switch
  a_mr_update_follows_dvfsq_switch:           assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) $rose(dvfsq_switch!=DVFSQ_HOLD) |-> (hwffc_st_nxt_wlp==HWFFC_ST_MR_UPDATE)[->1] within hwffc_dfi_init_start[->1]);
    
  // hwffc_asr_to_sre_hsr==1 must not immediately follow ppt2_asr_to_sre_asr==1. There must be SELFREF (SRPD) state in between.
  a_exclusive_asr_to_sre_hsr:                 assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) (hwffc_asr_to_sre_hsr || ppt2_asr_to_sre_asr) |-> !(hwffc_asr_to_sre_hsr && ppt2_asr_to_sre_asr));
  a_ppt2_asr_to_sre_asr_complete:             assert property(@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) $rose(ppt2_asr_to_sre_asr) |=> (gsfsm_next_state==GS_ST_SELFREF)[->1] within hwffc_asr_to_sre_hsr[->1]);

  a_cactive_ddrc_kept_high_ctrlupd_burst_busy: assert property (@(posedge co_yy_clk) disable iff (~core_ddrc_rstn) (ddrc_reg_ctrlupd_burst_busy |-> cactive_ddrc));

`SNPS_UNR_CONSTANT("dis_cam_drain is not supported", 1, dh_gs_dis_cam_drain_selfref, 0)
`SNPS_UNR_CONSTANT("LP3 enter is not supported", 1, lp3_required, 0)


`endif   // SNPS_ASSERT_ON
`endif // SYNTHESIS


endmodule  // gs_global_fsm_sr_hw_lp
