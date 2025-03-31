// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

module kse_jtag_fsm_sva
  import rot_pkg::*;
  import soc_mgmt_pkg::*;
(
  /// Clock, positive edge triggered
  input  logic                  i_clk,
  /// Asynchronous reset, active low
  input  logic                  i_rst_n,
  ///////////////////
  // TDR interface //
  ///////////////////
  input  kse3_jtag_req_t        i_kse3_jtag_req,
  input  kse3_jtag_resp_t       o_kse3_jtag_resp,
  input  logic                  i_tdr_valid,
  input  logic                  o_tdr_ready,
  input  logic                  i_tdr_jtag_dbg,
  input  logic                  i_lcs_valid,
  input  logic                  i_lcs_is_terminated,
  input  logic                  i_lcs_is_chip_wafer_test,
  input  logic                  i_lcs_is_chip_perso,
  input  logic                  i_lcs_is_chip_field_return,
  ///////////////////////////
  // AHB manager interface //
  ///////////////////////////
  input  soc_mgmt_haddr_t       o_ahb_m_haddr,
  input  logic                  o_ahb_m_hwrite,
  input  soc_mgmt_hdata_t       o_ahb_m_hwdata,
  input  axe_ahb_pkg::htrans_e  o_ahb_m_htrans,
  input  axe_ahb_pkg::hburst_e  o_ahb_m_hburst,
  input  axe_ahb_pkg::hsize_e   o_ahb_m_hsize,
  input  soc_mgmt_hdata_t       i_ahb_m_hrdata,
  input  logic                  i_ahb_m_hready,
  input  logic                  i_ahb_m_hresp
);

  // =====================================================
  // Local parameters
  // =====================================================
  localparam soc_mgmt_hdata_t OTP_PERSO_STR_LEN_MAX   = 32'h0000_0003;
  localparam soc_mgmt_hdata_t OTP_ANCHOR_VAL_LEN_MAX  = 32'h0000_0003;
  localparam int unsigned     AHB_RESP_MAX_WAIT       = 5;
  localparam int unsigned     LCS_VALID_MAX_WAIT      = 16;

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================
  logic req_is_ahb;
  logic req_is_kse_access;
  logic req_is_kse_command;
  logic req_is_otp_access;
  logic req_is_aor_access;
  logic req_is_enter_jtag_access_mode;
  logic req_is_init_kse3_adac_itf;
  logic resp_is_ignored;
  logic jtag_fsm_is_idle;
  logic jtag_fsm_is_keep_closed;
  logic jtag_fsm_is_fully_open;
  logic jtag_fsm_is_adac_only;
  logic jtag_fsm_is_busy;
  logic jtag_fsm_is_error;
  logic kse_cmd_is_challenge;

  always_comb req_is_ahb                    = i_tdr_valid & i_kse3_jtag_req.ahb_valid;
  always_comb req_is_kse_access             = req_is_ahb & (i_kse3_jtag_req.ahb_haddr[KSE3_JTAG_HAW-1:16] == 3'h0);
  always_comb req_is_otp_access             = req_is_ahb & (i_kse3_jtag_req.ahb_haddr[KSE3_JTAG_HAW-1:16] == 3'h5);
  always_comb req_is_aor_access             = req_is_ahb & (i_kse3_jtag_req.ahb_haddr[KSE3_JTAG_HAW-1:16] == 3'h4);
  always_comb req_is_enter_jtag_access_mode = i_tdr_valid & i_kse3_jtag_req.enter_jtag_access_mode;
  always_comb req_is_init_kse3_adac_itf     = i_tdr_valid & i_kse3_jtag_req.init_kse3_adac_itf;
  always_comb jtag_fsm_is_idle              = kse_jtag_fsm.jtag_cmd_state_q == JTAG_CMD_IDLE;
  always_comb jtag_fsm_is_keep_closed       = kse_jtag_fsm.jtag_cmd_state_q == JTAG_CMD_KEEP_CLOSED;
  always_comb jtag_fsm_is_fully_open        = kse_jtag_fsm.jtag_cmd_state_q == JTAG_CMD_FULLY_OPEN;
  always_comb jtag_fsm_is_adac_only         = kse_jtag_fsm.jtag_cmd_state_q == JTAG_CMD_ADAC_ONLY;
  always_comb jtag_fsm_is_error             = kse_jtag_fsm.jtag_cmd_state_q == JTAG_CMD_ERROR;
  always_comb resp_is_ignored               = o_kse3_jtag_resp.cmd_ignored;

  always_comb jtag_fsm_is_busy = ~(kse_jtag_fsm.jtag_cmd_state_q inside {
    JTAG_CMD_IDLE,
    JTAG_CMD_FULLY_OPEN,
    JTAG_CMD_KEEP_CLOSED,
    JTAG_CMD_ADAC_ONLY,
    JTAG_CMD_ERROR_REPORT,
    JTAG_CMD_ERROR}
  );

  always_comb req_is_kse_command = req_is_kse_access & i_kse3_jtag_req.ahb_hwrite & (i_kse3_jtag_req.ahb_haddr == KSE3_CMD_CTRL_ADDR[KSE3_JTAG_HAW-1:0]);
  always_comb kse_cmd_is_challenge = req_is_kse_command &
                                    ((i_kse3_jtag_req.ahb_hwdata[31:2] == kudelski_kse3_pkg::KSE3_CMD_GETCHALLENGE[31:2]) |
                                     (i_kse3_jtag_req.ahb_hwdata[31:2] == kudelski_kse3_pkg::KSE3_CMD_UNLOCKACCESS[31:2]));

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Properties
  // =====================================================

  // =====================================================
  // Assumes
  // =====================================================

  // i_tdr_valid stays high until o_tdr_ready == 1.
  assume_jtag_valid_ready : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_tdr_valid && !o_tdr_ready |-> ##1 i_tdr_valid
  );
  // i_tdr_valid is cleared for at least one cycle after o_tdr_ready is observed.
  assume_jtag_valid_clear : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    o_tdr_ready |-> ##1 !i_tdr_valid
  );
  // JTAG request does not change while valid is 1.
  assume_jtag_req_stable : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    ##1 i_tdr_valid && $stable(i_tdr_valid) |-> $stable(i_kse3_jtag_req)
  );
  // Reset is triggered if JTAG_DBG changes.
  assume_jtag_dbg_tdr_reset : assume property (
    @(posedge i_clk)
    $changed(i_tdr_jtag_dbg) |-> !i_rst_n
  );
  // i_lcs_valid shall be set at some point.
  assume_lcs_valid_set_max_wait : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    ##[1:LCS_VALID_MAX_WAIT] i_lcs_valid
  );
  // Once i_lcs_valid is set to 1 it cannot go back to 0.
  assume_lcs_valid_set_once : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_lcs_valid |-> ##1 i_lcs_valid
  );
  // LCS value does not change once i_lcs_valid is set.
  assume_lcs_stable : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    ##1 i_lcs_valid && $stable(i_lcs_valid) |-> $stable(i_lcs_is_terminated) &&
                                                $stable(i_lcs_is_chip_wafer_test) &&
                                                $stable(i_lcs_is_chip_perso) &&
                                                $stable(i_lcs_is_chip_field_return)
  );
  // Incoming haddr is word-aligned.
  assume_haddr_aligned : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_kse3_jtag_req.ahb_haddr[1:0] == 2'b00
  );
  // Limit the amount of time hready is 0 to avoid getting stuck waiting for AHB subordinate response.
  assume_ahb_resp_ready : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    !i_ahb_m_hready |=> ##[0:AHB_RESP_MAX_WAIT] i_ahb_m_hready
  );
  // KSE3_CMD_CTRL_ADDR reads always return hrdata[0]==0 to avoid getting stuck polling the KSE3.
  assume_kse_low_exectime : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (o_ahb_m_haddr == KSE3_CMD_CTRL_ADDR) && !o_ahb_m_hwrite |-> !i_ahb_m_hrdata[0]
  );
  // OTP_PERSO_STR_LEN_ADDR reads to return a low number to avoid getting stuck in INIT_DRAM_PERSO_LEN state.
  assume_perso_str_len_max : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (o_ahb_m_haddr == OTP_PERSO_STR_LEN_ADDR) && !o_ahb_m_hwrite |-> (i_ahb_m_hrdata < OTP_PERSO_STR_LEN_MAX)
  );
  // OTP_ANCHOR_VAL_LEN_ADDR reads to return a low number to avoid getting stuck in INIT_DRAM_PERSO_LEN state.
  assume_anchor_val_len_max : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (o_ahb_m_haddr == OTP_ANCHOR_VAL_LEN_ADDR) && !o_ahb_m_hwrite |-> (i_ahb_m_hrdata < OTP_ANCHOR_VAL_LEN_MAX)
  );
  assume_single_jtag_request: assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    $onehot({i_kse3_jtag_req.ahb_valid, i_kse3_jtag_req.enter_jtag_access_mode, i_kse3_jtag_req.init_kse3_adac_itf})
  );

  // =====================================================
  // Assertions
  // =====================================================

  // All requests are ignored when i_tdr_jtag_dbg == 0.
  assert_cmd_ignored_jtag_dbg : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    !i_tdr_jtag_dbg && i_tdr_valid && o_tdr_ready |-> resp_is_ignored && jtag_fsm_is_idle
  );
  // All requests are ignored when i_lcs_is_terminated.
  assert_cmd_ignored_terminated : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_lcs_is_terminated && i_tdr_valid && o_tdr_ready |-> resp_is_ignored && jtag_fsm_is_idle
  );
  // Ready is always 0 on busy states except when transitioning out of the busy state.
  assert_jtag_busy : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_busy && o_tdr_ready |-> ##1 !jtag_fsm_is_busy
  );
  // All JTAG commands should end in a finite amount of cycles.
  assert_jtag_resp_max_wait : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_tdr_valid && !o_tdr_ready |-> ##[0:$] (o_tdr_ready)
  );

  // -----------------------------------------------------
  // KSE3 mailbox access rights.
  // -----------------------------------------------------
  //
  // JTAG_CMD_IDLE state: All KSE3 commands via JTAG are ignored.
  assert_kse_cmd_ignored_idle : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    req_is_kse_access && jtag_fsm_is_idle && o_tdr_ready |-> resp_is_ignored
  );
  // JTAG_CMD_ADAC_ONLY state: only Getchallenge/UnlockAccess commands are allowed.
  assert_kse_cmd_ignored_adac_only : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_adac_only && req_is_kse_command && !kse_cmd_is_challenge && o_tdr_ready |-> resp_is_ignored
  );
  assert_kse_cmd_allowed_adac_only : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_adac_only && kse_cmd_is_challenge && o_tdr_ready |-> !resp_is_ignored
  );
  // JTAG_CMD_ADAC_ONLY state: AHB accesses to the KSE3 mailbox that do not generate commands are allowed.
  assert_kse_access_allowed_adac_only : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_adac_only && req_is_ahb && !req_is_kse_command && o_tdr_ready |-> !resp_is_ignored
  );
  // JTAG_CMD_KEEP_CLOSED state: All KSE3 commands via JTAG are ignored.
  assert_kse_cmd_ignored_keep_closed : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    req_is_kse_access && jtag_fsm_is_keep_closed && o_tdr_ready |-> resp_is_ignored
  );
  // JTAG_CMD_ERROR state: Only writes to KSE CMD_CTRL registers are ignored.
  assert_kse_cmd_ignored_error : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_error && (req_is_kse_command || !req_is_ahb) && o_tdr_ready |-> resp_is_ignored
  );
  assert_kse_cmd_allowed_error : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_error && req_is_ahb && !req_is_kse_command && o_tdr_ready |-> !resp_is_ignored
  );
  // JTAG_CMD_FULLY_OPEN: All AHB commands via JTAG are allowed.
  assert_all_allowed_fully_open : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_fully_open && req_is_ahb && i_tdr_valid && o_tdr_ready |-> !resp_is_ignored
  );

  // -----------------------------------------------------
  // OTP and AOR access rights.
  // -----------------------------------------------------
  //
  // OTP and AOR accesses are never ignored if LCS != terminated.
  assert_otp_aor_access_granted : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_tdr_jtag_dbg && !i_lcs_is_terminated && (req_is_otp_access || req_is_aor_access) && o_tdr_ready |-> !resp_is_ignored
  );

  // -----------------------------------------------------
  // Command sequences.
  // -----------------------------------------------------
  //
  // enter_jtag_access_mode is accepted only in JTAG_CMD_IDLE state.
  assert_enter_jtag_access_mode_ignored : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    !jtag_fsm_is_idle && req_is_enter_jtag_access_mode && $rose(i_tdr_valid) |-> s_eventually (o_tdr_ready && resp_is_ignored)
  );
  assert_enter_jtag_access_mode_allowed : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_tdr_jtag_dbg && !i_lcs_is_terminated && i_lcs_valid && jtag_fsm_is_idle && req_is_enter_jtag_access_mode |-> ##[0:$] (o_tdr_ready && !resp_is_ignored)
  );
  // init_kse3_adac_itf is accepted only in JTAG_CMD_KEEP_CLOSED state.
  assert_init_kse3_adac_itf_ignored : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    !jtag_fsm_is_keep_closed && req_is_init_kse3_adac_itf && $rose(i_tdr_valid) |-> s_eventually (o_tdr_ready && resp_is_ignored)
  );
  assert_init_kse3_adac_itf_allowed : assert property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_keep_closed && req_is_init_kse3_adac_itf && i_tdr_valid |-> ##[0:$] (o_tdr_ready && !resp_is_ignored)
  );

  // TODO(kluciani, consider adding assertions on enter_jtag_access_mode and init_kse3_adac_itf sequence of AHB transactions)

  // =====================================================
  // Covers
  // =====================================================
  cover_jtag_keep_closed : cover property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_keep_closed
  );
  cover_jtag_fully_open : cover property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_fully_open
  );
  cover_jtag_adac_only : cover property (
    @(posedge i_clk) disable iff (!i_rst_n)
    jtag_fsm_is_adac_only
  );

endmodule
