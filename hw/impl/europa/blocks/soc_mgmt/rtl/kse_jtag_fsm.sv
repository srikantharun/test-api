// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: kevin Luciani <kevin.luciani@axelera.ai>
//
/// Description: SoC Management Secure enclave KSE3 JTAG command FSM.
///

module kse_jtag_fsm
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
  output kse3_jtag_resp_t       o_kse3_jtag_resp,
  input  logic                  i_tdr_valid,
  output logic                  o_tdr_ready,
  input  logic                  i_tdr_jtag_dbg,
  input  logic                  i_lcs_valid,
  input  logic                  i_lcs_is_terminated,
  input  logic                  i_lcs_is_chip_wafer_test,
  input  logic                  i_lcs_is_chip_perso,
  input  logic                  i_lcs_is_chip_field_return,
  ///////////////////////////
  // AHB manager interface //
  ///////////////////////////
  output soc_mgmt_haddr_t       o_ahb_m_haddr,
  output logic                  o_ahb_m_hwrite,
  output soc_mgmt_hdata_t       o_ahb_m_hwdata,
  output axe_ahb_pkg::htrans_e  o_ahb_m_htrans,
  output axe_ahb_pkg::hburst_e  o_ahb_m_hburst,
  output axe_ahb_pkg::hsize_e   o_ahb_m_hsize,
  input  soc_mgmt_hdata_t       i_ahb_m_hrdata,
  input  logic                  i_ahb_m_hready,
  input  logic                  i_ahb_m_hresp
);

  // ----------------------------------------------------------------------------
  // Signal declarations
  // ----------------------------------------------------------------------------
  // AHB manager mux
  ahb_manager_sel_e         ahb_manager_sel;
  logic                     ahb_manager_mux_valid  [JTAG_FSM_AHB_MGR_SEL_N];
  logic                     ahb_manager_mux_wr     [JTAG_FSM_AHB_MGR_SEL_N];
  soc_mgmt_haddr_t          ahb_manager_mux_addr   [JTAG_FSM_AHB_MGR_SEL_N];
  soc_mgmt_hdata_t          ahb_manager_mux_wdata  [JTAG_FSM_AHB_MGR_SEL_N];
  logic                     ahb_manager_valid;
  logic                     ahb_manager_wr;
  soc_mgmt_haddr_t          ahb_manager_addr;
  soc_mgmt_hdata_t          ahb_manager_wdata;
  soc_mgmt_hdata_t          ahb_manager_rdata;
  logic                     ahb_manager_error;
  logic                     ahb_manager_ready;
  // OTP to KSE FSM
  soc_mgmt_haddr_t          otp_to_kse_otp_start_addr;
  soc_mgmt_haddr_t          otp_to_kse_kse_start_addr;
  otp_to_kse_tr_size_t      otp_to_kse_tr_size;
  logic                     otp_to_kse_invert;
  logic                     otp_to_kse_valid;
  logic                     otp_to_kse_ready;
  otp_to_kse_state_e        otp_to_kse_state_d;
  otp_to_kse_state_e        otp_to_kse_state_q;
  logic                     otp_to_kse_state_changed;
  logic                     otp_to_kse_error_d;
  logic                     otp_to_kse_error_q;
  soc_mgmt_haddr_t          otp_to_kse_otp_addr_d;
  soc_mgmt_haddr_t          otp_to_kse_otp_addr_q;
  soc_mgmt_haddr_t          otp_to_kse_kse_addr_d;
  soc_mgmt_haddr_t          otp_to_kse_kse_addr_q;
  otp_to_kse_tr_size_t      otp_to_kse_kse_byte_cnt_d;
  otp_to_kse_tr_size_t      otp_to_kse_kse_byte_cnt_q;
  soc_mgmt_hdata_t          otp_to_kse_rdata_d;
  soc_mgmt_hdata_t          otp_to_kse_rdata_q;
  // KSE cmd FSM
  kse_cmd_state_e           kse_cmd_state_d;
  kse_cmd_state_e           kse_cmd_state_q;
  logic                     kse_cmd_state_changed;
  soc_mgmt_hdata_t          kse_cmd;
  logic                     kse_cmd_valid;
  logic                     kse_cmd_ready;
  logic                     kse_ahb_error_d;
  logic                     kse_ahb_error_q;
  logic                     kse_cmd_error_d;
  logic                     kse_cmd_error_q;
  // Main JTAG command FSM
  jtag_cmd_state_e          jtag_cmd_state_d;
  jtag_cmd_state_e          jtag_cmd_state_q;
  logic                     jtag_cmd_state_changed;
  otp_to_kse_tr_size_t      perso_str_len_d;
  otp_to_kse_tr_size_t      perso_str_len_q;
  otp_to_kse_tr_size_t      anchor_len_d;
  otp_to_kse_tr_size_t      anchor_len_q;
  logic                     ca1_programmed_d;
  logic                     ca1_programmed_q;
  logic                     jtag_cmd_kse_error;
  logic                     jtag_cmd_ahb_error;
  logic                     jtag_cmd_ignored;
  // Others
  logic                     ahb_addr_is_otp;
  logic                     ahb_addr_is_aor;
  logic                     ahb_access_is_kse3_cmd;
  logic                     ahb_access_is_getchallenge;
  logic                     ahb_access_is_unlockaccess;
  logic                     jtag_fully_open;
  soc_mgmt_haddr_t          jtag_req_addr_extended;

  // ----------------------------------------------------------------------------
  // RTL
  // ----------------------------------------------------------------------------

  // Convert 20-bit JTAG address to 32-bit SoC address by adding secure enclave base address to it.
  always_comb jtag_req_addr_extended = {aipu_addr_map_pkg::SOC_MGMT_ST_ADDR[SOC_MGMT_HAW-1:KSE3_JTAG_HAW], i_kse3_jtag_req.ahb_haddr};

  // Useful flags for CMD filtering.
  always_comb ahb_addr_is_otp = i_kse3_jtag_req.ahb_haddr[KSE3_JTAG_HAW-1:OTP_ADDR_SPACE_W] == OTP_ST_ADDR[KSE3_JTAG_HAW-1:OTP_ADDR_SPACE_W];
  always_comb ahb_addr_is_aor = i_kse3_jtag_req.ahb_haddr[KSE3_JTAG_HAW-1:AOR_ADDR_SPACE_W] == AOR_ST_ADDR[KSE3_JTAG_HAW-1:AOR_ADDR_SPACE_W];
  // A KSE3 CMD is an AHB write request to the KSE3 CMD_CTRL address.
  always_comb ahb_access_is_kse3_cmd = i_kse3_jtag_req.ahb_valid & i_kse3_jtag_req.ahb_hwrite &
                                      (i_kse3_jtag_req.ahb_haddr == KSE3_CMD_CTRL_ADDR[KSE3_JTAG_HAW-1:0]);
  // Do not check CMD_CTRL bits 1:0 as they are not part of the KSE3 command encoding.
  always_comb ahb_access_is_getchallenge = ahb_access_is_kse3_cmd & (i_kse3_jtag_req.ahb_hwdata[31:2] == kudelski_kse3_pkg::KSE3_CMD_GETCHALLENGE[31:2]);
  always_comb ahb_access_is_unlockaccess = ahb_access_is_kse3_cmd & (i_kse3_jtag_req.ahb_hwdata[31:2] == kudelski_kse3_pkg::KSE3_CMD_UNLOCKACCESS[31:2]);

  always_comb jtag_fully_open = i_lcs_is_chip_perso | i_lcs_is_chip_field_return | i_lcs_is_chip_wafer_test;

  // ----------------------------------------------------------------------------
  // Main command FSM
  // ----------------------------------------------------------------------------
  //
  // This is the main FSM which controls the KSE CDM FSM and OTP to KSE FSM.
  // It interprets incoming JTAG commands, filters the allowed AHB accesses to
  // the KSE3 and contains the command sequences for enter_jtag_access_mode and
  // init_kse3_adac_itf.
  //
  // This FSM sets the ahb_manager_sel to give control of the AHB manager to
  // the KSE CMD FSM, OTP to KSE FSM, or the Main command FSM itself.
  // If the control is given to a subordinate FSM, it will also issue an
  // operation request to it using a valid/ready handshake.
  //
  always_comb begin : main_jtag_cmd_fsm

    ahb_manager_sel           = AHB_MGR_COMMAND_FSM_IDX;
    kse_cmd_valid             = 1'b0;
    kse_cmd                   = soc_mgmt_hdata_t'(0);
    otp_to_kse_valid          = 1'b0;
    otp_to_kse_invert         = 1'b0;
    otp_to_kse_otp_start_addr = soc_mgmt_haddr_t'(0);
    otp_to_kse_kse_start_addr = soc_mgmt_haddr_t'(0);
    otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(0);
    jtag_cmd_state_d          = jtag_cmd_state_q;
    perso_str_len_d           = perso_str_len_q;
    anchor_len_d              = anchor_len_q;
    ca1_programmed_d          = ca1_programmed_q;
    o_tdr_ready               = 1'b0;
    jtag_cmd_kse_error        = 1'b0;
    jtag_cmd_ahb_error        = ahb_manager_error;
    jtag_cmd_ignored          = 1'b0;

    ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b0;
    ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = 1'b0;
    ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = soc_mgmt_haddr_t'(0);
    ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = soc_mgmt_hdata_t'(0);

    case (jtag_cmd_state_q)
      JTAG_CMD_IDLE: begin
        // Wait for OTP to read LCS and set i_lcs_valid before starting any operation.
        if (i_tdr_valid && i_lcs_valid) begin
          if (i_tdr_jtag_dbg && !i_lcs_is_terminated) begin
            // Allow enter_jtag_access_mode command.
            if (i_kse3_jtag_req.enter_jtag_access_mode) begin
              jtag_cmd_state_d = INIT_CMD_INITROT;
            // Allow OTP and AOR access.
            end else if (i_kse3_jtag_req.ahb_valid && (ahb_addr_is_otp || ahb_addr_is_aor)) begin
              ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
              ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwrite;
              ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = jtag_req_addr_extended;
              ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwdata;
              o_tdr_ready = ahb_manager_ready;
            end else begin
              o_tdr_ready = 1'b1;
              jtag_cmd_ignored = 1'b1;
            end
          end else begin
            // Ignore all JTAG commands when i_lcs_is_terminated or !i_tdr_jtag_dbg.
            o_tdr_ready = 1'b1;
            jtag_cmd_ignored = 1'b1;
          end
        end
      end
      INIT_CMD_INITROT: begin
        ahb_manager_sel = AHB_MGR_KSE_CMD_FSM_IDX;
        kse_cmd         = kudelski_kse3_pkg::KSE3_CMD_INITROT;
        kse_cmd_valid   = 1'b1;
        if (kse_cmd_ready) begin
          if (kse_ahb_error_d || kse_cmd_error_d) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                                    jtag_cmd_state_d = INIT_DRAM_PERSO_LEN;
        end
      end
      INIT_DRAM_PERSO_LEN: begin
        ahb_manager_sel = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_PERSO_STR_LEN_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_PERSO_STR_LEN_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_PERSO_STR_LEN_SIZE);
        if (otp_to_kse_ready) begin
          perso_str_len_d = otp_to_kse_tr_size_t'(otp_to_kse_rdata_q);
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_DRAM_TRNG_CONFIG;
        end
      end
      INIT_DRAM_TRNG_CONFIG: begin
        ahb_manager_sel = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_TRNG_CFG_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_TRNG_CFG_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_TRNG_CFG_SIZE);
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_DRAM_PERSO_STRING;
        end
      end
      INIT_DRAM_PERSO_STRING: begin
        ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_PERSO_STR_VAL_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_PERSO_STR_VAL_ADDR;
        otp_to_kse_tr_size        = perso_str_len_q;
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_CMD_INITCRYPTO;
        end
      end
      INIT_CMD_INITCRYPTO: begin
        ahb_manager_sel = AHB_MGR_KSE_CMD_FSM_IDX;
        kse_cmd         = kudelski_kse3_pkg::KSE3_CMD_INITCRYPTO;
        kse_cmd_valid   = 1'b1;
        if (kse_cmd_ready) begin
          if (kse_ahb_error_d || kse_cmd_error_d) begin
            jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          end else if (jtag_fully_open) begin
            jtag_cmd_state_d = JTAG_CMD_FULLY_OPEN;
            o_tdr_ready      = 1'b1;
          end else begin
            jtag_cmd_state_d = JTAG_CMD_KEEP_CLOSED;
            o_tdr_ready      = 1'b1;
          end
        end
      end
      JTAG_CMD_FULLY_OPEN: begin
        if (i_tdr_valid) begin
          if (i_kse3_jtag_req.ahb_valid) begin
            ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
            ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwrite;
            ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = jtag_req_addr_extended;
            ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwdata;
            o_tdr_ready = ahb_manager_ready;
          end else begin
            o_tdr_ready = 1'b1;
            jtag_cmd_ignored = 1'b1;
          end
        end
      end
      JTAG_CMD_KEEP_CLOSED: begin
        if (i_tdr_valid) begin
          if (i_kse3_jtag_req.init_kse3_adac_itf) begin
            jtag_cmd_state_d = INIT_ADAC_DRAM_CA_ANCHOR_LEN;
          // Allow OTP and AOR access.
          end else if (i_kse3_jtag_req.ahb_valid && (ahb_addr_is_otp || ahb_addr_is_aor)) begin
            ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
            ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwrite;
            ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = jtag_req_addr_extended;
            ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwdata;
            o_tdr_ready = ahb_manager_ready;
          end else begin
            o_tdr_ready = 1'b1;
            jtag_cmd_ignored = 1'b1;
          end
        end
      end
      INIT_ADAC_DRAM_CA_ANCHOR_LEN: begin
        ahb_manager_sel = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_ANCHOR_VAL_LEN_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_ANCHOR_VAL_LEN_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_ANCHOR_VAL_LEN_SIZE);
        if (otp_to_kse_ready) begin
          anchor_len_d = otp_to_kse_tr_size_t'(otp_to_kse_rdata_q);
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_ADAC_DRAM_CA_ANCHOR_VAL;
        end
      end
      INIT_ADAC_DRAM_CA_ANCHOR_VAL: begin
        ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_kse_start_addr = KSE3_DRAM_PERSO_STR_VAL_ADDR;
        otp_to_kse_tr_size        = anchor_len_q;
        if (!ca1_programmed_q) otp_to_kse_otp_start_addr = OTP_CA1_ANCHOR_VAL_ADDR;
        else                   otp_to_kse_otp_start_addr = OTP_CA2_ANCHOR_VAL_ADDR;
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_ADAC_DRAM_CA_TYPE_ID;
        end
      end
      INIT_ADAC_DRAM_CA_TYPE_ID: begin
        ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
        ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = KSE3_DRAM_SET_OBJ_TYPEID_ADDR;
        if (!ca1_programmed_q) ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = kudelski_kse3_pkg::KSE3_DRAM_CA1_AV_TYPEID_VAL;
        else                   ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = kudelski_kse3_pkg::KSE3_DRAM_CA2_AV_TYPEID_VAL;
        if (ahb_manager_ready) begin
          if (ahb_manager_error) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                   jtag_cmd_state_d = INIT_ADAC_CMD_SETOBJECT;
        end
      end
      INIT_ADAC_CMD_SETOBJECT: begin
        ahb_manager_sel = AHB_MGR_KSE_CMD_FSM_IDX;
        kse_cmd         = kudelski_kse3_pkg::KSE3_CMD_SETOBJECT;
        kse_cmd_valid   = 1'b1;
        if (kse_cmd_ready) begin
          if (ca1_programmed_q) begin
            // Ignore KSE3 errors on CA2 AnchorValue programming. This is because CA2 AnchorTag is
            // programmed in the OTP by the customer (CA2) and might not be available for early
            // lifecycle states (before User secured).
            if (kse_ahb_error_d) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
            else                 jtag_cmd_state_d = INIT_ADAC_DRAM_SOC_ID;
          end else begin
            ca1_programmed_d = 1'b1;
            jtag_cmd_state_d = INIT_ADAC_DRAM_CA_ANCHOR_LEN;
          end
        end
      end
      INIT_ADAC_DRAM_SOC_ID: begin
        ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_CHIP_ID_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_SOC_ID_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_CHIP_ID_SIZE);
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_ADAC_DRAM_SOC_ID_INV;
        end
      end
      INIT_ADAC_DRAM_SOC_ID_INV: begin
        ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_invert         = 1'b1;
        otp_to_kse_otp_start_addr = OTP_CHIP_ID_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_SOC_ID_INV_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_CHIP_ID_SIZE);
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_ADAC_DRAM_DBG_CNT;
        end
      end
      INIT_ADAC_DRAM_DBG_CNT: begin
        ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_DBG_COUNTER_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_DBG_COUNTER_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_DBG_COUNTER_SIZE);
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_ADAC_DRAM_DBG_CNT_INV;
        end
      end
      INIT_ADAC_DRAM_DBG_CNT_INV: begin
        INIT_ADAC_DRAM_DBG_CNT: begin
          ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
          otp_to_kse_valid          = 1'b1;
          otp_to_kse_invert         = 1'b1;
          otp_to_kse_otp_start_addr = OTP_DBG_COUNTER_ADDR;
          otp_to_kse_kse_start_addr = KSE3_DRAM_DBG_COUNTER_INV_ADDR;
          otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_DBG_COUNTER_SIZE);
          if (otp_to_kse_ready) begin
            if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
            else                    jtag_cmd_state_d = INIT_ADAC_DRAM_SOC_CLASS;
          end
        end
      end
      INIT_ADAC_DRAM_SOC_CLASS: begin
        ahb_manager_sel           = AHB_MGR_OTP_TO_KSE_FSM_IDX;
        otp_to_kse_valid          = 1'b1;
        otp_to_kse_otp_start_addr = OTP_SOC_CLASS_ADDR;
        otp_to_kse_kse_start_addr = KSE3_DRAM_SOC_CLASS_ADDR;
        otp_to_kse_tr_size        = otp_to_kse_tr_size_t'(otp_wrapper_pkg::OTP_SOC_CLASS_SIZE);
        if (otp_to_kse_ready) begin
          if (otp_to_kse_error_q) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else                    jtag_cmd_state_d = INIT_ADAC_CMD_SETSOCCONFIG;
        end
      end
      INIT_ADAC_CMD_SETSOCCONFIG: begin
        ahb_manager_sel = AHB_MGR_KSE_CMD_FSM_IDX;
        kse_cmd         = kudelski_kse3_pkg::KSE3_CMD_SETSOCCONFIG;
        kse_cmd_valid   = 1'b1;
        if (kse_cmd_ready) begin
          if (kse_ahb_error_d || kse_cmd_error_d) jtag_cmd_state_d = JTAG_CMD_ERROR_REPORT;
          else begin
            jtag_cmd_state_d = JTAG_CMD_ADAC_ONLY;
            o_tdr_ready      = 1'b1;
          end
        end
      end
      JTAG_CMD_ADAC_ONLY: begin
        if (i_tdr_valid) begin
          // Only KSE CMD allowed are GetChallenge and UnlockAccess.
          if (i_kse3_jtag_req.ahb_valid && (!ahb_access_is_kse3_cmd || ahb_access_is_getchallenge || ahb_access_is_unlockaccess)) begin
            ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
            ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwrite;
            ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = jtag_req_addr_extended;
            ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwdata;
            o_tdr_ready = ahb_manager_ready;
          end
          else begin
            o_tdr_ready = 1'b1;
            jtag_cmd_ignored = 1'b1;
          end
        end
      end
      JTAG_CMD_ERROR_REPORT: begin
        // KSE errors collected by KSE CMD FSM.
        jtag_cmd_kse_error = kse_cmd_error_q | kse_ahb_error_q;
        // AHB errors collected by AHB manager, KSE CMD FSM, OTP to KSE FSM.
        jtag_cmd_ahb_error = otp_to_kse_error_q | kse_ahb_error_q | ahb_manager_error;
        o_tdr_ready = 1'b1;
        jtag_cmd_state_d = JTAG_CMD_ERROR;
      end
      JTAG_CMD_ERROR: begin
        if (i_tdr_valid) begin
          // Don't allow new KSE3 commands.
          if (i_kse3_jtag_req.ahb_valid && !ahb_access_is_kse3_cmd) begin
            ahb_manager_mux_valid [AHB_MGR_COMMAND_FSM_IDX] = 1'b1;
            ahb_manager_mux_wr    [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwrite;
            ahb_manager_mux_addr  [AHB_MGR_COMMAND_FSM_IDX] = jtag_req_addr_extended;
            ahb_manager_mux_wdata [AHB_MGR_COMMAND_FSM_IDX] = i_kse3_jtag_req.ahb_hwdata;
            o_tdr_ready = ahb_manager_ready;
          end
          else begin
            o_tdr_ready = 1'b1;
            jtag_cmd_ignored = 1'b1;
          end
        end
      end
      default: /* Keep default values */;
    endcase

  end

  always_comb jtag_cmd_state_changed = jtag_cmd_state_d != jtag_cmd_state_q;

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n) begin
      jtag_cmd_state_q <= JTAG_CMD_IDLE;
      perso_str_len_q  <= otp_to_kse_tr_size_t'(0);
      anchor_len_q     <= otp_to_kse_tr_size_t'(0);
      ca1_programmed_q <= 1'b0;
    end else begin
      if (jtag_cmd_state_changed) begin
        jtag_cmd_state_q <= jtag_cmd_state_d;
        perso_str_len_q  <= perso_str_len_d;
        anchor_len_q     <= anchor_len_d;
        ca1_programmed_q <= ca1_programmed_d;
      end
    end
  end

  // ----------------------------------------------------------------------------
  // OTP to KSE FSM
  // ----------------------------------------------------------------------------
  //
  // This FSM is in charge of moving data from the OTP to the KSE3 DRAM.
  // It works using a valid/ready handshake with the Main command FSM.
  //
  // Inputs from Main command FSM
  //  - otp_to_kse_otp_start_addr: OTP start address for memory transfer
  //  - otp_to_kse_kse_start_addr: KSE3 DRAM start address for memory transfer
  //  - otp_to_kse_tr_size: Transfer size in bytes
  //  - otp_to_kse_invert: Perform 1's complement of the source data before writing
  //                       it to the destination.
  //
  // Outputs to Main command FSM
  //  - otp_to_kse_error_q: Set to 1 if at least one AHB transaction in the transfer
  //                        resulted in an AHB error response.
  //
  // Handshake signals
  //  - otp_to_kse_valid
  //  - otp_to_kse_ready.
  //
  always_comb begin : otp_to_kse_fsm

    otp_to_kse_otp_addr_d     = otp_to_kse_otp_addr_q;
    otp_to_kse_kse_addr_d     = otp_to_kse_kse_addr_q;
    otp_to_kse_kse_byte_cnt_d = otp_to_kse_kse_byte_cnt_q;
    otp_to_kse_state_d        = otp_to_kse_state_q;
    otp_to_kse_rdata_d        = otp_to_kse_rdata_q;
    otp_to_kse_error_d        = otp_to_kse_error_q;

    ahb_manager_mux_valid [AHB_MGR_OTP_TO_KSE_FSM_IDX] = 1'b0;
    ahb_manager_mux_wr    [AHB_MGR_OTP_TO_KSE_FSM_IDX] = 1'b0;
    ahb_manager_mux_addr  [AHB_MGR_OTP_TO_KSE_FSM_IDX] = soc_mgmt_haddr_t'(0);
    ahb_manager_mux_wdata [AHB_MGR_OTP_TO_KSE_FSM_IDX] = soc_mgmt_hdata_t'(0);

    otp_to_kse_ready = 1'b0;

    unique case (otp_to_kse_state_q)
      OTP_TO_KSE_IDLE: begin
        if (otp_to_kse_valid) begin
          otp_to_kse_state_d        = OTP_TO_KSE_READ;
          otp_to_kse_otp_addr_d     = otp_to_kse_otp_start_addr;
          otp_to_kse_kse_addr_d     = otp_to_kse_kse_start_addr;
          otp_to_kse_kse_byte_cnt_d = otp_to_kse_tr_size_t'(0);
          otp_to_kse_error_d        = 1'b0;
        end
      end
      OTP_TO_KSE_READ: begin
        ahb_manager_mux_valid [AHB_MGR_OTP_TO_KSE_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_OTP_TO_KSE_FSM_IDX] = otp_to_kse_otp_addr_q;
        if (ahb_manager_ready) begin
          if (ahb_manager_error) begin
            otp_to_kse_ready   = 1'b1;
            otp_to_kse_error_d = 1'b1;
            otp_to_kse_state_d = OTP_TO_KSE_IDLE;
          end
          else begin
            // Store read data for next cycle, update error information.
            if (otp_to_kse_invert) otp_to_kse_rdata_d = ~ahb_manager_rdata;
            else                   otp_to_kse_rdata_d =  ahb_manager_rdata;

            otp_to_kse_state_d = OTP_TO_KSE_WRITE;
          end
        end
      end
      OTP_TO_KSE_WRITE: begin
        ahb_manager_mux_valid [AHB_MGR_OTP_TO_KSE_FSM_IDX] = 1'b1;
        ahb_manager_mux_wr    [AHB_MGR_OTP_TO_KSE_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_OTP_TO_KSE_FSM_IDX] = otp_to_kse_kse_addr_q;
        ahb_manager_mux_wdata [AHB_MGR_OTP_TO_KSE_FSM_IDX] = otp_to_kse_rdata_q;
        if (ahb_manager_ready) begin
          if (ahb_manager_error) begin
            otp_to_kse_ready   = 1'b1;
            otp_to_kse_error_d = 1'b1;
            otp_to_kse_state_d = OTP_TO_KSE_IDLE;
          end
          else begin
            // Increment address and byte count by 4 since we write one word at a time.
            otp_to_kse_otp_addr_d     = otp_to_kse_otp_addr_q     + soc_mgmt_haddr_t'(4);
            otp_to_kse_kse_addr_d     = otp_to_kse_kse_addr_q     + soc_mgmt_haddr_t'(4);
            otp_to_kse_kse_byte_cnt_d = otp_to_kse_kse_byte_cnt_q + otp_to_kse_tr_size_t'(4);
            otp_to_kse_state_d        = OTP_TO_KSE_ADDR_EVAL;
          end
        end
      end
      OTP_TO_KSE_ADDR_EVAL: begin
        if (otp_to_kse_kse_byte_cnt_q < otp_to_kse_tr_size) begin
          otp_to_kse_state_d = OTP_TO_KSE_READ;
        end else begin
          otp_to_kse_ready   = 1'b1;
          otp_to_kse_state_d = OTP_TO_KSE_IDLE;
        end
      end
      default: /* Keep default values */ ;
    endcase

  end

  always_comb otp_to_kse_state_changed = otp_to_kse_state_d != otp_to_kse_state_q;

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n) begin
      otp_to_kse_otp_addr_q     <= soc_mgmt_haddr_t'(0);
      otp_to_kse_kse_addr_q     <= soc_mgmt_haddr_t'(0);
      otp_to_kse_kse_byte_cnt_q <= otp_to_kse_tr_size_t'(0);
      otp_to_kse_state_q        <= OTP_TO_KSE_IDLE;
      otp_to_kse_rdata_q        <= soc_mgmt_hdata_t'(0);
      otp_to_kse_error_q        <= 1'b0;
    end else begin
      if (otp_to_kse_state_changed) begin
        otp_to_kse_kse_byte_cnt_q <= otp_to_kse_kse_byte_cnt_d;
        otp_to_kse_error_q        <= otp_to_kse_error_d;
        otp_to_kse_rdata_q        <= otp_to_kse_rdata_d;
        otp_to_kse_otp_addr_q     <= otp_to_kse_otp_addr_d;
        otp_to_kse_kse_addr_q     <= otp_to_kse_kse_addr_d;
        otp_to_kse_state_q        <= otp_to_kse_state_d;
      end
    end
  end

  // ----------------------------------------------------------------------------
  // KSE cmd FSM
  // ----------------------------------------------------------------------------
  //
  // This FSM is in charge of sending one command to the KSE3 following these steps:
  //  1. KSE_CMD_POLL0: Poll KSE_CMD_CTRL until the start bit is 0 (meaning KSE3 is ready)
  //  2. KSE_CMD_SEND: Write the requested command to the KSE_CMD_CTRL register
  //  3. KSE_CMD_POLL1: Poll KSE_CMD_CTRL until the start bit is 0 (meaning KSE3 is ready)
  //  4. KSE_CMD_ERR_CHECK: Read KSE_CMD_STATUS and set the kse_cmd_error_d output if
  //                        different than SECIP_SUCCESS.
  //
  // It works using a valid/ready handshake with the Main command FSM.
  //
  // Inputs from Main command FSM
  //  - kse_cmd: KSE3 command to be written to KSE_CMD_CTRL.
  //
  // Outputs to Main command FSM
  //  - kse_ahb_error_d: Set to 1 if at least one AHB transaction in the transfer
  //                     resulted in an AHB error response.
  //  - kse_cmd_error_d: Set to 1 if KSE_CMD_STATUS != SECIP_SUCCESS meaning that
  //                     KSE3 failed to execute the requested command.
  //
  // Handshake signals
  //  - kse_cmd_valid
  //  - kse_cmd_ready.
  //
  // TODO (kluciani, consider adding a counter to limit the number of AHB reads during POLL states, will save power.)
  //
  always_comb begin : kse_cmd_fsm

    kse_ahb_error_d = kse_ahb_error_q;
    kse_cmd_error_d = kse_cmd_error_q;
    kse_cmd_state_d = kse_cmd_state_q;

    ahb_manager_mux_valid [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b0;
    ahb_manager_mux_wr    [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b0;
    ahb_manager_mux_addr  [AHB_MGR_KSE_CMD_FSM_IDX] = soc_mgmt_haddr_t'(0);
    ahb_manager_mux_wdata [AHB_MGR_KSE_CMD_FSM_IDX] = soc_mgmt_hdata_t'(0);

    kse_cmd_ready = 1'b0;

    unique case (kse_cmd_state_q)
      KSE_CMD_IDLE: begin
        if (kse_cmd_valid) begin
          kse_cmd_state_d = KSE_CMD_POLL0;
          kse_ahb_error_d = 1'b0;
          kse_cmd_error_d = 1'b0;
        end
      end
      KSE_CMD_POLL0: begin
        ahb_manager_mux_valid [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_KSE_CMD_FSM_IDX] = KSE3_CMD_CTRL_ADDR;
        if (ahb_manager_ready) begin
          if (ahb_manager_error) begin
            kse_ahb_error_d = 1'b1;
            kse_cmd_ready   = 1'b1;
            kse_cmd_state_d = KSE_CMD_IDLE;
          end else if (!ahb_manager_rdata[0]) begin
            kse_cmd_state_d = KSE_CMD_SEND;
          end
        end
      end
      KSE_CMD_SEND: begin
        ahb_manager_mux_valid [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b1;
        ahb_manager_mux_wr    [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_KSE_CMD_FSM_IDX] = KSE3_CMD_CTRL_ADDR;
        ahb_manager_mux_wdata [AHB_MGR_KSE_CMD_FSM_IDX] = kse_cmd;
        if (ahb_manager_ready) begin
          if (ahb_manager_error) begin
            kse_ahb_error_d = 1'b1;
            kse_cmd_ready   = 1'b1;
            kse_cmd_state_d = KSE_CMD_IDLE;
          end else begin
            kse_cmd_state_d = KSE_CMD_POLL1;
          end
        end
      end
      KSE_CMD_POLL1: begin
        ahb_manager_mux_valid [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_KSE_CMD_FSM_IDX] = KSE3_CMD_CTRL_ADDR;
        if (ahb_manager_ready) begin
          if (ahb_manager_error) begin
            kse_ahb_error_d = 1'b1;
            kse_cmd_ready   = 1'b1;
            kse_cmd_state_d = KSE_CMD_IDLE;
          end else if (!ahb_manager_rdata[0]) begin
            kse_cmd_state_d = KSE_CMD_ERR_CHECK;
          end
        end
      end
      KSE_CMD_ERR_CHECK: begin
        ahb_manager_mux_valid [AHB_MGR_KSE_CMD_FSM_IDX] = 1'b1;
        ahb_manager_mux_addr  [AHB_MGR_KSE_CMD_FSM_IDX] = KSE3_CMD_STATUS_ADDR;
        if (ahb_manager_ready) begin
          kse_ahb_error_d = kse_ahb_error_q | ahb_manager_error;
          kse_cmd_error_d = ahb_manager_rdata != kudelski_kse3_pkg::KSE3_CMD_STATUS_SUCCESS;
          kse_cmd_ready = 1'b1;
          kse_cmd_state_d = KSE_CMD_IDLE;
        end
      end
      default: /* Keep default values */ ;
    endcase

  end

  always_comb kse_cmd_state_changed = kse_cmd_state_d != kse_cmd_state_q;

  always_ff @( posedge i_clk or negedge i_rst_n ) begin
    if (!i_rst_n) begin
      kse_cmd_state_q <= KSE_CMD_IDLE;
      kse_ahb_error_q <= 1'b0;
      kse_cmd_error_q <= 1'b0;
    end else begin
      if (kse_cmd_state_changed) begin
        kse_cmd_state_q <= kse_cmd_state_d;
        kse_ahb_error_q <= kse_ahb_error_d;
        kse_cmd_error_q <= kse_cmd_error_d;
      end
    end
  end

  // ----------------------------------------------------------------------------
  // AHB manager input muxing
  // ----------------------------------------------------------------------------
  always_comb begin

    ahb_manager_valid = ahb_manager_mux_valid [ahb_manager_sel];
    ahb_manager_wr    = ahb_manager_mux_wr    [ahb_manager_sel];
    ahb_manager_addr  = ahb_manager_mux_addr  [ahb_manager_sel];
    ahb_manager_wdata = ahb_manager_mux_wdata [ahb_manager_sel];

  end

  // ----------------------------------------------------------------------------
  // AHB manager
  // ----------------------------------------------------------------------------
  axe_ahb_manager #(
    .HAW  (SOC_MGMT_HAW),
    .HDW  (SOC_MGMT_HDW)
  )
  u_axe_ahb_manager (
    .i_clk           (i_clk),
    .i_rst_n         (i_rst_n),
    .o_ahb_m_haddr   (o_ahb_m_haddr),
    .o_ahb_m_hwrite  (o_ahb_m_hwrite),
    .o_ahb_m_hwdata  (o_ahb_m_hwdata),
    .o_ahb_m_htrans  (o_ahb_m_htrans),
    .o_ahb_m_hburst  (o_ahb_m_hburst),
    .o_ahb_m_hsize   (o_ahb_m_hsize),
    .i_ahb_m_hrdata  (i_ahb_m_hrdata),
    .i_ahb_m_hready  (i_ahb_m_hready),
    .i_ahb_m_hresp   (i_ahb_m_hresp),
    .i_valid         (ahb_manager_valid),
    .i_wr            (ahb_manager_wr),
    .i_addr          (ahb_manager_addr),
    .i_wdata         (ahb_manager_wdata),
    .o_rdata         (ahb_manager_rdata),
    .o_error         (ahb_manager_error),
    .o_ready         (ahb_manager_ready)
  );

  // Response to TDR
  always_comb o_kse3_jtag_resp = '{
    ahb_hrdata:   ahb_manager_rdata,
    kse_error:    jtag_cmd_kse_error,
    ahb_error:    jtag_cmd_ahb_error,
    cmd_ignored:  jtag_cmd_ignored
  };

endmodule
