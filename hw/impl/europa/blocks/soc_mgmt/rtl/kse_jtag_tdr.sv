// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: KSE JTAG TDR wrapper
// Implements glue logic for CSR/JTAG compatiblity and instantiates the TDR core
// Interface upstream with KSE3 JTAG TAP, downstream with secure_enclave
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

module kse_jtag_tdr
  import soc_mgmt_pkg::*;
  import rot_pkg::*;
#(
  parameter int unsigned SyncStages = 3
)(
  input  wire             i_clk,
  input  logic            i_ao_rst_n,
  // JTAG
  input  wire             tcki,
  input  logic            trsti,
  // TDR interface
  output logic            o_tdr_jtag_dbg,
  output kse3_jtag_req_t  o_kse3_jtag_req,
  input  kse3_jtag_resp_t i_kse3_jtag_resp,
  output logic            o_tdr_valid,
  input  logic            i_tdr_ready
);

  kse3_jtag_req_t                 jtag_req_data, jtag_req_data_sync;
  kse3_jtag_resp_t                jtag_resp_data_sync;
  logic                           jtag_ready;
  logic                           jtag_transaction_id_d, jtag_transaction_id_q;

  logic                           jtag_cmd_ready_q;
  logic                           jtag_req_pulse;
  logic                           jtag_req_pulse_sync;
  logic                           jtag_req_valid_q;
  logic                           jtag_req_sync_busy;
  logic                           jtag_resp_pulse;
  logic                           jtag_resp_pulse_sync;
  logic                           jtag_resp_sync_busy;

  kse_jtag_tdr_core u_kse_jtag_tdr_core (
    .o_ahb_haddr              (jtag_req_data.ahb_haddr),
    .o_ahb_hwdata             (jtag_req_data.ahb_hwdata),
    .o_ahb_hwrite             (jtag_req_data.ahb_hwrite),
    .o_ahb_valid              (jtag_req_data.ahb_valid),
    .o_enter_jtag_access_mode (jtag_req_data.enter_jtag_access_mode),
    .o_init_kse3_adac_itf     (jtag_req_data.init_kse3_adac_itf),
    .o_jtag_dbg               (o_tdr_jtag_dbg),
    .o_transaction_id         (jtag_transaction_id_d),
    .i_ahb_hrdata             (jtag_resp_data_sync.ahb_hrdata),
    .i_jtag_ready             (jtag_ready),
    .i_jtag_kse_error         (jtag_resp_data_sync.kse_error),
    .i_jtag_ahb_error         (jtag_resp_data_sync.ahb_error),
    .i_jtag_cmd_ignored       (jtag_resp_data_sync.cmd_ignored)
  );



  // instruction_id signal toggle is used as qualifier for JTAG request synchronization.
  always_ff @(posedge tcki, negedge trsti) begin
    if (!trsti) begin
      jtag_transaction_id_q <= 1'b0;
    end else begin
      jtag_transaction_id_q <= jtag_transaction_id_d;
    end
  end

  // Ignore new command if a previous JTAG operation is still ongoing.
  always_comb jtag_req_pulse = jtag_ready & (jtag_transaction_id_d ^ jtag_transaction_id_q);

  // --------------------------------------------------------------------------
  // CDC from TDR (tcki) to HW (i_clk)
  // --------------------------------------------------------------------------

  // Command sync jtag clock -> secure_enclave clock
  // Note that this uses always-on reset i_ao_rst_n to avoid spourious
  // o_dst_update pulses on warm reset.
  axe_ccl_cdc_bus #(
    .SyncStages     (SyncStages),
    .data_t         (kse3_jtag_req_t)
  )
  u_tdr2hw_resync
  (
    .i_src_clk    (tcki),
    .i_src_rst_n  (trsti),
    .i_src_en     (jtag_req_pulse),
    .i_src_data   (jtag_req_data),
    .o_src_busy   (jtag_req_sync_busy),
    .i_dst_clk    (i_clk),
    .i_dst_rst_n  (i_ao_rst_n),
    .o_dst_data   (o_kse3_jtag_req),
    .o_dst_update (jtag_req_pulse_sync)
  );

  // Valid bit in i_clk domain.
  // Works in always-on domain so that JTAG requests during warm reset are not lost.
  always_ff @(posedge i_clk, negedge i_ao_rst_n) begin
    if (!i_ao_rst_n) begin
      jtag_req_valid_q <= 1'b0;
    end else begin
      if (jtag_req_pulse_sync) jtag_req_valid_q <= 1'b1;              // New request synchronized: Set valid
      else if (i_tdr_ready)    jtag_req_valid_q <= 1'b0;              // New response pulse: Clear valid
      else                     jtag_req_valid_q <= jtag_req_valid_q;  // Keep previous value
    end
  end

  // Don't send out a valid request while previous HW to TDR CDC is busy.
  always_comb o_tdr_valid = jtag_req_valid_q & ~jtag_resp_sync_busy;

  // --------------------------------------------------------------------------
  // CDC from HW (i_clk) to TDR (tcki)
  // --------------------------------------------------------------------------
  always_comb jtag_resp_pulse = o_tdr_valid & i_tdr_ready;

  // Note that this uses always-on reset i_ao_rst_n to avoid spourious
  // o_dst_update pulses on warm reset.
  axe_ccl_cdc_bus #(
    .SyncStages   (SyncStages),
    .data_t       (kse3_jtag_resp_t)
    ) u_hw2tdr_resync (
    .i_src_clk    (i_clk),
    .i_src_rst_n  (i_ao_rst_n),
    .i_src_en     (jtag_resp_pulse),
    .i_src_data   (i_kse3_jtag_resp),
    .o_src_busy   (jtag_resp_sync_busy),
    .i_dst_clk    (tcki),
    .i_dst_rst_n  (trsti),
    .o_dst_data   (jtag_resp_data_sync),
    .o_dst_update (jtag_resp_pulse_sync)
  );

  // Ready bit in tcki domain.
  always_ff @(posedge tcki, negedge trsti) begin
    if (!trsti) begin
      jtag_cmd_ready_q <= 1'b1;
    end else begin
      if (jtag_req_pulse)            jtag_cmd_ready_q <= 1'b0;             // New valid JTAG command issued: Clear ready
      else if (jtag_resp_pulse_sync) jtag_cmd_ready_q <= 1'b1;             // Response synchronized: Set ready
      else                           jtag_cmd_ready_q <= jtag_cmd_ready_q; // Keep previous value
    end
  end

  // Keep jtag_ready low while TDR to HW CDC is busy.
  always_comb jtag_ready = jtag_cmd_ready_q & ~jtag_req_sync_busy;

endmodule
