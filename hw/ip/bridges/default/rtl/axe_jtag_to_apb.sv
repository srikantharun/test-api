// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Andrew Dickson <andrew.dickson@axelera.ai>

// JTAG_TO_APB
// Includes DW_tap IP for the tap controller.
// Uses tap controller instruction for APB address. 16bit
// And tap shift_dr state to transfer data.

module axe_jtag_to_apb #(
  // width definition for APB address bus
  parameter int  unsigned PAW = 16,
  // width definition for APB data bus
  parameter int  unsigned PDW = 32,
  // width definition for APB strobe bus
  parameter int  unsigned PSTRBW = 4,
  parameter int unsigned  SyncStages = 2,
  // APB types
  parameter type          paddr_t    = logic [PAW    -1:0],
  parameter type          pdata_t    = logic [PDW    -1:0],
  parameter type          pstrb_t    = logic [PSTRBW -1:0]
)(
  // Clock, positive edge triggered
  input  wire                         i_clk,
  // Asynchronous warm reset, active low
  input  wire                         i_rst_n,
  // Asynchronous cold reset, active low
  input  wire                         i_ao_rst_n,
  // JTAG interface
  input  wire                         tcki,
  input  wire                         trsti,
  // APB master interface
  output paddr_t                      o_apb_m_paddr,
  output pdata_t                      o_apb_m_pwdata,
  output logic                        o_apb_m_pwrite,
  output logic                        o_apb_m_psel,
  output logic                        o_apb_m_penable,
  output pstrb_t                      o_apb_m_pstrb,
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot,
  input  logic                        i_apb_m_pready,
  input  pdata_t                      i_apb_m_prdata,
  input  logic                        i_apb_m_pslverr
);

  // Set write strobe for all byte lanes
  localparam pstrb_t                 PSTRB_VAL = '1;
  localparam axe_apb_pkg::apb_prot_t PPROT_VAL = 3'h2;

  paddr_t          apb_paddr;
  pdata_t          apb_pwdata;
  pstrb_t          apb_pstrb;
  logic            apb_pwrite;
  pdata_t          apb_prdata;
  logic            apb_pslverr;
  logic            tdr_valid;
  logic            tdr_ready;

  axe_jtag_to_apb_tdr #(
    .PAW        (PAW),
    .PDW        (PDW),
    .SyncStages (SyncStages)
  ) u_axe_jtag_to_apb_tdr (
    .i_clk,
    .i_ao_rst_n,
    // JTAG
    .tcki,
    .trsti,
    // APB manager interface
    .o_apb_paddr   (apb_paddr),
    .o_apb_pwdata  (apb_pwdata),
    .o_apb_pwrite  (apb_pwrite),
    .i_apb_prdata  (apb_prdata),
    .i_apb_pslverr (apb_pslverr),
    .o_tdr_valid   (tdr_valid),
    .i_tdr_ready   (tdr_ready)
  );

  //==============================================================================
  // APB master
  axe_apb_manager #(
    .PAW    (PAW),
    .PDW    (PDW),
    .PSTRBW (PSTRBW)
  ) u_apb_manager (
    .i_clk,
    .i_rst_n,
    .o_apb_m_paddr,
    .o_apb_m_pwdata,
    .o_apb_m_pwrite,
    .o_apb_m_psel,
    .o_apb_m_penable,
    .o_apb_m_pstrb,
    .o_apb_m_pprot,
    .i_apb_m_pready,
    .i_apb_m_prdata,
    .i_apb_m_pslverr,
    .i_apb_valid      (tdr_valid),
    .i_apb_wr_req     (apb_pwrite),
    .i_apb_address    (apb_paddr),
    .i_apb_wdata      (apb_pwdata),
    .i_apb_pstrb      (PSTRB_VAL),
    .i_apb_pprot      (PPROT_VAL),
    .o_apb_ready      (tdr_ready),
    .o_apb_rdata      (apb_prdata),
    .o_apb_error      (apb_pslverr)
  );

endmodule
