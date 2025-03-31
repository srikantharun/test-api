// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// Generic APB demux.
/// Connects a single APB master to multiple subordinates.
/// Decoding logic handled externally.
module axe_apb_demux #(
  /// Number of APB managers
  parameter int  unsigned NB_APBOUT         = 3,
  /// Width definition for APB address bus
  parameter int  unsigned PAW               = 16,
  /// Width definition for APB data bus
  parameter int  unsigned PDW               = 32,
  /// Width definition for APB strobe bus
  parameter int  unsigned PSTRBW            = 4,
  /// Width definition for APB subordinate index
  parameter int  unsigned IDXW              = 2,
  /// Index of the default subordinate (0 to NB_APBOUT-1)
  parameter int  unsigned DEFAULT_SUB_IDX   = 2,
  /// APB address type
  parameter type  paddr_t                   = logic [PAW       -1:0],
  /// APB data type
  parameter type  pdata_t                   = logic [PDW       -1:0],
  /// APB strobe type
  parameter type  pstrb_t                   = logic [PSTRBW    -1:0],
  /// APB subordinate index type
  parameter type  idx_t                     = logic [IDXW      -1:0]
)(
  /// Clock, positive edge triggered
  input  wire                         i_clk,
  /// Asynchronous reset, active low
  input  wire                         i_rst_n,
  ///////////////////////////////////////////////////
  /// APB subordinate interface (input interface) ///
  ///////////////////////////////////////////////////
  input  paddr_t                      i_apb_s_paddr,
  input  pdata_t                      i_apb_s_pwdata,
  input  logic                        i_apb_s_pwrite,
  input  logic                        i_apb_s_psel,
  input  logic                        i_apb_s_penable,
  input  pstrb_t                      i_apb_s_pstrb,
  input  axe_apb_pkg::apb_prot_t      i_apb_s_pprot,
  output logic                        o_apb_s_pready,
  output pdata_t                      o_apb_s_prdata,
  output logic                        o_apb_s_pslverr,
  /////////////////////////////////////////////////
  /// APB master interfaces (output interfaces) ///
  /////////////////////////////////////////////////
  output paddr_t                      o_apb_m_paddr[NB_APBOUT],
  output pdata_t                      o_apb_m_pwdata[NB_APBOUT],
  output logic                        o_apb_m_pwrite[NB_APBOUT],
  output logic                        o_apb_m_psel[NB_APBOUT],
  output logic                        o_apb_m_penable[NB_APBOUT],
  output pstrb_t                      o_apb_m_pstrb[NB_APBOUT],
  output axe_apb_pkg::apb_prot_t      o_apb_m_pprot[NB_APBOUT],
  input  logic                        i_apb_m_pready[NB_APBOUT],
  input  pdata_t                      i_apb_m_prdata[NB_APBOUT],
  input  logic                        i_apb_m_pslverr[NB_APBOUT],
  // Selected subordinate from address decoder
  input  idx_t                        i_sub_idx_from_dec
);

// ----------------------------------------------------------------------------
// signal declarations
// ----------------------------------------------------------------------------
idx_t sub_idx;

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------

// Select the default subordinate if i_sub_idx_from_dec is out of the allowed range
assign sub_idx = (i_sub_idx_from_dec < NB_APBOUT) ? i_sub_idx_from_dec : DEFAULT_SUB_IDX;

// Signals to APB subordinates
always_comb begin
  for (int unsigned i=0; i<NB_APBOUT; i++) begin
    o_apb_m_penable [i] = (i == sub_idx) & i_apb_s_penable;
    o_apb_m_psel    [i] = (i == sub_idx) & i_apb_s_psel;
    // Signals that go to all subordinates
    o_apb_m_paddr   [i] = i_apb_s_paddr;
    o_apb_m_pwdata  [i] = i_apb_s_pwdata;
    o_apb_m_pwrite  [i] = i_apb_s_pwrite;
    o_apb_m_pstrb   [i] = i_apb_s_pstrb;
    o_apb_m_pprot   [i] = i_apb_s_pprot;
  end
end

// Signals to the APB master
always_comb begin
  o_apb_s_pready   = i_apb_m_pready  [sub_idx];
  o_apb_s_prdata   = i_apb_m_prdata  [sub_idx];
  o_apb_s_pslverr  = i_apb_m_pslverr [sub_idx];
end

endmodule
