// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

/// Generic AHB demux
/// Connects a single AHB manager to multiple subordinates
/// Decoding logic handled externally
module axe_ahb_demux
  import axe_ahb_pkg::*;
#(
  /// Number of AHB managers
  parameter int  unsigned NB_AHBOUT         = 3,
  /// Width definition for AHB subordinate index
  parameter int  unsigned IDXW              = 2,
  /// Width definition for AHB address bus
  parameter int  unsigned HAW               = 16,
  /// Width definition for AHB data bus
  parameter int  unsigned HDW               = 32,
  /// AHB types
  parameter  type         haddr_t           = logic [HAW       -1:0],
  parameter  type         hdata_t           = logic [HDW       -1:0],
  localparam type         idx_t             = logic [IDXW      -1:0]
)(
  /// Clock, positive edge triggered
  input  wire                     i_clk,
  /// Asynchronous reset, active low
  input  wire                     i_rst_n,
  /////////////////////////////////////////////////
  // AHB subordinate interface (input interface) //
  /////////////////////////////////////////////////
  input  haddr_t                  i_ahb_s_haddr,
  input  logic                    i_ahb_s_hwrite,
  input  hdata_t                  i_ahb_s_hwdata,
  input  htrans_e                 i_ahb_s_htrans,
  input  hburst_e                 i_ahb_s_hburst,
  input  hsize_e                  i_ahb_s_hsize,
  output hdata_t                  o_ahb_s_hrdata,
  /// This HREADY should be connected to each subordinate's HREADY input
  output logic                    o_ahb_s_hready,
  output logic                    o_ahb_s_hresp,
  ////////////////////////////////////////////////
  // AHB manager interfaces (output interfaces) //
  ////////////////////////////////////////////////
  input  idx_t                    i_ahb_s_select,
  output haddr_t                  o_ahb_m_haddr[NB_AHBOUT],
  output logic                    o_ahb_m_hwrite[NB_AHBOUT],
  output hdata_t                  o_ahb_m_hwdata[NB_AHBOUT],
  output htrans_e                 o_ahb_m_htrans[NB_AHBOUT],
  output hburst_e                 o_ahb_m_hburst[NB_AHBOUT],
  output hsize_e                  o_ahb_m_hsize[NB_AHBOUT],
  output logic                    o_ahb_m_hsel[NB_AHBOUT],
  input  hdata_t                  i_ahb_m_hrdata[NB_AHBOUT],
  /// This HREADY should be connected to subordinates' HREADYOUT output
  input  logic                    i_ahb_m_hready[NB_AHBOUT],
  input  logic                    i_ahb_m_hresp[NB_AHBOUT]
);

// ----------------------------------------------------------------------------
// signal declarations
// ----------------------------------------------------------------------------
idx_t slv_idx_clamped;
idx_t slv_idx_q;
logic new_transaction;

// -----------------------------------------------------------------------------
// RTL
// -----------------------------------------------------------------------------
// Select the last subordinate if i_ahb_s_select >= NB_AHBOUT
always_comb slv_idx_clamped = (i_ahb_s_select < NB_AHBOUT) ? i_ahb_s_select : NB_AHBOUT-1;
always_comb new_transaction = o_ahb_s_hready && (i_ahb_s_htrans == NONSEQ);

// i_ahb_s_select is combinatorial decoding of i_ahb_s_haddr.
// Sample i_ahb_s_select only during a valid address phase.
// slv_idx_q will be valid throughout the transaction's data phase.
always_ff @(posedge i_clk or negedge i_rst_n) begin
  if (!i_rst_n) begin
    slv_idx_q <= '0;
  end else begin
    if (new_transaction) begin
      slv_idx_q <= slv_idx_clamped;
    end
  end
end

// Signals to AHB subordinates
always_comb begin
  for (int i=0; i<NB_AHBOUT; i=i+1) begin
    // Signals that go to all subordinates
    // Set everything to constant values to non-selected subordinates,
    // this will save switching power when multiple transactions are meant
    // for the same subordinate.
    o_ahb_m_haddr   [i] = (i == slv_idx_clamped) ? i_ahb_s_haddr  : '0;
    o_ahb_m_hwrite  [i] = (i == slv_idx_clamped) ? i_ahb_s_hwrite : 1'b0;
    o_ahb_m_htrans  [i] = (i == slv_idx_clamped) ? i_ahb_s_htrans : IDLE;
    o_ahb_m_hburst  [i] = (i == slv_idx_clamped) ? i_ahb_s_hburst : SINGLE;
    o_ahb_m_hsize   [i] = (i == slv_idx_clamped) ? i_ahb_s_hsize  : BYTE;
    // Data-phase signals
    o_ahb_m_hwdata  [i] = (i == slv_idx_q)       ? i_ahb_s_hwdata : '0;
  end

  // HSEL has the same timing as HADDR: Address phase
  for (int i=0; i<NB_AHBOUT; i=i+1) begin
    o_ahb_m_hsel    [i] = (i == slv_idx_clamped);
  end
end

// Signals to the AHB manager: Data phase
always_comb begin
  o_ahb_s_hready   = i_ahb_m_hready  [slv_idx_q];
  o_ahb_s_hrdata   = i_ahb_m_hrdata  [slv_idx_q];
  o_ahb_s_hresp    = i_ahb_m_hresp   [slv_idx_q];
end

endmodule
