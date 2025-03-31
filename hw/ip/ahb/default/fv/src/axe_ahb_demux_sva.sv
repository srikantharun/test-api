// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

module axe_ahb_demux_sva
import axe_ahb_pkg::*;
#(
  /// number of AHB managers
  parameter int  unsigned NB_AHBOUT         = 3,
  /// width definition for AHB subordinate index
  parameter int  unsigned IDXW              = 2,
  /// width definition for AHB address bus
  parameter int  unsigned HAW               = 16,
  /// width definition for AHB data bus
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
  ////////////////////////////////////////////////
  // AHB manager interfaces (output interfaces) //
  ////////////////////////////////////////////////
  input  idx_t                    i_ahb_s_select,
  input  hdata_t                  i_ahb_m_hrdata[NB_AHBOUT],
  input  logic                    i_ahb_m_hready[NB_AHBOUT],
  input  logic                    i_ahb_m_hresp[NB_AHBOUT]
);
  // =====================================================
  // Local parameters
  // =====================================================

  // =====================================================
  // Type definition
  // =====================================================

  // =====================================================
  // Signal declarations
  // =====================================================

  // =====================================================
  // Bind signals
  // =====================================================

  // =====================================================
  // Properties
  // =====================================================

  // =====================================================
  // Assumes
  // =====================================================
  assume_decoder_idx_stable_addr : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    $stable(i_ahb_s_haddr) |-> $stable(i_ahb_s_select)
  );

  assume_decoder_idx_stable_trans : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    (i_ahb_s_htrans != htrans_e'(NONSEQ)) |-> $stable(i_ahb_s_select)
  );


  // =====================================================
  // Assertions
  // =====================================================

  // =====================================================
  // Covers
  // =====================================================

endmodule
