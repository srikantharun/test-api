// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

module axe_ahb_manager_sva
import axe_ahb_pkg::*;
#(
  // width definition for AHB address bus
  parameter int  unsigned HAW               = 5           ,
  // width definition for AHB data bus
  parameter int  unsigned HDW               = 32           ,
  // AHB types
  parameter type          haddr_t       = logic [HAW -1:0] ,
  parameter type          hdata_t       = logic [HDW -1:0]
)(
  // Clock, positive edge triggered
  input  wire                 i_clk                 ,
  // Asynchronous reset, active low
  input  wire                 i_rst_n               ,
  // AHB manager interface
  input  haddr_t              o_ahb_m_haddr         ,
  input  logic                o_ahb_m_hwrite        ,
  input  hdata_t              o_ahb_m_hwdata        ,
  input  htrans_e             o_ahb_m_htrans        ,
  input  hburst_e             o_ahb_m_hburst        ,
  input  hsize_e              o_ahb_m_hsize         ,
  input  hdata_t              i_ahb_m_hrdata        ,
  input  logic                i_ahb_m_hready        ,
  input  logic                i_ahb_m_hresp         ,
  // I/f to requestor
  input  logic                i_valid               ,
  input  logic                i_wr                  ,
  input  haddr_t              i_addr                ,
  input  hdata_t              i_wdata
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
  // Incoming HADDR is word-aligned
  assume_haddr_aligned : assume property (
    @(posedge i_clk) disable iff (!i_rst_n)
    i_addr[1:0] == 2'b00
  );

  // =====================================================
  // Assertions
  // =====================================================

  // =====================================================
  // Covers
  // =====================================================

endmodule
