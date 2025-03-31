// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Original Authors:
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>

/// Modify addresses on an AXI4 bus
///
/// This module assumes first ID followed by address on the AW and AR structs
module axe_axi_modify_address #(
  /// Type of manager port address to modify
  parameter type  axi_m_addr_t = axe_axi_default_types_pkg::axi_addr_40_t,
  // AXI channel structs
  parameter type  axi_s_aw_t   = axe_axi_default_types_pkg::axi_aw_4_64_4_t,
  parameter type  axi_m_aw_t   = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type  axi_w_t      = axe_axi_default_types_pkg::axi_w_512_64_4_t,
  parameter type  axi_b_t      = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type  axi_s_ar_t   = axe_axi_default_types_pkg::axi_ar_4_64_4_t,
  parameter type  axi_m_ar_t   = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type  axi_r_t      = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_s_aw_t   i_axi_s_aw,
  input  axi_m_addr_t i_axi_s_aw_addr,  // Modified address
  input  logic        i_axi_s_aw_valid,
  output logic        o_axi_s_aw_ready,
  input  axi_w_t      i_axi_s_w,
  input  logic        i_axi_s_w_valid,
  output logic        o_axi_s_w_ready,
  output axi_b_t      o_axi_s_b,
  output logic        o_axi_s_b_valid,
  input  logic        i_axi_s_b_ready,
  input  axi_s_ar_t   i_axi_s_ar,
  input  axi_m_addr_t i_axi_s_ar_addr,  // Modified address
  input  logic        i_axi_s_ar_valid,
  output logic        o_axi_s_ar_ready,
  output axi_r_t      o_axi_s_r,
  output logic        o_axi_s_r_valid,
  input  logic        i_axi_s_r_ready,

  //////////////////
  // Manager port //
  //////////////////
  output axi_m_aw_t   o_axi_m_aw,
  output logic        o_axi_m_aw_valid,
  input  logic        i_axi_m_aw_ready,
  output axi_w_t      o_axi_m_w,
  output logic        o_axi_m_w_valid,
  input  logic        i_axi_m_w_ready,
  input  axi_b_t      i_axi_m_b,
  input  logic        i_axi_m_b_valid,
  output logic        o_axi_m_b_ready,
  output axi_m_ar_t   o_axi_m_ar,
  output logic        o_axi_m_ar_valid,
  input  logic        i_axi_m_ar_ready,
  input  axi_r_t      i_axi_m_r,
  input  logic        i_axi_m_r_valid,
  output logic        o_axi_m_r_ready
);
  ///////////////////////////
  // Parameter Sanitations //
  ///////////////////////////
  if ($bits(i_axi_s_aw.id)   != $bits(o_axi_m_aw.id))   $fatal(1, "Port: '$bits(i_axi_s_aw.id)' != $bits(o_axi_m_aw.id);");
  if ($bits(i_axi_s_ar.id)   != $bits(o_axi_m_ar.id))   $fatal(1, "Port: '$bits(i_axi_s_ar.id)' != $bits(o_axi_m_ar.id);");
  if ($bits(i_axi_s_aw_addr) != $bits(o_axi_m_aw.addr)) $fatal(1, "Port: '$bits(i_axi_s_aw_addr)' != $bits(o_axi_m_aw.addr);");
  if ($bits(i_axi_s_ar_addr) != $bits(o_axi_m_ar.addr)) $fatal(1, "Port: '$bits(i_axi_s_ar_addr)' != $bits(o_axi_m_ar.addr);");

  ////////
  // AW //
  ////////
  // Note, this only wors if ID and address are on top of the struct
  always_comb begin
    o_axi_m_aw      = i_axi_s_aw;
    o_axi_m_aw.id   = i_axi_s_aw.id;
    o_axi_m_aw.addr = i_axi_s_aw_addr;
  end
  always_comb o_axi_m_aw_valid = i_axi_s_aw_valid;
  always_comb o_axi_s_aw_ready = i_axi_m_aw_ready;

  ////////
  // W  //
  ////////
  always_comb o_axi_m_w       = i_axi_s_w;
  always_comb o_axi_m_w_valid = i_axi_s_w_valid;
  always_comb o_axi_s_w_ready = i_axi_m_w_ready;

  ////////
  // B  //
  ////////
  always_comb o_axi_s_b       = i_axi_m_b;
  always_comb o_axi_s_b_valid = i_axi_m_b_valid;
  always_comb o_axi_m_b_ready = i_axi_s_b_ready;

  ////////
  // AR //
  ////////
  // Note, this only wors if ID and address are on top of the struct
  always_comb begin
    o_axi_m_ar      = i_axi_s_ar;
    o_axi_m_ar.id   = i_axi_s_ar.id;
    o_axi_m_ar.addr = i_axi_s_ar_addr;
  end
  always_comb o_axi_m_ar_valid = i_axi_s_ar_valid;
  always_comb o_axi_s_ar_ready = i_axi_m_ar_ready;

  ////////
  // R  //
  ////////
  always_comb o_axi_s_r       = i_axi_m_r;
  always_comb o_axi_s_r_valid = i_axi_m_r_valid;
  always_comb o_axi_m_r_ready = i_axi_s_r_ready;

endmodule
