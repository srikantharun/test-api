// Copyright 2019 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.
//
// Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

// AXI ID Prepend: This module prepends/strips the MSB from the AXI IDs.
// Constraints enforced through assertions: ID width of subordinate and manager port

module axe_axi_id_prepend #(
  /// The difference between the ID fields
  parameter int unsigned IdWidthDifference =
      axe_axi_default_types_pkg::WIDTH_ID_5-axe_axi_default_types_pkg::WIDTH_ID_4,
  parameter logic [IdWidthDifference-1:0] PrependId = '0,
  parameter type axi_s_aw_t     = axe_axi_default_types_pkg::axi_aw_4_40_4_t, // AW Channel Type for sub port
  parameter type axi_s_w_t      = axe_axi_default_types_pkg::axi_w_64_8_4_t,  //  W Channel Type for sub port
  parameter type axi_s_b_t      = axe_axi_default_types_pkg::axi_b_4_4_t,     //  B Channel Type for sub port
  parameter type axi_s_ar_t     = axe_axi_default_types_pkg::axi_ar_4_40_4_t, // AR Channel Type for sub port
  parameter type axi_s_r_t      = axe_axi_default_types_pkg::axi_r_4_64_4_t,  //  R Channel Type for sub port
  parameter type axi_m_aw_t     = axe_axi_default_types_pkg::axi_aw_5_40_4_t, // AW Channel Type for man port
  parameter type axi_m_w_t      = axe_axi_default_types_pkg::axi_w_64_8_4_t,  //  W Channel Type for man port
  parameter type axi_m_b_t      = axe_axi_default_types_pkg::axi_b_5_4_t,     //  B Channel Type for man port
  parameter type axi_m_ar_t     = axe_axi_default_types_pkg::axi_ar_5_40_4_t, // AR Channel Type for man port
  parameter type axi_m_r_t      = axe_axi_default_types_pkg::axi_r_5_64_4_t   //  R Channel Type for man port
)(
  // AW channel
  input  axi_s_aw_t i_axi_s_aw,
  input  logic      i_axi_s_aw_valid,
  output logic      o_axi_s_aw_ready,
  //  W channel
  input  axi_s_w_t  i_axi_s_w,
  input  logic      i_axi_s_w_valid,
  output logic      o_axi_s_w_ready,
  //  B channel
  output axi_s_b_t  o_axi_s_b,
  output logic      o_axi_s_b_valid,
  input  logic      i_axi_s_b_ready,
  // AR channel
  input  axi_s_ar_t i_axi_s_ar,
  input  logic      i_axi_s_ar_valid,
  output logic      o_axi_s_ar_ready,
  //  R channel
  output axi_s_r_t  o_axi_s_r,
  output logic      o_axi_s_r_valid,
  input  logic      i_axi_s_r_ready,
  // AW channel
  output axi_m_aw_t o_axi_m_aw,
  output logic      o_axi_m_aw_valid,
  input  logic      i_axi_m_aw_ready,
  //  W channel
  output axi_m_w_t  o_axi_m_w,
  output logic      o_axi_m_w_valid,
  input  logic      i_axi_m_w_ready,
  //  B channel
  input  axi_m_b_t  i_axi_m_b,
  input  logic      i_axi_m_b_valid,
  output logic      o_axi_m_b_ready,
  // AR channel
  output axi_m_ar_t o_axi_m_ar,
  output logic      o_axi_m_ar_valid,
  input  logic      i_axi_m_ar_ready,
  //  R channel
  input  axi_m_r_t  i_axi_m_r,
  input  logic      i_axi_m_r_valid,
  output logic      o_axi_m_r_ready
);

  /////////////////////
  // Type validation //
  /////////////////////
  if (IdWidthDifference != ($bits(o_axi_m_aw.id) - $bits(i_axi_s_aw.id)))
      $fatal(1, "IdWidthDifference: Not matching fields AW; is: %d M_AW: %d S_AW: %d",
      IdWidthDifference, $bits(o_axi_m_aw.id), $bits(i_axi_s_aw.id));
  if (IdWidthDifference != ($bits(i_axi_m_b.id) - $bits(o_axi_s_b.id)))
      $fatal(1, "IdWidthDifference: Not matching fields B; is: %d M_B: %d S_B: %d",
      IdWidthDifference, $bits(i_axi_m_b.id), $bits(o_axi_s_b.id));
  if (IdWidthDifference != ($bits(o_axi_m_ar.id) - $bits(i_axi_s_ar.id)))
      $fatal(1, "IdWidthDifference: Not matching fields AR; is: %d M_AR: %d S_AR: %d",
      IdWidthDifference, $bits(o_axi_m_ar.id), $bits(i_axi_s_ar.id));
  if (IdWidthDifference != ($bits(i_axi_m_r.id) - $bits(o_axi_s_r.id)))
      $fatal(1, "IdWidthDifference: Not matching fields R; is: %d M_R: %d S_R: %d",
      IdWidthDifference, $bits(i_axi_m_r.id), $bits(o_axi_s_r.id));

  if ($bits(o_axi_m_aw.id) < $bits(i_axi_s_aw.id))
      $fatal(1, "The manager AXI port has to have a wider ID than the subordinate port.");
  if ($bits(i_axi_m_b.id) < $bits(o_axi_s_b.id))
      $fatal(1, "The manager AXI port has to have a wider ID than the subordinate port.");
  if ($bits(o_axi_m_ar.id) < $bits(i_axi_s_ar.id))
      $fatal(1, "The manager AXI port has to have a wider ID than the subordinate port.");
  if ($bits(i_axi_m_r.id) < $bits(o_axi_s_r.id))
      $fatal(1, "The manager AXI port has to have a wider ID than the subordinate port.");

  always_comb begin
    o_axi_m_aw = i_axi_s_aw;
    if (IdWidthDifference > 0) o_axi_m_aw.id = {PrependId, i_axi_s_aw.id};
  end

  always_comb begin
    o_axi_m_ar = i_axi_s_ar;
    if (IdWidthDifference > 0) o_axi_m_ar.id = {PrependId, i_axi_s_ar.id};
  end

  // W feedthrough
  always_comb o_axi_m_w = i_axi_s_w;

  // The ID is in the highest bits of the struct, so an assignment from a channel with a wide ID
  // to a channel with a shorter ID correctly cuts the prepended ID.
  always_comb o_axi_s_b = i_axi_m_b;
  always_comb o_axi_s_r = i_axi_m_r;

  // Handshaking assign
  always_comb o_axi_m_aw_valid = i_axi_s_aw_valid;
  always_comb o_axi_s_aw_ready = i_axi_m_aw_ready;
  always_comb o_axi_m_w_valid  = i_axi_s_w_valid;
  always_comb o_axi_s_w_ready  = i_axi_m_w_ready;
  always_comb o_axi_s_b_valid  = i_axi_m_b_valid;
  always_comb o_axi_m_b_ready  = i_axi_s_b_ready;
  always_comb o_axi_m_ar_valid = i_axi_s_ar_valid;
  always_comb o_axi_s_ar_ready = i_axi_m_ar_ready;
  always_comb o_axi_s_r_valid  = i_axi_m_r_valid;
  always_comb o_axi_m_r_ready  = i_axi_s_r_ready;
endmodule
