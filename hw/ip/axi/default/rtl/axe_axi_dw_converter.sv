// Copyright 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

// NOTE: The upsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type. In addition to that, the downsizer also
// does not support FIXED bursts with incoming axlen != 0.

module axe_axi_dw_converter #(
  /// ID width of both subordinate and manager port
  parameter int unsigned AxiIdWidth          = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Address width of both subordinate and manager port
  parameter int unsigned AxiAddrWidth        = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Datawidth of the subordinate port
  parameter int unsigned AxiSubPortDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_512,
  /// Datawidth of the manager port
  parameter int unsigned AxiManPortDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// The number of parallel outstanding reads the converteer can do at a given time.
  parameter int unsigned AxiMaxReads         = 4,
  /// The actual slice width of a transaction ID that determines the uniques of an ID.
  /// This directly translates to the amount of counters instanziated:
  /// `(2**AxiIdUsedWidth) * NumSubPorts`
  /// Note: This parameter might change in the future.
  parameter int unsigned AxiIdUsedWidth = AxiIdWidth,

  parameter type  axi_aw_t  = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type  axi_s_w_t = axe_axi_default_types_pkg::axi_w_512_64_4_t,
  parameter type  axi_m_w_t = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type  axi_b_t   = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type  axi_ar_t  = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type  axi_s_r_t = axe_axi_default_types_pkg::axi_r_4_512_4_t,
  parameter type  axi_m_r_t = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_aw_t  i_axi_s_aw,
  input  logic     i_axi_s_aw_valid,
  output logic     o_axi_s_aw_ready,
  input  axi_s_w_t i_axi_s_w,
  input  logic     i_axi_s_w_valid,
  output logic     o_axi_s_w_ready,
  output axi_b_t   o_axi_s_b,
  output logic     o_axi_s_b_valid,
  input  logic     i_axi_s_b_ready,
  input  axi_ar_t  i_axi_s_ar,
  input  logic     i_axi_s_ar_valid,
  output logic     o_axi_s_ar_ready,
  output axi_s_r_t o_axi_s_r,
  output logic     o_axi_s_r_valid,
  input  logic     i_axi_s_r_ready,

  //////////////////
  // Manager port //
  //////////////////
  output axi_aw_t  o_axi_m_aw,
  output logic     o_axi_m_aw_valid,
  input  logic     i_axi_m_aw_ready,
  output axi_m_w_t o_axi_m_w,
  output logic     o_axi_m_w_valid,
  input  logic     i_axi_m_w_ready,
  input  axi_b_t   i_axi_m_b,
  input  logic     i_axi_m_b_valid,
  output logic     o_axi_m_b_ready,
  output axi_ar_t  o_axi_m_ar,
  output logic     o_axi_m_ar_valid,
  input  logic     i_axi_m_ar_ready,
  input  axi_m_r_t i_axi_m_r,
  input  logic     i_axi_m_r_valid,
  output logic     o_axi_m_r_ready
);

  if (AxiManPortDataWidth == AxiSubPortDataWidth) begin: gen_no_dw_conversion
    if ($bits(i_axi_s_aw) != $bits(o_axi_m_aw)) $fatal(1, "Width of AW ports don't match!");
    if ($bits(i_axi_s_w)  != $bits(o_axi_m_w))  $fatal(1, "Width of  W ports don't match!");
    if ($bits(o_axi_s_b)  != $bits(i_axi_m_b))  $fatal(1, "Width of  B ports don't match!");
    if ($bits(i_axi_s_ar) != $bits(o_axi_m_ar)) $fatal(1, "Width of AR ports don't match!");
    if ($bits(o_axi_s_r)  != $bits(i_axi_m_r))  $fatal(1, "Width of  R ports don't match!");

    assign o_axi_m_aw       = i_axi_s_aw;
    assign o_axi_m_aw_valid = i_axi_s_aw_valid;
    assign o_axi_s_aw_ready = i_axi_m_aw_ready;

    assign o_axi_m_w        = i_axi_s_w;
    assign o_axi_m_w_valid  = i_axi_s_w_valid;
    assign o_axi_s_w_ready  = i_axi_m_w_ready;

    assign o_axi_s_b        = i_axi_m_b;
    assign o_axi_s_b_valid  = i_axi_m_b_valid;
    assign o_axi_m_b_ready  = i_axi_s_b_ready;

    assign o_axi_m_ar       = i_axi_s_ar;
    assign o_axi_m_ar_valid = i_axi_s_ar_valid;
    assign o_axi_s_ar_ready = i_axi_m_ar_ready;

    assign o_axi_s_r        = i_axi_m_r;
    assign o_axi_s_r_valid  = i_axi_m_r_valid;
    assign o_axi_m_r_ready  = i_axi_s_r_ready;
  end : gen_no_dw_conversion

  if (AxiManPortDataWidth > AxiSubPortDataWidth) begin: gen_dw_upsize
    axe_axi_dw_upsizer #(
      .AxiIdWidth         (AxiIdWidth),
      .AxiAddrWidth       (AxiAddrWidth),
      .AxiSubPortDataWidth(AxiSubPortDataWidth),
      .AxiManPortDataWidth(AxiManPortDataWidth),
      .AxiMaxReads        (AxiMaxReads),
      .AxiIdUsedWidth     (AxiIdUsedWidth),
      .axi_aw_t           (axi_aw_t),
      .axi_s_w_t          (axi_s_w_t),
      .axi_m_w_t          (axi_m_w_t),
      .axi_b_t            (axi_b_t),
      .axi_ar_t           (axi_ar_t),
      .axi_s_r_t          (axi_s_r_t),
      .axi_m_r_t          (axi_m_r_t)
    ) u_axi_dw_upsizer (
      .i_clk,
      .i_rst_n,
      .i_axi_s_aw,
      .i_axi_s_aw_valid,
      .o_axi_s_aw_ready,
      .i_axi_s_w,
      .i_axi_s_w_valid,
      .o_axi_s_w_ready,
      .o_axi_s_b,
      .o_axi_s_b_valid,
      .i_axi_s_b_ready,
      .i_axi_s_ar,
      .i_axi_s_ar_valid,
      .o_axi_s_ar_ready,
      .o_axi_s_r,
      .o_axi_s_r_valid,
      .i_axi_s_r_ready,
      .o_axi_m_aw,
      .o_axi_m_aw_valid,
      .i_axi_m_aw_ready,
      .o_axi_m_w,
      .o_axi_m_w_valid,
      .i_axi_m_w_ready,
      .i_axi_m_b,
      .i_axi_m_b_valid,
      .o_axi_m_b_ready,
      .o_axi_m_ar,
      .o_axi_m_ar_valid,
      .i_axi_m_ar_ready,
      .i_axi_m_r,
      .i_axi_m_r_valid,
      .o_axi_m_r_ready
    );
  end : gen_dw_upsize

  if (AxiManPortDataWidth < AxiSubPortDataWidth) begin: gen_dw_downsize
    axe_axi_dw_downsizer #(
      .AxiIdWidth         (AxiIdWidth),
      .AxiAddrWidth       (AxiAddrWidth),
      .AxiSubPortDataWidth(AxiSubPortDataWidth),
      .AxiManPortDataWidth(AxiManPortDataWidth),
      .AxiMaxReads        (AxiMaxReads),
      .AxiIdUsedWidth     (AxiIdUsedWidth),
      .axi_aw_t           (axi_aw_t),
      .axi_s_w_t          (axi_s_w_t),
      .axi_m_w_t          (axi_m_w_t),
      .axi_b_t            (axi_b_t),
      .axi_ar_t           (axi_ar_t),
      .axi_s_r_t          (axi_s_r_t),
      .axi_m_r_t          (axi_m_r_t)
    ) u_axi_dw_downsizer (
      .i_clk,
      .i_rst_n,
      .i_axi_s_aw,
      .i_axi_s_aw_valid,
      .o_axi_s_aw_ready,
      .i_axi_s_w,
      .i_axi_s_w_valid,
      .o_axi_s_w_ready,
      .o_axi_s_b,
      .o_axi_s_b_valid,
      .i_axi_s_b_ready,
      .i_axi_s_ar,
      .i_axi_s_ar_valid,
      .o_axi_s_ar_ready,
      .o_axi_s_r,
      .o_axi_s_r_valid,
      .i_axi_s_r_ready,
      .o_axi_m_aw,
      .o_axi_m_aw_valid,
      .i_axi_m_aw_ready,
      .o_axi_m_w,
      .o_axi_m_w_valid,
      .i_axi_m_w_ready,
      .i_axi_m_b,
      .i_axi_m_b_valid,
      .o_axi_m_b_ready,
      .o_axi_m_ar,
      .o_axi_m_ar_valid,
      .i_axi_m_ar_ready,
      .i_axi_m_r,
      .i_axi_m_r_valid,
      .o_axi_m_r_ready
    );
  end : gen_dw_downsize

endmodule : axe_axi_dw_converter
