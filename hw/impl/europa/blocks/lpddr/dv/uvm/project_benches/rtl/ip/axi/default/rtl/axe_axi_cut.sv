// Copyright (c) 2014-2018 ETH Zurich, University of Bologna
//
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
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// An AXI4 cut.
///
/// Breaks all combinatorial paths between its input and output.
module axe_axi_cut #(
  // bypass enable
  parameter bit CutAw = 1'b1,
  parameter bit CutW  = 1'b1,
  parameter bit CutB  = 1'b1,
  parameter bit CutAr = 1'b1,
  parameter bit CutR  = 1'b1,
  // AXI channel structs
  parameter type  axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type  axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type  axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type  axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type  axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  input  wire     i_clk,
  input  wire     i_rst_n,

  input  axi_aw_t i_axi_s_aw,
  input  logic    i_axi_s_aw_valid,
  output logic    o_axi_s_aw_ready,
  input  axi_w_t  i_axi_s_w,
  input  logic    i_axi_s_w_valid,
  output logic    o_axi_s_w_ready,
  output axi_b_t  o_axi_s_b,
  output logic    o_axi_s_b_valid,
  input  logic    i_axi_s_b_ready,
  input  axi_ar_t i_axi_s_ar,
  input  logic    i_axi_s_ar_valid,
  output logic    o_axi_s_ar_ready,
  output axi_r_t  o_axi_s_r,
  output logic    o_axi_s_r_valid,
  input  logic    i_axi_s_r_ready,

  output axi_aw_t o_axi_m_aw,
  output logic    o_axi_m_aw_valid,
  input  logic    i_axi_m_aw_ready,
  output axi_w_t  o_axi_m_w,
  output logic    o_axi_m_w_valid,
  input  logic    i_axi_m_w_ready,
  input  axi_b_t  i_axi_m_b,
  input  logic    i_axi_m_b_valid,
  output logic    o_axi_m_b_ready,
  output axi_ar_t o_axi_m_ar,
  output logic    o_axi_m_ar_valid,
  input  logic    i_axi_m_ar_ready,
  input  axi_r_t  i_axi_m_r,
  input  logic    i_axi_m_r_valid,
  output logic    o_axi_m_r_ready
);

  // a spill register for each channel
  cc_stream_spill_reg #(
    .data_t(axi_aw_t),
    .Bypass(!CutAw)
  ) u_reg_aw (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_axi_s_aw),
    .i_valid(i_axi_s_aw_valid),
    .o_ready(o_axi_s_aw_ready),
    .o_data (o_axi_m_aw),
    .o_valid(o_axi_m_aw_valid),
    .i_ready(i_axi_m_aw_ready)
  );

  cc_stream_spill_reg #(
    .data_t(axi_w_t),
    .Bypass(!CutW)
  ) u_reg_w (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_axi_s_w),
    .i_valid(i_axi_s_w_valid),
    .o_ready(o_axi_s_w_ready),
    .o_data (o_axi_m_w),
    .o_valid(o_axi_m_w_valid),
    .i_ready(i_axi_m_w_ready)
  );

  cc_stream_spill_reg #(
    .data_t(axi_b_t),
    .Bypass(!CutB)
  ) u_reg_b  (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_axi_m_b),
    .i_valid(i_axi_m_b_valid),
    .o_ready(o_axi_m_b_ready),
    .o_data (o_axi_s_b),
    .o_valid(o_axi_s_b_valid),
    .i_ready(i_axi_s_b_ready)
  );

  cc_stream_spill_reg #(
    .data_t(axi_ar_t),
    .Bypass(!CutAr)
  ) u_reg_ar (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_axi_s_ar),
    .i_valid(i_axi_s_ar_valid),
    .o_ready(o_axi_s_ar_ready),
    .o_data (o_axi_m_ar),
    .o_valid(o_axi_m_ar_valid),
    .i_ready(i_axi_m_ar_ready)
  );

  cc_stream_spill_reg #(
    .data_t(axi_r_t),
    .Bypass(!CutR)
  ) u_reg_r  (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_axi_m_r),
    .i_valid(i_axi_m_r_valid),
    .o_ready(o_axi_m_r_ready),
    .o_data (o_axi_s_r),
    .o_valid(o_axi_s_r_valid),
    .i_ready(i_axi_s_r_ready)
  );
endmodule
