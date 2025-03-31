// Copyright (c) 2014-2019 ETH Zurich, University of Bologna
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Fabian Schuiki <fschuiki@iis.ee.ethz.ch>
// - Stefan Mach <smach@iis.ee.ethz.ch>

// Multiple AXI4 cuts.
//
// These can be used to relax timing pressure on very long AXI busses.
module axe_axi_multicut #(
  parameter int unsigned NumCuts = 32'd1, // Number of cuts.
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
  // instantiate all needed cuts
  axi_aw_t cut_aw[NumCuts+1];
  logic    cut_aw_valid[NumCuts+1];
  logic    cut_aw_ready[NumCuts+1];
  axi_w_t  cut_w[NumCuts+1];
  logic    cut_w_valid[NumCuts+1];
  logic    cut_w_ready[NumCuts+1];
  axi_b_t  cut_b[NumCuts+1];
  logic    cut_b_valid[NumCuts+1];
  logic    cut_b_ready[NumCuts+1];
  axi_ar_t cut_ar[NumCuts+1];
  logic    cut_ar_valid[NumCuts+1];
  logic    cut_ar_ready[NumCuts+1];
  axi_r_t  cut_r[NumCuts+1];
  logic    cut_r_valid[NumCuts+1];
  logic    cut_r_ready[NumCuts+1];

  // connect subordinate to the lowest index
  always_comb  cut_aw[0]        = i_axi_s_aw;
  always_comb  cut_aw_valid[0]  = i_axi_s_aw_valid;
  always_comb  o_axi_s_aw_ready = cut_aw_ready[0];
  always_comb  cut_w[0]         = i_axi_s_w;
  always_comb  cut_w_valid[0]   = i_axi_s_w_valid;
  always_comb  o_axi_s_w_ready  = cut_w_ready[0];
  always_comb  o_axi_s_b        = cut_b[0];
  always_comb  o_axi_s_b_valid  = cut_b_valid[0];
  always_comb  cut_b_ready[0]   = i_axi_s_b_ready;
  always_comb  cut_ar[0]        = i_axi_s_ar;
  always_comb  cut_ar_valid[0]  = i_axi_s_ar_valid;
  always_comb  o_axi_s_ar_ready = cut_ar_ready[0];
  always_comb  o_axi_s_r        = cut_r[0];
  always_comb  o_axi_s_r_valid  = cut_r_valid[0];
  always_comb  cut_r_ready[0]   = i_axi_s_r_ready;

  // AXI cuts
  for (genvar i = 0; i < NumCuts; i++) begin : gen_axi_cuts
    axe_axi_cut #(
      .CutAw   (1'b1),
      .CutW    (1'b1),
      .CutB    (1'b1),
      .CutAr   (1'b1),
      .CutR    (1'b1),
      .axi_aw_t(axi_aw_t),
      .axi_w_t (axi_w_t),
      .axi_b_t (axi_b_t),
      .axi_ar_t(axi_ar_t),
      .axi_r_t (axi_r_t)
    ) u_axi_cut (
      .i_clk,
      .i_rst_n,
      .i_axi_s_aw      (cut_aw[i]),
      .i_axi_s_aw_valid(cut_aw_valid[i]),
      .o_axi_s_aw_ready(cut_aw_ready[i]),
      .i_axi_s_w       (cut_w[i]),
      .i_axi_s_w_valid (cut_w_valid[i]),
      .o_axi_s_w_ready (cut_w_ready[i]),
      .o_axi_s_b       (cut_b[i]),
      .o_axi_s_b_valid (cut_b_valid[i]),
      .i_axi_s_b_ready (cut_b_ready[i]),
      .i_axi_s_ar      (cut_ar[i]),
      .i_axi_s_ar_valid(cut_ar_valid[i]),
      .o_axi_s_ar_ready(cut_ar_ready[i]),
      .o_axi_s_r       (cut_r[i]),
      .o_axi_s_r_valid (cut_r_valid[i]),
      .i_axi_s_r_ready (cut_r_ready[i]),
      .o_axi_m_aw      (cut_aw[i+1]),
      .o_axi_m_aw_valid(cut_aw_valid[i+1]),
      .i_axi_m_aw_ready(cut_aw_ready[i+1]),
      .o_axi_m_w       (cut_w[i+1]),
      .o_axi_m_w_valid (cut_w_valid[i+1]),
      .i_axi_m_w_ready (cut_w_ready[i+1]),
      .i_axi_m_b       (cut_b[i+1]),
      .i_axi_m_b_valid (cut_b_valid[i+1]),
      .o_axi_m_b_ready (cut_b_ready[i+1]),
      .o_axi_m_ar      (cut_ar[i+1]),
      .o_axi_m_ar_valid(cut_ar_valid[i+1]),
      .i_axi_m_ar_ready(cut_ar_ready[i+1]),
      .i_axi_m_r       (cut_r[i+1]),
      .i_axi_m_r_valid (cut_r_valid[i+1]),
      .o_axi_m_r_ready (cut_r_ready[i+1])
    );
  end

  // connect manager to the highest index
  always_comb o_axi_m_aw            = cut_aw[NumCuts];
  always_comb o_axi_m_aw_valid      = cut_aw_valid[NumCuts];
  always_comb cut_aw_ready[NumCuts] = i_axi_m_aw_ready;
  always_comb o_axi_m_w             = cut_w[NumCuts];
  always_comb o_axi_m_w_valid       = cut_w_valid[NumCuts];
  always_comb cut_w_ready[NumCuts]  = i_axi_m_w_ready;
  always_comb cut_b[NumCuts]        = i_axi_m_b;
  always_comb cut_b_valid[NumCuts]  = i_axi_m_b_valid;
  always_comb o_axi_m_b_ready       = cut_b_ready[NumCuts];
  always_comb o_axi_m_ar            = cut_ar[NumCuts];
  always_comb o_axi_m_ar_valid      = cut_ar_valid[NumCuts];
  always_comb cut_ar_ready[NumCuts] = i_axi_m_ar_ready;
  always_comb cut_r[NumCuts]        = i_axi_m_r;
  always_comb cut_r_valid[NumCuts]  = i_axi_m_r_valid;
  always_comb o_axi_m_r_ready       = cut_r_ready[NumCuts];
endmodule
