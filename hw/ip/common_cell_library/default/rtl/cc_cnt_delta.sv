// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Counter up or down with configurable delta
///
// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Up/down counter with variable delta

module cc_cnt_delta #(
  parameter int unsigned Width = 4,
  parameter bit StickyOverflow = 1'b0
)(
  input  wire              i_clk,
  input  wire              i_rst_n,
  input  logic             i_flush,    // synchronous clear
  input  logic             i_cnt_en,   // enable the counter
  input  logic             i_cnt_down, // downcount, default is up
  input  logic [Width-1:0] i_delta,
  output logic [Width-1:0] o_q,
  input  logic [Width-1:0] i_d,
  input  logic             i_d_load,   // load a new value
  output logic             o_overflow
);
  `ifdef AXE_CCL_DEPRECATION_WARNING
  $warning("AXE_CCL: `cc_cnt_delta` is deprecated, use `axe_ccl_cnt_delta` instead!");
  `endif

  logic overflow;
  logic underflow;

  axe_ccl_cnt_delta #(
    .Width         (Width),
    .StickyOverflow(StickyOverflow)
  ) u_axe_ccl_cnt_delta (
    .i_clk,
    .i_rst_n,
    .i_flush,
    .i_enable   (i_cnt_en),
    .i_decrement(i_cnt_down),
    .i_delta,
    .o_count    (o_q),
    .i_value    (i_d),
    .i_overwrite(i_d_load),
    .o_overflow (overflow),
    .o_underflow(underflow)
  );

  always_comb o_overflow = overflow | underflow;
endmodule
