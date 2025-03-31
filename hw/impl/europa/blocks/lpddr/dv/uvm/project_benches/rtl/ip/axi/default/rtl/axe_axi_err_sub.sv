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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>

/// AXI Error Subordinate: This module always responds with an AXI error for transactions that are sent to
/// it.  This module optionally supports ATOPs if the `SupportAtops` parameter is set.
///
module axe_axi_err_sub #(
  /// The ID width of the Transaction
  parameter int unsigned          AxiIdWidth   = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// The error code that is generated by this module
  parameter axi_pkg::axi_resp_e   Resp         = axi_pkg::RespDecErr,
  /// Data width to define the response value
  parameter int unsigned          DataWidth    = 64,
  // Data response, gets zero extended or truncated to r.data.
  parameter logic [DataWidth-1:0] ReadData     = 64'hCA11AB1E_BAD_CAB1E,
  // Maximum # of accepted transactions before stalling
  parameter int unsigned          MaxTxn       = 1,
  // Activate support for ATOP transactions, instantiates a axe_atop_filter at module port
  parameter bit                   SupportAtops = 1'b1,
  parameter type axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  /// Clock, positive edge triggered
  input wire i_clk,
  /// Asynchronous reset, active low
  // doc async
  input wire i_rst_n,
  // doc sync i_clk

  // Subordinate port
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
  input  logic    i_axi_s_r_ready
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (AxiIdWidth != $bits(i_axi_s_aw.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match aw.id;");

  typedef logic [AxiIdWidth-1:0] id_t;
  typedef struct packed {
    id_t               id;
    axi_pkg::axi_len_t len;
  } r_data_t;

  axi_aw_t axi_err_aw;
  logic    axi_err_aw_valid;
  logic    axi_err_aw_ready;
  axi_w_t  axi_err_w;
  logic    axi_err_w_valid;
  logic    axi_err_w_ready;
  axi_b_t  axi_err_b;
  logic    axi_err_b_valid;
  logic    axi_err_b_ready;
  axi_ar_t axi_err_ar;
  logic    axi_err_ar_valid;
  logic    axi_err_ar_ready;
  axi_r_t  axi_err_r;
  logic    axi_err_r_valid;
  logic    axi_err_r_ready;

  if (SupportAtops) begin : gen_atop
    axe_axi_atop_filter #(
      .AxiIdWidth     (AxiIdWidth),
      .AxiMaxWriteTxns(MaxTxn),
      .axi_aw_t       (axi_aw_t),
      .axi_w_t        (axi_w_t),
      .axi_b_t        (axi_b_t),
      .axi_ar_t       (axi_ar_t),
      .axi_r_t        (axi_r_t)
    ) u_atop_filter (
      .i_clk,
      .i_rst_n,

      .i_axi_s_aw      (i_axi_s_aw),
      .i_axi_s_aw_valid(i_axi_s_aw_valid),
      .o_axi_s_aw_ready(o_axi_s_aw_ready),
      .i_axi_s_w       (i_axi_s_w),
      .i_axi_s_w_valid (i_axi_s_w_valid),
      .o_axi_s_w_ready (o_axi_s_w_ready),
      .o_axi_s_b       (o_axi_s_b),
      .o_axi_s_b_valid (o_axi_s_b_valid),
      .i_axi_s_b_ready (i_axi_s_b_ready),
      .i_axi_s_ar      (i_axi_s_ar),
      .i_axi_s_ar_valid(i_axi_s_ar_valid),
      .o_axi_s_ar_ready(o_axi_s_ar_ready),
      .o_axi_s_r       (o_axi_s_r),
      .o_axi_s_r_valid (o_axi_s_r_valid),
      .i_axi_s_r_ready (i_axi_s_r_ready),

      .o_axi_m_aw      (axi_err_aw),
      .o_axi_m_aw_valid(axi_err_aw_valid),
      .i_axi_m_aw_ready(axi_err_aw_ready),
      .o_axi_m_w       (axi_err_w),
      .o_axi_m_w_valid (axi_err_w_valid),
      .i_axi_m_w_ready (axi_err_w_ready),
      .i_axi_m_b       (axi_err_b),
      .i_axi_m_b_valid (axi_err_b_valid),
      .o_axi_m_b_ready (axi_err_b_ready),
      .o_axi_m_ar      (axi_err_ar),
      .o_axi_m_ar_valid(axi_err_ar_valid),
      .i_axi_m_ar_ready(axi_err_ar_ready),
      .i_axi_m_r       (axi_err_r),
      .i_axi_m_r_valid (axi_err_r_valid),
      .o_axi_m_r_ready (axi_err_r_ready)
    );

  end else begin : gen_no_atop
    always_comb begin
      axi_err_aw       = i_axi_s_aw;
      axi_err_aw_valid = i_axi_s_aw_valid;
      o_axi_s_aw_ready = axi_err_aw_ready;
      axi_err_w        = i_axi_s_w;
      axi_err_w_valid  = i_axi_s_w_valid;
      o_axi_s_w_ready  = axi_err_w_ready;
      o_axi_s_b        = axi_err_b;
      o_axi_s_b_valid  = axi_err_b_valid;
      axi_err_b_ready  = i_axi_s_b_ready;
      axi_err_ar       = i_axi_s_ar;
      axi_err_ar_valid = i_axi_s_ar_valid;
      o_axi_s_ar_ready = axi_err_ar_ready;
      o_axi_s_r        = axi_err_r;
      o_axi_s_r_valid  = axi_err_r_valid;
      axi_err_r_ready  = i_axi_s_r_ready;
    end
  end

  // w fifo
  logic    w_fifo_full, w_fifo_empty;
  logic    w_fifo_push, w_fifo_pop;
  id_t     w_fifo_data;
  // b fifo
  // The ready valid is the input handshaking to the fifo
  logic    b_fifo_valid, b_fifo_ready;
  id_t     b_fifo_data;
  // r fifo
  r_data_t r_fifo_inp;
  logic    r_fifo_full, r_fifo_empty;
  logic    r_fifo_push, r_fifo_pop;
  r_data_t r_fifo_data;
  // r counter
  logic              r_cnt_clear, r_cnt_en, r_cnt_load;
  axi_pkg::axi_len_t r_current_beat;
  // r status
  logic    r_busy_d, r_busy_q, r_busy_load;

  ////////////////////////
  // Write Transactions //
  ////////////////////////
  // push, when there is room in the fifo
  assign w_fifo_push      = axi_err_aw_valid & ~w_fifo_full;
  assign axi_err_aw_ready = ~w_fifo_full;

  // TODO(@wolfgang.roenninger): Replace with cc_stream_fifo or equivalent
  fifo_v3 #(
    .FALL_THROUGH(1'b1),
    .DEPTH       (MaxTxn),
    .dtype_t     (id_t)
  ) i_w_fifo (
    .i_clk,
    .i_rst_n,
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .full_o    (w_fifo_full),
    .empty_o   (w_fifo_empty),
    .usage_o   (/*open*/),
    .data_i    (axi_err_aw.id),
    .push_i    (w_fifo_push),
    .data_o    (w_fifo_data),
    .pop_i     (w_fifo_pop)
  );

  always_comb begin : proc_w_channel
    axi_err_w_ready = 1'b0;
    w_fifo_pop      = 1'b0;
    b_fifo_valid    = 1'b0;
    // We can do listen to the redy as it is a spill register
    if (!w_fifo_empty && b_fifo_ready) begin
      // eat the beats
      axi_err_w_ready = 1'b1;
      // on the last w transaction
      if (axi_err_w_valid && axi_err_w.last) begin
        w_fifo_pop   = 1'b1;
        b_fifo_valid = 1'b1;
      end
    end
  end

  cc_stream_spill_reg #(
    .data_t(id_t),
    .Bypass(1'b0)
  ) u_b_fifo(
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (w_fifo_data),
    .i_valid(b_fifo_valid),
    .o_ready(b_fifo_ready),
    .o_data (b_fifo_data),
    .o_valid(axi_err_b_valid),
    .i_ready(axi_err_b_ready)
);

  always_comb begin : proc_b_channel
    axi_err_b      = '0;
    axi_err_b.id   = b_fifo_data;
    axi_err_b.resp = Resp;
  end

  ///////////////////////
  // Read Transactions //
  ///////////////////////
  // push if there is room in the fifo
  assign r_fifo_push      = axi_err_ar_valid & ~r_fifo_full;
  assign axi_err_ar_ready = ~r_fifo_full;

  // fifo data assignment
  always_comb r_fifo_inp = '{
    id:      axi_err_ar.id,
    len:     axi_err_ar.len,
    default: '0
  };

  // TODO(@wolfgang.roenninger): Replace with cc_stream_fifo or equivalent
  fifo_v3 #(
    .FALL_THROUGH(1'b0),
    .DEPTH       (MaxTxn),
    .dtype_t     (r_data_t)
  ) i_r_fifo (
    .i_clk,
    .i_rst_n,
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .full_o    (r_fifo_full  ),
    .empty_o   (r_fifo_empty ),
    .usage_o   (/*open*/),
    .data_i    (r_fifo_inp),
    .push_i    (r_fifo_push),
    .data_o    (r_fifo_data),
    .pop_i     (r_fifo_pop)
  );

  always_comb begin : proc_r_channel
    // default assignments
    r_busy_d    = r_busy_q;
    r_busy_load = 1'b0;
    // r fifo signals
    r_fifo_pop  = 1'b0;
    // r counter signals
    r_cnt_clear = 1'b0;
    r_cnt_en    = 1'b0;
    r_cnt_load  = 1'b0;
    // r_channel
    axi_err_r       = '0;
    axi_err_r.id    = r_fifo_data.id;
    axi_err_r.data  = ReadData;
    axi_err_r.resp  = Resp;
    axi_err_r_valid = 1'b0;
    // control
    if (r_busy_q) begin
      axi_err_r_valid = 1'b1;
      axi_err_r.last  = (r_current_beat == '0);
      // r transaction
      if (axi_err_r_ready) begin
        r_cnt_en = 1'b1;
        if (r_current_beat == '0) begin
          r_busy_d    = 1'b0;
          r_busy_load = 1'b1;
          r_cnt_clear = 1'b1;
          r_fifo_pop  = 1'b1;
        end
      end
    end else begin
      // when not busy and fifo not empty, start counter err gen
      if (!r_fifo_empty) begin
        r_busy_d    = 1'b1;
        r_busy_load = 1'b1;
        r_cnt_load  = 1'b1;
      end
    end
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)         r_busy_q <= 1'b0;
    else if (r_busy_load) r_busy_q <= r_busy_d;
  end

  cc_cnt_delta #(
    .Width         (axi_pkg::AXI_LEN_WIDTH),
    .StickyOverflow(1'b0)
  ) u_r_counter (
    .i_clk,
    .i_rst_n,
    .i_flush   (r_cnt_clear),
    .i_cnt_en  (r_cnt_en),
    .i_cnt_down(1'b1),
    .i_delta   (axi_pkg::axi_len_t'(1)),
    .o_q       (r_current_beat),
    .i_d       (r_fifo_data.len),
    .i_d_load  (r_cnt_load),
    .o_overflow(/*open*/)
  );

  // TODO(@wolfgang.roenninger): Put this into a bind

//  // pragma translate_off
//  `ifndef VERILATOR
//  `ifndef XSIM
//
//  default disable iff (!rst_ni);
//  if (!ATOPs) begin : gen_assert_atops_unsupported
//    assume property( @(posedge clk_i) (slv_req_i.aw_valid |-> slv_req_i.aw.atop == '0)) else
//     $fatal(1, "Got ATOP but not configured to support ATOPs!");
//  end
//  `endif
//  `endif
//  // pragma translate_on

endmodule
