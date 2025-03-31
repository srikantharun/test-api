// Copyright 2018 ETH Zurich and University of Bologna.
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
// - Andreas Kurth <akurth@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>

/// Filter atomic operations (ATOPs) in a protocol-compliant manner.
///
/// This module filters atomic operations (ATOPs), i.e., write transactions that have a non-zero
/// `aw_atop` value, from its `slv` to its `mst` port. This module guarantees that:
///
/// 1) `aw_atop` is always zero on the `mst` port;
///
/// 2) write transactions with non-zero `aw_atop` on the `slv` port are handled in conformance with
///    the AXI standard by replying to such write transactions with the proper B and R responses.
///    The response code on atomic operations that reach this module is always SLVERR
///    (implementation-specific, not defined in the AXI standard).
///
/// ## Intended usage
/// This module is intended to be placed between masters that may issue ATOPs and slaves that do not
/// support ATOPs. That way, this module ensures that the AXI protocol remains in a defined state on
/// systems with mixed ATOP capabilities.
///
/// ## Specification reminder
/// The AXI standard specifies that there may be no ordering requirements between different atomic
/// bursts (i.e., a burst started by an AW with ATOP other than 0) and none between atomic bursts
/// and non-atomic bursts [E2.1.4]. That is, **an atomic burst may never have the same ID as any
/// other write or read burst that is in-flight at the same time**.
module axe_axi_atop_filter #(
  /// The ID width of the Transaction
  parameter int unsigned AxiIdWidth = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Maximum number of in-flight AXI write transactions
  parameter int unsigned AxiMaxWriteTxns = 1,
  /// AXI AW channel struct
  parameter type  axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  /// AXI W channel struct
  parameter type  axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  /// AXI B channel struct
  parameter type  axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  /// AXI AR channel struct
  parameter type  axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  /// AXI R channel struct
  parameter type  axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  /// Rising-edge clock of both ports
  input wire i_clk,
  // doc async
  /// Asynchronous reset, active low
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
  input  logic    i_axi_s_r_ready,

  // Manager port
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
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////
  if (AxiIdWidth == 0)                    $fatal(1, "Parameter: 'AxiIdWidth' must be at least 1!");
  if (AxiIdWidth != $bits(i_axi_s_aw.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match aw.id;");
  if (AxiMaxWriteTxns == 0)               $fatal(1, "Parameter: 'AxiMaxWriteTxns' must be at least 1!");

  // Minimum counter width is 2 to detect underflows.
  localparam int unsigned COUNTER_WIDTH = (AxiMaxWriteTxns == 1) ? 2 : $clog2(AxiMaxWriteTxns+1);
  typedef struct packed {
    logic                     underflow;
    logic [COUNTER_WIDTH-1:0] cnt;
  } cnt_t;
  cnt_t   w_cnt_d, w_cnt_q;

  typedef enum logic [2:0] {
    W_FEEDTHROUGH, BLOCK_AW, ABSORB_W, HOLD_B, INJECT_B, WAIT_R
  } w_state_e;
  w_state_e   w_state_d, w_state_q;

  typedef enum logic [1:0] { R_FEEDTHROUGH, INJECT_R, R_HOLD } r_state_e;
  r_state_e   r_state_d, r_state_q;

  typedef logic [AxiIdWidth-1:0] id_t;
  id_t  id_d, id_q;

  typedef logic [7:0] len_t;
  len_t   r_beats_d,  r_beats_q;

  typedef struct packed {
    len_t len;
  } r_resp_cmd_t;
  r_resp_cmd_t  r_resp_cmd_push, r_resp_cmd_pop;

  logic aw_without_complete_w_downstream,
        complete_w_without_aw_downstream,
        r_resp_cmd_push_valid,  r_resp_cmd_push_ready,
        r_resp_cmd_pop_valid,   r_resp_cmd_pop_ready;

  // An AW without a complete W burst is in-flight downstream if the W counter is > 0 and not
  // underflowed.
  assign aw_without_complete_w_downstream = !w_cnt_q.underflow && (w_cnt_q.cnt > 0);
  // A complete W burst without AW is in-flight downstream if the W counter is -1.
  assign complete_w_without_aw_downstream = w_cnt_q.underflow && &(w_cnt_q.cnt);

  // Manage AW, W, and B channels.
  always_comb begin
    // Defaults:
    // Disable AW and W handshakes.
    o_axi_m_aw_valid = 1'b0;
    o_axi_s_aw_ready = 1'b0;
    o_axi_m_w_valid  = 1'b0;
    o_axi_s_w_ready  = 1'b0;
    // Feed write responses through.
    o_axi_m_b_ready  = i_axi_s_b_ready;
    o_axi_s_b_valid  = i_axi_m_b_valid;
    o_axi_s_b        = i_axi_m_b;
    // Keep ID stored for B and R response.
    id_d = id_q;
    // Do not push R response commands.
    r_resp_cmd_push_valid = 1'b0;
    // Keep the current state.
    w_state_d = w_state_q;

    unique case (w_state_q)
      W_FEEDTHROUGH: begin
        // Feed AW channel through if the maximum number of outstanding bursts is not reached.
        if (complete_w_without_aw_downstream || (w_cnt_q.cnt < AxiMaxWriteTxns)) begin
          o_axi_m_aw_valid = i_axi_s_aw_valid;
          o_axi_s_aw_ready = i_axi_m_aw_ready;
        end
        // Feed W channel through if ..
        if (aw_without_complete_w_downstream // .. downstream is missing W bursts ..
            // .. or a new non-ATOP AW is being applied and there is not already a complete W burst
            // downstream (to prevent underflows of w_cnt).
            || ((i_axi_s_aw_valid && i_axi_s_aw.atop[5:4] == axi_pkg::AXI_ATOP_NONE)
                && !complete_w_without_aw_downstream)
        ) begin
          o_axi_m_w_valid = i_axi_s_w_valid;
          o_axi_s_w_ready = i_axi_m_w_ready;
        end
        // Filter out AWs that are atomic operations.
        if (i_axi_s_aw_valid && i_axi_s_aw.atop[5:4] != axi_pkg::AXI_ATOP_NONE) begin
          o_axi_m_aw_valid = 1'b0;          // Do not let AW pass to master port.
          o_axi_s_aw_ready = 1'b1;          // Absorb AW on slave port.
          id_d             = i_axi_s_aw.id; // Store ID for B response.
          // Some atomic operations require a response on the R channel.
          if (i_axi_s_aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX]) begin
            // Push R response command.  We do not have to wait for the ready of the register
            // because we know it is ready: we are its only master and will wait for the register to
            // be emptied before going back to the `W_FEEDTHROUGH` state.
            r_resp_cmd_push_valid = 1'b1;
          end
          // If downstream is missing W beats, block the AW channel and let the W bursts complete.
          if (aw_without_complete_w_downstream) begin
            w_state_d = BLOCK_AW;
          // If downstream is not missing W beats, absorb the W beats for this atomic AW.
          end else begin
            o_axi_m_w_valid = 1'b0; // Do not let W beats pass to master port.
            o_axi_s_w_ready = 1'b1; // Absorb W beats on slave port.
            if (i_axi_s_w_valid && i_axi_s_w.last) begin
              // If the W beat is valid and the last, proceed by injecting the B response.
              // However, if there is a non-handshaked B on our response port, we must let that
              // complete first.
              if (o_axi_s_b_valid && !i_axi_s_b_ready) begin
                w_state_d = HOLD_B;
              end else begin
                w_state_d = INJECT_B;
              end
            end else begin
              // Otherwise continue with absorbing W beats.
              w_state_d = ABSORB_W;
            end
          end
        end
      end

      BLOCK_AW: begin
        // Feed W channel through to let outstanding bursts complete.
        if (aw_without_complete_w_downstream) begin
          o_axi_m_w_valid = i_axi_s_w_valid;
          o_axi_s_w_ready = i_axi_m_w_ready;
        end else begin
          // If there are no more outstanding W bursts, start absorbing the next W burst.
          o_axi_s_w_ready = 1'b1;
          if (i_axi_s_w_valid && i_axi_s_w.last) begin
            // If the W beat is valid and the last, proceed by injecting the B response.
            if (o_axi_s_b_valid && !i_axi_s_b_ready) begin
              w_state_d = HOLD_B;
            end else begin
              w_state_d = INJECT_B;
            end
          end else begin
            // Otherwise continue with absorbing W beats.
            w_state_d = ABSORB_W;
          end
        end
      end

      ABSORB_W: begin
        // Absorb all W beats of the current burst.
        o_axi_s_w_ready = 1'b1;
        if (i_axi_s_w_valid && i_axi_s_w.last) begin
          if (o_axi_s_b_valid && !i_axi_s_b_ready) begin
            w_state_d = HOLD_B;
          end else begin
            w_state_d = INJECT_B;
          end
        end
      end

      HOLD_B: begin
        // Proceed with injection of B response upon handshake.
        if (o_axi_s_b_valid && i_axi_s_b_ready) begin
          w_state_d = INJECT_B;
        end
      end

      INJECT_B: begin
        // Pause forwarding of B response.
        o_axi_m_b_ready = 1'b0;
        // Inject error response instead.  Since the B channel has an ID and the atomic burst we are
        // replying to is guaranteed to be the only burst with this ID in flight, we do not have to
        // observe any ordering and can immediately inject on the B channel.
        o_axi_s_b       = '0;
        o_axi_s_b.id    = id_q;
        o_axi_s_b.resp  = axi_pkg::RespSlvErr;
        o_axi_s_b_valid = 1'b1;
        if (i_axi_s_b_ready) begin
          // If not all beats of the R response have been injected, wait for them. Otherwise, return
          // to `W_FEEDTHROUGH`.
          if (r_resp_cmd_pop_valid && !r_resp_cmd_pop_ready) begin
            w_state_d = WAIT_R;
          end else begin
            w_state_d = W_FEEDTHROUGH;
          end
        end
      end

      WAIT_R: begin
        // Wait with returning to `W_FEEDTHROUGH` until all beats of the R response have been
        // injected.
        if (!r_resp_cmd_pop_valid) begin
          w_state_d = W_FEEDTHROUGH;
        end
      end

      default: w_state_d = W_FEEDTHROUGH;
    endcase
  end
  // Connect signals on AW and W channel that are not managed by the control FSM from slave port to
  // master port.
  // Feed-through of the AW and W vectors, make sure that downstream aw.atop is always zero
  always_comb begin
    // overwrite the atop signal
    o_axi_m_aw      = i_axi_s_aw;
    o_axi_m_aw.atop = axi_pkg::axi_atop_t'(0);
  end
  assign o_axi_m_w  = i_axi_s_w;

  // Manage R channel.
  always_comb begin
    // Defaults:
    // Feed read responses through.
    o_axi_s_r       = i_axi_m_r;
    o_axi_s_r_valid = i_axi_m_r_valid;
    o_axi_m_r_ready = i_axi_s_r_ready;
    // Do not pop R response command.
    r_resp_cmd_pop_ready = 1'b0;
    // Keep the current value of the beats counter.
    r_beats_d = r_beats_q;
    // Keep the current state.
    r_state_d = r_state_q;

    unique case (r_state_q)
      R_FEEDTHROUGH: begin
        if (i_axi_m_r_valid && !i_axi_s_r_ready) begin
          r_state_d = R_HOLD;
        end else if (r_resp_cmd_pop_valid) begin
          // Upon a command to inject an R response, immediately proceed with doing so because there
          // are no ordering requirements with other bursts that may be ongoing on the R channel at
          // this moment.
          r_beats_d = r_resp_cmd_pop.len;
          r_state_d = INJECT_R;
        end
      end

      INJECT_R: begin
        o_axi_m_r_ready = 1'b0;
        o_axi_s_r       = '0;
        o_axi_s_r.id    = id_q;
        o_axi_s_r.resp  = axi_pkg::RespSlvErr;
        o_axi_s_r.last  = (r_beats_q == '0);
        o_axi_s_r_valid = 1'b1;
        if (i_axi_s_r_ready) begin
          if (o_axi_s_r.last) begin
            r_resp_cmd_pop_ready = 1'b1;
            r_state_d = R_FEEDTHROUGH;
          end else begin
            r_beats_d -= 1;
          end
        end
      end

      R_HOLD: begin
        if (i_axi_m_r_valid && i_axi_s_r_ready) begin
          r_state_d = R_FEEDTHROUGH;
        end
      end

      default: r_state_d = R_FEEDTHROUGH;
    endcase
  end
  // Feed all signals on AR through.
  assign o_axi_m_ar       = i_axi_s_ar;
  assign o_axi_m_ar_valid = i_axi_s_ar_valid;
  assign o_axi_s_ar_ready = i_axi_m_ar_ready;

  // Keep track of outstanding downstream write bursts and responses.
  always_comb begin
    w_cnt_d = w_cnt_q;
    if (o_axi_m_aw_valid && i_axi_m_aw_ready) begin
      w_cnt_d.cnt += 1;
    end
    if (o_axi_m_w_valid && i_axi_m_w_ready && o_axi_m_w.last) begin
      w_cnt_d.cnt -= 1;
    end
    if (w_cnt_q.underflow && (w_cnt_d.cnt == '0)) begin
      w_cnt_d.underflow = 1'b0;
    end else if (w_cnt_q.cnt == '0 && &(w_cnt_d.cnt)) begin
      w_cnt_d.underflow = 1'b1;
    end
  end

  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (!i_rst_n) begin
      id_q <= '0;
      r_beats_q <= '0;
      r_state_q <= R_FEEDTHROUGH;
      w_cnt_q <= '{default: '0};
      w_state_q <= W_FEEDTHROUGH;
    end else begin
      id_q <= id_d;
      r_beats_q <= r_beats_d;
      r_state_q <= r_state_d;
      w_cnt_q <= w_cnt_d;
      w_state_q <= w_state_d;
    end
  end

  cc_stream_reg #(
    .data_t(r_resp_cmd_t)
  ) r_resp_cmd (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (r_resp_cmd_push),
    .i_valid(r_resp_cmd_push_valid),
    .o_ready(r_resp_cmd_push_ready),
    .o_data (r_resp_cmd_pop),
    .o_valid(r_resp_cmd_pop_valid),
    .i_ready(r_resp_cmd_pop_ready)
  );
  assign r_resp_cmd_push.len = i_axi_s_aw.len;

endmodule
