// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License. You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Stream arbiter: Arbitrates a parametrizable number of input streams (i.e., valid-ready
// handshaking with dependency rules as in AXI4) to a single output stream.  Once `oup_valid_o` is
// asserted, `oup_data_o` remains invariant until the output handshake has occurred.  The
// arbitration scheme is round-robin with "look ahead", see the `rrarbiter` for details.

`ifndef _CC_STREAM_ROUND_ROBIN_ARBITER_SV_
`define _CC_STREAM_ROUND_ROBIN_ARBITER_SV_

/// Stream round robin arbiter
///
module cc_stream_round_robin_arbiter #(
    parameter type      data_t = logic,   // Vivado requires a default value for type parameters.
    parameter integer   N_INP = -1,       // Synopsys DC requires a default value for parameters.
    parameter           ARBITER = "rr"    // "rr" or "prio"
) (
    input  wire              i_clk,
    input  wire              i_rst_n,

    input  data_t [N_INP-1:0] inp_data_i,
    input  logic  [N_INP-1:0] inp_valid_i,
    output logic  [N_INP-1:0] inp_ready_o,

    output data_t             oup_data_o,
    output logic              oup_valid_o,
    input  logic              oup_ready_i
);

  if (ARBITER == "rr") begin : gen_rr_arb
    rr_arb_tree #(
      .NumIn      (N_INP),
      .datatype_t (data_t),
      .ExtPrio    (1'b0),
      .AxiVldRdy  (1'b1),
      .LockIn     (1'b1)
    ) i_arbiter (
      .i_clk,
      .i_rst_n,
      .flush_i('0),
      .rr_i   ('0),
      .req_i  (inp_valid_i),
      .gnt_o  (inp_ready_o),
      .data_i (inp_data_i),
      .gnt_i  (oup_ready_i),
      .req_o  (oup_valid_o),
      .data_o (oup_data_o),
      .idx_o  ()  // ASO-UNUSED_OUTPUT : Index is not propagated.
    );

  end else if (ARBITER == "prio") begin : gen_prio_arb
    rr_arb_tree #(
      .NumIn      (N_INP),
      .DataType   (data_t),
      .ExtPrio    (1'b1),
      .AxiVldRdy  (1'b1),
      .LockIn     (1'b1)
    ) i_arbiter (
      .i_clk,
      .i_rst_n,
      .flush_i('0),
      .rr_i   ('0),
      .req_i  (inp_valid_i),
      .gnt_o  (inp_ready_o),
      .data_i (inp_data_i),
      .gnt_i  (oup_ready_i),
      .req_o  (oup_valid_o),
      .data_o (oup_data_o),
      .idx_o  ()  // ASO-UNUSED_OUTPUT : Index is not propagated.
    );

  end else begin : gen_arb_error
    // pragma translate_off
    $fatal(1, "Invalid value for parameter 'ARBITER'!");
    // pragma translate_on
  end

endmodule

`endif // _CC_STREAM_ROUND_ROBIN_ARBITER_SV_
