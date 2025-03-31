// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Based on the design: https://github.com/pulp-platform/common_cells/blob/master/src/cdc_4phase.sv

/// A 4-phase clock domain crossing. (Source Domain)
///
/// While this is less efficient than a 2-phase CDC, it doesn't suffer from the same issues
/// during one sided resets since the IDLE state doesn't alternate with every transaction.
///
module axe_ccl_cdc_4_phase_src #(
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of synchronizer stages
  parameter int unsigned SyncStages = 3,
  /// Wait with the input handshake until the `dst` side has completed the handshake.
  ///
  /// This increases the latency of the first transaction but has no effect on throughput.
  parameter int unsigned WaitHandshake = 1'b0,
  /// Start sending the `ResetMsg` within the asynchronous reset state.
  ///
  /// This is useful if we need to transmit m message to the other side of the CDC immediately
  /// during the asynchronous reset even if there is no clock available.
  ///
  /// Required for proper functionality of `axe_ccl_cdc_reset`.
  parameter bit SendResetMsg = 1'b0,
  /// The reset message to be transmitted if `SendResetMsg(1'b1)`.
  parameter data_t ResetMsg = data_t'(0)
)(
  ///////////////////
  // Source Domain //
  ///////////////////
  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  /// The input stream payload data
  input  data_t i_data,
  /// The input stream is valid
  input  logic  i_valid,
  /// The input stream is ready
  output logic  o_ready,

  ///////////////////
  // Async Signals //
  ///////////////////
  /// The asynchronous output data
  output data_t o_async_data,
  /// The asynchronous request to the dst domain
  output logic  o_async_req,
  /// The asynchronous acknowledge from the dst domain
  input  logic  i_async_ack
);
  typedef enum logic [1:0] {
    IDLE,
    WAIT_ACK_ASSERT,
    WAIT_ACK_DEASSERT
  } state_e;

  /////////////////////
  // Synchronization //
  /////////////////////
  logic acknowledged;
  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(1'b0)
  ) u_axe_tcl_seq_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_async_ack),
    .o_q    (acknowledged)
  );

  ///////////////////////
  // 4-phase handshake //
  ///////////////////////
  state_e state_d;
  state_e state_q;
  logic   request_d;
  data_t  data_d;
  logic   update_req;
  logic   load_data;

  always_comb begin
    state_d    = state_q;
    request_d  = 1'b0;
    o_ready    = 1'b0;
    update_req = 1'b0;
    load_data  = 1'b0;

    unique case (state_q)
      IDLE: begin
        o_ready = ~WaitHandshake;

        // Sample data the first cycle valid is going up.
        if (i_valid) begin
          request_d  = 1'b1;
          update_req = 1'b1;
          load_data  = 1'b1;
          state_d    = WAIT_ACK_ASSERT;
        end
      end
      WAIT_ACK_ASSERT: begin
        if (acknowledged) begin
          update_req = 1'b1; // Clear the request
          state_d    = WAIT_ACK_DEASSERT;
        end
      end
      WAIT_ACK_DEASSERT: begin
        if (!acknowledged) begin
          state_d = IDLE;
          o_ready = WaitHandshake;
        end
      end
      default: state_d = IDLE;
    endcase
  end

  logic       change_state;
  always_comb change_state = state_q != state_d;
  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          state_q <= IDLE;
    else if (change_state) state_q <= state_d;
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      o_async_req  <= SendResetMsg;
      o_async_data <= ResetMsg;
    end
    else if (update_req) begin
      o_async_req  <= request_d;
      if (load_data) o_async_data <= i_data;
    end
  end
endmodule
