// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Based on the design: https://github.com/pulp-platform/common_cells/blob/master/src/cdc_4phase.sv

/// A 4-phase clock domain crossing. (Destination Domain)
///
/// While this is less efficient than a 2-phase CDC, it doesn't suffer from the same issues
/// during one sided resets since the IDLE state doesn't alternate with every transaction.
///
module axe_ccl_cdc_4_phase_dst #(
  /// The width of the data (optional if data_t is given)
  parameter int unsigned DataWidth = 32,
  /// The concrete data type used
  parameter type data_t = logic[DataWidth-1:0],
  /// The number of synchronizer stages
  parameter int unsigned SyncStages = 3
)(
  ////////////////////////
  // Destination Domain //
  ////////////////////////
  /// Clock, positive edge triggered
  input  wire   i_clk,
  /// Asynchronous reset, active low
  input  wire   i_rst_n,
  /// The output stream payload data
  output data_t o_data,
  /// The output stream is valid
  output logic  o_valid,
  /// The output stream is ready
  input  logic  i_ready,

  ///////////////////
  // Async Signals //
  ///////////////////
  /// The asynchronous input data
  input  data_t i_async_data,
  /// The asynchronous request from the src domain
  input  logic  i_async_req,
  /// The asynchronous acknowledge to the src domain
  output logic  o_async_ack
);
  typedef enum logic [1:0] {
    IDLE,
    WAIT_DOWNSTREAM_ACK,
    WAIT_REQ_DEASSERT
  } state_e;

  /////////////////////
  // Synchronization //
  /////////////////////
  logic request;
  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(1'b0)
  ) u_axe_tcl_seq_sync (
    .i_clk,
    .i_rst_n,
    .i_d    (i_async_req),
    .o_q    (request)
  );

  ///////////////////////
  // 4-phase handshake //
  ///////////////////////
  state_e state_d;
  state_e state_q;
  logic   acknowledge_d;
  logic   valid;
  logic   ready;

  always_comb begin
    state_d       = state_q;
    acknowledge_d = 1'b0;
    valid         = 1'b0;

    unique case (state_q)
      IDLE: begin
        if (request) begin
          valid = 1'b1;
          if (ready) state_d = WAIT_REQ_DEASSERT;
          else       state_d = WAIT_DOWNSTREAM_ACK;
        end
      end
      WAIT_DOWNSTREAM_ACK: begin
        valid = 1'b1;
        if (ready) begin
          state_d       = WAIT_REQ_DEASSERT;
          acknowledge_d = 1'b1;
        end
      end
      WAIT_REQ_DEASSERT: begin
        acknowledge_d = 1'b1;
        if (!request) begin
          acknowledge_d = 1'b0;
          state_d       = IDLE;
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

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) o_async_ack <= 1'b0;
    else          o_async_ack <= acknowledge_d;
  end

  //////////////////////////////////
  // Handshaking and Data Capture //
  //////////////////////////////////
  logic capture_data;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          o_data <= data_t'(0);
    else if (capture_data) o_data <= i_async_data;
  end

  cc_stream_pipe_load #(
    .NumStages(1)
  ) u_capture_pipeline (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_valid(valid),
    .o_ready(ready),
    .o_load (capture_data),
    .o_state(/* not used */), // ASO-UNUSED_OUTPUT : No observability needed.
    .o_valid,
    .i_ready
  );
endmodule
