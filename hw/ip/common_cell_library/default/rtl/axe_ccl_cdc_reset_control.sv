// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Synchronize resets and flush signlas between different CDC sides.
///
module axe_ccl_cdc_reset_control #(
  /// The number of synchronizer stages
  parameter int unsigned SyncStages = 3,
  /// Initiate a flush on Async Reset on either side.
  parameter bit          FlushOnAsyncReset = 1'b1
)(
  //////////////////////////////////////////
  // Synchronous to the respective Domain //
  //////////////////////////////////////////
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /// Initiate a flush, pulse will trigger the full sequence
  input  logic i_flush,
  /// Request to isolate the input/output protocol from the actual CDC.
  ///
  /// For more complex protocols this could mean terminating all open transactions gracefully.
  output logic o_isolate_req,
  /// The isolation is acknoledged
  input  logic i_isolate_ack,
  /// Request a flush of all registers/memory in the respective domain
  output logic o_flush_req,
  /// The flush in the respective domain has been done.
  input  logic i_flush_ack,

  /////////////////////////////////////////////
  // Asynchronous Flush Sequence Handshaking //
  /////////////////////////////////////////////
  /// Flush sequence to the other domain (Initiator)
  output axe_ccl_cdc_pkg::flush_phase_e o_async_next_phase,
  /// Asynchronous next phase Request (Initiator)
  output logic                          o_async_request,
  /// Asynchronous next phase Acknoiledge (Initiator)
  input  logic                          i_async_acknowledge,
  /// Flush sequence to the other domain (Target)
  input  axe_ccl_cdc_pkg::flush_phase_e i_async_next_phase,
  /// Asynchronous next phase Request (Target)
  input  logic                          i_async_request,
  /// Asynchronous next phase Acknoiledge (Target)
  output logic                          o_async_acknowledge
);

  ///////////////
  // Initiator //
  ///////////////
  typedef enum logic [3:0] {
    IDLE,
    ISOLATE,
    WAIT_ISOLATE_PHASE_ACK,
    WAIT_ISOLATE_ACK,
    FLUSH,
    WAIT_FLUSH_PHASE_ACK,
    WAIT_FLUSH_ACK,
    POST_FLUSH,
    FINISHED
  } initiator_state_e;
  initiator_state_e initiator_state_d;
  initiator_state_e initiator_state_q;
  logic             initiator_state_change;
  always_comb       initiator_state_change = initiator_state_d != initiator_state_q;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                    initiator_state_q <= FlushOnAsyncReset ? ISOLATE : IDLE;
    else if (initiator_state_change) initiator_state_q <= initiator_state_d;
  end

  // The phase of the flush sequence is sent to the other side using a 4-phase CDC
  axe_ccl_cdc_pkg::flush_phase_e initiator_flush_phase;
  logic                          initiator_phase_change_req;
  logic                          initiator_phase_change_ack;
  logic                          initiator_isolate_output;
  logic                          initiator_flush_output;

  always_comb begin
    initiator_state_d          = initiator_state_q;
    initiator_phase_change_req = 1'b0;
    initiator_isolate_output   = 1'b0;
    initiator_flush_output     = 1'b0;
    initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_IDLE;

    unique case (initiator_state_q)
      IDLE: if (i_flush) initiator_state_d = ISOLATE;

      ISOLATE : begin
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_ISOLATE;
        initiator_phase_change_req = 1'b1;
        initiator_isolate_output   = 1'b1;

        if (initiator_phase_change_ack && i_isolate_ack) initiator_state_d = FLUSH;
        else if (initiator_phase_change_ack)             initiator_state_d = WAIT_ISOLATE_ACK;
        else if (i_isolate_ack)                          initiator_state_d = WAIT_ISOLATE_PHASE_ACK;
      end

      WAIT_ISOLATE_ACK: begin
        initiator_flush_phase    = axe_ccl_cdc_pkg::FLUSH_PHASE_ISOLATE;
        initiator_isolate_output = 1'b1;

        if (i_isolate_ack) initiator_state_d = FLUSH;
      end

      WAIT_ISOLATE_PHASE_ACK: begin
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_ISOLATE;
        initiator_phase_change_req = 1'b1;
        initiator_isolate_output   = 1'b1;

        if (initiator_phase_change_ack) initiator_state_d = FLUSH;
      end

      FLUSH: begin
        initiator_isolate_output   = 1'b1;
        initiator_flush_output     = 1'b1;
        initiator_phase_change_req = 1'b1;
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_FLUSH;

        if (initiator_phase_change_ack && i_flush_ack) initiator_state_d = POST_FLUSH;
        else if (initiator_phase_change_ack)           initiator_state_d = WAIT_FLUSH_ACK;
        else if (i_flush_ack)                          initiator_state_d = WAIT_FLUSH_PHASE_ACK;
      end

      WAIT_FLUSH_ACK: begin
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_FLUSH;
        initiator_isolate_output   = 1'b1;
        initiator_flush_output     = 1'b1;

        if (i_flush_ack) initiator_state_d = POST_FLUSH;
      end

      WAIT_FLUSH_PHASE_ACK: begin
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_FLUSH;
        initiator_phase_change_req = 1'b1;
        initiator_isolate_output   = 1'b1;
        initiator_flush_output     = 1'b1;

        if (initiator_phase_change_ack) initiator_state_d = POST_FLUSH;
      end

      POST_FLUSH: begin
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_POST_FLUSH;
        initiator_phase_change_req = 1'b1;
        initiator_isolate_output   = 1'b1;

        if (initiator_phase_change_ack) initiator_state_d = FINISHED;
      end

      FINISHED: begin
        initiator_flush_phase      = axe_ccl_cdc_pkg::FLUSH_PHASE_IDLE;
        initiator_phase_change_req = 1'b1;
        initiator_isolate_output   = 1'b1;

        if (initiator_phase_change_ack) initiator_state_d = IDLE;
      end

      default: initiator_state_d = ISOLATE;
    endcase
  end

  axe_ccl_cdc_4_phase_src #(
    .data_t       (axe_ccl_cdc_pkg::flush_phase_e),
    .SyncStages   (SyncStages),
    .WaitHandshake(1'b1), // Important! The CDC must wait on the handshake.
                          // Otherwise it would proceed to the next state
                          // without waiting for the new state to arrive
                          // on the other side.
    .SendResetMsg (FlushOnAsyncReset), // Start in the ISOLATE state on the other side immediatly on
                                       // async reset if it is enabled.
    .ResetMsg     (axe_ccl_cdc_pkg::FLUSH_PHASE_ISOLATE)
  ) u_initiator_flush_cdc_src (
    .i_clk,
    .i_rst_n,
    .i_data      (initiator_flush_phase),
    .i_valid     (initiator_phase_change_req),
    .o_ready     (initiator_phase_change_ack),
    .o_async_data(o_async_next_phase),
    .o_async_req (o_async_request),
    .i_async_ack (i_async_acknowledge)
  );

  ////////////
  // Target //
  ////////////

  axe_ccl_cdc_pkg::flush_phase_e target_flush_phase_d;
  axe_ccl_cdc_pkg::flush_phase_e target_flush_phase_q;

  logic                          target_phase_change_req;
  logic                          target_phase_change_ack;

  logic                          target_isolate_output;
  logic                          target_flush_output;

  axe_ccl_cdc_4_phase_dst #(
    .data_t       (axe_ccl_cdc_pkg::flush_phase_e),
    .SyncStages   (SyncStages)
  ) u_target_flush_cdc_dst (
    .i_clk,
    .i_rst_n,
    .o_data      (target_flush_phase_d),
    .o_valid     (target_phase_change_req),
    .i_ready     (target_phase_change_ack),
    .i_async_data(i_async_next_phase),
    .i_async_req (i_async_request),
    .o_async_ack (o_async_acknowledge)
  );

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) target_flush_phase_q <= axe_ccl_cdc_pkg::FLUSH_PHASE_IDLE;

    else if (target_phase_change_req && target_phase_change_ack)
        target_flush_phase_q <= target_flush_phase_d;
  end

  always_comb begin
    target_phase_change_ack = 1'b0;
    target_isolate_output   = 1'b0;
    target_flush_output     = 1'b0;

    if (target_phase_change_req) begin
      unique case (target_flush_phase_d)
        axe_ccl_cdc_pkg::FLUSH_PHASE_IDLE: begin
          target_phase_change_ack = 1'b1;
        end

        axe_ccl_cdc_pkg::FLUSH_PHASE_ISOLATE: begin
          target_phase_change_ack = i_isolate_ack; // Wait for isolate to complete
          target_isolate_output   = 1'b1;
        end

        axe_ccl_cdc_pkg::FLUSH_PHASE_FLUSH: begin
          target_phase_change_ack = i_flush_ack; // Wait for the flush acknowledge
          target_isolate_output   = 1'b1;
          target_flush_output     = 1'b1;
        end

        axe_ccl_cdc_pkg::FLUSH_PHASE_POST_FLUSH: begin
          target_phase_change_ack = 1'b1;
          target_isolate_output   = 1'b1;
        end

        default: /* use defaults */;
      endcase
    end else begin
      unique case (target_flush_phase_q)
        axe_ccl_cdc_pkg::FLUSH_PHASE_ISOLATE: begin
          target_isolate_output   = 1'b1;
        end

        axe_ccl_cdc_pkg::FLUSH_PHASE_FLUSH: begin
          target_isolate_output   = 1'b1;
          target_flush_output     = 1'b1;
        end

        axe_ccl_cdc_pkg::FLUSH_PHASE_POST_FLUSH: begin
          target_isolate_output   = 1'b1;
        end

        default: /* use defaults */;
      endcase
    end
  end

  ///////////////////////
  // Output Assignment //
  ///////////////////////

  // The flush and isolate signal are the OR combination of the receiver and
  // initiator's flush/isolate signal. This ensures that the correct sequence is
  // followed even if both sides are flushed independently at roughly the same
  // time.
  always_comb o_isolate_req = initiator_isolate_output | target_isolate_output;
  always_comb o_flush_req   = initiator_flush_output   | target_flush_output;
endmodule
