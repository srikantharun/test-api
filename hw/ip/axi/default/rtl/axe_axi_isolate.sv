// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Derived from: https://github.com/pulp-platform/axi/blob/master/src/axi_isolate.sv
//
// Original Authors:
// - Wolfgang Roenninger <wroennin@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// This module can isolate the AXI4+ATOPs bus on the master port from the slave port.  When the
/// isolation is not active, the two ports are directly connected.
///
/// This module counts how many open transactions are currently in flight on the read and write
/// channels.  It is further capable of tracking the amount of open atomic transactions with read
/// responses.
///
/// The isolation interface has two signals: `isolate_i` and `isolated_o`.  When `isolate_i` is
/// asserted, all open transactions are gracefully terminated.  When no transactions are in flight
/// anymore, the `isolated_o` output is asserted.  As long as `isolated_o` is asserted, all output
/// signals in `mst_req_o` are silenced to `'0`.  When isolated, new transactions initiated on the
/// slave port are stalled until the isolation is terminated by deasserting `isolate_i`.
///
/// ## Response
///
/// If the `TerminateTxn` parameter is set to `1'b1`, the module will return response errors
/// in case there is an incoming transaction while the module isolates.  The data returned on the
/// bus is `1501A7ED` (hexspeak for isolated).
///
/// If `TerminateTxn` is set to `1'b0`, the transaction will block indefinitely until the
/// module is de-isolated again.
module axe_axi_isolate #(
  /// ID width of all AXI4+ATOP ports
  parameter int signed AxiIdWidth = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Data width of all AXI4+ATOP ports
  parameter int signed AxiDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// Maximum number of pending transactions per channel
  parameter int unsigned MaxTxn = 32'd16,
  /// Gracefully terminate all incoming transactions in case of isolation by returning proper error
  /// responses.
  parameter bit TerminateTxn = 1'b1,
  /// Cut AW channel on the demux if `TerminateTxn == 1`
  parameter bit DemuxCutAw = 1'b0,
  /// Cut  W channel on the demux if `TerminateTxn == 1`
  parameter bit DemuxCutW  = 1'b0,
  /// Cut  B channel on the demux if `TerminateTxn == 1`
  parameter bit DemuxCutB  = 1'b0,
  /// Cut AR channel on the demux if `TerminateTxn == 1`
  parameter bit DemuxCutAr = 1'b0,
  /// Cut  R channel on the demux if `TerminateTxn == 1`
  parameter bit DemuxCutR  = 1'b0,
  /// Propagated parameter for demux if  `TerminateTxn == 1`
  parameter bit DemuxUniqueIds = 1'b0,
  /// The actual slice width of a transaction ID that determines the uniques of an ID.
  /// This directly translates to the amount of counters instantiated:
  /// `2**DemuxAxiIdUsedWidth`
  ///
  /// Note: This parameter might change in the future.
  parameter int unsigned DemuxAxiIdUsedWidth = AxiIdWidth,
  /// Support atomic operations (ATOPs)
  parameter bit SupportAtops = 1'b1,
  // Channel structs
  parameter type axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  /// Rising-edge clock of all ports
  input  wire     i_clk,
  /// Asynchronous reset, active low
  input  wire     i_rst_n,

  /// Isolate manager port from subordinate port
  input  logic    i_isolate,
  /// Manager port is isolated from subordinate port
  output logic    o_isolated,
  /// There are AXI transactions outstanding
  output logic    o_outstanding,

  //////////////////////
  // Subordinate Port //
  //////////////////////
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

  //////////////////
  // Manager port //
  //////////////////
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
  ///////////////////////////////
  // Parameters and sanitation //
  ///////////////////////////////
  if (MaxTxn <= 2) $fatal(1, "Parameter: 'MaxTxn' Must not be at least 3;");

  if (AxiIdWidth   != $bits(i_axi_s_aw.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match port width of: 'i_axi_s_aw.id';");
  if (AxiIdWidth   != $bits(o_axi_s_b.id))  $fatal(1, "Parameter: 'AxiIdWidth' does not match port width of: 'o_axi_s_b.id';");

  if (AxiIdWidth   != $bits(i_axi_s_ar.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match port width of: 'i_axi_s_ar.id';");
  if (AxiIdWidth   != $bits(o_axi_s_r.id))  $fatal(1, "Parameter: 'AxiIdWidth' does not match port width of: 'o_axi_s_r.id';");

  if (AxiDataWidth != $bits(i_axi_s_w.data)) $fatal(1, "Parameter: 'AxiDataWidth' does not match port width of: 'i_axi_s_w.data';");
  if (AxiDataWidth != $bits(o_axi_s_r.data)) $fatal(1, "Parameter: 'AxiDataWidth' does not match port width of: 'o_axi_s_r.data';");

  ///////////////////////////////////////////////////
  // Terminate transactions properly when isolated //
  ///////////////////////////////////////////////////
  // the number of demux ports depends on if one wants to have error response when isolated
  localparam int unsigned DemuxPorts = TerminateTxn ? 2 : 1;
  typedef enum logic {
    IdxPort  = 1'b0,
    IdxError = 1'b1
  } demux_port_idx_e;

  logic    send_aw_to_error;
  logic    send_ar_to_error;

  axi_aw_t axi_s_aw;
  logic    axi_s_aw_valid;
  logic    axi_s_aw_ready;
  axi_w_t  axi_s_w;
  logic    axi_s_w_valid;
  logic    axi_s_w_ready;
  axi_b_t  axi_s_b;
  logic    axi_s_b_valid;
  logic    axi_s_b_ready;
  axi_ar_t axi_s_ar;
  logic    axi_s_ar_valid;
  logic    axi_s_ar_ready;
  axi_r_t  axi_s_r;
  logic    axi_s_r_valid;
  logic    axi_s_r_ready;

  axi_aw_t axi_m_aw[DemuxPorts];
  logic    axi_m_aw_valid[DemuxPorts];
  logic    axi_m_aw_ready[DemuxPorts];
  axi_w_t  axi_m_w[DemuxPorts];
  logic    axi_m_w_valid[DemuxPorts];
  logic    axi_m_w_ready[DemuxPorts];
  axi_b_t  axi_m_b[DemuxPorts];
  logic    axi_m_b_valid[DemuxPorts];
  logic    axi_m_b_ready[DemuxPorts];
  axi_ar_t axi_m_ar[DemuxPorts];
  logic    axi_m_ar_valid[DemuxPorts];
  logic    axi_m_ar_ready[DemuxPorts];
  axi_r_t  axi_m_r[DemuxPorts];
  logic    axi_m_r_valid[DemuxPorts];
  logic    axi_m_r_ready[DemuxPorts];

  /////////////////////
  // Isolation Logic //
  /////////////////////

  // plus 1 in clog for accouning no open transaction, plus one bit for atomic injection
  localparam int unsigned CounterWidth = cc_math_pkg::index_width(MaxTxn + 32'd1) + 32'd1;
  typedef logic [CounterWidth-1:0] count_t;

  ////////////////////////////////////////////////////
  // Flags for transactions on the subordinate port //
  ////////////////////////////////////////////////////
  logic txn_s_aw;
  logic txn_s_w;
  logic txn_s_b;
  logic txn_s_ar;
  logic txn_s_r;

  always_comb txn_s_aw = (i_axi_s_aw_valid && o_axi_s_aw_ready);
  always_comb txn_s_w  = (i_axi_s_w_valid  && o_axi_s_w_ready);
  always_comb txn_s_b  = (o_axi_s_b_valid  && i_axi_s_b_ready);
  always_comb txn_s_ar = (i_axi_s_ar_valid && o_axi_s_ar_ready);
  always_comb txn_s_r  = (o_axi_s_r_valid  && i_axi_s_r_ready);

  //////////////////////////
  // Transaction Counters //
  //////////////////////////
  logic   increase_aw;
  logic   decrease_aw;
  logic   inject_atop;
  logic   decrease_w;

  always_comb begin
    increase_aw = 1'b0;
    inject_atop = 1'b0;

    // On atomic operations giving a read response inject a fake count into AR
    if (txn_s_aw) begin
      increase_aw = 1'b1;
      if (SupportAtops) begin
        inject_atop = i_axi_s_aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX];
      end
    end
  end

  always_comb decrease_w  = (txn_s_w && i_axi_s_w.last);
  always_comb decrease_aw =  txn_s_b;

  count_t     increment_ar;
  logic       increase_ar;
  logic       decrease_ar;
  logic       txn_s_r_last;
  always_comb txn_s_r_last = txn_s_r && o_axi_s_r.last;

  always_comb begin
    increase_ar  = 1'b0;
    increment_ar = count_t'(1);
    decrease_ar  = 1'b0;

    unique case ({txn_s_ar, txn_s_r_last, inject_atop})
      3'b100: increase_ar = 1'b1; // Only Transaction on AR
      3'b010: decrease_ar = 1'b1; // Only Transaction on R
      3'b001: increase_ar = 1'b1; // Only injected ATOP
      3'b101: begin
        increase_ar  = 1'b1;
        increment_ar = count_t'(2);
      end
      3'b111: increase_ar = 1'b1;
      default: /* do nothing:
        3'b000: No transactions happening
        3'b110: AR and R cancel each other out
        3'b011: R and inject cancel each other out
      */;
    endcase
  end

  count_t pending_aw_q;
  count_t pending_w_q;
  count_t pending_ar_q;

  logic   overflow_aw;
  logic   overflow_ar;

  cc_cnt_delta #(
    .Width         (CounterWidth),
    .StickyOverflow(1'b0)
  ) u_cnt_pending_aw (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (decrease_aw ^ increase_aw),
    .i_cnt_down(decrease_aw),
    .i_delta   (count_t'(1)),
    .o_q       (pending_aw_q),
    .i_d       (count_t'(0)),
    .i_d_load  (1'b0),
    .o_overflow(overflow_aw)
  );

  cc_cnt_delta #(
    .Width         (CounterWidth),
    .StickyOverflow(1'b0)
  ) u_cnt_pending_w (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (decrease_w ^ increase_aw), // W is announced via an AW
    .i_cnt_down(decrease_w),
    .i_delta   (count_t'(1)),
    .o_q       (pending_w_q),
    .i_d       (count_t'(0)),
    .i_d_load  (1'b0),
    .o_overflow(/* open */)
  );

  cc_cnt_delta #(
    .Width         (CounterWidth),
    .StickyOverflow(1'b0)
  ) u_cnt_pending_ar (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (decrease_ar ^ increase_ar),
    .i_cnt_down(decrease_ar),
    .i_delta   (increment_ar),
    .o_q       (pending_ar_q),
    .i_d       (count_t'(0)),
    .i_d_load  (1'b0),
    .o_overflow(overflow_ar)
  );

  // Flags for stopping further transactions
  logic at_max_txn_aw;
  logic at_max_txn_ar;
  // AW also depends on AR because of the atop injection...
  // Probably overkill to also listen on the overflow, to be save.
  always_comb at_max_txn_aw = overflow_aw | (pending_aw_q >= count_t'(MaxTxn)) | at_max_txn_ar;
  always_comb at_max_txn_ar = overflow_ar | (pending_ar_q >= count_t'(MaxTxn));

  // Flags for saying that there are no open txn
  logic no_active_aw;
  logic no_active_ar;
  always_comb no_active_aw = (pending_aw_q == count_t'(0)) & (pending_w_q == count_t'(0));
  always_comb no_active_ar = (pending_ar_q == count_t'(0));

  always_comb o_outstanding = !(no_active_aw && no_active_ar) || i_axi_s_aw_valid || i_axi_s_ar_valid;


  ///////////////////////
  // Perform isolation //
  ///////////////////////
  // We need controll over the handshaking of AW and AR, recast to keep the names alugned
  typedef enum logic [2:0] {
    Connect,
    DrainForIsolate,
    Isolate,
    DrainForConnect
  } isolate_state_e;
  isolate_state_e state_aw_d, state_aw_q, state_ar_d, state_ar_q;
  logic           state_aw_update,        state_ar_update;
  logic           accept_aw;
  logic           accept_w;
  logic           accept_ar;

  ///////////////////////
  // Write transaction //
  ///////////////////////
  // W channel is open only if there are expected Txn
  always_comb begin
    // Default assignments
    state_aw_d       = state_aw_q;
    state_aw_update  = 1'b0;
    // Connect channel per default
    accept_aw        = 1'b1;
    accept_w         = i_axi_s_aw_valid || (|pending_w_q);
    send_aw_to_error = 1'b0;
    unique case (state_aw_q)
      Connect:  begin // Normal operation
        // Cut valid handshake if a counter capacity is reached.  It has to check AR counter in case
        // of atomics.  Counters are wide enough to account for injected count in the read response
        // counter.
        if (at_max_txn_aw) begin
          accept_aw = 1'b0;
          accept_w  = |pending_w_q;
          if (i_isolate) begin
            state_aw_d      = DrainForIsolate;
            state_aw_update = 1'b1;
          end
        end else begin
          // Only switch if there is an active transaction or no new request
          if (
            i_isolate
            && (!i_axi_s_aw_valid || txn_s_aw)
          ) begin
            state_aw_d      = DrainForIsolate;
            state_aw_update = 1'b1;
          end
        end
      end
      DrainForIsolate: begin // cut the AW channel until counter is zero
        accept_aw = 1'b0;
        accept_w  = |pending_w_q;
        // To be safe wait until no transactions are in flight anymore
        if (no_active_aw && no_active_ar) begin
          state_aw_d      = Isolate;
          state_aw_update = 1'b1;
        end
      end
      Isolate: begin
        accept_aw        = TerminateTxn;
        accept_w         = |pending_w_q;
        send_aw_to_error = 1'b1;
        if (!i_isolate) begin
          if (TerminateTxn) begin
            // Only switch if there is no active request going on
            if (!i_axi_s_aw_valid || txn_s_aw) begin
              state_aw_d      = DrainForConnect;
              state_aw_update = 1'b1;
            end
          end else begin
            state_aw_d      = Connect;
            state_aw_update = 1'b1;
          end
        end
      end
      DrainForConnect: begin
        accept_aw = 1'b0;
        accept_w  = |pending_w_q;
        // To be safe wait until no transactions are in flight anymore
        if (no_active_aw && no_active_ar) begin
          state_aw_d      = Connect;
          state_aw_update = 1'b1;
        end
      end
      default: /* do nothing */;
    endcase
  end

  //////////////////////
  // Read transaction //
  //////////////////////
  always_comb begin
    // Default assignments
    state_ar_d       = state_ar_q;
    state_ar_update  = 1'b0;
    // Connect channel per default
    accept_ar        = 1'b1;
    send_ar_to_error = 1'b0;
    unique case (state_ar_q)
      Connect:  begin // Normal operation
        // Cut valid handshake if a counter capacity is reached.  It has to check AR counter in case
        // of atomics.  Counters are wide enough to account for injected count in the read response
        // counter.
        if (at_max_txn_ar) begin
          accept_ar = 1'b0;
          if (i_isolate) begin
            state_ar_d      = DrainForIsolate;
            state_ar_update = 1'b1;
          end
        end else begin
          // Only switch if there is an active transaction or no new request
          if (
            i_isolate
            && (!i_axi_s_ar_valid || txn_s_ar)
          ) begin
            state_ar_d      = DrainForIsolate;
            state_ar_update = 1'b1;
          end
        end
      end
      DrainForIsolate: begin // cut the AW channel until counter is zero
        accept_ar = 1'b0;
        // To be safe wait until no transactions are in flight anymore
        if (no_active_aw && no_active_ar) begin
          state_ar_d      = Isolate;
          state_ar_update = 1'b1;
        end
      end
      Isolate: begin
        accept_ar        = TerminateTxn;
        send_ar_to_error = 1'b1;
        if (!i_isolate) begin
          if (TerminateTxn) begin
            // Only switch if there is no active request going on
            if (!i_axi_s_ar_valid || txn_s_ar) begin
              state_ar_d      = DrainForConnect;
              state_ar_update = 1'b1;
            end
          end else begin
            state_ar_d      = Connect;
            state_ar_update = 1'b1;
          end
        end
      end
      DrainForConnect: begin
        accept_ar = 1'b0;
        // To be safe wait until no transactions are in flight anymore
        if (no_active_aw && no_active_ar) begin
          state_ar_d      = Connect;
          state_ar_update = 1'b1;
        end
      end
      default: /* do nothing */;
    endcase
  end

  cc_stream_disconnect #(
    .data_t(axi_aw_t)
  ) u_accept_aw (
    .i_disconnect (~accept_aw),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (i_axi_s_aw),
    .i_valid      (i_axi_s_aw_valid),
    .o_ready      (o_axi_s_aw_ready),
    .o_data       (axi_s_aw),
    .o_valid      (axi_s_aw_valid),
    .i_ready      (axi_s_aw_ready)
  );

  cc_stream_disconnect #(
    .data_t(axi_w_t)
  ) u_accept_w (
    .i_disconnect (~accept_w),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (i_axi_s_w),
    .i_valid      (i_axi_s_w_valid),
    .o_ready      (o_axi_s_w_ready),
    .o_data       (axi_s_w),
    .o_valid      (axi_s_w_valid),
    .i_ready      (axi_s_w_ready)
  );

  cc_stream_disconnect #(
    .data_t(axi_ar_t)
  ) u_accept_ar (
    .i_disconnect (~accept_ar),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (i_axi_s_ar),
    .i_valid      (i_axi_s_ar_valid),
    .o_ready      (o_axi_s_ar_ready),
    .o_data       (axi_s_ar),
    .o_valid      (axi_s_ar_valid),
    .i_ready      (axi_s_ar_ready)
  );

  // Return channels are connected always
  always_comb o_axi_s_b       =   axi_s_b;
  always_comb o_axi_s_b_valid =   axi_s_b_valid;
  always_comb   axi_s_b_ready = i_axi_s_b_ready;

  always_comb o_axi_s_r       =   axi_s_r;
  always_comb o_axi_s_r_valid =   axi_s_r_valid;
  always_comb   axi_s_r_ready = i_axi_s_r_ready;

  // the isolated output signal
  assign o_isolated = (state_aw_q == Isolate && state_ar_q == Isolate);

  ////////////////
  // Flip Flops //
  ////////////////

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      state_aw_q <= Isolate;
      state_ar_q <= Isolate;
    end
    else begin
      if (state_aw_update) state_aw_q <= state_aw_d;
      if (state_ar_update) state_ar_q <= state_ar_d;
    end
  end

  ////////////////////////
  // Error Response Mux //
  ////////////////////////
  axe_axi_demux #(
    .NumPorts    (DemuxPorts),
    .AxiIdWidth  (AxiIdWidth),
    .MaxTxn      (MaxTxn),
    .AxiLookBits (DemuxAxiIdUsedWidth),
    .SupportAtops(SupportAtops),
    .UniqueIds   (DemuxUniqueIds),
    .CutAw       (DemuxCutAw),
    .CutW        (DemuxCutW),
    .CutB        (DemuxCutB),
    .CutAr       (DemuxCutAr),
    .CutR        (DemuxCutR),
    .axi_aw_t    (axi_aw_t),
    .axi_w_t     (axi_w_t),
    .axi_b_t     (axi_b_t),
    .axi_ar_t    (axi_ar_t),
    .axi_r_t     (axi_r_t)
  ) u_axe_axi_demux (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw       (axi_s_aw),
    .i_axi_s_aw_select(send_aw_to_error),
    .i_axi_s_aw_valid (axi_s_aw_valid),
    .o_axi_s_aw_ready (axi_s_aw_ready),
    .i_axi_s_w        (axi_s_w),
    .i_axi_s_w_valid  (axi_s_w_valid),
    .o_axi_s_w_ready  (axi_s_w_ready),
    .o_axi_s_b        (axi_s_b),
    .o_axi_s_b_valid  (axi_s_b_valid),
    .i_axi_s_b_ready  (axi_s_b_ready),
    .i_axi_s_ar       (axi_s_ar),
    .i_axi_s_ar_select(send_ar_to_error),
    .i_axi_s_ar_valid (axi_s_ar_valid),
    .o_axi_s_ar_ready (axi_s_ar_ready),
    .o_axi_s_r        (axi_s_r),
    .o_axi_s_r_valid  (axi_s_r_valid),
    .i_axi_s_r_ready  (axi_s_r_ready),
    .o_axi_m_aw       (axi_m_aw),
    .o_axi_m_aw_valid (axi_m_aw_valid),
    .i_axi_m_aw_ready (axi_m_aw_ready),
    .o_axi_m_w        (axi_m_w),
    .o_axi_m_w_valid  (axi_m_w_valid),
    .i_axi_m_w_ready  (axi_m_w_ready),
    .i_axi_m_b        (axi_m_b),
    .i_axi_m_b_valid  (axi_m_b_valid),
    .o_axi_m_b_ready  (axi_m_b_ready),
    .o_axi_m_ar       (axi_m_ar),
    .o_axi_m_ar_valid (axi_m_ar_valid),
    .i_axi_m_ar_ready (axi_m_ar_ready),
    .i_axi_m_r        (axi_m_r),
    .i_axi_m_r_valid  (axi_m_r_valid),
    .o_axi_m_r_ready  (axi_m_r_ready)
  );

  if (TerminateTxn) begin : gen_term_txn
    axe_axi_err_sub #(
      .AxiIdWidth  (AxiIdWidth),
      .Resp        (axi_pkg::RespSlvErr),
      .DataWidth   (AxiDataWidth),
      .ReadData    (AxiDataWidth'(32'h1501_A7ED)),
      .MaxTxn      (2),
      .SupportAtops(SupportAtops),
      .axi_aw_t    (axi_aw_t),
      .axi_w_t     (axi_w_t),
      .axi_b_t     (axi_b_t),
      .axi_ar_t    (axi_ar_t),
      .axi_r_t     (axi_r_t)
    ) u_axe_axi_err_sub (
      .i_clk,
      .i_rst_n,
      .i_axi_s_aw      (axi_m_aw[IdxError]),
      .i_axi_s_aw_valid(axi_m_aw_valid[IdxError]),
      .o_axi_s_aw_ready(axi_m_aw_ready[IdxError]),
      .i_axi_s_w       (axi_m_w[IdxError]),
      .i_axi_s_w_valid (axi_m_w_valid[IdxError]),
      .o_axi_s_w_ready (axi_m_w_ready[IdxError]),
      .o_axi_s_b       (axi_m_b[IdxError]),
      .o_axi_s_b_valid (axi_m_b_valid[IdxError]),
      .i_axi_s_b_ready (axi_m_b_ready[IdxError]),
      .i_axi_s_ar      (axi_m_ar[IdxError]),
      .i_axi_s_ar_valid(axi_m_ar_valid[IdxError]),
      .o_axi_s_ar_ready(axi_m_ar_ready[IdxError]),
      .o_axi_s_r       (axi_m_r[IdxError]),
      .o_axi_s_r_valid (axi_m_r_valid[IdxError]),
      .i_axi_s_r_ready (axi_m_r_ready[IdxError])
    );
  end

  /////////////////////
  // Isolation Logic //
  /////////////////////
  // Silence all manager port signals when we are isolated
  cc_stream_disconnect #(
    .data_t(axi_aw_t)
  ) u_disconnect_aw (
    .i_disconnect (o_isolated),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (axi_m_aw[IdxPort]),
    .i_valid      (axi_m_aw_valid[IdxPort]),
    .o_ready      (axi_m_aw_ready[IdxPort]),
    .o_data       (o_axi_m_aw),
    .o_valid      (o_axi_m_aw_valid),
    .i_ready      (i_axi_m_aw_ready)
  );

  cc_stream_disconnect #(
    .data_t(axi_w_t)
  ) u_disconnect_w (
    .i_disconnect (o_isolated),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (axi_m_w[IdxPort]),
    .i_valid      (axi_m_w_valid[IdxPort]),
    .o_ready      (axi_m_w_ready[IdxPort]),
    .o_data       (o_axi_m_w),
    .o_valid      (o_axi_m_w_valid),
    .i_ready      (i_axi_m_w_ready)
  );

  cc_stream_disconnect #(
    .data_t(axi_b_t)
  ) u_disconnect_b (
    .i_disconnect (o_isolated),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (i_axi_m_b),
    .i_valid      (i_axi_m_b_valid),
    .o_ready      (o_axi_m_b_ready),
    .o_data       (axi_m_b[IdxPort]),
    .o_valid      (axi_m_b_valid[IdxPort]),
    .i_ready      (axi_m_b_ready[IdxPort])
  );

  cc_stream_disconnect #(
    .data_t(axi_ar_t)
  ) u_disconnect_ar (
    .i_disconnect (o_isolated),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (axi_m_ar[IdxPort]),
    .i_valid      (axi_m_ar_valid[IdxPort]),
    .o_ready      (axi_m_ar_ready[IdxPort]),
    .o_data       (o_axi_m_ar),
    .o_valid      (o_axi_m_ar_valid),
    .i_ready      (i_axi_m_ar_ready)
  );

  cc_stream_disconnect #(
    .data_t(axi_r_t)
  ) u_disconnect_r (
    .i_disconnect (o_isolated),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(/* not used */),
    .i_data       (i_axi_m_r),
    .i_valid      (i_axi_m_r_valid),
    .o_ready      (o_axi_m_r_ready),
    .o_data       (axi_m_r[IdxPort]),
    .o_valid      (axi_m_r_valid[IdxPort]),
    .i_ready      (axi_m_r_ready[IdxPort])
  );
endmodule
