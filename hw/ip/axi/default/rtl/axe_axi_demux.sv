// Copyright (c) 2019 ETH Zurich and University of Bologna.
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
// - Michael Rogenmoser <michaero@iis.ee.ethz.ch>
// - Thomas Benz <tbenz@iis.ee.ethz.ch>
// - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// Demultiplex one AXI4+ATOP slave port to multiple AXI4+ATOP master ports.
///
/// The AW and AR slave channels each have a `select` input to determine to which master port the
/// current request is sent.  The `select` can, for example, be driven by an address decoding module
/// to map address ranges to different AXI slaves.
///
/// ## Design overview
///
/// ![Block diagram](module.axi_demux.png "Block diagram")
///
/// Beats on the W channel are routed by demultiplexer according to the selection for the
/// corresponding AW beat.  This relies on the AXI property that W bursts must be sent in the same
/// order as AW beats and beats from different W bursts may not be interleaved.
///
/// Beats on the B and R channel are multiplexed from the master ports to the slave port with
/// a round-robin arbitration tree.
module axe_axi_demux #(
  parameter int unsigned  NumPorts       = 32'd2,
  /// The ID width of the Transaction
  parameter int unsigned  AxiIdWidth     = axe_axi_default_types_pkg::WIDTH_ID_4,
  parameter int unsigned  MaxTxn         = 32'd4,
  parameter int unsigned  AxiLookBits    = 32'd3,
  parameter bit           SupportAtops   = 1'b1,
  parameter bit           UniqueIds      = 1'b0,
  /// Add a spill register at the subordinate AW channel
  parameter bit           CutAw          = 1'b1,
  /// Add a spill register at the subordinate W channel
  parameter bit           CutW           = 1'b0,
  /// Add a spill register at the subordinate B channel
  parameter bit           CutB           = 1'b0,
  /// Add a spill register at the subordinate AR channel
  parameter bit           CutAr          = 1'b1,
  /// Add a spill register at the subordinate R channel
  parameter bit           CutR           = 1'b0,
  parameter type          axi_aw_t       = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type          axi_w_t        = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type          axi_b_t        = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type          axi_ar_t       = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type          axi_r_t        = axe_axi_default_types_pkg::axi_r_4_64_4_t,
  // Dependent parameters, DO NOT OVERRIDE!
  localparam int unsigned SelectWidth    = cc_math_pkg::index_width(NumPorts),
  localparam type         select_t       = logic[SelectWidth-1:0]
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  // doc async
  input  wire i_rst_n,
  // doc sync i_clk

  // Subordinate Port
  input  axi_aw_t i_axi_s_aw,
  input  select_t i_axi_s_aw_select,
  input  logic    i_axi_s_aw_valid,
  output logic    o_axi_s_aw_ready,
  input  axi_w_t  i_axi_s_w,
  input  logic    i_axi_s_w_valid,
  output logic    o_axi_s_w_ready,
  output axi_b_t  o_axi_s_b,
  output logic    o_axi_s_b_valid,
  input  logic    i_axi_s_b_ready,
  input  axi_ar_t i_axi_s_ar,
  input  select_t i_axi_s_ar_select,
  input  logic    i_axi_s_ar_valid,
  output logic    o_axi_s_ar_ready,
  output axi_r_t  o_axi_s_r,
  output logic    o_axi_s_r_valid,
  input  logic    i_axi_s_r_ready,

  // Manager Ports
  output axi_aw_t o_axi_m_aw[NumPorts],
  output logic    o_axi_m_aw_valid[NumPorts],
  input  logic    i_axi_m_aw_ready[NumPorts],
  output axi_w_t  o_axi_m_w[NumPorts],
  output logic    o_axi_m_w_valid[NumPorts],
  input  logic    i_axi_m_w_ready[NumPorts],
  input  axi_b_t  i_axi_m_b[NumPorts],
  input  logic    i_axi_m_b_valid[NumPorts],
  output logic    o_axi_m_b_ready[NumPorts],
  output axi_ar_t o_axi_m_ar[NumPorts],
  output logic    o_axi_m_ar_valid[NumPorts],
  input  logic    i_axi_m_ar_ready[NumPorts],
  input  axi_r_t  i_axi_m_r[NumPorts],
  input  logic    i_axi_m_r_valid[NumPorts],
  output logic    o_axi_m_r_ready[NumPorts]
);
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////

  if (NumPorts == 0)                      $fatal(1, "Parameter: 'NumPorts' has to be at least 1;");
  if (AxiIdWidth != $bits(i_axi_s_aw.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match aw.id;");
  if (AxiIdWidth < AxiLookBits)           $fatal(1, "Parameter: 'AxiIdWidth' has to be at least 'AxiLookBits';");
  if (MaxTxn == 0)                        $fatal(1, "Parameter: 'MaxTxn' has to be larger than 0;");

  localparam int unsigned IdCounterWidth = cc_math_pkg::index_width(MaxTxn);
  typedef logic [IdCounterWidth-1:0] id_cnt_t;

  //////////////////////////
  // Input cutting stage  //
  // Extra packing needed //
  //////////////////////////

  typedef struct packed {
    axi_aw_t aw;
    select_t select;
  } axi_aw_select_t;

  typedef struct packed {
    axi_ar_t ar;
    select_t select;
  } axi_ar_select_t;

  axi_aw_select_t inp_aw_select;
  axi_ar_select_t inp_ar_select;

  always_comb begin
    inp_aw_select = '{
      aw:     i_axi_s_aw,
      select: i_axi_s_aw_select
    };
    inp_ar_select = '{
      ar:     i_axi_s_ar,
      select: i_axi_s_ar_select
    };
  end

  axi_aw_select_t cut_aw_select;
  logic           cut_aw_valid,  cut_aw_ready;
  axi_w_t         cut_w;
  logic           cut_w_valid,   cut_w_ready;
  axi_b_t         cut_b;
  logic           cut_b_valid,   cut_b_ready;
  axi_ar_select_t cut_ar_select;
  logic           cut_ar_valid,  cut_ar_ready;
  axi_r_t         cut_r;
  logic           cut_r_valid,   cut_r_ready;

  axe_axi_cut #(
    .CutAw   (CutAw),
    .CutW    (CutW),
    .CutB    (CutB),
    .CutAr   (CutAr),
    .CutR    (CutR),
    .axi_aw_t(axi_aw_select_t),
    .axi_w_t (axi_w_t),
    .axi_b_t (axi_b_t),
    .axi_ar_t(axi_ar_select_t),
    .axi_r_t (axi_r_t)
  ) u_axi_cut (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (inp_aw_select),
    .i_axi_s_aw_valid,
    .o_axi_s_aw_ready,
    .i_axi_s_w,
    .i_axi_s_w_valid,
    .o_axi_s_w_ready,
    .o_axi_s_b,
    .o_axi_s_b_valid,
    .i_axi_s_b_ready,
    .i_axi_s_ar      (inp_ar_select),
    .i_axi_s_ar_valid,
    .o_axi_s_ar_ready,
    .o_axi_s_r,
    .o_axi_s_r_valid,
    .i_axi_s_r_ready,
    .o_axi_m_aw      (cut_aw_select),
    .o_axi_m_aw_valid(cut_aw_valid),
    .i_axi_m_aw_ready(cut_aw_ready),
    .o_axi_m_w       (cut_w),
    .o_axi_m_w_valid (cut_w_valid),
    .i_axi_m_w_ready (cut_w_ready),
    .i_axi_m_b       (cut_b),
    .i_axi_m_b_valid (cut_b_valid),
    .o_axi_m_b_ready (cut_b_ready),
    .o_axi_m_ar      (cut_ar_select),
    .o_axi_m_ar_valid(cut_ar_valid),
    .i_axi_m_ar_ready(cut_ar_ready),
    .i_axi_m_r       (cut_r),
    .i_axi_m_r_valid (cut_r_valid),
    .o_axi_m_r_ready (cut_r_ready)
  );

  if (NumPorts == 1) begin : gen_no_demux
  //////////////////////////////////////////
  // Pass-through if only one master port //
  //////////////////////////////////////////
    always_comb begin
      o_axi_m_aw[0]       = cut_aw_select.aw;
      o_axi_m_aw_valid[0] = cut_aw_valid;
      cut_aw_ready        = i_axi_m_aw_ready[0];
      o_axi_m_w[0]        = cut_w;
      o_axi_m_w_valid[0]  = cut_w_valid;
      cut_w_ready         = i_axi_m_w_ready[0];
      cut_b               = i_axi_m_b[0];
      cut_b_valid         = i_axi_m_b_valid[0];
      o_axi_m_b_ready[0]  = cut_b_ready;
      o_axi_m_ar[0]       = cut_ar_select.ar;
      o_axi_m_ar_valid[0] = cut_ar_valid;
      cut_ar_ready        = i_axi_m_ar_ready[0];
      cut_r               = i_axi_m_r[0];
      cut_r_valid         = i_axi_m_r_valid[0];
      o_axi_m_r_ready[0]  = cut_r_ready;
    end
  end else begin : gen_demux
  ///////////
  // Demux //
  ///////////

    ///////////////////////
    // Write Transaction //
    ///////////////////////

    // Register which locks the AW valid signal
    logic                     lock_aw_valid_d,    lock_aw_valid_q, load_aw_lock;
    logic                     aw_valid,           aw_ready;

    // AW ID counter
    select_t                  lookup_aw_select;
    logic                     aw_select_occupied;
    logic                     aw_id_cnt_full,     ar_id_cnt_full;
    // Upon an ATOP load, inject IDs from the AW into the AR channel
    logic                     atop_inject;

    // W select counter: stores the decision to which master W beats should go
    select_t                  w_select,           w_select_q;
    logic                     w_select_valid;
    id_cnt_t                  w_open;
    logic                     w_cnt_up,           w_cnt_down;

    /////////////////////
    // AW Channel      //
    /////////////////////

    // Control of the AW handshake
    always_comb begin
      // AXI Handshakes
      cut_aw_ready = 1'b0;
      aw_valid     = 1'b0;
      // `lock_aw_valid`, used to be protocol conform as it is not allowed to deassert
      // a valid if there was no corresponding ready. As this process has to be able to inject
      // an AXI ID into the counter of the AR channel on an ATOP, there could be a case where
      // this process waits on `aw_ready` but in the mean time on the AR channel the counter gets
      // full.
      lock_aw_valid_d = lock_aw_valid_q;
      load_aw_lock    = 1'b0;
      // AW ID counter and W FIFO
      w_cnt_up        = 1'b0;
      // ATOP injection into ar counter
      atop_inject     = 1'b0;
      // we had an arbitration decision, the valid is locked, wait for the transaction
      if (lock_aw_valid_q) begin
        aw_valid = 1'b1;
        // transaction
        if (aw_ready) begin
          cut_aw_ready    = 1'b1;
          lock_aw_valid_d = 1'b0;
          load_aw_lock    = 1'b1;
          // inject the ATOP if necessary
          atop_inject     = cut_aw_select.aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX] & SupportAtops;
        end
      end else begin
        // An AW can be handled if `i_aw_id_counter` and `i_counter_open_w` are not full.  An ATOP that
        // requires an R response can be handled if additionally `i_ar_id_counter` is not full (this
        // only applies if ATOPs are supported at all).
        if (   !aw_id_cnt_full
            && (w_open != {IdCounterWidth{1'b1}})
            && (
                   !(ar_id_cnt_full && cut_aw_select.aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX])
                || !SupportAtops
               )
        ) begin
          // There is a valid AW vector make the id lookup and go further, if it passes.
          // Also stall if previous transmitted AWs still have active W's in flight.
          // This prevents deadlocking of the W channel. The counters are there for the
          // Handling of the B responses.
          if (cut_aw_valid &&
                ((w_open == '0) || (w_select == cut_aw_select.select)) &&
                (!aw_select_occupied || (cut_aw_select.select == lookup_aw_select))) begin
            // connect the handshake
            aw_valid     = 1'b1;
            // push arbitration to the W FIFO regardless, do not wait for the AW transaction
            w_cnt_up     = 1'b1;
            // on AW transaction
            if (aw_ready) begin
              cut_aw_ready = 1'b1;
              atop_inject  = cut_aw_select.aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX] & SupportAtops;
            // no AW transaction this cycle, lock the decision
            end else begin
              lock_aw_valid_d = 1'b1;
              load_aw_lock    = 1'b1;
            end
          end
        end
      end
    end

    // lock the valid signal, as the selection gets pushed into the W FIFO on first assertion,
    // prevent further pushing
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)          lock_aw_valid_q <= '0;
      else if (load_aw_lock) lock_aw_valid_q <= lock_aw_valid_d;
    end

    cc_stream_demux_unpack #(
      .data_t     (axi_aw_t),
      .NumStreams (NumPorts),
      .DropOnError(1'b0)
    ) u_aw_demux (
      .i_data  (cut_aw_select.aw),
      .i_select(cut_aw_select.select),
      .i_valid (aw_valid),
      .o_ready (aw_ready),
      .o_error (/*open*/),
      .o_data  (o_axi_m_aw),
      .o_valid (o_axi_m_aw_valid),
      .i_ready (i_axi_m_aw_ready)
    );

    if (UniqueIds) begin : gen_unique_ids_aw
      // If the `UniqueIds` parameter is set, each write transaction has an ID that is unique among
      // all in-flight write transactions, or all write transactions with a given ID target the same
      // master port as all write transactions with the same ID, or both.  This means that the
      // signals that are driven by the ID counters if this parameter is not set can instead be
      // derived from existing signals.  The ID counters can therefore be omitted.
      assign lookup_aw_select = cut_aw_select.select;
      assign aw_select_occupied = 1'b0;
      assign aw_id_cnt_full = 1'b0;
    end else begin : gen_aw_id_counter
      axe_axi_demux_id_counters #(
        .AxiIdBits         ( AxiLookBits    ),
        .CounterWidth      ( IdCounterWidth ),
        .man_port_select_t ( select_t       )
      ) u_aw_id_counter (
        .i_clk,
        .i_rst_n,
        .i_lookup_axi_id             (cut_aw_select.aw.id[0+:AxiLookBits]),
        .o_lookup_mst_select         (lookup_aw_select),
        .o_lookup_mst_select_occupied(aw_select_occupied),
        .o_full                      (aw_id_cnt_full),
        .i_inject_axi_id             ('0),
        .i_inject                    (1'b0),
        .i_push_axi_id               (cut_aw_select.aw.id[0+:AxiLookBits]),
        .i_push_mst_select           (cut_aw_select.select),
        .i_push                      (w_cnt_up),
        .i_pop_axi_id                (cut_b.id[0+:AxiLookBits]),
        .i_pop                       (cut_b_valid & cut_b_ready)
      );
      // pop from ID counter on outward transaction
    end

    ////////////////
    //  W Channel //
    ////////////////

    // This counter steers the demultiplexer of the W channel.
    // `w_select` determines, which handshaking is connected.
    // AWs are only forwarded, if the counter is empty, or `w_select_q` is the same as
    // `i_axi_s_aw_select`.
    cc_cnt_delta #(
      .Width         (IdCounterWidth),
      .StickyOverflow(1'b0)
    ) u_counter_open_w (
      .i_clk,
      .i_rst_n,
      .i_flush   (1'b0),
      .i_cnt_en  (w_cnt_up ^ w_cnt_down),
      .i_cnt_down(w_cnt_down),
      .i_delta   (id_cnt_t'(1)),
      .o_q       (w_open),
      .i_d       (id_cnt_t'(0)),
      .i_d_load  (1'b0),
      .o_overflow(/*open*/)
    );

    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)      w_select_q <= select_t'(0);
      else if (w_cnt_up) w_select_q <= cut_aw_select.select;
    end

    assign w_select       = (|w_open) ? w_select_q : cut_aw_select.select;
    assign w_select_valid = w_cnt_up | (|w_open);

    // connect the valid only if we are allowed to by the select
    axi_w_t demux_w;
    logic   demux_w_valid, demux_w_ready;
    logic   demux_w_txn;

    // Only if we
    always_comb w_cnt_down = demux_w_txn & cut_w.last;

    cc_stream_disconnect #(
      .data_t(axi_w_t)
    ) u_w_disconnect (
      .i_disconnect (~w_select_valid),
      .i_drop       (1'b0),
      .o_dropped    (/*open*/),
      .o_transaction(demux_w_txn),
      .i_data       (cut_w),
      .i_valid      (cut_w_valid),
      .o_ready      (cut_w_ready),
      .o_data       (demux_w),
      .o_valid      (demux_w_valid),
      .i_ready      (demux_w_ready)
    );

    cc_stream_demux_unpack #(
      .data_t     (axi_w_t),
      .NumStreams (NumPorts),
      .DropOnError(1'b0)
    ) u_w_demux (
      .i_data  (demux_w),
      .i_select(w_select),
      .i_valid (demux_w_valid),
      .o_ready (demux_w_ready),
      .o_error (/*open*/),
      .o_data  (o_axi_m_w),
      .o_valid (o_axi_m_w_valid),
      .i_ready (i_axi_m_w_ready)
    );

    ////////////////
    //  B Channel //
    ////////////////

    // B channles input into the arbitration
    select_t             arb_b_idx;
    logic [NumPorts-1:0] arb_b_valid, arb_b_ready;

    // Pack the handshaking
    always_comb begin
      arb_b_valid     = {<< {i_axi_m_b_valid}};
      o_axi_m_b_ready = {<< {arb_b_ready}};
    end

    // Arbitration of the different B responses
    rr_arb_tree #(
      .NumIn     (NumPorts),
      .datatype_t(logic),
      .AxiVldRdy (1'b1),
      .LockIn    (1'b1),
      .FairArb   (1'b1)
    ) u_b_mux_rr (
      .i_clk,
      .i_rst_n,
      .flush_i(1'b0),
      .rr_i   ('0),
      .req_i  (arb_b_valid),
      .gnt_o  (arb_b_ready),
      .data_i ('0),
      .gnt_i  (cut_b_ready),
      .req_o  (cut_b_valid),
      .data_o (/*open*/),
      .idx_o  (arb_b_idx)
    );

    // Data Mux
    always_comb begin
      cut_b = '0;
      if (cut_b_valid) cut_b = i_axi_m_b[arb_b_idx];
    end

    //////////////////////
    // Read Transaction //
    //////////////////////

    // AR ID counter
    select_t lookup_ar_select;
    logic    ar_select_occupied;
    logic    ar_push;

    // Register which locks the AR valid signel
    logic lock_ar_valid_d,    lock_ar_valid_q, load_ar_lock;
    logic ar_valid,           ar_ready;

    /////////////////
    //  AR Channel //
    /////////////////

    // control of the AR handshake
    always_comb begin
      // AXI Handshakes
      cut_ar_ready    = 1'b0;
      ar_valid        = 1'b0;
      // `lock_ar_valid`: Used to be protocol conform as it is not allowed to deassert `ar_valid`
      // if there was no corresponding `ar_ready`. There is the possibility that an injection
      // of a R response from an `atop` from the AW channel can change the occupied flag of the
      // `i_ar_id_counter`, even if it was previously empty. This FF prevents the deassertion.
      lock_ar_valid_d = lock_ar_valid_q;
      load_ar_lock    = 1'b0;
      // AR id counter
      ar_push         = 1'b0;
      // The process had an arbitration decision in a previous cycle, the valid is locked,
      // wait for the AR transaction.
      if (lock_ar_valid_q) begin
        ar_valid = 1'b1;
        // transaction
        if (ar_ready) begin
          cut_ar_ready    = 1'b1;
          ar_push         = 1'b1;
          lock_ar_valid_d = 1'b0;
          load_ar_lock    = 1'b1;
        end
      end else begin
        // The process can start handling AR transaction if `i_ar_id_counter` has space.
        if (!ar_id_cnt_full) begin
          // There is a valid AR, so look the ID up.
          if (    cut_ar_valid
              && (    !ar_select_occupied
                  || (cut_ar_select.select == lookup_ar_select)
                 )
          ) begin
            // connect the AR handshake
            ar_valid     = 1'b1;
            // on transaction
            if (ar_ready) begin
              cut_ar_ready = 1'b1;
              ar_push      = 1'b1;
            // no transaction this cycle, lock the valid decision!
            end else begin
              lock_ar_valid_d = 1'b1;
              load_ar_lock    = 1'b1;
            end
          end
        end
      end
    end

    // this ff is needed so that ar does not get de-asserted if an atop gets injected
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)          lock_ar_valid_q <= '0;
      else if (load_ar_lock) lock_ar_valid_q <= lock_ar_valid_d;
    end

    cc_stream_demux_unpack #(
      .data_t     (axi_ar_t),
      .NumStreams (NumPorts),
      .DropOnError(1'b0)
    ) u_ar_demux (
      .i_data  (cut_ar_select.ar),
      .i_select(cut_ar_select.select),
      .i_valid (ar_valid),
      .o_ready (ar_ready),
      .o_error (/*open*/),
      .o_data  (o_axi_m_ar),
      .o_valid (o_axi_m_ar_valid),
      .i_ready (i_axi_m_ar_ready)
    );

    if (UniqueIds) begin : gen_unique_ids_ar
      // If the `UniqueIds` parameter is set, each read transaction has an ID that is unique among
      // all in-flight read transactions, or all read transactions with a given ID target the same
      // master port as all read transactions with the same ID, or both.  This means that the
      // signals that are driven by the ID counters if this parameter is not set can instead be
      // derived from existing signals.  The ID counters can therefore be omitted.
      assign lookup_ar_select = cut_ar_select.select;
      assign ar_select_occupied = 1'b0;
      assign ar_id_cnt_full = 1'b0;
    end else begin : gen_ar_id_counter
      axe_axi_demux_id_counters #(
        .AxiIdBits         (AxiLookBits),
        .CounterWidth      (IdCounterWidth),
        .man_port_select_t (select_t)
      ) u_ar_id_counter (
        .i_clk,
        .i_rst_n,
        .i_lookup_axi_id             (cut_ar_select.ar.id[0+:AxiLookBits]),
        .o_lookup_mst_select         (lookup_ar_select),
        .o_lookup_mst_select_occupied(ar_select_occupied),
        .o_full                      (ar_id_cnt_full),
        .i_inject_axi_id             (cut_aw_select.aw.id[0+:AxiLookBits]),
        .i_inject                    (atop_inject),
        .i_push_axi_id               (cut_ar_select.ar.id[0+:AxiLookBits]),
        .i_push_mst_select           (cut_ar_select.select),
        .i_push                      (ar_push),
        .i_pop_axi_id                (cut_r.id[0+:AxiLookBits]),
        .i_pop                       (cut_r_valid & cut_r_ready & cut_r.last)
      );
    end

    ////////////////
    //  R Channel //
    ////////////////
    // B channles input into the arbitration
    select_t             arb_r_idx;
    logic [NumPorts-1:0] arb_r_valid, arb_r_ready;

    // Pack the handshaking
    always_comb begin
      arb_r_valid     = {<< {i_axi_m_r_valid}};
      o_axi_m_r_ready = {<< {arb_r_ready}};
    end

    // Arbitration of the different r responses
    rr_arb_tree #(
      .NumIn     (NumPorts),
      .datatype_t(logic),
      .AxiVldRdy (1'b1),
      .LockIn    (1'b1),
      .FairArb   (1'b1)
    ) u_r_mux_rr (
      .i_clk,
      .i_rst_n,
      .flush_i(1'b0),
      .rr_i   ('0),
      .req_i  (arb_r_valid),
      .gnt_o  (arb_r_ready),
      .data_i ('0),
      .gnt_i  (cut_r_ready),
      .req_o  (cut_r_valid),
      .data_o (/*open*/),
      .idx_o  (arb_r_idx)
    );

    // Data Mux
    always_comb begin
      cut_r = '0;
      if (cut_r_valid) cut_r = i_axi_m_r[arb_r_idx];
    end

    ////////////////
    // Assertions //
    ////////////////
    `ifndef SYNTHESIS
    `ifdef ASSERTIONS_ON

      property p_select_value(
        valid,
        select
      );
        @(posedge i_clk)
        disable iff (!i_rst_n)
        (valid |-> (select < NumPorts));
      endproperty : p_select_value

      check_aw_select_value : assume property(p_select_value(i_axi_s_aw_valid, i_axi_s_aw_select))
      else $error("i_axi_s_aw_select is %d: AW has selected a slave that is not defined. NumPorts: %d", i_axi_s_aw_select, NumPorts);

      check_ar_select_value : assume property(p_select_value(i_axi_s_ar_valid, i_axi_s_ar_select))
      else $error("i_axi_s_ar_select is %d: AR has selected a slave that is not defined. NumPorts: %d", i_axi_s_ar_select, NumPorts);

      check_s_aw_valid_ready_handshake : assert property(
          axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, i_axi_s_aw_valid, o_axi_s_aw_ready)
      );
      check_s_w_valid_ready_handshake : assert property(
          axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, i_axi_s_w_valid, o_axi_s_w_ready)
      );
      check_s_b_valid_ready_handshake : assert property(
          axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, o_axi_s_b_valid, i_axi_s_b_ready)
      );
      check_s_ar_valid_ready_handshake : assert property(
          axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, i_axi_s_ar_valid, o_axi_s_ar_ready)
      );
      check_s_r_valid_ready_handshake : assert property(
          axe_dv_properties_pkg::p_valid_ready_handshake(i_clk, i_rst_n, o_axi_s_r_valid, i_axi_s_r_ready)
      );

      check_s_aw_valid_ready_vector_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, i_axi_s_aw_valid, o_axi_s_aw_ready, i_axi_s_aw)
      );
      check_s_aw_valid_ready_select_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, i_axi_s_aw_valid, o_axi_s_aw_ready, i_axi_s_aw_select)
      );
      check_s_w_valid_ready_vector_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, i_axi_s_w_valid, o_axi_s_w_ready, i_axi_s_w)
      );
      check_s_b_valid_ready_vector_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_axi_s_b_valid, i_axi_s_b_ready, o_axi_s_b)
      );
      check_s_ar_valid_ready_vector_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, i_axi_s_ar_valid, o_axi_s_ar_ready, i_axi_s_ar)
      );
      check_s_ar_valid_ready_select_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, i_axi_s_ar_valid, o_axi_s_ar_ready, i_axi_s_ar_select)
      );
      check_s_r_valid_ready_vector_stable : assert property(
          axe_dv_properties_pkg::p_valid_ready_stable(i_clk, i_rst_n, o_axi_s_r_valid, i_axi_s_r_ready, o_axi_s_r)
      );

    `endif
    `endif
  end
endmodule

/// Internal module to axe_axi_demux for bookkeeping of in flight transactions
///
module axe_axi_demux_id_counters #(
  // the lower bits of the AXI ID that should be considered, results in 2**AXI_ID_BITS counters
  parameter int unsigned AxiIdBits         = 2,
  parameter int unsigned CounterWidth      = 4,
  parameter type         man_port_select_t = logic
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Asynchronous reset, active low
  input  wire i_rst_n,
  // lookup
  input  logic [AxiIdBits-1:0] i_lookup_axi_id,
  output man_port_select_t     o_lookup_mst_select,
  output logic                 o_lookup_mst_select_occupied,
  // push
  output logic                 o_full,
  input  logic [AxiIdBits-1:0] i_push_axi_id,
  input  man_port_select_t     i_push_mst_select,
  input  logic                 i_push,
  // inject ATOPs in AR channel
  input  logic [AxiIdBits-1:0] i_inject_axi_id,
  input  logic                 i_inject,
  // pop
  input  logic [AxiIdBits-1:0] i_pop_axi_id,
  input  logic                 i_pop
);
  localparam int unsigned NumCounters = 2**AxiIdBits;
  typedef logic [CounterWidth-1:0] cnt_t;

  // registers, each gets loaded when push_en[i]
  man_port_select_t [NumCounters-1:0] mst_select_q;

  // counter signals
  logic [NumCounters-1:0] push_en, inject_en, pop_en, occupied, cnt_full;

  //-----------------------------------
  // Lookup
  //-----------------------------------
  assign o_lookup_mst_select          = mst_select_q[i_lookup_axi_id];
  assign o_lookup_mst_select_occupied = occupied[i_lookup_axi_id];
  //-----------------------------------
  // Push and Pop
  //-----------------------------------
  assign push_en   = (i_push)   ? (1 << i_push_axi_id)   : '0;
  assign inject_en = (i_inject) ? (1 << i_inject_axi_id) : '0;
  assign pop_en    = (i_pop)    ? (1 << i_pop_axi_id)    : '0;
  assign o_full    = |cnt_full;
  // counters
  for (genvar i = 0; unsigned'(i) < NumCounters; i++) begin : gen_counters
    logic cnt_en, cnt_down, overflow;
    cnt_t cnt_delta, in_flight;
    always_comb begin : proc_cnt
      unique case ({push_en[i], inject_en[i], pop_en[i]})
        3'b001  : begin // i_pop = -1
          cnt_en    = 1'b1;
          cnt_down  = 1'b1;
          cnt_delta = cnt_t'(1);
        end
        3'b010  : begin // i_inject = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
     // 3'b011, i_inject & i_pop = 0 --> use default
        3'b100  : begin // i_push = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
     // 3'b101, i_push & i_pop = 0 --> use default
        3'b110  : begin // i_push & i_inject = +2
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(2);
        end
        3'b111  : begin // i_push & i_inject & i_pop = +1
          cnt_en    = 1'b1;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(1);
        end
        default : begin // do nothing to the counters
          cnt_en    = 1'b0;
          cnt_down  = 1'b0;
          cnt_delta = cnt_t'(0);
        end
      endcase
    end

    cc_cnt_delta #(
      .Width         (CounterWidth),
      .StickyOverflow(1'b0)
    ) u_in_flight_cnt (
      .i_clk,
      .i_rst_n,
      .i_flush   (1'b0),
      .i_cnt_en  (cnt_en),
      .i_cnt_down(cnt_down),
      .i_delta   (cnt_delta),
      .o_q       (in_flight),
      .i_d       (cnt_t'(0)),
      .i_d_load  (1'b0),
      .o_overflow(overflow)
    );
    assign occupied[i] = |in_flight;
    assign cnt_full[i] = overflow | (&in_flight);

    // holds the selection signal for this id
    // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n)         mst_select_q[i] <= '0;
      else if (push_en[i]) mst_select_q[i] <= i_push_mst_select;
    end

    ////////////////
    // Assertions //
    ////////////////
    `ifndef SYNTHESIS
    `ifdef ASSERTIONS_ON
    cnt_underflow: assert property(
      @(posedge i_clk)
      disable iff (~i_rst_n)
      (pop_en[i] |=> !overflow)
    ) else $fatal(1, "axi_demux_id_counters > Counter: %0d underflowed. The reason is probably a faulty AXI response.", i);
    `endif
    `endif
  end
endmodule
