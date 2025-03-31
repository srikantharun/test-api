// Copyright (c) 2019 ETH Zurich, University of Bologna
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

/// AXI Multiplexer: This module multiplexes the AXI4 slave ports down to one master port.
/// The AXI IDs from the slave ports get extended with the respective slave port index.
/// The extension width can be calculated with `$clog2(NumPorts)`. This means the AXI
/// ID for the master port has to be this `$clog2(NumPorts)` wider than the ID for the
/// slave ports.
/// Responses are switched based on these bits. For example, with 4 slave ports
/// a response with ID `6'b100110` will be forwarded to slave port 2 (`2'b10`).
///
module axe_axi_mux #(
  /// The number of subordinate ports
  parameter int unsigned NumPorts      = axe_axi_default_types_pkg::NUM_PORTS,
  /// ID with on the subordinate ports.
  parameter int unsigned SubAxiIdWidth = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Maximum outstanding transaction on the W channel, contolls Fifo Depth
  parameter int unsigned MaxTxn        = 32'd8,
  /// The Fifo to the W channel is in Fall-Through mode
  parameter bit          FallThrough   = 1'b0,
  parameter bit          CutAw         = 1'b1,
  parameter bit          CutW          = 1'b0,
  parameter bit          CutB          = 1'b0,
  parameter bit          CutAr         = 1'b1,
  parameter bit          CutR          = 1'b0,
  parameter type         axi_s_aw_t    = axe_axi_default_types_pkg::axi_aw_4_40_4_t,     // AW Channel Type, slave ports
  parameter type         axi_m_aw_t    = axe_axi_default_types_pkg::axi_aw_5_40_4_t,     // AW Channel Type, master port
  parameter type         axi_w_t       = axe_axi_default_types_pkg::axi_w_64_8_4_t,      //  W Channel Type, all ports
  parameter type         axi_s_b_t     = axe_axi_default_types_pkg::axi_b_4_4_t,         //  B Channel Type, slave ports
  parameter type         axi_m_b_t     = axe_axi_default_types_pkg::axi_b_5_4_t,         //  B Channel Type, master port
  parameter type         axi_s_ar_t    = axe_axi_default_types_pkg::axi_ar_4_40_4_t,     // AR Channel Type, slave ports
  parameter type         axi_m_ar_t    = axe_axi_default_types_pkg::axi_ar_5_40_4_t,     // AR Channel Type, master port
  parameter type         axi_s_r_t     = axe_axi_default_types_pkg::axi_r_4_64_4_t,      //  R Channel Type, slave ports
  parameter type         axi_m_r_t     = axe_axi_default_types_pkg::axi_r_5_64_4_t       //  R Channel Type, master port
  // Maximum number of outstanding transactions per write
  // If enabled, this multiplexer is purely combinatorial
  // add spill register on write master ports, adds a cycle latency on write channels
)(
  /// Clock, positive edge triggered
  input  wire i_clk,
  /// Aysnchronous reset, active low.
  // doc async
  input  wire i_rst_n,
  // doc sync i_clk

  // Subordinate Ports
  input  axi_s_aw_t i_axi_s_aw[NumPorts],
  input  logic      i_axi_s_aw_valid[NumPorts],
  output logic      o_axi_s_aw_ready[NumPorts],
  input  axi_w_t    i_axi_s_w[NumPorts],
  input  logic      i_axi_s_w_valid[NumPorts],
  output logic      o_axi_s_w_ready[NumPorts],
  output axi_s_b_t  o_axi_s_b[NumPorts],
  output logic      o_axi_s_b_valid[NumPorts],
  input  logic      i_axi_s_b_ready[NumPorts],
  input  axi_s_ar_t i_axi_s_ar[NumPorts],
  input  logic      i_axi_s_ar_valid[NumPorts],
  output logic      o_axi_s_ar_ready[NumPorts],
  output axi_s_r_t  o_axi_s_r[NumPorts],
  output logic      o_axi_s_r_valid[NumPorts],
  input  logic      i_axi_s_r_ready[NumPorts],

  // Manager Port
  output axi_m_aw_t o_axi_m_aw,
  output logic      o_axi_m_aw_valid,
  input  logic      i_axi_m_aw_ready,
  output axi_w_t    o_axi_m_w,
  output logic      o_axi_m_w_valid,
  input  logic      i_axi_m_w_ready,
  input  axi_m_b_t  i_axi_m_b,
  input  logic      i_axi_m_b_valid,
  output logic      o_axi_m_b_ready,
  output axi_m_ar_t o_axi_m_ar,
  output logic      o_axi_m_ar_valid,
  input  logic      i_axi_m_ar_ready,
  input  axi_m_r_t  i_axi_m_r,
  input  logic      i_axi_m_r_valid,
  output logic      o_axi_m_r_ready
);
  ///////////////////////////////
  // Parameters and sanitation //
  ///////////////////////////////

  // We want the clog here as in case NumPorts == 1 no id is prepended!
  localparam int unsigned PortSelWidth  = $clog2(NumPorts);
  localparam int unsigned ManAxiIDWidth = SubAxiIdWidth + PortSelWidth;

  if (SubAxiIdWidth == 0) $fatal(1, "Parameter: 'SubAxiIdWidth' must be bigger than 0;");
  if (NumPorts == 0)      $fatal(1, "Parameter: 'NumPorts' must be bigger than 0;");
  if (MaxTxn == 0)        $fatal(1, "Parameter: 'MaxTxn' must be bigger than 0;");

  if (ManAxiIDWidth < SubAxiIdWidth + $clog2(NumPorts)) $fatal(1, "AXI ID width of master ports must be wide enough to identify subordinate ports!");

  if ($unsigned($bits(i_axi_s_aw[0].id)) != SubAxiIdWidth) $fatal(1, "ID width of AW channel of subordinate ports does not match parameter!");
  if ($unsigned($bits(i_axi_s_ar[0].id)) != SubAxiIdWidth) $fatal(1, "ID width of AR channel of subordinate ports does not match parameter!");
  if ($unsigned($bits(o_axi_s_b[0].id))  != SubAxiIdWidth) $fatal(1, "ID width of B channel of subordinate ports does not match parameter!");
  if ($unsigned($bits(o_axi_s_r[0].id))  != SubAxiIdWidth) $fatal(1, "ID width of R channel of subordinate ports does not match parameter!");

  if ($unsigned($bits(o_axi_m_aw.id)) != ManAxiIDWidth) $fatal(1, "ID width of AW channel of master port is wrong!");
  if ($unsigned($bits(o_axi_m_ar.id)) != ManAxiIDWidth) $fatal(1, "ID width of AR channel of master port is wrong!");
  if ($unsigned($bits(i_axi_m_b.id))  != ManAxiIDWidth) $fatal(1, "ID width of B channel of master port is wrong!");
  if ($unsigned($bits(i_axi_m_r.id))  != ManAxiIDWidth) $fatal(1, "ID width of R channel of master port is wrong!");

  //////////////////////////////////////////////
  // Output signals going into the output cut //
  //////////////////////////////////////////////
  axi_m_aw_t cut_aw;
  logic      cut_aw_valid, cut_aw_ready;
  axi_w_t    cut_w;
  logic      cut_w_valid,  cut_w_ready;
  axi_m_b_t  cut_b;
  logic      cut_b_valid,  cut_b_ready;
  axi_m_ar_t cut_ar;
  logic      cut_ar_valid, cut_ar_ready;
  axi_m_r_t  cut_r;
  logic      cut_r_valid,  cut_r_ready;

  ///////////////////////////////////
  // Pass Through when only 1 port //
  ///////////////////////////////////
  if (NumPorts == 32'h1) begin : gen_no_mux
    always_comb cut_aw              = i_axi_s_aw[0];
    always_comb cut_aw_valid        = i_axi_s_aw_valid[0];
    always_comb o_axi_s_aw_ready[0] = cut_aw_ready;
    always_comb cut_w               = i_axi_s_w[0];
    always_comb cut_w_valid         = i_axi_s_w_valid[0];
    always_comb o_axi_s_w_ready[0]  = cut_w_ready;
    always_comb o_axi_s_b[0]        = cut_b;
    always_comb o_axi_s_b_valid[0]  = cut_b_valid;
    always_comb cut_b_ready         = i_axi_s_b_ready[0];
    always_comb cut_ar              = i_axi_s_ar[0];
    always_comb cut_ar_valid        = i_axi_s_ar_valid[0];
    always_comb o_axi_s_ar_ready[0] = cut_ar_ready;
    always_comb o_axi_s_r[0]        = cut_r;
    always_comb o_axi_s_r_valid[0]  = cut_r_valid;
    always_comb cut_r_ready         = i_axi_s_r_ready[0];
  end
  ///////////////////////
  // Multiplexer Logic //
  ///////////////////////
  else begin : gen_mux

    typedef logic [PortSelWidth-1:0] port_idx_t;

    // AXI channels between the ID prepend unit and the rest of the multiplexer
    axi_m_aw_t pre_aw[NumPorts];
    logic      pre_aw_valid[NumPorts];
    logic      pre_aw_ready[NumPorts];
    axi_w_t    pre_w[NumPorts];
    logic      pre_w_valid[NumPorts];
    logic      pre_w_ready[NumPorts];
    axi_m_b_t  pre_b[NumPorts];
    logic      pre_b_valid[NumPorts];
    logic      pre_b_ready[NumPorts];
    axi_m_ar_t pre_ar[NumPorts];
    logic      pre_ar_valid[NumPorts];
    logic      pre_ar_ready[NumPorts];
    axi_m_r_t  pre_r[NumPorts];
    logic      pre_r_valid[NumPorts];
    logic      pre_r_ready[NumPorts];

    ///////////////////////////////////////////////////////
    // ID prepend for all subordinate ports              //
    // the port ID is used to keep track for backrouting //
    ///////////////////////////////////////////////////////
    for (genvar port_idx = 0; unsigned'(port_idx) < NumPorts; port_idx++) begin : gen_id_prepend
      axe_axi_id_prepend #(
        .IdWidthDifference(ManAxiIDWidth - SubAxiIdWidth),
        .PrependId        (port_idx_t'(port_idx)),
        .axi_s_aw_t       (axi_s_aw_t),
        .axi_s_w_t        (axi_w_t),
        .axi_s_b_t        (axi_s_b_t),
        .axi_s_ar_t       (axi_s_ar_t),
        .axi_s_r_t        (axi_s_r_t),
        .axi_m_aw_t       (axi_m_aw_t),
        .axi_m_w_t        (axi_w_t),
        .axi_m_b_t        (axi_m_b_t),
        .axi_m_ar_t       (axi_m_ar_t),
        .axi_m_r_t        (axi_m_r_t)
      ) u_id_prepend (
        .i_axi_s_aw      (i_axi_s_aw[port_idx]),
        .i_axi_s_aw_valid(i_axi_s_aw_valid[port_idx]),
        .o_axi_s_aw_ready(o_axi_s_aw_ready[port_idx]),
        .i_axi_s_w       (i_axi_s_w[port_idx]),
        .i_axi_s_w_valid (i_axi_s_w_valid[port_idx]),
        .o_axi_s_w_ready (o_axi_s_w_ready[port_idx]),
        .o_axi_s_b       (o_axi_s_b[port_idx]),
        .o_axi_s_b_valid (o_axi_s_b_valid[port_idx]),
        .i_axi_s_b_ready (i_axi_s_b_ready[port_idx]),
        .i_axi_s_ar      (i_axi_s_ar[port_idx]),
        .i_axi_s_ar_valid(i_axi_s_ar_valid[port_idx]),
        .o_axi_s_ar_ready(o_axi_s_ar_ready[port_idx]),
        .o_axi_s_r       (o_axi_s_r[port_idx]),
        .o_axi_s_r_valid (o_axi_s_r_valid[port_idx]),
        .i_axi_s_r_ready (i_axi_s_r_ready[port_idx]),
        .o_axi_m_aw      (pre_aw[port_idx]),
        .o_axi_m_aw_valid(pre_aw_valid[port_idx]),
        .i_axi_m_aw_ready(pre_aw_ready[port_idx]),
        .o_axi_m_w       (pre_w[port_idx]),
        .o_axi_m_w_valid (pre_w_valid[port_idx]),
        .i_axi_m_w_ready (pre_w_ready[port_idx]),
        .i_axi_m_b       (pre_b[port_idx]),
        .i_axi_m_b_valid (pre_b_valid[port_idx]),
        .o_axi_m_b_ready (pre_b_ready[port_idx]),
        .o_axi_m_ar      (pre_ar[port_idx]),
        .o_axi_m_ar_valid(pre_ar_valid[port_idx]),
        .i_axi_m_ar_ready(pre_ar_ready[port_idx]),
        .i_axi_m_r       (pre_r[port_idx]),
        .i_axi_m_r_valid (pre_r_valid[port_idx]),
        .o_axi_m_r_ready (pre_r_ready[port_idx])
      );
    end

    ////////////////
    // AW Channel //
    ////////////////
    axi_m_aw_t    [NumPorts-1:0] s_aw;
    logic         [NumPorts-1:0] s_aw_valid, s_aw_ready;

    // AW arbitration handshake
    logic aw_valid, aw_ready;

    // Pack the signals
    always_comb begin
      for (int unsigned port_idx = 0; port_idx < NumPorts; port_idx++) begin
        s_aw[port_idx] = pre_aw[port_idx];
      end
    end
    always_comb s_aw_valid   = {<< {pre_aw_valid}};
    always_comb pre_aw_ready = {<< {s_aw_ready}};

    rr_arb_tree #(
      .NumIn     (NumPorts),
      .datatype_t(axi_m_aw_t),
      .AxiVldRdy (1'b1),
      .LockIn    (1'b1),
      .FairArb   (1'b1)
    ) u_aw_arbiter (
      .i_clk,
      .i_rst_n,
      .flush_i(1'b0),
      .rr_i   ('0),
      .req_i  (s_aw_valid),
      .gnt_o  (s_aw_ready),
      .data_i (s_aw),
      .gnt_i  (aw_ready),
      .req_o  (aw_valid),
      .data_o (cut_aw),
      .idx_o  (/*open*/)
    );

    logic inp_w_fifo_valid, inp_w_fifo_ready;

    cc_stream_fork #(
      .NumStreams(2)
    ) u_aw_stream_fork (
      .i_clk,
      .i_rst_n,
      .i_flush (1'b0),
      .i_select(2'b11),
      .i_valid (aw_valid),
      .o_ready (aw_ready),
      .o_valid ({inp_w_fifo_valid, cut_aw_valid}),
      .i_ready ({inp_w_fifo_ready, cut_aw_ready})
    );

    ///////////////
    // W Channel //
    ///////////////

    // signals for the FIFO that holds the last switching decision of the AW channel
    port_idx_t      w_fifo_data;
    logic           w_fifo_full,  w_fifo_empty;
    logic           w_fifo_push,  w_fifo_pop;
    port_idx_t      w_port_select;

    // We select depending on the prepended ID that was arbited the W channel.
    always_comb w_fifo_data = cut_aw.id[SubAxiIdWidth+:PortSelWidth];

    always_comb w_fifo_push      = inp_w_fifo_valid & inp_w_fifo_ready;
    always_comb inp_w_fifo_ready = ~w_fifo_full;

    fifo_v3 #(
      .FALL_THROUGH(FallThrough),
      .DEPTH       (MaxTxn),
      .dtype_t     (port_idx_t)
    ) i_w_fifo (
      .i_clk,
      .i_rst_n,
      .flush_i   (1'b0),
      .testmode_i(1'b0),
      .full_o    (w_fifo_full),
      .empty_o   (w_fifo_empty),
      .usage_o   (/*open*/),
      .data_i    (w_fifo_data),
      .push_i    (w_fifo_push),
      .data_o    (w_port_select),
      .pop_i     (w_fifo_pop)
    );

    axi_w_t mux_w;
    logic   mux_w_valid,   mux_w_ready;
    logic   w_transaction;

    // Pop the fifo data if we have a W channel transaction and the last flag asserted
    always_comb w_fifo_pop = w_transaction & cut_w.last;

    cc_stream_mux_unpack #(
      .NumStreams(NumPorts),
      .data_t    (axi_w_t)
    ) u_w_mux (
      .i_select(w_port_select),
      .o_error (/*open*/),
      .i_data  (pre_w),
      .i_valid (pre_w_valid),
      .o_ready (pre_w_ready),
      .o_data  (mux_w),
      .o_valid (mux_w_valid),
      .i_ready (mux_w_ready)
    );

    cc_stream_disconnect #(
      .data_t(axi_w_t)
    ) u_w_disconnect (
      .i_disconnect (w_fifo_empty),
      .i_drop       (1'b0),
      .o_dropped    (/*open*/),
      .o_transaction(w_transaction),
      .i_data       (mux_w),
      .i_valid      (mux_w_valid),
      .o_ready      (mux_w_ready),
      .o_data       (cut_w),
      .o_valid      (cut_w_valid),
      .i_ready      (cut_w_ready)
    );

    ///////////////
    // B Channel //
    ///////////////
    port_idx_t  port_b_select;
    always_comb port_b_select = cut_b_valid ? cut_b.id[SubAxiIdWidth+:PortSelWidth] : PortSelWidth'(0);

    cc_stream_demux_unpack #(
      .data_t     (axi_m_b_t),
      .NumStreams (NumPorts),
      .DropOnError(1'b0)
    ) u_b_demux (
      .i_data  (cut_b),
      .i_select(port_b_select),
      .i_valid (cut_b_valid),
      .o_ready (cut_b_ready),
      .o_error (/*open*/),
      .o_data  (pre_b),
      .o_valid (pre_b_valid),
      .i_ready (pre_b_ready)
    );

    ////////////////
    // AR Channel //
    ////////////////
    axi_m_ar_t [NumPorts-1:0] s_ar;
    logic      [NumPorts-1:0] s_ar_valid, s_ar_ready;

    // Pack the signals
    always_comb begin
      for (int unsigned port_idx = 0; port_idx < NumPorts; port_idx++) begin
        s_ar[port_idx] = pre_ar[port_idx];
      end
    end
    always_comb s_ar_valid   = {<< {pre_ar_valid}};
    always_comb pre_ar_ready = {<< {s_ar_ready}};

    rr_arb_tree #(
      .NumIn     (NumPorts),
      .datatype_t(axi_m_ar_t),
      .AxiVldRdy (1'b1),
      .LockIn    (1'b1),
      .FairArb   (1'b1)
    ) u_ar_arbiter (
      .i_clk,
      .i_rst_n,
      .flush_i(1'b0),
      .rr_i   ('0),
      .req_i  (s_ar_valid),
      .gnt_o  (s_ar_ready),
      .data_i (s_ar),
      .gnt_i  (cut_ar_ready),
      .req_o  (cut_ar_valid),
      .data_o (cut_ar),
      .idx_o  (/*open*/)
    );

    ///////////////
    // R Channel //
    ///////////////
    port_idx_t  port_r_select;
    always_comb port_r_select = cut_r_valid ? cut_r.id[SubAxiIdWidth+:PortSelWidth] : PortSelWidth'(0);

    cc_stream_demux_unpack #(
      .data_t     (axi_m_r_t),
      .NumStreams (NumPorts),
      .DropOnError(1'b0)
    ) u_r_demux (
      .i_data  (cut_r),
      .i_select(port_r_select),
      .i_valid (cut_r_valid),
      .o_ready (cut_r_ready),
      .o_error (/*open*/),
      .o_data  (pre_r),
      .o_valid (pre_r_valid),
      .i_ready (pre_r_ready)
    );
  end

  axe_axi_cut #(
    .CutAw    (CutAw),
    .CutW     (CutW),
    .CutB     (CutB),
    .CutAr    (CutAr),
    .CutR     (CutR),
    .axi_aw_t (axi_m_aw_t),
    .axi_w_t  (axi_w_t),
    .axi_b_t  (axi_m_b_t),
    .axi_ar_t (axi_m_ar_t),
    .axi_r_t  (axi_m_r_t)
  ) u_axi_cut (
    .i_clk,
    .i_rst_n,

    .i_axi_s_aw      (cut_aw),
    .i_axi_s_aw_valid(cut_aw_valid),
    .o_axi_s_aw_ready(cut_aw_ready),
    .i_axi_s_w       (cut_w),
    .i_axi_s_w_valid (cut_w_valid),
    .o_axi_s_w_ready (cut_w_ready),
    .o_axi_s_b       (cut_b),
    .o_axi_s_b_valid (cut_b_valid),
    .i_axi_s_b_ready (cut_b_ready),
    .i_axi_s_ar      (cut_ar),
    .i_axi_s_ar_valid(cut_ar_valid),
    .o_axi_s_ar_ready(cut_ar_ready),
    .o_axi_s_r       (cut_r),
    .o_axi_s_r_valid (cut_r_valid),
    .i_axi_s_r_ready (cut_r_ready),

    .o_axi_m_aw,
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    .o_axi_m_w,
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    .i_axi_m_b,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,
    .o_axi_m_ar,
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    .i_axi_m_r,
    .i_axi_m_r_valid,
    .o_axi_m_r_ready
  );
endmodule
