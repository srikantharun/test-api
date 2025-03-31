// Copyright 2020 ETH Zurich and University of Bologna.
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
// - Matheus Cavalcante <matheusd@iis.ee.ethz.ch>
// - Wolfgang Roenninger <wolfgang.roennigner@axelera.ai>

// Description:
// Data width downsize conversion.
// Connects a wide master to a narrower slave.

// NOTE: The downsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type.  The downsizer does support FIXED
// bursts, but only if they consist of a single beat; it will answer with SLVERR
// on multi-beat FIXED bursts.
module axe_axi_dw_downsizer #(
  /// ID width of both subordinate and manager port
  parameter int unsigned AxiIdWidth          = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Address width of both subordinate and manager port
  parameter int unsigned AxiAddrWidth        = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Datawidth of the subordinate port
  parameter int unsigned AxiSubPortDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_512,
  /// Datawidth of the manager port
  parameter int unsigned AxiManPortDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// The number of parallel outstanding reads the converteer can do at a given time.
  parameter int unsigned AxiMaxReads         = 4,
  /// The actual slice width of a transaction ID that determines the uniques of an ID.
  /// This directly translates to the amount of counters instanziated:
  /// `2**AxiIdUsedWidth`
  /// Note: This parameter might change in the future.
  parameter int unsigned AxiIdUsedWidth      = AxiIdWidth,

  parameter type  axi_aw_t  = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type  axi_s_w_t = axe_axi_default_types_pkg::axi_w_512_64_4_t,
  parameter type  axi_m_w_t = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type  axi_b_t   = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type  axi_ar_t  = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type  axi_s_r_t = axe_axi_default_types_pkg::axi_r_4_512_4_t,
  parameter type  axi_m_r_t = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  // doc async
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  // doc sync i_clk

  //////////////////////
  // Subordinate Port //
  //////////////////////
  input  axi_aw_t  i_axi_s_aw,
  input  logic     i_axi_s_aw_valid,
  output logic     o_axi_s_aw_ready,
  input  axi_s_w_t i_axi_s_w,
  input  logic     i_axi_s_w_valid,
  output logic     o_axi_s_w_ready,
  output axi_b_t   o_axi_s_b,
  output logic     o_axi_s_b_valid,
  input  logic     i_axi_s_b_ready,
  input  axi_ar_t  i_axi_s_ar,
  input  logic     i_axi_s_ar_valid,
  output logic     o_axi_s_ar_ready,
  output axi_s_r_t o_axi_s_r,
  output logic     o_axi_s_r_valid,
  input  logic     i_axi_s_r_ready,

  //////////////////
  // Manager port //
  //////////////////
  output axi_aw_t  o_axi_m_aw,
  output logic     o_axi_m_aw_valid,
  input  logic     i_axi_m_aw_ready,
  output axi_m_w_t o_axi_m_w,
  output logic     o_axi_m_w_valid,
  input  logic     i_axi_m_w_ready,
  input  axi_b_t   i_axi_m_b,
  input  logic     i_axi_m_b_valid,
  output logic     o_axi_m_b_ready,
  output axi_ar_t  o_axi_m_ar,
  output logic     o_axi_m_ar_valid,
  input  logic     i_axi_m_ar_ready,
  input  axi_m_r_t i_axi_m_r,
  input  logic     i_axi_m_r_valid,
  output logic     o_axi_m_r_ready
);
  ////////////////
  // Parameters //
  ////////////////

  // Type used to index which adapter is handling each outstanding transaction.
  localparam int unsigned TranIdWidth = cc_math_pkg::index_width(AxiMaxReads);
  typedef logic [TranIdWidth-1:0] tran_id_t;

  // Data width
  localparam int unsigned AxiSubPortStrbWidth = AxiSubPortDataWidth / 8;
  localparam int unsigned AxiManPortStrbWidth = AxiManPortDataWidth / 8;

  localparam int unsigned AxiSlvPortMaxSize = $clog2(AxiSubPortStrbWidth);
  localparam int unsigned AxiMstPortMaxSize = $clog2(AxiManPortStrbWidth);

  localparam int unsigned  SlvPortByteMask = AxiSubPortStrbWidth - 1;
  localparam int unsigned  MstPortByteMask = AxiManPortStrbWidth - 1;

  // Byte-grouped data words
  typedef logic [AxiSubPortStrbWidth-1:0][7:0] sub_data_t;
  typedef logic [AxiManPortStrbWidth-1:0][7:0] man_data_t;

  // Address width
  typedef logic [AxiAddrWidth-1:0] addr_t;

  // ID width
  typedef logic [AxiIdWidth-1:0] id_t;

  // Length of burst after upsizing
  typedef logic [$clog2(AxiSubPortStrbWidth/AxiManPortStrbWidth) + 7:0] burst_len_t;

  ////////////////
  // Sanitation //
  ////////////////
  if (AxiIdWidth != $bits(i_axi_s_aw.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match AW.ID; is: %d and %d", AxiIdWidth, $bits(i_axi_s_aw.id));
  if (AxiIdWidth != $bits(o_axi_s_b.id))  $fatal(1, "Parameter: 'AxiIdWidth' does not match B.ID; is: %d and %d",  AxiIdWidth, $bits(o_axi_s_b.id));
  if (AxiIdWidth != $bits(i_axi_s_ar.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match AR.ID; is: %d and %d", AxiIdWidth, $bits(i_axi_s_ar.id));
  if (AxiIdWidth != $bits(o_axi_s_r.id))  $fatal(1, "Parameter: 'AxiIdWidth' does not match R.ID; is: %d and %d",  AxiIdWidth, $bits(o_axi_s_r.id));

  if (AxiAddrWidth != $bits(i_axi_s_aw.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' not match AW.addr; is: %d and %d", AxiAddrWidth, $bits(i_axi_s_aw.addr));
  if (AxiAddrWidth != $bits(i_axi_s_ar.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' not match AR.addr; is: %d and %d", AxiAddrWidth, $bits(i_axi_s_ar.addr));

  if (AxiSubPortDataWidth != $bits(i_axi_s_w.data))
      $fatal(1, "Parameter: 'AxiSubPortDataWidth' not match subordinate port W.data; is: %d and %d", AxiSubPortDataWidth, $bits(i_axi_s_w.data));
  if (AxiSubPortStrbWidth != $bits(i_axi_s_w.strb))
      $fatal(1, "Parameter: 'AxiSubPortStrbWidth' not match subordinate port W.strb; is: %d and %d", AxiSubPortStrbWidth, $bits(i_axi_s_w.strb));
  if (AxiSubPortDataWidth != $bits(o_axi_s_r.data))
      $fatal(1, "Parameter: 'AxiSubPortDataWidth' not match subordinate port R.data; is: %d and %d", AxiSubPortDataWidth, $bits(o_axi_s_r.data));

  if (AxiManPortDataWidth != $bits(o_axi_m_w.data))
      $fatal(1, "Parameter: 'AxiManPortDataWidth' not match manager port W.data; is: %d and %d", AxiManPortDataWidth, $bits(o_axi_m_w.data));
  if (AxiManPortStrbWidth != $bits(o_axi_m_w.strb))
      $fatal(1, "Parameter: 'AxiManPortStrbWidth' not match manager port W.strb; is: %d and %d", AxiManPortStrbWidth, $bits(o_axi_m_w.strb));
  if (AxiManPortDataWidth != $bits(i_axi_m_r.data))
      $fatal(1, "Parameter: 'AxiManPortDataWidth' not match manager port R.data; is: %d and %d", AxiManPortDataWidth, $bits(i_axi_m_r.data));

  //////////////////////
  // Internal AXI bus //
  //////////////////////

  axi_aw_t  axi_man_aw;
  logic     axi_man_aw_valid, axi_man_aw_ready;
  axi_m_w_t axi_man_w;
  logic     axi_man_w_valid,  axi_man_w_ready;
  axi_b_t   axi_man_b;
  logic     axi_man_b_valid,  axi_man_b_ready;
  axi_ar_t  axi_man_ar;
  logic     axi_man_ar_valid, axi_man_ar_ready;
  axi_m_r_t axi_man_r;
  logic     axi_man_r_valid,  axi_man_r_ready;

  ////////////////////////////////////////////
  // External connection and error handling //
  ////////////////////////////////////////////
  typedef enum logic {
    MuxToPort  = 0,
    MuxToError = 1
  } mux_sel_e;

  axi_aw_t  axi_mux_aw[2];
  logic     axi_mux_aw_valid[2];
  logic     axi_mux_aw_ready[2];
  axi_m_w_t axi_mux_w[2];
  logic     axi_mux_w_valid[2];
  logic     axi_mux_w_ready[2];
  axi_b_t   axi_mux_b[2];
  logic     axi_mux_b_valid[2];
  logic     axi_mux_b_ready[2];
  axi_ar_t  axi_mux_ar[2];
  logic     axi_mux_ar_valid[2];
  logic     axi_mux_ar_ready[2];
  axi_m_r_t axi_mux_r[2];
  logic     axi_mux_r_valid[2];
  logic     axi_mux_r_ready[2];

  always_comb o_axi_m_aw                  = axi_mux_aw[MuxToPort];
  always_comb o_axi_m_aw_valid            = axi_mux_aw_valid[MuxToPort];
  always_comb axi_mux_aw_ready[MuxToPort] = i_axi_m_aw_ready;
  always_comb o_axi_m_w                   = axi_mux_w[MuxToPort];
  always_comb o_axi_m_w_valid             = axi_mux_w_valid[MuxToPort];
  always_comb axi_mux_w_ready[MuxToPort]  = i_axi_m_w_ready;
  always_comb axi_mux_b[MuxToPort]        = i_axi_m_b;
  always_comb axi_mux_b_valid[MuxToPort]  = i_axi_m_b_valid;
  always_comb o_axi_m_b_ready             = axi_mux_b_ready[MuxToPort];
  always_comb o_axi_m_ar                  = axi_mux_ar[MuxToPort];
  always_comb o_axi_m_ar_valid            = axi_mux_ar_valid[MuxToPort];
  always_comb axi_mux_ar_ready[MuxToPort] = i_axi_m_ar_ready;
  always_comb axi_mux_r[MuxToPort]        = i_axi_m_r;
  always_comb axi_mux_r_valid[MuxToPort]  = i_axi_m_r_valid;
  always_comb o_axi_m_r_ready             = axi_mux_r_ready[MuxToPort];

  //////////////
  // Arbiters //
  //////////////

  ///////////////////////////////
  // Read response arbitration //
  ///////////////////////////////
  axi_s_r_t [AxiMaxReads-1:0] sub_r_tran;
  logic     [AxiMaxReads-1:0] sub_r_valid_tran;
  logic     [AxiMaxReads-1:0] sub_r_ready_tran;

  rr_arb_tree #(
    .NumIn     (AxiMaxReads),
    .datatype_t(axi_s_r_t),
    .AxiVldRdy (1'b1),
    .ExtPrio   (1'b0),
    .LockIn    (1'b1)
  ) u_sub_r_arb (
    .i_clk,
    .i_rst_n,
    .flush_i(1'b0),
    .rr_i   ('0),
    .req_i  (sub_r_valid_tran),
    .gnt_o  (sub_r_ready_tran),
    .data_i (sub_r_tran),
    .gnt_i  (i_axi_s_r_ready),
    .req_o  (o_axi_s_r_valid),
    .data_o (o_axi_s_r),
    .idx_o  (/* Unused */)
  );

  logic [AxiMaxReads-1:0] man_r_ready_tran;
  always_comb axi_man_r_ready = |man_r_ready_tran;

  //////////////////////////////
  // Read Request Arbitration //
  //////////////////////////////
  id_t                    arb_sub_ar_id;
  logic                   arb_sub_ar_req;
  logic                   arb_sub_ar_gnt;
  logic [AxiMaxReads-1:0] arb_sub_ar_gnt_tran;
  // Multiplex AR subordinate between AR and AW for the injection of atomic operations with an R response.
  logic                   inject_aw_into_ar;
  logic                   inject_aw_into_ar_req;
  logic                   inject_aw_into_ar_gnt;

  always_comb arb_sub_ar_gnt = |arb_sub_ar_gnt_tran;

  rr_arb_tree #(
    .NumIn    (2),
    .DataWidth(AxiIdWidth),
    .ExtPrio  (1'b0),
    .AxiVldRdy(1'b1),
    .LockIn   (1'b0)
  ) u_sub_ar_arb (
    .i_clk,
    .i_rst_n,
    .flush_i (1'b0),
    .rr_i    ('0),
    .req_i   ({inject_aw_into_ar_req, i_axi_s_ar_valid}),
    .gnt_o   ({inject_aw_into_ar_gnt, o_axi_s_ar_ready}),
    .data_i  ({i_axi_s_aw.id,         i_axi_s_ar.id}),
    .req_o   (arb_sub_ar_req),
    .gnt_i   (arb_sub_ar_gnt),
    .data_o  (arb_sub_ar_id),
    .idx_o   (inject_aw_into_ar)
  );

  axi_ar_t  [AxiMaxReads-1:0] man_ar_tran;
  id_t      [AxiMaxReads-1:0] man_ar_id;
  logic     [AxiMaxReads-1:0] man_ar_valid_tran;
  logic     [AxiMaxReads-1:0] man_ar_ready_tran;
  tran_id_t                   man_req_idx;

  rr_arb_tree #(
    .NumIn     (AxiMaxReads),
    .datatype_t(axi_ar_t),
    .AxiVldRdy (1'b1),
    .ExtPrio   (1'b0),
    .LockIn    (1'b1)
  ) u_man_ar_arb (
    .i_clk,
    .i_rst_n,
    .flush_i(1'b0),
    .rr_i   ('0),
    .req_i  (man_ar_valid_tran),
    .gnt_o  (man_ar_ready_tran),
    .data_i (man_ar_tran),
    .gnt_i  (axi_man_ar_ready),
    .req_o  (axi_man_ar_valid),
    .data_o (axi_man_ar),
    .idx_o  (man_req_idx)
  );

  ///////////////////////
  // Error Subordinate //
  ///////////////////////
  axe_axi_err_sub #(
    .AxiIdWidth  (AxiIdWidth),
    .Resp        (axi_pkg::RespSlvErr),
    .DataWidth   (AxiManPortDataWidth),
    .ReadData    ('hBAD_CAB1E_DEAD_DA7A),
    .MaxTxn      (4),     // We should not have to many here
    .SupportAtops(1'b1),
    .axi_aw_t    (axi_aw_t),
    .axi_w_t     (axi_m_w_t),
    .axi_b_t     (axi_b_t),
    .axi_ar_t    (axi_ar_t),
    .axi_r_t     (axi_m_r_t)
  ) u_axi_err_sub (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_mux_aw[MuxToError]),
    .i_axi_s_aw_valid(axi_mux_aw_valid[MuxToError]),
    .o_axi_s_aw_ready(axi_mux_aw_ready[MuxToError]),
    .i_axi_s_w       (axi_mux_w[MuxToError]),
    .i_axi_s_w_valid (axi_mux_w_valid[MuxToError]),
    .o_axi_s_w_ready (axi_mux_w_ready[MuxToError]),
    .o_axi_s_b       (axi_mux_b[MuxToError]),
    .o_axi_s_b_valid (axi_mux_b_valid[MuxToError]),
    .i_axi_s_b_ready (axi_mux_b_ready[MuxToError]),
    .i_axi_s_ar      (axi_mux_ar[MuxToError]),
    .i_axi_s_ar_valid(axi_mux_ar_valid[MuxToError]),
    .o_axi_s_ar_ready(axi_mux_ar_ready[MuxToError]),
    .o_axi_s_r       (axi_mux_r[MuxToError]),
    .o_axi_s_r_valid (axi_mux_r_valid[MuxToError]),
    .i_axi_s_r_ready (axi_mux_r_ready[MuxToError])
  );

  ///////////
  // DEMUX //
  ///////////

  // Requests can be sent either to the error subordinate,
  // or to the DWC's manager port.

  logic                   man_req_aw_err;
  logic [AxiMaxReads-1:0] man_req_ar_err;

  axe_axi_demux #(
    .NumPorts    (2),
    .AxiIdWidth  (AxiIdWidth),
    .MaxTxn      (AxiMaxReads),
    .AxiLookBits (AxiIdUsedWidth),
    .SupportAtops(1'b1),
    .UniqueIds   (1'b0),
    .CutAw       (1'b1),  // Required to break dependency between AW and W channels
    .CutW        (1'b0),
    .CutB        (1'b0),
    .CutAr       (1'b1),
    .CutR        (1'b0),
    .axi_aw_t    (axi_aw_t),
    .axi_w_t     (axi_m_w_t),
    .axi_b_t     (axi_b_t),
    .axi_ar_t    (axi_ar_t),
    .axi_r_t     (axi_m_r_t)
  ) u_axi_demux (
    .i_clk,
    .i_rst_n,

    .i_axi_s_aw       (axi_man_aw),
    .i_axi_s_aw_select(man_req_aw_err),
    .i_axi_s_aw_valid (axi_man_aw_valid),
    .o_axi_s_aw_ready (axi_man_aw_ready),
    .i_axi_s_w        (axi_man_w),
    .i_axi_s_w_valid  (axi_man_w_valid),
    .o_axi_s_w_ready  (axi_man_w_ready),
    .o_axi_s_b        (axi_man_b),
    .o_axi_s_b_valid  (axi_man_b_valid),
    .i_axi_s_b_ready  (axi_man_b_ready),
    .i_axi_s_ar       (axi_man_ar),
    .i_axi_s_ar_select(man_req_ar_err[man_req_idx]),
    .i_axi_s_ar_valid (axi_man_ar_valid),
    .o_axi_s_ar_ready (axi_man_ar_ready),
    .o_axi_s_r        (axi_man_r),
    .o_axi_s_r_valid  (axi_man_r_valid),
    .i_axi_s_r_ready  (axi_man_r_ready),

    .o_axi_m_aw       (axi_mux_aw),
    .o_axi_m_aw_valid (axi_mux_aw_valid),
    .i_axi_m_aw_ready (axi_mux_aw_ready),
    .o_axi_m_w        (axi_mux_w),
    .o_axi_m_w_valid  (axi_mux_w_valid),
    .i_axi_m_w_ready  (axi_mux_w_ready),
    .i_axi_m_b        (axi_mux_b),
    .i_axi_m_b_valid  (axi_mux_b_valid),
    .o_axi_m_b_ready  (axi_mux_b_ready),
    .o_axi_m_ar       (axi_mux_ar),
    .o_axi_m_ar_valid (axi_mux_ar_valid),
    .i_axi_m_ar_ready (axi_mux_ar_ready),
    .i_axi_m_r        (axi_mux_r),
    .i_axi_m_r_valid  (axi_mux_r_valid),
    .o_axi_m_r_ready  (axi_mux_r_ready)
  );

  ///////////////////////
  // Read Transactions //
  ///////////////////////

  typedef enum logic [2:0] {
    R_IDLE,
    R_INJECT_AW,
    R_PASSTHROUGH,
    R_INCR_DOWNSIZE,
    R_SPLIT_INCR_DOWNSIZE
  } r_state_e;

  typedef struct packed {
    axi_ar_t            ar;
    logic               ar_valid;
    logic               ar_throw_error;
    axi_s_r_t           r;
    logic               r_valid;
    burst_len_t         burst_len;
    axi_pkg::axi_size_e orig_ar_size;
    logic               injected_aw;
  } r_req_t;

  // Write-related type, but w_req_q is referenced from Read logic
  typedef struct packed {
    axi_aw_t             aw;
    logic                aw_valid;
    logic                aw_throw_error;
    burst_len_t          burst_len;
    axi_pkg::axi_len_t   orig_aw_len;
    axi_pkg::axi_burst_e orig_aw_burst;
    axi_pkg::axi_resp_e  burst_resp;
    axi_pkg::axi_size_e  orig_aw_size;
  } w_req_t;

  w_req_t   w_req_d, w_req_q;

  // Decide which downsizer will handle the incoming AXI transaction
  logic     [AxiMaxReads-1:0] idle_read_downsizer;
  tran_id_t                   idx_ar_downsizer;

  // Find an idle downsizer to handle this transaction
  tran_id_t idx_idle_downsizer;
  lzc #(
    .WIDTH(AxiMaxReads)
  ) u_idle_lzc (
    .in_i   (idle_read_downsizer),
    .cnt_o  (idx_idle_downsizer ),
    .empty_o(/* Unused */       )
  );

  // Is there already another downsizer handling a transaction with the same id
  logic     [AxiMaxReads-1:0] id_clash_downsizer;
  tran_id_t                   idx_id_clash_downsizer;
  for (genvar t = 0; unsigned'(t) < AxiMaxReads; t++) begin: gen_id_clash
    assign id_clash_downsizer[t] = arb_sub_ar_id == man_ar_id[t] && !idle_read_downsizer[t];
  end

  cc_decode_onehot #(
    .OhtWidth(AxiMaxReads)
  ) u_id_clash_onehot_to_bin (
    .i_onehot(id_clash_downsizer),
    .o_binary(idx_id_clash_downsizer),
    .o_empty (/*open*/),
    .o_error (/*open*/)
  );

  // Choose an idle downsizer, unless there is an id clash
  assign idx_ar_downsizer = (|id_clash_downsizer) ? idx_id_clash_downsizer : idx_idle_downsizer;

  // This ID queue is used to resolve which downsizer is handling
  // each outstanding read transaction.

  logic     [AxiMaxReads-1:0] idqueue_push;
  logic     [AxiMaxReads-1:0] idqueue_pop;
  tran_id_t                   idqueue_id;
  logic                       idqueue_valid;

  id_queue #(
    .ID_WIDTH(AxiIdWidth),
    .CAPACITY(AxiMaxReads),
    .data_t  (tran_id_t)
  ) u_read_id_queue (
    .clk_i           (i_clk),
    .rst_ni          (i_rst_n),
    .inp_id_i        (arb_sub_ar_id),
    .inp_data_i      (idx_ar_downsizer),
    .inp_req_i       (|idqueue_push),
    .inp_gnt_o       (/* Unused  */),
    .oup_id_i        (axi_man_r.id),
    .oup_pop_i       (|idqueue_pop),
    .oup_req_i       (1'b1),
    .oup_data_o      (idqueue_id),
    .oup_data_valid_o(idqueue_valid),
    .oup_gnt_o       (/* Unused  */),
    .exists_data_i   ('0),
    .exists_mask_i   ('0),
    .exists_req_i    ('0),
    .exists_o        (/* Unused  */),
    .exists_gnt_o    (/* Unused  */)
  );

  for (genvar t = 0; unsigned'(t) < AxiMaxReads; t++) begin: gen_read_downsizer
    r_state_e r_state_d, r_state_q;
    r_req_t r_req_d    , r_req_q  ;

    addr_t size_mask;
    addr_t conv_ratio;
    addr_t align_adj;
    addr_t mst_port_offset;
    addr_t slv_port_offset;

    // Are we idle?
    assign idle_read_downsizer[t] = (r_state_q == R_IDLE) || (r_state_q == R_INJECT_AW);

    // Byte-grouped data signal for the serialization step
    sub_data_t r_data;

    always_comb begin
      // Maintain state
      r_state_d = r_state_q;
      r_req_d   = r_req_q  ;

      size_mask       = addr_t'(0);
      conv_ratio      = addr_t'(0);
      align_adj       = addr_t'(0);
      mst_port_offset = addr_t'(0);
      slv_port_offset = addr_t'(0);

      // AR Channel
      man_ar_tran[t]       = r_req_q.ar;
      man_ar_id[t]         = r_req_q.ar.id;
      man_ar_valid_tran[t] = r_req_q.ar_valid;

      // Throw an error
      man_req_ar_err[t] = r_req_q.ar_throw_error;

      // R Channel
      sub_r_tran[t]       = r_req_q.r;
      sub_r_valid_tran[t] = r_req_q.r_valid;

      idqueue_push[t] = '0;
      idqueue_pop[t]  = '0;

      arb_sub_ar_gnt_tran[t] = 1'b0;

      man_r_ready_tran[t] = 1'b0;

      // Got a grant on the AR channel
      if (man_ar_valid_tran[t] && man_ar_ready_tran[t]) begin
        r_req_d.ar_valid       = 1'b0;
        r_req_d.ar_throw_error = 1'b0;
      end

      // Initialize r_data
      r_data = r_req_q.r.data;

      unique case (r_state_q)
        R_IDLE : begin
          // Reset channels
          r_req_d.ar = '0;
          r_req_d.r  = '0;

          // New read request
          if (arb_sub_ar_req && (idx_ar_downsizer == t)) begin
            arb_sub_ar_gnt_tran[t] = 1'b1;

            // Push to ID queue
            idqueue_push[t] = 1'b1;

            // Must inject an AW request into this upsizer
            if (inject_aw_into_ar) begin
              r_state_d = R_INJECT_AW;
            end else begin
              // Default state
              r_state_d = R_PASSTHROUGH;

              // Save beat
              r_req_d.ar           = i_axi_s_ar;
              r_req_d.ar_valid     = 1'b1;
              r_req_d.burst_len    = i_axi_s_ar.len;
              r_req_d.orig_ar_size = i_axi_s_ar.size;
              r_req_d.injected_aw  = 1'b0;
              r_req_d.r.resp       = axi_pkg::RespExOkay;

              unique case (r_req_d.ar.burst)
                axi_pkg::BurstIncr : begin
                  // Evaluate downsize ratio
                  size_mask  = (1 << r_req_d.ar.size) - 1                                              ;
                  conv_ratio = ((1 << r_req_d.ar.size) + AxiManPortStrbWidth - 1) / AxiManPortStrbWidth;

                  // Evaluate output burst length
                  align_adj         = (r_req_d.ar.addr & size_mask & ~MstPortByteMask) / AxiManPortStrbWidth;
                  r_req_d.burst_len = (r_req_d.ar.len + 1) * conv_ratio - align_adj - 1                     ;

                  if (conv_ratio != 1) begin
                    r_req_d.ar.size = axi_pkg::axi_size_e'(AxiMstPortMaxSize);

                    if (r_req_d.burst_len <= 255) begin
                      r_state_d      = R_INCR_DOWNSIZE  ;
                      r_req_d.ar.len = r_req_d.burst_len;
                    end else begin
                      r_state_d      = R_SPLIT_INCR_DOWNSIZE;
                      r_req_d.ar.len = 255 - align_adj      ;
                    end
                  end
                end

                axi_pkg::BurstFixed: begin
                  // Single transaction
                  if (r_req_d.ar.len == '0) begin
                    // Evaluate downsize ratio
                    size_mask  = (1 << r_req_d.ar.size) - 1                                              ;
                    conv_ratio = ((1 << r_req_d.ar.size) + AxiManPortStrbWidth - 1) / AxiManPortStrbWidth;

                    // Evaluate output burst length
                    align_adj         = (r_req_d.ar.addr & size_mask & ~MstPortByteMask) / AxiManPortStrbWidth;
                    r_req_d.burst_len = (conv_ratio >= align_adj + 1) ? (conv_ratio - align_adj - 1) : 0;

                    if (conv_ratio != 1) begin
                      r_state_d        = R_INCR_DOWNSIZE;
                      r_req_d.ar.len   = r_req_d.burst_len;
                      r_req_d.ar.size  = axi_pkg::axi_size_e'(AxiMstPortMaxSize);
                      r_req_d.ar.burst = axi_pkg::BurstIncr;
                    end
                  end else begin
                    // The downsizer does not support fixed burts
                    r_req_d.ar_throw_error = 1'b1;
                  end
                end

                axi_pkg::BurstWrap: begin
                  // The DW converter does not support this type of burst.
                  r_state_d              = R_PASSTHROUGH;
                  r_req_d.ar_throw_error = 1'b1         ;
                end
                default: r_state_d = R_IDLE;
              endcase
            end
          end
        end

        R_INJECT_AW : begin
          // Save beat
          // Keep defaults where possible, this is not propagated, only keep what needed
          r_req_d.ar = axi_ar_t'{
            id:      w_req_q.aw.id,
            addr:    w_req_q.aw.addr,
            size:    w_req_q.orig_aw_size,
            burst:   w_req_q.orig_aw_burst,
            len:     w_req_q.orig_aw_len,
            cache:   w_req_q.aw.cache,
            default: '0
          };

          r_req_d.ar_valid     = 1'b0                 ; // Injected "AR"s from AW are not valid.
          r_req_d.burst_len    = w_req_q.orig_aw_len  ;
          r_req_d.orig_ar_size = w_req_q.orig_aw_size ;
          r_req_d.injected_aw  = 1'b1                 ;
          r_req_d.r.resp       = axi_pkg::RespExOkay ;

          // Default state
          r_state_d = R_PASSTHROUGH;

          unique case (r_req_d.ar.burst)
            axi_pkg::BurstIncr: begin
              // Evaluate downsize ratio
              size_mask  = (1 << r_req_d.ar.size) - 1                                              ;
              conv_ratio = ((1 << r_req_d.ar.size) + AxiManPortStrbWidth - 1) / AxiManPortStrbWidth;

              // Evaluate output burst length
              align_adj         = (r_req_d.ar.addr & size_mask & ~MstPortByteMask) / AxiManPortStrbWidth;
              r_req_d.burst_len = (r_req_d.ar.len + 1) * conv_ratio - align_adj - 1                     ;

              if (conv_ratio != 1) begin
                r_req_d.ar.size = axi_pkg::axi_size_e'(AxiMstPortMaxSize);

                if (r_req_d.burst_len <= 255) begin
                  r_state_d      = R_INCR_DOWNSIZE  ;
                  r_req_d.ar.len = r_req_d.burst_len;
                end else begin
                  r_state_d      = R_SPLIT_INCR_DOWNSIZE;
                  r_req_d.ar.len = 255 - align_adj      ;
                end
              end
            end

            axi_pkg::BurstFixed: begin
              // Single transaction
              if (r_req_d.ar.len == '0) begin
                // Evaluate downsize ratio
                size_mask  = (1 << r_req_d.ar.size) - 1                                              ;
                conv_ratio = ((1 << r_req_d.ar.size) + AxiManPortStrbWidth - 1) / AxiManPortStrbWidth;

                // Evaluate output burst length
                align_adj         = (r_req_d.ar.addr & size_mask & ~MstPortByteMask) / AxiManPortStrbWidth;
                r_req_d.burst_len = (conv_ratio >= align_adj + 1) ? (conv_ratio - align_adj - 1) : 0;

                if (conv_ratio != 1) begin
                  r_state_d        = R_INCR_DOWNSIZE;
                  r_req_d.ar.len   = r_req_d.burst_len;
                  r_req_d.ar.size  = axi_pkg::axi_size_e'(AxiMstPortMaxSize);
                  r_req_d.ar.burst = axi_pkg::BurstIncr;
                end
              end else begin
                // The downsizer does not support fixed burts
                r_req_d.ar_throw_error = 1'b1;
              end
            end

            axi_pkg::BurstWrap: begin
              // The DW converter does not support this type of burst.
              r_state_d              = R_PASSTHROUGH;
              r_req_d.ar_throw_error = 1'b1         ;
            end
            default: r_state_d = R_IDLE;
          endcase
        end

        R_PASSTHROUGH, R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE: begin
          // Got a grant on the R channel
          if (sub_r_valid_tran[t] && sub_r_ready_tran[t]) begin
            r_req_d.r       = '0  ;
            r_req_d.r_valid = 1'b0;
            r_data          = '0  ;
          end

          // Request was accepted
          if (!r_req_q.ar_valid)
            // Our turn
            if ((idqueue_id == t) && idqueue_valid)
              // Ready to accept more data
              if (!sub_r_valid_tran[t] || (sub_r_valid_tran[t] && sub_r_ready_tran[t])) begin
                man_r_ready_tran[t] = 1'b1;

                if (axi_man_r_valid) begin
                  mst_port_offset = AxiManPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[cc_math_pkg::index_width(AxiManPortStrbWidth)-1:0];
                  slv_port_offset = AxiSubPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[cc_math_pkg::index_width(AxiSubPortStrbWidth)-1:0];

                  // Serialization
                  for (int b = 0; b < AxiSubPortStrbWidth; b++)
                    if ((b >= slv_port_offset) &&
                        (b - slv_port_offset < (1 << r_req_q.orig_ar_size)) &&
                        (b + mst_port_offset - slv_port_offset < AxiManPortStrbWidth)) begin
                      r_data[b] = axi_man_r.data[8*(b + mst_port_offset - slv_port_offset) +: 8];
                    end

                  r_req_d.burst_len = r_req_q.burst_len - 1   ;
                  r_req_d.ar.len    = r_req_q.ar.len - 1      ;
                  r_req_d.r.data    = r_data                  ;
                  r_req_d.r.last    = (r_req_q.burst_len == 0);
                  r_req_d.r.id      = axi_man_r.id           ;

                  // Merge response of this beat with prior one according to precedence rules.
                  r_req_d.r.resp = axi_pkg::axi_resp_precedence(r_req_q.r.resp, axi_man_r.resp);

                  unique case (r_req_d.ar.burst)
                    axi_pkg::BurstIncr: begin
                      r_req_d.ar.addr = axi_pkg::axi_aligned_addr(r_req_q.ar.addr, r_req_q.ar.size) + (1 << r_req_q.ar.size);
                    end
                    axi_pkg::BurstFixed: begin
                      r_req_d.ar.addr = r_req_q.ar.addr;
                    end
                    default: /*nothing*/;
                  endcase

                  if (r_req_q.burst_len == 0)
                    idqueue_pop[t] = 1'b1;

                  unique case (r_state_q)
                    R_PASSTHROUGH:
                      // Forward data as soon as we can
                      r_req_d.r_valid = 1'b1;

                    R_INCR_DOWNSIZE, R_SPLIT_INCR_DOWNSIZE:
                      // Forward when the burst is finished, or after filling up a word
                      if (    r_req_q.burst_len == 0
                          || (   axi_pkg::axi_aligned_addr(r_req_d.ar.addr, r_req_q.orig_ar_size)
                              != axi_pkg::axi_aligned_addr(r_req_q.ar.addr, r_req_q.orig_ar_size))
                      )
                          r_req_d.r_valid = 1'b1;
                    default: /*nothing*/;
                  endcase

                  // Trigger another burst request, if needed
                  if (r_state_q == R_SPLIT_INCR_DOWNSIZE)
                    // Finished current burst, but whole transaction hasn't finished
                    if (r_req_q.ar.len == '0 && r_req_q.burst_len != '0) begin
                      r_req_d.ar_valid = !r_req_q.injected_aw;
                      r_req_d.ar.len   = (r_req_d.burst_len <= 255) ? r_req_d.burst_len : 255;
                    end
                end
              end

          if (sub_r_valid_tran[t] && sub_r_ready_tran[t])
            if (r_req_q.burst_len == '1)
              r_state_d = R_IDLE;
        end
        default: r_state_d = R_IDLE;
      endcase
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) begin
        r_state_q <= R_IDLE;
        r_req_q   <= '0;
      end else begin
        r_state_q <= r_state_d;
        r_req_q   <= r_req_d;
      end
    end
  end : gen_read_downsizer

  ///////////////////////
  // Write Transaction //
  ///////////////////////
  typedef enum logic [1:0] {
    W_IDLE,
    W_PASSTHROUGH,
    W_INCR_DOWNSIZE,
    W_SPLIT_INCR_DOWNSIZE
  } w_state_e;

  w_state_e w_state_d, w_state_q;

  // This FIFO holds the number of bursts generated by each write transactions handled by this downsizer.
  // This is used to forward only the correct B beats to the slave.
  logic forward_b_beat_i;
  logic forward_b_beat_o;
  logic forward_b_beat_push;
  logic forward_b_beat_pop;
  logic forward_b_beat_full;

  fifo_v3 #(
    .DATA_WIDTH  (1),
    .DEPTH       (AxiMaxReads),
    .FALL_THROUGH(1'b1)
  ) u_forward_b_beats_queue (
    .i_clk,
    .i_rst_n,
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .data_i    (forward_b_beat_i),
    .push_i    (forward_b_beat_push),
    .full_o    (forward_b_beat_full),
    .data_o    (forward_b_beat_o),
    .pop_i     (forward_b_beat_pop),
    .empty_o   (/* Unused */),
    .usage_o   (/* Unused */)
  );

  // Byte-grouped data signal for the lane steering step
  man_data_t w_data;
  addr_t mst_port_offset_w;
  addr_t slv_port_offset_w;
  addr_t size_mask_w;
  addr_t conv_ratio_w;
  addr_t align_adj_w;

  always_comb begin
    inject_aw_into_ar_req = 1'b0;

    size_mask_w       = addr_t'(0);
    conv_ratio_w      = addr_t'(0);
    align_adj_w       = addr_t'(0);
    mst_port_offset_w = addr_t'(0);
    slv_port_offset_w = addr_t'(0);

    // i_num_b_beats default state
    forward_b_beat_i    = '0;
    forward_b_beat_push = 1'b0;
    forward_b_beat_pop  = 1'b0;

    // Maintain state
    w_state_d = w_state_q;
    w_req_d   = w_req_q  ;

    // AW Channel
    axi_man_aw       = w_req_q.aw;
    axi_man_aw_valid = w_req_q.aw_valid;
    o_axi_s_aw_ready = '0;

    // Throw an error.
    man_req_aw_err = w_req_q.aw_throw_error;

    // W Channel
    axi_man_w       = '0;
    axi_man_w_valid = '0;
    o_axi_s_w_ready = '0;

    // Initialize w_data
    w_data = '0;

    // B Channel (No latency)
    if (axi_man_b_valid) begin
      // Merge response of this burst with prior one according to precedence rules.
      w_req_d.burst_resp = axi_pkg::axi_resp_precedence(w_req_q.burst_resp, axi_man_b.resp);
    end
    o_axi_s_b      = axi_man_b;
    o_axi_s_b.resp = w_req_d.burst_resp;

    // Each write transaction might trigger several B beats on the master (narrow) side.
    // Only forward the last B beat of each transaction.
    if (forward_b_beat_o) begin
      o_axi_s_b_valid = axi_man_b_valid;
      axi_man_b_ready = i_axi_s_b_ready;

      // Got an ack on the B channel. Pop transaction.
      if (axi_man_b_ready && axi_man_b_valid)
        forward_b_beat_pop = 1'b1;
    end else begin
      // Otherwise, just acknowlegde the B beats
      o_axi_s_b_valid    = 1'b0;
      axi_man_b_ready    = 1'b1;
      forward_b_beat_pop = axi_man_b_valid;
    end

    // Got a grant on the AW channel
    if (axi_man_aw_valid & axi_man_aw_ready) begin
      w_req_d.aw_valid       = 1'b0;
      w_req_d.aw_throw_error = 1'b0;
    end

    unique case (w_state_q)
      W_PASSTHROUGH, W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE: begin
        // Request was accepted
        if (!w_req_q.aw_valid)
          if (i_axi_s_w_valid) begin
            mst_port_offset_w = AxiManPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[cc_math_pkg::index_width(AxiManPortStrbWidth)-1:0];
            slv_port_offset_w = AxiSubPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[cc_math_pkg::index_width(AxiSubPortStrbWidth)-1:0];

            // Valid output
            axi_man_w_valid = !forward_b_beat_full;
            axi_man_w.last  = w_req_q.aw.len == 0;

            // Lane steering
            for (int b = 0; b < AxiSubPortStrbWidth; b++)
              if ((b >= slv_port_offset_w) &&
                  (b - slv_port_offset_w < (1 << w_req_q.orig_aw_size)) &&
                  (b + mst_port_offset_w - slv_port_offset_w < AxiManPortStrbWidth)) begin
                w_data[b + mst_port_offset_w - slv_port_offset_w]         = i_axi_s_w.data[8*b +: 8];
                axi_man_w.strb[b + mst_port_offset_w - slv_port_offset_w] = i_axi_s_w.strb[b]       ;
              end
            axi_man_w.data = w_data;
          end

        // Acknowledgment
        if (axi_man_w_ready && axi_man_w_valid) begin
          w_req_d.burst_len = w_req_q.burst_len - 1;
          w_req_d.aw.len    = w_req_q.aw.len - 1   ;

          unique case (w_req_d.aw.burst)
            axi_pkg::BurstIncr: begin
              w_req_d.aw.addr = axi_pkg::axi_aligned_addr(w_req_q.aw.addr, w_req_q.aw.size) + (1 << w_req_q.aw.size);
            end
            axi_pkg::BurstFixed: begin
              w_req_d.aw.addr = w_req_q.aw.addr;
            end
            default: /*noting*/;
          endcase

          unique case (w_state_q)
            W_PASSTHROUGH:
              o_axi_s_w_ready = 1'b1;

            W_INCR_DOWNSIZE, W_SPLIT_INCR_DOWNSIZE:
              if (    w_req_q.burst_len == 0
                  || (   axi_pkg::axi_aligned_addr(w_req_d.aw.addr, w_req_q.orig_aw_size)
                      != axi_pkg::axi_aligned_addr(w_req_q.aw.addr, w_req_q.orig_aw_size)))
                o_axi_s_w_ready = 1'b1;
            default: /*nothing*/;
          endcase

          // Trigger another burst request, if needed
          if (w_state_q == W_SPLIT_INCR_DOWNSIZE)
            // Finished current burst, but whole transaction hasn't finished
            if (w_req_q.aw.len == '0 && w_req_q.burst_len != '0) begin
              w_req_d.aw_valid = 1'b1;
              w_req_d.aw.len   = (w_req_d.burst_len <= 255) ? w_req_d.burst_len : 255;

              // We will receive an extraneous B beat. Ignore it.
              forward_b_beat_i    = 1'b0;
              forward_b_beat_push = 1'b1;
            end

          if (w_req_q.burst_len == 0) begin
            w_state_d = W_IDLE;

            forward_b_beat_push = 1'b1;
            forward_b_beat_i    = 1'b1;
          end
        end
      end

      default: w_state_d = W_IDLE;
    endcase

    // Can start a new request as soon as w_state_d is W_IDLE
    if (w_state_d == W_IDLE) begin
      // Reset channels
      w_req_d.aw             = '0;
      w_req_d.aw_valid       = 1'b0;
      w_req_d.aw_throw_error = 1'b0;
      w_req_d.burst_resp     = axi_pkg::RespExOkay;

      if (!forward_b_beat_full) begin
        if (i_axi_s_aw_valid && i_axi_s_aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX]) begin // ATOP with an R response
          inject_aw_into_ar_req = 1'b1                 ;
          o_axi_s_aw_ready      = inject_aw_into_ar_gnt;
        end else begin // Regular AW
          o_axi_s_aw_ready = 1'b1;
        end

        // New write request
        if (i_axi_s_aw_valid && o_axi_s_aw_ready) begin
          // Default state
          w_state_d = W_PASSTHROUGH;

          // Save beat
          w_req_d.aw            = i_axi_s_aw      ;
          w_req_d.aw_valid      = 1'b1              ;
          w_req_d.burst_len     = i_axi_s_aw.len  ;
          w_req_d.orig_aw_len   = i_axi_s_aw.len  ;
          w_req_d.orig_aw_size  = i_axi_s_aw.size ;
          w_req_d.orig_aw_burst = i_axi_s_aw.burst;

          unique case (i_axi_s_aw.burst)
            axi_pkg::BurstIncr: begin
              // Evaluate downsize ratio
              size_mask_w  = (1 << i_axi_s_aw.size) - 1;
              conv_ratio_w = ((1 << i_axi_s_aw.size) + AxiManPortStrbWidth - 1) / AxiManPortStrbWidth;

              // Evaluate output burst length
              align_adj_w       = (i_axi_s_aw.addr & size_mask_w & ~MstPortByteMask) / AxiManPortStrbWidth;
              w_req_d.burst_len = (i_axi_s_aw.len + 1) * conv_ratio_w - align_adj_w - 1;

              if (conv_ratio_w != 1) begin
                w_req_d.aw.size = axi_pkg::axi_size_e'(AxiMstPortMaxSize);

                if (w_req_d.burst_len <= 255) begin
                  w_state_d      = W_INCR_DOWNSIZE;
                  w_req_d.aw.len = w_req_d.burst_len;
                end else begin
                  w_state_d      = W_SPLIT_INCR_DOWNSIZE;
                  w_req_d.aw.len = 255 - align_adj_w;
                end
              end
            end

            axi_pkg::BurstFixed: begin
              // Single transaction
              if (i_axi_s_aw.len == '0) begin
                // Evaluate downsize ratio
                size_mask_w  = (1 << i_axi_s_aw.size) - 1                                              ;
                conv_ratio_w = ((1 << i_axi_s_aw.size) + AxiManPortStrbWidth - 1) / AxiManPortStrbWidth;

                // Evaluate output burst length
                align_adj_w       = (i_axi_s_aw.addr & size_mask_w & ~MstPortByteMask) / AxiManPortStrbWidth;
                w_req_d.burst_len = (conv_ratio_w >= align_adj_w + 1) ? (conv_ratio_w - align_adj_w - 1) : 0;

                if (conv_ratio_w != 1) begin
                  w_state_d        = W_INCR_DOWNSIZE;
                  w_req_d.aw.len   = w_req_d.burst_len;
                  w_req_d.aw.size  = axi_pkg::axi_size_e'(AxiMstPortMaxSize);
                  w_req_d.aw.burst = axi_pkg::BurstIncr;
                end
              end else begin
                // The downsizer does not support fixed bursts
                w_req_d.aw_throw_error = 1'b1;
              end
            end

            axi_pkg::BurstWrap: begin
              // The DW converter does not support this type of burst.
              w_state_d              = W_PASSTHROUGH;
              w_req_d.aw_throw_error = 1'b1         ;
            end

            default: w_state_d = W_IDLE;
          endcase
        end
      end
    end
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      w_state_q <= W_IDLE;
      w_req_q   <= '0;
    end else begin
      w_state_q <= w_state_d;
      w_req_q   <= w_req_d;
    end
  end

endmodule : axe_axi_dw_downsizer
