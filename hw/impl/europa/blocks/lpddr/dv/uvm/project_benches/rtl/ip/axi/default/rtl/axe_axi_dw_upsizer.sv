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

// Description:
// Data width upsize conversion.
// Connects a narrow master to a wider slave.

// NOTE: The upsizer does not support WRAP bursts, and will answer with SLVERR
// upon receiving a burst of such type.

module axe_axi_dw_upsizer #(
  /// ID width of both subordinate and manager port
  parameter int unsigned AxiIdWidth          = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// Address width of both subordinate and manager port
  parameter int unsigned AxiAddrWidth        = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Datawidth of the subordinate port
  parameter int unsigned AxiSubPortDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// Datawidth of the manager port
  parameter int unsigned AxiManPortDataWidth = axe_axi_default_types_pkg::WIDTH_DATA_512,
  /// The number of parallel outstanding reads the converteer can do at a given time.
  parameter int unsigned AxiMaxReads         = 4,

  parameter type  axi_aw_t  = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type  axi_s_w_t = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type  axi_m_w_t = axe_axi_default_types_pkg::axi_w_512_64_4_t,
  parameter type  axi_b_t   = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type  axi_ar_t  = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type  axi_s_r_t = axe_axi_default_types_pkg::axi_r_4_64_4_t,
  parameter type  axi_m_r_t = axe_axi_default_types_pkg::axi_r_4_512_4_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,  // doc async
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

  localparam int unsigned AxiSubPortMaxSize = unsigned'($clog2(AxiSubPortStrbWidth));
  localparam int unsigned AxiManPortMaxSize = unsigned'($clog2(AxiManPortStrbWidth));

  // Byte-grouped data words
  typedef logic [AxiManPortStrbWidth-1:0][7:0] man_data_t;
  typedef logic [AxiSubPortStrbWidth-1:0][7:0] sub_data_t;

  // Address width
  typedef logic [AxiAddrWidth-1:0] addr_t;

  // ID width
  typedef logic [AxiIdWidth-1:0] id_t;

  // Length of burst after upsizing
  typedef logic [$clog2(AxiManPortStrbWidth/AxiSubPortStrbWidth) + 7:0] burst_len_t;

  ////////////////
  // Sanitation //
  ////////////////
  if (AxiIdWidth != $bits(i_axi_s_aw.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match AW.ID; is: %0d and %0d", AxiIdWidth, $bits(i_axi_s_aw.id));
  if (AxiIdWidth != $bits(o_axi_s_b.id))  $fatal(1, "Parameter: 'AxiIdWidth' does not match B.ID; is: %0d and %0d",  AxiIdWidth, $bits(o_axi_s_b.id));
  if (AxiIdWidth != $bits(i_axi_s_ar.id)) $fatal(1, "Parameter: 'AxiIdWidth' does not match AR.ID; is: %0d and %0d", AxiIdWidth, $bits(i_axi_s_ar.id));
  if (AxiIdWidth != $bits(o_axi_s_r.id))  $fatal(1, "Parameter: 'AxiIdWidth' does not match R.ID; is: %0d and %0d",  AxiIdWidth, $bits(o_axi_s_r.id));

  if (AxiAddrWidth != $bits(i_axi_s_aw.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' not match AW.addr; is: %0d and %0d", AxiAddrWidth, $bits(i_axi_s_aw.addr));
  if (AxiAddrWidth != $bits(i_axi_s_ar.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' not match AR.addr; is: %0d and %0d", AxiAddrWidth, $bits(i_axi_s_ar.addr));

  if (AxiSubPortDataWidth != $bits(i_axi_s_w.data))
      $fatal(1, "Parameter: 'AxiSubPortDataWidth' not match subordinate port W.data; is: %0d and %0d", AxiSubPortDataWidth, $bits(i_axi_s_w.data));
  if (AxiSubPortStrbWidth != $bits(i_axi_s_w.strb))
      $fatal(1, "Parameter: 'AxiSubPortStrbWidth' not match subordinate port W.strb; is: %0d and %0d", AxiSubPortStrbWidth, $bits(i_axi_s_w.strb));
  if (AxiSubPortDataWidth != $bits(o_axi_s_r.data))
      $fatal(1, "Parameter: 'AxiSubPortDataWidth' not match subordinate port R.data; is: %0d and %0d", AxiSubPortDataWidth, $bits(o_axi_s_r.data));

  if (AxiManPortDataWidth != $bits(o_axi_m_w.data))
      $fatal(1, "Parameter: 'AxiManPortDataWidth' not match manager port W.data; is: %0d and %0d", AxiManPortDataWidth, $bits(o_axi_m_w.data));
  if (AxiManPortStrbWidth != $bits(o_axi_m_w.strb))
      $fatal(1, "Parameter: 'AxiManPortStrbWidth' not match manager port W.strb; is: %0d and %0d", AxiManPortStrbWidth, $bits(o_axi_m_w.strb));
  if (AxiManPortDataWidth != $bits(i_axi_m_r.data))
      $fatal(1, "Parameter: 'AxiManPortDataWidth' not match manager port R.data; is: %0d and %0d", AxiManPortDataWidth, $bits(i_axi_m_r.data));


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

  // TODO(@wolfgang.roenninger): Replace with stream arbiter
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
    .gnt_i  (i_axi_s_r_ready ),
    .req_o  (o_axi_s_r_valid),
    .data_o (o_axi_s_r),
    .idx_o  (/* Unused */)
  );

  logic [AxiMaxReads-1:0] man_r_ready_tran;
  assign axi_man_r_ready = |man_r_ready_tran;

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
    .NumIn     (2),
    .DataWidth (AxiIdWidth),
    .ExtPrio   (1'b0),
    .AxiVldRdy (1'b1),
    .LockIn    (1'b0)
  ) u_sub_ar_arb (
    .i_clk,
    .i_rst_n,
    .flush_i(1'b0),
    .rr_i   ('0),
    .req_i  ({inject_aw_into_ar_req, i_axi_s_ar_valid}),
    .gnt_o  ({inject_aw_into_ar_gnt, o_axi_s_ar_ready}),
    .data_i ({i_axi_s_aw.id,         i_axi_s_ar.id}),
    .req_o  (arb_sub_ar_req),
    .gnt_i  (arb_sub_ar_gnt),
    .data_o (arb_sub_ar_id),
    .idx_o  (inject_aw_into_ar)
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
  axi_aw_t  axi_err_aw;
  logic     axi_err_aw_valid, axi_err_aw_ready;
  axi_m_w_t axi_err_w;
  logic     axi_err_w_valid,  axi_err_w_ready;
  axi_b_t   axi_err_b;
  logic     axi_err_b_valid,  axi_err_b_ready;
  axi_ar_t  axi_err_ar;
  logic     axi_err_ar_valid, axi_err_ar_ready;
  axi_m_r_t axi_err_r;
  logic     axi_err_r_valid,  axi_err_r_ready;

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

  // Requests can be sent either to the error slave,
  // or to the DWC's master port.

  logic [AxiMaxReads-1:0] man_req_ar_err;
  logic                   man_req_aw_err;

  axe_axi_demux #(
    .NumPorts    (2),
    .AxiIdWidth  (AxiIdWidth),
    .MaxTxn      (AxiMaxReads),
    .AxiLookBits (AxiIdWidth),
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

  typedef enum logic [1:0] {
    R_IDLE,
    R_INJECT_AW,
    R_PASSTHROUGH,
    R_INCR_UPSIZE
  } r_state_e;

  // Write-related type, but w_req_q is referenced from Read logic
  typedef struct packed {
    axi_aw_t            aw;
    logic               aw_valid;
    logic               aw_throw_error;
    axi_m_w_t           w;
    logic               w_valid;
    axi_pkg::axi_len_t  burst_len;
    axi_pkg::axi_size_e orig_aw_size;
  } w_req_t;

  w_req_t   w_req_d, w_req_q;

  // Decide which upsizer will handle the incoming AXI transaction
  logic     [AxiMaxReads-1:0] idle_read_upsizer;
  tran_id_t                   idx_ar_upsizer ;

  // Find an idle upsizer to handle this transaction
  tran_id_t idx_idle_upsizer;
  lzc #(
    .WIDTH(AxiMaxReads)
  ) u_idle_lzc (
    .in_i   (idle_read_upsizer),
    .cnt_o  (idx_idle_upsizer ),
    .empty_o(/* Unused */     )
  );

  // Is there already another upsizer handling a transaction with the same id
  logic     [AxiMaxReads-1:0] id_clash_upsizer;
  tran_id_t                   idx_id_clash_upsizer ;
  for (genvar t = 0; unsigned'(t) < AxiMaxReads; t++) begin: gen_id_clash
    assign id_clash_upsizer[t] = arb_sub_ar_id == man_ar_id[t] && !idle_read_upsizer[t];
  end

  cc_decode_onehot #(
    .OhtWidth(AxiMaxReads)
  ) u_id_clash_onehot_to_bin (
    .i_onehot(id_clash_upsizer),
    .o_binary(idx_id_clash_upsizer),
    .o_empty (/*open*/),
    .o_error (/*open*/)
  );

  // Choose an idle upsizer, unless there is an id clash
  always_comb idx_ar_upsizer = (|id_clash_upsizer) ? idx_id_clash_upsizer : idx_idle_upsizer;

  // This logic is used to resolve which upsizer is handling
  // each outstanding read transaction

  logic     r_upsizer_valid;
  tran_id_t idx_r_upsizer;

  logic [AxiMaxReads-1:0] rid_upsizer_match;

  // Is there a upsizer handling this transaction?
  always_comb r_upsizer_valid = |rid_upsizer_match;

  for (genvar t = 0; unsigned'(t) < AxiMaxReads; t++) begin: gen_rid_match
    assign rid_upsizer_match[t] = (axi_man_r.id == man_ar_id[t]) && !idle_read_upsizer[t];
  end

  cc_decode_onehot #(
    .OhtWidth(AxiMaxReads)
  ) u_rid_upsizer_onehot_match (
    .i_onehot(rid_upsizer_match),
    .o_binary(idx_r_upsizer),
    .o_empty (/*open*/),
    .o_error (/*open*/)
  );

  typedef struct packed {
    axi_ar_t            ar;
    logic               ar_valid;
    logic               ar_throw_error;
    axi_pkg::axi_len_t  burst_len;
    axi_pkg::axi_size_e orig_ar_size;
  } r_req_t;

  for (genvar t = 0; unsigned'(t) < AxiMaxReads; t++) begin: gen_read_upsizer
    r_state_e r_state_d, r_state_q;
    r_req_t   r_req_d,   r_req_q;

    // Are we idle?
    assign idle_read_upsizer[t] = (r_state_q == R_IDLE) || (r_state_q == R_INJECT_AW);

    // Byte-grouped data signal for the lane steering step
    sub_data_t r_data;

    always_comb begin
      // Maintain state
      r_state_d = r_state_q;
      r_req_d   = r_req_q  ;

      // AR Channel
      man_ar_tran[t]       = r_req_q.ar;
      man_ar_id[t]         = r_req_q.ar.id;
      man_ar_valid_tran[t] = r_req_q.ar_valid;

      // Throw an error
      man_req_ar_err[t] = r_req_q.ar_throw_error;

      // R Channel
      // No latency
      sub_r_tran[t]      = '0;
      sub_r_tran[t].id   = axi_man_r.id;
      sub_r_tran[t].resp = axi_man_r.resp;

      arb_sub_ar_gnt_tran[t] = 1'b0;

      man_r_ready_tran[t] = 1'b0;
      sub_r_valid_tran[t] = 1'b0;

      // Got a grant on the AR channel
      if (man_ar_valid_tran[t] && man_ar_ready_tran[t]) begin
        r_req_d.ar_valid       = 1'b0;
        r_req_d.ar_throw_error = 1'b0;
      end

      // Initialize r_data
      r_data = '0;

      unique case (r_state_q)
        R_IDLE : begin
          // Reset channels
          r_req_d.ar = '0;

          // New read request
          if (arb_sub_ar_req && (idx_ar_upsizer == t)) begin
            arb_sub_ar_gnt_tran[t] = 1'b1;

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

              unique case (r_req_d.ar.burst)
                axi_pkg::BurstIncr: begin
                  // Modifiable transaction
                  if (axi_pkg::axi_modifiable_bit_set(r_req_d.ar.cache)) begin
                    // No need to upsize single-beat transactions.
                    if (r_req_d.ar.len != '0) begin
                      // Evaluate output burst length
                      automatic addr_t start_addr = axi_pkg::axi_aligned_addr(r_req_d.ar.addr, AxiManPortMaxSize);
                      automatic addr_t end_addr   = axi_pkg::axi_aligned_addr(axi_pkg::axi_beat_addr(r_req_d.ar.addr,
                          r_req_d.orig_ar_size, r_req_d.burst_len, r_req_d.ar.burst,
                          r_req_d.burst_len), AxiManPortMaxSize);
                      r_req_d.ar.len  = (end_addr - start_addr) >> AxiManPortMaxSize;
                      r_req_d.ar.size = axi_pkg::axi_size_e'(AxiManPortMaxSize);
                      r_state_d       = R_INCR_UPSIZE;
                    end
                  end
                end

                axi_pkg::BurstFixed: begin
                  // Passes through the upsizer without any changes
                  r_state_d = R_PASSTHROUGH;
                end

                axi_pkg::BurstWrap: begin
                  // The DW converter does not support this kind of burst ...
                  r_state_d              = R_PASSTHROUGH;
                  r_req_d.ar_throw_error = 1'b1;

                  // ... but might if this is a single-beat transaction
                  if (r_req_d.ar.len == '0)
                    r_req_d.ar_throw_error = 1'b0;
                end
                default: /*do nothing*/;
              endcase
            end
          end
        end

        R_INJECT_AW : begin
          // Save beat
          // Use the defaults where possible, should be fine as it is not propagated:
          r_req_d.ar = axi_ar_t'{
            id:    w_req_q.aw.id,
            addr:  w_req_q.aw.addr,
            size:  w_req_q.orig_aw_size,
            burst: w_req_q.aw.burst,
            len:   w_req_q.burst_len,
            cache: w_req_q.aw.cache,
            default: '0
          };

          r_req_d.ar_valid     = 1'b0                ; // Injected "AR"s from AW are not valid.
          r_req_d.burst_len    = w_req_q.burst_len   ;
          r_req_d.orig_ar_size = w_req_q.orig_aw_size;

          // Default state
          r_state_d = R_PASSTHROUGH;

          unique case (r_req_d.ar.burst)
            axi_pkg::BurstIncr: begin
              // Modifiable transaction
              if (axi_pkg::axi_modifiable_bit_set(r_req_d.ar.cache)) begin
                // No need to upsize single-beat transactions.
                if (r_req_d.ar.len != '0) begin
                  // Evaluate output burst length
                  automatic addr_t start_addr = axi_pkg::axi_aligned_addr(r_req_d.ar.addr, AxiManPortMaxSize);
                  automatic addr_t end_addr   = axi_pkg::axi_aligned_addr(axi_pkg::axi_beat_addr(r_req_d.ar.addr,
                      r_req_d.orig_ar_size, r_req_d.burst_len, r_req_d.ar.burst,
                      r_req_d.burst_len), AxiManPortMaxSize);
                  r_req_d.ar.len  = (end_addr - start_addr) >> AxiManPortMaxSize;
                  r_req_d.ar.size = axi_pkg::axi_size_e'(AxiManPortMaxSize);
                  r_state_d       = R_INCR_UPSIZE;
                end
              end
            end

            axi_pkg::BurstFixed: begin
              // Passes through the upsizer without any changes
              r_state_d = R_PASSTHROUGH;
            end

            axi_pkg::BurstWrap: begin
              // The DW converter does not support this kind of burst ...
              r_state_d              = R_PASSTHROUGH;
              r_req_d.ar_throw_error = 1'b1         ;

              // ... but might if this is a single-beat transaction
              if (r_req_d.ar.len == '0)
                r_req_d.ar_throw_error = 1'b0;
            end
            default: /*do nothing*/;
          endcase
        end

        R_PASSTHROUGH, R_INCR_UPSIZE: begin
          // Request was accepted
          if (!r_req_q.ar_valid)
            if (axi_man_r_valid && (idx_r_upsizer == t) && r_upsizer_valid) begin
              automatic addr_t man_port_offset = AxiManPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[cc_math_pkg::index_width(AxiManPortStrbWidth)-1:0];
              automatic addr_t sub_port_offset = AxiSubPortStrbWidth == 1 ? '0 : r_req_q.ar.addr[cc_math_pkg::index_width(AxiSubPortStrbWidth)-1:0];

              // Valid output
              sub_r_valid_tran[t] = 1'b1;
              sub_r_tran[t].last  = axi_man_r.last && (r_req_q.burst_len == 0);

              // Lane steering
              for (int unsigned b = 0; b < AxiManPortStrbWidth; b++) begin
                if ((b >= man_port_offset) &&
                    (b - man_port_offset < (1 << r_req_q.orig_ar_size)) &&
                    (b + sub_port_offset - man_port_offset < AxiSubPortStrbWidth)) begin
                  r_data[b + sub_port_offset - man_port_offset] = axi_man_r.data[8*b +: 8];
                end
              end
              sub_r_tran[t].data = r_data;

              // Acknowledgment
              if (sub_r_ready_tran[t]) begin
                r_req_d.burst_len = r_req_q.burst_len - 1;

                unique case (r_req_q.ar.burst)
                  axi_pkg::BurstIncr: begin
                    r_req_d.ar.addr = axi_pkg::axi_aligned_addr(r_req_q.ar.addr, r_req_q.orig_ar_size) + (1 << r_req_q.orig_ar_size);
                  end
                  axi_pkg::BurstFixed: begin
                    r_req_d.ar.addr = r_req_q.ar.addr;
                  end
                  default: /*do nothing*/;
                endcase

                unique case (r_state_q)
                  R_PASSTHROUGH:
                    man_r_ready_tran[t] = 1'b1;

                  R_INCR_UPSIZE:
                    if (
                         r_req_q.burst_len == 0
                      || (axi_pkg::axi_aligned_addr(r_req_d.ar.addr, AxiManPortMaxSize) != axi_pkg::axi_aligned_addr(r_req_q.ar.addr, AxiManPortMaxSize))
                    )
                      man_r_ready_tran[t] = 1'b1;
                  default: /*do nothing*/;
                endcase

                if (r_req_q.burst_len == '0)
                  r_state_d = R_IDLE;
              end
            end
        end
        default: r_state_d = R_IDLE;
      endcase
    end

    always_ff @(posedge i_clk or negedge i_rst_n) begin
      if (!i_rst_n) begin
        r_state_q <= R_IDLE;
        r_req_q   <= '0    ;
      end else begin
        r_state_q <= r_state_d;
        r_req_q   <= r_req_d  ;
      end
    end
  end : gen_read_upsizer

  ///////////////////////
  // Write Transaction //
  ///////////////////////

  typedef enum logic [1:0] {
    W_IDLE,
    W_PASSTHROUGH,
    W_INCR_UPSIZE
  } w_state_e;

  w_state_e w_state_d, w_state_q;

  // Byte-grouped data signal for the serialization step
  man_data_t w_data;

  always_comb begin
    inject_aw_into_ar_req = 1'b0;

    // Maintain state
    w_state_d = w_state_q;
    w_req_d   = w_req_q;

    // AW Channel
    axi_man_aw       = w_req_q.aw;
    axi_man_aw_valid = w_req_q.aw_valid;
    o_axi_s_aw_ready = 1'b0;

    // Throw an error.
    man_req_aw_err = w_req_q.aw_throw_error;

    // W Channel
    axi_man_w       = w_req_q.w;
    axi_man_w_valid = w_req_q.w_valid;
    o_axi_s_w_ready = 1'b0;

    // Initialize w_data
    w_data = w_req_q.w.data;

    // B Channel (No latency)
    o_axi_s_b       = axi_man_b;
    o_axi_s_b_valid = axi_man_b_valid;
    axi_man_b_ready = i_axi_s_b_ready;

    // Got a grant on the AW channel
    if (axi_man_aw_valid && axi_man_aw_ready) begin
      w_req_d.aw_valid       = 1'b0;
      w_req_d.aw_throw_error = 1'b0;
    end

    unique case (w_state_q)
      W_PASSTHROUGH, W_INCR_UPSIZE: begin
        // Got a grant on the W channel
        if (axi_man_w_valid && axi_man_w_ready) begin
          w_data          = '0;
          w_req_d.w       = '0;
          w_req_d.w_valid = 1'b0;
        end

        // Request was accepted
        if (!w_req_q.aw_valid) begin
          // Ready if downstream interface is idle, or if it is ready
          o_axi_s_w_ready = ~axi_man_w_valid || axi_man_w_ready;

          if (i_axi_s_w_valid && o_axi_s_w_ready) begin
            automatic addr_t man_port_offset = AxiManPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[cc_math_pkg::index_width(AxiManPortStrbWidth)-1:0];
            automatic addr_t sub_port_offset = AxiSubPortStrbWidth == 1 ? '0 : w_req_q.aw.addr[cc_math_pkg::index_width(AxiSubPortStrbWidth)-1:0];

            // Serialization
            for (int unsigned b = 0; b < AxiManPortStrbWidth; b++)
              if ((b >= man_port_offset) &&
                  (b - man_port_offset < (1 << w_req_q.orig_aw_size)) &&
                  (b + sub_port_offset - man_port_offset < AxiSubPortStrbWidth)) begin
                w_data[b]         = i_axi_s_w.data[8*(b + sub_port_offset - man_port_offset) +: 8];
                w_req_d.w.strb[b] = i_axi_s_w.strb[b + sub_port_offset - man_port_offset];
              end

            w_req_d.burst_len = w_req_q.burst_len - 1;
            w_req_d.w.data    = w_data;
            w_req_d.w.last    = (w_req_q.burst_len == 0);

            unique case (w_req_q.aw.burst)
              axi_pkg::BurstIncr: begin
                w_req_d.aw.addr = axi_pkg::axi_aligned_addr(w_req_q.aw.addr, w_req_q.orig_aw_size) + (1 << w_req_q.orig_aw_size);
              end
              axi_pkg::BurstFixed: begin
                w_req_d.aw.addr = w_req_q.aw.addr;
              end
              default: /*do nothing*/;
            endcase

            unique case (w_state_q)
              W_PASSTHROUGH:
                // Forward data as soon as we can
                w_req_d.w_valid = 1'b1;

              W_INCR_UPSIZE:
                // Forward when the burst is finished, or after filling up a word
                if (
                     w_req_q.burst_len == 0
                  || (axi_pkg::axi_aligned_addr(w_req_d.aw.addr, AxiManPortMaxSize) != axi_pkg::axi_aligned_addr(w_req_q.aw.addr, AxiManPortMaxSize))
                )
                  w_req_d.w_valid = 1'b1;

              default: /*do nothing*/;
            endcase
          end
        end

        if (axi_man_w_valid && axi_man_w_ready)
          if (w_req_q.burst_len == '1) begin
            o_axi_s_w_ready = 1'b0;
            w_state_d       = W_IDLE;
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
      w_req_d.w              = '0;
      w_req_d.w_valid        = 1'b0;

      if (i_axi_s_aw_valid && i_axi_s_aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX]) begin // ATOP with an R response
        inject_aw_into_ar_req = 1'b1                 ;
        o_axi_s_aw_ready   = inject_aw_into_ar_gnt;
      end else begin // Regular AW
        o_axi_s_aw_ready = 1'b1;
      end

      // New write request
      if (i_axi_s_aw_valid & o_axi_s_aw_ready) begin
        // Default state
        w_state_d = W_PASSTHROUGH;

        // Save beat
        w_req_d.aw       = i_axi_s_aw;
        w_req_d.aw_valid = 1'b1;

        w_req_d.burst_len    = i_axi_s_aw.len;
        w_req_d.orig_aw_size = i_axi_s_aw.size;

        unique case (i_axi_s_aw.burst)
          axi_pkg::BurstIncr: begin
            // Modifiable transaction
            if (axi_pkg::axi_modifiable_bit_set(i_axi_s_aw.cache))
              // No need to upsize single-beat transactions.
              if (i_axi_s_aw.len != '0) begin
                // Evaluate output burst length
                automatic addr_t start_addr = axi_pkg::axi_aligned_addr(i_axi_s_aw.addr, AxiManPortMaxSize);
                automatic addr_t end_addr   = axi_pkg::axi_aligned_addr(axi_pkg::axi_beat_addr(i_axi_s_aw.addr,
                    i_axi_s_aw.size, i_axi_s_aw.len, i_axi_s_aw.burst, i_axi_s_aw.len),
                    AxiManPortMaxSize);

                w_req_d.aw.len  = (end_addr - start_addr) >> AxiManPortMaxSize;
                w_req_d.aw.size = axi_pkg::axi_size_e'(AxiManPortMaxSize);
                w_state_d       = W_INCR_UPSIZE;
              end
          end

          axi_pkg::BurstFixed: begin
            // Passes through the upsizer without any changes
            w_state_d = W_PASSTHROUGH;
          end

          axi_pkg::BurstWrap: begin
            // The DW converter does not support this kind of burst ...
            w_state_d              = W_PASSTHROUGH;
            w_req_d.aw_throw_error = 1'b1         ;

            // ... but might if this is a single-beat transaction
            if (i_axi_s_aw.len == '0)
              w_req_d.aw_throw_error = 1'b0;
          end
          default: /*do nothing*/;
        endcase
      end
    end
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      w_state_q <= W_IDLE;
      w_req_q   <= '0    ;
    end else begin
      w_state_q <= w_state_d;
      w_req_q   <= w_req_d  ;
    end
  end

endmodule : axe_axi_dw_upsizer
