// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Derived from: https://github.com/pulp-platform/axi_riscv_atomics/blob/master/src/axi_riscv_lrsc.sv
// Original Authors:
//   - Samuel Riedel <sriedel@iis.ee.ethz.ch>
//   - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// AXI RISC-V LR/SC Adapter
///
/// This adapter adds support for AXI4 exclusive accesses to a subordinate that natively does not support
/// exclusive accesses.  It is to be placed between that subordinate and the upstream manager port, so that
/// the `man` port of this module drives the subordinate and the `sub` port of this module is driven by
/// the upstream manager.
///
/// Exclusive accesses are only enabled for a range of addresses specified through parameters.  All
/// addresses within that range are guaranteed to fulfill the constraints described in A7.2 of the
/// AXI4 standard, both for normal and exclusive memory accesses.  Addresses outside that range
/// behave like a subordinate that does not support exclusive memory accesses (see AXI4, A7.2.5).
///
/// Limitations:
///  -   The adapter does not support bursts in exclusive accessing.  Only single words can be
///      reserved.
///
module axe_axi_riscv_lrsc #(
  /// AXI ID Field Width
  parameter int unsigned             AxiIdWidth      = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// AXI Address Width
  parameter int unsigned             AxiAddrWidth    = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Exclusively-accessible address range (closed interval from AddrStart to AddrEnd)
  parameter logic [AxiAddrWidth-1:0] AddrStart       = 40'h00_0000_0000,
  parameter logic [AxiAddrWidth-1:0] AddrEnd         = 40'h01_0000_0000,
  /// AXI Data Width
  parameter int unsigned             AxiDataWidth    = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// The Axi User Field Width
  parameter int unsigned             AxiUserWidth    = axe_axi_default_types_pkg::WIDTH_USER_4,
  /// Maximum number of in-flight read transactions
  parameter int unsigned             AxiMaxReadTxns  = 8,
  /// Maximum number of in-flight write transactions
  parameter int unsigned             AxiMaxWriteTxns = 8,
  /// Use the AXI User signal instead of the AXI ID to track reservations
  parameter bit                      AxiUserAsId     = 1'b0,
  /// MSB of the ID in the user signal (only needed if `AxiUserAsId == 1`)
  parameter int unsigned             AxiUserAsIdMsb  = 0,
  /// LSB of the ID in the user signal (only needed if `AxiUserAsId == 1`)
  parameter int unsigned             AxiUserAsIdLsb  = 0,
  /// log2 of granularity for reservations (ignored LSBs)
  parameter int unsigned             AxiAddrLsb      = $clog2(AxiDataWidth/8),
  /// Enable debug prints (not synthesizable).
  parameter bit                      DebugPrints     = 1'b0,
  /// Enable full bandwidth in ID queues
  parameter bit                      FullBandwidth   = 1'b1,
  // AXI channel structs
  parameter type                     axi_aw_t        = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type                     axi_w_t         = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type                     axi_b_t         = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type                     axi_ar_t        = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type                     axi_r_t         = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  input  wire     i_clk,
  input  wire     i_rst_n,

  ///////////////////////////
  // Subordinate Interface //
  ///////////////////////////
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

  ///////////////////////
  // Manager Interface //
  ///////////////////////
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
  // Parameter Sanitation //
  //////////////////////////
  if (AddrEnd <= AddrStart) $fatal(1, "AddrEnd must be greater than AddrStart!");
  if (AxiIdWidth      == 0) $fatal(1, "AxiIdWidth must be greater than 0!");
  if (AxiAddrWidth    == 0) $fatal(1, "AxiAddrWidth must be greater than 0!");
  if (AxiDataWidth    == 0) $fatal(1, "AxiDataWidth must be greater than 0!");
  if (AxiMaxReadTxns  == 0) $fatal(1, "AxiMaxReadTxns must be greater than 0!");
  if (AxiMaxWriteTxns == 0) $fatal(1, "AxiMaxWriteTxns must be greater than 0!");

  if (AxiUserAsId) begin : gen_user_as_id_sanitation
    if (AxiUserAsIdMsb <  AxiUserAsIdLsb) $fatal(1, "AxiUserAsIdMsb must be greater equal to AxiUserAsIdLsb!");
    if (AxiUserWidth   <= AxiUserAsIdMsb) $fatal(1, "AxiUserWidth must be greater than AxiUserAsIdMsb!");
  end

  if ($bits(i_axi_s_aw.id)   != AxiIdWidth)   $fatal(1, "`AxiIdWidth`   not matching `axi_aw_t.id`!");
  if ($bits(i_axi_s_aw.addr) != AxiAddrWidth) $fatal(1, "`AxiAddrWidth` not matching `axi_aw_t.addr`!");
  if ($bits(i_axi_s_aw.user) != AxiUserWidth) $fatal(1, "`AxiUserWidth` not matching `axi_aw_t.user`!");

  if ($bits(i_axi_s_w.data)  != AxiDataWidth) $fatal(1, "`AxiDataWidth` not matching `axi_w_t.data`!");
  if ($bits(i_axi_s_w.user)  != AxiUserWidth) $fatal(1, "`AxiUserWidth` not matching `axi_w_t.user`!");

  if ($bits(o_axi_s_b.id)    != AxiIdWidth)   $fatal(1, "`AxiIdWidth`   not matching `axi_b_t.id`!");
  if ($bits(o_axi_s_b.user)  != AxiUserWidth) $fatal(1, "`AxiUserWidth` not matching `axi_b_t.user`!");

  if ($bits(i_axi_s_ar.id)   != AxiIdWidth)   $fatal(1, "`AxiIdWidth`   not matching `axi_ar_t.id`!");
  if ($bits(i_axi_s_ar.addr) != AxiAddrWidth) $fatal(1, "`AxiAddrWidth` not matching `axi_ar_t.addr`!");
  if ($bits(i_axi_s_ar.user) != AxiUserWidth) $fatal(1, "`AxiUserWidth` not matching `axi_ar_t.user`!");

  if ($bits(o_axi_s_r.id)    != AxiIdWidth)   $fatal(1, "`AxiIdWidth`   not matching `axi_r_t.id`!");
  if ($bits(o_axi_s_r.data)  != AxiDataWidth) $fatal(1, "`AxiDataWidth` not matching `axi_r_t.data`!");
  if ($bits(o_axi_s_r.user)  != AxiUserWidth) $fatal(1, "`AxiUserWidth` not matching `axi_r_t.user`!");


  ///////////////////////////////////////
  // Declarations of Signals and Types //
  ///////////////////////////////////////
  localparam int unsigned ResIdWidth = AxiUserAsId ?
      AxiUserAsIdMsb - AxiUserAsIdLsb + 1
    : AxiIdWidth;

  typedef logic [AxiIdWidth-1:0]              axi_id_t;
  typedef logic [AxiAddrWidth-1:0]            axi_addr_t;
  typedef logic [AxiUserWidth-1:0]            axi_user_t;
  typedef logic [AxiAddrWidth-AxiAddrLsb-1:0] res_addr_t; // Track reservations with given granularity.
  typedef logic [ResIdWidth-1:0]              res_id_t;

  function automatic logic addr_in_exclusive_range(axi_addr_t addr);
    if (addr >= AddrStart && addr <= AddrEnd) return 1'b1;
    return 1'b0;
  endfunction

  typedef enum logic [1:0] {
      B_REGULAR   = 2'd0,
      B_EXCLUSIVE = 2'd1,
      B_INJECT    = 2'd2
  } b_cmd_e;

  typedef struct packed {
      axi_id_t    id;
      axi_user_t  user;
  } b_inj_t;


  typedef struct packed {
    logic   excl;
  } r_flight_t;

  typedef struct packed {
      logic       forward;
      axi_id_t    id;
      axi_user_t  user;
  } w_cmd_t;

  typedef struct packed {
      res_addr_t  addr;
      logic       excl;
  } w_flight_t;

  typedef struct packed {
      w_flight_t                      data;
      logic [$bits(w_flight_t)-1:0]   mask;
  } wifq_exists_t;

  typedef enum logic {
      AR_IDLE, AR_WAIT
  } ar_state_e;

  typedef enum logic [1:0] {
      AW_IDLE, AW_WAIT, AW_BURST
  } aw_state_e;

  typedef enum logic {
      B_NORMAL, B_FORWARD
  } b_state_e;

  axi_id_t        b_status_inp_id,
                  b_status_oup_id,
                  rifq_oup_id;

  res_addr_t      ar_push_addr,
                  art_check_clr_addr;

  res_id_t        art_set_id,
                  art_check_id;

  logic           ar_push_excl,
                  ar_push_res;

  logic           art_check_clr_excl;

  logic           ar_push_valid,              ar_push_ready,
                  art_check_clr_req,          art_check_clr_gnt,
                  art_filter_valid,           art_filter_ready,
                  art_set_req,                art_set_gnt;

  logic           rifq_inp_req,               rifq_inp_gnt,
                  rifq_oup_req,               rifq_oup_gnt,
                  rifq_oup_pop,
                  rifq_oup_data_valid;

  r_flight_t      rifq_inp_data,
                  rifq_oup_data;

  logic           wifq_exists,
                  ar_wifq_exists_req,         ar_wifq_exists_gnt,
                  aw_wifq_exists_req,         aw_wifq_exists_gnt,
                  wifq_exists_req,            wifq_exists_gnt,
                                              wifq_inp_gnt,
                  wifq_oup_req,               wifq_oup_gnt,
                  wifq_oup_data_valid;

  wifq_exists_t   ar_wifq_exists_inp,
                  aw_wifq_exists_inp,
                  wifq_exists_inp;

  axi_b_t         sub_b;

  logic           sub_b_valid,                sub_b_ready;

  axi_r_t         sub_r;

  logic           sub_r_valid,                sub_r_ready;

  logic           man_b_valid,                man_b_ready;

  w_cmd_t         w_cmd_inp,                  w_cmd_oup;

  logic           w_cmd_push,                 w_cmd_pop,
                  w_cmd_full,                 w_cmd_empty;

  b_inj_t         b_inj_inp,                  b_inj_oup;

  logic           b_inj_push,                 b_inj_pop,
                  b_inj_full,                 b_inj_empty;

  b_cmd_e         b_status_inp_cmd,           b_status_oup_cmd;

  logic           b_status_inp_req,           b_status_oup_req,
                  b_status_inp_gnt,           b_status_oup_gnt,
                  b_status_oup_pop,
                  b_status_oup_valid;

  logic           art_check_res;

  ar_state_e      ar_state_d,                 ar_state_q;

  aw_state_e      aw_state_d,                 aw_state_q;

  b_state_e       b_state_d,                  b_state_q;

  axi_aw_t                                    man_aw;

  logic           man_aw_valid,               man_aw_ready;

  res_addr_t      clr_addr_d,                 clr_addr_q;

  res_id_t        clr_id_d,                   clr_id_q;

  // 3 bits AxSIZE + 8 bits AxLEN - ignored LSBs
  logic [10-AxiAddrLsb:0] clr_len_d,        clr_len_q,
                            aw_res_len;

  logic           aw_wait_d,                  aw_wait_q;

  //////////////////////
  // AR and R Channel //
  //////////////////////

  // TODO: Refactor ID queue
  // IQ Queue to track in-flight reads
  id_queue #(
    .ID_WIDTH   (AxiIdWidth),
    .CAPACITY   (AxiMaxReadTxns),
    .data_t     (r_flight_t),
    .FULL_BW    (FullBandwidth)
  ) u_read_in_flight_queue (
    .clk_i              (i_clk),
    .rst_ni             (i_rst_n),
    .inp_id_i           (i_axi_s_ar.id),
    .inp_data_i         (rifq_inp_data),
    .inp_req_i          (rifq_inp_req),
    .inp_gnt_o          (rifq_inp_gnt),
    .exists_data_i      ('0),
    .exists_mask_i      ('0),
    .exists_req_i       (1'b0),
    .exists_o           (/* open */),
    .exists_gnt_o       (/* open */),
    .oup_id_i           (rifq_oup_id),
    .oup_pop_i          (rifq_oup_pop),
    .oup_req_i          (rifq_oup_req),
    .oup_data_o         (rifq_oup_data),
    .oup_data_valid_o   (rifq_oup_data_valid),
    .oup_gnt_o          (rifq_oup_gnt)
  );
  always_comb rifq_inp_data.excl = ar_push_excl;

  // Fork requests from AR into reservation table and queue of in-flight reads.
  cc_stream_fork #(
    .NumStreams(2)
  ) u_ar_push_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(2'b11),
    .i_valid (ar_push_valid),
    .o_ready (ar_push_ready),
    .o_valid ({art_filter_valid, rifq_inp_req}),
    .i_ready ({art_filter_ready, rifq_inp_gnt})
  );

  cc_stream_filter u_art_filter (
    .i_drop   (!ar_push_res),
    .o_dropped(/* open */),
    .i_valid  (art_filter_valid),
    .o_ready  (art_filter_ready),
    .o_valid  (art_set_req),
    .i_ready  (art_set_gnt)
  );

  // Time-Invariant Signal Assignments
  always_comb begin
    o_axi_m_ar      = i_axi_s_ar;
    o_axi_m_ar.lock = 1'b0;
  end

  // Control R Channel
  always_comb begin
    o_axi_m_r_ready = 1'b0;
    sub_r           = i_axi_m_r;
    // sub_r.resp      = '0;
    sub_r_valid     = 1'b0;
    rifq_oup_id     = '0;
    rifq_oup_pop    = 1'b0;
    rifq_oup_req    = 1'b0;
    if (i_axi_m_r_valid && sub_r_ready) begin
      rifq_oup_id  = i_axi_m_r.id;
      rifq_oup_pop = i_axi_m_r.last;
      rifq_oup_req = 1'b1;
      if (rifq_oup_gnt) begin
        o_axi_m_r_ready = 1'b1;
        if (i_axi_m_r.resp inside {axi_pkg::RespOkay, axi_pkg::RespExOkay}) begin
          sub_r.resp = rifq_oup_data.excl ? axi_pkg::RespExOkay : axi_pkg::RespOkay;
        end
        sub_r_valid = 1'b1;
      end
    end
  end

`ifndef SYNTHESIS
  always @(posedge i_clk) begin
    if (~i_rst_n) begin
      if (rifq_oup_req && rifq_oup_gnt) begin
        assert (rifq_oup_data_valid) else $error("Unexpected R with ID %0d!", i_axi_m_r.id);
      end
    end
  end
`endif

  // Control AR Channel
  always_comb begin
    o_axi_m_ar_valid              = 1'b0;
    o_axi_s_ar_ready              = 1'b0;
    ar_push_addr                  = '0;
    ar_push_excl                  = '0;
    ar_push_res                   = '0;
    ar_push_valid                 = 1'b0;
    ar_wifq_exists_inp.data.addr  = '0;
    ar_wifq_exists_inp.data.excl  = 1'b0;
    ar_wifq_exists_inp.mask       = '1;
    ar_wifq_exists_inp.mask[12:0] = '0; // Don't care on `excl` bit and page offset.
    ar_wifq_exists_req            = 1'b0;
    ar_state_d                    = ar_state_q;

    unique case (ar_state_q)

      AR_IDLE: begin
        if (i_axi_s_ar_valid) begin
          ar_push_addr = i_axi_s_ar.addr[AxiAddrWidth-1:AxiAddrLsb];
          ar_push_excl = (addr_in_exclusive_range(i_axi_s_ar.addr) && i_axi_s_ar.lock && i_axi_s_ar.len == 8'h00);
          if (ar_push_excl) begin
            ar_wifq_exists_inp.data.addr = i_axi_s_ar.addr[AxiAddrWidth-1:AxiAddrLsb];
            ar_wifq_exists_req           = 1'b1;
            if (ar_wifq_exists_gnt) begin
              ar_push_res   = ~wifq_exists;
              ar_push_valid = 1'b1;
            end
          end else begin
            ar_push_res   = 1'b0;
            ar_push_valid = 1'b1;
          end
          if (ar_push_ready) begin
            o_axi_m_ar_valid = 1'b1;
            if (i_axi_m_ar_ready) begin
              o_axi_s_ar_ready = 1'b1;
            end else begin
              ar_state_d = AR_WAIT;
            end
          end
        end
      end

      AR_WAIT: begin
        o_axi_m_ar_valid = i_axi_s_ar_valid;
        o_axi_s_ar_ready = i_axi_m_ar_ready;
        if (i_axi_m_ar_ready && o_axi_m_ar_valid) begin
          ar_state_d = AR_IDLE;
        end
      end

      default: begin
        ar_state_d = AR_IDLE;
      end
    endcase
  end

  /////////////////////////
  // AW, W and B Channel //
  /////////////////////////

  // FIFO to track commands for W bursts.
  // TODO: replace with a stream based fifo
  fifo_v3 #(
    .FALL_THROUGH(1'b0), // There would be a combinatorial loop if this were a fall-through
                         // register.  Optimizing this can reduce the latency of this module.
    .dtype_t     (w_cmd_t),
    .DEPTH       (AxiMaxWriteTxns)
  ) u_w_cmd_fifo (
    .i_clk,
    .i_rst_n,
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .full_o    (w_cmd_full),
    .empty_o   (w_cmd_empty),
    .usage_o   (),
    .data_i    (w_cmd_inp),
    .push_i    (w_cmd_push),
    .data_o    (w_cmd_oup),
    .pop_i     (w_cmd_pop)
  );

  // TODO: See if this workaround is no longer needed
  // ID Queue to track downstream W bursts and their pending B responses.
  // Workaround for bug in Questa (at least 2018.07 is affected) and VCS (at least 2020.12 is
  // affected):
  // Flatten the enum into a logic vector before using that type when instantiating `id_queue`.
  // typedef logic [$bits(b_cmd_e)-1:0] b_cmd_flat_t;
  // b_cmd_flat_t b_status_inp_cmd_flat, b_status_oup_cmd_flat;
  // always_comb b_status_inp_cmd_flat = b_cmd_flat_t'(b_status_inp_cmd);
  // always_comb b_status_oup_cmd = b_cmd_e'(b_status_oup_cmd_flat);
  id_queue #(
    .ID_WIDTH           (AxiIdWidth),
    .CAPACITY           (AxiMaxWriteTxns),
    .data_t             (b_cmd_e),
    .FULL_BW            (FullBandwidth),
    .CUT_OUP_POP_INP_GNT(1'b1) // TODO: Make sure this does not break anything:
                               // https://github.com/pulp-platform/axi_riscv_atomics/pull/34
  ) u_b_status_queue (
    .clk_i           (i_clk),
    .rst_ni          (i_rst_n),
    .inp_id_i        (b_status_inp_id),
    .inp_data_i      (b_status_inp_cmd),
    .inp_req_i       (b_status_inp_req),
    .inp_gnt_o       (b_status_inp_gnt),
    .exists_data_i   (B_REGULAR),
    .exists_mask_i   (B_REGULAR),
    .exists_req_i    (1'b0),
    .exists_o        (/* open */),
    .exists_gnt_o    (/* open */),
    .oup_id_i        (b_status_oup_id),
    .oup_pop_i       (b_status_oup_pop),
    .oup_req_i       (b_status_oup_req),
    .oup_data_o      (b_status_oup_cmd),
    .oup_data_valid_o(b_status_oup_valid),
    .oup_gnt_o       (b_status_oup_gnt)
  );

  // ID Queue to track in-flight writes.
  w_flight_t  wifq_inp_data;
  always_comb wifq_inp_data = '{
    addr: i_axi_s_aw.addr[AxiAddrWidth-1:AxiAddrLsb],
    excl: i_axi_s_aw.lock
  };

  id_queue #(
    .ID_WIDTH   (AxiIdWidth),
    .CAPACITY   (AxiMaxWriteTxns),
    .data_t     (w_flight_t),
    .FULL_BW    (FullBandwidth)
  ) u_write_in_flight_queue (
    .clk_i           (i_clk),
    .rst_ni          (i_rst_n),
    .inp_id_i        (o_axi_m_aw.id),
    .inp_data_i      (wifq_inp_data),
    .inp_req_i       (man_aw_valid && man_aw_ready),
    .inp_gnt_o       (wifq_inp_gnt),
    .exists_data_i   (wifq_exists_inp.data),
    .exists_mask_i   (wifq_exists_inp.mask),
    .exists_req_i    (wifq_exists_req),
    .exists_o        (wifq_exists),
    .exists_gnt_o    (wifq_exists_gnt),
    .oup_id_i        (i_axi_m_b.id),
    .oup_pop_i       (1'b1),
    .oup_req_i       (wifq_oup_req),
    .oup_data_o      (/* open */),
    .oup_data_valid_o(wifq_oup_data_valid),
    .oup_gnt_o       (wifq_oup_gnt)
  );

`ifndef SYNTHESIS
  always @(posedge i_clk) begin
    if (~i_rst_n) begin
      if (man_aw_valid && man_aw_ready) begin
        assert (wifq_inp_gnt) else $error("Missed enqueuing of in-flight write!");
      end
      if (wifq_oup_req && wifq_oup_gnt) begin
        assert (wifq_oup_data_valid) else $error("Unexpected B!");
      end
    end
  end
`endif

  cc_stream_round_robin_arbiter #(
    .data_t (wifq_exists_t),
    .N_INP  (2),
    .ARBITER("rr")
  ) u_wifq_exists_arb (
    .i_clk,
    .i_rst_n,
    .inp_data_i     ({ar_wifq_exists_inp,   aw_wifq_exists_inp}),
    .inp_valid_i    ({ar_wifq_exists_req,   aw_wifq_exists_req}),
    .inp_ready_o    ({ar_wifq_exists_gnt,   aw_wifq_exists_gnt}),
    .oup_data_o     (wifq_exists_inp),
    .oup_valid_o    (wifq_exists_req),
    .oup_ready_i    (wifq_exists_gnt)
  );

  cc_stream_fork #(
    .NumStreams(2)
  ) u_man_b_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(2'b11),
    .i_valid (i_axi_m_b_valid),
    .o_ready (o_axi_m_b_ready),
    .o_valid ({man_b_valid, wifq_oup_req}),
    .i_ready ({man_b_ready, wifq_oup_gnt})
  );

  // FIFO to track B responses that are to be injected.
  // TODO: replace with a stream based fifo
  fifo_v3 #(
    .FALL_THROUGH   (1'b0),
    .dtype_t        (b_inj_t),
    .DEPTH          (AxiMaxWriteTxns)
  ) u_b_inj_fifo (
    .i_clk,
    .i_rst_n,
    .flush_i   (1'b0),
    .testmode_i(1'b0),
    .full_o    (b_inj_full),
    .empty_o   (b_inj_empty),
    .usage_o   (/* open */),
    .data_i    (b_inj_inp),
    .push_i    (b_inj_push),
    .data_o    (b_inj_oup),
    .pop_i     (b_inj_pop)
  );

  // Fall-through register to hold AW transactin that passed
  always_comb begin
    o_axi_m_aw      = man_aw;
    o_axi_m_aw.lock = 1'b0;
  end

  cc_stream_reg_ft #(
    .data_t(axi_aw_t)
  ) u_aw_trans_reg (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (i_axi_s_aw),
    .i_valid(man_aw_valid),
    .o_ready(man_aw_ready),
    .o_data (man_aw),
    .o_valid(o_axi_m_aw_valid),
    .i_ready(i_axi_m_aw_ready)
  );


  // Compute number of reservations written by this write transaction
  always_comb begin
    // AWSIZE == GRANULARITY: use burst length = AWLEN + 1
    aw_res_len = i_axi_s_aw.len + 1;
    // AWSIZE > GRANULARITY: clear beat-size / granularity reservations per beat
    if (i_axi_s_aw.size > axi_pkg::axi_size_e'(AxiAddrLsb)) begin
      aw_res_len = (i_axi_s_aw.len + 1) << (i_axi_s_aw.size - AxiAddrLsb);
    end
    // AWSIZE < GRANULARITY: clear one reservation for every granularity / beat-size beat
    else if (i_axi_s_aw.size < axi_pkg::axi_size_e'(AxiAddrLsb)) begin
      aw_res_len = (i_axi_s_aw.len + 1) >> (AxiAddrLsb - i_axi_s_aw.size);
    end
  end

  // Control AW Channel
  always_comb begin
    man_aw_valid            = 1'b0;
    o_axi_s_aw_ready        = 1'b0;
    art_check_clr_addr      = '0;
    art_check_clr_excl      = '0;
    art_check_clr_req       = 1'b0;
    aw_wifq_exists_inp.data = '0;
    aw_wifq_exists_inp.mask = '1;
    aw_wifq_exists_req      = 1'b0;
    b_status_inp_id         = '0;
    b_status_inp_cmd        = B_REGULAR;
    b_status_inp_req        = 1'b0;
    w_cmd_inp               = '0;
    w_cmd_push              = 1'b0;
    aw_state_d              = aw_state_q;
    clr_addr_d              = clr_addr_q;
    clr_len_d               = clr_len_q;
    clr_id_d                = clr_id_q;
    aw_wait_d               = aw_wait_q;

    unique case (aw_state_q)
      AW_IDLE: begin
        if (i_axi_s_aw_valid && !w_cmd_full && b_status_inp_gnt && wifq_inp_gnt) begin
          // New AW and we are ready to handle it.
          if (addr_in_exclusive_range(i_axi_s_aw.addr)) begin
            // Inside exclusively-accessible range.
            // Make sure no exclusive AR to the same address is currently waiting.
            if (!(    i_axi_s_ar_valid
                  &&  i_axi_s_ar.lock
                  && (i_axi_s_ar.addr[AxiAddrWidth-1:AxiAddrLsb] == i_axi_s_aw.addr[AxiAddrWidth-1:AxiAddrLsb])
                  )
            ) begin
              // Make sure no exclusive write to the same address is currently in
              // flight.
              aw_wifq_exists_inp.data.addr = i_axi_s_aw.addr[AxiAddrWidth-1:AxiAddrLsb];
              aw_wifq_exists_inp.data.excl = 1'b1;
              // If this is a burst, check the entire page for exclusive writes in flight.
              if (i_axi_s_aw.len > 0) aw_wifq_exists_inp.mask[12:1] = '0;
              aw_wifq_exists_req = 1'b1;
              if (aw_wifq_exists_gnt && !wifq_exists) begin
                // Check reservation and clear identical addresses.
                art_check_clr_addr  = i_axi_s_aw.addr[AxiAddrWidth-1:AxiAddrLsb];
                art_check_clr_excl  = i_axi_s_aw.lock;
                if (man_aw_ready) begin
                    art_check_clr_req = 1'b1;
                end
                if (art_check_clr_gnt) begin
                  if (i_axi_s_aw.lock && i_axi_s_aw.len == axi_pkg::axi_len_t'(0)) begin
                    // Exclusive access and no burst, so check reservation.
                    if (art_check_res) begin
                      // Reservation exists, so forward downstream.
                      man_aw_valid     = 1'b1;
                      o_axi_s_aw_ready = man_aw_ready;
                      if (!man_aw_ready) begin
                        aw_state_d = AW_WAIT;
                      end
                    end else begin
                      // No reservation exists, so drop AW.
                      o_axi_s_aw_ready = 1'b1;
                    end
                    // Store command to forward or drop W burst.
                    w_cmd_inp = '{
                      forward: art_check_res,
                      id:      i_axi_s_aw.id,
                      user:    i_axi_s_aw.user // TODO: Wat to do with user?
                    };
                    w_cmd_push = 1'b1;
                    // Add B status for this ID (exclusive if there is a
                    // reservation, inject otherwise).
                    b_status_inp_cmd = art_check_res ? B_EXCLUSIVE : B_INJECT;
                  end else begin
                    // Non-exclusive access or burst, so forward downstream.
                    man_aw_valid     = 1'b1;
                    o_axi_s_aw_ready = man_aw_ready;
                    // Store command to forward W burst.
                    w_cmd_inp  = '{
                      forward: 1'b1,
                      id:      axi_id_t'(0),
                      user:    '0
                    };
                    w_cmd_push = 1'b1;
                    // Track B response as regular-okay.
                    b_status_inp_cmd = B_REGULAR;
                    // Is this write longer than our reservation granularity?
                    if (aw_res_len > 1) begin
                      // latch start address and length of write (burst)
                      clr_addr_d = i_axi_s_aw.addr[AxiAddrWidth-1:AxiAddrLsb] + 1;
                      clr_len_d  = aw_res_len - 1;
                      clr_id_d   = i_axi_s_aw.id;
                      aw_wait_d  = ~man_aw_ready;
                      aw_state_d = AW_BURST;
                    end
                    else if (!man_aw_ready) begin
                      aw_state_d = AW_WAIT;
                    end
                  end
                  b_status_inp_id = i_axi_s_aw.id;
                  b_status_inp_req = 1'b1;
                end
              end
            end
          end else begin
            // Outside exclusively-accessible address range, so bypass any
            // modifications.
            man_aw_valid     = 1'b1;
            o_axi_s_aw_ready = man_aw_ready;
            if (man_aw_ready) begin
              // Store command to forward W burst.
              w_cmd_inp = '{
                forward: 1'b1,
                id:      axi_id_t'(0),
                user:    '0
              };
              w_cmd_push = 1'b1;
              // Track B response as regular-okay.
              b_status_inp_id  = i_axi_s_aw.id;
              b_status_inp_cmd = B_REGULAR;
              b_status_inp_req = 1'b1;
            end
          end
        end
      end

      AW_WAIT: begin
        man_aw_valid     = 1'b1;
        o_axi_s_aw_ready = man_aw_ready;
        if (man_aw_ready) begin
          aw_state_d = AW_IDLE;
        end
      end

      AW_BURST: begin
        man_aw_valid = aw_wait_q;
        aw_wait_d    = aw_wait_q & ~man_aw_ready;
        // Make sure no exclusive AR to the same address is currently waiting.
        if (!(    i_axi_s_ar_valid
              &&  i_axi_s_ar.lock
              && (i_axi_s_ar.addr[AxiAddrWidth-1:AxiAddrLsb] == clr_addr_q)
             )
        ) begin
          // Check reservation and clear identical addresses.
          art_check_clr_addr = clr_addr_q;
          art_check_clr_req  = 1'b1;
          clr_addr_d         = clr_addr_q + 1;
          clr_len_d          = clr_len_q - 1;
          if (clr_len_q == 'd1) begin
            aw_state_d = aw_wait_d ? AW_WAIT : AW_IDLE;
          end
        end
      end

      default: aw_state_d = AW_IDLE;

    endcase
  end

`ifndef SYNTHESIS
  if (DebugPrints) begin : gen_debug_print_b_status
    always @(posedge i_clk) begin
      if (b_status_inp_req && b_status_inp_gnt) begin
        $display("%0t: AW added %0d as %0d", $time, b_status_inp_id, b_status_inp_cmd);
      end
    end
  end
`endif

  // Control W Channel
  // Time-Invariant Signal Assignments
  always_comb o_axi_m_w = i_axi_s_w;

  always_comb begin
    o_axi_m_w_valid = 1'b0;
    o_axi_s_w_ready = 1'b0;
    b_inj_inp       = '0;
    b_inj_push      = 1'b0;
    w_cmd_pop       = 1'b0;
    if (i_axi_s_w_valid && !w_cmd_empty && !b_inj_full) begin
      if (w_cmd_oup.forward) begin
        // Forward
        o_axi_m_w_valid = 1'b1;
        o_axi_s_w_ready = i_axi_m_w_ready;
      end else begin
        // Drop
        o_axi_s_w_ready = 1'b1;
      end
      if (o_axi_s_w_ready && i_axi_s_w.last) begin
        w_cmd_pop = 1'b1;
        if (!w_cmd_oup.forward) begin
          // Add command to inject B response.
          b_inj_inp = '{
            id:   w_cmd_oup.id,
            user: w_cmd_oup.user // TODO: What to do with user?
          };
          b_inj_push = 1'b1;
        end
      end
    end
  end

`ifndef SYNTHESIS
  if (DebugPrints) begin : gen_debug_print_b_inject
    always @(posedge i_clk) begin
      if (b_inj_push) begin
        $display("%0t: W added inject for %0d", $time, b_inj_inp.id);
      end
    end
  end
`endif

  // Control B Channel
  always_comb begin
    sub_b            = i_axi_m_b;
    sub_b_valid      = 1'b0;
    man_b_ready      = 1'b0;
    b_inj_pop        = 1'b0;
    b_status_oup_id  = '0;
    b_status_oup_req = 1'b0;
    b_state_d        = b_state_q;

    unique case (b_state_q)
      B_NORMAL: begin
        if (!b_inj_empty) begin
          // There is a response to be injected ..
          b_status_oup_id = b_inj_oup.id;
          b_status_oup_req = 1'b1;
          if (b_status_oup_gnt && b_status_oup_valid) begin
            if (b_status_oup_cmd == B_INJECT) begin
              // .. and the next B for that ID is indeed an injection, so go ahead and
              // inject it.
              sub_b = '{
                id:   b_inj_oup.id,
                resp: axi_pkg::RespOkay,
                user: b_inj_oup.user,    // TODO: What to do with the user?
                default: '0
              };
              sub_b_valid = 1'b1;
              b_inj_pop   = sub_b_ready;
            end else begin
              // .. but the next B for that ID is *not* an injection, so try to
              // forward a B.
              b_state_d = B_FORWARD;
            end
          end
        end else if (man_b_valid) begin
          // There is currently no response to be injected, so try to forward a B.
          b_status_oup_id  = i_axi_m_b.id;
          b_status_oup_req = 1'b1;
          if (b_status_oup_gnt && b_status_oup_valid) begin
            if (i_axi_m_b.resp inside {axi_pkg::RespOkay, axi_pkg::RespExOkay}) begin
              sub_b.resp = (b_status_oup_cmd == B_EXCLUSIVE) ? axi_pkg::RespExOkay : axi_pkg::RespOkay;
            end else begin
              sub_b.resp = i_axi_m_b.resp;
            end
            sub_b_valid = 1'b1;
            man_b_ready = sub_b_ready;
          end
        end
      end

      B_FORWARD: begin
        if (man_b_valid) begin
          b_status_oup_id  = i_axi_m_b.id;
          b_status_oup_req = 1'b1;
          if (b_status_oup_gnt && b_status_oup_valid) begin
            if (i_axi_m_b.resp inside {axi_pkg::RespOkay, axi_pkg::RespExOkay}) begin
              sub_b.resp = (b_status_oup_cmd == B_EXCLUSIVE) ? axi_pkg::RespExOkay : axi_pkg::RespOkay;
            end else begin
              sub_b.resp = i_axi_m_b.resp;
            end
            sub_b_valid = 1'b1;
            man_b_ready = sub_b_ready;
            if (sub_b_ready) begin
              b_state_d = B_NORMAL;
            end
          end
        end
      end

      default: b_state_d = B_NORMAL;

    endcase
  end

`ifndef SYNTHESIS
  always @(posedge i_clk) begin
    if (b_status_oup_req && b_status_oup_gnt) begin
      assert (b_status_oup_valid);
      if ((b_state_q == B_NORMAL && b_inj_empty) || b_state_q == B_FORWARD) begin
        assert (b_status_oup_cmd != B_INJECT);
      end
    end
  end

  if (DebugPrints) begin : gen_debug_print_b_handshake
    always @(posedge i_clk) begin
      if (sub_b_valid && sub_b_ready) begin
        if (man_b_ready) begin
          $display("%0t: B forwarded ID %0d", $time, sub_b.id);
        end else begin
          $display("%0t: B injected ID %0d", $time, sub_b.id);
        end
      end
    end
  end
`endif

  always_comb b_status_oup_pop = sub_b_valid && sub_b_ready;

  // Register in front of sub_b to prevent changes by FSM while valid and not yet ready.
  // Note: Was a `stream_register`
  cc_stream_spill_reg #(
    .data_t(axi_b_t),
    .Bypass(1'b0)
  ) u_sub_b_reg (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (sub_b),
    .i_valid(sub_b_valid),
    .o_ready(sub_b_ready),
    .o_data (o_axi_s_b),
    .o_valid(o_axi_s_b_valid),
    .i_ready(i_axi_s_b_ready)
  );

  // Fall-through register in front of sub_r to remove mutual dependency.
  cc_stream_spill_reg #( // There would be a combinatorial loop if this were a fall-through register.
                      // Optimizing this can reduce the latency of this module.
    .data_t(axi_r_t),
    .Bypass(1'b0)
  ) u_sub_r_reg (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (sub_r),
    .i_valid(sub_r_valid),
    .o_ready(sub_r_ready),
    .o_data (o_axi_s_r),
    .o_valid(o_axi_s_r_valid),
    .i_ready(i_axi_s_r_ready)
  );

  // AXI Reservation Table
  if (AxiUserAsId) begin : gen_user_as_id
    always_comb art_check_id = (aw_state_q == AW_BURST) ? clr_id_q : i_axi_s_aw.user[AxiUserAsIdMsb:AxiUserAsIdLsb];
    always_comb art_set_id   = i_axi_s_ar.user[AxiUserAsIdMsb:AxiUserAsIdLsb];
  end else begin : gen_id_as_id
    always_comb art_check_id = (aw_state_q == AW_BURST) ? clr_id_q : i_axi_s_aw.id;
    always_comb art_set_id   = i_axi_s_ar.id;
  end

  axe_axi_riscv_lrsc_res_tbl #(
    .AxiIdWidth   (ResIdWidth),
    .AxiAddrWidth (AxiAddrWidth-AxiAddrLsb) // Track reservations with given granularity.
  ) u_art (
    .i_clk,
    .i_rst_n,
    .i_check_clear_addr(art_check_clr_addr),
    .i_check_id        (art_check_id),
    .i_check_clear_excl(art_check_clr_excl),
    .o_check_res       (art_check_res),
    .i_check_clear_req (art_check_clr_req),
    .o_check_clear_gnt (art_check_clr_gnt),
    .i_set_addr        (ar_push_addr),
    .i_set_id          (art_set_id),
    .i_set_req         (art_set_req),
    .o_set_gnt         (art_set_gnt)
  );

  // Registers
  always_ff @(posedge i_clk, negedge i_rst_n) begin
    if (~i_rst_n) begin
      ar_state_q <= AR_IDLE;
      aw_state_q <= AW_IDLE;
      b_state_q  <= B_NORMAL;
      clr_addr_q <= '0;
      clr_len_q  <= '0;
      clr_id_q   <= '0;
      aw_wait_q  <= '0;
    end else begin
      ar_state_q <= ar_state_d;
      aw_state_q <= aw_state_d;
      b_state_q  <= b_state_d;
      clr_addr_q <= clr_addr_d;
      clr_len_q  <= clr_len_d;
      clr_id_q   <= clr_id_d;
      aw_wait_q  <= aw_wait_d;
    end
  end
endmodule
