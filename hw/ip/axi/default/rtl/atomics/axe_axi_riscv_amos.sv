// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Derived from: https://github.com/pulp-platform/axi_riscv_atomics/blob/master/src/axi_riscv_amos.sv
// Original Authors:
//   - Samuel Riedel <sriedel@iis.ee.ethz.ch>
//   - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// This adapter implements atomic memory operations in accordance with the RVWMO memory consistency
/// model.
///
/// !!! bug "Known Limitations"
///
///     This module is known to break AXI write data response handshaking when encountering
///     not supported ATOMIC operations.  It will send out the B response before having accepted the
///     write datat!  The module will issue simulation time assertions for not supported ATOPs!
///     The not supported constructs are:
///
///     - ATOMIC COMPARE
///     - ATOMIC LOAD/STORE BIG-Endian
///
///
/// Interface notes:
///
/// -  This module has combinational paths between AXI inputs and outputs for minimum latency. Add
///    slices upstream or downstream or in both directions if combinatorial paths become too long.
///    The module adheres to the AXI ready/valid dependency specification to prevent combinatorial
///    loops.
///
/// -  The AW and AR structs are  assumed to have the same order and amount of fields except
///    that AW contains the additional ATOP field. If this is not adhered you will see
///    Sideband shifts in the generated atomic AR requests!
module axe_axi_riscv_amos #(
  /// AXI ID Field Width
  parameter int unsigned AxiIdWidth      = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// AXI Address Width
  parameter int unsigned AxiAddrWidth    = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// AXI Data Width
  parameter int unsigned AxiDataWidth    = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// Maximum number of AXI write transactions outstanding at the same time
  parameter int unsigned AxiMaxWriteTxns = 4,
  /// Word width of the widest RISC-V processor that can issue requests to this module.
  /// 32 for RV32; 64 for RV64, where both 32-bit (.W suffix) and 64-bit (.D suffix) AMOs are
  /// supported if `aw_strb` is set correctly.
  parameter int unsigned RiscvWordWidth  = 64,
  // AXI channel structs
  parameter type  axi_aw_t = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type  axi_w_t  = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type  axi_b_t  = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type  axi_ar_t = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type  axi_r_t  = axe_axi_default_types_pkg::axi_r_4_64_4_t
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

  localparam int unsigned AxiStrbWidth = AxiDataWidth/8;

  if (AxiMaxWriteTxns == 0) $fatal(1, "Parameter: 'AxiMaxWriteTxns' must be larger than 0;");

  if (AxiIdWidth   != $bits(i_axi_s_aw.id))   $fatal(1, "Parameter: 'AxiIdWidth' not mathcing 'axi_aw_t.id';");
  if (AxiAddrWidth != $bits(i_axi_s_aw.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' not mathcing 'axi_aw_t.addr';");

  if (AxiDataWidth != $bits(i_axi_s_w.data)) $fatal(1, "Parameter: 'AxiDataWidth'  not mathcing 'axi_w_t.data';");
  if (AxiStrbWidth != $bits(i_axi_s_w.strb)) $fatal(1, "Parameter: 'AxiStrbWidth'  not mathcing 'axi_w_t.strb';");

  if (AxiIdWidth   != $bits(o_axi_s_b.id))   $fatal(1, "Parameter: 'AxiIdWidth' not mathcing 'axi_b_t.id';");

  if (AxiIdWidth   != $bits(i_axi_s_ar.id))   $fatal(1, "Parameter: 'AxiIdWidth' not mathcing 'axi_ar_t.id';");
  if (AxiAddrWidth != $bits(i_axi_s_ar.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' not mathcing 'axi_ar_t.addr';");

  if (AxiIdWidth   != $bits(o_axi_s_r.id))   $fatal(1, "Parameter: 'AxiIdWidth' not mathcing 'axi_r_t.id';");
  if (AxiDataWidth != $bits(o_axi_s_r.data)) $fatal(1, "Parameter: 'AxiDataWidth'  not mathcing 'axi_r_t.data';");

  localparam int unsigned OutstandingBurstsWidth = unsigned'($clog2(AxiMaxWriteTxns+1));
  localparam int unsigned AxiAluRatio            = AxiDataWidth / RiscvWordWidth;

  if (!(RiscvWordWidth == 32 || RiscvWordWidth == 64)) $fatal(1, "Parameter: 'RiscvWordWidth '  must be 32 or 64!;");
  if (AxiDataWidth < RiscvWordWidth)      $fatal(1, "Parameter: 'AxiDataWidth' can not represent 'RiscvWordWidth'!;");
  if (AxiDataWidth % RiscvWordWidth != 0) $fatal(1, "Parameter: 'RiscvWordWidth' is not a divisor of 'AxiDataWidth'!;");

  //////////////////////
  // Helper Functions //
  //////////////////////

  if ($bits(i_axi_s_aw) != ($bits(i_axi_s_ar) + axi_pkg::AXI_ATOP_WIDTH)) $fatal(1, "AW is only allowed to have additional ATOP field compared to AR;");

  // Determine the offset of the `atop` field in the AW struct
  // Due to the hierarchical access can not be used during elaboration
  function automatic int unsigned get_atop_offset;
    axi_aw_t aw_mask;
    aw_mask      = '0;
    aw_mask.atop = '1;
    for (int unsigned i = 0; i < $bits(aw_mask); i++) begin
      if (aw_mask[i] == 1'b1) return i;
    end
  endfunction

  // Needs bit assignment as it for above reason as the determined ranges are not constant.
  function automatic axi_ar_t assign_aw_to_ar(axi_aw_t aw);
    axi_ar_t ar;
    int unsigned atop_field_offset;

    atop_field_offset = get_atop_offset();

    for (int unsigned vector_idx = 0; vector_idx < $bits(ar); vector_idx++) begin
      if (vector_idx < atop_field_offset) ar[vector_idx] = aw[vector_idx];
      else                                ar[vector_idx] = aw[vector_idx + axi_pkg::AXI_ATOP_WIDTH];
    end

    return ar;
  endfunction

  ///////////////////////////////
  // Internal Type Definitions //
  ///////////////////////////////

  // State types
  typedef enum logic [1:0] { FEEDTHROUGH_AW, WAIT_RESULT_AW, SEND_AW } aw_state_e;
  aw_state_e   aw_state_d, aw_state_q;

  typedef enum logic [2:0] { FEEDTHROUGH_W, WAIT_DATA_W, WAIT_RESULT_W, WAIT_CHANNEL_W, SEND_W } w_state_e;
  w_state_e    w_state_d, w_state_q;

  typedef enum logic [1:0] { FEEDTHROUGH_B, WAIT_COMPLETE_B, WAIT_CHANNEL_B, SEND_B } b_state_e;
  b_state_e    b_state_d, b_state_q;

  typedef enum logic [1:0] { FEEDTHROUGH_AR, WAIT_CHANNEL_AR, SEND_AR } ar_state_e;
  ar_state_e   ar_state_d, ar_state_q;

  typedef enum logic [1:0] { FEEDTHROUGH_R, WAIT_DATA_R, WAIT_CHANNEL_R, SEND_R } r_state_e;
  r_state_e    r_state_d, r_state_q;

  typedef enum logic [1:0] { NONE, INVALID, LOAD, STORE } atop_req_e;
  atop_req_e   atop_valid_d, atop_valid_q;

  /////////////////////////
  // Signal declarations //
  /////////////////////////
  // Transaction FF
  axi_aw_t axi_ax_d, axi_ax_q;
  axi_w_t  axi_w_d,  axi_w_q;
  axi_r_t  axi_r_d,  axi_r_q;

  // Data FF
  logic [AxiDataWidth-1:0]           result_d,       result_q;       // Result of AMO operation
  logic                              w_d_valid_d,    w_d_valid_q,    // AMO operand valid
                                     r_d_valid_d,    r_d_valid_q;    // Data from memory valid
  // Counters
  logic [OutstandingBurstsWidth-1:0] aw_trans_d,     aw_trans_q;     // AW transaction in flight downstream
  logic [OutstandingBurstsWidth-1:0] w_cnt_d,        w_cnt_q;        // Outstanding W beats
  logic [OutstandingBurstsWidth-1:0] w_cnt_req_d,    w_cnt_req_q;    // W beats until AMO can read W
  logic [OutstandingBurstsWidth-1:0] w_cnt_inj_d,    w_cnt_inj_q;    // W beats until AMO can insert its W
  // States
  logic                              adapter_ready;
  logic                              transaction_collision;
  logic                              atop_r_resp_d,    atop_r_resp_q;
  logic                              force_wf_d,       force_wf_q;
  logic                              start_wf_d,       start_wf_q;
  logic                              b_resp_valid;
  logic                              aw_valid_q,       aw_ready_q,       aw_free,
                                     w_valid_q,        w_ready_q,        w_free,
                                     b_valid_q,        b_ready_q,        b_free,
                                     ar_valid_q,       ar_ready_q,       ar_free,
                                     r_valid_q,        r_ready_q,        r_free;
  // ALU Signals
  logic [RiscvWordWidth-1:0]                    alu_operand_a;
  logic [RiscvWordWidth-1:0]                    alu_operand_b;
  logic [RiscvWordWidth-1:0]                    alu_result;
  logic [AxiDataWidth-1:0]                      alu_result_ext;
  logic [AxiAluRatio-1:0][RiscvWordWidth-1:0]   op_a;
  logic [AxiAluRatio-1:0][RiscvWordWidth-1:0]   op_b;
  logic [AxiAluRatio-1:0][RiscvWordWidth-1:0]   op_a_sign_ext;
  logic [AxiAluRatio-1:0][RiscvWordWidth-1:0]   op_b_sign_ext;
  logic [AxiAluRatio-1:0][RiscvWordWidth-1:0]   res;
  logic [AxiStrbWidth-1:0][7:0]                 strb_ext;
  logic                                         sign_a;
  logic                                         sign_b;

  ////////////////////////////////////////////////
  // Calculate ready signals and channel states //
  ////////////////////////////////////////////////

  // Check if all state machines are ready for the next atomic request
  always_comb adapter_ready = (aw_state_q == FEEDTHROUGH_AW)
                           && ( w_state_q == FEEDTHROUGH_W )
                           && ( b_state_q == FEEDTHROUGH_B )
                           && (ar_state_q == FEEDTHROUGH_AR)
                           && ( r_state_q == FEEDTHROUGH_R );

  // Calculate if the channels are free
  always_comb aw_free = ~aw_valid_q | aw_ready_q;
  always_comb  w_free =  ~w_valid_q |  w_ready_q;
  always_comb  b_free =  ~b_valid_q |  b_ready_q;
  always_comb ar_free = ~ar_valid_q | ar_ready_q;
  always_comb  r_free =  ~r_valid_q |  r_ready_q;

  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if(~i_rst_n) begin
      aw_valid_q <= 1'b0;
      aw_ready_q <= 1'b0;
      w_valid_q  <= 1'b0;
      w_ready_q  <= 1'b0;
      b_valid_q  <= 1'b0;
      b_ready_q  <= 1'b0;
      ar_valid_q <= 1'b0;
      ar_ready_q <= 1'b0;
      r_valid_q  <= 1'b0;
      r_ready_q  <= 1'b0;
    end else begin
      aw_valid_q <= o_axi_m_aw_valid;
      aw_ready_q <= i_axi_m_aw_ready;
      w_valid_q  <= o_axi_m_w_valid;
      w_ready_q  <= i_axi_m_w_ready;
      b_valid_q  <= o_axi_s_b_valid;
      b_ready_q  <= i_axi_s_b_ready;
      ar_valid_q <= o_axi_m_ar_valid;
      ar_ready_q <= i_axi_m_ar_ready;
      r_valid_q  <= o_axi_s_r_valid;
      r_ready_q  <= i_axi_s_r_ready;
    end
  end

  // Calculate if the request interferes with the ongoing atomic transaction
  // The protected bytes go from addr_q up to addr_q + (1 << size_q) - 1
  always_comb transaction_collision = (i_axi_s_aw.addr < (  axi_ax_q.addr + (8'h01 <<   axi_ax_q.size)))
                                    & (  axi_ax_q.addr < (i_axi_s_aw.addr + (8'h01 << i_axi_s_aw.size)));

  always_comb begin : calc_atop_valid
    atop_valid_d  = atop_valid_q;
    atop_r_resp_d = atop_r_resp_q;
    if (adapter_ready) begin
      atop_valid_d = NONE;
      atop_r_resp_d = 1'b0;
      if (i_axi_s_aw_valid && (i_axi_s_aw.atop[5:4] != axi_pkg::AXI_ATOP_NONE)) begin
        // Default is invalid request
        atop_valid_d = INVALID;
        // Valid load operation
        if (  (i_axi_s_aw.atop      ==  axi_pkg::AXI_ATOP_ATOMICSWAP)
            ||(i_axi_s_aw.atop[5:3] == {axi_pkg::AXI_ATOP_ATOMICLOAD , axi_pkg::AXI_ATOP_LITTLE_END})
        ) begin
          atop_valid_d = LOAD;
        end
        // Valid store operation
        if (i_axi_s_aw.atop[5:3] == {axi_pkg::AXI_ATOP_ATOMICSTORE, axi_pkg::AXI_ATOP_LITTLE_END}) begin
          atop_valid_d = STORE;
        end
        // Invalidate valid request if control signals do not match
        // Burst or exclusive access
        if (i_axi_s_aw.len || i_axi_s_aw.lock) begin
          atop_valid_d = INVALID;
        end
        // Unsupported size
        if (i_axi_s_aw.size > axi_pkg::axi_size_e'($clog2(RiscvWordWidth/8))) begin
          atop_valid_d = INVALID;
        end
        // Do we have to issue a r_resp?
        if (i_axi_s_aw.atop[axi_pkg::AXI_ATOP_R_RESP_IDX]) begin
          atop_r_resp_d = 1'b1;
        end
      end
    end
  end

  //////////////////////////////////////////
  // Assertions for buggy error Behaviour //
  //////////////////////////////////////////
  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON

  property p_no_support_acompare;
    @(posedge i_clk)
    disable iff (!i_rst_n)
    i_axi_s_aw_valid |-> i_axi_s_aw.atop != axi_pkg::AXI_ATOP_ATOMICCMP;
  endproperty : p_no_support_acompare
  check_p_no_support_acompare : assume property (p_no_support_acompare);

  property p_no_support_big_endian;
    @(posedge i_clk)
    disable iff (!i_rst_n)
    i_axi_s_aw_valid |-> i_axi_s_aw.atop[3] != axi_pkg::AXI_ATOP_BIG_END;
  endproperty : p_no_support_big_endian
  check_p_no_support_big_endian : assume property (p_no_support_big_endian);

  `endif
  `endif

  always_ff @(posedge i_clk or negedge i_rst_n) begin : proc_atop_valid
    if(~i_rst_n) begin
      atop_valid_q <= NONE;
      atop_r_resp_q <= 1'b0;
    end else begin
      atop_valid_q <= atop_valid_d;
      atop_r_resp_q <= atop_r_resp_d;
    end
  end

  /////////////////////////////
  // Write Channel: AW, W, B //
  /////////////////////////////

  ////////
  // AW //                               =
  ////////
  always_comb begin : axi_aw_channel
    // Defaults AXI Bus
    o_axi_m_aw      = i_axi_s_aw;
    o_axi_m_aw.atop = 6'b00_0000;
    // Defaults FF
    axi_ax_d        = axi_ax_q;
    w_cnt_inj_d     = w_cnt_inj_q;
    // State Machine
    aw_state_d      = aw_state_q;

    // Default control: Block AW channel if...
    if (  i_axi_s_aw_valid
      && (i_axi_s_aw.atop[5:4] != axi_pkg::AXI_ATOP_NONE)
    ) begin
        // Block if atomic request
        o_axi_m_aw_valid = 1'b0;
        o_axi_s_aw_ready = 1'b0;
    end else if (
         (w_cnt_q    == AxiMaxWriteTxns)
      || (aw_trans_q == AxiMaxWriteTxns)
    ) begin
        // Block if counter is overflowing
        o_axi_m_aw_valid = 1'b0;
        o_axi_s_aw_ready = 1'b0;
    end else if (force_wf_q && aw_free) begin
        // Block if the adapter is in force wait-free mode and the AW is free
        o_axi_m_aw_valid = 1'b0;
        o_axi_s_aw_ready = 1'b0;
    end else if (i_axi_s_aw_valid && transaction_collision && !adapter_ready) begin
        // Block requests to the same address as current atomic transaction
        o_axi_m_aw_valid = 1'b0;
        o_axi_s_aw_ready = 1'b0;
    end else begin
        // Forward
        o_axi_m_aw_valid = i_axi_s_aw_valid;
        o_axi_s_aw_ready = i_axi_m_aw_ready;
    end

    // Count W burst to know when to inject the W data
    if (w_cnt_inj_q && o_axi_m_w_valid && i_axi_m_w_ready && o_axi_m_w.last) begin
        w_cnt_inj_d = w_cnt_inj_q - 1;
    end

    unique case (aw_state_q)

      FEEDTHROUGH_AW: begin
        // Feedthrough slave to master until atomic operation is detected
        if (  i_axi_s_aw_valid
          && (i_axi_s_aw.atop[5:4] != axi_pkg::AXI_ATOP_NONE)
          && adapter_ready
        ) begin
          // Acknowledge atomic transaction
          o_axi_s_aw_ready = 1'b1;
          // Remember request
          axi_ax_d         = i_axi_s_aw;
          // If valid AMO --> wait for result
          if (atop_valid_d != INVALID) begin
            aw_state_d = WAIT_RESULT_AW;
          end
        end

        if (start_wf_q) begin
          // Forced wait-free state --> wait for ALU once more
          aw_state_d = WAIT_RESULT_AW;
        end
      end // FEEDTHROUGH_AW

      WAIT_RESULT_AW, SEND_AW: begin
        // If the result is ready and the channel is free --> inject AW request
        if ( (r_d_valid_q && w_d_valid_q && aw_free)
          || (aw_state_q == SEND_AW)
        ) begin
          // Block
          o_axi_s_aw_ready = 1'b0;
          // Make write request
          o_axi_m_aw_valid = 1'b1;
          o_axi_m_aw       = axi_ax_q;
          o_axi_m_aw.atop  = axi_pkg::axi_atop_t'(0); // do not accidentally send out a atop field downstream
          o_axi_m_aw.len   = 8'h00;
          o_axi_m_aw.burst = axi_pkg::BurstIncr;
          o_axi_m_aw.lock  = ~force_wf_q;

          // Check if request is acknowledged
          if (i_axi_m_aw_ready) begin
            aw_state_d = FEEDTHROUGH_AW;
          end else begin
            aw_state_d = SEND_AW;
          end
          // Remember outstanding W beats before injected request
          if (aw_state_q == WAIT_RESULT_AW) begin
            if (w_cnt_q && o_axi_m_w_valid && i_axi_m_w_ready && o_axi_m_w.last) begin
              w_cnt_inj_d = w_cnt_q - 1;
            end else begin
              w_cnt_inj_d = w_cnt_q;
            end
          end
        end
      end // WAIT_RESULT_AW, SEND_AW

      default: aw_state_d = FEEDTHROUGH_AW;

    endcase
  end : axi_aw_channel

  ///////
  // W //
  ///////
  always_comb begin : axi_w_channel
    // Defaults AXI Bus
    o_axi_m_w    = i_axi_s_w;
    // Defaults FF
    axi_w_d      = axi_w_q;
    result_d     = result_q;
    w_d_valid_d  = w_d_valid_q;
    w_cnt_req_d  = w_cnt_req_q;
    // State Machine
    w_state_d    = w_state_q;

    // Default control
    // Make sure no data is sent without knowing if it's atomic
    if (w_cnt_q == 0) begin
      // Stall W as it precedes the AW request
      o_axi_m_w_valid = 1'b0;
      o_axi_s_w_ready = 1'b0;
    end else begin
      o_axi_m_w_valid = i_axi_s_w_valid;
      o_axi_s_w_ready = i_axi_m_w_ready;
    end

    unique case (w_state_q)

      FEEDTHROUGH_W: begin
        if (adapter_ready) begin
          // Reset read flag
          w_d_valid_d = 1'b0;
          result_d    = '0;

          if (atop_valid_d != NONE) begin
            // Check if data is also available and does not belong to previous request
            if (w_cnt_q == 0) begin
              // Block downstream
              o_axi_m_w_valid = 1'b0;
              // Fetch data and wait for all data
              o_axi_s_w_ready = 1'b1;
              if (i_axi_s_w_valid) begin
                if (atop_valid_d != INVALID) begin
                  axi_w_d     = i_axi_s_w;
                  w_d_valid_d = 1'b1;
                  w_state_d   = WAIT_RESULT_W;
                end
              end else begin
                w_cnt_req_d = '0;
                w_state_d   = WAIT_DATA_W;
              end
            end else begin
              // Remember the amount of outstanding bursts and count down
              if (o_axi_m_w_valid && i_axi_m_w_ready && o_axi_m_w.last) begin
                w_cnt_req_d = w_cnt_q - 1;
              end else begin
                w_cnt_req_d = w_cnt_q;
              end
              w_state_d   = WAIT_DATA_W;
            end
          end
        end

        if (start_wf_q) begin
          // Forced wait-free state --> wait for ALU once more
          w_state_d = WAIT_RESULT_W;
        end
      end // FEEDTHROUGH_W

      WAIT_DATA_W: begin
        // Count W beats until data arrives that belongs to the AMO request
        if (w_cnt_req_q == 0) begin
          // Block downstream
          o_axi_m_w_valid = 1'b0;
          // Ready upstream
          o_axi_s_w_ready = 1'b1;

          if (i_axi_s_w_valid) begin
            if (atop_valid_q == INVALID) begin
              w_state_d    = FEEDTHROUGH_W;
            end else begin
              axi_w_d     = i_axi_s_w;
              w_d_valid_d = 1'b1;
              w_state_d   = WAIT_RESULT_W;
            end
          end
        end else if (o_axi_m_w_valid && i_axi_m_w_ready && o_axi_m_w.last) begin
          w_cnt_req_d = w_cnt_req_q - 1;
        end
      end // WAIT_DATA_W

      WAIT_RESULT_W: begin
        // If the result is ready, try to write it
        if (r_d_valid_q && w_d_valid_q && aw_free) begin
          // Check if W channel is free and make sure data is not interleaved
          result_d = alu_result_ext;
          if (w_free && w_cnt_q == 0) begin
            // Block
            o_axi_s_w_ready = 1'b0;
            // Send write data
            o_axi_m_w_valid = 1'b1;
            o_axi_m_w       = axi_w_q;
            o_axi_m_w.data  = alu_result_ext;
            o_axi_m_w.last  = 1'b1;
            if (i_axi_m_w_ready) begin
              w_state_d = FEEDTHROUGH_W;
            end else begin
              w_state_d = SEND_W;
            end
          end else begin
            w_state_d = WAIT_CHANNEL_W;
          end
        end
      end // WAIT_RESULT_W

      WAIT_CHANNEL_W, SEND_W: begin
        // Wait to not interleave the data
        if ((w_free && w_cnt_inj_q == 0) || (w_state_q == SEND_W)) begin
          // Block
          o_axi_s_w_ready = 1'b0;
          // Send write data
          o_axi_m_w_valid = 1'b1;
          o_axi_m_w       = axi_w_q;
          o_axi_m_w.data  = result_q;
          o_axi_m_w.last  = 1'b1;
          if (i_axi_m_w_ready) begin
            w_state_d = FEEDTHROUGH_W;
          end else begin
            w_state_d = SEND_W;
          end
        end
      end // WAIT_CHANNEL_W, SEND_W

      default: w_state_d = FEEDTHROUGH_W;

    endcase
  end : axi_w_channel

  ///////
  // B //
  ///////
  always_comb begin : axi_b_channel
    // Defaults AXI Bus
    o_axi_s_b       = i_axi_m_b;
    o_axi_s_b_valid = i_axi_m_b_valid;
    o_axi_m_b_ready = i_axi_s_b_ready;
    // Defaults FF
    force_wf_d      = force_wf_q;
    start_wf_d      = 1'b0;
    b_resp_valid    = 1'b0;
    // State Machine
    b_state_d       = b_state_q;

    unique case (b_state_q)

      FEEDTHROUGH_B: begin
        if (adapter_ready) begin
          if (atop_valid_d == LOAD || atop_valid_d == STORE) begin
            // Wait until write is complete
            b_state_d = WAIT_COMPLETE_B;
          end else if (atop_valid_d == INVALID) begin
            // Inject B error resp once the channel is free
            if (b_free) begin
              // Block downstream
              o_axi_m_b_ready = 1'b0;
              // Write B response
              o_axi_s_b_valid = 1'b1;
              o_axi_s_b.id    = i_axi_s_aw.id;
              o_axi_s_b.resp  = axi_pkg::RespSlvErr;
              // o_axi_s_b.user  = axi_ax_q.user;
              if (!i_axi_s_b_ready) begin
                b_state_d = SEND_B;
              end
            end else begin
              b_state_d = WAIT_CHANNEL_B;
            end
          end
        end
      end // FEEDTHROUGH_B

      WAIT_CHANNEL_B, SEND_B: begin
        if (b_free || (b_state_q == SEND_B)) begin
          // Block downstream
          o_axi_m_b_ready = 1'b0;
          // Write B response
          o_axi_s_b_valid = 1'b1;
          o_axi_s_b.id    = axi_ax_q.id;
          o_axi_s_b.resp  = axi_pkg::RespSlvErr;
          // o_axi_s_b.user  = axi_ax_q.user;
          if (i_axi_s_b_ready) begin
            b_state_d = FEEDTHROUGH_B;
          end else begin
            b_state_d = SEND_B;
          end
        end
      end // WAIT_CHANNEL_B, SEND_B

      WAIT_COMPLETE_B: begin
        if (i_axi_m_b_valid && (i_axi_m_b.id == axi_ax_q.id)) begin
          // Check if store-conditional was successful
          if (i_axi_m_b.resp == axi_pkg::RespOkay) begin
            if (force_wf_q) begin
              // We were in wf mode so now we are done
              force_wf_d    = 1'b0;
              b_resp_valid  = 1'b1;
              b_state_d     = FEEDTHROUGH_B;
            end else begin
              // We were not in wf mode --> catch response
              o_axi_m_b_ready = 1'b1;
              o_axi_s_b_valid = 1'b0;
              // Go into wf mode
              start_wf_d      = 1'b1;
              force_wf_d      = 1'b1;
            end
          end else if (i_axi_m_b.resp == axi_pkg::RespExOkay) begin
            // Modify the B response to regular OK.
            b_resp_valid   = 1'b1;
            o_axi_s_b.resp = axi_pkg::RespOkay;
            if (i_axi_s_b_ready) begin
              b_state_d = FEEDTHROUGH_B;
            end
          end else begin
            b_resp_valid = 1'b1;
            b_state_d    = FEEDTHROUGH_B;
          end
        end
      end // WAIT_COMPLETE_B

      default: b_state_d = FEEDTHROUGH_B;

    endcase
  end : axi_b_channel

  // Keep track of AW requests missing a W and of downstream transactions
  always_comb begin
    w_cnt_d    = w_cnt_q;
    aw_trans_d = aw_trans_q;
    if (o_axi_m_aw_valid && i_axi_m_aw_ready) begin
      w_cnt_d    += 1;
      aw_trans_d += 1;
    end
    if (o_axi_m_w_valid && i_axi_m_w_ready && o_axi_m_w.last) begin
      w_cnt_d    -= 1;
    end
    if (i_axi_m_b_valid && o_axi_m_b_ready) begin
      aw_trans_d -= 1;
    end
  end

  always_ff @(posedge i_clk or negedge i_rst_n) begin : axi_write_channel_ff
    if(~i_rst_n) begin
      aw_state_q  <= FEEDTHROUGH_AW;
      w_state_q   <= FEEDTHROUGH_W;
      b_state_q   <= FEEDTHROUGH_B;
      aw_trans_q  <= '0;
      w_cnt_q     <= '0;
      w_cnt_req_q <= '0;
      w_cnt_inj_q <= '0;
      force_wf_q  <= 1'b0;
      start_wf_q  <= 1'b0;
      axi_ax_q    <= '0;
      axi_w_q     <= '0;
      result_q    <= '0;
      w_d_valid_q <= '0;
    end else begin
      aw_state_q  <= aw_state_d;
      w_state_q   <= w_state_d;
      b_state_q   <= b_state_d;
      aw_trans_q  <= aw_trans_d;
      w_cnt_q     <= w_cnt_d;
      w_cnt_req_q <= w_cnt_req_d;
      w_cnt_inj_q <= w_cnt_inj_d;
      force_wf_q  <= force_wf_d;
      start_wf_q  <= start_wf_d;
      axi_ax_q    <= axi_ax_d;
      axi_w_q     <= axi_w_d;
      result_q    <= result_d;
      w_d_valid_q <= w_d_valid_d;
    end
  end

  /////////////////////////
  // Read Channel: AR, R //
  /////////////////////////

  ////////
  // AR //
  ////////
  always_comb begin : axi_ar_channel
    // Defaults AXI Bus
    o_axi_m_ar       = i_axi_s_ar;
    o_axi_m_ar_valid = 1'b0;
    o_axi_s_ar_ready = 1'b0;
    // State Machine
    ar_state_d       = ar_state_q;

    unique case (ar_state_q)

      FEEDTHROUGH_AR: begin
        // Feed through
        o_axi_m_ar_valid = i_axi_s_ar_valid;
        o_axi_s_ar_ready = i_axi_m_ar_ready;

        if (adapter_ready && (atop_valid_d == LOAD || atop_valid_d == STORE)) begin
          if (ar_free) begin
            // Acquire channel
            o_axi_s_ar_ready  = 1'b0;
            // Immediately start read request
            o_axi_m_ar_valid = 1'b1;
            o_axi_m_ar       = assign_aw_to_ar(i_axi_s_aw);
            o_axi_m_ar.len   = 8'h00;
            o_axi_m_ar.burst = axi_pkg::BurstIncr;
            o_axi_m_ar.lock  = ~force_wf_q;
            if (!i_axi_m_ar_ready) begin
              // Hold read request but do not depend on AW
              ar_state_d = SEND_AR;
            end
          end else begin
            // Wait until AR is free
            ar_state_d   = WAIT_CHANNEL_AR;
          end
        end

        if (start_wf_q) begin
            ar_state_d = WAIT_CHANNEL_AR;
        end
      end // FEEDTHROUGH_AR

      WAIT_CHANNEL_AR, SEND_AR: begin
        // Issue read request
        if ((ar_free  && (aw_trans_q == 0 || force_wf_q == 0)) || (ar_state_q == SEND_AR)) begin
          // Inject read request
          o_axi_m_ar_valid = 1'b1;
          o_axi_m_ar       = assign_aw_to_ar(axi_ax_q);
          o_axi_m_ar.len   = 8'h00;
          o_axi_m_ar.burst = axi_pkg::BurstIncr;
          o_axi_m_ar.lock  = ~force_wf_q;
          if (i_axi_m_ar_ready) begin
            // Request acknowledged
            ar_state_d = FEEDTHROUGH_AR;
          end else begin
            // Hold read request
            ar_state_d = SEND_AR;
          end
        end else begin
          // Wait until AR is free
          o_axi_m_ar_valid = i_axi_s_ar_valid;
          o_axi_s_ar_ready = i_axi_m_ar_ready;
        end
      end // WAIT_CHANNEL_AR, SEND_AR

      default: ar_state_d = FEEDTHROUGH_AR;

    endcase
  end : axi_ar_channel

  ///////////////////////////
  // R : Read Data Channel //
  ///////////////////////////
  always_comb begin : axi_r_channel
    // Defaults AXI Bus
    o_axi_s_r       = i_axi_m_r;
    o_axi_s_r_valid = i_axi_m_r_valid;
    o_axi_m_r_ready = i_axi_s_r_ready;

    // Defaults FF
    axi_r_d       = axi_r_q;
    r_d_valid_d   = r_d_valid_q;
    // State Machine
    r_state_d     = r_state_q;

    unique case (r_state_q)

      FEEDTHROUGH_R: begin
        if (adapter_ready) begin
          // Reset read flag
          r_d_valid_d = 1'b0;

          if (atop_valid_d == LOAD || atop_valid_d == STORE) begin
            // Wait for R response to read data
            r_state_d = WAIT_DATA_R;
          end else if (atop_valid_d == INVALID && atop_r_resp_d) begin
            // Send R response once channel is free
            if (r_free) begin
              // Acquire the R channel
              // Block downstream
              o_axi_m_r_ready = 1'b0;
              // Send R error response
              o_axi_s_r_valid = 1'b1;
              o_axi_s_r.data  = '0;
              o_axi_s_r.id    = i_axi_s_aw.id;
              o_axi_s_r.last  = 1'b1;
              o_axi_s_r.resp  = axi_pkg::RespSlvErr;
              // o_axi_s_r.user  = axi_axi_q.user;
              if (!i_axi_s_r_ready) begin
                // Hold R response
                r_state_d = SEND_R;
              end
            end else begin
              r_state_d = WAIT_CHANNEL_R;
            end
          end
        end

        if (start_wf_q) begin
          r_d_valid_d = 1'b0;
          r_state_d   = WAIT_DATA_R;
        end
      end // FEEDTHROUGH_R

      WAIT_DATA_R: begin
        // Read data
        if (i_axi_m_r_valid && (i_axi_m_r.id == axi_ax_q.id)) begin
          // Acknowledge downstream and block upstream
          o_axi_m_r_ready = 1'b1;
          o_axi_s_r_valid = 1'b0;
          // Store data
          axi_r_d     = i_axi_m_r;
          r_d_valid_d = 1'b1;
          if (atop_valid_q == STORE) begin
            r_state_d = FEEDTHROUGH_R;
          end else begin
            // Wait for B resp before injecting R
            r_state_d = WAIT_CHANNEL_R;
          end
        end
      end // WAIT_DATA_R

      WAIT_CHANNEL_R, SEND_R: begin
        // Wait for the R channel to become free and B response to be valid
        if ((r_free && (b_resp_valid || b_state_q != WAIT_COMPLETE_B)) || (r_state_q == SEND_R)) begin
          // Block downstream
          o_axi_m_r_ready = 1'b0;
          // Send R response
          o_axi_s_r_valid = 1'b1;
          o_axi_s_r       = axi_r_q;
          o_axi_s_r.id    = axi_ax_q.id;
          o_axi_s_r.last  = 1'b1;
          if (atop_valid_q == INVALID && atop_r_resp_q) begin
            o_axi_s_r.data = '0;
            o_axi_s_r.resp = axi_pkg::RespSlvErr;
            // o_axi_s_r.user = axi_ax_q.user;
          end
          if (i_axi_s_r_ready) begin
            r_state_d = FEEDTHROUGH_R;
          end else begin
            r_state_d = SEND_R;
          end
        end

        if (start_wf_q) begin
          r_d_valid_d = 1'b0;
          r_state_d   = WAIT_DATA_R;
        end
      end // WAIT_CHANNEL_R, SEND_R

      default: r_state_d = FEEDTHROUGH_R;

    endcase
  end // axi_r_channel

  always_ff @(posedge i_clk or negedge i_rst_n) begin : axi_read_channel_ff
    if(~i_rst_n) begin
      ar_state_q  <= FEEDTHROUGH_AR;
      r_state_q   <= FEEDTHROUGH_R;
      axi_r_q     <= '0;
      r_d_valid_q <= 1'b0;
    end else begin
      ar_state_q  <= ar_state_d;
      r_state_q   <= r_state_d;
      axi_r_q     <= axi_r_d;
      r_d_valid_q <= r_d_valid_d;
    end
  end

  ///////////////////////////
  // Arithmetic Logic Unit //
  ///////////////////////////

  always_comb op_a           = axi_r_q.data & strb_ext;
  always_comb op_b           = axi_w_q.data & strb_ext;
  always_comb sign_a         = |(op_a & ~(strb_ext >> 1));
  always_comb sign_b         = |(op_b & ~(strb_ext >> 1));
  always_comb alu_result_ext = res;

  if (AxiAluRatio == 1 && RiscvWordWidth == 32) begin : gen_riscv_32
    always_comb alu_operand_a = op_a;
    always_comb alu_operand_b = op_b;
    always_comb res           = alu_result;
  end : gen_riscv_32
  else if (AxiAluRatio == 1 && RiscvWordWidth == 64) begin : gen_riscv_64
    always_comb res = alu_result;
    always_comb begin
      op_a_sign_ext = op_a | ({AxiAluRatio*RiscvWordWidth{sign_a}} & ~strb_ext);
      op_b_sign_ext = op_b | ({AxiAluRatio*RiscvWordWidth{sign_b}} & ~strb_ext);

      if ( axi_ax_q.atop[2:0] == axi_pkg::AXI_ATOP_SMAX
        || axi_ax_q.atop[2:0] == axi_pkg::AXI_ATOP_SMIN
      ) begin
        // Sign extend
        alu_operand_a = op_a_sign_ext;
        alu_operand_b = op_b_sign_ext;
      end else begin
        // No sign extension necessary
        alu_operand_a = op_a;
        alu_operand_b = op_b;
      end
    end
  end : gen_riscv_64
  else begin : gen_riscv_extended
    always_comb begin
      op_a_sign_ext = op_a | ({AxiAluRatio*RiscvWordWidth{sign_a}} & ~strb_ext);
      op_b_sign_ext = op_b | ({AxiAluRatio*RiscvWordWidth{sign_b}} & ~strb_ext);

      if ( axi_ax_q.atop[2:0] == axi_pkg::AXI_ATOP_SMAX
        || axi_ax_q.atop[2:0] == axi_pkg::AXI_ATOP_SMIN
      ) begin
        // Sign extend
        alu_operand_a = op_a_sign_ext[axi_ax_q.addr[$clog2(AxiDataWidth/8)-1:$clog2(RiscvWordWidth/8)]];
        alu_operand_b = op_b_sign_ext[axi_ax_q.addr[$clog2(AxiDataWidth/8)-1:$clog2(RiscvWordWidth/8)]];
      end else begin
        // No sign extension necessary
        alu_operand_a = op_a[axi_ax_q.addr[$clog2(AxiDataWidth/8)-1:$clog2(RiscvWordWidth/8)]];
        alu_operand_b = op_b[axi_ax_q.addr[$clog2(AxiDataWidth/8)-1:$clog2(RiscvWordWidth/8)]];
      end

      res = '0;
      res[axi_ax_q.addr[$clog2(AxiDataWidth/8)-1:$clog2(RiscvWordWidth/8)]] = alu_result;
    end
  end : gen_riscv_extended

  always_comb begin
    strb_ext = '0;
    for (int unsigned strb_idx = 0; strb_idx < AxiStrbWidth; strb_idx++)
      if (axi_w_q.strb[strb_idx]) strb_ext[strb_idx] = 8'hFF;
  end

  axe_axi_riscv_amos_alu #(
    .DataWidth(RiscvWordWidth)
  ) u_amo_alu (
    .i_amo_op       (axi_ax_q.atop),
    .i_amo_operand_a(alu_operand_a),
    .i_amo_operand_b(alu_operand_b),
    .o_amo_result   (alu_result)
  );
endmodule
