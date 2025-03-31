// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// This unit combines the read data and a copy request into AXI AW/W transactions.
///
/// The *copy write unit* handles the handshaking of the write related AXI channels independently.
/// A copy command is broken up into the respective transactions and distributed to each channel
/// respective logic.  A stream fork on the `AW` channel takes care of distribution.
/// The overall structure is depicted in the diagram:
///
/// ![AIC_CD_COPY_WRITE_REQUEST: Block Diagram](figures/aic_cd_copy_write_request.drawio.svg)
///
///
/// ## Write Request (AW)
///
/// Each *copy command* is broken down into AW transactions.  The unit calculates the largest possible
/// transfer that is allowed in a 4KB window.  When a copy command would cross this boundary it performs
/// a transactions the boundary then continue with max length transactions.  It keeps track of the
/// remaining bytes which need to be transferred via a counter.  Here we also determine the metadata
/// which is needed to properly form the *strobes* for the write data.  For transferring an `AW` vector
/// we forward the respective metadata information to the write and response queues.  This is handled
/// via a *stream fork* to ensure proper handshaking and back-pressure.
///
/// !!! warning "Data Availability"
///
///     The unit does **not wait** for data to be available before making a AW request!
///
///
/// ## Write Data (W)
///
/// The metadata buffer towards the write channel contains information to steer the strobes.
/// The control also has a counter to keep track of how many beats must be transferred.
/// The *stream disconnect* will only let data through when we know the respective metadata.
///
/// !!! tip "Strobe Calculation"
///
///     The strobe is calculated from the metadata by applying some masks on the strobe.  Special
///     cases are the first and last beat of an transaction.  The mask for these are exrtracted from
///     the *write metadata* and applied on the respective beats.  The metadata contains the number of
///     bytes which are not used. Therefore the masks can be calculated by applying shifts.
///     The final `w.strb` is the `AND`-ing of all masks that apply for that respective beat.
///
///
/// ## Write Response (B)
///
/// The responses only job is to report eventual errors coming back from the bus.  The instruction
/// index resides in the spill register.  The moment we know the instruction index we expect a response
/// for the bus `ready` is asserted.  On transaction we can pop the index from the buffer.
/// The response will generate an error appropriately and report the instruction which was responsible.
///
module aic_cd_copy_write_request #(
  /// The Axi ID width of the AXI channel
  parameter int unsigned AxiIdWidth = aic_cd_defaults_pkg::AXI_M_ID_WIDTH,
  /// The Concrete AXI ID to use
  parameter logic [AxiIdWidth-1:0] AxiIdForCopy = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(0),
  /// The Address width of the AXI channel
  parameter int unsigned AxiAddrWidth = aic_cd_defaults_pkg::AXI_M_ADDR_WIDTH,
  /// The Data width of the AXI channel
  parameter int unsigned AxiDataWidth = aic_cd_defaults_pkg::AXI_M_DATA_WIDTH,
  /// AW Channel Type
  parameter type axi_aw_t = aic_cd_defaults_pkg::axi_m_aw_t,
  ///  W Channel Type
  parameter type axi_w_t  = aic_cd_defaults_pkg::axi_m_w_t,
  ///  B Channel Type
  parameter type axi_b_t  = aic_cd_defaults_pkg::axi_m_b_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ///////////////////////
  // Status and errors //
  ///////////////////////
  /// The unit is busy
  output logic                               o_busy,
  /// The write response returnd a SLVERR
  output logic                               o_resp_slverr,
  /// The write response returnd a DECERR
  output logic                               o_resp_decerr,
  /// The instruction index the error occured
  output aic_cd_pkg::task_list_word_length_t o_instruction_index,

  //////////////////
  // Copy Request //
  //////////////////
  /// The copy command
  input  aic_cd_pkg::copy_command_t i_copy_command,
  /// The copy command is valid
  input  logic                      i_copy_command_valid,
  /// Dowstream consumes copy command
  output logic                      o_copy_command_ready,

  /////////////////////////////
  // Data from the read side //
  /////////////////////////////
  /// The (potentially patched) data to write back
  input  logic [AxiDataWidth-1:0] i_patched_data,
  /// The data is valid
  input  logic                    i_patched_data_valid,
  /// The data is ready
  output logic                    o_patched_data_ready,

  ///////////////////////////////////
  // AXI W Manager (Only AW and W) //
  ///////////////////////////////////
  /// The AW channel payload
  output axi_aw_t o_axi_m_aw,
  /// The AW channel is valid
  output logic    o_axi_m_aw_valid,
  /// The AW channel is ready
  input  logic    i_axi_m_aw_ready,
  /// The W channel payload
  output axi_w_t  o_axi_m_w,
  /// The W channel is valid
  output logic    o_axi_m_w_valid,
  /// The W channel is ready
  input  logic    i_axi_m_w_ready,
  /// The W channel payload
  input  axi_b_t  i_axi_m_b,
  /// The W channel is valid
  input  logic    i_axi_m_b_valid,
  /// The W channel is ready
  output logic    o_axi_m_b_ready
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  if (AxiIdWidth != $bits(o_axi_m_aw.id))
      $fatal(1, "Parameter: 'AxiIdWidth (%d)' must match axi_aw_t.id (%d);",
      AxiIdWidth, $bits(o_axi_m_aw.id));
  if (AxiDataWidth != $bits(o_axi_m_w.data))
      $fatal(1, "Parameter: 'AxiDataWidth (%d)' must match axi_aw_t.id (%d);",
      AxiDataWidth, $bits(o_axi_m_w.data));
  if (AxiDataWidth != 64) $fatal(1, "Parameter: 'AxiDataWidth (%d)' must be 64;", AxiDataWidth);


  /// The AXI field type
  typedef logic [AxiAddrWidth-1:0] axi_addr_t;
  /// The AXI strobe width
  localparam int unsigned AxiStrbWidth = AxiDataWidth / 8;
  /// The AXi strobe field type
  typedef logic [AxiStrbWidth-1:0] axi_strb_t;
  /// The width needed to represent how many bits are active in a strobe
  localparam int unsigned AxiNumStrbWidth = cc_math_pkg::index_width(AxiStrbWidth);
  /// Representation of how many strobes are active
  typedef logic [AxiNumStrbWidth-1:0] num_inactive_strb_t;


  /// This encodes the information for the strobing of W
  typedef struct packed {
    /// The number of inactive strobes on the last beat
    num_inactive_strb_t  num_inactive_strb_last;
    /// The number of inactive strobes on the first beat
    num_inactive_strb_t  num_inactive_strb_first;
    /// The AXI len field transmitted
    axi_pkg::axi_len_t   axi_len;
  } write_metadata_t;

  ///////////////////////////
  // AW Request Generation //
  ///////////////////////////
  typedef enum logic [1:0] {
    AW_IDLE,
    AW_ACTIVE
  } aw_state_e;
  aw_state_e aw_state_q, aw_state_d;

  localparam axi_aw_t AxiAwDefaults = axi_aw_t'{
    id:    AxiIdForCopy,
    size:  axi_pkg::Bytes008,
    burst: axi_pkg::BurstIncr,
    /*
    cache:   Uses default,
    prot:    Uses default,
    */
    default: 0
  };

  aic_cd_pkg::copy_byte_length_t bytes_to_copy_q;
  aic_cd_pkg::copy_byte_length_t bytes_in_transaction;
  axi_addr_t                     aw_addr_q, aw_addr_d;
  logic                          aw_addr_update;
  logic                          axi_m_aw_valid;
  logic                          axi_m_aw_ready;
  write_metadata_t               aw_metadata;
  logic                          aw_metadata_valid;
  logic                          aw_metadata_ready;

  cc_cnt_delta #(
    .Width(aic_cd_pkg::CopyByteLengthWidth)
  ) u_cnt_remaining_bytes (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (axi_m_aw_valid & axi_m_aw_ready),
    .i_cnt_down(1'b1),
    .i_delta   (bytes_in_transaction),
    .o_q       (bytes_to_copy_q),
    .i_d       (i_copy_command.num_bytes),
    .i_d_load  (i_copy_command_valid & o_copy_command_ready),
    .o_overflow(/* not used */)
  );

  // We are allowed to transfer up to the 4K boundary
  aic_cd_pkg::copy_byte_length_t bytes_to_4k_boundary;
  aic_cd_pkg::copy_byte_length_t bytes_in_max_len_transaction;

  always_comb bytes_to_4k_boundary =
      aic_cd_pkg::copy_byte_length_t'(4096)
    - aic_cd_pkg::copy_byte_length_t'(aw_addr_q[0+:$clog2(4096)]);
  always_comb bytes_in_max_len_transaction =
      (aic_cd_pkg::copy_byte_length_t'(2**axi_pkg::AXI_LEN_WIDTH) * aic_cd_pkg::copy_byte_length_t'(axi_pkg::axi_num_bytes(axi_pkg::Bytes008)))
    - aic_cd_pkg::copy_byte_length_t'(aw_addr_q[0+:axi_pkg::Bytes008]); // Substract unaligned first bytes

  // The amount of bytes we are allowed to transfer is the minimum of these 3
  aic_cd_pkg::copy_byte_length_t min_bytes_in_transaction[2];
  always_comb min_bytes_in_transaction[0] = (bytes_in_max_len_transaction < bytes_to_4k_boundary)
                                          ?  bytes_in_max_len_transaction : bytes_to_4k_boundary;
  always_comb min_bytes_in_transaction[1] = (bytes_in_max_len_transaction < bytes_to_copy_q)
                                          ?  bytes_in_max_len_transaction : bytes_to_copy_q;
  always_comb     bytes_in_transaction    = (min_bytes_in_transaction[0]  < min_bytes_in_transaction[1])
                                          ?  min_bytes_in_transaction[0]  : min_bytes_in_transaction[1];

  axi_pkg::axi_len_t aw_len;
  // Note: One less len for the case that the data and the address are aligned to the bus boundary
  always_comb aw_len = axi_pkg::axi_len_t'(bytes_in_transaction >> axi_pkg::Bytes008)
                     - axi_pkg::axi_len_t'(
                             (bytes_in_transaction[0+:axi_pkg::Bytes008] == axi_pkg::Bytes008'(0))
                          && (aw_addr_q[0+:axi_pkg::Bytes008]            == axi_pkg::Bytes008'(0))
                       );

  always_comb aw_metadata = '{
    num_inactive_strb_last:  num_inactive_strb_t'(
        (axi_pkg::axi_num_bytes(axi_pkg::Bytes008) * (aw_len+1)) // All possible bytes in a transaction
      - bytes_in_transaction                                     // All active bytes
      - aw_addr_q[0+:axi_pkg::Bytes008]                          // unalignemtn offset
    ),
     // The unaligned address points to the index of the first active strb
    num_inactive_strb_first: aw_addr_q[0+:axi_pkg::Bytes008],
    axi_len:                 aw_len
  };

  logic       is_last_transaction;
  always_comb is_last_transaction = bytes_in_transaction == bytes_to_copy_q;

  always_comb begin : proc_aw_fsm
    aw_state_d           = aw_state_q;
    o_copy_command_ready = 1'b0;
    axi_m_aw_valid       = 1'b0;

    aw_addr_d      = axi_addr_t'(i_copy_command.addr_destination);
    aw_addr_update = 1'b0;
    o_axi_m_aw     = AxiAwDefaults;

    unique case (aw_state_q)
      AW_IDLE: begin
        o_copy_command_ready = 1'b1;
        if (i_copy_command_valid) begin
          aw_addr_update = 1'b1;
          aw_state_d     = AW_ACTIVE;
        end
      end
      AW_ACTIVE: begin
        o_axi_m_aw.addr = aw_addr_q;
        o_axi_m_aw.len  = aw_len;
        axi_m_aw_valid  = 1'b1;
        if (axi_m_aw_ready) begin
          if (is_last_transaction) begin
            o_copy_command_ready = 1'b1;
            if (i_copy_command_valid) begin
              aw_addr_update = 1'b1;
            end else begin
              aw_state_d = AW_IDLE;
            end
          end else begin
            aw_addr_d      = aw_addr_q + axi_addr_t'(bytes_in_transaction);
            aw_addr_update = 1'b1;
          end
        end
      end
      default: aw_state_d = AW_IDLE;
    endcase
  end

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) aw_state_q <= AW_IDLE;
    else          aw_state_q <= aw_state_d;
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)            aw_addr_q <= axi_addr_t'(0);
    else if (aw_addr_update) aw_addr_q <= aw_addr_d;
  end

  aic_cd_pkg::task_list_word_length_t b_metadata_q;
  logic                               b_metadata_valid;
  logic                               b_metadata_ready;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)                                          b_metadata_q <= aic_cd_pkg::task_list_word_length_t'(0);
    else if (i_copy_command_valid && o_copy_command_ready) b_metadata_q <= i_copy_command.instruction_index;
  end

  cc_stream_fork #(
    .NumStreams(3)
  ) u_aw_fork (
    .i_clk,
    .i_rst_n,
    .i_flush (1'b0),
    .i_select(3'b111),
    .i_valid (axi_m_aw_valid),
    .o_ready (axi_m_aw_ready),
    .o_valid ({aw_metadata_valid, b_metadata_valid, o_axi_m_aw_valid}),
    .i_ready ({aw_metadata_ready, b_metadata_ready, i_axi_m_aw_ready})
  );

  /////////////////////////////////////
  // Spill register between AW and W //
  /////////////////////////////////////

  write_metadata_t w_metadata;
  logic            w_metadata_valid;
  logic            w_metadata_ready;

  cc_stream_spill_reg #(
    .data_t(write_metadata_t)
  ) u_write_metadata_buffer (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (aw_metadata),
    .i_valid(aw_metadata_valid),
    .o_ready(aw_metadata_ready),
    .o_data (w_metadata),
    .o_valid(w_metadata_valid),
    .i_ready(w_metadata_ready)
  );

  ///////////////////////////
  // Write data Management //
  ///////////////////////////
  logic              axi_w_transaction;
  axi_pkg::axi_len_t w_remaining_beats_q; // This runs backwards
  axi_strb_t         w_strb_of_first_beat_q;
  axi_strb_t         w_strb_of_last_beat_q;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)    begin
      w_strb_of_first_beat_q <= {AxiStrbWidth{1'b1}};
      w_strb_of_last_beat_q  <= {AxiStrbWidth{1'b1}};
    end else if (w_metadata_valid && w_metadata_ready) begin
      w_strb_of_first_beat_q <= {AxiStrbWidth{1'b1}} << w_metadata.num_inactive_strb_first;
      w_strb_of_last_beat_q  <= {AxiStrbWidth{1'b1}} >> w_metadata.num_inactive_strb_last;
    end
  end

  logic is_first_beat;
  logic is_last_beat;

  cc_cnt_delta #(
    .Width         (axi_pkg::AXI_LEN_WIDTH),
    .StickyOverflow(1'b0)
  ) u_w_beat_cnt (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (axi_w_transaction),
    .i_cnt_down(1'b1),
    .i_delta   (axi_pkg::axi_len_t'(1)),
    .o_q       (w_remaining_beats_q),
    .i_d       (w_metadata.axi_len),
    .i_d_load  (w_metadata_valid & w_metadata_ready),
    .o_overflow(/* not used */)
  );

  always_comb is_last_beat = w_remaining_beats_q == axi_pkg::axi_len_t'(0);

  typedef enum logic [1:0] {
    W_IDLE,
    W_FIRST,
    W_ACTIVE
  } w_state_e;
  w_state_e w_state_q, w_state_d;
  logic disconnect_axi_w;

  always_comb begin : proc_w_fsm
    w_state_d        = w_state_q;
    is_first_beat    = 1'b0;
    w_metadata_ready = 1'b0;
    disconnect_axi_w = 1'b0;
    unique case (w_state_q)
      W_IDLE: begin
        disconnect_axi_w = 1'b1;
        if (w_metadata_valid) begin
          w_metadata_ready = 1'b1;
          w_state_d        = W_FIRST;
        end
      end
      W_FIRST,
      W_ACTIVE: begin
        if (w_state_q == W_FIRST) is_first_beat = 1'b1;
        if (axi_w_transaction && is_last_beat) begin
          if (w_metadata_valid) begin
            w_metadata_ready = 1'b1;
            w_state_d        = W_FIRST;
          end else begin
            w_state_d = W_IDLE;
          end
        end else if (axi_w_transaction) begin
          w_state_d = W_ACTIVE;
        end
      end
      default: w_state_d = W_IDLE;
    endcase
  end

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) w_state_q <= W_IDLE;
    else          w_state_q <= w_state_d;
  end

  // Strobe calculation
  axi_strb_t w_strb;
  always_comb begin
    if (is_first_beat && is_last_beat) w_strb = w_strb_of_first_beat_q & w_strb_of_last_beat_q;
    else if (is_first_beat)            w_strb = w_strb_of_first_beat_q;
    else if (is_last_beat)             w_strb = w_strb_of_last_beat_q;
    else                               w_strb = {AxiStrbWidth{1'b1}};
  end

  // Output assignemnt
  axi_w_t axi_m_w;
  always_comb axi_m_w = '{
    data: i_patched_data,
    strb: w_strb,
    last: is_last_beat,
    default: '0
  };

  cc_stream_disconnect #(
    .data_t(axi_w_t)
  ) u_w_disconnect (
    .i_disconnect (disconnect_axi_w),
    .i_drop       (1'b0),
    .o_dropped    (/* not used */),
    .o_transaction(axi_w_transaction),
    .i_data       (axi_m_w),
    .i_valid      (i_patched_data_valid),
    .o_ready      (o_patched_data_ready),
    .o_data       (o_axi_m_w),
    .o_valid      (o_axi_m_w_valid),
    .i_ready      (i_axi_m_w_ready)
  );

  ////////////////
  // B Response //
  ////////////////

  cc_stream_spill_reg #(
    .data_t(aic_cd_pkg::task_list_word_length_t)
  ) u_response_metadata_buffer (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (b_metadata_q),
    .i_valid(b_metadata_valid),
    .o_ready(b_metadata_ready),
    .o_data (o_instruction_index),
    // Yes this intended, we are ready for B when the data here is valid
    .o_valid(o_axi_m_b_ready),
    .i_ready(i_axi_m_b_valid)
  );

  always_comb o_resp_slverr = i_axi_m_b_valid & (axi_pkg::axi_resp_e'(i_axi_m_b.resp) == axi_pkg::RespSlvErr);
  always_comb o_resp_decerr = i_axi_m_b_valid & (axi_pkg::axi_resp_e'(i_axi_m_b.resp) == axi_pkg::RespDecErr);

  ////////////
  // Status //
  ////////////
  always_comb o_busy =
      i_copy_command_valid
    | (aw_state_q == AW_ACTIVE)
    | w_metadata_valid
    | (w_state_q  == W_ACTIVE)
    | o_axi_m_b_ready;

endmodule
