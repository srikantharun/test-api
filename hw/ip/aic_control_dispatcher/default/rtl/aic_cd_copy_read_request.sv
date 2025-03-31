// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// This converts a copy request into a not quite compliant AXI request
///
/// Takes in a copy command and splits it up onto AXI-like requests.  These will then be alignes to
/// be protocol conform by further downstream units.
///
/// ![AIC_CD_COPY_READ_REQUEST: Block Diagram](figures/aic_cd_copy_read_request.drawio.svg)
///
/// The module contains a simple FSM, a counter and AXI AR register.  When a command arrives the state is set and the
/// module goes into a busy mode where it is not accepting ancy new commands. The request is broken up such that it
/// fits's into an `axi_m_ar_t` vector.  This happens without taking into account correct AXI transfer forming.  It is
/// expected that this request will be further broken down before going onto the AXI manager port.  Each time such an
/// AXI-like request leaves the module the counter and address are updated.
///
/// As the `length` value of the command is wider than the respective `AXI.AR.LEN` field, the unit needs to break it up.
/// The first request will only contain a length which will cause all consecutive requests for the same command to utilize
/// the maxumim `AXI.AR.LEN` value of all `'1`. This way the counter only needs to keep track of how many additional
/// full length requests need to be sent out.
///
module aic_cd_copy_read_request #(
  /// The Axi ID width of the AXI AR channel
  parameter int unsigned AxiIdWidth = aic_cd_defaults_pkg::AXI_M_ID_WIDTH,
  /// The Concrete AXI ID to use
  parameter logic [AxiIdWidth-1:0] AxiIdForCopy = aic_cd_defaults_pkg::AXI_M_ID_WIDTH'(0),
  /// The Address width of the AXI AR channel
  parameter int unsigned AxiAddrWidth = aic_cd_defaults_pkg::AXI_M_ADDR_WIDTH,
  /// AXI AR channel type
  parameter type axi_ar_t = aic_cd_defaults_pkg::axi_m_ar_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ////////////
  // Status //
  ////////////
  /// The unit is busy
  output logic o_busy,

  //////////////////
  // Copy Request //
  //////////////////
  /// The copy command
  input  aic_cd_pkg::copy_command_t i_copy_command,
  /// The copy command is valid
  input  logic                      i_copy_command_valid,
  /// Dowstream consumes copy command
  output logic                      o_copy_command_ready,

  ///////////////////////////////////////////////////////////////////
  // AXI Request AR Port                                           //
  // Not manager, as it does not completely adhere to AXI protocol //
  ///////////////////////////////////////////////////////////////////
  /// The AR channel payload
  output axi_ar_t o_request_ar,
  /// The AR channel is valid
  output logic    o_request_ar_valid,
  /// The AR channel is ready
  input  logic    i_request_ar_ready
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  typedef logic [AxiAddrWidth-1:0] axi_addr_t;
  if (AxiAddrWidth != $bits(o_request_ar.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' must match 'o_request_ar.addr';");

  localparam int unsigned CounterWidth = aic_cd_pkg::CopyMaxNumWordsLength - axi_pkg::AXI_LEN_WIDTH;
  typedef logic [CounterWidth-1:0] count_t;

  ///////////////////////////
  // Flags for handshaking //
  ///////////////////////////
  logic       command_transaction;
  logic       request_transaction;
  always_comb command_transaction = i_copy_command_valid & o_copy_command_ready;
  always_comb request_transaction = o_request_ar_valid   & i_request_ar_ready;

  ///////////////////////////////////////////
  // Convert the copylength int AXI format //
  ///////////////////////////////////////////
  aic_cd_pkg::copy_num_words_t copy_length_in_axi_format;
  always_comb copy_length_in_axi_format = i_copy_command.num_words - aic_cd_pkg::copy_num_words_t'(1);

  /////////////////////////////////////////////////
  // Count of how many large requests we've done //
  /////////////////////////////////////////////////
  logic   counter_enable;
  logic   counter_load;
  count_t counter_value_q;

  cc_cnt_delta #(
    .Width         (CounterWidth),
    .StickyOverflow(1'b0)
  ) u_axe_ccl_cnt_delta (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (counter_enable),
    .i_cnt_down(1'b1),
    .i_delta   (count_t'(1)),
    .o_q       (counter_value_q),
    .i_d       (copy_length_in_axi_format[axi_pkg::AXI_LEN_WIDTH+:CounterWidth]), // Upper bits
    .i_d_load  (counter_load),
    .o_overflow(/*not used*/)
  );

  /////////////////////////
  // Control the request //
  /////////////////////////
  axi_ar_t request_ar_d;
  logic    request_ar_update;
  localparam axi_ar_t RequestDefaults = axi_ar_t'{
    id:    AxiIdForCopy,
    size:  axi_pkg::Bytes008,
    burst: axi_pkg::BurstIncr,
    /*
    cache:   Uses Default,
    prot:    Uses Default,
    */
    default: 0
  };

  typedef enum logic {
    IDLE,
    BUSY
  } state_e;
  state_e state_q, state_d;
  logic   change_state;

  always_comb begin : proc_control
    state_d      = state_q;
    change_state = 1'b0;

    request_ar_d       = o_request_ar;
    request_ar_update  = 1'b0;

    o_request_ar_valid   = 1'b0;
    o_copy_command_ready = 1'b0;

    counter_enable = 1'b0;
    counter_load   = 1'b0;

    unique case (state_q)
      IDLE: begin
        o_copy_command_ready = 1'b1;
        if (command_transaction) begin
          state_d      = BUSY;
          change_state = 1'b1;

          request_ar_d.addr = i_copy_command.addr_source;
          request_ar_d.len  = copy_length_in_axi_format[0+:axi_pkg::AXI_LEN_WIDTH];
          request_ar_update = 1'b1;
          counter_load      = 1'b1;
        end
      end
      BUSY: begin
        o_request_ar_valid = 1'b1;

        request_ar_d.addr =
            axi_addr_t'(axi_pkg::axi_aligned_addr(axi_pkg::axi_largest_addr_t'(o_request_ar.addr), o_request_ar.size))
          + axi_addr_t'(axi_pkg::axi_num_bytes(o_request_ar.size) * (o_request_ar.len + 1));

        request_ar_d.len  = {axi_pkg::AXI_LEN_WIDTH{1'b1}};

        if (request_transaction) begin
          if (counter_value_q == count_t'(0)) begin
            // This was the last request
            state_d      = IDLE;
            change_state = 1'b1;
          end else begin
            request_ar_update = 1'b1;
            counter_enable    = 1'b1;
          end
        end
      end
      default: begin
        state_d      = IDLE;
        change_state = 1'b1;
      end
    endcase
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)               o_request_ar <= RequestDefaults;
    else if (request_ar_update) o_request_ar <= request_ar_d;
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)          state_q <= IDLE;
    else if (change_state) state_q <= state_d;
  end

  ////////////
  // Status //
  ////////////
  always_comb o_busy = i_copy_command_valid | (state_q == BUSY);
endmodule
