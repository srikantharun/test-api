// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Request data on the AXI read channel, buffer response data.
///
/// This units only purpose it to take AXI-like `AR` requests and transform them to `AXI4` compliant transactions.
/// It contains buffer space for the requested data in form of a FIFO.  Via the parameterization one can choose if
/// this buffer is implemented with Flip-Flops or with a memory.  The unit makes sure that it will only request an amount
/// of data which it has space for in the buffer.
///
///
/// !!! note "AXI-like in Context of the AIC_CD"
///
///     With `AXI-like` we refer to `AXI4 A[R|W]` vectors which already conform to the respective bus vector
///     parameterization, however are breaking the specification in some way.  This might be crossing a 4K boundary
///     or requesting too much data.
///
///
/// ![AIC_CD_AXI_READ: Block Diagram](./figures/aic_cd_axi_read.drawio.svg)
///
///
/// The `AXI Read Unit` is used for both the [Instruction Fetch](instruction_fetch/index.md) as well as the
/// [Copy Unit](copy_unit/index.md) read request forming.
///
///
/// The processing of an `AXI.AR-like` request is done as follows:
///
/// 1. Load the `axi_ar_q` register and jump into the busy state.
/// 2. In busy, signal to the bus that the handshaking is valid.
///     - Makes sure valid is only signaled if the sum of the current requestes outstanding `AXI.R` beats and buffered
///       responses does not exceed the free space the next transaction would occupy.
///     - Here the output `axi.ar.len` is reduced to either `0` if the next preferred transaction would cross the `4K`
///       boundary, or the preffered length which can be changed via a parameter.
/// 3. On handshake update the respective next `axi_ar_d` according to the values that are set on the port.
/// 4. If the last transfer, either load a new request if present, or jump back to idle.
///
///
/// !!! note "Busy State"
///
///     This unit is considered `busy` when:
///     - A new request is valid.
///     - The unit is in the `BUSY` state.
///     - There are `AXI.R` beats outstanding.
///     - There is data present in the response FIFO.
///
module aic_cd_axi_read #(
  /// The Address width of the AXI AR channel
  parameter int unsigned AxiAddrWidth = aic_cd_defaults_pkg::AXI_M_ADDR_WIDTH,
  /// The depth of the read data buffer.
  parameter int unsigned ReadBufferDepth = 0,
  /// The buffer usage pointer width
  localparam int unsigned UsageWidth = cc_math_pkg::index_width(ReadBufferDepth) + 1,
  /// The usage type of the buffer
  localparam type usage_t = logic[UsageWidth-1:0],
  /// The maximum length of a sigular AR that is allowed to be emitted.
  /// Followes the same encoding as AXI `ar.len`, so a 0 corresponds to 1 `R` transaction!
  parameter axi_pkg::axi_len_t MaxArLen = axi_pkg::axi_len_t'(ReadBufferDepth/2)-1,

  /// The AXI AR channel type
  parameter type axi_ar_t = aic_cd_defaults_pkg::axi_m_ar_t,
  /// The AXI R channel type
  parameter type axi_r_t = aic_cd_defaults_pkg::axi_m_r_t,

  /// Use a memory for the buffer
  parameter bit BufferUsesMacro = 1'b1,
  /// Memory Implementation Key
  parameter MemImplKey = "default",
  /// Sideband input signal type to tc_sram
  parameter type ram_impl_inp_t = axe_tcl_sram_pkg::impl_inp_t,
  /// Sideband output signal type from ts_sram
  parameter type ram_impl_oup_t = axe_tcl_sram_pkg::impl_oup_t
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,

  ////////////
  // Status //
  ////////////
  /// There are outstanding requests going on
  output logic   o_busy,
  /// Usage pointer of the data buffer
  output usage_t o_num_data_buffered,

  /////////////////////
  // Request AR Port //
  /////////////////////
  /// The AR channel payload
  input  axi_ar_t i_request_ar,
  /// The AR channel payload
  input  logic    i_request_ar_valid,
  /// The AR channel payload
  output logic    o_request_ar_ready,

  /////////////////////
  // Manager AR Port //
  /////////////////////
  /// The AR channel payload
  output axi_ar_t o_axi_m_ar,
  /// The AR channel payload
  output logic    o_axi_m_ar_valid,
  /// The AR channel payload
  input  logic    i_axi_m_ar_ready,
  /// The AR channel payload
  input  axi_r_t  i_axi_m_r,
  /// The AR channel payload
  input  logic    i_axi_m_r_valid,
  /// The AR channel payload
  output logic    o_axi_m_r_ready,

  /////////////////////
  // Response R Port //
  /////////////////////
  /// The AR channel payload
  output axi_r_t  o_response_r,
  /// The AR channel payload
  output logic    o_response_r_valid,
  /// The AR channel payload
  input  logic    i_response_r_ready,

  /////////////////////////////
  // Memory Sideband Signals //
  /////////////////////////////
  /// Memory sideband input signals (tie to `'0` if `BufferUsesMacro == 1'b0`)
  input  ram_impl_inp_t i_ram_impl,
  /// Memory sideband output signals
  output ram_impl_oup_t o_ram_impl
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////

  if (ReadBufferDepth == 0) $fatal(1, "Parameter: 'ReadBufferDepth' Must be at least 1;");
  if (ReadBufferDepth >= (2**axi_pkg::AXI_LEN_WIDTH) * 2) $fatal(1, "Parameter: 'ReadBufferDepth' maximum size exceeded; is: %d", ReadBufferDepth);

  if (MaxArLen + 1 > ReadBufferDepth) $fatal(1, "Parameter: 'MaxArLen + 1' is not allowed to exceed 'ReadBufferDepth'");

  if (AxiAddrWidth != $bits(o_axi_m_ar.addr)) $fatal(1, "Parameter: 'AxiAddrWidth' must match type in `axi_ar_t`");
  typedef logic [AxiAddrWidth-1:0] axi_addr_t;

  ///////////////////////////////
  // Flags for relevant Events //
  ///////////////////////////////
  logic axi_request_transaction_ar;
  logic axi_manager_transaction_ar;
  logic axi_manager_transaction_r;

  always_comb axi_request_transaction_ar = i_request_ar_valid & o_request_ar_ready;
  always_comb axi_manager_transaction_ar = o_axi_m_ar_valid   & i_axi_m_ar_ready;
  always_comb axi_manager_transaction_r  = i_axi_m_r_valid    & o_axi_m_r_ready;

  /////////////////////////
  // Outstanding Counter //
  /////////////////////////
  usage_t num_data_outstanding;
  usage_t outstanding_delta;
  logic   outstanding_enable;
  logic   outstanding_decrement;

  always_comb outstanding_enable    =  axi_manager_transaction_ar | axi_manager_transaction_r;
  always_comb outstanding_decrement = ~axi_manager_transaction_ar & axi_manager_transaction_r;

  always_comb begin
    unique case ({axi_manager_transaction_ar, axi_manager_transaction_r})
      2'b01:   outstanding_delta = usage_t'(1);                            // We remove one from the outstanding count
      2'b10:   outstanding_delta = usage_t'(o_axi_m_ar.len) + usage_t'(1); // Just increment with the expected number of items
      2'b11:   outstanding_delta = usage_t'(o_axi_m_ar.len);               // We count in the read in the delta
      default: outstanding_delta = usage_t'(0);                            // Do nothing
    endcase
  end

  cc_cnt_delta #(
    .Width         (UsageWidth),
    .StickyOverflow(1'b0)
  ) u_counter_outstanding (
    .i_clk,
    .i_rst_n,
    .i_flush   (1'b0),
    .i_cnt_en  (outstanding_enable),
    .i_cnt_down(outstanding_decrement),
    .i_delta   (outstanding_delta),
    .o_q       (num_data_outstanding),
    .i_d       (usage_t'(0)),
    .i_d_load  (1'b0),
    .o_overflow(/* not used */)
  );

  //////////////////////////
  // Response Data Buffer //
  //////////////////////////
  if (BufferUsesMacro) begin : gen_buffer_macro
    axe_ccl_stream_fifo_mem #(
      .Depth         (ReadBufferDepth),
      .data_t        (axi_r_t),
      .MemImplKey    (MemImplKey),
      .ram_impl_inp_t(ram_impl_inp_t),
      .ram_impl_oup_t(ram_impl_oup_t)
    ) u_response_buffer (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (i_axi_m_r),
      .i_valid(i_axi_m_r_valid),
      .o_ready(o_axi_m_r_ready),
      .o_data (o_response_r),
      .o_valid(o_response_r_valid),
      .i_ready(i_response_r_ready),
      .o_usage(o_num_data_buffered),
      .o_full (/* not used */),
      .o_empty(/* not used */),
      .i_ram_impl,
      .o_ram_impl
    );
  end else begin : gen_buffer_flops
    cc_stream_fifo #(
      .Depth      (ReadBufferDepth),
      .data_t     (axi_r_t),
      .FallThrough(1'b0)
    ) u_response_buffer (
      .i_clk,
      .i_rst_n,
      .i_flush(1'b0),
      .i_data (i_axi_m_r),
      .i_valid(i_axi_m_r_valid),
      .o_ready(o_axi_m_r_ready),
      .o_data (o_response_r),
      .o_valid(o_response_r_valid),
      .i_ready(i_response_r_ready),
      .o_usage(o_num_data_buffered),
      .o_full (/* not used */),
      .o_empty(/* not used */)
    );
    always_comb o_ram_impl = '0;
  end

  //////////////////////////////////////////
  // Manage the request on the AR Channel //
  //////////////////////////////////////////
  // Save a description of the AR we use to operate on.
  axi_ar_t axi_ar_q, axi_ar_d;
  logic    axi_ar_load;

  // DFFRL: D-Flip-Flop, asynchronous reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)         axi_ar_q <= '0;
    else if (axi_ar_load) axi_ar_q <= axi_ar_d;
  end

  // Are we at all allowed
  usage_t     num_free_outstanding;
  always_comb num_free_outstanding = usage_t'(ReadBufferDepth) - (num_data_outstanding + o_num_data_buffered);
  logic       new_ar_request_allowed;
  always_comb new_ar_request_allowed = num_free_outstanding > usage_t'(MaxArLen);

  // We have a preference of the next len value
  axi_pkg::axi_len_t preferred_ar_len;
  always_comb        preferred_ar_len = (axi_ar_q.len > MaxArLen) ? MaxArLen : axi_ar_q.len;

  // Determine if we would cross the 4Kb boundary
  logic       preferred_crosses_4kb_boundary;
  always_comb preferred_crosses_4kb_boundary = axi_pkg::axi_burst_crosses_4kb_boundary(
    .addr (axi_pkg::axi_largest_addr_t'(axi_ar_q.addr)),
    .size (axi_ar_q.size),
    .len  (preferred_ar_len),
    .burst(axi_ar_q.burst)
  );

  always_comb begin
    o_axi_m_ar = axi_ar_q;
    // We take a conservative approach
    // Take small steps to the boundary until we cross it
    if (preferred_crosses_4kb_boundary) o_axi_m_ar.len = axi_pkg::axi_len_t'(0);
    else                                o_axi_m_ar.len = preferred_ar_len;
  end

  // Is this the last AR we want to transfer?
  logic       axi_ar_last;
  always_comb axi_ar_last = o_axi_m_ar_valid & (o_axi_m_ar.len == axi_ar_q.len);

  /////////
  // FSM //
  /////////
  typedef enum logic {
    IDLE,
    BUSY
  } state_e;
  state_e state_q, state_d;

  always_comb begin
    state_d     = state_q;
    axi_ar_d    = axi_ar_q;
    axi_ar_load = 1'b0;

    o_request_ar_ready = 1'b0;
    o_axi_m_ar_valid   = 1'b0;

    unique case (state_q)
      IDLE: begin
        if (i_request_ar_valid) begin
          axi_ar_d           = i_request_ar;
          axi_ar_load        = 1'b1;
          o_request_ar_ready = 1'b1;
          state_d            = BUSY;
        end
      end
      BUSY: begin
        o_axi_m_ar_valid = new_ar_request_allowed;

        // On transaction
        if (axi_manager_transaction_ar) begin
          // Update our request
          axi_ar_load = 1'b1;
          if (axi_ar_last) begin
            // This is the last request
            if (i_request_ar_valid) begin
              // We have a new one!
              axi_ar_d           = i_request_ar;
              o_request_ar_ready = 1'b1;
            end else begin
              // Go to idle again
              axi_ar_d = '0;
              state_d  = IDLE;
            end
          end else begin
            // Update remaining for the next request
            axi_ar_d.addr = AxiAddrWidth'(axi_pkg::axi_beat_addr(
              .addr  (axi_pkg::axi_largest_addr_t'(o_axi_m_ar.addr)),
              .size  (o_axi_m_ar.size),
              .len   (o_axi_m_ar.len),
              .burst (o_axi_m_ar.burst),
              .i_beat(o_axi_m_ar.len + axi_pkg::axi_len_t'(1))
            ));
            axi_ar_d.len = axi_ar_q.len - (o_axi_m_ar.len + axi_pkg::axi_len_t'(1));
          end
        end
      end
      default: state_d = IDLE;
    endcase
  end

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) state_q <= IDLE;
    else          state_q <= state_d;
  end

  /////////////////////
  // Busy indication //
  /////////////////////
  always_comb o_busy =
      i_request_ar_valid
    | (state_q == BUSY)
    | (|num_data_outstanding)
    | (|o_num_data_buffered);

endmodule
