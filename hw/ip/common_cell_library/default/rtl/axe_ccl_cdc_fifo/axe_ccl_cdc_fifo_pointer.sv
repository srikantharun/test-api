// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner:
// - Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
// - Spyridoula Koumousi <spyridoula.koumousi@axelera.ai>

/// Write and read pointer calculation for `axe_ccl_cdc_fifo`.
///
/// Supports both calculating the current write and read pointers.
/// All logic in this module inherently is synchronous to the respective domain, so all inputs and
/// outputs have to be synchronized to the port `i_clk`.
///
module axe_ccl_cdc_fifo_pointer #(
  /// The pointer calculation mode.
  ///
  /// - `0`: Write pointer calculation. `o_flag` is the full flag.
  /// - `1`: Read pointer calculation. `o_flag` is the empty flag.
  parameter bit          Mode = 1'b0,
  /// Depth of the instantiated FIFO.
  ///
  /// This value has to be even. (`Depth % 2 != 0`)
  parameter int unsigned Depth = 6,
  /// The address width to access the data.
  ///
  localparam int unsigned AddrWidth = cc_math_pkg::index_width(Depth)
)(
  /// Clock, positive edge triggered
  input  wire  i_clk,
  /// Asynchronous reset, active low
  input  wire  i_rst_n,
  /// Synchronously flush pointer (should be controlled by `axe_ccl_cdc_reset_control`)
  input  logic i_flush,
  /// When this is `1` an update is initiated.
  ///
  /// - `Mode == 0`: Write request, push to the FIFO.
  /// - `Mode == 1`: Read reaquest, pop from the FIFO.
  ///
  /// Only assert when `o_flag == 0`!
  input  logic i_update,
  /// The graycoded pointer from the other domain.
  /// This vlaue has to be synchronized to `clk_i`.
  input  logic [AddrWidth:0] i_gray_pointer,
  /// Status flag.
  /// When this is one a pointer condiditon occurs, depending on the parameter `PtrMode`:
  ///
  /// - `Mode == 0`: The FIFO is full.
  /// - `Mode == 1`: The FIFO es empty.
  output logic o_flag,
  /// Data access address.
  ///
  /// * `Mode == 0`: Write data address.
  /// * `Mode == 1`:  Read data address.
  output logic [AddrWidth-1:0] o_address,
  /// The graycoded pointer to the other domain.
  /// This signal has to be synchronized to the other domain..
  output logic [AddrWidth:0] o_gray_pointer
);
  ///////////////////////////////
  // Parameters and Validation //
  ///////////////////////////////
  if (Depth == 0) $fatal(1, "Parameter: 'Depth (%d)' must not be 0.", Depth);
  if (Depth % 2 != 0) $fatal(1, "Parameter: 'Depth (%d)' must be even.", Depth);

  /// Pointer data type
  typedef logic [AddrWidth:0] pointer_t;

  localparam pointer_t ResetIdxBin  = pointer_t'(axe_ccl_cdc_pkg::get_rst_bin_index(Depth));
  localparam pointer_t ResetIdxGray = pointer_t'(axe_ccl_cdc_pkg::bin_to_gray(32'(ResetIdxBin)));
  localparam pointer_t LowerIndex   = pointer_t'(32'(ResetIdxBin) + Depth - 1);
  localparam pointer_t JumpIndex    = pointer_t'(32'(ResetIdxBin) + (1 << AddrWidth));
  localparam pointer_t UpperIndex   = pointer_t'(32'(JumpIndex)   + Depth - 1);

  /////////////////////
  // Flops and Flags //
  /////////////////////
  pointer_t pointer_gray_d;

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n)      o_gray_pointer <= ResetIdxGray;
    else if (i_flush)  o_gray_pointer <= ResetIdxGray;
    else if (i_update) o_gray_pointer <= pointer_gray_d;
  end

  //////////////////////////////////////////////
  // Pointer Advance in Binary Representation //
  //////////////////////////////////////////////
  pointer_t pointer_bin_current;
  pointer_t pointer_bin_next;

  axe_ccl_decode_gray #(
    .Mode  (1),
    .data_t(pointer_t)
  ) u_gray_to_bin (
    .i_data(o_gray_pointer),
    .o_data(pointer_bin_current)
  );

  axe_ccl_decode_gray #(
    .Mode  (0),
    .data_t(pointer_t)
  ) u_bin_to_gray (
    .i_data(pointer_bin_next),
    .o_data(pointer_gray_d)
  );

  always_comb begin : calc_next_pointer
    unique case (pointer_bin_current)
      LowerIndex: pointer_bin_next = JumpIndex;
      UpperIndex: pointer_bin_next = ResetIdxBin;
      default:    pointer_bin_next = pointer_bin_current + pointer_t'(1);
    endcase
  end

  //////////////////////////////
  // Data Address Calculation //
  //////////////////////////////
  always_comb o_address = AddrWidth'(pointer_bin_current - ResetIdxBin);

  //////////////////////////////
  // Full / Empty Calculation //
  //////////////////////////////
  case (Mode)
    1'b0: begin : gen_flag_full
      always_comb o_flag = (o_gray_pointer == { ~i_gray_pointer[AddrWidth:AddrWidth-1], i_gray_pointer[AddrWidth-2:0] });
    end
    1'b1: begin : gen_flag_empty
      always_comb o_flag = (o_gray_pointer == i_gray_pointer);
    end
  endcase

  ////////////////
  // Assertions //
  ////////////////
  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON

  property p_pointer_is_gray_coded;
    disable iff (!i_rst_n)
    @(posedge i_clk)
    $changed(o_gray_pointer) |-> $onehot(o_gray_pointer ^ $past(o_gray_pointer));
  endproperty : p_pointer_is_gray_coded
  check_p_pointer_is_gray_coded : assert property (p_pointer_is_gray_coded);

  property p_address_is_in_range;
    @(posedge i_clk)
    (o_address < AddrWidth'(Depth));
  endproperty : p_address_is_in_range
  check_p_address_is_in_range : assert property (p_address_is_in_range);

  property p_binary_pointer_value_reset;
    @(posedge i_clk)
    (!i_rst_n) |-> (pointer_bin_current == ResetIdxBin);
  endproperty : p_binary_pointer_value_reset
  check_p_binary_pointer_value_reset : assert property (p_binary_pointer_value_reset);

  // Mode is chosen such that it matches the reset condiditon of the respective flag.
  property p_mode_appropriate_flag_reset;
    @(posedge i_clk)
    (!i_rst_n) |-> (o_flag == Mode);
  endproperty : p_mode_appropriate_flag_reset
  check_p_mode_appropriate_flag_reset : assert property (p_mode_appropriate_flag_reset);

  `endif
  `endif
endmodule
