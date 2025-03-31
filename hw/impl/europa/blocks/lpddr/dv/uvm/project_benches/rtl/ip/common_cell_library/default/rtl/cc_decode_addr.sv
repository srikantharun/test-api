// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Dynamically configurable address decoder
///
module cc_decode_addr #(
  /// Number of address rules
  parameter int unsigned NumRules = 0,
  /// The index type for the output port
  parameter type index_t = cc_lib_pkg::index_4_t,
  /// The address type for the input port
  parameter type addr_t = cc_lib_pkg::addr_40_t,
  /// Rule packed struct type.
  /// The address decoder expects three fields in `rule_t`:
  ///
  /// typedef struct packed {
  ///   index_t index;
  ///   addr_t  addr_start;
  ///   addr_t  addr_end;
  /// } rule_t;
  ///
  ///  - `idx`:        index of the rule, has to be < `NoIndices`
  ///  - `start_addr`: start address of the range the rule describes, value is included in range
  ///  - `end_addr`:   end address of the range the rule describes, value is NOT included in range
  ///                  if `end_addr == '0` end of address space is assumed
  ///
  /// The fields widths are asserted at elaboration time
  parameter type rule_t = cc_lib_pkg::default_addr_rule_t
)(
  /// Address to decode
  input  addr_t  i_address,
  /// Address map: matching rule with the lowest array index has priority
  input  rule_t  i_address_map[NumRules],
  /// Decoded index when a rule matched
  output index_t o_index,
  /// Decode is valid
  output logic   o_decode_valid,
  /// Decode is not valid, no matching rule found
  output logic   o_decode_error,
  /// Enable default port mapping.
  ///
  /// When not used, tie to `0`.
  input  logic   i_default_index_en,
  /// Default port index
  input  index_t i_default_index,
  /// Assert when the address mas is being reconfigured. No rule will match
  input  logic   i_config_ongoing
);
  //////////////////////////
  // Parameter sanitation //
  //////////////////////////
  if (NumRules == 0) $fatal(1, "Parameter: 'NumRules' has to be larger than 0; is: %d", NumRules);

  if ($bits(addr_t) != $bits(i_address_map[0].addr_start))
      $fatal(1, "Parameter: '$bits(addr_t)' unequal $bits(rule_t.addr_start); is: %d and %d",
      $bits(addr_t), $bits(i_address_map[0].addr_start));

  if ($bits(addr_t) != $bits(i_address_map[0].addr_end))
      $fatal(1, "Parameter: '$bits(addr_t)' unequal $bits(rule_t.addr_start); is: %d and %d",
      $bits(addr_t), $bits(i_address_map[0].addr_end));

  if ($bits(index_t) < $bits(i_address_map[0].index))
      $fatal(1, "Parameter: '$bits(index_t)' not able to represent $bits(rule_t.index); is: %d and %d",
      $bits(index_t), $bits(i_address_map[0].index));

  localparam int unsigned MatchIndexWidth = cc_math_pkg::index_width(NumRules);
  typedef logic [MatchIndexWidth-1:0] match_index_t;

  logic [NumRules-1:0] matched_rules;
  match_index_t        matched_index;
  logic                no_rule_matched;

  for (genvar rule_idx = 0; unsigned'(rule_idx) < NumRules; rule_idx++) begin : gen_matches
    assign matched_rules[rule_idx] =
          (i_address >= i_address_map[rule_idx].addr_start)
       && (
             (i_address < i_address_map[rule_idx].addr_end)
          || (i_address_map[rule_idx].addr_end == addr_t'(0))
          );
  end

  // TODO(@wolfgang.roenninger): replace with updated leading zero counter
  lzc #(
    .WIDTH (NumRules),
    // Mode selection: 0 -> trailing zero, 1 -> leading zero
    .MODE  (1'b0)
  ) u_lzc (
  /// Input vector to be counted.
    .in_i   (matched_rules),
    .cnt_o  (matched_index),
    .empty_o(no_rule_matched)
  );

  // Output calculation
  always_comb begin
    o_index        = i_default_index_en ? i_default_index : index_t'(0);
    o_decode_valid = 1'b0;
    o_decode_error = 1'b0;

    if (!i_config_ongoing) begin
      if (no_rule_matched) begin
        o_decode_error = ~i_default_index_en;
      end else begin
        o_decode_valid = 1'b1;
        o_index        = index_t'(i_address_map[matched_index].index);
      end
    end
  end
endmodule
