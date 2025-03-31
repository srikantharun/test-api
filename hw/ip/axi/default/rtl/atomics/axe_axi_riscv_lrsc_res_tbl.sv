// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Derived from: https://github.com/pulp-platform/axi_riscv_atomics/blob/master/src/axi_res_tbl.sv
// Original Authors:
//   - Samuel Riedel <sriedel@iis.ee.ethz.ch>
//   - Andreas Kurth <akurth@iis.ee.ethz.ch>


/// AXI Reservation Table
///
module axe_axi_riscv_lrsc_res_tbl #(
  /// The width of the AXI ID field
  ///
  /// Note: This width determines the amount of counters instantiated which will be: `2**AxiIdWidth`!
  parameter int unsigned AxiIdWidth   = 0,
  /// The width of the AXI Addr field
  parameter int unsigned AxiAddrWidth = 0,
  /// The number of table Entries
  parameter int unsigned NumEntries   = 2**AxiIdWidth
)(
  /// Clock , positive edge triggered
  input  wire                     i_clk,
  /// Asynchronous reset, active low
  input  wire                     i_rst_n,
  input  logic [AxiAddrWidth-1:0] i_check_clear_addr,
  input  logic [AxiIdWidth  -1:0] i_check_id,
  input  logic                    i_check_clear_excl,
  output logic                    o_check_res,
  input  logic                    i_check_clear_req,
  output logic                    o_check_clear_gnt,
  input  logic [AxiAddrWidth-1:0] i_set_addr,
  input  logic [AxiIdWidth  -1:0] i_set_id,
  input  logic                    i_set_req,
  output logic                    o_set_gnt
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (AxiIdWidth   == 0)             $fatal(1, "Parameter: 'AxiIdWidth' must be greater than 0!;");
  if (AxiAddrWidth == 0)             $fatal(1, "Parameter: 'AxiAddrWidth' must be greater than 0!;");
  if (NumEntries   == 0)             $fatal(1, "Parameter: 'NumEntries' must be greater than 0!;");
  if (NumEntries    > 2**AxiIdWidth) $fatal(1, "Parameter: 'NumEntries' must not be greater than `2**AxiIdWidth`!;");

  localparam int unsigned EntryIdxWidth = cc_math_pkg::index_width(NumEntries);
  typedef logic [EntryIdxWidth-1:0] entry_idx_t;

  typedef struct packed {
    /// The table entry is valid
    logic                    valid;
    /// The transaction ID the address belongs to
    logic [AxiIdWidth  -1:0] id;
    /// The saved exclusive address that is accessed
    logic [AxiAddrWidth-1:0] address;
  } table_entry_t;

  /////////////////////////////////
  // The actual table to be used //
  /////////////////////////////////
  table_entry_t                  table_q[NumEntries];
  logic         [NumEntries-1:0] entry_clear;
  logic         [NumEntries-1:0] entry_set;

  ///////////////////////////////////////
  // Determine free space in the table //
  ///////////////////////////////////////

  logic [NumEntries-1:0] entry_is_free;
  entry_idx_t            next_free_entry;
  logic                  all_entries_used;

  always_comb begin
    for (int unsigned entry_idx = 0; entry_idx < NumEntries; entry_idx++) begin
      entry_is_free[entry_idx] = ~table_q[entry_idx].valid;
    end
  end

  lzc #(
    .WIDTH(NumEntries),
    .MODE (1'b0)
  ) u_lzc_find_free_entry (
    .in_i   (entry_is_free),
    .cnt_o  (next_free_entry),
    .empty_o(all_entries_used)
  );

  ////////////////////////////////////////
  // Look up if an entry is already set //
  ////////////////////////////////////////
  logic [NumEntries-1:0] set_id_match;
  always_comb begin
    for (int unsigned entry_idx = 0; entry_idx < NumEntries; entry_idx++) begin
      set_id_match[entry_idx] = table_q[entry_idx].valid && (table_q[entry_idx].id == i_set_id);
    end
  end

  //////////////////////////////////
  // Determine if we have a match //
  //////////////////////////////////

  logic [NumEntries-1:0] check_matches;
  logic [NumEntries-1:0] id_match;

  // Table-Managing Logic
  always_comb begin
    for (int unsigned entry_idx = 0; entry_idx < NumEntries; entry_idx++) begin
      check_matches[entry_idx] =
            table_q[entry_idx].valid
         & (table_q[entry_idx].address == i_check_clear_addr);
    end
  end

  always_comb begin
    for (int unsigned entry_idx = 0; entry_idx < NumEntries; entry_idx++) begin
      id_match[entry_idx] =
           check_matches[entry_idx]
        & (table_q[entry_idx].id == i_check_id);
    end
  end


  always_comb begin
    entry_clear       = '0;
    entry_set         = '0;
    o_set_gnt         = 1'b0;
    o_check_res       = 1'b0;
    o_check_clear_gnt = 1'b0;

    if (i_check_clear_req) begin
      o_check_clear_gnt = 1'b1;
      o_check_res       = |id_match;
      entry_clear       = (~i_check_clear_excl | (|id_match)) ? check_matches : '0;
    end else if (i_set_req) begin
      if (|set_id_match) begin
        entry_set = set_id_match;
        o_set_gnt = 1'b1;
      end else if (!all_entries_used) begin
        entry_set[next_free_entry] = 1'b1;
        o_set_gnt                  = 1'b1;
      end
    end
  end

  // Registers
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) begin
      foreach (table_q[entry_idx]) table_q[entry_idx] <= table_entry_t'(0);
    end else begin
      foreach (table_q[entry_idx]) begin
        if (entry_clear[entry_idx])    table_q[entry_idx].valid <= 1'b0;
        else if (entry_set[entry_idx]) table_q[entry_idx]       <= table_entry_t'{
          valid:   1'b1,
          id:      i_set_id,
          address: i_set_addr
        };
      end
    end
  end

  ////////////////
  // Assertions //
  ////////////////
  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON

  property p_signal_must_be_onehot0(onehot_signal);
    @(posedge i_clk)
    disable iff (!i_rst_n)
    $onehot0(onehot_signal)
  endproperty : p_signal_must_be_onehot0

  check_set_id_match_must_be_onehot0 : assert property (p_signal_must_be_onehot0(set_id_match)) else $error("Only one set ID is allowed to match at a time.");
  check_entry_set_must_be_onehot0 :    assert property (p_signal_must_be_onehot0(entry_set))    else $error("Only one entry is allowed to be set at a time.");
  check_id_match_must_be_onehot :      assert property (p_signal_must_be_onehot0(id_match))     else $error("More than one check ID matched.");

  `endif
  `endif

endmodule
