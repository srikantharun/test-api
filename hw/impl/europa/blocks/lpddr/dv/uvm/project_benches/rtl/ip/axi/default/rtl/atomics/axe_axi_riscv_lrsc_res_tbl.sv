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
/// TODO(@wolfgang.roenninger): Refactor to use a parameter NumEntries to not scale quadratically
///
module axe_axi_riscv_lrsc_res_tbl #(
  /// The width of the AXI ID field
  ///
  /// Note: This width determines the amount of counters instantiated which will be: `2**AxiIdWidth`!
  parameter int unsigned AxiIdWidth   = 0,
  /// The width of the AXI Addr field
  parameter int unsigned AxiAddrWidth = 0
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
  if (AxiIdWidth   == 0) $fatal(1, "Parameter: 'AxiIdWidth' must be greater than 0!;");
  if (AxiAddrWidth == 0) $fatal(1, "Parameter: 'AxiAddrWidth' must be greater than 0!;");

  localparam int unsigned NumEntries = 2**AxiIdWidth;

  ///////////////////////////////////////
  // Declarations of Signals and Types //
  ///////////////////////////////////////
  logic [NumEntries-1:0][AxiAddrWidth-1:0] table_d, table_q;
  logic [NumEntries-1:0]                   clear;
  logic [NumEntries-1:0]                   set;


  logic [NumEntries-1:0]                   check_matches;
  logic                                    id_match;

  // Table-Managing Logic
  always_comb begin
    for (int unsigned entry_idx = 0; entry_idx < NumEntries; entry_idx++) begin
      check_matches[entry_idx] = table_q[entry_idx] == i_check_clear_addr;
    end
  end

  always_comb id_match = check_matches[i_check_id];

  always_comb begin
    clear             = '0;
    set               = '0;
    o_set_gnt         = 1'b0;
    o_check_res       = 1'b0;
    o_check_clear_gnt = 1'b0;

    if (i_check_clear_req) begin
      o_check_clear_gnt = 1'b1;
      o_check_res       = id_match;
      clear             = (~i_check_clear_excl | id_match) ? check_matches : '0;
    end else if (i_set_req) begin
      set[i_set_id] = 1'b1;
      o_set_gnt     = 1'b1;
    end
  end

  // Registers
  // DFFRCL: D-Flip-Flop, asynchronous reset, synchronous clear, load enable
  always_ff @(posedge i_clk or negedge i_rst_n) begin
    if (!i_rst_n) table_q <= '0;
    else begin
      for (int unsigned entry_idx = 0; entry_idx < NumEntries; entry_idx++) begin
        if (clear[entry_idx])    table_q[entry_idx] <= '0;
        else if (set[entry_idx]) table_q[entry_idx] <= i_set_addr;
      end
    end
  end
endmodule
