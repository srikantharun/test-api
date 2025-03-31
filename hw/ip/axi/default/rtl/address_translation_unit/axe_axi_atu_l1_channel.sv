// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Original Autor: Andreas Kurth <akurth@iis.ee.ethz.ch>

/// Internal module of [`axi_atu_l1`](module.axi_atu_l1): Channel handler.
///
module axe_axi_atu_l1_channel #(
  /// Number of entries in translation table
  parameter int unsigned NumEntries = axe_axi_default_types_pkg::AtuNumEntries,
  /// Number of bits in the page offset field of an address. These bist are not considered in the match
  /// and are added to the translated address. May not be smaller than 12 (AMBA)
  parameter int unsigned PageOffsetSize = axe_axi_default_types_pkg::AtuPageOffsetSize,
  /// Width of addresses in output address space
  parameter int unsigned OupAddrWidth = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Is this channel is used for writes?
  parameter logic IsWriteChannel = 1'b0,
  /// Type of request address
  parameter type req_addr_t = axe_axi_default_types_pkg::axi_addr_64_t,
  /// Type of a translation table entry
  parameter type entry_t = axe_axi_default_types_pkg::atu_entry_t,
  /// Type of translation result
  parameter type result_t = axe_axi_default_types_pkg::atu_result_t
)(
  /// Rising-edge clock
  input  wire       i_clk,
  /// Asynchronous reset, active low
  input  wire       i_rst_n,
  /// Translation table entries
  input  entry_t    i_entries[NumEntries],
  /// Whether atu is bypassed (no translation)
  input  logic      i_bypass,
  /// Request address
  input  req_addr_t i_req_addr,
  /// Request valid
  input  logic      i_req_valid,
  /// Request ready
  output logic      o_req_ready,
  /// Translation result
  output result_t   o_res,
  /// Translation result valid
  output logic      o_res_valid,
  /// Translation result ready
  input  logic      i_res_ready
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if ($bits(i_req_addr) <= 12) $fatal(1, "Parameter: '$bits(i_req_addr)' Input address space must be larger than one 4 KiB page!;");
  if (OupAddrWidth      <= 12) $fatal(1, "Parameter: 'OupAddrWidth' Output address space must be larger than one 4 KiB page!;");
  if (PageOffsetSize    <  12) $fatal(1, "Parameter: 'PageOffsetSize' Page Offset Size must be larger than 4 KiB page!;");

  localparam int unsigned EntryIdxWidth = cc_math_pkg::index_width(NumEntries);

  typedef logic [EntryIdxWidth-1:0] entry_idx_t;

  // Determine all entries matching a request.
  logic [NumEntries-1:0] entry_matches;
  for (genvar i = 0; unsigned'(i) < NumEntries; i++) begin : gen_matches
    assign entry_matches[i] = i_entries[i].valid & i_req_valid
        & ((i_req_addr >> PageOffsetSize) >= i_entries[i].first)
        & ((i_req_addr >> PageOffsetSize) <= i_entries[i].last)
        & (~IsWriteChannel | ~i_entries[i].read_only);
  end

  // Determine entry with lowest index that matches the request.
  entry_idx_t match_idx;
  logic       no_match;
  lzc #(
    .WIDTH(NumEntries),
    .MODE (1'b0)         // trailing zeros -> lowest match
  ) u_lzc (
    .in_i   (entry_matches),
    .cnt_o  (match_idx),
    .empty_o(no_match)
  );

  // Handle request and translate address.
  logic res_valid, res_ready;
  result_t res;
  always_comb begin
    res_valid = 1'b0;
    o_req_ready = 1'b0;
    res = '{default: '0};
    if (i_bypass) begin
      // In bypass mode, we always "hit" with the original address
      res = '{hit: 1'b1, addr: i_req_addr};
      res_valid = i_req_valid;
      o_req_ready = res_ready;
    end else if (i_req_valid) begin
      if (no_match) begin
        res = '{default: '0};
      end else begin
        res.hit = 1'b1;
        res.addr = {
          (OupAddrWidth-PageOffsetSize)'(
          ((i_req_addr >> PageOffsetSize) - i_entries[match_idx].first) + i_entries[match_idx].base
        ),
          i_req_addr[PageOffsetSize-1:0]
        };
      end
      res_valid   = 1'b1;
      o_req_ready = res_ready;
    end
  end
  // Store translation in fall-through register.  This prevents changes in the translated address
  // due to changes in `i_entries` while downstream handshake is outstanding.
  cc_stream_reg_ft #(
    .data_t(result_t)
  ) u_res_ft_reg (
    .i_clk,
    .i_rst_n,
    .i_flush(1'b0),
    .i_data (res),
    .i_valid(res_valid),
    .o_ready(res_ready),
    .o_data (o_res),
    .o_valid(o_res_valid),
    .i_ready(i_res_ready)
  );
endmodule
