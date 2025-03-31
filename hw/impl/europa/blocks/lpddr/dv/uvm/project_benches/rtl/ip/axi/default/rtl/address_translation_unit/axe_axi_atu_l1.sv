// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Original Author: Andreas Kurth  <akurth@iis.ee.ethz.ch>

/// Internal module of [`axi_atu`](module.axi_atu): L1 translation table.
///
module axe_axi_atu_l1 #(
  /// Width of addresses in input address space
  parameter int unsigned InpAddrWidth = axe_axi_default_types_pkg::WIDTH_ADDR_64,
  /// Width of addresses in output address space
  parameter int unsigned OupAddrWidth = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// Number of entries in translation table
  parameter int unsigned NumEntries = axe_axi_default_types_pkg::AtuNumEntries,
  /// Number of bits in the page offset field of an address. These bist are not considered in the match
  /// and are added to the translated address. May not be smaller than 12 (AMBA)
  parameter int unsigned PageOffsetSize = axe_axi_default_types_pkg::AtuPageOffsetSize,
  /// Type of translation result.  Must have a single-bit field `hit` and an `addr` field as wide as
  /// the output address.
  parameter type result_t = axe_axi_default_types_pkg::atu_result_t,
  /// Type of page table entry
  parameter type entry_t = axe_axi_default_types_pkg::atu_entry_t,
  /// Derived (=do not override) type of input addresses
  localparam type inp_addr_t = logic[InpAddrWidth-1:0],
  /// Derived (=do not override) type of output addresses
  localparam type oup_addr_t = logic[OupAddrWidth-1:0]
)(
  /// Rising-edge clock of all ports
  input  wire       i_clk,
  /// Asynchronous reset, active low
  input  wire       i_rst_n,
  /// Write request input address
  input  inp_addr_t i_wr_req_addr,
  /// Write request valid
  input  logic      i_wr_req_valid,
  /// Write request ready
  output logic      o_wr_req_ready,
  /// Write translation result
  output result_t   o_wr_res,
  /// Write translation result valid
  output logic      o_wr_res_valid,
  /// Write translation result ready
  input  logic      i_wr_res_ready,
  /// Read request input address
  input  inp_addr_t i_rd_req_addr,
  /// Read request valid
  input  logic      i_rd_req_valid,
  /// Read request ready
  output logic      o_rd_req_ready,
  /// Read translation result
  output result_t   o_rd_res,
  /// Read translation result valid
  output logic      o_rd_res_valid,
  /// Read translation result ready
  input  logic      i_rd_res_ready,
  /// Configured translation entries
  input  entry_t    i_entries[NumEntries],
  /// Whether atu is bypassed (no translation)
  input  logic      i_bypass
);

  // Write channel
  axe_axi_atu_l1_channel #(
    .NumEntries    (NumEntries),
    .PageOffsetSize(PageOffsetSize),
    .OupAddrWidth  (OupAddrWidth),
    .IsWriteChannel(1'b1),
    .req_addr_t    (inp_addr_t),
    .entry_t       (entry_t),
    .result_t      (result_t)
  ) u_wr_chan (
    .i_clk,
    .i_rst_n,
    .i_entries,
    .i_bypass,
    .i_req_addr (i_wr_req_addr),
    .i_req_valid(i_wr_req_valid),
    .o_req_ready(o_wr_req_ready),
    .o_res      (o_wr_res),
    .o_res_valid(o_wr_res_valid),
    .i_res_ready(i_wr_res_ready)
  );

  // Read channel
  axe_axi_atu_l1_channel #(
    .NumEntries    (NumEntries),
    .PageOffsetSize(PageOffsetSize),
    .OupAddrWidth  (OupAddrWidth),
    .IsWriteChannel(1'b0),
    .req_addr_t    (inp_addr_t),
    .entry_t       (entry_t),
    .result_t      (result_t)
  ) u_rd_chan (
    .i_clk,
    .i_rst_n,
    .i_entries,
    .i_bypass,
    .i_req_addr (i_rd_req_addr),
    .i_req_valid(i_rd_req_valid),
    .o_req_ready(o_rd_req_ready),
    .o_res      (o_rd_res),
    .o_res_valid(o_rd_res_valid),
    .i_res_ready(i_rd_res_ready)
  );
endmodule
