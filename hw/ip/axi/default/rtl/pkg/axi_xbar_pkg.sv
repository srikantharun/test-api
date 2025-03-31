// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Package containing type definitions for the 'axi_xbar'.
///
package axi_xbar_pkg;

  // `xbar_latency_e` and `xbar_cfg_t` are documented in `doc/axi_xbar.md`.
  /// Slice on Demux AW channel.
  parameter bit [9:0] DemuxAw = (1 << 9);
  /// Slice on Demux W channel.
  parameter bit [9:0] DemuxW  = (1 << 8);
  /// Slice on Demux B channel.
  parameter bit [9:0] DemuxB  = (1 << 7);
  /// Slice on Demux AR channel.
  parameter bit [9:0] DemuxAr = (1 << 6);
  /// Slice on Demux R channel.
  parameter bit [9:0] DemuxR  = (1 << 5);
  /// Slice on Mux AW channel.
  parameter bit [9:0] MuxAw   = (1 << 4);
  /// Slice on Mux W channel.
  parameter bit [9:0] MuxW    = (1 << 3);
  /// Slice on Mux B channel.
  parameter bit [9:0] MuxB    = (1 << 2);
  /// Slice on Mux AR channel.
  parameter bit [9:0] MuxAr   = (1 << 1);
  /// Slice on Mux R channel.
  parameter bit [9:0] MuxR    = (1 << 0);
  /// Latency configuration for `axi_xbar`.
  typedef enum bit [9:0] {
    NO_LATENCY    = 10'b000_00_000_00,
    CUT_SUB_AX    = DemuxAw | DemuxAr,
    CUT_MAN_AX    = MuxAw | MuxAr,
    CUT_ALL_AX    = DemuxAw | DemuxAr | MuxAw | MuxAr,
    CUT_SUB_PORTS = DemuxAw | DemuxW | DemuxB | DemuxAr | DemuxR,
    CUT_MAN_PORTS = MuxAw | MuxW | MuxB | MuxAr | MuxR,
    CUT_ALL_PORTS = 10'b111_11_111_11
  } xbar_latency_e;
endpackage
