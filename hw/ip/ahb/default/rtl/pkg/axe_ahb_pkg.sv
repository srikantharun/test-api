// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: kevin luciani <kevin.luciani@axelera.ai>

//! AHB Package
/// Contains all necessary AHB type definitions, constants, and generally useful functions.
///
package axe_ahb_pkg;

  /// HTRANS width
  parameter int unsigned HTRANS_W = 2;
  /// HSIZE width
  parameter int unsigned HSIZE_W  = 3;
  /// HBURST width
  parameter int unsigned HBURST_W = 3;

  /// AHB Transfer logic type (HTRANS)
  typedef logic [HTRANS_W-1:0] htrans_t;
  /// AHB Size logic type (HSIZE)
  typedef logic [HSIZE_W -1:0] hsize_t;
  /// AHB Burst logic type (HTRANS)
  typedef logic [HBURST_W-1:0] hburst_t;

  /// AHB Transfer enum type (HTRANS)
  typedef enum logic [HTRANS_W-1:0] {
    /// No data transfer is required
    IDLE    = 2'b00,
    /// The master is continuing the burst
    BUSY    = 2'b01,
    /// Indicates the first transfer of a burst or a single transfer
    NONSEQ  = 2'b10,
    /// Remaining transfers in a burst
    SEQ     = 2'b11
  } htrans_e;

  /// AHB Size enum type (HSIZE)
  typedef enum logic [HSIZE_W-1:0] {
    /// 8-bit transfer
    BYTE        = 3'b000,
    /// 16-bit transfer
    HALFWORD    = 3'b001,
    /// 32-bit transfer
    WORD        = 3'b010,
    /// 64-bit transfer
    DOUBLEWORD  = 3'b011,
    /// 128-bit transfer
    QUADWORD    = 3'b100,
    /// 256-bit transfer
    OCTWORD     = 3'b101
  } hsize_e;

  /// AHB Burst enum type (HBURST)
  typedef enum logic [HBURST_W-1:0] {
    /// Single transfer
    SINGLE     = 3'b000,
    /// Incremental burst
    INCR       = 3'b001,
    /// 4-beat wrapping burst
    WRAP4      = 3'b010,
    /// 4-beat incremental burst
    INCR4      = 3'b011,
    /// 8-beat wrapping burst
    WRAP8      = 3'b100,
    /// 8-beat incremental burst
    INCR8      = 3'b101,
    /// 16-beat wrapping burst
    WRAP16     = 3'b110,
    /// 16-beat incremental burst
    INCR16     = 3'b111
  } hburst_e;

  /// AHB byte width
  parameter int unsigned  BYTE_W       = 8;
  /// AHB half word width
  parameter int unsigned  HALFWORD_W   = 16;
  /// AHB word width
  parameter int unsigned  WORD_W       = 32;
  /// AHB double word width
  parameter int unsigned  DOUBLEWORD_W = 64;
  /// AHB quad word width
  parameter int unsigned  QUADWORD_W   = 128;
  /// AHB oct word width
  parameter int unsigned  OCTWORD_W    = 256;

endpackage
