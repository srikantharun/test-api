// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>
//
// Derived from: https://github.com/pulp-platform/axi_riscv_atomics/blob/master/src/axi_riscv_atomics.sv
// Original Authors:
//   - Samuel Riedel <sriedel@iis.ee.ethz.ch>
//   - Andreas Kurth <akurth@iis.ee.ethz.ch>

/// AXI RISC-V Atomics ("A" Extension) Adapter
///
/// This AXI adapter implements the RISC-V "A" extension and adheres to the RVWMO memory consistency
/// model.
///
module axe_axi_riscv_atomics #(
  /// AXI ID Field Width
  parameter int unsigned AxiIdWidth      = axe_axi_default_types_pkg::WIDTH_ID_4,
  /// AXI Address Width
  parameter int unsigned AxiAddrWidth    = axe_axi_default_types_pkg::WIDTH_ADDR_40,
  /// AXI Data Width
  parameter int unsigned AxiDataWidth    = axe_axi_default_types_pkg::WIDTH_DATA_64,
  /// The Axi User Field Width
  parameter int unsigned AxiUserWidth    = axe_axi_default_types_pkg::WIDTH_USER_4,
  /// Maximum number of in-flight read transactions
  parameter int unsigned AxiMaxReadTxns  = 8,
  /// Maximum number of in-flight write transactions
  parameter int unsigned AxiMaxWriteTxns = 8,
  /// The number of reservation table entries (lrsc)
  parameter int unsigned ResTableEntries = AxiMaxReadTxns + AxiMaxWriteTxns,
  /// Use the AXI User signal instead of the AXI ID to track reservations
  parameter bit          AxiUserAsId     = 1'b0,
  /// MSB of the ID in the user signal (only needed if `AxiUserAsId == 1`)
  parameter int unsigned AxiUserAsIdMsb  = 0,
  /// LSB of the ID in the user signal (only needed if `AxiUserAsId == 1`)
  parameter int unsigned AxiUserAsIdLsb  = 0,
  /// LSB of the AXI address for reservations (determines the reservation granularity)
  parameter int unsigned AxiAddrLsb      = $clog2(AxiDataWidth/8),
  /// Enable full bandwidth in ID queues
  parameter bit          FullBandwidth   = 1'b1,
  /// Word width of the widest RISC-V processor that can issue requests to this module.
  /// 32 for RV32; 64 for RV64, where both 32-bit (.W suffix) and 64-bit (.D suffix) AMOs are
  /// supported if `aw_strb` is set correctly.
  parameter int unsigned RiscvWordWidth  = 64,
  /// Add a cut between axi_riscv_amos and axi_riscv_lrsc
  parameter int unsigned NumCuts = 1,

  // AXI channel structs
  parameter type         axi_aw_t        = axe_axi_default_types_pkg::axi_aw_4_40_4_t,
  parameter type         axi_w_t         = axe_axi_default_types_pkg::axi_w_64_8_4_t,
  parameter type         axi_b_t         = axe_axi_default_types_pkg::axi_b_4_4_t,
  parameter type         axi_ar_t        = axe_axi_default_types_pkg::axi_ar_4_40_4_t,
  parameter type         axi_r_t         = axe_axi_default_types_pkg::axi_r_4_64_4_t
)(
  input  wire     i_clk,
  input  wire     i_rst_n,

  ///////////////////////////
  // Subordinate Interface //
  ///////////////////////////
  input  axi_aw_t i_axi_s_aw,
  input  logic    i_axi_s_aw_valid,
  output logic    o_axi_s_aw_ready,
  input  axi_w_t  i_axi_s_w,
  input  logic    i_axi_s_w_valid,
  output logic    o_axi_s_w_ready,
  output axi_b_t  o_axi_s_b,
  output logic    o_axi_s_b_valid,
  input  logic    i_axi_s_b_ready,
  input  axi_ar_t i_axi_s_ar,
  input  logic    i_axi_s_ar_valid,
  output logic    o_axi_s_ar_ready,
  output axi_r_t  o_axi_s_r,
  output logic    o_axi_s_r_valid,
  input  logic    i_axi_s_r_ready,

  ///////////////////////
  // Manager Interface //
  ///////////////////////
  output axi_aw_t o_axi_m_aw,
  output logic    o_axi_m_aw_valid,
  input  logic    i_axi_m_aw_ready,
  output axi_w_t  o_axi_m_w,
  output logic    o_axi_m_w_valid,
  input  logic    i_axi_m_w_ready,
  input  axi_b_t  i_axi_m_b,
  input  logic    i_axi_m_b_valid,
  output logic    o_axi_m_b_ready,
  output axi_ar_t o_axi_m_ar,
  output logic    o_axi_m_ar_valid,
  input  logic    i_axi_m_ar_ready,
  input  axi_r_t  i_axi_m_r,
  input  logic    i_axi_m_r_valid,
  output logic    o_axi_m_r_ready
);

  // Make the entire address range exclusively accessible. Since the AMO adapter does not support
  // address ranges, it would not make sense to expose the address range as a parameter of this
  // module.
  localparam logic [AxiAddrWidth-1:0] ADDR_START = {AxiAddrWidth{1'b0}};
  localparam logic [AxiAddrWidth-1:0] ADDR_END   = {AxiAddrWidth{1'b1}};

  typedef enum int unsigned {
    AmosToCut = 0,
    CutToLrsc = 1
  } axi_bus_idx_e;

  axi_aw_t axi_internal_aw[2];
  logic    axi_internal_aw_valid[2];
  logic    axi_internal_aw_ready[2];
  axi_w_t  axi_internal_w[2];
  logic    axi_internal_w_valid[2];
  logic    axi_internal_w_ready[2];
  axi_b_t  axi_internal_b[2];
  logic    axi_internal_b_valid[2];
  logic    axi_internal_b_ready[2];
  axi_ar_t axi_internal_ar[2];
  logic    axi_internal_ar_valid[2];
  logic    axi_internal_ar_ready[2];
  axi_r_t  axi_internal_r[2];
  logic    axi_internal_r_valid[2];
  logic    axi_internal_r_ready[2];

  axe_axi_riscv_amos #(
    .AxiIdWidth     (AxiIdWidth),
    .AxiAddrWidth   (AxiAddrWidth),
    .AxiDataWidth   (AxiDataWidth),
    .AxiMaxWriteTxns(AxiMaxWriteTxns),
    .RiscvWordWidth (RiscvWordWidth),
    .axi_aw_t       (axi_aw_t),
    .axi_w_t        (axi_w_t),
    .axi_b_t        (axi_b_t),
    .axi_ar_t       (axi_ar_t),
    .axi_r_t        (axi_r_t)
  ) u_amos (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw,
    .i_axi_s_aw_valid,
    .o_axi_s_aw_ready,
    .i_axi_s_w,
    .i_axi_s_w_valid,
    .o_axi_s_w_ready,
    .o_axi_s_b,
    .o_axi_s_b_valid,
    .i_axi_s_b_ready,
    .i_axi_s_ar,
    .i_axi_s_ar_valid,
    .o_axi_s_ar_ready,
    .o_axi_s_r,
    .o_axi_s_r_valid,
    .i_axi_s_r_ready,
    .o_axi_m_aw      (axi_internal_aw[AmosToCut]),
    .o_axi_m_aw_valid(axi_internal_aw_valid[AmosToCut]),
    .i_axi_m_aw_ready(axi_internal_aw_ready[AmosToCut]),
    .o_axi_m_w       (axi_internal_w[AmosToCut]),
    .o_axi_m_w_valid (axi_internal_w_valid[AmosToCut]),
    .i_axi_m_w_ready (axi_internal_w_ready[AmosToCut]),
    .i_axi_m_b       (axi_internal_b[AmosToCut]),
    .i_axi_m_b_valid (axi_internal_b_valid[AmosToCut]),
    .o_axi_m_b_ready (axi_internal_b_ready[AmosToCut]),
    .o_axi_m_ar      (axi_internal_ar[AmosToCut]),
    .o_axi_m_ar_valid(axi_internal_ar_valid[AmosToCut]),
    .i_axi_m_ar_ready(axi_internal_ar_ready[AmosToCut]),
    .i_axi_m_r       (axi_internal_r[AmosToCut]),
    .i_axi_m_r_valid (axi_internal_r_valid[AmosToCut]),
    .o_axi_m_r_ready (axi_internal_r_ready[AmosToCut])
  );

  axe_axi_multicut #(
    .NumCuts (NumCuts),
    .axi_aw_t(axi_aw_t),
    .axi_w_t (axi_w_t),
    .axi_b_t (axi_b_t),
    .axi_ar_t(axi_ar_t),
    .axi_r_t (axi_r_t)
  ) u_axi_wide_in_cut (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_internal_aw[AmosToCut]),
    .i_axi_s_aw_valid(axi_internal_aw_valid[AmosToCut]),
    .o_axi_s_aw_ready(axi_internal_aw_ready[AmosToCut]),
    .i_axi_s_w       (axi_internal_w[AmosToCut]),
    .i_axi_s_w_valid (axi_internal_w_valid[AmosToCut]),
    .o_axi_s_w_ready (axi_internal_w_ready[AmosToCut]),
    .o_axi_s_b       (axi_internal_b[AmosToCut]),
    .o_axi_s_b_valid (axi_internal_b_valid[AmosToCut]),
    .i_axi_s_b_ready (axi_internal_b_ready[AmosToCut]),
    .i_axi_s_ar      (axi_internal_ar[AmosToCut]),
    .i_axi_s_ar_valid(axi_internal_ar_valid[AmosToCut]),
    .o_axi_s_ar_ready(axi_internal_ar_ready[AmosToCut]),
    .o_axi_s_r       (axi_internal_r[AmosToCut]),
    .o_axi_s_r_valid (axi_internal_r_valid[AmosToCut]),
    .i_axi_s_r_ready (axi_internal_r_ready[AmosToCut]),
    .o_axi_m_aw      (axi_internal_aw[CutToLrsc]),
    .o_axi_m_aw_valid(axi_internal_aw_valid[CutToLrsc]),
    .i_axi_m_aw_ready(axi_internal_aw_ready[CutToLrsc]),
    .o_axi_m_w       (axi_internal_w[CutToLrsc]),
    .o_axi_m_w_valid (axi_internal_w_valid[CutToLrsc]),
    .i_axi_m_w_ready (axi_internal_w_ready[CutToLrsc]),
    .i_axi_m_b       (axi_internal_b[CutToLrsc]),
    .i_axi_m_b_valid (axi_internal_b_valid[CutToLrsc]),
    .o_axi_m_b_ready (axi_internal_b_ready[CutToLrsc]),
    .o_axi_m_ar      (axi_internal_ar[CutToLrsc]),
    .o_axi_m_ar_valid(axi_internal_ar_valid[CutToLrsc]),
    .i_axi_m_ar_ready(axi_internal_ar_ready[CutToLrsc]),
    .i_axi_m_r       (axi_internal_r[CutToLrsc]),
    .i_axi_m_r_valid (axi_internal_r_valid[CutToLrsc]),
    .o_axi_m_r_ready (axi_internal_r_ready[CutToLrsc])
  );

  axe_axi_riscv_lrsc #(
    .AxiIdWidth     (AxiIdWidth),
    .AxiAddrWidth   (AxiAddrWidth),
    .AddrStart      (ADDR_START),
    .AddrEnd        (ADDR_END),
    .AxiDataWidth   (AxiDataWidth),
    .AxiUserWidth   (AxiUserWidth),
    .AxiMaxReadTxns (AxiMaxReadTxns),
    .AxiMaxWriteTxns(AxiMaxWriteTxns),
    .ResTableEntries(ResTableEntries),
    .AxiUserAsId    (AxiUserAsId),
    .AxiUserAsIdMsb (AxiUserAsIdMsb),
    .AxiUserAsIdLsb (AxiUserAsIdLsb),
    .AxiAddrLsb     (AxiAddrLsb),
    .DebugPrints    (1'b0),
    .FullBandwidth  (FullBandwidth),
    .axi_aw_t       (axi_aw_t),
    .axi_w_t        (axi_w_t),
    .axi_b_t        (axi_b_t),
    .axi_ar_t       (axi_ar_t),
    .axi_r_t        (axi_r_t)
  ) u_lrsc (
    .i_clk,
    .i_rst_n,
    .i_axi_s_aw      (axi_internal_aw[CutToLrsc]),
    .i_axi_s_aw_valid(axi_internal_aw_valid[CutToLrsc]),
    .o_axi_s_aw_ready(axi_internal_aw_ready[CutToLrsc]),
    .i_axi_s_w       (axi_internal_w[CutToLrsc]),
    .i_axi_s_w_valid (axi_internal_w_valid[CutToLrsc]),
    .o_axi_s_w_ready (axi_internal_w_ready[CutToLrsc]),
    .o_axi_s_b       (axi_internal_b[CutToLrsc]),
    .o_axi_s_b_valid (axi_internal_b_valid[CutToLrsc]),
    .i_axi_s_b_ready (axi_internal_b_ready[CutToLrsc]),
    .i_axi_s_ar      (axi_internal_ar[CutToLrsc]),
    .i_axi_s_ar_valid(axi_internal_ar_valid[CutToLrsc]),
    .o_axi_s_ar_ready(axi_internal_ar_ready[CutToLrsc]),
    .o_axi_s_r       (axi_internal_r[CutToLrsc]),
    .o_axi_s_r_valid (axi_internal_r_valid[CutToLrsc]),
    .i_axi_s_r_ready (axi_internal_r_ready[CutToLrsc]),
    .o_axi_m_aw,
    .o_axi_m_aw_valid,
    .i_axi_m_aw_ready,
    .o_axi_m_w,
    .o_axi_m_w_valid,
    .i_axi_m_w_ready,
    .i_axi_m_b,
    .i_axi_m_b_valid,
    .o_axi_m_b_ready,
    .o_axi_m_ar,
    .o_axi_m_ar_valid,
    .i_axi_m_ar_ready,
    .i_axi_m_r,
    .i_axi_m_r_valid,
    .o_axi_m_r_ready
  );
endmodule
