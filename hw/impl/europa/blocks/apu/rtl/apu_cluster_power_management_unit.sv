/// Description: APU Power management unit handling automatic clock gating of the AX65 cluster
///
module apu_cluster_power_management_unit #(
  parameter int unsigned CORE_WIDTH = 4,
  parameter int unsigned SYNC_STAGES = 2,
  parameter int unsigned PIPELINE_STAGES = 3
) (
    /// Fast core clocks
    input wire [CORE_WIDTH - 1:0] i_cores_clk,
    input wire [CORE_WIDTH - 1:0] i_cores_rst_n,
    /// Fast l2c clock
    input wire i_l2c_clk,
    input wire i_l2c_rst_n,

    /// Fast core clocks
    output wire  [CORE_WIDTH - 1:0] o_cores_clk,
    output wire  [CORE_WIDTH - 1:0] o_cores_dcu_clk,
    /// Enable sigs for apu_core_p
    output logic [CORE_WIDTH - 1:0] o_cores_clk_enable,
    output logic [CORE_WIDTH - 1:0] o_cores_dcu_clk_enable,
    /// Fast l2c clock
    output wire o_l2c_clk,
    /// Div2 l2c clock
    output wire o_l2c_banks_clk,
    output wire o_l2c_banks_clk_en,

    /// DFT
    input logic i_test_en,

    /// internal state
    input logic [CORE_WIDTH - 1:0] i_cores_wfi_mode,
    input logic [CORE_WIDTH - 1:0] i_cores_debugint,
    input logic [CORE_WIDTH - 1:0] i_cores_nmi,
    input logic [CORE_WIDTH - 1:0] i_cores_meip,
    input logic [CORE_WIDTH - 1:0] i_cores_seip,
    input logic [CORE_WIDTH - 1:0] i_cores_msip,
    input logic [CORE_WIDTH - 1:0] i_cores_mtip,
    input logic [CORE_WIDTH - 1:0] i_cores_coherent_state,
    input logic [CORE_WIDTH - 1:0] i_cores_coherent_enable
);

  // Sync to cores clk
  logic [CORE_WIDTH - 1:0] cores_debugint_synced;
  logic [CORE_WIDTH - 1:0] cores_nmi_synced;
  logic [CORE_WIDTH - 1:0] cores_meip_synced;
  logic [CORE_WIDTH - 1:0] cores_seip_synced;
  logic [CORE_WIDTH - 1:0] cores_msip_synced;
  logic [CORE_WIDTH - 1:0] cores_mtip_synced;

  for (genvar i = 0; unsigned'(i) < CORE_WIDTH; i++) begin: g_cores_sync
    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b0)
    ) u_debugint_sync (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_d(i_cores_debugint[i]),
      .o_q(cores_debugint_synced[i])
    );

    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b0)
    ) u_nmi_sync (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_d(i_cores_nmi[i]),
      .o_q(cores_nmi_synced[i])
    );

    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b0)
    ) u_meip_sync (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_d(i_cores_meip[i]),
      .o_q(cores_meip_synced[i])
    );

    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b0)
    ) u_seip_sync (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_d(i_cores_seip[i]),
      .o_q(cores_seip_synced[i])
    );

    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b0)
    ) u_msip_sync (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_d(i_cores_msip[i]),
      .o_q(cores_msip_synced[i])
    );

    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b0)
    ) u_mtip_sync (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_d(i_cores_mtip[i]),
      .o_q(cores_mtip_synced[i])
    );
  end

  // Cores clk
  logic [CORE_WIDTH - 1:0] cores_gate_enable;
  always_comb cores_gate_enable =
    (~i_cores_wfi_mode) |
    cores_debugint_synced |
    cores_nmi_synced |
    cores_meip_synced |
    cores_seip_synced |
    cores_msip_synced |
    cores_mtip_synced;

  logic [CORE_WIDTH - 1:0] cores_gate_enable_pipelined;
  for (genvar i = 0; unsigned'(i) < CORE_WIDTH; i++) begin: g_cores_clk
    cc_cnt_shift_reg #(
      .Width(1),
      .Stages(PIPELINE_STAGES)
    ) u_pipeline (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_clear('0),
      .i_stall('0),
      .i_data(cores_gate_enable[i]),
      .i_data_en('1),
      .o_data(cores_gate_enable_pipelined[i]),
      .o_updated()
    );

    axe_tcl_clk_gating u_tcl_clk_gate (
      .i_clk(i_cores_clk[i]),
      .i_en(cores_gate_enable_pipelined[i]),
      .i_test_en,
      .o_clk(o_cores_clk[i])
    );
  end
  always_comb o_cores_clk_enable = cores_gate_enable_pipelined;

  // Cores DCU clk
  logic [CORE_WIDTH - 1:0] cores_dcu_gate_enable;
  always_comb cores_dcu_gate_enable =
    cores_gate_enable |
    i_cores_coherent_state |
    i_cores_coherent_enable;

  logic [CORE_WIDTH - 1:0] cores_dcu_gate_enable_pipelined;
  for (genvar i = 0; unsigned'(i) < CORE_WIDTH; i++) begin: g_cores_dcu_clk
    cc_cnt_shift_reg #(
      .Width(1),
      .Stages(PIPELINE_STAGES)
    ) u_pipeline (
      .i_clk(i_cores_clk[i]),
      .i_rst_n(i_cores_rst_n[i]),
      .i_clear('0),
      .i_stall('0),
      .i_data(cores_dcu_gate_enable[i]),
      .i_data_en('1),
      .o_data(cores_dcu_gate_enable_pipelined[i]),
      .o_updated()
    );

    axe_tcl_clk_gating u_tcl_clk_gate (
      .i_clk(i_cores_clk[i]),
      .i_en(cores_dcu_gate_enable_pipelined[i]),
      .i_test_en,
      .o_clk(o_cores_dcu_clk[i])
    );
  end
  always_comb o_cores_dcu_clk_enable = cores_dcu_gate_enable_pipelined;

  // Sync to l2c clk
  logic [CORE_WIDTH - 1:0] cores_dcu_gate_enable_synced;
  for (genvar i = 0; unsigned'(i) < CORE_WIDTH; i++) begin: g_l2c_sync
    axe_tcl_seq_sync #(
      .SyncStages(SYNC_STAGES),
      .ResetValue(1'b1)
    ) u_dcu_gate_enable_sync (
      .i_clk(i_l2c_clk),
      .i_rst_n(i_l2c_rst_n),
      .i_d(cores_dcu_gate_enable[i]),
      .o_q(cores_dcu_gate_enable_synced[i])
    );
  end

  // L2c clk
  logic l2c_gate_enable;
  always_comb l2c_gate_enable = |cores_dcu_gate_enable_synced;

  wire l2c_clk;
  axe_tcl_clk_gating u_tcl_l2c_clk_gate (
    .i_clk(i_l2c_clk),
    .i_en(l2c_gate_enable),
    .i_test_en,
    .o_clk(l2c_clk)
  );

  // l2c clk buffer (DFT request)
  axe_tcl_clk_buffer u_l2c_clk_occ_buf (
    .i_clk(l2c_clk),
    .o_clk(o_l2c_clk)
  );

  // l2c banks clk
  wire l2c_banks_clk;
  wire l2c_banks_clk_buf;
  wire l2c_banks_clk_en;

  axe_ccl_clk_div_by_2 u_l2c_clk_div_by_2 (
    .i_clk(l2c_clk),
    .i_rst_n(i_l2c_rst_n),
    .i_test_mode(1'b0), // DFT request
    .i_enable(1'b1),
    .o_clk(l2c_banks_clk)
  );

  // l2c banks clk buffer (DFT request)
  axe_tcl_clk_buffer u_l2c_banks_clk_occ_buf (
    .i_clk(l2c_banks_clk),
    .o_clk(l2c_banks_clk_buf)
  );
  assign o_l2c_banks_clk = l2c_banks_clk_buf;

  axe_tcl_clk_inverter u_l2c_clk_inv (
    .i_clk(l2c_banks_clk_buf),
    .o_clk(o_l2c_banks_clk_en)
  );

endmodule
