// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Matt Morris <matt.morris@axelera.ai>


module pctl
  #(
      parameter int                                 N_FAST_CLKS        = pctl_ao_csr_reg_pkg::MAX_CLOCKS,
      parameter int                                 N_RESETS           = pctl_ao_csr_reg_pkg::MAX_RESETS,
      parameter int                                 N_MEM_PG           = pctl_ao_csr_reg_pkg::MAX_MEM_GRPS,
      parameter int                                 N_FENCES           = pctl_ao_csr_reg_pkg::MAX_FENCES,
      parameter int                                 N_THROTTLE_PINS    = pctl_ao_csr_reg_pkg::MAX_THROTTLE_PINS,
      parameter bit [N_FAST_CLKS-1:0][N_RESETS-1:0] CLKRST_MATRIX      = '1,
      parameter bit [N_FAST_CLKS-1:0]               PLL_CLK_IS_I_CLK   = '0,
      parameter bit [$clog2(N_RESETS)-1:0]          NOC_RST_IDX        = 0,
      parameter bit [$clog2(N_FAST_CLKS+1)-1:0]     SYNC_CLK_IDX       = 0,
      parameter bit                                 AUTO_RESET_REMOVE  = 1'b0,
      parameter bit                                 AUTO_FENCE_REMOVE  = 1'b0,
      parameter type                                paddr_t            = logic[15:0],
      parameter type                                pdata_t            = logic[31:0],
      parameter type                                pstrb_t            = logic[3:0],
      // Dependent parameter
      localparam int unsigned                       N_THROTTLE_PINS_WD = (N_THROTTLE_PINS == 0) ? 1 : N_THROTTLE_PINS
  )
  (

  input  wire                           i_clk,
  input  wire                           i_ao_rst_n,
  input  wire                           i_global_rst_n,
  input  logic                          i_test_mode,

  input  wire  [N_FAST_CLKS-1:0]        i_pll_clk,
  output wire  [N_FAST_CLKS-1:0]        o_partition_clk,

  output wire  [N_RESETS-1:0]           o_partition_rst_n,
  output wire                           o_ao_rst_sync_n,

  output logic [N_FENCES-1:0]           o_noc_async_idle_req,
  input  logic [N_FENCES-1:0]           i_noc_async_idle_ack,
  input  logic [N_FENCES-1:0]           i_noc_async_idle_val,
  output logic [N_FAST_CLKS-1:0]        o_noc_clken,
  output logic                          o_noc_rst_n,

  output logic                          o_int_shutdown_req,
  input  logic                          i_int_shutdown_ack,

  output logic [N_MEM_PG-1:0]           o_ret,
  output logic [N_MEM_PG-1:0]           o_pde,
  input  logic [N_MEM_PG-1:0]           i_prn,

  input  logic                          i_global_sync_async,
  output logic                          o_global_sync,

  input  logic [N_THROTTLE_PINS_WD-1:0] i_throttle,

  //////////////////////////////////////////////
  /// SYS_CFG Bus
  //////////////////////////////////////////////

  input  paddr_t                     i_cfg_apb4_s_paddr,
  input  pdata_t                     i_cfg_apb4_s_pwdata,
  input  logic                       i_cfg_apb4_s_pwrite,
  input  logic                       i_cfg_apb4_s_psel,
  input  logic                       i_cfg_apb4_s_penable,
  input  pstrb_t                     i_cfg_apb4_s_pstrb,
  input  logic [3-1:0]               i_cfg_apb4_s_pprot,
  output logic                       o_cfg_apb4_s_pready,
  output pdata_t                     o_cfg_apb4_s_prdata,
  output logic                       o_cfg_apb4_s_pslverr,

  output pctl_ao_csr_reg_pkg::apb_h2d_t o_ao_csr_apb_req,
  input  pctl_ao_csr_reg_pkg::apb_d2h_t i_ao_csr_apb_rsp

  );

  logic [N_RESETS-1:0]    ppmu_clken_n;
  logic [N_FAST_CLKS-1:0] noc_clken;
  wire  [N_RESETS-1:0]    partition_rst_n;

  pctl_ao_csr_reg_pkg::pctl_ao_csr_reg2hw_t reg2hw;
  pctl_ao_csr_reg_pkg::pctl_ao_csr_hw2reg_t hw2reg;

  pctl_ao_csr_reg_pkg::apb_h2d_t reg_apb_req;

  // Resync ao_rst_n - this is por so all fast clocks will run at 20MHz
  // Requires only 2 stages

  axe_ccl_rst_n_sync #(
    .SyncStages ( 2 )
  ) u_rst_sync_ao (
    .i_clk,
    .i_rst_n    (i_ao_rst_n),
    .i_test_mode,
    .o_rst_n    (o_ao_rst_sync_n)
  );

  // Resync of global reset to the local clock - can be at speed => 3 cycles
  wire global_rst_sync_n;
  axe_ccl_rst_n_sync #(
    .SyncStages ( 3 )
  ) u_rst_sync_global (
    .i_clk,
    .i_rst_n    (i_global_rst_n),
    .i_test_mode,
    .o_rst_n    (global_rst_sync_n)
  );

  if (AUTO_FENCE_REMOVE) begin : g_auto_fence_remove
    logic auto_fence_remove_q, auto_fence_remove_d;

    // Enabling drop fence operation during AO reset
    always_ff @(posedge i_clk or negedge o_ao_rst_sync_n) begin : auto_fence_remove_seq_proc
      if (!i_ao_rst_n)               auto_fence_remove_q <= '0;
      else if (!auto_fence_remove_q) auto_fence_remove_q <= auto_fence_remove_d;
    end

    // Checking drop operation
    always_comb auto_fence_remove_d = !(|reg2hw.ppmu_isolation_control);

    // Updating the CSR value to match with drop operation
    always_comb foreach(reg2hw.ppmu_isolation_control[fence]) begin
      hw2reg.ppmu_isolation_control[fence].d  = 1'b0;
      hw2reg.ppmu_isolation_control[fence].de = !auto_fence_remove_q;
    end

    // Requesting drop operation to the NoC and give control to CSRs once the operation update is confirmed in the CSRs output
    always_comb foreach(o_noc_async_idle_req[fence]) o_noc_async_idle_req[fence] = auto_fence_remove_q && reg2hw.ppmu_isolation_control[fence].q;

  end else begin : g_not_auto_fence_remove

    always_comb foreach(o_noc_async_idle_req[fence]) o_noc_async_idle_req[fence] = reg2hw.ppmu_isolation_control[fence].q;

    // Don't touch the CSRs
    always_comb foreach(reg2hw.ppmu_isolation_control[fence]) begin
      hw2reg.ppmu_isolation_control[fence].d  = 1'b0;
      hw2reg.ppmu_isolation_control[fence].de = 1'b0;
    end

  end

  // AO CSR block
  // ============
  // These contain the common set of AO CSR and an output bus to the partition
  // specific logic for partition specific AO CSR.

  // Wrap the incoming sys_cfg bus to match generated RTL structs

  always_comb reg_apb_req = '{ paddr   : i_cfg_apb4_s_paddr,
                               pwrite  : i_cfg_apb4_s_pwrite,
                               pwdata  : i_cfg_apb4_s_pwdata,
                               psel    : i_cfg_apb4_s_psel,
                               pprot   : i_cfg_apb4_s_pprot,
                               penable : i_cfg_apb4_s_penable,
                               pstrb   : i_cfg_apb4_s_pstrb
                           };

  pctl_ao_csr_reg_pkg::apb_d2h_t reg_apb_rsp;

  always_comb o_cfg_apb4_s_pready = reg_apb_rsp.pready;
  always_comb o_cfg_apb4_s_prdata = reg_apb_rsp.prdata;
  always_comb o_cfg_apb4_s_pslverr = reg_apb_rsp.pslverr;

  pctl_ao_csr_reg_top u_ao_csr (
    .clk_i  (i_clk),
    .rst_ni (o_ao_rst_sync_n),
    .apb_i  (reg_apb_req),
    .apb_o  (reg_apb_rsp),
    .apb_win_o(o_ao_csr_apb_req),
    .apb_win_i(i_ao_csr_apb_rsp),
    .reg2hw (reg2hw),
    .hw2reg (hw2reg),
    .devmode_i(1'b1)
  );


  // Per Reset PPMU
  // Required only for fast clocks
  // This is synchronous to the AO CSR

  logic [N_RESETS-1:0] prst_remove_clr;
  logic [N_RESETS-1:0] prst_activate_clr;

  for (genvar I = N_RESETS; I < pctl_ao_csr_reg_pkg::MAX_RESETS; I++) begin : g_not_implemented_rst_regs
    always_comb hw2reg.ppmu_status[I] = '{default: '0};
  end

  for (genvar I = N_MEM_PG; I < pctl_ao_csr_reg_pkg::MAX_MEM_GRPS; I++) begin : g_not_implemented_mem_regs
    always_comb hw2reg.mem_power_up_ready[I] = '{default: '0};
  end

  for (genvar I = 0; I < N_RESETS; I++) begin : g_ppmu
    pctl_ppmu u_ppmu
    (
      .i_clk              (i_clk),
      .i_rst_n            (global_rst_sync_n),
      .i_test_mode        (i_test_mode),
      .i_pre_rst_0_cycles (reg2hw.ppmu_reset_timing_control[I].pre_rst_0_cycles),
      .i_pre_rst_1_cycles (reg2hw.ppmu_reset_timing_control[I].pre_rst_1_cycles),
      .i_pre_rst_2_cycles (reg2hw.ppmu_reset_timing_control[I].pre_rst_2_cycles),
      .i_pre_rel_cycles   (reg2hw.ppmu_reset_timing_control[I].pre_rel_cycles),
      .i_rst_remove       (reg2hw.ppmu_reset_control[I].prst_remove || AUTO_RESET_REMOVE),
      .i_rst_activate     (reg2hw.ppmu_reset_control[I].prst_activate),
      .o_rst_remove_clr   (prst_remove_clr[I]),
      .o_rst_activate_clr (prst_activate_clr[I]),
      .o_fsm_state        (hw2reg.ppmu_status[I].d),
      .o_clken_n          (ppmu_clken_n[I]),
      .o_partition_rst_n  (partition_rst_n[I])
    );

    axe_tcl_std_buffer u_rst_buffer (
      .i_a (partition_rst_n[I]),
      .o_z (o_partition_rst_n[I])
    );
  end : g_ppmu


// Per Fast Clock - Clock Skip / Gate

  for (genvar I = 0; I < N_FAST_CLKS; I++) begin : g_clkdiv

    localparam int unsigned DIV_W = 8;
    logic                pllc_clock_en;
    logic    [DIV_W-1:0] pllc_clk_divider_q;
    logic                pllc_clk_divider_qe;
    logic                pllc_sw_clken_n;
    logic [N_RESETS-1:0] pllc_ppmu_clken_n;
    wire                 pll_clk;

    if (PLL_CLK_IS_I_CLK[I]) begin: g_pll_clk_is_i_clk

      assign      pll_clk = i_clk;
      always_comb pllc_clk_divider_q  = reg2hw.ppmu_clock_gating_control[I].clk_divider.q;
      always_comb pllc_clk_divider_qe = reg2hw.ppmu_clock_gating_control[I].clk_divider.qe;
      always_comb pllc_ppmu_clken_n   = ppmu_clken_n;
      always_comb pllc_sw_clken_n     = reg2hw.ppmu_clock_gating_control[I].clock_disable.q;

    end: g_pll_clk_is_i_clk
    else begin: g_pll_clk_is_ext_pll_clk

      logic clk_div_busy;
      logic latest_not_synced_q;

      assign pll_clk = i_pll_clk[I];

    // Resyncing control to the PLL domain
    // Using Standard Modules

      always_ff @ (posedge i_clk or negedge global_rst_sync_n)
        if (!global_rst_sync_n)
          latest_not_synced_q <= 1'b0;
        else if (reg2hw.ppmu_clock_gating_control[I].clk_divider.qe && clk_div_busy)
          latest_not_synced_q <= 1'b1;
        else if (!clk_div_busy)
          latest_not_synced_q <= 1'b0;

      axe_ccl_cdc_bus #(
        .SyncStages ( 3 ),
        .data_t     ( logic [DIV_W-1:0] )
      ) u_div_resync (
        .i_src_clk    (i_clk),
        .i_src_rst_n  (global_rst_sync_n),
        .i_src_en     (reg2hw.ppmu_clock_gating_control[I].clk_divider.qe || latest_not_synced_q),
        .i_src_data   (reg2hw.ppmu_clock_gating_control[I].clk_divider.q),
        .o_src_busy   (clk_div_busy),

        .i_dst_clk    (pll_clk),
        .i_dst_rst_n  (o_ao_rst_sync_n),
        .o_dst_data   (pllc_clk_divider_q),
        .o_dst_update (pllc_clk_divider_qe)
      );

      for (genvar rst_index = 0; rst_index < N_RESETS; rst_index++) begin : g_clken_sync
      axe_tcl_seq_sync #(
          .SyncStages( 3 ),
          .ResetValue(1'b0)
      ) u_ppmu_clken_resync (
          .i_clk  (pll_clk),
          .i_rst_n(o_ao_rst_sync_n),
          .i_d    (ppmu_clken_n[rst_index]),
          .o_q    (pllc_ppmu_clken_n[rst_index])
      );
      end

      axe_tcl_seq_sync #(
          .SyncStages( 3 ),
          .ResetValue(1'b0)
      ) u_sw_clken_resync (
          .i_clk  (pll_clk),
          .i_rst_n(o_ao_rst_sync_n),
          .i_d    (reg2hw.ppmu_clock_gating_control[I].clock_disable.q),
          .o_q    (pllc_sw_clken_n)
      );

    end: g_pll_clk_is_ext_pll_clk

    // Clock enable based upon SW control reg and PPMU FSM output

    always_comb pllc_clock_en = (|(CLKRST_MATRIX[I] & ~pllc_ppmu_clken_n)) && !pllc_sw_clken_n;

    // CLK Skipper / Divider Standard Component
    // Note DelayClkPulse to allow enable retime in NOC partition

    axe_ccl_clk_div_by_pt #(
      .PhaseAccWidth (8),
      .ResetValClkEn (0),
      .DelayClkPulse (1)
    ) u_clkdiv (
      .i_clk       (pll_clk),
      .i_rst_n     (o_ao_rst_sync_n),
      .i_test_en   (i_test_mode),
      .i_div_en    (pllc_clock_en),
      .i_acc_clr   (pllc_clk_divider_qe),
      .i_acc_incr  (pllc_clk_divider_q),
      .o_active    (o_noc_clken[I]),
      .o_clk       (o_partition_clk[I])
    );

  end : g_clkdiv

  always_comb o_noc_rst_n = o_partition_rst_n[NOC_RST_IDX];

  for(genvar fence = 0; fence < pctl_ao_csr_reg_pkg::MAX_FENCES; fence++) begin : g_fences
    if(fence < N_FENCES) begin : g_impl
      axe_tcl_seq_sync #(
        .SyncStages( 3 ),
        .ResetValue(1'b0)
      ) u_noc_idle_ack_resync (
        .i_clk  (i_clk),
        .i_rst_n(o_ao_rst_sync_n),
        .i_d    (i_noc_async_idle_ack[fence]),
        .o_q    (hw2reg.ppmu_isolation_status[fence].iso_idle_ack.d)
      );
      axe_tcl_seq_sync #(
        .SyncStages( 3 ),
        .ResetValue(1'b0)
      ) u_noc_idle_val_resync (
        .i_clk  (i_clk),
        .i_rst_n(o_ao_rst_sync_n),
        .i_d    (i_noc_async_idle_val[fence]),
        .o_q    (hw2reg.ppmu_isolation_status[fence].iso_idle_val.d)
      );
    end else begin: g_unconnected
      always_comb hw2reg.ppmu_isolation_status[fence] = '{default: 0};
    end
  end

  always_comb begin
    for (int unsigned I = 0; I < pctl_ao_csr_reg_pkg::MAX_RESETS; I++) begin
      if (I < N_RESETS) begin
        hw2reg.ppmu_reset_control[I].prst_remove.d = 1'b0;
        hw2reg.ppmu_reset_control[I].prst_activate.d = 1'b0;
        hw2reg.ppmu_reset_control[I].prst_remove.de = prst_remove_clr[I];
        hw2reg.ppmu_reset_control[I].prst_activate.de = prst_activate_clr[I];
      end else begin
        hw2reg.ppmu_reset_control[I] = '{default: '0};
      end
    end
    hw2reg.ppmu_internal_shutdown_status.d = i_int_shutdown_ack || reg2hw.ppmu_internal_shutdown_ack;
    hw2reg.ppmu_internal_shutdown_ack.d = 1'b0;
    hw2reg.ppmu_internal_shutdown_ack.de = |(~partition_rst_n);
    o_int_shutdown_req = reg2hw.ppmu_internal_shutdown_control.q;
  end

  for (genvar I = 0; I < N_MEM_PG; I++) begin: g_mem_pg
    axe_tcl_seq_sync #(
      .SyncStages( 3 ),
      .ResetValue(1'b0)
    ) u_prn_resync (
      .i_clk  (i_clk),
      .i_rst_n(o_ao_rst_sync_n),
      .i_d    (i_prn[I]),
      .o_q    (hw2reg.mem_power_up_ready[I].d)
    );

    always_comb o_ret[I] = reg2hw.mem_power_mode[I].ret;
    always_comb o_pde[I] = reg2hw.mem_power_mode[I].pde;

  end: g_mem_pg



  localparam int GLOBAL_SYNC_MAX_DELAY = 31;
  localparam int GLOBAL_SYNC_MAX_DELAY_W = $clog2(GLOBAL_SYNC_MAX_DELAY + 1);

  wire sync_clk;
  logic [GLOBAL_SYNC_MAX_DELAY_W-1:0] global_sync_control;

  if (SYNC_CLK_IDX == 0 || PLL_CLK_IS_I_CLK[SYNC_CLK_IDX]) begin : g_global_sync_no_resync
    assign sync_clk = i_clk;
    always_comb global_sync_control = reg2hw.global_sync_control;

  end : g_global_sync_no_resync
  else begin : g_global_sync_resync

    logic latest_delay_not_synced_q;
    logic delay_sync_busy;

    assign sync_clk = i_pll_clk[SYNC_CLK_IDX-1];

    always_ff @ (posedge i_clk or negedge global_rst_sync_n)
      if (!global_rst_sync_n)
        latest_delay_not_synced_q <= 1'b0;
      else if (reg2hw.global_sync_control.qe && delay_sync_busy)
        latest_delay_not_synced_q <= 1'b1;
      else if (!delay_sync_busy)
        latest_delay_not_synced_q <= 1'b0;

      axe_ccl_cdc_bus #(
        .SyncStages ( 3 ),
        .data_t     ( logic [GLOBAL_SYNC_MAX_DELAY_W-1:0] )
      ) u_div_resync (
        .i_src_clk    (i_clk),
        .i_src_rst_n  (global_rst_sync_n),
        .i_src_en     (reg2hw.global_sync_control.qe || latest_delay_not_synced_q),
        .i_src_data   (reg2hw.global_sync_control.q),
        .o_src_busy   (delay_sync_busy),

        .i_dst_clk    (sync_clk),
        .i_dst_rst_n  (o_ao_rst_sync_n),
        .o_dst_data   (global_sync_control),
        .o_dst_update ()
      );

  end : g_global_sync_resync

  logic global_sync;
  axe_tcl_seq_sync #(
    .SyncStages( 3 ),
    .ResetValue(1'b0)
  ) u_global_sync_resync (
    .i_clk  (sync_clk),
    .i_rst_n(o_ao_rst_sync_n),
    .i_d    (i_global_sync_async),
    .o_q    (global_sync)
  );

  logic [GLOBAL_SYNC_MAX_DELAY:0] sync_delay_d;
  logic [GLOBAL_SYNC_MAX_DELAY-1:0] sync_delay_q;

  always_ff @ (posedge sync_clk or negedge o_ao_rst_sync_n)
    if (!o_ao_rst_sync_n)
      sync_delay_q <= '0;
    else if (^({sync_delay_q,global_sync}))
      sync_delay_q <= sync_delay_d;

  always_comb sync_delay_d = {sync_delay_q, global_sync};

  always_comb o_global_sync = sync_delay_d[global_sync_control];

endmodule
