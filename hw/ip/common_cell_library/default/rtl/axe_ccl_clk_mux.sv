// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Wolfgang Roenninger <wolfgang.roenninger@axelera.ai>


/// Glich-free clock multiplexer, uses tc_lib cells on all clock paths.
///
module axe_ccl_clk_mux #(
  /// Number of input clocks
  parameter int unsigned NumClocks = 2,
  /// The number of synchronization stages for each enable sync
  parameter int unsigned SyncStages = 3,
  /// Clock 0 is active during reset
  parameter bit          ClkActiveReset = 1'b0,
  /// Clock that should be active if `ClkActiveReset == 1`
  parameter int unsigned ClkActiveResetIdx = 0,
  /// Dependent parameter
  /// The select signal width
  localparam int unsigned SelectWidth = cc_math_pkg::index_width(NumClocks),
  /// Dependent parameter
  /// The select signal width
  localparam type select_t = logic[SelectWidth-1:0]
)(
  ///////////////////
  // Configuration //
  ///////////////////
  /// Clock, positive edge triggered
  input  wire     i_clk_cfg,
  // doc async
  /// Asynchronous reset for the configuration clock
  /// Note this reset will be synchonized to each clock to be switched!!!
  input  wire     i_rst_cfg_n,
  /// Reset bypass enable in all slices reset synchronizers
  input  logic    i_test_mode,
  // doc sync i_clk_cfg
  /// Select input Clock
  input  select_t i_select,
  /// Enable the clock downstream
  input  logic    i_enable,

  ///////////////////
  // Observability //
  ///////////////////
  /// The selected clock slice downstream is activated
  output logic [NumClocks-1:0] o_active,
  /// The FSM is in the on-state, the dwonstream clock is safely on
  output logic                 o_is_on,


  //////////////////////
  // Clocks to select //
  //////////////////////
  // doc async
  /// Clocks to multiplex, positive edge triggered
  input  wire     i_clk[NumClocks],
  /// Output selected clock
  output wire     o_clk
);
  //////////////////////////
  // Parameter Sanitation //
  //////////////////////////
  if (NumClocks < 2)                  $fatal(1, "Parameter: 'NumClocks' must be a least 2;");
  if (ClkActiveResetIdx >= NumClocks) $fatal(1, "Parameter: 'ClkActiveResetIdx' must be smaller than 'NumClocks;'");

  // We need a small FSM to slow down the switching
  typedef enum logic[1:0] {
    ClkIsOff,
    TurnClkOn,
    ClkIsOn,
    TurnClkOff
  } state_e;

  /////////////
  // Signals //
  /////////////
  state_e  state_d, state_q;
  logic    update_state;
  select_t select_q;
  logic    update_select;

  logic [NumClocks-1:0] oht_slice_enable;
  logic                 slice_enable;
  logic [NumClocks-1:0] slice_active;
  logic                 any_slice_active;

  wire clk[NumClocks];

  /////////////////
  // Control FSM //
  /////////////////
  always_comb update_select    = (state_q == ClkIsOff) & update_state;
  always_comb slice_enable     =  state_q inside {TurnClkOn, ClkIsOn};
  always_comb oht_slice_enable = NumClocks'(slice_enable) << select_q;
  always_comb any_slice_active = |slice_active;
  always_comb o_active         =  slice_active;
  always_comb o_is_on          =  state_q inside {ClkIsOn};

  always_comb begin
    // The FSM is a cycle, so default points to the next state
    // Wraps around when end is reached
    state_d = state_q;

    unique case (state_q)
      ClkIsOff:   if (i_enable && !any_slice_active)       state_d = TurnClkOn;
      TurnClkOn:  if (any_slice_active)                    state_d = ClkIsOn;
      ClkIsOn:    if (!i_enable || (i_select != select_q)) state_d = TurnClkOff;
      TurnClkOff: if (!any_slice_active)                   state_d = ClkIsOff;
      default:                                             state_d = TurnClkOff;
    endcase
  end

  always_comb update_state = state_q != state_d;

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk_cfg or negedge i_rst_cfg_n) begin
    if (!i_rst_cfg_n)      state_q <= (ClkActiveReset ? ClkIsOn : ClkIsOff);
    else if (update_state) state_q <= state_d;
  end

  // DFFRL: D-Flip-Flop, asynchronous low reset, load enable
  always_ff @(posedge i_clk_cfg or negedge i_rst_cfg_n) begin
    if (!i_rst_cfg_n)       select_q <= select_t'(0);
    else if (update_select) select_q <= i_select;
  end

  /////////////////////////////////////////////////
  // Snynchonization Slice for each clock domain //
  /////////////////////////////////////////////////
  for (genvar clk_idx = 0; unsigned'(clk_idx) < NumClocks; clk_idx++) begin : gen_slice
    localparam bit SliceActiveReset = (unsigned'(clk_idx) == ClkActiveResetIdx) && ClkActiveReset;

    axe_ccl_clk_mux_slice #(
      .SyncStages    (SyncStages),
      .ClkActiveReset(SliceActiveReset)
    ) u_clk_mux_slice (
      .i_clk_cfg,
      .i_rst_cfg_n,
      .i_test_mode,
      .i_enable   (oht_slice_enable[clk_idx]),
      .o_active   (slice_active[clk_idx]),
      .i_clk      (i_clk[clk_idx]),
      .o_clk      (clk[clk_idx])
    );
  end

  ///////////////////////////////////////////////
  // Output or tree (buffer is included there) //
  ///////////////////////////////////////////////
  axe_ccl_clk_or_tree #(
    .NumClocks(NumClocks)
  ) u_clk_or (
    .i_clk(clk),
    .o_clk
  );

  ////////////////
  // Assertions //
  ////////////////
  `ifndef SYNTHESIS
  `ifdef ASSERTIONS_ON

  property p_signal_is_onehot(onehot_signal);
    @(posedge i_clk_cfg)
    $onehot0(onehot_signal);
  endproperty : p_signal_is_onehot

  check_p_oht_slice_enable_is_onehot : assert property (p_signal_is_onehot(oht_slice_enable));
  check_p_slice_active_is_onehot : assert property (p_signal_is_onehot(slice_active));

  `endif
  `endif
endmodule


/// Synchronization slice for axe_ccl_clk_mux
///
module axe_ccl_clk_mux_slice #(
  /// Synchronizer stages
  parameter int unsigned SyncStages = 3,
  /// Clock is active during Reset
  parameter bit          ClkActiveReset = 1'b0
)(
  /// Configuraion Clock, positive edge triggered
  input  wire  i_clk_cfg,
  /// Asynchronous reset, active low
  input  wire  i_rst_cfg_n,
  /// Test mode enable, opens the clock gate
  input  logic i_test_mode,
  /// Enable the downstream clock, active low
  input  logic i_enable,
  /// The downstream clock is active, active low
  output logic o_active,
  /// Input clock, positive edge triggered
  input  wire  i_clk,
  /// Output clock, positive edge triggered
  output wire  o_clk
);
  ///////////////////////////////////////
  // Reset synchronization into domain //
  ///////////////////////////////////////
  wire rst_n;

  axe_ccl_rst_n_sync #(
    .SyncStages(SyncStages)
  ) u_rst_sync (
    .i_clk,
    .i_rst_n    (i_rst_cfg_n),
    .i_test_mode,
    .o_rst_n    (rst_n)
  );

  //////////////////////////////////////////
  // Input flop to shield enable glicthes //
  //////////////////////////////////////////
  logic enable_q;
  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk_cfg or negedge i_rst_cfg_n) begin
    if (!i_rst_cfg_n) enable_q <= ClkActiveReset;
    else              enable_q <= i_enable;
  end

  /////////////////////////////////////
  // Synchronization into clk Domain //
  /////////////////////////////////////
  logic enable;

  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(ClkActiveReset)
  ) u_sync_enable (
    .i_clk,
    .i_rst_n(rst_n),
    .i_d    (enable_q),
    .o_q    (enable)
  );

  /////////////////////////////////////////////
  // The gate for the respective clock       //
  /////////////////////////////////////////////
  axe_tcl_clk_gating u_clk_gate (
    .i_clk,
    .i_en     (enable),
    .i_test_en(1'b0),
    .o_clk
  );

  //////////////////////////////////////////
  // Back synchronization into cfg Domain //
  // Additional delay Flop to prevent     //
  // Sync glitches propagating to CFG     //
  //////////////////////////////////////////
  logic active_q;

  // DFFR: D-Flip-Flop, asynchronous low reset
  always_ff @(posedge i_clk or negedge rst_n) begin
    if (!rst_n) active_q <= ClkActiveReset;
    else        active_q <= enable;
  end

  axe_tcl_seq_sync #(
    .SyncStages(SyncStages),
    .ResetValue(ClkActiveReset)
  ) u_sync_active (
    .i_clk  (i_clk_cfg),
    .i_rst_n(i_rst_cfg_n),
    .i_d    (active_q),
    .o_q    (o_active)
  );
endmodule
