/// Description: APU Power management unit handling AXI fabric automatic clock gating
/// - handle merging/dispatching of multiple Q-channels
module apu_axi_power_management_unit #(
  /// Number of supported AXI managers
  parameter int unsigned DEVICE_WIDTH = 3,
  /// Before gating counter width
  parameter int unsigned IDLE_DELAY_WIDTH = 4
) (
  /// Fast bus clock
  input wire i_clk,
  input wire i_rst_n,
  output wire o_clk,

  /// DFT
  input logic i_test_en,

  /// CSR status
  input  logic                        i_low_power_en,
  input  logic [IDLE_DELAY_WIDTH-1:0] i_low_power_idle_delay,

  /////////////////////////
  // Low Power Interface //
  /////////////////////////
  /// QREQn
  output logic [DEVICE_WIDTH-1:0] o_devices_qreq_n,
  /// QDENY
  input  logic [DEVICE_WIDTH-1:0] i_devices_qdeny,
  /// QACCEPTn
  input  logic [DEVICE_WIDTH-1:0] i_devices_qaccept_n,
  /// QACTIVE
  input  logic [DEVICE_WIDTH-1:0] i_devices_qactive
);

  // Dispatch Qreq
  logic qreq_n;

  always_comb o_devices_qreq_n = {DEVICE_WIDTH{qreq_n}};


  // Merge Q-channels
  logic qdeny;
  logic qaccept_n;
  logic qactive;

  always_comb qdeny     = |i_devices_qdeny;
  always_comb qaccept_n = |i_devices_qaccept_n;
  always_comb qactive   = |i_devices_qactive;


  axe_ccl_clk_lp_control #(
    .IdleDelayW(IDLE_DELAY_WIDTH)
  ) u_clk_lp_control (
    ///////////////////
    // Configuration //
    ///////////////////
    /// Clock, positive edge triggered
    .i_clk,
    /// Asynchronous reset
    .i_rst_n,
    /// Clock_gate bypass enable
    .i_scan_en(i_test_en),

    /// Low Power enable
    .i_low_power_en,
    /// Low Power active, clock is gated when set
    .o_low_power_active(),
    /// Low Power idle delay, wait this amount of cycles before going into low power state
    .i_low_power_idle_delay,

    /////////////////////////
    // Low Power Interface //
    /////////////////////////
    /// QREQn
    .o_qreq_n(qreq_n),
    /// QDENY
    .i_qdeny(qdeny),
    /// QACCEPTn
    .i_qaccept_n(qaccept_n),
    /// QACTIVE
    .i_qactive(qactive),

    /// Output gated clock
    .o_clk
  );

endmodule
