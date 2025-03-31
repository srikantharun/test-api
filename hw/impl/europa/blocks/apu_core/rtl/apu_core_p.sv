module apu_core_p #(
    localparam int unsigned BHT_WIDTH = apu_pkg::AX65_BHT_WIDTH,
    localparam int unsigned DCACHE_WIDTH = apu_pkg::AX65_DCACHE_WIDTH,
    localparam int unsigned ICACHE_WIDTH = apu_pkg::AX65_ICACHE_WIDTH,
    localparam int unsigned L2_WIDTH = apu_pkg::AX65_L2_WIDTH,
    localparam int unsigned SINK_WIDTH = apu_pkg::AX65_SINK_WIDTH,
    localparam int unsigned SOURCE_WIDTH = apu_pkg::AX65_SOURCE_WIDTH,
    localparam int unsigned CTRL_IN_WIDTH = apu_pkg::AX65_CTRL_IN_WIDTH,
    localparam int unsigned CTRL_OUT_WIDTH = apu_pkg::AX65_CTRL_OUT_WIDTH
) (
    input wire i_clk,
    input wire i_rst_n,

    // Core clocks management
    input  logic i_core_clk_enable,
    input  logic i_core_dcu_clk_enable,

    // JTAG
    input  wire  ijtag_tck,
    input  wire  ijtag_reset,
    input  logic ijtag_sel,
    input  logic ijtag_ue,
    input  logic ijtag_se,
    input  logic ijtag_ce,
    input  logic ijtag_si,
    output logic ijtag_so,
    // DFT
    input  wire  test_clk,
    input  logic test_mode,
    input  logic edt_update,
    input  logic scan_en,
    input  logic [11:0] scan_in,
    output logic [11:0] scan_out,
    // BIST
    input  wire  bisr_clk,
    input  wire  bisr_reset,
    input  logic bisr_shift_en,
    input  logic bisr_si,
    output logic bisr_so,

    //////////////////////////////////////////////
    /// CORE sigs
    //////////////////////////////////////////////
    // Coherency
    input logic i_coherent_state,
    output logic o_coherent_enable,

    // TileLink-C DCU manager
    // TileLink chan A
    output logic [39:0] o_dcu_a_address,
    output logic o_dcu_a_corrupt,
    output logic [255:0] o_dcu_a_data,
    output logic [31:0] o_dcu_a_mask,
    output logic [2:0] o_dcu_a_opcode,
    output logic [2:0] o_dcu_a_param,
    output logic [2:0] o_dcu_a_size,
    output logic [SOURCE_WIDTH - 1:0] o_dcu_a_source,
    output logic [11:0] o_dcu_a_user,
    input logic i_dcu_a_ready,
    output logic o_dcu_a_valid,
    // TileLink chan B
    input logic [39:0] i_dcu_b_address,
    input logic i_dcu_b_corrupt,
    input logic [255:0] i_dcu_b_data,
    input logic [31:0] i_dcu_b_mask,
    input logic [2:0] i_dcu_b_opcode,
    input logic [2:0] i_dcu_b_param,
    input logic [2:0] i_dcu_b_size,
    input logic [SOURCE_WIDTH - 1:0] i_dcu_b_source,
    output logic o_dcu_b_ready,
    input logic i_dcu_b_valid,
    // TileLink chan C
    output logic [39:0] o_dcu_c_address,
    output logic o_dcu_c_corrupt,
    output logic [255:0] o_dcu_c_data,
    output logic [2:0] o_dcu_c_opcode,
    output logic [2:0] o_dcu_c_param,
    output logic [2:0] o_dcu_c_size,
    output logic [SOURCE_WIDTH - 1:0] o_dcu_c_source,
    output logic [7:0] o_dcu_c_user,
    input logic i_dcu_c_ready,
    output logic o_dcu_c_valid,
    // TileLink chan D
    input logic i_dcu_d_corrupt,
    input logic [255:0] i_dcu_d_data,
    input logic i_dcu_d_denied,
    input logic [2:0] i_dcu_d_opcode,
    input logic [1:0] i_dcu_d_param,
    input logic [2:0] i_dcu_d_size,
    input logic [SINK_WIDTH - 1:0] i_dcu_d_sink,
    input logic [SOURCE_WIDTH - 1:0] i_dcu_d_source,
    input logic [5:0] i_dcu_d_user,
    output logic o_dcu_d_ready,
    input logic i_dcu_d_valid,
    // TileLink chan E
    output logic [SINK_WIDTH - 1:0] o_dcu_e_sink,
    input logic i_dcu_e_ready,
    output logic o_dcu_e_valid,

    // TileLink-U ICU manager
    // TileLink chan A
    output logic [39:0] o_icu_a_address,
    output logic o_icu_a_corrupt,
    output logic [255:0] o_icu_a_data,
    output logic [31:0] o_icu_a_mask,
    output logic [2:0] o_icu_a_opcode,
    output logic [2:0] o_icu_a_param,
    output logic [2:0] o_icu_a_size,
    output logic [SOURCE_WIDTH - 1:0] o_icu_a_source,
    output logic [11:0] o_icu_a_user,
    input logic i_icu_a_ready,
    output logic o_icu_a_valid,
    // TileLink chan D
    input logic i_icu_d_corrupt,
    input logic [255:0] i_icu_d_data,
    input logic i_icu_d_denied,
    input logic [2:0] i_icu_d_opcode,
    input logic [1:0] i_icu_d_param,
    input logic [2:0] i_icu_d_size,
    input logic [SINK_WIDTH - 1:0] i_icu_d_sink,
    input logic [SOURCE_WIDTH - 1:0] i_icu_d_source,
    input logic [5:0] i_icu_d_user,
    output logic o_icu_d_ready,
    input logic i_icu_d_valid,

    // AXI mpipe manager
    // AXI write address channel
    output logic [39:0] o_mpipe_axi_m_awaddr,
    output logic [1:0] o_mpipe_axi_m_awburst,
    output logic [3:0] o_mpipe_axi_m_awcache,
    output logic [4:0] o_mpipe_axi_m_awid,
    output logic [7:0] o_mpipe_axi_m_awlen,
    output logic o_mpipe_axi_m_awlock,
    output logic [2:0] o_mpipe_axi_m_awprot,
    output logic [2:0] o_mpipe_axi_m_awsize,
    input logic i_mpipe_axi_m_awready,
    output logic o_mpipe_axi_m_awvalid,
    // AXI write data channel
    output logic [63:0] o_mpipe_axi_m_wdata,
    output logic o_mpipe_axi_m_wlast,
    output logic [(64 / 8) - 1:0] o_mpipe_axi_m_wstrb,
    input logic i_mpipe_axi_m_wready,
    output logic o_mpipe_axi_m_wvalid,
    // AXI write response channel
    input logic [4:0] i_mpipe_axi_m_bid,
    input logic [1:0] i_mpipe_axi_m_bresp,
    output logic o_mpipe_axi_m_bready,
    input logic i_mpipe_axi_m_bvalid,
    // AXI read address channel
    output logic [39:0] o_mpipe_axi_m_araddr,
    output logic [1:0] o_mpipe_axi_m_arburst,
    output logic [3:0] o_mpipe_axi_m_arcache,
    output logic [4:0] o_mpipe_axi_m_arid,
    output logic [7:0] o_mpipe_axi_m_arlen,
    output logic o_mpipe_axi_m_arlock,
    output logic [2:0] o_mpipe_axi_m_arprot,
    output logic [2:0] o_mpipe_axi_m_arsize,
    input logic i_mpipe_axi_m_arready,
    output logic o_mpipe_axi_m_arvalid,
    // AXI read data/response channel
    input logic [63:0] i_mpipe_axi_m_rdata,
    input logic [4:0] i_mpipe_axi_m_rid,
    input logic i_mpipe_axi_m_rlast,
    input logic [1:0] i_mpipe_axi_m_rresp,
    output logic o_mpipe_axi_m_rready,
    input logic i_mpipe_axi_m_rvalid,

    // Misc live cfg
    input logic i_dcache_disable_init,
    input logic i_icache_disable_init,
    input logic [47:0] i_reset_vector,
    input logic [63:0] i_hart_id,

    // Debug sigs
    input logic i_debugint,
    input logic i_resethaltreq,
    output logic o_hart_unavail,
    output logic o_hart_under_reset,

    // Status sigs
    input logic i_meip,
    input logic i_msip,
    input logic i_mtip,
    input logic i_nmi,
    input logic i_seip,
    output logic o_wfi_mode,
    output logic o_stoptime,

    // SRAM impl signals
    input logic [CTRL_IN_WIDTH - 1:0] i_core_ctrl,
    output logic [CTRL_OUT_WIDTH - 1:0] o_core_ctrl
);

  // Clock gates
  wire core_clk;
  wire core_dcu_clk;

  axe_tcl_clk_gating u_core_clk_gate (
    .i_clk(i_clk),
    .i_en(i_core_clk_enable),
    .i_test_en('0),
    .o_clk(core_clk)
  );

  axe_tcl_clk_gating u_core_dcu_clk_gate (
    .i_clk(i_clk),
    .i_en(i_core_dcu_clk_enable),
    .i_test_en('0),
    .o_clk(core_dcu_clk)
  );

  // Chain SRAM impl sigs
  axe_tcl_sram_pkg::impl_inp_t i_local_ctrl;

  always_comb begin
    i_local_ctrl = i_core_ctrl;

    // DFT
    i_local_ctrl.se = scan_en;
  end

  localparam int unsigned NUM_SRAMS = BHT_WIDTH + ICACHE_WIDTH * 2 + DCACHE_WIDTH * 3 + L2_WIDTH * 5;

  axe_tcl_sram_pkg::impl_inp_t [NUM_SRAMS - 1:0] i_all_ctrl;
  axe_tcl_sram_pkg::impl_oup_t [NUM_SRAMS - 1:0] o_all_ctrl;

  logic [BHT_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_bht_ctrl;
  logic [BHT_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_bht_ctrl;
  logic [ICACHE_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_icache_data_ctrl;
  logic [ICACHE_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_icache_data_ctrl;
  logic [ICACHE_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_icache_tag_ctrl;
  logic [ICACHE_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_icache_tag_ctrl;
  logic [DCACHE_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_dcache_data_ctrl;
  logic [DCACHE_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_dcache_data_ctrl;
  logic [DCACHE_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_dcache_tag_ctrl;
  logic [DCACHE_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_dcache_tag_ctrl;
  logic [DCACHE_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_dcache_dtag_ctrl;
  logic [DCACHE_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_dcache_dtag_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_l2btb_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_l2btb_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_l2itlb_tag_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_l2itlb_tag_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_l2itlb_data_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_l2itlb_data_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_l2dtlb_tag_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_l2dtlb_tag_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_IN_WIDTH - 1:0] i_l2dtlb_data_ctrl;
  logic [L2_WIDTH - 1:0][CTRL_OUT_WIDTH - 1:0] o_l2dtlb_data_ctrl;

  always_comb {
    i_bht_ctrl,
    i_icache_data_ctrl,
    i_icache_tag_ctrl,
    i_dcache_data_ctrl,
    i_dcache_tag_ctrl,
    i_dcache_dtag_ctrl,
    i_l2btb_ctrl,
    i_l2itlb_tag_ctrl,
    i_l2itlb_data_ctrl,
    i_l2dtlb_tag_ctrl,
    i_l2dtlb_data_ctrl
  } = i_all_ctrl;

  always_comb o_all_ctrl = {
    o_bht_ctrl,
    o_icache_data_ctrl,
    o_icache_tag_ctrl,
    o_dcache_data_ctrl,
    o_dcache_tag_ctrl,
    o_dcache_dtag_ctrl,
    o_l2btb_ctrl,
    o_l2itlb_tag_ctrl,
    o_l2itlb_data_ctrl,
    o_l2dtlb_tag_ctrl,
    o_l2dtlb_data_ctrl
  };

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(NUM_SRAMS)
  ) u_sram_cfg (
    .i_s(i_local_ctrl),
    .o_s(o_core_ctrl),
    .o_m(i_all_ctrl),
    .i_m(o_all_ctrl)
  );

  logic [143:0] unused_mbist_rdata;

  ax65_core_wrapper #(
    .BHT_WIDTH(BHT_WIDTH),
    .DCACHE_WIDTH(DCACHE_WIDTH),
    .ICACHE_WIDTH(ICACHE_WIDTH),
    .L2_WIDTH(L2_WIDTH),
    .SINK_WIDTH(SINK_WIDTH),
    .SOURCE_WIDTH(SOURCE_WIDTH),
    .CTRL_IN_WIDTH(CTRL_IN_WIDTH),
    .CTRL_OUT_WIDTH(CTRL_OUT_WIDTH)
  ) u_ax65_core_wrapper (
    .i_clk(core_clk),
    .i_rst_n,
    .i_dcu_clk(core_dcu_clk),
    .i_scan_enable('0),
    .i_test_mode('0),
    // Unused mbist
    .i_mbist_addr('0),
    .i_mbist_bwe('0),
    .i_mbist_en('0),
    .i_mbist_ramsel('0),
    .o_mbist_rdata(unused_mbist_rdata),
    .i_mbist_wdata('0),
    .i_mbist_we('0),
    // Unused hart_halted
    .o_hart_halted(),
    // Unused trace
    .o_trace_cause(),
    .o_trace_context(),
    .o_trace_ctype(),
    .i_trace_enabled('0),
    .o_trace_halted(),
    .o_trace_iaddr(),
    .o_trace_ilastsize(),
    .o_trace_iretire(),
    .o_trace_itype(),
    .o_trace_priv(),
    .o_trace_reset(),
    .i_trace_stall('0),
    .o_trace_trigger(),
    .o_trace_tval(),
    .*
  );

endmodule
