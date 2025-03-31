module apu_l2c_p #(
    localparam int unsigned CORE_WIDTH = apu_pkg::AX65_MAX_CORE_WIDTH,
    localparam int unsigned L2C_BANK_WIDTH = apu_pkg::AX65_L2C_BANK_WIDTH,
    localparam int unsigned L2C_BANK_DATA_WIDTH = apu_pkg::AX65_L2C_BANK_DATA_WIDTH,
    localparam int unsigned L2C_BANK_TAG_WIDTH = apu_pkg::AX65_L2C_BANK_TAG_WIDTH,
    localparam int unsigned SINK_WIDTH = apu_pkg::AX65_SINK_WIDTH,
    localparam int unsigned SOURCE_WIDTH = apu_pkg::AX65_SOURCE_WIDTH,
    localparam int unsigned CTRL_IN_WIDTH = apu_pkg::AX65_CTRL_IN_WIDTH,
    localparam int unsigned CTRL_OUT_WIDTH = apu_pkg::AX65_CTRL_OUT_WIDTH
) (
    /// Fast l2 clock
    input wire i_clk,
    input wire i_rst_n,
    /// Fast AXI clock
    input wire i_aclk,
    input wire i_arst_n,
    /// l2 clock div by 2
    input wire  i_l2c_banks_clk,
    input logic i_l2c_banks_clk_en,

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
    /// CORES sigs
    //////////////////////////////////////////////
    input logic i_core0_coherent_enable,
    output logic o_core0_coherent_state,
    input logic [39:0] i_core0_m0_a_address,
    input logic i_core0_m0_a_corrupt,
    input logic [255:0] i_core0_m0_a_data,
    input logic [31:0] i_core0_m0_a_mask,
    input logic [2:0] i_core0_m0_a_opcode,
    input logic [2:0] i_core0_m0_a_param,
    input logic [2:0] i_core0_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core0_m0_a_source,
    input logic [11:0] i_core0_m0_a_user,
    output logic o_core0_m0_a_ready,
    input logic i_core0_m0_a_valid,
    output logic [39:0] o_core0_m0_b_address,
    output logic o_core0_m0_b_corrupt,
    output logic [255:0] o_core0_m0_b_data,
    output logic [31:0] o_core0_m0_b_mask,
    output logic [2:0] o_core0_m0_b_opcode,
    output logic [2:0] o_core0_m0_b_param,
    output logic [2:0] o_core0_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core0_m0_b_source,
    input logic i_core0_m0_b_ready,
    output logic o_core0_m0_b_valid,
    input logic [39:0] i_core0_m0_c_address,
    input logic i_core0_m0_c_corrupt,
    input logic [255:0] i_core0_m0_c_data,
    input logic [2:0] i_core0_m0_c_opcode,
    input logic [2:0] i_core0_m0_c_param,
    input logic [2:0] i_core0_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core0_m0_c_source,
    input logic [7:0] i_core0_m0_c_user,
    output logic o_core0_m0_c_ready,
    input logic i_core0_m0_c_valid,
    output logic o_core0_m0_d_corrupt,
    output logic [255:0] o_core0_m0_d_data,
    output logic o_core0_m0_d_denied,
    output logic [2:0] o_core0_m0_d_opcode,
    output logic [1:0] o_core0_m0_d_param,
    output logic [2:0] o_core0_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core0_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core0_m0_d_source,
    output logic [5:0] o_core0_m0_d_user,
    input logic i_core0_m0_d_ready,
    output logic o_core0_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core0_m0_e_sink,
    output logic o_core0_m0_e_ready,
    input logic i_core0_m0_e_valid,
    input logic [39:0] i_core0_m1_axi_s_araddr,
    input logic [1:0] i_core0_m1_axi_s_arburst,
    input logic [3:0] i_core0_m1_axi_s_arcache,
    input logic [4:0] i_core0_m1_axi_s_arid,
    input logic [7:0] i_core0_m1_axi_s_arlen,
    input logic i_core0_m1_axi_s_arlock,
    input logic [2:0] i_core0_m1_axi_s_arprot,
    input logic [2:0] i_core0_m1_axi_s_arsize,
    output logic o_core0_m1_axi_s_arready,
    input logic i_core0_m1_axi_s_arvalid,
    input logic [39:0] i_core0_m1_axi_s_awaddr,
    input logic [1:0] i_core0_m1_axi_s_awburst,
    input logic [3:0] i_core0_m1_axi_s_awcache,
    input logic [4:0] i_core0_m1_axi_s_awid,
    input logic [7:0] i_core0_m1_axi_s_awlen,
    input logic i_core0_m1_axi_s_awlock,
    input logic [2:0] i_core0_m1_axi_s_awprot,
    input logic [2:0] i_core0_m1_axi_s_awsize,
    output logic o_core0_m1_axi_s_awready,
    input logic i_core0_m1_axi_s_awvalid,
    output logic [4:0] o_core0_m1_axi_s_bid,
    output logic [1:0] o_core0_m1_axi_s_bresp,
    input logic i_core0_m1_axi_s_bready,
    output logic o_core0_m1_axi_s_bvalid,
    output logic [63:0] o_core0_m1_axi_s_rdata,
    output logic [4:0] o_core0_m1_axi_s_rid,
    output logic o_core0_m1_axi_s_rlast,
    output logic [1:0] o_core0_m1_axi_s_rresp,
    input logic i_core0_m1_axi_s_rready,
    output logic o_core0_m1_axi_s_rvalid,
    input logic [63:0] i_core0_m1_axi_s_wdata,
    input logic i_core0_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core0_m1_axi_s_wstrb,
    output logic o_core0_m1_axi_s_wready,
    input logic i_core0_m1_axi_s_wvalid,
    input logic [39:0] i_core0_m2_a_address,
    input logic i_core0_m2_a_corrupt,
    input logic [255:0] i_core0_m2_a_data,
    input logic [31:0] i_core0_m2_a_mask,
    input logic [2:0] i_core0_m2_a_opcode,
    input logic [2:0] i_core0_m2_a_param,
    input logic [2:0] i_core0_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core0_m2_a_source,
    input logic [11:0] i_core0_m2_a_user,
    output logic o_core0_m2_a_ready,
    input logic i_core0_m2_a_valid,
    output logic o_core0_m2_d_corrupt,
    output logic [255:0] o_core0_m2_d_data,
    output logic o_core0_m2_d_denied,
    output logic [2:0] o_core0_m2_d_opcode,
    output logic [1:0] o_core0_m2_d_param,
    output logic [2:0] o_core0_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core0_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core0_m2_d_source,
    output logic [5:0] o_core0_m2_d_user,
    input logic i_core0_m2_d_ready,
    output logic o_core0_m2_d_valid,

    input logic i_core1_coherent_enable,
    output logic o_core1_coherent_state,
    input logic [39:0] i_core1_m0_a_address,
    input logic i_core1_m0_a_corrupt,
    input logic [255:0] i_core1_m0_a_data,
    input logic [31:0] i_core1_m0_a_mask,
    input logic [2:0] i_core1_m0_a_opcode,
    input logic [2:0] i_core1_m0_a_param,
    input logic [2:0] i_core1_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core1_m0_a_source,
    input logic [11:0] i_core1_m0_a_user,
    output logic o_core1_m0_a_ready,
    input logic i_core1_m0_a_valid,
    output logic [39:0] o_core1_m0_b_address,
    output logic o_core1_m0_b_corrupt,
    output logic [255:0] o_core1_m0_b_data,
    output logic [31:0] o_core1_m0_b_mask,
    output logic [2:0] o_core1_m0_b_opcode,
    output logic [2:0] o_core1_m0_b_param,
    output logic [2:0] o_core1_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core1_m0_b_source,
    input logic i_core1_m0_b_ready,
    output logic o_core1_m0_b_valid,
    input logic [39:0] i_core1_m0_c_address,
    input logic i_core1_m0_c_corrupt,
    input logic [255:0] i_core1_m0_c_data,
    input logic [2:0] i_core1_m0_c_opcode,
    input logic [2:0] i_core1_m0_c_param,
    input logic [2:0] i_core1_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core1_m0_c_source,
    input logic [7:0] i_core1_m0_c_user,
    output logic o_core1_m0_c_ready,
    input logic i_core1_m0_c_valid,
    output logic o_core1_m0_d_corrupt,
    output logic [255:0] o_core1_m0_d_data,
    output logic o_core1_m0_d_denied,
    output logic [2:0] o_core1_m0_d_opcode,
    output logic [1:0] o_core1_m0_d_param,
    output logic [2:0] o_core1_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core1_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core1_m0_d_source,
    output logic [5:0] o_core1_m0_d_user,
    input logic i_core1_m0_d_ready,
    output logic o_core1_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core1_m0_e_sink,
    output logic o_core1_m0_e_ready,
    input logic i_core1_m0_e_valid,
    input logic [39:0] i_core1_m1_axi_s_araddr,
    input logic [1:0] i_core1_m1_axi_s_arburst,
    input logic [3:0] i_core1_m1_axi_s_arcache,
    input logic [4:0] i_core1_m1_axi_s_arid,
    input logic [7:0] i_core1_m1_axi_s_arlen,
    input logic i_core1_m1_axi_s_arlock,
    input logic [2:0] i_core1_m1_axi_s_arprot,
    input logic [2:0] i_core1_m1_axi_s_arsize,
    output logic o_core1_m1_axi_s_arready,
    input logic i_core1_m1_axi_s_arvalid,
    input logic [39:0] i_core1_m1_axi_s_awaddr,
    input logic [1:0] i_core1_m1_axi_s_awburst,
    input logic [3:0] i_core1_m1_axi_s_awcache,
    input logic [4:0] i_core1_m1_axi_s_awid,
    input logic [7:0] i_core1_m1_axi_s_awlen,
    input logic i_core1_m1_axi_s_awlock,
    input logic [2:0] i_core1_m1_axi_s_awprot,
    input logic [2:0] i_core1_m1_axi_s_awsize,
    output logic o_core1_m1_axi_s_awready,
    input logic i_core1_m1_axi_s_awvalid,
    output logic [4:0] o_core1_m1_axi_s_bid,
    output logic [1:0] o_core1_m1_axi_s_bresp,
    input logic i_core1_m1_axi_s_bready,
    output logic o_core1_m1_axi_s_bvalid,
    output logic [63:0] o_core1_m1_axi_s_rdata,
    output logic [4:0] o_core1_m1_axi_s_rid,
    output logic o_core1_m1_axi_s_rlast,
    output logic [1:0] o_core1_m1_axi_s_rresp,
    input logic i_core1_m1_axi_s_rready,
    output logic o_core1_m1_axi_s_rvalid,
    input logic [63:0] i_core1_m1_axi_s_wdata,
    input logic i_core1_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core1_m1_axi_s_wstrb,
    output logic o_core1_m1_axi_s_wready,
    input logic i_core1_m1_axi_s_wvalid,
    input logic [39:0] i_core1_m2_a_address,
    input logic i_core1_m2_a_corrupt,
    input logic [255:0] i_core1_m2_a_data,
    input logic [31:0] i_core1_m2_a_mask,
    input logic [2:0] i_core1_m2_a_opcode,
    input logic [2:0] i_core1_m2_a_param,
    input logic [2:0] i_core1_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core1_m2_a_source,
    input logic [11:0] i_core1_m2_a_user,
    output logic o_core1_m2_a_ready,
    input logic i_core1_m2_a_valid,
    output logic o_core1_m2_d_corrupt,
    output logic [255:0] o_core1_m2_d_data,
    output logic o_core1_m2_d_denied,
    output logic [2:0] o_core1_m2_d_opcode,
    output logic [1:0] o_core1_m2_d_param,
    output logic [2:0] o_core1_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core1_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core1_m2_d_source,
    output logic [5:0] o_core1_m2_d_user,
    input logic i_core1_m2_d_ready,
    output logic o_core1_m2_d_valid,

    input logic i_core2_coherent_enable,
    output logic o_core2_coherent_state,
    input logic [39:0] i_core2_m0_a_address,
    input logic i_core2_m0_a_corrupt,
    input logic [255:0] i_core2_m0_a_data,
    input logic [31:0] i_core2_m0_a_mask,
    input logic [2:0] i_core2_m0_a_opcode,
    input logic [2:0] i_core2_m0_a_param,
    input logic [2:0] i_core2_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core2_m0_a_source,
    input logic [11:0] i_core2_m0_a_user,
    output logic o_core2_m0_a_ready,
    input logic i_core2_m0_a_valid,
    output logic [39:0] o_core2_m0_b_address,
    output logic o_core2_m0_b_corrupt,
    output logic [255:0] o_core2_m0_b_data,
    output logic [31:0] o_core2_m0_b_mask,
    output logic [2:0] o_core2_m0_b_opcode,
    output logic [2:0] o_core2_m0_b_param,
    output logic [2:0] o_core2_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core2_m0_b_source,
    input logic i_core2_m0_b_ready,
    output logic o_core2_m0_b_valid,
    input logic [39:0] i_core2_m0_c_address,
    input logic i_core2_m0_c_corrupt,
    input logic [255:0] i_core2_m0_c_data,
    input logic [2:0] i_core2_m0_c_opcode,
    input logic [2:0] i_core2_m0_c_param,
    input logic [2:0] i_core2_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core2_m0_c_source,
    input logic [7:0] i_core2_m0_c_user,
    output logic o_core2_m0_c_ready,
    input logic i_core2_m0_c_valid,
    output logic o_core2_m0_d_corrupt,
    output logic [255:0] o_core2_m0_d_data,
    output logic o_core2_m0_d_denied,
    output logic [2:0] o_core2_m0_d_opcode,
    output logic [1:0] o_core2_m0_d_param,
    output logic [2:0] o_core2_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core2_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core2_m0_d_source,
    output logic [5:0] o_core2_m0_d_user,
    input logic i_core2_m0_d_ready,
    output logic o_core2_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core2_m0_e_sink,
    output logic o_core2_m0_e_ready,
    input logic i_core2_m0_e_valid,
    input logic [39:0] i_core2_m1_axi_s_araddr,
    input logic [1:0] i_core2_m1_axi_s_arburst,
    input logic [3:0] i_core2_m1_axi_s_arcache,
    input logic [4:0] i_core2_m1_axi_s_arid,
    input logic [7:0] i_core2_m1_axi_s_arlen,
    input logic i_core2_m1_axi_s_arlock,
    input logic [2:0] i_core2_m1_axi_s_arprot,
    input logic [2:0] i_core2_m1_axi_s_arsize,
    output logic o_core2_m1_axi_s_arready,
    input logic i_core2_m1_axi_s_arvalid,
    input logic [39:0] i_core2_m1_axi_s_awaddr,
    input logic [1:0] i_core2_m1_axi_s_awburst,
    input logic [3:0] i_core2_m1_axi_s_awcache,
    input logic [4:0] i_core2_m1_axi_s_awid,
    input logic [7:0] i_core2_m1_axi_s_awlen,
    input logic i_core2_m1_axi_s_awlock,
    input logic [2:0] i_core2_m1_axi_s_awprot,
    input logic [2:0] i_core2_m1_axi_s_awsize,
    output logic o_core2_m1_axi_s_awready,
    input logic i_core2_m1_axi_s_awvalid,
    output logic [4:0] o_core2_m1_axi_s_bid,
    output logic [1:0] o_core2_m1_axi_s_bresp,
    input logic i_core2_m1_axi_s_bready,
    output logic o_core2_m1_axi_s_bvalid,
    output logic [63:0] o_core2_m1_axi_s_rdata,
    output logic [4:0] o_core2_m1_axi_s_rid,
    output logic o_core2_m1_axi_s_rlast,
    output logic [1:0] o_core2_m1_axi_s_rresp,
    input logic i_core2_m1_axi_s_rready,
    output logic o_core2_m1_axi_s_rvalid,
    input logic [63:0] i_core2_m1_axi_s_wdata,
    input logic i_core2_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core2_m1_axi_s_wstrb,
    output logic o_core2_m1_axi_s_wready,
    input logic i_core2_m1_axi_s_wvalid,
    input logic [39:0] i_core2_m2_a_address,
    input logic i_core2_m2_a_corrupt,
    input logic [255:0] i_core2_m2_a_data,
    input logic [31:0] i_core2_m2_a_mask,
    input logic [2:0] i_core2_m2_a_opcode,
    input logic [2:0] i_core2_m2_a_param,
    input logic [2:0] i_core2_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core2_m2_a_source,
    input logic [11:0] i_core2_m2_a_user,
    output logic o_core2_m2_a_ready,
    input logic i_core2_m2_a_valid,
    output logic o_core2_m2_d_corrupt,
    output logic [255:0] o_core2_m2_d_data,
    output logic o_core2_m2_d_denied,
    output logic [2:0] o_core2_m2_d_opcode,
    output logic [1:0] o_core2_m2_d_param,
    output logic [2:0] o_core2_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core2_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core2_m2_d_source,
    output logic [5:0] o_core2_m2_d_user,
    input logic i_core2_m2_d_ready,
    output logic o_core2_m2_d_valid,

    input logic i_core3_coherent_enable,
    output logic o_core3_coherent_state,
    input logic [39:0] i_core3_m0_a_address,
    input logic i_core3_m0_a_corrupt,
    input logic [255:0] i_core3_m0_a_data,
    input logic [31:0] i_core3_m0_a_mask,
    input logic [2:0] i_core3_m0_a_opcode,
    input logic [2:0] i_core3_m0_a_param,
    input logic [2:0] i_core3_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core3_m0_a_source,
    input logic [11:0] i_core3_m0_a_user,
    output logic o_core3_m0_a_ready,
    input logic i_core3_m0_a_valid,
    output logic [39:0] o_core3_m0_b_address,
    output logic o_core3_m0_b_corrupt,
    output logic [255:0] o_core3_m0_b_data,
    output logic [31:0] o_core3_m0_b_mask,
    output logic [2:0] o_core3_m0_b_opcode,
    output logic [2:0] o_core3_m0_b_param,
    output logic [2:0] o_core3_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core3_m0_b_source,
    input logic i_core3_m0_b_ready,
    output logic o_core3_m0_b_valid,
    input logic [39:0] i_core3_m0_c_address,
    input logic i_core3_m0_c_corrupt,
    input logic [255:0] i_core3_m0_c_data,
    input logic [2:0] i_core3_m0_c_opcode,
    input logic [2:0] i_core3_m0_c_param,
    input logic [2:0] i_core3_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core3_m0_c_source,
    input logic [7:0] i_core3_m0_c_user,
    output logic o_core3_m0_c_ready,
    input logic i_core3_m0_c_valid,
    output logic o_core3_m0_d_corrupt,
    output logic [255:0] o_core3_m0_d_data,
    output logic o_core3_m0_d_denied,
    output logic [2:0] o_core3_m0_d_opcode,
    output logic [1:0] o_core3_m0_d_param,
    output logic [2:0] o_core3_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core3_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core3_m0_d_source,
    output logic [5:0] o_core3_m0_d_user,
    input logic i_core3_m0_d_ready,
    output logic o_core3_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core3_m0_e_sink,
    output logic o_core3_m0_e_ready,
    input logic i_core3_m0_e_valid,
    input logic [39:0] i_core3_m1_axi_s_araddr,
    input logic [1:0] i_core3_m1_axi_s_arburst,
    input logic [3:0] i_core3_m1_axi_s_arcache,
    input logic [4:0] i_core3_m1_axi_s_arid,
    input logic [7:0] i_core3_m1_axi_s_arlen,
    input logic i_core3_m1_axi_s_arlock,
    input logic [2:0] i_core3_m1_axi_s_arprot,
    input logic [2:0] i_core3_m1_axi_s_arsize,
    output logic o_core3_m1_axi_s_arready,
    input logic i_core3_m1_axi_s_arvalid,
    input logic [39:0] i_core3_m1_axi_s_awaddr,
    input logic [1:0] i_core3_m1_axi_s_awburst,
    input logic [3:0] i_core3_m1_axi_s_awcache,
    input logic [4:0] i_core3_m1_axi_s_awid,
    input logic [7:0] i_core3_m1_axi_s_awlen,
    input logic i_core3_m1_axi_s_awlock,
    input logic [2:0] i_core3_m1_axi_s_awprot,
    input logic [2:0] i_core3_m1_axi_s_awsize,
    output logic o_core3_m1_axi_s_awready,
    input logic i_core3_m1_axi_s_awvalid,
    output logic [4:0] o_core3_m1_axi_s_bid,
    output logic [1:0] o_core3_m1_axi_s_bresp,
    input logic i_core3_m1_axi_s_bready,
    output logic o_core3_m1_axi_s_bvalid,
    output logic [63:0] o_core3_m1_axi_s_rdata,
    output logic [4:0] o_core3_m1_axi_s_rid,
    output logic o_core3_m1_axi_s_rlast,
    output logic [1:0] o_core3_m1_axi_s_rresp,
    input logic i_core3_m1_axi_s_rready,
    output logic o_core3_m1_axi_s_rvalid,
    input logic [63:0] i_core3_m1_axi_s_wdata,
    input logic i_core3_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core3_m1_axi_s_wstrb,
    output logic o_core3_m1_axi_s_wready,
    input logic i_core3_m1_axi_s_wvalid,
    input logic [39:0] i_core3_m2_a_address,
    input logic i_core3_m2_a_corrupt,
    input logic [255:0] i_core3_m2_a_data,
    input logic [31:0] i_core3_m2_a_mask,
    input logic [2:0] i_core3_m2_a_opcode,
    input logic [2:0] i_core3_m2_a_param,
    input logic [2:0] i_core3_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core3_m2_a_source,
    input logic [11:0] i_core3_m2_a_user,
    output logic o_core3_m2_a_ready,
    input logic i_core3_m2_a_valid,
    output logic o_core3_m2_d_corrupt,
    output logic [255:0] o_core3_m2_d_data,
    output logic o_core3_m2_d_denied,
    output logic [2:0] o_core3_m2_d_opcode,
    output logic [1:0] o_core3_m2_d_param,
    output logic [2:0] o_core3_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core3_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core3_m2_d_source,
    output logic [5:0] o_core3_m2_d_user,
    input logic i_core3_m2_d_ready,
    output logic o_core3_m2_d_valid,

    input logic i_core4_coherent_enable,
    output logic o_core4_coherent_state,
    input logic [39:0] i_core4_m0_a_address,
    input logic i_core4_m0_a_corrupt,
    input logic [255:0] i_core4_m0_a_data,
    input logic [31:0] i_core4_m0_a_mask,
    input logic [2:0] i_core4_m0_a_opcode,
    input logic [2:0] i_core4_m0_a_param,
    input logic [2:0] i_core4_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core4_m0_a_source,
    input logic [11:0] i_core4_m0_a_user,
    output logic o_core4_m0_a_ready,
    input logic i_core4_m0_a_valid,
    output logic [39:0] o_core4_m0_b_address,
    output logic o_core4_m0_b_corrupt,
    output logic [255:0] o_core4_m0_b_data,
    output logic [31:0] o_core4_m0_b_mask,
    output logic [2:0] o_core4_m0_b_opcode,
    output logic [2:0] o_core4_m0_b_param,
    output logic [2:0] o_core4_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core4_m0_b_source,
    input logic i_core4_m0_b_ready,
    output logic o_core4_m0_b_valid,
    input logic [39:0] i_core4_m0_c_address,
    input logic i_core4_m0_c_corrupt,
    input logic [255:0] i_core4_m0_c_data,
    input logic [2:0] i_core4_m0_c_opcode,
    input logic [2:0] i_core4_m0_c_param,
    input logic [2:0] i_core4_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core4_m0_c_source,
    input logic [7:0] i_core4_m0_c_user,
    output logic o_core4_m0_c_ready,
    input logic i_core4_m0_c_valid,
    output logic o_core4_m0_d_corrupt,
    output logic [255:0] o_core4_m0_d_data,
    output logic o_core4_m0_d_denied,
    output logic [2:0] o_core4_m0_d_opcode,
    output logic [1:0] o_core4_m0_d_param,
    output logic [2:0] o_core4_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core4_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core4_m0_d_source,
    output logic [5:0] o_core4_m0_d_user,
    input logic i_core4_m0_d_ready,
    output logic o_core4_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core4_m0_e_sink,
    output logic o_core4_m0_e_ready,
    input logic i_core4_m0_e_valid,
    input logic [39:0] i_core4_m1_axi_s_araddr,
    input logic [1:0] i_core4_m1_axi_s_arburst,
    input logic [3:0] i_core4_m1_axi_s_arcache,
    input logic [4:0] i_core4_m1_axi_s_arid,
    input logic [7:0] i_core4_m1_axi_s_arlen,
    input logic i_core4_m1_axi_s_arlock,
    input logic [2:0] i_core4_m1_axi_s_arprot,
    input logic [2:0] i_core4_m1_axi_s_arsize,
    output logic o_core4_m1_axi_s_arready,
    input logic i_core4_m1_axi_s_arvalid,
    input logic [39:0] i_core4_m1_axi_s_awaddr,
    input logic [1:0] i_core4_m1_axi_s_awburst,
    input logic [3:0] i_core4_m1_axi_s_awcache,
    input logic [4:0] i_core4_m1_axi_s_awid,
    input logic [7:0] i_core4_m1_axi_s_awlen,
    input logic i_core4_m1_axi_s_awlock,
    input logic [2:0] i_core4_m1_axi_s_awprot,
    input logic [2:0] i_core4_m1_axi_s_awsize,
    output logic o_core4_m1_axi_s_awready,
    input logic i_core4_m1_axi_s_awvalid,
    output logic [4:0] o_core4_m1_axi_s_bid,
    output logic [1:0] o_core4_m1_axi_s_bresp,
    input logic i_core4_m1_axi_s_bready,
    output logic o_core4_m1_axi_s_bvalid,
    output logic [63:0] o_core4_m1_axi_s_rdata,
    output logic [4:0] o_core4_m1_axi_s_rid,
    output logic o_core4_m1_axi_s_rlast,
    output logic [1:0] o_core4_m1_axi_s_rresp,
    input logic i_core4_m1_axi_s_rready,
    output logic o_core4_m1_axi_s_rvalid,
    input logic [63:0] i_core4_m1_axi_s_wdata,
    input logic i_core4_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core4_m1_axi_s_wstrb,
    output logic o_core4_m1_axi_s_wready,
    input logic i_core4_m1_axi_s_wvalid,
    input logic [39:0] i_core4_m2_a_address,
    input logic i_core4_m2_a_corrupt,
    input logic [255:0] i_core4_m2_a_data,
    input logic [31:0] i_core4_m2_a_mask,
    input logic [2:0] i_core4_m2_a_opcode,
    input logic [2:0] i_core4_m2_a_param,
    input logic [2:0] i_core4_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core4_m2_a_source,
    input logic [11:0] i_core4_m2_a_user,
    output logic o_core4_m2_a_ready,
    input logic i_core4_m2_a_valid,
    output logic o_core4_m2_d_corrupt,
    output logic [255:0] o_core4_m2_d_data,
    output logic o_core4_m2_d_denied,
    output logic [2:0] o_core4_m2_d_opcode,
    output logic [1:0] o_core4_m2_d_param,
    output logic [2:0] o_core4_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core4_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core4_m2_d_source,
    output logic [5:0] o_core4_m2_d_user,
    input logic i_core4_m2_d_ready,
    output logic o_core4_m2_d_valid,

    input logic i_core5_coherent_enable,
    output logic o_core5_coherent_state,
    input logic [39:0] i_core5_m0_a_address,
    input logic i_core5_m0_a_corrupt,
    input logic [255:0] i_core5_m0_a_data,
    input logic [31:0] i_core5_m0_a_mask,
    input logic [2:0] i_core5_m0_a_opcode,
    input logic [2:0] i_core5_m0_a_param,
    input logic [2:0] i_core5_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core5_m0_a_source,
    input logic [11:0] i_core5_m0_a_user,
    output logic o_core5_m0_a_ready,
    input logic i_core5_m0_a_valid,
    output logic [39:0] o_core5_m0_b_address,
    output logic o_core5_m0_b_corrupt,
    output logic [255:0] o_core5_m0_b_data,
    output logic [31:0] o_core5_m0_b_mask,
    output logic [2:0] o_core5_m0_b_opcode,
    output logic [2:0] o_core5_m0_b_param,
    output logic [2:0] o_core5_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core5_m0_b_source,
    input logic i_core5_m0_b_ready,
    output logic o_core5_m0_b_valid,
    input logic [39:0] i_core5_m0_c_address,
    input logic i_core5_m0_c_corrupt,
    input logic [255:0] i_core5_m0_c_data,
    input logic [2:0] i_core5_m0_c_opcode,
    input logic [2:0] i_core5_m0_c_param,
    input logic [2:0] i_core5_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core5_m0_c_source,
    input logic [7:0] i_core5_m0_c_user,
    output logic o_core5_m0_c_ready,
    input logic i_core5_m0_c_valid,
    output logic o_core5_m0_d_corrupt,
    output logic [255:0] o_core5_m0_d_data,
    output logic o_core5_m0_d_denied,
    output logic [2:0] o_core5_m0_d_opcode,
    output logic [1:0] o_core5_m0_d_param,
    output logic [2:0] o_core5_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core5_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core5_m0_d_source,
    output logic [5:0] o_core5_m0_d_user,
    input logic i_core5_m0_d_ready,
    output logic o_core5_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core5_m0_e_sink,
    output logic o_core5_m0_e_ready,
    input logic i_core5_m0_e_valid,
    input logic [39:0] i_core5_m1_axi_s_araddr,
    input logic [1:0] i_core5_m1_axi_s_arburst,
    input logic [3:0] i_core5_m1_axi_s_arcache,
    input logic [4:0] i_core5_m1_axi_s_arid,
    input logic [7:0] i_core5_m1_axi_s_arlen,
    input logic i_core5_m1_axi_s_arlock,
    input logic [2:0] i_core5_m1_axi_s_arprot,
    input logic [2:0] i_core5_m1_axi_s_arsize,
    output logic o_core5_m1_axi_s_arready,
    input logic i_core5_m1_axi_s_arvalid,
    input logic [39:0] i_core5_m1_axi_s_awaddr,
    input logic [1:0] i_core5_m1_axi_s_awburst,
    input logic [3:0] i_core5_m1_axi_s_awcache,
    input logic [4:0] i_core5_m1_axi_s_awid,
    input logic [7:0] i_core5_m1_axi_s_awlen,
    input logic i_core5_m1_axi_s_awlock,
    input logic [2:0] i_core5_m1_axi_s_awprot,
    input logic [2:0] i_core5_m1_axi_s_awsize,
    output logic o_core5_m1_axi_s_awready,
    input logic i_core5_m1_axi_s_awvalid,
    output logic [4:0] o_core5_m1_axi_s_bid,
    output logic [1:0] o_core5_m1_axi_s_bresp,
    input logic i_core5_m1_axi_s_bready,
    output logic o_core5_m1_axi_s_bvalid,
    output logic [63:0] o_core5_m1_axi_s_rdata,
    output logic [4:0] o_core5_m1_axi_s_rid,
    output logic o_core5_m1_axi_s_rlast,
    output logic [1:0] o_core5_m1_axi_s_rresp,
    input logic i_core5_m1_axi_s_rready,
    output logic o_core5_m1_axi_s_rvalid,
    input logic [63:0] i_core5_m1_axi_s_wdata,
    input logic i_core5_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core5_m1_axi_s_wstrb,
    output logic o_core5_m1_axi_s_wready,
    input logic i_core5_m1_axi_s_wvalid,
    input logic [39:0] i_core5_m2_a_address,
    input logic i_core5_m2_a_corrupt,
    input logic [255:0] i_core5_m2_a_data,
    input logic [31:0] i_core5_m2_a_mask,
    input logic [2:0] i_core5_m2_a_opcode,
    input logic [2:0] i_core5_m2_a_param,
    input logic [2:0] i_core5_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core5_m2_a_source,
    input logic [11:0] i_core5_m2_a_user,
    output logic o_core5_m2_a_ready,
    input logic i_core5_m2_a_valid,
    output logic o_core5_m2_d_corrupt,
    output logic [255:0] o_core5_m2_d_data,
    output logic o_core5_m2_d_denied,
    output logic [2:0] o_core5_m2_d_opcode,
    output logic [1:0] o_core5_m2_d_param,
    output logic [2:0] o_core5_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core5_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core5_m2_d_source,
    output logic [5:0] o_core5_m2_d_user,
    input logic i_core5_m2_d_ready,
    output logic o_core5_m2_d_valid,

    input logic i_core6_coherent_enable,
    output logic o_core6_coherent_state,
    input logic [39:0] i_core6_m0_a_address,
    input logic i_core6_m0_a_corrupt,
    input logic [255:0] i_core6_m0_a_data,
    input logic [31:0] i_core6_m0_a_mask,
    input logic [2:0] i_core6_m0_a_opcode,
    input logic [2:0] i_core6_m0_a_param,
    input logic [2:0] i_core6_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core6_m0_a_source,
    input logic [11:0] i_core6_m0_a_user,
    output logic o_core6_m0_a_ready,
    input logic i_core6_m0_a_valid,
    output logic [39:0] o_core6_m0_b_address,
    output logic o_core6_m0_b_corrupt,
    output logic [255:0] o_core6_m0_b_data,
    output logic [31:0] o_core6_m0_b_mask,
    output logic [2:0] o_core6_m0_b_opcode,
    output logic [2:0] o_core6_m0_b_param,
    output logic [2:0] o_core6_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core6_m0_b_source,
    input logic i_core6_m0_b_ready,
    output logic o_core6_m0_b_valid,
    input logic [39:0] i_core6_m0_c_address,
    input logic i_core6_m0_c_corrupt,
    input logic [255:0] i_core6_m0_c_data,
    input logic [2:0] i_core6_m0_c_opcode,
    input logic [2:0] i_core6_m0_c_param,
    input logic [2:0] i_core6_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core6_m0_c_source,
    input logic [7:0] i_core6_m0_c_user,
    output logic o_core6_m0_c_ready,
    input logic i_core6_m0_c_valid,
    output logic o_core6_m0_d_corrupt,
    output logic [255:0] o_core6_m0_d_data,
    output logic o_core6_m0_d_denied,
    output logic [2:0] o_core6_m0_d_opcode,
    output logic [1:0] o_core6_m0_d_param,
    output logic [2:0] o_core6_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core6_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core6_m0_d_source,
    output logic [5:0] o_core6_m0_d_user,
    input logic i_core6_m0_d_ready,
    output logic o_core6_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core6_m0_e_sink,
    output logic o_core6_m0_e_ready,
    input logic i_core6_m0_e_valid,
    input logic [39:0] i_core6_m1_axi_s_araddr,
    input logic [1:0] i_core6_m1_axi_s_arburst,
    input logic [3:0] i_core6_m1_axi_s_arcache,
    input logic [4:0] i_core6_m1_axi_s_arid,
    input logic [7:0] i_core6_m1_axi_s_arlen,
    input logic i_core6_m1_axi_s_arlock,
    input logic [2:0] i_core6_m1_axi_s_arprot,
    input logic [2:0] i_core6_m1_axi_s_arsize,
    output logic o_core6_m1_axi_s_arready,
    input logic i_core6_m1_axi_s_arvalid,
    input logic [39:0] i_core6_m1_axi_s_awaddr,
    input logic [1:0] i_core6_m1_axi_s_awburst,
    input logic [3:0] i_core6_m1_axi_s_awcache,
    input logic [4:0] i_core6_m1_axi_s_awid,
    input logic [7:0] i_core6_m1_axi_s_awlen,
    input logic i_core6_m1_axi_s_awlock,
    input logic [2:0] i_core6_m1_axi_s_awprot,
    input logic [2:0] i_core6_m1_axi_s_awsize,
    output logic o_core6_m1_axi_s_awready,
    input logic i_core6_m1_axi_s_awvalid,
    output logic [4:0] o_core6_m1_axi_s_bid,
    output logic [1:0] o_core6_m1_axi_s_bresp,
    input logic i_core6_m1_axi_s_bready,
    output logic o_core6_m1_axi_s_bvalid,
    output logic [63:0] o_core6_m1_axi_s_rdata,
    output logic [4:0] o_core6_m1_axi_s_rid,
    output logic o_core6_m1_axi_s_rlast,
    output logic [1:0] o_core6_m1_axi_s_rresp,
    input logic i_core6_m1_axi_s_rready,
    output logic o_core6_m1_axi_s_rvalid,
    input logic [63:0] i_core6_m1_axi_s_wdata,
    input logic i_core6_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core6_m1_axi_s_wstrb,
    output logic o_core6_m1_axi_s_wready,
    input logic i_core6_m1_axi_s_wvalid,
    input logic [39:0] i_core6_m2_a_address,
    input logic i_core6_m2_a_corrupt,
    input logic [255:0] i_core6_m2_a_data,
    input logic [31:0] i_core6_m2_a_mask,
    input logic [2:0] i_core6_m2_a_opcode,
    input logic [2:0] i_core6_m2_a_param,
    input logic [2:0] i_core6_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core6_m2_a_source,
    input logic [11:0] i_core6_m2_a_user,
    output logic o_core6_m2_a_ready,
    input logic i_core6_m2_a_valid,
    output logic o_core6_m2_d_corrupt,
    output logic [255:0] o_core6_m2_d_data,
    output logic o_core6_m2_d_denied,
    output logic [2:0] o_core6_m2_d_opcode,
    output logic [1:0] o_core6_m2_d_param,
    output logic [2:0] o_core6_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core6_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core6_m2_d_source,
    output logic [5:0] o_core6_m2_d_user,
    input logic i_core6_m2_d_ready,
    output logic o_core6_m2_d_valid,

    input logic i_core7_coherent_enable,
    output logic o_core7_coherent_state,
    input logic [39:0] i_core7_m0_a_address,
    input logic i_core7_m0_a_corrupt,
    input logic [255:0] i_core7_m0_a_data,
    input logic [31:0] i_core7_m0_a_mask,
    input logic [2:0] i_core7_m0_a_opcode,
    input logic [2:0] i_core7_m0_a_param,
    input logic [2:0] i_core7_m0_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core7_m0_a_source,
    input logic [11:0] i_core7_m0_a_user,
    output logic o_core7_m0_a_ready,
    input logic i_core7_m0_a_valid,
    output logic [39:0] o_core7_m0_b_address,
    output logic o_core7_m0_b_corrupt,
    output logic [255:0] o_core7_m0_b_data,
    output logic [31:0] o_core7_m0_b_mask,
    output logic [2:0] o_core7_m0_b_opcode,
    output logic [2:0] o_core7_m0_b_param,
    output logic [2:0] o_core7_m0_b_size,
    output logic [SOURCE_WIDTH - 1:0] o_core7_m0_b_source,
    input logic i_core7_m0_b_ready,
    output logic o_core7_m0_b_valid,
    input logic [39:0] i_core7_m0_c_address,
    input logic i_core7_m0_c_corrupt,
    input logic [255:0] i_core7_m0_c_data,
    input logic [2:0] i_core7_m0_c_opcode,
    input logic [2:0] i_core7_m0_c_param,
    input logic [2:0] i_core7_m0_c_size,
    input logic [SOURCE_WIDTH - 1:0] i_core7_m0_c_source,
    input logic [7:0] i_core7_m0_c_user,
    output logic o_core7_m0_c_ready,
    input logic i_core7_m0_c_valid,
    output logic o_core7_m0_d_corrupt,
    output logic [255:0] o_core7_m0_d_data,
    output logic o_core7_m0_d_denied,
    output logic [2:0] o_core7_m0_d_opcode,
    output logic [1:0] o_core7_m0_d_param,
    output logic [2:0] o_core7_m0_d_size,
    output logic [SINK_WIDTH - 1:0] o_core7_m0_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core7_m0_d_source,
    output logic [5:0] o_core7_m0_d_user,
    input logic i_core7_m0_d_ready,
    output logic o_core7_m0_d_valid,
    input logic [SINK_WIDTH - 1:0] i_core7_m0_e_sink,
    output logic o_core7_m0_e_ready,
    input logic i_core7_m0_e_valid,
    input logic [39:0] i_core7_m1_axi_s_araddr,
    input logic [1:0] i_core7_m1_axi_s_arburst,
    input logic [3:0] i_core7_m1_axi_s_arcache,
    input logic [4:0] i_core7_m1_axi_s_arid,
    input logic [7:0] i_core7_m1_axi_s_arlen,
    input logic i_core7_m1_axi_s_arlock,
    input logic [2:0] i_core7_m1_axi_s_arprot,
    input logic [2:0] i_core7_m1_axi_s_arsize,
    output logic o_core7_m1_axi_s_arready,
    input logic i_core7_m1_axi_s_arvalid,
    input logic [39:0] i_core7_m1_axi_s_awaddr,
    input logic [1:0] i_core7_m1_axi_s_awburst,
    input logic [3:0] i_core7_m1_axi_s_awcache,
    input logic [4:0] i_core7_m1_axi_s_awid,
    input logic [7:0] i_core7_m1_axi_s_awlen,
    input logic i_core7_m1_axi_s_awlock,
    input logic [2:0] i_core7_m1_axi_s_awprot,
    input logic [2:0] i_core7_m1_axi_s_awsize,
    output logic o_core7_m1_axi_s_awready,
    input logic i_core7_m1_axi_s_awvalid,
    output logic [4:0] o_core7_m1_axi_s_bid,
    output logic [1:0] o_core7_m1_axi_s_bresp,
    input logic i_core7_m1_axi_s_bready,
    output logic o_core7_m1_axi_s_bvalid,
    output logic [63:0] o_core7_m1_axi_s_rdata,
    output logic [4:0] o_core7_m1_axi_s_rid,
    output logic o_core7_m1_axi_s_rlast,
    output logic [1:0] o_core7_m1_axi_s_rresp,
    input logic i_core7_m1_axi_s_rready,
    output logic o_core7_m1_axi_s_rvalid,
    input logic [63:0] i_core7_m1_axi_s_wdata,
    input logic i_core7_m1_axi_s_wlast,
    input logic [(64 / 8) -1:0] i_core7_m1_axi_s_wstrb,
    output logic o_core7_m1_axi_s_wready,
    input logic i_core7_m1_axi_s_wvalid,
    input logic [39:0] i_core7_m2_a_address,
    input logic i_core7_m2_a_corrupt,
    input logic [255:0] i_core7_m2_a_data,
    input logic [31:0] i_core7_m2_a_mask,
    input logic [2:0] i_core7_m2_a_opcode,
    input logic [2:0] i_core7_m2_a_param,
    input logic [2:0] i_core7_m2_a_size,
    input logic [SOURCE_WIDTH - 1:0] i_core7_m2_a_source,
    input logic [11:0] i_core7_m2_a_user,
    output logic o_core7_m2_a_ready,
    input logic i_core7_m2_a_valid,
    output logic o_core7_m2_d_corrupt,
    output logic [255:0] o_core7_m2_d_data,
    output logic o_core7_m2_d_denied,
    output logic [2:0] o_core7_m2_d_opcode,
    output logic [1:0] o_core7_m2_d_param,
    output logic [2:0] o_core7_m2_d_size,
    output logic [SINK_WIDTH - 1:0] o_core7_m2_d_sink,
    output logic [SOURCE_WIDTH - 1:0] o_core7_m2_d_source,
    output logic [5:0] o_core7_m2_d_user,
    input logic i_core7_m2_d_ready,
    output logic o_core7_m2_d_valid,

    //////////////////////////////////////////////
    /// AXI sigs
    //////////////////////////////////////////////
    input logic [39:0] i_iocp_axi_s_araddr,
    input logic [1:0] i_iocp_axi_s_arburst,
    input logic [3:0] i_iocp_axi_s_arcache,
    input logic [12:0] i_iocp_axi_s_arid,
    input logic [7:0] i_iocp_axi_s_arlen,
    input logic i_iocp_axi_s_arlock,
    input logic [2:0] i_iocp_axi_s_arprot,
    input logic [2:0] i_iocp_axi_s_arsize,
    output logic o_iocp_axi_s_arready,
    input logic i_iocp_axi_s_arvalid,
    input logic [39:0] i_iocp_axi_s_awaddr,
    input logic [1:0] i_iocp_axi_s_awburst,
    input logic [3:0] i_iocp_axi_s_awcache,
    input logic [12:0] i_iocp_axi_s_awid,
    input logic [7:0] i_iocp_axi_s_awlen,
    input logic i_iocp_axi_s_awlock,
    input logic [2:0] i_iocp_axi_s_awprot,
    input logic [2:0] i_iocp_axi_s_awsize,
    output logic o_iocp_axi_s_awready,
    input logic i_iocp_axi_s_awvalid,
    output logic [12:0] o_iocp_axi_s_bid,
    output logic [1:0] o_iocp_axi_s_bresp,
    input logic i_iocp_axi_s_bready,
    output logic o_iocp_axi_s_bvalid,
    output logic [255:0] o_iocp_axi_s_rdata,
    output logic [12:0] o_iocp_axi_s_rid,
    output logic o_iocp_axi_s_rlast,
    output logic [1:0] o_iocp_axi_s_rresp,
    input logic i_iocp_axi_s_rready,
    output logic o_iocp_axi_s_rvalid,
    input logic [255:0] i_iocp_axi_s_wdata,
    input logic i_iocp_axi_s_wlast,
    input logic [(256 / 8) - 1:0] i_iocp_axi_s_wstrb,
    output logic o_iocp_axi_s_wready,
    input logic i_iocp_axi_s_wvalid,
    output logic [39:0] o_mem_axi_m_araddr,
    output logic [1:0] o_mem_axi_m_arburst,
    output logic [3:0] o_mem_axi_m_arcache,
    output logic [7:0] o_mem_axi_m_arid,
    output logic [7:0] o_mem_axi_m_arlen,
    output logic o_mem_axi_m_arlock,
    output logic [2:0] o_mem_axi_m_arprot,
    output logic [2:0] o_mem_axi_m_arsize,
    input logic i_mem_axi_m_arready,
    output logic o_mem_axi_m_arvalid,
    output logic [39:0] o_mem_axi_m_awaddr,
    output logic [1:0] o_mem_axi_m_awburst,
    output logic [3:0] o_mem_axi_m_awcache,
    output logic [7:0] o_mem_axi_m_awid,
    output logic [7:0] o_mem_axi_m_awlen,
    output logic o_mem_axi_m_awlock,
    output logic [2:0] o_mem_axi_m_awprot,
    output logic [2:0] o_mem_axi_m_awsize,
    input logic i_mem_axi_m_awready,
    output logic o_mem_axi_m_awvalid,
    input logic [7:0] i_mem_axi_m_bid,
    input logic [1:0] i_mem_axi_m_bresp,
    output logic o_mem_axi_m_bready,
    input logic i_mem_axi_m_bvalid,
    input logic [255:0] i_mem_axi_m_rdata,
    input logic [7:0] i_mem_axi_m_rid,
    input logic i_mem_axi_m_rlast,
    input logic [1:0] i_mem_axi_m_rresp,
    output logic o_mem_axi_m_rready,
    input logic i_mem_axi_m_rvalid,
    output logic [255:0] o_mem_axi_m_wdata,
    output logic o_mem_axi_m_wlast,
    output logic [(256 / 8) - 1:0] o_mem_axi_m_wstrb,
    input logic i_mem_axi_m_wready,
    output logic o_mem_axi_m_wvalid,
    output logic [39:0] o_mmio_axi_m_araddr,
    output logic [1:0] o_mmio_axi_m_arburst,
    output logic [3:0] o_mmio_axi_m_arcache,
    output logic [7:0] o_mmio_axi_m_arid,
    output logic [7:0] o_mmio_axi_m_arlen,
    output logic o_mmio_axi_m_arlock,
    output logic [2:0] o_mmio_axi_m_arprot,
    output logic [2:0] o_mmio_axi_m_arsize,
    input logic i_mmio_axi_m_arready,
    output logic o_mmio_axi_m_arvalid,
    output logic [39:0] o_mmio_axi_m_awaddr,
    output logic [1:0] o_mmio_axi_m_awburst,
    output logic [3:0] o_mmio_axi_m_awcache,
    output logic [7:0] o_mmio_axi_m_awid,
    output logic [7:0] o_mmio_axi_m_awlen,
    output logic o_mmio_axi_m_awlock,
    output logic [2:0] o_mmio_axi_m_awprot,
    output logic [2:0] o_mmio_axi_m_awsize,
    input logic i_mmio_axi_m_awready,
    output logic o_mmio_axi_m_awvalid,
    input logic [7:0] i_mmio_axi_m_bid,
    input logic [1:0] i_mmio_axi_m_bresp,
    output logic o_mmio_axi_m_bready,
    input logic i_mmio_axi_m_bvalid,
    input logic [63:0] i_mmio_axi_m_rdata,
    input logic [7:0] i_mmio_axi_m_rid,
    input logic i_mmio_axi_m_rlast,
    input logic [1:0] i_mmio_axi_m_rresp,
    output logic o_mmio_axi_m_rready,
    input logic i_mmio_axi_m_rvalid,
    output logic [63:0] o_mmio_axi_m_wdata,
    output logic o_mmio_axi_m_wlast,
    output logic [(64 / 8) - 1:0] o_mmio_axi_m_wstrb,
    input logic i_mmio_axi_m_wready,
    output logic o_mmio_axi_m_wvalid,
    output logic [39:0] o_plmt_axi_m_araddr,
    output logic [1:0] o_plmt_axi_m_arburst,
    output logic [3:0] o_plmt_axi_m_arcache,
    output logic [7:0] o_plmt_axi_m_arid,
    output logic [7:0] o_plmt_axi_m_arlen,
    output logic o_plmt_axi_m_arlock,
    output logic [2:0] o_plmt_axi_m_arprot,
    output logic [2:0] o_plmt_axi_m_arsize,
    input logic i_plmt_axi_m_arready,
    output logic o_plmt_axi_m_arvalid,
    output logic [39:0] o_plmt_axi_m_awaddr,
    output logic [1:0] o_plmt_axi_m_awburst,
    output logic [3:0] o_plmt_axi_m_awcache,
    output logic [7:0] o_plmt_axi_m_awid,
    output logic [7:0] o_plmt_axi_m_awlen,
    output logic o_plmt_axi_m_awlock,
    output logic [2:0] o_plmt_axi_m_awprot,
    output logic [2:0] o_plmt_axi_m_awsize,
    input logic i_plmt_axi_m_awready,
    output logic o_plmt_axi_m_awvalid,
    input logic [7:0] i_plmt_axi_m_bid,
    input logic [1:0] i_plmt_axi_m_bresp,
    output logic o_plmt_axi_m_bready,
    input logic i_plmt_axi_m_bvalid,
    input logic [63:0] i_plmt_axi_m_rdata,
    input logic [7:0] i_plmt_axi_m_rid,
    input logic i_plmt_axi_m_rlast,
    input logic [1:0] i_plmt_axi_m_rresp,
    output logic o_plmt_axi_m_rready,
    input logic i_plmt_axi_m_rvalid,
    output logic [63:0] o_plmt_axi_m_wdata,
    output logic o_plmt_axi_m_wlast,
    output logic [(64 / 8) - 1:0] o_plmt_axi_m_wstrb,
    input logic i_plmt_axi_m_wready,
    output logic o_plmt_axi_m_wvalid,

    //////////////////////////////////////////////
    /// L2C bank sigs
    //////////////////////////////////////////////
    input logic [CTRL_IN_WIDTH - 1:0] i_l2c_ctrl,
    output logic [CTRL_OUT_WIDTH - 1:0] o_l2c_ctrl,
    input logic i_l2c_disable_init,
    output logic o_l2c_err_int
);

  axe_tcl_sram_pkg::impl_inp_t i_local_ctrl;

  always_comb begin
    i_local_ctrl = i_l2c_ctrl;

    // DFT
    i_local_ctrl.se = scan_en;
  end

  localparam int unsigned NUM_SRAMS = L2C_BANK_WIDTH * (L2C_BANK_TAG_WIDTH + L2C_BANK_DATA_WIDTH);

  axe_tcl_sram_pkg::impl_inp_t [NUM_SRAMS - 1:0] i_all_ctrl;
  axe_tcl_sram_pkg::impl_oup_t [NUM_SRAMS - 1:0] o_all_ctrl;

  logic [L2C_BANK_WIDTH - 1:0][(L2C_BANK_TAG_WIDTH * CTRL_IN_WIDTH) - 1:0] i_l2c_banks_tag_ctrl;
  logic [L2C_BANK_WIDTH - 1:0][(L2C_BANK_TAG_WIDTH * CTRL_OUT_WIDTH) - 1:0] o_l2c_banks_tag_ctrl;
  logic [L2C_BANK_WIDTH - 1:0][(L2C_BANK_DATA_WIDTH * CTRL_IN_WIDTH) - 1:0] i_l2c_banks_data_ctrl;
  logic [L2C_BANK_WIDTH - 1:0][(L2C_BANK_DATA_WIDTH * CTRL_OUT_WIDTH) - 1:0] o_l2c_banks_data_ctrl;

  always_comb {
    i_l2c_banks_tag_ctrl,
    i_l2c_banks_data_ctrl
  } = i_all_ctrl;

  always_comb o_all_ctrl = {
    o_l2c_banks_tag_ctrl,
    o_l2c_banks_data_ctrl
  };

  axe_tcl_sram_cfg #(
    .NUM_SRAMS(NUM_SRAMS)
  ) u_sram_cfg (
    .i_s(i_local_ctrl),
    .o_s(o_l2c_ctrl),
    .o_m(i_all_ctrl),
    .i_m(o_all_ctrl)
  );

  logic [CORE_WIDTH - 1:0] i_cores_coherent_enable;
  logic [CORE_WIDTH - 1:0] o_cores_coherent_state;
  logic [CORE_WIDTH - 1:0][39:0] i_cores_m0_a_address;
  logic [CORE_WIDTH - 1:0] i_cores_m0_a_corrupt;
  logic [CORE_WIDTH - 1:0][255:0] i_cores_m0_a_data;
  logic [CORE_WIDTH - 1:0][31:0] i_cores_m0_a_mask;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m0_a_opcode;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m0_a_param;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m0_a_size;
  logic [CORE_WIDTH - 1:0][SOURCE_WIDTH - 1:0] i_cores_m0_a_source;
  logic [CORE_WIDTH - 1:0][11:0] i_cores_m0_a_user;
  logic [CORE_WIDTH - 1:0] o_cores_m0_a_ready;
  logic [CORE_WIDTH - 1:0] i_cores_m0_a_valid;
  logic [CORE_WIDTH - 1:0][39:0] o_cores_m0_b_address;
  logic [CORE_WIDTH - 1:0] o_cores_m0_b_corrupt;
  logic [CORE_WIDTH - 1:0][255:0] o_cores_m0_b_data;
  logic [CORE_WIDTH - 1:0][31:0] o_cores_m0_b_mask;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m0_b_opcode;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m0_b_param;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m0_b_size;
  logic [CORE_WIDTH - 1:0][SOURCE_WIDTH - 1:0] o_cores_m0_b_source;
  logic [CORE_WIDTH - 1:0] i_cores_m0_b_ready;
  logic [CORE_WIDTH - 1:0] o_cores_m0_b_valid;
  logic [CORE_WIDTH - 1:0][39:0] i_cores_m0_c_address;
  logic [CORE_WIDTH - 1:0] i_cores_m0_c_corrupt;
  logic [CORE_WIDTH - 1:0][255:0] i_cores_m0_c_data;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m0_c_opcode;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m0_c_param;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m0_c_size;
  logic [CORE_WIDTH - 1:0][SOURCE_WIDTH - 1:0] i_cores_m0_c_source;
  logic [CORE_WIDTH - 1:0][7:0] i_cores_m0_c_user;
  logic [CORE_WIDTH - 1:0] o_cores_m0_c_ready;
  logic [CORE_WIDTH - 1:0] i_cores_m0_c_valid;
  logic [CORE_WIDTH - 1:0] o_cores_m0_d_corrupt;
  logic [CORE_WIDTH - 1:0][255:0] o_cores_m0_d_data;
  logic [CORE_WIDTH - 1:0] o_cores_m0_d_denied;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m0_d_opcode;
  logic [CORE_WIDTH - 1:0][1:0] o_cores_m0_d_param;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m0_d_size;
  logic [CORE_WIDTH - 1:0][SINK_WIDTH - 1:0] o_cores_m0_d_sink;
  logic [CORE_WIDTH - 1:0][SOURCE_WIDTH - 1:0] o_cores_m0_d_source;
  logic [CORE_WIDTH - 1:0][5:0] o_cores_m0_d_user;
  logic [CORE_WIDTH - 1:0] i_cores_m0_d_ready;
  logic [CORE_WIDTH - 1:0] o_cores_m0_d_valid;
  logic [CORE_WIDTH - 1:0][SINK_WIDTH - 1:0] i_cores_m0_e_sink;
  logic [CORE_WIDTH - 1:0] o_cores_m0_e_ready;
  logic [CORE_WIDTH - 1:0] i_cores_m0_e_valid;
  logic [CORE_WIDTH - 1:0][39:0] i_cores_m1_axi_s_araddr;
  logic [CORE_WIDTH - 1:0][1:0] i_cores_m1_axi_s_arburst;
  logic [CORE_WIDTH - 1:0][3:0] i_cores_m1_axi_s_arcache;
  logic [CORE_WIDTH - 1:0][4:0] i_cores_m1_axi_s_arid;
  logic [CORE_WIDTH - 1:0][7:0] i_cores_m1_axi_s_arlen;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_arlock;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m1_axi_s_arprot;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m1_axi_s_arsize;
  logic [CORE_WIDTH - 1:0] o_cores_m1_axi_s_arready;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_arvalid;
  logic [CORE_WIDTH - 1:0][39:0] i_cores_m1_axi_s_awaddr;
  logic [CORE_WIDTH - 1:0][1:0] i_cores_m1_axi_s_awburst;
  logic [CORE_WIDTH - 1:0][3:0] i_cores_m1_axi_s_awcache;
  logic [CORE_WIDTH - 1:0][4:0] i_cores_m1_axi_s_awid;
  logic [CORE_WIDTH - 1:0][7:0] i_cores_m1_axi_s_awlen;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_awlock;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m1_axi_s_awprot;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m1_axi_s_awsize;
  logic [CORE_WIDTH - 1:0] o_cores_m1_axi_s_awready;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_awvalid;
  logic [CORE_WIDTH - 1:0][4:0] o_cores_m1_axi_s_bid;
  logic [CORE_WIDTH - 1:0][1:0] o_cores_m1_axi_s_bresp;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_bready;
  logic [CORE_WIDTH - 1:0] o_cores_m1_axi_s_bvalid;
  logic [CORE_WIDTH - 1:0][63:0] o_cores_m1_axi_s_rdata;
  logic [CORE_WIDTH - 1:0][4:0] o_cores_m1_axi_s_rid;
  logic [CORE_WIDTH - 1:0] o_cores_m1_axi_s_rlast;
  logic [CORE_WIDTH - 1:0][1:0] o_cores_m1_axi_s_rresp;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_rready;
  logic [CORE_WIDTH - 1:0] o_cores_m1_axi_s_rvalid;
  logic [CORE_WIDTH - 1:0][63:0] i_cores_m1_axi_s_wdata;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_wlast;
  logic [CORE_WIDTH - 1:0][(64 / 8) -1:0] i_cores_m1_axi_s_wstrb;
  logic [CORE_WIDTH - 1:0] o_cores_m1_axi_s_wready;
  logic [CORE_WIDTH - 1:0] i_cores_m1_axi_s_wvalid;
  logic [CORE_WIDTH - 1:0][39:0] i_cores_m2_a_address;
  logic [CORE_WIDTH - 1:0] i_cores_m2_a_corrupt;
  logic [CORE_WIDTH - 1:0][255:0] i_cores_m2_a_data;
  logic [CORE_WIDTH - 1:0][31:0] i_cores_m2_a_mask;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m2_a_opcode;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m2_a_param;
  logic [CORE_WIDTH - 1:0][2:0] i_cores_m2_a_size;
  logic [CORE_WIDTH - 1:0][SOURCE_WIDTH - 1:0] i_cores_m2_a_source;
  logic [CORE_WIDTH - 1:0][11:0] i_cores_m2_a_user;
  logic [CORE_WIDTH - 1:0] o_cores_m2_a_ready;
  logic [CORE_WIDTH - 1:0] i_cores_m2_a_valid;
  logic [CORE_WIDTH - 1:0] o_cores_m2_d_corrupt;
  logic [CORE_WIDTH - 1:0][255:0] o_cores_m2_d_data;
  logic [CORE_WIDTH - 1:0] o_cores_m2_d_denied;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m2_d_opcode;
  logic [CORE_WIDTH - 1:0][1:0] o_cores_m2_d_param;
  logic [CORE_WIDTH - 1:0][2:0] o_cores_m2_d_size;
  logic [CORE_WIDTH - 1:0][SINK_WIDTH - 1:0] o_cores_m2_d_sink;
  logic [CORE_WIDTH - 1:0][SOURCE_WIDTH - 1:0] o_cores_m2_d_source;
  logic [CORE_WIDTH - 1:0][5:0] o_cores_m2_d_user;
  logic [CORE_WIDTH - 1:0] i_cores_m2_d_ready;
  logic [CORE_WIDTH - 1:0] o_cores_m2_d_valid;

  always_comb i_cores_coherent_enable[0] = i_core0_coherent_enable;
  always_comb o_core0_coherent_state = o_cores_coherent_state[0];
  always_comb i_cores_m0_a_address[0] = i_core0_m0_a_address;
  always_comb i_cores_m0_a_corrupt[0] = i_core0_m0_a_corrupt;
  always_comb i_cores_m0_a_data[0] = i_core0_m0_a_data;
  always_comb i_cores_m0_a_mask[0] = i_core0_m0_a_mask;
  always_comb i_cores_m0_a_opcode[0] = i_core0_m0_a_opcode;
  always_comb i_cores_m0_a_param[0] = i_core0_m0_a_param;
  always_comb i_cores_m0_a_size[0] = i_core0_m0_a_size;
  always_comb i_cores_m0_a_source[0] = i_core0_m0_a_source;
  always_comb i_cores_m0_a_user[0] = i_core0_m0_a_user;
  always_comb o_core0_m0_a_ready = o_cores_m0_a_ready[0];
  always_comb i_cores_m0_a_valid[0] = i_core0_m0_a_valid;
  always_comb o_core0_m0_b_address = o_cores_m0_b_address[0];
  always_comb o_core0_m0_b_corrupt = o_cores_m0_b_corrupt[0];
  always_comb o_core0_m0_b_data = o_cores_m0_b_data[0];
  always_comb o_core0_m0_b_mask = o_cores_m0_b_mask[0];
  always_comb o_core0_m0_b_opcode = o_cores_m0_b_opcode[0];
  always_comb o_core0_m0_b_param = o_cores_m0_b_param[0];
  always_comb o_core0_m0_b_size = o_cores_m0_b_size[0];
  always_comb o_core0_m0_b_source = o_cores_m0_b_source[0];
  always_comb i_cores_m0_b_ready[0] = i_core0_m0_b_ready;
  always_comb o_core0_m0_b_valid = o_cores_m0_b_valid[0];
  always_comb i_cores_m0_c_address[0] = i_core0_m0_c_address;
  always_comb i_cores_m0_c_corrupt[0] = i_core0_m0_c_corrupt;
  always_comb i_cores_m0_c_data[0] = i_core0_m0_c_data;
  always_comb i_cores_m0_c_opcode[0] = i_core0_m0_c_opcode;
  always_comb i_cores_m0_c_param[0] = i_core0_m0_c_param;
  always_comb i_cores_m0_c_size[0] = i_core0_m0_c_size;
  always_comb i_cores_m0_c_source[0] = i_core0_m0_c_source;
  always_comb i_cores_m0_c_user[0] = i_core0_m0_c_user;
  always_comb o_core0_m0_c_ready = o_cores_m0_c_ready[0];
  always_comb i_cores_m0_c_valid[0] = i_core0_m0_c_valid;
  always_comb o_core0_m0_d_corrupt = o_cores_m0_d_corrupt[0];
  always_comb o_core0_m0_d_data = o_cores_m0_d_data[0];
  always_comb o_core0_m0_d_denied = o_cores_m0_d_denied[0];
  always_comb o_core0_m0_d_opcode = o_cores_m0_d_opcode[0];
  always_comb o_core0_m0_d_param = o_cores_m0_d_param[0];
  always_comb o_core0_m0_d_size = o_cores_m0_d_size[0];
  always_comb o_core0_m0_d_sink = o_cores_m0_d_sink[0];
  always_comb o_core0_m0_d_source = o_cores_m0_d_source[0];
  always_comb o_core0_m0_d_user = o_cores_m0_d_user[0];
  always_comb i_cores_m0_d_ready[0] = i_core0_m0_d_ready;
  always_comb o_core0_m0_d_valid = o_cores_m0_d_valid[0];
  always_comb i_cores_m0_e_sink[0] = i_core0_m0_e_sink;
  always_comb o_core0_m0_e_ready = o_cores_m0_e_ready[0];
  always_comb i_cores_m0_e_valid[0] = i_core0_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[0] = i_core0_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[0] = i_core0_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[0] = i_core0_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[0] = i_core0_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[0] = i_core0_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[0] = i_core0_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[0] = i_core0_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[0] = i_core0_m1_axi_s_arsize;
  always_comb o_core0_m1_axi_s_arready = o_cores_m1_axi_s_arready[0];
  always_comb i_cores_m1_axi_s_arvalid[0] = i_core0_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[0] = i_core0_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[0] = i_core0_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[0] = i_core0_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[0] = i_core0_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[0] = i_core0_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[0] = i_core0_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[0] = i_core0_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[0] = i_core0_m1_axi_s_awsize;
  always_comb o_core0_m1_axi_s_awready = o_cores_m1_axi_s_awready[0];
  always_comb i_cores_m1_axi_s_awvalid[0] = i_core0_m1_axi_s_awvalid;
  always_comb o_core0_m1_axi_s_bid = o_cores_m1_axi_s_bid[0];
  always_comb o_core0_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[0];
  always_comb i_cores_m1_axi_s_bready[0] = i_core0_m1_axi_s_bready;
  always_comb o_core0_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[0];
  always_comb o_core0_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[0];
  always_comb o_core0_m1_axi_s_rid = o_cores_m1_axi_s_rid[0];
  always_comb o_core0_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[0];
  always_comb o_core0_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[0];
  always_comb i_cores_m1_axi_s_rready[0] = i_core0_m1_axi_s_rready;
  always_comb o_core0_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[0];
  always_comb i_cores_m1_axi_s_wdata[0] = i_core0_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[0] = i_core0_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[0] = i_core0_m1_axi_s_wstrb;
  always_comb o_core0_m1_axi_s_wready = o_cores_m1_axi_s_wready[0];
  always_comb i_cores_m1_axi_s_wvalid[0] = i_core0_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[0] = i_core0_m2_a_address;
  always_comb i_cores_m2_a_corrupt[0] = i_core0_m2_a_corrupt;
  always_comb i_cores_m2_a_data[0] = i_core0_m2_a_data;
  always_comb i_cores_m2_a_mask[0] = i_core0_m2_a_mask;
  always_comb i_cores_m2_a_opcode[0] = i_core0_m2_a_opcode;
  always_comb i_cores_m2_a_param[0] = i_core0_m2_a_param;
  always_comb i_cores_m2_a_size[0] = i_core0_m2_a_size;
  always_comb i_cores_m2_a_source[0] = i_core0_m2_a_source;
  always_comb i_cores_m2_a_user[0] = i_core0_m2_a_user;
  always_comb o_core0_m2_a_ready = o_cores_m2_a_ready[0];
  always_comb i_cores_m2_a_valid[0] = i_core0_m2_a_valid;
  always_comb o_core0_m2_d_corrupt = o_cores_m2_d_corrupt[0];
  always_comb o_core0_m2_d_data = o_cores_m2_d_data[0];
  always_comb o_core0_m2_d_denied = o_cores_m2_d_denied[0];
  always_comb o_core0_m2_d_opcode = o_cores_m2_d_opcode[0];
  always_comb o_core0_m2_d_param = o_cores_m2_d_param[0];
  always_comb o_core0_m2_d_size = o_cores_m2_d_size[0];
  always_comb o_core0_m2_d_sink = o_cores_m2_d_sink[0];
  always_comb o_core0_m2_d_source = o_cores_m2_d_source[0];
  always_comb o_core0_m2_d_user = o_cores_m2_d_user[0];
  always_comb i_cores_m2_d_ready[0] = i_core0_m2_d_ready;
  always_comb o_core0_m2_d_valid = o_cores_m2_d_valid[0];

  always_comb i_cores_coherent_enable[1] = i_core1_coherent_enable;
  always_comb o_core1_coherent_state = o_cores_coherent_state[1];
  always_comb i_cores_m0_a_address[1] = i_core1_m0_a_address;
  always_comb i_cores_m0_a_corrupt[1] = i_core1_m0_a_corrupt;
  always_comb i_cores_m0_a_data[1] = i_core1_m0_a_data;
  always_comb i_cores_m0_a_mask[1] = i_core1_m0_a_mask;
  always_comb i_cores_m0_a_opcode[1] = i_core1_m0_a_opcode;
  always_comb i_cores_m0_a_param[1] = i_core1_m0_a_param;
  always_comb i_cores_m0_a_size[1] = i_core1_m0_a_size;
  always_comb i_cores_m0_a_source[1] = i_core1_m0_a_source;
  always_comb i_cores_m0_a_user[1] = i_core1_m0_a_user;
  always_comb o_core1_m0_a_ready = o_cores_m0_a_ready[1];
  always_comb i_cores_m0_a_valid[1] = i_core1_m0_a_valid;
  always_comb o_core1_m0_b_address = o_cores_m0_b_address[1];
  always_comb o_core1_m0_b_corrupt = o_cores_m0_b_corrupt[1];
  always_comb o_core1_m0_b_data = o_cores_m0_b_data[1];
  always_comb o_core1_m0_b_mask = o_cores_m0_b_mask[1];
  always_comb o_core1_m0_b_opcode = o_cores_m0_b_opcode[1];
  always_comb o_core1_m0_b_param = o_cores_m0_b_param[1];
  always_comb o_core1_m0_b_size = o_cores_m0_b_size[1];
  always_comb o_core1_m0_b_source = o_cores_m0_b_source[1];
  always_comb i_cores_m0_b_ready[1] = i_core1_m0_b_ready;
  always_comb o_core1_m0_b_valid = o_cores_m0_b_valid[1];
  always_comb i_cores_m0_c_address[1] = i_core1_m0_c_address;
  always_comb i_cores_m0_c_corrupt[1] = i_core1_m0_c_corrupt;
  always_comb i_cores_m0_c_data[1] = i_core1_m0_c_data;
  always_comb i_cores_m0_c_opcode[1] = i_core1_m0_c_opcode;
  always_comb i_cores_m0_c_param[1] = i_core1_m0_c_param;
  always_comb i_cores_m0_c_size[1] = i_core1_m0_c_size;
  always_comb i_cores_m0_c_source[1] = i_core1_m0_c_source;
  always_comb i_cores_m0_c_user[1] = i_core1_m0_c_user;
  always_comb o_core1_m0_c_ready = o_cores_m0_c_ready[1];
  always_comb i_cores_m0_c_valid[1] = i_core1_m0_c_valid;
  always_comb o_core1_m0_d_corrupt = o_cores_m0_d_corrupt[1];
  always_comb o_core1_m0_d_data = o_cores_m0_d_data[1];
  always_comb o_core1_m0_d_denied = o_cores_m0_d_denied[1];
  always_comb o_core1_m0_d_opcode = o_cores_m0_d_opcode[1];
  always_comb o_core1_m0_d_param = o_cores_m0_d_param[1];
  always_comb o_core1_m0_d_size = o_cores_m0_d_size[1];
  always_comb o_core1_m0_d_sink = o_cores_m0_d_sink[1];
  always_comb o_core1_m0_d_source = o_cores_m0_d_source[1];
  always_comb o_core1_m0_d_user = o_cores_m0_d_user[1];
  always_comb i_cores_m0_d_ready[1] = i_core1_m0_d_ready;
  always_comb o_core1_m0_d_valid = o_cores_m0_d_valid[1];
  always_comb i_cores_m0_e_sink[1] = i_core1_m0_e_sink;
  always_comb o_core1_m0_e_ready = o_cores_m0_e_ready[1];
  always_comb i_cores_m0_e_valid[1] = i_core1_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[1] = i_core1_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[1] = i_core1_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[1] = i_core1_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[1] = i_core1_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[1] = i_core1_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[1] = i_core1_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[1] = i_core1_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[1] = i_core1_m1_axi_s_arsize;
  always_comb o_core1_m1_axi_s_arready = o_cores_m1_axi_s_arready[1];
  always_comb i_cores_m1_axi_s_arvalid[1] = i_core1_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[1] = i_core1_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[1] = i_core1_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[1] = i_core1_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[1] = i_core1_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[1] = i_core1_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[1] = i_core1_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[1] = i_core1_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[1] = i_core1_m1_axi_s_awsize;
  always_comb o_core1_m1_axi_s_awready = o_cores_m1_axi_s_awready[1];
  always_comb i_cores_m1_axi_s_awvalid[1] = i_core1_m1_axi_s_awvalid;
  always_comb o_core1_m1_axi_s_bid = o_cores_m1_axi_s_bid[1];
  always_comb o_core1_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[1];
  always_comb i_cores_m1_axi_s_bready[1] = i_core1_m1_axi_s_bready;
  always_comb o_core1_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[1];
  always_comb o_core1_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[1];
  always_comb o_core1_m1_axi_s_rid = o_cores_m1_axi_s_rid[1];
  always_comb o_core1_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[1];
  always_comb o_core1_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[1];
  always_comb i_cores_m1_axi_s_rready[1] = i_core1_m1_axi_s_rready;
  always_comb o_core1_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[1];
  always_comb i_cores_m1_axi_s_wdata[1] = i_core1_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[1] = i_core1_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[1] = i_core1_m1_axi_s_wstrb;
  always_comb o_core1_m1_axi_s_wready = o_cores_m1_axi_s_wready[1];
  always_comb i_cores_m1_axi_s_wvalid[1] = i_core1_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[1] = i_core1_m2_a_address;
  always_comb i_cores_m2_a_corrupt[1] = i_core1_m2_a_corrupt;
  always_comb i_cores_m2_a_data[1] = i_core1_m2_a_data;
  always_comb i_cores_m2_a_mask[1] = i_core1_m2_a_mask;
  always_comb i_cores_m2_a_opcode[1] = i_core1_m2_a_opcode;
  always_comb i_cores_m2_a_param[1] = i_core1_m2_a_param;
  always_comb i_cores_m2_a_size[1] = i_core1_m2_a_size;
  always_comb i_cores_m2_a_source[1] = i_core1_m2_a_source;
  always_comb i_cores_m2_a_user[1] = i_core1_m2_a_user;
  always_comb o_core1_m2_a_ready = o_cores_m2_a_ready[1];
  always_comb i_cores_m2_a_valid[1] = i_core1_m2_a_valid;
  always_comb o_core1_m2_d_corrupt = o_cores_m2_d_corrupt[1];
  always_comb o_core1_m2_d_data = o_cores_m2_d_data[1];
  always_comb o_core1_m2_d_denied = o_cores_m2_d_denied[1];
  always_comb o_core1_m2_d_opcode = o_cores_m2_d_opcode[1];
  always_comb o_core1_m2_d_param = o_cores_m2_d_param[1];
  always_comb o_core1_m2_d_size = o_cores_m2_d_size[1];
  always_comb o_core1_m2_d_sink = o_cores_m2_d_sink[1];
  always_comb o_core1_m2_d_source = o_cores_m2_d_source[1];
  always_comb o_core1_m2_d_user = o_cores_m2_d_user[1];
  always_comb i_cores_m2_d_ready[1] = i_core1_m2_d_ready;
  always_comb o_core1_m2_d_valid = o_cores_m2_d_valid[1];

  always_comb i_cores_coherent_enable[2] = i_core2_coherent_enable;
  always_comb o_core2_coherent_state = o_cores_coherent_state[2];
  always_comb i_cores_m0_a_address[2] = i_core2_m0_a_address;
  always_comb i_cores_m0_a_corrupt[2] = i_core2_m0_a_corrupt;
  always_comb i_cores_m0_a_data[2] = i_core2_m0_a_data;
  always_comb i_cores_m0_a_mask[2] = i_core2_m0_a_mask;
  always_comb i_cores_m0_a_opcode[2] = i_core2_m0_a_opcode;
  always_comb i_cores_m0_a_param[2] = i_core2_m0_a_param;
  always_comb i_cores_m0_a_size[2] = i_core2_m0_a_size;
  always_comb i_cores_m0_a_source[2] = i_core2_m0_a_source;
  always_comb i_cores_m0_a_user[2] = i_core2_m0_a_user;
  always_comb o_core2_m0_a_ready = o_cores_m0_a_ready[2];
  always_comb i_cores_m0_a_valid[2] = i_core2_m0_a_valid;
  always_comb o_core2_m0_b_address = o_cores_m0_b_address[2];
  always_comb o_core2_m0_b_corrupt = o_cores_m0_b_corrupt[2];
  always_comb o_core2_m0_b_data = o_cores_m0_b_data[2];
  always_comb o_core2_m0_b_mask = o_cores_m0_b_mask[2];
  always_comb o_core2_m0_b_opcode = o_cores_m0_b_opcode[2];
  always_comb o_core2_m0_b_param = o_cores_m0_b_param[2];
  always_comb o_core2_m0_b_size = o_cores_m0_b_size[2];
  always_comb o_core2_m0_b_source = o_cores_m0_b_source[2];
  always_comb i_cores_m0_b_ready[2] = i_core2_m0_b_ready;
  always_comb o_core2_m0_b_valid = o_cores_m0_b_valid[2];
  always_comb i_cores_m0_c_address[2] = i_core2_m0_c_address;
  always_comb i_cores_m0_c_corrupt[2] = i_core2_m0_c_corrupt;
  always_comb i_cores_m0_c_data[2] = i_core2_m0_c_data;
  always_comb i_cores_m0_c_opcode[2] = i_core2_m0_c_opcode;
  always_comb i_cores_m0_c_param[2] = i_core2_m0_c_param;
  always_comb i_cores_m0_c_size[2] = i_core2_m0_c_size;
  always_comb i_cores_m0_c_source[2] = i_core2_m0_c_source;
  always_comb i_cores_m0_c_user[2] = i_core2_m0_c_user;
  always_comb o_core2_m0_c_ready = o_cores_m0_c_ready[2];
  always_comb i_cores_m0_c_valid[2] = i_core2_m0_c_valid;
  always_comb o_core2_m0_d_corrupt = o_cores_m0_d_corrupt[2];
  always_comb o_core2_m0_d_data = o_cores_m0_d_data[2];
  always_comb o_core2_m0_d_denied = o_cores_m0_d_denied[2];
  always_comb o_core2_m0_d_opcode = o_cores_m0_d_opcode[2];
  always_comb o_core2_m0_d_param = o_cores_m0_d_param[2];
  always_comb o_core2_m0_d_size = o_cores_m0_d_size[2];
  always_comb o_core2_m0_d_sink = o_cores_m0_d_sink[2];
  always_comb o_core2_m0_d_source = o_cores_m0_d_source[2];
  always_comb o_core2_m0_d_user = o_cores_m0_d_user[2];
  always_comb i_cores_m0_d_ready[2] = i_core2_m0_d_ready;
  always_comb o_core2_m0_d_valid = o_cores_m0_d_valid[2];
  always_comb i_cores_m0_e_sink[2] = i_core2_m0_e_sink;
  always_comb o_core2_m0_e_ready = o_cores_m0_e_ready[2];
  always_comb i_cores_m0_e_valid[2] = i_core2_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[2] = i_core2_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[2] = i_core2_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[2] = i_core2_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[2] = i_core2_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[2] = i_core2_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[2] = i_core2_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[2] = i_core2_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[2] = i_core2_m1_axi_s_arsize;
  always_comb o_core2_m1_axi_s_arready = o_cores_m1_axi_s_arready[2];
  always_comb i_cores_m1_axi_s_arvalid[2] = i_core2_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[2] = i_core2_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[2] = i_core2_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[2] = i_core2_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[2] = i_core2_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[2] = i_core2_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[2] = i_core2_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[2] = i_core2_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[2] = i_core2_m1_axi_s_awsize;
  always_comb o_core2_m1_axi_s_awready = o_cores_m1_axi_s_awready[2];
  always_comb i_cores_m1_axi_s_awvalid[2] = i_core2_m1_axi_s_awvalid;
  always_comb o_core2_m1_axi_s_bid = o_cores_m1_axi_s_bid[2];
  always_comb o_core2_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[2];
  always_comb i_cores_m1_axi_s_bready[2] = i_core2_m1_axi_s_bready;
  always_comb o_core2_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[2];
  always_comb o_core2_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[2];
  always_comb o_core2_m1_axi_s_rid = o_cores_m1_axi_s_rid[2];
  always_comb o_core2_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[2];
  always_comb o_core2_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[2];
  always_comb i_cores_m1_axi_s_rready[2] = i_core2_m1_axi_s_rready;
  always_comb o_core2_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[2];
  always_comb i_cores_m1_axi_s_wdata[2] = i_core2_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[2] = i_core2_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[2] = i_core2_m1_axi_s_wstrb;
  always_comb o_core2_m1_axi_s_wready = o_cores_m1_axi_s_wready[2];
  always_comb i_cores_m1_axi_s_wvalid[2] = i_core2_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[2] = i_core2_m2_a_address;
  always_comb i_cores_m2_a_corrupt[2] = i_core2_m2_a_corrupt;
  always_comb i_cores_m2_a_data[2] = i_core2_m2_a_data;
  always_comb i_cores_m2_a_mask[2] = i_core2_m2_a_mask;
  always_comb i_cores_m2_a_opcode[2] = i_core2_m2_a_opcode;
  always_comb i_cores_m2_a_param[2] = i_core2_m2_a_param;
  always_comb i_cores_m2_a_size[2] = i_core2_m2_a_size;
  always_comb i_cores_m2_a_source[2] = i_core2_m2_a_source;
  always_comb i_cores_m2_a_user[2] = i_core2_m2_a_user;
  always_comb o_core2_m2_a_ready = o_cores_m2_a_ready[2];
  always_comb i_cores_m2_a_valid[2] = i_core2_m2_a_valid;
  always_comb o_core2_m2_d_corrupt = o_cores_m2_d_corrupt[2];
  always_comb o_core2_m2_d_data = o_cores_m2_d_data[2];
  always_comb o_core2_m2_d_denied = o_cores_m2_d_denied[2];
  always_comb o_core2_m2_d_opcode = o_cores_m2_d_opcode[2];
  always_comb o_core2_m2_d_param = o_cores_m2_d_param[2];
  always_comb o_core2_m2_d_size = o_cores_m2_d_size[2];
  always_comb o_core2_m2_d_sink = o_cores_m2_d_sink[2];
  always_comb o_core2_m2_d_source = o_cores_m2_d_source[2];
  always_comb o_core2_m2_d_user = o_cores_m2_d_user[2];
  always_comb i_cores_m2_d_ready[2] = i_core2_m2_d_ready;
  always_comb o_core2_m2_d_valid = o_cores_m2_d_valid[2];

  always_comb i_cores_coherent_enable[3] = i_core3_coherent_enable;
  always_comb o_core3_coherent_state = o_cores_coherent_state[3];
  always_comb i_cores_m0_a_address[3] = i_core3_m0_a_address;
  always_comb i_cores_m0_a_corrupt[3] = i_core3_m0_a_corrupt;
  always_comb i_cores_m0_a_data[3] = i_core3_m0_a_data;
  always_comb i_cores_m0_a_mask[3] = i_core3_m0_a_mask;
  always_comb i_cores_m0_a_opcode[3] = i_core3_m0_a_opcode;
  always_comb i_cores_m0_a_param[3] = i_core3_m0_a_param;
  always_comb i_cores_m0_a_size[3] = i_core3_m0_a_size;
  always_comb i_cores_m0_a_source[3] = i_core3_m0_a_source;
  always_comb i_cores_m0_a_user[3] = i_core3_m0_a_user;
  always_comb o_core3_m0_a_ready = o_cores_m0_a_ready[3];
  always_comb i_cores_m0_a_valid[3] = i_core3_m0_a_valid;
  always_comb o_core3_m0_b_address = o_cores_m0_b_address[3];
  always_comb o_core3_m0_b_corrupt = o_cores_m0_b_corrupt[3];
  always_comb o_core3_m0_b_data = o_cores_m0_b_data[3];
  always_comb o_core3_m0_b_mask = o_cores_m0_b_mask[3];
  always_comb o_core3_m0_b_opcode = o_cores_m0_b_opcode[3];
  always_comb o_core3_m0_b_param = o_cores_m0_b_param[3];
  always_comb o_core3_m0_b_size = o_cores_m0_b_size[3];
  always_comb o_core3_m0_b_source = o_cores_m0_b_source[3];
  always_comb i_cores_m0_b_ready[3] = i_core3_m0_b_ready;
  always_comb o_core3_m0_b_valid = o_cores_m0_b_valid[3];
  always_comb i_cores_m0_c_address[3] = i_core3_m0_c_address;
  always_comb i_cores_m0_c_corrupt[3] = i_core3_m0_c_corrupt;
  always_comb i_cores_m0_c_data[3] = i_core3_m0_c_data;
  always_comb i_cores_m0_c_opcode[3] = i_core3_m0_c_opcode;
  always_comb i_cores_m0_c_param[3] = i_core3_m0_c_param;
  always_comb i_cores_m0_c_size[3] = i_core3_m0_c_size;
  always_comb i_cores_m0_c_source[3] = i_core3_m0_c_source;
  always_comb i_cores_m0_c_user[3] = i_core3_m0_c_user;
  always_comb o_core3_m0_c_ready = o_cores_m0_c_ready[3];
  always_comb i_cores_m0_c_valid[3] = i_core3_m0_c_valid;
  always_comb o_core3_m0_d_corrupt = o_cores_m0_d_corrupt[3];
  always_comb o_core3_m0_d_data = o_cores_m0_d_data[3];
  always_comb o_core3_m0_d_denied = o_cores_m0_d_denied[3];
  always_comb o_core3_m0_d_opcode = o_cores_m0_d_opcode[3];
  always_comb o_core3_m0_d_param = o_cores_m0_d_param[3];
  always_comb o_core3_m0_d_size = o_cores_m0_d_size[3];
  always_comb o_core3_m0_d_sink = o_cores_m0_d_sink[3];
  always_comb o_core3_m0_d_source = o_cores_m0_d_source[3];
  always_comb o_core3_m0_d_user = o_cores_m0_d_user[3];
  always_comb i_cores_m0_d_ready[3] = i_core3_m0_d_ready;
  always_comb o_core3_m0_d_valid = o_cores_m0_d_valid[3];
  always_comb i_cores_m0_e_sink[3] = i_core3_m0_e_sink;
  always_comb o_core3_m0_e_ready = o_cores_m0_e_ready[3];
  always_comb i_cores_m0_e_valid[3] = i_core3_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[3] = i_core3_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[3] = i_core3_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[3] = i_core3_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[3] = i_core3_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[3] = i_core3_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[3] = i_core3_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[3] = i_core3_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[3] = i_core3_m1_axi_s_arsize;
  always_comb o_core3_m1_axi_s_arready = o_cores_m1_axi_s_arready[3];
  always_comb i_cores_m1_axi_s_arvalid[3] = i_core3_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[3] = i_core3_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[3] = i_core3_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[3] = i_core3_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[3] = i_core3_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[3] = i_core3_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[3] = i_core3_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[3] = i_core3_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[3] = i_core3_m1_axi_s_awsize;
  always_comb o_core3_m1_axi_s_awready = o_cores_m1_axi_s_awready[3];
  always_comb i_cores_m1_axi_s_awvalid[3] = i_core3_m1_axi_s_awvalid;
  always_comb o_core3_m1_axi_s_bid = o_cores_m1_axi_s_bid[3];
  always_comb o_core3_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[3];
  always_comb i_cores_m1_axi_s_bready[3] = i_core3_m1_axi_s_bready;
  always_comb o_core3_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[3];
  always_comb o_core3_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[3];
  always_comb o_core3_m1_axi_s_rid = o_cores_m1_axi_s_rid[3];
  always_comb o_core3_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[3];
  always_comb o_core3_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[3];
  always_comb i_cores_m1_axi_s_rready[3] = i_core3_m1_axi_s_rready;
  always_comb o_core3_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[3];
  always_comb i_cores_m1_axi_s_wdata[3] = i_core3_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[3] = i_core3_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[3] = i_core3_m1_axi_s_wstrb;
  always_comb o_core3_m1_axi_s_wready = o_cores_m1_axi_s_wready[3];
  always_comb i_cores_m1_axi_s_wvalid[3] = i_core3_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[3] = i_core3_m2_a_address;
  always_comb i_cores_m2_a_corrupt[3] = i_core3_m2_a_corrupt;
  always_comb i_cores_m2_a_data[3] = i_core3_m2_a_data;
  always_comb i_cores_m2_a_mask[3] = i_core3_m2_a_mask;
  always_comb i_cores_m2_a_opcode[3] = i_core3_m2_a_opcode;
  always_comb i_cores_m2_a_param[3] = i_core3_m2_a_param;
  always_comb i_cores_m2_a_size[3] = i_core3_m2_a_size;
  always_comb i_cores_m2_a_source[3] = i_core3_m2_a_source;
  always_comb i_cores_m2_a_user[3] = i_core3_m2_a_user;
  always_comb o_core3_m2_a_ready = o_cores_m2_a_ready[3];
  always_comb i_cores_m2_a_valid[3] = i_core3_m2_a_valid;
  always_comb o_core3_m2_d_corrupt = o_cores_m2_d_corrupt[3];
  always_comb o_core3_m2_d_data = o_cores_m2_d_data[3];
  always_comb o_core3_m2_d_denied = o_cores_m2_d_denied[3];
  always_comb o_core3_m2_d_opcode = o_cores_m2_d_opcode[3];
  always_comb o_core3_m2_d_param = o_cores_m2_d_param[3];
  always_comb o_core3_m2_d_size = o_cores_m2_d_size[3];
  always_comb o_core3_m2_d_sink = o_cores_m2_d_sink[3];
  always_comb o_core3_m2_d_source = o_cores_m2_d_source[3];
  always_comb o_core3_m2_d_user = o_cores_m2_d_user[3];
  always_comb i_cores_m2_d_ready[3] = i_core3_m2_d_ready;
  always_comb o_core3_m2_d_valid = o_cores_m2_d_valid[3];

  always_comb i_cores_coherent_enable[4] = i_core4_coherent_enable;
  always_comb o_core4_coherent_state = o_cores_coherent_state[4];
  always_comb i_cores_m0_a_address[4] = i_core4_m0_a_address;
  always_comb i_cores_m0_a_corrupt[4] = i_core4_m0_a_corrupt;
  always_comb i_cores_m0_a_data[4] = i_core4_m0_a_data;
  always_comb i_cores_m0_a_mask[4] = i_core4_m0_a_mask;
  always_comb i_cores_m0_a_opcode[4] = i_core4_m0_a_opcode;
  always_comb i_cores_m0_a_param[4] = i_core4_m0_a_param;
  always_comb i_cores_m0_a_size[4] = i_core4_m0_a_size;
  always_comb i_cores_m0_a_source[4] = i_core4_m0_a_source;
  always_comb i_cores_m0_a_user[4] = i_core4_m0_a_user;
  always_comb o_core4_m0_a_ready = o_cores_m0_a_ready[4];
  always_comb i_cores_m0_a_valid[4] = i_core4_m0_a_valid;
  always_comb o_core4_m0_b_address = o_cores_m0_b_address[4];
  always_comb o_core4_m0_b_corrupt = o_cores_m0_b_corrupt[4];
  always_comb o_core4_m0_b_data = o_cores_m0_b_data[4];
  always_comb o_core4_m0_b_mask = o_cores_m0_b_mask[4];
  always_comb o_core4_m0_b_opcode = o_cores_m0_b_opcode[4];
  always_comb o_core4_m0_b_param = o_cores_m0_b_param[4];
  always_comb o_core4_m0_b_size = o_cores_m0_b_size[4];
  always_comb o_core4_m0_b_source = o_cores_m0_b_source[4];
  always_comb i_cores_m0_b_ready[4] = i_core4_m0_b_ready;
  always_comb o_core4_m0_b_valid = o_cores_m0_b_valid[4];
  always_comb i_cores_m0_c_address[4] = i_core4_m0_c_address;
  always_comb i_cores_m0_c_corrupt[4] = i_core4_m0_c_corrupt;
  always_comb i_cores_m0_c_data[4] = i_core4_m0_c_data;
  always_comb i_cores_m0_c_opcode[4] = i_core4_m0_c_opcode;
  always_comb i_cores_m0_c_param[4] = i_core4_m0_c_param;
  always_comb i_cores_m0_c_size[4] = i_core4_m0_c_size;
  always_comb i_cores_m0_c_source[4] = i_core4_m0_c_source;
  always_comb i_cores_m0_c_user[4] = i_core4_m0_c_user;
  always_comb o_core4_m0_c_ready = o_cores_m0_c_ready[4];
  always_comb i_cores_m0_c_valid[4] = i_core4_m0_c_valid;
  always_comb o_core4_m0_d_corrupt = o_cores_m0_d_corrupt[4];
  always_comb o_core4_m0_d_data = o_cores_m0_d_data[4];
  always_comb o_core4_m0_d_denied = o_cores_m0_d_denied[4];
  always_comb o_core4_m0_d_opcode = o_cores_m0_d_opcode[4];
  always_comb o_core4_m0_d_param = o_cores_m0_d_param[4];
  always_comb o_core4_m0_d_size = o_cores_m0_d_size[4];
  always_comb o_core4_m0_d_sink = o_cores_m0_d_sink[4];
  always_comb o_core4_m0_d_source = o_cores_m0_d_source[4];
  always_comb o_core4_m0_d_user = o_cores_m0_d_user[4];
  always_comb i_cores_m0_d_ready[4] = i_core4_m0_d_ready;
  always_comb o_core4_m0_d_valid = o_cores_m0_d_valid[4];
  always_comb i_cores_m0_e_sink[4] = i_core4_m0_e_sink;
  always_comb o_core4_m0_e_ready = o_cores_m0_e_ready[4];
  always_comb i_cores_m0_e_valid[4] = i_core4_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[4] = i_core4_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[4] = i_core4_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[4] = i_core4_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[4] = i_core4_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[4] = i_core4_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[4] = i_core4_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[4] = i_core4_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[4] = i_core4_m1_axi_s_arsize;
  always_comb o_core4_m1_axi_s_arready = o_cores_m1_axi_s_arready[4];
  always_comb i_cores_m1_axi_s_arvalid[4] = i_core4_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[4] = i_core4_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[4] = i_core4_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[4] = i_core4_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[4] = i_core4_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[4] = i_core4_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[4] = i_core4_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[4] = i_core4_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[4] = i_core4_m1_axi_s_awsize;
  always_comb o_core4_m1_axi_s_awready = o_cores_m1_axi_s_awready[4];
  always_comb i_cores_m1_axi_s_awvalid[4] = i_core4_m1_axi_s_awvalid;
  always_comb o_core4_m1_axi_s_bid = o_cores_m1_axi_s_bid[4];
  always_comb o_core4_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[4];
  always_comb i_cores_m1_axi_s_bready[4] = i_core4_m1_axi_s_bready;
  always_comb o_core4_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[4];
  always_comb o_core4_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[4];
  always_comb o_core4_m1_axi_s_rid = o_cores_m1_axi_s_rid[4];
  always_comb o_core4_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[4];
  always_comb o_core4_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[4];
  always_comb i_cores_m1_axi_s_rready[4] = i_core4_m1_axi_s_rready;
  always_comb o_core4_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[4];
  always_comb i_cores_m1_axi_s_wdata[4] = i_core4_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[4] = i_core4_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[4] = i_core4_m1_axi_s_wstrb;
  always_comb o_core4_m1_axi_s_wready = o_cores_m1_axi_s_wready[4];
  always_comb i_cores_m1_axi_s_wvalid[4] = i_core4_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[4] = i_core4_m2_a_address;
  always_comb i_cores_m2_a_corrupt[4] = i_core4_m2_a_corrupt;
  always_comb i_cores_m2_a_data[4] = i_core4_m2_a_data;
  always_comb i_cores_m2_a_mask[4] = i_core4_m2_a_mask;
  always_comb i_cores_m2_a_opcode[4] = i_core4_m2_a_opcode;
  always_comb i_cores_m2_a_param[4] = i_core4_m2_a_param;
  always_comb i_cores_m2_a_size[4] = i_core4_m2_a_size;
  always_comb i_cores_m2_a_source[4] = i_core4_m2_a_source;
  always_comb i_cores_m2_a_user[4] = i_core4_m2_a_user;
  always_comb o_core4_m2_a_ready = o_cores_m2_a_ready[4];
  always_comb i_cores_m2_a_valid[4] = i_core4_m2_a_valid;
  always_comb o_core4_m2_d_corrupt = o_cores_m2_d_corrupt[4];
  always_comb o_core4_m2_d_data = o_cores_m2_d_data[4];
  always_comb o_core4_m2_d_denied = o_cores_m2_d_denied[4];
  always_comb o_core4_m2_d_opcode = o_cores_m2_d_opcode[4];
  always_comb o_core4_m2_d_param = o_cores_m2_d_param[4];
  always_comb o_core4_m2_d_size = o_cores_m2_d_size[4];
  always_comb o_core4_m2_d_sink = o_cores_m2_d_sink[4];
  always_comb o_core4_m2_d_source = o_cores_m2_d_source[4];
  always_comb o_core4_m2_d_user = o_cores_m2_d_user[4];
  always_comb i_cores_m2_d_ready[4] = i_core4_m2_d_ready;
  always_comb o_core4_m2_d_valid = o_cores_m2_d_valid[4];

  always_comb i_cores_coherent_enable[5] = i_core5_coherent_enable;
  always_comb o_core5_coherent_state = o_cores_coherent_state[5];
  always_comb i_cores_m0_a_address[5] = i_core5_m0_a_address;
  always_comb i_cores_m0_a_corrupt[5] = i_core5_m0_a_corrupt;
  always_comb i_cores_m0_a_data[5] = i_core5_m0_a_data;
  always_comb i_cores_m0_a_mask[5] = i_core5_m0_a_mask;
  always_comb i_cores_m0_a_opcode[5] = i_core5_m0_a_opcode;
  always_comb i_cores_m0_a_param[5] = i_core5_m0_a_param;
  always_comb i_cores_m0_a_size[5] = i_core5_m0_a_size;
  always_comb i_cores_m0_a_source[5] = i_core5_m0_a_source;
  always_comb i_cores_m0_a_user[5] = i_core5_m0_a_user;
  always_comb o_core5_m0_a_ready = o_cores_m0_a_ready[5];
  always_comb i_cores_m0_a_valid[5] = i_core5_m0_a_valid;
  always_comb o_core5_m0_b_address = o_cores_m0_b_address[5];
  always_comb o_core5_m0_b_corrupt = o_cores_m0_b_corrupt[5];
  always_comb o_core5_m0_b_data = o_cores_m0_b_data[5];
  always_comb o_core5_m0_b_mask = o_cores_m0_b_mask[5];
  always_comb o_core5_m0_b_opcode = o_cores_m0_b_opcode[5];
  always_comb o_core5_m0_b_param = o_cores_m0_b_param[5];
  always_comb o_core5_m0_b_size = o_cores_m0_b_size[5];
  always_comb o_core5_m0_b_source = o_cores_m0_b_source[5];
  always_comb i_cores_m0_b_ready[5] = i_core5_m0_b_ready;
  always_comb o_core5_m0_b_valid = o_cores_m0_b_valid[5];
  always_comb i_cores_m0_c_address[5] = i_core5_m0_c_address;
  always_comb i_cores_m0_c_corrupt[5] = i_core5_m0_c_corrupt;
  always_comb i_cores_m0_c_data[5] = i_core5_m0_c_data;
  always_comb i_cores_m0_c_opcode[5] = i_core5_m0_c_opcode;
  always_comb i_cores_m0_c_param[5] = i_core5_m0_c_param;
  always_comb i_cores_m0_c_size[5] = i_core5_m0_c_size;
  always_comb i_cores_m0_c_source[5] = i_core5_m0_c_source;
  always_comb i_cores_m0_c_user[5] = i_core5_m0_c_user;
  always_comb o_core5_m0_c_ready = o_cores_m0_c_ready[5];
  always_comb i_cores_m0_c_valid[5] = i_core5_m0_c_valid;
  always_comb o_core5_m0_d_corrupt = o_cores_m0_d_corrupt[5];
  always_comb o_core5_m0_d_data = o_cores_m0_d_data[5];
  always_comb o_core5_m0_d_denied = o_cores_m0_d_denied[5];
  always_comb o_core5_m0_d_opcode = o_cores_m0_d_opcode[5];
  always_comb o_core5_m0_d_param = o_cores_m0_d_param[5];
  always_comb o_core5_m0_d_size = o_cores_m0_d_size[5];
  always_comb o_core5_m0_d_sink = o_cores_m0_d_sink[5];
  always_comb o_core5_m0_d_source = o_cores_m0_d_source[5];
  always_comb o_core5_m0_d_user = o_cores_m0_d_user[5];
  always_comb i_cores_m0_d_ready[5] = i_core5_m0_d_ready;
  always_comb o_core5_m0_d_valid = o_cores_m0_d_valid[5];
  always_comb i_cores_m0_e_sink[5] = i_core5_m0_e_sink;
  always_comb o_core5_m0_e_ready = o_cores_m0_e_ready[5];
  always_comb i_cores_m0_e_valid[5] = i_core5_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[5] = i_core5_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[5] = i_core5_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[5] = i_core5_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[5] = i_core5_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[5] = i_core5_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[5] = i_core5_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[5] = i_core5_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[5] = i_core5_m1_axi_s_arsize;
  always_comb o_core5_m1_axi_s_arready = o_cores_m1_axi_s_arready[5];
  always_comb i_cores_m1_axi_s_arvalid[5] = i_core5_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[5] = i_core5_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[5] = i_core5_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[5] = i_core5_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[5] = i_core5_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[5] = i_core5_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[5] = i_core5_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[5] = i_core5_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[5] = i_core5_m1_axi_s_awsize;
  always_comb o_core5_m1_axi_s_awready = o_cores_m1_axi_s_awready[5];
  always_comb i_cores_m1_axi_s_awvalid[5] = i_core5_m1_axi_s_awvalid;
  always_comb o_core5_m1_axi_s_bid = o_cores_m1_axi_s_bid[5];
  always_comb o_core5_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[5];
  always_comb i_cores_m1_axi_s_bready[5] = i_core5_m1_axi_s_bready;
  always_comb o_core5_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[5];
  always_comb o_core5_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[5];
  always_comb o_core5_m1_axi_s_rid = o_cores_m1_axi_s_rid[5];
  always_comb o_core5_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[5];
  always_comb o_core5_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[5];
  always_comb i_cores_m1_axi_s_rready[5] = i_core5_m1_axi_s_rready;
  always_comb o_core5_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[5];
  always_comb i_cores_m1_axi_s_wdata[5] = i_core5_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[5] = i_core5_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[5] = i_core5_m1_axi_s_wstrb;
  always_comb o_core5_m1_axi_s_wready = o_cores_m1_axi_s_wready[5];
  always_comb i_cores_m1_axi_s_wvalid[5] = i_core5_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[5] = i_core5_m2_a_address;
  always_comb i_cores_m2_a_corrupt[5] = i_core5_m2_a_corrupt;
  always_comb i_cores_m2_a_data[5] = i_core5_m2_a_data;
  always_comb i_cores_m2_a_mask[5] = i_core5_m2_a_mask;
  always_comb i_cores_m2_a_opcode[5] = i_core5_m2_a_opcode;
  always_comb i_cores_m2_a_param[5] = i_core5_m2_a_param;
  always_comb i_cores_m2_a_size[5] = i_core5_m2_a_size;
  always_comb i_cores_m2_a_source[5] = i_core5_m2_a_source;
  always_comb i_cores_m2_a_user[5] = i_core5_m2_a_user;
  always_comb o_core5_m2_a_ready = o_cores_m2_a_ready[5];
  always_comb i_cores_m2_a_valid[5] = i_core5_m2_a_valid;
  always_comb o_core5_m2_d_corrupt = o_cores_m2_d_corrupt[5];
  always_comb o_core5_m2_d_data = o_cores_m2_d_data[5];
  always_comb o_core5_m2_d_denied = o_cores_m2_d_denied[5];
  always_comb o_core5_m2_d_opcode = o_cores_m2_d_opcode[5];
  always_comb o_core5_m2_d_param = o_cores_m2_d_param[5];
  always_comb o_core5_m2_d_size = o_cores_m2_d_size[5];
  always_comb o_core5_m2_d_sink = o_cores_m2_d_sink[5];
  always_comb o_core5_m2_d_source = o_cores_m2_d_source[5];
  always_comb o_core5_m2_d_user = o_cores_m2_d_user[5];
  always_comb i_cores_m2_d_ready[5] = i_core5_m2_d_ready;
  always_comb o_core5_m2_d_valid = o_cores_m2_d_valid[5];

  always_comb i_cores_coherent_enable[6] = i_core6_coherent_enable;
  always_comb o_core6_coherent_state = o_cores_coherent_state[6];
  always_comb i_cores_m0_a_address[6] = i_core6_m0_a_address;
  always_comb i_cores_m0_a_corrupt[6] = i_core6_m0_a_corrupt;
  always_comb i_cores_m0_a_data[6] = i_core6_m0_a_data;
  always_comb i_cores_m0_a_mask[6] = i_core6_m0_a_mask;
  always_comb i_cores_m0_a_opcode[6] = i_core6_m0_a_opcode;
  always_comb i_cores_m0_a_param[6] = i_core6_m0_a_param;
  always_comb i_cores_m0_a_size[6] = i_core6_m0_a_size;
  always_comb i_cores_m0_a_source[6] = i_core6_m0_a_source;
  always_comb i_cores_m0_a_user[6] = i_core6_m0_a_user;
  always_comb o_core6_m0_a_ready = o_cores_m0_a_ready[6];
  always_comb i_cores_m0_a_valid[6] = i_core6_m0_a_valid;
  always_comb o_core6_m0_b_address = o_cores_m0_b_address[6];
  always_comb o_core6_m0_b_corrupt = o_cores_m0_b_corrupt[6];
  always_comb o_core6_m0_b_data = o_cores_m0_b_data[6];
  always_comb o_core6_m0_b_mask = o_cores_m0_b_mask[6];
  always_comb o_core6_m0_b_opcode = o_cores_m0_b_opcode[6];
  always_comb o_core6_m0_b_param = o_cores_m0_b_param[6];
  always_comb o_core6_m0_b_size = o_cores_m0_b_size[6];
  always_comb o_core6_m0_b_source = o_cores_m0_b_source[6];
  always_comb i_cores_m0_b_ready[6] = i_core6_m0_b_ready;
  always_comb o_core6_m0_b_valid = o_cores_m0_b_valid[6];
  always_comb i_cores_m0_c_address[6] = i_core6_m0_c_address;
  always_comb i_cores_m0_c_corrupt[6] = i_core6_m0_c_corrupt;
  always_comb i_cores_m0_c_data[6] = i_core6_m0_c_data;
  always_comb i_cores_m0_c_opcode[6] = i_core6_m0_c_opcode;
  always_comb i_cores_m0_c_param[6] = i_core6_m0_c_param;
  always_comb i_cores_m0_c_size[6] = i_core6_m0_c_size;
  always_comb i_cores_m0_c_source[6] = i_core6_m0_c_source;
  always_comb i_cores_m0_c_user[6] = i_core6_m0_c_user;
  always_comb o_core6_m0_c_ready = o_cores_m0_c_ready[6];
  always_comb i_cores_m0_c_valid[6] = i_core6_m0_c_valid;
  always_comb o_core6_m0_d_corrupt = o_cores_m0_d_corrupt[6];
  always_comb o_core6_m0_d_data = o_cores_m0_d_data[6];
  always_comb o_core6_m0_d_denied = o_cores_m0_d_denied[6];
  always_comb o_core6_m0_d_opcode = o_cores_m0_d_opcode[6];
  always_comb o_core6_m0_d_param = o_cores_m0_d_param[6];
  always_comb o_core6_m0_d_size = o_cores_m0_d_size[6];
  always_comb o_core6_m0_d_sink = o_cores_m0_d_sink[6];
  always_comb o_core6_m0_d_source = o_cores_m0_d_source[6];
  always_comb o_core6_m0_d_user = o_cores_m0_d_user[6];
  always_comb i_cores_m0_d_ready[6] = i_core6_m0_d_ready;
  always_comb o_core6_m0_d_valid = o_cores_m0_d_valid[6];
  always_comb i_cores_m0_e_sink[6] = i_core6_m0_e_sink;
  always_comb o_core6_m0_e_ready = o_cores_m0_e_ready[6];
  always_comb i_cores_m0_e_valid[6] = i_core6_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[6] = i_core6_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[6] = i_core6_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[6] = i_core6_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[6] = i_core6_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[6] = i_core6_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[6] = i_core6_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[6] = i_core6_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[6] = i_core6_m1_axi_s_arsize;
  always_comb o_core6_m1_axi_s_arready = o_cores_m1_axi_s_arready[6];
  always_comb i_cores_m1_axi_s_arvalid[6] = i_core6_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[6] = i_core6_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[6] = i_core6_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[6] = i_core6_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[6] = i_core6_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[6] = i_core6_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[6] = i_core6_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[6] = i_core6_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[6] = i_core6_m1_axi_s_awsize;
  always_comb o_core6_m1_axi_s_awready = o_cores_m1_axi_s_awready[6];
  always_comb i_cores_m1_axi_s_awvalid[6] = i_core6_m1_axi_s_awvalid;
  always_comb o_core6_m1_axi_s_bid = o_cores_m1_axi_s_bid[6];
  always_comb o_core6_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[6];
  always_comb i_cores_m1_axi_s_bready[6] = i_core6_m1_axi_s_bready;
  always_comb o_core6_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[6];
  always_comb o_core6_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[6];
  always_comb o_core6_m1_axi_s_rid = o_cores_m1_axi_s_rid[6];
  always_comb o_core6_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[6];
  always_comb o_core6_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[6];
  always_comb i_cores_m1_axi_s_rready[6] = i_core6_m1_axi_s_rready;
  always_comb o_core6_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[6];
  always_comb i_cores_m1_axi_s_wdata[6] = i_core6_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[6] = i_core6_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[6] = i_core6_m1_axi_s_wstrb;
  always_comb o_core6_m1_axi_s_wready = o_cores_m1_axi_s_wready[6];
  always_comb i_cores_m1_axi_s_wvalid[6] = i_core6_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[6] = i_core6_m2_a_address;
  always_comb i_cores_m2_a_corrupt[6] = i_core6_m2_a_corrupt;
  always_comb i_cores_m2_a_data[6] = i_core6_m2_a_data;
  always_comb i_cores_m2_a_mask[6] = i_core6_m2_a_mask;
  always_comb i_cores_m2_a_opcode[6] = i_core6_m2_a_opcode;
  always_comb i_cores_m2_a_param[6] = i_core6_m2_a_param;
  always_comb i_cores_m2_a_size[6] = i_core6_m2_a_size;
  always_comb i_cores_m2_a_source[6] = i_core6_m2_a_source;
  always_comb i_cores_m2_a_user[6] = i_core6_m2_a_user;
  always_comb o_core6_m2_a_ready = o_cores_m2_a_ready[6];
  always_comb i_cores_m2_a_valid[6] = i_core6_m2_a_valid;
  always_comb o_core6_m2_d_corrupt = o_cores_m2_d_corrupt[6];
  always_comb o_core6_m2_d_data = o_cores_m2_d_data[6];
  always_comb o_core6_m2_d_denied = o_cores_m2_d_denied[6];
  always_comb o_core6_m2_d_opcode = o_cores_m2_d_opcode[6];
  always_comb o_core6_m2_d_param = o_cores_m2_d_param[6];
  always_comb o_core6_m2_d_size = o_cores_m2_d_size[6];
  always_comb o_core6_m2_d_sink = o_cores_m2_d_sink[6];
  always_comb o_core6_m2_d_source = o_cores_m2_d_source[6];
  always_comb o_core6_m2_d_user = o_cores_m2_d_user[6];
  always_comb i_cores_m2_d_ready[6] = i_core6_m2_d_ready;
  always_comb o_core6_m2_d_valid = o_cores_m2_d_valid[6];

  always_comb i_cores_coherent_enable[7] = i_core7_coherent_enable;
  always_comb o_core7_coherent_state = o_cores_coherent_state[7];
  always_comb i_cores_m0_a_address[7] = i_core7_m0_a_address;
  always_comb i_cores_m0_a_corrupt[7] = i_core7_m0_a_corrupt;
  always_comb i_cores_m0_a_data[7] = i_core7_m0_a_data;
  always_comb i_cores_m0_a_mask[7] = i_core7_m0_a_mask;
  always_comb i_cores_m0_a_opcode[7] = i_core7_m0_a_opcode;
  always_comb i_cores_m0_a_param[7] = i_core7_m0_a_param;
  always_comb i_cores_m0_a_size[7] = i_core7_m0_a_size;
  always_comb i_cores_m0_a_source[7] = i_core7_m0_a_source;
  always_comb i_cores_m0_a_user[7] = i_core7_m0_a_user;
  always_comb o_core7_m0_a_ready = o_cores_m0_a_ready[7];
  always_comb i_cores_m0_a_valid[7] = i_core7_m0_a_valid;
  always_comb o_core7_m0_b_address = o_cores_m0_b_address[7];
  always_comb o_core7_m0_b_corrupt = o_cores_m0_b_corrupt[7];
  always_comb o_core7_m0_b_data = o_cores_m0_b_data[7];
  always_comb o_core7_m0_b_mask = o_cores_m0_b_mask[7];
  always_comb o_core7_m0_b_opcode = o_cores_m0_b_opcode[7];
  always_comb o_core7_m0_b_param = o_cores_m0_b_param[7];
  always_comb o_core7_m0_b_size = o_cores_m0_b_size[7];
  always_comb o_core7_m0_b_source = o_cores_m0_b_source[7];
  always_comb i_cores_m0_b_ready[7] = i_core7_m0_b_ready;
  always_comb o_core7_m0_b_valid = o_cores_m0_b_valid[7];
  always_comb i_cores_m0_c_address[7] = i_core7_m0_c_address;
  always_comb i_cores_m0_c_corrupt[7] = i_core7_m0_c_corrupt;
  always_comb i_cores_m0_c_data[7] = i_core7_m0_c_data;
  always_comb i_cores_m0_c_opcode[7] = i_core7_m0_c_opcode;
  always_comb i_cores_m0_c_param[7] = i_core7_m0_c_param;
  always_comb i_cores_m0_c_size[7] = i_core7_m0_c_size;
  always_comb i_cores_m0_c_source[7] = i_core7_m0_c_source;
  always_comb i_cores_m0_c_user[7] = i_core7_m0_c_user;
  always_comb o_core7_m0_c_ready = o_cores_m0_c_ready[7];
  always_comb i_cores_m0_c_valid[7] = i_core7_m0_c_valid;
  always_comb o_core7_m0_d_corrupt = o_cores_m0_d_corrupt[7];
  always_comb o_core7_m0_d_data = o_cores_m0_d_data[7];
  always_comb o_core7_m0_d_denied = o_cores_m0_d_denied[7];
  always_comb o_core7_m0_d_opcode = o_cores_m0_d_opcode[7];
  always_comb o_core7_m0_d_param = o_cores_m0_d_param[7];
  always_comb o_core7_m0_d_size = o_cores_m0_d_size[7];
  always_comb o_core7_m0_d_sink = o_cores_m0_d_sink[7];
  always_comb o_core7_m0_d_source = o_cores_m0_d_source[7];
  always_comb o_core7_m0_d_user = o_cores_m0_d_user[7];
  always_comb i_cores_m0_d_ready[7] = i_core7_m0_d_ready;
  always_comb o_core7_m0_d_valid = o_cores_m0_d_valid[7];
  always_comb i_cores_m0_e_sink[7] = i_core7_m0_e_sink;
  always_comb o_core7_m0_e_ready = o_cores_m0_e_ready[7];
  always_comb i_cores_m0_e_valid[7] = i_core7_m0_e_valid;
  always_comb i_cores_m1_axi_s_araddr[7] = i_core7_m1_axi_s_araddr;
  always_comb i_cores_m1_axi_s_arburst[7] = i_core7_m1_axi_s_arburst;
  always_comb i_cores_m1_axi_s_arcache[7] = i_core7_m1_axi_s_arcache;
  always_comb i_cores_m1_axi_s_arid[7] = i_core7_m1_axi_s_arid;
  always_comb i_cores_m1_axi_s_arlen[7] = i_core7_m1_axi_s_arlen;
  always_comb i_cores_m1_axi_s_arlock[7] = i_core7_m1_axi_s_arlock;
  always_comb i_cores_m1_axi_s_arprot[7] = i_core7_m1_axi_s_arprot;
  always_comb i_cores_m1_axi_s_arsize[7] = i_core7_m1_axi_s_arsize;
  always_comb o_core7_m1_axi_s_arready = o_cores_m1_axi_s_arready[7];
  always_comb i_cores_m1_axi_s_arvalid[7] = i_core7_m1_axi_s_arvalid;
  always_comb i_cores_m1_axi_s_awaddr[7] = i_core7_m1_axi_s_awaddr;
  always_comb i_cores_m1_axi_s_awburst[7] = i_core7_m1_axi_s_awburst;
  always_comb i_cores_m1_axi_s_awcache[7] = i_core7_m1_axi_s_awcache;
  always_comb i_cores_m1_axi_s_awid[7] = i_core7_m1_axi_s_awid;
  always_comb i_cores_m1_axi_s_awlen[7] = i_core7_m1_axi_s_awlen;
  always_comb i_cores_m1_axi_s_awlock[7] = i_core7_m1_axi_s_awlock;
  always_comb i_cores_m1_axi_s_awprot[7] = i_core7_m1_axi_s_awprot;
  always_comb i_cores_m1_axi_s_awsize[7] = i_core7_m1_axi_s_awsize;
  always_comb o_core7_m1_axi_s_awready = o_cores_m1_axi_s_awready[7];
  always_comb i_cores_m1_axi_s_awvalid[7] = i_core7_m1_axi_s_awvalid;
  always_comb o_core7_m1_axi_s_bid = o_cores_m1_axi_s_bid[7];
  always_comb o_core7_m1_axi_s_bresp = o_cores_m1_axi_s_bresp[7];
  always_comb i_cores_m1_axi_s_bready[7] = i_core7_m1_axi_s_bready;
  always_comb o_core7_m1_axi_s_bvalid = o_cores_m1_axi_s_bvalid[7];
  always_comb o_core7_m1_axi_s_rdata = o_cores_m1_axi_s_rdata[7];
  always_comb o_core7_m1_axi_s_rid = o_cores_m1_axi_s_rid[7];
  always_comb o_core7_m1_axi_s_rlast = o_cores_m1_axi_s_rlast[7];
  always_comb o_core7_m1_axi_s_rresp = o_cores_m1_axi_s_rresp[7];
  always_comb i_cores_m1_axi_s_rready[7] = i_core7_m1_axi_s_rready;
  always_comb o_core7_m1_axi_s_rvalid = o_cores_m1_axi_s_rvalid[7];
  always_comb i_cores_m1_axi_s_wdata[7] = i_core7_m1_axi_s_wdata;
  always_comb i_cores_m1_axi_s_wlast[7] = i_core7_m1_axi_s_wlast;
  always_comb i_cores_m1_axi_s_wstrb[7] = i_core7_m1_axi_s_wstrb;
  always_comb o_core7_m1_axi_s_wready = o_cores_m1_axi_s_wready[7];
  always_comb i_cores_m1_axi_s_wvalid[7] = i_core7_m1_axi_s_wvalid;
  always_comb i_cores_m2_a_address[7] = i_core7_m2_a_address;
  always_comb i_cores_m2_a_corrupt[7] = i_core7_m2_a_corrupt;
  always_comb i_cores_m2_a_data[7] = i_core7_m2_a_data;
  always_comb i_cores_m2_a_mask[7] = i_core7_m2_a_mask;
  always_comb i_cores_m2_a_opcode[7] = i_core7_m2_a_opcode;
  always_comb i_cores_m2_a_param[7] = i_core7_m2_a_param;
  always_comb i_cores_m2_a_size[7] = i_core7_m2_a_size;
  always_comb i_cores_m2_a_source[7] = i_core7_m2_a_source;
  always_comb i_cores_m2_a_user[7] = i_core7_m2_a_user;
  always_comb o_core7_m2_a_ready = o_cores_m2_a_ready[7];
  always_comb i_cores_m2_a_valid[7] = i_core7_m2_a_valid;
  always_comb o_core7_m2_d_corrupt = o_cores_m2_d_corrupt[7];
  always_comb o_core7_m2_d_data = o_cores_m2_d_data[7];
  always_comb o_core7_m2_d_denied = o_cores_m2_d_denied[7];
  always_comb o_core7_m2_d_opcode = o_cores_m2_d_opcode[7];
  always_comb o_core7_m2_d_param = o_cores_m2_d_param[7];
  always_comb o_core7_m2_d_size = o_cores_m2_d_size[7];
  always_comb o_core7_m2_d_sink = o_cores_m2_d_sink[7];
  always_comb o_core7_m2_d_source = o_cores_m2_d_source[7];
  always_comb o_core7_m2_d_user = o_cores_m2_d_user[7];
  always_comb i_cores_m2_d_ready[7] = i_core7_m2_d_ready;
  always_comb o_core7_m2_d_valid = o_cores_m2_d_valid[7];

  ax65_l2_wrapper #(
    .CORE_WIDTH(CORE_WIDTH),
    .L2C_BANK_WIDTH(L2C_BANK_WIDTH),
    .L2C_BANK_DATA_WIDTH(L2C_BANK_DATA_WIDTH),
    .L2C_BANK_TAG_WIDTH(L2C_BANK_TAG_WIDTH),
    .SINK_WIDTH(SINK_WIDTH),
    .SOURCE_WIDTH(SOURCE_WIDTH),
    .CTRL_IN_WIDTH(CTRL_IN_WIDTH),
    .CTRL_OUT_WIDTH(CTRL_OUT_WIDTH)
  ) u_ax65_l2_wrapper (
    .i_test_mode(test_mode),
    .i_iocp_aclk(i_aclk),
    .i_mem_aclk(i_aclk),
    .i_mmio_aclk(i_aclk),
    .i_mmio_arst_n(i_arst_n),
    .i_l2c_banks_clk({L2C_BANK_WIDTH{i_l2c_banks_clk}}),
    .i_l2c_banks_clk_en({L2C_BANK_WIDTH{i_l2c_banks_clk_en}}),
    .*
  );

endmodule
