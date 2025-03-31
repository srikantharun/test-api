// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Top-level TestBench instancing and connecting the DUT with the AXI Master and Slave Interfaces
// Owner: Sultan.Khan
// --------------------------------------------------

`ifndef AIC_DP_CMD_GEN_COMMAND_TYPE
  `define AIC_DP_CMD_GEN_COMMAND_TYPE aic_dp_cmd_gen_pkg::dummy_dp_command_t
`endif

`ifndef AIC_DP_CMD_GEN_COMMAND_DEPTH
  `define AIC_DP_CMD_GEN_COMMAND_DEPTH 1024
`endif

`ifndef AIC_DP_CMD_GEN_MAX_OUTSTANDING
  `define AIC_DP_CMD_GEN_MAX_OUTSTANDING 3
`endif

// This introduces the AXI Master and Slave VIP Interfaces
`define AXI_VIP


module hdl_top;
  // Time unit and precision
  timeunit 1ns;
  timeprecision 1ps;

  // Packages import
  import aic_common_pkg::*;
  import axi_pkg::*;
  import uvm_pkg::*;
  import ai_core_dp_cmd_gen_uvm_pkg::*;
  import common_seq_lib_uvm_pkg::*;

`ifdef AXI_VIP
  import svt_uvm_pkg::*;
  import svt_axi_uvm_pkg::*;
`endif

  parameter real         clk_freq_mhz           = 1200.0;
  parameter int unsigned DpCommandMemoryDepth   = `AIC_DP_CMD_GEN_COMMAND_DEPTH;
  parameter int unsigned MaxOutstanding         = `AIC_DP_CMD_GEN_MAX_OUTSTANDING;
  parameter type         dp_command_t           = `AIC_DP_CMD_GEN_COMMAND_TYPE;
  parameter int unsigned AxiIdWidth             = aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH;
  parameter int unsigned AxiAddrWidth           = aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH;
  parameter int unsigned AxiDataWidth           = aic_common_pkg::AIC_LT_AXI_DATA_WIDTH;
  parameter int unsigned AxiStrbWidth           = AxiDataWidth / 8;

  //--------------------------------------------------
  // DUT Port Signals
  //--------------------------------------------------
  // Clock, positive edge triggered
  logic clk, clk_en;
  // Asynchronous reset, active low
  logic  rst, rst_n;

  /////////////////////////////
  // CMD Block Command Input //
  /////////////////////////////
  dp_cmd_gen_cmdb_if cmdb_if(.clk(clk),  .rst_n(rst_n));

  ////////////////////////////////////
  // Datapath Command Stream Output //
  ////////////////////////////////////
  dp_cmd_gen_command_if#(.dp_command_t(dp_command_t)) command_if(.clk(clk), .rst_n(rst_n));

  axe_gnt u_command_gnt_delay(.clk(clk),
                              .rst_n(rst_n),
                              .req(command_if.command_valid),
                              .gnt(command_if.command_ready)
                             );

  axe_delay u_command_done_delay(.clk(clk),
                                 .rst_n(rst_n),
                                 .inp(command_if.command_last && command_if.command_valid && command_if.command_ready),
                                 .oup(command_if.command_done)
                                );

  initial begin
    u_command_gnt_delay.add_range(0, 10, 1);
    u_command_done_delay.add_range(0, 10, 1);
  end

`ifdef AXI_VIP

  // VIP Interface instance representing the AXI system
  // Number of AXI Master and Slave VIPs defined by uvm/env/axi_vip_config.sv
  //   - 1 AXI MASTER VIP
  // Connect up the clks and resets to the VIPs

  svt_axi_if axi_if ();
  assign axi_if.common_aclk        = clk;
  assign axi_if.master_if[0].aclk  = clk;

  assign axi_if.master_if[0].aresetn =  rst_n;

  axi_reset_if axi_reset_if ();
  assign axi_reset_if.clk = clk;

`endif


// =============================================================================================================
// Assign the DUT Ports to various interfaces.
// =============================================================================================================


// =============================================================================================================
// CLOCK and RESET Generators
// =============================================================================================================

  axe_clk_generator u_clk_generator(
    .i_enable(clk_en),
    .o_clk(clk)
    );

  axe_rst_generator u_rst_generator(
    .i_clk(clk),
    .o_rst(rst)
    );

  assign rst_n = ~rst;

  // =============================================================================================================
  // Instantiate test harness/DUT
  // =============================================================================================================
 aic_dp_cmd_gen #(
  .AxiIdWidth(AxiIdWidth),
  .AxiAddrWidth(AxiAddrWidth),
  .AxiDataWidth(AxiDataWidth),
  .AxiEndpointStart('0),
  .AxiEndpointSize('h1_0000),
  .DpCommandMemoryDepth(DpCommandMemoryDepth),
  .MaxOutstanding(MaxOutstanding),
  .dp_command_t(dp_command_t)
 ) u_dut (
  .i_clk                             ( clk                         ),
  .i_rst_n                           ( rst_n                       ),
  .i_flush                           ( cmdb_if.cmdb_flush          ),
  .i_test_mode                       ( 1'b0                        ),

  .i_cmdb_command                    ( cmdb_if.cmdb_command        ),
  .i_cmdb_format                     ( cmdb_if.cmdb_format         ),
  .i_cmdb_config                     ( '0                          ), // TODO(@andrew.bond)
  .i_cmdb_valid                      ( cmdb_if.cmdb_valid          ),
  .o_cmdb_ready                      ( cmdb_if.cmdb_ready          ),
  .o_cmdb_done                       ( cmdb_if.cmdb_done           ),

  //// AXI subordinate
  // Write Address Channel
  .i_axi_s_aw_id                     ( axi_if.master_if[0].awid),
  .i_axi_s_aw_addr                   ( axi_if.master_if[0].awaddr[AxiAddrWidth-1:0]  ),
  .i_axi_s_aw_len                    ( axi_if.master_if[0].awlen   ),
  .i_axi_s_aw_size                   ( axi_if.master_if[0].awsize  ),
  .i_axi_s_aw_burst                  ( axi_if.master_if[0].awburst ),
  .i_axi_s_aw_valid                  ( axi_if.master_if[0].awvalid ),
  .o_axi_s_aw_ready                  ( axi_if.master_if[0].awready ),
  // Read Address Channel
  .i_axi_s_ar_id                     ( axi_if.master_if[0].arid),
  .i_axi_s_ar_addr                   ( axi_if.master_if[0].araddr[AxiAddrWidth-1:0]  ),
  .i_axi_s_ar_len                    ( axi_if.master_if[0].arlen   ),
  .i_axi_s_ar_size                   ( axi_if.master_if[0].arsize  ),
  .i_axi_s_ar_burst                  ( axi_if.master_if[0].arburst ),
  .i_axi_s_ar_valid                  ( axi_if.master_if[0].arvalid ),
  .o_axi_s_ar_ready                  ( axi_if.master_if[0].arready ),
  // Write Data Channel
  .i_axi_s_w_data                    ( axi_if.master_if[0].wdata   ),
  .i_axi_s_w_strb                    ( axi_if.master_if[0].wstrb   ),
  .i_axi_s_w_last                    ( axi_if.master_if[0].wlast   ),
  .i_axi_s_w_valid                   ( axi_if.master_if[0].wvalid  ),
  .o_axi_s_w_ready                   ( axi_if.master_if[0].wready  ),
  // Read Data Channel
  .o_axi_s_r_id                      ( axi_if.master_if[0].rid),
  .o_axi_s_r_data                    ( axi_if.master_if[0].rdata   ),
  .o_axi_s_r_resp                    ( axi_if.master_if[0].rresp   ),
  .o_axi_s_r_last                    ( axi_if.master_if[0].rlast   ),
  .o_axi_s_r_valid                   ( axi_if.master_if[0].rvalid  ),
  .i_axi_s_r_ready                   ( axi_if.master_if[0].rready  ),
  // Write Response Channel
  .o_axi_s_b_id                      ( axi_if.master_if[0].bid     ),
  .o_axi_s_b_resp                    ( axi_if.master_if[0].bresp   ),
  .o_axi_s_b_valid                   ( axi_if.master_if[0].bvalid  ),
  .i_axi_s_b_ready                   ( axi_if.master_if[0].bready  ),

  .o_dp_command_data                 ( command_if.command_data         ),
  .o_dp_command_metadata             ( command_if.command_metadata     ),
  .o_dp_command_iterations           ( command_if.command_iterations   ),
  .o_dp_command_last                 ( command_if.command_last         ),
  .o_dp_command_valid                ( command_if.command_valid        ),
  .i_dp_command_ready                ( command_if.command_ready        ),
  .i_dp_done                         ( command_if.command_done         ),

  .o_errors                          ( cmdb_if.cmdb_errors         ),

  .i_ram_impl                        ( '0                          ),
  .o_ram_impl                        (                             )
);

  // =============================================================================================================
  // Reset and clock generation
  // =============================================================================================================
  // Generate the clock
  initial begin
    u_clk_generator.set_clock(.freq_mhz(clk_freq_mhz), .duty(50));
    clk_en = 1'b1;
  end

  initial begin
    u_rst_generator.async_rst(.duration_ns(10));
  end

  // =============================================================================================================
  initial begin
    import uvm_pkg::uvm_config_db;

    uvm_config_db#(virtual dp_cmd_gen_cmdb_if)::set(uvm_root::get(),                                  "uvm_test_top.m_env", "cmdb_vif",    cmdb_if);
    uvm_config_db#(virtual dp_cmd_gen_command_if#(.dp_command_t(dp_command_t)))::set(uvm_root::get(), "uvm_test_top.m_env", "command_vif", command_if);

    `ifdef AXI_VIP

    // Set the reset interface on the virtual sequencer
    uvm_config_db#(virtual axi_reset_if.axi_reset_modport)::set(uvm_root::get(), "uvm_test_top.m_env.sequencer", "reset_mp", axi_reset_if.axi_reset_modport);

    // =============================================================================================================
    // Provide the AXI SV interface to the AXI System ENV. This step establishes the connection between the AXI
    // System ENV and the DUT through the AXI interface.
    // =============================================================================================================
    uvm_config_db#(svt_axi_vif)::set(uvm_root::get(), "uvm_test_top.m_env.axi_system_env", "vif", axi_if);
    `endif
  end

  // Run test
  initial begin
    run_test();
  end

  // AXI Monitor
  axe_axi4_csv#(.NAME("m"),
                .AXI_DATA_WIDTH(aic_common_pkg::AIC_LT_AXI_DATA_WIDTH),
                .AXI_ADDR_WIDTH(aic_common_pkg::AIC_LT_AXI_LOCAL_ADDR_WIDTH),
                .AXI_ID_WIDTH(aic_common_pkg::AIC_LT_AXI_S_ID_WIDTH)
) u_axi4_csv (
    .aclk         (clk),
    .arstn        (rst_n),
    .awaddr       (axi_if.master_if[0].awaddr ),
    .awid         (axi_if.master_if[0].awid   ),
    .awburst      (axi_if.master_if[0].awburst),
    .awsize       (axi_if.master_if[0].awsize ),
    .awcache      (axi_if.master_if[0].awcache),
    .awlen        (axi_if.master_if[0].awlen  ),
    .awprot       (axi_if.master_if[0].awprot ),
    .awlock       (axi_if.master_if[0].awlock ),
    .awready      (axi_if.master_if[0].awready),
    .awvalid      (axi_if.master_if[0].awvalid),
    .awqos        (axi_if.master_if[0].awqos  ),
    .wdata        (axi_if.master_if[0].wdata  ),
    .wstrb        (axi_if.master_if[0].wstrb  ),
    .wlast        (axi_if.master_if[0].wlast  ),
    .wready       (axi_if.master_if[0].wready ),
    .wvalid       (axi_if.master_if[0].wvalid ),
    .bid          (axi_if.master_if[0].bid    ),
    .bresp        (axi_if.master_if[0].bresp  ),
    .bready       (axi_if.master_if[0].bready ),
    .bvalid       (axi_if.master_if[0].bvalid ),
    .araddr       (axi_if.master_if[0].araddr ),
    .arid         (axi_if.master_if[0].arid   ),
    .arburst      (axi_if.master_if[0].arburst),
    .arsize       (axi_if.master_if[0].arsize ),
    .arcache      (axi_if.master_if[0].arcache),
    .arlen        (axi_if.master_if[0].arlen  ),
    .arprot       (axi_if.master_if[0].arprot ),
    .arlock       (axi_if.master_if[0].arlock ),
    .arready      (axi_if.master_if[0].arready),
    .arvalid      (axi_if.master_if[0].arvalid),
    .arqos        (axi_if.master_if[0].arqos  ),
    .rid          (axi_if.master_if[0].rid    ),
    .rdata        (axi_if.master_if[0].rdata  ),
    .rresp        (axi_if.master_if[0].rresp  ),
    .rlast        (axi_if.master_if[0].rlast  ),
    .rready       (axi_if.master_if[0].rready ),
    .rvalid       (axi_if.master_if[0].rvalid )
  );

endmodule : hdl_top
