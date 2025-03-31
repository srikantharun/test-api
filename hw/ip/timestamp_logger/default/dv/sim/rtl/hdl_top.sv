// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Top-level TestBench instancing and connecting the DUT with the AXI Master and Slave Interfaces
// Owner: Andrew.Bond
// --------------------------------------------------

`include "axi_intf.sv"

module hdl_top;
  // Time unit and precision
  timeunit 1ns;
  timeprecision 1ps;

  // Packages import
  import tb_axi_pkg::*;
  import uvm_pkg::*;
  import tb_axi_pkg::*;
  import timestamp_logger_uvm_pkg::*;


  localparam real         clk_freq_mhz = 1200.0;

  //--------------------------------------------------
  // DUT Port Signals
  //--------------------------------------------------
  // Clock, positive edge triggered
  logic clk, clk_en;
  // Asynchronous reset, active low
  logic  rst, rst_n;

  // =============================================================================================================
  // AXI
  // =============================================================================================================
  axi_intf #(
    .DW (`DW),
    .AW (`AW),
    .IDW(`SIDW)
  ) axi_if ();

  axi_intf #(
    .DW (`DW),
    .AW (`AW),
    .IDW(`MIDW)
  ) axi_if_m ();

  assign axi_if.clk     = clk;
  assign axi_if.rst_n   = rst_n;
  assign axi_if_m.clk   = clk;
  assign axi_if_m.rst_n = rst_n;

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

  // Generate the clock
  initial begin
    u_clk_generator.set_clock(.freq_mhz(clk_freq_mhz), .duty(50));
    clk_en = 1'b1;
  end

  initial begin
    u_rst_generator.async_rst(.duration_ns(10));
  end

  // =============================================================================================================
  // DUT
  // =============================================================================================================
  timestamp_logger_event_if u_event_if (.clk(clk), .rst_n(rst_n));
  always_comb u_event_if.timestamp      = i_dut.timestamp; // Yes, hacky but assertions check the counter and this keeps model simple
  always_comb u_event_if.capture_enable = i_dut.capture_en; // TODO
  `DUT #(
    .NumGroups(`NUM_GROUPS),
    .AxiSIdWidth(`SIDW),
    .AxiMIdWidth(`MIDW),
    .AxiAddrWidth(`AW),
    .AxiDataWidth(`DW),
    .GroupMsgWidth(`GROUP_MSG_WIDTH),
    .GroupFifoDepth(`GROUP_FIFO_DEPTH),
    .TimestampFifoDepth(`TIMESTAMP_FIFO_DEPTH),
    .MemDepth(`MEM_DEPTH),
    .UseMacro(`USE_MACRO),
    .REGION_ST_ADDR({`CSR_ST_ADDR, `MEM_ST_ADDR}),
    .REGION_END_ADDR({`CSR_END_ADDR, `MEM_END_ADDR})
  ) i_dut (
    .i_clk  (clk),
    .i_rst_n(rst_n),

    .i_scan_en(1'b0),

    .i_group_trigger(u_event_if.group_triggers),
    .i_group_message(u_event_if.group_msgs),

    .i_sync_start(u_event_if.sync_start),

    .i_axi_s_aw_id(axi_if.awid),
    .i_axi_s_aw_addr(axi_if.awaddr),
    .i_axi_s_aw_len(axi_if.awlen),
    .i_axi_s_aw_size(axi_if.awsize),
    .i_axi_s_aw_burst(axi_if.awburst),
    .i_axi_s_aw_valid(axi_if.awvalid),
    .o_axi_s_aw_ready(axi_if.awready),

    .i_axi_s_ar_id(axi_if.arid),
    .i_axi_s_ar_addr(axi_if.araddr),
    .i_axi_s_ar_len(axi_if.arlen),
    .i_axi_s_ar_size(axi_if.arsize),
    .i_axi_s_ar_burst(axi_if.arburst),
    .i_axi_s_ar_valid(axi_if.arvalid),
    .o_axi_s_ar_ready(axi_if.arready),

    .i_axi_s_w_data (axi_if.wdata),
    .i_axi_s_w_strb (axi_if.wstrb),
    .i_axi_s_w_last (axi_if.wlast),
    .i_axi_s_w_valid(axi_if.wvalid),
    .o_axi_s_w_ready(axi_if.wready),

    .o_axi_s_r_id(axi_if.rid),
    .o_axi_s_r_data(axi_if.rdata),
    .o_axi_s_r_resp(axi_if.rresp),
    .o_axi_s_r_last(axi_if.rlast),
    .o_axi_s_r_valid(axi_if.rvalid),
    .i_axi_s_r_ready(axi_if.rready),

    .o_axi_s_b_id(axi_if.bid),
    .o_axi_s_b_resp(axi_if.bresp),
    .o_axi_s_b_valid(axi_if.bvalid),
    .i_axi_s_b_ready(axi_if.bready),

    .o_axi_m_aw_id(axi_if_m.awid),
    .o_axi_m_aw_addr(axi_if_m.awaddr),
    .o_axi_m_aw_len(axi_if_m.awlen),
    .o_axi_m_aw_size(axi_if_m.awsize),
    .o_axi_m_aw_burst(axi_if_m.awburst),
    .o_axi_m_aw_valid(axi_if_m.awvalid),
    .i_axi_m_aw_ready(axi_if_m.awready),

    .o_axi_m_ar_id(axi_if_m.arid),
    .o_axi_m_ar_addr(axi_if_m.araddr),
    .o_axi_m_ar_len(axi_if_m.arlen),
    .o_axi_m_ar_size(axi_if_m.arsize),
    .o_axi_m_ar_burst(axi_if_m.arburst),
    .o_axi_m_ar_valid(axi_if_m.arvalid),
    .i_axi_m_ar_ready(axi_if_m.arready),

    .o_axi_m_w_data (axi_if_m.wdata),
    .o_axi_m_w_strb (axi_if_m.wstrb),
    .o_axi_m_w_last (axi_if_m.wlast),
    .o_axi_m_w_valid(axi_if_m.wvalid),
    .i_axi_m_w_ready(axi_if_m.wready),

    .i_axi_m_r_id(axi_if_m.rid),
    .i_axi_m_r_data(axi_if_m.rdata),
    .i_axi_m_r_resp(axi_if_m.rresp),
    .i_axi_m_r_last(axi_if_m.rlast),
    .i_axi_m_r_valid(axi_if_m.rvalid),
    .o_axi_m_r_ready(axi_if_m.rready),

    .i_axi_m_b_id(axi_if_m.bid),
    .i_axi_m_b_resp(axi_if_m.bresp),
    .i_axi_m_b_valid(axi_if_m.bvalid),
    .o_axi_m_b_ready(axi_if_m.bready),

    .o_ip_csr_req(),
    .i_ip_csr_rsp('0),

    .i_sram_impl('0),
    .o_sram_impl()
  );

  // Run test
  initial begin
    import uvm_pkg::uvm_config_db;

    uvm_config_db#(virtual timestamp_logger_event_if)::set(uvm_root::get(),                "*", "event_vif",  u_event_if);
    uvm_config_db#(virtual axi_intf#(.DW(`DW),.AW(`AW),.IDW(`SIDW)))::set(uvm_root::get(), "*", "cfg_vif",    axi_if);
    uvm_config_db#(virtual axi_intf#(.DW(`DW),.AW(`AW),.IDW(`MIDW)))::set(uvm_root::get(), "*", "extmem_vif", axi_if_m);
    run_test();
  end

endmodule : hdl_top
