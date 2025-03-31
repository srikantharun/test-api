// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
//   Top-level TestBench instancing and connecting the DUT
// Owner: Andrew.Bond
// --------------------------------------------------

`ifndef DATAW
  `define DATAW 64
`endif
`ifndef DEPTH
  `define DEPTH 1024
`endif
`ifndef MACRO_DATAW
  `define MACRO_DATAW `DATAW
`endif
`ifndef MACRO_DEPTH
  `define MACRO_DEPTH `DEPTH
`endif

module hdl_top;
  // Time unit and precision
  timeunit 1ns;
  timeprecision 1ps;

  // Packages import
  import uvm_pkg::*;
  import noc_mem_uvm_pkg::*;

  parameter real         clk_freq_mhz           = 1200.0;

// =============================================================================================================
// CLOCK and RESET Generators
// =============================================================================================================
  // Clock, positive edge triggered
  logic clk, clk_en;

  axe_clk_generator u_clk_generator(
    .i_enable(clk_en),
    .o_clk(clk)
    );

  // Asynchronous reset, active low
  logic  rst, rst_n;

  axe_rst_generator u_rst_generator(
    .i_clk(clk),
    .o_rst(rst)
    );

  assign rst_n = ~rst;

// =============================================================================================================
// Ticker
// =============================================================================================================
  axe_timeout u_axe_timeout();

  initial begin
    u_axe_timeout.ticker(200);
  end

// =============================================================================================================
// Read / Write Interfaces
// =============================================================================================================
  noc_mem_rd_if #(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) rd_if (.clk(clk),  .rst_n(rst_n));
  noc_mem_wr_if #(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))) wr_if (.clk(clk),  .rst_n(rst_n));

// =============================================================================================================
//  DUT
// =============================================================================================================

noc_common_mem_wrap_top #(
    .DATAW(`DATAW),
    .DEPTH(`DEPTH),
    .MACRO_DATAW(`MACRO_DATAW),
    .MACRO_DEPTH(`MACRO_DEPTH)
) u_dut (
    .Clk(clk),
    .RstN(rst_n),
    .RdEn(rd_if.en),
    .RdAddr(rd_if.addr),
    .RdData(rd_if.data),
    .WrEn(wr_if.en),
    .WrAddr(wr_if.addr),
    .WrBitEn(wr_if.ben),
    .WrData(wr_if.data),
    .se('0),
    .pde('0),
    .prn( ),
    .ret('0)
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

    uvm_config_db#(virtual noc_mem_rd_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::set(uvm_root::get(), "uvm_test_top.m_env", "rd_vif",    rd_if);
    uvm_config_db#(virtual noc_mem_wr_if#(.DATAW(`DATAW), .ADDRW($clog2(`DEPTH))))::set(uvm_root::get(), "uvm_test_top.m_env", "wr_vif",    wr_if);

  end

  // Run test
  initial begin
    run_test();
  end

endmodule : hdl_top
