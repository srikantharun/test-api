// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>


// IP design testbench for the OTP wrapper
//
module otp_design_tb;
  import uvm_pkg::*;
  `include "uvm_macros.svh"

  import otp_wrapper_csr_reg_pkg::*;
  import otp_wrapper_pkg::*;

  localparam APB_ADDR_W = 32;
  localparam APB_DATA_W = 32;
  localparam APB_STRB_W = 4;

  typedef logic [APB_ADDR_W-1:0] paddr_t;
  typedef logic [APB_DATA_W-1:0] pdata_t;
  typedef logic [APB_STRB_W-1:0] pstrb_t;

  // --------------------------------------------------------------------------
  // Signal declarations
  // --------------------------------------------------------------------------
  logic                        i_clk;
  logic                        i_rst_n;
  logic                        i_analog_clk;
  apb_h2d_t                    i_apb;
  apb_d2h_t                    o_apb;
  logic                        i_otp_clear;
  logic                        o_otp_clear_ack;
  logic                        o_lcs_valid;
  logic                        o_lcs_is_chip_wafer_test;
  logic                        o_lcs_is_chip_perso;
  logic                        o_lcs_is_user_delivery;
  logic                        o_lcs_is_user_secured;
  logic                        o_lcs_is_user_decommissioned;
  logic                        o_lcs_is_chip_field_return;
  logic                        o_lcs_is_terminated;
  logic                        i_dft_scan_test_mode;
  logic                        i_dft_otp_test_mode;
  logic  [OTP_BIT_ADDR_W-1:0]  i_dft_otp_tst_a;
  logic                        i_dft_otp_tst_din;
  logic                        i_dft_otp_tst_readen;
  logic                        i_dft_otp_tst_ceb;
  logic                        i_dft_otp_tst_cle;
  logic                        i_dft_otp_tst_dle;
  logic                        i_dft_otp_tst_web;
  logic                        i_dft_otp_tst_rstb;
  logic                        i_dft_otp_tst_cpumpen;
  logic                        i_dft_otp_tst_pgmen;
  logic                        i_dft_otp_tst_seltm;
  logic                        i_dft_otp_tst_vddrdy;
  logic                        i_dft_otp_tst_clken;
  logic  [OTP_DATA_W-1:0]      o_dft_otp_tst_d;
  logic  [OTP_LOCK_DEPTH-1:0]  o_dft_otp_tst_lock;

  wire                         io_otp_vtdo;
  wire                         io_otp_vrefm;
  wire                         io_otp_vpp;

  pdata_t                      otp_rdata;
  pdata_t                      otp_wdata;
  paddr_t                      otp_addr[4];

  // --------------------------------------------------------------------------
  // Test
  // --------------------------------------------------------------------------
  initial begin

    i_dft_otp_test_mode = 1'b0;
    i_dft_scan_test_mode = 1'b0;
    i_otp_clear = 1'b0;
    i_apb = otp_wrapper_csr_reg_pkg::apb_h2d_t'(0);

    @(posedge i_rst_n);

    // Wait for end of OTP command FSM read commands
    @(posedge o_lcs_valid);
    @(posedge i_clk);

    // Check lifecycle state
    if (!o_lcs_is_chip_perso) begin
      `uvm_error("TEST ERROR", "OTP lifecycle state != CHIP_PERSO")
      $error();
    end else begin
      `uvm_info("TEST INFO ", "OTP lifecycle state == CHIP_PERSO", UVM_NONE)
    end

    otp_wdata = 'hDEAD_BEEF;
    otp_addr  = {
      32'h0000_0004,
      32'h0000_0008,
      32'h0000_000C,
      32'h0000_0010
    };

    // Set OTP smart enable ON
    apb_wr(otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_CONTROL_OFFSET, 32'h0000_0002);

    foreach (otp_addr[i]) begin
      apb_wr(otp_addr[i], otp_wdata);
      apb_rd(otp_addr[i], otp_rdata);

      // Check read value
      if (otp_rdata != otp_wdata) begin
        `uvm_error("TEST ERROR", $sformatf("OTP read fail: address = %h, expected = %h , actual = %h", otp_addr[i], otp_wdata, otp_rdata))
        $error();
      end else begin
        `uvm_info("TEST INFO ", $sformatf("OTP read OK  : address = %h, expected = %h , actual = %h", otp_addr[i], otp_wdata, otp_rdata), UVM_NONE)
      end

      // Check for write errors
      apb_rd(otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_STATUS_OFFSET, otp_rdata);

      if (otp_rdata[0]) begin
        `uvm_error("TEST ERROR", $sformatf("OTP read status is program error for address = %h", otp_addr[i]))
        $error();
      end
    end

    otp_addr  = {
      32'h0000_0014,
      32'h0000_0018,
      32'h0000_001C,
      32'h0000_0020
    };

    // Set OTP smart enable OFF
    apb_wr(otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_CONTROL_OFFSET, 32'h0000_0000);

    foreach (otp_addr[i]) begin
      apb_wr(otp_addr[i], otp_wdata);
      apb_rd(otp_addr[i], otp_rdata);

      // Check read value
      if (otp_rdata != otp_wdata) begin
        `uvm_error("TEST ERROR", $sformatf("OTP read fail: address = %h, expected = %h , actual = %h", otp_addr[i], otp_wdata, otp_rdata))
        $error();
      end else begin
        `uvm_info("TEST INFO ", $sformatf("OTP read OK  : address = %h, expected = %h , actual = %h", otp_addr[i], otp_wdata, otp_rdata), UVM_NONE)
      end

      // Check for write error flag
      apb_rd(otp_wrapper_csr_reg_pkg::OTP_WRAPPER_CSR_STATUS_OFFSET, otp_rdata);

      if (otp_rdata[0]) begin
        `uvm_error("TEST ERROR", $sformatf("OTP read status is program error for address = %h", otp_addr[i]))
        $error();
      end
    end

    $finish();

  end

  // --------------------------------------------------------------------------
  // Design Under Test (DUT)
  // --------------------------------------------------------------------------
  otp_wrapper u_otp_wrapper(.*);

  // --------------------------------------------------------------------------
  // Clocks: 50MHz (digital wrapper), 3MHz (analog OTP CLK)
  // --------------------------------------------------------------------------
  logic clk_en;
  axe_clk_generator u_axe_clk_generator(
    .i_enable(clk_en),
    .o_clk(i_clk)
  );

  axe_clk_generator u_axe_analog_clk_generator(
    .i_enable(clk_en),
    .o_clk(i_analog_clk)
  );

  initial begin
    u_axe_clk_generator.set_clock(.freq_mhz(50), .duty(50));
    u_axe_analog_clk_generator.set_clock(.freq_mhz(3), .duty(50));
    clk_en = 1'b1;
  end

  // --------------------------------------------------------------------------
  // Reset
  // --------------------------------------------------------------------------
  logic reset;
  axe_rst_generator u_axe_rst_generator(
    .i_clk(i_clk),
    .o_rst(reset)
  );

  always_comb i_rst_n = ~reset;

  initial begin
      u_axe_rst_generator.async_rst(.duration_ns(1000));
  end


  // --------------------------------------------------------------------------
  // Useful tasks
  // --------------------------------------------------------------------------

  task apb_rd (input paddr_t paddr, output pdata_t prdata);

    @(posedge i_clk);
    i_apb.pwrite = 1'b0;
    i_apb.paddr = paddr;
    i_apb.psel = 1'b1;
    @(posedge i_clk);
    i_apb.penable = 1'b1;
    // Wait for pready
    while (!o_apb.pready) begin
      @(posedge i_clk);
    end
    i_apb.psel = 1'b0;
    i_apb.penable = 1'b0;

    prdata = o_apb.prdata;

  endtask

  task apb_wr (input paddr_t paddr, input pdata_t pwdata);

    @(posedge i_clk);
    i_apb.pwrite = 1'b1;
    i_apb.paddr = paddr;
    i_apb.pwdata = pwdata;
    i_apb.pstrb = APB_STRB_W'('1);
    i_apb.psel = 1'b1;
    @(posedge i_clk);
    i_apb.penable = 1'b1;
    // Wait for pready
    while (!o_apb.pready) begin
      @(posedge i_clk);
    end
    i_apb.psel = 1'b0;
    i_apb.penable = 1'b0;
    i_apb.pstrb = APB_STRB_W'('0);
    i_apb.pwrite = 1'b0;

  endtask

endmodule
