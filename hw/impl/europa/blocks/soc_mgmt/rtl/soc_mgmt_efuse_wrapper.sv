// (C) Copyright Axelera AI 2022
// All Rights Reserved
// *** Axelera AI Confidential ***

// Description: eFUSE wrapper.

// Module declaration

module soc_mgmt_efuse_wrapper
  # (
      parameter int unsigned SOC_MGMT_EFUSE_ADDR_W = 14
    )
    (
      // Group: services
      /// OTP wrapper clock and APB clock. Free running, initially at 20MHz. Range 20MHz to 800MHz.
      input  wire          i_clk,
      /// Asynchronous assert, synchronous deassert active low reset.
      input  wire          i_rst_n,

      // Group: efuse
      // The Efuse interface from TESSENT needs to be finalized and added here.

      // Efuse interface analog signals.
      inout  wire io_efuse_vqps,
      inout  wire io_efuse_vddwl
    );


  //wire vdd = 1'b1;
  //wire vss = 1'b1;

  logic i_efuse_csb;
  logic i_efuse_strobe;
  logic i_efuse_load;
  logic i_efuse_pgenb;
  logic i_efuse_psm;
  logic [SOC_MGMT_EFUSE_ADDR_W-1:0] i_efuse_a;
  logic [39:0] o_efuse_q;
  logic i_efuse_te;
  logic [2:0] i_efuse_ts;
  logic [1:0] o_efuse_qt;
  logic [1:0] i_efuse_pmr;
  logic i_efuse_vddrdy;


  // TODO - The Tessent interface glue logic required to connect and drive the eFUSE module.
  assign i_efuse_csb = '0;
  assign i_efuse_strobe = '0;
  assign i_efuse_load = '0;
  assign i_efuse_pgenb = '0;
  assign i_efuse_psm = '0;
  assign i_efuse_a = '0;
  assign i_efuse_te = '0;
  assign i_efuse_ts = '0;
  assign i_efuse_pmr = '0;
  assign i_efuse_vddrdy = '0;

  efuse_wrapper u_efuse_wrapper (
    .i_efuse_csb        (i_efuse_csb),
    .i_efuse_strobe     (i_efuse_strobe),
    .i_efuse_load       (i_efuse_load),
    .i_efuse_pgenb      (i_efuse_pgenb),
    .i_efuse_psm        (i_efuse_psm),
    .i_efuse_a          (i_efuse_a),
    .o_efuse_q          (o_efuse_q),
    .i_efuse_te         (i_efuse_te),
    .i_efuse_ts         (i_efuse_ts),
    .o_efuse_qt         (o_efuse_qt),
    .i_efuse_pmr        (i_efuse_pmr),
    .i_efuse_vddrdy     (i_efuse_vddrdy),
    `ifdef POWER_PINS
    //.VDD        (),
    //.VSS        (),
    `endif
    .io_efuse_vqps      (io_efuse_vqps),
    .io_efuse_vddwl     (io_efuse_vddwl)
  );

endmodule
