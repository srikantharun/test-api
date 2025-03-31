// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

// Manager
bind axe_ahb_error_sub snps_ahb_lite_master_aip
#(.ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .CONFIG_X_CHECK  (1),
  .LOCKIDLE_RCMND  (1),
  .CHECK_FORMAL    (1),
  .ADDR_WIDTH      (HAW),
  .DATA_WIDTH      (HDW),
  .ERROR_IDLE      (1),
  .ARB_ALLOW_EBT   (1),
  .CHECK_MAX_WAITS (1),
  .MAX_WAITS       (16),
  .ADDR_RANGE      (2),
  .MIN_ADDR        ({32'h0000_0000, 32'h4000_0000}),
  .MAX_ADDR        ({32'h3fff_ffff, 32'hefff_ffff}))
u_snps_ahb_lite_master_aip_sva
  (
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .htrans    (i_ahb_s_htrans),
  .haddr     (),
  .hwrite    (),
  .hsize     (),
  .hburst    (),
  .hprot     (),
  .hmastlock (),
  .hwdata    (),
  .hready    (i_ahb_s_hready),
  .hresp     (o_ahb_s_hresp),
  .hrdata    ());

//
// AHB decoder AIP used to drive i_ahb_s_hsel and i_ahb_s_hready signals
// of the AHB subordinate.
//
bind axe_ahb_error_sub snps_ahb_decoder_aip
#(.ENABLE_ASSERT  (1),
  .ENABLE_ASSUME  (1),
  .DEF_SLAVE      (1),
  .ADDR_WIDTH     (HAW),
  .DATA_WIDTH     (HDW),
  .RESP_WIDTH     (1),
  .HSEL_WIDTH     (1),
  .NUM_SLAVES     (1),
  .MAX_WAITS      (8),
  .MIN_ADDR       ({'0}),
  .MAX_ADDR       ({'h4}),
  .AMBA5_AHB      (0))
u_snps_ahb_decoder_aip_sva
  (
  .hclk         (i_clk),
  .hresetn      (i_rst_n),
  .htrans       (i_ahb_s_htrans),
  .haddr        (),
  .hreadyout_s  ({o_ahb_s_hreadyout}),
  .hresp_s      ({o_ahb_s_hresp}),
  .hexokay_s    (),
  .hrdata_s     (),
  .hruser_s     (),
  .hsel         (i_ahb_s_hsel),
  .hready       (i_ahb_s_hready),
  .hresp        (),
  .hexokay      (),
  .hrdata       (),
  .hruser       ());
