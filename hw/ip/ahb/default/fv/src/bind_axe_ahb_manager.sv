// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

bind axe_ahb_manager axe_ahb_manager_sva u_axe_ahb_manager_sva(.*);

bind axe_ahb_manager snps_ahb_lite_slave_aip
#(.ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .CONFIG_X_CHECK  (1),
  .LOCKIDLE_RCMND  (0),
  .CHECK_FORMAL    (1),
  .ADDR_WIDTH      (HAW),
  .DATA_WIDTH      (HDW),
  .ERROR_IDLE      (0),
  .ARB_ALLOW_EBT   (0),
  .CHECK_MAX_WAITS (1),
  .HBURST_SINGLE   (1),
  .MAX_WAITS       (16))
u_snps_ahb_lite_slave_aip_sva
(
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .hsel      (1'b1),
  .htrans    (o_ahb_m_htrans),
  .haddr     (o_ahb_m_haddr),
  .hwrite    (o_ahb_m_hwrite),
  .hsize     (o_ahb_m_hsize),
  .hburst    (o_ahb_m_hburst),
  .hprot     (),
  .hmastlock (),
  .hwdata    (o_ahb_m_hwdata),
  .hready    (i_ahb_m_hready),
  .hreadyout (),
  .hresp     (i_ahb_m_hresp),
  .hrdata    (i_ahb_m_hrdata),
  .* );
