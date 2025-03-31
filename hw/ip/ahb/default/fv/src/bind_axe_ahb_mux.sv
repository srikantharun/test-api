// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

// Subordinate
bind axe_ahb_mux snps_ahb_lite_slave_aip
#(.ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .CONFIG_X_CHECK  (1),
  .LOCKIDLE_RCMND  (0),
  .CHECK_FORMAL    (1),
  .ADDR_WIDTH      (HAW),
  .DATA_WIDTH      (HDW),
  .ERROR_IDLE      (1),
  .ARB_ALLOW_EBT   (0),
  .CHECK_MAX_WAITS (1),
  .MAX_WAITS       (5))
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
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (o_ahb_m_hwdata),
  .hready    (i_ahb_m_hready),
  .hreadyout (i_ahb_m_hready),
  .hresp     (i_ahb_m_hresp),
  .hrdata    (i_ahb_m_hrdata),
  .* );

// Manager 0
bind axe_ahb_mux snps_ahb_lite_master_aip
#(.ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .CONFIG_X_CHECK  (1),
  .LOCKIDLE_RCMND  (0),
  .CHECK_FORMAL    (1),
  .ADDR_WIDTH      (HAW),
  .DATA_WIDTH      (HDW),
  .ERROR_IDLE      (1),
  .ARB_ALLOW_EBT   (0),
  .CHECK_MAX_WAITS (!STATIC_ARB),
  .MAX_WAITS       (16))
u_snps_ahb_lite_master_aip_sva_0
  (
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .htrans    (i_ahb_s_htrans[0]),
  .haddr     (i_ahb_s_haddr[0]),
  .hwrite    (i_ahb_s_hwrite[0]),
  .hsize     (i_ahb_s_hsize[0]),
  .hburst    (i_ahb_s_hburst[0]),
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (i_ahb_s_hwdata[0]),
  .hready    (o_ahb_s_hready[0]),
  .hresp     (o_ahb_s_hresp[0]),
  .hrdata    (o_ahb_s_hrdata[0]),
  .* );

// Manager 1
bind axe_ahb_mux snps_ahb_lite_master_aip
#(.ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .CONFIG_X_CHECK  (1),
  .LOCKIDLE_RCMND  (0),
  .CHECK_FORMAL    (1),
  .ADDR_WIDTH      (HAW),
  .DATA_WIDTH      (HDW),
  .ERROR_IDLE      (1),
  .ARB_ALLOW_EBT   (0),
  .CHECK_MAX_WAITS (!STATIC_ARB),
  .MAX_WAITS       (16))
u_snps_ahb_lite_master_aip_sva_1
  (
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .htrans    (i_ahb_s_htrans[1]),
  .haddr     (i_ahb_s_haddr[1]),
  .hwrite    (i_ahb_s_hwrite[1]),
  .hsize     (i_ahb_s_hsize[1]),
  .hburst    (i_ahb_s_hburst[1]),
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (i_ahb_s_hwdata[1]),
  .hready    (o_ahb_s_hready[1]),
  .hresp     (o_ahb_s_hresp[1]),
  .hrdata    (o_ahb_s_hrdata[1]),
  .* );
