// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

bind axe_ahb_demux axe_ahb_demux_sva u_axe_ahb_demux_sva(.*);

// Manager
bind axe_ahb_demux snps_ahb_lite_master_aip
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
  .CHECK_MAX_WAITS (0),
  .MAX_WAITS       (16),
  .ADDR_RANGE      (2),
  .MIN_ADDR        ({32'h0000_0000, 32'h4000_0000}),
  .MAX_ADDR        ({32'h3fff_ffff, 32'hefff_ffff}))
u_snps_ahb_lite_master_aip_sva_0
  (
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .htrans    (i_ahb_s_htrans),
  .haddr     (i_ahb_s_haddr),
  .hwrite    (i_ahb_s_hwrite),
  .hsize     (i_ahb_s_hsize),
  .hburst    (i_ahb_s_hburst),
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (i_ahb_s_hwdata),
  .hready    (o_ahb_s_hready),
  .hresp     (o_ahb_s_hresp),
  .hrdata    (o_ahb_s_hrdata));

// Subordinate 0
bind axe_ahb_demux snps_ahb_lite_slave_aip
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
u_snps_ahb_lite_slave_aip_sva_0
(
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .hsel      (1'b1),
  .htrans    (o_ahb_m_htrans[0]),
  .haddr     (o_ahb_m_haddr[0]),
  .hwrite    (o_ahb_m_hwrite[0]),
  .hsize     (o_ahb_m_hsize[0]),
  .hburst    (o_ahb_m_hburst[0]),
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (o_ahb_m_hwdata[0]),
  .hready    (o_ahb_s_hready),
  .hreadyout (i_ahb_m_hready[0]),
  .hresp     (i_ahb_m_hresp[0]),
  .hrdata    (i_ahb_m_hrdata[0]));

// Subordinate 1
bind axe_ahb_demux snps_ahb_lite_slave_aip
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
u_snps_ahb_lite_slave_aip_sva_1
(
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .hsel      (1'b1),
  .htrans    (o_ahb_m_htrans[1]),
  .haddr     (o_ahb_m_haddr[1]),
  .hwrite    (o_ahb_m_hwrite[1]),
  .hsize     (o_ahb_m_hsize[1]),
  .hburst    (o_ahb_m_hburst[1]),
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (o_ahb_m_hwdata[1]),
  .hready    (o_ahb_s_hready),
  .hreadyout (i_ahb_m_hready[1]),
  .hresp     (i_ahb_m_hresp[1]),
  .hrdata    (i_ahb_m_hrdata[1]));

// Subordinate 2
bind axe_ahb_demux snps_ahb_lite_slave_aip
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
u_snps_ahb_lite_slave_aip_sva_2
(
  .hclk      (i_clk),
  .hresetn   (i_rst_n),
  .hsel      (1'b1),
  .htrans    (o_ahb_m_htrans[2]),
  .haddr     (o_ahb_m_haddr[2]),
  .hwrite    (o_ahb_m_hwrite[2]),
  .hsize     (o_ahb_m_hsize[2]),
  .hburst    (o_ahb_m_hburst[2]),
  .hprot     (4'b0011),
  .hmastlock (1'b0),
  .hwdata    (o_ahb_m_hwdata[2]),
  .hready    (o_ahb_s_hready),
  .hreadyout (i_ahb_m_hready[2]),
  .hresp     (i_ahb_m_hresp[2]),
  .hrdata    (i_ahb_m_hrdata[2]));
