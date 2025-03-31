// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

// AHB Manager
bind axe_ahb_to_apb snps_ahb_lite_master_aip
#(.ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .CONFIG_X_CHECK  (1),
  .LOCKIDLE_RCMND  (0),
  .CHECK_FORMAL    (1),
  .ADDR_WIDTH      (AW),
  .DATA_WIDTH      (DW),
  .ERROR_IDLE      (1),
  .ARB_ALLOW_EBT   (0),
  .CHECK_MAX_WAITS (1),
  .MAX_WAITS       (6),
  .ADDR_RANGE      (2),
  .MIN_ADDR        ({32'h0000_0000, 32'h4000_0000}),
  .MAX_ADDR        ({32'h3fff_ffff, 32'hefff_ffff}))
u_snps_ahb_lite_master_aip_sva
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
  .hrdata    (o_ahb_s_hrdata),
  .* );

// APB Subordinate
bind axe_ahb_to_apb snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::SLAVE),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .PSEL_WIDTH      (1),
  .MAX_PSEL_WIDTH  (1),
  .MAX_WAITS       (2),
  .ADDR_WIDTH      (AW),
  .WDATA_WIDTH     (DW),
  .RDATA_WIDTH     (DW),
  .CHECK_FORMAL    (1),
  .CONFIG_LOWPOWER (1),
  .CONFIG_X_CHECK  (1),
  .PSLVERR_RCMND   (1)
) apb_subordinate_sva
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (o_apb_m_psel),
  .penable (o_apb_m_penable),
  .pwrite  (o_apb_m_pwrite),
  .paddr   (o_apb_m_paddr),
  .pwdata  (o_apb_m_pwdata),
  .pstrb   (o_apb_m_pstrb),
  .pprot   (o_apb_m_pprot),
  .prdata  (i_apb_m_prdata),
  .pready  (i_apb_m_pready),
  .pslverr (i_apb_m_pslverr)
);
