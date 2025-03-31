// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

bind axe_apb_demux axe_apb_demux_sva u_axe_apb_demux_sva(.*);

// Manager
bind axe_apb_demux snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::MASTER),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .PSEL_WIDTH      (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .CHECK_FORMAL    (1),
  .CHECK_MAX_WAITS (1),
  .CONFIG_LOWPOWER (1),
  .CONFIG_X_CHECK  (0),
  .PSLVERR_RCMND   (1)
) apb_manager_sva
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (i_apb_s_psel),
  .penable (i_apb_s_penable),
  .pwrite  (i_apb_s_pwrite),
  .paddr   (i_apb_s_paddr),
  .pwdata  (i_apb_s_pwdata),
  .pstrb   (i_apb_s_pstrb),
  .pprot   (i_apb_s_pprot),
  .prdata  (o_apb_s_prdata),
  .pready  (o_apb_s_pready),
  .pslverr (o_apb_s_pslverr));

// Subordiunate 0
bind axe_apb_demux snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::SLAVE),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .PSEL_WIDTH      (1),
  .MAX_PSEL_WIDTH  (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .CHECK_FORMAL    (1),
  .CONFIG_LOWPOWER (0),
  .CONFIG_X_CHECK  (0),
  .PSLVERR_RCMND   (1)
) apb_subordinate_sva_0
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (o_apb_m_psel[0]),
  .penable (o_apb_m_penable[0]),
  .pwrite  (o_apb_m_pwrite[0]),
  .paddr   (o_apb_m_paddr[0]),
  .pwdata  (o_apb_m_pwdata[0]),
  .pstrb   (o_apb_m_pstrb[0]),
  .pprot   (o_apb_m_pprot[0]),
  .prdata  (i_apb_m_prdata[0]),
  .pready  (i_apb_m_pready[0]),
  .pslverr (i_apb_m_pslverr[0])
);

// Subordiunate 1
bind axe_apb_demux snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::SLAVE),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .PSEL_WIDTH      (1),
  .MAX_PSEL_WIDTH  (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .CHECK_FORMAL    (1),
  .CONFIG_LOWPOWER (0),
  .CONFIG_X_CHECK  (0),
  .PSLVERR_RCMND   (1)
) apb_subordinate_sva_1
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (o_apb_m_psel[1]),
  .penable (o_apb_m_penable[1]),
  .pwrite  (o_apb_m_pwrite[1]),
  .paddr   (o_apb_m_paddr[1]),
  .pwdata  (o_apb_m_pwdata[1]),
  .pstrb   (o_apb_m_pstrb[1]),
  .pprot   (o_apb_m_pprot[1]),
  .prdata  (i_apb_m_prdata[1]),
  .pready  (i_apb_m_pready[1]),
  .pslverr (i_apb_m_pslverr[1])
);

// Subordiunate 2
bind axe_apb_demux snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::SLAVE),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (0),
  .PSEL_WIDTH      (1),
  .MAX_PSEL_WIDTH  (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .CHECK_FORMAL    (1),
  .CONFIG_LOWPOWER (0),
  .CONFIG_X_CHECK  (0),
  .PSLVERR_RCMND   (1)
) apb_subordinate_sva_2
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (o_apb_m_psel[2]),
  .penable (o_apb_m_penable[2]),
  .pwrite  (o_apb_m_pwrite[2]),
  .paddr   (o_apb_m_paddr[2]),
  .pwdata  (o_apb_m_pwdata[2]),
  .pstrb   (o_apb_m_pstrb[2]),
  .pprot   (o_apb_m_pprot[2]),
  .prdata  (i_apb_m_prdata[2]),
  .pready  (i_apb_m_pready[2]),
  .pslverr (i_apb_m_pslverr[2])
);
