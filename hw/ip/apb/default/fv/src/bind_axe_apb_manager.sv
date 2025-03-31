// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

bind axe_apb_manager snps_apb_aip #(
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
  .CONFIG_LOWPOWER (1),
  .CONFIG_X_CHECK  (0),
  .PSLVERR_RCMND   (1)
)
apb_subordinate_sva
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
