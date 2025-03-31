// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Kevin Luciani <kevin.luciani@axelera.ai>

bind axe_apb_mux snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::SLAVE),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (1),
  .PSEL_WIDTH      (1),
  .MAX_PSEL_WIDTH  (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .MAX_WAITS       (4),
  .CHECK_FORMAL    (1),
  .CONFIG_LOWPOWER (0),
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

bind axe_apb_mux snps_apb_aip #(
  .APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::MASTER),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (1),
  .PSEL_WIDTH      (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .CHECK_FORMAL    (1),
  // CHECK_MAX_WAITS will result in failures when STATIC_ARB=1 since
  // the manager with highest priority could take control of the bus indefinitely.
  .CHECK_MAX_WAITS (!STATIC_ARB),
  .CONFIG_LOWPOWER (1),
  .CONFIG_X_CHECK  (1),
  .PSLVERR_RCMND   (1)
) apb_manager_sva_0
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (i_apb_s_psel[0]),
  .penable (i_apb_s_penable[0]),
  .pwrite  (i_apb_s_pwrite[0]),
  .paddr   (i_apb_s_paddr[0]),
  .pwdata  (i_apb_s_pwdata[0]),
  .pstrb   (i_apb_s_pstrb[0]),
  .pprot   (i_apb_s_pprot[0]),
  .prdata  (o_apb_s_prdata[0]),
  .pready  (o_apb_s_pready[0]),
  .pslverr (o_apb_s_pslverr[0]));

bind axe_apb_mux snps_apb_aip
#(.APB_VERSION     (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE      (snps_apb_aip_pkg::MASTER),
  .ENABLE_ASSERT   (1),
  .ENABLE_ASSUME   (1),
  .ENABLE_COVER    (1),
  .PSEL_WIDTH      (1),
  .ADDR_WIDTH      (PAW),
  .WDATA_WIDTH     (PDW),
  .RDATA_WIDTH     (PDW),
  .CHECK_FORMAL    (1),
  .CHECK_MAX_WAITS (!STATIC_ARB),
  .CONFIG_LOWPOWER (1),
  .CONFIG_X_CHECK  (1),
  .PSLVERR_RCMND   (1)
) apb_manager_sva_1
( .pclk    (i_clk),
  .presetn (i_rst_n),
  .pselx   (i_apb_s_psel[1]),
  .penable (i_apb_s_penable[1]),
  .pwrite  (i_apb_s_pwrite[1]),
  .paddr   (i_apb_s_paddr[1]),
  .pwdata  (i_apb_s_pwdata[1]),
  .pstrb   (i_apb_s_pstrb[1]),
  .pprot   (i_apb_s_pprot[1]),
  .prdata  (o_apb_s_prdata[1]),
  .pready  (o_apb_s_pready[1]),
  .pslverr (o_apb_s_pslverr[1]));
