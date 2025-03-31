// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Manuel Oliveira <manuel.oliveira@axelera.ai>

/// Bind SVA in pctl
///

bind pctl pctl_sva #(
  .N_FAST_CLKS       (N_FAST_CLKS      ),
  .N_RESETS          (N_RESETS         ),
  .N_MEM_PG          (N_MEM_PG         ),
  .N_FENCES          (N_FENCES         ),
  .CLKRST_MATRIX     (CLKRST_MATRIX    ),
  .PLL_CLK_IS_I_CLK  (PLL_CLK_IS_I_CLK ),
  .NOC_RST_IDX       (NOC_RST_IDX      ),
  .SYNC_CLK_IDX      (SYNC_CLK_IDX     ),
  .AUTO_RESET_REMOVE (AUTO_RESET_REMOVE),
  .paddr_t           (paddr_t          ),
  .pdata_t           (pdata_t          ),
  .pstrb_t           (pstrb_t          )
  ) u_pctl_sva (.*);

bind pctl snps_apb_aip #(
  .PROTOCOL_VER         (snps_apb_aip_pkg::AMBA4),
  .APB_VERSION          (snps_apb_aip_pkg::APB4),
  .AGENT_TYPE           (snps_apb_aip_pkg::MASTER),
  .ENABLE_ASSERT        (0),
  .ENABLE_ASSUME        (1),
  .ENABLE_COVER         (0),
  .PSEL_WIDTH           (1),
  .ADDR_WIDTH           ($bits(i_cfg_apb4_s_paddr)),
  .WDATA_WIDTH          ($bits(i_cfg_apb4_s_pwdata)),
  .WSTRB_WIDTH          ($bits(i_cfg_apb4_s_pstrb)),
  .RDATA_WIDTH          ($bits(o_cfg_apb4_s_prdata)),
  .CHECK_FORMAL         (snps_apb_aip_pkg::SNPS_APB_AIP_CHECK_FORMAL),
  .CONFIG_LOWPOWER      (0),
  .CONFIG_X_CHECK       (0),
  .PSLVERR_RCMND        (snps_apb_aip_pkg::SNPS_APB_AIP_PSLVERR_RCMND),
  .CHECK_MAX_WAITS      (snps_apb_aip_pkg::SNPS_APB_AIP_CHECK_MAX_WAITS),
  .MAX_WAITS            (snps_apb_aip_pkg::SNPS_APB_AIP_MAX_WAITS),
  .PSTRB_ON_READ        (snps_apb_aip_pkg::SNPS_APB_AIP_PSTRB_ON_READ),
  .CHECK_STABLE_PER_BIT (0),
  //---- FRV related parameters ----
  .FRV                  (1),
  .FRV_SLAVE            (0),
  .FRV_RSVD_MODE        (1),
  .FRV_WR_LATENCY       (1),
  .FRV_RD_LATENCY       (0),
  .FRV_RD_ACT_LATENCY   (1),
  .FRV_LATENCY_MD       (0),
  .FRV_OUTABLK_MD       (2),
  .FRV_RO_RD_CHK        (1),
  .FRV_SNPS_ND_ABS      (0),
  .FRV_COMPOSITE        (1),
  .FRV_CHECK_FORMAL     (1),
  .FRV_COVER_TYPE       (3'h7),
  .FRV_COVER_WRITE      (0),
  .FRV_COVER_READ       (1),
  .FRV_COVER_BYTE_UPDATE(0),
  .FRV_OUTADDR_EN       (0)
) u_snps_frv_apb (
  .pclk   (i_clk),
  .presetn(pctl.o_ao_rst_sync_n),
  .pselx  (i_cfg_apb4_s_psel),
  .penable(i_cfg_apb4_s_penable),
  .paddr  (i_cfg_apb4_s_paddr),
  .pprot  (i_cfg_apb4_s_pprot),
  .pstrb  (i_cfg_apb4_s_pstrb),
  .pwrite (i_cfg_apb4_s_pwrite),
  .pwdata (i_cfg_apb4_s_pwdata),
  .prdata (o_cfg_apb4_s_prdata),
  .pready (o_cfg_apb4_s_pready),
  .pslverr(o_cfg_apb4_s_pslverr)
);
