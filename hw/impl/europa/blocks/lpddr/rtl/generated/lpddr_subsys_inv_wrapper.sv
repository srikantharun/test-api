// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Inverse wrapper of lpddr_p and lpddr_subsys_wrapper.sv to return to snps names as much as possible and bypass lpddr_p wrapper logic when required. Auto generated using wrap_snps_subsys.py/hjson/mako
// Owner: Roel Uytterhoeven

module lpddr_subsys_inv_wrapper (
    input logic  pclk,
    input logic  presetn,
    input logic  pclk_apbrw,
    input logic  aclk_0,
    input logic  aresetn_0,
    input logic  csysreq_0,
    input logic [32:0] araddr_0,
    input logic  arautopre_0,
    input logic [1:0] arburst_0,
    input logic [3:0] arcache_0,
    input logic [7:0] arid_0,
    input logic [7:0] arlen_0,
    input logic  arlock_0,
    input logic  arpoison_0,
    input logic [2:0] arprot_0,
    input logic [3:0] arqos_0,
    input logic [3:0] arregion_0,
    input logic [2:0] arsize_0,
    input logic  arurgentb_0,
    input logic  arurgentr_0,
    input logic  arvalid_0,
    input logic  rready_0,
    input logic [32:0] awaddr_0,
    input logic  awautopre_0,
    input logic [1:0] awburst_0,
    input logic [3:0] awcache_0,
    input logic [7:0] awid_0,
    input logic [7:0] awlen_0,
    input logic  awlock_0,
    input logic  awpoison_0,
    input logic [2:0] awprot_0,
    input logic [3:0] awqos_0,
    input logic [3:0] awregion_0,
    input logic [2:0] awsize_0,
    input logic  awurgent_0,
    input logic  awvalid_0,
    input logic [255:0] wdata_0,
    input logic  wlast_0,
    input logic [31:0] wstrb_0,
    input logic  wvalid_0,
    input logic  bready_0,
    input wire  BP_PWROK,
    input logic  core_ddrc_core_clk,
    input logic  core_ddrc_core_clk_apbrw,
    input logic  core_ddrc_rstn,
    input logic  csysdiscamdrain_ddrc,
    input logic [4:0] csysfrequency_ddrc,
    input logic  csysfsp_ddrc,
    input logic  csysmode_ddrc,
    input logic  csysreq_ddrc,
    input logic  DfiClk,
    input logic  sbr_clk,
    input logic  sbr_resetn,
    input logic  dfi_reset_n_in,
    input logic  init_mr_done_in,
    input logic  Reset_async,
    input logic [2:0] acsm_ADME,
    input logic  acsm_CRE1,
    input logic  acsm_CRE2,
    input logic [5:0] acsm_FCA1,
    input logic [5:0] acsm_FCA2,
    input logic [5:0] acsm_FRA1,
    input logic [5:0] acsm_FRA2,
    input logic [1:0] acsm_MCS,
    input logic  acsm_MCSW,
    input logic  acsm_PDE,
    input logic  acsm_RET,
    input logic  acsm_RREN1,
    input logic  acsm_RREN2,
    input logic [2:0] bc_ADME,
    input logic  bc_CRE1,
    input logic  bc_CRE2,
    input logic [3:0] bc_FCA1,
    input logic [3:0] bc_FCA2,
    input logic [4:0] bc_FRA1,
    input logic [4:0] bc_FRA2,
    input logic [1:0] bc_MCS,
    input logic  bc_MCSW,
    input logic  bc_PDE,
    input logic  bc_RET,
    input logic  bc_RREN1,
    input logic  bc_RREN2,
    input logic [2:0] dccm_ADME,
    input logic  dccm_CRE1,
    input logic  dccm_CRE2,
    input logic [4:0] dccm_FCA1,
    input logic [4:0] dccm_FCA2,
    input logic [6:0] dccm_FRA1,
    input logic [6:0] dccm_FRA2,
    input logic [1:0] dccm_MCS,
    input logic  dccm_MCSW,
    input logic  dccm_PDE,
    input logic  dccm_RET,
    input logic  dccm_RREN1,
    input logic  dccm_RREN2,
    input logic [2:0] gs_ADME,
    input logic  gs_CRE1,
    input logic  gs_CRE2,
    input logic [1:0] gs_FCA1,
    input logic [1:0] gs_FCA2,
    input logic [5:0] gs_FRA1,
    input logic [5:0] gs_FRA2,
    input logic [1:0] gs_MCS,
    input logic  gs_MCSW,
    input logic  gs_PDE,
    input logic  gs_RET,
    input logic  gs_RREN1,
    input logic  gs_RREN2,
    input logic [2:0] iccm_ADME,
    input logic  iccm_CRE1,
    input logic  iccm_CRE2,
    input logic [5:0] iccm_FCA1,
    input logic [5:0] iccm_FCA2,
    input logic [6:0] iccm_FRA1,
    input logic [6:0] iccm_FRA2,
    input logic [1:0] iccm_MCS,
    input logic  iccm_MCSW,
    input logic  iccm_PDE,
    input logic  iccm_RET,
    input logic  iccm_RREN1,
    input logic  iccm_RREN2,
    input logic [31:0] paddr,
    input logic  penable,
    input logic [2:0] pie_ADME,
    input logic  pie_CRE1,
    input logic  pie_CRE2,
    input logic [4:0] pie_FCA1,
    input logic [4:0] pie_FCA2,
    input logic [5:0] pie_FRA1,
    input logic [5:0] pie_FRA2,
    input logic [1:0] pie_MCS,
    input logic  pie_MCSW,
    input logic  pie_PDE,
    input logic  pie_RET,
    input logic  pie_RREN1,
    input logic  pie_RREN2,
    input logic [2:0] pprot,
    input logic [2:0] pprot_pin,
    input logic  psel,
    input logic [3:0] pstrb,
    input logic [31:0] pwdata,
    input logic  pwrite,
    input logic [5:0] scan_shift_i,
    input logic [2:0] wdata_ADME,
    input logic  wdata_CRE1,
    input logic  wdata_CRE2,
    input logic [4:0] wdata_FCA1,
    input logic [4:0] wdata_FCA2,
    input logic [4:0] wdata_FRA1,
    input logic [4:0] wdata_FRA2,
    input logic  wdata_KCS,
    input logic [1:0] wdata_MCSRD,
    input logic [1:0] wdata_MCSWR,
    input logic  wdata_PDE,
    input logic  wdata_RET,
    input logic  wdata_RREN1,
    input logic  wdata_RREN2,
    input logic  PllBypClk,
    input logic  PllRefClk,
    input logic [1:0] pa_rmask,
    input logic  pa_wmask,
    input logic  dis_regs_ecc_syndrome,
    input logic  Reset,
    input logic  scan_DlyTestClk,
    input logic  scan_asst_mode,
    input logic  scan_clk,
    input logic  scan_mode,
    input logic  scan_occ_bypass,
    input logic  scan_occ_reset,
    input logic  scan_shift_async,
    input logic  scan_shift_cg,
    input logic [1367:0] scan_si,
    input logic  DdrPhyCsrCmdTdrCaptureEn,
    input logic  DdrPhyCsrCmdTdrShiftEn,
    input logic  DdrPhyCsrCmdTdrUpdateEn,
    input logic  DdrPhyCsrRdDataTdrCaptureEn,
    input logic  DdrPhyCsrRdDataTdrShiftEn,
    input logic  DdrPhyCsrRdDataTdrUpdateEn,
    input logic  TDRCLK,
    input logic  WRSTN,
    input logic  WSI,
    input logic  BurnIn,
    input logic  Iddq_mode,
    output logic  cactive_0,
    output logic  csysack_0,
    output logic  arpoison_intr_0,
    output logic  arready_0,
    output logic  raq_split_0,
    output logic  raqb_pop_0,
    output logic  raqb_push_0,
    output logic [5:0] raqb_wcount_0,
    output logic  raqr_pop_0,
    output logic  raqr_push_0,
    output logic [5:0] raqr_wcount_0,
    output logic [255:0] rdata_0,
    output logic [7:0] rid_0,
    output logic  rlast_0,
    output logic [1:0] rresp_0,
    output logic  rvalid_0,
    output logic  awpoison_intr_0,
    output logic  awready_0,
    output logic  waq_pop_0,
    output logic  waq_push_0,
    output logic  waq_split_0,
    output logic [5:0] waq_wcount_0,
    output logic  wready_0,
    output logic [7:0] bid_0,
    output logic [1:0] bresp_0,
    output logic  bvalid_0,
    output wire  BP_MEMRESET_L,
    output logic [6:0] hpr_credit_cnt,
    output logic [6:0] lpr_credit_cnt,
    output logic [6:0] wr_credit_cnt,
    output logic [6:0] wrecc_credit_cnt,
    output logic  cactive_ddrc,
    output logic  csysack_ddrc,
    output logic [1:0] stat_ddrc_reg_selfref_type,
    output logic  sbr_done_intr,
    output logic [2:0] dbg_dfi_ie_cmd_type,
    output logic  derate_temp_limit_intr,
    output logic [1:0] derate_temp_limit_intr_fault,
    output logic  ecc_ap_err_intr,
    output logic [1:0] ecc_ap_err_intr_fault,
    output logic  ecc_corrected_err_intr,
    output logic [1:0] ecc_corrected_err_intr_fault,
    output logic  ecc_uncorrected_err_intr,
    output logic [1:0] ecc_uncorrected_err_intr_fault,
    output logic  rd_linkecc_corr_err_intr,
    output logic [1:0] rd_linkecc_corr_err_intr_fault,
    output logic  rd_linkecc_uncorr_err_intr,
    output logic [1:0] rd_linkecc_uncorr_err_intr_fault,
    output logic  dfi_reset_n_ref,
    output logic  init_mr_done_out,
    output logic  acsm_PRN,
    output logic  bc_PRN,
    output logic  dccm_PRN,
    output logic  gs_PRN,
    output logic  iccm_PRN,
    output logic  pie_PRN,
    output logic [31:0] prdata,
    output logic [3:0] prdata_par,
    output logic  pready,
    output logic  pslverr,
    output logic  wdata_PRN,
    output logic [5:0] PhyInt_fault,
    output logic [15:0] PhyInt_n,
    output logic  dwc_lpddr5xphy_pll_lock,
    output logic  dwc_lpddr5xphy_pmu_busy,
    output logic [31:0] hif_mrr_data,
    output logic  hif_mrr_data_valid,
    output logic [5:0] hif_refresh_req_bank,
    output logic [2:0] perf_bank,
    output logic [1:0] perf_bg,
    output logic  perf_dfi_rd_data_cycles,
    output logic  perf_dfi_wr_data_cycles,
    output logic  perf_hif_hi_pri_rd,
    output logic  perf_hif_rd,
    output logic  perf_hif_rd_or_wr,
    output logic  perf_hif_rmw,
    output logic  perf_hif_wr,
    output logic  perf_hpr_req_with_nocredit,
    output logic  perf_hpr_xact_when_critical,
    output logic  perf_ie_blk_hazard,
    output logic  perf_lpr_req_with_nocredit,
    output logic  perf_lpr_xact_when_critical,
    output logic  perf_op_is_activate,
    output logic  perf_op_is_cas,
    output logic  perf_op_is_cas_wck_sus,
    output logic  perf_op_is_cas_ws,
    output logic  perf_op_is_cas_ws_off,
    output logic  perf_op_is_crit_ref,
    output logic  perf_op_is_dqsosc_mpc,
    output logic  perf_op_is_dqsosc_mrr,
    output logic  perf_op_is_enter_dsm,
    output logic [1:0] perf_op_is_enter_powerdown,
    output logic [1:0] perf_op_is_enter_selfref,
    output logic  perf_op_is_load_mode,
    output logic  perf_op_is_mwr,
    output logic  perf_op_is_precharge,
    output logic  perf_op_is_rd,
    output logic  perf_op_is_rd_activate,
    output logic  perf_op_is_rd_or_wr,
    output logic  perf_op_is_refresh,
    output logic  perf_op_is_rfm,
    output logic  perf_op_is_spec_ref,
    output logic  perf_op_is_tcr_mrr,
    output logic  perf_op_is_wr,
    output logic  perf_op_is_zqlatch,
    output logic  perf_op_is_zqstart,
    output logic  perf_precharge_for_other,
    output logic  perf_precharge_for_rdwr,
    output logic  perf_rank,
    output logic  perf_raw_hazard,
    output logic  perf_rdwr_transitions,
    output logic [1:0] perf_selfref_mode,
    output logic  perf_visible_window_limit_reached_rd,
    output logic  perf_visible_window_limit_reached_wr,
    output logic  perf_war_hazard,
    output logic  perf_waw_hazard,
    output logic  perf_wr_xact_when_critical,
    output logic  perf_write_combine,
    output logic  perf_write_combine_noecc,
    output logic  perf_write_combine_wrecc,
    output wire  VIO_TIEHI,
    output logic [1367:0] scan_so,
    output logic  DdrPhyCsrCmdTdr_Tdo,
    output logic  DdrPhyCsrRdDataTdr_Tdo,
    output logic [1:0] dwc_lpddr5xphy_dto,
    inout wire [19:0] BP_A,
    inout wire  BP_ATO,
    inout wire  BP_ATO_PLL,
    inout wire [12:0] BP_B0_D,
    inout wire [12:0] BP_B1_D,
    inout wire [12:0] BP_B2_D,
    inout wire [12:0] BP_B3_D,
    inout wire  BP_CK0_C,
    inout wire  BP_CK0_T,
    inout wire  BP_CK1_C,
    inout wire  BP_CK1_T,
    inout wire  BP_ZN
);

    lpddr_p axelera_lpddr_top_inst (
        // Ports that have no direct relation to SNPS ports
        .i_ao_clk(i_clk),
        .i_lpddr_clk(pclk),
        .i_ao_rst_n(presetn),
        .i_global_rst_n(presetn),
        .o_ao_rst_sync_n(),
        .o_noc_async_idle_req(),
        .i_noc_async_idle_ack('0),
        .i_noc_async_idle_val(),
        .o_noc_clken(),
        .o_noc_rst_n(),
        .i_lpddr_axi_m_aruser('0),
        .i_lpddr_axi_m_awuser('0),
        .i_lpddr_axi_m_wuser('0),
        .o_lpddr_axi_m_ruser(),
        .o_lpddr_axi_m_buser(),
        .i_lpddr_syscfg_apb4_s_paddr('0),
        .i_lpddr_syscfg_apb4_s_pwdata('0),
        .i_lpddr_syscfg_apb4_s_pwrite('0),
        .i_lpddr_syscfg_apb4_s_psel('0),
        .i_lpddr_syscfg_apb4_s_penable('0),
        .i_lpddr_syscfg_apb4_s_pstrb('0),
        .i_lpddr_syscfg_apb4_s_pprot('0),
        .o_lpddr_syscfg_apb4_s_pready(),
        .o_lpddr_syscfg_apb4_s_prdata(),
        .o_lpddr_syscfg_apb4_s_pslverr(),
        .o_phy_pie_prog_err_intr(),
        .o_phy_ecc_err_intr(),
        .o_phy_rdfptrchk_err_intr(),
        .o_phy_pie_parity_err_intr(),
        .o_phy_acsm_parity_err_intr(),
        .o_phy_trng_fail_intr(),
        .o_phy_init_cmplt_intr(),
        .o_phy_trng_cmplt_intr(),
        .tck('0),
        .trst('0),
        .tms('0),
        .tdi('0),
        .tdo_en(),
        .tdo(),
        .ssn_bus_clk('0),
        .ssn_bus_data_in('0),
        .ssn_bus_data_out(),
        .bisr_clk('0),
        .bisr_reset('0),
        .bisr_shift_en('0),
        .bisr_si('0),
        .bisr_so(),
        .o_lpddr_obs(),
        // Ports that have a direct relation to SNPS ports (i.e. renamed or passed through spill reg)
        .i_lpddr_axi_m_araddr(araddr_0),
        .i_lpddr_axi_m_arburst(arburst_0),
        .i_lpddr_axi_m_arcache(arcache_0),
        .i_lpddr_axi_m_arid(arid_0),
        .i_lpddr_axi_m_arlen(arlen_0),
        .i_lpddr_axi_m_arlock(arlock_0),
        .i_lpddr_axi_m_arprot(arprot_0),
        .i_lpddr_axi_m_arqos(arqos_0),
        .i_lpddr_axi_m_arregion(arregion_0),
        .i_lpddr_axi_m_arsize(arsize_0),
        .i_lpddr_axi_m_arvalid(arvalid_0),
        .i_lpddr_axi_m_rready(rready_0),
        .i_lpddr_axi_m_awaddr(awaddr_0),
        .i_lpddr_axi_m_awburst(awburst_0),
        .i_lpddr_axi_m_awcache(awcache_0),
        .i_lpddr_axi_m_awid(awid_0),
        .i_lpddr_axi_m_awlen(awlen_0),
        .i_lpddr_axi_m_awlock(awlock_0),
        .i_lpddr_axi_m_awprot(awprot_0),
        .i_lpddr_axi_m_awqos(awqos_0),
        .i_lpddr_axi_m_awregion(awregion_0),
        .i_lpddr_axi_m_awsize(awsize_0),
        .i_lpddr_axi_m_awvalid(awvalid_0),
        .i_lpddr_axi_m_wdata(wdata_0),
        .i_lpddr_axi_m_wlast(wlast_0),
        .i_lpddr_axi_m_wstrb(wstrb_0),
        .i_lpddr_axi_m_wvalid(wvalid_0),
        .i_lpddr_axi_m_bready(bready_0),
        .i_lpddr_cfg_apb4_s_paddr(paddr),
        .i_lpddr_cfg_apb4_s_penable(penable),
        .i_lpddr_cfg_apb4_s_pprot(pprot),
        .i_lpddr_cfg_apb4_s_psel(psel),
        .i_lpddr_cfg_apb4_s_pstrb(pstrb),
        .i_lpddr_cfg_apb4_s_pwdata(pwdata),
        .i_lpddr_cfg_apb4_s_pwrite(pwrite),
        .o_lpddr_axi_m_arready(arready_0),
        .o_lpddr_axi_m_rdata(rdata_0),
        .o_lpddr_axi_m_rid(rid_0),
        .o_lpddr_axi_m_rlast(rlast_0),
        .o_lpddr_axi_m_rresp(rresp_0),
        .o_lpddr_axi_m_rvalid(rvalid_0),
        .o_lpddr_axi_m_awready(awready_0),
        .o_lpddr_axi_m_wready(wready_0),
        .o_lpddr_axi_m_bid(bid_0),
        .o_lpddr_axi_m_bresp(bresp_0),
        .o_lpddr_axi_m_bvalid(bvalid_0),
        .BP_MEMRESET_L(BP_MEMRESET_L),
        .o_ctrl_sbr_done_intr(sbr_done_intr),
        .o_ctrl_derate_temp_limit_intr(derate_temp_limit_intr),
        .o_ctrl_ecc_ap_err_intr(ecc_ap_err_intr),
        .o_ctrl_ecc_corrected_err_intr(ecc_corrected_err_intr),
        .o_ctrl_ecc_uncorrected_err_intr(ecc_uncorrected_err_intr),
        .o_ctrl_rd_linkecc_corr_err_intr(rd_linkecc_corr_err_intr),
        .o_ctrl_rd_linkecc_uncorr_err_intr(rd_linkecc_uncorr_err_intr),
        .o_lpddr_cfg_apb4_s_prdata(prdata),
        .o_lpddr_cfg_apb4_s_pready(pready),
        .o_lpddr_cfg_apb4_s_pslverr(pslverr),
        .BP_A(BP_A),
        .BP_ATO(BP_ATO),
        .BP_ATO_PLL(BP_ATO_PLL),
        .BP_B0_D(BP_B0_D),
        .BP_B1_D(BP_B1_D),
        .BP_B2_D(BP_B2_D),
        .BP_B3_D(BP_B3_D),
        .BP_CK0_C(BP_CK0_C),
        .BP_CK0_T(BP_CK0_T),
        .BP_CK1_C(BP_CK1_C),
        .BP_CK1_T(BP_CK1_T),
        .BP_ZN(BP_ZN)
    );

    // Force outputs that axelera does not connect in their wrapper to directly connect with the ports of the snps subsys
    initial begin
        force arpoison_intr_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.arpoison_intr_0;
        force awpoison_intr_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.awpoison_intr_0;
        force stat_ddrc_reg_selfref_type = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.stat_ddrc_reg_selfref_type;
        force dbg_dfi_ie_cmd_type = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dbg_dfi_ie_cmd_type;
        force derate_temp_limit_intr_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.derate_temp_limit_intr_fault;
        force ecc_ap_err_intr_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.ecc_ap_err_intr_fault;
        force ecc_corrected_err_intr_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.ecc_corrected_err_intr_fault;
        force ecc_uncorrected_err_intr_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.ecc_uncorrected_err_intr_fault;
        force rd_linkecc_corr_err_intr_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.rd_linkecc_corr_err_intr_fault;
        force rd_linkecc_uncorr_err_intr_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.rd_linkecc_uncorr_err_intr_fault;
        force dfi_reset_n_ref = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dfi_reset_n_ref;
        force init_mr_done_out = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.init_mr_done_out;
        force prdata_par = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.prdata_par;
        force PhyInt_fault = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.PhyInt_fault;
        force hif_refresh_req_bank = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.hif_refresh_req_bank;
        force scan_so = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_so;
        force DdrPhyCsrCmdTdr_Tdo = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrCmdTdr_Tdo;
        force DdrPhyCsrRdDataTdr_Tdo = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrRdDataTdr_Tdo;
    end

    // Force the output of the pctl lpddr_clk to be exactly the same as the core_ddrc_core_clk to avoid delays between both due to the clock gate in the pctl.
    initial begin
        force axelera_lpddr_top_inst.lpddr_clk = core_ddrc_core_clk;
        force axelera_lpddr_top_inst.ctrl_rst_n = aresetn_0;
    end
    
    // Force inputs that axelera ties-off in their wrapper to directly connect with their original signal names.
    initial begin
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.arautopre_0 = arautopre_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.arpoison_0 = arpoison_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.awautopre_0 = awautopre_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.awpoison_0 = awpoison_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dfi_reset_n_in = dfi_reset_n_in;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.init_mr_done_in = init_mr_done_in;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_ADME = acsm_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_CRE1 = acsm_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_CRE2 = acsm_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_FCA1 = acsm_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_FCA2 = acsm_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_FRA1 = acsm_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_FRA2 = acsm_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_MCS = acsm_MCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_MCSW = acsm_MCSW;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_RREN1 = acsm_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_RREN2 = acsm_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_ADME = bc_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_CRE1 = bc_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_CRE2 = bc_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_FCA1 = bc_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_FCA2 = bc_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_FRA1 = bc_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_FRA2 = bc_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_MCS = bc_MCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_MCSW = bc_MCSW;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_RREN1 = bc_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_RREN2 = bc_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_ADME = dccm_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_CRE1 = dccm_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_CRE2 = dccm_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_FCA1 = dccm_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_FCA2 = dccm_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_FRA1 = dccm_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_FRA2 = dccm_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_MCS = dccm_MCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_MCSW = dccm_MCSW;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_RREN1 = dccm_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_RREN2 = dccm_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_ADME = gs_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_CRE1 = gs_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_CRE2 = gs_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_FCA1 = gs_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_FCA2 = gs_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_FRA1 = gs_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_FRA2 = gs_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_MCS = gs_MCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_MCSW = gs_MCSW;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_RREN1 = gs_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_RREN2 = gs_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_ADME = iccm_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_CRE1 = iccm_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_CRE2 = iccm_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_FCA1 = iccm_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_FCA2 = iccm_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_FRA1 = iccm_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_FRA2 = iccm_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_MCS = iccm_MCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_MCSW = iccm_MCSW;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_RREN1 = iccm_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_RREN2 = iccm_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_ADME = pie_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_CRE1 = pie_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_CRE2 = pie_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_FCA1 = pie_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_FCA2 = pie_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_FRA1 = pie_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_FRA2 = pie_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_MCS = pie_MCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_MCSW = pie_MCSW;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_RREN1 = pie_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_RREN2 = pie_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_shift_i = scan_shift_i;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_ADME = wdata_ADME;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_CRE1 = wdata_CRE1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_CRE2 = wdata_CRE2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_FCA1 = wdata_FCA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_FCA2 = wdata_FCA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_FRA1 = wdata_FRA1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_FRA2 = wdata_FRA2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_KCS = wdata_KCS;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_MCSRD = wdata_MCSRD;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_MCSWR = wdata_MCSWR;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_RREN1 = wdata_RREN1;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_RREN2 = wdata_RREN2;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pa_rmask = pa_rmask;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pa_wmask = pa_wmask;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_DlyTestClk = scan_DlyTestClk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_asst_mode = scan_asst_mode;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_clk = scan_clk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_mode = scan_mode;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_occ_bypass = scan_occ_bypass;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_occ_reset = scan_occ_reset;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_shift_async = scan_shift_async;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_shift_cg = scan_shift_cg;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.scan_si = scan_si;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrCmdTdrCaptureEn = DdrPhyCsrCmdTdrCaptureEn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrCmdTdrShiftEn = DdrPhyCsrCmdTdrShiftEn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrCmdTdrUpdateEn = DdrPhyCsrCmdTdrUpdateEn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrRdDataTdrCaptureEn = DdrPhyCsrRdDataTdrCaptureEn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrRdDataTdrShiftEn = DdrPhyCsrRdDataTdrShiftEn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DdrPhyCsrRdDataTdrUpdateEn = DdrPhyCsrRdDataTdrUpdateEn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.TDRCLK = TDRCLK;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.WRSTN = WRSTN;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.WSI = WSI;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.BurnIn = BurnIn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.Iddq_mode = Iddq_mode;
    end

    // Force signals that end in the axelera lpddr_p module, either in a csr or some other logic that is not just unconnected or tie.
    initial begin
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pclk = pclk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.presetn = presetn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pclk_apbrw = pclk_apbrw;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.aclk_0 = aclk_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.aresetn_0 = aresetn_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysreq_0 = csysreq_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.arurgentb_0 = arurgentb_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.arurgentr_0 = arurgentr_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.awurgent_0 = awurgent_0;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.BP_PWROK = BP_PWROK;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.core_ddrc_core_clk = core_ddrc_core_clk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.core_ddrc_core_clk_apbrw = core_ddrc_core_clk_apbrw;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.core_ddrc_rstn = core_ddrc_rstn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysdiscamdrain_ddrc = csysdiscamdrain_ddrc;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysfrequency_ddrc = csysfrequency_ddrc;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysfsp_ddrc = csysfsp_ddrc;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysmode_ddrc = csysmode_ddrc;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysreq_ddrc = csysreq_ddrc;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.DfiClk = DfiClk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.sbr_clk = sbr_clk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.sbr_resetn = sbr_resetn;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.Reset_async = Reset_async;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_PDE = acsm_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_RET = acsm_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_PDE = bc_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_RET = bc_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_PDE = dccm_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_RET = dccm_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_PDE = gs_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_RET = gs_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_PDE = iccm_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_RET = iccm_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_PDE = pie_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_RET = pie_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pprot_pin = pprot_pin;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_PDE = wdata_PDE;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_RET = wdata_RET;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.PllBypClk = PllBypClk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.PllRefClk = PllRefClk;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dis_regs_ecc_syndrome = dis_regs_ecc_syndrome;
        force axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.Reset = Reset;
        force cactive_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.cactive_0;
        force csysack_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysack_0;
        force raq_split_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raq_split_0;
        force raqb_pop_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raqb_pop_0;
        force raqb_push_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raqb_push_0;
        force raqb_wcount_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raqb_wcount_0;
        force raqr_pop_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raqr_pop_0;
        force raqr_push_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raqr_push_0;
        force raqr_wcount_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.raqr_wcount_0;
        force waq_pop_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.waq_pop_0;
        force waq_push_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.waq_push_0;
        force waq_split_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.waq_split_0;
        force waq_wcount_0 = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.waq_wcount_0;
        force hpr_credit_cnt = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.hpr_credit_cnt;
        force lpr_credit_cnt = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.lpr_credit_cnt;
        force wr_credit_cnt = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wr_credit_cnt;
        force wrecc_credit_cnt = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wrecc_credit_cnt;
        force cactive_ddrc = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.cactive_ddrc;
        force csysack_ddrc = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.csysack_ddrc;
        force acsm_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.acsm_PRN;
        force bc_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.bc_PRN;
        force dccm_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dccm_PRN;
        force gs_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.gs_PRN;
        force iccm_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.iccm_PRN;
        force pie_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.pie_PRN;
        force wdata_PRN = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.wdata_PRN;
        force PhyInt_n = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.PhyInt_n;
        force dwc_lpddr5xphy_pll_lock = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dwc_lpddr5xphy_pll_lock;
        force dwc_lpddr5xphy_pmu_busy = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dwc_lpddr5xphy_pmu_busy;
        force hif_mrr_data = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.hif_mrr_data;
        force hif_mrr_data_valid = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.hif_mrr_data_valid;
        force perf_bank = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_bank;
        force perf_bg = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_bg;
        force perf_dfi_rd_data_cycles = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_dfi_rd_data_cycles;
        force perf_dfi_wr_data_cycles = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_dfi_wr_data_cycles;
        force perf_hif_hi_pri_rd = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hif_hi_pri_rd;
        force perf_hif_rd = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hif_rd;
        force perf_hif_rd_or_wr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hif_rd_or_wr;
        force perf_hif_rmw = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hif_rmw;
        force perf_hif_wr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hif_wr;
        force perf_hpr_req_with_nocredit = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hpr_req_with_nocredit;
        force perf_hpr_xact_when_critical = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_hpr_xact_when_critical;
        force perf_ie_blk_hazard = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_ie_blk_hazard;
        force perf_lpr_req_with_nocredit = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_lpr_req_with_nocredit;
        force perf_lpr_xact_when_critical = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_lpr_xact_when_critical;
        force perf_op_is_activate = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_activate;
        force perf_op_is_cas = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_cas;
        force perf_op_is_cas_wck_sus = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_cas_wck_sus;
        force perf_op_is_cas_ws = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_cas_ws;
        force perf_op_is_cas_ws_off = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_cas_ws_off;
        force perf_op_is_crit_ref = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_crit_ref;
        force perf_op_is_dqsosc_mpc = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_dqsosc_mpc;
        force perf_op_is_dqsosc_mrr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_dqsosc_mrr;
        force perf_op_is_enter_dsm = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_enter_dsm;
        force perf_op_is_enter_powerdown = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_enter_powerdown;
        force perf_op_is_enter_selfref = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_enter_selfref;
        force perf_op_is_load_mode = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_load_mode;
        force perf_op_is_mwr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_mwr;
        force perf_op_is_precharge = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_precharge;
        force perf_op_is_rd = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_rd;
        force perf_op_is_rd_activate = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_rd_activate;
        force perf_op_is_rd_or_wr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_rd_or_wr;
        force perf_op_is_refresh = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_refresh;
        force perf_op_is_rfm = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_rfm;
        force perf_op_is_spec_ref = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_spec_ref;
        force perf_op_is_tcr_mrr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_tcr_mrr;
        force perf_op_is_wr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_wr;
        force perf_op_is_zqlatch = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_zqlatch;
        force perf_op_is_zqstart = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_op_is_zqstart;
        force perf_precharge_for_other = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_precharge_for_other;
        force perf_precharge_for_rdwr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_precharge_for_rdwr;
        force perf_rank = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_rank;
        force perf_raw_hazard = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_raw_hazard;
        force perf_rdwr_transitions = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_rdwr_transitions;
        force perf_selfref_mode = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_selfref_mode;
        force perf_visible_window_limit_reached_rd = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_visible_window_limit_reached_rd;
        force perf_visible_window_limit_reached_wr = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_visible_window_limit_reached_wr;
        force perf_war_hazard = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_war_hazard;
        force perf_waw_hazard = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_waw_hazard;
        force perf_wr_xact_when_critical = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_wr_xact_when_critical;
        force perf_write_combine = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_write_combine;
        force perf_write_combine_noecc = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_write_combine_noecc;
        force perf_write_combine_wrecc = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.perf_write_combine_wrecc;
        force VIO_TIEHI = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.VIO_TIEHI;
        force dwc_lpddr5xphy_dto = axelera_lpddr_top_inst.u_lpddr_subsys_wrapper.snps_ddr_subsystem_inst.dwc_lpddr5xphy_dto;
    end

endmodule
