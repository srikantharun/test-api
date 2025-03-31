// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Wrapper of snps LPDDR subsys to align snps naming with our naming convention. 
// This is the actual LPDDR module instanciated inside lpddr_p. 
// Auto generated using wrap_snps_subsys.py/hjson/mako
// Owner: Roel Uytterhoeven

module lpddr_p_lpddr_subsys_wrapper (
    input logic  i_pclk,
    input logic  i_cfg_rst_n,
    input logic  i_pclk_apbrw,
    input logic  i_aclk,
    input logic  i_ctrl_rst_n,
    input logic  i_csysreq,
    input logic [32:0] i_lpddr_axi_m_araddr,
    input logic [1:0] i_lpddr_axi_m_arburst,
    input logic [3:0] i_lpddr_axi_m_arcache,
    input logic [7:0] i_lpddr_axi_m_arid,
    input logic [7:0] i_lpddr_axi_m_arlen,
    input logic  i_lpddr_axi_m_arlock,
    input logic [2:0] i_lpddr_axi_m_arprot,
    input logic [3:0] i_lpddr_axi_m_arqos,
    input logic [3:0] i_lpddr_axi_m_arregion,
    input logic [2:0] i_lpddr_axi_m_arsize,
    input logic  i_arurgentb,
    input logic  i_arurgentr,
    input logic  i_lpddr_axi_m_arvalid,
    input logic  i_lpddr_axi_m_rready,
    input logic [32:0] i_lpddr_axi_m_awaddr,
    input logic [1:0] i_lpddr_axi_m_awburst,
    input logic [3:0] i_lpddr_axi_m_awcache,
    input logic [7:0] i_lpddr_axi_m_awid,
    input logic [7:0] i_lpddr_axi_m_awlen,
    input logic  i_lpddr_axi_m_awlock,
    input logic [2:0] i_lpddr_axi_m_awprot,
    input logic [3:0] i_lpddr_axi_m_awqos,
    input logic [3:0] i_lpddr_axi_m_awregion,
    input logic [2:0] i_lpddr_axi_m_awsize,
    input logic  i_awurgent,
    input logic  i_lpddr_axi_m_awvalid,
    input logic [255:0] i_lpddr_axi_m_wdata,
    input logic  i_lpddr_axi_m_wlast,
    input logic [31:0] i_lpddr_axi_m_wstrb,
    input logic  i_lpddr_axi_m_wvalid,
    input logic  i_lpddr_axi_m_bready,
    input logic  i_core_ddrc_core_clk,
    input logic  i_core_ddrc_core_clk_apbrw,
    input logic  i_csysdiscamdrain_ddrc,
    input logic [4:0] i_csysfrequency_ddrc,
    input logic  i_csysfsp_ddrc,
    input logic  i_csysmode_ddrc,
    input logic  i_csysreq_ddrc,
    input logic  i_dficlk,
    input logic  i_sbr_clk,
    input logic  i_phy_rst,
    input logic  i_acsm_pde,
    input logic  i_acsm_ret,
    input logic  i_bc_pde,
    input logic  i_bc_ret,
    input logic  i_dccm_pde,
    input logic  i_dccm_ret,
    input logic  i_gs_pde,
    input logic  i_gs_ret,
    input logic  i_iccm_pde,
    input logic  i_iccm_ret,
    input logic [31:0] i_lpddr_cfg_apb_m_paddr,
    input logic  i_lpddr_cfg_apb_m_penable,
    input logic  i_pie_pde,
    input logic  i_pie_ret,
    input logic [2:0] i_lpddr_cfg_apb_m_pprot,
    input logic [2:0] i_pprot_pin,
    input logic  i_lpddr_cfg_apb_m_psel,
    input logic [3:0] i_lpddr_cfg_apb_m_pstrb,
    input logic [31:0] i_lpddr_cfg_apb_m_pwdata,
    input logic  i_lpddr_cfg_apb_m_pwrite,
    input logic  i_wdata_pde,
    input logic  i_wdata_ret,
    input logic  i_pllbypclk,
    input logic  i_pllrefclk,
    input logic  i_dis_regs_ecc_syndrome,
    output logic  o_cactive,
    output logic  o_csysack,
    output logic  o_lpddr_axi_m_arready,
    output logic  o_raq_split,
    output logic  o_raqb_pop,
    output logic  o_raqb_push,
    output logic [5:0] o_raqb_wcount,
    output logic  o_raqr_pop,
    output logic  o_raqr_push,
    output logic [5:0] o_raqr_wcount,
    output logic [255:0] o_lpddr_axi_m_rdata,
    output logic [7:0] o_lpddr_axi_m_rid,
    output logic  o_lpddr_axi_m_rlast,
    output logic [1:0] o_lpddr_axi_m_rresp,
    output logic  o_lpddr_axi_m_rvalid,
    output logic  o_lpddr_axi_m_awready,
    output logic  o_waq_pop,
    output logic  o_waq_push,
    output logic  o_waq_split,
    output logic [5:0] o_waq_wcount,
    output logic  o_lpddr_axi_m_wready,
    output logic [7:0] o_lpddr_axi_m_bid,
    output logic [1:0] o_lpddr_axi_m_bresp,
    output logic  o_lpddr_axi_m_bvalid,
    output wire  BP_MEMRESET_L,
    output logic [6:0] o_hpr_credit_cnt,
    output logic [6:0] o_lpr_credit_cnt,
    output logic [6:0] o_wr_credit_cnt,
    output logic [6:0] o_wrecc_credit_cnt,
    output logic  o_cactive_ddrc,
    output logic  o_csysack_ddrc,
    output logic  o_sbr_done_intr,
    output logic  o_derate_temp_limit_intr,
    output logic  o_ecc_ap_err_intr,
    output logic  o_ecc_corrected_err_intr,
    output logic  o_ecc_uncorrected_err_intr,
    output logic  o_rd_linkecc_corr_err_intr,
    output logic  o_rd_linkecc_uncorr_err_intr,
    output logic  o_acsm_prn,
    output logic  o_bc_prn,
    output logic  o_dccm_prn,
    output logic  o_gs_prn,
    output logic  o_iccm_prn,
    output logic  o_pie_prn,
    output logic [31:0] o_lpddr_cfg_apb_m_prdata,
    output logic  o_lpddr_cfg_apb_m_pready,
    output logic  o_lpddr_cfg_apb_m_pslverr,
    output logic  o_wdata_prn,
    output logic [15:0] o_phyint_n,
    output logic  o_dwc_lpddr5xphy_pll_lock,
    output logic  o_dwc_lpddr5xphy_pmu_busy,
    output logic [31:0] o_hif_mrr_data,
    output logic  o_hif_mrr_data_valid,
    output logic [2:0] o_perf_bank,
    output logic [1:0] o_perf_bg,
    output logic  o_perf_dfi_rd_data_cycles,
    output logic  o_perf_dfi_wr_data_cycles,
    output logic  o_perf_hif_hi_pri_rd,
    output logic  o_perf_hif_rd,
    output logic  o_perf_hif_rd_or_wr,
    output logic  o_perf_hif_rmw,
    output logic  o_perf_hif_wr,
    output logic  o_perf_hpr_req_with_nocredit,
    output logic  o_perf_hpr_xact_when_critical,
    output logic  o_perf_ie_blk_hazard,
    output logic  o_perf_lpr_req_with_nocredit,
    output logic  o_perf_lpr_xact_when_critical,
    output logic  o_perf_op_is_activate,
    output logic  o_perf_op_is_cas,
    output logic  o_perf_op_is_cas_wck_sus,
    output logic  o_perf_op_is_cas_ws,
    output logic  o_perf_op_is_cas_ws_off,
    output logic  o_perf_op_is_crit_ref,
    output logic  o_perf_op_is_dqsosc_mpc,
    output logic  o_perf_op_is_dqsosc_mrr,
    output logic  o_perf_op_is_enter_dsm,
    output logic [1:0] o_perf_op_is_enter_powerdown,
    output logic [1:0] o_perf_op_is_enter_selfref,
    output logic  o_perf_op_is_load_mode,
    output logic  o_perf_op_is_mwr,
    output logic  o_perf_op_is_precharge,
    output logic  o_perf_op_is_rd,
    output logic  o_perf_op_is_rd_activate,
    output logic  o_perf_op_is_rd_or_wr,
    output logic  o_perf_op_is_refresh,
    output logic  o_perf_op_is_rfm,
    output logic  o_perf_op_is_spec_ref,
    output logic  o_perf_op_is_tcr_mrr,
    output logic  o_perf_op_is_wr,
    output logic  o_perf_op_is_zqlatch,
    output logic  o_perf_op_is_zqstart,
    output logic  o_perf_precharge_for_other,
    output logic  o_perf_precharge_for_rdwr,
    output logic  o_perf_rank,
    output logic  o_perf_raw_hazard,
    output logic  o_perf_rdwr_transitions,
    output logic [1:0] o_perf_selfref_mode,
    output logic  o_perf_visible_window_limit_reached_rd,
    output logic  o_perf_visible_window_limit_reached_wr,
    output logic  o_perf_war_hazard,
    output logic  o_perf_waw_hazard,
    output logic  o_perf_wr_xact_when_critical,
    output logic  o_perf_write_combine,
    output logic  o_perf_write_combine_noecc,
    output logic  o_perf_write_combine_wrecc,
    output logic [1:0] o_dwc_lpddr5xphy_dto,
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
    , output wire snps_ddr_subsystem_inst_so, input wire tdr_scan_mode_data_out, 
    input wire tdr_iddq_mode_data_out, input wire tdr_burnIn_data_out, 
    input wire tdr_scan_ucclk_mode_data_out, 
    input wire tdr_scan_occ_reset_data_out, 
    input wire tdr_scan_occ_bypass_data_out, 
    input wire tdr_scan_asst_mode_data_out, 
    input wire tdr_scan_shift_async_data_out, 
    input wire tdr_scan_shift_cg_data_out, input wire tdi, 
    input wire lpddr_p_rtl2_tessent_sib_subs_inst_to_select, 
    input wire test_logic_reset, input wire capture_dr_en, 
    input wire shift_dr_en, input wire tck, input wire update_dr_en, 
    input wire sri_ctrl_all_test, input wire sri_ctrl_ltest_en, 
    input wire scan_en, output wire bscan_scan_out, 
    input wire host_bscan_to_sel, input wire force_disable, 
    input wire select_jtag_input, input wire select_jtag_output, 
    input wire bisr_shift_en, input wire bisr_clk, input wire bisr_reset, 
    input wire bisr_si, output wire bisr_so, 
    input wire to_DdrPhyCsrCmdTdrCaptureEn, 
    input wire to_DdrPhyCsrCmdTdrShiftEn, 
    input wire to_DdrPhyCsrCmdTdrUpdateEn, output wire DdrPhyCsrCmdTdr_Tdo, 
    input wire to_DdrPhyCsrRdDataTdrCaptureEn, 
    input wire to_DdrPhyCsrRdDataTdrShiftEn, 
    input wire to_DdrPhyCsrRdDataTdrUpdateEn, 
    output wire DdrPhyCsrRdDataTdr_Tdo, input wire to_WSI, 
    input wire clock_out, input wire clock_out_ts1);
    wire  VIO_TIEHI;

    snps_ddr_subsystem snps_ddr_subsystem_inst (
        .pclk(i_pclk),
        .presetn(i_cfg_rst_n),
        .pclk_apbrw(i_pclk_apbrw),
        .aclk_0(i_aclk),
        .aresetn_0(i_ctrl_rst_n),
        .csysreq_0(i_csysreq),
        .araddr_0(i_lpddr_axi_m_araddr),
        .arautopre_0('0),
        .arburst_0(i_lpddr_axi_m_arburst),
        .arcache_0(i_lpddr_axi_m_arcache),
        .arid_0(i_lpddr_axi_m_arid),
        .arlen_0(i_lpddr_axi_m_arlen),
        .arlock_0(i_lpddr_axi_m_arlock),
        .arpoison_0('0),
        .arprot_0(i_lpddr_axi_m_arprot),
        .arqos_0(i_lpddr_axi_m_arqos),
        .arregion_0(i_lpddr_axi_m_arregion),
        .arsize_0(i_lpddr_axi_m_arsize),
        .arurgentb_0(i_arurgentb),
        .arurgentr_0(i_arurgentr),
        .arvalid_0(i_lpddr_axi_m_arvalid),
        .rready_0(i_lpddr_axi_m_rready),
        .awaddr_0(i_lpddr_axi_m_awaddr),
        .awautopre_0('0),
        .awburst_0(i_lpddr_axi_m_awburst),
        .awcache_0(i_lpddr_axi_m_awcache),
        .awid_0(i_lpddr_axi_m_awid),
        .awlen_0(i_lpddr_axi_m_awlen),
        .awlock_0(i_lpddr_axi_m_awlock),
        .awpoison_0('0),
        .awprot_0(i_lpddr_axi_m_awprot),
        .awqos_0(i_lpddr_axi_m_awqos),
        .awregion_0(i_lpddr_axi_m_awregion),
        .awsize_0(i_lpddr_axi_m_awsize),
        .awurgent_0(i_awurgent),
        .awvalid_0(i_lpddr_axi_m_awvalid),
        .wdata_0(i_lpddr_axi_m_wdata),
        .wlast_0(i_lpddr_axi_m_wlast),
        .wstrb_0(i_lpddr_axi_m_wstrb),
        .wvalid_0(i_lpddr_axi_m_wvalid),
        .bready_0(i_lpddr_axi_m_bready),
        .BP_PWROK(VIO_TIEHI),
        .core_ddrc_core_clk(i_core_ddrc_core_clk),
        .core_ddrc_core_clk_apbrw(i_core_ddrc_core_clk_apbrw),
        .core_ddrc_rstn(i_ctrl_rst_n),
        .csysdiscamdrain_ddrc(i_csysdiscamdrain_ddrc),
        .csysfrequency_ddrc(i_csysfrequency_ddrc),
        .csysfsp_ddrc(i_csysfsp_ddrc),
        .csysmode_ddrc(i_csysmode_ddrc),
        .csysreq_ddrc(i_csysreq_ddrc),
        .DfiClk(i_dficlk),
        .sbr_clk(i_sbr_clk),
        .sbr_resetn(i_ctrl_rst_n),
        .dfi_reset_n_in('1),
        .init_mr_done_in('1),
        .Reset_async(i_phy_rst),
        .acsm_ADME(axe_tcl_pkg::ADME),
        .acsm_CRE1('0),
        .acsm_CRE2('0),
        .acsm_FCA1('0),
        .acsm_FCA2('0),
        .acsm_FRA1('0),
        .acsm_FRA2('0),
        .acsm_MCS(axe_tcl_pkg::MCS),
        .acsm_MCSW(axe_tcl_pkg::MCSW),
        .acsm_PDE(i_acsm_pde),
        .acsm_RET(i_acsm_ret),
        .acsm_RREN1('0),
        .acsm_RREN2('0),
        .bc_ADME(axe_tcl_pkg::ADME),
        .bc_CRE1('0),
        .bc_CRE2('0),
        .bc_FCA1('0),
        .bc_FCA2('0),
        .bc_FRA1('0),
        .bc_FRA2('0),
        .bc_MCS(axe_tcl_pkg::MCS),
        .bc_MCSW(axe_tcl_pkg::MCSW),
        .bc_PDE(i_bc_pde),
        .bc_RET(i_bc_ret),
        .bc_RREN1('0),
        .bc_RREN2('0),
        .dccm_ADME(axe_tcl_pkg::ADME),
        .dccm_CRE1('0),
        .dccm_CRE2('0),
        .dccm_FCA1('0),
        .dccm_FCA2('0),
        .dccm_FRA1('0),
        .dccm_FRA2('0),
        .dccm_MCS(axe_tcl_pkg::MCS),
        .dccm_MCSW(axe_tcl_pkg::MCSW),
        .dccm_PDE(i_dccm_pde),
        .dccm_RET(i_dccm_ret),
        .dccm_RREN1('0),
        .dccm_RREN2('0),
        .gs_ADME(axe_tcl_pkg::ADME),
        .gs_CRE1('0),
        .gs_CRE2('0),
        .gs_FCA1('0),
        .gs_FCA2('0),
        .gs_FRA1('0),
        .gs_FRA2('0),
        .gs_MCS(axe_tcl_pkg::MCS),
        .gs_MCSW(axe_tcl_pkg::MCSW),
        .gs_PDE(i_gs_pde),
        .gs_RET(i_gs_ret),
        .gs_RREN1('0),
        .gs_RREN2('0),
        .iccm_ADME(axe_tcl_pkg::ADME),
        .iccm_CRE1('0),
        .iccm_CRE2('0),
        .iccm_FCA1('0),
        .iccm_FCA2('0),
        .iccm_FRA1('0),
        .iccm_FRA2('0),
        .iccm_MCS(axe_tcl_pkg::MCS),
        .iccm_MCSW(axe_tcl_pkg::MCSW),
        .iccm_PDE(i_iccm_pde),
        .iccm_RET(i_iccm_ret),
        .iccm_RREN1('0),
        .iccm_RREN2('0),
        .paddr(i_lpddr_cfg_apb_m_paddr),
        .penable(i_lpddr_cfg_apb_m_penable),
        .pie_ADME(axe_tcl_pkg::ADME),
        .pie_CRE1('0),
        .pie_CRE2('0),
        .pie_FCA1('0),
        .pie_FCA2('0),
        .pie_FRA1('0),
        .pie_FRA2('0),
        .pie_MCS(axe_tcl_pkg::MCS),
        .pie_MCSW(axe_tcl_pkg::MCSW),
        .pie_PDE(i_pie_pde),
        .pie_RET(i_pie_ret),
        .pie_RREN1('0),
        .pie_RREN2('0),
        .pprot(i_lpddr_cfg_apb_m_pprot),
        .pprot_pin(i_pprot_pin),
        .psel(i_lpddr_cfg_apb_m_psel),
        .pstrb(i_lpddr_cfg_apb_m_pstrb),
        .pwdata(i_lpddr_cfg_apb_m_pwdata),
        .pwrite(i_lpddr_cfg_apb_m_pwrite),
        .scan_shift_i('0),
        .wdata_ADME(axe_tcl_pkg::ADME),
        .wdata_CRE1('0),
        .wdata_CRE2('0),
        .wdata_FCA1('0),
        .wdata_FCA2('0),
        .wdata_FRA1('0),
        .wdata_FRA2('0),
        .wdata_KCS('0),
        .wdata_MCSRD(axe_tcl_pkg::MCS),
        .wdata_MCSWR(axe_tcl_pkg::MCS),
        .wdata_PDE(i_wdata_pde),
        .wdata_RET(i_wdata_ret),
        .wdata_RREN1('0),
        .wdata_RREN2('0),
        .PllBypClk(i_pllbypclk),
        .PllRefClk(i_pllrefclk),
        .pa_rmask('0),
        .pa_wmask('0),
        .dis_regs_ecc_syndrome(i_dis_regs_ecc_syndrome),
        .Reset(i_phy_rst),
        .scan_DlyTestClk(clock_out),
        .scan_asst_mode(tdr_scan_asst_mode_data_out),
        .scan_clk(clock_out_ts1),
        .scan_mode(tdr_scan_mode_data_out),
        .scan_occ_bypass(tdr_scan_occ_bypass_data_out),
        .scan_occ_reset(tdr_scan_occ_reset_data_out),
        .scan_shift_async(tdr_scan_shift_async_data_out),
        .scan_shift_cg(tdr_scan_shift_cg_data_out),
        .scan_si('0),
        .DdrPhyCsrCmdTdrCaptureEn(to_DdrPhyCsrCmdTdrCaptureEn),
        .DdrPhyCsrCmdTdrShiftEn(to_DdrPhyCsrCmdTdrShiftEn),
        .DdrPhyCsrCmdTdrUpdateEn(to_DdrPhyCsrCmdTdrUpdateEn),
        .DdrPhyCsrRdDataTdrCaptureEn(to_DdrPhyCsrRdDataTdrCaptureEn),
        .DdrPhyCsrRdDataTdrShiftEn(to_DdrPhyCsrRdDataTdrShiftEn),
        .DdrPhyCsrRdDataTdrUpdateEn(to_DdrPhyCsrRdDataTdrUpdateEn),
        .TDRCLK(tck),
        .WRSTN(test_logic_reset),
        .WSI(to_WSI),
        .BurnIn(tdr_burnIn_data_out),
        .Iddq_mode(tdr_iddq_mode_data_out),
        .cactive_0(o_cactive),
        .csysack_0(o_csysack),
        .arpoison_intr_0(),
        .arready_0(o_lpddr_axi_m_arready),
        .raq_split_0(o_raq_split),
        .raqb_pop_0(o_raqb_pop),
        .raqb_push_0(o_raqb_push),
        .raqb_wcount_0(o_raqb_wcount),
        .raqr_pop_0(o_raqr_pop),
        .raqr_push_0(o_raqr_push),
        .raqr_wcount_0(o_raqr_wcount),
        .rdata_0(o_lpddr_axi_m_rdata),
        .rid_0(o_lpddr_axi_m_rid),
        .rlast_0(o_lpddr_axi_m_rlast),
        .rresp_0(o_lpddr_axi_m_rresp),
        .rvalid_0(o_lpddr_axi_m_rvalid),
        .awpoison_intr_0(),
        .awready_0(o_lpddr_axi_m_awready),
        .waq_pop_0(o_waq_pop),
        .waq_push_0(o_waq_push),
        .waq_split_0(o_waq_split),
        .waq_wcount_0(o_waq_wcount),
        .wready_0(o_lpddr_axi_m_wready),
        .bid_0(o_lpddr_axi_m_bid),
        .bresp_0(o_lpddr_axi_m_bresp),
        .bvalid_0(o_lpddr_axi_m_bvalid),
        .BP_MEMRESET_L(BP_MEMRESET_L),
        .hpr_credit_cnt(o_hpr_credit_cnt),
        .lpr_credit_cnt(o_lpr_credit_cnt),
        .wr_credit_cnt(o_wr_credit_cnt),
        .wrecc_credit_cnt(o_wrecc_credit_cnt),
        .cactive_ddrc(o_cactive_ddrc),
        .csysack_ddrc(o_csysack_ddrc),
        .stat_ddrc_reg_selfref_type(),
        .sbr_done_intr(o_sbr_done_intr),
        .dbg_dfi_ie_cmd_type(),
        .derate_temp_limit_intr(o_derate_temp_limit_intr),
        .derate_temp_limit_intr_fault(),
        .ecc_ap_err_intr(o_ecc_ap_err_intr),
        .ecc_ap_err_intr_fault(),
        .ecc_corrected_err_intr(o_ecc_corrected_err_intr),
        .ecc_corrected_err_intr_fault(),
        .ecc_uncorrected_err_intr(o_ecc_uncorrected_err_intr),
        .ecc_uncorrected_err_intr_fault(),
        .rd_linkecc_corr_err_intr(o_rd_linkecc_corr_err_intr),
        .rd_linkecc_corr_err_intr_fault(),
        .rd_linkecc_uncorr_err_intr(o_rd_linkecc_uncorr_err_intr),
        .rd_linkecc_uncorr_err_intr_fault(),
        .dfi_reset_n_ref(),
        .init_mr_done_out(),
        .acsm_PRN(o_acsm_prn),
        .bc_PRN(o_bc_prn),
        .dccm_PRN(o_dccm_prn),
        .gs_PRN(o_gs_prn),
        .iccm_PRN(o_iccm_prn),
        .pie_PRN(o_pie_prn),
        .prdata(o_lpddr_cfg_apb_m_prdata),
        .prdata_par(),
        .pready(o_lpddr_cfg_apb_m_pready),
        .pslverr(o_lpddr_cfg_apb_m_pslverr),
        .wdata_PRN(o_wdata_prn),
        .PhyInt_fault(),
        .PhyInt_n(o_phyint_n),
        .dwc_lpddr5xphy_pll_lock(o_dwc_lpddr5xphy_pll_lock),
        .dwc_lpddr5xphy_pmu_busy(o_dwc_lpddr5xphy_pmu_busy),
        .hif_mrr_data(o_hif_mrr_data),
        .hif_mrr_data_valid(o_hif_mrr_data_valid),
        .hif_refresh_req_bank(),
        .perf_bank(o_perf_bank),
        .perf_bg(o_perf_bg),
        .perf_dfi_rd_data_cycles(o_perf_dfi_rd_data_cycles),
        .perf_dfi_wr_data_cycles(o_perf_dfi_wr_data_cycles),
        .perf_hif_hi_pri_rd(o_perf_hif_hi_pri_rd),
        .perf_hif_rd(o_perf_hif_rd),
        .perf_hif_rd_or_wr(o_perf_hif_rd_or_wr),
        .perf_hif_rmw(o_perf_hif_rmw),
        .perf_hif_wr(o_perf_hif_wr),
        .perf_hpr_req_with_nocredit(o_perf_hpr_req_with_nocredit),
        .perf_hpr_xact_when_critical(o_perf_hpr_xact_when_critical),
        .perf_ie_blk_hazard(o_perf_ie_blk_hazard),
        .perf_lpr_req_with_nocredit(o_perf_lpr_req_with_nocredit),
        .perf_lpr_xact_when_critical(o_perf_lpr_xact_when_critical),
        .perf_op_is_activate(o_perf_op_is_activate),
        .perf_op_is_cas(o_perf_op_is_cas),
        .perf_op_is_cas_wck_sus(o_perf_op_is_cas_wck_sus),
        .perf_op_is_cas_ws(o_perf_op_is_cas_ws),
        .perf_op_is_cas_ws_off(o_perf_op_is_cas_ws_off),
        .perf_op_is_crit_ref(o_perf_op_is_crit_ref),
        .perf_op_is_dqsosc_mpc(o_perf_op_is_dqsosc_mpc),
        .perf_op_is_dqsosc_mrr(o_perf_op_is_dqsosc_mrr),
        .perf_op_is_enter_dsm(o_perf_op_is_enter_dsm),
        .perf_op_is_enter_powerdown(o_perf_op_is_enter_powerdown),
        .perf_op_is_enter_selfref(o_perf_op_is_enter_selfref),
        .perf_op_is_load_mode(o_perf_op_is_load_mode),
        .perf_op_is_mwr(o_perf_op_is_mwr),
        .perf_op_is_precharge(o_perf_op_is_precharge),
        .perf_op_is_rd(o_perf_op_is_rd),
        .perf_op_is_rd_activate(o_perf_op_is_rd_activate),
        .perf_op_is_rd_or_wr(o_perf_op_is_rd_or_wr),
        .perf_op_is_refresh(o_perf_op_is_refresh),
        .perf_op_is_rfm(o_perf_op_is_rfm),
        .perf_op_is_spec_ref(o_perf_op_is_spec_ref),
        .perf_op_is_tcr_mrr(o_perf_op_is_tcr_mrr),
        .perf_op_is_wr(o_perf_op_is_wr),
        .perf_op_is_zqlatch(o_perf_op_is_zqlatch),
        .perf_op_is_zqstart(o_perf_op_is_zqstart),
        .perf_precharge_for_other(o_perf_precharge_for_other),
        .perf_precharge_for_rdwr(o_perf_precharge_for_rdwr),
        .perf_rank(o_perf_rank),
        .perf_raw_hazard(o_perf_raw_hazard),
        .perf_rdwr_transitions(o_perf_rdwr_transitions),
        .perf_selfref_mode(o_perf_selfref_mode),
        .perf_visible_window_limit_reached_rd(o_perf_visible_window_limit_reached_rd),
        .perf_visible_window_limit_reached_wr(o_perf_visible_window_limit_reached_wr),
        .perf_war_hazard(o_perf_war_hazard),
        .perf_waw_hazard(o_perf_waw_hazard),
        .perf_wr_xact_when_critical(o_perf_wr_xact_when_critical),
        .perf_write_combine(o_perf_write_combine),
        .perf_write_combine_noecc(o_perf_write_combine_noecc),
        .perf_write_combine_wrecc(o_perf_write_combine_wrecc),
        .VIO_TIEHI(VIO_TIEHI),
        .scan_so(),
        .DdrPhyCsrCmdTdr_Tdo(DdrPhyCsrCmdTdr_Tdo),
        .DdrPhyCsrRdDataTdr_Tdo(DdrPhyCsrRdDataTdr_Tdo),
        .dwc_lpddr5xphy_dto(o_dwc_lpddr5xphy_dto),
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
        .BP_ZN(BP_ZN), .ijtag_tck(tck), .ijtag_reset(test_logic_reset), 
                        .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), 
                        .ijtag_ue(update_dr_en), .ijtag_sel(lpddr_p_rtl2_tessent_sib_subs_inst_to_select), 
                        .ijtag_si(tdi), .ijtag_so(snps_ddr_subsystem_inst_so), 
                        .ltest_en(sri_ctrl_ltest_en), .all_test(sri_ctrl_all_test), 
                        .scan_en(scan_en), .bscan_select(host_bscan_to_sel), 
                        .bscan_force_disable(force_disable), 
                        .bscan_select_jtag_input(select_jtag_input), 
                        .bscan_select_jtag_output(select_jtag_output), 
                        .bscan_clock(tck), .bscan_capture_en(capture_dr_en), 
                        .bscan_shift_en(shift_dr_en), .bscan_update_en(update_dr_en), 
                        .bscan_scan_in(tdi), .bscan_scan_out(bscan_scan_out), 
                        .bisr_so(bisr_so), .bisr_si(bisr_si), .bisr_shift_en(bisr_shift_en), 
                        .bisr_clk(bisr_clk), .bisr_reset(bisr_reset), 
                        .scan_UcClk(clock_out), .scan_ucclk_mode(tdr_scan_ucclk_mode_data_out)
    );

endmodule
