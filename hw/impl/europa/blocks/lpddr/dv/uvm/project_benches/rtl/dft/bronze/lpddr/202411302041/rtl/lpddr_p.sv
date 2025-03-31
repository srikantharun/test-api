
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//

module lpddr_p
  import chip_pkg::*;
  import axi_pkg::*;
  import lpddr_pkg::*;
  (
  // Clocks
  input  wire   i_ao_clk,
  input  wire   i_lpddr_clk,

  //-------------------------------
  // Partition Controller Interface
  //-------------------------------
  input  wire                         i_ao_rst_n          ,
  input  wire                         i_global_rst_n      ,
  output wire                         o_ao_rst_sync_n     ,
  output logic          [1:0]         o_noc_async_idle_req, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  input  logic          [1:0]         i_noc_async_idle_ack, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  input  logic          [1:0]         i_noc_async_idle_val, // Fence 0 for lpddr_cfg_apb noc interface, Fence 1 for lpddr_axi noc interface
  output logic                        o_noc_clken         ,
  output wire                         o_noc_rst_n         ,

  //-------------------------------
  // AXI4 lpddr_axi
  //-------------------------------
  input  logic [39:0]  i_lpddr_axi_m_araddr  ,
  input  logic [1:0]   i_lpddr_axi_m_arburst ,
  input  logic [3:0]   i_lpddr_axi_m_arcache ,
  input  logic [7:0]   i_lpddr_axi_m_arid    ,
  input  logic [7:0]   i_lpddr_axi_m_arlen   ,
  input  logic i_lpddr_axi_m_arlock  ,
  input  logic [2:0]   i_lpddr_axi_m_arprot  ,
  input  logic [3:0]   i_lpddr_axi_m_arqos   ,
  input  logic [3:0]   i_lpddr_axi_m_arregion,
  input  logic         i_lpddr_axi_m_aruser  ,
  input  logic [2:0]   i_lpddr_axi_m_arsize  ,
  input  logic i_lpddr_axi_m_arvalid ,
  input  logic i_lpddr_axi_m_rready  ,
  input  logic [39:0]  i_lpddr_axi_m_awaddr  ,
  input  logic [1:0]   i_lpddr_axi_m_awburst ,
  input  logic [3:0]   i_lpddr_axi_m_awcache ,
  input  logic [7:0]   i_lpddr_axi_m_awid    ,
  input  logic [7:0]   i_lpddr_axi_m_awlen   ,
  input  logic i_lpddr_axi_m_awlock  ,
  input  logic [2:0]   i_lpddr_axi_m_awprot  ,
  input  logic [3:0]   i_lpddr_axi_m_awqos   ,
  input  logic [3:0]   i_lpddr_axi_m_awregion,
  input  logic         i_lpddr_axi_m_awuser  ,
  input  logic [2:0]   i_lpddr_axi_m_awsize  ,
  input  logic i_lpddr_axi_m_awvalid ,
  input  logic [255:0] i_lpddr_axi_m_wdata   ,
  input  logic i_lpddr_axi_m_wlast   ,
  input  logic [31:0]  i_lpddr_axi_m_wstrb   ,
  input  logic i_lpddr_axi_m_wvalid  ,
  input  logic i_lpddr_axi_m_wuser  ,
  input  logic i_lpddr_axi_m_bready  ,
  output logic o_lpddr_axi_m_arready,
  output logic [255:0] o_lpddr_axi_m_rdata  ,
  output logic [7:0]   o_lpddr_axi_m_rid    ,
  output logic o_lpddr_axi_m_rlast  ,
  output logic o_lpddr_axi_m_ruser ,
  output logic [1:0]   o_lpddr_axi_m_rresp  ,
  output logic o_lpddr_axi_m_rvalid ,
  output logic o_lpddr_axi_m_awready,
  output logic o_lpddr_axi_m_wready ,
  output logic [7:0]   o_lpddr_axi_m_bid    ,
  output logic [1:0]   o_lpddr_axi_m_bresp  ,
  output logic o_lpddr_axi_m_bvalid ,
  output logic o_lpddr_axi_m_buser ,

  //-------------------------------
  // APB4 lpddr_cfg_apb (sync to i_lpddr_clk)
  //-------------------------------
  input  logic [31:0] i_lpddr_cfg_apb4_s_paddr,
  input  logic        i_lpddr_cfg_apb4_s_penable,
  input  logic [2:0]  i_lpddr_cfg_apb4_s_pprot,
  input  logic        i_lpddr_cfg_apb4_s_psel,
  input  logic [3:0]  i_lpddr_cfg_apb4_s_pstrb,
  input  logic [31:0] i_lpddr_cfg_apb4_s_pwdata,
  input  logic        i_lpddr_cfg_apb4_s_pwrite,
  output logic [31:0] o_lpddr_cfg_apb4_s_prdata,
  output logic        o_lpddr_cfg_apb4_s_pready,
  output logic        o_lpddr_cfg_apb4_s_pslverr,
  //-------------------------------
  // APB4 lpddr_syscfg_apb (sync to i_ao_clk)
  //-------------------------------
  input  chip_syscfg_addr_t           i_lpddr_syscfg_apb4_s_paddr  ,
  input  chip_apb_syscfg_data_t       i_lpddr_syscfg_apb4_s_pwdata ,
  input  logic                        i_lpddr_syscfg_apb4_s_pwrite ,
  input  logic                        i_lpddr_syscfg_apb4_s_psel   ,
  input  logic                        i_lpddr_syscfg_apb4_s_penable,
  input  chip_apb_syscfg_strb_t       i_lpddr_syscfg_apb4_s_pstrb  ,
  input  logic                  [2:0] i_lpddr_syscfg_apb4_s_pprot  ,
  output logic                        o_lpddr_syscfg_apb4_s_pready ,
  output chip_apb_syscfg_data_t       o_lpddr_syscfg_apb4_s_prdata ,
  output logic                        o_lpddr_syscfg_apb4_s_pslverr,

  // CTRL Interrupts
  output logic  o_ctrl_sbr_done_intr,
  output logic  o_ctrl_derate_temp_limit_intr,
  output logic  o_ctrl_ecc_ap_err_intr,
  output logic  o_ctrl_ecc_corrected_err_intr,
  output logic  o_ctrl_ecc_uncorrected_err_intr,
  output logic  o_ctrl_rd_linkecc_corr_err_intr,
  output logic  o_ctrl_rd_linkecc_uncorr_err_intr,

  // PHY interrupts
  output logic  o_phy_pie_prog_err_intr,
  output logic  o_phy_ecc_err_intr,
  output logic  o_phy_rdfptrchk_err_intr,
  output logic  o_phy_pie_parity_err_intr,
  output logic  o_phy_acsm_parity_err_intr,
  output logic  o_phy_trng_fail_intr,
  output logic  o_phy_init_cmplt_intr,
  output logic  o_phy_trng_cmplt_intr,

  //-------------------------------
  // DFT Interface add by axelera
  //-------------------------------
  input wire  tck,
  input wire  trst,
  input logic tms,
  input logic tdi,
  output logic tdo_en,
  output logic tdo,

  input wire  ssn_bus_clk,
  input logic [24 -1: 0] ssn_bus_data_in,
  output logic [24 -1: 0] ssn_bus_data_out,

  input wire  bisr_clk,
  input wire  bisr_reset,
  input logic  bisr_shift_en,
  input logic  bisr_si,
  output logic  bisr_so,

  // Observability signals for lpddr
  output logic [15:0] o_lpddr_obs,

  //-----------
  // PHY Bump signals
  //-----------
  output wire  BP_MEMRESET_L,
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

  //-------------------------------
  // Partition controller Instance
  //-------------------------------
  
  wire [0:0] lpddr_p_rtl2_tessent_tdr_phy_inst_dout0, tdr_scan_mode_data_out, 
             tdr_iddq_mode_data_out, tdr_burnIn_data_out, 
             tdr_scan_ucclk_mode_data_out, tdr_scan_occ_reset_data_out, 
             tdr_scan_occ_bypass_data_out, tdr_scan_asst_mode_data_out, 
             tdr_scan_shift_async_data_out, tdr_scan_shift_cg_data_out;
  wire [23:0] bus_data_out;
  logic bisr_so_ts1;
  wire [11:0] ssh_sh_grp_gi_to_scan_in, edt_channels_out;
  wire [4:0] ssh_sh_grp_gx_to_scan_in, edt_channels_out_ts1;
  wire [449:0] edt_scan_in;
  wire lpddr_p_rtl2_tessent_sib_sri_inst_so, 
       lpddr_p_rtl2_tessent_sib_sri_local_inst_so, 
       lpddr_p_rtl2_tessent_tap_main_inst_to_select, snps_ddr_subsystem_inst_so, 
       lpddr_p_rtl2_tessent_sib_sri_inst_to_select, 
       lpddr_p_rtl2_tessent_sib_subs_inst_so, 
       lpddr_p_rtl2_tessent_scanmux_tdr_inst_so, 
       lpddr_p_rtl2_tessent_sib_tdr_inst_so, 
       lpddr_p_rtl2_tessent_tdr_scan_shift_cg_inst_so, 
       lpddr_p_rtl2_tessent_sib_scan_cfg_inst_so, 
       lpddr_p_rtl2_tessent_sib_ssn_inst_so, 
       lpddr_p_rtl2_tessent_sib_occ_inst_so, 
       lpddr_p_rtl2_tessent_sib_edt_inst_so, 
       lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst_so, 
       lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_so, 
       dwc_ddrphy_jtag_dfttdrs_Cmd_inst_so, 
       dwc_ddrphy_jtag_dfttdrs_RdData_inst_so, 
       lpddr_p_rtl2_tessent_sib_tdr_inst_to_enable_in, 
       lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_to_select, 
       lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select, 
       lpddr_p_rtl2_tessent_tdr_scan_mode_inst_so, 
       lpddr_p_rtl2_tessent_tdr_iddq_mode_inst_so, 
       lpddr_p_rtl2_tessent_tdr_burnIn_inst_so, 
       lpddr_p_rtl2_tessent_tdr_scan_ucclk_mode_inst_so, 
       lpddr_p_rtl2_tessent_tdr_scan_occ_reset_inst_so, 
       lpddr_p_rtl2_tessent_tdr_scan_occ_bypass_inst_so, 
       lpddr_p_rtl2_tessent_tdr_scan_asst_mode_inst_so, 
       lpddr_p_rtl2_tessent_tdr_scan_shift_async_inst_so, 
       lpddr_p_rtl2_tessent_tdr_phy_inst_so, 
       lpddr_p_rtl2_tessent_scanmux_tdr_inst_to_select0, 
       lpddr_p_rtl2_tessent_scanmux_tdr_inst_to_select1, 
       lpddr_p_rtl2_tessent_sib_subs_inst_to_select, test_logic_reset, 
       capture_dr_en, shift_dr_en, update_dr_en, test_clock, scan_en, 
       edt_update_inv, edt_update, sri_ctrl_all_test, sri_ctrl_ltest_en, 
       ijtag_to_sel, ssh0_so, bscan_scan_out, host_bscan_to_sel, force_disable, 
       select_jtag_input, select_jtag_output, i_lpddr_clk_ts1, o_clk, 
       occ_kill_clock_en, ijtag_to_sel_ts1, i_ao_clk_ts1, ijtag_so, 
       ijtag_so_ts1, o_clk_ts1, edt_bypass, edt_low_power_shift_en, 
       ijtag_to_sel_ts2, edt_bypass_ts1, ijtag_so_ts2, ijtag_so_ts3, o_z, 
       o_z_ts1, o_z_ts2, o_z_ts3, o_z_ts4, o_z_ts5, o_z_ts6, o_z_ts7, o_z_ts8, 
       o_z_ts9, o_z_ts10, o_z_ts11, o_z_ts12, o_z_ts13, o_z_ts14, o_z_ts15, 
       o_z_ts16, o_z_ts17, o_z_ts18, o_z_ts19, o_z_ts20, o_z_ts21, o_z_ts22, 
       o_z_ts23, o_z_ts24, o_z_ts25, o_z_ts26, o_z_ts27, o_z_ts28, o_z_ts29, 
       o_z_ts30, o_z_ts31, o_z_ts32, o_z_ts33, o_z_ts34, o_z_ts35, o_z_ts36, 
       o_z_ts37, o_z_ts38, o_z_ts39, o_z_ts40, o_z_ts41, o_z_ts42, o_z_ts43, 
       o_z_ts44, o_z_ts45, o_z_ts46, o_z_ts47, o_z_ts48, o_z_ts49, o_z_ts50, 
       o_z_ts51, o_z_ts52, o_z_ts53, o_z_ts54, o_z_ts55, o_z_ts56, o_z_ts57, 
       o_z_ts58, o_z_ts59, o_z_ts60, o_z_ts61, o_z_ts62, o_z_ts63, o_z_ts64, 
       o_z_ts65, o_z_ts66, o_z_ts67, o_z_ts68, o_z_ts69, o_z_ts70, o_z_ts71, 
       o_z_ts72, o_z_ts73, o_z_ts74, o_z_ts75, o_z_ts76, o_z_ts77, o_z_ts78, 
       o_z_ts79, o_z_ts80, o_z_ts81, o_z_ts82, o_z_ts83, o_z_ts84, o_z_ts85, 
       o_z_ts86, o_z_ts87, o_z_ts88, o_z_ts89, o_z_ts90, o_z_ts91, o_z_ts92, 
       o_z_ts93, o_z_ts94, o_z_ts95, o_z_ts96, o_z_ts97, o_z_ts98, o_z_ts99, 
       o_z_ts100, o_z_ts101, o_z_ts102, o_z_ts103, o_z_ts104, o_z_ts105, 
       o_z_ts106, o_z_ts107, o_z_ts108, o_z_ts109, o_z_ts110, o_z_ts111, 
       o_z_ts112, o_z_ts113, o_z_ts114, o_z_ts115, o_z_ts116, o_z_ts117, 
       o_z_ts118, o_z_ts119, o_z_ts120, o_z_ts121, o_z_ts122, o_z_ts123, 
       o_z_ts124, o_z_ts125, o_z_ts126, o_z_ts127, o_z_ts128, o_z_ts129, 
       o_z_ts130, o_z_ts131, o_z_ts132, o_z_ts133, o_z_ts134, o_z_ts135, 
       o_z_ts136, o_z_ts137, o_z_ts138, o_z_ts139, o_z_ts140, o_z_ts141, 
       o_z_ts142, o_z_ts143, o_z_ts144, o_z_ts145, o_z_ts146, o_z_ts147, 
       o_z_ts148, o_z_ts149, o_z_ts150, o_z_ts151, o_z_ts152, o_z_ts153, 
       o_z_ts154, o_z_ts155, o_z_ts156, o_z_ts157, o_z_ts158, o_z_ts159, 
       o_z_ts160, o_z_ts161, o_z_ts162, o_z_ts163, o_z_ts164, o_z_ts165, 
       o_z_ts166, o_z_ts167, o_z_ts168, o_z_ts169, o_z_ts170, o_z_ts171, 
       o_z_ts172, o_z_ts173, o_z_ts174, o_z_ts175, o_z_ts176, o_z_ts177, 
       o_z_ts178, o_z_ts179, o_z_ts180, o_z_ts181, o_z_ts182, o_z_ts183, 
       o_z_ts184, o_z_ts185, o_z_ts186, o_z_ts187, o_z_ts188, o_z_ts189, 
       o_z_ts190, o_z_ts191, o_z_ts192, o_z_ts193, o_z_ts194, o_z_ts195, 
       o_z_ts196, o_z_ts197, o_z_ts198, o_z_ts199, o_z_ts200, o_z_ts201, 
       o_z_ts202, o_z_ts203, o_z_ts204, o_z_ts205, o_z_ts206, o_z_ts207, 
       o_z_ts208, o_z_ts209, o_z_ts210, o_z_ts211, o_z_ts212, o_z_ts213, 
       o_z_ts214, o_z_ts215, o_z_ts216, o_z_ts217, o_z_ts218, o_z_ts219, 
       o_z_ts220, o_z_ts221, o_z_ts222, o_z_ts223, o_z_ts224, o_z_ts225, 
       o_z_ts226, o_z_ts227, o_z_ts228, o_z_ts229, o_z_ts230, o_z_ts231, 
       o_z_ts232, o_z_ts233, o_z_ts234, o_z_ts235, o_z_ts236, o_z_ts237, 
       o_z_ts238, o_z_ts239, o_z_ts240, o_z_ts241, o_z_ts242, o_z_ts243, 
       o_z_ts244, o_z_ts245, o_z_ts246, o_z_ts247, o_z_ts248, o_z_ts249, 
       o_z_ts250, o_z_ts251, o_z_ts252, o_z_ts253, o_z_ts254, o_z_ts255, 
       o_z_ts256, o_z_ts257, o_z_ts258, o_z_ts259, o_z_ts260, o_z_ts261, 
       o_z_ts262, o_z_ts263, o_z_ts264, o_z_ts265, o_z_ts266, o_z_ts267, 
       o_z_ts268, o_z_ts269, o_z_ts270, o_z_ts271, o_z_ts272, o_z_ts273, 
       o_z_ts274, o_z_ts275, o_z_ts276, o_z_ts277, o_z_ts278, o_z_ts279, 
       o_z_ts280, o_z_ts281, o_z_ts282, o_z_ts283, o_z_ts284, o_z_ts285, 
       o_z_ts286, o_z_ts287, o_z_ts288, o_z_ts289, o_z_ts290, o_z_ts291, 
       o_z_ts292, o_z_ts293, o_z_ts294, o_z_ts295, o_z_ts296, o_z_ts297, 
       o_z_ts298, o_z_ts299, o_z_ts300, o_z_ts301, o_z_ts302, o_z_ts303, 
       o_z_ts304, o_z_ts305, o_z_ts306, o_z_ts307, o_z_ts308, o_z_ts309, 
       o_z_ts310, o_z_ts311, o_z_ts312, o_z_ts313, o_z_ts314, o_z_ts315, 
       o_z_ts316, o_z_ts317, o_z_ts318, o_z_ts319, o_z_ts320, o_z_ts321, 
       o_z_ts322, o_z_ts323, o_z_ts324, o_z_ts325, o_z_ts326, o_z_ts327, 
       o_z_ts328, o_z_ts329, o_z_ts330, o_z_ts331, o_z_ts332, o_z_ts333, 
       o_z_ts334, o_z_ts335, o_z_ts336, o_z_ts337, o_z_ts338, o_z_ts339, 
       o_z_ts340, o_z_ts341, o_z_ts342, o_z_ts343, o_z_ts344, o_z_ts345, 
       o_z_ts346, o_z_ts347, o_z_ts348, o_z_ts349, o_z_ts350, o_z_ts351, 
       o_z_ts352, o_z_ts353, o_z_ts354, o_z_ts355, o_z_ts356, o_z_ts357, 
       o_z_ts358, o_z_ts359, o_z_ts360, o_z_ts361, o_z_ts362, o_z_ts363, 
       o_z_ts364, o_z_ts365, o_z_ts366, o_z_ts367, o_z_ts368, o_z_ts369, 
       o_z_ts370, o_z_ts371, o_z_ts372, o_z_ts373, o_z_ts374, o_z_ts375, 
       o_z_ts376, o_z_ts377, o_z_ts378, o_z_ts379, o_z_ts380, o_z_ts381, 
       o_z_ts382, o_z_ts383, o_z_ts384, o_z_ts385, o_z_ts386, o_z_ts387, 
       o_z_ts388, o_z_ts389, o_z_ts390, o_z_ts391, o_z_ts392, o_z_ts393, 
       o_z_ts394, o_z_ts395, o_z_ts396, o_z_ts397, o_z_ts398, o_z_ts399, 
       o_z_ts400, o_z_ts401, o_z_ts402, o_z_ts403, o_z_ts404, o_z_ts405, 
       o_z_ts406, o_z_ts407, o_z_ts408, o_z_ts409, o_z_ts410, o_z_ts411, 
       o_z_ts412, o_z_ts413, o_z_ts414, o_z_ts415, o_z_ts416, o_z_ts417, 
       o_z_ts418, o_z_ts419, o_z_ts420, o_z_ts421, o_z_ts422, o_z_ts423, 
       o_z_ts424, o_z_ts425, o_z_ts426, o_z_ts427, o_z_ts428, o_z_ts429, 
       o_z_ts430, o_z_ts431, o_z_ts432, o_z_ts433, o_z_ts434, o_z_ts435, 
       o_z_ts436, o_z_ts437, o_z_ts438, o_z_ts439, o_z_ts440, o_z_ts441, 
       o_z_ts442, o_z_ts443, o_z_ts444, o_z_ts445, o_z_ts446, o_z_ts447, 
       o_z_ts448, o_z_ts449, o_z_ts450, o_z_ts451, o_z_ts452, o_z_ts453, 
       o_z_ts454, o_z_ts455, o_z_ts456, o_z_ts457, o_z_ts458, o_z_ts459, 
       o_z_ts460, to_DdrPhyCsrCmdTdrCaptureEn_ts1, 
       to_DdrPhyCsrCmdTdrShiftEn_ts1, to_DdrPhyCsrCmdTdrUpdateEn_ts1, 
       DdrPhyCsrCmdTdr_Tdo, to_DdrPhyCsrRdDataTdrCaptureEn_ts1, 
       to_DdrPhyCsrRdDataTdrShiftEn_ts1, to_DdrPhyCsrRdDataTdrUpdateEn_ts1, 
       DdrPhyCsrRdDataTdr_Tdo, to_WSI_ts1;
  wire [10:0] edt_scan_in_ts1;
  logic test_mode = 1'b0;

  // Clocks
  wire lpddr_clk;
  wire lpddr_pll_ref_clk;
  wire [1:0] lpddr_clks, lpddr_clkens;
  assign lpddr_clk = lpddr_clks[0];
  assign lpddr_pll_ref_clk = lpddr_clks[1];
  assign o_noc_clken = lpddr_clkens[0];

  // Resets
  wire  cfg_rst_n;
  wire  ctrl_rst_n;
  wire  phy_rst;
  wire [2:0] lpddr_rsts_n;
  assign cfg_rst_n = lpddr_rsts_n[0];
  assign ctrl_rst_n = lpddr_rsts_n[1];
  assign phy_rst = ~lpddr_rsts_n[2]; // Inverted as PHY resets are active high.

  // MEM PG control signals
  logic [1:0] ret;
  logic [1:0] pde;
  logic [1:0] prn;
  logic lpddr_ctrl_pde, lpddr_ctrl_ret, lpddr_ctrl_prn;
  logic lpddr_phy_pde, lpddr_phy_ret, lpddr_phy_prn;
  assign lpddr_ctrl_ret= ret[0];
  assign lpddr_ctrl_pde= pde[0];
  assign prn[0] = lpddr_ctrl_prn;
  assign lpddr_phy_ret = ret[1];
  assign lpddr_phy_pde = pde[1];
  assign prn[1] = lpddr_phy_prn;

  // Tie off unused AXI user signals
  assign o_lpddr_axi_m_ruser = '0;
  assign o_lpddr_axi_m_buser = '0;

  //-------------------------------
  // AO Reg
  //-------------------------------
  lpddr_csr_reg_pkg::lpddr_csr_reg2hw_t             reg2hw;
  lpddr_csr_reg_pkg::lpddr_csr_hw2reg_t             hw2reg;
  pctl_ao_csr_reg_pkg::apb_h2d_t ao_csr_apb_req;
  pctl_ao_csr_reg_pkg::apb_d2h_t ao_csr_apb_rsp;

  //-------------------------------
  // PCTL setup
  //-------------------------------
  // CLOCKS and RESET
  // LPDDR has two incoming clocks. The ao_clk that drives all the always-on logic in the wrapper, and the i_lpddr_clk that drives the SNPS IP through the pctlP
  // The pctl needs 2 dividers on i_lpddr_clk to split it in a normal lpddr-clk and a lpddr_pll_ref_clk clock.
  // The first is used to drive all subsys clocks related to interfaces, ctrl, and dfi.
  // The second is used to drive the PHYs internal pll_ref_clk and the pll_bypass_clk. In a normal use-case (i.e. as pll_ref_clk), the PHYs pll will multiply it with 4x to obtain a 3.2GHz clock
  // Further, the lpddr has 3 resets, cfg, ctrl and phy. When any of them is deasserted, only the lpddr_clk is stopped. The lpddr_pll_ref_clk is never stopped for a reset deassert to avoid losing pll lock.
  // The noc signals should be driven based on the 'normal' lpddr_clk, and the `cfg` reset.
  // FENCES
  // LPDDR needs to have its apb cfg interface up and running to start the IP configuration and link training.
  // During this period the AXI interface will not respond since the remainder of the CTRL is still in reset.
  // To keep the AXI still fenced during this time, the APB CFG interface and AXI interface each needs an individual fence
  // APB takes fence 0, AXI takes fence 1.
  pctl #(
    .N_FAST_CLKS (2),
    .N_RESETS (3),
    .N_MEM_PG(2),
    .N_FENCES(2),
    .N_THROTTLE_PINS(0),
    .CLKRST_MATRIX ({
      3'b000,     // clock index 1 -> lpddr_pll_ref_clk -> No reset de-assertion causes a gating of lpddr_pll_ref_clk, it should never be stopped.
      3'b111}),   // clock index 0 -> lpddr_clk ->Any reset de-assertion causes a gating of lpddr_clk
    .PLL_CLK_IS_I_CLK ({1'b0, 1'b0}),
    .NOC_RST_IDX (0),
    .AUTO_RESET_REMOVE (1'b0),
    .paddr_t (chip_syscfg_addr_t),
    .pdata_t (chip_apb_syscfg_data_t),
    .pstrb_t (chip_apb_syscfg_strb_t)
  ) u_pctl (
    .i_clk(i_ao_clk_ts1),
    .i_ao_rst_n(i_ao_rst_n),
    .i_global_rst_n(i_global_rst_n),
    .i_test_mode(sri_ctrl_all_test),
    .i_pll_clk({i_lpddr_clk_ts1, i_lpddr_clk_ts1}),
    .o_partition_clk(lpddr_clks),
    .o_partition_rst_n(lpddr_rsts_n),
    .o_ao_rst_sync_n(o_ao_rst_sync_n),
    .o_noc_async_idle_req(o_noc_async_idle_req),
    .i_noc_async_idle_ack(i_noc_async_idle_ack),
    .i_noc_async_idle_val(i_noc_async_idle_val),
    .o_noc_clken(lpddr_clkens),
    .o_noc_rst_n(o_noc_rst_n),
    .o_int_shutdown_req  (),// ASO-UNUSED_OUTPUT: LPDDR doesn't request shutdown
    .i_int_shutdown_ack  (1'b1),
    .o_ret(ret),
    .o_pde(pde),
    .i_prn(prn),
    .i_global_sync_async('0), // LPDDR does not have a global sync feature
    .o_global_sync(), // ASO-UNUSED_OUTPUT: LPDDR does not have a global sync feature
    .i_cfg_apb4_s_paddr(i_lpddr_syscfg_apb4_s_paddr),
    .i_cfg_apb4_s_pwdata(i_lpddr_syscfg_apb4_s_pwdata),
    .i_cfg_apb4_s_pwrite(i_lpddr_syscfg_apb4_s_pwrite),
    .i_cfg_apb4_s_psel(i_lpddr_syscfg_apb4_s_psel),
    .i_cfg_apb4_s_penable(i_lpddr_syscfg_apb4_s_penable),
    .i_cfg_apb4_s_pstrb(i_lpddr_syscfg_apb4_s_pstrb),
    .i_cfg_apb4_s_pprot(i_lpddr_syscfg_apb4_s_pprot),
    .o_cfg_apb4_s_pready(o_lpddr_syscfg_apb4_s_pready),
    .o_cfg_apb4_s_prdata(o_lpddr_syscfg_apb4_s_prdata),
    .o_cfg_apb4_s_pslverr(o_lpddr_syscfg_apb4_s_pslverr),
    .o_ao_csr_apb_req(ao_csr_apb_req),
    .i_ao_csr_apb_rsp(ao_csr_apb_rsp),
    .i_throttle(1'b0) // LPDDR does not support throttling.
  );

  wire pclk_clk_buf_out;
  wire pclk_apbrw_clk_buf_out;
  wire aclk_clk_buf_out;
  wire core_ddrc_core_clk_clk_buf_out;
  wire core_ddrc_core_clk_apbrw_clk_buf_out;
  wire dficlk_clk_buf_out;
  wire sbr_clk_clk_buf_out;
  wire pllbypclk_clk_buf_out;
  wire pllrefclk_clk_buf_out;

  // Clock buffer for clock definition of pclk
  axe_tcl_clk_buffer i_pclk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (pclk_clk_buf_out)
  );
  // Clock buffer for clock definition of pclk_apbrw
  axe_tcl_clk_buffer i_pclk_apbrw_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (pclk_apbrw_clk_buf_out)
  );
  // Clock buffer for clock definition of aclk
  axe_tcl_clk_buffer i_aclk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (aclk_clk_buf_out)
  );
  // Clock buffer for clock definition of core_ddrc_core_clk
  axe_tcl_clk_buffer i_core_ddrc_core_clk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (core_ddrc_core_clk_clk_buf_out)
  );
  // Clock buffer for clock definition of core_ddrc_core_clk_apbrw
  axe_tcl_clk_buffer i_core_ddrc_core_clk_apbrw_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (core_ddrc_core_clk_apbrw_clk_buf_out)
  );
  // Clock buffer for clock definition of dficlk
  axe_tcl_clk_buffer i_dficlk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (dficlk_clk_buf_out)
  );
  // Clock buffer for clock definition of sbr_clk
  axe_tcl_clk_buffer i_sbr_clk_clk_buf (
    .i_clk (lpddr_clk),
    .o_clk (sbr_clk_clk_buf_out)
  );
  // Clock buffer for clock definition of pllbypclk
  axe_tcl_clk_buffer i_pllbypclk_clk_buf (
    .i_clk (lpddr_pll_ref_clk),
    .o_clk (pllbypclk_clk_buf_out)
  );
  // Clock buffer for clock definition of pllrefclk
  axe_tcl_clk_buffer i_pllrefclk_clk_buf (
    .i_clk (lpddr_pll_ref_clk),
    .o_clk (pllrefclk_clk_buf_out)
  );


  //-------------------------------
  // AO CSR
  //-------------------------------
  lpddr_csr_reg_top u_lpddr_ao_csr (
    .clk_i    (i_ao_clk_ts1),
    .rst_ni   (o_ao_rst_sync_n),
    .apb_i    (ao_csr_apb_req),
    .apb_o    (ao_csr_apb_rsp),
    .reg2hw,
    .hw2reg,
    .devmode_i(1'b1)
  );

  //-------------------------------
  // SRAM implementation signals
  //-------------------------------
  logic  acsm_pde;
  logic  acsm_ret;
  logic  acsm_prn;
  logic  bc_pde;
  logic  bc_ret;
  logic  bc_prn;
  logic  dccm_pde;
  logic  dccm_ret;
  logic  dccm_prn;
  logic  gs_pde;
  logic  gs_ret;
  logic  gs_prn;
  logic  iccm_pde;
  logic  iccm_ret;
  logic  iccm_prn;
  logic  pie_pde;
  logic  pie_ret;
  logic  pie_prn;
  logic  wdata_pde;
  logic  wdata_ret;
  logic  wdata_prn;
  // CTRL memory control signal connections
  assign wdata_pde = lpddr_ctrl_pde;
  assign wdata_ret = lpddr_ctrl_ret;
  assign lpddr_ctrl_prn = wdata_prn;

  // PHY memory control signal connections
  // Power down enable daisy chain
  assign acsm_pde = lpddr_phy_pde;
  assign bc_pde = acsm_prn;
  assign dccm_pde = bc_prn;
  assign gs_pde = dccm_prn;
  assign iccm_pde = gs_prn;
  assign pie_pde = iccm_prn;
  assign lpddr_phy_prn = pie_prn;
  // Retention setting is broadcasted
  assign acsm_ret = lpddr_phy_ret;
  assign bc_ret = lpddr_phy_ret;
  assign dccm_ret = lpddr_phy_ret;
  assign gs_ret = lpddr_phy_ret;
  assign iccm_ret = lpddr_phy_ret;
  assign pie_ret = lpddr_phy_ret;

  // PLL debug signals, linked to csr with sync stage
  logic dwc_lpddr5xphy_pll_lock, dwc_lpddr5xphy_pll_lock_ao_synced;
  logic dwc_lpddr5xphy_pmu_busy, dwc_lpddr5xphy_pmu_busy_ao_synced;
  assign hw2reg.debug_phy_status.pll_lock.d = dwc_lpddr5xphy_pll_lock_ao_synced;
  assign hw2reg.debug_phy_status.pmu_busy.d = dwc_lpddr5xphy_pmu_busy_ao_synced;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) dwc_lpddr5xphy_pll_lock_sync_inst (
    .i_clk (i_ao_clk_ts1),
    .i_rst_n (i_ao_rst_n),
    .i_d (dwc_lpddr5xphy_pll_lock),
    .o_q (dwc_lpddr5xphy_pll_lock_ao_synced)
  );
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) dwc_lpddr5xphy_pmu_busy_sync_inst (
    .i_clk (i_ao_clk_ts1),
    .i_rst_n (i_ao_rst_n),
    .i_d (dwc_lpddr5xphy_pmu_busy),
    .o_q (dwc_lpddr5xphy_pmu_busy_ao_synced)
  );

  //-------------------------------
  // APB Spill lpddr_cfg_apb
  //-------------------------------
  logic [31:0] piped_lpddr_cfg_apb4_s_paddr;
  logic        piped_lpddr_cfg_apb4_s_penable;
  logic [2:0]  piped_lpddr_cfg_apb4_s_pprot;
  logic        piped_lpddr_cfg_apb4_s_psel;
  logic [3:0]  piped_lpddr_cfg_apb4_s_pstrb;
  logic [31:0] piped_lpddr_cfg_apb4_s_pwdata;
  logic        piped_lpddr_cfg_apb4_s_pwrite;
  logic [31:0] piped_lpddr_cfg_apb4_s_prdata;
  logic        piped_lpddr_cfg_apb4_s_pready;
  logic        piped_lpddr_cfg_apb4_s_pslverr;

  axe_apb_cut #(
    /// Width of the APB address (only used for typedef)
    .ApbAddrWidth(32),
    /// Width of the APB data (only used for typedef)
    .ApbDataWidth(32)
  ) lpddr_cfg_apb_cut_inst (
    /// Clock, positive edge triggered
    .i_clk              (lpddr_clk),
    /// Asynchronous reset, active low
    .i_rst_n            (cfg_rst_n),
    /////////////////
    // Subordinate //
    /////////////////
    .i_apb_s_paddr      (i_lpddr_cfg_apb4_s_paddr),
    .i_apb_s_pwdata     (i_lpddr_cfg_apb4_s_pwdata),
    .i_apb_s_pwrite     (i_lpddr_cfg_apb4_s_pwrite),
    .i_apb_s_psel       (i_lpddr_cfg_apb4_s_psel),
    .i_apb_s_penable    (i_lpddr_cfg_apb4_s_penable),
    .i_apb_s_pstrb      (i_lpddr_cfg_apb4_s_pstrb),
    .i_apb_s_pprot      (i_lpddr_cfg_apb4_s_pprot),
    .o_apb_s_pready     (o_lpddr_cfg_apb4_s_pready),
    .o_apb_s_prdata     (o_lpddr_cfg_apb4_s_prdata),
    .o_apb_s_pslverr    (o_lpddr_cfg_apb4_s_pslverr),
    /////////////
    // Manager //
    /////////////
    .o_apb_m_paddr      (piped_lpddr_cfg_apb4_s_paddr),
    .o_apb_m_pwdata     (piped_lpddr_cfg_apb4_s_pwdata),
    .o_apb_m_pwrite     (piped_lpddr_cfg_apb4_s_pwrite),
    .o_apb_m_psel       (piped_lpddr_cfg_apb4_s_psel),
    .o_apb_m_penable    (piped_lpddr_cfg_apb4_s_penable),
    .o_apb_m_pstrb      (piped_lpddr_cfg_apb4_s_pstrb),
    .o_apb_m_pprot      (piped_lpddr_cfg_apb4_s_pprot),
    .i_apb_m_pready     (piped_lpddr_cfg_apb4_s_pready),
    .i_apb_m_prdata     (piped_lpddr_cfg_apb4_s_prdata),
    .i_apb_m_pslverr    (piped_lpddr_cfg_apb4_s_pslverr)
  );

  //-------------------------------
  // AXI SPILL lpddr_axi
  //-------------------------------
  logic [7:0] i_lpddr_axi_m_subip_awid   ;
  logic [32:0] i_lpddr_axi_m_subip_awaddr ;
  logic [7:0] i_lpddr_axi_m_subip_awlen  ;
  logic [2:0] i_lpddr_axi_m_subip_awsize ;
  logic [1:0] i_lpddr_axi_m_subip_awburst;
  logic i_lpddr_axi_m_subip_awlock ;
  logic [3:0] i_lpddr_axi_m_subip_awcache;
  logic [2:0] i_lpddr_axi_m_subip_awprot ;
  logic [3:0] i_lpddr_axi_m_subip_awqos  ;
  logic [3:0] i_lpddr_axi_m_subip_awregion;
  logic i_lpddr_axi_m_subip_awvalid;
  logic [255:0] i_lpddr_axi_m_subip_wdata  ;
  logic [31:0] i_lpddr_axi_m_subip_wstrb  ;
  logic i_lpddr_axi_m_subip_wlast  ;
  logic i_lpddr_axi_m_subip_wvalid ;
  logic i_lpddr_axi_m_subip_bready ;
  logic [7:0] i_lpddr_axi_m_subip_arid   ;
  logic [32:0] i_lpddr_axi_m_subip_araddr ;
  logic [7:0] i_lpddr_axi_m_subip_arlen  ;
  logic [2:0] i_lpddr_axi_m_subip_arsize ;
  logic [1:0] i_lpddr_axi_m_subip_arburst;
  logic i_lpddr_axi_m_subip_arlock ;
  logic [3:0] i_lpddr_axi_m_subip_arcache;
  logic [2:0] i_lpddr_axi_m_subip_arprot ;
  logic [3:0] i_lpddr_axi_m_subip_arqos  ;
  logic [3:0] i_lpddr_axi_m_subip_arregion;
  logic i_lpddr_axi_m_subip_arvalid;
  logic i_lpddr_axi_m_subip_rready ;
  logic o_lpddr_axi_m_subip_awready;
  logic o_lpddr_axi_m_subip_wready ;
  logic [7:0] o_lpddr_axi_m_subip_bid    ;
  logic [1:0] o_lpddr_axi_m_subip_bresp  ;
  logic o_lpddr_axi_m_subip_bvalid ;
  logic o_lpddr_axi_m_subip_arready;
  logic [7:0] o_lpddr_axi_m_subip_rid    ;
  logic [255:0] o_lpddr_axi_m_subip_rdata  ;
  logic [1:0] o_lpddr_axi_m_subip_rresp  ;
  logic o_lpddr_axi_m_subip_rlast  ;
  logic o_lpddr_axi_m_subip_rvalid ;

  axe_axi_multicut_flat #(
    .AxiAddrWidth (33),
    .AxiIdWidth (8),
    .AxiDataWidth (256),
    .NumCuts(1)
  ) o_lpddr_axi_m_spill_flat (
    .i_clk(lpddr_clk),
    .i_rst_n(ctrl_rst_n),
    .i_axi_s_aw_id(i_lpddr_axi_m_awid),
    .i_axi_s_aw_addr(i_lpddr_axi_m_awaddr[32:0]),  // LPDDR is only 33b, NoC internally uses 33b as well, but top-level integration pads to 40b using 0-ties
    .i_axi_s_aw_len(i_lpddr_axi_m_awlen),
    .i_axi_s_aw_size(i_lpddr_axi_m_awsize),
    .i_axi_s_aw_burst(i_lpddr_axi_m_awburst),
    .i_axi_s_aw_lock(i_lpddr_axi_m_awlock),
    .i_axi_s_aw_cache(i_lpddr_axi_m_awcache),
    .i_axi_s_aw_prot(i_lpddr_axi_m_awprot),
    .i_axi_s_aw_qos(i_lpddr_axi_m_awqos),
    .i_axi_s_aw_region(i_lpddr_axi_m_awregion),
    .i_axi_s_aw_user('0),
    .i_axi_s_aw_valid(i_lpddr_axi_m_awvalid),
    .o_axi_s_aw_ready(o_lpddr_axi_m_awready),
    .i_axi_s_w_data(i_lpddr_axi_m_wdata),
    .i_axi_s_w_strb(i_lpddr_axi_m_wstrb),
    .i_axi_s_w_last(i_lpddr_axi_m_wlast),
    .i_axi_s_w_user('0),
    .i_axi_s_w_valid(i_lpddr_axi_m_wvalid),
    .o_axi_s_w_ready(o_lpddr_axi_m_wready),
    .o_axi_s_b_id(o_lpddr_axi_m_bid),
    .o_axi_s_b_resp(o_lpddr_axi_m_bresp),
    .o_axi_s_b_user(),
    .o_axi_s_b_valid(o_lpddr_axi_m_bvalid),
    .i_axi_s_b_ready(i_lpddr_axi_m_bready),
    .i_axi_s_ar_id(i_lpddr_axi_m_arid),
    .i_axi_s_ar_addr(i_lpddr_axi_m_araddr[32:0]), // LPDDR is only 33b, NoC internally uses 33b as well, but top-level integration pads to 40b using 0-ties
    .i_axi_s_ar_len(i_lpddr_axi_m_arlen),
    .i_axi_s_ar_size(i_lpddr_axi_m_arsize),
    .i_axi_s_ar_burst(i_lpddr_axi_m_arburst),
    .i_axi_s_ar_lock(i_lpddr_axi_m_arlock),
    .i_axi_s_ar_cache(i_lpddr_axi_m_arcache),
    .i_axi_s_ar_prot(i_lpddr_axi_m_arprot),
    .i_axi_s_ar_qos(i_lpddr_axi_m_arqos),
    .i_axi_s_ar_region(i_lpddr_axi_m_arregion),
    .i_axi_s_ar_user('0),
    .i_axi_s_ar_valid(i_lpddr_axi_m_arvalid),
    .o_axi_s_ar_ready(o_lpddr_axi_m_arready),
    .o_axi_s_r_id(o_lpddr_axi_m_rid),
    .o_axi_s_r_data(o_lpddr_axi_m_rdata),
    .o_axi_s_r_resp(o_lpddr_axi_m_rresp),
    .o_axi_s_r_last(o_lpddr_axi_m_rlast),
    .o_axi_s_r_user(),
    .o_axi_s_r_valid(o_lpddr_axi_m_rvalid),
    .i_axi_s_r_ready(i_lpddr_axi_m_rready),
    .o_axi_m_aw_id(i_lpddr_axi_m_subip_awid),
    .o_axi_m_aw_addr(i_lpddr_axi_m_subip_awaddr),
    .o_axi_m_aw_len(i_lpddr_axi_m_subip_awlen),
    .o_axi_m_aw_size(i_lpddr_axi_m_subip_awsize),
    .o_axi_m_aw_burst(i_lpddr_axi_m_subip_awburst),
    .o_axi_m_aw_lock(i_lpddr_axi_m_subip_awlock),
    .o_axi_m_aw_cache(i_lpddr_axi_m_subip_awcache),
    .o_axi_m_aw_prot(i_lpddr_axi_m_subip_awprot),
    .o_axi_m_aw_qos(i_lpddr_axi_m_subip_awqos),
    .o_axi_m_aw_region(i_lpddr_axi_m_subip_awregion),
    .o_axi_m_aw_valid(i_lpddr_axi_m_subip_awvalid),
    .o_axi_m_aw_user(),
    .i_axi_m_aw_ready(o_lpddr_axi_m_subip_awready),
    .o_axi_m_w_data(i_lpddr_axi_m_subip_wdata),
    .o_axi_m_w_strb(i_lpddr_axi_m_subip_wstrb),
    .o_axi_m_w_last(i_lpddr_axi_m_subip_wlast),
    .o_axi_m_w_user(),
    .o_axi_m_w_valid(i_lpddr_axi_m_subip_wvalid),
    .i_axi_m_w_ready(o_lpddr_axi_m_subip_wready),
    .i_axi_m_b_id(o_lpddr_axi_m_subip_bid),
    .i_axi_m_b_resp(o_lpddr_axi_m_subip_bresp),
    .i_axi_m_b_user('0),
    .i_axi_m_b_valid(o_lpddr_axi_m_subip_bvalid),
    .o_axi_m_b_ready(i_lpddr_axi_m_subip_bready),
    .o_axi_m_ar_id(i_lpddr_axi_m_subip_arid),
    .o_axi_m_ar_addr(i_lpddr_axi_m_subip_araddr),
    .o_axi_m_ar_len(i_lpddr_axi_m_subip_arlen),
    .o_axi_m_ar_size(i_lpddr_axi_m_subip_arsize),
    .o_axi_m_ar_burst(i_lpddr_axi_m_subip_arburst),
    .o_axi_m_ar_lock(i_lpddr_axi_m_subip_arlock),
    .o_axi_m_ar_cache(i_lpddr_axi_m_subip_arcache),
    .o_axi_m_ar_prot(i_lpddr_axi_m_subip_arprot),
    .o_axi_m_ar_qos(i_lpddr_axi_m_subip_arqos),
    .o_axi_m_ar_region(i_lpddr_axi_m_subip_arregion),
    .o_axi_m_ar_user(),
    .o_axi_m_ar_valid(i_lpddr_axi_m_subip_arvalid),
    .i_axi_m_ar_ready(o_lpddr_axi_m_subip_arready),
    .i_axi_m_r_id(o_lpddr_axi_m_subip_rid),
    .i_axi_m_r_data(o_lpddr_axi_m_subip_rdata),
    .i_axi_m_r_resp(o_lpddr_axi_m_subip_rresp),
    .i_axi_m_r_last(o_lpddr_axi_m_subip_rlast),
    .i_axi_m_r_user('0),
    .i_axi_m_r_valid(o_lpddr_axi_m_subip_rvalid),
    .o_axi_m_r_ready(i_lpddr_axi_m_subip_rready)
  );

  //-------------------------------
  // AXI low power interface
  //-------------------------------
  // Tied-off, CSR control only over Low power modes.
  logic csysreq, cactive, csysack;
  assign csysreq = '1;

  //-------------------------------
  // Additional AXI interface signal (non-std). given csr control.
  //-------------------------------
  logic  arurgent_ao_sync, arurgent;
  logic  awurgent_ao_sync, awurgent;
  assign arurgent_ao_sync = reg2hw.config_lpddr.arurgent.q;
  assign awurgent_ao_sync = reg2hw.config_lpddr.awurgent.q;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) arurgent_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (cfg_rst_n),
    .i_d (arurgent_ao_sync),
    .o_q (arurgent)
  );
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) awurgent_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (cfg_rst_n),
    .i_d (awurgent_ao_sync),
    .o_q (awurgent)
  );

  // Flags about evens in the read and write address queues. Connected to csrs counter for debug, otherwise not used
  logic raq_split;
  logic raqb_pop;
  logic raqb_push;
  logic raqr_pop;
  logic raqr_push;
  logic waq_pop;
  logic waq_push;
  logic waq_split;

  // ADDRESS FIFO position indicators, connected to csrs for debug, otherwise not used.
  logic [5:0] raqb_wcount, raqb_wcount_ao_sync;
  logic [5:0] raqr_wcount, raqr_wcount_ao_sync;
  logic [5:0] waq_wcount, waq_wcount_ao_sync;
  assign hw2reg.debug_address_fifos_lpddr.raqb_wcount.d = raqb_wcount_ao_sync;
  assign hw2reg.debug_address_fifos_lpddr.raqr_wcount.d = raqr_wcount_ao_sync;
  assign hw2reg.debug_address_fifos_lpddr.waq_wcount.d = waq_wcount_ao_sync;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [5:0])
  ) raqb_wcount_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (raqb_wcount),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (raqb_wcount_ao_sync),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [5:0])
  ) raqr_wcount_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (raqr_wcount),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (raqr_wcount_ao_sync),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [5:0])
  ) waq_wcount_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (waq_wcount),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (waq_wcount_ao_sync),
    .o_dst_update ()
  );

  //--------------------------------
  // DDRC Low power interface
  //--------------------------------
  // DDRC Hard-ware lower power and fast frequency change interface is not used, tied-off here.
  logic csysreq_ddrc, cactive_ddrc, csysack_ddrc;
  assign csysreq_ddrc = '1;
  logic csysdiscamdrain_ddrc;
  assign csysdiscamdrain_ddrc = '0;
  logic [4:0] csysfrequency_ddrc;
  assign csysfrequency_ddrc = '0;
  logic csysfsp_ddrc;
  assign csysfsp_ddrc = '0;
  logic csysmode_ddrc;
  assign csysmode_ddrc = '0;

  //-----------------
  // APB security
  //-----------------
  // 7.3.1.2 PPROT_PIN Configuration and Purpose
  // -  Typically tied off to a particular value, sometimes fuse programmed, or in some highly secure environments this is randomized by a different security engine.
  // -  The PHY only responds to APB requests where PPROT_APB matches the value of PPROT_PIN.
  // This functionality prevents unauthorized accesses to the registers. A hardware configurable port for comparison against the value on PPROT during activity PPROT_PIN[2:0] is a static value provided by the SOC.
  logic [2:0] pprot_pin;
  // Solution used in Omega, just use apb pprot signal on pprot pin as well.
  assign pprot_pin = piped_lpddr_cfg_apb4_s_pprot;

  //-----------------
  // ECC related signals
  //------------------
  logic dis_regs_ecc_syndrome, dis_regs_ecc_syndrome_ao_sync;
  assign dis_regs_ecc_syndrome_ao_sync = reg2hw.config_lpddr.dis_regs_ecc_syndrome.q;
  axe_tcl_seq_sync #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .ResetValue(0)
  ) dis_regs_ecc_syndrome_sync_inst (
    .i_clk (lpddr_clk),
    .i_rst_n (ctrl_rst_n),
    .i_d (dis_regs_ecc_syndrome_ao_sync),
    .o_q (dis_regs_ecc_syndrome)
  );

  //-----------------
  // CAM credit counters
  //-----------------
  logic [6:0] hpr_credit_cnt, hpr_credit_cnt_ao_synced;
  logic [6:0] lpr_credit_cnt, lpr_credit_cnt_ao_synced;
  logic [6:0] wr_credit_cnt, wr_credit_cnt_ao_synced;
  logic [6:0] wrecc_credit_cnt, wrecc_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.hpr_credit_cnt.d = hpr_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.lpr_credit_cnt.d = lpr_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.wr_credit_cnt.d = wr_credit_cnt_ao_synced;
  assign hw2reg.debug_cam_credit_count_lpddr.wrecc_credit_cnt.d = wrecc_credit_cnt_ao_synced;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) hpr_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (hpr_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (hpr_credit_cnt_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) lpr_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (lpr_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (lpr_credit_cnt_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) wr_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (wr_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (wr_credit_cnt_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [6:0])
  ) wrecc_credit_cnt_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en ('1),
    .i_src_data (wrecc_credit_cnt),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (wrecc_credit_cnt_ao_synced),
    .o_dst_update ()
  );

  //-------------------
  // Mode register read
  //-----------------
  logic [31:0] hif_mrr_data, hif_mrr_data_ao_synced;
  logic hif_mrr_data_valid;
  assign hw2reg.hif_mode_read.d = hif_mrr_data_ao_synced;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [31:0])
  ) hif_mrr_data_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (hif_mrr_data_valid),
    .i_src_data (hif_mrr_data),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (hif_mrr_data_ao_synced),
    .o_dst_update ()
  );

  //-----------------
  // Performance counters
  //-----------------
  logic  perf_dfi_rd_data_cycles;
  logic  perf_dfi_wr_data_cycles;
  logic  perf_hif_hi_pri_rd;
  logic  perf_hif_rd;
  logic  perf_hif_rd_or_wr;
  logic  perf_hif_rmw;
  logic  perf_hif_wr;
  logic  perf_hpr_req_with_nocredit;
  logic  perf_hpr_xact_when_critical;
  logic  perf_ie_blk_hazard;
  logic  perf_lpr_req_with_nocredit;
  logic  perf_lpr_xact_when_critical;
  logic  perf_op_is_activate;
  logic  perf_op_is_cas;
  logic  perf_op_is_cas_wck_sus;
  logic  perf_op_is_cas_ws;
  logic  perf_op_is_cas_ws_off;
  logic  perf_op_is_crit_ref;
  logic  perf_op_is_dqsosc_mpc;
  logic  perf_op_is_dqsosc_mrr;
  logic  perf_op_is_enter_dsm;
  logic  perf_op_is_load_mode;
  logic  perf_op_is_mwr;
  logic  perf_op_is_precharge;
  logic  perf_op_is_rd;
  logic  perf_op_is_rd_activate;
  logic  perf_op_is_rd_or_wr;
  logic  perf_op_is_refresh;
  logic  perf_op_is_rfm;
  logic  perf_op_is_spec_ref;
  logic  perf_op_is_tcr_mrr;
  logic  perf_op_is_wr;
  logic  perf_op_is_zqlatch;
  logic  perf_op_is_zqstart;
  logic  perf_precharge_for_other;
  logic  perf_precharge_for_rdwr;
  logic  perf_raw_hazard;
  logic  perf_rdwr_transitions;
  logic  perf_visible_window_limit_reached_rd;
  logic  perf_visible_window_limit_reached_wr;
  logic  perf_war_hazard;
  logic  perf_waw_hazard;
  logic  perf_wr_xact_when_critical;
  logic  perf_write_combine;
  logic  perf_write_combine_noecc;
  logic  perf_write_combine_wrecc;
  // Multi-bit counter increment signals per rank split in separate signals.
  logic perf_selfref_mode_rank_0;
  logic perf_selfref_mode_rank_1;
  logic perf_op_is_enter_powerdown_rank_0;
  logic perf_op_is_enter_powerdown_rank_1;
  logic perf_op_is_enter_selfref_rank_0;
  logic perf_op_is_enter_selfref_rank_1;

  // Debug signals, no counter signals
  logic       perf_rank, perf_rank_ao_synced;
  logic [2:0] perf_bank, perf_bank_ao_synced;
  logic [1:0] perf_bg, perf_bg_ao_synced;
  logic debug_cam_valid;
  assign debug_cam_valid = perf_op_is_rd_or_wr | perf_op_is_rd | perf_op_is_wr;
  assign hw2reg.debug_cam_schedule_lpddr.perf_rank.d = perf_rank_ao_synced;
  assign hw2reg.debug_cam_schedule_lpddr.perf_bank.d = perf_bank_ao_synced;
  assign hw2reg.debug_cam_schedule_lpddr.perf_bank_group.d = perf_bg_ao_synced;
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic)
  ) perf_rank_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (debug_cam_valid),
    .i_src_data (perf_rank),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (perf_rank_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [2:0])
  ) perf_bank_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (debug_cam_valid),
    .i_src_data (perf_bank),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (perf_bank_ao_synced),
    .o_dst_update ()
  );
  axe_ccl_cdc_bus #(
    .SyncStages(LPDDR_SYNC_STAGES),
    .data_t(logic [1:0])
  ) perf_bg_sync_inst (
    .i_src_clk (lpddr_clk),
    .i_src_rst_n (ctrl_rst_n),
    .i_src_en (debug_cam_valid),
    .i_src_data (perf_bg),
    .o_src_busy (),
    .i_dst_clk (i_ao_clk_ts1),
    .i_dst_rst_n (i_ao_rst_n),
    .o_dst_data (perf_bg_ao_synced),
    .o_dst_update ()
  );

  // Digital test output signal (PHY signals for debug)
  logic [1:0] dwc_lpddr5xphy_dto;

  // PHY interrupts come out of a single bundle that is active low.
  // See section 7.5 of PUB databook
  // Assign to individual interrupt signals here, and invert to active high for PLIC handling
  // Not all 16 bits are actually used. Mapping taken from PhyInterruptStatus register in the PUB databook
  logic [15:0] phyint_n;
  assign o_phy_pie_prog_err_intr = ~phyint_n[12];
  assign o_phy_ecc_err_intr = ~phyint_n[11];
  assign o_phy_rdfptrchk_err_intr = ~phyint_n[10];
  assign o_phy_pie_parity_err_intr = ~phyint_n[9];
  assign o_phy_acsm_parity_err_intr = ~phyint_n[8];
  assign o_phy_trng_fail_intr = ~phyint_n[2];
  assign o_phy_init_cmplt_intr = ~phyint_n[1];
  assign o_phy_trng_cmplt_intr = ~phyint_n[0];

  // Observability connections
  assign o_lpddr_obs[0] = dwc_lpddr5xphy_pll_lock;
  assign o_lpddr_obs[1] = dwc_lpddr5xphy_pmu_busy;
  assign o_lpddr_obs[2] = o_phy_pie_prog_err_intr;
  assign o_lpddr_obs[3] = o_phy_rdfptrchk_err_intr;
  assign o_lpddr_obs[4] = o_phy_trng_fail_intr;
  assign o_lpddr_obs[5] = o_phy_init_cmplt_intr;
  assign o_lpddr_obs[6] = o_phy_trng_cmplt_intr;
  assign o_lpddr_obs[8:7] = dwc_lpddr5xphy_dto;
  assign o_lpddr_obs[9] = o_ctrl_sbr_done_intr;
  assign o_lpddr_obs[10] = o_ctrl_derate_temp_limit_intr;
  assign o_lpddr_obs[11] = o_ctrl_ecc_ap_err_intr;
  assign o_lpddr_obs[12] = o_ctrl_ecc_corrected_err_intr;
  assign o_lpddr_obs[13] = o_ctrl_ecc_uncorrected_err_intr;
  assign o_lpddr_obs[14] = o_ctrl_rd_linkecc_corr_err_intr;
  assign o_lpddr_obs[15] = o_ctrl_rd_linkecc_uncorr_err_intr;


  //-------------------------------
  // JTAG TDR integration of snps TDR
  //-------------------------------

wire to_DdrPhyCsrCmdTdrCaptureEn,to_DdrPhyCsrCmdTdrShiftEn,to_DdrPhyCsrCmdTdrUpdateEn;
wire to_DdrPhyCsrRdDataTdrCaptureEn,to_DdrPhyCsrRdDataTdrShiftEn,to_DdrPhyCsrRdDataTdrUpdateEn;
wire to_WSI,from_DdrPhyCsrCmdTdr_Tdo,from_DdrPhyCsrRdDataTdr_Tdo;

dwc_ddrphy_jtag_dfttdrs_cmd dwc_ddrphy_jtag_dfttdrs_Cmd_inst (
        .ijtag_sel            (lpddr_p_rtl2_tessent_scanmux_tdr_inst_to_select0),
        .tck               (tck),
        .scan_in           (lpddr_p_rtl2_tessent_tdr_phy_inst_so),
        .scan_out          (dwc_ddrphy_jtag_dfttdrs_Cmd_inst_so),
        .reset             (test_logic_reset),
        .shift_en          (shift_dr_en),
        .capture_en        (capture_dr_en),
        .update_en         (update_dr_en),
        .to_DdrPhyCsrCmdTdrCaptureEn(to_DdrPhyCsrCmdTdrCaptureEn_ts1),
        .to_DdrPhyCsrCmdTdrShiftEn(to_DdrPhyCsrCmdTdrShiftEn_ts1),
        .to_DdrPhyCsrCmdTdrUpdateEn(to_DdrPhyCsrCmdTdrUpdateEn_ts1),
        .to_WSI(to_WSI_ts1),
	.from_DdrPhyCsrCmdTdr_Tdo(DdrPhyCsrCmdTdr_Tdo)
);

dwc_ddrphy_jtag_dfttdrs_RdData dwc_ddrphy_jtag_dfttdrs_RdData_inst (
        .ijtag_sel         (lpddr_p_rtl2_tessent_scanmux_tdr_inst_to_select1),
        .tck               (tck),
        .scan_in           (lpddr_p_rtl2_tessent_tdr_phy_inst_so),
        .scan_out          (dwc_ddrphy_jtag_dfttdrs_RdData_inst_so),
        .reset             (test_logic_reset),
        .shift_en          (shift_dr_en),
        .capture_en        (capture_dr_en),
        .update_en         (update_dr_en),
        .to_DdrPhyCsrRdDataTdrCaptureEn(to_DdrPhyCsrRdDataTdrCaptureEn_ts1),
        .to_DdrPhyCsrRdDataTdrShiftEn(to_DdrPhyCsrRdDataTdrShiftEn_ts1),
        .to_DdrPhyCsrRdDataTdrUpdateEn(to_DdrPhyCsrRdDataTdrUpdateEn_ts1),
        .to_WSI(to_WSI),
        .from_DdrPhyCsrRdDataTdr_Tdo(DdrPhyCsrRdDataTdr_Tdo)
);


  //-------------------------------
  // Wrapped module instantiation
  //-------------------------------
  lpddr_p_lpddr_subsys_wrapper u_lpddr_subsys_wrapper (
    // Clocks
    .i_pclk (pclk_clk_buf_out),
    .i_pclk_apbrw (pclk_apbrw_clk_buf_out),
    .i_aclk (aclk_clk_buf_out),
    .i_core_ddrc_core_clk (core_ddrc_core_clk_clk_buf_out),
    .i_core_ddrc_core_clk_apbrw (core_ddrc_core_clk_apbrw_clk_buf_out),
    .i_dficlk (dficlk_clk_buf_out),
    .i_sbr_clk (sbr_clk_clk_buf_out),
    .i_pllbypclk (pllbypclk_clk_buf_out),
    .i_pllrefclk (pllrefclk_clk_buf_out),
    // Resets
    .i_cfg_rst_n(cfg_rst_n),
    .i_ctrl_rst_n(ctrl_rst_n),
    .i_phy_rst(phy_rst),
    // DDRC low power interface
    .i_csysreq_ddrc(csysreq_ddrc),
    .i_csysdiscamdrain_ddrc(csysdiscamdrain_ddrc),
    .i_csysfrequency_ddrc(csysfrequency_ddrc),
    .i_csysfsp_ddrc(csysfsp_ddrc),
    .i_csysmode_ddrc(csysmode_ddrc),
    .o_cactive_ddrc(cactive_ddrc),
    .o_csysack_ddrc(csysack_ddrc),
    // AXI low power interface
    .i_csysreq(csysreq),
    .o_cactive(cactive),
    .o_csysack(csysack),
    // AXI interface
    .i_lpddr_axi_m_araddr(i_lpddr_axi_m_subip_araddr),
    .i_lpddr_axi_m_arburst(i_lpddr_axi_m_subip_arburst),
    .i_lpddr_axi_m_arcache(i_lpddr_axi_m_subip_arcache),
    .i_lpddr_axi_m_arid(i_lpddr_axi_m_subip_arid),
    .i_lpddr_axi_m_arlen(i_lpddr_axi_m_subip_arlen),
    .i_lpddr_axi_m_arlock(i_lpddr_axi_m_subip_arlock),
    .i_lpddr_axi_m_arprot(i_lpddr_axi_m_subip_arprot),
    .i_lpddr_axi_m_arqos(i_lpddr_axi_m_subip_arqos),
    .i_lpddr_axi_m_arregion(i_lpddr_axi_m_subip_arregion),
    .i_lpddr_axi_m_arsize(i_lpddr_axi_m_subip_arsize),
    .i_lpddr_axi_m_arvalid(i_lpddr_axi_m_subip_arvalid),
    .i_lpddr_axi_m_rready(i_lpddr_axi_m_subip_rready),
    .i_lpddr_axi_m_awaddr(i_lpddr_axi_m_subip_awaddr),
    .i_lpddr_axi_m_awburst(i_lpddr_axi_m_subip_awburst),
    .i_lpddr_axi_m_awcache(i_lpddr_axi_m_subip_awcache),
    .i_lpddr_axi_m_awid(i_lpddr_axi_m_subip_awid),
    .i_lpddr_axi_m_awlen(i_lpddr_axi_m_subip_awlen),
    .i_lpddr_axi_m_awlock(i_lpddr_axi_m_subip_awlock),
    .i_lpddr_axi_m_awprot(i_lpddr_axi_m_subip_awprot),
    .i_lpddr_axi_m_awqos(i_lpddr_axi_m_subip_awqos),
    .i_lpddr_axi_m_awregion(i_lpddr_axi_m_subip_awregion),
    .i_lpddr_axi_m_awsize(i_lpddr_axi_m_subip_awsize),
    .i_lpddr_axi_m_awvalid(i_lpddr_axi_m_subip_awvalid),
    .i_lpddr_axi_m_wdata(i_lpddr_axi_m_subip_wdata),
    .i_lpddr_axi_m_wlast(i_lpddr_axi_m_subip_wlast),
    .i_lpddr_axi_m_wstrb(i_lpddr_axi_m_subip_wstrb),
    .i_lpddr_axi_m_wvalid(i_lpddr_axi_m_subip_wvalid),
    .i_lpddr_axi_m_bready(i_lpddr_axi_m_subip_bready),
    .o_lpddr_axi_m_arready(o_lpddr_axi_m_subip_arready),
    .o_lpddr_axi_m_rdata(o_lpddr_axi_m_subip_rdata),
    .o_lpddr_axi_m_rid(o_lpddr_axi_m_subip_rid),
    .o_lpddr_axi_m_rlast(o_lpddr_axi_m_subip_rlast),
    .o_lpddr_axi_m_rresp(o_lpddr_axi_m_subip_rresp),
    .o_lpddr_axi_m_rvalid(o_lpddr_axi_m_subip_rvalid),
    .o_lpddr_axi_m_awready(o_lpddr_axi_m_subip_awready),
    .o_lpddr_axi_m_wready(o_lpddr_axi_m_subip_wready),
    .o_lpddr_axi_m_bid(o_lpddr_axi_m_subip_bid),
    .o_lpddr_axi_m_bresp(o_lpddr_axi_m_subip_bresp),
    .o_lpddr_axi_m_bvalid(o_lpddr_axi_m_subip_bvalid),
    .i_awurgent(awurgent),
    .i_arurgentb(arurgent),  // There is no difference in this signal between read or blue queue
    .i_arurgentr(arurgent),  // in both cases the rd_port_urgent_en register is set (see ref manual)
    .o_raq_split(raq_split),
    .o_raqb_pop(raqb_pop),
    .o_raqb_push(raqb_push),
    .o_raqb_wcount(raqb_wcount),
    .o_raqr_pop(raqr_pop),
    .o_raqr_push(raqr_push),
    .o_raqr_wcount(raqr_wcount),
    .o_waq_pop(waq_pop),
    .o_waq_push(waq_push),
    .o_waq_split(waq_split),
    .o_waq_wcount(waq_wcount),
    // APB interface
    .i_lpddr_cfg_apb_m_pprot(piped_lpddr_cfg_apb4_s_pprot),
    .i_lpddr_cfg_apb_m_paddr(piped_lpddr_cfg_apb4_s_paddr),
    .i_lpddr_cfg_apb_m_penable(piped_lpddr_cfg_apb4_s_penable),
    .i_lpddr_cfg_apb_m_psel(piped_lpddr_cfg_apb4_s_psel),
    .i_lpddr_cfg_apb_m_pstrb(piped_lpddr_cfg_apb4_s_pstrb),
    .i_lpddr_cfg_apb_m_pwdata(piped_lpddr_cfg_apb4_s_pwdata),
    .i_lpddr_cfg_apb_m_pwrite(piped_lpddr_cfg_apb4_s_pwrite),
    .o_lpddr_cfg_apb_m_prdata(piped_lpddr_cfg_apb4_s_prdata),
    .o_lpddr_cfg_apb_m_pready(piped_lpddr_cfg_apb4_s_pready),
    .o_lpddr_cfg_apb_m_pslverr(piped_lpddr_cfg_apb4_s_pslverr),
    .i_pprot_pin(pprot_pin),
    // ECC security signal
    .i_dis_regs_ecc_syndrome(dis_regs_ecc_syndrome),
    // Credit counters
    .o_hpr_credit_cnt(hpr_credit_cnt),
    .o_lpr_credit_cnt(lpr_credit_cnt),
    .o_wr_credit_cnt(wr_credit_cnt),
    .o_wrecc_credit_cnt(wrecc_credit_cnt),
    // CTRL interupts
    .o_sbr_done_intr(o_ctrl_sbr_done_intr),
    .o_derate_temp_limit_intr(o_ctrl_derate_temp_limit_intr),
    .o_ecc_ap_err_intr(o_ctrl_ecc_ap_err_intr),
    .o_ecc_corrected_err_intr(o_ctrl_ecc_corrected_err_intr),
    .o_ecc_uncorrected_err_intr(o_ctrl_ecc_uncorrected_err_intr),
    .o_rd_linkecc_corr_err_intr(o_ctrl_rd_linkecc_corr_err_intr),
    .o_rd_linkecc_uncorr_err_intr(o_ctrl_rd_linkecc_uncorr_err_intr),
    // PHY interrupts
    .o_phyint_n(phyint_n),
    // PHY PLL status
    .o_dwc_lpddr5xphy_pll_lock(dwc_lpddr5xphy_pll_lock),
    .o_dwc_lpddr5xphy_pmu_busy(dwc_lpddr5xphy_pmu_busy),
    // Mode register read output
    .o_hif_mrr_data(hif_mrr_data),
    .o_hif_mrr_data_valid(hif_mrr_data_valid),
    // Perf counter increment flags
    .o_perf_bank(perf_bank),
    .o_perf_bg(perf_bg),
    .o_perf_dfi_rd_data_cycles(perf_dfi_rd_data_cycles),
    .o_perf_dfi_wr_data_cycles(perf_dfi_wr_data_cycles),
    .o_perf_hif_hi_pri_rd(perf_hif_hi_pri_rd),
    .o_perf_hif_rd(perf_hif_rd),
    .o_perf_hif_rd_or_wr(perf_hif_rd_or_wr),
    .o_perf_hif_rmw(perf_hif_rmw),
    .o_perf_hif_wr(perf_hif_wr),
    .o_perf_hpr_req_with_nocredit(perf_hpr_req_with_nocredit),
    .o_perf_hpr_xact_when_critical(perf_hpr_xact_when_critical),
    .o_perf_ie_blk_hazard(perf_ie_blk_hazard),
    .o_perf_lpr_req_with_nocredit(perf_lpr_req_with_nocredit),
    .o_perf_lpr_xact_when_critical(perf_lpr_xact_when_critical),
    .o_perf_op_is_activate(perf_op_is_activate),
    .o_perf_op_is_cas(perf_op_is_cas),
    .o_perf_op_is_cas_wck_sus(perf_op_is_cas_wck_sus),
    .o_perf_op_is_cas_ws(perf_op_is_cas_ws),
    .o_perf_op_is_cas_ws_off(perf_op_is_cas_ws_off),
    .o_perf_op_is_crit_ref(perf_op_is_crit_ref),
    .o_perf_op_is_dqsosc_mpc(perf_op_is_dqsosc_mpc),
    .o_perf_op_is_dqsosc_mrr(perf_op_is_dqsosc_mrr),
    .o_perf_op_is_enter_dsm(perf_op_is_enter_dsm),
    .o_perf_op_is_enter_powerdown({perf_op_is_enter_powerdown_rank_1, perf_op_is_enter_powerdown_rank_0}),
    .o_perf_op_is_enter_selfref({perf_op_is_enter_selfref_rank_1,perf_op_is_enter_selfref_rank_0}),
    .o_perf_op_is_load_mode(perf_op_is_load_mode),
    .o_perf_op_is_mwr(perf_op_is_mwr),
    .o_perf_op_is_precharge(perf_op_is_precharge),
    .o_perf_op_is_rd(perf_op_is_rd),
    .o_perf_op_is_rd_activate(perf_op_is_rd_activate),
    .o_perf_op_is_rd_or_wr(perf_op_is_rd_or_wr),
    .o_perf_op_is_refresh(perf_op_is_refresh),
    .o_perf_op_is_rfm(perf_op_is_rfm),
    .o_perf_op_is_spec_ref(perf_op_is_spec_ref),
    .o_perf_op_is_tcr_mrr(perf_op_is_tcr_mrr),
    .o_perf_op_is_wr(perf_op_is_wr),
    .o_perf_op_is_zqlatch(perf_op_is_zqlatch),
    .o_perf_op_is_zqstart(perf_op_is_zqstart),
    .o_perf_precharge_for_other(perf_precharge_for_other),
    .o_perf_precharge_for_rdwr(perf_precharge_for_rdwr),
    .o_perf_rank(perf_rank),
    .o_perf_raw_hazard(perf_raw_hazard),
    .o_perf_rdwr_transitions(perf_rdwr_transitions),
    .o_perf_selfref_mode({perf_selfref_mode_rank_1, perf_selfref_mode_rank_0}),     // Increment signal per rank, split in two counters
    .o_perf_visible_window_limit_reached_rd(perf_visible_window_limit_reached_rd),
    .o_perf_visible_window_limit_reached_wr(perf_visible_window_limit_reached_wr),
    .o_perf_war_hazard(perf_war_hazard),
    .o_perf_waw_hazard(perf_waw_hazard),
    .o_perf_wr_xact_when_critical(perf_wr_xact_when_critical),
    .o_perf_write_combine(perf_write_combine),
    .o_perf_write_combine_noecc(perf_write_combine_noecc),
    .o_perf_write_combine_wrecc(perf_write_combine_wrecc),
    // SRAM control signals
    .i_acsm_pde(acsm_pde),
    .i_acsm_ret(acsm_ret),
    .i_bc_pde(bc_pde),
    .i_bc_ret(bc_ret),
    .i_dccm_pde(dccm_pde),
    .i_dccm_ret(dccm_ret),
    .i_gs_pde(gs_pde),
    .i_gs_ret(gs_ret),
    .i_iccm_pde(iccm_pde),
    .i_iccm_ret(iccm_ret),
    .i_pie_pde(pie_pde),
    .i_pie_ret(pie_ret),
    .i_wdata_pde(wdata_pde),
    .i_wdata_ret(wdata_ret),
    .o_acsm_prn(acsm_prn),
    .o_bc_prn(bc_prn),
    .o_dccm_prn(dccm_prn),
    .o_gs_prn(gs_prn),
    .o_iccm_prn(iccm_prn),
    .o_pie_prn(pie_prn),
    .o_wdata_prn(wdata_prn),
    // PHY debug signal
    .o_dwc_lpddr5xphy_dto(dwc_lpddr5xphy_dto),
    // PHY BUMPS
    .BP_MEMRESET_L(BP_MEMRESET_L),
    .BP_A (BP_A),
    .BP_ATO (BP_ATO),
    .BP_ATO_PLL (BP_ATO_PLL),
    .BP_B0_D (BP_B0_D),
    .BP_B1_D (BP_B1_D),
    .BP_B2_D (BP_B2_D),
    .BP_B3_D (BP_B3_D),
    .BP_CK0_C (BP_CK0_C),
    .BP_CK0_T (BP_CK0_T),
    .BP_CK1_C (BP_CK1_C),
    .BP_CK1_T (BP_CK1_T),
    .BP_ZN (BP_ZN), .snps_ddr_subsystem_inst_so(snps_ddr_subsystem_inst_so), 
                                .tdr_scan_mode_data_out(tdr_scan_mode_data_out), 
                                .tdr_iddq_mode_data_out(tdr_iddq_mode_data_out), 
                                .tdr_burnIn_data_out(tdr_burnIn_data_out), 
                                .tdr_scan_ucclk_mode_data_out(tdr_scan_ucclk_mode_data_out), 
                                .tdr_scan_occ_reset_data_out(tdr_scan_occ_reset_data_out), 
                                .tdr_scan_occ_bypass_data_out(tdr_scan_occ_bypass_data_out), 
                                .tdr_scan_asst_mode_data_out(tdr_scan_asst_mode_data_out), 
                                .tdr_scan_shift_async_data_out(tdr_scan_shift_async_data_out), 
                                .tdr_scan_shift_cg_data_out(tdr_scan_shift_cg_data_out), 
                                .tdi(tdi), 
                                .lpddr_p_rtl2_tessent_sib_subs_inst_to_select(lpddr_p_rtl2_tessent_sib_subs_inst_to_select), 
                                .test_logic_reset(test_logic_reset), 
                                .capture_dr_en(capture_dr_en), .shift_dr_en(shift_dr_en), 
                                .tck(tck), .update_dr_en(update_dr_en), 
                                .sri_ctrl_all_test(sri_ctrl_all_test), 
                                .sri_ctrl_ltest_en(sri_ctrl_ltest_en), 
                                .scan_en(scan_en), .bscan_scan_out(bscan_scan_out), 
                                .host_bscan_to_sel(host_bscan_to_sel), 
                                .force_disable(force_disable), 
                                .select_jtag_input(select_jtag_input), 
                                .select_jtag_output(select_jtag_output), 
                                .bisr_shift_en(bisr_shift_en), .bisr_clk(bisr_clk), 
                                .bisr_reset(bisr_reset), .bisr_si(bisr_si), 
                                .bisr_so(bisr_so), 
                                .to_DdrPhyCsrCmdTdrCaptureEn(to_DdrPhyCsrCmdTdrCaptureEn_ts1), 
                                .to_DdrPhyCsrCmdTdrShiftEn(to_DdrPhyCsrCmdTdrShiftEn_ts1), 
                                .to_DdrPhyCsrCmdTdrUpdateEn(to_DdrPhyCsrCmdTdrUpdateEn_ts1), 
                                .DdrPhyCsrCmdTdr_Tdo(DdrPhyCsrCmdTdr_Tdo), 
                                .to_DdrPhyCsrRdDataTdrCaptureEn(to_DdrPhyCsrRdDataTdrCaptureEn_ts1), 
                                .to_DdrPhyCsrRdDataTdrShiftEn(to_DdrPhyCsrRdDataTdrShiftEn_ts1), 
                                .to_DdrPhyCsrRdDataTdrUpdateEn(to_DdrPhyCsrRdDataTdrUpdateEn_ts1), 
                                .DdrPhyCsrRdDataTdr_Tdo(DdrPhyCsrRdDataTdr_Tdo), 
                                .to_WSI(to_WSI_ts1), .clock_out(i_lpddr_clk_ts1), 
                                .clock_out_ts1(i_ao_clk_ts1)
  );

  //-------------------------
  // Performance counters
  //-------------------------
  logic flush_perf_dfi_rd_data_cycles;
  assign flush_perf_dfi_rd_data_cycles = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_dfi_rd_data_cycles_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_dfi_rd_data_cycles_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_dfi_rd_data_cycles),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_dfi_rd_data_cycles.q),
    .i_ctrl_cnt_flush   (flush_perf_dfi_rd_data_cycles),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_dfi_rd_data_cycles_count.d)
  );

  logic flush_perf_counter_dfi_wr_data_cycles;
  assign flush_perf_counter_dfi_wr_data_cycles = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_dfi_wr_data_cycles_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_dfi_wr_data_cycles_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_dfi_wr_data_cycles),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_dfi_wr_data_cycles.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_dfi_wr_data_cycles),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_dfi_wr_data_cycles_count.d)
  );

  logic flush_perf_counter_hif_hi_pri_rd;
  assign flush_perf_counter_hif_hi_pri_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_hi_pri_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_hi_pri_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_hi_pri_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_hi_pri_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_hi_pri_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_hi_pri_rd_count.d)
  );

  logic flush_perf_counter_hif_rd;
  assign flush_perf_counter_hif_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_rd_count.d)
  );

  logic flush_perf_counter_hif_rd_or_wr;
  assign flush_perf_counter_hif_rd_or_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_rd_or_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_rd_or_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_rd_or_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_rd_or_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_rd_or_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_rd_or_wr_count.d)
  );

  logic flush_perf_counter_hif_rmw;
  assign flush_perf_counter_hif_rmw = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_rmw_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_rmw_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_rmw),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_rmw.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_rmw),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_rmw_count.d)
  );

  logic flush_perf_counter_hif_wr;
  assign flush_perf_counter_hif_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hif_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hif_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hif_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hif_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hif_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hif_wr_count.d)
  );

  logic flush_perf_counter_hpr_req_with_nocredit;
  assign flush_perf_counter_hpr_req_with_nocredit = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hpr_req_with_nocredit_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hpr_req_with_nocredit_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hpr_req_with_nocredit),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hpr_req_with_nocredit.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hpr_req_with_nocredit),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hpr_req_with_nocredit_count.d)
  );

  logic flush_perf_counter_hpr_xact_when_critical;
  assign flush_perf_counter_hpr_xact_when_critical = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_hpr_xact_when_critical_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_hpr_xact_when_critical_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_hpr_xact_when_critical),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_hpr_xact_when_critical.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_hpr_xact_when_critical),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_hpr_xact_when_critical_count.d)
  );

  logic flush_perf_counter_ie_blk_hazard;
  assign flush_perf_counter_ie_blk_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_ie_blk_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_ie_blk_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_ie_blk_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_ie_blk_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_ie_blk_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_ie_blk_hazard_count.d)
  );

  logic flush_perf_counter_lpr_req_with_nocredit;
  assign flush_perf_counter_lpr_req_with_nocredit = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_lpr_req_with_nocredit_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_lpr_req_with_nocredit_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_lpr_req_with_nocredit),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_lpr_req_with_nocredit.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_lpr_req_with_nocredit),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_lpr_req_with_nocredit_count.d)
  );

  logic flush_perf_counter_lpr_xact_when_critical;
  assign flush_perf_counter_lpr_xact_when_critical = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_lpr_xact_when_critical_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_lpr_xact_when_critical_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_lpr_xact_when_critical),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_lpr_xact_when_critical.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_lpr_xact_when_critical),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_lpr_xact_when_critical_count.d)
  );

  logic flush_perf_counter_op_is_activate;
  assign flush_perf_counter_op_is_activate = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_activate_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_activate_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_activate),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_activate.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_activate),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_activate_count.d)
  );

  logic flush_perf_counter_op_is_cas;
  assign flush_perf_counter_op_is_cas = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_count.d)
  );

  logic flush_perf_counter_op_is_cas_wck_sus;
  assign flush_perf_counter_op_is_cas_wck_sus = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_wck_sus_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_wck_sus_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas_wck_sus),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas_wck_sus.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas_wck_sus),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_wck_sus_count.d)
  );

  logic flush_perf_counter_op_is_cas_ws;
  assign flush_perf_counter_op_is_cas_ws = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_ws_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_ws_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas_ws),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas_ws.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas_ws),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_ws_count.d)
  );

  logic flush_perf_counter_op_is_cas_ws_off;
  assign flush_perf_counter_op_is_cas_ws_off = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_cas_ws_off_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_cas_ws_off_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_cas_ws_off),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_cas_ws_off.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_cas_ws_off),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_cas_ws_off_count.d)
  );

  logic flush_perf_counter_op_is_crit_ref;
  assign flush_perf_counter_op_is_crit_ref = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_crit_ref_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_crit_ref_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_crit_ref),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_crit_ref.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_crit_ref),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_crit_ref_count.d)
  );

  logic flush_perf_counter_op_is_dqsosc_mpc;
  assign flush_perf_counter_op_is_dqsosc_mpc = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_dqsosc_mpc_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_dqsosc_mpc_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_dqsosc_mpc),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_dqsosc_mpc.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_dqsosc_mpc),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_dqsosc_mpc_count.d)
  );

  logic flush_perf_counter_op_is_dqsosc_mrr;
  assign flush_perf_counter_op_is_dqsosc_mrr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_dqsosc_mrr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_dqsosc_mrr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_dqsosc_mrr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_dqsosc_mrr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_dqsosc_mrr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_dqsosc_mrr_count.d)
  );

  logic flush_perf_counter_op_is_enter_dsm;
  assign flush_perf_counter_op_is_enter_dsm = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_dsm_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_dsm_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_dsm),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_dsm.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_dsm),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_dsm_count.d)
  );

  logic flush_perf_counter_op_is_enter_powerdown_rank_0;
  assign flush_perf_counter_op_is_enter_powerdown_rank_0 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_powerdown_rank_0_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_powerdown_rank_0_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_powerdown_rank_0),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_powerdown_rank_0.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_powerdown_rank_0),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_powerdown_rank_0_count.d)
  );

  logic flush_perf_counter_op_is_enter_powerdown_rank_1;
  assign flush_perf_counter_op_is_enter_powerdown_rank_1 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_powerdown_rank_1_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_powerdown_rank_1_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_powerdown_rank_1),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_powerdown_rank_1.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_powerdown_rank_1),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_powerdown_rank_1_count.d)
  );

  logic flush_perf_counter_op_is_enter_selfref_rank_0;
  assign flush_perf_counter_op_is_enter_selfref_rank_0 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_selfref_rank_0_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_selfref_rank_0_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_selfref_rank_0),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_selfref_rank_0.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_selfref_rank_0),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_selfref_rank_0_count.d)
  );

  logic flush_perf_counter_op_is_enter_selfref_rank_1;
  assign flush_perf_counter_op_is_enter_selfref_rank_1 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_enter_selfref_rank_1_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_enter_selfref_rank_1_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_enter_selfref_rank_1),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_enter_selfref_rank_1.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_enter_selfref_rank_1),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_enter_selfref_rank_1_count.d)
  );

  logic flush_perf_counter_op_is_load_mode;
  assign flush_perf_counter_op_is_load_mode = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_load_mode_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_load_mode_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_load_mode),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_load_mode.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_load_mode),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_load_mode_count.d)
  );

  logic flush_perf_counter_op_is_mwr;
  assign flush_perf_counter_op_is_mwr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_mwr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_mwr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_mwr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_mwr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_mwr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_mwr_count.d)
  );

  logic flush_perf_counter_op_is_precharge;
  assign flush_perf_counter_op_is_precharge = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_precharge_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_precharge_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_precharge),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_precharge.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_precharge),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_precharge_count.d)
  );

  logic flush_perf_counter_op_is_rd;
  assign flush_perf_counter_op_is_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rd_count.d)
  );

  logic flush_perf_counter_op_is_rd_activate;
  assign flush_perf_counter_op_is_rd_activate = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rd_activate_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rd_activate_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rd_activate),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_rd_activate.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rd_activate),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rd_activate_count.d)
  );

  logic flush_perf_counter_op_is_rd_or_wr;
  assign flush_perf_counter_op_is_rd_or_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rd_or_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rd_or_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rd_or_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_rd_or_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rd_or_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rd_or_wr_count.d)
  );

  logic flush_perf_counter_op_is_refresh;
  assign flush_perf_counter_op_is_refresh = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_refresh_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_refresh_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_refresh),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_0.perf_op_is_refresh.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_refresh),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_refresh_count.d)
  );

  logic flush_perf_counter_op_is_rfm;
  assign flush_perf_counter_op_is_rfm = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_rfm_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_rfm_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_rfm),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_rfm.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_rfm),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_rfm_count.d)
  );

  logic flush_perf_counter_op_is_spec_ref;
  assign flush_perf_counter_op_is_spec_ref = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_spec_ref_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_spec_ref_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_spec_ref),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_spec_ref.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_spec_ref),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_spec_ref_count.d)
  );

  logic flush_perf_counter_op_is_tcr_mrr;
  assign flush_perf_counter_op_is_tcr_mrr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_tcr_mrr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_tcr_mrr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_tcr_mrr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_tcr_mrr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_tcr_mrr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_tcr_mrr_count.d)
  );

  logic flush_perf_counter_op_is_wr;
  assign flush_perf_counter_op_is_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_wr_count.d)
  );

  logic flush_perf_counter_op_is_zqlatch;
  assign flush_perf_counter_op_is_zqlatch = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_zqlatch_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_zqlatch_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_zqlatch),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_zqlatch.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_zqlatch),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_zqlatch_count.d)
  );

  logic flush_perf_counter_op_is_zqstart;
  assign flush_perf_counter_op_is_zqstart = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_op_is_zqstart_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_op_is_zqstart_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_op_is_zqstart),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_op_is_zqstart.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_op_is_zqstart),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_op_is_zqstart_count.d)
  );

  logic flush_perf_counter_precharge_for_other;
  assign flush_perf_counter_precharge_for_other = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_precharge_for_other_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_precharge_for_other_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_precharge_for_other),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_precharge_for_other.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_precharge_for_other),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_precharge_for_other_count.d)
  );

  logic flush_perf_counter_precharge_for_rdwr;
  assign flush_perf_counter_precharge_for_rdwr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_precharge_for_rdwr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_precharge_for_rdwr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_precharge_for_rdwr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_precharge_for_rdwr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_precharge_for_rdwr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_precharge_for_rdwr_count.d)
  );

  logic flush_perf_counter_raw_hazard;
  assign flush_perf_counter_raw_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_raw_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raw_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_raw_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_raw_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raw_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_raw_hazard_count.d)
  );

  logic flush_perf_counter_rdwr_transitions;
  assign flush_perf_counter_rdwr_transitions = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_rdwr_transitions_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_rdwr_transitions_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_rdwr_transitions),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_rdwr_transitions.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_rdwr_transitions),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_rdwr_transitions_count.d)
  );

  logic flush_perf_counter_selfref_mode_rank_0;
  assign flush_perf_counter_selfref_mode_rank_0 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_selfref_mode_rank_0_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_selfref_mode_rank_0_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_selfref_mode_rank_0),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_selfref_mode_rank_0.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_selfref_mode_rank_0),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_selfref_mode_rank_0_count.d)
  );

  logic flush_perf_counter_selfref_mode_rank_1;
  assign flush_perf_counter_selfref_mode_rank_1 = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_selfref_mode_rank_1_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_selfref_mode_rank_1_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_selfref_mode_rank_1),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_selfref_mode_rank_1.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_selfref_mode_rank_1),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_selfref_mode_rank_1_count.d)
  );

  logic flush_perf_counter_visible_window_limit_reached_rd;
  assign flush_perf_counter_visible_window_limit_reached_rd = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_visible_window_limit_reached_rd_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_visible_window_limit_reached_rd_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_visible_window_limit_reached_rd),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_visible_window_limit_reached_rd.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_visible_window_limit_reached_rd),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_visible_window_limit_reached_rd_count.d)
  );

  logic flush_perf_counter_visible_window_limit_reached_wr;
  assign flush_perf_counter_visible_window_limit_reached_wr = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_visible_window_limit_reached_wr_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_visible_window_limit_reached_wr_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_visible_window_limit_reached_wr),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_visible_window_limit_reached_wr.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_visible_window_limit_reached_wr),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_visible_window_limit_reached_wr_count.d)
  );

  logic flush_perf_counter_war_hazard;
  assign flush_perf_counter_war_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_war_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_war_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_war_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_war_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_war_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_war_hazard_count.d)
  );

  logic flush_perf_counter_waw_hazard;
  assign flush_perf_counter_waw_hazard = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_waw_hazard_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waw_hazard_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_waw_hazard),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_waw_hazard.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waw_hazard),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_waw_hazard_count.d)
  );

  logic flush_perf_counter_wr_xact_when_critical;
  assign flush_perf_counter_wr_xact_when_critical = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_wr_xact_when_critical_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_wr_xact_when_critical_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_wr_xact_when_critical),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_wr_xact_when_critical.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_wr_xact_when_critical),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_wr_xact_when_critical_count.d)
  );

  logic flush_perf_counter_write_combine;
  assign flush_perf_counter_write_combine = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_write_combine_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_write_combine_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_write_combine),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_write_combine.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_write_combine),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_write_combine_count.d)
  );

  logic flush_perf_counter_write_combine_noecc;
  assign flush_perf_counter_write_combine_noecc = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_write_combine_noecc_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_write_combine_noecc_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_write_combine_noecc),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_write_combine_noecc.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_write_combine_noecc),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_write_combine_noecc_count.d)
  );

  logic flush_perf_counter_write_combine_wrecc;
  assign flush_perf_counter_write_combine_wrecc = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_perf_write_combine_wrecc_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_write_combine_wrecc_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (perf_write_combine_wrecc),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.perf_write_combine_wrecc.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_write_combine_wrecc),
    .o_ctrl_cnt_value   (hw2reg.lpddr_perf_write_combine_wrecc_count.d)
  );

  logic flush_perf_counter_raq_split;
  assign flush_perf_counter_raq_split = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raq_split_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raq_split_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raq_split),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raq_split.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raq_split),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raq_split_count.d)
  );

  logic flush_perf_counter_raqb_pop;
  assign flush_perf_counter_raqb_pop = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqb_pop_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqb_pop_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqb_pop),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqb_pop.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqb_pop),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqb_pop_count.d)
  );

  logic flush_perf_counter_raqb_push;
  assign flush_perf_counter_raqb_push = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqb_push_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqb_push_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqb_push),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqb_push.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqb_push),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqb_push_count.d)
  );

  logic flush_perf_counter_raqr_pop;
  assign flush_perf_counter_raqr_pop = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqr_pop_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqr_pop_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqr_pop),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqr_pop.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqr_pop),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqr_pop_count.d)
  );

  logic flush_perf_counter_raqr_push;
  assign flush_perf_counter_raqr_push = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_raqr_push_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_raqr_push_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (raqr_push),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.raqr_push.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_raqr_push),
    .o_ctrl_cnt_value   (hw2reg.lpddr_raqr_push_count.d)
  );

  logic flush_perf_counter_waq_pop;
  assign flush_perf_counter_waq_pop = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_waq_pop_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waq_pop_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (waq_pop),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.waq_pop.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waq_pop),
    .o_ctrl_cnt_value   (hw2reg.lpddr_waq_pop_count.d)
  );

  logic flush_perf_counter_waq_push;
  assign flush_perf_counter_waq_push = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_waq_push_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waq_push_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (waq_push),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.waq_push.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waq_push),
    .o_ctrl_cnt_value   (hw2reg.lpddr_waq_push_count.d)
  );

  logic flush_perf_counter_waq_split;
  assign flush_perf_counter_waq_split = (reg2hw.lpddr_perf_count_config.lpddr_perf_clear_on_read.q &
                                          reg2hw.lpddr_waq_split_count.re) |
                                          reg2hw.lpddr_perf_count_config.lpddr_perf_clear_all.q;
  europa_lpddr_async_perf_counter #(
    .CounterWidth(LPDDR_PERF_COUNTER_WIDTH),
    .SyncStages(LPDDR_SYNC_STAGES)
  ) perf_counter_waq_split_inst (
    // Signals sync to the count clk
    .i_count_clk        (lpddr_clk),
    .i_count_rst_n      (ctrl_rst_n),
    .i_count_inc        (waq_split),

    // Signals sync to the ctrl_clk
    .i_ctrl_clk         (i_ao_clk_ts1),
    .i_ctrl_rst_n       (i_ao_rst_n),
    .i_ctrl_cnt_en      (reg2hw.lpddr_perf_count_enables_1.waq_split.q),
    .i_ctrl_cnt_flush   (flush_perf_counter_waq_split),
    .o_ctrl_cnt_value   (hw2reg.lpddr_waq_split_count.d)
  );


  lpddr_p_rtl2_tessent_tap_main lpddr_p_rtl2_tessent_tap_main_inst(
      .tdi(tdi), .tms(tms), .tck(tck), .trst(trst), .tdo(tdo), .fsm_state(), .host_bscan_to_sel(host_bscan_to_sel), 
      .host_bscan_from_so(bscan_scan_out), .force_disable(force_disable), .select_jtag_input(select_jtag_input), 
      .select_jtag_output(select_jtag_output), .extest_pulse(), .extest_train(), 
      .host_1_to_sel(lpddr_p_rtl2_tessent_tap_main_inst_to_select), .host_1_from_so(lpddr_p_rtl2_tessent_sib_sri_inst_so), 
      .capture_dr_en(capture_dr_en), .test_logic_reset(test_logic_reset), .shift_dr_en(shift_dr_en), 
      .update_dr_en(update_dr_en), .tdo_en(tdo_en)
  );

  lpddr_p_rtl2_tessent_sib_1 lpddr_p_rtl2_tessent_sib_sri_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_tap_main_inst_to_select), 
      .ijtag_si(tdi), .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), 
      .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_sri_inst_so), .ijtag_from_so(lpddr_p_rtl2_tessent_sib_sri_local_inst_so), 
      .ijtag_to_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_subs_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(tdi), .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), 
      .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_subs_inst_so), .ijtag_from_so(snps_ddr_subsystem_inst_so), 
      .ijtag_to_sel(lpddr_p_rtl2_tessent_sib_subs_inst_to_select)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_tdr_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_subs_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_tdr_inst_so), 
      .ijtag_from_so(lpddr_p_rtl2_tessent_scanmux_tdr_inst_so), .ijtag_to_sel(lpddr_p_rtl2_tessent_sib_tdr_inst_to_enable_in)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_scan_cfg_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_tdr_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_so), 
      .ijtag_from_so(lpddr_p_rtl2_tessent_tdr_scan_shift_cg_inst_so), .ijtag_to_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_ssn_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_ssn_inst_so), 
      .ijtag_from_so(ssh0_so), .ijtag_to_sel(ijtag_to_sel)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_occ_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_ssn_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_occ_inst_so), 
      .ijtag_from_so(ijtag_so_ts1), .ijtag_to_sel(ijtag_to_sel_ts1)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_edt_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_occ_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_edt_inst_so), 
      .ijtag_from_so(ijtag_so_ts3), .ijtag_to_sel(ijtag_to_sel_ts2)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_sri_ctrl_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_edt_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_so), 
      .ijtag_from_so(lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst_so), .ijtag_to_sel(lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_to_select)
  );

  lpddr_p_rtl2_tessent_sib_2 lpddr_p_rtl2_tessent_sib_sri_local_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_so(lpddr_p_rtl2_tessent_sib_sri_local_inst_so), 
      .ijtag_from_so(lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_so), .ijtag_to_sel()
  );

  lpddr_p_rtl2_tessent_tdr_sri_ctrl lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_sri_ctrl_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_edt_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .occ_kill_clock_en(occ_kill_clock_en), 
      .observe_test_point_en(), .control_test_point_en(), .async_set_reset_static_disable(), 
      .ltest_en(sri_ctrl_ltest_en), .all_test(sri_ctrl_all_test), .ijtag_so(lpddr_p_rtl2_tessent_tdr_sri_ctrl_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_mode_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_tdr_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_mode_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_mode_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_iddq_mode_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_scan_mode_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_iddq_mode_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_iddq_mode_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_burnIn_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_iddq_mode_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_burnIn_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_burnIn_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_ucclk_mode_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_burnIn_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_ucclk_mode_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_ucclk_mode_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_occ_reset_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_scan_ucclk_mode_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_occ_reset_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_occ_reset_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_occ_bypass_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_scan_occ_reset_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_occ_bypass_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_occ_bypass_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_asst_mode_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_scan_occ_bypass_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_asst_mode_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_asst_mode_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_shift_async_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_scan_asst_mode_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_shift_async_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_shift_async_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_scan_mode lpddr_p_rtl2_tessent_tdr_scan_shift_cg_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_to_select), 
      .ijtag_si(lpddr_p_rtl2_tessent_tdr_scan_shift_async_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(tdr_scan_shift_cg_data_out), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_scan_shift_cg_inst_so)
  );

  lpddr_p_rtl2_tessent_tdr_phy lpddr_p_rtl2_tessent_tdr_phy_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(lpddr_p_rtl2_tessent_sib_tdr_inst_to_enable_in), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_subs_inst_so), .ijtag_ce(capture_dr_en), 
      .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), .ijtag_tck(tck), .ijtag_data_out(lpddr_p_rtl2_tessent_tdr_phy_inst_dout0), 
      .ijtag_so(lpddr_p_rtl2_tessent_tdr_phy_inst_so)
  );

  lpddr_p_rtl2_tessent_scanmux_1 lpddr_p_rtl2_tessent_scanmux_tdr_inst(
      .mux_in0(dwc_ddrphy_jtag_dfttdrs_Cmd_inst_so), .mux_in1(dwc_ddrphy_jtag_dfttdrs_RdData_inst_so), 
      .mux_out(lpddr_p_rtl2_tessent_scanmux_tdr_inst_so), .mux_select(lpddr_p_rtl2_tessent_tdr_phy_inst_dout0), 
      .enable_in(lpddr_p_rtl2_tessent_sib_tdr_inst_to_enable_in), .enable_out0(lpddr_p_rtl2_tessent_scanmux_tdr_inst_to_select0), 
      .enable_out1(lpddr_p_rtl2_tessent_scanmux_tdr_inst_to_select1)
  );

  lpddr_p_rtl2_tessent_ssn_scan_host_sh lpddr_p_rtl2_tessent_ssn_scan_host_sh_inst(
      .bus_clock(ssn_bus_clk), .bus_data_in(bus_data_out), .bus_data_out(ssn_bus_data_out), 
      .ijtag_reset(test_logic_reset), .ijtag_tck(tck), .ijtag_sel(ijtag_to_sel), 
      .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), 
      .ijtag_si(lpddr_p_rtl2_tessent_sib_scan_cfg_inst_so), .ijtag_so(ssh0_so), 
      .scan_en(scan_en), .edt_update(edt_update), .test_clock(test_clock), .to_scan_in_gx(ssh_sh_grp_gx_to_scan_in[4:0]), 
      .from_scan_out_gx(edt_channels_out_ts1[4:0]), .to_scan_in_gi(ssh_sh_grp_gi_to_scan_in[11:0]), 
      .from_scan_out_gi(edt_channels_out[11:0])
  );

  lpddr_p_rtl2_tessent_ssn_receiver_1x_pipe_w24_1 lpddr_p_rtl2_tessent_ssn_receiver_1x_pipe_pi_inst(
      .bus_clock(ssn_bus_clk), .bus_data_in(ssn_bus_data_in), .bus_data_out(bus_data_out), 
      .ijtag_reset(test_logic_reset)
  );

  axe_tcl_clk_gating tessent_persistent_cell_edt_clock(
      .o_clk(o_clk_ts1), .i_clk(test_clock), .i_en(scan_en), .i_test_en(scan_en)
  );

  axe_tcl_clk_gating tessent_persistent_cell_shift_capture_clock(
      .o_clk(o_clk), .i_clk(test_clock), .i_en(edt_update_inv), .i_test_en(edt_update_inv)
  );

  axe_tcl_std_inverter shift_capture_clock_fe_inv(
      .o_z(edt_update_inv), .i_a(edt_update)
  );

  assign bisr_so_ts1 = bisr_si;

  lpddr_p_rtl2_tessent_occ lpddr_p_rtl2_tessent_occ_lpddr_clk_inst(
      .fast_clock(i_lpddr_clk), .slow_clock(o_clk), .scan_en(scan_en), .shift_only_mode(1'b0), 
      .kill_clock_en(occ_kill_clock_en), .ijtag_tck(tck), .ijtag_reset(test_logic_reset), 
      .ijtag_sel(ijtag_to_sel_ts1), .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), 
      .ijtag_ue(update_dr_en), .ijtag_si(lpddr_p_rtl2_tessent_sib_ssn_inst_so), 
      .ijtag_so(ijtag_so), .clock_out(i_lpddr_clk_ts1), .scan_in(1'b0), .scan_out()
  );

  lpddr_p_rtl2_tessent_occ lpddr_p_rtl2_tessent_occ_ao_clk_inst(
      .fast_clock(i_ao_clk), .slow_clock(o_clk), .scan_en(scan_en), .shift_only_mode(1'b0), 
      .kill_clock_en(occ_kill_clock_en), .ijtag_tck(tck), .ijtag_reset(test_logic_reset), 
      .ijtag_sel(ijtag_to_sel_ts1), .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), 
      .ijtag_ue(update_dr_en), .ijtag_si(ijtag_so), .ijtag_so(ijtag_so_ts1), .clock_out(i_ao_clk_ts1), 
      .scan_in(1'b0), .scan_out()
  );

  lpddr_p_rtl2_tessent_edt_c1_int lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .edt_clock(o_clk_ts1), .edt_update(edt_update), .edt_low_power_shift_en(edt_low_power_shift_en), 
      .edt_bypass(edt_bypass), .edt_channels_in(ssh_sh_grp_gi_to_scan_in[11:0]), 
      .edt_channels_out(edt_channels_out[11:0]), .edt_scan_in(edt_scan_in[449:0]), 
      .edt_scan_out({o_z, o_z_ts1, o_z_ts2, o_z_ts3, o_z_ts4, o_z_ts5, 
      o_z_ts6, o_z_ts7, o_z_ts8, o_z_ts9, o_z_ts10, o_z_ts11, o_z_ts12, 
      o_z_ts13, o_z_ts14, o_z_ts15, o_z_ts16, o_z_ts17, o_z_ts18, o_z_ts19, 
      o_z_ts20, o_z_ts21, o_z_ts22, o_z_ts23, o_z_ts24, o_z_ts25, o_z_ts26, 
      o_z_ts27, o_z_ts28, o_z_ts29, o_z_ts30, o_z_ts31, o_z_ts32, o_z_ts33, 
      o_z_ts34, o_z_ts35, o_z_ts36, o_z_ts37, o_z_ts38, o_z_ts39, o_z_ts40, 
      o_z_ts41, o_z_ts42, o_z_ts43, o_z_ts44, o_z_ts45, o_z_ts46, o_z_ts47, 
      o_z_ts48, o_z_ts49, o_z_ts50, o_z_ts51, o_z_ts52, o_z_ts53, o_z_ts54, 
      o_z_ts55, o_z_ts56, o_z_ts57, o_z_ts58, o_z_ts59, o_z_ts60, o_z_ts61, 
      o_z_ts62, o_z_ts63, o_z_ts64, o_z_ts65, o_z_ts66, o_z_ts67, o_z_ts68, 
      o_z_ts69, o_z_ts70, o_z_ts71, o_z_ts72, o_z_ts73, o_z_ts74, o_z_ts75, 
      o_z_ts76, o_z_ts77, o_z_ts78, o_z_ts79, o_z_ts80, o_z_ts81, o_z_ts82, 
      o_z_ts83, o_z_ts84, o_z_ts85, o_z_ts86, o_z_ts87, o_z_ts88, o_z_ts89, 
      o_z_ts90, o_z_ts91, o_z_ts92, o_z_ts93, o_z_ts94, o_z_ts95, o_z_ts96, 
      o_z_ts97, o_z_ts98, o_z_ts99, o_z_ts100, o_z_ts101, o_z_ts102, 
      o_z_ts103, o_z_ts104, o_z_ts105, o_z_ts106, o_z_ts107, o_z_ts108, 
      o_z_ts109, o_z_ts110, o_z_ts111, o_z_ts112, o_z_ts113, o_z_ts114, 
      o_z_ts115, o_z_ts116, o_z_ts117, o_z_ts118, o_z_ts119, o_z_ts120, 
      o_z_ts121, o_z_ts122, o_z_ts123, o_z_ts124, o_z_ts125, o_z_ts126, 
      o_z_ts127, o_z_ts128, o_z_ts129, o_z_ts130, o_z_ts131, o_z_ts132, 
      o_z_ts133, o_z_ts134, o_z_ts135, o_z_ts136, o_z_ts137, o_z_ts138, 
      o_z_ts139, o_z_ts140, o_z_ts141, o_z_ts142, o_z_ts143, o_z_ts144, 
      o_z_ts145, o_z_ts146, o_z_ts147, o_z_ts148, o_z_ts149, o_z_ts150, 
      o_z_ts151, o_z_ts152, o_z_ts153, o_z_ts154, o_z_ts155, o_z_ts156, 
      o_z_ts157, o_z_ts158, o_z_ts159, o_z_ts160, o_z_ts161, o_z_ts162, 
      o_z_ts163, o_z_ts164, o_z_ts165, o_z_ts166, o_z_ts167, o_z_ts168, 
      o_z_ts169, o_z_ts170, o_z_ts171, o_z_ts172, o_z_ts173, o_z_ts174, 
      o_z_ts175, o_z_ts176, o_z_ts177, o_z_ts178, o_z_ts179, o_z_ts180, 
      o_z_ts181, o_z_ts182, o_z_ts183, o_z_ts184, o_z_ts185, o_z_ts186, 
      o_z_ts187, o_z_ts188, o_z_ts189, o_z_ts190, o_z_ts191, o_z_ts192, 
      o_z_ts193, o_z_ts194, o_z_ts195, o_z_ts196, o_z_ts197, o_z_ts198, 
      o_z_ts199, o_z_ts200, o_z_ts201, o_z_ts202, o_z_ts203, o_z_ts204, 
      o_z_ts205, o_z_ts206, o_z_ts207, o_z_ts208, o_z_ts209, o_z_ts210, 
      o_z_ts211, o_z_ts212, o_z_ts213, o_z_ts214, o_z_ts215, o_z_ts216, 
      o_z_ts217, o_z_ts218, o_z_ts219, o_z_ts220, o_z_ts221, o_z_ts222, 
      o_z_ts223, o_z_ts224, o_z_ts225, o_z_ts226, o_z_ts227, o_z_ts228, 
      o_z_ts229, o_z_ts230, o_z_ts231, o_z_ts232, o_z_ts233, o_z_ts234, 
      o_z_ts235, o_z_ts236, o_z_ts237, o_z_ts238, o_z_ts239, o_z_ts240, 
      o_z_ts241, o_z_ts242, o_z_ts243, o_z_ts244, o_z_ts245, o_z_ts246, 
      o_z_ts247, o_z_ts248, o_z_ts249, o_z_ts250, o_z_ts251, o_z_ts252, 
      o_z_ts253, o_z_ts254, o_z_ts255, o_z_ts256, o_z_ts257, o_z_ts258, 
      o_z_ts259, o_z_ts260, o_z_ts261, o_z_ts262, o_z_ts263, o_z_ts264, 
      o_z_ts265, o_z_ts266, o_z_ts267, o_z_ts268, o_z_ts269, o_z_ts270, 
      o_z_ts271, o_z_ts272, o_z_ts273, o_z_ts274, o_z_ts275, o_z_ts276, 
      o_z_ts277, o_z_ts278, o_z_ts279, o_z_ts280, o_z_ts281, o_z_ts282, 
      o_z_ts283, o_z_ts284, o_z_ts285, o_z_ts286, o_z_ts287, o_z_ts288, 
      o_z_ts289, o_z_ts290, o_z_ts291, o_z_ts292, o_z_ts293, o_z_ts294, 
      o_z_ts295, o_z_ts296, o_z_ts297, o_z_ts298, o_z_ts299, o_z_ts300, 
      o_z_ts301, o_z_ts302, o_z_ts303, o_z_ts304, o_z_ts305, o_z_ts306, 
      o_z_ts307, o_z_ts308, o_z_ts309, o_z_ts310, o_z_ts311, o_z_ts312, 
      o_z_ts313, o_z_ts314, o_z_ts315, o_z_ts316, o_z_ts317, o_z_ts318, 
      o_z_ts319, o_z_ts320, o_z_ts321, o_z_ts322, o_z_ts323, o_z_ts324, 
      o_z_ts325, o_z_ts326, o_z_ts327, o_z_ts328, o_z_ts329, o_z_ts330, 
      o_z_ts331, o_z_ts332, o_z_ts333, o_z_ts334, o_z_ts335, o_z_ts336, 
      o_z_ts337, o_z_ts338, o_z_ts339, o_z_ts340, o_z_ts341, o_z_ts342, 
      o_z_ts343, o_z_ts344, o_z_ts345, o_z_ts346, o_z_ts347, o_z_ts348, 
      o_z_ts349, o_z_ts350, o_z_ts351, o_z_ts352, o_z_ts353, o_z_ts354, 
      o_z_ts355, o_z_ts356, o_z_ts357, o_z_ts358, o_z_ts359, o_z_ts360, 
      o_z_ts361, o_z_ts362, o_z_ts363, o_z_ts364, o_z_ts365, o_z_ts366, 
      o_z_ts367, o_z_ts368, o_z_ts369, o_z_ts370, o_z_ts371, o_z_ts372, 
      o_z_ts373, o_z_ts374, o_z_ts375, o_z_ts376, o_z_ts377, o_z_ts378, 
      o_z_ts379, o_z_ts380, o_z_ts381, o_z_ts382, o_z_ts383, o_z_ts384, 
      o_z_ts385, o_z_ts386, o_z_ts387, o_z_ts388, o_z_ts389, o_z_ts390, 
      o_z_ts391, o_z_ts392, o_z_ts393, o_z_ts394, o_z_ts395, o_z_ts396, 
      o_z_ts397, o_z_ts398, o_z_ts399, o_z_ts400, o_z_ts401, o_z_ts402, 
      o_z_ts403, o_z_ts404, o_z_ts405, o_z_ts406, o_z_ts407, o_z_ts408, 
      o_z_ts409, o_z_ts410, o_z_ts411, o_z_ts412, o_z_ts413, o_z_ts414, 
      o_z_ts415, o_z_ts416, o_z_ts417, o_z_ts418, o_z_ts419, o_z_ts420, 
      o_z_ts421, o_z_ts422, o_z_ts423, o_z_ts424, o_z_ts425, o_z_ts426, 
      o_z_ts427, o_z_ts428, o_z_ts429, o_z_ts430, o_z_ts431, o_z_ts432, 
      o_z_ts433, o_z_ts434, o_z_ts435, o_z_ts436, o_z_ts437, o_z_ts438, 
      o_z_ts439, o_z_ts440, o_z_ts441, o_z_ts442, o_z_ts443, o_z_ts444, 
      o_z_ts445, o_z_ts446, o_z_ts447, o_z_ts448, o_z_ts449})
  );

  lpddr_p_rtl2_tessent_edt_cx lpddr_p_rtl2_tessent_edt_cx_inst(
      .edt_clock(o_clk_ts1), .edt_update(edt_update), .edt_bypass(edt_bypass_ts1), 
      .edt_channels_in(ssh_sh_grp_gx_to_scan_in[4:0]), .edt_channels_out(edt_channels_out_ts1[4:0]), 
      .edt_scan_in(edt_scan_in_ts1[10:0]), .edt_scan_out({o_z_ts450, 
      o_z_ts451, o_z_ts452, o_z_ts453, o_z_ts454, o_z_ts455, o_z_ts456, 
      o_z_ts457, o_z_ts458, o_z_ts459, o_z_ts460})
  );

  lpddr_p_rtl2_tessent_edt_c1_int_tdr lpddr_p_rtl2_tessent_edt_c1_int_tdr_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(ijtag_to_sel_ts2), .ijtag_si(lpddr_p_rtl2_tessent_sib_occ_inst_so), 
      .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), 
      .ijtag_tck(tck), .edt_bypass(edt_bypass), .edt_low_power_shift_en(edt_low_power_shift_en), 
      .ijtag_so(ijtag_so_ts2)
  );

  lpddr_p_rtl2_tessent_edt_cx_tdr lpddr_p_rtl2_tessent_edt_cx_tdr_inst(
      .ijtag_reset(test_logic_reset), .ijtag_sel(ijtag_to_sel_ts2), .ijtag_si(ijtag_so_ts2), 
      .ijtag_ce(capture_dr_en), .ijtag_se(shift_dr_en), .ijtag_ue(update_dr_en), 
      .ijtag_tck(tck), .edt_bypass(edt_bypass_ts1), .ijtag_so(ijtag_so_ts3)
  );

  axe_tcl_std_buffer tessent_scan_buf_i_449_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[449])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_448_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[448])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_447_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[447])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_446_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[446])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_445_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[445])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_444_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[444])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_443_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[443])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_442_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[442])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_441_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[441])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_440_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[440])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_439_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[439])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_438_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[438])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_437_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[437])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_436_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[436])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_435_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[435])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_434_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[434])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_433_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[433])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_432_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[432])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_431_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[431])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_430_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[430])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_429_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[429])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_428_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[428])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_427_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[427])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_426_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[426])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_425_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[425])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_424_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[424])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_423_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[423])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_422_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[422])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_421_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[421])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_420_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[420])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_419_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[419])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_418_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[418])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_417_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[417])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_416_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[416])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_415_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[415])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_414_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[414])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_413_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[413])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_412_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[412])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_411_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[411])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_410_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[410])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_409_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[409])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_408_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[408])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_407_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[407])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_406_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[406])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_405_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[405])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_404_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[404])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_403_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[403])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_402_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[402])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_401_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[401])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_400_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[400])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_399_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[399])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_398_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[398])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_397_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[397])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_396_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[396])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_395_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[395])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_394_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[394])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_393_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[393])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_392_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[392])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_391_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[391])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_390_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[390])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_389_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[389])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_388_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[388])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_387_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[387])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_386_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[386])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_385_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[385])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_384_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[384])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_383_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[383])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_382_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[382])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_381_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[381])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_380_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[380])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_379_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[379])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_378_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[378])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_377_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[377])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_376_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[376])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_375_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[375])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_374_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[374])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_373_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[373])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_372_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[372])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_371_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[371])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_370_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[370])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_369_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[369])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_368_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[368])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_367_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[367])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_366_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[366])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_365_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[365])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_364_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[364])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_363_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[363])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_362_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[362])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_361_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[361])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_360_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[360])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_359_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[359])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_358_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[358])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_357_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[357])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_356_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[356])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_355_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[355])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_354_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[354])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_353_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[353])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_352_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[352])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_351_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[351])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_350_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[350])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_349_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[349])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_348_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[348])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_347_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[347])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_346_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[346])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_345_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[345])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_344_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[344])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_343_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[343])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_342_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[342])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_341_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[341])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_340_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[340])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_339_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[339])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_338_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[338])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_337_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[337])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_336_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[336])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_335_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[335])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_334_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[334])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_333_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[333])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_332_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[332])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_331_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[331])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_330_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[330])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_329_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[329])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_328_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[328])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_327_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[327])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_326_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[326])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_325_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[325])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_324_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[324])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_323_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[323])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_322_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[322])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_321_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[321])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_320_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[320])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_319_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[319])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_318_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[318])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_317_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[317])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_316_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[316])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_315_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[315])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_314_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[314])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_313_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[313])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_312_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[312])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_311_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[311])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_310_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[310])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_309_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[309])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_308_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[308])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_307_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[307])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_306_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[306])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_305_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[305])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_304_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[304])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_303_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[303])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_302_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[302])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_301_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[301])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_300_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[300])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_299_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[299])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_298_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[298])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_297_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[297])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_296_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[296])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_295_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[295])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_294_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[294])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_293_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[293])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_292_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[292])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_291_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[291])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_290_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[290])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_289_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[289])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_288_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[288])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_287_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[287])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_286_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[286])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_285_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[285])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_284_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[284])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_283_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[283])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_282_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[282])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_281_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[281])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_280_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[280])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_279_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[279])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_278_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[278])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_277_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[277])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_276_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[276])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_275_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[275])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_274_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[274])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_273_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[273])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_272_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[272])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_271_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[271])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_270_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[270])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_269_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[269])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_268_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[268])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_267_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[267])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_266_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[266])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_265_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[265])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_264_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[264])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_263_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[263])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_262_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[262])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_261_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[261])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_260_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[260])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_259_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[259])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_258_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[258])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_257_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[257])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_256_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[256])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_255_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[255])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_254_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[254])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_253_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[253])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_252_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[252])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_251_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[251])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_250_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[250])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_249_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[249])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_248_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[248])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_247_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[247])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_246_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[246])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_245_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[245])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_244_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[244])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_243_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[243])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_242_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[242])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_241_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[241])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_240_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[240])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_239_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[239])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_238_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[238])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_237_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[237])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_236_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[236])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_235_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[235])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_234_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[234])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_233_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[233])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_232_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[232])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_231_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[231])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_230_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[230])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_229_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[229])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_228_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[228])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_227_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[227])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_226_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[226])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_225_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[225])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_224_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[224])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_223_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[223])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_222_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[222])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_221_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[221])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_220_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[220])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_219_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[219])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_218_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[218])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_217_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[217])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_216_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[216])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_215_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[215])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_214_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[214])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_213_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[213])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_212_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[212])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_211_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[211])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_210_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[210])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_209_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[209])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_208_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[208])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_207_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[207])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_206_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[206])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_205_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[205])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_204_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[204])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_203_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[203])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_202_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[202])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_201_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[201])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_200_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[200])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_199_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[199])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_198_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[198])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_197_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[197])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_196_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[196])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_195_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[195])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_194_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[194])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_193_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[193])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_192_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[192])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_191_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[191])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_190_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[190])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_189_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[189])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_188_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[188])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_187_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[187])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_186_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[186])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_185_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[185])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_184_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[184])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_183_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[183])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_182_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[182])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_181_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[181])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_180_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[180])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_179_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[179])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_178_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[178])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_177_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[177])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_176_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[176])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_175_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[175])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_174_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[174])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_173_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[173])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_172_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[172])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_171_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[171])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_170_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[170])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_169_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[169])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_168_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[168])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_167_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[167])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_166_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[166])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_165_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[165])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_164_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[164])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_163_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[163])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_162_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[162])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_161_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[161])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_160_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[160])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_159_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[159])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_158_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[158])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_157_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[157])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_156_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[156])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_155_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[155])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_154_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[154])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_153_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[153])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_152_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[152])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_151_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[151])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_150_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[150])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_149_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[149])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_148_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[148])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_147_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[147])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_146_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[146])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_145_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[145])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_144_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[144])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_143_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[143])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_142_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[142])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_141_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[141])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_140_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[140])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_139_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[139])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_138_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[138])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_137_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[137])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_136_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[136])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_135_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[135])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_134_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[134])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_133_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[133])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_132_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[132])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_131_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[131])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_130_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[130])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_129_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[129])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_128_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[128])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_127_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[127])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_126_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[126])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_125_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[125])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_124_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[124])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_123_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[123])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_122_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[122])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_121_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[121])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_120_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[120])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_119_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[119])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_118_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[118])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_117_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[117])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_116_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[116])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_115_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[115])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_114_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[114])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_113_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[113])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_112_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[112])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_111_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[111])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_110_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[110])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_109_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[109])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_108_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[108])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_107_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[107])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_106_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[106])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_105_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[105])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_104_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[104])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_103_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[103])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_102_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[102])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_101_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[101])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_100_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[100])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_99_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[99])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_98_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[98])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_97_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[97])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_96_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[96])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_95_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[95])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_94_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[94])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_93_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[93])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_92_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[92])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_91_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[91])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_90_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[90])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_89_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[89])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_88_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[88])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_87_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[87])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_86_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[86])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_85_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[85])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_84_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[84])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_83_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[83])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_82_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[82])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_81_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[81])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_80_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[80])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_79_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[79])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_78_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[78])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_77_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[77])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_76_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[76])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_75_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[75])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_74_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[74])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_73_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[73])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_72_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[72])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_71_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[71])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_70_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[70])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_69_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[69])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_68_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[68])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_67_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[67])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_66_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[66])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_65_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[65])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_64_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[64])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_63_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[63])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_62_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[62])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_61_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[61])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_60_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[60])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_59_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[59])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_58_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[58])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_57_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[57])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_56_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[56])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_55_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[55])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_54_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[54])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_53_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[53])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_52_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[52])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_51_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[51])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_50_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[50])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_49_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[49])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_48_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[48])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_47_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[47])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_46_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[46])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_45_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[45])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_44_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[44])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_43_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[43])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_42_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[42])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_41_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[41])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_40_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[40])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_39_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[39])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_38_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[38])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_37_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[37])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_36_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[36])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_35_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[35])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_34_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[34])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_33_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[33])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_32_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[32])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_31_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[31])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_30_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[30])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_29_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[29])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_28_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[28])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_27_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[27])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_26_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[26])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_25_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[25])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_24_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[24])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_23_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[23])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_22_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[22])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_21_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[21])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_20_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[20])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_19_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[19])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_18_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[18])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_17_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[17])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_16_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[16])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_15_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[15])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_14_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[14])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_13_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[13])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_12_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[12])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_11_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[11])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_10_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[10])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_9_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[9])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_8_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[8])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_7_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[7])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_6_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[6])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_5_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[5])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_4_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[4])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_3_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[3])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_2_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[2])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_1_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[1])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_0_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(), .i_a(edt_scan_in[0])
  );

  axe_tcl_std_buffer tessent_scan_buf_o_449_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_448_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts1), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_447_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts2), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_446_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts3), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_445_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts4), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_444_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts5), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_443_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts6), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_442_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts7), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_441_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts8), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_440_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts9), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_439_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts10), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_438_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts11), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_437_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts12), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_436_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts13), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_435_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts14), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_434_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts15), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_433_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts16), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_432_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts17), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_431_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts18), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_430_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts19), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_429_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts20), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_428_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts21), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_427_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts22), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_426_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts23), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_425_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts24), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_424_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts25), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_423_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts26), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_422_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts27), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_421_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts28), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_420_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts29), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_419_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts30), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_418_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts31), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_417_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts32), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_416_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts33), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_415_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts34), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_414_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts35), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_413_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts36), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_412_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts37), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_411_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts38), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_410_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts39), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_409_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts40), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_408_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts41), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_407_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts42), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_406_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts43), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_405_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts44), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_404_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts45), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_403_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts46), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_402_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts47), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_401_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts48), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_400_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts49), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_399_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts50), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_398_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts51), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_397_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts52), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_396_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts53), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_395_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts54), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_394_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts55), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_393_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts56), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_392_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts57), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_391_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts58), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_390_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts59), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_389_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts60), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_388_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts61), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_387_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts62), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_386_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts63), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_385_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts64), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_384_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts65), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_383_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts66), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_382_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts67), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_381_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts68), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_380_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts69), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_379_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts70), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_378_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts71), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_377_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts72), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_376_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts73), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_375_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts74), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_374_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts75), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_373_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts76), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_372_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts77), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_371_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts78), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_370_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts79), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_369_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts80), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_368_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts81), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_367_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts82), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_366_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts83), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_365_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts84), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_364_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts85), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_363_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts86), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_362_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts87), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_361_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts88), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_360_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts89), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_359_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts90), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_358_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts91), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_357_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts92), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_356_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts93), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_355_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts94), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_354_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts95), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_353_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts96), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_352_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts97), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_351_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts98), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_350_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts99), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_349_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts100), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_348_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts101), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_347_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts102), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_346_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts103), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_345_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts104), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_344_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts105), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_343_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts106), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_342_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts107), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_341_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts108), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_340_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts109), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_339_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts110), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_338_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts111), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_337_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts112), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_336_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts113), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_335_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts114), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_334_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts115), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_333_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts116), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_332_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts117), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_331_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts118), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_330_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts119), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_329_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts120), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_328_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts121), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_327_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts122), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_326_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts123), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_325_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts124), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_324_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts125), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_323_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts126), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_322_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts127), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_321_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts128), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_320_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts129), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_319_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts130), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_318_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts131), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_317_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts132), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_316_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts133), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_315_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts134), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_314_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts135), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_313_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts136), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_312_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts137), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_311_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts138), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_310_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts139), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_309_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts140), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_308_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts141), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_307_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts142), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_306_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts143), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_305_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts144), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_304_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts145), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_303_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts146), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_302_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts147), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_301_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts148), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_300_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts149), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_299_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts150), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_298_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts151), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_297_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts152), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_296_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts153), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_295_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts154), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_294_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts155), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_293_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts156), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_292_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts157), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_291_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts158), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_290_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts159), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_289_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts160), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_288_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts161), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_287_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts162), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_286_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts163), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_285_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts164), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_284_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts165), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_283_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts166), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_282_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts167), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_281_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts168), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_280_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts169), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_279_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts170), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_278_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts171), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_277_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts172), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_276_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts173), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_275_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts174), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_274_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts175), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_273_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts176), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_272_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts177), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_271_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts178), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_270_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts179), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_269_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts180), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_268_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts181), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_267_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts182), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_266_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts183), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_265_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts184), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_264_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts185), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_263_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts186), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_262_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts187), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_261_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts188), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_260_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts189), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_259_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts190), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_258_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts191), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_257_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts192), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_256_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts193), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_255_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts194), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_254_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts195), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_253_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts196), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_252_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts197), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_251_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts198), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_250_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts199), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_249_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts200), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_248_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts201), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_247_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts202), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_246_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts203), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_245_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts204), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_244_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts205), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_243_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts206), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_242_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts207), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_241_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts208), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_240_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts209), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_239_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts210), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_238_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts211), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_237_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts212), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_236_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts213), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_235_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts214), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_234_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts215), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_233_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts216), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_232_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts217), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_231_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts218), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_230_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts219), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_229_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts220), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_228_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts221), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_227_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts222), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_226_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts223), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_225_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts224), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_224_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts225), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_223_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts226), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_222_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts227), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_221_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts228), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_220_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts229), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_219_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts230), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_218_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts231), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_217_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts232), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_216_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts233), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_215_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts234), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_214_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts235), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_213_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts236), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_212_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts237), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_211_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts238), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_210_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts239), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_209_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts240), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_208_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts241), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_207_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts242), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_206_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts243), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_205_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts244), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_204_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts245), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_203_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts246), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_202_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts247), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_201_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts248), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_200_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts249), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_199_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts250), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_198_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts251), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_197_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts252), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_196_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts253), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_195_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts254), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_194_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts255), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_193_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts256), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_192_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts257), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_191_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts258), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_190_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts259), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_189_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts260), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_188_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts261), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_187_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts262), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_186_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts263), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_185_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts264), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_184_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts265), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_183_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts266), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_182_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts267), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_181_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts268), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_180_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts269), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_179_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts270), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_178_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts271), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_177_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts272), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_176_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts273), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_175_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts274), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_174_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts275), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_173_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts276), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_172_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts277), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_171_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts278), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_170_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts279), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_169_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts280), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_168_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts281), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_167_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts282), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_166_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts283), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_165_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts284), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_164_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts285), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_163_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts286), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_162_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts287), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_161_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts288), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_160_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts289), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_159_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts290), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_158_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts291), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_157_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts292), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_156_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts293), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_155_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts294), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_154_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts295), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_153_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts296), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_152_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts297), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_151_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts298), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_150_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts299), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_149_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts300), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_148_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts301), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_147_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts302), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_146_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts303), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_145_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts304), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_144_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts305), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_143_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts306), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_142_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts307), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_141_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts308), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_140_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts309), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_139_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts310), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_138_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts311), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_137_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts312), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_136_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts313), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_135_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts314), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_134_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts315), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_133_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts316), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_132_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts317), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_131_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts318), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_130_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts319), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_129_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts320), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_128_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts321), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_127_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts322), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_126_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts323), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_125_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts324), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_124_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts325), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_123_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts326), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_122_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts327), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_121_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts328), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_120_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts329), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_119_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts330), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_118_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts331), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_117_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts332), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_116_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts333), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_115_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts334), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_114_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts335), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_113_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts336), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_112_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts337), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_111_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts338), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_110_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts339), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_109_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts340), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_108_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts341), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_107_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts342), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_106_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts343), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_105_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts344), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_104_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts345), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_103_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts346), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_102_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts347), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_101_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts348), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_100_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts349), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_99_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts350), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_98_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts351), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_97_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts352), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_96_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts353), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_95_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts354), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_94_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts355), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_93_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts356), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_92_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts357), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_91_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts358), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_90_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts359), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_89_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts360), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_88_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts361), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_87_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts362), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_86_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts363), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_85_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts364), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_84_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts365), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_83_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts366), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_82_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts367), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_81_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts368), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_80_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts369), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_79_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts370), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_78_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts371), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_77_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts372), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_76_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts373), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_75_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts374), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_74_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts375), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_73_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts376), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_72_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts377), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_71_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts378), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_70_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts379), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_69_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts380), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_68_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts381), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_67_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts382), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_66_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts383), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_65_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts384), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_64_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts385), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_63_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts386), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_62_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts387), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_61_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts388), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_60_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts389), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_59_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts390), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_58_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts391), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_57_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts392), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_56_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts393), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_55_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts394), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_54_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts395), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_53_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts396), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_52_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts397), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_51_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts398), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_50_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts399), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_49_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts400), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_48_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts401), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_47_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts402), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_46_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts403), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_45_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts404), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_44_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts405), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_43_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts406), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_42_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts407), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_41_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts408), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_40_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts409), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_39_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts410), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_38_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts411), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_37_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts412), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_36_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts413), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_35_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts414), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_34_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts415), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_33_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts416), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_32_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts417), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_31_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts418), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_30_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts419), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_29_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts420), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_28_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts421), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_27_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts422), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_26_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts423), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_25_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts424), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_24_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts425), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_23_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts426), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_22_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts427), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_21_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts428), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_20_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts429), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_19_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts430), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_18_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts431), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_17_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts432), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_16_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts433), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_15_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts434), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_14_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts435), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_13_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts436), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_12_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts437), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_11_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts438), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_10_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts439), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_9_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts440), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_8_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts441), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_7_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts442), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_6_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts443), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_5_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts444), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_4_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts445), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_3_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts446), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_2_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts447), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_1_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts448), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_0_lpddr_p_rtl2_tessent_edt_c1_int_inst(
      .o_z(o_z_ts449), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_i_10_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[10])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_9_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[9])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_8_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[8])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_7_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[7])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_6_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[6])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_5_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[5])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_4_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[4])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_3_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[3])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_2_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[2])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_1_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[1])
  );

  axe_tcl_std_buffer tessent_scan_buf_i_0_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(), .i_a(edt_scan_in_ts1[0])
  );

  axe_tcl_std_buffer tessent_scan_buf_o_10_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts450), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_9_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts451), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_8_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts452), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_7_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts453), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_6_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts454), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_5_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts455), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_4_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts456), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_3_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts457), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_2_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts458), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_1_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts459), .i_a()
  );

  axe_tcl_std_buffer tessent_scan_buf_o_0_lpddr_p_rtl2_tessent_edt_cx_inst(
      .o_z(o_z_ts460), .i_a()
  );
endmodule
