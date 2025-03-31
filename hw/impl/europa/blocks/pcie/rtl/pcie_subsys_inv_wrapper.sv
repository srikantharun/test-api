// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Inverse wrapper of pcie_p to return to snps names as much as possible and bypass pcie_p wrapper logic when required.
// Owner: Milos Stanisavljevic

module pcie_subsys_inv_wrapper 
  import chip_pkg::*;
  import axi_pkg::*;
  import pcie_pkg::*;
(
// Clock and Reset Signals
  input                                     aux_clk,
  output                                    o_core_clk,
  output                                    o_muxd_aux_clk,

  output                                    local_ref_clk_req_n,
  input                                     clkreq_in_n,
  input                                     power_up_rst_n,
  input                                     perst_n,
  output                                    o_core_rst_n,
  output                                    o_pwr_rst_n,

  // AXI Clock and Reset Signals

  output                                    o_mstr_aresetn,

  output                                    o_slv_aresetn,

  output                                    o_dbi_aresetn,
  // APB Clock interface Signals
  input                                     apb_pclk,
  input                                     apb_presetn,

  // AXI Master interface
  output                                    mstr_awvalid,
  output [       PCIE_INIT_MT_AXI_ID_W-1:0] mstr_awid,
  output [                            63:0] mstr_awaddr,
  output [               AXI_LEN_WIDTH-1:0] mstr_awlen,
  output [                             2:0] mstr_awsize,
  output [                             1:0] mstr_awburst,
  output                                    mstr_awlock,
  output [                             3:0] mstr_awcache,
  output [                             2:0] mstr_awprot,
  output [                             3:0] mstr_awqos,
  input                                     mstr_awready,
  output [                            49:0] mstr_awmisc_info,
  output                                    mstr_awmisc_info_last_dcmp_tlp,
  output [                            63:0] mstr_awmisc_info_hdr_34dw,
  output [                             4:0] mstr_awmisc_info_dma,
  output                                    mstr_awmisc_info_ep,
  output                                    mstr_awmisc_info_nw,
  output [                             1:0] mstr_awmisc_info_ats,

  output                                    mstr_wvalid,
  output [     PCIE_INIT_MT_AXI_DATA_W-1:0] mstr_wdata,
  output [     PCIE_INIT_MT_AXI_STRB_W-1:0] mstr_wstrb,
  output                                    mstr_wlast,
  input                                     mstr_wready,
     
  input                                     mstr_bvalid,
  input  [       PCIE_INIT_MT_AXI_ID_W-1:0] mstr_bid,
  input  [              AXI_RESP_WIDTH-1:0] mstr_bresp,
  output                                    mstr_bready,
  input  [                             2:0] mstr_bmisc_info_cpl_stat,

  output                                    mstr_arvalid,
  output [       PCIE_INIT_MT_AXI_ID_W-1:0] mstr_arid,
  output [                            63:0] mstr_araddr,
  output [               AXI_LEN_WIDTH-1:0] mstr_arlen,
  output [                             2:0] mstr_arsize,
  output [                             1:0] mstr_arburst,
  output                                    mstr_arlock,
  output [                             3:0] mstr_arcache,
  output [                             2:0] mstr_arprot,
  output [                             3:0] mstr_arqos,
  input                                     mstr_arready,
  output [                            49:0] mstr_armisc_info,
  output                                    mstr_armisc_info_last_dcmp_tlp,
  output [                             4:0] mstr_armisc_info_dma,
  output                                    mstr_armisc_info_zeroread,
  output                                    mstr_armisc_info_nw,
  output [                             1:0] mstr_armisc_info_ats,

  input                                     mstr_rvalid,
  input  [       PCIE_INIT_MT_AXI_ID_W-1:0] mstr_rid,
  input                                     mstr_rlast,
  input  [     PCIE_INIT_MT_AXI_DATA_W-1:0] mstr_rdata,
  input  [                             1:0] mstr_rresp,
  output                                    mstr_rready,
  input  [                            12:0] mstr_rmisc_info,
  input  [                             2:0] mstr_rmisc_info_cpl_stat,

  input                                     mstr_aclk,

  // AXI Slave interface
  input                                     slv_awvalid,
  input  [       PCIE_TARG_MT_AXI_ID_W-1:0] slv_awid,
  input  [                            63:0] slv_awaddr,
  input  [               AXI_LEN_WIDTH-1:0] slv_awlen,
  input  [                             2:0] slv_awsize,
  input  [                             1:0] slv_awburst,
  input                                     slv_awlock,
  input  [                             3:0] slv_awcache,
  input  [                             2:0] slv_awprot,
  input  [                             3:0] slv_awqos,
  output                                    slv_awready,
  input  [                            21:0] slv_awmisc_info,
  input  [                            63:0] slv_awmisc_info_hdr_34dw,
  input  [                             9:0] slv_awmisc_info_p_tag,
  input                                     slv_awmisc_info_atu_bypass,
  input                                     slv_awmisc_info_nw,
  input  [                             1:0] slv_awmisc_info_ats,

  input                                     slv_wvalid,
  input  [     PCIE_TARG_MT_AXI_DATA_W-1:0] slv_wdata,
  input  [     PCIE_TARG_MT_AXI_STRB_W-1:0] slv_wstrb,
  input                                     slv_wlast,
  output                                    slv_wready,
  input                                     slv_wmisc_info_ep,
  input                                     slv_wmisc_info_silentDrop,

  output                                    slv_bvalid,
  output [       PCIE_TARG_MT_AXI_ID_W-1:0] slv_bid,
  output [              AXI_RESP_WIDTH-1:0] slv_bresp,
  input                                     slv_bready,
  output [                            10:0] slv_bmisc_info,

  input                                     slv_arvalid,
  input  [       PCIE_TARG_MT_AXI_ID_W-1:0] slv_arid,
  input  [                            63:0] slv_araddr,
  input  [               AXI_LEN_WIDTH-1:0] slv_arlen,
  input  [                             2:0] slv_arsize,
  input  [                             1:0] slv_arburst,
  input                                     slv_arlock,
  input  [                             3:0] slv_arcache,
  input  [                             2:0] slv_arprot,
  input  [                             3:0] slv_arqos,
  output                                    slv_arready,
  input  [                            21:0] slv_armisc_info,
  input                                     slv_armisc_info_atu_bypass,
  input                                     slv_armisc_info_nw,
  input  [                             1:0] slv_armisc_info_ats,

  output                                    slv_rvalid,
  output [       PCIE_TARG_MT_AXI_ID_W-1:0] slv_rid,
  output [     PCIE_TARG_MT_AXI_DATA_W-1:0] slv_rdata,
  output [                             1:0] slv_rresp,
  output                                    slv_rlast,
  input                                     slv_rready,
  output [                            10:0] slv_rmisc_info,

  input                                     slv_aclk,

  // Subordinate DBI interfaces of AXI
  input                                     dbi_awvalid,
  input  [  PCIE_TARG_CFG_DBI_AXI_ID_W-1:0] dbi_awid,
  input  [                            31:0] dbi_awaddr,
  input  [               AXI_LEN_WIDTH-1:0] dbi_awlen,
  input  [                             2:0] dbi_awsize,
  input  [                             1:0] dbi_awburst,
  input                                     dbi_awlock,
  input  [                             3:0] dbi_awcache,
  input  [                             2:0] dbi_awprot,
  input  [                             3:0] dbi_awqos,
  output                                    dbi_awready,

  input                                     dbi_wvalid,
  input  [PCIE_TARG_CFG_DBI_AXI_DATA_W-1:0] dbi_wdata,
  input  [PCIE_TARG_CFG_DBI_AXI_STRB_W-1:0] dbi_wstrb,
  input                                     dbi_wlast,
  output                                    dbi_wready,

  output                                    dbi_bvalid,
  output [  PCIE_TARG_CFG_DBI_AXI_ID_W-1:0] dbi_bid,
  output [                             1:0] dbi_bresp,
  input                                     dbi_bready,

  input                                     dbi_arvalid,
  input  [  PCIE_TARG_CFG_DBI_AXI_ID_W-1:0] dbi_arid,
  input  [                            31:0] dbi_araddr,
  input  [               AXI_LEN_WIDTH-1:0] dbi_arlen,
  input  [                             2:0] dbi_arsize,
  input  [                             1:0] dbi_arburst,
  input                                     dbi_arlock,
  input  [                             3:0] dbi_arcache,
  input  [                             2:0] dbi_arprot,
  input  [                             3:0] dbi_arqos,
  output                                    dbi_arready,

  output                                    dbi_rvalid,
  output [  PCIE_TARG_CFG_DBI_AXI_ID_W-1:0] dbi_rid,
  output [PCIE_TARG_CFG_DBI_AXI_DATA_W-1:0] dbi_rdata,
  output [                             1:0] dbi_rresp,
  output                                    dbi_rlast,
  input                                     dbi_rready,

  input                                     dbi_aclk,

  // Hot reset request
  output                                    smlh_req_rst_not,

  // MSI interface
  input  [                            31:0] msi_int,
  // Misc Interrupt Signal
  input                                     sys_int,
  output                                    pcie_int,
  output [                            15:0] pcie_dbg_signal,


  // FLR interface
  output                                    wake,
  // Test Signals
  input                                     mac_scan_mode,
  input                                     mac_scan_rst_n,
  input                                     mac_scan_shift,
  input                                     mac_scan_shift_cg,
  input                                     mac_scan_coreclk,


  // Boundary Scan Port Signals
  input                                     phy_bs_acmode,
  input                                     phy_bs_actest,
  input                                     phy_bs_cdr,
  input                                     phy_bs_ce,
  input                                     phy_bs_rx_bigswing,
  input                                     phy_bs_rx_init,
  input  [                             4:0] phy_bs_rx_level,
  input                                     phy_bs_sdr,
  input                                     phy_bs_tdi,
  output                                    phy_bs_tdo,
  input                                     phy_bs_tx_lowswing,
  input                                     phy_bs_udr,

  // JTAG Port
  input                                     phy0_jtag_tck,
  input                                     phy0_jtag_tdi,
  output                                    phy0_jtag_tdo,
  output                                    phy0_jtag_tdo_en,
  input                                     phy0_jtag_tms,
  input                                     phy0_jtag_trst_n,

  // PCS Scan Interface
  input                                     pcs_scan_clk,
  input                                     pcs_scan_clk_sel,
  input                                     pcs_scan_mode,
  input                                     pcs_scan_pclk,
  input                                     pcs_scan_pcs_clk,
  input                                     pcs_scan_pma_clk,
  input                                     pcs_scan_rst,
  input                                     pcs_scan_shift,
  input                                     pcs_scan_shift_cg,

  // PHY Scan Interface
  input                                     phy0_scan_mode,
  input                                     phy0_scan_clk,
  input                                     phy0_scan_clk_sel,
  input                                     phy0_scan_cr_clk,
  input                                     phy0_scan_mpll_dword_clk,
  input                                     phy0_scan_mpll_qword_clk,
  input                                     phy0_scan_rx_dword_clk,
  input                                     phy0_scan_occ_clk,
  input                                     phy0_scan_ref_clk,
  input                                     phy0_scan_set_rst,
  input                                     phy0_scan_shift,
  input                                     phy0_scan_shift_cg,
  input                                     phy0_scan_pma_occ_en,

  input  [                 PHY_SCAN_CR-1:0] phy0_scan_cr_in,
  output [                 PHY_SCAN_CR-1:0] phy0_scan_cr_out,
  input  [                 PHY_SCAN_CR-1:0] phy0_scan_mpll_dword_in,
  output [                 PHY_SCAN_CR-1:0] phy0_scan_mpll_dword_out,
  input  [         PHY_SCAN_MPLL_QWORD-1:0] phy0_scan_mpll_qword_in,
  output [         PHY_SCAN_MPLL_QWORD-1:0] phy0_scan_mpll_qword_out,
  input  [           PHY_SCAN_RX_DWORD-1:0] phy0_scan_rx_dword_in,
  output [           PHY_SCAN_RX_DWORD-1:0] phy0_scan_rx_dword_out,
  input  [                PHY_SCAN_OCC-1:0] phy0_scan_occ_in,
  output [                PHY_SCAN_OCC-1:0] phy0_scan_occ_out,
  input  [                PHY_SCAN_REF-1:0] phy0_scan_ref_in,
  output [                PHY_SCAN_REF-1:0] phy0_scan_ref_out,

  input  [                             1:0] phy0_scan_apb0_in,
  output [                             1:0] phy0_scan_apb0_out,
  input                                     phy0_scan_apb1_in,
  output                                    phy0_scan_apb1_out,
  input                                     phy0_scan_fw_in,
  output                                    phy0_scan_fw_out,
  input  [               PHY_SCAN_JTAG-1:0] phy0_scan_jtag_in,
  output [               PHY_SCAN_JTAG-1:0] phy0_scan_jtag_out,

  input                                     phy_test_burnin,
  input                                     phy_test_powerdown,
  input                                     phy_test_stop_clk_en,
  input                                     phy_test_tx_ref_clk_en,
  input                                     phy0_test_flyover_en,

  input                                     phy_apb0_if_sel,

  // Signals 
  input                                     tap_phy0_ref_use_pad,
  input                                     tap_phy0_reset,
  input                                     ate_test_mode,

  output [                             1:0] phy0_dtb_out,

  input                                     phy_fw_clk,

  // APB Slave Signals
  output                                    apbslv_active,
  input                                     apbslv_psel,
  input                                     apbslv_penable,
  input  [                            31:0] apbslv_paddr,
  input                                     apbslv_pwrite,
  input  [                             3:0] apbslv_pstrb,
  input  [                            31:0] apbslv_pwdata,
  output                                    apbslv_pready,
  output                                    apbslv_pslverr,
  output [                            31:0] apbslv_prdata,

  // DFT ports 
  input  [                           899:0] snps_scan_in,
  output [                           899:0] snps_scan_out,

  // PHY Pads
  inout                                     resref, 
  input                                     ref_pad_clk_p, 
  input                                     ref_pad_clk_m, 
  input                                     ref_alt_clk_p, 
  
  input  [                             3:0] rxp,
  input  [                             3:0] rxm,
  output [                             3:0] txp,
  output [                             3:0] txm
);

  pcie_p pcie_top_wrapper (
    // Global Clock and Reset Signals
    // Ref Clock, positive edge triggered
    .i_ref_clk(aux_clk),
    // Asynchronous POR / always On reset, active low
    .i_ao_rst_n(power_up_rst_n),
    // Asynchronous global reset, active low
    .i_global_rst_n(power_up_rst_n),
    // NoC Control Signals
    .o_noc_async_idle_init_mt_axi_req     (  ),
    .o_noc_async_idle_targ_mt_axi_req     (  ),
    .o_noc_async_idle_targ_cfg_dbi_axi_req(  ),
    .o_noc_async_idle_targ_cfg_apb_req    (  ),
    .i_noc_async_idle_init_mt_axi_ack     ('0),
    .i_noc_async_idle_targ_mt_axi_ack     ('0),
    .i_noc_async_idle_targ_cfg_dbi_axi_ack('0),
    .i_noc_async_idle_targ_cfg_apb_ack    ('0),
    .i_noc_async_idle_init_mt_axi_val     ('0),
    .i_noc_async_idle_targ_mt_axi_val     ('0),
    .i_noc_async_idle_targ_cfg_dbi_axi_val('0),
    .i_noc_async_idle_targ_cfg_apb_val    ('0),
    .o_noc_init_mt_axi_clken              (  ),
    .o_noc_targ_mt_axi_clken              (  ),
    .o_noc_targ_cfg_dbi_axi_clken         (  ),
    .o_noc_targ_cfg_apb_clken             (  ),
    .o_noc_rst_n                          (  ),
    // PCIe Auxilary Clock
    .i_pcie_aux_clk(aux_clk),
    // AXI Clock and Reset Signals
    .i_pcie_init_mt_axi_clk       (mstr_aclk),
    .i_pcie_targ_mt_axi_clk       (slv_aclk),
    .i_pcie_targ_cfg_dbi_axi_clk  (dbi_aclk),
    .o_pcie_init_mt_axi_rst_n     (o_mstr_aresetn),
    .o_pcie_targ_mt_axi_rst_n     (o_slv_aresetn),
    .o_pcie_targ_cfg_dbi_axi_rst_n(o_dbi_aresetn),
    // APB Clock
    .i_apb_pclk(apb_pclk),
    // PHY Alternative Clock
    .i_ref_alt_clk_p(ref_alt_clk_p),
    // PHY Pads
    .io_pcie_resref (resref),
    .i_ref_pad_clk_p(ref_pad_clk_p),
    .i_ref_pad_clk_m(ref_pad_clk_m),
    .i_pcie_rxm_00  (rxm[0]),
    .i_pcie_rxm_01  (rxm[1]),
    .i_pcie_rxm_02  (rxm[2]),
    .i_pcie_rxm_03  (rxm[3]),
    .i_pcie_rxp_00  (rxp[0]),
    .i_pcie_rxp_01  (rxp[1]),
    .i_pcie_rxp_02  (rxp[2]),
    .i_pcie_rxp_03  (rxp[3]),
    .o_pcie_txm_00  (txm[0]),
    .o_pcie_txm_01  (txm[1]),
    .o_pcie_txm_02  (txm[2]),
    .o_pcie_txm_03  (txm[3]),
    .o_pcie_txp_00  (txp[0]),
    .o_pcie_txp_01  (txp[1]),
    .o_pcie_txp_02  (txp[2]),
    .o_pcie_txp_03  (txp[3]),

    // AXI M Interface Signals
    // AW
    .o_pcie_init_mt_axi_awvalid (mstr_awvalid),
    .o_pcie_init_mt_axi_awid    (mstr_awid   ),
    .o_pcie_init_mt_axi_awaddr  (mstr_awaddr[CHIP_AXI_ADDR_W-1:0]),
    .o_pcie_init_mt_axi_awlen   (mstr_awlen  ),
    .o_pcie_init_mt_axi_awsize  (mstr_awsize ),
    .o_pcie_init_mt_axi_awburst (mstr_awburst),
    .o_pcie_init_mt_axi_awlock  (mstr_awlock ),
    .o_pcie_init_mt_axi_awcache (mstr_awcache),
    .o_pcie_init_mt_axi_awprot  (mstr_awprot ),
    .o_pcie_init_mt_axi_awqos   (mstr_awqos  ),
    .o_pcie_init_mt_axi_awregion(            ),
    .o_pcie_init_mt_axi_awuser  (            ),
    .i_pcie_init_mt_axi_awready (mstr_awready),
    // W
    .o_pcie_init_mt_axi_wvalid  (mstr_wvalid),
    .o_pcie_init_mt_axi_wdata   (mstr_wdata ),
    .o_pcie_init_mt_axi_wstrb   (mstr_wstrb ),
    .o_pcie_init_mt_axi_wlast   (mstr_wlast ),
    .o_pcie_init_mt_axi_wuser   (           ),
    .i_pcie_init_mt_axi_wready  (mstr_wready),
    // B
    .i_pcie_init_mt_axi_bvalid  (mstr_bvalid),
    .i_pcie_init_mt_axi_bid     (mstr_bid   ),
    .i_pcie_init_mt_axi_bresp   (mstr_bresp ),
    .i_pcie_init_mt_axi_buser   ('0         ),
    .o_pcie_init_mt_axi_bready  (mstr_bready),
    // AR
    .o_pcie_init_mt_axi_arvalid (mstr_arvalid),
    .o_pcie_init_mt_axi_arid    (mstr_arid   ),
    .o_pcie_init_mt_axi_araddr  (mstr_araddr[CHIP_AXI_ADDR_W-1:0]),
    .o_pcie_init_mt_axi_arlen   (mstr_arlen  ),
    .o_pcie_init_mt_axi_arsize  (mstr_arsize ),
    .o_pcie_init_mt_axi_arburst (mstr_arburst),
    .o_pcie_init_mt_axi_arlock  (mstr_arlock ),
    .o_pcie_init_mt_axi_arcache (mstr_arcache),
    .o_pcie_init_mt_axi_arprot  (mstr_arprot ),
    .o_pcie_init_mt_axi_arqos   (mstr_arqos  ),
    .o_pcie_init_mt_axi_arregion(            ),
    .o_pcie_init_mt_axi_aruser  (            ),
    .i_pcie_init_mt_axi_arready (mstr_arready),
    // R
    .i_pcie_init_mt_axi_rvalid  (mstr_rvalid),
    .i_pcie_init_mt_axi_rid     (mstr_rid   ),
    .i_pcie_init_mt_axi_rdata   (mstr_rdata ),
    .i_pcie_init_mt_axi_rresp   (mstr_rresp ),
    .i_pcie_init_mt_axi_rlast   (mstr_rlast ),
    .i_pcie_init_mt_axi_ruser   ('0         ),
    .o_pcie_init_mt_axi_rready  (mstr_rready),
    // AXI M Interface Signals
    // AW
    .i_pcie_targ_mt_axi_awvalid (slv_awvalid),
    .i_pcie_targ_mt_axi_awid    (slv_awid   ),
    .i_pcie_targ_mt_axi_awaddr  (slv_awaddr[CHIP_AXI_ADDR_W-1:0]),
    .i_pcie_targ_mt_axi_awlen   (slv_awlen  ),
    .i_pcie_targ_mt_axi_awsize  (slv_awsize ),
    .i_pcie_targ_mt_axi_awburst (slv_awburst),
    .i_pcie_targ_mt_axi_awlock  (slv_awlock ),
    .i_pcie_targ_mt_axi_awcache (slv_awcache),
    .i_pcie_targ_mt_axi_awprot  (slv_awprot ),
    .i_pcie_targ_mt_axi_awqos   (slv_awqos  ),
    .i_pcie_targ_mt_axi_awregion('0         ),
    .i_pcie_targ_mt_axi_awuser  ('0         ),
    .o_pcie_targ_mt_axi_awready (slv_awready),
    // W
    .i_pcie_targ_mt_axi_wvalid  (slv_wvalid),
    .i_pcie_targ_mt_axi_wdata   (slv_wdata ),
    .i_pcie_targ_mt_axi_wstrb   (slv_wstrb ),
    .i_pcie_targ_mt_axi_wlast   (slv_wlast ),
    .i_pcie_targ_mt_axi_wuser   ('0        ),
    .o_pcie_targ_mt_axi_wready  (slv_wready),
    // B
    .o_pcie_targ_mt_axi_bvalid  (slv_bvalid),
    .o_pcie_targ_mt_axi_bid     (slv_bid   ),
    .o_pcie_targ_mt_axi_bresp   (slv_bresp ),
    .o_pcie_targ_mt_axi_buser   (          ),
    .i_pcie_targ_mt_axi_bready  (slv_bready),
    // AR
    .i_pcie_targ_mt_axi_arvalid (slv_arvalid),
    .i_pcie_targ_mt_axi_arid    (slv_arid   ),
    .i_pcie_targ_mt_axi_araddr  (slv_araddr[CHIP_AXI_ADDR_W-1:0]),
    .i_pcie_targ_mt_axi_arlen   (slv_arlen  ),
    .i_pcie_targ_mt_axi_arsize  (slv_arsize ),
    .i_pcie_targ_mt_axi_arburst (slv_arburst),
    .i_pcie_targ_mt_axi_arlock  (slv_arlock ),
    .i_pcie_targ_mt_axi_arcache (slv_arcache),
    .i_pcie_targ_mt_axi_arprot  (slv_arprot ),
    .i_pcie_targ_mt_axi_arqos   (slv_arqos  ),
    .i_pcie_targ_mt_axi_arregion('0         ),
    .i_pcie_targ_mt_axi_aruser  ('0         ),
    .o_pcie_targ_mt_axi_arready (slv_arready),
    // R
    .o_pcie_targ_mt_axi_rvalid  (slv_rvalid),
    .o_pcie_targ_mt_axi_rid     (slv_rid   ),
    .o_pcie_targ_mt_axi_rdata   (slv_rdata ),
    .o_pcie_targ_mt_axi_rresp   (slv_rresp ),
    .o_pcie_targ_mt_axi_rlast   (slv_rlast ),
    .o_pcie_targ_mt_axi_ruser   (          ),
    .i_pcie_targ_mt_axi_rready  (slv_rready),
    // AXI S DBI Interface Signals
    // AW
    .i_pcie_targ_cfg_dbi_axi_awvalid (dbi_awvalid),
    .i_pcie_targ_cfg_dbi_axi_awid    (dbi_awid   ),
    .i_pcie_targ_cfg_dbi_axi_awaddr  ({{CHIP_AXI_ADDR_W-32{1'b0}}, dbi_awaddr}),
    .i_pcie_targ_cfg_dbi_axi_awlen   (dbi_awlen  ),
    .i_pcie_targ_cfg_dbi_axi_awsize  (dbi_awsize ),
    .i_pcie_targ_cfg_dbi_axi_awburst (dbi_awburst),
    .i_pcie_targ_cfg_dbi_axi_awlock  (dbi_awlock ),
    .i_pcie_targ_cfg_dbi_axi_awcache (dbi_awcache),
    .i_pcie_targ_cfg_dbi_axi_awprot  (dbi_awprot ),
    .i_pcie_targ_cfg_dbi_axi_awqos   (dbi_awqos  ),
    .i_pcie_targ_cfg_dbi_axi_awregion('0         ),
    .i_pcie_targ_cfg_dbi_axi_awuser  ('0         ),
    .o_pcie_targ_cfg_dbi_axi_awready (dbi_awready),
    // W
    .i_pcie_targ_cfg_dbi_axi_wvalid  (dbi_wvalid),
    .i_pcie_targ_cfg_dbi_axi_wdata   (dbi_wdata ),
    .i_pcie_targ_cfg_dbi_axi_wstrb   (dbi_wstrb ),
    .i_pcie_targ_cfg_dbi_axi_wlast   (dbi_wlast ),
    .i_pcie_targ_cfg_dbi_axi_wuser   ('0        ),
    .o_pcie_targ_cfg_dbi_axi_wready  (dbi_wready),
    // B
    .o_pcie_targ_cfg_dbi_axi_bvalid  (dbi_bvalid),
    .o_pcie_targ_cfg_dbi_axi_bid     (dbi_bid   ),
    .o_pcie_targ_cfg_dbi_axi_bresp   (dbi_bresp ),
    .o_pcie_targ_cfg_dbi_axi_buser   (          ),
    .i_pcie_targ_cfg_dbi_axi_bready  (dbi_bready),
    // AR
    .i_pcie_targ_cfg_dbi_axi_arvalid (dbi_arvalid),
    .i_pcie_targ_cfg_dbi_axi_arid    (dbi_arid   ),
    .i_pcie_targ_cfg_dbi_axi_araddr  ({{CHIP_AXI_ADDR_W-32{1'b0}}, dbi_araddr}),
    .i_pcie_targ_cfg_dbi_axi_arlen   (dbi_arlen  ),
    .i_pcie_targ_cfg_dbi_axi_arsize  (dbi_arsize ),
    .i_pcie_targ_cfg_dbi_axi_arburst (dbi_arburst),
    .i_pcie_targ_cfg_dbi_axi_arlock  (dbi_arlock ),
    .i_pcie_targ_cfg_dbi_axi_arcache (dbi_arcache),
    .i_pcie_targ_cfg_dbi_axi_arprot  (dbi_arprot ),
    .i_pcie_targ_cfg_dbi_axi_arqos   (dbi_arqos  ),
    .i_pcie_targ_cfg_dbi_axi_arregion('0         ),
    .i_pcie_targ_cfg_dbi_axi_aruser  ('0         ),
    .o_pcie_targ_cfg_dbi_axi_arready (dbi_arready),
    // R
    .o_pcie_targ_cfg_dbi_axi_rvalid  (dbi_rvalid),
    .o_pcie_targ_cfg_dbi_axi_rid     (dbi_rid   ),
    .o_pcie_targ_cfg_dbi_axi_rdata   (dbi_rdata ),
    .o_pcie_targ_cfg_dbi_axi_rresp   (dbi_rresp ),
    .o_pcie_targ_cfg_dbi_axi_rlast   (dbi_rlast ),
    .o_pcie_targ_cfg_dbi_axi_ruser   (          ),
    .i_pcie_targ_cfg_dbi_axi_rready  (dbi_rready),
    // APB Config Interface Signals
    .i_pcie_targ_cfg_apb_paddr  (apbslv_paddr[PCIE_TARG_CFG_APB3_ADDR_W-1:0]),
    .i_pcie_targ_cfg_apb_pwdata (apbslv_pwdata ),
    .i_pcie_targ_cfg_apb_pwrite (apbslv_pwrite ),
    .i_pcie_targ_cfg_apb_psel   (apbslv_psel   ),
    .i_pcie_targ_cfg_apb_penable(apbslv_penable),
    .i_pcie_targ_cfg_apb_pstrb  (apbslv_pstrb  ),
    .i_pcie_targ_cfg_apb_pprot  ('0            ),
    .o_pcie_targ_cfg_apb_pready (apbslv_pready ),
    .o_pcie_targ_cfg_apb_prdata (apbslv_prdata ),
    .o_pcie_targ_cfg_apb_pslverr(apbslv_pslverr),
    // APB SysConfig Interface Signals
    .i_pcie_targ_syscfg_apb_paddr  ('0),
    .i_pcie_targ_syscfg_apb_pwdata ('0),
    .i_pcie_targ_syscfg_apb_pwrite ('0),
    .i_pcie_targ_syscfg_apb_psel   ('0),
    .i_pcie_targ_syscfg_apb_penable('0),
    .i_pcie_targ_syscfg_apb_pstrb  ('0),
    .i_pcie_targ_syscfg_apb_pprot  ('0),
    .o_pcie_targ_syscfg_apb_pready (  ),
    .o_pcie_targ_syscfg_apb_prdata (  ),
    .o_pcie_targ_syscfg_apb_pslverr(  ),

    // Interrupts
    .o_pcie_int(pcie_int),
    // Observability signals for PCIe
    .o_pcie_obs(        ),

    /////////////////////////////////////////////
    // DFT
    /////////////////////////////////////////////
    // JTAG
    .tck   (phy0_jtag_tck   ),
    .trst  (phy0_jtag_trst_n),
    .tms   (phy0_jtag_tms   ),
    .tdi   (phy0_jtag_tdi   ),
    .tdo_en(phy0_jtag_tdo_en),
    .tdo   (phy0_jtag_tdo   ),
    // SCAN
    .ssn_bus_clk     (1'b0),
    .ssn_bus_data_in ('0  ),
    .ssn_bus_data_out(    ),
    // BIST
    .bisr_clk     (1'b0),
    .bisr_reset   (1'b0),
    .bisr_shift_en(1'b0),
    .bisr_si      (1'b0),
    .bisr_so      (    )
  );
  assign mstr_awaddr[63:CHIP_AXI_ADDR_W] = '0;
  assign mstr_araddr[63:CHIP_AXI_ADDR_W] = '0;

  // Force the output of the pctl pcie clocks to be exactly the same as the corresponding input clocks to avoid delays between both due to the clock gate in the pctl.
  initial begin
    force pcie_top_wrapper.pcie_aux_clk               = aux_clk;
    force pcie_top_wrapper.pcie_init_mt_axi_aclk      = mstr_aclk;
    force pcie_top_wrapper.pcie_targ_mt_axi_aclk      = slv_aclk;
    force pcie_top_wrapper.pcie_targ_cfg_dbi_axi_aclk = dbi_aclk;
    force pcie_top_wrapper.test_mode                  = ate_test_mode;
  end

  // Force outputs that axelera does not connect in their wrapper, connects to csr or or some other logic to directly connect with the ports of the snps subsys
  initial begin
    force o_core_clk               = pcie_top_wrapper.u_pcie_subsys.o_core_clk;
    force o_muxd_aux_clk           = pcie_top_wrapper.u_pcie_subsys.o_muxd_aux_clk;
    force local_ref_clk_req_n      = pcie_top_wrapper.u_pcie_subsys.local_ref_clk_req_n;
    force o_core_rst_n             = pcie_top_wrapper.u_pcie_subsys.o_core_rst_n;
    force o_pwr_rst_n              = pcie_top_wrapper.u_pcie_subsys.o_pwr_rst_n;
    force smlh_req_rst_not         = pcie_top_wrapper.u_pcie_subsys.smlh_req_rst_not;
    force pcie_dbg_signal          = pcie_top_wrapper.u_pcie_subsys.pcie_dbg_signal;
    force wake                     = pcie_top_wrapper.u_pcie_subsys.wake;
    force phy_bs_tdo               = pcie_top_wrapper.u_pcie_subsys.phy_bs_tdo;
    force phy0_scan_cr_out         = pcie_top_wrapper.u_pcie_subsys.phy0_scan_cr_out;
    force phy0_scan_mpll_dword_out = pcie_top_wrapper.u_pcie_subsys.phy0_scan_mpll_dword_out;
    force phy0_scan_mpll_qword_out = pcie_top_wrapper.u_pcie_subsys.phy0_scan_mpll_qword_out;
    force phy0_scan_rx_dword_out   = pcie_top_wrapper.u_pcie_subsys.phy0_scan_rx_dword_out;
    force phy0_scan_occ_out        = pcie_top_wrapper.u_pcie_subsys.phy0_scan_occ_out;
    force phy0_scan_ref_out        = pcie_top_wrapper.u_pcie_subsys.phy0_scan_ref_out;
    force phy0_scan_apb0_out       = pcie_top_wrapper.u_pcie_subsys.phy0_scan_apb0_out;
    force phy0_scan_apb1_out       = pcie_top_wrapper.u_pcie_subsys.phy0_scan_apb1_out;
    force phy0_scan_fw_out         = pcie_top_wrapper.u_pcie_subsys.phy0_scan_fw_out;
    force phy0_scan_jtag_out       = pcie_top_wrapper.u_pcie_subsys.phy0_scan_jtag_out;
    force phy0_dtb_out             = pcie_top_wrapper.u_pcie_subsys.phy0_dtb_out;
    force apbslv_active            = pcie_top_wrapper.u_pcie_subsys.apbslv_active;
    force snps_scan_out            = pcie_top_wrapper.u_pcie_subsys.snps_scan_out;
  end

  // Force inputs that axelera ties-off in their wrapper, connects to csr or some other logic to directly connect with their original signal names.
  initial begin
    force pcie_top_wrapper.u_pcie_subsys.clkreq_in_n             = clkreq_in_n;
    force pcie_top_wrapper.u_pcie_subsys.power_up_rst_n          = power_up_rst_n;
    force pcie_top_wrapper.u_pcie_subsys.perst_n                 = perst_n;
    force pcie_top_wrapper.u_pcie_subsys.apb_presetn             = apb_presetn;
    force pcie_top_wrapper.u_pcie_subsys.msi_int                 = msi_int;
    force pcie_top_wrapper.u_pcie_subsys.sys_int                 = sys_int;
    force pcie_top_wrapper.u_pcie_subsys.mac_scan_mode           = mac_scan_mode;
    force pcie_top_wrapper.u_pcie_subsys.mac_scan_rst_n          = mac_scan_rst_n;
    force pcie_top_wrapper.u_pcie_subsys.mac_scan_shift          = mac_scan_shift;
    force pcie_top_wrapper.u_pcie_subsys.mac_scan_shift_cg       = mac_scan_shift_cg;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_acmode           = phy_bs_acmode;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_actest           = phy_bs_actest;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_cdr              = phy_bs_cdr;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_ce               = phy_bs_ce;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_rx_bigswing      = phy_bs_rx_bigswing;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_rx_init          = phy_bs_rx_init;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_rx_level         = phy_bs_rx_level;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_sdr              = phy_bs_sdr;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_tdi              = phy_bs_tdi;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_tx_lowswing      = phy_bs_tx_lowswing;
    force pcie_top_wrapper.u_pcie_subsys.phy_bs_udr              = phy_bs_udr;
    force pcie_top_wrapper.u_pcie_subsys.pcs_scan_clk_sel        = pcs_scan_clk_sel;
    force pcie_top_wrapper.u_pcie_subsys.pcs_scan_mode           = pcs_scan_mode;
    force pcie_top_wrapper.u_pcie_subsys.pcs_scan_rst            = pcs_scan_rst;
    force pcie_top_wrapper.u_pcie_subsys.pcs_scan_shift          = pcs_scan_shift;
    force pcie_top_wrapper.u_pcie_subsys.pcs_scan_shift_cg       = pcs_scan_shift_cg;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_mode          = phy0_scan_mode;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_clk_sel       = phy0_scan_clk_sel;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_set_rst       = phy0_scan_set_rst;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_shift         = phy0_scan_shift;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_shift_cg      = phy0_scan_shift_cg;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_pma_occ_en    = phy0_scan_pma_occ_en;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_cr_in         = phy0_scan_cr_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_mpll_dword_in = phy0_scan_mpll_dword_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_mpll_qword_in = phy0_scan_mpll_qword_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_rx_dword_in   = phy0_scan_rx_dword_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_occ_in        = phy0_scan_occ_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_ref_in        = phy0_scan_ref_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_apb0_in       = phy0_scan_apb0_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_apb1_in       = phy0_scan_apb1_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_fw_in         = phy0_scan_fw_in;
    force pcie_top_wrapper.u_pcie_subsys.phy0_scan_jtag_in       = phy0_scan_jtag_in;
    force pcie_top_wrapper.u_pcie_subsys.phy_test_burnin         = phy_test_burnin;
    force pcie_top_wrapper.u_pcie_subsys.phy_test_powerdown      = phy_test_powerdown;
    force pcie_top_wrapper.u_pcie_subsys.phy_test_stop_clk_en    = phy_test_stop_clk_en;
    force pcie_top_wrapper.u_pcie_subsys.phy_test_tx_ref_clk_en  = phy_test_tx_ref_clk_en;
    force pcie_top_wrapper.u_pcie_subsys.phy0_test_flyover_en    = phy0_test_flyover_en;
    force pcie_top_wrapper.u_pcie_subsys.phy_apb0_if_sel         = phy_apb0_if_sel;
    force pcie_top_wrapper.u_pcie_subsys.tap_phy0_ref_use_pad    = tap_phy0_ref_use_pad;
    force pcie_top_wrapper.u_pcie_subsys.tap_phy0_reset          = tap_phy0_reset;
    force pcie_top_wrapper.u_pcie_subsys.ate_test_mode           = ate_test_mode;
    force pcie_top_wrapper.u_pcie_subsys.snps_scan_in            = snps_scan_in;
  end

endmodule
