// (C) Copyright 2024 Axelera AI B.V.
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Milos Stanisavljevic <milos.stanisavljevic@axelera.ai>

/// Package for PCIE partition wrapper

package pcie_pkg;
    parameter int unsigned N_FAST_CLKS = 3;
    parameter int unsigned N_FENCES = 4;

    // AXI Init MT
    parameter int unsigned PCIE_INIT_MT_AXI_DATA_W = 128;
    typedef logic [PCIE_INIT_MT_AXI_DATA_W-1:0] pcie_init_mt_axi_data_t;
    parameter int unsigned PCIE_INIT_MT_AXI_STRB_W = PCIE_INIT_MT_AXI_DATA_W/8;
    typedef logic [PCIE_INIT_MT_AXI_STRB_W-1:0] pcie_init_mt_axi_strb_t;
    parameter int unsigned PCIE_INIT_MT_AXI_ID_W = 7;
    typedef logic [PCIE_INIT_MT_AXI_ID_W-1:0] pcie_init_mt_axi_id_t;
    // AXI Targ MT
    parameter int unsigned PCIE_TARG_MT_AXI_DATA_W = 128;
    typedef logic [PCIE_TARG_MT_AXI_DATA_W-1:0] pcie_targ_mt_axi_data_t;
    parameter int unsigned PCIE_TARG_MT_AXI_STRB_W = PCIE_TARG_MT_AXI_DATA_W/8;
    typedef logic [PCIE_TARG_MT_AXI_STRB_W-1:0] pcie_targ_mt_axi_strb_t;
    parameter int unsigned PCIE_TARG_MT_AXI_ID_W = 6;
    typedef logic [PCIE_TARG_MT_AXI_ID_W-1:0] pcie_targ_mt_axi_id_t;
    // AXI Targ CFG-DBI
    parameter int unsigned PCIE_TARG_CFG_DBI_AXI_DATA_W = 32;
    typedef logic [PCIE_TARG_CFG_DBI_AXI_DATA_W-1:0] pcie_targ_cfg_dbi_axi_data_t;
    parameter int unsigned PCIE_TARG_CFG_DBI_AXI_STRB_W = PCIE_TARG_CFG_DBI_AXI_DATA_W/8;
    typedef logic [PCIE_TARG_CFG_DBI_AXI_STRB_W-1:0] pcie_targ_cfg_dbi_axi_strb_t;
    parameter int unsigned PCIE_TARG_CFG_DBI_AXI_ID_W = 4;
    typedef logic [PCIE_TARG_CFG_DBI_AXI_ID_W-1:0] pcie_targ_cfg_dbi_axi_id_t;
    // APB CFG
    parameter int unsigned PCIE_TARG_CFG_APB3_ADDR_W = 20;
    typedef logic [PCIE_TARG_CFG_APB3_ADDR_W-1:0] pcie_targ_cfg_apb3_addr_t;
    parameter int unsigned PCIE_TARG_CFG_APB3_DATA_W = 32;
    typedef logic [PCIE_TARG_CFG_APB3_DATA_W-1:0] pcie_targ_cfg_apb3_data_t;
    parameter int unsigned PCIE_TARG_CFG_APB3_STRB_W  = PCIE_TARG_CFG_APB3_DATA_W/8;
    typedef logic [PCIE_TARG_CFG_APB3_STRB_W-1:0] pcie_targ_cfg_apb3_strb_t;

    // Number of sync stages in all synchronisers used between ao clk and muxd_aux_clk
    parameter int unsigned PCIE_SYNC_STAGES = 3;

    // PHY SCAN
    parameter int unsigned PMA_SCAN_CR_SUP = 24;
    parameter int unsigned PMA_SCAN_CR_TX = 12;
    parameter int unsigned PMA_SCAN_CR_RX = 27;
    parameter int unsigned PMA_SCAN_CR = PMA_SCAN_CR_SUP + 4*PMA_SCAN_CR_TX + 4*PMA_SCAN_CR_RX;
    parameter int unsigned RAW_SCAN_CR_CMN_X4 = 45;
    parameter int unsigned RAW_SCAN_CR_LANE_FSM = 0;
    parameter int unsigned RAW_SCAN_CR_LANE_TX = 30;
    parameter int unsigned RAW_SCAN_CR_LANE_RX = 41;
    parameter int unsigned RAW_SCAN_CR = RAW_SCAN_CR_CMN_X4 + 4*RAW_SCAN_CR_LANE_FSM + 4*RAW_SCAN_CR_LANE_TX + 4*RAW_SCAN_CR_LANE_RX;
    parameter int unsigned PHY_SCAN_CR = PMA_SCAN_CR + RAW_SCAN_CR;

    parameter int unsigned PMA_SCAN_MPLL_DWORD_SUP = 2;
    parameter int unsigned PMA_SCAN_MPLL_DWORD_TX = 9;
    parameter int unsigned PMA_SCAN_MPLL_DWORD_RX = 0;
    parameter int unsigned PMA_SCAN_MPLL_DWORD = PMA_SCAN_MPLL_DWORD_SUP + 4*PMA_SCAN_MPLL_DWORD_TX + 4*PMA_SCAN_MPLL_DWORD_RX;
    parameter int unsigned RAW_SCAN_MPLL_DWORD_CMN =  0;
    parameter int unsigned RAW_SCAN_MPLL_DWORD_LANE_FSM = 0;
    parameter int unsigned RAW_SCAN_MPLL_DWORD_LANE_TX = 0;
    parameter int unsigned RAW_SCAN_MPLL_DWORD_LANE_RX = 1;
    parameter int unsigned RAW_SCAN_MPLL_DWORD = RAW_SCAN_MPLL_DWORD_CMN + 4*RAW_SCAN_MPLL_DWORD_LANE_FSM + 4*RAW_SCAN_MPLL_DWORD_LANE_TX + 4*RAW_SCAN_MPLL_DWORD_LANE_RX;
    parameter int unsigned PHY_SCAN_MPLL_DWORD = PMA_SCAN_MPLL_DWORD + RAW_SCAN_MPLL_DWORD;

    parameter int unsigned PMA_SCAN_MPLL_QWORD_SUP = 0;
    parameter int unsigned PMA_SCAN_MPLL_QWORD_TX = 0;
    parameter int unsigned PMA_SCAN_MPLL_QWORD_RX = 29;
    parameter int unsigned PMA_SCAN_MPLL_QWORD = PMA_SCAN_MPLL_QWORD_SUP + 4*PMA_SCAN_MPLL_QWORD_TX + 4*PMA_SCAN_MPLL_QWORD_RX;
    parameter int unsigned RAW_SCAN_MPLL_QWORD_CMN =  0;
    parameter int unsigned RAW_SCAN_MPLL_QWORD_LANE_FSM = 0;
    parameter int unsigned RAW_SCAN_MPLL_QWORD_LANE_TX = 1;
    parameter int unsigned RAW_SCAN_MPLL_QWORD_LANE_RX = 1;
    parameter int unsigned RAW_SCAN_MPLL_QWORD = RAW_SCAN_MPLL_QWORD_CMN + 4*RAW_SCAN_MPLL_QWORD_LANE_FSM + 4*RAW_SCAN_MPLL_QWORD_LANE_TX + 4*RAW_SCAN_MPLL_QWORD_LANE_RX;
    parameter int unsigned PHY_SCAN_MPLL_QWORD = PMA_SCAN_MPLL_QWORD + RAW_SCAN_MPLL_QWORD;

    parameter int unsigned PMA_SCAN_RX_DWORD_SUP = 0;
    parameter int unsigned PMA_SCAN_RX_DWORD_TX = 0;
    parameter int unsigned PMA_SCAN_RX_DWORD_RX = 4;
    parameter int unsigned PMA_SCAN_RX_DWORD = PMA_SCAN_RX_DWORD_SUP + 4*PMA_SCAN_RX_DWORD_TX + 4*PMA_SCAN_RX_DWORD_RX;
    parameter int unsigned RAW_SCAN_RX_DWORD_CMN = 0;
    parameter int unsigned RAW_SCAN_RX_DWORD_LANE_FSM = 0;
    parameter int unsigned RAW_SCAN_RX_DWORD_LANE_TX = 0;
    parameter int unsigned RAW_SCAN_RX_DWORD_LANE_RX = 1;
    parameter int unsigned RAW_SCAN_RX_DWORD = RAW_SCAN_RX_DWORD_CMN + 4*RAW_SCAN_RX_DWORD_LANE_FSM + 4*RAW_SCAN_RX_DWORD_LANE_TX + 4*RAW_SCAN_RX_DWORD_LANE_RX;
    parameter int unsigned PHY_SCAN_RX_DWORD = PMA_SCAN_RX_DWORD + RAW_SCAN_RX_DWORD;

    parameter int unsigned PMA_SCAN_OCC_SUP = 8;
    parameter int unsigned PMA_SCAN_OCC_TX = 0;
    parameter int unsigned PMA_SCAN_OCC_RX = 0;
    parameter int unsigned PMA_SCAN_OCC = PMA_SCAN_OCC_SUP + 4*PMA_SCAN_OCC_TX + 4*PMA_SCAN_OCC_RX;
    parameter int unsigned PHY_SCAN_OCC = PMA_SCAN_OCC;

    parameter int unsigned PMA_SCAN_REF_SUP = 16;
    parameter int unsigned PMA_SCAN_REF_TX = 6;
    parameter int unsigned PMA_SCAN_REF_RX = 7;
    parameter int unsigned PMA_SCAN_REF = PMA_SCAN_REF_SUP + 4*PMA_SCAN_REF_TX + 4*PMA_SCAN_REF_RX;
    parameter int unsigned RAW_SCAN_REF_CMN = 2;
    parameter int unsigned RAW_SCAN_REF_LANE_FSM = 0;
    parameter int unsigned RAW_SCAN_REF_LANE_TX = 1;
    parameter int unsigned RAW_SCAN_REF_LANE_RX = 3;
    parameter int unsigned RAW_SCAN_REF = RAW_SCAN_REF_CMN + 4*RAW_SCAN_REF_LANE_FSM + 4*RAW_SCAN_REF_LANE_TX + 4*RAW_SCAN_REF_LANE_RX;
    parameter int unsigned PHY_SCAN_REF = PMA_SCAN_REF+RAW_SCAN_REF;

    parameter int unsigned RAW_SCAN_JTAG_CMN = 2;
    parameter int unsigned RAW_SCAN_JTAG = RAW_SCAN_JTAG_CMN;
    parameter int unsigned PHY_SCAN_JTAG = RAW_SCAN_JTAG;
endpackage
