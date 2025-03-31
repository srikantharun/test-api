// ------------------------------------------------------------------------------
// 
// Copyright 2024 Synopsys, INC.
// 
// This Synopsys IP and all associated documentation are proprietary to
// Synopsys, Inc. and may only be used pursuant to the terms and conditions of a
// written license agreement with Synopsys, Inc. All other use, reproduction,
// modification, or distribution of the Synopsys IP or the associated
// documentation is strictly prohibited.
// Inclusivity & Diversity - Visit SolvNetPlus to read the "Synopsys Statement on
//            Inclusivity and Diversity" (Refer to article 000036315 at
//                        https://solvnetplus.synopsys.com)
// 
// Component Name   : DWC_ddrctl_lpddr54
// Component Version: 1.60a-lca00
// Release Type     : LCA
// Build ID         : 0.0.0.0.TreMctl_302.DwsDdrChip_8.26.6.DwsDdrctlTop_5.12.7
// ------------------------------------------------------------------------------


/**
 * @file dwc_ddrctl_cinit.c
 * @brief Controller initialization software library.
 */

#include "dwc_ddrctl_cinit.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_ddrctl_cinit_io.h"
#include "dwc_ddrctl_reg_map.h"
#include "dwc_ddrctl_reg_map_macros.h"
#include "dwc_ddrctl_cinit_kconfig.h"
#include "dwc_ddrctl_cinit_jedec_ddr_timing.h"
#include "dwc_ddrctl_cinit_types_str.h"
#include "ddrctl_cinit_ime.h"
#include "ddrctl_regmap.h"
#include "dwc_ddrctl_cinit_cfg_check.h"

#ifdef DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC
#include "dwc_ddrctl_cinit_SPD.h"
#endif //DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC

#ifdef DWC_IME_NUM_REGIONS
#if DWC_IME_NUM_REGIONS > IME_MAX_REGIONS
#error DWC_IME_NUM_REGIONS is higher than IME_MAX_REGIONS, please check
#endif // IME_MAX_REGIONS > DWC_IME_NUM_REGIONS
#endif // DWC_IME_NUM_REGIONS

#ifdef DDRCTL_SECURE
void dwc_cinit_ime_pre_cfg(void);
#endif // DDRCTL_SECURE


SubsysHdlr_t *hdlr;
ddr_ctrl_regs_t g_ctrl_regs;


uint32_t ddr_cinit_get_major_version()
{
    return FW_VERSION_MAJOR;
}


uint32_t ddr_cinit_get_minor_version()
{
    return FW_VERSION_MINOR;
}


/**
 * @brief Initial CINIT function this function will open log files for writing.
 **/
void dwc_ddrctl_cinit_begin(SubsysHdlr_t *cinit_cfg)
{
    uint8_t crtl_inst;
    ddrctl_error_t rslt;
    /// - set global pointer
    hdlr = cinit_cfg;

    cinit_cfg->spdData_m.ddr5_jedec_spec = JESD79_5B;

    memset(&g_ctrl_regs, 0, sizeof(g_ctrl_regs));

    /// - open log files
    ddr_bsp_log_file_create(SNPS_MAIN_LOG);
    ddr_bsp_log_file_create(SNPS_SEQUENCES_LOG);
    ddr_bsp_log_file_create(SNPS_REGMAP_LOG);
    ddr_bsp_log_file_create(SNPS_CONFIG_LOG);

    /// - apply reset values to the registers and structures
    dwc_cinit_reg_defaults(hdlr);
    dwc_ddrctl_cinit_set_static_cfg_initial_values();
    dwc_ddrctl_cinit_set_qdyn_cfg_initial_values();
    dwc_ddrctl_cinit_set_dyn_cfg_initial_values();

#ifdef USE_KCONFIG_DEFINITIONS
    rslt = dwc_ddrctl_cinit_kconfig(cinit_cfg);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Kconfiguration failed");
        dwc_ddrctl_cinit_exit(1);
    }
#endif /* USE_KCONFIG_DEFINITIONS */

    // Always configure the base address for the possible channels
    for (crtl_inst = 0; crtl_inst < DWC_DDRCTL_NUM_CHANNEL; crtl_inst++) {
        ddrctl_set_base_addr(crtl_inst, cinit_cfg->ddrctl_base_addr[crtl_inst]);
    }

#ifdef DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC
    rslt = dwc_ddrctl_cinit_SPD_retrieve();
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("SPD retrieval process failed");
        dwc_ddrctl_cinit_exit(1);
    }
#endif /* DWC_DDRCTL_CINIT_SPD_DYNAMIC_JEDEC */

    /// - get the JEDEC TCK value
    dwc_cinit_get_jedec_clk_speed(cinit_cfg);


#ifdef DDRCTL_DDR
    /// - get user input if in CPU_DPI mode
    dwc_ddrctl_cinit_ddr_setuserinput();
#else
    dwc_ddrctl_cinit_lpddr_setuserinput();
#endif


    rslt = ddrctl_cinit_cfg_check(cinit_cfg);
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("Configuration not suported, exiting");
        dwc_ddrctl_cinit_exit(1);
    }

    /// - setup address mapper
    for (uint32_t am = 0;am < cinit_cfg->num_amap; am++) {
        dwc_ddrctl_cinit_ddr_address_mapper(am);
    }

    ddrctl_cinit_ime_region_auto_calc(cinit_cfg);
}

/** @brief main CINIT method */
void dwc_ddrctl_cinit_main(SubsysHdlr_t *phdlr)
{
    hdlr = phdlr;

    dwc_cinit_setup(hdlr);
    dwc_cinit_setup_mmap();
}

/**
 * @brief End of cinit program
 * This will call dwc_cinit_setup, dwc_cinit_setup_mmap and close the log files
 */
void dwc_ddrctl_cinit_end(void)
{
    ddr_bsp_log_file_close(SNPS_MAIN_LOG);
    ddr_bsp_log_file_close(SNPS_SEQUENCES_LOG);
    ddr_bsp_log_file_close(SNPS_REGMAP_LOG);
    ddr_bsp_log_file_close(SNPS_CONFIG_LOG);
}



/**
 * @brief The register defaults are applied to the C structures.
 * @note The body of this method is automated.
 */
void dwc_cinit_reg_defaults(SubsysHdlr_t *phdlr)
{
    hdlr = phdlr;
    dwc_ddrctl_cinit_set_REGB_default();
}

/**
 * @brief Function called from simulation env to initialize the CINIT structures.
 * The memory clock must be set prior to this function call
 * To set the operational clock frequencies use the following methods:
 *
 *  dwc_cinit_get_jedec_clk_speed(g_mctl_cfg);
 *  dwc_cinit_set_operational_clk_period(g_mctl_cfg);
 *
 * @param hdlr pointer to SubsysHdlr_t
 * @note in simulation mode the SubsysHdlr_t memory is allocated in the UVM env.
 **/
void dwc_cinit_setup(SubsysHdlr_t *phdlr)
{
    ddrctl_error_t rslt;

    hdlr = phdlr;
    rslt = dwc_cinit_ddr_set_timing();
    if (DDRCTL_SUCCESS != rslt) {
        SNPS_ERROR("DDR set timing failed = %u", rslt);
        dwc_ddrctl_cinit_exit(DDRCTL_SUCCESS);
    }
}

/**
 * @brief function to set the operational clock period
 * @note dwc_cinit_ddr_set_timing must be call prior to this function.
 * if enable_non_jedec_tck is set then it is assumed that
 * SPD.tck_ps[] set been set externally.
 */
void dwc_cinit_set_operational_clk_period(SubsysHdlr_t *phdlr)
{
    SNPS_TRACE("Entering");
    hdlr = phdlr;

    for (int p = 0; p < hdlr->num_pstates; p++) {
        ddrTimingParameters_t *timing = &CFG->timingParams_m[p][0];
        if (CFG->enable_non_jedec_tck) {
            CINIT_ASSERT(SPD.tck_ps[p] != 0); // check that the period as been set by user.
        } else {
            if (SPD.tck_ps[p] == 0) {
                SPD.tck_ps[p] = timing->sg_tck_ps;
                SNPS_LOG("SPD.tck_ps[%d] = %u", p, SPD.tck_ps[p]);
            }
            // get the clock period from JEDEC timing library. In LPDDR, other frequency(tck_ps[1]) will be set in lpddr_sdram_cfg

#ifdef MEMC_DDR3_OR_4
#ifdef CINIT_DDR4
            if (IS_DDR4) {
                if (QDYN.dll_off_mode == 1) {
                    // in DLL off mode the min TCK period is 8ns
                    // JESD79-4A spec Table 103
                    SPD.tck_ps[p] = 8000;
                    SNPS_LOG("SPD.tck_ps[%d] = %u", p, SPD.tck_ps[p]);
                }
            }
#endif  // CINIT_DDR4
#endif /* MEMC_DDR3_OR_4 */
        }
    }

#ifdef DDRCTL_LPDDR
    //Map tck_ps[pstate] to data_rate[pstate]
    dwc_cinit_map_tck_ps_to_data_rate(hdlr);
#endif /* DDRCTL_LPDDR */

    SNPS_TRACE("Leaving");
}


/**
 * @brief method to read the contents of PAS DU command buffer.
 */
uint32_t dwc_ddrctl_cinit_read_du_cmdbuf(uint32_t addr, uint32_t block_type, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DU_CMDBUF_CTRL_t du_cmdbuf_ctrl;
    uint32_t val;

    du_cmdbuf_ctrl.value = 0;
    du_cmdbuf_ctrl.du_cmdbuf_addr = addr;
    du_cmdbuf_ctrl.du_cmdbuf_select = block_type;
    du_cmdbuf_ctrl.du_cmdbuf_rw_type = 0; // Read
    du_cmdbuf_ctrl.du_cmdbuf_rw_start = 1;

    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CMDBUF_CTRL, du_cmdbuf_ctrl.value);
    val = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + DU_CMDBUF_STAT);

    SNPS_TRACE("Leaving");
    return val;
}

/**
 * @brief method to write the contents of PAS DU command buffer.
 */
void dwc_ddrctl_cinit_write_du_cmdbuf(uint32_t addr, uint32_t data, uint32_t block_type, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DU_CMDBUF_CTRL_t du_cmdbuf_ctrl;

    du_cmdbuf_ctrl.value = 0;
    du_cmdbuf_ctrl.du_cmdbuf_wdata = data;
    du_cmdbuf_ctrl.du_cmdbuf_addr = addr;
    du_cmdbuf_ctrl.du_cmdbuf_select = block_type;
    du_cmdbuf_ctrl.du_cmdbuf_rw_type = 1; // write
    du_cmdbuf_ctrl.du_cmdbuf_rw_start = 0;
    du_cmdbuf_ctrl.du_cmdbuf_select = block_type;

    if(UMCTL2_P_ASYNC_EN){
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CMDBUF_CTRL, du_cmdbuf_ctrl.value);
    }
    du_cmdbuf_ctrl.du_cmdbuf_rw_start = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CMDBUF_CTRL, du_cmdbuf_ctrl.value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief method to read the contents of PAS LP command buffer.
 */
uint32_t dwc_ddrctl_cinit_read_lp_cmdbuf(uint32_t addr, uint32_t ch)
{
    SNPS_TRACE("Entering");
    LP_CMDBUF_CTRL_t lp_cmdbuf_ctrl;
    uint32_t val;

    lp_cmdbuf_ctrl.value = 0;
    lp_cmdbuf_ctrl.lp_cmdbuf_addr = addr;
    lp_cmdbuf_ctrl.lp_cmdbuf_rw_type = 0; // Read
    lp_cmdbuf_ctrl.lp_cmdbuf_rw_start = 1;

    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LP_CMDBUF_CTRL, lp_cmdbuf_ctrl.value);
    val = dwc_ddrctl_cinit_io_read32(REGB_DDRC_CH_OFFSET(ch) + LP_CMDBUF_STAT);

    SNPS_TRACE("Leaving");
    return val;
}

/**
 * @brief method to write the contents of PAS LP command buffer.
 */
void dwc_ddrctl_cinit_write_lp_cmdbuf(uint32_t addr, uint32_t data, uint32_t ch)
{
    SNPS_TRACE("Entering");
    LP_CMDBUF_CTRL_t lp_cmdbuf_ctrl;

    lp_cmdbuf_ctrl.value = 0;
    lp_cmdbuf_ctrl.lp_cmdbuf_wdata = data;
    lp_cmdbuf_ctrl.lp_cmdbuf_addr = addr;
    lp_cmdbuf_ctrl.lp_cmdbuf_rw_type = 1; // write

    if(UMCTL2_P_ASYNC_EN){
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LP_CMDBUF_CTRL, lp_cmdbuf_ctrl.value);
    }
    lp_cmdbuf_ctrl.lp_cmdbuf_rw_start = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + LP_CMDBUF_CTRL, lp_cmdbuf_ctrl.value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief method to write the contents of PAS DU configuration buffer
 */
void dwc_ddrctl_cinit_write_du_cfgbuf(uint32_t addr, uint32_t blk_sel, uint32_t blk_ba, uint32_t blk_size, uint32_t blk_thres,uint32_t blk_type, uint32_t ch)
{
    SNPS_TRACE("Entering");
    DU_CFGBUF_CTRL_t du_cfgbuf_ctrl;

    du_cfgbuf_ctrl.value = 0;
    du_cfgbuf_ctrl.du_cfgbuf_op_mode = 0;
    du_cfgbuf_ctrl.du_cfgbuf_select = blk_sel;
    du_cfgbuf_ctrl.du_cfgbuf_rw_type = 1; // write
    du_cfgbuf_ctrl.du_cfgbuf_addr = addr;
    du_cfgbuf_ctrl.du_cfgbuf_wdata = (blk_size << 8) | blk_ba;
    du_cfgbuf_ctrl.du_cfgbuf_rw_start = 0;

    if(UMCTL2_P_ASYNC_EN){
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CFGBUF_CTRL, du_cfgbuf_ctrl.value);
    }
    du_cfgbuf_ctrl.du_cfgbuf_rw_start = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CFGBUF_CTRL, du_cfgbuf_ctrl.value);

    du_cfgbuf_ctrl.du_cfgbuf_addr += 1;
    du_cfgbuf_ctrl.du_cfgbuf_wdata = (blk_type << 15) | blk_thres;

    if(UMCTL2_P_ASYNC_EN){
        du_cfgbuf_ctrl.du_cfgbuf_rw_start = 0;
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CFGBUF_CTRL, du_cfgbuf_ctrl.value);
    }
    du_cfgbuf_ctrl.du_cfgbuf_rw_start = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + DU_CFGBUF_CTRL, du_cfgbuf_ctrl.value);

    SNPS_TRACE("Leaving");
}

/**
 * @brief method to write the contents of PAS CAPAR command buffer.
 */
void dwc_ddrctl_cinit_write_capar_cmdbuf(uint32_t addr, uint32_t data, uint32_t ch)
{
    SNPS_TRACE("Entering");
    CAPAR_CMDBUF_CTRL_t capar_cmdbuf_ctrl;

    capar_cmdbuf_ctrl.value = 0;
    /*SNPS_LOG("addr=%u, data=%u, ch=%u", addr,data,ch);*/
    capar_cmdbuf_ctrl.capar_cmdbuf_wdata = data;
    capar_cmdbuf_ctrl.capar_cmdbuf_addr = addr;
    capar_cmdbuf_ctrl.capar_cmdbuf_rw_type = 1; // write
    capar_cmdbuf_ctrl.capar_cmdbuf_rw_start = 0;

    if(UMCTL2_P_ASYNC_EN){
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CAPAR_CMDBUF_CTRL, capar_cmdbuf_ctrl.value);
    }
    capar_cmdbuf_ctrl.capar_cmdbuf_rw_start = 1;
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(ch) + CAPAR_CMDBUF_CTRL, capar_cmdbuf_ctrl.value);

    SNPS_TRACE("Leaving");
}



#ifdef DDRCTL_HWFFC_EXT_AND_LPDDR5X
/**
 * @brief method to write the contents of HWFFC MRW buffer.
 */
void dwc_ddrctl_cinit_write_hwffc_mrwbuf(uint32_t pstate, uint32_t addr, uint32_t mrwbuf_wdata)
{
    uint32_t ctrl0, ctrl1;
    // reset whole bit
    ctrl0 = 0;
    ctrl1 = 0;

    SNPS_WRITE_FIELD(ctrl0, HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_SELECT,  pstate);
    SNPS_WRITE_FIELD(ctrl0, HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_ADDR,    addr);
    SNPS_WRITE_FIELD(ctrl0, HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_RW_TYPE, 1); // rw_type=1: write
    SNPS_WRITE_FIELD(ctrl1, HWFFC_MRWBUF_CTRL1_HWFFC_MRWBUF_WDATA,   mrwbuf_wdata);

    // program
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + HWFFC_MRWBUF_CTRL1, ctrl1);

    if(UMCTL2_P_ASYNC_EN){
        dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + HWFFC_MRWBUF_CTRL0, ctrl0);
    }
    SNPS_WRITE_FIELD(ctrl0, HWFFC_MRWBUF_CTRL0_HWFFC_MRWBUF_RW_START, 1); // rw_start=1: start MRWBUF write
    dwc_ddrctl_cinit_io_write32(REGB_DDRC_CH_OFFSET(0) + HWFFC_MRWBUF_CTRL0, ctrl0);
}
#else
inline void dwc_ddrctl_cinit_write_hwffc_mrwbuf(uint32_t pstate, uint32_t addr, uint32_t mrwbuf_wdata) {}
#endif // DDRCTL_HWFFC_EXT_AND_LPDDR5X

