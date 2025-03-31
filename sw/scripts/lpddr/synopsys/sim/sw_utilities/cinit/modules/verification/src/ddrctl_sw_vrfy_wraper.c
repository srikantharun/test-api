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


#include "ddrctl_sw_vrfy_wraper.h"
#include "dwc_ddrctl_cinit_helpers.h"
#include "dwc_cinit_log.h"
#include "dwc_ddrctl_cinit_log_config.h"
#include "dwc_ddrctl_cinit_helpers.h"

/* SystemVerilog function prototype to write the config struct to the config log */
extern void ddrctl_sim_log_cfg_struct(const SubsysHdlr_t *cfg);

/**
 * @brief This is a wraper for the SystemVerilog interfaces.
 * The CINIT config structure is created in SystemVerilog but since the
 * struct is passed by copy only we cannot unsure it life time.
 * Due to this, the CINIT config stucture will be static created here
 * and the information from SystemVerilog copied to it,
 */

static ddrctl_bool_t    s_cinit_cfg_init_done = DDRCTL_FALSE;
static SubsysHdlr_t     s_vrfy_cinit_cfg;
static SubsysHdlr_t    *s_prvs_cinit_cfg_ptr = NULL;

#define CHECK_STRUCT_CALL_FUNCTION(func, cfg) \
    do {                                                    \
        if (_verify_update_config(cfg) != DDRCTL_SUCCESS) { \
            SNPS_LOG_CFG_STRUCT(#func " received:");               \
            ddrctl_sim_log_cfg_struct(cfg);                 \
        }                                                   \
        func(&s_vrfy_cinit_cfg);                            \
        _update_vrfy_config(cfg);                           \
        SNPS_LOG_CFG_STRUCT(#func " returns:");                    \
        ddrctl_sim_log_cfg_struct(cfg);                     \
    } while (0)

/**
 * @brief Function to update the local CINIT config structure and validate
 *        no unexpected changes were introduced
 * 
 * @param vrfy_handler  SystemVerilog cinit config structure
 */
ddrctl_error_t _verify_update_config(SubsysHdlr_t *vrfy_handler)
{
    int cmp_rslt;

    if (DDRCTL_FALSE == s_cinit_cfg_init_done ) {
        SNPS_INFO("Verify wraper init CINIT config");
        // Configuration structure to the allocated one
        memcpy(&s_vrfy_cinit_cfg, vrfy_handler, sizeof(SubsysHdlr_t));
        s_prvs_cinit_cfg_ptr = vrfy_handler;
        s_cinit_cfg_init_done = DDRCTL_TRUE;
    } else {
        if (s_prvs_cinit_cfg_ptr != vrfy_handler) {
            SNPS_WARN("Configuration pointer changed (from: %p to %p)",
                       s_prvs_cinit_cfg_ptr, vrfy_handler);
            s_prvs_cinit_cfg_ptr = vrfy_handler;
        }

        cmp_rslt = memcmp(&s_vrfy_cinit_cfg, vrfy_handler, sizeof(SubsysHdlr_t));
        if (0 != cmp_rslt) {
            SNPS_WARN("Stored config differs from passed config");
            // Update with the new data from testbench
            memcpy(&s_vrfy_cinit_cfg, vrfy_handler, sizeof(SubsysHdlr_t));
            return DDRCTL_ERROR;
        }
    }
    return DDRCTL_SUCCESS;
}

/**
 * @brief Function to update the structure to be copied to SystemVerilog context
 * 
 * @param vrfy_handler  SystemVerilog cinit config structure
 */
void _update_vrfy_config(SubsysHdlr_t *vrfy_handler)
{
    memcpy(vrfy_handler, &s_vrfy_cinit_cfg, sizeof(SubsysHdlr_t));
}


void ddrctl_sw_wrapper_cfg_to_cinit(SubsysHdlr_t *vrfy_handler)
{
#ifdef DDRCTL_SECURE
    uint8_t channel;

    for (channel = 0; channel < DWC_DDRCTL_NUM_CHANNEL; channel++) {
        vrfy_handler->ime_cfg[channel].enable = STATIC_FIELD(vrfy_handler, ime_en[channel]);
    }
#endif

#ifdef DDRCTL_LPDDR
    uint8_t pstate;

    for (pstate = 0; pstate < UMCTL2_FREQUENCY_NUM; pstate++) {
        if (DDRCTL_GET_PROTOCOL(vrfy_handler) == DWC_LPDDR5) {
            if (DWC_WCKCK_2_1 == vrfy_handler->spdData_m.lpddr5_wckck_ratio[pstate]) {
                vrfy_handler->spdData_m.frequency_ratio[pstate] = DWC_RATIO_WCK_CK_2_1;
            } else {
                vrfy_handler->spdData_m.frequency_ratio[pstate] = DWC_RATIO_WCK_CK_4_1;
            }
        } else {
            if (1 == QDYN_FIELD(vrfy_handler, frequency_ratio[pstate])) {
                vrfy_handler->spdData_m.frequency_ratio[pstate] = DWC_RATIO_1_4;
            } else {
                vrfy_handler->spdData_m.frequency_ratio[pstate] = DWC_RATIO_1_2;
            }
        }
    }
#endif /* DDRCTL_LPDDR */
}


void ddrctl_sw_wrapper_cfg_to_testbench(SubsysHdlr_t *vrfy_handler)
{
#ifdef DDRCTL_SECURE
    uint8_t channel;

    for (channel = 0; channel < DWC_DDRCTL_NUM_CHANNEL; channel++) {
        STATIC_FIELD(vrfy_handler, ime_en[channel]) = vrfy_handler->ime_cfg[channel].enable;
    }
#endif

    uint8_t pstate;

    for (pstate = 0; pstate < UMCTL2_FREQUENCY_NUM; pstate++) {
        switch (vrfy_handler->spdData_m.frequency_ratio[pstate])
        {
#ifdef DDRCTL_LPDDR
            case DWC_RATIO_WCK_CK_4_1:
                vrfy_handler->spdData_m.lpddr5_wckck_ratio[pstate] = DWC_WCKCK_4_1;
                QDYN_FIELD(vrfy_handler, frequency_ratio[pstate]) = 1;
                break;
            case DWC_RATIO_WCK_CK_2_1:
                vrfy_handler->spdData_m.lpddr5_wckck_ratio[pstate] = DWC_WCKCK_2_1;
                QDYN_FIELD(vrfy_handler, frequency_ratio[pstate]) = 0;
                break;
#endif /* DDRCTL_LPDDR */
            case DWC_RATIO_1_4:
                QDYN_FIELD(vrfy_handler, frequency_ratio[pstate]) = 1;
                break;
            case DWC_RATIO_1_2:
            default:
                QDYN_FIELD(vrfy_handler, frequency_ratio[pstate]) = 0;
                break;
        }
    }
}

/**
 * @brief Function wrapper for dwc_ddrctl_cinit_begin.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_begin(SubsysHdlr_t *vrfy_handler)
{
    ddrctl_sw_wrapper_cfg_to_cinit(vrfy_handler);
    CHECK_STRUCT_CALL_FUNCTION(dwc_ddrctl_cinit_begin, vrfy_handler);
    ddrctl_sw_wrapper_cfg_to_testbench(vrfy_handler);
}


/**
 * @brief Function wrapper for dwc_ddrctl_cinit_main.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_main(SubsysHdlr_t *vrfy_handler)
{
    ddrctl_sw_wrapper_cfg_to_cinit(vrfy_handler);
    CHECK_STRUCT_CALL_FUNCTION(dwc_ddrctl_cinit_main, vrfy_handler);
    ddrctl_sw_wrapper_cfg_to_testbench(vrfy_handler);
}

/**
 * @brief Function wrapper for dwc_cinit_set_operational_clk_period.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_set_clk(SubsysHdlr_t *vrfy_handler)
{
    CHECK_STRUCT_CALL_FUNCTION(dwc_cinit_set_operational_clk_period, vrfy_handler);
}

/**
 * @brief Function wrapper for ddrctl_sw_wraper_cinit_get_min_t_xsr.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler  SystemVerilog cinit config structure
 * @param tck_ps        tCK(AVG) 
 * @param dvfsc_type    Supported DVFSC modes
 * @return int unsigned Minimum Self refresh exit - tXSR(min)
 */
int unsigned ddrctl_sw_wraper_cinit_get_min_t_xsr(SubsysHdlr_t *vrfy_handler, int tck_ps, int dvfsc_type)
{
    uint32_t min_t_xsr;
    
    if (_verify_update_config(vrfy_handler) != DDRCTL_SUCCESS) { 
        SNPS_LOG_CFG_STRUCT("ddrctl_sw_wraper_cinit_get_min_t_xsr received:");
        ddrctl_sim_log_cfg_struct(vrfy_handler);
    }

    min_t_xsr = dwc_cinit_get_min_t_xsr(&s_vrfy_cinit_cfg, tck_ps, dvfsc_type);

    _update_vrfy_config(vrfy_handler);

    return min_t_xsr;
}

/**
 * @brief Function wrapper for dwc_ddrctl_cinit_prgm_ucode.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_prgm_ucode(SubsysHdlr_t *vrfy_handler)
{
    CHECK_STRUCT_CALL_FUNCTION(dwc_ddrctl_cinit_prgm_ucode, vrfy_handler);
}

/**
 * @brief Function wrapper for dwc_ddrctl_cinit_prgm_cfgbuf.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_prgm_cfgbuf(SubsysHdlr_t *vrfy_handler)
{
    CHECK_STRUCT_CALL_FUNCTION(dwc_ddrctl_cinit_prgm_cfgbuf, vrfy_handler);
}

/**
 * @brief Function wrapper for dwc_ddrctl_cinit_prgm_hwffcmrw.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_prgm_hwffcmrw(SubsysHdlr_t *vrfy_handler)
{
    CHECK_STRUCT_CALL_FUNCTION(dwc_ddrctl_cinit_prgm_hwffcmrw, vrfy_handler);
}

/**
 * @brief Function wrapper for dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUT_entry.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_prgm_addr_map_lut(SubsysHdlr_t *vrfy_handler)
{
    CHECK_STRUCT_CALL_FUNCTION(dwc_ddrctl_cinit_prgm_REGB_ADDR_MAP_LUT_entry, vrfy_handler);
}

/**
 * @brief Function wrapper for dwc_cinit_phyinit_setuserinput.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 */
void ddrctl_sw_wraper_cinit_phyinit(SubsysHdlr_t *vrfy_handler)
{
    CHECK_STRUCT_CALL_FUNCTION(dwc_cinit_phyinit_setuserinput, vrfy_handler);
}

/**
 * @brief Function wrapper for dwc_ddrphy_cinit_cpu_dpi_main.
 *  It will verify if the received config structure was changed
 * 
 * @param vrfy_handler SystemVerilog cinit config structure
 * @param cinit_seq    cinit sequence to be trigger
 */
void ddrctl_sw_wraper_cpu_dpi_main(SubsysHdlr_t *vrfy_handler, dwc_ddrctl_cinit_seq_e cinit_seq)
{
    if (_verify_update_config(vrfy_handler) != DDRCTL_SUCCESS) { 
        SNPS_LOG_CFG_STRUCT("ddrctl_sw_wraper_cpu_dpi_main received:");
        ddrctl_sim_log_cfg_struct(vrfy_handler);
    }

    dwc_ddrphy_cinit_cpu_dpi_main(&s_vrfy_cinit_cfg, cinit_seq);

    _update_vrfy_config(vrfy_handler);

    SNPS_LOG_CFG_STRUCT("ddrctl_sw_wraper_cpu_dpi_main returns:");
    ddrctl_sim_log_cfg_struct(vrfy_handler);
}


/**
 * @brief Function wrapper for ddr_bsp_log_write.
 * 
 * @param text  string to log
 */
void ddrctl_sw_wraper_log_write(const char *text)
{
    ddr_bsp_log_write(SNPS_CONFIG_LOG, text);
}
