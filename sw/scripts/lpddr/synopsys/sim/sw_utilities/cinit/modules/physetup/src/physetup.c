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


#include "physetup.h"
#include "dwc_cinit_bsp.h"
#include "dwc_ddrctl_cinit_util.h"
#include "dwc_cinit_macros.h"

#ifdef PHYINIT

// Extern PhyInit functoins, The Phyinit code doesn't have header guards.
// As workaround the propotypes are defines here.

// Logging
extern int dwc_ddrphy_phyinit_log();
extern int dwc_ddrphy_phyinit_end_log();

//Struct Allocation
#ifdef LPDDR54_PHY
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug);
#else
#ifdef DDR5_PHY
#ifdef DWC_PHYINIT_RID_GE202311
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, char *pllSettings, int pubRev);
#else
#ifdef DWC_PHYINIT_RID_GE202303
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, char *pllSettings);
#else
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug);
#endif
#endif
#else
#ifdef LPDDR5X4_PHY
#ifdef DWC_PHYINIT_RID_GE202310
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, char *pllSettings, int pubRev);
#else
#ifdef DWC_PHYINIT_RID_GE202307
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, char* pllSettings);
#else
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug);
#endif
#endif
#else

#ifdef DWC_PHYINIT_RID_GE202401
extern phyinit_config_t* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, int initCtrl, int pub_rev, char *pllSettings);
#else
#ifdef DWC_PHYINIT_RID_GE202206
extern void* dwc_ddrphy_phyinit_configAlloc(int skip_train, int Train2D, int debug, int initCtrl, int pub_rev);
#else
extern void* dwc_ddrphy_phyinit_configAlloc(int skip_training, int Train2D, int debug, int initCtrl);
#endif
#endif
#endif
#endif
#endif
// void dwc_ddrphy_phyinit_configFree(void* ptr);


// IO
extern void dwc_ddrphy_phyinit_userCustom_io_write16(uint32_t adr, uint16_t dat);
extern uint16_t dwc_ddrphy_phyinit_userCustom_io_read16(uint32_t adr);


// Configuration
#ifdef LPDDR54_PHY
extern int dwc_ddrphy_phyinit_setMb(phyinit_config_t* phyctx, int ps, char *field, int value, int Train2D);
#else
#ifdef LPDDR5X4_PHY
extern int dwc_ddrphy_phyinit_setMb(phyinit_config_t* phyctx, int ps, char *field, int value);
#else
extern int dwc_ddrphy_phyinit_setMb(phyinit_config_t* phyctx, int ps, char *field, int value);
#endif
#endif

extern int dwc_ddrphy_phyinit_setUserInput(phyinit_config_t* phyctx, char *field, int value);

// Sequence
#if defined (LPDDR54_PHY) || defined (LPDDR5X4_PHY)
extern int dwc_ddrphy_phyinit_restore_sequence(phyinit_config_t* phyctx);
#endif
extern int dwc_ddrphy_phyinit_sequence(phyinit_config_t* phyctx);

#endif

#ifdef PHYINIT
static ddrctl_bool_t s_log_opened = DDRCTL_FALSE;
#endif

/***********************************************
 *
 * Phyinit functions wrappers for CINIT
 *
 ***********************************************/

void physetup_log_open()
{
#ifdef PHYINIT
    int rslt;

    if (s_log_opened == DDRCTL_TRUE) {
        SNPS_WARN("Log file already open");
        return;
    }

    rslt = dwc_ddrphy_phyinit_log();
    if (0 != rslt) {
        SNPS_ERROR("PHYINIT log open failed with %d, exiting ", rslt);
    }

    s_log_opened = DDRCTL_TRUE;
#else
    SNPS_LOG("PHYINIT not defined: dwc_ddrphy_phyinit_log()");
#endif
}


void physetup_log_close()
{
#ifdef PHYINIT
    int rslt;

    if (s_log_opened == DDRCTL_FALSE) {
        SNPS_WARN("Cannot close log file, is not open");
        return;
    }

    rslt = dwc_ddrphy_phyinit_end_log();
    if (0 != rslt) {
        SNPS_ERROR("PHYINIT log close failed with %d, exiting ", rslt);
    }
#else
    SNPS_LOG("PHYINIT not defined: dwc_ddrphy_phyinit_end_log()");
#endif
}


ddrctl_error_t physetup_config_init(SubsysHdlr_t *config)
{
#ifdef PHYINIT
    phyinit_config_t *  phy_config;
    uint32_t            skip_train;

    if (NULL != config->phy_config) {
        SNPS_WARN("Phy config Init already done, skipping");
        return DDRCTL_SUCCESS;
    }

    SNPS_LOG("PHY Train mode = %d", config->phy_training);

    switch (config->phy_training) {
        case DWC_PHY_TRAINING:
            skip_train = 0;
            SNPS_LOG("Execute firmware train");
            break;
        case DWC_PHY_DEV_INIT:
            skip_train = 2;
            SNPS_LOG("Execute firmware to initialize the DRAM state, zero board delay used");
            break;
        case DWC_PHY_SKIP_TRAINING:
            skip_train = 1;
            SNPS_LOG("Skip train");
            break;
        default:
            SNPS_ERROR("Invalid train mode");
            return DDRCTL_PARAM_ERROR;
    }

    SNPS_LOG("Alloc Phy config structure");

    /* Workaround until the initialization at dwc_ddrphy_phyinit_configAlloc is corrected */
    phy_config = (phyinit_config_t *) calloc(1, sizeof(phyinit_config_t));

    if (NULL == phy_config) {
        return DDRCTL_MEMORY_ERROR;
    }

    phy_config->runtimeConfig.skip_train = skip_train;
    phy_config->runtimeConfig.Train2D = 0;
    phy_config->runtimeConfig.debug = 1;
#ifndef LPDDR5X4_PHY
#ifndef LPDDR54_PHY
#ifndef DDR5_PHY
    phy_config->runtimeConfig.initCtrl = 0;
    phy_config->runtimeConfig.pubRev = DWC_DDRPHY_PUB_RID;
#endif // DDR5_PHY
#endif // LPDDR54_PHY
#endif // LPDDR5X4_PHY

#ifdef LPDDR5X4_PHY
#ifdef DWC_PHYINIT_RID_GE202310
    phy_config->runtimeConfig.pubRev = DWC_LPDDR5XPHY_PUB_RID;
    phy_config->runtimeConfig.pllSettings = NULL;
#else
#ifdef DWC_PHYINIT_RID_GE202307
    phy_config->runtimeConfig.pllSettings = NULL;
#endif // DWC_PHYINIT_RID_GE202307
#endif // DWC_PHYINIT_RID_GE202310
#endif // LPDDR5X4_PHY

    config->phy_config = (void *) phy_config;
#endif // PHYINIT
    return DDRCTL_SUCCESS;
}


void physetup_config_free(SubsysHdlr_t *config)
{
    if (NULL != config->phy_config) {
        free(config->phy_config);
        config->phy_config = NULL;
    }
}


void physetup_io_write16(uint32_t addr, uint16_t data)
{
#ifdef PHYINIT
    dwc_ddrphy_phyinit_userCustom_io_write16(addr, data);
#else
    SNPS_LOG("PHYINIT not defined: dwc_ddrphy_phyinit_userCustom_io_write16(0x%08x, 0x%08x)", addr, data);
#endif
}


uint16_t physetup_io_read16(uint32_t addr)
{
#ifdef PHYINIT
    return dwc_ddrphy_phyinit_userCustom_io_read16(addr);
#else
    SNPS_LOG("PHYINIT not defined: dwc_ddrphy_phyinit_userCustom_io_read16(0x%08x)", addr);
    return 0;
#endif
}



ddrctl_error_t physetup_sequence(SubsysHdlr_t *config)
{
#ifdef PHYINIT
    int rslt = dwc_ddrphy_phyinit_sequence(config->phy_config);
    if (0 != rslt) {
        SNPS_ERROR("PHYINIT sequence failed with %d", rslt);
        return DDRCTL_PHYINIT_ERROR;
    }
#else
    SNPS_LOG("PHYINIT not defined: physetup_sequence()");
#endif
    return DDRCTL_SUCCESS;
}


ddrctl_error_t physetup_restore_sequence(SubsysHdlr_t *config)
{
#ifdef PHYINIT
    int rslt = dwc_ddrphy_phyinit_restore_sequence(config->phy_config);
    if (0 != rslt) {
        SNPS_ERROR("PHYINIT restore sequence failed with %d", rslt);
        return DDRCTL_PHYINIT_ERROR;
    }
#else
    SNPS_LOG("PHYINIT not defined: dwc_ddrphy_phyinit_restore_sequence()");
#endif
    return DDRCTL_SUCCESS;
}


//Replace: dwc_cinit_phyinit_set_inputr
void physetup_set_user_input(SubsysHdlr_t *config, char *field, int value)
{
    SNPS_LOG("dwc_ddrphy_phyinit_setUserInput(%s, %d)", field, value);
#ifdef PHYINIT
    int rslt;

    rslt = dwc_ddrphy_phyinit_setUserInput(config->phy_config, field, value);
    if (0 != rslt) {
        SNPS_ERROR("PHYINIT: set user input failed, field %s = %d", field, value);
        dwc_ddrctl_cinit_exit(DDRCTL_PHYINIT_ERROR);
    }
#endif
}

//phyinit_setMb
void physetup_set_msg_block(SubsysHdlr_t *config, int ps, char *field, int value, int train_2d)
{
    SNPS_LOG("dwc_ddrphy_phyinit_setMb(pstate = %d, %s, 0x%x)", ps, field, value);
#ifdef PHYINIT
    int rslt;
#ifdef LPDDR54_PHY
    rslt = dwc_ddrphy_phyinit_setMb(config->phy_config, ps, field, value, train_2d);
#else
    rslt = dwc_ddrphy_phyinit_setMb(config->phy_config, ps, field, value);
#endif
    if (0 != rslt) {
        SNPS_ERROR("PHYINIT: set msg block failed, pstate %d, field %s = %d", ps, field, value);
        dwc_ddrctl_cinit_exit(DDRCTL_PHYINIT_ERROR);
    }
#endif // PHYINIT
}

#ifdef DWC_DDRCTL_CINIT_CPU_DPI_MODE
/** @brief this method is implemented in the PVE and imported through DPI
 *  we re-define it here to avoid going back into SV world from PHYINIT.
 */
void overrideUserInput_sv(void)
{
    dwc_cinit_phyinit_setuserinput(CFG);
}
#endif

