#include "pctl_utils.h"
#include <testutils.h>
#include <log.h>


const module_pctl_info module_pctl_arr[] = {
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_0_AO_CSR_BASE,    SYS_CFG_AICORE_0_AO_CSR_SIZE},       // 0
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_1_AO_CSR_BASE,    SYS_CFG_AICORE_1_AO_CSR_SIZE},       // 1
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_2_AO_CSR_BASE,    SYS_CFG_AICORE_2_AO_CSR_SIZE},       // 2
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_3_AO_CSR_BASE,    SYS_CFG_AICORE_3_AO_CSR_SIZE},       // 3
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_4_AO_CSR_BASE,    SYS_CFG_AICORE_4_AO_CSR_SIZE},       // 4
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_5_AO_CSR_BASE,    SYS_CFG_AICORE_5_AO_CSR_SIZE},       // 5
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_6_AO_CSR_BASE,    SYS_CFG_AICORE_6_AO_CSR_SIZE},       // 6
    {"AI_CORE_MODULE_0", 1, 1, 1, SYS_CFG_AICORE_7_AO_CSR_BASE,    SYS_CFG_AICORE_7_AO_CSR_SIZE},       // 7

    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_0_AO_CSR_BASE, SYS_CFG_L2_MODULE_0_AO_CSR_SIZE},    // 8
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_1_AO_CSR_BASE, SYS_CFG_L2_MODULE_1_AO_CSR_SIZE},    // 9
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_2_AO_CSR_BASE, SYS_CFG_L2_MODULE_2_AO_CSR_SIZE},    // 10
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_3_AO_CSR_BASE, SYS_CFG_L2_MODULE_3_AO_CSR_SIZE},    // 11
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_4_AO_CSR_BASE, SYS_CFG_L2_MODULE_4_AO_CSR_SIZE},    // 12
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_5_AO_CSR_BASE, SYS_CFG_L2_MODULE_5_AO_CSR_SIZE},    // 13
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_6_AO_CSR_BASE, SYS_CFG_L2_MODULE_6_AO_CSR_SIZE},    // 14
    {"L2_MODULE_0",      1, 1, 1, SYS_CFG_L2_MODULE_7_AO_CSR_BASE, SYS_CFG_L2_MODULE_7_AO_CSR_SIZE},    // 15

    {"SDMA_MODULE_0",    1, 1, 1, SYS_CFG_SDMA_0_AO_CSR_BASE,      SYS_CFG_SDMA_0_AO_CSR_SIZE},         // 16
    {"SDMA_MODULE_0",    1, 1, 1, SYS_CFG_SDMA_1_AO_CSR_BASE,      SYS_CFG_SDMA_1_AO_CSR_SIZE},         // 17

    {"DECODER_MODULE",   2, 2, 2, SYS_CFG_DECODER_AO_CSR_BASE,     SYS_CFG_DECODER_AO_CSR_SIZE},        // 18

    {"PVE_MODULE_0",     1, 1, 1, SYS_CFG_PVE_0_AO_CSR_BASE,       SYS_CFG_PVE_0_AO_CSR_SIZE},          // 19
    {"PVE_MODULE_0",     1, 1, 1, SYS_CFG_PVE_1_AO_CSR_BASE,       SYS_CFG_PVE_1_AO_CSR_SIZE}           // 20
};


void pctl_enable_l2() {
    ASSERT(HW_DEFINES_L2_MODULE_NUMBER, "There is no L2 module in this design.");
    if (HW_DEFINES_HAS_PCTL && HW_DEFINES_L2_MODULE_NUMBER) {
        uint64_t l2_module_0 = L2_MODULE_0;
        for (uint64_t i = l2_module_0; i < l2_module_0 + HW_DEFINES_L2_MODULE_NUMBER; i++) {
            pctl_enable_module(i);
        }
    }
}

void pctl_disable_l2() {
    if (HW_DEFINES_HAS_PCTL && HW_DEFINES_L2_MODULE_NUMBER) {
        uint64_t l2_module_0 = L2_MODULE_0;
        for (uint64_t i = l2_module_0; i < l2_module_0 + HW_DEFINES_L2_MODULE_NUMBER; i++) {
            pctl_disable_module(i);
        }
    }
}

void pctl_enable_pve_0() {
    ASSERT(HW_DEFINES_PVE_0_CORE_NUMBER, "There is no PVE_0 in this design.");
    if (HW_DEFINES_HAS_PCTL && HW_DEFINES_PVE_0_CORE_NUMBER) {
        pctl_enable_module(PVE_MODULE_0);
    }
}

void pctl_disable_pve_0() {
    if (HW_DEFINES_HAS_PCTL && HW_DEFINES_PVE_0_CORE_NUMBER) {
        pctl_disable_module(PVE_MODULE_0);
    }
}

void pctl_enable_pve_1() {
    ASSERT(HW_DEFINES_PVE_1_CORE_NUMBER, "There is no PVE_1 in this design.");
    if (HW_DEFINES_HAS_PCTL && HW_DEFINES_PVE_1_CORE_NUMBER) {
        pctl_enable_module(PVE_MODULE_1);
    }
}

void pctl_disable_pve_1() {
    if (HW_DEFINES_HAS_PCTL && HW_DEFINES_PVE_1_CORE_NUMBER) {
        pctl_disable_module(PVE_MODULE_1);
    }
}

void pctl_enable_aicore(uint64_t core_id) {
    ASSERT(HW_DEFINES_AICORE_MODULE_NUMBER, "There is no AICORE in this design.\n");

    if (HW_DEFINES_HAS_PCTL) {
        core_id = core_id - AI_CORE_0;
        ASSERT(core_id < HW_DEFINES_AICORE_MODULE_NUMBER, "The hart_id needs to be in range [%d, %d]\n", AI_CORE_0, AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER - 1);

        uint64_t aicore_module = AI_CORE_MODULE_0 + core_id;
        pctl_enable_module(aicore_module);
    }
}

void pctl_disable_aicore(uint64_t core_id) {
    ASSERT(HW_DEFINES_AICORE_MODULE_NUMBER, "There is no AICORE in this design.\n");

    if (HW_DEFINES_HAS_PCTL) {
        core_id = core_id - AI_CORE_0;
        ASSERT(core_id < HW_DEFINES_AICORE_MODULE_NUMBER, "The hart_id needs to be in range [%d, %d]\n", AI_CORE_0, AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER - 1);

        uint64_t aicore_module = AI_CORE_MODULE_0 + core_id;
        pctl_disable_module(aicore_module);
    }
}

void pctl_enable_module(uint64_t module_id) {
    if (HW_DEFINES_HAS_PCTL) {
        pctl_regs* pctl = (void*)(module_pctl_arr[module_id].base);
        LOG_DBG("Enabling module %s", module_pctl_arr[module_id].name);

        for(uint64_t k = 0; k < module_pctl_arr[module_id].n_resets; k++) {
            LOG_DBG("Removing %d-th clock gate", k);
            pctlClockGate(pctl, k, CLOCK_GATE_OFF);
        }
        for(uint64_t k = 0; k < module_pctl_arr[module_id].n_resets; k++) {
            LOG_DBG("Removing %d-th reset", k);
            ASSERT(pctlResetRemove(pctl, k) == 0, "Failed to remove %d-th reset!", k);
        }
        for(uint64_t k = 0; k < module_pctl_arr[module_id].n_fences; k++) {
            LOG_DBG("Removing %d-th fence", k);
            ASSERT(pctlFenceRemove(pctl, k) == 0, "Failed to remove %d-th fence!", k);
        }
    }
}

void pctl_disable_module(uint64_t module_id) {
    if (HW_DEFINES_HAS_PCTL) {
        pctl_regs* pctl = (void*)(module_pctl_arr[module_id].base);
        LOG_DBG("Disabling module %s", module_pctl_arr[module_id].name);

        for(uint64_t k = 0; k < module_pctl_arr[module_id].n_fences; k++) {
            LOG_DBG("Activating fence %lu", k);
            ASSERT(pctlFenceActivate(pctl, k) == 0, "Failed to activate the fence!");
        }
        for(uint64_t k = 0; k < module_pctl_arr[module_id].n_resets; k++) {
            LOG_DBG("Activating reset %lu", k);
            ASSERT(pctlResetActivate(pctl, k) == 0, "Failed to activate the reset!");
        }
        for(uint64_t k = 0; k < module_pctl_arr[module_id].n_resets; k++) {
            LOG_DBG("Removing %d-th clock gate", k);
            pctlClockGate(pctl, k, CLOCK_GATE_ON);
        }
    }
}
