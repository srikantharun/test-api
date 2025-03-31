#pragma once

#include <pctl/drv_pctl.h>
#include <hw_defines.h>
#include <stdint.h>


typedef struct {
    char*     name;     // Module name to which the PCTL belongs to
    uint64_t  n_resets; // Number of PPMUs per PCTL
    uint64_t  n_clkdiv; // Number of Clock Dividers per PCTL
    uint64_t  n_fences; // Number of Fences per PCTL
    uintptr_t base;     // Base address of the first PCTL
    uintptr_t size;     // Offset between PCTL bases
} module_pctl_info;

enum module_ids {
    AI_CORE_MODULE_0,   // 0
    AI_CORE_MODULE_1,   // 1
    AI_CORE_MODULE_2,   // 2
    AI_CORE_MODULE_3,   // 3
    AI_CORE_MODULE_4,   // 4
    AI_CORE_MODULE_5,   // 5
    AI_CORE_MODULE_6,   // 6
    AI_CORE_MODULE_7,   // 7

    L2_MODULE_0,        // 8
    L2_MODULE_1,        // 9
    L2_MODULE_2,        // 10
    L2_MODULE_3,        // 11
    L2_MODULE_4,        // 12
    L2_MODULE_5,        // 13
    L2_MODULE_6,        // 14
    L2_MODULE_7,        // 15

    SDMA_MODULE_0,      // 16
    SDMA_MODULE_1,      // 17

    DECODER_MODULE,     // 18

    PVE_MODULE_0,       // 19
    PVE_MODULE_1,       // 20
};


/**
 * @brief Encapsulates the enable sequence for all L2 modules.
 *
 * This function performs the enable sequence for all L2 modules at once,
 * ensuring they are activated as required.
 */
void pctl_enable_l2();
void pctl_disable_l2();


void pctl_enable_pve_0();
void pctl_disable_pve_0();

void pctl_enable_pve_1();
void pctl_disable_pve_1();

void pctl_enable_aicore(uint64_t core_id);
void pctl_disable_aicore(uint64_t core_id);


/**
 * @brief Encapsulates the enable sequence for a specific module.
 *
 * This function enables the specified module by removing all resets and fences of it's
 * PCTL instance.
 *
 * @param[in] l2_module_idx Index of the module to enable.
 */
void pctl_enable_module(uint64_t module_id);
void pctl_disable_module(uint64_t module_id);
