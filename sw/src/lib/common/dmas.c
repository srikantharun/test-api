
// AUTO GENERATED, DON'T MANUALLY EDIT!!
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// List of all DMAs in the system along with their names and base addresses for the CSR config

#include <memorymap.h>
#include "dmas.h"
#include <string.h>
#include <testutils.h>

const struct DmaRegion dma_regions[] = {
{ (uintptr_t) AICORE_0_DATAPATH_CSR_DMA_HP_DMA_0_BASE, "HP_DMA_AI0"},
{ (uintptr_t) AICORE_1_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI1"},
{ (uintptr_t) AICORE_2_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI2"},
{ (uintptr_t) AICORE_3_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI3"},
{ (uintptr_t) AICORE_4_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI4"},
{ (uintptr_t) AICORE_5_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI5"},
{ (uintptr_t) AICORE_6_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI6"},
{ (uintptr_t) AICORE_7_DATAPATH_CSR_DMA_HP_DMA_0_BASE,  "HP_DMA_AI7"},
{ (uintptr_t) SDMA_0_DMA_CHANNELS_BASE,  "SDMA0"},
{ (uintptr_t) SDMA_1_DMA_CHANNELS_BASE,  "SDMA1"},
{ (uintptr_t) PVE_0_DMA0_CHANNELS_BASE,  "HP_DMA0_PVE0"},
{ (uintptr_t) PVE_0_DMA1_CHANNELS_BASE,  "HP_DMA1_PVE0"},
{ (uintptr_t) PVE_1_DMA0_CHANNELS_BASE,  "HP_DMA0_PVE1"},
{ (uintptr_t) PVE_1_DMA1_CHANNELS_BASE,  "HP_DMA1_PVE1"},
{ (uintptr_t) APU_DMA_BASE , "LP_DMA_APU" },
{ (uintptr_t) AICORE_0_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI0" },
{ (uintptr_t) AICORE_1_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI1" },
{ (uintptr_t) AICORE_2_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI2" },
{ (uintptr_t) AICORE_3_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI3" },
{ (uintptr_t) AICORE_4_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI4" },
{ (uintptr_t) AICORE_5_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI5" },
{ (uintptr_t) AICORE_6_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI6" },
{ (uintptr_t) AICORE_7_CONFIGURATION_CONTROL_LP_DMA_BASE , "LP_DMA_AI7" },
{}, // null-terminated array
};

const char* get_dma_name(uintptr_t address) {

    for (int i = 0; dma_regions[i].name != NULL; i++) {
        uintptr_t region_base = dma_regions[i].base;

        if (address == region_base) {
            return dma_regions[i].name;
        }
    }
    return "Unknown DMA name";
}


uintptr_t get_dma_base_addr(const char* name) {

    for (int i = 0; dma_regions[i].name != NULL; i++) {
        if (strcmp(name, dma_regions[i].name) == 0) {
            return dma_regions[i].base;
        }
    }
    ASSERT(0, "dma name not found");
    return 1;
}
