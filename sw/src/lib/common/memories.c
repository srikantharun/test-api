// AUTO GENERATED, DON'T MANUALLY EDIT!!
// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description: Automatic generated module with all memories
// Owner: hw/scripts/addr_map


#include "memories.h"

const struct MemoryRegion memory_regions[] = {

{ 0x000000010000, 0x000000010000, true, false, true, "APU_BOOTROM"},
{ 0x000007000000, 0x000000800000, true, true, true, "SYS_SPM"},
{ 0x000008000000, 0x000001000000, true, true, true, "L2_MODULE_0"},
{ 0x000009000000, 0x000001000000, true, true, true, "L2_MODULE_1"},
{ 0x00000A000000, 0x000001000000, true, true, true, "L2_MODULE_2"},
{ 0x00000B000000, 0x000001000000, true, true, true, "L2_MODULE_3"},
{ 0x00000C000000, 0x000001000000, true, true, true, "L2_MODULE_4"},
{ 0x00000D000000, 0x000001000000, true, true, true, "L2_MODULE_5"},
{ 0x00000E000000, 0x000001000000, true, true, true, "L2_MODULE_6"},
{ 0x00000F000000, 0x000001000000, true, true, true, "L2_MODULE_7"},
{ 0x000014000000, 0x000000080000, true, true, true, "AICORE_0_SPM"},
{ 0x000018000000, 0x000000400000, true, true, true, "AICORE_0_L1"},
{ 0x000024000000, 0x000000080000, true, true, true, "AICORE_1_SPM"},
{ 0x000028000000, 0x000000400000, true, true, true, "AICORE_1_L1"},
{ 0x000034000000, 0x000000080000, true, true, true, "AICORE_2_SPM"},
{ 0x000038000000, 0x000000400000, true, true, true, "AICORE_2_L1"},
{ 0x000044000000, 0x000000080000, true, true, true, "AICORE_3_SPM"},
{ 0x000048000000, 0x000000400000, true, true, true, "AICORE_3_L1"},
{ 0x000054000000, 0x000000080000, true, true, true, "AICORE_4_SPM"},
{ 0x000058000000, 0x000000400000, true, true, true, "AICORE_4_L1"},
{ 0x000064000000, 0x000000080000, true, true, true, "AICORE_5_SPM"},
{ 0x000068000000, 0x000000400000, true, true, true, "AICORE_5_L1"},
{ 0x000074000000, 0x000000080000, true, true, true, "AICORE_6_SPM"},
{ 0x000078000000, 0x000000400000, true, true, true, "AICORE_6_L1"},
{ 0x000084000000, 0x000000080000, true, true, true, "AICORE_7_SPM"},
{ 0x000088000000, 0x000000400000, true, true, true, "AICORE_7_L1"},
{ 0x000094000000, 0x000000040000, true, true, true, "PVE_0_SPM"},
{ 0x000098000000, 0x000000400000, true, true, true, "PVE_0_L1_0"},
{ 0x000098400000, 0x000000400000, true, true, true, "PVE_0_L1_1"},
{ 0x000098800000, 0x000000400000, true, true, true, "PVE_0_L1_2"},
{ 0x000098C00000, 0x000000400000, true, true, true, "PVE_0_L1_3"},
{ 0x0000A4000000, 0x000000040000, true, true, true, "PVE_1_SPM"},
{ 0x0000A8000000, 0x000000400000, true, true, true, "PVE_1_L1_0"},
{ 0x0000A8400000, 0x000000400000, true, true, true, "PVE_1_L1_1"},
{ 0x0000A8800000, 0x000000400000, true, true, true, "PVE_1_L1_2"},
{ 0x0000A8C00000, 0x000000400000, true, true, true, "PVE_1_L1_3"},
{ 0x002000000000, 0x000800000000, true, true, true, "DDR_0"},
{ 0x002800000000, 0x000800000000, true, true, true, "DDR_1"},
{}, // null-terminated array
};

const char* get_memory_region_name(uintptr_t address) {

    for (int i = 0; memory_regions[i].name != NULL; i++) {
        uintptr_t region_start = memory_regions[i].base;
        uintptr_t region_end = memory_regions[i].base + memory_regions[i].size;

        if (address >= region_start && address < region_end) {
            return memory_regions[i].name;
        }
    }
    return "Unknown Memory";
}

