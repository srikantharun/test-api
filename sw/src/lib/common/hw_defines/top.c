#include "hw_defines.h"

__attribute__((weak)) const uint32_t HW_DEFINES_HAS_PCTL = 1;

__attribute__((weak)) const uint32_t HW_DEFINES_L2_MODULE_NUMBER = 8;
__attribute__((weak)) const l2_interleaving_t HW_DEFINES_L2_DEFAULT_INTERLEAVING = INTER_1X8_4K;

// Cores
__attribute__((weak)) const uint32_t HW_DEFINES_APU_CORE_NUMBER = 6;
__attribute__((weak)) const uint32_t HW_DEFINES_PVE_0_CORE_NUMBER = 8;
__attribute__((weak)) const uint32_t HW_DEFINES_PVE_1_CORE_NUMBER = 8;
__attribute__((weak)) const uint32_t HW_DEFINES_AICORE_MODULE_NUMBER = 8;
