/*
 * memorymap_patch.h - changes to the memory map for certain platforms
 *
 * On some platforms, there are issues which (temporarily) prevent using the
 * official memory map for some components. For these cases, adaptions to the
 * memory map can be made using this header.
 *
 * WARNING: This should only be used in special cases. All changes must be well
 *          documented and a rationale for the change must be provided.
 */
#pragma once

// comparing non-numeric macro values is hard; see https://stackoverflow.com/a/45450646
#define _CONCAT_IMPL(x, y) x ## y
#define _CONCAT(x, y) _CONCAT_IMPL(x, y)
#define _MEMORYMAP_PATCH _CONCAT(_MEMORYMAP_PATCH_, MEMORYMAP_PATCH)
// numeric values for the individual macros
#define _MEMORYMAP_PATCH_SKYRAY 1
#define _MEMORYMAP_PATCH_MININOC 2


#if _MEMORYMAP_PATCH == _MEMORYMAP_PATCH_SKYRAY
// ---------------------------------------------------------
// SKYRAY
// ---------------------------------------------------------

// The PLDM should be 1 MiB aligned. This is for completeness and not currently
// used by software.
// https://git.axelera.ai/prod/europa/-/issues/826#note_204504
#undef SOC_PERIPH_PLDM_BASE
#define SOC_PERIPH_PLDM_BASE 0x00000000020a0000

// The Skyray version of the APU routes all addresses below 0x0400_0000 on an
// internal AXI XBAR. Thus, the UART is currently mapped at 0x0400_0000.
// https://git.axelera.ai/prod/europa/-/merge_requests/483#note_204892
#undef SOC_PERIPH_UART_BASE
#define SOC_PERIPH_UART_BASE 0x0000000004000000

// Skyray currently only provides a single memory (namely DRAM), instead of
// having a separate SYS-SPM. We map SYS-SPM to the first part of DRAM.
// https://git.axelera.ai/prod/europa/-/issues/802#note_201052
#define _SKYRAY_DRAM_BASE 0x0000000080000000
#define _SKYRAY_DRAM_SIZE 0x0000000020000000 // 512 MB
// SYS_SPM
#undef SYS_SPM_BASE
#define SYS_SPM_BASE _SKYRAY_DRAM_BASE
// aicore.SPM
#undef AICORE_0_SPM_BASE
#define AICORE_0_SPM_BASE (SYS_SPM_BASE + SYS_SPM_SIZE)
// DDR
#undef DDR_BASE
#define DDR_BASE (AICORE_0_SPM_BASE + AICORE_0_SPM_SIZE)
#undef DDR_SIZE
#define DDR_SIZE (_SKYRAY_DRAM_SIZE - SYS_SPM_SIZE - AICORE_0_SPM_SIZE)

// The Skyray design containing the decoder (europa-codec) uses a non-standard
// memory map. This temporary design has a non-standard memory map to ease
// implementation.
// https://axeleraai.atlassian.net/wiki/spaces/archrd/pages/556007425/Skyray+for+Europa#Memory-Map
#undef DECODER_BASE
#undef DECODER_SIZE
#define DECODER_BASE 0x0000000002080000
#define DECODER_SIZE 0x0000000000003000

#else
#error "Invalid value for -DMEMORYMAP_PATCH"
#endif
