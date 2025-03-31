// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "snps_dma_test_utils.h"
#include <testutils.h>
#include <printf.h>
#include <rng.h>
#include "dmas.h"

// Random-initialized source and destination arrays
char __attribute__((aligned(4096), section(".sys_spm"))) arr_spm[2][DATA_SIZE_1KB] = {{INIT_DATA_1KB}, {INIT_DATA_1KB}};
char __attribute__((aligned(4096), section(".ddr.")))    arr_ddr[2][DATA_SIZE_1KB] = {{INIT_DATA_1KB}, {INIT_DATA_1KB}};

int main()
{
    testcase_init();

    // Generate 1KB random data that changes with seed change
    uint64_t seed = 0x01E123A6CF69EEFF;
    uint64_t randOffset = get_random_offset(seed, DATA_SIZE_16KB);
    // You should not access more than 16KB starting from this address
    char* arrRand = (char*)(arrRef + randOffset);
    // TODO: Enable cache control
    // dcache_flush();

    // Check correct section allocation
    CHECK_TRUE((uint64_t)arr_spm >= (uint64_t)SYS_SPM_BASE && (uint64_t)arr_spm < (uint64_t)(SYS_SPM_BASE + SYS_SPM_SIZE));
    CHECK_TRUE((uint64_t)arr_ddr >= (uint64_t)DDR_1_BASE && (uint64_t)arr_ddr < (uint64_t)(DDR_1_BASE + DDR_1_SIZE));

    // Transfer data with the DMA and check
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_APU"), arrRand,    arr_spm[0], 0, 0, "SPM > SPM");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_APU"), arr_spm[0], arr_ddr[0], 0, 0, "SPM > DDR");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_APU"), arr_ddr[0], arr_ddr[1], 0, 0, "DDR > DDR");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_APU"), arr_ddr[1], arr_spm[1], 0, 0, "DDR > SPM");

    return testcase_finalize();
}
