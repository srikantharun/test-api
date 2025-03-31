// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "snps_dma_test_utils.h"
#include <testutils.h>
#include <printf.h>
#include <rng.h>
#include "dmas.h"


// Random-initialized source and destination arrays
char __attribute__((aligned(4096), section(".sys_spm"))) arr_sys_spm[1][DATA_SIZE_1KB] = {{INIT_DATA_1KB}};
char __attribute__((aligned(4096), section(".spm")))     arr_spm[3][DATA_SIZE_1KB]     = {{INIT_DATA_1KB}, {INIT_DATA_1KB}, {INIT_DATA_1KB}};
char __attribute__((aligned(4096), section(".l1")))      arr_l1[4][DATA_SIZE_1KB]      = {{INIT_DATA_1KB}, {INIT_DATA_1KB}};
char __attribute__((aligned(4096), section(".ddr")))     arr_ddr[1][DATA_SIZE_1KB]     = {{INIT_DATA_1KB}};
// TODO: Implement proper L2 linking and preloading
char* arr_l2 = (void*)L2_BASE;

int main()
{
    testcase_init();

    // Generate 1KB random data that changes with seed change
    uint64_t seed = 0x01E123A6CF69EEFF;
    uint64_t randOffset = get_random_offset(seed, DATA_SIZE_16KB);
    // You should not access more than 16KB starting from this address
    char* arrRand = (char*)(arrRef + randOffset);
    // TODO: Cache control
    // dcache_flush();

    // Check that variables are allocated to the correct sections
    CHECK_TRUE((uint64_t)arr_sys_spm >= (uint64_t)SYS_SPM_BASE && (uint64_t)arr_sys_spm < (uint64_t)(SYS_SPM_BASE + SYS_SPM_SIZE));
    CHECK_TRUE((uint64_t)arr_spm >= (uint64_t)AICORE_0_SPM_BASE && (uint64_t)arr_spm < (uint64_t)(AICORE_0_SPM_BASE + AICORE_0_SPM_SIZE));
    CHECK_TRUE((uint64_t)arr_l1 >= (uint64_t)AICORE_0_L1_BASE && (uint64_t)arr_l1 < (uint64_t)(AICORE_0_L1_BASE + AICORE_0_L1_SIZE));
    CHECK_TRUE((uint64_t)arr_ddr >= (uint64_t)DDR_1_BASE && (uint64_t)arr_ddr < (uint64_t)(DDR_1_BASE + DDR_1_SIZE));
    // Redundant until proper L2 linking is done
    CHECK_TRUE((uint64_t)arr_l2 >= (uint64_t)L2_BASE && (uint64_t)arr_l2 < (uint64_t)(L2_BASE + L2_SIZE));

    // Transfer data with the DMA and check
    // AICORE_FEAT_LPDMA_1: SYS_SPM <> SPM
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arrRand,        arr_sys_spm[0], 0, 0, "SPM > SYS-SPM");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_sys_spm[0], arr_spm[0],     0, 0, "SYS-SPM > SPM");

    // AICORE_FEAT_LPDMA_[3,4]: [SPM, L1] <> [SPM, L1]
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_spm[0],     arr_spm[1],     0, 0, "SPM > SPM");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_spm[0],     arr_l1[0],      0, 0, "SPM > L1");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_l1[0],      arr_l1[1],      0, 0, "L1  > L1");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_l1[1],      arr_spm[1],     0, 0, "L1  > SPM");

    // AICORE_FEAT_LPDMA_2: L1 <> [L2, DDR]
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_l1[1],      arr_l2,        0, 0, "L1 > L2");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_l2,         arr_l1[2],     0, 0, "L2 > L1");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_l1[2],      arr_ddr[0],    0, 0, "L1 > DDR");
    test_dma_aligned((snps_dmac_regs *)get_dma_base_addr("LP_DMA_AI0"), arr_ddr[0],     arr_l1[3],     0, 0, "DDR > L1");

    return testcase_finalize();
}
