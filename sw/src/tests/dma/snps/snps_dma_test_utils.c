// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "snps_dma_test_utils.h"
#include <memutils.h>
#include <printf.h>
#include <rng.h>

/**************************************************************************
 * Comment on DMA tests:
 * There are different types of tests which try to cover as much as
 * possible. The tests are implemented in functions so that they can
 * be run for the APU and the AI Core DMA.
 *
 * Overview:
 *  - test_dma_aligned: Simple 16kB transfer
 *
 *************************************************************************/

/**************************************************************************
 * test_dma_aligned
 * Transfers 1kB of data from src to dst
 * TODO: Enable varying transfer size
 *************************************************************************/

#define EXPAND_MACRO(x) x  // Helper to force evaluation
void test_dma_aligned(snps_dmac_regs* dmac, const char* src, char* dst, uint64_t ctl_flags, uint64_t cfg_flags, const char* msg) {
    ctl_flags |= DMAC_TR_WIDTH_SETTING;

    snps_dma_channel chan;
    snps_dma_init_dmac(dmac, 0);
    snps_dma_init_channel(&chan, dmac, 0);
    snps_dma_configure_channel(&chan, SNPS_SINGLE_BLOCK, cfg_flags);
    snps_dma_configure_block_transfer(&chan, (uintptr_t)src, (uintptr_t)dst, DATA_BLOCK_TS, ctl_flags);

    snps_dma_enable_channel(&chan);
    while (snps_dma_channel_enabled(&chan));

    CHECK_TRUE(chan.regs->intstatus == CH_INTSTATUS_DMA_TFR_DONE);
    CHECK_TRUE(chan.regs->status == DATA_BLOCK_TS + 1);
    // Caches not yet functional
    // dcache_flush();

    mem_check_equal(src, dst, 0, DATA_SIZE, msg);
}
