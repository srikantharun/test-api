// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#ifndef SNPS_DMA_TEST_UTILS_H
#define SNPS_DMA_TEST_UTILS_H

#include "../dma_test_utils.h"

// Defines data size to be transfered from source to destination arrays
#define DATA_SIZE       DATA_SIZE_1KB
#define DATA_BLOCK_TS   (DATA_SIZE / DMAC_TR_WIDTH - 1)

// Transfers 16kB of data from src to dst
void test_dma_aligned(snps_dmac_regs* dmac, const char* src, char* dst, uint64_t ctl_flags, uint64_t cfg_flags, const char* msg);

#endif  // ifndef SNPS_DMA_TEST_UTILS_H
