// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#ifndef DMA_TEST_UTILS_H
#define DMA_TEST_UTILS_H

#include <testutils.h>
#include <dma/snps/drv_snps_dma.h>
#include "generated_data.h"

/**************************************************************************
 * Provide access to common variables used accross tests
 *************************************************************************/

// 32kB random data, used as first source and as reference to compare against
extern const char __attribute__((aligned(4096))) arrRef[DATA_SIZE_32KB];
// 16kB of 0x55 to reset memory
extern const char __attribute__((aligned(4096))) arr55[DATA_SIZE_16KB];

#endif  // ifndef DMA_TEST_UTILS_H
