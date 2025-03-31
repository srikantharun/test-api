// Generated register defines for dma

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _DMA_AXE_
#define _DMA_AXE_

#include <std/std_basetype.h>
#include <memorymap.h>
#include "axe_dma.h"
#include "axe_dma_mmu.h"
#include "axe_dma_channel.h"

#ifdef __cplusplus
extern "C" {
#endif

#ifndef DMA_CTRL_SIZE
#define DMA_CTRL_SIZE 0x80
#endif

#ifndef DMA_MAX_CHANNELS
#define DMA_MAX_CHANNELS 4
#endif

#ifndef DMA_MAX_MASTERS
#define DMA_MAX_MASTERS 2
#endif

#ifndef COMMON_REG_LEN
#define COMMON_REG_LEN 0x10000
#endif

#ifndef MMU_REG_LEN
#define MMU_REG_LEN 0x10000
#endif

#ifndef CMD_BLK_REG_LEN
#define CMD_BLK_REG_LEN 0x1000
#endif

#ifndef CH_REG_LEN
#define CH_REG_LEN 0x2000
#endif

#ifndef CH_TRAN_CSR_OFFSET
#define CH_TRAN_CSR_OFFSET 0x100
#endif


// Register width
#ifndef DMA_PARAM_REG_WIDTH
#define DMA_PARAM_REG_WIDTH 64
#endif

#ifndef DMA_PARAM_AXI_DATAW_BYTES
#define DMA_PARAM_AXI_DATAW_BYTES 64
#endif

#define DMA_BIT_MASK(low, high) ((1UL << (high + 1)) - (1UL << (low)))
#define DMA_BITS(low, high, n) ((n##UL << (low)) & DMA_BIT_MASK(low, high))
#define DMA_SET_FIELD(offset, mask, n)  (((uint64_t)(n) & ((mask))) << (offset) )

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _DMA_AXE_
// End generated register defines for dma
