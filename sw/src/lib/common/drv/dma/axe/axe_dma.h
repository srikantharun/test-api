// Generated register defines for dma

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _DMA_REG_DEFS_
#define _DMA_REG_DEFS_

#include <std/std_basetype.h>

#ifdef __cplusplus
extern "C" {
#endif
#define DMA_PARAM_AXI_AW 40

#define DMA_PARAM_AXI_IDW 10

#define DMA_PARAM_AXI_LENW 8

// Register width
#define DMA_PARAM_REG_WIDTH 64

//  This register  defines the mode in which each channel will operate.
#define DMA_CH_MODE_REG_OFFSET 0x0
#define DMA_CH_MODE_REG_RESVAL 0x0
#define DMA_CH_MODE_CH0_MODE_BIT 0
#define DMA_CH_MODE_CH1_MODE_BIT 1
#define DMA_CH_MODE_CH2_MODE_BIT 2
#define DMA_CH_MODE_CH3_MODE_BIT 3

// This register indicates if the channels are busy.
#define DMA_CH_STATUS_REG_OFFSET 0x8
#define DMA_CH_STATUS_REG_RESVAL 0x0
#define DMA_CH_STATUS_CH0_BUSY_BIT 0
#define DMA_CH_STATUS_CH1_BUSY_BIT 1
#define DMA_CH_STATUS_CH2_BUSY_BIT 2
#define DMA_CH_STATUS_CH3_BUSY_BIT 3

typedef struct {
  reg64_t ch_mode; // 0x00
  reg64_t ch_status; // 0x08
} HalDmaReg;

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _DMA_REG_DEFS_
// End generated register defines for dma
