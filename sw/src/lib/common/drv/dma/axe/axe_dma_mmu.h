// Generated register defines for dma_mmu

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _DMA_MMU_REG_DEFS_
#define _DMA_MMU_REG_DEFS_

#include <std/std_basetype.h>

#ifdef __cplusplus
extern "C" {
#endif
#define DMA_MMU_PARAM_AXI_AW 40

#define DMA_MMU_PARAM_AXI_IDW 10

#define DMA_MMU_PARAM_AXI_LENW 8

#define DMA_MMU_PARAM_N_MMU_ENTRIES 16

// Register width
#define DMA_MMU_PARAM_REG_WIDTH 64

// This register configures the MMU entry (common parameters)
#define DMA_MMU_CH_MMU_CFG_VALID_FIELD_WIDTH 1
#define DMA_MMU_CH_MMU_CFG_MULTIREG_COUNT 1

// This register configures the MMU entry
#define DMA_MMU_CH_MMU_CFG_REG_OFFSET 0x0
#define DMA_MMU_CH_MMU_CFG_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_CFG_VALID_0_BIT 0
#define DMA_MMU_CH_MMU_CFG_VALID_1_BIT 1
#define DMA_MMU_CH_MMU_CFG_VALID_2_BIT 2
#define DMA_MMU_CH_MMU_CFG_VALID_3_BIT 3
#define DMA_MMU_CH_MMU_CFG_VALID_4_BIT 4
#define DMA_MMU_CH_MMU_CFG_VALID_5_BIT 5
#define DMA_MMU_CH_MMU_CFG_VALID_6_BIT 6
#define DMA_MMU_CH_MMU_CFG_VALID_7_BIT 7
#define DMA_MMU_CH_MMU_CFG_VALID_8_BIT 8
#define DMA_MMU_CH_MMU_CFG_VALID_9_BIT 9
#define DMA_MMU_CH_MMU_CFG_VALID_10_BIT 10
#define DMA_MMU_CH_MMU_CFG_VALID_11_BIT 11
#define DMA_MMU_CH_MMU_CFG_VALID_12_BIT 12
#define DMA_MMU_CH_MMU_CFG_VALID_13_BIT 13
#define DMA_MMU_CH_MMU_CFG_VALID_14_BIT 14
#define DMA_MMU_CH_MMU_CFG_VALID_15_BIT 15

// This register configures the MMU entry: first_address (common parameters)
#define DMA_MMU_CH_MMU_FIRST_FIRST_FIELD_WIDTH 28
#define DMA_MMU_CH_MMU_FIRST_MULTIREG_COUNT 8

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_0_REG_OFFSET 0x8
#define DMA_MMU_CH_MMU_FIRST_0_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_0_FIRST_0_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_0_FIRST_0_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_0_FIRST_0_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_0_FIRST_0_MASK, .index = DMA_MMU_CH_MMU_FIRST_0_FIRST_0_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_0_FIRST_1_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_0_FIRST_1_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_0_FIRST_1_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_0_FIRST_1_MASK, .index = DMA_MMU_CH_MMU_FIRST_0_FIRST_1_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_1_REG_OFFSET 0x10
#define DMA_MMU_CH_MMU_FIRST_1_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_1_FIRST_2_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_1_FIRST_2_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_1_FIRST_2_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_1_FIRST_2_MASK, .index = DMA_MMU_CH_MMU_FIRST_1_FIRST_2_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_1_FIRST_3_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_1_FIRST_3_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_1_FIRST_3_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_1_FIRST_3_MASK, .index = DMA_MMU_CH_MMU_FIRST_1_FIRST_3_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_2_REG_OFFSET 0x18
#define DMA_MMU_CH_MMU_FIRST_2_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_2_FIRST_4_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_2_FIRST_4_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_2_FIRST_4_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_2_FIRST_4_MASK, .index = DMA_MMU_CH_MMU_FIRST_2_FIRST_4_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_2_FIRST_5_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_2_FIRST_5_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_2_FIRST_5_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_2_FIRST_5_MASK, .index = DMA_MMU_CH_MMU_FIRST_2_FIRST_5_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_3_REG_OFFSET 0x20
#define DMA_MMU_CH_MMU_FIRST_3_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_3_FIRST_6_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_3_FIRST_6_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_3_FIRST_6_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_3_FIRST_6_MASK, .index = DMA_MMU_CH_MMU_FIRST_3_FIRST_6_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_3_FIRST_7_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_3_FIRST_7_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_3_FIRST_7_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_3_FIRST_7_MASK, .index = DMA_MMU_CH_MMU_FIRST_3_FIRST_7_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_4_REG_OFFSET 0x28
#define DMA_MMU_CH_MMU_FIRST_4_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_4_FIRST_8_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_4_FIRST_8_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_4_FIRST_8_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_4_FIRST_8_MASK, .index = DMA_MMU_CH_MMU_FIRST_4_FIRST_8_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_4_FIRST_9_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_4_FIRST_9_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_4_FIRST_9_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_4_FIRST_9_MASK, .index = DMA_MMU_CH_MMU_FIRST_4_FIRST_9_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_5_REG_OFFSET 0x30
#define DMA_MMU_CH_MMU_FIRST_5_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_5_FIRST_10_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_5_FIRST_10_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_5_FIRST_10_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_5_FIRST_10_MASK, .index = DMA_MMU_CH_MMU_FIRST_5_FIRST_10_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_5_FIRST_11_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_5_FIRST_11_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_5_FIRST_11_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_5_FIRST_11_MASK, .index = DMA_MMU_CH_MMU_FIRST_5_FIRST_11_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_6_REG_OFFSET 0x38
#define DMA_MMU_CH_MMU_FIRST_6_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_6_FIRST_12_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_6_FIRST_12_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_6_FIRST_12_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_6_FIRST_12_MASK, .index = DMA_MMU_CH_MMU_FIRST_6_FIRST_12_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_6_FIRST_13_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_6_FIRST_13_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_6_FIRST_13_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_6_FIRST_13_MASK, .index = DMA_MMU_CH_MMU_FIRST_6_FIRST_13_OFFSET })

// This register configures the MMU entry: first_address
#define DMA_MMU_CH_MMU_FIRST_7_REG_OFFSET 0x40
#define DMA_MMU_CH_MMU_FIRST_7_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_FIRST_7_FIRST_14_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_7_FIRST_14_OFFSET 0
#define DMA_MMU_CH_MMU_FIRST_7_FIRST_14_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_7_FIRST_14_MASK, .index = DMA_MMU_CH_MMU_FIRST_7_FIRST_14_OFFSET })
#define DMA_MMU_CH_MMU_FIRST_7_FIRST_15_MASK 0xfffffff
#define DMA_MMU_CH_MMU_FIRST_7_FIRST_15_OFFSET 28
#define DMA_MMU_CH_MMU_FIRST_7_FIRST_15_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_FIRST_7_FIRST_15_MASK, .index = DMA_MMU_CH_MMU_FIRST_7_FIRST_15_OFFSET })

// This register configures the MMU entry: last_address (common parameters)
#define DMA_MMU_CH_MMU_LAST_LAST_FIELD_WIDTH 28
#define DMA_MMU_CH_MMU_LAST_MULTIREG_COUNT 8

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_0_REG_OFFSET 0x48
#define DMA_MMU_CH_MMU_LAST_0_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_0_LAST_0_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_0_LAST_0_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_0_LAST_0_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_0_LAST_0_MASK, .index = DMA_MMU_CH_MMU_LAST_0_LAST_0_OFFSET })
#define DMA_MMU_CH_MMU_LAST_0_LAST_1_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_0_LAST_1_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_0_LAST_1_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_0_LAST_1_MASK, .index = DMA_MMU_CH_MMU_LAST_0_LAST_1_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_1_REG_OFFSET 0x50
#define DMA_MMU_CH_MMU_LAST_1_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_1_LAST_2_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_1_LAST_2_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_1_LAST_2_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_1_LAST_2_MASK, .index = DMA_MMU_CH_MMU_LAST_1_LAST_2_OFFSET })
#define DMA_MMU_CH_MMU_LAST_1_LAST_3_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_1_LAST_3_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_1_LAST_3_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_1_LAST_3_MASK, .index = DMA_MMU_CH_MMU_LAST_1_LAST_3_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_2_REG_OFFSET 0x58
#define DMA_MMU_CH_MMU_LAST_2_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_2_LAST_4_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_2_LAST_4_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_2_LAST_4_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_2_LAST_4_MASK, .index = DMA_MMU_CH_MMU_LAST_2_LAST_4_OFFSET })
#define DMA_MMU_CH_MMU_LAST_2_LAST_5_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_2_LAST_5_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_2_LAST_5_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_2_LAST_5_MASK, .index = DMA_MMU_CH_MMU_LAST_2_LAST_5_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_3_REG_OFFSET 0x60
#define DMA_MMU_CH_MMU_LAST_3_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_3_LAST_6_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_3_LAST_6_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_3_LAST_6_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_3_LAST_6_MASK, .index = DMA_MMU_CH_MMU_LAST_3_LAST_6_OFFSET })
#define DMA_MMU_CH_MMU_LAST_3_LAST_7_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_3_LAST_7_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_3_LAST_7_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_3_LAST_7_MASK, .index = DMA_MMU_CH_MMU_LAST_3_LAST_7_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_4_REG_OFFSET 0x68
#define DMA_MMU_CH_MMU_LAST_4_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_4_LAST_8_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_4_LAST_8_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_4_LAST_8_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_4_LAST_8_MASK, .index = DMA_MMU_CH_MMU_LAST_4_LAST_8_OFFSET })
#define DMA_MMU_CH_MMU_LAST_4_LAST_9_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_4_LAST_9_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_4_LAST_9_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_4_LAST_9_MASK, .index = DMA_MMU_CH_MMU_LAST_4_LAST_9_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_5_REG_OFFSET 0x70
#define DMA_MMU_CH_MMU_LAST_5_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_5_LAST_10_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_5_LAST_10_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_5_LAST_10_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_5_LAST_10_MASK, .index = DMA_MMU_CH_MMU_LAST_5_LAST_10_OFFSET })
#define DMA_MMU_CH_MMU_LAST_5_LAST_11_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_5_LAST_11_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_5_LAST_11_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_5_LAST_11_MASK, .index = DMA_MMU_CH_MMU_LAST_5_LAST_11_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_6_REG_OFFSET 0x78
#define DMA_MMU_CH_MMU_LAST_6_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_6_LAST_12_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_6_LAST_12_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_6_LAST_12_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_6_LAST_12_MASK, .index = DMA_MMU_CH_MMU_LAST_6_LAST_12_OFFSET })
#define DMA_MMU_CH_MMU_LAST_6_LAST_13_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_6_LAST_13_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_6_LAST_13_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_6_LAST_13_MASK, .index = DMA_MMU_CH_MMU_LAST_6_LAST_13_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_LAST_7_REG_OFFSET 0x80
#define DMA_MMU_CH_MMU_LAST_7_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_LAST_7_LAST_14_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_7_LAST_14_OFFSET 0
#define DMA_MMU_CH_MMU_LAST_7_LAST_14_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_7_LAST_14_MASK, .index = DMA_MMU_CH_MMU_LAST_7_LAST_14_OFFSET })
#define DMA_MMU_CH_MMU_LAST_7_LAST_15_MASK 0xfffffff
#define DMA_MMU_CH_MMU_LAST_7_LAST_15_OFFSET 28
#define DMA_MMU_CH_MMU_LAST_7_LAST_15_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_LAST_7_LAST_15_MASK, .index = DMA_MMU_CH_MMU_LAST_7_LAST_15_OFFSET })

// This register configures the MMU entry: last_address (common parameters)
#define DMA_MMU_CH_MMU_BASE_BASE_FIELD_WIDTH 28
#define DMA_MMU_CH_MMU_BASE_MULTIREG_COUNT 8

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_0_REG_OFFSET 0x88
#define DMA_MMU_CH_MMU_BASE_0_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_0_BASE_0_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_0_BASE_0_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_0_BASE_0_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_0_BASE_0_MASK, .index = DMA_MMU_CH_MMU_BASE_0_BASE_0_OFFSET })
#define DMA_MMU_CH_MMU_BASE_0_BASE_1_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_0_BASE_1_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_0_BASE_1_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_0_BASE_1_MASK, .index = DMA_MMU_CH_MMU_BASE_0_BASE_1_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_1_REG_OFFSET 0x90
#define DMA_MMU_CH_MMU_BASE_1_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_1_BASE_2_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_1_BASE_2_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_1_BASE_2_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_1_BASE_2_MASK, .index = DMA_MMU_CH_MMU_BASE_1_BASE_2_OFFSET })
#define DMA_MMU_CH_MMU_BASE_1_BASE_3_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_1_BASE_3_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_1_BASE_3_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_1_BASE_3_MASK, .index = DMA_MMU_CH_MMU_BASE_1_BASE_3_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_2_REG_OFFSET 0x98
#define DMA_MMU_CH_MMU_BASE_2_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_2_BASE_4_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_2_BASE_4_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_2_BASE_4_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_2_BASE_4_MASK, .index = DMA_MMU_CH_MMU_BASE_2_BASE_4_OFFSET })
#define DMA_MMU_CH_MMU_BASE_2_BASE_5_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_2_BASE_5_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_2_BASE_5_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_2_BASE_5_MASK, .index = DMA_MMU_CH_MMU_BASE_2_BASE_5_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_3_REG_OFFSET 0xa0
#define DMA_MMU_CH_MMU_BASE_3_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_3_BASE_6_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_3_BASE_6_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_3_BASE_6_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_3_BASE_6_MASK, .index = DMA_MMU_CH_MMU_BASE_3_BASE_6_OFFSET })
#define DMA_MMU_CH_MMU_BASE_3_BASE_7_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_3_BASE_7_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_3_BASE_7_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_3_BASE_7_MASK, .index = DMA_MMU_CH_MMU_BASE_3_BASE_7_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_4_REG_OFFSET 0xa8
#define DMA_MMU_CH_MMU_BASE_4_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_4_BASE_8_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_4_BASE_8_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_4_BASE_8_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_4_BASE_8_MASK, .index = DMA_MMU_CH_MMU_BASE_4_BASE_8_OFFSET })
#define DMA_MMU_CH_MMU_BASE_4_BASE_9_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_4_BASE_9_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_4_BASE_9_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_4_BASE_9_MASK, .index = DMA_MMU_CH_MMU_BASE_4_BASE_9_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_5_REG_OFFSET 0xb0
#define DMA_MMU_CH_MMU_BASE_5_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_5_BASE_10_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_5_BASE_10_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_5_BASE_10_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_5_BASE_10_MASK, .index = DMA_MMU_CH_MMU_BASE_5_BASE_10_OFFSET })
#define DMA_MMU_CH_MMU_BASE_5_BASE_11_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_5_BASE_11_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_5_BASE_11_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_5_BASE_11_MASK, .index = DMA_MMU_CH_MMU_BASE_5_BASE_11_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_6_REG_OFFSET 0xb8
#define DMA_MMU_CH_MMU_BASE_6_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_6_BASE_12_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_6_BASE_12_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_6_BASE_12_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_6_BASE_12_MASK, .index = DMA_MMU_CH_MMU_BASE_6_BASE_12_OFFSET })
#define DMA_MMU_CH_MMU_BASE_6_BASE_13_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_6_BASE_13_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_6_BASE_13_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_6_BASE_13_MASK, .index = DMA_MMU_CH_MMU_BASE_6_BASE_13_OFFSET })

// This register configures the MMU entry: last_address
#define DMA_MMU_CH_MMU_BASE_7_REG_OFFSET 0xc0
#define DMA_MMU_CH_MMU_BASE_7_REG_RESVAL 0x0
#define DMA_MMU_CH_MMU_BASE_7_BASE_14_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_7_BASE_14_OFFSET 0
#define DMA_MMU_CH_MMU_BASE_7_BASE_14_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_7_BASE_14_MASK, .index = DMA_MMU_CH_MMU_BASE_7_BASE_14_OFFSET })
#define DMA_MMU_CH_MMU_BASE_7_BASE_15_MASK 0xfffffff
#define DMA_MMU_CH_MMU_BASE_7_BASE_15_OFFSET 28
#define DMA_MMU_CH_MMU_BASE_7_BASE_15_FIELD \
  ((bitfield_field32_t) { .mask = DMA_MMU_CH_MMU_BASE_7_BASE_15_MASK, .index = DMA_MMU_CH_MMU_BASE_7_BASE_15_OFFSET })

typedef struct {
  reg64_t ch_mmu_cfg; // 0x00
  reg64_t ch_mmu_first_0; // 0x08
  reg64_t ch_mmu_first_1; // 0x10
  reg64_t ch_mmu_first_2; // 0x18
  reg64_t ch_mmu_first_3; // 0x20
  reg64_t ch_mmu_first_4; // 0x28
  reg64_t ch_mmu_first_5; // 0x30
  reg64_t ch_mmu_first_6; // 0x38
  reg64_t ch_mmu_first_7; // 0x40
  reg64_t ch_mmu_last_0; // 0x48
  reg64_t ch_mmu_last_1; // 0x50
  reg64_t ch_mmu_last_2; // 0x58
  reg64_t ch_mmu_last_3; // 0x60
  reg64_t ch_mmu_last_4; // 0x68
  reg64_t ch_mmu_last_5; // 0x70
  reg64_t ch_mmu_last_6; // 0x78
  reg64_t ch_mmu_last_7; // 0x80
  reg64_t ch_mmu_base_0; // 0x88
  reg64_t ch_mmu_base_1; // 0x90
  reg64_t ch_mmu_base_2; // 0x98
  reg64_t ch_mmu_base_3; // 0xa0
  reg64_t ch_mmu_base_4; // 0xa8
  reg64_t ch_mmu_base_5; // 0xb0
  reg64_t ch_mmu_base_6; // 0xb8
  reg64_t ch_mmu_base_7; // 0xc0
} HalDma_MmuReg;

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _DMA_MMU_REG_DEFS_
// End generated register defines for dma_mmu
