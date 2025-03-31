// Generated register defines for dma_channel

// Copyright information found in source file:
// Copyright lowRISC contributors.

// Licensing information found in source file:
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef _DMA_CHANNEL_REG_DEFS_
#define _DMA_CHANNEL_REG_DEFS_

#include <std/std_basetype.h>

#ifdef __cplusplus
extern "C" {
#endif
#define DMA_CHANNEL_PARAM_AXI_AW 40

#define DMA_CHANNEL_PARAM_AXI_IDW 10

#define DMA_CHANNEL_PARAM_AXI_LENW 8

// Register width
#define DMA_CHANNEL_PARAM_REG_WIDTH 64

// Control register of the CMD Block.
#define DMA_CHANNEL_CMDBLK_CTRL_REG_OFFSET 0x0
#define DMA_CHANNEL_CMDBLK_CTRL_REG_RESVAL 0x0
#define DMA_CHANNEL_CMDBLK_CTRL_EXEC_EN_BIT 0
#define DMA_CHANNEL_CMDBLK_CTRL_PTR_RST_BIT 1

// Status register of the CMD Block.
#define DMA_CHANNEL_CMDBLK_STATUS_REG_OFFSET 0x8
#define DMA_CHANNEL_CMDBLK_STATUS_REG_RESVAL 0x0
#define DMA_CHANNEL_CMDBLK_STATUS_STATE_MASK 0x3
#define DMA_CHANNEL_CMDBLK_STATUS_STATE_OFFSET 0
#define DMA_CHANNEL_CMDBLK_STATUS_STATE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CMDBLK_STATUS_STATE_MASK, .index = DMA_CHANNEL_CMDBLK_STATUS_STATE_OFFSET })
#define DMA_CHANNEL_CMDBLK_STATUS_WAIT_TOKEN_BIT 2
#define DMA_CHANNEL_CMDBLK_STATUS_IN_WORD_PTR_MASK 0xff
#define DMA_CHANNEL_CMDBLK_STATUS_IN_WORD_PTR_OFFSET 8
#define DMA_CHANNEL_CMDBLK_STATUS_IN_WORD_PTR_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CMDBLK_STATUS_IN_WORD_PTR_MASK, .index = DMA_CHANNEL_CMDBLK_STATUS_IN_WORD_PTR_OFFSET })
#define DMA_CHANNEL_CMDBLK_STATUS_FIFO_CNT_MASK 0xff
#define DMA_CHANNEL_CMDBLK_STATUS_FIFO_CNT_OFFSET 16
#define DMA_CHANNEL_CMDBLK_STATUS_FIFO_CNT_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CMDBLK_STATUS_FIFO_CNT_MASK, .index = DMA_CHANNEL_CMDBLK_STATUS_FIFO_CNT_OFFSET })
#define DMA_CHANNEL_CMDBLK_STATUS_OUTST_CMDS_MASK 0xff
#define DMA_CHANNEL_CMDBLK_STATUS_OUTST_CMDS_OFFSET 24
#define DMA_CHANNEL_CMDBLK_STATUS_OUTST_CMDS_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CMDBLK_STATUS_OUTST_CMDS_MASK, .index = DMA_CHANNEL_CMDBLK_STATUS_OUTST_CMDS_OFFSET })
#define DMA_CHANNEL_CMDBLK_STATUS_PENDING_TOKENS_MASK 0xffff
#define DMA_CHANNEL_CMDBLK_STATUS_PENDING_TOKENS_OFFSET 32
#define DMA_CHANNEL_CMDBLK_STATUS_PENDING_TOKENS_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CMDBLK_STATUS_PENDING_TOKENS_MASK, .index = DMA_CHANNEL_CMDBLK_STATUS_PENDING_TOKENS_OFFSET })

// The Channel DMA Control register allows the SW to control the operation of
// a DMA instruction.
#define DMA_CHANNEL_CH_CTRL_REG_OFFSET 0x100
#define DMA_CHANNEL_CH_CTRL_REG_RESVAL 0x8079e000
#define DMA_CHANNEL_CH_CTRL_ENABLE_BIT 0
#define DMA_CHANNEL_CH_CTRL_CLEAR_BIT 1
#define DMA_CHANNEL_CH_CTRL_INTERRUPT_EN_BIT 8
#define DMA_CHANNEL_CH_CTRL_INTERRUPT_CLR_BIT 9
#define DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_MASK 0x3f
#define DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_OFFSET 13
#define DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_MASK, .index = DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_OFFSET })
#define DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_MASK 0x3f
#define DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_OFFSET 19
#define DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_MASK, .index = DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_OFFSET })
#define DMA_CHANNEL_CH_CTRL_SRC_MS_MASK 0x3
#define DMA_CHANNEL_CH_CTRL_SRC_MS_OFFSET 25
#define DMA_CHANNEL_CH_CTRL_SRC_MS_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CTRL_SRC_MS_MASK, .index = DMA_CHANNEL_CH_CTRL_SRC_MS_OFFSET })
#define DMA_CHANNEL_CH_CTRL_DST_MS_MASK 0x3
#define DMA_CHANNEL_CH_CTRL_DST_MS_OFFSET 27
#define DMA_CHANNEL_CH_CTRL_DST_MS_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CTRL_DST_MS_MASK, .index = DMA_CHANNEL_CH_CTRL_DST_MS_OFFSET })
#define DMA_CHANNEL_CH_CTRL_LL_MS_MASK 0x3
#define DMA_CHANNEL_CH_CTRL_LL_MS_OFFSET 29
#define DMA_CHANNEL_CH_CTRL_LL_MS_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CTRL_LL_MS_MASK, .index = DMA_CHANNEL_CH_CTRL_LL_MS_OFFSET })
#define DMA_CHANNEL_CH_CTRL_MMU_EN_BIT 31
#define DMA_CHANNEL_CH_CTRL_OVERALLOC_MODE_MASK 0x3
#define DMA_CHANNEL_CH_CTRL_OVERALLOC_MODE_OFFSET 32
#define DMA_CHANNEL_CH_CTRL_OVERALLOC_MODE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CTRL_OVERALLOC_MODE_MASK, .index = DMA_CHANNEL_CH_CTRL_OVERALLOC_MODE_OFFSET })
#define DMA_CHANNEL_CH_CTRL_LL_EN_BIT 48
#define DMA_CHANNEL_CH_CTRL_LL_MODE_BIT 49

// The Channel DMA Control register allows the SW to configure the DMA
// instruction/transfer.
#define DMA_CHANNEL_CH_CFG_REG_OFFSET 0x108
#define DMA_CHANNEL_CH_CFG_REG_RESVAL 0x3f3f00000016
#define DMA_CHANNEL_CH_CFG_TRANSIZE_MASK 0xf
#define DMA_CHANNEL_CH_CFG_TRANSIZE_OFFSET 0
#define DMA_CHANNEL_CH_CFG_TRANSIZE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CFG_TRANSIZE_MASK, .index = DMA_CHANNEL_CH_CFG_TRANSIZE_OFFSET })
#define DMA_CHANNEL_CH_CFG_XTYPE_MASK 0xf
#define DMA_CHANNEL_CH_CFG_XTYPE_OFFSET 4
#define DMA_CHANNEL_CH_CFG_XTYPE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CFG_XTYPE_MASK, .index = DMA_CHANNEL_CH_CFG_XTYPE_OFFSET })
#define DMA_CHANNEL_CH_CFG_YTYPE_MASK 0xf
#define DMA_CHANNEL_CH_CFG_YTYPE_OFFSET 8
#define DMA_CHANNEL_CH_CFG_YTYPE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CFG_YTYPE_MASK, .index = DMA_CHANNEL_CH_CFG_YTYPE_OFFSET })
#define DMA_CHANNEL_CH_CFG_FILLVAL_MODE_BIT 12
#define DMA_CHANNEL_CH_CFG_FILLVAL_MASK 0xffff
#define DMA_CHANNEL_CH_CFG_FILLVAL_OFFSET 16
#define DMA_CHANNEL_CH_CFG_FILLVAL_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CFG_FILLVAL_MASK, .index = DMA_CHANNEL_CH_CFG_FILLVAL_OFFSET })
#define DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_MASK 0xff
#define DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_OFFSET 32
#define DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_MASK, .index = DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_OFFSET })
#define DMA_CHANNEL_CH_CFG_DST_BURSTLEN_MASK 0xff
#define DMA_CHANNEL_CH_CFG_DST_BURSTLEN_OFFSET 40
#define DMA_CHANNEL_CH_CFG_DST_BURSTLEN_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_CFG_DST_BURSTLEN_MASK, .index = DMA_CHANNEL_CH_CFG_DST_BURSTLEN_OFFSET })
#define DMA_CHANNEL_CH_CFG_TRANSFORM_EN_BIT 50

// Source Address
#define DMA_CHANNEL_CH_SRC_ADDR_REG_OFFSET 0x110
#define DMA_CHANNEL_CH_SRC_ADDR_REG_RESVAL 0x0

// Destination Address
#define DMA_CHANNEL_CH_DST_ADDR_REG_OFFSET 0x118
#define DMA_CHANNEL_CH_DST_ADDR_REG_RESVAL 0x0

// X Byte Size
#define DMA_CHANNEL_CH_XBYTESIZE_REG_OFFSET 0x120
#define DMA_CHANNEL_CH_XBYTESIZE_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_MASK 0xffffffff
#define DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_OFFSET 0
#define DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_MASK, .index = DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_OFFSET })
#define DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_MASK 0xffffffff
#define DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_OFFSET 32
#define DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_MASK, .index = DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_OFFSET })

// Y Row Size
#define DMA_CHANNEL_CH_YROWSIZE_REG_OFFSET 0x128
#define DMA_CHANNEL_CH_YROWSIZE_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_MASK 0xffffffff
#define DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_OFFSET 0
#define DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_MASK, .index = DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_OFFSET })
#define DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_MASK 0xffffffff
#define DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_OFFSET 32
#define DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_MASK, .index = DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_OFFSET })

// Transfer Config
#define DMA_CHANNEL_CH_TRAN_CFG_REG_OFFSET 0x130
#define DMA_CHANNEL_CH_TRAN_CFG_REG_RESVAL 0x40000000400
#define DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRLO_MASK 0xf
#define DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRLO_OFFSET 0
#define DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRLO_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRLO_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRLO_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRHI_MASK 0xf
#define DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRHI_OFFSET 4
#define DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRHI_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRHI_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_SRCMEMATTRHI_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_SRCSHAREATTR_MASK 0x3
#define DMA_CHANNEL_CH_TRAN_CFG_SRCSHAREATTR_OFFSET 8
#define DMA_CHANNEL_CH_TRAN_CFG_SRCSHAREATTR_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_SRCSHAREATTR_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_SRCSHAREATTR_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_SRCNONSECATTR_BIT 10
#define DMA_CHANNEL_CH_TRAN_CFG_SRCPRIVATTR_BIT 11
#define DMA_CHANNEL_CH_TRAN_CFG_SRCUSERFIELD_MASK 0x3ff
#define DMA_CHANNEL_CH_TRAN_CFG_SRCUSERFIELD_OFFSET 15
#define DMA_CHANNEL_CH_TRAN_CFG_SRCUSERFIELD_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_SRCUSERFIELD_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_SRCUSERFIELD_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRLO_MASK 0xf
#define DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRLO_OFFSET 32
#define DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRLO_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRLO_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRLO_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRHI_MASK 0xf
#define DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRHI_OFFSET 36
#define DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRHI_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRHI_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_DSTMEMATTRHI_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_DSTSHAREATTR_MASK 0x3
#define DMA_CHANNEL_CH_TRAN_CFG_DSTSHAREATTR_OFFSET 40
#define DMA_CHANNEL_CH_TRAN_CFG_DSTSHAREATTR_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_DSTSHAREATTR_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_DSTSHAREATTR_OFFSET })
#define DMA_CHANNEL_CH_TRAN_CFG_DSTNONSECATTR_BIT 42
#define DMA_CHANNEL_CH_TRAN_CFG_DSTPRIVATTR_BIT 43
#define DMA_CHANNEL_CH_TRAN_CFG_DSTUSERFIELD_MASK 0x3ff
#define DMA_CHANNEL_CH_TRAN_CFG_DSTUSERFIELD_OFFSET 47
#define DMA_CHANNEL_CH_TRAN_CFG_DSTUSERFIELD_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_TRAN_CFG_DSTUSERFIELD_MASK, .index = DMA_CHANNEL_CH_TRAN_CFG_DSTUSERFIELD_OFFSET })

// X dimension increment
#define DMA_CHANNEL_CH_XADDRINC_REG_OFFSET 0x138
#define DMA_CHANNEL_CH_XADDRINC_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_MASK 0xffffffff
#define DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_OFFSET 0
#define DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_MASK, .index = DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_OFFSET })
#define DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_MASK 0xffffffff
#define DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_OFFSET 32
#define DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_MASK, .index = DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_OFFSET })

// Y dimension Stride
#define DMA_CHANNEL_CH_YADDRSTRIDE_REG_OFFSET 0x140
#define DMA_CHANNEL_CH_YADDRSTRIDE_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_MASK 0xffffffff
#define DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_OFFSET 0
#define DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_MASK, .index = DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_OFFSET })
#define DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_MASK 0xffffffff
#define DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_OFFSET 32
#define DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_MASK, .index = DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_OFFSET })

// Linked List Register
#define DMA_CHANNEL_CH_LINK_DESCR_REG_OFFSET 0x148
#define DMA_CHANNEL_CH_LINK_DESCR_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_LINK_DESCR_LL_LAST_BIT 0
#define DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_MASK 0x1fffffffffffffff
#define DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_OFFSET 3
#define DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_MASK, .index = DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_OFFSET })

// Channel Status Register
#define DMA_CHANNEL_CH_STATUS_REG_OFFSET 0x150
#define DMA_CHANNEL_CH_STATUS_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_STATUS_LINK_ADDR_BIT 0

// Channel Error Reporting Register
#define DMA_CHANNEL_CH_ERR_INFO_REG_OFFSET 0x158
#define DMA_CHANNEL_CH_ERR_INFO_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_ERR_INFO_SLV_ERR_BIT 0
#define DMA_CHANNEL_CH_ERR_INFO_DEC_ERR_BIT 1
#define DMA_CHANNEL_CH_ERR_INFO_CFG_ERR_BIT 2
#define DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_BIT 3
#define DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_TYPE_BIT 5
#define DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_MEM_LOC_MASK 0x3ffffff
#define DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_MEM_LOC_OFFSET 6
#define DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_MEM_LOC_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_MEM_LOC_MASK, .index = DMA_CHANNEL_CH_ERR_INFO_ECC_ERR_MEM_LOC_OFFSET })

// Margin of overcommitting to the bus
#define DMA_CHANNEL_CH_REQ_BUS_CTRL_REG_OFFSET 0x160
#define DMA_CHANNEL_CH_REQ_BUS_CTRL_REG_RESVAL 0x0
#define DMA_CHANNEL_CH_REQ_BUS_CTRL_OVERCOMMIT_MASK 0xff
#define DMA_CHANNEL_CH_REQ_BUS_CTRL_OVERCOMMIT_OFFSET 0
#define DMA_CHANNEL_CH_REQ_BUS_CTRL_OVERCOMMIT_FIELD \
  ((bitfield_field32_t) { .mask = DMA_CHANNEL_CH_REQ_BUS_CTRL_OVERCOMMIT_MASK, .index = DMA_CHANNEL_CH_REQ_BUS_CTRL_OVERCOMMIT_OFFSET })

typedef struct {
  reg64_t cmdblk_ctrl; // 0x00
  reg64_t cmdblk_status; // 0x08
  reg64_t reserved1[30]; // 0x10 .. 0xf8
  reg64_t ch_ctrl; // 0x100
  reg64_t ch_cfg; // 0x108
  reg64_t ch_src_addr; // 0x110
  reg64_t ch_dst_addr; // 0x118
  reg64_t ch_xbytesize; // 0x120
  reg64_t ch_yrowsize; // 0x128
  reg64_t ch_tran_cfg; // 0x130
  reg64_t ch_xaddrinc; // 0x138
  reg64_t ch_yaddrstride; // 0x140
  reg64_t ch_link_descr; // 0x148
  reg64_t ch_status; // 0x150
  reg64_t ch_err_info; // 0x158
  reg64_t ch_req_bus_ctrl; // 0x160
} HalDma_ChannelReg;

#ifdef __cplusplus
}  // extern "C"
#endif
#endif  // _DMA_CHANNEL_REG_DEFS_
// End generated register defines for dma_channel
