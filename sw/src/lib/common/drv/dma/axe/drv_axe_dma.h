// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Description:
// Owner:

#ifndef DRV_DMA_H_
#define DRV_DMA_H_
#include <std/std_basetype.h>
#include <stdint.h>
#include <util.h>
#include "regdef_axe_dma.h"

typedef struct {
  reg64_t ch_mode; // 0x00
  reg64_t ch_status; // 0x08
} axe_dma_regs;

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
} axe_dma_mmu_regs;

typedef struct {
  reg64_t ch_ctrl; // 0x00
  reg64_t ch_cfg; // 0x08
  reg64_t ch_src_addr; // 0x10
  reg64_t ch_dst_addr; // 0x18
  reg64_t ch_xbytesize; // 0x20
  reg64_t ch_yrowsize; // 0x28
  reg64_t ch_tran_cfg; // 0x30
  reg64_t ch_xaddrinc; // 0x38
  reg64_t ch_yaddrstride; // 0x40
  reg64_t ch_link_descr; // 0x48
  reg64_t ch_status; // 0x50
  reg64_t ch_err_info; // 0x58
  reg64_t ch_req_bus_ctrl; // 0x60
} axe_dma_ch_regs;

typedef struct {
  axe_dma_regs* axe_dma_regs;
  axe_dma_mmu_regs* axe_dma_mmu_regs;
  axe_dma_ch_regs* regs;
  uint8_t id;
} axe_dma_channel;


// Common fields macro
#define DMA_COMMON_FIELDS \
   axe_dma_channel* chan;

#define DMA_CTRL_FIELDS \
    uint64_t src_ms; \
    uint64_t dst_ms; \
    uint64_t irq_en; \
    uint64_t irq_clr; \
    uint64_t src_osr_lmt; \
    uint64_t dst_osr_lmt;

// 1D-specific fields macro
#define DMA_1D_FIELDS \
    uintptr_t src_addr; \
    uintptr_t dst_addr; \
    uint64_t src_xbytesize; \
    uint64_t dst_xbytesize; \
    uint64_t src_xaddrinc; \
    uint64_t dst_xaddrinc; \
    uint64_t tran_size; \
    uint64_t xtype; \
    uint64_t fillval_mode; \
    uint64_t fillval; \
    uint64_t src_burstlen; \
    uint64_t dst_burstlen;

// 2D-specific fields macro
#define DMA_2D_FIELDS \
    uint64_t ytype; \
    uint64_t src_yrowsize; \
    uint64_t dst_yrowsize; \
    uint64_t src_yaddrstride; \
    uint64_t dst_yaddrstride;

// Linked List specific fields macro
#define DMA_LL_FIELDS \
    uintptr_t next_ll; \
    uint64_t ll_last;

#define DMA_LL_CTRL_FIELDS \
    uint64_t ll_ms; \
    uint64_t ll_mode; \
    uint64_t ll_en; \
    uint64_t irq_en; \
    uint64_t irq_clr;

// Define the DMA CTRL config structure
typedef struct {
    DMA_COMMON_FIELDS;
    DMA_CTRL_FIELDS;
} axe_dma_ctrl_config;

// Define the 1D DMA config structure
typedef struct {
    DMA_COMMON_FIELDS;
    DMA_1D_FIELDS;
} axe_dma_1d_config;

// Define the 2D DMA config structure
typedef struct {
    DMA_COMMON_FIELDS;
    DMA_1D_FIELDS;
    DMA_2D_FIELDS;
} axe_dma_2d_config;

typedef struct {
    DMA_COMMON_FIELDS;
    DMA_LL_FIELDS;
} axe_dma_ll_config;

typedef struct {
    DMA_COMMON_FIELDS;
    DMA_LL_CTRL_FIELDS;
} axe_dma_ll_ctrl_config;


/* Bitfields in CH_MODE */
#define DMA_CH_MODE(id) BIT(id)

/* Bitfields in CH_CTRL */
#define DMA_CH_CTRL_ENABLE BIT(DMA_CHANNEL_CH_CTRL_ENABLE_BIT)
#define DMA_CH_CTRL_CLEAR BIT(DMA_CHANNEL_CH_CTRL_CLEAR_BIT)
#define DMA_CH_CTRL_INTR_ENABLE BIT(DMA_CHANNEL_CH_CTRL_INTERRUPT_EN_BIT)
#define DMA_CH_CTRL_INTR_CLEAR BIT(DMA_CHANNEL_CH_CTRL_INTERRUPT_CLR_BIT)
#define DMA_CH_CTRL_SRC_OSR_LMT(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_OFFSET, DMA_CHANNEL_CH_CTRL_SRC_OSR_LMT_MASK, n)
#define DMA_CH_CTRL_DST_OSR_LMT(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_OFFSET, DMA_CHANNEL_CH_CTRL_DST_OSR_LMT_MASK, n)
#define DMA_CH_CTRL_SRC_MS(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CTRL_SRC_MS_OFFSET, DMA_CHANNEL_CH_CTRL_SRC_MS_MASK, n)
#define DMA_CH_CTRL_DST_MS(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CTRL_DST_MS_OFFSET, DMA_CHANNEL_CH_CTRL_DST_MS_MASK, n)
#define DMA_CH_CTRL_LL_MS(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CTRL_LL_MS_OFFSET, DMA_CHANNEL_CH_CTRL_LL_MS_MASK, n)
#define DMA_CH_CTRL_LL_EN BIT(DMA_CHANNEL_CH_CTRL_LL_EN_BIT)
#define DMA_CH_CTRL_LL_MODE BIT(DMA_CHANNEL_CH_CTRL_LL_MODE_BIT)

/* Bitfields in CH_CFG */
#define DMA_CH_CFG_TRAN_SIZE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CFG_TRANSIZE_OFFSET, DMA_CHANNEL_CH_CFG_TRANSIZE_MASK, n)
#define DMA_CH_CFG_XTYPE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CFG_XTYPE_OFFSET, DMA_CHANNEL_CH_CFG_XTYPE_MASK, n)
#define DMA_CH_CFG_YTYPE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CFG_YTYPE_OFFSET, DMA_CHANNEL_CH_CFG_YTYPE_MASK, n)
#define DMA_CH_CFG_FILLVAL_MODE BIT(DMA_CHANNEL_CH_CFG_FILLVAL_MODE_BIT)
#define DMA_CH_CFG_FILLVAL(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CFG_FILLVAL_OFFSET, DMA_CHANNEL_CH_CFG_FILLVAL_MASK, n)
#define DMA_CH_CFG_SRC_BURSTLEN(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_OFFSET, DMA_CHANNEL_CH_CFG_SRC_BURSTLEN_MASK, n)
#define DMA_CH_CFG_DST_BURSTLEN(n) DMA_SET_FIELD(DMA_CHANNEL_CH_CFG_DST_BURSTLEN_OFFSET, DMA_CHANNEL_CH_CFG_DST_BURSTLEN_MASK, n)
#define DMA_CH_CFG_TRANSFORM_EN BIT(DMA_CHANNEL_CH_CFG_TRANSFORM_EN_BIT)

/* Bitfields in CH_SRC_ADDR */
#define DMA_CH_SRC_ADDR(n) DMA_BITS(63, 0, n)

/* Bitfields in CH_DST_ADDR */
#define DMA_CH_DST_ADDR(n) DMA_BITS(63, 0, n)

/* Bitfields in CH_XBYTESIZE */
#define DMA_CH_CFG_SRC_XBYTESIZE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_OFFSET, DMA_CHANNEL_CH_XBYTESIZE_SRC_XBYTESIZE_MASK, n)
#define DMA_CH_CFG_DST_XBYTESIZE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_OFFSET, DMA_CHANNEL_CH_XBYTESIZE_DST_XBYTESIZE_MASK, n)

/* Bitfields in CH_YROWSIZE */
#define DMA_CH_CFG_SRC_CH_YROWSIZE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_OFFSET, DMA_CHANNEL_CH_YROWSIZE_SRC_YROWSIZE_MASK, n)
#define DMA_CH_CFG_DST_CH_YROWSIZE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_OFFSET, DMA_CHANNEL_CH_YROWSIZE_DST_YROWSIZE_MASK, n)

/* TODO: Bitfields in Transfer Config */

/* Bitfields in CH_XADDRINC */
#define DMA_CH_CFG_SRC_CH_XADDRINC(n) DMA_SET_FIELD(DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_OFFSET, DMA_CHANNEL_CH_XADDRINC_SRC_XADDRINC_MASK, n)
#define DMA_CH_CFG_DST_CH_XADDRINC(n) DMA_SET_FIELD(DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_OFFSET, DMA_CHANNEL_CH_XADDRINC_DST_XADDRINC_MASK, n)

/* Bitfields in YADDRSTRIDE */
#define DMA_CH_CFG_SRC_CH_YADDRSTRIDE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_OFFSET, DMA_CHANNEL_CH_YADDRSTRIDE_SRC_YADDRSTRIDE_MASK, n)
#define DMA_CH_CFG_DST_CH_YADDRSTRIDE(n) DMA_SET_FIELD(DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_OFFSET, DMA_CHANNEL_CH_YADDRSTRIDE_DST_YADDRSTRIDE_MASK, n)

/* Bitfields in LINK_DESCR */
#define DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR(n) DMA_SET_FIELD(DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_OFFSET, DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR_MASK, n)
#define DMA_CHANNEL_CH_LINK_DESCR_LAST    BIT(DMA_CHANNEL_CH_LINK_DESCR_LL_LAST_BIT)

/* Channel configuration helpers */
void axe_dma_init_channel(axe_dma_channel* chan, axe_dma_regs* axe_dma_regs, uint64_t id);
// void axe_dma_enable_channel(axe_dma_channel* chan, uint64_t src_osr_lmt, uint64_t  dst_osr_lmt,
//                             uint64_t src_ms, uint64_t dst_ms, uint64_t irq_en, uint64_t irq_clr );
void axe_dma_enable_channel(const axe_dma_ctrl_config* config);
void axe_dma_configure_1d_transfer(const axe_dma_1d_config* config);
void axe_dma_configure_2d_transfer(const axe_dma_2d_config* config);

void axe_dma_setup_ll(const axe_dma_ll_config* config);
void axe_dma_enable_ll(const axe_dma_ll_ctrl_config* config);


/* Status helpers */
int axe_dma_transfer_done(axe_dma_channel* chan);
int axe_dma_channel_enabled(axe_dma_channel* chan);


#endif  // DRV_DMA_H_
