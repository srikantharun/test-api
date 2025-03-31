// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#ifndef DRV_SNPS_DMA_H
#define DRV_SNPS_DMA_H

/*
 * DMA introduction
 * ````````````````
 * There is no documentation on how to use the Synopsy DMA, hence some comments:
 *
 * Transfer size: Hardcoded to 64B, so if BLOCK_TS is set to 3 the DMA will transfer (3+1)*64B = 256B.
 *
 * Alignement transfers: Source and destination addresses are ideally aligned to 64B.
 * Unaligned transfers: TODO
 * Linked list transfers: TODO, items have to be aligned to 64B.
 *
 * Transfer Type and Flow Control: We only support 'Memory to Memory'.
 *
 * Master interfaces: The LP DMAs inside APU and AI Cores have only one AXI master interfaces (M1) which is connected
 * to all memories.
 *
 * For more details, check the following sources:
 *  - Datasheet of the DMA controller (DW_axi_dmac_databook.pdf)
 *  - Internal documentation (https://axeleraai.atlassian.net/wiki/x/0AIYGg)
 *
 */

#include <std/std_basetype.h>
#include <stdint.h>
#include <memorymap.h>
#include <util.h>
#include <dma/snps/drv_snps_dma_helper.h>


// todo: import something similar or share it in common header
#define DMA_BIT_MASK(low, high) ((1UL << (high + 1)) - (1UL << (low)))
#define DMA_BITS(low, high, n) ((n##UL << (low)) & DMA_BIT_MASK(low, high))

#define DMAC_MAX_CHANNELS 4
#define DMAC_MAX_MASTERS 2

#define COMMON_REG_LEN 0x100
#define CH_REG_LEN 0x100

/* Common registers offset */
typedef struct {
    reg64_t id;                          // 0x000 - Component ID Register
    reg64_t compver;                     // 0x008 - Component Version Register
    reg64_t cfg;                         // 0x010 - Global Configuration Register
    reg64_t chen;                        // 0x018 - Channel Enable Register
    reg64_t chsuspreg;                   // 0x020 - Channel Suspend Register
    reg64_t chabortreg;                  // 0x028 - Channel Abort Register
    reg64_t intstatus;                   // 0x030 - Combined Interrupt Status Register
    reg64_t commonreg_intclear;          // 0x038 - Common Register Space Interrupt Clear Register
    reg64_t commonreg_intstatus_enable;  // 0x040 - Common Register Space Interrupt Enable Register
    reg64_t commonreg_intsignal_enable;  // 0x048 - Common Register Space Interrupt Signal Enable Register
    reg64_t commonreg_intstatus;         // 0x050 - Common Register Space Interrupt Status Register
    reg64_t reset;                       // 0x058 - Software Reset Register
    reg64_t lowpower_cfg;                // 0x060 - Low Power Configuration Register
    reg64_t reserved;                    // 0x068
    reg64_t common_parctl;               // 0x070 - Parity Control Register
    reg64_t common_eccctlstatus;         // 0x078 - ECC Control and Status Register
} snps_dmac_regs;

/* Bitfields in DMAC_CFG */
#define DMAC_CFG_INT_EN BIT(1)   // This bit is used to globally enable the interrupt generation
#define DMAC_CFG_DMAC_EN BIT(0)  // This bit is used to enable the DW_axi_dmac

/* Bitfields in DMAC_CHEN (n must be 1-4) */
#define DMAC_CHEN_CH_EN(id) BIT(id)          // Enable channel n
#define DMAC_CHEN_CH_EN_WE(id) BIT(id + 8)   // Write enable
#define DMAC_CHEN_SUSP(id) BIT(id + 16)      // Channel n Suspend Request
#define DMAC_CHEN_SUSP_WE(id) BIT(id + 24)   // Write enable
#define DMAC_CHEN_ABORT(id) BIT(id + 32)     // Channel n Abort Request
#define DMAC_CHEN_ABORT_WE(id) BIT(id + 40)  // Write enable

/* Bitfields in DMAC_INTSTATUS           -> add when needed */
#define CH_INTSTAT_ECC_PROT_UIDMem_UnCorrERR BIT(35)
#define CH_INTSTAT_ECC_PROT_UIDMem_CorrERR BIT(34)
#define CH_INTSTAT_ECC_PROT_CHMem_UnCorrERR BIT(33)
#define CH_INTSTAT_ECC_PROT_CHMem_CorrERR BIT(32)
#define CH_INTSTAT_CH_ABORTED BIT(31)
#define CH_INTSTAT_CH_DISABLED BIT(30)
#define CH_INTSTAT_CH_SUSPENDED BIT(29)
#define CH_INTSTAT_CH_SRC_SUSPENDED BIT(28)
#define CH_INTSTAT_CH_LOCK_CLEARED BIT(27)
#define CH_INTSTAT_SLVIF_WRPARITY_ERR BIT(25)
#define CH_INTSTAT_SLVIF_WRONHOLD_ERR BIT(21)
#define CH_INTSTAT_SLVIF_SHADOWREG_WRON_VALID_ERR BIT(20)
#define CH_INTSTAT_SLVIF_WRONCHEN_ERR BIT(19)
#define CH_INTSTAT_SLVIF_RD2RWO_ERR BIT(18)
#define CH_INTSTAT_SLVIF_WR2RO_ERR BIT(17)
#define CH_INTSTAT_SL VIF_DEC_ERR BIT(16)
#define CH_INTSTAT_SLVIF_MULTIBLKTYPE_ERR BIT(14)
#define CH_INTSTAT_SHADOWREG_OR_LLI_INVALID_ERR BIT(13)
#define CH_INTSTAT_LLI_WR_SLV_ERR BIT(12)
#define CH_INTSTAT_LLI_RD_SLV_ERR BIT(11)
#define CH_INTSTAT_LLI_WR_DEC_ERR BIT(10)
#define CH_INTSTAT_LLI_RD_DEC_ERR BIT(9)
#define CH_INTSTAT_DST_SLV_ERR BIT(8)
#define CH_INTSTAT_SRC_SLV_ERR BIT(7)
#define CH_INTSTAT_DST_DEC_ERR BIT(6)
#define CH_INTSTAT_SRC_DEC_ERR BIT(5)
#define CH_INTSTAT_DST_TRANSCOMP BIT(4)
#define CH_INTSTAT_SRC_TRANSCOMP BIT(3)
#define CH_INTSTAT_DMA_TFR_DONE BIT(1)
#define CH_INTSTAT_BLOCK_TFR_DONE BIT(0)

/* Bitfields in DMAC_COMMON_INT          -> add when needed */
/* Bitfields in DMAC_RESET               -> add when needed */
/* Bitfields in DMAC_LOWPOWER_CFG        -> add when needed */
/* Bitfields in DMAC_COMMON_PARCTL       -> add when needed */
/* Bitfields in DMAC_COMMON_ECCCTLSTATUS -> add when needed */

///////////////////////////////////////////////////////////////////////////////////////////

/* Channel registers offset */
typedef struct {
    reg64_t sar;                // 0x000 - Channel Source Address Register
    reg64_t dar;                // 0x008 - Channel Destination Address Register
    reg64_t block_ts;           // 0x010 - Channel Block Transfer Size Register
    reg64_t ctl;                // 0x018 - Channel Control Register
    reg64_t cfg;                // 0x020 - Channel Configuration Register
    reg64_t llp;                // 0x028 - Channel Linked List Pointer Register
    reg64_t status;             // 0x030 - Channel Status Register
    reg64_t swhssrc;            // 0x038 - Channel Software Handshake Source Register
    reg64_t swhsdst;            // 0x040 - Channel Software Handshake Destination Register
    reg64_t blk_tfr_resumereq;  // 0x048 - Channel Block Transfer Resume Request Register
    reg64_t axi_id;             // 0x050 - Channel AXI ID Register
    reg64_t axi_qos;            // 0x058 - Channel AXI QoS Register
    reg64_t sstat;              // 0x060 - Channel Source Status Register
    reg64_t dstat;              // 0x068 - Channel Destination Status Register
    reg64_t sstatar;            // 0x070 - Channel Source Status Fetch Register
    reg64_t dstatar;            // 0x078 - Channel Destination Status Fetch Register
    reg64_t intstatus_enable;   // 0x080 - Channel Interrupt Status Enable Register
    reg64_t intstatus;          // 0x088 - Channel Interrupt Status Register
    reg64_t intsignal_enable;   // 0x090 - Channel Interrupt Signal Enable Register
    reg64_t intclear;           // 0x098 - Channel Interrupt Status Clear Register
} snps_dma_ch_regs;

/* Linked List Item Descriptor */
typedef struct __attribute__((packed)) {
    reg64_t sar;
    reg64_t dar;
    reg32_t block_ts;
    reg32_t _reserved_0x14;
    reg64_t llp;
    reg64_t ctl;
    reg32_t sstat;
    reg32_t dstat;
    reg64_t status;
    reg64_t _reserved_0x38;
} snps_dma_lli;

/* Bitfields in CHx_CTL */
#define CH_CTL_SHADOWREG_OR_LLI_VALID BIT(63)   // Shadow Register content/Linked List Item valid
#define CH_CTL_SHADOWREG_OR_LLI_LAST BIT(62)    // Last Shadow Register/Linked List Item
#define CH_CTL_IOC_BlkTfr BIT(58)               // Interrupt On completion of Block Transfer
#define CH_CTL_DST_STAT_EN BIT(57)              // Destination Status Enable
#define CH_CTL_SRC_STAT_EN BIT(56)              // Source Status Enable
#define CH_CTL_AWLEN(n) DMA_BITS(48, 55, n)         // Destination Burst Length
#define CH_CTL_AWLEN_EN BIT(47)                 // Destination Burst Length Enable
#define CH_CTL_ARLEN(n) DMA_BITS(39, 46, n)         // Source Burst Length
#define CH_CTL_ARLEN_EN BIT(38)                 // Source Burst Length Enable
#define CH_CTL_AW_PROT(n) DMA_BITS(35, 37, n)       // AXI 'aw_prot' signal
#define CH_CTL_AR_PROT(n) DMA_BITS(32, 34, n)       // AXI 'ar_prot' signal
#define CH_CTL_NonPosted_LastWrite_En BIT(30)   // Non Posted Last Write Enable
#define CH_CTL_AW_CACHE(n) DMA_BITS(26, 29, n)      // AXI 'aw_cache' signal
#define CH_CTL_AR_CACHE(n) DMA_BITS(22, 25, n)      // AXI 'ar_cache' signal
#define CH_CTL_DST_MSIZE(n) DMA_BITS(18, 21, n)     // Destination Burst Transaction Length
#define CH_CTL_SRC_MSIZE(n) DMA_BITS(14, 17, n)     // Source Burst Transaction Length
#define CH_CTL_DST_TR_WIDTH(n) DMA_BITS(11, 13, n*1)  // Destination Burst Transaction Length
#define CH_CTL_SRC_TR_WIDTH(n) DMA_BITS(8, 10, n*1)   // Destination Transfer Width
#define CH_CTL_DINC BIT(6)                      // Destination Address Increment
#define CH_CTL_SINC BIT(4)                      // Source Address Increment
#define CH_CTL_DMS BIT(2)                       // Destination Master Select
#define CH_CTL_SMS BIT(0)                       // Source Master Select

/* Bitfields in CHx_CFG */
#define CH_CFG_DST_OSR_LMT(n) DMA_BITS(59, 62, n)  // Destination Outstanding Request Limit
#define CH_CFG_SRC_OSR_LMT(n) DMA_BITS(55, 58, n)  // Source Outstanding Request Limit
#define CH_CFG_LOCK_CH_L(n) DMA_BITS(53, 54, n)    // Channel Lock Level
#define CH_CFG_LOCK_CH BIT(52)                 // Channel Lock bit
#define CH_CFG_CH_PRIOR(n) DMA_BITS(49, 51, n)     // Channel Priority
// Bits for Hardware Handshaking skipped
#define CH_CFG_TT_FC(n) DMA_BITS(32, 34, n)  // Transfer Type and Flow Control
#define CH_CFG_WR_UID(n) \
    DMA_BITS(25, 27, n)  // Defines the number of AXI Unique ID's supported for the AXI Write Channel
#define CH_CFG_RD_UID(n) \
    DMA_BITS(18, 20, n)  // Defines the number of AXI Unique ID's supported for the AXI Read Channel
#define CH_CFG_DST_MULTBLK_TYPE(n) DMA_BITS(2, 3, n)  // Destination Multi Block Transfer Type
#define CH_CFG_SRC_MULTBLK_TYPE(n) DMA_BITS(0, 1, n)  // Source Multi Block Transfer Type

/* Bitfields in CHx_STATUS */
#define CH_INTSTATUS_ECC_PROT_UIDMem_UnCorrERR BIT(35)
#define CH_INTSTATUS_ECC_PROT_UIDMem_CorrERR BIT(34)
#define CH_INTSTATUS_ECC_PROT_CHMem_UnCorrERR BIT(33)
#define CH_INTSTATUS_ECC_PROT_CHMem_CorrERR BIT(32)
#define CH_INTSTATUS_CH_ABORTED BIT(31)
#define CH_INTSTATUS_CH_DISABLED BIT(30)
#define CH_INTSTATUS_CH_SUSPENDED BIT(29)
#define CH_INTSTATUS_CH_SRC_SUSPENDED BIT(28)
#define CH_INTSTATUS_CH_LOCK_CLEARED BIT(27)
#define CH_INTSTATUS_SLVIF_WRPARITY_ERR BIT(25)
#define CH_INTSTATUS_SLVIF_WRONHOLD_ERR BIT(21)
#define CH_INTSTATUS_SLVIF_SHADOWREG_WRON_VALID_ERR BIT(20)
#define CH_INTSTATUS_SLVIF_WRONCHEN_ERR BIT(19)
#define CH_INTSTATUS_SLVIF_RD2RWO_ERR BIT(18)
#define CH_INTSTATUS_SLVIF_WR2RO_ERR BIT(17)
#define CH_INTSTATUS_SLVIF_DEC_ERR BIT(16)
#define CH_INTSTATUS_SLVIF_MULTIBLKTYPE_ERR BIT(14)
#define CH_INTSTATUS_SHADOWREG_OR_LLI_INVALID_ERR BIT(13)
#define CH_INTSTATUS_LLI_WR_SLV_ERR BIT(12)
#define CH_INTSTATUS_LLI_RD_SLV_ERR BIT(11)
#define CH_INTSTATUS_LLI_WR_DEC_ERR BIT(10)
#define CH_INTSTATUS_LLI_RD_DEC_ERR BIT(9)
#define CH_INTSTATUS_DST_SLV_ERR BIT(8)
#define CH_INTSTATUS_SRC_SLV_ERR BIT(7)
#define CH_INTSTATUS_DST_DEC_ERR BIT(6)
#define CH_INTSTATUS_SRC_DEC_ERR BIT(5)
#define CH_INTSTATUS_DST_TRANSCOMP BIT(4)
#define CH_INTSTATUS_SRC_TRANSCOMP BIT(3)
#define CH_INTSTATUS_DMA_TFR_DONE BIT(1)
#define CH_INTSTATUS_BLOCK_TFR_DONE BIT(0)

/* Bitfields in CHx_LLP */
#define CH_LLP_LMS BIT(0)

///////////////////////////////////////////////////////////////////////////////////////////

typedef struct {
    snps_dmac_regs* dmac_regs;
    snps_dma_ch_regs* regs;
    uint8_t id;
} snps_dma_channel;

typedef enum {
	SNPS_SINGLE_BLOCK	= 0,
	SNPS_SHADOW_REGISTER	= 2,
	SNPS_LINKED_LIST	    = 3
} snps_dma_transfer_mode;

typedef enum {
    SNPS_DMA_TR_WIDTH_8 = 0,
    SNPS_DMA_TR_WIDTH_16 = 1,
    SNPS_DMA_TR_WIDTH_32 = 2,
    SNPS_DMA_TR_WIDTH_64 = 3,
    SNPS_DMA_TR_WIDTH_128 = 4,
    SNPS_DMA_TR_WIDTH_256 = 5,
    SNPS_DMA_TR_WIDTH_512 = 6
} dma_tr_width;

#define SNPS_DMA_CTL_TR_WIDTH(SRC,DST) (CH_CTL_DST_TR_WIDTH(SNPS_DMA_TR_WIDTH_##DST) | CH_CTL_SRC_TR_WIDTH(SNPS_DMA_TR_WIDTH_##SRC))

/* Basic helpers */
void snps_dma_init_dmac(snps_dmac_regs* dmac_regs, int enable_interrupt);

/* Channel configuration helpers */
void snps_dma_init_channel(snps_dma_channel* chan, snps_dmac_regs* dmac_regs, uint64_t id);
void snps_dma_enable_channel(snps_dma_channel* chan);
void snps_dma_configure_channel(snps_dma_channel* chan, snps_dma_transfer_mode mode, uint64_t cfg_flags);
void snps_dma_configure_block_transfer_ext(snps_dma_channel* chan, uintptr_t sar, uintptr_t dar, uint64_t block_ts, uint64_t ctl_flags);
void snps_dma_configure_block_transfer(snps_dma_channel* chan, uintptr_t sar, uintptr_t dar, uint64_t block_ts, uint64_t ctl_flags);

/* Status helpers */
int snps_dma_channel_enabled(snps_dma_channel* chan);
int snps_dma_transfer_done(snps_dma_channel* chan);
int snps_dma_get_complete_transfer_size(snps_dma_channel* chan);
int snps_dma_shadow_regs_loaded(snps_dma_channel* chan);


/* Linked list multi block transfer */
void snps_dma_configure_llp(snps_dma_channel* chan, snps_dma_lli* llp, int ll_mif);
void snps_dma_setup_lli(snps_dma_lli* lli, uintptr_t sar, uintptr_t dar, uint64_t block_ts, uint64_t ctl_flags, snps_dma_lli* next_lli);
void snps_dma_print_lli(snps_dma_lli* lli);

#endif  // ifndef DRV_SNPS_DMA_H
