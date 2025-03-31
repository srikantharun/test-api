// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***


#include "drv_snps_dma.h"
#include <stddef.h>
#include <platform.h>
// TODO: #include <interrupt.h>
#include <printf.h>


/* Basic helpers */

void snps_dma_init_dmac(snps_dmac_regs* dmac_regs, int enable_interrupt)
{
    (void) enable_interrupt;
    dmac_regs->cfg = DMAC_CFG_DMAC_EN;
    // TODO: PLIC support on AI Core (https://git.axelera.ai/prod/europa/-/issues/1883)
    // if (enable_interrupt) {
    //     dmac_regs->cfg = DMAC_CFG_DMAC_EN | DMAC_CFG_INT_EN;
    //     HAL_INTERRUPT_ENABLE(IRQ_DMA_CMNREG_SOURCE);
    //     HAL_INTERRUPT_ENABLE(IRQ_DMA_CH0_SOURCE);
    //     HAL_INTERRUPT_ENABLE(IRQ_DMA_CH1_SOURCE);
    //     HAL_INTERRUPT_ENABLE(IRQ_DMA_CH2_SOURCE);
    //     HAL_INTERRUPT_ENABLE(IRQ_DMA_CH3_SOURCE);
    //     HAL_INTERRUPT_SET_LEVEL(IRQ_DMA_CMNREG_SOURCE, IRQ_PRIORITY_DEFAULT);
    //     HAL_INTERRUPT_SET_LEVEL(IRQ_DMA_CH0_SOURCE, IRQ_PRIORITY_DEFAULT);
    //     HAL_INTERRUPT_SET_LEVEL(IRQ_DMA_CH1_SOURCE, IRQ_PRIORITY_DEFAULT);
    //     HAL_INTERRUPT_SET_LEVEL(IRQ_DMA_CH2_SOURCE, IRQ_PRIORITY_DEFAULT);
    //     HAL_INTERRUPT_SET_LEVEL(IRQ_DMA_CH3_SOURCE, IRQ_PRIORITY_DEFAULT);
    // } else {
    //     dmac_regs->cfg = DMAC_CFG_DMAC_EN;
    // }
}

/* Basic channel helpers */

void snps_dma_init_channel(snps_dma_channel* chan, snps_dmac_regs* dmac_regs, uint64_t id)
{
    chan->id = id;
    chan->dmac_regs = dmac_regs;
    chan->regs = (snps_dma_ch_regs*)((uintptr_t)dmac_regs + COMMON_REG_LEN + id * CH_REG_LEN);
    chan->regs->intclear = 0xFFFFFFFFFFFFFFFF;
}

void snps_dma_enable_channel(snps_dma_channel* chan)
{
    chan->dmac_regs->chen = DMAC_CHEN_CH_EN(chan->id) | DMAC_CHEN_CH_EN_WE(chan->id);
}

void snps_dma_configure_channel(snps_dma_channel* chan, snps_dma_transfer_mode mode, uint64_t cfg_flags)
{
    // TO-DO: Came from Omega, check if needed and why not
    // CH_CFG_DST_MULTBLK_TYPE(mode) | CH_CFG_SRC_MULTBLK_TYPE(mode)
    chan->regs->cfg = cfg_flags | mode | (mode << 2);
}

void snps_dma_configure_block_transfer_ext(snps_dma_channel* chan, uintptr_t sar, uintptr_t dar, uint64_t block_ts, uint64_t ctl_flags)
{
    chan->regs->sar = (uint64_t)sar;
    chan->regs->dar = (uint64_t)dar;
    chan->regs->block_ts = block_ts;
    chan->regs->ctl = ctl_flags | CH_CTL_SHADOWREG_OR_LLI_VALID | CH_CTL_AW_CACHE(2) | CH_CTL_AR_CACHE(2);
}

void snps_dma_configure_block_transfer(snps_dma_channel* chan, uintptr_t sar, uintptr_t dar, uint64_t block_ts, uint64_t ctl_flags)
{
    snps_dma_configure_block_transfer_ext(chan, sar, dar, block_ts, ctl_flags);
}

/* Status helpers */

int snps_dma_channel_enabled(snps_dma_channel* chan)
{
    return (chan->dmac_regs->chen & DMAC_CHEN_CH_EN(chan->id)) > 0;
}

int snps_dma_transfer_done(snps_dma_channel* chan)
{
    return (chan->regs->intstatus & CH_INTSTATUS_DMA_TFR_DONE) > 0;
}

int snps_dma_get_complete_transfer_size(snps_dma_channel* chan)
{
    return chan->regs->status & DMA_BIT_MASK(0, 21);
}

int snps_dma_shadow_regs_loaded(snps_dma_channel* chan)
{
    return !(chan->regs->ctl & CH_CTL_SHADOWREG_OR_LLI_VALID);
}

/* Linked list multi block transfer */

void snps_dma_configure_llp(snps_dma_channel* chan, snps_dma_lli* lli, int ll_mif)
{
    uint64_t llp_reg = (uint64_t)lli;
    if (ll_mif) llp_reg |= CH_LLP_LMS;
    chan->regs->llp = llp_reg;
}

void snps_dma_setup_lli(snps_dma_lli* lli, uintptr_t sar, uintptr_t dar, uint64_t block_ts, uint64_t ctl_flags, snps_dma_lli* next_lli)
{
    lli->sar = (uint64_t)sar;
    lli->dar = (uint64_t)dar;
    lli->block_ts = block_ts;
    lli->ctl = CH_CTL_SHADOWREG_OR_LLI_VALID | CH_CTL_AW_CACHE(2) | CH_CTL_AR_CACHE(2) | ctl_flags | SNPS_DMA_CTL_TR_WIDTH(512,512);
    if (next_lli == NULL) {
        lli->ctl |= CH_CTL_SHADOWREG_OR_LLI_LAST;
    } else {
        lli->llp = (uint64_t)next_lli;
    }
}

void snps_dma_print_lli(snps_dma_lli* lli) {
    printf("sar      : %016lx\n", lli->sar);
    printf("dar      : %016lx\n", lli->dar);
    printf("block_ts : %08x\n",  lli->block_ts);
    printf("llp      : %016lx\n", lli->llp);
    printf("ctl      : %016lx\n", lli->ctl);
    printf("status   : %016lx\n", lli->status);
}
