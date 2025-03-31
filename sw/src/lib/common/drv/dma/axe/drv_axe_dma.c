// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***


#include "drv_axe_dma.h"

#include <stddef.h>
#include <platform.h>
#include <printf.h>


/* Basic channel helpers */

void axe_dma_init_channel(
  axe_dma_channel* chan, axe_dma_regs* dma_regs, uint64_t id)
{

  chan->id = id;

  // The following code is only active when the request is made to any AICORE HP DMA.
  // The AICORE has a remapped internal memory map to align the all the regions of different IPs. This has as a result the DMA channels to
  // have an offset of AICORE_X_DATAPATH_CSR_DMA_HP_DMA_1_BASE-AICORE_X_DATAPATH_CSR_DMA_HP_DMA_0_BASE instead of the offset defined in the IP memory map.
  // The base address of AICORE_X_DATAPATH_CSR_DMA_HP_DMA_0_BASE is provided as a base address of the DMA IP for this driver in the
  // regdef_axe_dma.h file. The offset based on the configured channel is calculated in this function.

  // Define a mask for the lower 28 bits
  const uintptr_t LOWER_28_MASK = 0x0FFFFFFF;

  if (((uintptr_t)dma_regs & LOWER_28_MASK) == ((uintptr_t)AICORE_0_DATAPATH_CSR_DMA_HP_DMA_0_BASE & LOWER_28_MASK)) {

      if (id==1) {
        // Compute the new address by replacing only the lower 28 bits
        uintptr_t base_addr = (uintptr_t)dma_regs; // Cast base to uintptr_t
        uintptr_t new_addr = (base_addr & ~LOWER_28_MASK) |  // Preserve upper bits
                             ((uintptr_t)AICORE_0_DATAPATH_CSR_DMA_HP_DMA_1_BASE & LOWER_28_MASK); // Replace lower bits

        // Cast the new address back to a pointer
        dma_regs = (axe_dma_regs*)(new_addr);
      }

      chan->axe_dma_regs = dma_regs;
      chan->regs = (axe_dma_ch_regs*)((uintptr_t)dma_regs + CH_TRAN_CSR_OFFSET);


  } else {

   chan->axe_dma_regs = dma_regs;
   chan->regs = (axe_dma_ch_regs*)((uintptr_t)dma_regs + id * CH_REG_LEN + CMD_BLK_REG_LEN + CH_TRAN_CSR_OFFSET);

  }

}

void axe_dma_enable_channel(const axe_dma_ctrl_config* config)
{
  config->chan->regs->ch_ctrl = DMA_CH_CTRL_ENABLE | DMA_CH_CTRL_SRC_MS(config->src_ms) | DMA_CH_CTRL_DST_MS(config->dst_ms) |
                        DMA_CH_CTRL_SRC_OSR_LMT(config->src_osr_lmt) | DMA_CH_CTRL_DST_OSR_LMT(config->dst_osr_lmt) |
                        ((config->irq_en) ? DMA_CH_CTRL_INTR_ENABLE : 0) | ((config->irq_clr) ? DMA_CH_CTRL_INTR_CLEAR : 0);
}

void axe_dma_configure_1d_transfer(const axe_dma_1d_config* config)
{
  config->chan->regs->ch_src_addr = (uint64_t)config->src_addr;
  config->chan->regs->ch_dst_addr = (uint64_t)config->dst_addr;
  config->chan->regs->ch_xbytesize = DMA_CH_CFG_SRC_XBYTESIZE(config->src_xbytesize) | DMA_CH_CFG_DST_XBYTESIZE(config->dst_xbytesize);
  config->chan->regs->ch_xaddrinc =  DMA_CH_CFG_SRC_CH_XADDRINC(config->src_xaddrinc) | DMA_CH_CFG_DST_CH_XADDRINC(config->dst_xaddrinc);
  config->chan->regs->ch_cfg = DMA_CH_CFG_TRAN_SIZE(config->tran_size) | DMA_CH_CFG_XTYPE(config->xtype)| \
                       ((config->fillval_mode) ? DMA_CH_CFG_FILLVAL_MODE : 0) |  DMA_CH_CFG_FILLVAL(config->fillval) | \
                       DMA_CH_CFG_SRC_BURSTLEN(config->src_burstlen) | DMA_CH_CFG_DST_BURSTLEN(config->dst_burstlen) ;
}

void axe_dma_configure_2d_transfer(const axe_dma_2d_config* config)
{
  config->chan->regs->ch_src_addr = (uint64_t)config->src_addr;
  config->chan->regs->ch_dst_addr = (uint64_t)config->dst_addr;
  config->chan->regs->ch_xbytesize = DMA_CH_CFG_SRC_XBYTESIZE(config->src_xbytesize) | DMA_CH_CFG_DST_XBYTESIZE(config->dst_xbytesize);
  config->chan->regs->ch_xaddrinc =  DMA_CH_CFG_SRC_CH_XADDRINC(config->src_xaddrinc) | DMA_CH_CFG_DST_CH_XADDRINC(config->dst_xaddrinc);
  config->chan->regs->ch_yrowsize =  DMA_CH_CFG_SRC_CH_YROWSIZE(config->src_yrowsize) | DMA_CH_CFG_DST_CH_YROWSIZE(config->dst_yrowsize);
  config->chan->regs->ch_yaddrstride =  DMA_CH_CFG_SRC_CH_YADDRSTRIDE(config->src_yaddrstride) | DMA_CH_CFG_DST_CH_YADDRSTRIDE(config->dst_yaddrstride);
  config->chan->regs->ch_cfg = DMA_CH_CFG_TRAN_SIZE(config->tran_size) | DMA_CH_CFG_XTYPE(config->xtype)| DMA_CH_CFG_YTYPE(config->ytype)| \
                       ((config->fillval_mode) ? DMA_CH_CFG_FILLVAL_MODE : 0) |  DMA_CH_CFG_FILLVAL(config->fillval) | \
                       DMA_CH_CFG_SRC_BURSTLEN(config->src_burstlen) | DMA_CH_CFG_DST_BURSTLEN(config->dst_burstlen) ;
}

/* Linked list */
void axe_dma_setup_ll(const axe_dma_ll_config* config)
{
  config->chan->regs->ch_link_descr = DMA_CHANNEL_CH_LINK_DESCR_LINK_ADDR(config->next_ll) |
                             ((config->ll_last) ? DMA_CHANNEL_CH_LINK_DESCR_LAST: 0);
}

void axe_dma_enable_ll(const axe_dma_ll_ctrl_config* config)
{
  config->chan->regs->ch_ctrl = DMA_CH_CTRL_ENABLE |  DMA_CH_CTRL_LL_EN |
                                DMA_CH_CTRL_LL_MS(config->ll_ms) | ((config->ll_mode) ? DMA_CH_CTRL_LL_MODE: 0) |
                                ((config->irq_en) ? DMA_CH_CTRL_INTR_ENABLE : 0) | ((config->irq_clr) ? DMA_CH_CTRL_INTR_CLEAR : 0);
}


/* Status helpers */
int axe_dma_transfer_done(
  axe_dma_channel* chan)
{
  return (chan->regs->ch_status) == 0;
}

int axe_dma_channel_enabled(
  axe_dma_channel* chan)
{
  return (chan->regs->ch_status) > 0;
}
