/*
 * Copyright (c) 2012-2021 Andes Technology Corporation
 * All rights reserved.
 *
 */

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#define USE_PLIC

#include <encoding.h>
#include <platform.h>
#include <memorymap.h>
#include <nds_csr.h>
#include "plic.h"

/*
* Handling Functions
*/
typedef void (*isr_func)(void);

void mext_interrupt(unsigned int irq_source);
void interrupt_core(tid_t hart_id);


void local_irq_lcof_handler(void);
void local_irq_imecc_handler(void);
void local_irq_bwe_handler(void);


/*
 * CPU Machine timer control
 */
#define HAL_MTIMER_INITIAL()
#define HAL_MTIME_ENABLE() set_csr(NDS_MIE, MIP_MTIP)
#define HAL_MTIME_DISABLE() clear_csr(NDS_MIE, MIP_MTIP);

/*
 * CPU Machine SWI control
 *
 * Machine SWI (MSIP) is connected to PLIC_SW source 1.
 */
#define HAL_MSWI_INITIAL(vector)             \
  {                                          \
    __nds__plic_sw_set_priority(vector, 1);  \
    __nds__plic_sw_enable_interrupt(vector); \
  }
#define HAL_MSWI_ENABLE() set_csr(NDS_MIE, MIP_MSIP)
#define HAL_MSWI_DISABLE() clear_csr(NDS_MIE, MIP_MSIP)
#define HAL_MSWI_PENDING(vector) __nds__plic_sw_set_pending(vector)
#define HAL_MSWI_CLEAR() __nds__plic_sw_claim_interrupt()
#define HAL_MSWI_COMPLETE(vector) __nds__plic_sw_complete_interrupt(vector)

void msw_interrupt(unsigned int irq_source);

/*
 * Platform defined interrupt controller access
 *
 * This uses the vectored PLIC scheme.
 */
#define HAL_MEIP_ENABLE() set_csr(NDS_MIE, MIP_MEIP)
#define HAL_MEIP_DISABLE() clear_csr(NDS_MIE, MIP_MEIP)
#define HAL_INTERRUPT_ENABLE(vector) __nds__plic_enable_interrupt(vector)
#define HAL_INTERRUPT_DISABLE(vector) __nds__plic_disable_interrupt(vector)
#define HAL_INTERRUPT_THRESHOLD(threshold) __nds__plic_set_threshold(threshold)
#define HAL_INTERRUPT_SET_LEVEL(vector, level) __nds__plic_set_priority(vector, level)

/*
 * Vectored based inline interrupt attach and detach control
 */
extern int __vectors[];
extern void default_irq_entry(void);

#define HAL_INLINE_INTERRUPT_ATTACH(vector, isr) \
  { __vectors[vector] = (int)isr; }
#define HAL_INLINE_INTERRUPT_DETACH(vector, isr)                                   \
  {                                                                                \
    if (__vectors[vector] == (int)isr) __vectors[vector] = (int)default_irq_entry; \
  }

/*
 * Inline nested interrupt entry/exit macros
 */
/* Save/Restore macro */
#define SAVE_CSR(r) long __##r = read_csr(r);
#define RESTORE_CSR(r) write_csr(r, __##r);

#if SUPPORT_PFT_ARCH
#define SAVE_MXSTATUS() SAVE_CSR(NDS_MXSTATUS)
#define RESTORE_MXSTATUS() RESTORE_CSR(NDS_MXSTATUS)
#else
#define SAVE_MXSTATUS()
#define RESTORE_MXSTATUS()
#endif

#ifdef __riscv_flen
#define SAVE_FCSR() int __fcsr = read_fcsr();
#define RESTORE_FCSR() write_fcsr(__fcsr);
#else
#define SAVE_FCSR()
#define RESTORE_FCSR()
#endif

#ifdef __riscv_dsp
#define SAVE_UCODE() SAVE_CSR(NDS_UCODE)
#define RESTORE_UCODE() RESTORE_CSR(NDS_UCODE)
#else
#define SAVE_UCODE()
#define RESTORE_UCODE()
#endif

/* Nested IRQ entry macro : Save CSRs and enable global interrupt. */
#define NESTED_IRQ_ENTER() \
  SAVE_CSR(NDS_MEPC)       \
  SAVE_CSR(NDS_MSTATUS)    \
  SAVE_MXSTATUS()          \
  SAVE_FCSR()              \
  SAVE_UCODE()             \
  set_csr(NDS_MSTATUS, MSTATUS_MIE);

/* Nested IRQ exit macro : Restore CSRs */
#define NESTED_IRQ_EXIT()              \
  clear_csr(NDS_MSTATUS, MSTATUS_MIE); \
  RESTORE_CSR(NDS_MSTATUS)             \
  RESTORE_CSR(NDS_MEPC)                \
  RESTORE_MXSTATUS()                   \
  RESTORE_FCSR()                       \
  RESTORE_UCODE()

/* additional local interrupts (AX65 datasheet, 16.2.1) */
#define IRQ_IMECC 16 /* imprecise ECC error local interrupt */
#define IRQ_BWE   17 /* bus read/write transaction error local interrupt */
#define MIP_IMECCI (1ULL << IRQ_IMECC)
#define MIP_BWEI   (1ULL << IRQ_BWE)

#ifdef __cplusplus
}
#endif
