// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#pragma once

#ifdef __cplusplus
extern "C" {
#endif

#include <encoding.h>
#include <platform.h>
#include <memorymap.h>
#include <plic.h>
#include <critical_section.h>

void init_interrupts(void);

/*
* Handling Functions
*/
typedef void (*isr_func)(void);

void mext_interrupt(unsigned int irq_source);

/*
 * CPU Machine timer control
 */
#define HAL_MTIMER_INITIAL()
#define HAL_MTIME_ENABLE() set_csr(CSR_MIE, MIP_MTIP)
#define HAL_MTIME_DISABLE() clear_csr(CSR_MIE, MIP_MTIP);

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
#define HAL_MSWI_ENABLE() set_csr(CSR_MIE, MIP_MSIP)
#define HAL_MSWI_DISABLE() clear_csr(CSR_MIE, MIP_MSIP)
#define HAL_MSWI_PENDING(vector) __nds__plic_sw_set_pending(vector)
#define HAL_MSWI_CLEAR() __nds__plic_sw_claim_interrupt()
#define HAL_MSWI_COMPLETE(vector) __nds__plic_sw_complete_interrupt(vector)

void msw_interrupt(unsigned int irq_source);

/*
 * Platform defined interrupt controller access
 *
 * This uses the vectored PLIC scheme.
 */
#define HAL_MEIP_ENABLE() set_csr(CSR_MIE, MIP_MEIP)
#define HAL_MEIP_DISABLE() clear_csr(CSR_MIE, MIP_MEIP)
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

#ifdef __riscv_flen
#define SAVE_FCSR() int __fcsr = read_fcsr();
#define RESTORE_FCSR() write_fcsr(__fcsr);
#else
#define SAVE_FCSR()
#define RESTORE_FCSR()
#endif

/* Nested IRQ entry macro : Save CSRs and enable global interrupt. */
#define NESTED_IRQ_ENTER() \
  SAVE_CSR(CSR_MEPC)       \
  SAVE_CSR(CSR_MSTATUS)    \
  SAVE_FCSR()              \
  set_csr(CSR_MSTATUS, MSTATUS_MIE);

/* Nested IRQ exit macro : Restore CSRs */
#define NESTED_IRQ_EXIT()              \
  clear_csr(CSR_MSTATUS, MSTATUS_MIE); \
  RESTORE_CSR(CSR_MSTATUS)             \
  RESTORE_CSR(CSR_MEPC)                \
  RESTORE_FCSR()

#ifdef __cplusplus
}
#endif
