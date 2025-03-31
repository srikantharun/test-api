/*
 * Copyright (c) 2012-2021 Andes Technology Corporation
 * All rights reserved.
 *
 */

#include <stdbool.h>
#include <encoding.h>
#include <interrupt.h>
#include <platform.h>
#include <interrupt.h>
#include <trap.h>
#include <util.h>

const char *EXCEPTION_MCAUSE_REASONS[NUM_EXCEPTION_SOURCE] = {
  [EXC_INSTRUCTION_ADDRESS_MISALIGNED]   = "instruction address misaligned",    // 0
  [EXC_INSTRUCTION_ACCESS_FAULT]         = "instruction access fault",          // 1
  [EXC_ILLEGAL_INSTRUCTION]              = "illegal instruction",               // 2
  [EXC_BREAKPOINT]                       = "breakpoint",                        // 3
  [EXC_LOAD_ADDRESS_MISALIGNED]          = "load address misaligned",           // 4
  [EXC_LOAD_ACCESS_FAULT]                = "load access fault",                 // 5
  [EXC_STORE_AMO_ADDRESS_MISALIGNED]     = "store/AMO address misaligned",      // 6
  [EXC_STORE_AMO_ACCESS_FAULT]           = "store/AMO access fault",            // 7
  [EXC_ENVIRONMENT_CALL_FROM_U_MODE]     = "environment call from U-mode",      // 8
  [EXC_ENVIRONMENT_CALL_FROM_S_MODE]     = "environment call from S-mode",      // 9
  [EXC_RESERVED_1]                       = "reserved",                          // 10
  [EXC_ENVIRONMENT_CALL_FROM_M_MODE]     = "environment call from M-mode",      // 11
  [EXC_INSTRUCTION_PAGE_FAULT]           = "instruction page fault",            // 12
  [EXC_LOAD_PAGE_FAULT]                  = "load page fault",                   // 13
  [EXC_RESERVED_2]                       = "reserved",                          // 14
  [EXC_STORE_AMO_PAGE_FAULT]             = "store/AMO page fault"               // 15
};


static __thread struct {
  bool enabled;
  uint32_t cause;
  uint64_t next_pc;
} allowed_exception;

void exception_allow_once(uint32_t cause, void *next_pc) {
  allowed_exception.cause = cause;
  allowed_exception.next_pc = (uint64_t)next_pc;
  allowed_exception.enabled = true;
}

__attribute__((weak)) void mtime_handler(void) { HAL_MTIME_DISABLE(); }
__attribute__((weak)) void verify_mtimer() {/*Optionally override for verification*/}

__attribute__((weak)) long except_handler(SAVED_CONTEXT* ctx) {
  const char *reason = NULL;
  uint64_t cause = (uint64_t)ctx->mcause & MCAUSE_CAUSE;
  if (cause < ARRAY_LENGTH(EXCEPTION_MCAUSE_REASONS))
    reason = EXCEPTION_MCAUSE_REASONS[cause];

  printf("\r\n");
  printf("=== UNHANDLED EXCEPTION ===\r\n");
  printf("mcause: 0x%08lx", ctx->mcause);
  if (reason)
    printf(" (%s)", reason);
  printf("\r\n");
  printf("mepc:   0x%016lx\r\n", ctx->mepc);
  printf("mtval:  0x%016lx\r\n", ctx->mtval);
  printf("\r\n");
  printf("aborting...\r\n");

  exit((0b1 << 16) | ctx->mcause);
  while (1) {
  }
}

long default_interrupt_handler(SAVED_CONTEXT* ctx) {
  printf("\r\n");
  printf("=== UNHANDLED INTERRUPT ===\r\n");
  printf("mcause: 0x%08lx\r\n", ctx->mcause);
  printf("\r\n");
  printf("aborting...\r\n");

  exit((0b11 << 16) | ctx->mcause);
  while (1)
    ;
}

trap_func exception_handler[NUM_EXCEPTION_SOURCE] = {
  [EXC_INSTRUCTION_ADDRESS_MISALIGNED]   = except_handler,
  [EXC_INSTRUCTION_ACCESS_FAULT]         = except_handler,
  [EXC_ILLEGAL_INSTRUCTION]              = except_handler,
  [EXC_BREAKPOINT]                       = except_handler,
  [EXC_LOAD_ADDRESS_MISALIGNED]          = except_handler,
  [EXC_LOAD_ACCESS_FAULT]                = except_handler,
  [EXC_STORE_AMO_ADDRESS_MISALIGNED]     = except_handler,
  [EXC_STORE_AMO_ACCESS_FAULT]           = except_handler,
  [EXC_ENVIRONMENT_CALL_FROM_U_MODE]     = except_handler,
  [EXC_ENVIRONMENT_CALL_FROM_S_MODE]     = except_handler,
  [EXC_RESERVED_1]                       = except_handler,
  [EXC_ENVIRONMENT_CALL_FROM_M_MODE]     = except_handler,
  [EXC_INSTRUCTION_PAGE_FAULT]           = except_handler,
  [EXC_LOAD_PAGE_FAULT]                  = except_handler,
  [EXC_RESERVED_2]                       = except_handler,
  [EXC_STORE_AMO_PAGE_FAULT]             = except_handler,
};

void trap_handler(SAVED_CONTEXT* context) {
  /* Do your trap handling */
  if (context->mcause & MCAUSE_INT) {
    switch (context->mcause & MCAUSE_CAUSE) {
      case IRQ_M_TIMER:
        /* Machine timer interrupt */
        mtime_handler();
        verify_mtimer();
        break;
      case IRQ_M_EXT:
        /* Machine-level interrupt from PLIC */
        mext_interrupt(__nds__plic_claim_interrupt());
        break;
      case IRQ_LCOF:
        local_irq_lcof_handler();
        break;
      case IRQ_IMECC:
        local_irq_imecc_handler();
        break;
      case IRQ_BWE:
        local_irq_bwe_handler();
        break;
      case IRQ_M_SOFT:
        /* Machine SWI interrupt */
        msw_interrupt(__nds__plic_sw_claim_interrupt());
        break;
      default:
        /* Unhandled Trap */
        context->mepc = default_interrupt_handler(context);
        break;
    }
  } else {
    uint64_t cause = context->mcause & MCAUSE_CAUSE;

    // For verification, one can "allow" a certain exception to occur without
    // aborting. The user can detect this happened as (a) control flow will jump
    // to next_pc rather than continuing linearly.
    if (allowed_exception.enabled && (cause == allowed_exception.cause)) {
      context->mepc = (uint64_t)allowed_exception.next_pc;
      // Clear the pointer such that this doesn't run multiple times by accident.
      allowed_exception.enabled = false;
      return;
    }

    if (cause < NUM_EXCEPTION_SOURCE){
      exception_handler[cause](context);
    } else {
      /* Unhandled Exception */
      except_handler(context);
    }
  }
}
