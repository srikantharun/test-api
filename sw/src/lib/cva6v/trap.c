/*
 * Copyright (c) 2012-2021 Andes Technology Corporation
 * All rights reserved.
 *
 */

#include <asm.h>
#include <stdbool.h>
#include <stdint.h>
#include <encoding.h>
#include <memorymap.h>
#include <printf.h>
#include <platform.h>
#include <trap.h>
#include <printf.h>

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

__attribute__((weak)) void interrupt_handler(SAVED_CONTEXT *ctx) {
  UNUSED(ctx);
  uint64_t cause = ctx->mcause & MCAUSE_CAUSE;
  exit((0b1111 << 16) | cause);
  while (1)
    ;
}

#ifndef SYSTEM_CVA6V // required to make CVA6V block level testing work
void trap_handler(SAVED_CONTEXT* context) {
  /* Trap handling */
  if (context->mcause & MCAUSE_INT) {
    /* interrupt: different for AICOREs and PVEs */
    interrupt_handler(context);
  } else {
    uint64_t cause = context->mcause & MCAUSE_CAUSE;

     switch (cause) {
      /* ecall handler should be added */
      default:
        /* Unhandled Exception */
        context->mepc = except_handler(context);
        break;
    }
  }
}
#endif
