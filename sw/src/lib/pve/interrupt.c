#include <clint.h>
#include <encoding.h>
#include <platform.h>
#include <printf.h>
#include <trap.h>
#include <interrupt.h>

void init_interrupts(void) {

  uint64_t key = arch_irq_lock();

  // Enable interrupts in general.
  set_csr(CSR_MSTATUS, MSTATUS_MIE);
  /* Enable Machine Software Interrupt */
  set_csr(CSR_MIE, MIP_MSIP);

  arch_irq_unlock(key);
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

__attribute__((weak)) void verify_mtime() {
  // do nothing, optionally override for verification
}

static void mext_handler() {
  printf("\r\n");
  printf("=== UNHANDLED EXTERNAL INTERRUPT ===\r\n");
  printf("aborting...\r\n");

  exit(0b111 << 16);
  while (1)
    ;
}

static void msw_handler() {
  // used for waking up cores only, clear IRQ and do nothing else
  clint_clear_sw_irq();
}

static void mtime_handler() {
  clint_reset_timer();
  verify_mtime();
}

void interrupt_handler(SAVED_CONTEXT *ctx) {
  // overrides weak implementation in lib/cva6v/trap.c
  uint64_t cause = ctx->mcause & MCAUSE_CAUSE;

  switch (cause) {
    case IRQ_M_EXT:
      mext_handler();
      break;
    case IRQ_M_SOFT:
      msw_handler();
      break;
    case IRQ_M_TIMER:
      mtime_handler();
      break;
    default:
      default_interrupt_handler(ctx);
      break;
  }
}
