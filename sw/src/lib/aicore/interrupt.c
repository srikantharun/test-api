#include <encoding.h>
#include <trap.h>
#include <interrupt.h>
#include <testutils.h>

void init_interrupts(void) {
  // Do not set the timer bit (MTIP) in MIE here. This will be set by the timer
  // driver (if required).

  uint64_t key = arch_irq_lock();

  // Enable interrupts in general.
  set_csr(CSR_MSTATUS, MSTATUS_MIE);

  // Enable external (PLIC) interrupts
  HAL_MEIP_ENABLE();

  // Enable SW interrupts
  HAL_MSWI_ENABLE();
  HAL_MSWI_INITIAL(r_mhartid());

  arch_irq_unlock(key);
}

void default_interrupt_handler(SAVED_CONTEXT* ctx) {
  printf("\r\n");
  printf("=== UNHANDLED INTERRUPT ===\r\n");
  printf("mcause: 0x%08lx\r\n", ctx->mcause);
  printf("\r\n");
  printf("aborting...\r\n");

  exit((0b11 << 16) | ctx->mcause);
  while (1)
    ;
}

void default_irq_handler(void){
  while (1)
    ;
}

/* Timer IRQs */
__attribute__((weak)) void mtime_handler(void) { HAL_MTIME_DISABLE(); }
__attribute__((weak)) void verify_mtimer() {/*Optionally override for verification*/}

/** External IRQs **/
const isr_func irq_handler[] = {
    [0] = default_irq_handler
};

__attribute__((weak)) void verify_interrupt(unsigned int irq_source) { /*Optionally override for verification*/
  UNUSED(irq_source);
}

__attribute__((weak)) void mext_interrupt(unsigned int irq_source) {

  ASSERT(irq_source != 0, "External interrupts are not yet fully supported!");

  /* Optionally verify interrupts for verification */
  verify_interrupt(irq_source);

  /* Do interrupt handler */
  irq_handler[irq_source]();

  __nds__plic_complete_interrupt(irq_source);
}


/** SW IRQs **/
__attribute__((weak)) void mswi_handler_apu(void) {
  ;
}

__attribute__((weak)) void mswi_handler_aicore(void) {
  ;
}

const isr_func sw_irq_handler[SW_IRQ_TOTAL] = {
    mswi_handler_apu,
    mswi_handler_apu,
    mswi_handler_apu,
    mswi_handler_apu,
    mswi_handler_apu,
    mswi_handler_apu,
    mswi_handler_aicore,
    mswi_handler_aicore,
    mswi_handler_aicore,
    mswi_handler_aicore,
    mswi_handler_aicore,
    mswi_handler_aicore,
    mswi_handler_aicore,
    mswi_handler_aicore,
};

__attribute__((weak)) void msw_interrupt(unsigned int irq_source) {
  /* Enable interrupts in general to allow nested */
  set_csr(CSR_MSTATUS, MSTATUS_MIE);

  /* Do interrupt handler */
  sw_irq_handler[irq_source]();

  __nds__plic_sw_complete_interrupt(irq_source);
}


/* Handler */
void interrupt_handler(SAVED_CONTEXT *ctx) {
  // overrides weak implementation in lib/cva6v/trap.c
  uint64_t cause = ctx->mcause & MCAUSE_CAUSE;
  // UNUSED(cause);

  switch (cause) {
    case IRQ_M_EXT:
      /* Machine-level interrupt from PLIC */
      mext_interrupt(__nds__plic_claim_interrupt());
      break;
    case IRQ_M_SOFT:
      /* Machine SWI interrupt */
      msw_interrupt(__nds__plic_sw_claim_interrupt());
      break;
    case IRQ_M_TIMER:
      /* Machine timer interrupt */
      mtime_handler();
      verify_mtimer();
      break;
    default:
      default_interrupt_handler(ctx);
      break;
  }
}
