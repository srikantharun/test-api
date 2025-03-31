#include <limits.h>
#include <stdint.h>
#include <string.h>

#include "asm.h"
#include "encoding.h"
#include "interrupt.h"
#include "nds_csr.h"
#include <multicore.h>
#include <critical_section.h>
#include "platform.h"
#include "printf.h"
#include "thread.h"
#include "stack.h"
#include "util.h"

// This should not be part of .bss, as .bss is not zeroed when loading via JTAG
// with GDB. To avoid a race between HART 0 initializing the value and the other
// HARTs reading it, put it in .data (which is loaded by GDB).
__attribute__((section(".data")))
volatile static int init_complete = 0;

volatile uint64_t stack_addrs[NUM_CORES];
extern void* _stack_begin;

void __attribute__((noreturn)) __attribute__((weak))  exit(int code)
{
  UNUSED(code);

  // Ensure the infinite loop is not the first instruction in the function,
  // cleaning up instruction traces in Veloce.
  asm volatile ("nop");

  while (1) {
    asm volatile("wfi");
  }
}

void abort()
{
  exit(128 + SIGABRT);
}

int __attribute__((weak)) main()
{
  // single-threaded programs override this function.
  printf("Implement main(), foo!\n");
  return -1;
}

static void init_interrupts(void) {
  // Do not set the timer bit (MTIP) in MIE here. This will be set by the timer
  // driver (if required).

  uint64_t key = arch_irq_lock();

  // Enable interrupts in general.
  set_csr(NDS_MSTATUS, MSTATUS_MIE);

  // Enable local interrupts (LCOF, IMECC, BWE) which should not go unhandled.
  set_csr(NDS_MIE, MIP_LCOFIP | MIP_IMECCI | MIP_BWEI);

  // Enable external (PLIC) interrupts
  HAL_MEIP_ENABLE();

  // Enable SW interrupts
  HAL_MSWI_ENABLE();
  HAL_MSWI_INITIAL(r_mhartid());

  arch_irq_unlock(key);
}

void populate_stack_var(){
  stack_addrs[r_mhartid()] = (uint64_t)(&_stack_begin) + (uint64_t)APU_STACK_SIZE * (1 + (uint64_t)r_mhartid() - (uint64_t)processor_first_hart_id());
}

// This is called from assembly startup code. Stack pointer is initialized, but
// thread-local storage (TLS) and thread pointer are still invalid.
void _init()
{
  _init_tls();

#ifndef NO_INTERRUPTS
  init_interrupts();
#else
  UNUSED(init_interrupts);
#endif

  if (r_mhartid() == 0) {
    // First core: Initialization.
#ifndef NO_INIT_BSS_AND_TLS
    _init_bss();
#endif
    _init_printf();
    _thread_init();
    _multicores_init();

    // Signal to other cores.
    init_complete = 1;
    populate_stack_var();
  } else {
    // Other cores: Wait for initialization to complete.
    while (init_complete == 0);
    populate_stack_var();

    _thread_worker_main();
    // Previous function should not return.
    while (1);
  }

  // only single-threaded programs should ever get here.
  int ret = main();
  exit(ret);
}
