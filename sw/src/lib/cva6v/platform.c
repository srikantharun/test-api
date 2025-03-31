#include <stddef.h>
#include <stdint.h>

#include <multicore_common.h>
#include <platform.h>
#include <printf.h>
#include <string.h>
#include <stack.h>
#include <util.h>

#ifndef SYSTEM_CVA6V
#include <interrupt.h>
#endif

__attribute__((weak)) int main() {
  printf("Implement main(), foo!\n");
  return -1;
}

#ifdef SYSTEM_TOP
extern volatile core_t multicore_sync[NUM_CORES];
extern volatile uint64_t stack_addrs[NUM_CORES];
extern void* _stack_begin;
#endif

void __attribute__((weak,noreturn,noinline)) exit(int code)
{
  // Ensure the infinite loop is not the first instruction in the function,
  // cleaning up instruction traces in Veloce.
  asm volatile ("nop");

#ifdef SYSTEM_TOP
  tid_t id = r_uhartid();
  multicore_sync[id].ret = code;
  multicore_sync[id].status = STATUS_EXITED;
#else
  UNUSED(code);
#endif

  while (1) {
    asm volatile("wfi");
  }
}

void abort()
{
  exit(128 + SIGABRT);
}

// This is called from assembly startup code. Stack pointer is initialized, but
// thread-local storage (TLS) and thread pointer are still invalid.
void _init() {
  _init_tls();
  // TODO: initialize BSS (for PVE on only one core)

#ifndef SYSTEM_CVA6V
#ifndef NO_INTERRUPTS
  init_interrupts();
#endif
#endif

#ifdef SYSTEM_TOP
  tid_t id = r_mhartid();
  stack_addrs[r_mhartid()] = (uint64_t)(&_stack_begin) + (uint64_t)PVE_STACK_SIZE * (1 + (uint64_t)r_mhartid() - (uint64_t)processor_first_hart_id());

  // Wait for the status to be changed away from idle (by the manager).
  multicore_sync[id].status = STATUS_READY;
  asm volatile("wfi");
  multicore_sync[id].status = STATUS_RUNNING;
#endif


  // Run the provided function.
  int ret = main();

  exit(ret);
}
