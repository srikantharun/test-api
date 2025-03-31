#include <stddef.h>
#include "asm.h"
#include "platform.h"
#include "hw_defines.h"
#include "thread.h"
#include "interrupt.h"


/* NOTE: threads[0] is unused as the manager does not need this block.
 * Use the nominal number of APU cores, reserve maximum space, but only work
 * with the number of cores instantiated in hardware. */
volatile static thread_t threads[NUM_APU_CORES];

void _thread_init()
{
  memset((void*)&threads, 0, sizeof(threads));

  // Initalize all worker cores to idle status.
  for (size_t id = 1; id < HW_DEFINES_APU_CORE_NUMBER; id++) {
    threads[id].status = STATUS_IDLE;
  }
}

void _thread_worker_main()
{
  tid_t id = r_mhartid();
  while (1)
  {
    // Wait for the status to be changed away from idle (by the manager).
    while (threads[id].status != STATUS_READY) {
#ifndef NO_INTERRUPTS
      asm volatile("wfi");
#endif
    };

    threads[id].status = STATUS_RUNNING;
    // Run the provided function.
    threads[id].ret = threads[id].fp(threads[id].arg);
    threads[id].status = STATUS_EXITED;

  }
}

void thread_launch(tid_t id, int (*fp)(void *), void *arg)
{
  // Ensure the provided id is valid (exists and not the manager).
  if (id <= 0 || id >= HW_DEFINES_APU_CORE_NUMBER) abort();
  // Ensure the selected worker is not currently running a job.
  if (threads[id].status != STATUS_IDLE &&
      threads[id].status != STATUS_EXITED)
  {
      abort();
  }
  // Set the function pointer and argument first.
  threads[id].fp = fp;
  threads[id].arg = arg;
  // Set the status to READY, which releases the worker.
  threads[id].status = STATUS_READY;

#ifndef NO_INTERRUPTS
  // Interrupt core
  interrupt_core(id);
#endif
}

int thread_join(tid_t id)
{
  // Ensure the thread has been launched at least once.
  switch (threads[id].status)
  {
    case STATUS_READY:
    case STATUS_RUNNING:
    case STATUS_EXITED:
      break;
    default:
      abort();
  }

  // Wait for finish.
  while (threads[id].status != STATUS_EXITED);

  // Move thread to idle (so it is not joined multiple times).
  threads[id].status = STATUS_IDLE;

  return threads[id].ret;
}

int thread_join_all() {
  int ret = 0;
  for (size_t id = 1; id < HW_DEFINES_APU_CORE_NUMBER; id++) {
    if (threads[id].status == STATUS_IDLE) {
      // No need to join().
      continue;
    }
    ret |= thread_join(id);
  }
  return ret;
}

extern printf_t multicore_printf;
static volatile int multicore_printf_loop = 1;
static int thread_printf(void *arg) {
  UNUSED(arg);

  while(1)
  {

    while(multicore_printf.status != PRINTF_EXITED) {
      if(!multicore_printf_loop) {
        return 0;
      }
    };
    printf("<- %s", multicore_printf.buf);

    multicore_printf.status = PRINTF_IDLE;

  }

  return 0;
}

void enable_simple_multicore_printf(tid_t id)
{
  multicore_printf.status = PRINTF_IDLE;
  thread_launch(id, thread_printf, NULL);
}

void disable_simple_multicore_printf(tid_t id)
{
  multicore_printf_loop = 0;
  thread_join(id);
}
