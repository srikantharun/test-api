// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

#include <platform.h>
#include <stdbool.h>
#include <critical_section.h>
#include <regutils.h>
#include <memorymap.h>
#include <plmt/drv_plmt.h>
#include <testutils.h>

#define PLMT_TIMER_PERIOD 120000

static volatile __thread uint64_t num_mtimer_triggered = 0;

void verify_mtimer(void) {
  num_mtimer_triggered++;
}

int thread_test_plmt(void *arg) {
  UNUSED(arg);
  testcase_init();

  // // TODO: Should add proper delay function. See Triton.
  // while (!mtimer_triggered) {
  //     printf("waiting in the loop...\n");
  // }

  {
    printf("checking mtime register read...\n");

    uint64_t t1, t2;
    t1 = read_mtime();
    t2 = read_mtime();

    CHECK_TRUE(t2 > t1, "plmt is not running");
  }

  {
    printf("checking timer interrupts...\n");

    // 1. enable timer interr
    /* Disable interrupts in general. */
    uint64_t key = arch_irq_lock();
    plmtSetupInterrupt(PLMT_TIMER_PERIOD);
    /* Enable interrupts in general. */
    arch_irq_unlock(key);

    // 2. busy loop for timer period
    delay_mtime_cycles(PLMT_TIMER_PERIOD);

    // 3. check interrupt has fired at least once
    CHECK_TRUE(num_mtimer_triggered >= 1, "timer interrupt has not fired");

    // 4. disable interrupts
    plmtDisableInterrupt();
    uint64_t num_mtimer_triggered_after_disable = num_mtimer_triggered;

    // 5. wait for twice the timer period
    delay_mtime_cycles(2 * PLMT_TIMER_PERIOD);

    // 6. check interrupt has not fired since
    CHECK_EQUAL_INT(num_mtimer_triggered_after_disable, num_mtimer_triggered,
        "timer interrupt fired after disabling");
  }

  return testcase_finalize();
}

int main() {
  printf("*** PLMT test starts!\n");

  for (tid_t id = 1; id < HW_DEFINES_APU_CORE_NUMBER; id++) {
    thread_launch(id, thread_test_plmt, NULL);
  }
  int ret = thread_test_plmt(NULL);
  ret |= thread_join_all();

  return ret;
}

