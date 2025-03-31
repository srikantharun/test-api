#include <testutils.h>
#include <stdbool.h>
#include <critical_section.h>
#include <plmt/drv_plmt.h>
#include <timer.h>

volatile bool interrupt_fired = false;
atomic_flag lock = ATOMIC_FLAG_INIT;

#define TIMER_INTERVAL_CYCLES 12000

void verify_mtimer(void) {
  interrupt_fired = true;
  plmtDisableInterrupt();
}

void test_critical_section_effectiveness() {
  // setup timer interrupt
  uint64_t key = arch_irq_lock();
  plmtSetupInterrupt(TIMER_INTERVAL_CYCLES);
  arch_irq_unlock(key);

  enter_critical_section(&lock);

  delay_mtime_cycles(2 * TIMER_INTERVAL_CYCLES);

  // Check if interrupt did fire
  CHECK_TRUE(!interrupt_fired, "Interrupt should not have fired\n");

  exit_critical_section(&lock);

  delay_mtime_cycles(2 * TIMER_INTERVAL_CYCLES);

  // Verify that interrupt did fire
  CHECK_TRUE(interrupt_fired, "Interrupt did not fire as expected\n");
}

int main() {
  testcase_init();

  /* START TEST */
  printf("*** Critical Section Effectiveness Test starts!\n");

  test_critical_section_effectiveness();

  /* END TEST */
  return testcase_finalize();
}

