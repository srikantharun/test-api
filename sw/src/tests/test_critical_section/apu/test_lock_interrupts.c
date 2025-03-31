#include <testutils.h>
#include <critical_section.h>
#include <plmt/drv_plmt.h>
#include <timer.h>

volatile uint64_t cnt = 0;

#define TIMER_INTERVAL_CYCLES 50000

void verify_mtimer(void) {
  cnt++;
  plmtDisableInterrupt();
}

static void configureMachineTimerInterrupts(){
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();
  plmtSetupInterrupt(TIMER_INTERVAL_CYCLES);
  /* Enable interrupts in general. */
  arch_irq_unlock(key);
}

static void test_lock_interrupts(void) {
  /* Lock interrupts */
  unsigned int key = arch_irq_lock();
  cnt = 0; // Reset the count

  delay_mtime_cycles(2 * TIMER_INTERVAL_CYCLES);
  CHECK_TRUE(cnt == 0, "Interrupt should not have fired\n");

  arch_irq_unlock(key); // Unlock interrupts

  delay_mtime_cycles(2 * TIMER_INTERVAL_CYCLES);
  CHECK_TRUE(cnt != 0, "Interrupt did not fire as expected\n");
}

int main() {
  testcase_init();

  /* START TEST */
  printf("*** Test lock interrupts starts!\n");

  configureMachineTimerInterrupts();

  test_lock_interrupts();

  /* END TEST */
  return testcase_finalize();
}

