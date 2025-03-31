#include <testutils.h>
#include <atomics.h>
#include <plmt/drv_plmt.h>
#include <platform.h>
#include <timer.h>
#include <critical_section.h>

volatile uint64_t cnt = 0;
_Atomic uint64_t shared_variable = 0;

#define NUM_ITERATIONS 1000

void atomic_add_incrementation() {
  for (int i = 0; i < NUM_ITERATIONS; i++) {
    atomic_add(&shared_variable, 1);
  }
}

void verify_mtimer(void) {
  cnt++;
  atomic_add(&shared_variable, 1);
}

void test_contention_atomics_basic() {
  /* Disable interrupts in general. */
  uint64_t key = arch_irq_lock();
  plmtSetupInterrupt(7200);
  /* Enable interrupts in general. */
  arch_irq_unlock(key);

  atomic_add_incrementation();

  plmtDisableInterrupt();

  CHECK_EQUAL_INT(NUM_ITERATIONS + cnt, shared_variable);
  CHECK_TRUE(cnt > 0, "Interrupt did not fire as expected\n");
}

int main() {
  testcase_init();

  /* START TEST */
  printf("*** Contention Atomic Basics Test starts!\n");

  test_contention_atomics_basic();

  /* END TEST */
  return testcase_finalize();
}

