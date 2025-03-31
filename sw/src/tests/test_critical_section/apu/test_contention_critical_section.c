#include <testutils.h>
#include <critical_section.h>
#include <plmt/drv_plmt.h>
#include <timer.h>

atomic_flag lock = ATOMIC_FLAG_INIT;
volatile uint64_t shared_variable = 0;
volatile uint64_t cnt = 0;

#define NUM_ITERATIONS 100
#define ITERATION_DELAY_CYCLES 10
#define TIMER_INTERVAL_CYCLES 24000

void critical_section_incrementation() {
  for (int i = 0; i < NUM_ITERATIONS; i++) {
    enter_critical_section(&lock);
    shared_variable++;
    // additional delay to ensure timer interrupt fires while this function is running
    delay_mtime_cycles(ITERATION_DELAY_CYCLES);
    exit_critical_section(&lock);
  }
}

void verify_mtimer(void) {
  cnt++;
  enter_critical_section(&lock);
  shared_variable++;
  exit_critical_section(&lock);
}

void test_contention_critical_section() {
  // setup timer interrupt
  uint64_t key = arch_irq_lock();
  plmtSetupInterrupt(TIMER_INTERVAL_CYCLES);
  arch_irq_unlock(key);

  critical_section_incrementation();

  plmtDisableInterrupt();

  CHECK_EQUAL_INT(NUM_ITERATIONS + cnt, shared_variable);
  printf("[INFO] Received %d MTIME interrupts during test\r\n", cnt);
  CHECK_TRUE(cnt > 0, "Interrupt did not fire as expected\n");
}

int main() {
  testcase_init();

  /* START TEST */
  printf("*** Contention Critical Section Test starts!\n");

  test_contention_critical_section();

  /* END TEST */
  return testcase_finalize();
}

