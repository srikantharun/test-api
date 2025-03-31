#include <dw_timer/drv_dw_timer.h>
#include <timer.h>
#include <testutils.h>
#include <platform.h>
#include <interrupt.h>
#include <critical_section.h>

#define TIMER_LOAD_VALUE 0xFFAB
#define TIMER_LOAD_VALUE_IRQ 0x1000
#define TIMER_INITIAL_VALUE 0xFFFFFFFF
#define TIMER_STEP_TOLERANZ 0x1000

static uint32_t timer_irq_triggered[SOC_PERIPH_TIMER_NB] = {0};

void timer0_irq_handler() {
  timerDisable(0);
  timerClearIsr(0);

  printf("timer 0 irq triggered\n");
  timer_irq_triggered[0]++;
}

void timer1_irq_handler() {
  timerDisable(1);
  timerClearIsr(1);

  printf("timer 1 irq triggered\n");
  timer_irq_triggered[1]++;
}

#ifndef NO_INTERRUPTS
static void test_timer_irq(int timer_idx) {
  /* Disable interrupts in general. */
  timerDisable(timer_idx);
  timerSetMode(timer_idx, kTimerUserMode);
  timerLoad(timer_idx, TIMER_LOAD_VALUE_IRQ);
  timerSetupInterrupt();

  timerEnable(timer_idx);
  asm volatile("wfi");

  for (int i = 0; i < SOC_PERIPH_TIMER_NB; i++) {
    if(timer_idx == i) {
      CHECK_EQUAL_INT(1, timer_irq_triggered[i], "Failed to trigger timer once, triggered %d times.", timer_irq_triggered[i]);
    } else {
      CHECK_EQUAL_INT(0, timer_irq_triggered[i], "Triggered wrong timer once, triggered timer %d.", i);
    }
    timer_irq_triggered[i] = 0;
  }
}
#endif

static bool isTimerNearLoadValue(int32_t value) {
  return (TIMER_LOAD_VALUE - value <= TIMER_STEP_TOLERANZ) && (TIMER_LOAD_VALUE - value >= 0);
}

static void test_timer(int timer_idx) {
  /* Disable interrupts in general. */
  timerDisable(timer_idx);
  timerSetMode(timer_idx, kTimerUserMode);
  timerLoad(timer_idx, TIMER_LOAD_VALUE);
  timerEnable(timer_idx);

  cycledelay(10); // Super small delay does the job to startup the timer

  int32_t val = timerRead(timer_idx);
  CHECK_TRUE(isTimerNearLoadValue(val), "Timer value is %d (after loading to %d)", val, TIMER_LOAD_VALUE);
}

int main() {
  testcase_init();

  printf("*** TIMER test starts!\n");

  for(int i = 0; i < SOC_PERIPH_TIMER_NB; i++) // TODO: SOC_PERIPH_TIMER_NB
  {
    test_timer(i);

#ifndef NO_INTERRUPTS
    test_timer_irq(i);
#endif // NO_INTERRUPTS
  }


  return testcase_finalize();
}

