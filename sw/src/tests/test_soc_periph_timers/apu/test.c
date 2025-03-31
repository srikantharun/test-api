// TIMER tests
//
// test_soc_periph_timer_count:
//
// 1. For each timer (1 and 2)
// 2. Enable user mode
// 3. Enable interrupts
// 4. Set its load value to 0xFFFFu
// 5. Start the timer and wait for its interrupt
// 6. Verify the timer has correctly looped in the expected amount of time with
// an error margin of 5%.

#include <dw_timer/drv_dw_timer.h>
#include <stdbool.h>
#include <stdint.h>
#include <testutils.h>
#include <uvm_ipc/uvm_sw_ipc.h>

#define TIMER_FREQ_MHZ 100
#define TIMER_PERIOD_NS ((double)1000.0 / TIMER_FREQ_MHZ)
#define TIMER_LOADVAL 0xFFFu

void timer0_irq_handler() {
  timerClearIsr(0);
}

void timer1_irq_handler() {
  timerClearIsr(1);
}


void test_soc_periph_timer_count() {
  const char *wire_timer_int = "spike_top_tb.th.o_timer_int";
  for (int timer_idx = 0; timer_idx < SOC_PERIPH_TIMER_NB; timer_idx++) {
    uint64_t time_ns;

    // Configure timer
    timerDisable(timer_idx);
    timerSetMode(timer_idx, kTimerUserMode);
    timerUnmaskIsr(timer_idx);
    timerLoad(timer_idx, TIMER_LOADVAL);
    CHECK_EQUAL_INT(0u, uvm_sw_ipc_hdl_read(wire_timer_int));
    // Tell the UVM to monitor the IRQ
    timerEnable(timer_idx);
    uvm_sw_ipc_gen_event(0u);
    uvm_sw_ipc_wait_event(0u);
    CHECK_EQUAL_INT(1u, uvm_sw_ipc_hdl_read(wire_timer_int));
    // Clear irq
    timerClearIsr(timer_idx);
    // Get the time taken by the timer to get an IRQ
    uvm_sw_ipc_pull_data(0u, &time_ns);
    // Check experimental and expected durations are within 5% of each other
    CHECK_RTOL((TIMER_PERIOD_NS * TIMER_LOADVAL), time_ns, 0.05, 0.0);
    timerDisable(timer_idx);
  }
}

int main() {
  testcase_init();
  test_soc_periph_timer_count();
  return testcase_finalize();
}
