#include "drv_dw_timer.h"
#include <interrupt.h>
#include <memorymap.h>
#include <std/std_basetype.h>
#include <std/std_bit.h>
#include <testutils.h>

// Max number of timers present inside dw_timer component
#define MAX_TIMER 8

#define TIMERNCONTROLREG_TIMER_ENABLE_BIT 0
#define TIMERNCONTROLREG_TIMER_MODE_BIT 1
#define TIMERNCONTROLREG_TIMER_INTERRUPT_MASK 2

typedef struct {
  struct {
    reg32_t TimerNLoadCount;    // 0x000+(N-1)*0x14
    reg32_t TimerNCurrentValue; // 0x004+(N-1)*0x14
    reg32_t TimerNControlReg;   // 0x008+(N-1)*0x14
    reg32_t TimerNEOI;          // 0x00c+(N-1)*0x14
    reg32_t TimerNIntStatus;    // 0x010+(N-1)*0x14
  } timer_n_regs[SOC_PERIPH_TIMER_NB];
  reg32_t reserved1[5 * (MAX_TIMER - SOC_PERIPH_TIMER_NB)]; // 0x028 : Reserved
                                                            // for rest timers
  reg32_t TimersIntStatus;                                  // 0x0a0
  reg32_t TimersEOI;                                        // 0x0a4
  reg32_t TimersRawIntStatus;                               // 0x0a8
  reg32_t TIMERS_COMP_VERSION;                              // 0x0ac
  reg32_t TimerNLoadCount2[SOC_PERIPH_TIMER_NB];            // 0x0b0 + (N-1)*0x4
  reg32_t reserved2[2 * (MAX_TIMER - SOC_PERIPH_TIMER_NB)];
  reg32_t TIMER_N_PROT_LEVEL; // 0x0d0
} HalTimerReg;

void default_timer_irq_handler(void) {};
void timer0_irq_handler(void) __attribute__((weak, alias("default_timer_irq_handler")));
void timer1_irq_handler(void) __attribute__((weak, alias("default_timer_irq_handler")));

const isr_func irq_handler_func[SOC_PERIPH_TIMER_NB] = {
    [0] = timer0_irq_handler,
    [1] = timer1_irq_handler,
};

#define pTIMER ((HalTimerReg *)(SOC_PERIPH_TIMER_BASE))
#define TIMER_N_REGS(idx) pTIMER->timer_n_regs[idx]
#define CHECK_IDX_VALID(idx) ASSERT(timer_idx < SOC_PERIPH_TIMER_NB)

void timerUnmaskIsr(int timer_idx) {
  CHECK_IDX_VALID(timer_idx);
  TIMER_N_REGS(timer_idx).TimerNControlReg =
      stdBitClearU32(TIMER_N_REGS(timer_idx).TimerNControlReg,
                     TIMERNCONTROLREG_TIMER_INTERRUPT_MASK);
#ifndef NO_INTERRUPTS
  HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_TIMER_SOURCE);
  HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_TIMER_SOURCE, IRQ_PRIORITY_DEFAULT);
#endif
}

void timerEnable(int timer_idx) {
  CHECK_IDX_VALID(timer_idx);
  TIMER_N_REGS(timer_idx).TimerNControlReg =
      stdBitSetU32(TIMER_N_REGS(timer_idx).TimerNControlReg,
                   TIMERNCONTROLREG_TIMER_ENABLE_BIT);
}

void timerDisable(int timer_idx) {
  CHECK_IDX_VALID(timer_idx);
  TIMER_N_REGS(timer_idx).TimerNControlReg =
      stdBitClearU32(TIMER_N_REGS(timer_idx).TimerNControlReg,
                     TIMERNCONTROLREG_TIMER_ENABLE_BIT);
}

void timerLoad(int timer_idx, uint32_t value) {
  CHECK_IDX_VALID(timer_idx);
  TIMER_N_REGS(timer_idx).TimerNLoadCount = value;
}

void timerSetMode(int timer_idx, timerMode mode) {
  CHECK_IDX_VALID(timer_idx);
  if (mode == kTimerUserMode) {
    TIMER_N_REGS(timer_idx).TimerNControlReg =
        stdBitSetU32(TIMER_N_REGS(timer_idx).TimerNControlReg,
                     TIMERNCONTROLREG_TIMER_MODE_BIT);
  } else if (mode == kTimerFreeMode) {
    TIMER_N_REGS(timer_idx).TimerNControlReg =
        stdBitClearU32(TIMER_N_REGS(timer_idx).TimerNControlReg,
                       TIMERNCONTROLREG_TIMER_MODE_BIT);
  }
}

uint32_t timerRead(int timer_idx) {
  CHECK_IDX_VALID(timer_idx);
  return TIMER_N_REGS(timer_idx).TimerNCurrentValue;
}

bool timerIsIsrActive(int timer_idx) {
  CHECK_IDX_VALID(timer_idx);
  return (TIMER_N_REGS(timer_idx).TimerNIntStatus != 0u);
}

void timer_irq_handler(void) {
  for (int i = 0; i < SOC_PERIPH_TIMER_NB; i++) {
    if(!timerIsIsrActive(i)) {
      continue;
    }

    irq_handler_func[i]();
  }
}

void timerSetupInterrupt() {
  HAL_INTERRUPT_ENABLE(IRQ_SOC_PERIPH_TIMER_SOURCE);
  HAL_INTERRUPT_SET_LEVEL(IRQ_SOC_PERIPH_TIMER_SOURCE, IRQ_PRIORITY_DEFAULT);
}

void timerClearIsr(int timer_idx) {
  CHECK_IDX_VALID(timer_idx);
  TIMER_N_REGS(timer_idx).TimerNEOI;
}
