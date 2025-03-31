
#ifndef DRV_DW_TIMERS_H
#define DRV_DW_TIMERS_H

#include <platform.h>
#include <stdbool.h>
#include <stdint.h>

// Number of timers instantiated inside SOC_PERIPH's dw_timer component
#define SOC_PERIPH_TIMER_NB 2

// Choose a timer mode
// 0 : USER_DEFINED
// 1 : FREE_RUNNINGS
typedef enum {
  kTimerUserMode = 0,
  kTimerFreeMode = 1,
} timerMode;

void timerUnmaskIsr(int timer_idx);
void timerEnable(int timer_idx);
void timerDisable(int timer_idx);
void timerLoad(int timer_idx, uint32_t value);
void timerSetMode(int timer_idx, timerMode mode);
uint32_t timerRead(int timer_idx);
bool timerIsIsrActive(int timer_idx);
void timerClearIsr(int timer_idx);
void timerSetupInterrupt();

#endif // DRV_DW_TIMERS_H
