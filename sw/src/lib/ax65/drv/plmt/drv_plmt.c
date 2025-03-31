#include "drv_plmt.h"

uint64_t MACHINE_TIMER_PERIOD = 1000;

typedef struct {
  reg64_t MTIME;    /* 0x00 Machine Time */
  reg64_t MTIMECMP[NUM_APU_CORES]; /* 0x08 Machine Time Compare */
} HalPlmtReg;

/* the pointer to the PLMT register file */
#define pPLMT ((HalPlmtReg*)(APU_PLMT_BASE))

static void reset_timer() {
  uint64_t hartid = r_mhartid();
  pPLMT->MTIMECMP[hartid] = pPLMT->MTIME + MACHINE_TIMER_PERIOD;
}

void plmtSetupInterrupt(uint64_t set_timer_period) {
  MACHINE_TIMER_PERIOD = set_timer_period;
  reset_timer();
  HAL_MTIME_ENABLE();
}

void plmtDisableInterrupt(void) {
  HAL_MTIME_DISABLE();
}

void mtime_handler(void)
{
  reset_timer();
}

uint64_t read_mtime() {
  return pPLMT->MTIME;
}

void delay_mtime_cycles(uint64_t mtime_cycles) {
  uint64_t end = read_mtime() + mtime_cycles;
  while (read_mtime() < end)
    ;
}
