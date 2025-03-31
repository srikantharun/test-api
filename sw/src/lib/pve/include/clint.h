#include <stdbool.h>
#include <stdint.h>

/*
 * Driver for RISC-V ACLINT-compatibile CLINT (core-local interrupt controller)
 *
 * https://github.com/riscv/riscv-aclint/blob/main/riscv-aclint.adoc
 *
 * Each PVE comes with its own CLINT, handling the 8 HARTs in that PVE.
 */

// MSIP
bool clint_is_sw_irq_pending();
void clint_set_sw_irq(uint64_t hartid);
void clint_clear_sw_irq();

// MTIMECMP
uint64_t clint_read_mtimecmp();
void clint_write_mtimecmp(uint64_t timecmp);

// MTIME
uint64_t clint_read_mtime();
void clint_write_mtime(uint64_t time);

// timer
void clint_reset_timer();
void clint_enable_timer(uint64_t interval);
void clint_disable_timer();

// delay
void clint_delay_mtime_cycles(uint64_t cycles);
