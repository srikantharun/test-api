#include <stdbool.h>
#include <stdint.h>

/*
 * Driver for RISC-V ACLINT-compatibile CLINT (core-local interrupt controller)
 *
 * https://github.com/riscv/riscv-aclint/blob/main/riscv-aclint.adoc
 *
 * Each PVE comes with its own CLINT, handling the 8 HARTs in that PVE.
 * This file only contains the code required on other cores (i.e., to send SW
 * IRQs to the PVE cores). See pve/clint.c for full implementation
 */

// MSIP
void pve_clint_set_sw_irq(uint64_t hartid);
