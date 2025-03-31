#include <asm.h>
#include <memorymap.h>
#include <platform.h>
#include <stdint.h>

#include "pve_clint.h"

/*
 * Driver for RISC-V ACLINT-compatibile CLINT (core-local interrupt controller)
 *
 * https://github.com/riscv/riscv-aclint/blob/main/riscv-aclint.adoc
 *
 * Each PVE comes with its own CLINT, handling the 8 HARTs in that PVE.
 * This file only contains the code required on other cores (i.e., to send SW
 * IRQs to the PVE cores). See pve/clint.c for full implementation.
 */

// values taken from gc_clint.sv
#define CLINT_MSIP_BASE     0x0

static uintptr_t get_clint_base(uint64_t hartid) {
    // return correct CLINT base depending on if hartid is part of PVE0 or PVE1
    if (hartid < PVE_1_CLUSTER_0_CORE_0) {
        return PVE_0_CLINT_BASE;
    } else {
        return PVE_1_CLINT_BASE;
    }
}

static uint64_t get_clint_relative_id(uint64_t hartid) {
    // return "relative ID" inside PVE
    hartid = (hartid - PVE_0_CLUSTER_0_CORE_0 ) % NUM_PVE_CORES;
    return hartid & 0b111;
}

static volatile uint32_t* get_clint_msip_reg(uint64_t hartid) {
    volatile uint32_t *msip = (volatile uint32_t*)(get_clint_base(hartid) + CLINT_MSIP_BASE);
    return &msip[get_clint_relative_id(hartid)];
}

void pve_clint_set_sw_irq(uint64_t hartid) {
    *get_clint_msip_reg(hartid) = 0x1;
}
