#include <asm.h>
#include <encoding.h>
#include <memorymap.h>
#include <platform.h>
#include <stdint.h>

#include "clint.h"

/*
 * Driver for RISC-V ACLINT-compatibile CLINT (core-local interrupt controller)
 *
 * https://github.com/riscv/riscv-aclint/blob/main/riscv-aclint.adoc
 *
 * Each PVE comes with its own CLINT, handling the 8 HARTs in that PVE.
 */

// values taken from gc_clint.sv
#define CLINT_MSIP_BASE     0x0
#define CLINT_MTIMECMP_BASE 0x4000
#define CLINT_MTIME_BASE    0xbff8

static uint64_t timer_interval = 0;

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
    hartid -= PVE_0_CLUSTER_0_CORE_0;
    return hartid & 0b111;
}

static volatile uint32_t* get_clint_msip_reg(uint64_t hartid) {
    volatile uint32_t *msip = (volatile uint32_t*)(get_clint_base(hartid) + CLINT_MSIP_BASE);
    return &msip[get_clint_relative_id(hartid)];
}

static volatile uint64_t* get_clint_mtimecmp_reg(uint64_t hartid) {
    volatile uint64_t *mtimecmp = (volatile uint64_t*)(get_clint_base(hartid) + CLINT_MTIMECMP_BASE);
    return &mtimecmp[get_clint_relative_id(hartid)];
}

static volatile uint64_t* get_clint_mtime_reg(uint64_t hartid) {
    volatile uint64_t *mtime = (volatile uint64_t*)(get_clint_base(hartid) +  CLINT_MTIME_BASE);
    return mtime;
}

bool clint_is_sw_irq_pending() {
    uint64_t hartid = r_mhartid(); // this core
    return *get_clint_msip_reg(hartid) != 0;
}

void clint_set_sw_irq(uint64_t hartid) {
    *get_clint_msip_reg(hartid) = 0x1;
}

void clint_clear_sw_irq() {
    uint64_t hartid = r_mhartid(); // this core
    *get_clint_msip_reg(hartid) = 0x0;
}

uint64_t clint_read_mtimecmp() {
    uint64_t hartid = r_mhartid(); // this core
    return *get_clint_mtimecmp_reg(hartid);
}

void clint_write_mtimecmp(uint64_t timecmp) {
    uint64_t hartid = r_mhartid(); // this core
    *get_clint_mtimecmp_reg(hartid) = timecmp;
}

uint64_t clint_read_mtime() {
    uint64_t hartid = r_mhartid(); // this core
    return *get_clint_mtime_reg(hartid);
}

void clint_write_mtime(uint64_t time) {
    uint64_t hartid = r_mhartid(); // this core
    *get_clint_mtime_reg(hartid) = time;
}

// timer interrupt functionality
// -----------------------------
void clint_reset_timer() {
    if (timer_interval == 0) abort();
    uint64_t mtimecmp = clint_read_mtime() + timer_interval;
    clint_write_mtimecmp(mtimecmp);
}

void clint_enable_timer(uint64_t interval) {
    timer_interval = interval;
    clint_reset_timer();
    // enable timer interrupts
    set_csr(CSR_MIE, MIP_MTIP);
}

void clint_disable_timer() {
    clear_csr(CSR_MIE, MIP_MTIP);
    timer_interval = 0;
}

void clint_delay_mtime_cycles(uint64_t cycles) {
    uint64_t end = clint_read_mtime() + cycles;
    while (clint_read_mtime() < end)
        ;
}
