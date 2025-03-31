// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***

#include "pctl/drv_pctl.h"
#include <testutils.h>
#include <regutils.h>


uint32_t pctlResetStatus(pctl_regs* pctl_regs, unsigned int num)
{
    ASSERT(num < MAX_RESETS, "num should be less than %u", MAX_RESETS);
    return get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_status), 4 * num, PARTITION_RESET_FSM_STATE_0_MASK);
}

int pctlResetRemove(pctl_regs* pctl_regs, unsigned int num)
{
    unsigned int iterations = 0;
    ASSERT(num < MAX_RESETS, "num should be less than %u", MAX_RESETS);

    set_reg_u32((uintptr_t)&(pctl_regs->ppmu_reset_control[num]), RESET_REMOVE_MASK << RESET_REMOVE_OFFSET);
    while(get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_status), 4 * num, PARTITION_RESET_FSM_STATE_0_MASK) != PPMU_FSM_ACTIVE) {
        if(++iterations > MAX_ITERATIONS)
            return 1;
    }
    return 0;
}

int pctlResetActivate(pctl_regs* pctl_regs, unsigned int num)
{
    unsigned int iterations = 0;
    ASSERT(num < MAX_RESETS, "num should be less than %u", MAX_RESETS);

    set_reg_u32((uintptr_t)&(pctl_regs->ppmu_reset_control[num]), RESET_ACTIVATE_MASK << RESET_ACTIVATE_OFFSET);
    while(get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_status), 4 * num, PARTITION_RESET_FSM_STATE_0_MASK) != PPMU_FSM_RESET) {
        if(++iterations > MAX_ITERATIONS)
            return 1;
    }
    return 0;
}

void pctlSetTiming(pctl_regs* pctl_regs, unsigned int num, ppmu_timing_control* timing_config)
{
    ASSERT(num < MAX_RESETS, "num should be less than %u", MAX_RESETS);
    uint32_t timing_control = 0;
    timing_control |= ((uint32_t)timing_config->pre_rst_0_cycles << PRE_RST_0_CYCLES_OFFSET);
    timing_control |= ((uint32_t)timing_config->pre_rst_1_cycles << PRE_RST_1_CYCLES_OFFSET);
    timing_control |= ((uint32_t)timing_config->pre_rst_2_cycles << PRE_RST_2_CYCLES_OFFSET);
    timing_control |= ((uint32_t)timing_config->pre_rel_cycles << PRE_REL_CYCLES_OFFSET);
    set_reg_u32((uintptr_t)&(pctl_regs->ppmu_reset_timing_control[num]), timing_control);
}

void pctlGetTiming(pctl_regs* pctl_regs, unsigned int num, ppmu_timing_control* timing_config)
{
    ASSERT(num < MAX_RESETS, "num should be less than %u", MAX_RESETS);
    uint32_t timing_control = get_reg_u32((uintptr_t)&(pctl_regs->ppmu_reset_timing_control[num]));
    timing_config->pre_rst_0_cycles = (timing_control >> PRE_RST_0_CYCLES_OFFSET) & PRE_RST_0_CYCLES_MASK;
    timing_config->pre_rst_1_cycles = (timing_control >> PRE_RST_1_CYCLES_OFFSET) & PRE_RST_1_CYCLES_MASK;
    timing_config->pre_rst_2_cycles = (timing_control >> PRE_RST_2_CYCLES_OFFSET) & PRE_RST_2_CYCLES_MASK;
    timing_config->pre_rel_cycles = (timing_control >> PRE_REL_CYCLES_OFFSET) & PRE_REL_CYCLES_MASK;
}


void pctlClockGate(pctl_regs* pctl_regs, unsigned int num, uint32_t control)
{
    ASSERT(num < MAX_CLKDIVS, "num should be less than %u", MAX_CLKDIVS);
    ASSERT(control <= 1, "control should be either 0 or 1");

    set_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_clock_gating_control[num]), control, CLOCK_DISABLE_OFFSET, CLOCK_DISABLE_MASK);
}

void pctlClockSetDivider(pctl_regs* pctl_regs, unsigned int num, uint32_t div)
{
    ASSERT(num < MAX_CLKDIVS, "num should be less than %u", MAX_CLKDIVS);
    set_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_clock_gating_control[num]), div, CLOCK_DIVIDER_OFFSET, CLOCK_DIVIDER_OFFSET);
}


uint32_t pctlFenceStatus(pctl_regs* pctl_regs, unsigned int num)
{
    ASSERT(num < MAX_FENCES, "num should be less than %u", MAX_FENCES);
    return get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_status[num]), ISOLATION_IDLE_VAL_OFFSET, ISOLATION_IDLE_VAL_MASK);
}

int pctlFenceRemove(pctl_regs* pctl_regs, unsigned int num)
{
    unsigned int iterations = 0;
    ASSERT(num < MAX_FENCES, "num should be less than %u", MAX_FENCES);

    set_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_control), 0, num, ISOLATION_IDLE_REQ_0_MASK);
    while(get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_status[num]), ISOLATION_IDLE_ACK_OFFSET, ISOLATION_IDLE_ACK_MASK) != 0x00) {
        if(++iterations > MAX_ITERATIONS)
            return 1;
    }
    while(get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_status[num]), ISOLATION_IDLE_VAL_OFFSET, ISOLATION_IDLE_VAL_MASK) != 0x00) {
        if(++iterations > MAX_ITERATIONS)
            return 1;
    }
    return 0;
}

int pctlFenceActivate(pctl_regs* pctl_regs, unsigned int num)
{
    unsigned int iterations = 0;
    ASSERT(num < MAX_FENCES, "num should be less than %u", MAX_FENCES);

    set_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_control), 1, num, ISOLATION_IDLE_REQ_0_MASK);
    while(get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_status[num]), ISOLATION_IDLE_ACK_OFFSET, ISOLATION_IDLE_ACK_MASK) != 0x01) {
        if(++iterations > MAX_ITERATIONS)
            return 1;
    }
    while(get_range_u32_mask((uintptr_t)&(pctl_regs->ppmu_isolation_status[num]), ISOLATION_IDLE_VAL_OFFSET, ISOLATION_IDLE_VAL_MASK) != 0x01) {
        if(++iterations > MAX_ITERATIONS)
            return 1;
    }
    return 0;
}
