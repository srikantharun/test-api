#include <stddef.h>
#include <stdint.h>

#include "asm.h"
#include "interrupt.h"
#include "multicore.h"
#include "platform.h"
#include <testutils.h>
#include <pctl_utils.h>
#include <regutils.h>

volatile core_t multicore_sync[NUM_CORES] = {0};

void _multicores_init() {
    for(int i = APU_CORE_0; i < NUM_CORES; i ++) {
        multicore_sync[i].status = STATUS_IDLE;
    }
}

int is_core_available(uint32_t core_id) {
    if (core_id <= APU_CORE_5) {
        if (core_id < HW_DEFINES_APU_CORE_NUMBER)
            return 1;
    } else if (core_id <= AI_CORE_7) {
        if (core_id < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER)
            return 1;
    } else if (core_id <= PVE_0_CLUSTER_3_CORE_1) {
        if (core_id < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER)
            return 1;
    } else if (core_id <= PVE_1_CLUSTER_3_CORE_1) {
        if (core_id < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER)
            return 1;
    }
    return 0;
}

void boot_aicore(uint32_t core_id)
{
    // Activate neccassary signals controled by the PCTL
    pctl_enable_aicore(core_id);
    // Set boot address and clock enable bit
    core_id = core_id - AI_CORE_0;
    set_reg_u64(SYS_CFG_AICORE_0_AO_CSR_BASE + 0x200 + SYS_CFG_AICORE_0_AO_CSR_SIZE * core_id, AICORE_0_SPM_BASE + AICORE_0_SIZE * core_id); // reset vector aicore0
    set_reg_u64(AICORE_0_CONFIGURATION_PERIPHERALS_CSR_BASE + 0x58 + AICORE_0_SIZE * core_id, 0x1);                                          // cva6v clock enable
}

void boot_pve_core(uint32_t core_id)
{
    uintptr_t base;
    uintptr_t boot_addr;

    // Select correct register pointers and activate neccassary signals controled by the PCTL
    if(core_id < PVE_1_CLUSTER_0_CORE_0) {
        core_id -= PVE_0_CLUSTER_0_CORE_0;
        base = SYS_CFG_PVE_0_AO_CSR_BASE;
        boot_addr = PVE_0_SPM_BASE;
        pctl_enable_pve_0();
    } else {
        core_id -= PVE_1_CLUSTER_0_CORE_0;
        base = SYS_CFG_PVE_1_AO_CSR_BASE;
        boot_addr = PVE_1_SPM_BASE;
        pctl_enable_pve_1();
    }
    uintptr_t pve_boot_lsb_ptr = base + SYS_CFG_PVE_BOOT_ADDR_LSB_OFFSET + core_id * SYS_CFG_PVE_REG_SIZE;
    uintptr_t pve_boot_msb_ptr = base + SYS_CFG_PVE_BOOT_ADDR_MSB_OFFSET + core_id * SYS_CFG_PVE_REG_SIZE;
    uintptr_t pve_clk_en_ptr   = base + SYS_CFG_PVE_BOOT_ADDR_CLK_EN_OFFSET;

    // Set boot address and clock enable bit
    set_reg_u32(pve_boot_lsb_ptr, (uint64_t)boot_addr & 0xffffffff); // LSB of the the Boot Address
    set_reg_u32(pve_boot_msb_ptr, (uint64_t)boot_addr >> 32);        // MSB of the the Boot Address
    set_range_u32(pve_clk_en_ptr, 1, core_id, core_id);              // Clock enable
}

void start_core(uint32_t core_id) {
    ASSERT(core_id >= AI_CORE_0 && core_id < NUM_CORES, "The hart_id must be in range [%d, %d]\n", AI_CORE_0, PVE_1_CLUSTER_3_CORE_1);

    if(core_id < PVE_0_CLUSTER_0_CORE_0) {
        boot_aicore(core_id);
    } else {
        boot_pve_core(core_id);
    }

    // Ensure the selected worker is not currently running a job.
    if (multicore_sync[core_id].status != STATUS_IDLE && multicore_sync[core_id].status != STATUS_EXITED)
    {
        abort();
    }

    while (multicore_sync[core_id].status != STATUS_READY);

#ifndef NO_INTERRUPTS
    // Interrupt core
    interrupt_core(core_id);
#endif
};

void start_aicores() {
    for(uint32_t core_id = AI_CORE_0; core_id < PVE_0_CLUSTER_0_CORE_0; core_id ++) {
        start_core(core_id);
    }
};

void start_aicores_available() {
    for(uint32_t core_id = AI_CORE_0; core_id < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER; core_id ++) {
        start_core(core_id);
    }
};

void start_cores_pve0() {
    for(uint32_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id < PVE_1_CLUSTER_0_CORE_0; core_id ++) {
        start_core(core_id);
    }
};

void start_cores_pve0_available() {
    for(uint32_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER; core_id ++) {
        start_core(core_id);
    }
};

void start_cores_pve1() {
    for(uint32_t core_id = PVE_1_CLUSTER_0_CORE_0; core_id < NUM_CORES; core_id ++) {
        start_core(core_id);
    }
};

void start_cores_pve1_available() {
    for(uint32_t core_id = PVE_1_CLUSTER_0_CORE_0; core_id < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER; core_id ++) {
        start_core(core_id);
    }
};

void start_cores_all() {
    start_aicores();
    start_cores_pve0();
    start_cores_pve1();
};

void start_cores_available() {
    start_aicores_available();
    start_cores_pve0_available();
    start_cores_pve1_available();
};


int wait_core(uint32_t core_id) {
    // Ensure the thread has been launched at least once.
    switch (multicore_sync[core_id].status)
    {
        case STATUS_READY:
        case STATUS_RUNNING:
        case STATUS_EXITED:
            break;
        default:
            abort();
    }

    // Wait for finish.
    while (multicore_sync[core_id].status != STATUS_EXITED);

    // Move core to idle (so it is not joined multiple times).
    multicore_sync[core_id].status = STATUS_IDLE;

    return multicore_sync[core_id].ret;
};

int wait_aicores() {
    int ret = 0;
    for(uint32_t core_id = AI_CORE_0; core_id < PVE_0_CLUSTER_0_CORE_0; core_id ++) {
        ret |= wait_core(core_id);
    }
    return ret;
};

int wait_aicores_available() {
    int ret = 0;
    for(uint32_t core_id = AI_CORE_0; core_id < AI_CORE_0 + HW_DEFINES_AICORE_MODULE_NUMBER; core_id ++) {
        ret |= wait_core(core_id);
    }
    return ret;
};

int wait_cores_pve0() {
    int ret = 0;
    for(uint32_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id < PVE_1_CLUSTER_0_CORE_0; core_id ++) {
        ret |= wait_core(core_id);
    }
    return ret;
};

int wait_cores_pve0_available() {
    int ret = 0;
    for(uint32_t core_id = PVE_0_CLUSTER_0_CORE_0; core_id < PVE_0_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_0_CORE_NUMBER; core_id ++) {
        ret |= wait_core(core_id);
    }
    return ret;
};

int wait_cores_pve1() {
    int ret = 0;
    for(uint32_t core_id = PVE_1_CLUSTER_0_CORE_0; core_id < NUM_CORES; core_id ++) {
        ret |= wait_core(core_id);
    }
    return ret;
};

int wait_cores_pve1_available() {
    int ret = 0;
    for(uint32_t core_id = PVE_1_CLUSTER_0_CORE_0; core_id < PVE_1_CLUSTER_0_CORE_0 + HW_DEFINES_PVE_1_CORE_NUMBER; core_id ++) {
        ret |= wait_core(core_id);
    }
    return ret;
};

int wait_cores_available() {
    int ret = 0;
    ret |= wait_aicores_available();
    ret |= wait_cores_pve0_available();
    ret |= wait_cores_pve1_available();
    return ret;
};
