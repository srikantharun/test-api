// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
#include <testutils.h>
#include <util.h>
#include <decoder/decoder.h>
#include "pctl_utils.h"

void check_config_access(volatile uint32_t *base_addr, size_t num_regs, const char *description) {
    printf("%s: reading %2lu registers at address %p...\r\n", description, num_regs, base_addr);
    for (size_t i = 0 ; i < num_regs; i++) {
        UNUSED(base_addr[i]);
    }
}

// List of register banks, taken from IP_Registers.html
struct reg_bank {
    uintptr_t offset;
    size_t num_regs;
    char const *description;
};
static struct reg_bank reg_banks[] = {
    { 0x0000, 20, "TOP" },
    { 0x0400, 28, "MCU"},
    { 0x1000, 12, "CORE0_DEC1A_TOP" },
    { 0x1000, 12, "CORE0_DEC1A_TOP" },
    { 0x1040, 24, "CORE0_DEC1A_CMD" },
    { 0x11C0,  4, "CORE0_DEC1A_STAT" },
    { 0x1200, 12, "CORE0_DEC1B_TOP" },
    { 0x1240, 24, "CORE0_DEC1B_CMD" },
    { 0x13C0,  4, "CORE0_DEC1B_STAT" },
    { 0x1800, 12, "CORE0_DEC2_TOP" },
    { 0x1840, 36, "CORE0_DEC2_CMD" },
    { 0x1AC0,  4, "CORE0_DEC2_STAT" },
    { 0x1B00, 12, "CORE0_SCD_TOP" },
    { 0x1B40, 10, "CORE0_SCD_CMD" },
    { 0x1BC0,  3, "CORE0_SCD_STAT" },
    { 0x1C00, 12, "CORE0_JPEG_TOP" },
    { 0x1C40, 31, "CORE0_JPEG_CMD" },
    { 0x1D40,  1, "CORE0_JPEG_STAT" },
    { 0x1F00, 17, "CORE0_AXI" },
    { 0x2000, 12, "CORE1_DEC1A_TOP" },
    { 0x2040, 24, "CORE1_DEC1A_CMD" },
    { 0x21C0,  4, "CORE1_DEC1A_STAT" },
    { 0x2200, 12, "CORE1_DEC1B_TOP" },
    { 0x2240, 24, "CORE1_DEC1B_CMD" },
    { 0x23C0,  4, "CORE1_DEC1B_STAT" },
    { 0x2800, 12, "CORE1_DEC2_TOP" },
    { 0x2840, 36, "CORE1_DEC2_CMD" },
    { 0x2AC0,  4, "CORE1_DEC2_STAT" },
    { 0x2B00, 12, "CORE1_SCD_TOP" },
    { 0x2B40, 10, "CORE1_SCD_CMD" },
    { 0x2BC0,  3, "CORE1_SCD_STAT" },
    { 0x2C00, 12, "CORE1_JPEG_TOP" },
    { 0x2C40, 31, "CORE1_JPEG_CMD" },
    { 0x2D40,  1, "CORE1_JPEG_STAT" },
    { 0x2F00, 17, "CORE1_AXI" }
};

int main() {
    printf("*** test_decoder_reg_read\r\n");

    pctl_enable_module(DECODER_MODULE);

    // No MCU firmware load required as we are only reading configuration
    // registers and do not care about the values.

    // WARNING: This test is unable to verify that the reads actually reach the
    // decoder IP. We only check that no access faults happen while reading.

    // WARNING: Bus errors are not supported on CVA6 cores, meaning this test
    //          only checks anything running on a real APU core.

    for (size_t i = 0; i < ARRAY_LENGTH(reg_banks); i++) {
        uintptr_t bank_base = DECODER_BASE + reg_banks[i].offset;
        check_config_access((volatile uint32_t *)bank_base, reg_banks[i].num_regs, reg_banks[i].description);
    }

    return 0;
}
