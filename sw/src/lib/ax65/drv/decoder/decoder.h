// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
#pragma once

#include <assert.h>
#include <stddef.h>
#include <stdint.h>

#include <memorymap.h>

// top + MCU offsets
#define DECODER_REG_TOP_OFFSET        (0x0000)
#define DECODER_REG_MCU_OFFSET        (0x0400)

struct decoder_reg_top {
    volatile uint32_t ip_identification_number;          // REG_TOP_000
    volatile uint32_t ip_architecture;                   // REG_TOP_001
    volatile uint32_t ip_date;                           // REG_TOP_002
    volatile uint32_t ip_version;                        // REG_TOP_003
    volatile uint32_t ip_soft_reset_control;             // REG_TOP_004 
    volatile uint32_t ip_interrupt_mask;                 // REG_TOP_005 
    volatile uint32_t ip_interrupt_status_and_clear;     // REG_TOP_006 
    volatile uint32_t reserved0;
    volatile uint32_t interrupt_from_mcu_to_cpu;         // REG_TOP_008 
    volatile uint32_t watchdog_control;                  // REG_TOP_009 
    volatile uint32_t watchdog_status;                   // REG_TOP_010
    volatile uint32_t watchdog_value;                    // REG_TOP_011
    volatile uint32_t timer_control;                     // REG_TOP_012
    volatile uint32_t timer_status;                      // REG_TOP_013
    volatile uint32_t timer_value;                       // REG_TOP_014
    volatile uint32_t reserved1;
    volatile uint32_t core_0_interrupt_mask;             // REG_TOP_016
    volatile uint32_t core_0_interrupt_status_and_clear; // REG_TOP_017
    volatile uint32_t core_1_interrupt_mask;             // REG_TOP_018
    volatile uint32_t core_1_interrupt_status_and_clear; // REG_TOP_019
};
_Static_assert(offsetof(struct decoder_reg_top, core_1_interrupt_status_and_clear) == 0x004C, "struct decoder_reg_top: last register has correct address offset");
#define DECODER_REG_TOP ((struct decoder_reg_top *)(DECODER_BASE + DECODER_REG_TOP_OFFSET))

struct decoder_reg_mcu {
    volatile uint32_t control_clock;           // REG_MCU_000
    volatile uint32_t control_reset;           // REG_MCU_001
    volatile uint32_t control_status;          // REG_MCU_002
    volatile uint32_t control_interrupt;       // REG_MCU_003
    volatile uint32_t address_boot_hi;         // REG_MCU_004
    volatile uint32_t address_boot_lo;         // REG_MCU_005
    volatile uint32_t reserved0[4];
    volatile uint32_t address_peripherals_hi;  // REG_MCU_010
    volatile uint32_t address_peripherals_lo;  // REG_MCU_011
    volatile uint32_t mtime_hi;                // REG_MCU_012
    volatile uint32_t mtime_lo;                // REG_MCU_013
    volatile uint32_t mtimecmp_hi;             // REG_MCU_014
    volatile uint32_t mtimecmp_lo;             // REG_MCU_015
    volatile uint32_t interrupt_mask;          // REG_MCU_016
    volatile uint32_t external_interrupt;      // REG_MCU_017
    volatile uint32_t external_interrupt_prev; // REG_MCU_018
    volatile uint32_t external_interrupt_next; // REG_MCU_019
    volatile uint32_t instruction_offset_hi;   // REG_MCU_020
    volatile uint32_t instruction_offset_lo;   // REG_MCU_021
    volatile uint32_t data_offset_hi;          // REG_MCU_022
    volatile uint32_t data_offset_lo;          // REG_MCU_023
    volatile uint32_t debug_module_address;    // REG_MCU_024
    volatile uint32_t debug_module_write;      // REG_MCU_025
    volatile uint32_t debug_module_read;       // REG_MCU_026
    volatile uint32_t debug_module_status;     // REG_MCU_027
};
_Static_assert(offsetof(struct decoder_reg_mcu, debug_module_status) == 0x006C, "struct decoder_reg_mcu: last register has correct address offset");
#define DECODER_REG_MCU ((struct decoder_reg_mcu *)(DECODER_BASE + DECODER_REG_MCU_OFFSET))

static inline void decoder_soft_reset() {
    DECODER_REG_TOP->ip_soft_reset_control = 0x1;
}
