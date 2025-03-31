// (C) Copyright Axelera AI 2021
// All Rights Reserved
// *** Axelera AI Confidential ***

/*
 * Platform-Level Machine Timer (PLMT)
 *
 * The NCEPLMT100 module implemented in the AX65 cluster is a RISC-V compliant machine timer,
 * providing a real-time counter and timer interrupt generation capabilities.
 *
 *                     +---------------------------------+
 *                     |            NCEPLMT100           |
 *                     |                                 |
 *   mtime_clk         |     +--------------------+      |
 * --------------------|---->|        mtime       |      |            +---------------------+
 *                     |     +--------------------+      | stoptime   |                     |
 *                     |                                 |<-----------|      AndesCore      |
 *                     |     +--------------------+      |            |      Processor      |
 *                     |     |      mtimecmp      |      |  mtip      |                     |
 *                     |     +--------------------+      |----------->|                     |
 *                     |                                 |            +---------------------+
 *                     +---------------------------------+
 *
 * Timer Functionality:
 * - The PLMT comprises a 64-bit counter (mtime) driven by a fixed-frequency timer clock (mtime_clk),
 *   which is not affected by the dynamic clock adjustments in the rest of the system. The mtime
 *   counter continuously increments in real-time and is used for generating precise timing events.
 *
 * - Each hart in the AX65 cluster has a corresponding 64-bit mtime comparison register (mtimecmpn),
 *   which is used to set up timer interrupts. An interrupt is triggered when the mtime counter value
 *   equals or surpasses the value set in mtimecmpn. Writing to mtimecmpn also clears the interrupt
 *   and deasserts the interrupt signal (mtip).
 *
 * Memory Mapped Registers:
 * - The PLMT registers, including mtime and multiple mtimecmpn registers (one for each hart), are
 *   accessible through the AX65 internal bus fabric. These registers support only 32-bit or 64-bit
 *   access, with narrower accesses being undefined and potentially leading to errors.
 *
 * Address Mapping:
 * - mtime is located at offsets 0x0 - 0x7 (split across two 32-bit registers for full 64-bit access).
 * - Each mtimecmp register for the harts (mtimecmpn) is spaced starting from 0x8, with each subsequent
 *   register spaced 8 bytes apart (each 64-bit register split into two 32-bit parts).
 *
 * Note: for more info see AndesCore™ AX65 Data Sheet section 23.
 */
#pragma once

#include <interrupt.h>
#include <memorymap.h>
#include <platform.h>
#include <std/std_basetype.h>
#include <asm.h>
#include <thread.h>

void plmtSetupInterrupt(uint64_t set_timer_period);
void plmtDisableInterrupt(void);
void mtime_handler(void);

// Read MTIME cycle count.
uint64_t read_mtime();
// Delay by a specified amount of MTIME cycles (using a busy loop).
void delay_mtime_cycles(uint64_t mtime_cycles);
