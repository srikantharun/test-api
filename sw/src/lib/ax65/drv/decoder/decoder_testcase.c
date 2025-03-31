// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Max Wipfli <max.wipfli@axelera.ai>
// Description: C implementation of the Allegro decoder integration testbench
#include <interrupt.h>
#include <printf.h>
#include <string.h>
#include <testutils.h>
#include <util.h>
#include <dw_timer/drv_dw_timer.h>
#include <timer.h>

#include "decoder.h"
#include "decoder_testcase.h"

// use UVM-accelerated memory operations if available
#ifdef UVM_SW_IPC
#include <uvm_ipc/uvm_sw_ipc.h>
#define _MEMCMP uvm_sw_ipc_memcmp
#define _MEMCPY uvm_sw_ipc_memcpy
#define _MEMSET uvm_sw_ipc_memset
#else
#define _MEMCMP memcmp
#define _MEMCPY memcpy
#define _MEMSET memset
#endif

#define DECODER_MCU2CPU_IRQ_BIT 30

// interrupt handling
// TODO: This should be atomic, but not yet supported my NoC.
static volatile uint64_t num_irq_pending = 0;

void decoder_irq_handler(void) {
// TODO: https://git.axelera.ai/prod/europa/-/issues/1478
//    printf("[decoder_testcase] IRQ handler: received IRQ\n");
    num_irq_pending++;
    uint32_t mask = BIT(DECODER_MCU2CPU_IRQ_BIT);
    ASSERT(
        (DECODER_REG_TOP->ip_interrupt_status_and_clear & mask) != 0,
        "decoder IRQ handler triggered but MCU2CPU IRQ bit not set"
    );
    // clear IRQ
    DECODER_REG_TOP->ip_interrupt_status_and_clear = mask;
//    printf("[decoder_testcase] IRQ handler: cleared IRQ\n");

    // Setup a timer in can the decoder IRQ occured right before the wfi
    timerDisable(0);
    timerSetMode(0, kTimerUserMode);
    timerLoad(0, 0x1000);
    timerSetupInterrupt();
    timerEnable(0);
}

static bool load_input_buffers(const char *frame_process, size_t frame_idx, struct decoder_testcase *testcase) {
    size_t num_loaded = 0;
    int memset_size;
    printf("[decoder_testcase] start_frame: Loading input buffers\n");

    for (size_t i = 0; i < testcase->in_buffers_length; i++) {
        struct decoder_testcase_buffer *buf = &testcase->in_buffers[i];

        // check if buffer matches frame index and process
        if (buf->frame_idx != frame_idx) continue;
        if (strcmp(buf->frame_process, frame_process) != 0) continue;

        printf("[decoder_testcase] start_frame: memcpy(0x%010x, 0x%010x, %0ld)\n",
            buf->load_address, buf->data, buf->size);
        _MEMCPY((void*)buf->load_address, buf->data, buf->size);

        // memset for the trailing zeros
        // 1024B max, to lower the runtime overhead
        if (buf->full_size > buf->size) {
           memset_size = ((buf->full_size - buf->size) > 1024) ? 1024 : (buf->full_size - buf->size);
           printf("[decoder_testcase] start_frame: memset(0x%010x, 0, %0ld)\n",
               buf->load_address+buf->size, memset_size);
          _MEMSET((void*)(buf->load_address+buf->size), 0, memset_size);
        }
        num_loaded++;
    }
    printf("[decoder_testcase] start_frame: Loaded %0ld input buffers\n", num_loaded);
    return true;
}

static bool initialize_output_buffers(const char *frame_process, size_t frame_idx, struct decoder_testcase *testcase) {
    // Initializing output buffers to zero is required as for some frames, the
    // decoder block will not use the entire buffer to write data. In that case,
    // the reference outputs are padded with zeros, so we need to do the same.
    size_t num_initalized = 0;

    for (size_t i = 0; i < testcase->ref_buffers_length; i++) {
        struct decoder_testcase_buffer *buf = &testcase->ref_buffers[i];

        // check if buffer matches frame index and process
        if (buf->frame_idx != frame_idx) continue;
        if (strcmp(buf->frame_process, frame_process) != 0) continue;

        printf("[decoder_testcase] start_frame: memset(0x%010x, 0, %0ld)\n",
            buf->load_address, buf->size);
        _MEMSET((void*)buf->load_address, 0, buf->size);
        num_initalized++;
    }
    printf("[decoder_testcase] start_frame: Initialized %0ld output buffers\n", num_initalized);
    return true;
}

static bool check_output_buffers(const char *frame_process, size_t frame_idx, struct decoder_testcase *testcase) {
    size_t num_checked = 0;
    bool success = true;
    printf("[decoder_testcase] end_frame: Checking output buffers\n");

    for (size_t i = 0; i < testcase->ref_buffers_length; i++) {
        struct decoder_testcase_buffer *buf = &testcase->ref_buffers[i];

        // check if buffer matches frame index and process
        if (buf->frame_idx != frame_idx) continue;
        if (strcmp(buf->frame_process, frame_process) != 0) continue;

        printf("[decoder_testcase] end_frame: memcmp(0x%010x, 0x%010x, %0ld)\n",
            buf->load_address, buf->data, buf->size);
        if (_MEMCMP((void*)buf->load_address, buf->data, buf->size) != 0) {
            printf("[decoder_testcase] end_frame: MISMATCH\n");
            success = false;
        }
        num_checked++;
    }
    printf("[decoder_testcase] end_frame: Checked %0ld output buffers\n", num_checked);
    if (success) {
        printf("[decoder_testcase] end_frame: PASS\n");
    } else {
        printf("[decoder_testcase] end_frame: FAIL\n");
    }
    return success;
}

static bool execute_single_instruction(
    struct decoder_testcase_instruction *inst,
    struct decoder_testcase *testcase
) {
    switch (inst->type) {
        case DECODER_TESTCASE_INSTRUCTION_START_FRAME: {
            printf("[decoder_testcase] start_frame(process=%s,idx=%0d)\n", inst->frame_process, inst->frame_idx);
            // Initialize output buffers before loading inputs, as some of them may overlap.
            // Doing it in reverse order could overwrite some of the inputs with zeros.
            if (!initialize_output_buffers(inst->frame_process, inst->frame_idx, testcase)) {
                return false;
            }
            if (!load_input_buffers(inst->frame_process, inst->frame_idx, testcase)) {
                return false;
            }
            if (strcmp(inst->frame_process, "MCU") != 0) {
                printf("[decoder_testcase] start_frame: Sending start signal to MCU\n");
                // Wait for IRQ bit to be cleared by the MCU (if set)
                while (DECODER_REG_MCU->control_interrupt & 0x1)
                    ;
                // Send signal by setting IRQ bit
                DECODER_REG_MCU->control_interrupt = 0x1;
            }
            break;
        }
        case DECODER_TESTCASE_INSTRUCTION_END_FRAME: {
            printf("[decoder_testcase] end_frame(process=%s,idx=%0d)\n", inst->frame_process, inst->frame_idx);
            if (!check_output_buffers(inst->frame_process, inst->frame_idx, testcase)) {
                return false;
            }
            break;
        }
        case DECODER_TESTCASE_INSTRUCTION_WRITE: {
            printf("[decoder_testcase] write(address=0x%010x,data=0x%08x)\n", inst->address, (uint64_t)inst->data);
            volatile uint32_t *reg = (volatile uint32_t*)inst->address;
            *reg = inst->data;
            break;
        }
        case DECODER_TESTCASE_INSTRUCTION_IRQ: {
            printf("[decoder_testcase] irq(address=0x%010x,bit=%0d)\n", inst->irq_address, inst->irq_bit);
            ASSERT((void*)inst->irq_address == &DECODER_REG_TOP->ip_interrupt_status_and_clear, "");
            ASSERT(inst->irq_bit == DECODER_MCU2CPU_IRQ_BIT, "");
            printf("[decoder_testcase] irq: wait for IRQ handler to receive interrupt\n");
            while (num_irq_pending == 0) {
                asm volatile ("wfi");
            }
            timerDisable(0);
            num_irq_pending--;
            printf("[decoder_testcase] irq: received IRQ\n");
            break;
        }
        default: {
            printf("[decoder_testcase] ERROR: Unimplemeted instruction type.\n");
            return false;
        }
    }
    return true;
}

bool decoder_testcase_execute(struct decoder_testcase *testcase) {

    if (DECODER_BASE != 0xB0000000) {
        printf("[decoder_testcase] ERROR: Decoder base address has changed.\n");
        printf("[decoder_testcase]        This requires manual changes to the testcase files.\n");
        return false;
    }
    if (SYS_SPM_BASE != 0x07000000) {
        printf("[decoder_testcase] ERROR: SYS-SPM base address has changed.\n");
        printf("[decoder_testcase]        This requires manual changes to the testcase files.\n");
        return false;
    }

    // full reset of the decoder IP
    printf("[decoder_testcase] Resetting decoder IP...\n");
    decoder_soft_reset();

#ifdef DDR_INIT_ZERO
    // in simulation, zero fake LPDDR to avoid reading X's into MCU cache
    printf("[decoder_testcase] Zeroing fake LPDDR...\n");
    _MEMSET((void*)DDR_1_BASE, 0, 64 * 1024 * 1024); // fake LPDDR is 64 MiB
#endif

    printf("[decoder_testcase] Enabling decoder interrupts...\n");
    HAL_INTERRUPT_ENABLE(IRQ_DCD_INT_SOURCE);
    HAL_INTERRUPT_SET_LEVEL(IRQ_DCD_INT_SOURCE, IRQ_PRIORITY_DEFAULT);
    num_irq_pending = 0;

    printf("[decoder_testcase] Executing testcase with %0ld instructions...\n", testcase->instructions_length);
    for (size_t i = 0; i < testcase->instructions_length; i++) {
        if (!execute_single_instruction(&testcase->instructions[i], testcase)) {
            return false;
        }
    }

    printf("[decoder_testcase] Testcase execution complete\n");

    return true;
}
