// (C) Copyright Axelera AI 2024
// All Rights Reserved
// *** Axelera AI Confidential ***
//
// Owner: Jovin Langenegger <jovin.langenegger@axelera.ai>
//
// This test was ported from the Andes AX65 test suit.
//
// Hetzner: /data/foundry/LIB/andes/v2.0.0/andes_vip/patterns/samples/test_pmp

#include "platform.h"
#include "printf.h"
#include <testutils.h>
#include <nds_csr.h>
#include <trap.h>

volatile long mcause;

long IACCFAULT_error_handler (SAVED_CONTEXT * context) {
    context->mepc = read_csr(NDS_MEPC) + 4;
    mcause = read_csr(NDS_MCAUSE) & 0x3FF;

    return 0;
}

long error_handler (SAVED_CONTEXT * context) {
    uint8_t  *except_pc;
    uint8_t  instr8;
    except_pc = (uint8_t *)read_csr(NDS_MEPC);
    instr8 = *(except_pc);
    if( (instr8 & 0x3) == 0x3)
            context->mepc = read_csr(NDS_MEPC) + 4;
    else
            context->mepc = read_csr(NDS_MEPC) + 2;
    mcause = read_csr(NDS_MCAUSE) & 0x3FF;

    return 0;
}

long ecall_handler(SAVED_CONTEXT *ctx)
{
    long pmpaddr;
    long pmpcfg;
    long addr;

    ctx->mepc = read_csr(NDS_MEPC) + 4;
    mcause = read_csr(NDS_MCAUSE) & 0x3FF;

    // Test PMP entry - check if we can write to the NDS_PMPADDR2 register
    write_csr(NDS_PMPADDR2, -1);
    pmpaddr = read_csr(NDS_PMPADDR2);

    CHECK_TRUE(pmpaddr != 0, "Failed to set NDS_PMPADDR2 register");

    // Enable all region at PMP entry 2
    write_csr(NDS_PMPADDR2, -1);
    write_csr(NDS_PMPCFG0, 0x1f << 16);

    // Set up PMP entry 0 ~ 1
    asm volatile("la %0, memory_region" : "=r"(addr));
    addr = addr >> 2;
    pmpcfg = (PMP_NAPOT | PMP_L);

    addr = (addr >> 1) << 1;
    write_csr(NDS_PMPADDR0, addr);
    set_csr(NDS_PMPCFG0, pmpcfg);

    return 0;
}

extern trap_func exception_handler[NUM_EXCEPTION_SOURCE];

int main()
{
    int *ptr;
	volatile int temp;
    UNUSED(temp); // The linker complains without this one here.

    exception_handler[EXC_INSTRUCTION_ACCESS_FAULT] = IACCFAULT_error_handler;
    exception_handler[EXC_LOAD_ACCESS_FAULT] = error_handler;
    exception_handler[EXC_STORE_AMO_ACCESS_FAULT] = error_handler;
    exception_handler[EXC_ENVIRONMENT_CALL_FROM_M_MODE] = ecall_handler;

    testcase_init();

    asm volatile("ecall");
    asm volatile("la %0, memory_region" : "=r"(ptr));
    temp = *ptr;
    CHECK_EQUAL_INT(EXC_LOAD_ACCESS_FAULT, mcause, "Failed to trigger the data load access fault.");

    *ptr = 0;
    CHECK_EQUAL_INT(EXC_STORE_AMO_ACCESS_FAULT, mcause, "Failed to trigger the data store access fault.");

    // A memory region for PMP test
	// - support 4 to 4096 (power of 2) bytes setting of PMP_GRANULARITY
	asm volatile("j memory_region");  // skip nop codes
	asm volatile(".p2align 12");      // aligned to 4KiB
	asm volatile("memory_region:");
	asm volatile(".fill 1024, 4, 0x00000013");  // fill 4KiB nop for PMP test

    CHECK_EQUAL_INT(EXC_INSTRUCTION_ACCESS_FAULT, mcause, "Failed to trigger the instruction access fault.");

    return testcase_finalize();
}
