#include <encoding.h>
#include <trap.h>
#include <testutils.h>

volatile bool failed;

void illegal_instruction(void) {
    return;
}

void valid_fn(void) {
    failed = false;
    return;
}

int main() {
    printf("*** test_rv_exception starts...\n");
    testcase_init();
    volatile uint64_t *invalid_ptr = (volatile uint64_t*)0x00000040;

    {
        printf("testing cause = 0: instruction (fetch) address misaligned\n");
        printf("  SKIP: misaligned instruction fetch supported by AX65\n");
        // void (*misaligned_fn)(void) = (void (*)(void))((uint64_t)invalid_ptr + 1);
        // failed = true;
        // exception_allow_once(CAUSE_MISALIGNED_FETCH, &valid_fn);
        // (*misaligned_fn)();
        // CHECK_TRUE(!failed, "misaligned instruction address exception not triggered");
    }

    {
        printf("testing cause = 1: instruction (fetch) access fault\n");
        void (*invalid_fn)(void) = (void (*)(void))invalid_ptr;
        failed = true;
        exception_allow_once(CAUSE_FETCH_ACCESS, &valid_fn);
        (*invalid_fn)();
        CHECK_TRUE(!failed, "instruction access fault not triggered");
    }

    {
        printf("testing cause = 2: illegal instruction\n");
        failed = false;
        exception_allow_once(CAUSE_ILLEGAL_INSTRUCTION, &&skip_illegal_instruction);
        asm volatile (".dword 0");
        failed = true;
    skip_illegal_instruction:
        CHECK_TRUE(!failed, "illegal instruction exception not triggered");
    }

    {
        printf("testing cause = 3: breakpoint\n");
        failed = false;
        exception_allow_once(CAUSE_BREAKPOINT, &&skip_breakpoint);
        asm volatile ("ebreak");
        failed = true;
    skip_breakpoint:
        CHECK_TRUE(!failed, "breakpoint exception not triggered");
    }

    {
        printf("testing cause = 4: load address misaligned\n");
        printf("  SKIP: misaligned loads supported by AX65\n");
    }

    {
        printf("testing cause = 5: load access fault\n");
        printf("  SKIP: load accesse errors may be imprecise on AX65 (delivered via BWE local interrupt)\n");
        // failed = false;
        // exception_allow_once(CAUSE_LOAD_ACCESS, &&skip_load_access_fault);
        // *invalid_ptr;
        // failed = true;
        // skip_load_access_fault:
        // CHECK_TRUE(!failed, "load access fault not triggered");
    }

    {
        printf("testing cause = 6: store/AMO address misaligned (regular store)\n");
        printf("  SKIP: misaligned stores supported by AX65\n");
    }

    {
        printf("testing cause = 7: store/AMO access fault (regular store)\n");
        printf("  SKIP: store accesse errors may be imprecise on AX65 (delivered via BWE local interrupt)\n");
        // failed = false;
        // exception_allow_once(CAUSE_STORE_ACCESS, &&skip_store_access_fault);
        // *invalid_ptr = 0xdeadbeef;
        // failed = true;
        // skip_store_access_fault:
        // CHECK_TRUE(!failed, "store access fault not triggered");
    }

    // TODO(mwipfli): Test causes 6/7 for AMO once supported by NoC.

    // TODO(mwipfli): Test causes starting from 8.


    return testcase_finalize();
}
