// This is a test file for sp_based_load_store_instr_rvc
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

// Function to test RISC-V Compressed (RVC) stack-pointer-based load/store instructions
void test_sp_based_load_store_instr_rvc() {
    uint64_t result, expected;
    uint64_t stack_memory[32] = {0}; // Simulated stack memory for load/store instructions

    // Random initialization of stack memory
    for (int i = 0; i < 32; i++) {
        stack_memory[i] = (uint64_t)rand() << 32 | rand();
    }

    // Test c.lwsp (compressed load word from stack pointer)
    int32_t word;
    __asm__ volatile("c.lwsp %0, %1(%2)" : "=r"(word) : "I"(0), "r"(stack_memory));
    expected = (int32_t)stack_memory[0];
    printf("c.lwsp: loaded %d, Expected: %d %s\n", word, (int32_t)expected, word == (int32_t)expected ? "PASS" : "FAIL");

    // Test c.ldsp (compressed load double word from stack pointer)
    __asm__ volatile("c.ldsp %0, %1(%2)" : "=r"(result) : "I"(0), "r"(stack_memory));
    expected = stack_memory[0];
    printf("c.ldsp: loaded %lld, Expected: %lld %s\n", result, expected, result == expected ? "PASS" : "FAIL");

    // Test c.flwsp (compressed floating-point load word from stack pointer)
    float fword;
    __asm__ volatile("c.flwsp %0, %1(%2)" : "=f"(fword) : "I"(0), "r"(stack_memory));
    expected = *(float *)&stack_memory[0];
    printf("c.flwsp: loaded %f, Expected: %f %s\n", fword, *(float *)&expected, fword == *(float *)&expected ? "PASS" : "FAIL");

    // Test c.fldsp (compressed floating-point load double word from stack pointer)
    double fdouble;
    __asm__ volatile("c.fldsp %0, %1(%2)" : "=f"(fdouble) : "I"(0), "r"(stack_memory));
    expected = *(double *)&stack_memory[0];
    printf("c.fldsp: loaded %lf, Expected: %lf %s\n", fdouble, *(double *)&expected, fdouble == *(double *)&expected ? "PASS" : "FAIL");

    // Test c.swsp (compressed store word to stack pointer)
    word = (int32_t)rand();
    __asm__ volatile("c.swsp %1, %0(%2)" : : "I"(0), "r"(word), "r"(stack_memory));
    expected = word;
    printf("c.swsp: stored %d, Memory: %d %s\n", word, (int32_t)stack_memory[0], (int32_t)stack_memory[0] == (int32_t)expected ? "PASS" : "FAIL");

    // Test c.sdsp (compressed store double word to stack pointer)
    result = (uint64_t)rand() << 32 | rand();
    __asm__ volatile("c.sdsp %1, %0(%2)" : : "I"(0), "r"(result), "r"(stack_memory));
    expected = result;
    printf("c.sdsp: stored %lld, Memory: %lld %s\n", result, stack_memory[0], stack_memory[0] == expected ? "PASS" : "FAIL");

    // Test c.fswsp (compressed floating-point store word to stack pointer)
    fword = (float)rand() / (float)(rand() + 1);
    __asm__ volatile("c.fswsp %1, %0(%2)" : : "I"(0), "f"(fword), "r"(stack_memory));
    expected = *(uint32_t *)&fword;
    printf("c.fswsp: stored %f, Memory: %f %s\n", fword, *(float *)&stack_memory[0], *(float *)&stack_memory[0] == *(float *)&expected ? "PASS" : "FAIL");

    // Test c.fsdsp (compressed floating-point store double word to stack pointer)
    fdouble = (double)rand() / (double)(rand() + 1);
    __asm__ volatile("c.fsdsp %1, %0(%2)" : : "I"(0), "f"(fdouble), "r"(stack_memory));
    expected = *(uint64_t *)&fdouble;
    printf("c.fsdsp: stored %lf, Memory: %lf %s\n", fdouble, *(double *)&stack_memory[0], *(double *)&stack_memory[0] == *(double *)&expected ? "PASS" : "FAIL");
}

int main() {
    printf("Running test: sp_based_load_store_instr_rvc\n");
    initialize_registers();
    test_sp_based_load_store_instr_rvc();
    return 0;
}
