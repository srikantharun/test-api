// This is a test file for exception_handling
// CVA6V directed C tests : Author : Abhilash Chadhar
#include "common.h"

//todo - need to check with arch team
// Function to test exception handling for various scenarios
void test_exception_handling() {
    uint64_t result;

    // Test illegal instruction handling
    printf("Testing Illegal Instruction Handling...\n");
    asm volatile (" .word 0xFFFFFFFF ");  // Illegal instruction
    printf("Illegal Instruction Handling Test: Expected to trigger an illegal instruction exception.\n");

    // Test division by zero - should not trigger an exception but return defined results
    printf("Testing Division by Zero Handling...\n");
    uint64_t dividend = 42;
    uint64_t divisor = 0;

    // Unsigned division by zero
    asm volatile ("divu %0, %1, %2" : "=r"(result) : "r"(dividend), "r"(divisor));
    printf("Unsigned Division by Zero: Dividend=%lu, Divisor=%lu, Result=%lu\n", dividend, divisor, result);

    // Signed division by zero
    asm volatile ("div %0, %1, %2" : "=r"(result) : "r"(dividend), "r"(divisor));
    printf("Signed Division by Zero: Dividend=%ld, Divisor=%ld, Result=%ld\n", (int64_t)dividend, (int64_t)divisor, (int64_t)result);

    // Test environment call (ECALL)
    printf("Testing Environment Call Handling...\n");
    asm volatile ("ecall");
    printf("Environment Call Test: Expected to trigger an environment call exception.\n");

    // Test breakpoint (EBREAK)
    printf("Testing Breakpoint Handling...\n");
    asm volatile ("ebreak");
    printf("Breakpoint Handling Test: Expected to trigger a breakpoint exception.\n");

    printf("Exception Handling Tests Completed.\n");
}

int main() {
    printf("Running test: exception_handling\n");
    initialize_registers();
    test_exception_handling();
    return 0;
}
